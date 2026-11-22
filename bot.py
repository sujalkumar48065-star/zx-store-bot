# ZX STORE

from __future__ import annotations

import asyncio
import base64
import gzip
import hashlib
import html
import io
import json
import logging
import os
import random
import re
import secrets
import sqlite3
import string
import time
from datetime import datetime, timedelta

import aiosqlite
from telegram import (
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    InputFile,
    KeyboardButton,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
    Update,
)
from telegram.constants import ParseMode
from telegram.error import BadRequest, NetworkError, RetryAfter, TelegramError, TimedOut
from telegram.ext import (
    Application,
    ApplicationBuilder,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    ConversationHandler,
    MessageHandler,
    filters,
)
from telegram.request import HTTPXRequest


# Security: never hardcode the bot token. Set the BOT_TOKEN environment variable
# (or place the token in a file named bot_token.txt next to this script).
def _load_bot_token() -> str:
    token = os.environ.get("BOT_TOKEN", "").strip()
    if token:
        return token
    token_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bot_token.txt")
    try:
        if os.path.exists(token_file):
            with open(token_file, "r", encoding="utf-8") as fh:
                return fh.read().strip()
    except OSError:
        pass
    return ""


BOT_TOKEN = _load_bot_token()
OWNER_ID = int(os.environ.get("OWNER_ID", "8799679469"))
BOT_USERNAME = os.environ.get("BOT_USERNAME", "ZX_MULTI_REACTIONBOT").lstrip("@")
BOT_VERSION = "v1.0"

DB_PATH = os.environ.get(
    "DB_PATH",
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "zx_store.db"),
)

logging.basicConfig(
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
    level=logging.INFO,
)
logging.getLogger("httpx").setLevel(logging.WARNING)
log = logging.getLogger("zx_store")


def _env_int(name: str, default: int = 0) -> int:
    raw = os.environ.get(name, "").strip()
    if not raw:
        return default
    try:
        return int(raw)
    except ValueError:
        log.warning("Ignoring invalid integer for %s: %r", name, raw)
        return default


def _env_float(name: str, default: float) -> float:
    raw = os.environ.get(name, "").strip()
    if not raw:
        return default
    try:
        return float(raw)
    except ValueError:
        log.warning("Ignoring invalid number for %s: %r", name, raw)
        return default


# Telegram channel used as the primary persistent database. The channel must
# be private, and the bot must be an administrator with "Post Messages" and
# "Pin Messages" permissions.
DATABASE_CHANNEL_ID = _env_int("DATABASE_CHANNEL_ID", 0)
CHANNEL_DB_FLUSH_INTERVAL = max(1.0, _env_float("CHANNEL_DB_FLUSH_INTERVAL", 4.0))
CHANNEL_DB_REQUIRED = os.environ.get("CHANNEL_DB_REQUIRED", "0").strip().lower() not in {
    "0",
    "false",
    "no",
    "off",
}
CHANNEL_DB_SNAPSHOT_PREFIX = "zx_store_snapshot_"
REMOVE_ADMIN_IDS = {
    int(part)
    for part in os.environ.get("REMOVE_ADMIN_IDS", "").replace(",", " ").split()
    if part.lstrip("-").isdigit()
}

# Optional legacy product file storage can share the same channel.
_PRODUCT_CHANNEL_ID = (
    os.environ.get("PRODUCT_CHANNEL_ID", "").strip()
    or (str(DATABASE_CHANNEL_ID) if DATABASE_CHANNEL_ID else "")
)

DEFAULT_SETTINGS = {
    "bot_name": "𝐙𝚇 𝐒ᴛᴏʀᴇ",
    "product_channel_id": _PRODUCT_CHANNEL_ID,
    "referral_reward": "1",
    "referral_reward_enabled": "1",
    "leaderboard_enabled": "1",
    "support_username": "duifioookn2",
    "force_join": "1",
    "maintenance": "0",
    "premium_pricing": json.dumps([
        {"days": 7, "price": 300},
        {"days": 30, "price": 900},
        {"days": 90, "price": 2200},
        {"days": 0, "price": 6000},
    ]),
    "referral_milestones": json.dumps([
        {"count": 5, "reward": 100},
        {"count": 10, "reward": 250},
        {"count": 25, "reward": 700},
        {"count": 50, "reward": 1500},
    ]),
    "streak_rewards": json.dumps([
        {"days": 3, "reward": 30},
        {"days": 7, "reward": 80},
        {"days": 14, "reward": 150},
        {"days": 30, "reward": 500},
    ]),
}

FILE_TYPE_ICON = {
    "document": "📄", "video": "🎬", "audio": "🎵", "photo": "🖼",
    "voice": "🎙", "animation": "🎞", "video_note": "🎥",
}

USE_CUSTOM_EMOJI = False
CUSTOM_EMOJI: dict[str, str] = {
}

DIVIDER = "───────────────────"


_db_lock = asyncio.Lock()


DUPLICATE_COOLDOWN_SECONDS = 0.6
FLOOD_WINDOW_SECONDS = 3.0
FLOOD_MAX_ACTIONS = 12

_last_action_by_key: dict[tuple[int, str], float] = {}
_recent_action_times: dict[int, list[float]] = {}

_user_action_locks: dict[int, asyncio.Lock] = {}
_user_action_locks_guard = asyncio.Lock()


async def get_user_action_lock(user_id: int) -> asyncio.Lock:
    async with _user_action_locks_guard:
        lock = _user_action_locks.get(user_id)
        if lock is None:
            lock = asyncio.Lock()
            _user_action_locks[user_id] = lock
        return lock


async def group_restriction_guard(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    chat = update.effective_chat
    if chat is None or chat.type == "private":
        return

    if update.callback_query:
        is_bot_trigger = True
    else:
        msg = update.message
        if msg is None or not msg.text:
            return
        is_bot_trigger = msg.text.startswith("/") or msg.text in TEXT_ROUTES

    if not is_bot_trigger:
        return

    try:
        await update.effective_message.reply_text("📩 Please Use this bot in Bot DM.")
    except TelegramError:
        pass
    raise ApplicationHandlerStop


async def flood_guard(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    if user is None:
        return

    if update.callback_query:
        action_id = update.callback_query.data or ""
    elif update.message and update.message.text:
        action_id = update.message.text
    else:
        return

    now = time.monotonic()

    key = (user.id, action_id)
    last_same = _last_action_by_key.get(key, 0.0)
    _last_action_by_key[key] = now
    if now - last_same < DUPLICATE_COOLDOWN_SECONDS:
        if update.callback_query:
            try:
                await update.callback_query.answer()
            except TelegramError:
                pass
        raise ApplicationHandlerStop

    history = _recent_action_times.setdefault(user.id, [])
    history[:] = [t for t in history if now - t < FLOOD_WINDOW_SECONDS]
    history.append(now)
    if len(history) > FLOOD_MAX_ACTIONS:
        if update.callback_query:
            try:
                await update.callback_query.answer("⏳ Please slow down a little.", show_alert=False)
            except TelegramError:
                pass
        raise ApplicationHandlerStop


class RateLimiter:
    def __init__(self, rate: float):
        self.interval = 1.0 / rate
        self._lock = asyncio.Lock()
        self._next_time = time.monotonic()

    async def acquire(self) -> None:
        async with self._lock:
            now = time.monotonic()
            wait = self._next_time - now
            if wait > 0:
                await asyncio.sleep(wait)
                now = time.monotonic()
            self._next_time = now + self.interval


TELEGRAM_SEND_LIMITER = RateLimiter(25)

DB_POOL_SIZE = int(os.environ.get("DB_POOL_SIZE", "64"))
_db_pool: asyncio.Queue[aiosqlite.Connection] = None

# Active channel-backed storage layer (None until initialization completes).
_channel_db: ChannelDatabase | None = None


async def init_db_pool() -> None:
    global _db_pool
    _db_pool = asyncio.Queue(maxsize=DB_POOL_SIZE)
    for _ in range(DB_POOL_SIZE):
        conn = await aiosqlite.connect(DB_PATH)
        conn.row_factory = aiosqlite.Row
        await conn.execute("PRAGMA journal_mode = WAL;")
        await conn.execute("PRAGMA synchronous = NORMAL;")
        await conn.execute("PRAGMA busy_timeout = 8000;")
        await conn.execute("PRAGMA foreign_keys = ON;")
        await _db_pool.put(conn)
    log.info("DB connection pool ready (%d connections)", DB_POOL_SIZE)


async def close_db_pool() -> None:
    if _db_pool is None:
        return
    while not _db_pool.empty():
        conn = await _db_pool.get()
        await conn.close()


class _ChannelAwareConnection:
    """Thin proxy around an aiosqlite connection.

    All reads/writes pass through unchanged. On ``commit()`` the write is
    committed locally first, then awaited until the channel snapshot that
    contains this commit has been confirmed by Telegram. This keeps the
    existing SQL-based code working while making the Telegram channel the
    durable source of truth.
    """

    __slots__ = ("_conn",)

    def __init__(self, conn: aiosqlite.Connection):
        object.__setattr__(self, "_conn", conn)

    def __getattr__(self, name):
        return getattr(self._conn, name)

    def __setattr__(self, name, value):
        if name == "_conn":
            object.__setattr__(self, name, value)
        else:
            setattr(self._conn, name, value)

    async def commit(self) -> None:
        store = _channel_db
        if store is None or not store.active:
            await self._conn.commit()
            return
        try:
            await self._conn.execute(
                "INSERT INTO channel_db_meta (key, value) VALUES ('write_seq', '1') "
                "ON CONFLICT(key) DO UPDATE SET value = CAST(value AS INTEGER) + 1"
            )
        except aiosqlite.Error:
            # Meta table may not exist during unusual recovery paths; the
            # commit must still succeed.
            pass
        await self._conn.commit()
        store.mark_dirty()
        await store.ensure_flushed()

    async def rollback(self) -> None:
        await self._conn.rollback()


class _PooledConnection:
    """Async context manager — borrows a connection from the shared pool
    instead of opening a new one. Drop-in replacement for
    `aiosqlite.connect(DB_PATH)` at every call site."""

    async def __aenter__(self) -> _ChannelAwareConnection:
        self.conn = await _db_pool.get()
        self.wrapped = _ChannelAwareConnection(self.conn)
        return self.wrapped

    async def __aexit__(self, exc_type, exc, tb) -> None:
        if exc_type is not None:
            # Never return a connection to the pool with an open write
            # transaction (e.g. after an IntegrityError), otherwise other
            # pooled connections can hit "database is locked".
            try:
                await self.conn.rollback()
            except aiosqlite.Error:
                pass
        await _db_pool.put(self.conn)


def db_conn() -> _PooledConnection:
    return _PooledConnection()


CHANNEL_DB_FORMAT = "ZX_STORE_CHANNEL_DB"
CHANNEL_DB_VERSION = 1
CHANNEL_DB_SCHEMA_VERSION = 1
CHANNEL_DB_MAX_BYTES = 49 * 1024 * 1024
CHANNEL_DB_TABLE_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
CHANNEL_DB_EXCLUDED_TABLES = {"channel_db_meta"}


class ChannelDatabaseError(RuntimeError):
    """Raised when the Telegram channel database cannot be used safely."""


def _quote_ident(name: str) -> str:
    if not CHANNEL_DB_TABLE_RE.match(name):
        raise ChannelDatabaseError(f"Unsafe SQL identifier: {name!r}")
    return '"' + name.replace('"', '""') + '"'


def _json_safe_value(value):
    if isinstance(value, (bytes, bytearray, memoryview)):
        return {"__zx_bytes__": base64.b64encode(bytes(value)).decode("ascii")}
    return value


def _json_restore_value(value):
    if isinstance(value, dict) and set(value) == {"__zx_bytes__"}:
        try:
            return base64.b64decode(value["__zx_bytes__"], validate=True)
        except Exception as exc:
            raise ChannelDatabaseError("Invalid binary value in channel snapshot") from exc
    return value


def _canonical_snapshot_bytes(envelope: dict) -> bytes:
    return json.dumps(
        {
            "sequence": envelope.get("sequence", 0),
            "tables": envelope.get("tables", {}),
            "sequences": envelope.get("sequences", {}),
        },
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")


def _snapshot_checksum(envelope: dict) -> str:
    return hashlib.sha256(_canonical_snapshot_bytes(envelope)).hexdigest()


def _validate_envelope(envelope) -> dict:
    if not isinstance(envelope, dict):
        raise ChannelDatabaseError("Channel snapshot is not a JSON object")
    if envelope.get("format") != CHANNEL_DB_FORMAT:
        raise ChannelDatabaseError("Pinned message is not a ZX Store channel database snapshot")
    if envelope.get("version") != CHANNEL_DB_VERSION:
        raise ChannelDatabaseError(
            f"Unsupported channel snapshot version: {envelope.get('version')!r}"
        )
    schema_version = envelope.get("schema_version")
    if not isinstance(schema_version, int) or schema_version < 1:
        raise ChannelDatabaseError("Invalid channel snapshot schema version")
    if schema_version > CHANNEL_DB_SCHEMA_VERSION:
        raise ChannelDatabaseError(
            f"Channel snapshot uses newer schema {schema_version}; update the bot first"
        )
    sequence = envelope.get("sequence", 0)
    if not isinstance(sequence, int) or sequence < 0:
        raise ChannelDatabaseError("Invalid channel snapshot sequence")
    tables = envelope.get("tables")
    if not isinstance(tables, dict):
        raise ChannelDatabaseError("Channel snapshot has no tables object")
    sequences = envelope.get("sequences", {})
    if not isinstance(sequences, dict):
        raise ChannelDatabaseError("Invalid channel snapshot sequences")
    for name, table in tables.items():
        if not isinstance(name, str) or not CHANNEL_DB_TABLE_RE.match(name):
            raise ChannelDatabaseError(f"Invalid table name in snapshot: {name!r}")
        if name in CHANNEL_DB_EXCLUDED_TABLES:
            raise ChannelDatabaseError(f"Table {name!r} must not be in a snapshot")
        if not isinstance(table, dict):
            raise ChannelDatabaseError(f"Invalid table definition for {name!r}")
        columns = table.get("columns")
        records = table.get("records")
        if (
            not isinstance(columns, list)
            or not columns
            or not all(isinstance(c, str) and CHANNEL_DB_TABLE_RE.match(c) for c in columns)
        ):
            raise ChannelDatabaseError(f"Invalid columns for table {name!r}")
        if not isinstance(records, list):
            raise ChannelDatabaseError(f"Invalid records for table {name!r}")
        seen_ids = set()
        for record in records:
            if not isinstance(record, dict):
                raise ChannelDatabaseError(f"Invalid record in table {name!r}")
            if record.get("record_type") != name:
                raise ChannelDatabaseError(f"Record type mismatch in table {name!r}")
            record_id = record.get("record_id")
            if not isinstance(record_id, str) or not record_id:
                raise ChannelDatabaseError(f"Missing record_id in table {name!r}")
            if record_id in seen_ids:
                raise ChannelDatabaseError(f"Duplicate record_id {record_id!r} in {name!r}")
            seen_ids.add(record_id)
            if not isinstance(record.get("data_version", 1), int):
                raise ChannelDatabaseError(f"Invalid data_version in table {name!r}")
            payload = record.get("payload")
            if not isinstance(payload, dict):
                raise ChannelDatabaseError(f"Invalid payload in table {name!r}")
            if any(column not in columns for column in payload):
                raise ChannelDatabaseError(f"Unknown column in snapshot table {name!r}")
    checksum = envelope.get("checksum")
    if not isinstance(checksum, str) or len(checksum) != 64:
        raise ChannelDatabaseError("Channel snapshot checksum is missing or malformed")
    if not secrets.compare_digest(checksum, _snapshot_checksum(envelope)):
        raise ChannelDatabaseError("Channel snapshot checksum mismatch")
    return envelope


def _build_snapshot_sync(db_path: str) -> dict:
    """Read a transactionally consistent copy of every application table."""
    if not os.path.exists(db_path):
        raise ChannelDatabaseError(f"Database file not found: {db_path}")
    conn = sqlite3.connect(db_path, timeout=30)
    conn.row_factory = sqlite3.Row
    try:
        conn.execute("PRAGMA busy_timeout=8000")
        conn.execute("BEGIN")
        rows = conn.execute(
            "SELECT name FROM sqlite_master WHERE type='table' "
            "AND name NOT LIKE 'sqlite_%'"
        ).fetchall()
        table_names = sorted(
            row[0]
            for row in rows
            if row[0] not in CHANNEL_DB_EXCLUDED_TABLES
            and CHANNEL_DB_TABLE_RE.match(row[0])
        )
        tables = {}
        for name in table_names:
            quoted = _quote_ident(name)
            info = conn.execute(f"PRAGMA table_info({quoted})").fetchall()
            columns = [row[1] for row in info]
            if not columns:
                continue
            primary_key = [row[1] for row in info if row[5]]
            records = []
            for index, row in enumerate(conn.execute(f"SELECT * FROM {quoted}").fetchall()):
                record_id = (
                    str(row[primary_key[0]]) if len(primary_key) == 1 else f"row:{index}"
                )
                records.append(
                    {
                        "record_id": record_id,
                        "record_type": name,
                        "data_version": 1,
                        "payload": {column: _json_safe_value(row[column]) for column in columns},
                    }
                )
            tables[name] = {
                "columns": columns,
                "primary_key": primary_key,
                "records": records,
            }
        sequences = {}
        try:
            for row in conn.execute("SELECT name, seq FROM sqlite_sequence"):
                if row[0] in tables:
                    sequences[row[0]] = int(row[1])
        except sqlite3.OperationalError:
            pass
        sequence = 0
        try:
            meta_row = conn.execute(
                "SELECT value FROM channel_db_meta WHERE key = 'write_seq'"
            ).fetchone()
            if meta_row is not None:
                sequence = int(meta_row[0])
        except (sqlite3.OperationalError, TypeError, ValueError):
            sequence = 0
        conn.commit()
        return {"tables": tables, "sequences": sequences, "sequence": max(0, sequence)}
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()


def _read_channel_meta_sync(db_path: str) -> dict:
    if not os.path.exists(db_path):
        return {}
    conn = sqlite3.connect(db_path, timeout=30)
    try:
        conn.execute("PRAGMA busy_timeout=8000")
        rows = conn.execute("SELECT key, value FROM channel_db_meta").fetchall()
        return {str(key): str(value) for key, value in rows}
    except sqlite3.OperationalError:
        return {}
    finally:
        conn.close()


def _write_channel_meta_sync(db_path: str, values: dict, max_keys=()) -> None:
    conn = sqlite3.connect(db_path, timeout=30)
    try:
        conn.execute("PRAGMA busy_timeout=8000")
        conn.execute(
            "CREATE TABLE IF NOT EXISTS channel_db_meta ("
            "key TEXT PRIMARY KEY, value TEXT NOT NULL)"
        )
        for key, value in values.items():
            if key in max_keys:
                # Never move a sequence backwards if another connection
                # committed a newer write while this snapshot was uploading.
                conn.execute(
                    "INSERT INTO channel_db_meta (key, value) VALUES (?, ?) "
                    "ON CONFLICT(key) DO UPDATE SET value = CAST(MAX("
                    "CAST(channel_db_meta.value AS INTEGER), "
                    "CAST(excluded.value AS INTEGER)) AS TEXT)",
                    (str(key), str(value)),
                )
            else:
                conn.execute(
                    "INSERT INTO channel_db_meta (key, value) VALUES (?, ?) "
                    "ON CONFLICT(key) DO UPDATE SET value = excluded.value",
                    (str(key), str(value)),
                )
        conn.commit()
    finally:
        conn.close()


def _mark_channel_snapshot_flushed(
    db_path: str, sequence: int, checksum: str, **extra
) -> None:
    """Record a confirmed snapshot without ever lowering the local write
    sequence. A concurrent commit may have advanced it while the snapshot was
    being built; keeping the higher value makes the next startup upload that
    local change instead of silently restoring older channel data."""
    values = {
        "write_seq": int(sequence),
        "flushed_seq": int(sequence),
        "checksum": checksum,
    }
    values.update(extra)
    _write_channel_meta_sync(db_path, values, max_keys=("write_seq",))


def _restore_snapshot_sync(db_path: str, envelope: dict) -> None:
    """Replace local application tables with a validated channel snapshot."""
    _validate_envelope(envelope)
    conn = sqlite3.connect(db_path, timeout=30)
    try:
        conn.execute("PRAGMA busy_timeout=8000")
        conn.execute("PRAGMA foreign_keys=OFF")
        local_tables = {
            row[0]
            for row in conn.execute(
                "SELECT name FROM sqlite_master WHERE type='table' "
                "AND name NOT LIKE 'sqlite_%'"
            )
        }
        for name in envelope["tables"]:
            if name not in local_tables:
                raise ChannelDatabaseError(
                    f"Channel snapshot contains unknown table {name!r}"
                )
        conn.execute("BEGIN IMMEDIATE")
        for name, table in envelope["tables"].items():
            quoted = _quote_ident(name)
            local_columns = {
                row[1] for row in conn.execute(f"PRAGMA table_info({quoted})")
            }
            missing = [column for column in table["columns"] if column not in local_columns]
            if missing:
                raise ChannelDatabaseError(
                    f"Channel snapshot table {name!r} is missing local columns: {missing}"
                )
            conn.execute(f"DELETE FROM {quoted}")
            records = table["records"]
            if records:
                column_list = ", ".join(_quote_ident(column) for column in table["columns"])
                placeholders = ", ".join("?" for _ in table["columns"])
                values = [
                    [
                        _json_restore_value(record["payload"].get(column))
                        for column in table["columns"]
                    ]
                    for record in records
                ]
                conn.executemany(
                    f"INSERT INTO {quoted} ({column_list}) VALUES ({placeholders})",
                    values,
                )
        for name in local_tables - set(envelope["tables"]) - CHANNEL_DB_EXCLUDED_TABLES:
            if CHANNEL_DB_TABLE_RE.match(name):
                conn.execute(f"DELETE FROM {_quote_ident(name)}")
        for name, sequence in envelope.get("sequences", {}).items():
            if name not in local_tables or not CHANNEL_DB_TABLE_RE.match(name):
                continue
            try:
                conn.execute("DELETE FROM sqlite_sequence WHERE name = ?", (name,))
                conn.execute(
                    "INSERT INTO sqlite_sequence (name, seq) VALUES (?, ?)",
                    (name, int(sequence)),
                )
            except sqlite3.OperationalError:
                break
        violations = conn.execute("PRAGMA foreign_key_check").fetchall()
        if violations:
            raise ChannelDatabaseError(
                f"Channel snapshot violates {len(violations)} foreign key constraint(s)"
            )
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()
    now = datetime.now().isoformat(timespec="seconds")
    _mark_channel_snapshot_flushed(
        db_path,
        int(envelope.get("sequence", 0)),
        envelope["checksum"],
        restored_at=now,
    )


def _enum_text(value) -> str:
    if value is None:
        return ""
    return str(getattr(value, "value", value)).lower()


class ChannelDatabase:
    """Durable database snapshots stored as a pinned Telegram channel document."""

    def __init__(
        self,
        bot,
        channel_id: int,
        db_path: str,
        flush_interval: float = CHANNEL_DB_FLUSH_INTERVAL,
    ):
        self.bot = bot
        self.channel_id = int(channel_id)
        self.db_path = db_path
        self.flush_interval = max(1.0, float(flush_interval))
        self.active = False
        self.initialized = False
        self.snapshot: dict | None = None
        self.snapshot_checksum: str | None = None
        self.last_sequence = 0
        self.channel_title = ""
        self.pinned_message_id: int | None = None
        self.upload_count = 0
        self.last_upload_at = 0.0
        self.last_error: str | None = None
        self._dirty = 0
        self._flushed = 0
        self._lock = asyncio.Lock()
        self._closed = False

    async def _tg_call(self, func, *args, **kwargs):
        delay = 1.0
        for attempt in range(1, 5):
            try:
                return await func(*args, **kwargs)
            except RetryAfter as exc:
                raw = getattr(exc, "retry_after", 5)
                wait = raw.total_seconds() if hasattr(raw, "total_seconds") else float(raw)
                wait = max(0.5, wait) + 0.5
                self.last_error = f"rate limited for {wait:.1f}s"
                log.warning("Channel database rate limited; sleeping %.1fs", wait)
                if attempt == 4:
                    raise ChannelDatabaseError(
                        f"Telegram rate limit prevented channel database update ({wait:.1f}s)"
                    ) from exc
                await asyncio.sleep(wait)
            except (NetworkError, TimedOut) as exc:
                self.last_error = str(exc)
                if attempt == 4:
                    raise ChannelDatabaseError(
                        f"Telegram network error during channel database operation: {exc}"
                    ) from exc
                log.warning(
                    "Channel database network error (attempt %s/4): %s", attempt, exc
                )
                await asyncio.sleep(delay)
                delay = min(delay * 2, 30)
            except TelegramError as exc:
                self.last_error = str(exc)
                raise ChannelDatabaseError(
                    f"Telegram rejected a channel database operation: {exc}"
                ) from exc
        raise ChannelDatabaseError("Channel database operation failed")

    async def _download_bytes(self, file) -> bytes:
        delay = 1.0
        for attempt in range(1, 4):
            try:
                return bytes(await file.download_as_bytearray())
            except (NetworkError, TimedOut) as exc:
                if attempt == 3:
                    raise ChannelDatabaseError(
                        f"Could not download channel snapshot: {exc}"
                    ) from exc
                await asyncio.sleep(delay)
                delay = min(delay * 2, 20)
        raise ChannelDatabaseError("Could not download channel snapshot")

    async def _download_envelope(self, file_id: str) -> dict:
        file = await self._tg_call(self.bot.get_file, file_id)
        raw = await self._download_bytes(file)
        try:
            raw = gzip.decompress(raw)
        except OSError:
            # Older snapshots may have been stored without compression.
            pass
        try:
            envelope = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ChannelDatabaseError("Channel snapshot is not valid JSON") from exc
        return _validate_envelope(envelope)

    async def initialize(self) -> dict | None:
        if not self.channel_id:
            raise ChannelDatabaseError(
                "DATABASE_CHANNEL_ID is not set. Create a private channel, add the bot "
                "as an administrator with post/pin permissions, and set its numeric ID."
            )
        me = await self._tg_call(self.bot.get_me)
        try:
            chat = await self._tg_call(self.bot.get_chat, self.channel_id)
        except TelegramError as exc:
            raise ChannelDatabaseError(
                f"Cannot access DATABASE_CHANNEL_ID {self.channel_id}: {exc}. "
                "Make sure the bot is a member/administrator of that channel."
            ) from exc
        if _enum_text(getattr(chat, "type", "")) != "channel":
            raise ChannelDatabaseError(
                f"DATABASE_CHANNEL_ID {self.channel_id} is not a Telegram channel"
            )
        self.channel_title = str(getattr(chat, "title", "") or self.channel_id)
        try:
            member = await self._tg_call(
                self.bot.get_chat_member, self.channel_id, me.id
            )
        except TelegramError as exc:
            raise ChannelDatabaseError(
                f"Cannot verify bot permissions in channel {self.channel_id}: {exc}"
            ) from exc
        status = _enum_text(getattr(member, "status", ""))
        if status not in {"administrator", "creator"}:
            raise ChannelDatabaseError(
                "The bot must be an administrator of DATABASE_CHANNEL_ID"
            )
        if status == "administrator":
            if getattr(member, "can_post_messages", True) is False:
                raise ChannelDatabaseError(
                    "The bot lacks the 'Post Messages' permission in DATABASE_CHANNEL_ID"
                )
            if getattr(member, "can_pin_messages", True) is False:
                raise ChannelDatabaseError(
                    "The bot lacks the 'Pin Messages' permission in DATABASE_CHANNEL_ID"
                )
            if getattr(member, "can_delete_messages", True) is False:
                raise ChannelDatabaseError(
                    "The bot lacks the 'Delete Messages' permission in DATABASE_CHANNEL_ID"
                )
        pinned = getattr(chat, "pinned_message", None)
        if pinned is not None:
            document = getattr(pinned, "document", None)
            filename = str(getattr(document, "file_name", "") or "")
            if document is not None and filename.startswith(CHANNEL_DB_SNAPSHOT_PREFIX):
                log.info("Loading channel database snapshot %s", filename)
                envelope = await self._download_envelope(document.file_id)
                self.snapshot = envelope
                self.snapshot_checksum = envelope["checksum"]
                self.last_sequence = int(envelope.get("sequence", 0))
                self.pinned_message_id = int(pinned.message_id)
                log.info(
                    "Channel snapshot ready: seq=%s tables=%s",
                    self.last_sequence,
                    len(envelope["tables"]),
                )
            elif document is not None:
                log.warning(
                    "Pinned message in DATABASE_CHANNEL_ID is not a ZX Store snapshot; "
                    "a new snapshot will replace the pin."
                )
        self.initialized = True
        return self.snapshot

    def activate(self) -> None:
        if not self.initialized:
            raise ChannelDatabaseError("Channel database has not been initialized")
        self.active = True
        self._closed = False
        self._dirty = 0
        self._flushed = 0

    def mark_dirty(self) -> None:
        self._dirty += 1

    def _make_envelope(self, payload: dict) -> dict:
        now = datetime.now().isoformat(timespec="seconds")
        envelope = {
            "format": CHANNEL_DB_FORMAT,
            "version": CHANNEL_DB_VERSION,
            "schema_version": CHANNEL_DB_SCHEMA_VERSION,
            "created_at": now,
            "updated_at": now,
            "sequence": int(payload.get("sequence", 0)),
            "tables": payload["tables"],
            "sequences": payload.get("sequences", {}),
        }
        envelope["checksum"] = _snapshot_checksum(envelope)
        return envelope

    async def _upload_envelope(self, envelope: dict) -> int:
        serialized = json.dumps(
            envelope, ensure_ascii=False, separators=(",", ":")
        ).encode("utf-8")
        data = gzip.compress(serialized, compresslevel=6)
        if len(data) > CHANNEL_DB_MAX_BYTES:
            raise ChannelDatabaseError(
                f"Database snapshot is {len(data) / 1024 / 1024:.1f} MiB, over the "
                "Telegram bot upload limit. Reduce stored data or use a larger storage "
                "backend."
            )
        filename = (
            f"{CHANNEL_DB_SNAPSHOT_PREFIX}v{CHANNEL_DB_VERSION}_"
            f"{envelope['sequence']}_{envelope['checksum'][:12]}.json.gz"
        )
        rows = sum(len(table["records"]) for table in envelope["tables"].values())
        caption = (
            f"ZX Store database snapshot | v{CHANNEL_DB_VERSION} | seq {envelope['sequence']} "
            f"| {rows} rows | {len(envelope['tables'])} tables"
        )
        sent = await self._tg_call(
            self.bot.send_document,
            chat_id=self.channel_id,
            document=InputFile(io.BytesIO(data), filename=filename),
            caption=caption[:1024],
            disable_notification=True,
        )
        try:
            await self._tg_call(
                self.bot.pin_chat_message,
                chat_id=self.channel_id,
                message_id=sent.message_id,
                disable_notification=True,
            )
        except Exception:
            try:
                await self.bot.delete_message(self.channel_id, sent.message_id)
            except TelegramError:
                pass
            raise
        old_message_id = self.pinned_message_id
        self.pinned_message_id = int(sent.message_id)
        if old_message_id and old_message_id != sent.message_id:
            try:
                await self._tg_call(
                    self.bot.delete_message, self.channel_id, old_message_id
                )
            except (TelegramError, ChannelDatabaseError) as exc:
                log.warning("Could not delete old channel snapshot: %s", exc)
        return len(data)

    async def flush(self, force: bool = False) -> None:
        if not self.initialized or self._closed:
            return
        async with self._lock:
            if not force and self._dirty <= self._flushed:
                return
            if self.last_upload_at:
                wait = self.last_upload_at + self.flush_interval - time.monotonic()
                if wait > 0:
                    await asyncio.sleep(wait)
            start_dirty = self._dirty
            payload = await asyncio.to_thread(_build_snapshot_sync, self.db_path)
            envelope = self._make_envelope(payload)
            if (
                self.snapshot_checksum is not None
                and envelope["checksum"] == self.snapshot_checksum
            ):
                self._flushed = max(self._flushed, start_dirty)
                _mark_channel_snapshot_flushed(
                    self.db_path,
                    int(envelope["sequence"]),
                    envelope["checksum"],
                    last_attempt_at=datetime.now().isoformat(timespec="seconds"),
                )
                return
            try:
                size = await self._upload_envelope(envelope)
            except Exception as exc:
                self.last_error = str(exc)
                raise
            self.snapshot = envelope
            self.snapshot_checksum = envelope["checksum"]
            self.last_sequence = int(envelope["sequence"])
            self._flushed = max(self._flushed, start_dirty)
            self.last_upload_at = time.monotonic()
            self.upload_count += 1
            self.last_error = None
            _mark_channel_snapshot_flushed(
                self.db_path,
                int(envelope["sequence"]),
                envelope["checksum"],
                uploaded_at=datetime.now().isoformat(timespec="seconds"),
            )
            log.info(
                "Channel database snapshot uploaded: seq=%s rows=%s bytes=%s",
                envelope["sequence"],
                sum(len(t["records"]) for t in envelope["tables"].values()),
                size,
            )

    async def ensure_flushed(self) -> None:
        if not self.active or self._closed:
            return
        if self._dirty <= self._flushed:
            return
        await self.flush()

    async def shutdown(self) -> None:
        if not self.initialized or self._closed:
            return
        try:
            await self.flush(force=True)
        except Exception:
            log.exception("Final channel database flush failed")
            raise
        finally:
            self._closed = True
            self.active = False


async def job_channel_db_flush(context: ContextTypes.DEFAULT_TYPE) -> None:
    store = _channel_db
    if store is None or not store.active:
        return
    try:
        await store.flush()
    except Exception:
        log.exception("Periodic channel database flush failed")


def backup_database_once() -> None:
    """Create a one-time, consistent backup of an existing database before
    migrations. Uses sqlite3's backup API (safe with WAL) and never overwrites
    an existing backup file."""
    if not os.path.exists(DB_PATH) or os.path.getsize(DB_PATH) == 0:
        return
    backup_path = DB_PATH + ".bak"
    if os.path.exists(backup_path):
        return
    try:
        import sqlite3

        src = sqlite3.connect(DB_PATH)
        dst = sqlite3.connect(backup_path)
        try:
            src.backup(dst)
        finally:
            dst.close()
            src.close()
        log.info("Database backup created at %s", backup_path)
    except Exception:
        log.exception("Could not create database backup (continuing safely)")


async def _init_db_schema() -> None:
    backup_database_once()
    async with aiosqlite.connect(DB_PATH) as db:
        await db.executescript(
            """
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                username TEXT,
                first_name TEXT,
                join_date TEXT,
                is_banned INTEGER DEFAULT 0,
                referred_by INTEGER,
                last_bonus_time TEXT,
                last_seen TEXT
            );

            CREATE TABLE IF NOT EXISTS files (
                file_pk INTEGER PRIMARY KEY AUTOINCREMENT,
                tg_file_id TEXT NOT NULL,
                tg_file_unique_id TEXT,
                file_kind TEXT NOT NULL,
                file_name TEXT NOT NULL,
                file_size INTEGER DEFAULT 0,
                description TEXT DEFAULT '',
                price INTEGER DEFAULT 0,
                upload_date TEXT,
                downloads_count INTEGER DEFAULT 0,
                uploaded_by INTEGER,
                premium_only INTEGER DEFAULT 0,
                is_deleted INTEGER DEFAULT 0
            );

            CREATE TABLE IF NOT EXISTS wallet (
                user_id INTEGER PRIMARY KEY,
                coins INTEGER DEFAULT 0
            );

            CREATE TABLE IF NOT EXISTS transactions (
                tx_id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                tx_type TEXT,
                amount INTEGER,
                description TEXT,
                timestamp TEXT
            );

            CREATE TABLE IF NOT EXISTS redeems (
                code TEXT PRIMARY KEY,
                coin_reward INTEGER DEFAULT 0,
                premium_days INTEGER DEFAULT 0,
                usage_limit INTEGER DEFAULT 0,
                used_count INTEGER DEFAULT 0,
                expiry_date TEXT,
                status TEXT DEFAULT 'active',
                created_by INTEGER,
                created_at TEXT
            );

            CREATE TABLE IF NOT EXISTS redeem_uses (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                code TEXT,
                user_id INTEGER,
                timestamp TEXT,
                UNIQUE(code, user_id)
            );

            CREATE TABLE IF NOT EXISTS referrals (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                referrer_id INTEGER,
                new_user_id INTEGER UNIQUE,
                date TEXT,
                reward INTEGER
            );

            CREATE TABLE IF NOT EXISTS force_channels (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT UNIQUE,
                chat_id INTEGER,
                title TEXT,
                invite_link TEXT,
                chat_type TEXT,
                added_date TEXT
            );

            CREATE TABLE IF NOT EXISTS admins (
                user_id INTEGER PRIMARY KEY,
                added_date TEXT
            );

            CREATE TABLE IF NOT EXISTS settings (
                key TEXT PRIMARY KEY,
                value TEXT
            );

            -- Local bookkeeping only; never included in channel snapshots.
            CREATE TABLE IF NOT EXISTS channel_db_meta (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS downloads (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                file_pk INTEGER,
                timestamp TEXT
            );

            CREATE TABLE IF NOT EXISTS premium (
                user_id INTEGER PRIMARY KEY,
                expiry_date TEXT,
                is_lifetime INTEGER DEFAULT 0,
                granted_by INTEGER,
                granted_at TEXT
            );

            CREATE TABLE IF NOT EXISTS purchases (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                file_pk INTEGER,
                price INTEGER,
                timestamp TEXT
            );

            CREATE TABLE IF NOT EXISTS tickets (
                ticket_id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                subject TEXT,
                body TEXT,
                status TEXT DEFAULT 'open',
                admin_id INTEGER,
                created_at TEXT,
                closed_at TEXT
            );

            CREATE TABLE IF NOT EXISTS admin_logs (
                log_id INTEGER PRIMARY KEY AUTOINCREMENT,
                actor_id INTEGER,
                action_text TEXT,
                timestamp TEXT
            );

            CREATE TABLE IF NOT EXISTS file_requests (
                request_id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                request_text TEXT,
                status TEXT DEFAULT 'open',
                timestamp TEXT
            );

            -- New Buy catalogue: Bot Source Code and Method products.
            CREATE TABLE IF NOT EXISTS products (
                product_id INTEGER PRIMARY KEY AUTOINCREMENT,
                category TEXT NOT NULL,
                name TEXT NOT NULL,
                description TEXT DEFAULT '',
                price INTEGER NOT NULL DEFAULT 0,
                preview_file_id TEXT,
                preview_file_unique_id TEXT,
                attachment_file_id TEXT,
                attachment_file_unique_id TEXT,
                attachment_kind TEXT,
                attachment_name TEXT,
                attachment_size INTEGER DEFAULT 0,
                storage_chat_id INTEGER,
                storage_message_id INTEGER,
                is_active INTEGER DEFAULT 1,
                is_deleted INTEGER DEFAULT 0,
                created_at TEXT,
                updated_at TEXT
            );

            CREATE TABLE IF NOT EXISTS product_purchases (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                product_id INTEGER NOT NULL,
                product_name TEXT,
                category TEXT,
                price INTEGER,
                delivery_status TEXT DEFAULT 'pending',
                delivered_at TEXT,
                delivery_error TEXT,
                timestamp TEXT,
                UNIQUE(user_id, product_id)
            );

            CREATE INDEX IF NOT EXISTS idx_files_deleted ON files(is_deleted);
            CREATE INDEX IF NOT EXISTS idx_tx_user ON transactions(user_id);
            CREATE INDEX IF NOT EXISTS idx_purchases_user_file ON purchases(user_id, file_pk);
            CREATE INDEX IF NOT EXISTS idx_downloads_user ON downloads(user_id);
            CREATE INDEX IF NOT EXISTS idx_products_cat ON products(category, is_deleted, is_active);
            CREATE INDEX IF NOT EXISTS idx_pp_user ON product_purchases(user_id);
            CREATE INDEX IF NOT EXISTS idx_pp_product ON product_purchases(product_id);
            """
        )
        await db.commit()

        migrations = [
            ("files", "premium_only", "INTEGER DEFAULT 0"),
            ("redeems", "source", "TEXT DEFAULT 'admin'"),
            ("admins", "role", "TEXT DEFAULT 'junior'"),
            ("users", "login_streak", "INTEGER DEFAULT 0"),
            ("users", "last_login_date", "TEXT"),
            ("users", "referral_milestone_reached", "INTEGER DEFAULT 0"),
            ("force_channels", "chat_type", "TEXT"),
            ("force_channels", "invite_link", "TEXT"),
            ("users", "spin_count_today", "INTEGER DEFAULT 0"),
            ("users", "spin_reset_date", "TEXT"),
            ("files", "mystery_tier", "TEXT"),
            ("files", "featured", "INTEGER DEFAULT 0"),
            ("products", "storage_chat_id", "INTEGER"),
            ("products", "storage_message_id", "INTEGER"),
        ]
        for table, column, coltype in migrations:
            try:
                await db.execute(f"ALTER TABLE {table} ADD COLUMN {column} {coltype}")
                await db.commit()
                log.info("Migrated: added %s.%s", table, column)
            except aiosqlite.OperationalError:
                pass

        for k, v in DEFAULT_SETTINGS.items():
            await db.execute(
                "INSERT OR IGNORE INTO settings (key, value) VALUES (?, ?)", (k, v)
            )
        await db.execute(
            "INSERT OR IGNORE INTO admins (user_id, added_date) VALUES (?, ?)",
            (OWNER_ID, datetime.utcnow().isoformat()),
        )
        await db.commit()
    log.info("Database ready at %s", DB_PATH)


async def _apply_admin_overrides() -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT OR IGNORE INTO admins (user_id, added_date) VALUES (?, ?)",
            (OWNER_ID, datetime.utcnow().isoformat()),
        )
        for admin_id in REMOVE_ADMIN_IDS:
            if admin_id != OWNER_ID:
                await db.execute("DELETE FROM admins WHERE user_id=?", (admin_id,))
        await db.commit()


async def init_db(bot=None, require_channel: bool | None = None) -> None:
    """Prepare the local database and, when a bot is supplied, synchronize it
    with the configured Telegram database channel."""
    global _channel_db
    if require_channel is None:
        require_channel = bot is not None
    store = None
    if bot is not None and (DATABASE_CHANNEL_ID or require_channel):
        store = ChannelDatabase(
            bot, DATABASE_CHANNEL_ID, DB_PATH, CHANNEL_DB_FLUSH_INTERVAL
        )
        try:
            await store.initialize()
        except Exception as exc:
            if require_channel:
                if isinstance(exc, ChannelDatabaseError):
                    raise
                raise ChannelDatabaseError(
                    f"Channel database initialization failed: {exc}"
                ) from exc
            log.warning(
                "Channel database unavailable; continuing with local database: %s", exc
            )
            store = None

    await _init_db_schema()

    if store is None:
        await _apply_admin_overrides()
        return

    if store.snapshot is not None:
        meta = _read_channel_meta_sync(DB_PATH)
        try:
            local_write = int(meta.get("write_seq", "0"))
            local_flushed = int(meta.get("flushed_seq", "0"))
        except (TypeError, ValueError):
            local_write = 0
            local_flushed = 0
        if local_write <= local_flushed:
            try:
                await asyncio.to_thread(
                    _restore_snapshot_sync, DB_PATH, store.snapshot
                )
                log.info(
                    "Restored local database from channel snapshot seq=%s",
                    store.last_sequence,
                )
            except ChannelDatabaseError:
                raise
            except Exception as exc:
                raise ChannelDatabaseError(
                    f"Could not restore database from channel snapshot: {exc}"
                ) from exc
        else:
            log.warning(
                "Local database has unflushed writes (write_seq=%s, flushed_seq=%s); "
                "keeping local state and uploading it instead of restoring the channel.",
                local_write,
                local_flushed,
            )

    await _apply_admin_overrides()
    store.activate()
    store.mark_dirty()
    _channel_db = store
    try:
        await store.flush(force=True)
    except Exception as exc:
        _channel_db = None
        store.active = False
        raise ChannelDatabaseError(
            f"Could not upload the initial channel database snapshot: {exc}"
        ) from exc
    log.info(
        "Channel database active: channel=%s (%s), seq=%s",
        store.channel_id,
        store.channel_title,
        store.last_sequence,
    )


async def get_setting(key: str, default: str = "") -> str:
    async with db_conn() as db:
        cur = await db.execute("SELECT value FROM settings WHERE key=?", (key,))
        row = await cur.fetchone()
        return row[0] if row else default


async def set_setting(key: str, value: str) -> None:
    async with db_conn() as db:
        await db.execute(
            "INSERT INTO settings (key, value) VALUES (?, ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (key, value),
        )
        await db.commit()



async def ensure_user(user_id: int, username: str | None, first_name: str | None,
                       referred_by: int | None = None) -> bool:
    """Returns True if this is a newly created user."""
    async with db_conn() as db:
        cur = await db.execute("SELECT user_id FROM users WHERE user_id=?", (user_id,))
        exists = await cur.fetchone()
        now = datetime.utcnow().isoformat()
        if exists:
            await db.execute(
                "UPDATE users SET username=?, first_name=?, last_seen=? WHERE user_id=?",
                (username, first_name, now, user_id),
            )
            await db.commit()
            return False
        await db.execute(
            "INSERT INTO users (user_id, username, first_name, join_date, referred_by, last_seen) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (user_id, username, first_name, now, referred_by, now),
        )
        await db.execute(
            "INSERT OR IGNORE INTO wallet (user_id, coins) VALUES (?, 0)", (user_id,)
        )
        await db.commit()
        return True


async def is_admin(user_id: int) -> bool:
    if user_id == OWNER_ID:
        return True
    async with db_conn() as db:
        cur = await db.execute("SELECT 1 FROM admins WHERE user_id=?", (user_id,))
        return (await cur.fetchone()) is not None


async def is_banned(user_id: int) -> bool:
    async with db_conn() as db:
        cur = await db.execute("SELECT is_banned FROM users WHERE user_id=?", (user_id,))
        row = await cur.fetchone()
        return bool(row and row[0])


async def get_user_row(user_id: int):
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM users WHERE user_id=?", (user_id,))
        return await cur.fetchone()



async def get_balance(user_id: int) -> int:
    async with db_conn() as db:
        cur = await db.execute("SELECT coins FROM wallet WHERE user_id=?", (user_id,))
        row = await cur.fetchone()
        if row is None:
            await db.execute("INSERT OR IGNORE INTO wallet (user_id, coins) VALUES (?, 0)", (user_id,))
            await db.commit()
            return 0
        return row[0]


async def add_coins(user_id: int, amount: int, tx_type: str, description: str = "") -> int:
    async with _db_lock:
        async with db_conn() as db:
            await db.execute(
                "INSERT INTO wallet (user_id, coins) VALUES (?, 0) "
                "ON CONFLICT(user_id) DO NOTHING", (user_id,)
            )
            await db.execute(
                "UPDATE wallet SET coins = coins + ? WHERE user_id=?", (amount, user_id)
            )
            await db.execute(
                "INSERT INTO transactions (user_id, tx_type, amount, description, timestamp) "
                "VALUES (?, ?, ?, ?, ?)",
                (user_id, tx_type, amount, description, datetime.utcnow().isoformat()),
            )
            await db.commit()
            cur = await db.execute("SELECT coins FROM wallet WHERE user_id=?", (user_id,))
            row = await cur.fetchone()
            return row[0]


async def remove_coins(user_id: int, amount: int, tx_type: str, description: str = "") -> bool:
    """Returns False if insufficient balance."""
    async with _db_lock:
        async with db_conn() as db:
            cur = await db.execute("SELECT coins FROM wallet WHERE user_id=?", (user_id,))
            row = await cur.fetchone()
            bal = row[0] if row else 0
            if bal < amount:
                return False
            await db.execute(
                "UPDATE wallet SET coins = coins - ? WHERE user_id=?", (amount, user_id)
            )
            await db.execute(
                "INSERT INTO transactions (user_id, tx_type, amount, description, timestamp) "
                "VALUES (?, ?, ?, ?, ?)",
                (user_id, tx_type, -amount, description, datetime.utcnow().isoformat()),
            )
            await db.commit()
            return True



async def get_premium(user_id: int):
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM premium WHERE user_id=?", (user_id,))
        return await cur.fetchone()


async def is_premium_active(user_id: int) -> bool:
    row = await get_premium(user_id)
    if not row:
        return False
    if row["is_lifetime"]:
        return True
    if row["expiry_date"] and datetime.fromisoformat(row["expiry_date"]) > datetime.utcnow():
        return True
    return False


async def grant_premium(user_id: int, days: int | None, admin_id: int) -> None:
    async with db_conn() as db:
        if days is None:
            await db.execute(
                "INSERT INTO premium (user_id, expiry_date, is_lifetime, granted_by, granted_at) "
                "VALUES (?, NULL, 1, ?, ?) ON CONFLICT(user_id) DO UPDATE SET "
                "expiry_date=NULL, is_lifetime=1, granted_by=excluded.granted_by, granted_at=excluded.granted_at",
                (user_id, admin_id, datetime.utcnow().isoformat()),
            )
        else:
            expiry = (datetime.utcnow() + timedelta(days=days)).isoformat()
            await db.execute(
                "INSERT INTO premium (user_id, expiry_date, is_lifetime, granted_by, granted_at) "
                "VALUES (?, ?, 0, ?, ?) ON CONFLICT(user_id) DO UPDATE SET "
                "expiry_date=excluded.expiry_date, is_lifetime=0, granted_by=excluded.granted_by, granted_at=excluded.granted_at",
                (user_id, expiry, admin_id, datetime.utcnow().isoformat()),
            )
        await db.commit()


async def remove_premium(user_id: int) -> None:
    async with db_conn() as db:
        await db.execute("DELETE FROM premium WHERE user_id=?", (user_id,))
        await db.commit()



def user_reply_keyboard(admin: bool) -> ReplyKeyboardMarkup:
    rows = [
        [KeyboardButton("Buy", style="success")],
        [KeyboardButton("My Wallet", style="primary"), KeyboardButton("Invite Friend", style="primary")],
        [KeyboardButton("Leaderboard", style="primary"), KeyboardButton("Referral Code", style="primary")],
        [KeyboardButton("My Stats", style="primary"), KeyboardButton("Support", style="primary")],
    ]
    if admin:
        rows.append([KeyboardButton("👑 Admin Panel", style="primary")])
    return ReplyKeyboardMarkup(rows, resize_keyboard=True)


def admin_reply_keyboard(is_owner: bool = True) -> ReplyKeyboardMarkup:
    """Full admin control keyboard — replaces the user keyboard entirely while
    the admin is inside the Admin Panel. Senior/Junior admins get a reduced
    set — Force Channels and Settings are Owner-only sections. Requires
    python-telegram-bot >= 22.7 (Bot API 9.4+) for `style` to render as
    colored buttons in Telegram; see requirements.txt."""
    admin_mgr_label = "🛡 Admin Manager" if is_owner else "📋 Admin List"
    buttons = [
        "📤 Upload File", "📂 Manage Files",
        "🛒 Product Manager", "💹 Economy Manager",
        "🚀 Referral Manager", "💰 Wallet Manager",
        "🎟 Redeem Manager",
    ]
    if is_owner:
        buttons += ["📡 Force Channels"]
    buttons += ["📢 Broadcast", "👥 User Manager", "👤 All Users", "👑 Premium Manager", "📊 Statistics", "🛠 Maintenance"]
    if is_owner:
        buttons += ["⚙ Settings"]
    buttons += [admin_mgr_label]

    rows = [
        [KeyboardButton(buttons[i], style="primary")] + (
            [KeyboardButton(buttons[i + 1], style="primary")] if i + 1 < len(buttons) else []
        )
        for i in range(0, len(buttons), 2)
    ]
    rows.append([KeyboardButton("⬅️ Back to Main", style="primary")])
    return ReplyKeyboardMarkup(rows, resize_keyboard=True)


def admin_panel_keyboard() -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton("📤 Upload File", callback_data="ad:upload", style="primary"),
         InlineKeyboardButton("📂 Manage Files", callback_data="ad:managefiles", style="primary")],
        [InlineKeyboardButton("🛒 Product Manager", callback_data="ad:products", style="primary"),
         InlineKeyboardButton("💹 Economy Manager", callback_data="ad:economy", style="primary")],
        [InlineKeyboardButton("🚀 Referral Manager", callback_data="ad:referrals", style="primary"),
         InlineKeyboardButton("💰 Wallet Manager", callback_data="ad:walletmgr", style="primary")],
        [InlineKeyboardButton("🎟 Redeem Manager", callback_data="ad:redeemmgr", style="primary"),
         InlineKeyboardButton("📡 Force Channels", callback_data="ad:fcmgr", style="primary")],
        [InlineKeyboardButton("📢 Broadcast", callback_data="ad:broadcast", style="primary"),
         InlineKeyboardButton("👥 User Manager", callback_data="ad:usermgr", style="primary")],
        [InlineKeyboardButton("👑 Premium Manager", callback_data="ad:premiummgr", style="primary"),
         InlineKeyboardButton("📊 Statistics", callback_data="ad:stats", style="primary")],
        [InlineKeyboardButton("🛠 Maintenance", callback_data="ad:maintenance", style="primary"),
         InlineKeyboardButton("⚙ Settings", callback_data="ad:settings", style="primary")],
        [InlineKeyboardButton("🛡 Admin Manager", callback_data="ad:adminmgr", style="primary")],
    ]
    return InlineKeyboardMarkup(rows)


def back_button(cb: str = "ad:home") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("⬅ Back", callback_data=cb, style="primary")]])



async def list_force_channels():
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM force_channels ORDER BY id")
        return await cur.fetchall()


async def check_force_join(bot, user_id: int) -> list[dict]:
    """Returns list of channels the user has NOT joined."""
    if (await get_setting("force_join", "1")) != "1":
        return []
    channels = await list_force_channels()
    missing = []
    for ch in channels:
        try:
            member = await bot.get_chat_member(chat_id=ch["chat_id"], user_id=user_id)
            if member.status in ("left", "kicked"):
                missing.append(dict(ch))
        except TelegramError:
            missing.append(dict(ch))
    return missing


async def send_force_join_prompt(update: Update, missing: list[dict]) -> None:
    buttons = []
    for ch in missing:
        if ch.get("username"):
            url = f"https://t.me/{ch['username'].lstrip('@')}"
        elif ch.get("invite_link"):
            url = ch["invite_link"]
        else:
            continue
        buttons.append([InlineKeyboardButton(f"📢 {ch['title']}", url=url, style="primary")])
    buttons.append([InlineKeyboardButton("✅ Verify", callback_data="verify_join", style="primary")])
    text = (
        "🔒 <b>Access Restricted</b>\n\n"
        "To use this bot, please join all required channels below, "
        "then tap <b>✅ Verify</b>."
    )
    if update.callback_query:
        await update.callback_query.message.reply_text(
            text, reply_markup=InlineKeyboardMarkup(buttons), parse_mode=ParseMode.HTML
        )
    else:
        await update.effective_message.reply_text(
            text, reply_markup=InlineKeyboardMarkup(buttons), parse_mode=ParseMode.HTML
        )



(UP_FILE, UP_NAME, UP_DESC, UP_PRICE, UP_PREVIEW) = range(5)
(RD_CODE,) = range(20, 21)
(FC_ADD,) = range(30, 31)
(UM_SEARCH, UM_AMOUNT) = range(40, 42)
(RM_CODE, RM_COINS, RM_PREMIUM, RM_LIMIT, RM_EXPIRY, RM_DELETE) = range(50, 56)
(BR_CONTENT,) = range(60, 61)
(ST_VALUE,) = range(70, 71)
(EF_FIELD,) = range(80, 81)
(WB_IDS, WB_ACTION, WB_AMOUNT, WB_PREMIUM) = range(90, 94)
(GC_AMOUNT,) = range(96, 97)
(AM_ADD_USER, AM_ADD_ROLE) = range(97, 99)
(TK_SUBJECT, TK_BODY, TK_REPLY, TK_USER_REPLY) = range(99, 103)
(FR_TEXT,) = range(103, 104)
(MF_SEARCH,) = range(104, 105)
(PR_NAME, PR_DESC, PR_PRICE, PR_PREVIEW, PR_FILE, PR_STATUS, PR_CONFIRM) = range(110, 117)
(PE_VALUE, PE_PREVIEW, PE_FILE) = range(117, 120)
(ECO_REWARD,) = range(125, 126)
(STC_CHANNEL,) = range(126, 127)

ADMIN_ONLY_MSG = "🚫 This action is for admins only."
OWNER_ONLY_MSG = "🚫 This is restricted to the Owner only. Senior/Junior admins don't have access to this section."
ADMIN_MAX_REDEEM_COINS = 300
ADMIN_MIN_REDEEM_COINS = 20
ADMIN_DAILY_REDEEM_LIMIT = 2


async def require_owner(update: Update) -> bool:
    """Gate for Owner-only sections (Settings, Force Channels,
    Bulk User Manage, Manage Files list). Senior and Junior admins are both
    blocked — only OWNER_ID passes. Sends a denial message/alert and returns
    False if the caller isn't the owner."""
    if update.effective_user.id == OWNER_ID:
        return True
    if update.callback_query:
        await update.callback_query.answer(OWNER_ONLY_MSG, show_alert=True)
    else:
        await update.effective_message.reply_text(OWNER_ONLY_MSG)
    return False


def fmt_size(num: int) -> str:
    step = 1024.0
    for unit in ["B", "KB", "MB", "GB", "TB"]:
        if num < step:
            return f"{num:.1f} {unit}" if unit != "B" else f"{int(num)} {unit}"
        num /= step
    return f"{num:.1f} PB"


def fmt_date(iso: str | None) -> str:
    if not iso:
        return "—"
    try:
        return datetime.fromisoformat(iso).strftime("%d %b %Y, %H:%M")
    except Exception:
        return iso



async def _update_login_streak(bot, user_id: int) -> None:
    """Increments a user's consecutive-day login streak (resets if a day was
    missed), and grants a one-time bonus whenever a configured streak
    milestone is newly reached. Cheap no-op on repeat calls within the same
    day since guard_user runs on every interaction."""
    today = datetime.utcnow().strftime("%Y-%m-%d")
    async with db_conn() as db:
        cur = await db.execute("SELECT login_streak, last_login_date FROM users WHERE user_id=?", (user_id,))
        row = await cur.fetchone()
        if not row:
            return
        streak, last_date = row[0] or 0, row[1]
        if last_date == today:
            return

        yesterday = (datetime.utcnow() - timedelta(days=1)).strftime("%Y-%m-%d")
        new_streak = streak + 1 if last_date == yesterday else 1
        await db.execute(
            "UPDATE users SET login_streak=?, last_login_date=? WHERE user_id=?", (new_streak, today, user_id)
        )
        await db.commit()

    rewards = json.loads(await get_setting("streak_rewards", "[]"))
    for r in rewards:
        if r["days"] == new_streak:
            await add_coins(user_id, r["reward"], "login_streak", f"{new_streak}-day login streak bonus")
            try:
                await bot.send_message(
                    user_id,
                    f"🔥 <b>{new_streak}-Day Login Streak!</b>\n\n🪙 Bonus: <b>+{r['reward']} Coins</b>\n\nKeep it going!",
                    parse_mode=ParseMode.HTML,
                )
            except TelegramError:
                pass
            break


async def guard_user(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    """Returns True if the update should proceed normally."""
    user = update.effective_user
    if user is None:
        return False

    await ensure_user(user.id, user.username, user.first_name)
    await _update_login_streak(context.bot, user.id)

    admin = await is_admin(user.id)

    maintenance = (await get_setting("maintenance", "0")) == "1"
    if maintenance and not admin:
        await update.effective_message.reply_text(
            "🚧 <b>Bot is under maintenance.</b>\nPlease try again later.",
            parse_mode=ParseMode.HTML,
        )
        return False

    if await is_banned(user.id):
        await update.effective_message.reply_text(
            "🚫 You have been banned from using this bot. Contact support if you think this is a mistake."
        )
        return False

    if not admin:
        missing = await check_force_join(context.bot, user.id)
        if missing:
            await send_force_join_prompt(update, missing)
            return False

    return True



async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    args = context.args

    maintenance = (await get_setting("maintenance", "0")) == "1"
    admin = await is_admin(user.id)
    if maintenance and not admin:
        await update.effective_message.reply_text(
            "🚧 <b>Bot is under maintenance.</b>\nPlease try again later.",
            parse_mode=ParseMode.HTML,
        )
        return

    if await is_banned(user.id):
        await update.effective_message.reply_text("🚫 You have been banned from using this bot.")
        return

    referred_by = None
    if args and args[0].isdigit():
        ref_id = int(args[0])
        if ref_id != user.id:
            existing = await get_user_row(user.id)
            if existing is None:
                referred_by = ref_id

    is_new = await ensure_user(user.id, user.username, user.first_name, referred_by)

    if not admin:
        missing = await check_force_join(context.bot, user.id)
        if missing:
            await send_force_join_prompt(update, missing)
            return

    await maybe_process_referral(context.bot, user.id)

    await show_main_menu(update, context)


async def maybe_process_referral(bot, user_id: int) -> None:
    """Grants the referral reward once the referred user actually reaches the
    bot (i.e. after passing force-join, or immediately if none is required).
    Safe to call repeatedly — process_referral() is idempotent."""
    row = await get_user_row(user_id)
    if row and row["referred_by"]:
        await process_referral(bot, row["referred_by"], user_id)


async def process_referral(bot, referrer_id: int, new_user_id: int) -> None:
    if referrer_id == new_user_id:
        return
    if (await get_setting("referral_reward_enabled", "1")) != "1":
        return
    try:
        reward = int(float(await get_setting("referral_reward", "1")))
    except (TypeError, ValueError):
        reward = 1
    if reward < 0:
        reward = 0
    async with db_conn() as db:
        cur = await db.execute("SELECT 1 FROM users WHERE user_id=?", (referrer_id,))
        if not await cur.fetchone():
            return
        cur = await db.execute("SELECT 1 FROM referrals WHERE new_user_id=?", (new_user_id,))
        if await cur.fetchone():
            return
        try:
            await db.execute(
                "INSERT INTO referrals (referrer_id, new_user_id, date, reward) VALUES (?, ?, ?, ?)",
                (referrer_id, new_user_id, datetime.utcnow().isoformat(), reward),
            )
            await db.commit()
        except aiosqlite.IntegrityError:
            await db.rollback()
            return

    new_balance = await add_coins(referrer_id, reward, "referral", f"Referral bonus for inviting user {new_user_id}")

    new_user_row = await get_user_row(new_user_id)
    if new_user_row and new_user_row["username"]:
        uname = f"@{new_user_row['username']}"
    elif new_user_row and new_user_row["first_name"]:
        uname = new_user_row["first_name"]
    else:
        uname = f"User {new_user_id}"

    try:
        await bot.send_message(
            referrer_id,
            "🎉 <b>New Referral Alert!</b> 🎉\n\n"
            f"👤 <b>User:</b> {html.escape(uname)}\n"
            f"🪙 <b>You earned:</b> +{reward} coins\n"
            f"💰 <b>Your new balance:</b> {new_balance} coins",
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        pass

    await _check_referral_milestone(bot, referrer_id)


async def _check_referral_milestone(bot, referrer_id: int) -> None:
    """Grants a one-time bonus the first time a referrer's total count crosses
    a configured milestone (e.g. 5, 10, 25, 50 referrals)."""
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (referrer_id,))
        total = (await cur.fetchone())[0]
        cur = await db.execute("SELECT referral_milestone_reached FROM users WHERE user_id=?", (referrer_id,))
        row = await cur.fetchone()
        already_reached = row[0] if row and row[0] else 0

    milestones = json.loads(await get_setting("referral_milestones", "[]"))
    for m in sorted(milestones, key=lambda x: x["count"]):
        if total >= m["count"] > already_reached:
            await add_coins(referrer_id, m["reward"], "referral_milestone", f"Referral milestone: {m['count']} referrals")
            async with db_conn() as db:
                await db.execute("UPDATE users SET referral_milestone_reached=? WHERE user_id=?", (m["count"], referrer_id))
                await db.commit()
            try:
                await bot.send_message(
                    referrer_id,
                    f"🏆 <b>Referral Milestone Reached!</b>\n\n"
                    f"🚀 You've referred <b>{m['count']}</b> people!\n"
                    f"🪙 Bonus: <b>+{m['reward']} Coins</b>",
                    parse_mode=ParseMode.HTML,
                )
            except TelegramError:
                pass
            break


async def show_main_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    admin = await is_admin(user.id)
    bot_name = await get_setting("bot_name", "𝐙𝚇 𝐒ᴛᴏʀᴇ")
    balance = await get_balance(user.id)

    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (user.id,))
        ref_count = (await cur.fetchone())[0]

    is_premium = await is_premium_active(user.id)
    premium_line = "👑 <b>Premium — Active</b>" if is_premium else "⭐ Premium: <i>Not Active</i>"
    name_tag = f"👑 {html.escape(user.first_name or 'Friend')}" if is_premium else html.escape(user.first_name or "Friend")

    text = (
        f"🫴🏻 <b>Welcome , {name_tag}!</b>\n\n"
        f"🏷 <b>{html.escape(bot_name)}</b>\n"
        f"{DIVIDER}\n"
        f"🪙 <b>Wallet:</b> {balance} Coins\n"
        f"💱 <b>1 Coin = ₹1</b>\n"
        f"💬 <b>Buy coins:</b> @duifioookn2\n"
        f"👥 <b>Referrals:</b> {ref_count}\n"
        f"{premium_line}\n"
        f"{DIVIDER}\n\n"
        f"Keyboard Button Ka Use Karo 👇"
    )
    await update.effective_message.reply_text(
        text, parse_mode=ParseMode.HTML, reply_markup=user_reply_keyboard(admin)
    )


async def cb_verify_join(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    user = update.effective_user
    missing = await check_force_join(context.bot, user.id)
    if missing:
        await query.answer("❌ You haven't joined all channels yet.", show_alert=True)
        return
    await query.answer("✅ Verified!")
    try:
        await query.message.delete()
    except BadRequest:
        pass
    await ensure_user(user.id, user.username, user.first_name)
    await maybe_process_referral(context.bot, user.id)
    await show_main_menu(update, context)



async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    text = (
        "📖 <b>Help & Guide</b>\n\n"
        "🛒 <b>Buy</b> — Browse Bot Source Code and Method products.\n"
        "🪙 <b>Coins</b> — 1 Coin = ₹1. Buy coins by DMing @duifioookn2, "
        "or earn them via Referrals and Redeem Codes.\n"
        "👥 <b>Referral</b> — Share your personal link, earn coins per new user.\n"
        "🎟️ <b>Redeem</b> — Enter a code from the admin to instantly get coins.\n"
        "💬 <b>Support</b> — Reach out any time via the Support menu.\n"
    )
    await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)


async def handle_support(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    support_username = await get_setting("support_username", "duifioookn2")
    text = (
        "💬 <b>Support</b>\n\n"
        f"👤 Contact: @{html.escape(support_username)}\n"
        "🕒 Business Hours: 10:00 AM – 10:00 PM (IST)\n\n"
        "We usually reply within a few hours."
    )
    await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)



async def handle_support_ticket_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await guard_user(update, context):
        return ConversationHandler.END
    await update.effective_message.reply_text(
        "🎫 <b>Open a Support Ticket</b>\n\nWhat's the subject? (short, one line):",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="ticket:cancel", style="primary")]]),
    )
    return TK_SUBJECT


async def cb_ticket_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    await update.callback_query.answer()
    await update.callback_query.message.reply_text("❌ Cancelled.")
    context.user_data.pop("tk_subject", None)
    return ConversationHandler.END


async def conv_ticket_subject(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    subject = update.message.text.strip()
    if len(subject) > 100:
        await update.message.reply_text("❌ Please keep the subject under 100 characters.")
        return TK_SUBJECT
    context.user_data["tk_subject"] = subject
    await update.message.reply_text("📝 Now describe your issue in detail:")
    return TK_BODY


async def conv_ticket_body(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    body = update.message.text.strip()
    subject = context.user_data.pop("tk_subject", "")
    user = update.effective_user

    async with db_conn() as db:
        await db.execute(
            "INSERT INTO tickets (user_id, subject, body, status, created_at) VALUES (?, ?, ?, 'open', ?)",
            (user.id, subject, body, datetime.utcnow().isoformat()),
        )
        await db.commit()
        cur = await db.execute("SELECT last_insert_rowid()")
        ticket_id = (await cur.fetchone())[0]

    await update.message.reply_text(
        f"✅ <b>Ticket #{ticket_id} Submitted!</b>\n\nOur team will get back to you soon.",
        parse_mode=ParseMode.HTML,
    )

    uname = f"@{user.username}" if user.username else "—"
    notify = (
        f"🎫 <b>New Support Ticket #{ticket_id}</b>\n\n"
        f"👤 From: {html.escape(uname)}\n🆔 User ID: <code>{user.id}</code>\n"
        f"📌 Subject: {html.escape(subject)}\n\n📝 {html.escape(body)}"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("💬 Reply", callback_data=f"ticket:reply:{ticket_id}", style="primary"),
         InlineKeyboardButton("✅ Close", callback_data=f"ticket:close:{ticket_id}", style="primary")],
    ])
    for admin_id in await get_all_admin_ids():
        try:
            await context.bot.send_message(admin_id, notify, parse_mode=ParseMode.HTML, reply_markup=kb)
        except TelegramError:
            pass
    return ConversationHandler.END


async def cb_ticket_reply_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    if not await is_admin(update.effective_user.id):
        await query.answer(ADMIN_ONLY_MSG, show_alert=True)
        return ConversationHandler.END
    await query.answer()
    ticket_id = int(query.data.split(":")[2])
    context.user_data["tk_reply_id"] = ticket_id
    await query.message.reply_text("💬 Type your reply — it will be sent to the user:")
    return TK_REPLY


async def conv_ticket_reply(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    ticket_id = context.user_data.pop("tk_reply_id", None)
    if ticket_id is None:
        await update.message.reply_text("❌ Something went wrong — please try again.")
        return ConversationHandler.END
    reply_text = update.message.text.strip()

    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM tickets WHERE ticket_id=?", (ticket_id,))
        ticket = await cur.fetchone()

    if not ticket:
        await update.message.reply_text("❌ Ticket not found.")
        return ConversationHandler.END
    if ticket["status"] != "open":
        await update.message.reply_text("🚫 This ticket is already closed.")
        return ConversationHandler.END

    user_kb = InlineKeyboardMarkup([[InlineKeyboardButton("💬 Reply", callback_data=f"ticket:ureply:{ticket_id}", style="primary")]])
    try:
        await context.bot.send_message(
            ticket["user_id"],
            f"🎫 <b>Support Reply (Ticket #{ticket_id})</b>\n\n{html.escape(reply_text)}",
            parse_mode=ParseMode.HTML,
            reply_markup=user_kb,
        )
        await update.message.reply_text("✅ Reply sent to the user.")
    except TelegramError:
        await update.message.reply_text("⚠️ Couldn't deliver the reply — the user may have blocked the bot.")

    await log_admin_action(context.bot, update.effective_user.id, f"💬 Replied to ticket #{ticket_id}")
    return ConversationHandler.END


async def cb_ticket_user_reply_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    ticket_id = int(query.data.split(":")[2])
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM tickets WHERE ticket_id=?", (ticket_id,))
        ticket = await cur.fetchone()

    if not ticket:
        await query.answer("❌ Ticket not found.", show_alert=True)
        return ConversationHandler.END
    if ticket["user_id"] != update.effective_user.id:
        await query.answer("🚫 This isn't your ticket.", show_alert=True)
        return ConversationHandler.END
    if ticket["status"] != "open":
        await query.answer("🚫 This ticket is already closed.", show_alert=True)
        return ConversationHandler.END

    await query.answer()
    context.user_data["tk_user_reply_id"] = ticket_id
    await query.message.reply_text(
        "💬 Type your reply:",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="ticket:cancel", style="primary")]]),
    )
    return TK_USER_REPLY


async def conv_ticket_user_reply(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    ticket_id = context.user_data.pop("tk_user_reply_id", None)
    if ticket_id is None:
        await update.message.reply_text("❌ Something went wrong — please try again.")
        return ConversationHandler.END
    reply_text = update.message.text.strip()
    user = update.effective_user

    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM tickets WHERE ticket_id=?", (ticket_id,))
        ticket = await cur.fetchone()

    if not ticket:
        await update.message.reply_text("❌ Ticket not found.")
        return ConversationHandler.END
    if ticket["status"] != "open":
        await update.message.reply_text("🚫 This ticket is already closed.")
        return ConversationHandler.END

    await update.message.reply_text("✅ Reply sent to support.")

    uname = f"@{user.username}" if user.username else "—"
    notify = (
        f"🎫 <b>Ticket #{ticket_id} — User Reply</b>\n\n"
        f"👤 From: {html.escape(uname)}\n🆔 User ID: <code>{user.id}</code>\n\n💬 {html.escape(reply_text)}"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("💬 Reply", callback_data=f"ticket:reply:{ticket_id}", style="primary"),
         InlineKeyboardButton("✅ Close", callback_data=f"ticket:close:{ticket_id}", style="primary")],
    ])
    for admin_id in await get_all_admin_ids():
        try:
            await context.bot.send_message(admin_id, notify, parse_mode=ParseMode.HTML, reply_markup=kb)
        except TelegramError:
            pass
    return ConversationHandler.END


async def cb_ticket_close(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not await is_admin(update.effective_user.id):
        await query.answer(ADMIN_ONLY_MSG, show_alert=True)
        return
    ticket_id = int(query.data.split(":")[2])
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM tickets WHERE ticket_id=?", (ticket_id,))
        ticket = await cur.fetchone()
        if not ticket:
            await query.answer("❌ Not found.", show_alert=True)
            return
        await db.execute(
            "UPDATE tickets SET status='closed', admin_id=?, closed_at=? WHERE ticket_id=?",
            (update.effective_user.id, datetime.utcnow().isoformat(), ticket_id),
        )
        await db.commit()
    await query.answer("✅ Closed")
    try:
        await query.message.delete()
    except TelegramError:
        pass
    try:
        await context.bot.send_message(
            ticket["user_id"], f"✅ <b>Your ticket #{ticket_id} has been closed.</b>", parse_mode=ParseMode.HTML
        )
    except TelegramError:
        pass
    await log_admin_action(context.bot, update.effective_user.id, f"✅ Closed ticket #{ticket_id}")



async def handle_file_request_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await guard_user(update, context):
        return ConversationHandler.END
    await update.effective_message.reply_text(
        "📥 <b>Request a File</b>\n\nTell us what file/project you're looking for — we'll try to add it:",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="freq:cancel", style="primary")]]),
    )
    return FR_TEXT


async def cb_file_request_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    await update.callback_query.answer()
    await update.callback_query.message.reply_text("❌ Cancelled.")
    return ConversationHandler.END


async def conv_file_request_text(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    user = update.effective_user

    async with db_conn() as db:
        await db.execute(
            "INSERT INTO file_requests (user_id, request_text, status, timestamp) VALUES (?, ?, 'open', ?)",
            (user.id, text, datetime.utcnow().isoformat()),
        )
        await db.commit()
        cur = await db.execute("SELECT last_insert_rowid()")
        req_id = (await cur.fetchone())[0]

    await update.message.reply_text("✅ <b>Request Submitted!</b>\n\nThanks — we'll review it soon.", parse_mode=ParseMode.HTML)

    uname = f"@{user.username}" if user.username else "—"
    notify = (
        f"📥 <b>New File Request #{req_id}</b>\n\n"
        f"👤 From: {html.escape(uname)}\n🆔 User ID: <code>{user.id}</code>\n\n📝 {html.escape(text)}"
    )
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("✅ Mark Fulfilled", callback_data=f"freq:done:{req_id}", style="primary")]])
    for admin_id in await get_all_admin_ids():
        try:
            await context.bot.send_message(admin_id, notify, parse_mode=ParseMode.HTML, reply_markup=kb)
        except TelegramError:
            pass
    return ConversationHandler.END


async def cb_file_request_done(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not await is_admin(update.effective_user.id):
        await query.answer(ADMIN_ONLY_MSG, show_alert=True)
        return
    req_id = int(query.data.split(":")[2])
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM file_requests WHERE request_id=?", (req_id,))
        req = await cur.fetchone()
        if not req:
            await query.answer("❌ Not found.", show_alert=True)
            return
        await db.execute("UPDATE file_requests SET status='fulfilled' WHERE request_id=?", (req_id,))
        await db.commit()
    await query.answer("✅ Marked fulfilled")
    try:
        await query.message.delete()
    except TelegramError:
        pass
    try:
        await context.bot.send_message(
            req["user_id"],
            f"✅ <b>Your file request has been fulfilled!</b>\n\n📝 {html.escape(req['request_text'])}\n\nCheck -- Buy Files!",
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        pass
    await log_admin_action(context.bot, update.effective_user.id, f"✅ Fulfilled file request #{req_id}")


async def handle_my_wallet(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    await send_wallet_view(update, context)


async def send_wallet_view(update: Update, context: ContextTypes.DEFAULT_TYPE, edit: bool = False) -> None:
    user = update.effective_user
    balance = await get_balance(user.id)
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (user.id,))
        ref_count = (await cur.fetchone())[0]
    is_premium = await is_premium_active(user.id)
    premium_line = "👑 <b>Premium — Active</b>" if is_premium else "⭐ Premium: <i>Not Active</i>"

    text = (
        "💼 <b>My Wallet</b>\n"
        f"{DIVIDER}\n"
        f"🪙 <b>Coins:</b> {balance}\n"
        f"💱 <b>Rate:</b> 1 Coin = ₹1\n"
        f"👥 <b>Total Referrals:</b> {ref_count}\n"
        f"{premium_line}\n"
        f"{DIVIDER}\n"
        "💬 <b>Buy coins:</b> DM @duifioookn2"
    )
    buttons = [
        [InlineKeyboardButton("💬 Buy Coins via Owner", url="https://t.me/duifioookn2", style="success")],
        [InlineKeyboardButton("📜 Transactions", callback_data="wallet:tx:0", style="primary")],
    ]
    if not is_premium:
        buttons.append([InlineKeyboardButton("👑 Buy Premium with Coins", callback_data="wallet:buypremium", style="primary")])
    kb = InlineKeyboardMarkup(buttons)
    if edit and update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_wallet_buy_premium(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    if await is_premium_active(update.effective_user.id):
        await query.answer("✅ You already have Premium active.", show_alert=True)
        return
    pricing = json.loads(await get_setting("premium_pricing", "[]"))
    balance = await get_balance(update.effective_user.id)
    lines = [f"👑 <b>Buy Premium with Coins</b>\n{DIVIDER}", f"🪙 Your balance: <b>{balance}</b>\n"]
    buttons = []
    for p in pricing:
        label = "Lifetime" if p["days"] == 0 else f"{p['days']} Days"
        lines.append(f"• {label} — 🪙 {p['price']}")
        buttons.append([InlineKeyboardButton(f"👑 {label} — {p['price']} coins", callback_data=f"premium:buy:{p['days']}:{p['price']}", style="primary")])
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="wallet:home", style="primary")])
    await query.edit_message_text("\n".join(lines), parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_premium_purchase(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    user = update.effective_user
    _, _, days, price = query.data.split(":")
    days, price = int(days), int(price)

    lock = await get_user_action_lock(user.id)
    async with lock:
        if await is_premium_active(user.id):
            await query.answer("✅ You already have Premium active.", show_alert=True)
            return
        ok = await remove_coins(user.id, price, "premium_purchase", f"Bought Premium ({'Lifetime' if days == 0 else f'{days} days'})")
        if not ok:
            await query.answer("❌ Not enough Coins for this plan.", show_alert=True)
            return
        await grant_premium(user.id, None if days == 0 else days, admin_id=0)

    await query.answer("👑 Premium activated!")
    label = "Lifetime" if days == 0 else f"{days} Days"
    await query.edit_message_text(
        f"🎉 <b>Premium Activated!</b>\n\n👑 Plan: <b>{label}</b>\n🪙 Paid: <b>{price} coins</b>\n\n"
        "Enjoy your Premium badge, bonus multiplier, and priority support!",
        parse_mode=ParseMode.HTML,
    )


async def cb_wallet_tx(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    user = update.effective_user
    page = int(query.data.split(":")[2])
    per_page = 8
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT * FROM transactions WHERE user_id=? ORDER BY tx_id DESC LIMIT ? OFFSET ?",
            (user.id, per_page, page * per_page),
        )
        rows = await cur.fetchall()

    if not rows and page == 0:
        text = "📜 <b>Transactions</b>\n\nNo transactions yet."
    else:
        lines = ["📜 <b>Transactions</b>\n"]
        for r in rows:
            sign = "+" if r["amount"] >= 0 else ""
            lines.append(
                f"{'🟢' if r['amount']>=0 else '🔴'} {sign}{r['amount']} 🪙 — {html.escape(r['tx_type'])} "
                f"<i>({fmt_date(r['timestamp'])})</i>"
            )
        text = "\n".join(lines)

    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"wallet:tx:{page-1}", style="primary"))
    if len(rows) == per_page:
        nav.append(InlineKeyboardButton("Next ➡", callback_data=f"wallet:tx:{page+1}", style="primary"))
    buttons = [nav] if nav else []
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="wallet:home", style="primary")])
    await query.answer()
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_wallet_home(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.callback_query.answer()
    await send_wallet_view(update, context, edit=True)



async def get_all_admin_ids() -> list[int]:
    ids = {OWNER_ID}
    async with db_conn() as db:
        cur = await db.execute("SELECT user_id FROM admins")
        rows = await cur.fetchall()
        for r in rows:
            ids.add(r[0])
    return list(ids)


async def get_admin_role(user_id: int) -> str | None:
    """Returns 'owner', 'senior', 'junior', or None (not an admin)."""
    if user_id == OWNER_ID:
        return "owner"
    async with db_conn() as db:
        cur = await db.execute("SELECT role FROM admins WHERE user_id=?", (user_id,))
        row = await cur.fetchone()
        return row[0] if row else None


async def log_admin_action(bot, actor_id: int, action_text: str) -> None:
    """Audit trail with a Senior/Junior hierarchy:
    - Junior admin actions -> notify Owner + all Senior admins.
    - Senior admin actions -> notify Owner only.
    - Owner's own actions -> no notification needed.
    Every action (including the Owner's own) is persisted to admin_logs for
    the browsable Action Log Viewer."""
    async with db_conn() as db:
        await db.execute(
            "INSERT INTO admin_logs (actor_id, action_text, timestamp) VALUES (?, ?, ?)",
            (actor_id, action_text, datetime.utcnow().isoformat()),
        )
        await db.commit()

    if actor_id == OWNER_ID:
        return
    role = await get_admin_role(actor_id)
    actor_row = await get_user_row(actor_id)
    actor_label = f"@{actor_row['username']}" if actor_row and actor_row["username"] else str(actor_id)
    role_tag = f" [{role}]" if role else ""
    text = f"📋 <b>Admin Action</b>\n\n👤 By: {html.escape(actor_label)}{role_tag} (<code>{actor_id}</code>)\n{action_text}"

    recipients = {OWNER_ID}
    if role == "junior":
        async with db_conn() as db:
            cur = await db.execute("SELECT user_id FROM admins WHERE role='senior'")
            for r in await cur.fetchall():
                recipients.add(r[0])

    for uid in recipients:
        try:
            await bot.send_message(uid, text, parse_mode=ParseMode.HTML)
        except TelegramError:
            pass


async def handle_invite_friends(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    user = update.effective_user
    reward = await get_setting("referral_reward", "1")
    enabled = (await get_setting("referral_reward_enabled", "1")) == "1"
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (user.id,))
        count = (await cur.fetchone())[0]
        cur = await db.execute(
            "SELECT COALESCE(SUM(reward), 0) FROM referrals WHERE referrer_id=?", (user.id,)
        )
        earned = (await cur.fetchone())[0]
    link = f"https://t.me/{BOT_USERNAME}?start={user.id}"
    status_line = f"Earn <b>{reward} Coins</b> for every friend who joins using your link!" if enabled \
        else "Referral rewards are currently <b>paused</b> by the admin."
    share_url = f"https://t.me/share/url?url={link}&text=Join%20this%20store%20bot"
    text = (
        "🚀 <b>Invite Friends</b>\n\n"
        f"{status_line}\n\n"
        f"🔗 <code>{link}</code>\n\n"
        f"👥 Total Referrals: <b>{count}</b>\n"
        f"🪙 Referral Coins Earned: <b>{earned}</b>"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("📤 Share Link", url=share_url, style="success")],
        [InlineKeyboardButton("👥 My Referrals", callback_data="myrefs:0", style="primary")],
    ])
    await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def handle_referral_code(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    user = update.effective_user
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (user.id,))
        count = (await cur.fetchone())[0]
    link = f"https://t.me/{BOT_USERNAME}?start={user.id}"
    text = (
        "🎟️ <b>Referral Code</b>\n"
        f"{DIVIDER}\n"
        f"👤 <b>Your Referral ID:</b> <code>{user.id}</code>\n"
        f"🔗 <b>Your Invite Link:</b>\n<code>{link}</code>\n\n"
        f"👥 <b>Valid Referrals:</b> {count}\n\n"
        "Share your link with a friend. When they start the bot through it for "
        "the first time, your referral is recorded automatically."
    )
    await update.effective_message.reply_text(
        text, parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("👥 My Referrals", callback_data="myrefs:0", style="primary")],
        ]),
    )


async def cb_my_referrals(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    page = int(query.data.split(":")[1])
    per_page = 10
    user = update.effective_user
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT new_user_id, date, reward FROM referrals WHERE referrer_id=? ORDER BY date DESC LIMIT ? OFFSET ?",
            (user.id, per_page, page * per_page),
        )
        rows = await cur.fetchall()

    if not rows and page == 0:
        text = "👥 <b>My Referrals</b>\n\nYou haven't referred anyone yet."
    else:
        lines = ["👥 <b>My Referrals</b>\n"]
        for r in rows:
            u = await get_user_row(r["new_user_id"])
            label = f"@{u['username']}" if u and u["username"] else (u["first_name"] if u else f"User {r['new_user_id']}")
            lines.append(f"• {html.escape(label or '—')} — 🪙 +{r['reward']} <i>({fmt_date(r['date'])})</i>")
        text = "\n".join(lines)

    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"myrefs:{page-1}", style="primary"))
    if len(rows) == per_page:
        nav.append(InlineKeyboardButton("Next ➡", callback_data=f"myrefs:{page+1}", style="primary"))
    kb = InlineKeyboardMarkup([nav]) if nav else None
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def handle_leaderboard(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    if (await get_setting("leaderboard_enabled", "1")) != "1":
        await update.effective_message.reply_text(
            "🏆 <b>Leaderboard</b>\n\nThe leaderboard is currently disabled.",
            parse_mode=ParseMode.HTML,
        )
        return
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT referrer_id, COUNT(*) as cnt FROM referrals GROUP BY referrer_id "
            "ORDER BY cnt DESC LIMIT 10"
        )
        rows = await cur.fetchall()

    if not rows:
        await update.effective_message.reply_text("🏆 <b>Leaderboard</b>\n\nNo referrals yet.", parse_mode=ParseMode.HTML)
        return

    medals = ["🥇", "🥈", "🥉"]
    lines = ["🏆 <b>Top 10 Referrals</b>\n"]
    for i, r in enumerate(rows):
        u = await get_user_row(r["referrer_id"])
        name = html.escape(u["first_name"] or "Unknown") if u else "Unknown"
        rank = medals[i] if i < 3 else f"{i+1}."
        lines.append(f"{rank} {name} — <b>{r['cnt']}</b> referrals")
    await update.effective_message.reply_text("\n".join(lines), parse_mode=ParseMode.HTML)



async def handle_redeem_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("🔑 Redeem a Code", callback_data="redeem:enter", style="primary")],
        [InlineKeyboardButton("🎁 Convert Coins to Gift Code", callback_data="redeem:gift", style="primary")],
    ])
    await update.effective_message.reply_text(
        "🎟️ <b>Redeem Center</b>\n\nWhat would you like to do?",
        parse_mode=ParseMode.HTML,
        reply_markup=kb,
    )


async def cb_redeem_enter_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.message.reply_text(
        "🎟️ Please enter your redeem code:",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="redeem:cancel", style="primary")]]),
    )
    return RD_CODE


async def cb_redeem_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    await update.callback_query.answer()
    await update.callback_query.message.reply_text("❌ Cancelled.")
    return ConversationHandler.END


async def handle_redeem_code(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    code = update.message.text.strip().upper()
    user = update.effective_user
    lock = await get_user_action_lock(user.id)

    async with lock:
        async with db_conn() as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM redeems WHERE code=?", (code,))
            redeem = await cur.fetchone()

            admin = await is_admin(user.id)
            if not redeem:
                await update.message.reply_text("❌ Invalid Redeem Code.", reply_markup=user_reply_keyboard(admin))
                return ConversationHandler.END

            if redeem["status"] != "active":
                await update.message.reply_text("❌ This code is no longer active.", reply_markup=user_reply_keyboard(admin))
                return ConversationHandler.END

            if redeem["expiry_date"]:
                try:
                    if datetime.fromisoformat(redeem["expiry_date"]) < datetime.utcnow():
                        await db.execute("UPDATE redeems SET status='expired' WHERE code=?", (code,))
                        await db.commit()
                        await update.message.reply_text("❌ This code has expired.", reply_markup=user_reply_keyboard(admin))
                        return ConversationHandler.END
                except ValueError:
                    pass

            if redeem["usage_limit"] and redeem["used_count"] >= redeem["usage_limit"]:
                await update.message.reply_text("❌ This code has reached its usage limit.", reply_markup=user_reply_keyboard(admin))
                return ConversationHandler.END

            cur = await db.execute(
                "SELECT 1 FROM redeem_uses WHERE code=? AND user_id=?", (code, user.id)
            )
            if await cur.fetchone():
                await update.message.reply_text("❌ You have already redeemed this code.", reply_markup=user_reply_keyboard(admin))
                return ConversationHandler.END

            await db.execute(
                "INSERT INTO redeem_uses (code, user_id, timestamp) VALUES (?, ?, ?)",
                (code, user.id, datetime.utcnow().isoformat()),
            )
            await db.execute("UPDATE redeems SET used_count = used_count + 1 WHERE code=?", (code,))
            await db.commit()

        if redeem["coin_reward"]:
            await add_coins(user.id, redeem["coin_reward"], "redeem", f"Redeem code {code}")
        if redeem["premium_days"]:
            await grant_premium(user.id, redeem["premium_days"], admin_id=0)

    msg = f"✅ <b>Redeem Successful!</b>\n🪙 +{redeem['coin_reward']} Coins"
    if redeem["premium_days"]:
        msg += f"\n⭐ +{redeem['premium_days']} Days Premium"
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=user_reply_keyboard(admin))
    return ConversationHandler.END



def _generate_gift_code() -> str:
    alphabet = string.ascii_uppercase + string.digits
    return "GIFT" + "".join(secrets.choice(alphabet) for _ in range(8))


async def cb_redeem_gift_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    balance = await get_balance(update.effective_user.id)
    await query.message.reply_text(
        f"🎁 <b>Convert Coins to Gift Code</b>\n\n"
        f"🪙 Your balance: <b>{balance}</b>\n\n"
        "Enter how many coins to convert into a one-time gift code "
        "(you can share it with anyone — they redeem it once for that many coins):",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="redeem:cancel", style="primary")]]),
    )
    return GC_AMOUNT


async def conv_gift_amount(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit() or int(text) <= 0:
        await update.message.reply_text("❌ Please enter a valid positive number of coins.")
        return GC_AMOUNT
    amount = int(text)
    user = update.effective_user
    lock = await get_user_action_lock(user.id)

    async with lock:
        ok = await remove_coins(user.id, amount, "gift_code_created", f"Converted {amount} coins to a gift code")
        if not ok:
            await update.message.reply_text("❌ You don't have enough coins for that.")
            return ConversationHandler.END

        code = _generate_gift_code()
        async with db_conn() as db:
            for _ in range(5):
                cur = await db.execute("SELECT 1 FROM redeems WHERE code=?", (code,))
                if not await cur.fetchone():
                    break
                code = _generate_gift_code()
            await db.execute(
                "INSERT INTO redeems (code, coin_reward, premium_days, usage_limit, status, created_by, created_at, source) "
                "VALUES (?, ?, 0, 1, 'active', ?, ?, 'user')",
                (code, amount, user.id, datetime.utcnow().isoformat()),
            )
            await db.commit()

    await update.message.reply_text(
        f"✅ <b>Gift Code Created!</b>\n\n🎟 Code: <code>{code}</code>\n🪙 Value: <b>{amount} Coins</b>\n\n"
        "Share this code with anyone — they can redeem it once via 🎟️ Redeem Code → Redeem a Code.",
        parse_mode=ParseMode.HTML,
    )
    return ConversationHandler.END



async def handle_my_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    user = update.effective_user
    row = await get_user_row(user.id)
    balance = await get_balance(user.id)
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM purchases WHERE user_id=?", (user.id,))
        purchased = (await cur.fetchone())[0]
        cur = await db.execute("SELECT COUNT(*) FROM product_purchases WHERE user_id=?", (user.id,))
        product_purchased = (await cur.fetchone())[0]
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (user.id,))
        refs = (await cur.fetchone())[0]
        cur = await db.execute("SELECT COUNT(*) FROM redeem_uses WHERE user_id=?", (user.id,))
        redeems = (await cur.fetchone())[0]
        cur = await db.execute(
            "SELECT COALESCE(SUM(amount),0) FROM transactions WHERE user_id=? AND amount > 0", (user.id,)
        )
        earned = (await cur.fetchone())[0]
        cur = await db.execute(
            "SELECT COALESCE(SUM(amount),0) FROM transactions WHERE user_id=? AND amount < 0", (user.id,)
        )
        spent = abs((await cur.fetchone())[0])

    is_premium = await is_premium_active(user.id)
    premium_line = "👑 <b>Premium — Active</b>" if is_premium else "⭐ Premium: <i>Not Active</i>"
    text = (
        "📊 <b>My Stats</b>\n"
        f"{DIVIDER}\n"
        f"👤 <b>User ID:</b> <code>{user.id}</code>\n"
        f"📅 <b>Join Date:</b> {fmt_date(row['join_date']) if row else '—'}\n"
        f"🪙 <b>Coins:</b> {balance}\n"
        f"🛒 <b>Purchased Files:</b> {purchased}\n"
        f"🧩 <b>Purchased Products:</b> {product_purchased}\n"
        f"👥 <b>Referrals:</b> {refs}\n"
        f"🎁 <b>Redeem Count:</b> {redeems}\n"
        f"📈 <b>Coins Earned:</b> {earned}\n"
        f"📉 <b>Coins Spent:</b> {spent}\n"
        f"{premium_line}\n"
        f"{DIVIDER}"
    )
    await update.effective_message.reply_text(
        text, parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🗂 My Purchases", callback_data="purchases:0", style="primary")],
        ]),
    )



PRODUCT_CATEGORIES = {"bot": "Bot Source Code", "method": "Method"}
PRODUCTS_PER_PAGE = 8
PRODUCT_LONG_NAME_THRESHOLD = 20


def _category_label(category: str) -> str:
    return PRODUCT_CATEGORIES.get(category, category)


async def _get_product(product_id: int, include_deleted: bool = False):
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        if include_deleted:
            cur = await db.execute(
                "SELECT * FROM products WHERE product_id=?", (product_id,)
            )
        else:
            cur = await db.execute(
                "SELECT * FROM products WHERE product_id=? AND is_deleted=0", (product_id,)
            )
        return await cur.fetchone()


async def _user_owns_product(user_id: int, product_id: int) -> bool:
    async with db_conn() as db:
        cur = await db.execute(
            "SELECT 1 FROM product_purchases WHERE user_id=? AND product_id=?",
            (user_id, product_id),
        )
        return (await cur.fetchone()) is not None


def _build_product_buttons(rows, category: str, page: int) -> list:
    """Short names → two per row; long names → one full-width button."""
    buttons: list = []
    short_row: list = []
    for r in rows:
        label = r["name"]
        cb = f"buy:view:{r['product_id']}:{category}:{page}"
        btn = InlineKeyboardButton(label, callback_data=cb, style="primary")
        if len(label) <= PRODUCT_LONG_NAME_THRESHOLD:
            short_row.append(btn)
            if len(short_row) == 2:
                buttons.append(short_row)
                short_row = []
        else:
            if short_row:
                buttons.append(short_row)
                short_row = []
            buttons.append([btn])
    if short_row:
        buttons.append(short_row)
    return buttons


async def handle_buy_home(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    text = (
        "🛒 <b>Buy</b>\n\n"
        "💱 <b>1 Coin = ₹1</b>\n"
        "💬 <b>Buy coins:</b> DM @duifioookn2\n\n"
        "<b>Choose Option</b>"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("Bot Source Code", callback_data="buy:cat:bot:0", style="primary")],
        [InlineKeyboardButton("Method", callback_data="buy:cat:method:0", style="primary")],
        [InlineKeyboardButton("📂 Store", callback_data="buy:legacy", style="primary"),
         InlineKeyboardButton("🗂 My Purchases", callback_data="purchases:0", style="primary")],
    ])
    if update.callback_query:
        await update.callback_query.answer()
        try:
            await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        except BadRequest:
            await update.callback_query.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_buy_home(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await handle_buy_home(update, context)


async def cb_buy_legacy(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    await send_file_list(update, context, page=0, edit=True)


async def cb_buy_category(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    parts = query.data.split(":")
    category = parts[2] if len(parts) > 2 else "bot"
    try:
        page = max(0, int(parts[3]))
    except (IndexError, ValueError):
        page = 0
    await query.answer()
    await render_product_list(update, category, page)


async def render_product_list(update: Update, category: str, page: int) -> None:
    query = update.callback_query
    if category not in PRODUCT_CATEGORIES:
        await query.answer("❌ Invalid category.", show_alert=True)
        return
    page = max(0, page)
    per_page = PRODUCTS_PER_PAGE
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT COUNT(*) FROM products WHERE category=? AND is_deleted=0 AND is_active=1",
            (category,),
        )
        total = (await cur.fetchone())[0]
        if total and page * per_page >= total:
            page = max(0, (total - 1) // per_page)
        cur = await db.execute(
            "SELECT * FROM products WHERE category=? AND is_deleted=0 AND is_active=1 "
            "ORDER BY product_id DESC LIMIT ? OFFSET ?",
            (category, per_page, page * per_page),
        )
        rows = await cur.fetchall()

    title = _category_label(category)
    if total == 0:
        text = f"<b>{title}</b>\n\nNo {title} Available"
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("⬅ Back", callback_data="buy:home", style="primary")]])
    else:
        text = f"<b>{title}</b>\n\nSelect a product to view details:\n\n💱 <b>1 Coin = ₹1</b>"
        kb_rows = _build_product_buttons(rows, category, page)
        nav = []
        if page > 0:
            nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"buy:cat:{category}:{page-1}", style="primary"))
        if (page + 1) * per_page < total:
            nav.append(InlineKeyboardButton("Next ➡", callback_data=f"buy:cat:{category}:{page+1}", style="primary"))
        if nav:
            kb_rows.append(nav)
        total_pages = (total + per_page - 1) // per_page
        if total_pages > 1:
            text += f"\n<i>Page {page + 1}/{total_pages}</i>"
        kb_rows.append([InlineKeyboardButton("⬅ Back", callback_data="buy:home", style="primary")])
        kb = InlineKeyboardMarkup(kb_rows)

    try:
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    except BadRequest:
        await query.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_product_view(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    parts = query.data.split(":")
    try:
        product_id = int(parts[2])
        category = parts[3] if len(parts) > 3 else "bot"
        page = max(0, int(parts[4])) if len(parts) > 4 else 0
    except (IndexError, ValueError):
        await query.answer("❌ Invalid product.", show_alert=True)
        return
    product = await _get_product(product_id)
    if not product:
        await query.answer("❌ Product not found.", show_alert=True)
        return
    await query.answer()
    owned = await _user_owns_product(update.effective_user.id, product_id)
    await _render_product_details(update, product, category, page, owned)


async def _render_product_details(update: Update, product, category: str, page: int, owned: bool) -> None:
    query = update.callback_query
    description = html.escape(product["description"] or "")
    price = product["price"]
    price_line = "🟢 <b>FREE</b>" if price == 0 else f"🪙 <b>{price} Coins</b>"
    text = (
        f"🧩 <b>{html.escape(product['name'])}</b>\n"
        f"📂 Category: <b>{_category_label(product['category'])}</b>\n"
        f"{DIVIDER}\n"
        f"{description if description else '<i>No description provided.</i>'}\n"
        f"{DIVIDER}\n"
        f"{price_line}\n"
        "💱 <b>1 Coin = ₹1</b>"
    )
    if owned:
        text += "\n✅ <b>You already own this product.</b>"

    rows = []
    if owned:
        rows.append([InlineKeyboardButton("⬇ Redeliver", callback_data=f"buy:redeliver:{product['product_id']}", style="success")])
    else:
        rows.append([InlineKeyboardButton("🛒 Buy Now", callback_data=f"buy:buy:{product['product_id']}", style="success")])
    cat = product["category"]
    rows.append([
        InlineKeyboardButton("⬅ Back", callback_data=f"buy:cat:{cat}:{page}", style="primary"),
        InlineKeyboardButton("🏠 Buy Menu", callback_data="buy:home", style="primary"),
    ])
    kb = InlineKeyboardMarkup(rows)

    preview_id = product["preview_file_id"]
    if preview_id:
        caption = text if len(text) <= 1000 else text[:980] + "…"
        try:
            await query.message.reply_photo(
                photo=preview_id, caption=caption, parse_mode=ParseMode.HTML, reply_markup=kb
            )
            return
        except TelegramError:
            pass
    if len(text) > 3900:
        text = text[:3800] + "…"
    try:
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    except BadRequest:
        await query.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


def _row_get(row, key, default=None):
    try:
        return row[key]
    except (IndexError, KeyError, TypeError):
        return default


async def get_storage_channel_id() -> int | None:
    """Return the configured private storage channel id, if valid."""
    raw = (await get_setting("product_channel_id", "") or "").strip()
    if raw:
        try:
            return int(raw)
        except ValueError:
            pass
    env_raw = (
        os.environ.get("PRODUCT_CHANNEL_ID", "").strip()
        or os.environ.get("DATABASE_CHANNEL_ID", "").strip()
        or _PRODUCT_CHANNEL_ID
    )
    if env_raw:
        try:
            return int(env_raw)
        except ValueError:
            pass
    return None


async def check_storage_channel(bot) -> tuple[bool, str]:
    """Verify the bot can access and post to the configured storage channel."""
    channel_id = await get_storage_channel_id()
    if not channel_id:
        return False, "No storage channel configured."
    try:
        chat = await bot.get_chat(channel_id)
        member = await bot.get_chat_member(channel_id, bot.id)
    except TelegramError as exc:
        return False, f"Cannot access channel: {exc}"
    status = str(getattr(member, "status", ""))
    if status not in ("administrator", "creator"):
        return False, "Bot is not an admin in this channel. Add the bot as an admin with Post Messages permission."
    title = getattr(chat, "title", None) or str(channel_id)
    return True, title


async def store_product_in_channel(bot, source_chat_id: int, source_message_id: int, label: str) -> tuple[int | None, int | None, str]:
    """Copy an admin-uploaded product message into the private storage channel.

    Returns (channel_id, message_id, error). On success error is empty; on
    failure both ids are None and error explains why so callers can fall back
    to storing the Telegram file_id directly.
    """
    channel_id = await get_storage_channel_id()
    if not channel_id:
        return None, None, "not_configured"
    try:
        sent = await bot.copy_message(
            chat_id=channel_id,
            from_chat_id=source_chat_id,
            message_id=source_message_id,
            caption=f"📦 Product: {label}"[:1024],
        )
        return channel_id, sent.message_id, ""
    except TelegramError as exc:
        log.warning("Could not store product in channel %s: %s", channel_id, exc)
        return None, None, str(exc)


async def copy_stored_product(bot, chat_id: int, product) -> bool:
    """Deliver a product directly from the storage channel message."""
    channel_id = _row_get(product, "storage_chat_id")
    message_id = _row_get(product, "storage_message_id")
    if not channel_id or not message_id:
        return False
    try:
        await bot.copy_message(
            chat_id=chat_id,
            from_chat_id=int(channel_id),
            message_id=int(message_id),
        )
        return True
    except TelegramError as exc:
        log.warning("Stored product copy failed (channel=%s msg=%s): %s", channel_id, message_id, exc)
        return False


async def _send_product_attachment(bot, chat_id: int, product) -> None:
    file_id = product["attachment_file_id"]
    if not file_id:
        return
    kind = (product["attachment_kind"] or "document").lower()
    name = product["attachment_name"] or "product"
    caption = f"🧩 {html.escape(product['name'])}"
    if kind == "photo":
        await bot.send_photo(chat_id=chat_id, photo=file_id, caption=caption, parse_mode=ParseMode.HTML)
    elif kind == "video":
        await bot.send_video(chat_id=chat_id, video=file_id, caption=caption, parse_mode=ParseMode.HTML)
    elif kind == "audio":
        await bot.send_audio(chat_id=chat_id, audio=file_id, caption=caption, parse_mode=ParseMode.HTML)
    elif kind == "voice":
        await bot.send_voice(chat_id=chat_id, voice=file_id, caption=caption, parse_mode=ParseMode.HTML)
    elif kind == "animation":
        await bot.send_animation(chat_id=chat_id, animation=file_id, caption=caption, parse_mode=ParseMode.HTML)
    else:
        await bot.send_document(
            chat_id=chat_id, document=file_id,
            caption=caption, parse_mode=ParseMode.HTML
        )


async def deliver_product(bot, user_id: int, product, purchase_id: int | None = None) -> tuple[bool, str]:
    """Deliver admin content/attachment. Returns (success, error_message)."""
    delivered_any = False
    errors: list[str] = []
    description = (product["description"] or "").strip()
    if description:
        try:
            await bot.send_message(
                user_id,
                "📦 <b>Your purchase:</b>\n\n" + html.escape(description),
                parse_mode=ParseMode.HTML,
            )
            delivered_any = True
        except TelegramError as exc:
            errors.append(f"text: {exc}")
    attachment_file_id = _row_get(product, "attachment_file_id")
    if _row_get(product, "storage_message_id") or attachment_file_id:
        copied = await copy_stored_product(bot, user_id, product)
        if copied:
            delivered_any = True
        elif attachment_file_id:
            # Channel message may have been deleted — fall back to the file_id
            # captured when the product was created.
            try:
                await _send_product_attachment(bot, user_id, product)
                delivered_any = True
            except TelegramError as exc:
                errors.append(f"file: {exc}")
        else:
            errors.append("file: stored channel message unavailable and no fallback file")

    if delivered_any and not errors:
        if purchase_id is not None:
            async with db_conn() as db:
                await db.execute(
                    "UPDATE product_purchases SET delivery_status='sent', delivered_at=?, delivery_error=NULL "
                    "WHERE id=?",
                    (datetime.utcnow().isoformat(), purchase_id),
                )
                await db.commit()
        return True, ""

    error_text = "; ".join(errors) if errors else "No deliverable content or attachment configured."
    if purchase_id is not None:
        async with db_conn() as db:
            await db.execute(
                "UPDATE product_purchases SET delivery_status='failed', delivery_error=? WHERE id=?",
                (error_text[:500], purchase_id),
            )
            await db.commit()
    log.warning("Product delivery issue for user %s purchase %s: %s", user_id, purchase_id, error_text)
    return False, error_text


async def cb_product_buy(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    try:
        product_id = int(query.data.split(":")[2])
    except (IndexError, ValueError):
        await query.answer("❌ Invalid product.", show_alert=True)
        return
    user = update.effective_user
    lock = await get_user_action_lock(user.id)
    async with lock:
        product = await _get_product(product_id)
        if not product or not product["is_active"]:
            await query.answer("❌ This product is no longer available.", show_alert=True)
            return
        if await _user_owns_product(user.id, product_id):
            await query.answer("✅ You already own this product. Use Redeliver.", show_alert=True)
            return

        price = int(product["price"] or 0)
        if price > 0:
            ok = await remove_coins(
                user.id, price, "product_purchase", f"Purchased product #{product_id}: {product['name']}"
            )
            if not ok:
                balance = await get_balance(user.id)
                await query.answer("❌ Not enough Coins.", show_alert=True)
                low_kb = InlineKeyboardMarkup([
                    [InlineKeyboardButton("💼 Open Wallet", callback_data="wallet:home", style="primary")],
                    [InlineKeyboardButton("⬅ Back", callback_data=f"buy:cat:{product['category']}:0", style="primary")],
                ])
                low_text = (
                    "❌ <b>Not enough Coins.</b>\n\n"
                    "💱 <b>1 Coin = ₹1</b>\n"
                    "💬 <b>Buy coins:</b> DM @duifioookn2\n\n"
                    f"🧩 Product: <b>{html.escape(product['name'])}</b>\n"
                    f"🪙 Required: <b>{price}</b>\n"
                    f"👛 Your balance: <b>{balance}</b>"
                )
                try:
                    await query.edit_message_text(low_text, parse_mode=ParseMode.HTML, reply_markup=low_kb)
                except BadRequest:
                    await query.message.reply_text(low_text, parse_mode=ParseMode.HTML, reply_markup=low_kb)
                return

        try:
            async with db_conn() as db:
                await db.execute(
                    "INSERT INTO product_purchases (user_id, product_id, product_name, category, price, "
                    "delivery_status, timestamp) VALUES (?, ?, ?, ?, ?, 'pending', ?)",
                    (user.id, product_id, product["name"], product["category"], price,
                     datetime.utcnow().isoformat()),
                )
                await db.commit()
                cur = await db.execute("SELECT last_insert_rowid()")
                purchase_id = (await cur.fetchone())[0]
        except aiosqlite.IntegrityError:
            if price > 0:
                await add_coins(user.id, price, "product_refund", "Duplicate purchase prevented — refunded")
            await query.answer("✅ You already own this product.", show_alert=True)
            return
        except aiosqlite.Error:
            log.exception("Failed to record product purchase")
            if price > 0:
                await add_coins(user.id, price, "product_refund", "Purchase failed — coins refunded")
            await query.answer("❌ Could not complete the purchase. Your coins were refunded.", show_alert=True)
            return

    success, err = await deliver_product(context.bot, user.id, product, purchase_id)
    if success:
        await query.answer("✅ Purchased!")
        try:
            await query.edit_message_text(
                "✅ <b>Purchase Successful!</b>\n\n"
                f"🧩 <b>{html.escape(product['name'])}</b>\n"
                f"🪙 Paid: <b>{price} Coins</b>\n\n"
                "Your content has been delivered above.",
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("⬇ Redeliver", callback_data=f"buy:redeliver:{product_id}", style="success")],
                    [InlineKeyboardButton("🛒 Buy Menu", callback_data="buy:home", style="primary")],
                ]),
            )
        except BadRequest:
            pass
    else:
        await query.answer("⚠️ Purchase recorded but delivery failed.", show_alert=True)
        try:
            await query.edit_message_text(
                "⚠️ <b>Purchase recorded, but delivery failed.</b>\n\n"
                f"🧩 <b>{html.escape(product['name'])}</b>\n"
                f"🪙 Paid: <b>{price} Coins</b>\n\n"
                "You will not be charged again. Tap Redeliver to try again, or contact support.",
                parse_mode=ParseMode.HTML,
                reply_markup=InlineKeyboardMarkup([
                    [InlineKeyboardButton("⬇ Retry Delivery", callback_data=f"buy:redeliver:{product_id}", style="danger")],
                    [InlineKeyboardButton("💬 Support", callback_data="buy:support", style="primary")],
                ]),
            )
        except BadRequest:
            pass


async def cb_product_redeliver(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    try:
        product_id = int(query.data.split(":")[2])
    except (IndexError, ValueError):
        await query.answer("❌ Invalid product.", show_alert=True)
        return
    user = update.effective_user
    # Allow redelivery even if the product was later deactivated/deleted, as
    # long as the user already owns it — purchases must never be lost.
    product = await _get_product(product_id, include_deleted=True)
    if not product:
        await query.answer("❌ Product not found.", show_alert=True)
        return
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT * FROM product_purchases WHERE user_id=? AND product_id=?",
            (user.id, product_id),
        )
        purchase = await cur.fetchone()
    if not purchase:
        await query.answer("❌ You have not purchased this product.", show_alert=True)
        return
    await query.answer("⬇ Delivering...")
    success, _ = await deliver_product(context.bot, user.id, product, purchase["id"])
    if success:
        try:
            await query.message.reply_text(
                "✅ <b>Redelivered successfully.</b>", parse_mode=ParseMode.HTML
            )
        except TelegramError:
            pass
    else:
        try:
            await query.message.reply_text(
                "⚠️ Delivery still failing. Please contact support.", parse_mode=ParseMode.HTML
            )
        except TelegramError:
            pass


async def cb_buy_support(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    support_username = await get_setting("support_username", "duifioookn2")
    await query.message.reply_text(
        "💬 <b>Support</b>\n\n" f"👤 Contact: @{html.escape(support_username)}",
        parse_mode=ParseMode.HTML,
    )


async def handle_buy_files(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    await send_file_list(update, context, page=0)


async def send_file_list(update: Update, context: ContextTypes.DEFAULT_TYPE, page: int, edit: bool = False) -> None:
    per_page = 8
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT file_pk, file_name, price FROM files WHERE is_deleted=0 "
            "ORDER BY file_pk DESC LIMIT ? OFFSET ?",
            (per_page, page * per_page),
        )
        rows = await cur.fetchall()

    if not rows:
        text = "🛒 <b>Buy Files</b>\n\nNo files available right now."
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("🛒 My Purchases", callback_data="purchases:0", style="primary")]])
    else:
        text = "🛒 <b>Buy Files</b>\n\nSelect a file to view details:"
        buttons = []
        for r in rows:
            tag = "🟢 FREE" if r["price"] == 0 else f"🪙 {r['price']}"
            buttons.append([InlineKeyboardButton(f"📄 {r['file_name']} — {tag}", callback_data=f"file:view:{r['file_pk']}", style="primary")])
        nav = []
        if page > 0:
            nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"files:list:{page-1}", style="primary"))
        if len(rows) == per_page:
            nav.append(InlineKeyboardButton("Next ➡", callback_data=f"files:list:{page+1}", style="primary"))
        if nav:
            buttons.append(nav)
        buttons.append([InlineKeyboardButton("🛒 My Purchases", callback_data="purchases:0", style="primary")])
        kb = InlineKeyboardMarkup(buttons)

    if edit and update.callback_query:
        try:
            await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        except BadRequest:
            await update.callback_query.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_files_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    page = int(query.data.split(":")[2])
    await send_file_list(update, context, page, edit=True)


async def cb_file_view(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    file_pk = int(query.data.split(":")[2])
    user = update.effective_user

    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM files WHERE file_pk=? AND is_deleted=0", (file_pk,))
        f = await cur.fetchone()
        if not f:
            await query.answer("❌ File not found.", show_alert=True)
            return
        cur = await db.execute(
            "SELECT 1 FROM purchases WHERE user_id=? AND file_pk=?", (user.id, file_pk)
        )
        owned = bool(await cur.fetchone())

    await query.answer()
    icon = FILE_TYPE_ICON.get(f["file_kind"], "📄")
    text = (
        f"{icon} <b>{html.escape(f['file_name'])}</b>\n\n"
        f"📦 Size: <b>{fmt_size(f['file_size'])}</b>\n"
        f"📄 Description: {html.escape(f['description']) if f['description'] else '—'}\n"
    )
    if f["price"] == 0 or owned:
        text += "\n🟢 <b>FREE</b>" if f["price"] == 0 and not owned else "\n✅ <b>You own this file</b>"
        buttons = [[InlineKeyboardButton("⬇ Download", callback_data=f"file:dl:{file_pk}", style="primary")]]
    else:
        text += f"\n🪙 <b>{f['price']} Coins</b>"
        buttons = [[InlineKeyboardButton("🛒 Buy Now", callback_data=f"file:buy:{file_pk}", style="primary")]]
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="files:list:0", style="primary")])
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_file_buy(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    file_pk = int(query.data.split(":")[2])
    user = update.effective_user
    lock = await get_user_action_lock(user.id)
    async with lock:
        async with db_conn() as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM files WHERE file_pk=? AND is_deleted=0", (file_pk,))
            f = await cur.fetchone()
            if not f:
                await query.answer("❌ File not found.", show_alert=True)
                return
            cur = await db.execute("SELECT 1 FROM purchases WHERE user_id=? AND file_pk=?", (user.id, file_pk))
            if await cur.fetchone():
                await query.answer("✅ You already own this file.", show_alert=True)
                return

        if f["price"] > 0:
            ok = await remove_coins(user.id, f["price"], "purchase", f"Purchased file: {f['file_name']}")
            if not ok:
                await query.answer("❌ Not enough Coins.", show_alert=True)
                await query.edit_message_text(
                    "❌ <b>Not enough Coins.</b>\n\nPlease top up your wallet to continue.",
                    parse_mode=ParseMode.HTML,
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("💼 Open Wallet", callback_data="wallet:home", style="primary")]]),
                )
                return

        async with db_conn() as db:
            await db.execute(
                "INSERT INTO purchases (user_id, file_pk, price, timestamp) VALUES (?, ?, ?, ?)",
                (user.id, file_pk, f["price"], datetime.utcnow().isoformat()),
            )
            await db.commit()

    await query.answer("✅ Purchased!")
    await query.edit_message_text(
        f"✅ <b>Purchase Successful!</b>\n\nYou now own <b>{html.escape(f['file_name'])}</b> forever.",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬇ Download Now", callback_data=f"file:dl:{file_pk}", style="primary")]]),
    )


async def cb_file_download(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    file_pk = int(query.data.split(":")[2])
    user = update.effective_user

    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM files WHERE file_pk=? AND is_deleted=0", (file_pk,))
        f = await cur.fetchone()
        if not f:
            await query.answer("❌ File not found.", show_alert=True)
            return
        if f["price"] > 0:
            cur = await db.execute("SELECT 1 FROM purchases WHERE user_id=? AND file_pk=?", (user.id, file_pk))
            if not await cur.fetchone():
                await query.answer("❌ You need to purchase this file first.", show_alert=True)
                return

    await query.answer("⬇ Sending file...")
    try:
        await context.bot.send_document(
            chat_id=user.id, document=f["tg_file_id"], caption=f"📄 {html.escape(f['file_name'])}", parse_mode=ParseMode.HTML
        )
    except (BadRequest, TelegramError):
        try:
            await context.bot.send_message(user.id, "⚠️ Could not deliver file, please contact support.")
        except TelegramError:
            pass
        return

    async with db_conn() as db:
        await db.execute(
            "INSERT INTO downloads (user_id, file_pk, timestamp) VALUES (?, ?, ?)",
            (user.id, file_pk, datetime.utcnow().isoformat()),
        )
        await db.execute("UPDATE files SET downloads_count = downloads_count + 1 WHERE file_pk=?", (file_pk,))
        await db.commit()


async def cb_my_purchases(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    user = update.effective_user
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT * FROM product_purchases WHERE user_id=? ORDER BY id DESC LIMIT 20",
            (user.id,),
        )
        products = await cur.fetchall()
        cur = await db.execute(
            "SELECT p.*, f.file_name FROM purchases p JOIN files f ON p.file_pk=f.file_pk "
            "WHERE p.user_id=? ORDER BY p.id DESC LIMIT 20",
            (user.id,),
        )
        files = await cur.fetchall()

    lines = ["🛒 <b>My Purchases</b>"]
    buttons = []
    if products:
        lines.append(f"\n🧩 <b>Products ({len(products)})</b>")
        for r in products:
            status = "" if r["delivery_status"] == "sent" else " ⚠️"
            lines.append(f"• {html.escape(r['product_name'] or ('Product #' + str(r['product_id'])))}{status}")
            buttons.append([InlineKeyboardButton(
                f"⬇ {r['product_name'] or ('Product #' + str(r['product_id']))}",
                callback_data=f"buy:redeliver:{r['product_id']}", style="success",
            )])
    if files:
        lines.append(f"\n📂 <b>Files ({len(files)})</b>")
        for r in files:
            lines.append(f"• {html.escape(r['file_name'])}")
            buttons.append([InlineKeyboardButton(
                f"⬇ {r['file_name']}", callback_data=f"file:dl:{r['file_pk']}", style="primary",
            )])
    if not products and not files:
        lines.append("\nYou haven't purchased anything yet.")

    buttons.append([InlineKeyboardButton("🏠 Buy Menu", callback_data="buy:home", style="primary")])
    text = "\n".join(lines)
    if len(text) > 3900:
        text = text[:3800] + "…"
    kb = InlineKeyboardMarkup(buttons)
    try:
        await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    except BadRequest:
        await query.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)



async def require_admin(update: Update) -> bool:
    if await is_admin(update.effective_user.id):
        return True
    if update.callback_query:
        await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
    else:
        await update.effective_message.reply_text(ADMIN_ONLY_MSG)
    return False


# ---------------------------------------------------------------------------
# Admin: Product Manager
# ---------------------------------------------------------------------------

async def cb_admin_products(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_admin(update):
        return
    if update.callback_query:
        await update.callback_query.answer()
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM products WHERE is_deleted=0")
        total = (await cur.fetchone())[0]
        cur = await db.execute("SELECT COUNT(*) FROM products WHERE is_deleted=0 AND is_active=1")
        active = (await cur.fetchone())[0]
        cur = await db.execute("SELECT COUNT(*) FROM products WHERE is_deleted=0 AND category='bot'")
        bots = (await cur.fetchone())[0]
        cur = await db.execute("SELECT COUNT(*) FROM products WHERE is_deleted=0 AND category='method'")
        methods = (await cur.fetchone())[0]
    text = (
        "🛒 <b>Product Manager</b>\n"
        f"{DIVIDER}\n"
        f"🧩 Total Products: <b>{total}</b>\n"
        f"✅ Active: <b>{active}</b>\n"
        f"🤖 Bot Source Code: <b>{bots}</b>\n"
        f"📘 Methods: <b>{methods}</b>"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ Add Product", callback_data="pm:addsel", style="success")],
        [InlineKeyboardButton("🤖 Bot Source Code", callback_data="pm:list:bot:0", style="primary")],
        [InlineKeyboardButton("📘 Method", callback_data="pm:list:method:0", style="primary")],
        [InlineKeyboardButton("⬅ Back", callback_data="ad:home", style="primary")],
    ])
    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_pm_add_select(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await require_admin(update):
        return ConversationHandler.END
    query = update.callback_query
    await query.answer()
    await query.edit_message_text(
        "➕ <b>Add Product</b>\n\n<b>Choose Product Category</b>",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("Method", callback_data="pm:add:method", style="primary")],
            [InlineKeyboardButton("Bot Source Code", callback_data="pm:add:bot", style="primary")],
            [InlineKeyboardButton("❌ Cancel", callback_data="pm:cancel", style="danger")],
        ]),
    )
    return ConversationHandler.END


async def cb_pm_add_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await require_admin(update):
        return ConversationHandler.END
    query = update.callback_query
    await query.answer()
    parts = query.data.split(":")
    category = parts[2] if len(parts) > 2 else "bot"
    if category not in PRODUCT_CATEGORIES:
        await query.answer("❌ Invalid category.", show_alert=True)
        return ConversationHandler.END
    context.user_data["pm_draft"] = {
        "category": category,
        "name": "",
        "description": "",
        "price": 0,
        "preview_file_id": None,
        "preview_file_unique_id": None,
        "attachment_file_id": None,
        "attachment_file_unique_id": None,
        "attachment_kind": None,
        "attachment_name": None,
        "attachment_size": 0,
        "storage_chat_id": None,
        "storage_message_id": None,
        "is_active": 1,
    }
    await query.message.reply_text(
        f"➕ <b>Add {_category_label(category)}</b>\n\n"
        "Step 1/6 — Enter the product <b>name</b>:\n\nSend /cancel to abort.",
        parse_mode=ParseMode.HTML,
    )
    return PR_NAME


async def conv_pm_name(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    draft = context.user_data.get("pm_draft")
    if not draft:
        await update.message.reply_text("❌ Session expired. Please start again from Product Manager.")
        return ConversationHandler.END
    name = update.message.text.strip()
    if not name:
        await update.message.reply_text("❌ Name cannot be empty. Please enter a product name.")
        return PR_NAME
    if len(name) > 100:
        await update.message.reply_text("❌ Name is too long (max 100 characters).")
        return PR_NAME
    draft["name"] = name
    await update.message.reply_text(
        "Step 2/6 — Enter the <b>description / content</b> shown to users.\n"
        "Send - to skip.",
        parse_mode=ParseMode.HTML,
    )
    return PR_DESC


async def conv_pm_desc(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    draft = context.user_data.get("pm_draft")
    if not draft:
        await update.message.reply_text("❌ Session expired. Please start again.")
        return ConversationHandler.END
    text = update.message.text.strip()
    draft["description"] = "" if text in ("-", "") else text
    await update.message.reply_text("Step 3/6 — Enter the <b>coin price</b> (0 = free):", parse_mode=ParseMode.HTML)
    return PR_PRICE


async def conv_pm_price(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    draft = context.user_data.get("pm_draft")
    if not draft:
        await update.message.reply_text("❌ Session expired. Please start again.")
        return ConversationHandler.END
    text = update.message.text.strip()
    if not text.isdigit() or int(text) < 0:
        await update.message.reply_text("❌ Please enter a valid non-negative whole number.")
        return PR_PRICE
    draft["price"] = int(text)
    await update.message.reply_text(
        "Step 4/6 — Send an optional <b>preview image</b>, or tap Skip.",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("⏭ Skip Image", callback_data="pm:skip:preview", style="primary")],
            [InlineKeyboardButton("❌ Cancel", callback_data="pm:cancel", style="danger")],
        ]),
    )
    return PR_PREVIEW


async def conv_pm_preview(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    draft = context.user_data.get("pm_draft")
    if not draft:
        await update.message.reply_text("❌ Session expired. Please start again.")
        return ConversationHandler.END
    if not update.message.photo:
        await update.message.reply_text("❌ Please send a photo image, or tap Skip Image.")
        return PR_PREVIEW
    photo = update.message.photo[-1]
    draft["preview_file_id"] = photo.file_id
    draft["preview_file_unique_id"] = photo.file_unique_id
    await update.message.reply_text(
        "Step 5/6 — Send the optional <b>product file/attachment</b>, or tap Skip.",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("⏭ Skip File", callback_data="pm:skip:file", style="primary")],
            [InlineKeyboardButton("❌ Cancel", callback_data="pm:cancel", style="danger")],
        ]),
    )
    return PR_FILE


async def conv_pm_file(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    draft = context.user_data.get("pm_draft")
    if not draft:
        await update.message.reply_text("❌ Session expired. Please start again.")
        return ConversationHandler.END
    msg = update.message
    kind = None
    tg_file = None
    file_name = None
    file_size = 0
    if msg.document:
        kind, tg_file = "document", msg.document
        file_name, file_size = tg_file.file_name or "file", tg_file.file_size or 0
    elif msg.video:
        kind, tg_file = "video", msg.video
        file_name, file_size = tg_file.file_name or "video.mp4", tg_file.file_size or 0
    elif msg.audio:
        kind, tg_file = "audio", msg.audio
        file_name, file_size = tg_file.file_name or "audio.mp3", tg_file.file_size or 0
    elif msg.photo:
        tg_file, kind = msg.photo[-1], "photo"
        file_name, file_size = f"photo_{tg_file.file_unique_id}.jpg", tg_file.file_size or 0
    elif msg.voice:
        kind, tg_file = "voice", msg.voice
        file_name, file_size = f"voice_{tg_file.file_unique_id}.ogg", tg_file.file_size or 0
    elif msg.animation:
        kind, tg_file = "animation", msg.animation
        file_name, file_size = tg_file.file_name or "animation.mp4", tg_file.file_size or 0

    if not tg_file:
        await update.message.reply_text(
            "❌ Unsupported file type. Send a document, photo, video, audio, voice, or GIF, or tap Skip File."
        )
        return PR_FILE
    draft["attachment_file_id"] = tg_file.file_id
    draft["attachment_file_unique_id"] = tg_file.file_unique_id
    draft["attachment_kind"] = kind
    draft["attachment_name"] = file_name
    draft["attachment_size"] = file_size
    channel_id, channel_msg_id, store_err = await store_product_in_channel(
        context.bot, update.effective_chat.id, msg.message_id,
        draft.get("name") or file_name or "product",
    )
    draft["storage_chat_id"] = channel_id
    draft["storage_message_id"] = channel_msg_id
    if store_err == "not_configured":
        note = ("\n\n⚠️ <b>Storage channel set nahi hai.</b> File seedha file_id se "
                "deliver hogi. Admin Panel → 📦 Storage Channel se set karo.")
    elif store_err:
        note = ("\n\n⚠️ <b>Channel upload failed:</b> " + html.escape(store_err) +
                "\nFile fallback file_id se deliver hogi.")
    else:
        note = "\n\n📦 Channel me save ho gaya."
    await update.message.reply_text(
        "Step 6/6 — Choose the product status:" + note,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("✅ Active", callback_data="pm:status:active", style="success"),
             InlineKeyboardButton("⛔ Inactive", callback_data="pm:status:inactive", style="primary")],
            [InlineKeyboardButton("❌ Cancel", callback_data="pm:cancel", style="danger")],
        ]),
    )
    return PR_STATUS


async def cb_pm_skip_preview(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    if not context.user_data.get("pm_draft"):
        await query.message.reply_text("❌ Session expired. Please start again.")
        return ConversationHandler.END
    await query.message.reply_text(
        "Step 5/6 — Send the optional <b>product file/attachment</b>, or tap Skip.",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("⏭ Skip File", callback_data="pm:skip:file", style="primary")],
            [InlineKeyboardButton("❌ Cancel", callback_data="pm:cancel", style="danger")],
        ]),
    )
    return PR_FILE


async def cb_pm_skip_file(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    if not context.user_data.get("pm_draft"):
        await query.message.reply_text("❌ Session expired. Please start again.")
        return ConversationHandler.END
    await query.message.reply_text(
        "Step 6/6 — Choose the product status:",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("✅ Active", callback_data="pm:status:active", style="success"),
             InlineKeyboardButton("⛔ Inactive", callback_data="pm:status:inactive", style="primary")],
            [InlineKeyboardButton("❌ Cancel", callback_data="pm:cancel", style="danger")],
        ]),
    )
    return PR_STATUS


async def cb_pm_status(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    draft = context.user_data.get("pm_draft")
    if not draft:
        await query.message.reply_text("❌ Session expired. Please start again.")
        return ConversationHandler.END
    draft["is_active"] = 1 if query.data.endswith("active") else 0
    await _pm_show_review(query.message, draft)
    return PR_CONFIRM


def _pm_review_text(draft: dict) -> str:
    return (
        "🧾 <b>Review Product</b>\n"
        f"{DIVIDER}\n"
        f"📂 Category: <b>{_category_label(draft['category'])}</b>\n"
        f"🧩 Name: <b>{html.escape(draft['name'])}</b>\n"
        f"🪙 Price: <b>{draft['price']}</b>\n"
        f"🖼 Preview Image: {'✅ Yes' if draft['preview_file_id'] else '❌ None'}\n"
        f"📎 Attachment: {'✅ ' + html.escape(str(draft['attachment_name'])) if draft['attachment_file_id'] else '❌ None'}\n"
        f"📦 Channel copy: {'✅ Saved' if draft.get('storage_message_id') else '❌ Not saved'}\n"
        f"📌 Status: {'✅ Active' if draft['is_active'] else '⛔ Inactive'}\n"
        f"{DIVIDER}\n"
        f"📝 Description:\n{html.escape(draft['description']) if draft['description'] else '<i>None</i>'}"
    )


async def _pm_show_review(message, draft: dict) -> None:
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Confirm & Save", callback_data="pm:save", style="success")],
        [InlineKeyboardButton("✏️ Edit", callback_data="pm:editmenu", style="primary"),
         InlineKeyboardButton("❌ Cancel", callback_data="pm:cancel", style="danger")],
    ])
    await message.reply_text(_pm_review_text(draft), parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_pm_edit_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    if not context.user_data.get("pm_draft"):
        await query.message.reply_text("❌ Session expired. Please start again.")
        return ConversationHandler.END
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("🧩 Name", callback_data="pm:edit:name", style="primary"),
         InlineKeyboardButton("📝 Description", callback_data="pm:edit:desc", style="primary")],
        [InlineKeyboardButton("🪙 Price", callback_data="pm:edit:price", style="primary"),
         InlineKeyboardButton("🖼 Preview", callback_data="pm:edit:preview", style="primary")],
        [InlineKeyboardButton("📎 Attachment", callback_data="pm:edit:file", style="primary"),
         InlineKeyboardButton("📌 Status", callback_data="pm:edit:status", style="primary")],
        [InlineKeyboardButton("⬅ Back to Review", callback_data="pm:review", style="primary")],
    ])
    await query.message.reply_text("✏️ <b>Edit Product — choose a field:</b>", parse_mode=ParseMode.HTML, reply_markup=kb)
    return PR_CONFIRM


async def cb_pm_edit_field(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    field = query.data.split(":")[2]
    if not context.user_data.get("pm_draft"):
        await query.message.reply_text("❌ Session expired. Please start again.")
        return ConversationHandler.END
    if field == "name":
        await query.message.reply_text("📝 Enter the new product name:")
        return PR_NAME
    if field == "desc":
        await query.message.reply_text("📝 Enter the new description (send - to clear):")
        return PR_DESC
    if field == "price":
        await query.message.reply_text("🪙 Enter the new coin price (0 = free):")
        return PR_PRICE
    if field == "preview":
        await query.message.reply_text(
            "🖼 Send a new preview image, or choose an option:",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("⏭ Skip", callback_data="pm:skip:preview", style="primary")],
                [InlineKeyboardButton("🗑 Remove Image", callback_data="pm:edit:rmpreview", style="danger")],
            ]),
        )
        return PR_PREVIEW
    if field == "file":
        await query.message.reply_text(
            "📎 Send a new attachment, or choose an option:",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("⏭ Skip", callback_data="pm:skip:file", style="primary")],
                [InlineKeyboardButton("🗑 Remove File", callback_data="pm:edit:rmfile", style="danger")],
            ]),
        )
        return PR_FILE
    if field == "status":
        await query.message.reply_text(
            "📌 Choose the product status:",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("✅ Active", callback_data="pm:status:active", style="success"),
                 InlineKeyboardButton("⛔ Inactive", callback_data="pm:status:inactive", style="primary")],
            ]),
        )
        return PR_STATUS
    await query.message.reply_text("❌ Unknown field.")
    return PR_CONFIRM


async def cb_pm_remove_preview(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    draft = context.user_data.get("pm_draft")
    if draft:
        draft["preview_file_id"] = None
        draft["preview_file_unique_id"] = None
    await _pm_show_review(query.message, draft) if draft else None
    return PR_CONFIRM if draft else ConversationHandler.END


async def cb_pm_remove_file(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    draft = context.user_data.get("pm_draft")
    if draft:
        draft["attachment_file_id"] = None
        draft["attachment_file_unique_id"] = None
        draft["attachment_kind"] = None
        draft["attachment_name"] = None
        draft["attachment_size"] = 0
        draft["storage_chat_id"] = None
        draft["storage_message_id"] = None
    await _pm_show_review(query.message, draft) if draft else None
    return PR_CONFIRM if draft else ConversationHandler.END


async def cb_pm_review(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    draft = context.user_data.get("pm_draft")
    if not draft:
        await query.message.reply_text("❌ Session expired. Please start again.")
        return ConversationHandler.END
    await _pm_show_review(query.message, draft)
    return PR_CONFIRM


async def cb_pm_save(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    draft = context.user_data.get("pm_draft")
    if not draft:
        await query.answer("⚠️ This product was already saved or cancelled.", show_alert=True)
        return ConversationHandler.END
    if not await require_admin(update):
        return ConversationHandler.END
    if not draft.get("name"):
        await query.answer("❌ Product name missing.", show_alert=True)
        return PR_CONFIRM
    if not draft.get("description") and not draft.get("attachment_file_id"):
        await query.answer("❌ Add a description or an attachment first.", show_alert=True)
        return PR_CONFIRM
    now = datetime.utcnow().isoformat()
    try:
        async with db_conn() as db:
            await db.execute(
                "INSERT INTO products (category, name, description, price, preview_file_id, "
                "preview_file_unique_id, attachment_file_id, attachment_file_unique_id, "
                "attachment_kind, attachment_name, attachment_size, storage_chat_id, storage_message_id, "
                "is_active, created_at, updated_at) "
                "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (
                    draft["category"], draft["name"], draft["description"], draft["price"],
                    draft["preview_file_id"], draft["preview_file_unique_id"],
                    draft["attachment_file_id"], draft["attachment_file_unique_id"],
                    draft["attachment_kind"], draft["attachment_name"], draft["attachment_size"],
                    draft.get("storage_chat_id"), draft.get("storage_message_id"),
                    draft["is_active"], now, now,
                ),
            )
            await db.commit()
            cur = await db.execute("SELECT last_insert_rowid()")
            pid = (await cur.fetchone())[0]
    except aiosqlite.Error as exc:
        log.exception("Failed to save product")
        await query.answer("❌ Failed to save product.", show_alert=True)
        await query.message.reply_text(f"❌ <b>Save failed:</b> {html.escape(str(exc))}", parse_mode=ParseMode.HTML)
        return PR_CONFIRM
    context.user_data.pop("pm_draft", None)
    await query.answer("✅ Product saved")
    await query.message.reply_text(
        f"✅ <b>Product Saved!</b>\n\n🆔 ID: <code>{pid}</code>\n"
        f"🧩 {html.escape(draft['name'])}\n"
        f"📂 {_category_label(draft['category'])}",
        parse_mode=ParseMode.HTML,
    )
    await log_admin_action(
        context.bot, update.effective_user.id,
        f"🛒 Added product #{pid} ({draft['category']}): {html.escape(draft['name'])}",
    )
    return ConversationHandler.END


async def cb_pm_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    context.user_data.pop("pm_draft", None)
    try:
        await query.message.reply_text("❌ Cancelled.")
    except TelegramError:
        pass
    return ConversationHandler.END


async def cb_pm_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_admin(update):
        return
    query = update.callback_query
    await query.answer()
    parts = query.data.split(":")
    category = parts[2] if len(parts) > 2 else "bot"
    try:
        page = max(0, int(parts[3]))
    except (IndexError, ValueError):
        page = 0
    per_page = 10
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT COUNT(*) FROM products WHERE category=? AND is_deleted=0", (category,)
        )
        total = (await cur.fetchone())[0]
        if total and page * per_page >= total:
            page = max(0, (total - 1) // per_page)
        cur = await db.execute(
            "SELECT * FROM products WHERE category=? AND is_deleted=0 "
            "ORDER BY product_id DESC LIMIT ? OFFSET ?",
            (category, per_page, page * per_page),
        )
        rows = await cur.fetchall()
    title = _category_label(category)
    text = f"🛒 <b>{title} Products</b>\n\nTotal: <b>{total}</b>\n\nSelect a product to manage:"
    buttons = []
    for r in rows:
        status = "✅" if r["is_active"] else "⛔"
        buttons.append([InlineKeyboardButton(
            f"{status} #{r['product_id']} {r['name']} — 🪙{r['price']}",
            callback_data=f"pm:view:{r['product_id']}", style="primary",
        )])
    if not rows:
        text += "\n\n<i>No products in this category yet.</i>"
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"pm:list:{category}:{page-1}", style="primary"))
    if (page + 1) * per_page < total:
        nav.append(InlineKeyboardButton("Next ➡", callback_data=f"pm:list:{category}:{page+1}", style="primary"))
    if nav:
        buttons.append(nav)
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="ad:products", style="primary")])
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_pm_view(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_admin(update):
        return
    query = update.callback_query
    await query.answer()
    try:
        pid = int(query.data.split(":")[2])
    except (IndexError, ValueError):
        await query.answer("❌ Invalid product.", show_alert=True)
        return
    product = await _get_product(pid)
    if not product:
        await query.answer("❌ Product not found.", show_alert=True)
        return
    text = _pm_review_text({
        "category": product["category"], "name": product["name"],
        "description": product["description"] or "", "price": product["price"],
        "preview_file_id": product["preview_file_id"],
        "attachment_file_id": product["attachment_file_id"],
        "attachment_name": product["attachment_name"],
        "is_active": product["is_active"],
    })
    text += f"\n\n🆔 Product ID: <code>{product['product_id']}</code>"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("🧩 Name", callback_data=f"pm:ef:name:{pid}", style="primary"),
         InlineKeyboardButton("📝 Description", callback_data=f"pm:ef:desc:{pid}", style="primary")],
        [InlineKeyboardButton("🪙 Price", callback_data=f"pm:ef:price:{pid}", style="primary"),
         InlineKeyboardButton("🖼 Preview", callback_data=f"pm:ef:preview:{pid}", style="primary")],
        [InlineKeyboardButton("📎 Attachment", callback_data=f"pm:ef:file:{pid}", style="primary"),
         InlineKeyboardButton("📌 Toggle Status", callback_data=f"pm:togglestatus:{pid}", style="primary")],
        [InlineKeyboardButton("🗑 Delete Product", callback_data=f"pm:del:{pid}", style="danger")],
        [InlineKeyboardButton("⬅ Back", callback_data=f"pm:list:{product['category']}:0", style="primary")],
    ])
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_pm_toggle_status(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_admin(update):
        return
    query = update.callback_query
    try:
        pid = int(query.data.split(":")[2])
    except (IndexError, ValueError):
        await query.answer("❌ Invalid product.", show_alert=True)
        return
    async with db_conn() as db:
        cur = await db.execute("SELECT is_active, name FROM products WHERE product_id=? AND is_deleted=0", (pid,))
        row = await cur.fetchone()
        if not row:
            await query.answer("❌ Product not found.", show_alert=True)
            return
        new_val = 0 if row[0] else 1
        await db.execute(
            "UPDATE products SET is_active=?, updated_at=? WHERE product_id=?",
            (new_val, datetime.utcnow().isoformat(), pid),
        )
        await db.commit()
    await query.answer("✅ Activated" if new_val else "⛔ Deactivated")
    await log_admin_action(
        context.bot, update.effective_user.id,
        f"{'✅ Activated' if new_val else '⛔ Deactivated'} product #{pid}",
    )
    await cb_pm_view(update, context)


async def cb_pm_delete_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_admin(update):
        return
    query = update.callback_query
    await query.answer()
    try:
        pid = int(query.data.split(":")[2])
    except (IndexError, ValueError):
        return
    product = await _get_product(pid)
    if not product:
        await query.answer("❌ Product not found.", show_alert=True)
        return
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Yes, Delete", callback_data=f"pm:delok:{pid}", style="danger"),
         InlineKeyboardButton("❌ No", callback_data=f"pm:view:{pid}", style="primary")],
    ])
    await query.edit_message_text(
        f"⚠️ <b>Delete Product?</b>\n\n🧩 {html.escape(product['name'])}\n🆔 #{pid}\n\n"
        "Historical purchases are preserved.",
        parse_mode=ParseMode.HTML, reply_markup=kb,
    )


async def cb_pm_delete_confirm(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_admin(update):
        return
    query = update.callback_query
    try:
        pid = int(query.data.split(":")[2])
    except (IndexError, ValueError):
        return
    async with db_conn() as db:
        cur = await db.execute("SELECT product_id FROM products WHERE product_id=? AND is_deleted=0", (pid,))
        if not await cur.fetchone():
            await query.answer("⚠️ Already deleted.", show_alert=True)
            return
        await db.execute(
            "UPDATE products SET is_deleted=1, is_active=0, updated_at=? WHERE product_id=?",
            (datetime.utcnow().isoformat(), pid),
        )
        await db.commit()
    await query.answer("🗑 Deleted")
    await query.edit_message_text("🗑 <b>Product deleted (history preserved).</b>", parse_mode=ParseMode.HTML)
    await log_admin_action(context.bot, update.effective_user.id, f"🗑 Deleted product #{pid}")


async def cb_pe_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await require_admin(update):
        return ConversationHandler.END
    query = update.callback_query
    await query.answer()
    parts = query.data.split(":")
    field, pid = parts[2], int(parts[3])
    product = await _get_product(pid)
    if not product:
        await query.answer("❌ Product not found.", show_alert=True)
        return ConversationHandler.END
    context.user_data["pe_pid"] = pid
    context.user_data["pe_field"] = field
    prompts = {
        "name": "📝 Enter the new product name:",
        "desc": "📝 Enter the new description (send - to clear):",
        "price": "🪙 Enter the new coin price (0 = free):",
    }
    await query.message.reply_text(prompts[field])
    return PE_VALUE


async def conv_pe_value(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    pid = context.user_data.pop("pe_pid", None)
    field = context.user_data.pop("pe_field", None)
    if pid is None or field is None:
        await update.message.reply_text("❌ Session expired.")
        return ConversationHandler.END
    value = update.message.text.strip()
    if field == "name":
        if not value or len(value) > 100:
            await update.message.reply_text("❌ Name must be 1-100 characters.")
            context.user_data["pe_pid"] = pid
            context.user_data["pe_field"] = field
            return PE_VALUE
        column = "name"
    elif field == "desc":
        column, value = "description", ("" if value == "-" else value)
    elif field == "price":
        if not value.isdigit():
            await update.message.reply_text("❌ Enter a valid non-negative number.")
            context.user_data["pe_pid"] = pid
            context.user_data["pe_field"] = field
            return PE_VALUE
        column, value = "price", int(value)
    else:
        await update.message.reply_text("❌ Unknown field.")
        return ConversationHandler.END
    await _apply_product_update(pid, {column: value})
    await update.message.reply_text("✅ Product updated.")
    return ConversationHandler.END


async def _apply_product_update(pid: int, fields: dict) -> bool:
    if not fields:
        return False
    allowed = {
        "name", "description", "price", "preview_file_id", "preview_file_unique_id",
        "attachment_file_id", "attachment_file_unique_id", "attachment_kind",
        "attachment_name", "attachment_size", "storage_chat_id", "storage_message_id", "is_active",
    }
    sets, values = [], []
    for key, val in fields.items():
        if key not in allowed:
            continue
        sets.append(f"{key}=?")
        values.append(val)
    if not sets:
        return False
    sets.append("updated_at=?")
    values.append(datetime.utcnow().isoformat())
    values.append(pid)
    try:
        async with db_conn() as db:
            await db.execute(f"UPDATE products SET {', '.join(sets)} WHERE product_id=?", values)
            await db.commit()
        return True
    except aiosqlite.Error:
        log.exception("Product update failed for #%s", pid)
        return False


async def cb_pe_preview_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await require_admin(update):
        return ConversationHandler.END
    query = update.callback_query
    await query.answer()
    try:
        pid = int(query.data.split(":")[3])
    except (IndexError, ValueError):
        return ConversationHandler.END
    context.user_data["pe_pid"] = pid
    await query.message.reply_text(
        "🖼 Send the new preview image, or choose an option:",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🗑 Remove Image", callback_data="pe:rmpreview", style="danger")],
            [InlineKeyboardButton("❌ Cancel", callback_data="pm:cancel", style="primary")],
        ]),
    )
    return PE_PREVIEW


async def conv_pe_preview(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    pid = context.user_data.pop("pe_pid", None)
    if pid is None:
        await update.message.reply_text("❌ Session expired.")
        return ConversationHandler.END
    if not update.message.photo:
        await update.message.reply_text("❌ Please send an image, or use the Remove button.")
        context.user_data["pe_pid"] = pid
        return PE_PREVIEW
    photo = update.message.photo[-1]
    ok = await _apply_product_update(pid, {
        "preview_file_id": photo.file_id,
        "preview_file_unique_id": photo.file_unique_id,
    })
    await update.message.reply_text("✅ Preview image updated." if ok else "❌ Failed to update image.")
    return ConversationHandler.END


async def cb_pe_remove_preview(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    pid = context.user_data.pop("pe_pid", None)
    if pid is None:
        await query.message.reply_text("❌ Session expired.")
        return ConversationHandler.END
    ok = await _apply_product_update(pid, {
        "preview_file_id": None, "preview_file_unique_id": None,
    })
    await query.message.reply_text("✅ Preview image removed." if ok else "❌ Failed to remove image.")
    return ConversationHandler.END


async def cb_pe_file_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await require_admin(update):
        return ConversationHandler.END
    query = update.callback_query
    await query.answer()
    try:
        pid = int(query.data.split(":")[3])
    except (IndexError, ValueError):
        return ConversationHandler.END
    context.user_data["pe_pid"] = pid
    await query.message.reply_text(
        "📎 Send the new attachment, or choose an option:",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🗑 Remove File", callback_data="pe:rmfile", style="danger")],
            [InlineKeyboardButton("❌ Cancel", callback_data="pm:cancel", style="primary")],
        ]),
    )
    return PE_FILE


async def conv_pe_file(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    pid = context.user_data.pop("pe_pid", None)
    if pid is None:
        await update.message.reply_text("❌ Session expired.")
        return ConversationHandler.END
    msg = update.message
    kind = None
    tg_file = None
    name = None
    size = 0
    if msg.document:
        kind, tg_file = "document", msg.document
        name, size = tg_file.file_name or "file", tg_file.file_size or 0
    elif msg.video:
        kind, tg_file = "video", msg.video
        name, size = tg_file.file_name or "video.mp4", tg_file.file_size or 0
    elif msg.audio:
        kind, tg_file = "audio", msg.audio
        name, size = tg_file.file_name or "audio.mp3", tg_file.file_size or 0
    elif msg.photo:
        tg_file, kind = msg.photo[-1], "photo"
        name, size = f"photo_{tg_file.file_unique_id}.jpg", tg_file.file_size or 0
    elif msg.voice:
        kind, tg_file = "voice", msg.voice
        name, size = f"voice_{tg_file.file_unique_id}.ogg", tg_file.file_size or 0
    elif msg.animation:
        kind, tg_file = "animation", msg.animation
        name, size = tg_file.file_name or "animation.mp4", tg_file.file_size or 0
    if not tg_file:
        await update.message.reply_text("❌ Unsupported attachment. Send a supported file, or use Remove.")
        context.user_data["pe_pid"] = pid
        return PE_FILE
    channel_id, channel_msg_id, store_err = await store_product_in_channel(
        context.bot, update.effective_chat.id, msg.message_id,
        name or "product",
    )
    ok = await _apply_product_update(pid, {
        "attachment_file_id": tg_file.file_id,
        "attachment_file_unique_id": tg_file.file_unique_id,
        "attachment_kind": kind,
        "attachment_name": name,
        "attachment_size": size,
        "storage_chat_id": channel_id,
        "storage_message_id": channel_msg_id,
    })
    if not ok:
        await update.message.reply_text("❌ Failed to update attachment.")
    elif store_err == "not_configured":
        await update.message.reply_text(
            "✅ Attachment updated (local).\n⚠️ Storage channel set nahi hai — Admin Panel → 📦 Storage Channel me set karo."
        )
    elif store_err:
        await update.message.reply_text(
            f"✅ Attachment updated (local).\n⚠️ Channel upload failed: {html.escape(store_err)}"
        )
    else:
        await update.message.reply_text("✅ Attachment updated and saved in storage channel.")
    return ConversationHandler.END


async def cb_pe_remove_file(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    pid = context.user_data.pop("pe_pid", None)
    if pid is None:
        await query.message.reply_text("❌ Session expired.")
        return ConversationHandler.END
    ok = await _apply_product_update(pid, {
        "attachment_file_id": None, "attachment_file_unique_id": None,
        "attachment_kind": None, "attachment_name": None, "attachment_size": 0,
        "storage_chat_id": None, "storage_message_id": None,
    })
    await query.message.reply_text("✅ Attachment removed." if ok else "❌ Failed to remove attachment.")
    return ConversationHandler.END


# ---------------------------------------------------------------------------
# Admin: Coin Package Manager
# ---------------------------------------------------------------------------

async def cb_admin_economy(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_admin(update):
        return
    if update.callback_query:
        await update.callback_query.answer()
    reward = await get_setting("referral_reward", "1")
    enabled = (await get_setting("referral_reward_enabled", "1")) == "1"
    leaderboard = (await get_setting("leaderboard_enabled", "1")) == "1"
    async with db_conn() as db:
        cur = await db.execute("SELECT COALESCE(SUM(coins),0) FROM wallet")
        total_wallet = (await cur.fetchone())[0]
        cur = await db.execute("SELECT COALESCE(SUM(amount),0) FROM transactions WHERE amount > 0")
        issued = (await cur.fetchone())[0]
        cur = await db.execute("SELECT COALESCE(SUM(amount),0) FROM transactions WHERE amount < 0")
        spent = abs((await cur.fetchone())[0])
        cur = await db.execute(
            "SELECT COALESCE(SUM(reward),0) FROM referrals"
        )
        ref_rewards = (await cur.fetchone())[0]
    text = (
        "💹 <b>Economy Manager</b>\n"
        f"{DIVIDER}\n"
        f"👛 Coins in Wallets: <b>{total_wallet}</b>\n"
        f"📈 Coins Issued (lifetime): <b>{issued}</b>\n"
        f"📉 Coins Spent (lifetime): <b>{spent}</b>\n"
        f"🚀 Referral Rewards Issued: <b>{ref_rewards}</b>\n"
        f"{DIVIDER}\n"
        f"🎁 Reward per Referral: <b>{reward}</b> coins\n"
        f"🚀 Referral Rewards: <b>{'ON' if enabled else 'OFF'}</b>\n"
        f"🏆 Leaderboard: <b>{'ON' if leaderboard else 'OFF'}</b>"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✏️ Change Referral Reward", callback_data="eco:refreward", style="primary")],
        [InlineKeyboardButton("🚀 Rewards ON", callback_data="eco:refon", style="success"),
         InlineKeyboardButton("⛔ Rewards OFF", callback_data="eco:refoff", style="danger")],
        [InlineKeyboardButton("🏆 Leaderboard ON", callback_data="eco:lbon", style="success"),
         InlineKeyboardButton("⛔ Leaderboard OFF", callback_data="eco:lboff", style="danger")],
        [InlineKeyboardButton("➕ Add Coins", callback_data="wm:add", style="primary"),
         InlineKeyboardButton("➖ Deduct Coins", callback_data="wm:remove", style="primary")],
        [InlineKeyboardButton("📜 Wallet History", callback_data="wm:history", style="primary")],
        [InlineKeyboardButton("⬅ Back", callback_data="ad:home", style="primary")],
    ])
    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_eco_refreward_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await require_admin(update):
        return ConversationHandler.END
    query = update.callback_query
    await query.answer()
    current = await get_setting("referral_reward", "1")
    await query.message.reply_text(
        f"✏️ Current referral reward: <b>{html.escape(current)}</b> coins\n\n"
        "Send the new reward amount (non-negative whole number):",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="pm:cancel", style="danger")]]),
    )
    return ECO_REWARD


async def conv_eco_reward(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await update.message.reply_text("❌ Please enter a non-negative whole number.")
        return ECO_REWARD
    await set_setting("referral_reward", str(int(text)))
    await update.message.reply_text(f"✅ Referral reward updated to <b>{int(text)}</b> coins.", parse_mode=ParseMode.HTML)
    await log_admin_action(
        context.bot, update.effective_user.id,
        f"🚀 Changed referral reward to {int(text)} coins",
    )
    return ConversationHandler.END


async def cb_eco_toggle(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_admin(update):
        return
    query = update.callback_query
    await query.answer()
    data = query.data
    if data == "eco:refon":
        await set_setting("referral_reward_enabled", "1")
        msg = "✅ Referral rewards enabled."
    elif data == "eco:refoff":
        await set_setting("referral_reward_enabled", "0")
        msg = "⛔ Referral rewards disabled."
    elif data == "eco:lbon":
        await set_setting("leaderboard_enabled", "1")
        msg = "✅ Leaderboard enabled."
    else:
        await set_setting("leaderboard_enabled", "0")
        msg = "⛔ Leaderboard disabled."
    await query.answer(msg, show_alert=False)
    await log_admin_action(context.bot, update.effective_user.id, msg)
    await cb_admin_economy(update, context)


async def cb_admin_referrals(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_admin(update):
        return
    if update.callback_query:
        await update.callback_query.answer()
    reward = await get_setting("referral_reward", "1")
    enabled = (await get_setting("referral_reward_enabled", "1")) == "1"
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT COUNT(*) FROM referrals")
        total = (await cur.fetchone())[0]
        cur = await db.execute("SELECT COALESCE(SUM(reward),0) FROM referrals")
        total_reward = (await cur.fetchone())[0]
        cur = await db.execute(
            "SELECT referrer_id, COUNT(*) AS cnt, COALESCE(SUM(reward),0) AS coins "
            "FROM referrals GROUP BY referrer_id ORDER BY cnt DESC LIMIT 5"
        )
        top = await cur.fetchall()
        cur = await db.execute(
            "SELECT * FROM referrals ORDER BY id DESC LIMIT 10"
        )
        recent = await cur.fetchall()
    lines = [
        "🚀 <b>Referral Manager</b>\n" + DIVIDER,
        f"👥 Total Valid Referrals: <b>{total}</b>",
        f"🪙 Total Rewards Issued: <b>{total_reward}</b>",
        f"🎁 Current Reward: <b>{reward}</b> coins",
        f"Status: <b>{'ON' if enabled else 'OFF'}</b>",
        DIVIDER,
        "🏆 <b>Top Referrers</b>",
    ]
    if not top:
        lines.append("No referrals yet.")
    for i, r in enumerate(top):
        u = await get_user_row(r["referrer_id"])
        label = f"@{u['username']}" if u and u["username"] else (u["first_name"] if u else str(r["referrer_id"]))
        lines.append(f"{i+1}. {html.escape(label or '—')} — {r['cnt']} referrals ({r['coins']} coins)")
    lines.append(DIVIDER)
    lines.append("🕘 <b>Recent Referrals</b>")
    if not recent:
        lines.append("None.")
    for r in recent:
        u = await get_user_row(r["new_user_id"])
        label = f"@{u['username']}" if u and u["username"] else (u["first_name"] if u else str(r["new_user_id"]))
        lines.append(f"• {html.escape(str(r['referrer_id']))} → {html.escape(label or '—')} (+{r['reward']})")
    text = "\n".join(lines)
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✏️ Change Reward", callback_data="eco:refreward", style="primary")],
        [InlineKeyboardButton("🚀 ON", callback_data="eco:refon", style="success"),
         InlineKeyboardButton("⛔ OFF", callback_data="eco:refoff", style="danger")],
        [InlineKeyboardButton("⬅ Back", callback_data="ad:home", style="primary")],
    ])
    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_admin_upload_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return ConversationHandler.END
    if update.callback_query:
        await update.callback_query.answer()
    await update.effective_message.reply_text(
        "📤 <b>Upload File</b>\n\nSend me the file you want to add to the store.",
        parse_mode=ParseMode.HTML,
    )
    return UP_FILE


async def conv_upload_file(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    msg = update.message
    kind = None
    tg_file = None
    file_name = None
    file_size = 0

    if msg.document:
        kind, tg_file = "document", msg.document
        file_name, file_size = tg_file.file_name or "file", tg_file.file_size or 0
    elif msg.video:
        kind, tg_file = "video", msg.video
        file_name = tg_file.file_name or f"video_{tg_file.file_unique_id}.mp4"
        file_size = tg_file.file_size or 0
    elif msg.audio:
        kind, tg_file = "audio", msg.audio
        file_name = tg_file.file_name or f"audio_{tg_file.file_unique_id}.mp3"
        file_size = tg_file.file_size or 0
    elif msg.photo:
        tg_file = msg.photo[-1]
        kind = "photo"
        file_name = f"photo_{tg_file.file_unique_id}.jpg"
        file_size = tg_file.file_size or 0
    elif msg.voice:
        kind, tg_file = "voice", msg.voice
        file_name = f"voice_{tg_file.file_unique_id}.ogg"
        file_size = tg_file.file_size or 0
    elif msg.animation:
        kind, tg_file = "animation", msg.animation
        file_name = tg_file.file_name or f"gif_{tg_file.file_unique_id}.mp4"
        file_size = tg_file.file_size or 0
    else:
        await msg.reply_text("❌ Unsupported file type. Please send a valid file.")
        return UP_FILE

    context.user_data["up_kind"] = kind
    context.user_data["up_file_id"] = tg_file.file_id
    context.user_data["up_unique_id"] = tg_file.file_unique_id
    context.user_data["up_orig_name"] = file_name
    context.user_data["up_size"] = file_size

    await msg.reply_text(
        f"✅ File received ({fmt_size(file_size)}).\n\n📝 Enter File Name (or send - to use original filename):"
    )
    return UP_NAME


async def conv_upload_name(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    name = context.user_data["up_orig_name"] if text == "-" else text
    context.user_data["up_name"] = name
    await update.message.reply_text("📄 Enter Description (or send - to skip):")
    return UP_DESC


async def conv_upload_desc(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    context.user_data["up_desc"] = "" if text == "-" else text
    await update.message.reply_text("💰 Enter Coin Price (0 = FREE):\n\nExample: 0, 50, 100, 250, 500, 1000")
    return UP_PRICE


async def conv_upload_price(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await update.message.reply_text("❌ Please enter a valid number.")
        return UP_PRICE
    context.user_data["up_price"] = int(text)
    return await show_upload_preview(update, context)


async def show_upload_preview(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    d = context.user_data
    text = (
        "👀 <b>Preview</b>\n\n"
        f"🛒 File Name: {html.escape(d['up_name'])}\n"
        f"📦 File Size: {fmt_size(d['up_size'])}\n"
        f"📄 Description: {html.escape(d['up_desc']) if d['up_desc'] else '—'}\n"
        f"💰 Coin Price: {d['up_price']}\n"
        f"📅 Upload Date: {fmt_date(datetime.utcnow().isoformat())}"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Publish", callback_data="up:publish", style="primary"),
         InlineKeyboardButton("✏ Edit", callback_data="up:edit", style="primary")],
        [InlineKeyboardButton("❌ Cancel", callback_data="up:cancel", style="primary")],
    ])
    await update.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    return UP_PREVIEW


async def cb_upload_publish(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    d = context.user_data
    user = update.effective_user
    async with db_conn() as db:
        await db.execute(
            "INSERT INTO files (tg_file_id, tg_file_unique_id, file_kind, file_name, file_size, "
            "description, price, upload_date, uploaded_by) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (d["up_file_id"], d["up_unique_id"], d["up_kind"], d["up_name"], d["up_size"],
             d["up_desc"], d["up_price"], datetime.utcnow().isoformat(), user.id),
        )
        await db.commit()
    await query.edit_message_text("✅ <b>File Published Successfully!</b>", parse_mode=ParseMode.HTML)
    for key in ["up_kind", "up_file_id", "up_unique_id", "up_orig_name", "up_size", "up_name", "up_desc", "up_price"]:
        context.user_data.pop(key, None)
    return ConversationHandler.END


async def cb_upload_edit(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.message.reply_text("📝 Enter File Name (or send - to use original filename):")
    return UP_NAME


async def cb_upload_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.edit_message_text("❌ Upload cancelled.")
    for key in ["up_kind", "up_file_id", "up_unique_id", "up_orig_name", "up_size", "up_name", "up_desc", "up_price"]:
        context.user_data.pop(key, None)
    return ConversationHandler.END



async def cb_admin_managefiles(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    if update.callback_query:
        await update.callback_query.answer()
    await send_manage_files_list(update, context, page=0)


async def send_manage_files_list(update: Update, context: ContextTypes.DEFAULT_TYPE, page: int) -> None:
    viewer_id = update.effective_user.id
    is_owner = viewer_id == OWNER_ID
    per_page = 8
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        if is_owner:
            cur = await db.execute(
                "SELECT file_pk, file_name, price, downloads_count FROM files WHERE is_deleted=0 "
                "ORDER BY file_pk DESC LIMIT ? OFFSET ?",
                (per_page, page * per_page),
            )
        else:
            cur = await db.execute(
                "SELECT file_pk, file_name, price, downloads_count FROM files WHERE is_deleted=0 AND uploaded_by=? "
                "ORDER BY file_pk DESC LIMIT ? OFFSET ?",
                (viewer_id, per_page, page * per_page),
            )
        rows = await cur.fetchall()

    text = "📂 <b>Manage Files</b>\n\n"
    text += "Select a file to edit or delete:" if is_owner else "Files you've uploaded — select one to edit or delete:"
    buttons = []
    for r in rows:
        buttons.append([InlineKeyboardButton(
            f"📄 {r['file_name']} ({r['downloads_count']}⬇)", callback_data=f"mf:view:{r['file_pk']}:{page}"
        , style="primary")])
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"mf:list:{page-1}", style="primary"))
    if len(rows) == per_page:
        nav.append(InlineKeyboardButton("Next ➡", callback_data=f"mf:list:{page+1}", style="primary"))
    if nav:
        buttons.append(nav)
    buttons.append([InlineKeyboardButton("🔍 Search Files", callback_data="mf:searchstart", style="primary")])
    buttons.append([InlineKeyboardButton("⬅ Back to Admin Panel", callback_data="ad:home", style="primary")])

    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_mf_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    page = int(query.data.split(":")[2])
    await send_manage_files_list(update, context, page)


async def cb_mf_search_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.message.reply_text("🔍 Enter a keyword to search your files by name:")
    return MF_SEARCH


async def conv_mf_search(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    keyword = update.message.text.strip()
    viewer_id = update.effective_user.id
    is_owner = viewer_id == OWNER_ID
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        if is_owner:
            cur = await db.execute(
                "SELECT file_pk, file_name FROM files WHERE is_deleted=0 AND file_name LIKE ? LIMIT 15",
                (f"%{keyword}%",),
            )
        else:
            cur = await db.execute(
                "SELECT file_pk, file_name FROM files WHERE is_deleted=0 AND uploaded_by=? AND file_name LIKE ? LIMIT 15",
                (viewer_id, f"%{keyword}%"),
            )
        rows = await cur.fetchall()

    if not rows:
        await update.message.reply_text("❌ No files matched that keyword.")
        return ConversationHandler.END

    buttons = [[InlineKeyboardButton(f"📄 {r['file_name']}", callback_data=f"mf:view:{r['file_pk']}:0", style="primary")] for r in rows]
    await update.message.reply_text(
        f"🔍 Found <b>{len(rows)}</b> matching file(s):", parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup(buttons),
    )
    return ConversationHandler.END


async def cb_mf_view(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    _, _, file_pk, page = query.data.split(":")
    await _render_mf_view(update, int(file_pk), int(page))


async def _render_mf_view(update: Update, file_pk: int, page: int) -> None:
    query = update.callback_query
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM files WHERE file_pk=?", (file_pk,))
        f = await cur.fetchone()
    if not f:
        await query.edit_message_text("❌ File not found.")
        return
    if update.effective_user.id != OWNER_ID and f["uploaded_by"] != update.effective_user.id:
        await query.edit_message_text("🚫 You can only manage files you uploaded.")
        return
    text = (
        f"📄 <b>{html.escape(f['file_name'])}</b>\n\n"
        f"📦 Size: {fmt_size(f['file_size'])}\n"
        f"📄 Description: {html.escape(f['description']) if f['description'] else '—'}\n"
        f"💰 Price: {f['price']} coins\n"
        f"⬇ Downloads: {f['downloads_count']}\n"
        f"📌 Featured: {'Yes' if f['featured'] else 'No'}\n"
        f"📅 Uploaded: {fmt_date(f['upload_date'])}"
    )
    feature_label = "📌 Unfeature" if f["featured"] else "📌 Make Featured"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✏️ Edit Name", callback_data=f"mf:ename:{file_pk}", style="primary"),
         InlineKeyboardButton("✏️ Edit Desc", callback_data=f"mf:edesc:{file_pk}", style="primary")],
        [InlineKeyboardButton("✏️ Edit Price", callback_data=f"mf:eprice:{file_pk}", style="primary")],
        [InlineKeyboardButton(feature_label, callback_data=f"mf:tfeat:{file_pk}:{page}", style="primary")],
        [InlineKeyboardButton("🗑 Delete File", callback_data=f"mf:delete:{file_pk}", style="primary")],
        [InlineKeyboardButton("⬅ Back", callback_data=f"mf:list:{page}", style="primary")],
    ])
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_mf_toggle_featured(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    _, _, file_pk, page = query.data.split(":")
    file_pk = int(file_pk)
    if not await _can_manage_file(update.effective_user.id, file_pk):
        await query.answer("🚫 You can only manage files you uploaded.", show_alert=True)
        return
    async with db_conn() as db:
        cur = await db.execute("SELECT featured FROM files WHERE file_pk=?", (file_pk,))
        row = await cur.fetchone()
        new_val = 0 if (row and row[0]) else 1
        await db.execute("UPDATE files SET featured=? WHERE file_pk=?", (new_val, file_pk))
        await db.commit()
    await query.answer("📌 Featured!" if new_val else "Unfeatured")
    await _render_mf_view(update, file_pk, int(page))


async def _can_manage_file(user_id: int, file_pk: int) -> bool:
    if user_id == OWNER_ID:
        return True
    async with db_conn() as db:
        cur = await db.execute("SELECT uploaded_by FROM files WHERE file_pk=?", (file_pk,))
        row = await cur.fetchone()
        return bool(row and row[0] == user_id)


async def cb_mf_edit_field(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    _, field, file_pk = query.data.split(":")
    file_pk = int(file_pk)
    if not await _can_manage_file(update.effective_user.id, file_pk):
        await query.answer("🚫 You can only manage files you uploaded.", show_alert=True)
        return ConversationHandler.END
    await query.answer()
    context.user_data["ef_file_pk"] = file_pk
    context.user_data["ef_field"] = field
    prompts = {
        "ename": "📝 Enter new File Name:",
        "edesc": "📄 Enter new Description:",
        "eprice": "💰 Enter new Coin Price:",
    }
    if field not in prompts:
        await query.answer("❌ Unknown field.", show_alert=True)
        return ConversationHandler.END
    await query.message.reply_text(prompts[field], parse_mode=ParseMode.HTML)
    return EF_FIELD


async def conv_edit_field_value(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    field = context.user_data.pop("ef_field")
    file_pk = context.user_data.pop("ef_file_pk")
    value = update.message.text.strip()

    column_map = {"ename": "file_name", "edesc": "description", "eprice": "price"}
    if field not in column_map:
        await update.message.reply_text("❌ Unknown field.")
        return ConversationHandler.END
    column = column_map[field]

    if field == "eprice":
        if not value.isdigit():
            await update.message.reply_text("❌ Please enter a valid number.")
            context.user_data["ef_field"] = field
            context.user_data["ef_file_pk"] = file_pk
            return EF_FIELD
        value = int(value)

    async with db_conn() as db:
        await db.execute(f"UPDATE files SET {column}=? WHERE file_pk=?", (value, file_pk))
        await db.commit()

    await update.message.reply_text("✅ File updated successfully.")
    return ConversationHandler.END


async def cb_mf_delete(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    file_pk = int(query.data.split(":")[2])
    if not await _can_manage_file(update.effective_user.id, file_pk):
        await query.answer("🚫 You can only manage files you uploaded.", show_alert=True)
        return
    await query.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Yes, Delete", callback_data=f"mf:delconfirm:{file_pk}", style="primary"),
         InlineKeyboardButton("❌ No", callback_data=f"mf:view:{file_pk}:0", style="primary")],
    ])
    await query.edit_message_text("⚠️ Are you sure you want to delete this file?", reply_markup=kb)


async def cb_mf_delete_confirm(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    file_pk = int(query.data.split(":")[2])
    if not await _can_manage_file(update.effective_user.id, file_pk):
        await query.answer("🚫 You can only manage files you uploaded.", show_alert=True)
        return
    async with db_conn() as db:
        await db.execute("UPDATE files SET is_deleted=1 WHERE file_pk=?", (file_pk,))
        await db.commit()
    await query.answer("🗑 Deleted")
    await query.edit_message_text("🗑 <b>File deleted successfully.</b>", parse_mode=ParseMode.HTML)



async def cb_admin_fcmgr(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_owner(update):
        return
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ Add Channel", callback_data="fc:add", style="primary"),
         InlineKeyboardButton("➖ Remove Channel", callback_data="fc:remove", style="primary")],
        [InlineKeyboardButton("📋 Channel List", callback_data="fc:list", style="primary")],
        [InlineKeyboardButton("⬅ Back", callback_data="ad:home", style="primary")],
    ])
    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.edit_message_text("📡 <b>Force Channel Manager</b>", parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text("📡 <b>Force Channel Manager</b>", parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_fc_add_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await require_owner(update):
        return ConversationHandler.END
    query = update.callback_query
    await query.answer()
    await query.message.reply_text(
        "➕ <b>Add Force-Join Channel/Group</b>\n\n"
        "Send either:\n"
        "• A public <b>@username</b>\n"
        "• Or a <b>https://t.me/username</b> link\n\n"
        "I need to already be a <b>member</b> of it — admin rights aren't required.",
        parse_mode=ParseMode.HTML,
    )
    return FC_ADD


async def conv_fc_add(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    msg = update.message
    try:
        text = (msg.text or "").strip()
        username = None

        if text.startswith("@") and re.match(r"^@[A-Za-z0-9_]{5,32}$", text):
            username = text
        else:
            m = re.match(r"^https?://t\.me/([A-Za-z0-9_]{5,32})/?$", text)
            if m:
                username = f"@{m.group(1)}"

        if not username:
            await msg.reply_text("❌ Please send a valid @username or a https://t.me/username link.")
            return FC_ADD

        try:
            chat = await context.bot.get_chat(username)
        except TelegramError as e:
            await msg.reply_text(
                f"❌ Couldn't find that channel/group ({html.escape(str(e))}).\n"
                "Make sure the username is correct and I've already been added to it.",
                parse_mode=ParseMode.HTML,
            )
            return FC_ADD

        try:
            me = await context.bot.get_me()
            member = await context.bot.get_chat_member(chat.id, me.id)
            if member.status in ("left", "kicked"):
                await msg.reply_text("❌ I'm not currently a member of that chat. Please add me first, then try again.")
                return FC_ADD
        except TelegramError as e:
            await msg.reply_text(
                f"❌ I can't access that chat's member list ({html.escape(str(e))}).\n"
                "Please make sure I've been added to it.",
                parse_mode=ParseMode.HTML,
            )
            return FC_ADD

        resolved_username = f"@{chat.username}" if chat.username else username
        await _save_force_channel(chat.id, resolved_username, chat.title, str(chat.type))
        await msg.reply_text(f"✅ Added: <b>{html.escape(chat.title)}</b>", parse_mode=ParseMode.HTML)
        return ConversationHandler.END

    except Exception as e:
        log.exception("Unexpected error in conv_fc_add")
        await msg.reply_text(
            f"⚠️ <b>Something went wrong adding this channel.</b>\n<code>{html.escape(str(e))}</code>\n\n"
            "This has been logged — please share this exact message so it can be fixed.",
            parse_mode=ParseMode.HTML,
        )
        return ConversationHandler.END


async def _save_force_channel(chat_id: int, username: str, title: str, chat_type: str) -> None:
    async with db_conn() as db:
        await db.execute(
            "INSERT INTO force_channels (username, chat_id, title, chat_type, added_date) "
            "VALUES (?, ?, ?, ?, ?) ON CONFLICT(username) DO UPDATE SET "
            "chat_id=excluded.chat_id, title=excluded.title, chat_type=excluded.chat_type",
            (username, chat_id, title, chat_type, datetime.utcnow().isoformat()),
        )
        await db.commit()


async def cb_fc_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    channels = await list_force_channels()
    if not channels:
        text = "📋 <b>Channel List</b>\n\nNo channels added yet."
    else:
        lines = ["📋 <b>Channel List</b>\n"]
        for ch in channels:
            lines.append(f"• <b>{html.escape(ch['title'])}</b> — added {fmt_date(ch['added_date'])}")
        text = "\n".join(lines)
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=back_button("ad:fcmgr"))


async def cb_fc_remove_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    channels = await list_force_channels()
    if not channels:
        await query.edit_message_text("No channels to remove.", reply_markup=back_button("ad:fcmgr"))
        return
    buttons = [[InlineKeyboardButton(f"➖ {ch['title']}", callback_data=f"fc:rm:{ch['id']}", style="primary")] for ch in channels]
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="ad:fcmgr", style="primary")])
    await query.edit_message_text("➖ Select a channel to remove:", reply_markup=InlineKeyboardMarkup(buttons))


async def cb_fc_remove_confirm(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    ch_id = int(query.data.split(":")[2])
    async with db_conn() as db:
        await db.execute("DELETE FROM force_channels WHERE id=?", (ch_id,))
        await db.commit()
    await query.answer("➖ Removed")
    await cb_fc_remove_menu(update, context)



async def cb_admin_walletmgr(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    is_owner = update.effective_user.id == OWNER_ID
    rows = [
        [InlineKeyboardButton("➕ Add Coins", callback_data="wm:add", style="primary"),
         InlineKeyboardButton("➖ Remove Coins", callback_data="wm:remove", style="primary")],
        [InlineKeyboardButton("♻ Reset Coins", callback_data="wm:reset", style="primary")],
    ]
    if is_owner:
        rows.append([InlineKeyboardButton("🎯 Set Exact Balance", callback_data="wm:setbal", style="primary")])
        rows.append([InlineKeyboardButton("👥 Bulk Manage Users", callback_data="wm:bulk", style="primary")])
    rows.append([InlineKeyboardButton("📜 Wallet History", callback_data="wm:history", style="primary")])
    rows.append([InlineKeyboardButton("⬅ Back", callback_data="ad:home", style="primary")])
    kb = InlineKeyboardMarkup(rows)
    text = "💰 <b>Wallet Manager</b>\n\nEnter a User ID to manage their wallet, or view recent history."
    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_wm_action_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    action = query.data.split(":")[1]
    if action == "setbal" and not await require_owner(update):
        return ConversationHandler.END
    await query.answer()
    context.user_data["wm_action"] = action
    await query.message.reply_text("👤 Enter the target User ID:")
    return UM_SEARCH


async def conv_wm_user_id(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await update.message.reply_text("❌ Please send a valid numeric User ID.")
        return UM_SEARCH
    target_id = int(text)
    row = await get_user_row(target_id)
    if not row:
        await update.message.reply_text("❌ User not found.")
        return ConversationHandler.END
    context.user_data["wm_target"] = target_id
    action = context.user_data["wm_action"]
    if action == "reset":
        async with db_conn() as db:
            await db.execute("UPDATE wallet SET coins=0 WHERE user_id=?", (target_id,))
            await db.execute(
                "INSERT INTO transactions (user_id, tx_type, amount, description, timestamp) VALUES (?, ?, ?, ?, ?)",
                (target_id, "admin_reset", 0, "Admin reset wallet to 0", datetime.utcnow().isoformat()),
            )
            await db.commit()
        await update.message.reply_text(f"♻ Wallet reset to 0 for user {target_id}.")
        await log_admin_action(context.bot, update.effective_user.id, f"♻ Reset wallet to 0 for user {target_id}")
        return ConversationHandler.END

    if action == "setbal":
        await update.message.reply_text("🎯 Enter the exact balance to set:")
        return UM_AMOUNT

    await update.message.reply_text("🪙 Enter the amount:")
    return UM_AMOUNT


async def conv_wm_amount(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    action = context.user_data.get("wm_action")
    min_ok = 0 if action == "setbal" else 1
    if not text.isdigit() or int(text) < min_ok:
        await update.message.reply_text("❌ Please enter a valid number." if action == "setbal" else "❌ Please enter a valid positive number.")
        return UM_AMOUNT
    amount = int(text)
    target_id = context.user_data.pop("wm_target")
    action = context.user_data.pop("wm_action")

    if action == "setbal":
        async with db_conn() as db:
            await db.execute(
                "INSERT INTO wallet (user_id, coins) VALUES (?, ?) ON CONFLICT(user_id) DO UPDATE SET coins=excluded.coins",
                (target_id, amount),
            )
            await db.execute(
                "INSERT INTO transactions (user_id, tx_type, amount, description, timestamp) VALUES (?, ?, ?, ?, ?)",
                (target_id, "admin_setbal", amount, f"Admin set exact balance to {amount}", datetime.utcnow().isoformat()),
            )
            await db.commit()
        await update.message.reply_text(f"🎯 Balance for user {target_id} set to {amount} coins.")
        await log_admin_action(context.bot, update.effective_user.id, f"🎯 Set exact balance for user {target_id} to {amount} coins")
        return ConversationHandler.END

    if action == "add":
        new_bal = await add_coins(target_id, amount, "admin_gift", f"Admin added {amount} coins")
        await update.message.reply_text(f"✅ Added {amount} coins. New balance: {new_bal}")
        await log_admin_action(context.bot, update.effective_user.id, f"➕ Added {amount} coins to user {target_id}")
        try:
            await context.bot.send_message(target_id, f"🎁 <b>{amount} Coins</b> have been added to your wallet by admin!", parse_mode=ParseMode.HTML)
        except TelegramError:
            pass
    else:
        ok = await remove_coins(target_id, amount, "admin_deduct", f"Admin removed {amount} coins")
        if ok:
            await update.message.reply_text(f"✅ Removed {amount} coins.")
            await log_admin_action(context.bot, update.effective_user.id, f"➖ Removed {amount} coins from user {target_id}")
        else:
            await update.message.reply_text("❌ User doesn't have enough coins to remove that amount.")
    return ConversationHandler.END


async def cb_wm_bulk_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await require_owner(update):
        return ConversationHandler.END
    query = update.callback_query
    await query.answer()
    await query.message.reply_text(
        "👥 <b>Bulk Manage Users</b>\n\n"
        "Send the target users separated by space, comma, or a new line — "
        "numeric User IDs, @usernames, or a mix of both:\n"
        "<code>111 222 @alice @bob</code>",
        parse_mode=ParseMode.HTML,
    )
    return WB_IDS


async def conv_wm_bulk_ids(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    raw = update.message.text.strip()
    tokens = [tok for tok in re.split(r"[\s,]+", raw) if tok]
    if not tokens:
        await update.message.reply_text("❌ Please send at least one User ID or @username.")
        return WB_IDS

    resolved: list[int] = []
    not_found: list[str] = []

    async with db_conn() as db:
        for tok in tokens:
            if tok.startswith("@"):
                uname = tok.lstrip("@")
                cur = await db.execute("SELECT user_id FROM users WHERE username=?", (uname,))
                row = await cur.fetchone()
                if row:
                    resolved.append(row[0])
                else:
                    not_found.append(tok)
            elif tok.isdigit():
                resolved.append(int(tok))
            else:
                not_found.append(tok)

    if not resolved:
        await update.message.reply_text(
            "❌ None of those could be resolved to a real user. Check the IDs/usernames and try again."
        )
        return WB_IDS

    context.user_data["wb_ids"] = resolved
    msg = f"✅ Resolved <b>{len(resolved)}</b> users.\n\nWhat should be applied to all of them?"
    if not_found:
        msg += f"\n\n⚠️ Not found (skipped): {', '.join(not_found[:15])}"
        if len(not_found) > 15:
            msg += f" (+{len(not_found) - 15} more)"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ Add Coins", callback_data="wb:add", style="primary"),
         InlineKeyboardButton("➖ Remove Coins", callback_data="wb:remove", style="primary")],
        [InlineKeyboardButton("🚫 Ban All", callback_data="wb:ban", style="primary"),
         InlineKeyboardButton("✅ Unban All", callback_data="wb:unban", style="primary")],
        [InlineKeyboardButton("👑 Give Premium", callback_data="wb:premium", style="primary")],
        [InlineKeyboardButton("❌ Cancel", callback_data="wb:cancel", style="primary")],
    ])
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=kb)
    return WB_ACTION


async def cb_wb_action_coins(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    context.user_data["wb_coin_action"] = "add" if query.data == "wb:add" else "remove"
    verb = "add to" if query.data == "wb:add" else "remove from"
    await query.message.reply_text(f"🪙 Enter the coin amount to {verb} all {len(context.user_data['wb_ids'])} users:")
    return WB_AMOUNT


async def conv_wm_bulk_amount(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit() or int(text) <= 0:
        await update.message.reply_text("❌ Please enter a valid positive number.")
        return WB_AMOUNT
    amount = int(text)
    target_ids = context.user_data.pop("wb_ids")
    action = context.user_data.pop("wb_coin_action")
    is_add = action == "add"

    verb = "Adding" if is_add else "Removing"
    status_msg = await update.message.reply_text(f"⏳ {verb} {amount} coins for {len(target_ids)} users...")
    ok_list: list[int] = []
    skipped: list[int] = []

    async def process_one(uid: int) -> None:
        row = await get_user_row(uid)
        if not row:
            skipped.append(uid)
            return
        if is_add:
            await add_coins(uid, amount, "admin_gift", f"Bulk admin gift: {amount} coins")
            success = True
        else:
            success = await remove_coins(uid, amount, "admin_deduct", f"Bulk admin deduct: {amount} coins")
        if not success:
            skipped.append(uid)
            return
        ok_list.append(uid)
        await TELEGRAM_SEND_LIMITER.acquire()
        try:
            verb_msg = f"🎁 <b>{amount} Coins</b> have been added to your wallet by admin!" if is_add \
                else f"⚠️ <b>{amount} Coins</b> have been deducted from your wallet by admin."
            await context.bot.send_message(uid, verb_msg, parse_mode=ParseMode.HTML)
        except TelegramError:
            pass

    await asyncio.gather(*(process_one(uid) for uid in target_ids))

    past_verb = "Added" if is_add else "Removed"
    result = f"✅ <b>Bulk {past_verb} Complete</b>\n\n🪙 {past_verb} {amount} coins for <b>{len(ok_list)}</b> users."
    if skipped:
        result += f"\n⚠️ Skipped (not found or insufficient balance): {', '.join(str(u) for u in skipped[:20])}"
        if len(skipped) > 20:
            result += f" (+{len(skipped) - 20} more)"
    await status_msg.edit_text(result, parse_mode=ParseMode.HTML)
    return ConversationHandler.END


async def cb_wb_action_ban(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    target_ids = context.user_data.pop("wb_ids")
    banned = 1 if query.data == "wb:ban" else 0
    async with db_conn() as db:
        for uid in target_ids:
            await db.execute("UPDATE users SET is_banned=? WHERE user_id=?", (banned, uid))
        await db.commit()
    action_word = "Banned" if banned else "Unbanned"
    await query.message.reply_text(f"✅ <b>{action_word}</b> {len(target_ids)} users.", parse_mode=ParseMode.HTML)
    return ConversationHandler.END


async def cb_wb_action_premium_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("7 Days", callback_data="wb:pset:7", style="primary"),
         InlineKeyboardButton("30 Days", callback_data="wb:pset:30", style="primary")],
        [InlineKeyboardButton("90 Days", callback_data="wb:pset:90", style="primary"),
         InlineKeyboardButton("Lifetime", callback_data="wb:pset:0", style="primary")],
    ])
    await query.message.reply_text("👑 Select Premium duration to grant to all selected users:", reply_markup=kb)
    return WB_PREMIUM


async def cb_wb_action_premium_set(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    days = int(query.data.split(":")[2])
    target_ids = context.user_data.pop("wb_ids")
    for uid in target_ids:
        await grant_premium(uid, None if days == 0 else days, update.effective_user.id)
        await TELEGRAM_SEND_LIMITER.acquire()
        try:
            label = "Lifetime" if days == 0 else f"{days} days"
            await context.bot.send_message(
                uid, f"👑 <b>You've been granted Premium!</b>\nDuration: {label}", parse_mode=ParseMode.HTML
            )
        except TelegramError:
            pass
    label = "Lifetime" if days == 0 else f"{days} Days"
    await query.message.reply_text(f"✅ Granted <b>{label}</b> Premium to {len(target_ids)} users.", parse_mode=ParseMode.HTML)
    return ConversationHandler.END


async def cb_wb_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    context.user_data.pop("wb_ids", None)
    context.user_data.pop("wb_coin_action", None)
    await query.message.reply_text("❌ Cancelled.")
    return ConversationHandler.END



async def cb_wm_history(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM transactions ORDER BY tx_id DESC LIMIT 15")
        rows = await cur.fetchall()
    if not rows:
        text = "📜 No transactions yet."
    else:
        lines = ["📜 <b>Recent Wallet History</b>\n"]
        for r in rows:
            lines.append(f"👤 <code>{r['user_id']}</code> {'+' if r['amount']>=0 else ''}{r['amount']} — {html.escape(r['tx_type'])}")
        text = "\n".join(lines)
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=back_button("ad:walletmgr"))



async def cb_admin_redeemmgr(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    is_owner = update.effective_user.id == OWNER_ID
    rows = [
        [InlineKeyboardButton("➕ Create Code", callback_data="rm:create", style="primary")],
        [InlineKeyboardButton("📋 List Codes", callback_data="rm:list", style="primary")],
        [InlineKeyboardButton("🗑 Delete Code", callback_data="rm:delstart", style="primary")],
    ]
    if is_owner:
        rows.append([InlineKeyboardButton("🗑 Delete ALL Codes", callback_data="rm:delall", style="primary")])
    rows.append([InlineKeyboardButton("⬅ Back", callback_data="ad:home", style="primary")])
    kb = InlineKeyboardMarkup(rows)
    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.edit_message_text("🎟 <b>Redeem Manager</b>", parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text("🎟 <b>Redeem Manager</b>", parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_rm_create_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    user_id = update.effective_user.id
    if user_id != OWNER_ID:
        today_start = datetime.utcnow().replace(hour=0, minute=0, second=0, microsecond=0).isoformat()
        async with db_conn() as db:
            cur = await db.execute(
                "SELECT COUNT(*) FROM redeems WHERE created_by=? AND created_at >= ?",
                (user_id, today_start),
            )
            count_today = (await cur.fetchone())[0]
        if count_today >= ADMIN_DAILY_REDEEM_LIMIT:
            await query.answer(
                f"🚫 Daily limit reached — admins can create up to {ADMIN_DAILY_REDEEM_LIMIT} redeem codes per day.",
                show_alert=True,
            )
            return ConversationHandler.END
    await query.answer()
    await query.message.reply_text("🎟 Enter the redeem code (e.g. WELCOME500):")
    return RM_CODE


async def conv_rm_code(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    code = update.message.text.strip().upper()
    if not re.match(r"^[A-Z0-9_\-]{3,32}$", code):
        await update.message.reply_text("❌ Invalid code format. Use letters/numbers only (3-32 chars).")
        return RM_CODE
    async with db_conn() as db:
        cur = await db.execute("SELECT 1 FROM redeems WHERE code=?", (code,))
        if await cur.fetchone():
            await update.message.reply_text("❌ This code already exists. Try another.")
            return RM_CODE
    context.user_data["rm_code"] = code
    await update.message.reply_text("💰 Enter Coin Reward (e.g. 500):")
    return RM_COINS


async def conv_rm_coins(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await update.message.reply_text("❌ Please enter a valid number.")
        return RM_COINS
    amount = int(text)
    if update.effective_user.id != OWNER_ID:
        if amount > ADMIN_MAX_REDEEM_COINS or amount < ADMIN_MIN_REDEEM_COINS:
            await update.message.reply_text(
                f"🚫 Admins can only create codes worth between {ADMIN_MIN_REDEEM_COINS}–{ADMIN_MAX_REDEEM_COINS} coins."
            )
            return RM_COINS
    context.user_data["rm_coins"] = amount
    await update.message.reply_text("⭐ Enter Premium Reward in days (0 for none):")
    return RM_PREMIUM


async def conv_rm_premium(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await update.message.reply_text("❌ Please enter a valid number.")
        return RM_PREMIUM
    context.user_data["rm_premium"] = int(text)
    await update.message.reply_text("🔢 Enter Usage Limit (0 for unlimited):")
    return RM_LIMIT


async def conv_rm_limit(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await update.message.reply_text("❌ Please enter a valid number.")
        return RM_LIMIT
    context.user_data["rm_limit"] = int(text)
    await update.message.reply_text("📅 Enter Expiry Date (DD-MM-YYYY) or send - for no expiry:")
    return RM_EXPIRY


async def conv_rm_expiry(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    expiry_iso = None
    if text != "-":
        try:
            expiry_iso = datetime.strptime(text, "%d-%m-%Y").isoformat()
        except ValueError:
            await update.message.reply_text("❌ Invalid date format. Use DD-MM-YYYY or send -.")
            return RM_EXPIRY

    d = context.user_data
    async with db_conn() as db:
        await db.execute(
            "INSERT INTO redeems (code, coin_reward, premium_days, usage_limit, expiry_date, status, created_by, created_at) "
            "VALUES (?, ?, ?, ?, ?, 'active', ?, ?)",
            (d["rm_code"], d["rm_coins"], d["rm_premium"], d["rm_limit"], expiry_iso,
             update.effective_user.id, datetime.utcnow().isoformat()),
        )
        await db.commit()

    await update.message.reply_text(
        f"✅ <b>Redeem Code Created!</b>\n\n🎟 Code: <code>{d['rm_code']}</code>\n💰 Coins: {d['rm_coins']}\n"
        f"⭐ Premium Days: {d['rm_premium']}\n🔢 Usage Limit: {d['rm_limit'] or 'Unlimited'}\n"
        f"📅 Expiry: {text if text != '-' else 'Never'}",
        parse_mode=ParseMode.HTML,
    )
    await log_admin_action(
        context.bot, update.effective_user.id,
        f"🎟 Created redeem code <code>{d['rm_code']}</code> — {d['rm_coins']} coins"
    )
    for k in ["rm_code", "rm_coins", "rm_premium", "rm_limit"]:
        context.user_data.pop(k, None)
    return ConversationHandler.END


async def cb_rm_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM redeems ORDER BY created_at DESC LIMIT 15")
        rows = await cur.fetchall()
    if not rows:
        text = "📋 No redeem codes yet."
    else:
        lines = ["📋 <b>Redeem Codes</b>\n"]
        for r in rows:
            lines.append(
                f"🎟 <code>{r['code']}</code> — {r['coin_reward']}🪙 | "
                f"{r['used_count']}/{r['usage_limit'] or '∞'} used | {r['status']}"
            )
        text = "\n".join(lines)
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=back_button("ad:redeemmgr"))


async def cb_rm_delete_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.message.reply_text(
        "🗑 Enter the exact redeem code to delete:",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="rm:delcancel", style="primary")]]),
    )
    return RM_DELETE


async def conv_rm_delete(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    code = update.message.text.strip().upper()
    async with db_conn() as db:
        cur = await db.execute("SELECT 1 FROM redeems WHERE code=?", (code,))
        if not await cur.fetchone():
            await update.message.reply_text("❌ No such code found. Please check and try again, or /cancel.")
            return RM_DELETE
        await db.execute("DELETE FROM redeems WHERE code=?", (code,))
        await db.execute("DELETE FROM redeem_uses WHERE code=?", (code,))
        await db.commit()
    await update.message.reply_text(f"✅ Deleted code: <code>{html.escape(code)}</code>", parse_mode=ParseMode.HTML)
    return ConversationHandler.END


async def cb_rm_delete_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    await update.callback_query.answer()
    await update.callback_query.message.reply_text("❌ Cancelled.")
    return ConversationHandler.END


async def cb_rm_delete_all_confirm(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_owner(update):
        return
    query = update.callback_query
    await query.answer()
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM redeems")
        count = (await cur.fetchone())[0]
    if count == 0:
        await query.edit_message_text("No redeem codes to delete.", reply_markup=back_button("ad:redeemmgr"))
        return
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Yes, Delete ALL", callback_data="rm:delallconfirm", style="primary"),
         InlineKeyboardButton("❌ No", callback_data="ad:redeemmgr", style="primary")],
    ])
    await query.edit_message_text(
        f"⚠️ <b>Delete ALL {count} Redeem Codes?</b>\n\nThis cannot be undone.",
        parse_mode=ParseMode.HTML, reply_markup=kb,
    )


async def cb_rm_delete_all_execute(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_owner(update):
        return
    query = update.callback_query
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM redeems")
        count = (await cur.fetchone())[0]
        await db.execute("DELETE FROM redeems")
        await db.execute("DELETE FROM redeem_uses")
        await db.commit()
    await query.answer("🗑 Deleted all codes")
    await query.edit_message_text(f"🗑 <b>Deleted {count} redeem codes.</b>", parse_mode=ParseMode.HTML)
    await log_admin_action(context.bot, update.effective_user.id, f"🗑 Deleted ALL {count} redeem codes")



async def cb_admin_usermgr(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return ConversationHandler.END
    if update.callback_query:
        await update.callback_query.answer()
    await update.effective_message.reply_text("🔍 Enter User ID or @username to search:")
    return UM_SEARCH


async def conv_um_search(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        if text.isdigit():
            cur = await db.execute("SELECT * FROM users WHERE user_id=?", (int(text),))
        else:
            uname = text.lstrip("@")
            cur = await db.execute("SELECT * FROM users WHERE username=?", (uname,))
        row = await cur.fetchone()

    if not row:
        await update.message.reply_text("❌ User not found.")
        return ConversationHandler.END

    await send_user_profile(update.message, row["user_id"])
    return ConversationHandler.END


async def send_user_profile(message_or_query, target_id: int, edit: bool = False):
    row = await get_user_row(target_id)
    if not row:
        return
    balance = await get_balance(target_id)
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (target_id,))
        refs = (await cur.fetchone())[0]
    premium = "⭐ Active" if await is_premium_active(target_id) else "❌ None"
    banned = "🚫 Banned" if row["is_banned"] else "✅ Active"

    text = (
        f"👤 <b>User Profile</b>\n\n"
        f"🆔 ID: <code>{target_id}</code>\n"
        f"📛 Name: {html.escape(row['first_name'] or '—')}\n"
        f"🔗 Username: @{html.escape(row['username']) if row['username'] else '—'}\n"
        f"📅 Joined: {fmt_date(row['join_date'])}\n"
        f"🪙 Wallet: {balance}\n"
        f"👥 Referrals: {refs}\n"
        f"⭐ Premium: {premium}\n"
        f"🔒 Status: {banned}"
    )
    is_owner = message_or_query.from_user.id == OWNER_ID
    rows = [
        [InlineKeyboardButton("➕ Add Coins", callback_data=f"um:addc:{target_id}", style="primary"),
         InlineKeyboardButton("➖ Remove Coins", callback_data=f"um:remc:{target_id}", style="primary")],
    ]
    if is_owner:
        rows.append([InlineKeyboardButton("🚫 Ban", callback_data=f"um:ban:{target_id}", style="primary"),
                     InlineKeyboardButton("✅ Unban", callback_data=f"um:unban:{target_id}", style="primary")])
    rows.append([InlineKeyboardButton("👑 Give Premium", callback_data=f"um:givep:{target_id}", style="primary"),
                 InlineKeyboardButton("❌ Remove Premium", callback_data=f"um:remp:{target_id}", style="primary")])
    kb = InlineKeyboardMarkup(rows)
    if hasattr(message_or_query, "edit_message_text") and edit:
        await message_or_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await message_or_query.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)



async def cb_admin_all_users(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    if update.callback_query:
        await update.callback_query.answer()
    await send_all_users_list(update, context, page=0)


async def send_all_users_list(update: Update, context: ContextTypes.DEFAULT_TYPE, page: int) -> None:
    per_page = 10
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        total = (await (await db.execute("SELECT COUNT(*) FROM users")).fetchone())[0]
        cur = await db.execute(
            "SELECT user_id, username, first_name, is_banned FROM users "
            "ORDER BY join_date DESC LIMIT ? OFFSET ?",
            (per_page, page * per_page),
        )
        rows = await cur.fetchall()

    text = f"👤 <b>All Users</b>\n\n👥 Total Registered: <b>{total}</b>\n\nTap a user to view or manage their profile:"
    buttons = []
    for r in rows:
        label = f"@{r['username']}" if r["username"] else (r["first_name"] or f"ID {r['user_id']}")
        tag = "🚫 " if r["is_banned"] else "👤 "
        buttons.append([InlineKeyboardButton(f"{tag}{label}", callback_data=f"au:view:{r['user_id']}:{page}", style="primary")])
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"au:list:{page-1}", style="primary"))
    if (page + 1) * per_page < total:
        nav.append(InlineKeyboardButton("Next ➡", callback_data=f"au:list:{page+1}", style="primary"))
    if nav:
        buttons.append(nav)

    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_au_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    page = int(query.data.split(":")[2])
    await send_all_users_list(update, context, page)


async def cb_au_view(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    target_id = int(query.data.split(":")[2])
    await send_user_profile(query, target_id, edit=True)


async def cb_um_ban(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_owner(update):
        return
    query = update.callback_query
    action, target_id = query.data.split(":")[1], int(query.data.split(":")[2])
    banned = 1 if action == "ban" else 0
    async with db_conn() as db:
        await db.execute("UPDATE users SET is_banned=? WHERE user_id=?", (banned, target_id))
        await db.commit()
    await query.answer("✅ Updated")
    await log_admin_action(context.bot, update.effective_user.id, f"{'🚫 Banned' if banned else '✅ Unbanned'} user {target_id}")
    await send_user_profile(query, target_id, edit=True)


async def cb_um_premium(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    action, target_id = query.data.split(":")[1], int(query.data.split(":")[2])
    if action == "remp":
        await remove_premium(target_id)
        await query.answer("✅ Premium removed")
        await send_user_profile(query, target_id, edit=True)
        return
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("7 Days", callback_data=f"um:pset:{target_id}:7", style="primary"),
         InlineKeyboardButton("30 Days", callback_data=f"um:pset:{target_id}:30", style="primary")],
        [InlineKeyboardButton("90 Days", callback_data=f"um:pset:{target_id}:90", style="primary"),
         InlineKeyboardButton("Lifetime", callback_data=f"um:pset:{target_id}:0", style="primary")],
        [InlineKeyboardButton("⬅ Back", callback_data=f"um:back:{target_id}", style="primary")],
    ])
    await query.answer()
    await query.edit_message_text("👑 Select Premium Duration:", reply_markup=kb)


async def cb_um_pset(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    _, _, target_id, days = query.data.split(":")
    target_id, days = int(target_id), int(days)
    await grant_premium(target_id, None if days == 0 else days, update.effective_user.id)
    await query.answer("✅ Premium granted")
    try:
        await context.bot.send_message(
            target_id,
            f"👑 <b>You've been granted Premium!</b>\nDuration: {'Lifetime' if days==0 else f'{days} days'}",
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        pass
    await log_admin_action(
        context.bot, update.effective_user.id,
        f"👑 Granted {'Lifetime' if days == 0 else f'{days} days'} Premium to user {target_id}"
    )
    await send_user_profile(query, target_id, edit=True)


async def cb_um_back(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    target_id = int(query.data.split(":")[2])
    await query.answer()
    await send_user_profile(query, target_id, edit=True)


async def cb_um_coins_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    action, target_id = query.data.split(":")[1], int(query.data.split(":")[2])
    context.user_data["um_action"] = "add" if action == "addc" else "remove"
    context.user_data["um_target"] = target_id
    await query.message.reply_text("🪙 Enter the coin amount:")
    return UM_AMOUNT


async def conv_um_coins_amount(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit() or int(text) <= 0:
        await update.message.reply_text("❌ Please enter a valid positive number.")
        return UM_AMOUNT
    amount = int(text)
    target_id = context.user_data.pop("um_target")
    action = context.user_data.pop("um_action")
    if action == "add":
        await add_coins(target_id, amount, "admin_gift", "Admin added coins via User Manager")
        await update.message.reply_text(f"✅ Added {amount} coins to user {target_id}.")
    else:
        ok = await remove_coins(target_id, amount, "admin_deduct", "Admin removed coins via User Manager")
        await update.message.reply_text(
            f"✅ Removed {amount} coins from user {target_id}." if ok else "❌ Insufficient balance to remove that amount."
        )
    return ConversationHandler.END



async def cb_admin_premiummgr(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    if update.callback_query:
        await update.callback_query.answer()
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM premium ORDER BY granted_at DESC LIMIT 20")
        rows = await cur.fetchall()
    if not rows:
        text = "👑 <b>Premium Manager</b>\n\nNo premium users yet.\n\nUse 👥 User Manager to grant premium to a specific user."
    else:
        lines = ["👑 <b>Premium Users</b>\n"]
        for r in rows:
            status = "Lifetime" if r["is_lifetime"] else fmt_date(r["expiry_date"])
            lines.append(f"🆔 <code>{r['user_id']}</code> — {status}")
        text = "\n".join(lines)
    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=back_button("ad:home"))
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)



async def cb_admin_adminmgr(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    if update.callback_query:
        await update.callback_query.answer()

    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM admins ORDER BY added_date")
        rows = await cur.fetchall()

    lines = ["🛡 <b>Admin Manager</b>\n"]
    lines.append(f"👑 Owner: <code>{OWNER_ID}</code>")
    for r in rows:
        if r["user_id"] == OWNER_ID:
            continue
        u = await get_user_row(r["user_id"])
        label = f"@{u['username']}" if u and u["username"] else (u["first_name"] if u else "Unknown")
        role_tag = "🥇 Senior" if r["role"] == "senior" else "🥈 Junior"
        lines.append(f"🛡 <code>{r['user_id']}</code> — {html.escape(label or '—')} ({role_tag})")
    text = "\n".join(lines)

    buttons = []
    is_owner = update.effective_user.id == OWNER_ID
    if is_owner:
        buttons.append([InlineKeyboardButton("➕ Add Admin", callback_data="am:add", style="primary"),
                         InlineKeyboardButton("➖ Remove Admin", callback_data="am:remove", style="primary")])
        buttons.append([InlineKeyboardButton("📜 Action Log", callback_data="am:log:0", style="primary")])
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="ad:home", style="primary")])
    kb = InlineKeyboardMarkup(buttons)

    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_am_log_view(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not await require_owner(update):
        return
    await query.answer()
    page = int(query.data.split(":")[2])
    per_page = 10
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT * FROM admin_logs ORDER BY log_id DESC LIMIT ? OFFSET ?", (per_page, page * per_page)
        )
        rows = await cur.fetchall()

    if not rows and page == 0:
        text = "📜 <b>Admin Action Log</b>\n\nNo actions recorded yet."
    else:
        lines = ["📜 <b>Admin Action Log</b>\n"]
        for r in rows:
            u = await get_user_row(r["actor_id"])
            label = f"@{u['username']}" if u and u["username"] else str(r["actor_id"])
            lines.append(f"👤 {html.escape(label)} — {r['action_text']}\n<i>{fmt_date(r['timestamp'])}</i>")
        text = "\n\n".join(lines)

    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"am:log:{page-1}", style="primary"))
    if len(rows) == per_page:
        nav.append(InlineKeyboardButton("Next ➡", callback_data=f"am:log:{page+1}", style="primary"))
    buttons = [nav] if nav else []
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="ad:adminmgr", style="primary")])
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_am_add_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    if update.effective_user.id != OWNER_ID:
        await query.answer("🚫 Only the owner can add admins.", show_alert=True)
        return ConversationHandler.END
    await query.answer()
    await query.message.reply_text("👤 Send the User ID or @username to promote to admin:")
    return AM_ADD_USER


async def conv_am_add_user(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    target_id = None
    async with db_conn() as db:
        if text.startswith("@"):
            cur = await db.execute("SELECT user_id FROM users WHERE username=?", (text.lstrip("@"),))
            row = await cur.fetchone()
            if row:
                target_id = row[0]
        elif text.isdigit():
            target_id = int(text)

    if target_id is None:
        await update.message.reply_text(
            "❌ Couldn't find that user. They need to have started the bot at least once. Try again, or /cancel."
        )
        return AM_ADD_USER

    context.user_data["am_target_id"] = target_id
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("🥇 Senior Admin", callback_data="am:role:senior", style="primary"),
         InlineKeyboardButton("🥈 Junior Admin", callback_data="am:role:junior", style="primary")],
    ])
    await update.message.reply_text(
        "🛡 Choose their role:\n\n"
        "🥇 <b>Senior</b> — their actions are only reported to you (the Owner).\n"
        "🥈 <b>Junior</b> — their actions are reported to you AND all Senior admins.",
        parse_mode=ParseMode.HTML, reply_markup=kb,
    )
    return AM_ADD_ROLE


async def cb_am_add_role(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    role = query.data.split(":")[2]
    target_id = context.user_data.pop("am_target_id", None)
    if target_id is None:
        await query.message.reply_text("❌ Something went wrong — please start again.")
        return ConversationHandler.END

    async with db_conn() as db:
        await db.execute(
            "INSERT INTO admins (user_id, added_date, role) VALUES (?, ?, ?) "
            "ON CONFLICT(user_id) DO UPDATE SET role=excluded.role",
            (target_id, datetime.utcnow().isoformat(), role),
        )
        await db.commit()

    role_label = "Senior Admin 🥇" if role == "senior" else "Junior Admin 🥈"
    await query.message.reply_text(
        f"✅ User <code>{target_id}</code> is now a <b>{role_label}</b>.", parse_mode=ParseMode.HTML
    )
    try:
        await context.bot.send_message(
            target_id, f"🛡 <b>You've been made a {role_label} of this bot!</b>", parse_mode=ParseMode.HTML
        )
    except TelegramError:
        pass
    return ConversationHandler.END


async def cb_am_remove_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if update.effective_user.id != OWNER_ID:
        await query.answer("🚫 Only the owner can remove admins.", show_alert=True)
        return
    await query.answer()
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM admins WHERE user_id != ? ORDER BY added_date", (OWNER_ID,))
        rows = await cur.fetchall()
    if not rows:
        await query.edit_message_text("No sub-admins to remove.", reply_markup=back_button("ad:adminmgr"))
        return
    buttons = []
    for r in rows:
        u = await get_user_row(r["user_id"])
        label = f"@{u['username']}" if u and u["username"] else str(r["user_id"])
        buttons.append([InlineKeyboardButton(f"➖ {label}", callback_data=f"am:rm:{r['user_id']}", style="primary")])
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="ad:adminmgr", style="primary")])
    await query.edit_message_text("➖ Select an admin to remove:", reply_markup=InlineKeyboardMarkup(buttons))


async def cb_am_remove_confirm(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if update.effective_user.id != OWNER_ID:
        await query.answer("🚫 Only the owner can remove admins.", show_alert=True)
        return
    target_id = int(query.data.split(":")[2])
    if target_id == OWNER_ID:
        await query.answer("🚫 Can't remove the owner.", show_alert=True)
        return
    async with db_conn() as db:
        await db.execute("DELETE FROM admins WHERE user_id=?", (target_id,))
        await db.commit()
    await query.answer("✅ Removed")
    await cb_am_remove_menu(update, context)



async def cb_admin_broadcast_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return ConversationHandler.END
    if update.callback_query:
        await update.callback_query.answer()
    await update.effective_message.reply_text(
        "📢 Send the message you want to broadcast (text, photo, video, animation, sticker, document, voice, or audio).\n\n"
        "Send /cancel to abort."
    )
    return BR_CONTENT


async def conv_broadcast_content(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    msg = update.message
    async with db_conn() as db:
        cur = await db.execute("SELECT user_id FROM users")
        all_users = [r[0] for r in await cur.fetchall()]

    status_msg = await msg.reply_text(f"📢 Broadcasting to {len(all_users)} users...")
    counters = {"done": 0, "failed": 0}
    counters_lock = asyncio.Lock()

    async def send_one(uid: int) -> None:
        await TELEGRAM_SEND_LIMITER.acquire()
        try:
            await context.bot.copy_message(chat_id=uid, from_chat_id=msg.chat_id, message_id=msg.message_id)
            async with counters_lock:
                counters["done"] += 1
        except RetryAfter as e:
            await asyncio.sleep(e.retry_after + 0.5)
            try:
                await context.bot.copy_message(chat_id=uid, from_chat_id=msg.chat_id, message_id=msg.message_id)
                async with counters_lock:
                    counters["done"] += 1
            except TelegramError:
                async with counters_lock:
                    counters["failed"] += 1
        except TelegramError:
            async with counters_lock:
                counters["failed"] += 1

    await asyncio.gather(*(send_one(uid) for uid in all_users))

    await status_msg.edit_text(
        f"✅ <b>Broadcast Complete</b>\n\n✅ Sent: {counters['done']}\n❌ Failed: {counters['failed']}",
        parse_mode=ParseMode.HTML,
    )
    await log_admin_action(
        context.bot, update.effective_user.id,
        f"📢 Sent a broadcast — reached {counters['done']}, failed {counters['failed']}"
    )
    return ConversationHandler.END


async def cmd_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    admin = await is_admin(update.effective_user.id)
    await update.message.reply_text("❌ Cancelled.", reply_markup=user_reply_keyboard(admin))
    context.user_data.clear()
    return ConversationHandler.END



async def cb_admin_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    if update.callback_query:
        await update.callback_query.answer()

    async with db_conn() as db:
        total_users = (await (await db.execute("SELECT COUNT(*) FROM users")).fetchone())[0]
        active_users = (await (await db.execute(
            "SELECT COUNT(*) FROM users WHERE last_seen > ?",
            ((datetime.utcnow() - timedelta(days=7)).isoformat(),)
        )).fetchone())[0]
        premium_users = (await (await db.execute(
            "SELECT COUNT(*) FROM premium WHERE is_lifetime=1 OR expiry_date > ?",
            (datetime.utcnow().isoformat(),)
        )).fetchone())[0]
        total_files = (await (await db.execute("SELECT COUNT(*) FROM files WHERE is_deleted=0")).fetchone())[0]
        total_downloads = (await (await db.execute("SELECT COUNT(*) FROM downloads")).fetchone())[0]
        coins_distributed = (await (await db.execute(
            "SELECT COALESCE(SUM(amount),0) FROM transactions WHERE amount > 0"
        )).fetchone())[0]
        redeem_count = (await (await db.execute("SELECT COUNT(*) FROM redeem_uses")).fetchone())[0]
        referral_count = (await (await db.execute("SELECT COUNT(*) FROM referrals")).fetchone())[0]

    text = (
        "📊 <b>Statistics</b>\n\n"
        f"👥 Total Users: <b>{total_users}</b>\n"
        f"🟢 Active (7d): <b>{active_users}</b>\n"
        f"⭐ Premium Users: <b>{premium_users}</b>\n"
        f"🛒 Total Files: <b>{total_files}</b>\n"
        f"⬇ Downloads: <b>{total_downloads}</b>\n"
        f"🪙 Coins Distributed: <b>{coins_distributed}</b>\n"
        f"🎟 Redeem Count: <b>{redeem_count}</b>\n"
        f"🚀 Referral Count: <b>{referral_count}</b>"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("📈 Top Downloaded Files", callback_data="stats:topfiles", style="primary")],
        [InlineKeyboardButton("⬅ Back", callback_data="ad:home", style="primary")],
    ])
    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_stats_top_files(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not await is_admin(update.effective_user.id):
        await query.answer(ADMIN_ONLY_MSG, show_alert=True)
        return
    await query.answer()
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT file_name, downloads_count, price FROM files WHERE is_deleted=0 "
            "ORDER BY downloads_count DESC LIMIT 10"
        )
        rows = await cur.fetchall()

    if not rows:
        text = "📈 <b>Top Downloaded Files</b>\n\nNo files yet."
    else:
        medals = ["🥇", "🥈", "🥉"]
        lines = ["📈 <b>Top 10 Downloaded Files</b>\n"]
        for i, r in enumerate(rows):
            rank = medals[i] if i < 3 else f"{i+1}."
            tag = "FREE" if r["price"] == 0 else f"{r['price']} coins"
            lines.append(f"{rank} {html.escape(r['file_name'])} — <b>{r['downloads_count']}</b> downloads ({tag})")
        text = "\n".join(lines)
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=back_button("ad:stats"))



async def cb_admin_maintenance(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    current = await get_setting("maintenance", "0")
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Enable", callback_data="mt:on", style="primary"),
         InlineKeyboardButton("❌ Disable", callback_data="mt:off", style="primary")],
        [InlineKeyboardButton("⬅ Back", callback_data="ad:home", style="primary")],
    ])
    status = "🚧 ENABLED" if current == "1" else "✅ DISABLED"
    text = f"🛠 <b>Maintenance Mode</b>\n\nCurrent status: <b>{status}</b>"
    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_mt_toggle(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    val = "1" if query.data == "mt:on" else "0"
    await set_setting("maintenance", val)
    await query.answer("✅ Updated")
    await log_admin_action(context.bot, update.effective_user.id, f"🛠 Maintenance mode turned {'ON' if val == '1' else 'OFF'}")
    await cb_admin_maintenance(update, context)



SETTINGS_FIELDS = {
    "referral_reward": "🚀 Referral Reward (coins)",
    "premium_pricing": "👑 Premium Pricing (JSON list)",
    "referral_milestones": "🚀 Referral Milestone Rewards (JSON)",
    "streak_rewards": "🔥 Login Streak Rewards (JSON)",
    "support_username": "💬 Support Username",
    "bot_name": "🏷 Bot Name",
    "force_join": "📡 Force Join (1/0)",
}


async def cb_admin_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await require_owner(update):
        return
    buttons = [[InlineKeyboardButton(label, callback_data=f"set:{key}", style="primary")] for key, label in SETTINGS_FIELDS.items()]
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="ad:home", style="primary")])
    text = "⚙ <b>Settings</b>\n\nSelect a setting to edit:"
    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_settings_field(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await require_owner(update):
        return ConversationHandler.END
    query = update.callback_query
    await query.answer()
    key = query.data.split(":")[1]
    current = await get_setting(key, "")
    context.user_data["st_key"] = key
    await query.message.reply_text(
        f"✏️ Current value of <b>{SETTINGS_FIELDS.get(key, key)}</b>:\n<code>{html.escape(current)}</code>\n\n"
        f"Send the new value:",
        parse_mode=ParseMode.HTML,
    )
    return ST_VALUE


async def conv_settings_value(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    key = context.user_data.pop("st_key")
    value = update.message.text.strip()
    await set_setting(key, value)
    await update.message.reply_text("✅ Setting updated successfully.")
    return ConversationHandler.END



async def handle_admin_panel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    is_owner = update.effective_user.id == OWNER_ID
    await update.effective_message.reply_text(
        f"👑 <b>Admin Panel</b> <i>({BOT_VERSION})</i>\n\nAll admin controls are now available on your keyboard below.\n"
        "Tap <b>⬅️ Back to Main</b> anytime to return to the normal menu.",
        parse_mode=ParseMode.HTML,
        reply_markup=admin_reply_keyboard(is_owner),
    )


async def handle_admin_back_to_main(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        return
    await update.effective_message.reply_text(
        "🏠 <b>Main Menu</b>", parse_mode=ParseMode.HTML, reply_markup=user_reply_keyboard(True)
    )


async def cb_admin_home(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    await query.edit_message_text("👑 <b>Admin Panel</b>\n\nSelect an option below:", parse_mode=ParseMode.HTML, reply_markup=admin_panel_keyboard())



async def job_expire_premium(context: ContextTypes.DEFAULT_TYPE) -> None:
    async with db_conn() as db:
        await db.execute(
            "DELETE FROM premium WHERE is_lifetime=0 AND expiry_date IS NOT NULL AND expiry_date < ?",
            (datetime.utcnow().isoformat(),),
        )
        await db.commit()


async def job_expire_redeem_codes(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Auto-deletes redeem codes past their expiry_date, along with their
    usage records, so admins never have to clean these up manually."""
    now = datetime.utcnow().isoformat()
    async with db_conn() as db:
        cur = await db.execute(
            "SELECT code FROM redeems WHERE expiry_date IS NOT NULL AND expiry_date < ?", (now,)
        )
        expired = [r[0] for r in await cur.fetchall()]
        if expired:
            placeholders = ",".join("?" * len(expired))
            await db.execute(f"DELETE FROM redeems WHERE code IN ({placeholders})", expired)
            await db.execute(f"DELETE FROM redeem_uses WHERE code IN ({placeholders})", expired)
            await db.commit()
            log.info("Auto-deleted %d expired redeem code(s)", len(expired))



async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    log.error("Exception while handling update:", exc_info=context.error)



TEXT_ROUTES = {
    "Buy": handle_buy_home,
    "My Wallet": handle_my_wallet,
    "Invite Friend": handle_invite_friends,
    "Leaderboard": handle_leaderboard,
    "Referral Code": handle_referral_code,
    "My Stats": handle_my_stats,
    "Support": handle_support,
    "👑 Admin Panel": handle_admin_panel,
    "📂 Manage Files": cb_admin_managefiles,
    "🛒 Product Manager": cb_admin_products,
    "💹 Economy Manager": cb_admin_economy,
    "🚀 Referral Manager": cb_admin_referrals,
    "💰 Wallet Manager": cb_admin_walletmgr,
    "🎟 Redeem Manager": cb_admin_redeemmgr,
    "📡 Force Channels": cb_admin_fcmgr,
    "👤 All Users": cb_admin_all_users,
    "👑 Premium Manager": cb_admin_premiummgr,
    "🛡 Admin Manager": cb_admin_adminmgr,
    "📋 Admin List": cb_admin_adminmgr,
    "📊 Statistics": cb_admin_stats,
    "🛠 Maintenance": cb_admin_maintenance,
    "⚙ Settings": cb_admin_settings,
    "⬅️ Back to Main": handle_admin_back_to_main,
}


async def text_router(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_user is None or update.message is None or update.message.text is None:
        return
    text = update.message.text
    handler = TEXT_ROUTES.get(text)
    if handler:
        await handler(update, context)



def build_application() -> Application:
    concurrent_updates = int(os.environ.get("CONCURRENT_UPDATES", "512"))
    app = (
        ApplicationBuilder()
        .token(BOT_TOKEN)
        .concurrent_updates(concurrent_updates)
        .request(HTTPXRequest(
            connection_pool_size=concurrent_updates,
            pool_timeout=20.0,
            connect_timeout=15.0,
            read_timeout=20.0,
            write_timeout=20.0,
        ))
        .get_updates_request(HTTPXRequest(connection_pool_size=64, pool_timeout=20.0))
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .build()
    )

    app.add_handler(MessageHandler(filters.ALL, group_restriction_guard), group=-2)
    app.add_handler(CallbackQueryHandler(group_restriction_guard), group=-2)

    app.add_handler(MessageHandler(filters.ALL, flood_guard), group=-1)
    app.add_handler(CallbackQueryHandler(flood_guard), group=-1)

    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("help", cmd_help))

    app.add_handler(CallbackQueryHandler(cb_verify_join, pattern="^verify_join$"))

    app.add_handler(CallbackQueryHandler(cb_wallet_home, pattern="^wallet:home$"))
    app.add_handler(CallbackQueryHandler(cb_wallet_tx, pattern="^wallet:tx:"))
    app.add_handler(CallbackQueryHandler(cb_wallet_buy_premium, pattern="^wallet:buypremium$"))

    ticket_conv = ConversationHandler(
        entry_points=[MessageHandler(filters.Regex("^🎫 Support Ticket$"), handle_support_ticket_prompt)],
        states={
            TK_SUBJECT: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_ticket_subject)],
            TK_BODY: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_ticket_body)],
        },
        fallbacks=[CallbackQueryHandler(cb_ticket_cancel, pattern="^ticket:cancel$"), CommandHandler("cancel", cmd_cancel)],
        per_message=True,
    )
    app.add_handler(ticket_conv)

    ticket_reply_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_ticket_reply_start, pattern=r"^ticket:reply:\d+$")],
        states={TK_REPLY: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_ticket_reply)]},
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(ticket_reply_conv)

    ticket_user_reply_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_ticket_user_reply_start, pattern=r"^ticket:ureply:\d+$")],
        states={TK_USER_REPLY: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_ticket_user_reply)]},
        fallbacks=[CallbackQueryHandler(cb_ticket_cancel, pattern="^ticket:cancel$"), CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(ticket_user_reply_conv)
    app.add_handler(CallbackQueryHandler(cb_ticket_close, pattern=r"^ticket:close:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_premium_purchase, pattern=r"^premium:buy:\d+:\d+$"))


    app.add_handler(MessageHandler(filters.Regex("^🎟️ Redeem Code$"), handle_redeem_prompt))
    app.add_handler(CallbackQueryHandler(cb_redeem_cancel, pattern="^redeem:cancel$"))

    redeem_enter_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_redeem_enter_start, pattern="^redeem:enter$")],
        states={RD_CODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_redeem_code)]},
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(redeem_enter_conv)

    redeem_gift_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_redeem_gift_start, pattern="^redeem:gift$")],
        states={GC_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_gift_amount)]},
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(redeem_gift_conv)

    app.add_handler(CallbackQueryHandler(cb_files_list, pattern=r"^files:list:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_file_view, pattern=r"^file:view:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_file_buy, pattern=r"^file:buy:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_file_download, pattern=r"^file:dl:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_my_purchases, pattern=r"^purchases:\d+$"))

    app.add_handler(CallbackQueryHandler(cb_buy_home, pattern="^buy:home$"))
    app.add_handler(CallbackQueryHandler(cb_buy_legacy, pattern="^buy:legacy$"))
    app.add_handler(CallbackQueryHandler(cb_buy_category, pattern=r"^buy:cat:\w+:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_product_view, pattern=r"^buy:view:\d+:\w+:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_product_buy, pattern=r"^buy:buy:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_product_redeliver, pattern=r"^buy:redeliver:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_buy_support, pattern="^buy:support$"))

    app.add_handler(CallbackQueryHandler(cb_admin_home, pattern="^ad:home$"))
    app.add_handler(CallbackQueryHandler(cb_admin_managefiles, pattern="^ad:managefiles$"))
    app.add_handler(CallbackQueryHandler(cb_admin_walletmgr, pattern="^ad:walletmgr$"))
    app.add_handler(CallbackQueryHandler(cb_admin_redeemmgr, pattern="^ad:redeemmgr$"))
    app.add_handler(CallbackQueryHandler(cb_admin_fcmgr, pattern="^ad:fcmgr$"))
    app.add_handler(CallbackQueryHandler(cb_admin_premiummgr, pattern="^ad:premiummgr$"))
    app.add_handler(CallbackQueryHandler(cb_admin_adminmgr, pattern="^ad:adminmgr$"))
    app.add_handler(CallbackQueryHandler(cb_am_remove_menu, pattern="^am:remove$"))
    app.add_handler(CallbackQueryHandler(cb_am_log_view, pattern=r"^am:log:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_am_remove_confirm, pattern=r"^am:rm:\d+$"))

    am_add_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_am_add_start, pattern="^am:add$")],
        states={
            AM_ADD_USER: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_am_add_user)],
            AM_ADD_ROLE: [CallbackQueryHandler(cb_am_add_role, pattern=r"^am:role:(senior|junior)$")],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(am_add_conv)
    app.add_handler(CallbackQueryHandler(cb_admin_stats, pattern="^ad:stats$"))
    app.add_handler(CallbackQueryHandler(cb_stats_top_files, pattern="^stats:topfiles$"))
    app.add_handler(CallbackQueryHandler(cb_admin_maintenance, pattern="^ad:maintenance$"))
    app.add_handler(CallbackQueryHandler(cb_mt_toggle, pattern="^mt:(on|off)$"))
    app.add_handler(CallbackQueryHandler(cb_admin_settings, pattern="^ad:settings$"))

    app.add_handler(CallbackQueryHandler(cb_admin_products, pattern="^ad:products$"))
    app.add_handler(CallbackQueryHandler(cb_admin_economy, pattern="^ad:economy$"))
    app.add_handler(CallbackQueryHandler(cb_admin_referrals, pattern="^ad:referrals$"))

    app.add_handler(CallbackQueryHandler(cb_pm_add_select, pattern="^pm:addsel$"))
    app.add_handler(CallbackQueryHandler(cb_pm_list, pattern=r"^pm:list:(bot|method):\d+$"))
    app.add_handler(CallbackQueryHandler(cb_pm_view, pattern=r"^pm:view:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_pm_toggle_status, pattern=r"^pm:togglestatus:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_pm_delete_prompt, pattern=r"^pm:del:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_pm_delete_confirm, pattern=r"^pm:delok:\d+$"))

    app.add_handler(CallbackQueryHandler(cb_eco_toggle, pattern=r"^eco:(refon|refoff|lbon|lboff)$"))

    product_add_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_pm_add_start, pattern=r"^pm:add:(bot|method)$")],
        states={
            PR_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_pm_name)],
            PR_DESC: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_pm_desc)],
            PR_PRICE: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_pm_price)],
            PR_PREVIEW: [
                MessageHandler(filters.PHOTO, conv_pm_preview),
                CallbackQueryHandler(cb_pm_skip_preview, pattern="^pm:skip:preview$"),
                CallbackQueryHandler(cb_pm_remove_preview, pattern="^pm:edit:rmpreview$"),
                CallbackQueryHandler(cb_pm_cancel, pattern="^pm:cancel$"),
            ],
            PR_FILE: [
                MessageHandler(
                    (filters.Document.ALL | filters.VIDEO | filters.AUDIO | filters.PHOTO |
                     filters.VOICE | filters.ANIMATION) & ~filters.COMMAND,
                    conv_pm_file,
                ),
                CallbackQueryHandler(cb_pm_skip_file, pattern="^pm:skip:file$"),
                CallbackQueryHandler(cb_pm_remove_file, pattern="^pm:edit:rmfile$"),
                CallbackQueryHandler(cb_pm_cancel, pattern="^pm:cancel$"),
            ],
            PR_STATUS: [
                CallbackQueryHandler(cb_pm_status, pattern=r"^pm:status:(active|inactive)$"),
                CallbackQueryHandler(cb_pm_cancel, pattern="^pm:cancel$"),
            ],
            PR_CONFIRM: [
                CallbackQueryHandler(cb_pm_save, pattern="^pm:save$"),
                CallbackQueryHandler(cb_pm_edit_menu, pattern="^pm:editmenu$"),
                CallbackQueryHandler(cb_pm_edit_field, pattern=r"^pm:edit:(name|desc|price|preview|file|status)$"),
                CallbackQueryHandler(cb_pm_review, pattern="^pm:review$"),
                CallbackQueryHandler(cb_pm_cancel, pattern="^pm:cancel$"),
            ],
        },
        fallbacks=[CallbackQueryHandler(cb_pm_cancel, pattern="^pm:cancel$"), CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(product_add_conv)

    product_edit_conv = ConversationHandler(
        entry_points=[
            CallbackQueryHandler(cb_pe_start, pattern=r"^pm:ef:(name|desc|price):\d+$"),
            CallbackQueryHandler(cb_pe_preview_start, pattern=r"^pm:ef:preview:\d+$"),
            CallbackQueryHandler(cb_pe_file_start, pattern=r"^pm:ef:file:\d+$"),
        ],
        states={
            PE_VALUE: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_pe_value)],
            PE_PREVIEW: [
                MessageHandler(filters.PHOTO, conv_pe_preview),
                CallbackQueryHandler(cb_pe_remove_preview, pattern="^pe:rmpreview$"),
                CallbackQueryHandler(cb_pm_cancel, pattern="^pm:cancel$"),
            ],
            PE_FILE: [
                MessageHandler(
                    (filters.Document.ALL | filters.VIDEO | filters.AUDIO | filters.PHOTO |
                     filters.VOICE | filters.ANIMATION) & ~filters.COMMAND,
                    conv_pe_file,
                ),
                CallbackQueryHandler(cb_pe_remove_file, pattern="^pe:rmfile$"),
                CallbackQueryHandler(cb_pm_cancel, pattern="^pm:cancel$"),
            ],
        },
        fallbacks=[CallbackQueryHandler(cb_pm_cancel, pattern="^pm:cancel$"), CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(product_edit_conv)


    eco_reward_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_eco_refreward_start, pattern="^eco:refreward$")],
        states={ECO_REWARD: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_eco_reward)]},
        fallbacks=[CallbackQueryHandler(cb_pm_cancel, pattern="^pm:cancel$"), CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(eco_reward_conv)

    upload_conv = ConversationHandler(
        entry_points=[
            CallbackQueryHandler(cb_admin_upload_start, pattern="^ad:upload$"),
            MessageHandler(filters.Regex("^📤 Upload File$"), cb_admin_upload_start),
        ],
        states={
            UP_FILE: [MessageHandler(
                (filters.Document.ALL | filters.VIDEO | filters.AUDIO | filters.PHOTO | filters.VOICE | filters.ANIMATION) & ~filters.COMMAND,
                conv_upload_file
            )],
            UP_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_upload_name)],
            UP_DESC: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_upload_desc)],
            UP_PRICE: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_upload_price)],
            UP_PREVIEW: [
                CallbackQueryHandler(cb_upload_publish, pattern="^up:publish$"),
                CallbackQueryHandler(cb_upload_edit, pattern="^up:edit$"),
                CallbackQueryHandler(cb_upload_cancel, pattern="^up:cancel$"),
            ],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(upload_conv)

    app.add_handler(CallbackQueryHandler(cb_mf_list, pattern=r"^mf:list:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_mf_view, pattern=r"^mf:view:\d+:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_mf_delete, pattern=r"^mf:delete:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_mf_delete_confirm, pattern=r"^mf:delconfirm:\d+$"))

    edit_field_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_mf_edit_field, pattern=r"^mf:(ename|edesc|eprice|etier):\d+$")],
        states={EF_FIELD: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_edit_field_value)]},
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(edit_field_conv)

    fc_add_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_fc_add_start, pattern="^fc:add$")],
        states={
            FC_ADD: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_fc_add)],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(fc_add_conv)
    app.add_handler(CallbackQueryHandler(cb_fc_list, pattern="^fc:list$"))
    app.add_handler(CallbackQueryHandler(cb_fc_remove_menu, pattern="^fc:remove$"))
    app.add_handler(CallbackQueryHandler(cb_fc_remove_confirm, pattern=r"^fc:rm:\d+$"))

    wm_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_wm_action_start, pattern="^wm:(add|remove|reset|setbal)$")],
        states={
            UM_SEARCH: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_wm_user_id)],
            UM_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_wm_amount)],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(wm_conv)
    app.add_handler(CallbackQueryHandler(cb_wm_history, pattern="^wm:history$"))

    wb_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_wm_bulk_start, pattern="^wm:bulk$")],
        states={
            WB_IDS: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_wm_bulk_ids)],
            WB_ACTION: [
                CallbackQueryHandler(cb_wb_action_coins, pattern="^wb:(add|remove)$"),
                CallbackQueryHandler(cb_wb_action_ban, pattern="^wb:(ban|unban)$"),
                CallbackQueryHandler(cb_wb_action_premium_menu, pattern="^wb:premium$"),
                CallbackQueryHandler(cb_wb_cancel, pattern="^wb:cancel$"),
            ],
            WB_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_wm_bulk_amount)],
            WB_PREMIUM: [CallbackQueryHandler(cb_wb_action_premium_set, pattern=r"^wb:pset:\d+$")],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(wb_conv)


    rm_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_rm_create_start, pattern="^rm:create$")],
        states={
            RM_CODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_rm_code)],
            RM_COINS: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_rm_coins)],
            RM_PREMIUM: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_rm_premium)],
            RM_LIMIT: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_rm_limit)],
            RM_EXPIRY: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_rm_expiry)],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(rm_conv)
    app.add_handler(CallbackQueryHandler(cb_rm_list, pattern="^rm:list$"))
    app.add_handler(CallbackQueryHandler(cb_rm_delete_all_confirm, pattern="^rm:delall$"))
    app.add_handler(CallbackQueryHandler(cb_rm_delete_all_execute, pattern="^rm:delallconfirm$"))

    rm_delete_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_rm_delete_start, pattern="^rm:delstart$")],
        states={RM_DELETE: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_rm_delete)]},
        fallbacks=[CallbackQueryHandler(cb_rm_delete_cancel, pattern="^rm:delcancel$"), CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(rm_delete_conv)

    um_conv = ConversationHandler(
        entry_points=[
            CallbackQueryHandler(cb_admin_usermgr, pattern="^ad:usermgr$"),
            MessageHandler(filters.Regex("^👥 User Manager$"), cb_admin_usermgr),
            CallbackQueryHandler(cb_um_coins_start, pattern=r"^um:(addc|remc):\d+$"),
        ],
        states={
            UM_SEARCH: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_um_search)],
            UM_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_um_coins_amount)],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(um_conv)
    app.add_handler(CallbackQueryHandler(cb_um_ban, pattern=r"^um:(ban|unban):\d+$"))
    app.add_handler(CallbackQueryHandler(cb_um_premium, pattern=r"^um:(givep|remp):\d+$"))
    app.add_handler(CallbackQueryHandler(cb_um_pset, pattern=r"^um:pset:\d+:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_um_back, pattern=r"^um:back:\d+$"))

    app.add_handler(CallbackQueryHandler(cb_au_list, pattern=r"^au:list:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_au_view, pattern=r"^au:view:\d+:\d+$"))

    broadcast_conv = ConversationHandler(
        entry_points=[
            CallbackQueryHandler(cb_admin_broadcast_start, pattern="^ad:broadcast$"),
            MessageHandler(filters.Regex("^📢 Broadcast$"), cb_admin_broadcast_start),
        ],
        states={BR_CONTENT: [MessageHandler(
            (filters.TEXT | filters.PHOTO | filters.VIDEO | filters.ANIMATION | filters.Sticker.ALL |
             filters.Document.ALL | filters.VOICE | filters.AUDIO) & ~filters.COMMAND,
            conv_broadcast_content
        )]},
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(broadcast_conv)

    settings_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_settings_field, pattern=r"^set:\w+$")],
        states={ST_VALUE: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_settings_value)]},
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(settings_conv)

    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, text_router))

    app.add_handler(CommandHandler("cancel", cmd_cancel), group=1)

    app.add_error_handler(error_handler)
    return app


async def post_init(app: Application) -> None:
    try:
        await init_db(bot=app.bot, require_channel=CHANNEL_DB_REQUIRED)
    except ChannelDatabaseError as exc:
        log.error("Channel database startup failed: %s", exc)
        try:
            await app.bot.send_message(
                OWNER_ID,
                "❌ Channel database startup failed.\n\n"
                f"{html.escape(str(exc))}\n\n"
                "The bot was not started. Fix DATABASE_CHANNEL_ID and permissions, "
                "then restart.",
                parse_mode=ParseMode.HTML,
            )
        except TelegramError:
            log.exception("Could not notify the owner about the channel database error")
        raise
    await init_db_pool()
    if app.job_queue:
        app.job_queue.run_repeating(job_expire_premium, interval=3600, first=10)
        app.job_queue.run_repeating(job_expire_redeem_codes, interval=3600, first=15)
        app.job_queue.run_repeating(job_channel_db_flush, interval=60, first=60)
    log.info("Bot initialized and ready.")


async def post_shutdown(app: Application) -> None:
    if _channel_db is not None:
        try:
            await _channel_db.shutdown()
        except Exception:
            log.exception("Channel database shutdown flush failed")
    await close_db_pool()


def main() -> None:
    if not BOT_TOKEN:
        log.error(
            "BOT_TOKEN is not set. Export BOT_TOKEN=<your token> or create "
            "bot_token.txt next to this script."
        )
        raise SystemExit(1)
    if CHANNEL_DB_REQUIRED and not DATABASE_CHANNEL_ID:
        log.error(
            "DATABASE_CHANNEL_ID is not set. Create a private channel, add the bot "
            "as an administrator with post/pin/delete permissions, then set "
            "DATABASE_CHANNEL_ID to the channel's numeric ID. Use "
            "CHANNEL_DB_REQUIRED=0 only for local-only development."
        )
        raise SystemExit(1)
    app = build_application()
    log.info("Starting 𝐙𝚇 𝐒ᴛᴏʀᴇ BOT...")
    app.run_polling(
        allowed_updates=["message", "callback_query"],
        drop_pending_updates=True,
    )


if __name__ == "__main__":
    main()
