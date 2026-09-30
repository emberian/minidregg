//! Opaque, fallible exact-byte SQLite compare-and-swap transport.
//!
//! This crate assigns no Hyperdocument, link, authorization, replay, checksum,
//! or acceptance meaning to the bytes.  It uses SQLite's rollback-journal
//! transaction boundary and returns only bytes, control status, or an error.
//! Lean owns all semantic decoding and acceptance.
//!
//! Successful `PRAGMA synchronous=EXTRA`, `BEGIN IMMEDIATE`, and `COMMIT`
//! calls are observations of the linked SQLite/host stack.  They are not a
//! proof of SQLite, POSIX locks, filesystem ordering, `fsync`, stable media,
//! power-loss survival, or behavior under hostile directory mutation.

use std::ffi::{c_char, c_int, c_void, CStr, CString};
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::ptr::{self, NonNull};
use std::slice;

// A deployment bound, not a semantic resource allowance. Lean owns the
// snapshot/journal encoding and the exact resource charge of each intent.
pub const MAX_RECORD_BYTES: usize = 64 * 1024 * 1024;
const DATABASE_NAME: &str = "forward-link.sqlite3";

const SQLITE_OK: c_int = 0;
const SQLITE_ROW: c_int = 100;
const SQLITE_DONE: c_int = 101;
const SQLITE_OPEN_READWRITE: c_int = 0x0000_0002;
const SQLITE_OPEN_CREATE: c_int = 0x0000_0004;
const SQLITE_OPEN_FULLMUTEX: c_int = 0x0001_0000;
const SQLITE_OPEN_NOFOLLOW: c_int = 0x0100_0000;

#[repr(C)]
struct sqlite3 {
    _private: [u8; 0],
}

#[repr(C)]
struct sqlite3_stmt {
    _private: [u8; 0],
}

#[link(name = "sqlite3")]
extern "C" {
    fn sqlite3_open_v2(
        filename: *const c_char,
        database: *mut *mut sqlite3,
        flags: c_int,
        vfs: *const c_char,
    ) -> c_int;
    fn sqlite3_close_v2(database: *mut sqlite3) -> c_int;
    fn sqlite3_errmsg(database: *mut sqlite3) -> *const c_char;
    fn sqlite3_extended_errcode(database: *mut sqlite3) -> c_int;
    fn sqlite3_busy_timeout(database: *mut sqlite3, milliseconds: c_int) -> c_int;
    fn sqlite3_exec(
        database: *mut sqlite3,
        sql: *const c_char,
        callback: Option<unsafe extern "C" fn() -> c_int>,
        callback_argument: *mut c_void,
        error_message: *mut *mut c_char,
    ) -> c_int;
    fn sqlite3_prepare_v2(
        database: *mut sqlite3,
        sql: *const c_char,
        sql_bytes: c_int,
        statement: *mut *mut sqlite3_stmt,
        tail: *mut *const c_char,
    ) -> c_int;
    fn sqlite3_step(statement: *mut sqlite3_stmt) -> c_int;
    fn sqlite3_finalize(statement: *mut sqlite3_stmt) -> c_int;
    fn sqlite3_bind_blob(
        statement: *mut sqlite3_stmt,
        index: c_int,
        value: *const c_void,
        bytes: c_int,
        destructor: Option<unsafe extern "C" fn(*mut c_void)>,
    ) -> c_int;
    fn sqlite3_column_blob(statement: *mut sqlite3_stmt, column: c_int) -> *const c_void;
    fn sqlite3_column_bytes(statement: *mut sqlite3_stmt, column: c_int) -> c_int;
    fn sqlite3_column_int(statement: *mut sqlite3_stmt, column: c_int) -> c_int;
    fn sqlite3_column_int64(statement: *mut sqlite3_stmt, column: c_int) -> i64;
    fn sqlite3_bind_int64(statement: *mut sqlite3_stmt, index: c_int, value: i64) -> c_int;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PublishStatus {
    Installed,
    AlreadyPresent,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PublishPhase {
    Begun,
    Inserted,
    Committed,
}

#[derive(Debug)]
pub enum StoreError {
    Missing,
    TooLarge { actual: usize, maximum: usize },
    Conflict,
    /// The Store holds the retired single whole-image record. It is never
    /// reinterpreted as a durable log; the deployment must re-genesis.
    RetiredImage,
    InvalidRoot(PathBuf),
    InvalidPath,
    Sqlite { code: i32, message: String },
    Io(io::Error),
}

impl fmt::Display for StoreError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Missing => formatter.write_str("published byte record is missing"),
            Self::TooLarge { actual, maximum } => {
                write!(formatter, "record has {actual} bytes; maximum is {maximum}")
            }
            Self::Conflict => {
                formatter.write_str("current bytes differ from expected and proposed bytes")
            }
            Self::RetiredImage => formatter.write_str(
                "store holds a retired whole-image record; re-genesis (no migration)",
            ),
            Self::InvalidRoot(path) => {
                write!(
                    formatter,
                    "store root is not a real directory: {}",
                    path.display()
                )
            }
            Self::InvalidPath => formatter.write_str("store path cannot be passed to SQLite"),
            Self::Sqlite { code, message } => {
                write!(formatter, "opaque SQLite failure {code}: {message}")
            }
            Self::Io(error) => write!(formatter, "opaque filesystem failure: {error}"),
        }
    }
}

impl std::error::Error for StoreError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            _ => None,
        }
    }
}

impl From<io::Error> for StoreError {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

struct Database {
    raw: NonNull<sqlite3>,
}

impl Database {
    fn error(&self, fallback_code: c_int) -> StoreError {
        // SAFETY: `raw` is an open SQLite handle for the lifetime of `self`.
        let code = unsafe { sqlite3_extended_errcode(self.raw.as_ptr()) };
        // SAFETY: SQLite owns a nul-terminated message valid until the next
        // call on this connection.  We copy it immediately.
        let message = unsafe {
            let pointer = sqlite3_errmsg(self.raw.as_ptr());
            if pointer.is_null() {
                "unknown SQLite error".to_owned()
            } else {
                CStr::from_ptr(pointer).to_string_lossy().into_owned()
            }
        };
        StoreError::Sqlite {
            code: if code == SQLITE_OK {
                fallback_code
            } else {
                code
            },
            message,
        }
    }

    fn exec(&self, sql: &'static [u8]) -> Result<(), StoreError> {
        debug_assert_eq!(sql.last(), Some(&0));
        // SAFETY: `sql` is nul terminated and the database handle is live.
        let code = unsafe {
            sqlite3_exec(
                self.raw.as_ptr(),
                sql.as_ptr().cast(),
                None,
                ptr::null_mut(),
                ptr::null_mut(),
            )
        };
        if code == SQLITE_OK {
            Ok(())
        } else {
            Err(self.error(code))
        }
    }

    fn prepare(&self, sql: &'static [u8]) -> Result<Statement<'_>, StoreError> {
        debug_assert_eq!(sql.last(), Some(&0));
        let mut raw = ptr::null_mut();
        // SAFETY: arguments satisfy SQLite's prepare contract and `raw` is an
        // out pointer initialized by SQLite on success.
        let code = unsafe {
            sqlite3_prepare_v2(
                self.raw.as_ptr(),
                sql.as_ptr().cast(),
                -1,
                &mut raw,
                ptr::null_mut(),
            )
        };
        if code != SQLITE_OK {
            return Err(self.error(code));
        }
        let raw = NonNull::new(raw).ok_or_else(|| self.error(code))?;
        Ok(Statement {
            database: self,
            raw,
        })
    }
}

impl Drop for Database {
    fn drop(&mut self) {
        // SAFETY: the handle was returned by `sqlite3_open_v2`; all statements
        // borrow it and therefore have been dropped first.
        let _ = unsafe { sqlite3_close_v2(self.raw.as_ptr()) };
    }
}

struct Statement<'database> {
    database: &'database Database,
    raw: NonNull<sqlite3_stmt>,
}

impl Statement<'_> {
    fn step(&self) -> Result<c_int, StoreError> {
        // SAFETY: `raw` is a prepared, non-finalized statement.
        let code = unsafe { sqlite3_step(self.raw.as_ptr()) };
        if code == SQLITE_ROW || code == SQLITE_DONE {
            Ok(code)
        } else {
            Err(self.database.error(code))
        }
    }

    fn bind_blob(&self, bytes: &[u8]) -> Result<(), StoreError> {
        // SQLITE_STATIC (`None`) is sound because `bytes` outlives this
        // statement and the statement is stepped/finalized before returning.
        let code = unsafe {
            sqlite3_bind_blob(
                self.raw.as_ptr(),
                1,
                bytes.as_ptr().cast(),
                bytes.len() as c_int,
                None,
            )
        };
        if code == SQLITE_OK {
            Ok(())
        } else {
            Err(self.database.error(code))
        }
    }

    fn bind_blob_at(&self, index: c_int, bytes: &[u8]) -> Result<(), StoreError> {
        // SQLITE_STATIC (`None`): `bytes` outlives the statement's use.
        let code = unsafe {
            sqlite3_bind_blob(
                self.raw.as_ptr(),
                index,
                bytes.as_ptr().cast(),
                bytes.len() as c_int,
                None,
            )
        };
        if code == SQLITE_OK {
            Ok(())
        } else {
            Err(self.database.error(code))
        }
    }

    fn bind_int64(&self, index: c_int, value: i64) -> Result<(), StoreError> {
        // SAFETY: `raw` is a prepared, non-finalized statement.
        let code = unsafe { sqlite3_bind_int64(self.raw.as_ptr(), index, value) };
        if code == SQLITE_OK {
            Ok(())
        } else {
            Err(self.database.error(code))
        }
    }

    fn column_int64(&self, column: c_int) -> i64 {
        // SAFETY: called only while the statement is on SQLITE_ROW.
        unsafe { sqlite3_column_int64(self.raw.as_ptr(), column) }
    }

    fn column_blob(&self) -> Result<Vec<u8>, StoreError> {
        self.column_blob_at(0)
    }

    fn column_blob_at(&self, column: c_int) -> Result<Vec<u8>, StoreError> {
        // SAFETY: this is called only while the statement is on SQLITE_ROW.
        let length = unsafe { sqlite3_column_bytes(self.raw.as_ptr(), column) };
        if length < 0 {
            return Err(self.database.error(length));
        }
        let length = length as usize;
        if length > MAX_RECORD_BYTES {
            return Err(StoreError::TooLarge {
                actual: length,
                maximum: MAX_RECORD_BYTES,
            });
        }
        // SAFETY: SQLite guarantees at least `length` bytes until the next
        // step/finalize.  A zero-length blob may have a null pointer.
        let pointer = unsafe { sqlite3_column_blob(self.raw.as_ptr(), column) }.cast::<u8>();
        if length == 0 {
            Ok(Vec::new())
        } else if pointer.is_null() {
            Err(self.database.error(SQLITE_OK))
        } else {
            Ok(unsafe { slice::from_raw_parts(pointer, length) }.to_vec())
        }
    }
}

impl Drop for Statement<'_> {
    fn drop(&mut self) {
        // SAFETY: `raw` is finalized exactly once here.
        let _ = unsafe { sqlite3_finalize(self.raw.as_ptr()) };
    }
}

struct Transaction<'store> {
    store: &'store SqliteByteStore,
    active: bool,
}

impl Transaction<'_> {
    fn commit(mut self) -> Result<(), StoreError> {
        self.store.database.exec(b"COMMIT\0")?;
        self.active = false;
        Ok(())
    }
}

impl Drop for Transaction<'_> {
    fn drop(&mut self) {
        if self.active {
            let _ = self.store.database.exec(b"ROLLBACK\0");
        }
    }
}

pub struct SqliteByteStore {
    root: PathBuf,
    database_path: PathBuf,
    database: Database,
}

// Existing link clients use the exact same transport. This alias carries no
// separate publication implementation or semantic store.
pub type SqliteLinkStore = SqliteByteStore;

impl SqliteByteStore {
    pub fn open(root: impl AsRef<Path>) -> Result<Self, StoreError> {
        fs::create_dir_all(root.as_ref())?;
        // Canonicalize the already-created directory before asking SQLite for
        // `SQLITE_OPEN_NOFOLLOW`.  On macOS `/var` itself is a compatibility
        // symlink to `/private/var`; retaining that spelling would make the
        // deliberately strict open reject an otherwise real test directory.
        let root = fs::canonicalize(root.as_ref())?;
        let metadata = fs::symlink_metadata(&root)?;
        if !metadata.file_type().is_dir() || metadata.file_type().is_symlink() {
            return Err(StoreError::InvalidRoot(root));
        }
        let database_path = root.join(DATABASE_NAME);
        let filename = CString::new(database_path.to_string_lossy().as_bytes())
            .map_err(|_| StoreError::InvalidPath)?;
        let mut raw = ptr::null_mut();
        // SAFETY: filename is nul terminated and `raw` is an out pointer.
        let code = unsafe {
            sqlite3_open_v2(
                filename.as_ptr(),
                &mut raw,
                SQLITE_OPEN_READWRITE
                    | SQLITE_OPEN_CREATE
                    | SQLITE_OPEN_FULLMUTEX
                    | SQLITE_OPEN_NOFOLLOW,
                ptr::null(),
            )
        };
        let raw = match NonNull::new(raw) {
            Some(raw) => raw,
            None => {
                return Err(StoreError::Sqlite {
                    code,
                    message: "SQLite returned no database handle".to_owned(),
                })
            }
        };
        let database = Database { raw };
        if code != SQLITE_OK {
            return Err(database.error(code));
        }
        // SAFETY: the database handle is open.  A bounded wait turns lock
        // contention into an opaque, fallible result rather than an unbounded
        // native promise.
        let busy = unsafe { sqlite3_busy_timeout(database.raw.as_ptr(), 5_000) };
        if busy != SQLITE_OK {
            return Err(database.error(busy));
        }
        database.exec(b"PRAGMA trusted_schema=OFF\0")?;
        database.exec(b"PRAGMA journal_mode=DELETE\0")?;
        database.exec(b"PRAGMA synchronous=EXTRA\0")?;
        database.exec(b"PRAGMA fullfsync=ON\0")?;
        database.exec(b"PRAGMA checkpoint_fullfsync=ON\0")?;
        let store = Self {
            root,
            database_path,
            database,
        };
        store.upgrade_schema()?;
        Ok(store)
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn database_path(&self) -> &Path {
        &self.database_path
    }

    fn upgrade_schema(&self) -> Result<(), StoreError> {
        self.database.exec(b"BEGIN IMMEDIATE\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        let statement = self.database.prepare(b"PRAGMA user_version\0")?;
        if statement.step()? != SQLITE_ROW {
            return Err(self.database.error(SQLITE_DONE));
        }
        // SAFETY: the pragma result has one integer column and is on ROW.
        let version = unsafe { sqlite3_column_int(statement.raw.as_ptr(), 0) };
        drop(statement);
        match version {
            0 => {
                // Preserve the old one-shot table's exact BLOB while replacing
                // its 4096-byte bound, all within one SQLite transaction.
                self.database.exec(b"CREATE TABLE IF NOT EXISTS opaque_record (slot INTEGER PRIMARY KEY CHECK(slot=1), bytes BLOB NOT NULL CHECK(length(bytes)<=4096)) WITHOUT ROWID\0")?;
                self.database.exec(b"CREATE TABLE opaque_record_v2 (slot INTEGER PRIMARY KEY CHECK(slot=1), bytes BLOB NOT NULL CHECK(length(bytes)<=67108864)) WITHOUT ROWID\0")?;
                self.database
                    .exec(b"INSERT INTO opaque_record_v2 SELECT slot,bytes FROM opaque_record\0")?;
                self.database.exec(b"DROP TABLE opaque_record\0")?;
                self.database
                    .exec(b"ALTER TABLE opaque_record_v2 RENAME TO opaque_record\0")?;
                Self::create_durable_tables(&self.database)?;
                self.database.exec(b"PRAGMA user_version=3\0")?;
            }
            2 => {
                Self::create_durable_tables(&self.database)?;
                self.database.exec(b"PRAGMA user_version=3\0")?;
            }
            3 => {}
            _ => {
                return Err(StoreError::Sqlite {
                    code: version,
                    message: "unsupported opaque byte-store schema version".to_owned(),
                })
            }
        }
        transaction.commit()
    }

    fn create_durable_tables(database: &Database) -> Result<(), StoreError> {
        database.exec(b"CREATE TABLE IF NOT EXISTS durable_seed (slot INTEGER PRIMARY KEY CHECK(slot=1), bytes BLOB NOT NULL CHECK(length(bytes)<=67108864)) WITHOUT ROWID\0")?;
        database.exec(b"CREATE TABLE IF NOT EXISTS durable_log (height INTEGER PRIMARY KEY CHECK(height>=1), record BLOB NOT NULL CHECK(length(record)<=67108864), tag BLOB NOT NULL CHECK(length(tag)<=4096))\0")?;
        database.exec(b"CREATE TABLE IF NOT EXISTS durable_checkpoint (height INTEGER PRIMARY KEY CHECK(height>=1), bytes BLOB NOT NULL CHECK(length(bytes)<=67108864))\0")
    }

    fn validate_bound(bytes: &[u8]) -> Result<(), StoreError> {
        if bytes.len() > MAX_RECORD_BYTES {
            Err(StoreError::TooLarge {
                actual: bytes.len(),
                maximum: MAX_RECORD_BYTES,
            })
        } else {
            Ok(())
        }
    }

    fn select_record(&self) -> Result<Option<Vec<u8>>, StoreError> {
        let statement = self
            .database
            .prepare(b"SELECT bytes FROM opaque_record WHERE slot=1\0")?;
        match statement.step()? {
            SQLITE_ROW => Ok(Some(statement.column_blob()?)),
            SQLITE_DONE => Ok(None),
            _ => unreachable!("step accepts only ROW or DONE"),
        }
    }

    pub fn read(&self) -> Result<Vec<u8>, StoreError> {
        self.select_record()?.ok_or(StoreError::Missing)
    }

    pub fn publish(&self, bytes: &[u8]) -> Result<PublishStatus, StoreError> {
        self.compare_exchange(None, bytes)
    }

    pub fn publish_with_hook<F>(&self, bytes: &[u8], hook: F) -> Result<PublishStatus, StoreError>
    where
        F: FnMut(PublishPhase),
    {
        self.compare_exchange_with_hook(None, bytes, hook)
    }

    /// Exact-byte CAS with idempotent recognition of the proposed post image.
    /// `None` means physically absent; an empty BLOB is `Some(&[])`.
    /// No digest, transaction id, or semantic field is interpreted here.
    pub fn compare_exchange(
        &self,
        expected: Option<&[u8]>,
        proposed: &[u8],
    ) -> Result<PublishStatus, StoreError> {
        self.compare_exchange_with_hook(expected, proposed, |_| {})
    }

    pub fn compare_exchange_with_hook<F>(
        &self,
        expected: Option<&[u8]>,
        proposed: &[u8],
        mut hook: F,
    ) -> Result<PublishStatus, StoreError>
    where
        F: FnMut(PublishPhase),
    {
        Self::validate_bound(proposed)?;
        if let Some(expected) = expected {
            Self::validate_bound(expected)?;
        }
        self.database.exec(b"BEGIN IMMEDIATE\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        hook(PublishPhase::Begun);

        let current = self.select_record()?;
        if current.as_deref() == Some(proposed) {
            transaction.commit()?;
            hook(PublishPhase::Committed);
            return Ok(PublishStatus::AlreadyPresent);
        }
        if current.as_deref() != expected {
            return Err(StoreError::Conflict);
        }

        let statement = self
            .database
            .prepare(b"INSERT INTO opaque_record(slot,bytes) VALUES(1,?1) ON CONFLICT(slot) DO UPDATE SET bytes=excluded.bytes\0")?;
        statement.bind_blob(proposed)?;
        let status = statement.step()?;
        if status != SQLITE_DONE {
            return Err(self.database.error(status));
        }
        drop(statement);
        hook(PublishPhase::Inserted);
        transaction.commit()?;
        hook(PublishPhase::Committed);
        Ok(PublishStatus::Installed)
    }
}


/// The durable log interface: a seed, an append-only log of opaque
/// `(record, tag)` entries at consecutive heights from 1, and opaque
/// checkpoints keyed by height. Lean owns every byte's meaning, the chain and
/// the MAC; this store only enforces "append `h + 1` while the head is `h`".
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DurableEntry {
    pub height: u64,
    pub record: Vec<u8>,
    pub tag: Vec<u8>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DurableRead {
    pub head: u64,
    pub base: Option<(Vec<u8>, Option<(u64, Vec<u8>)>)>,
    pub entries: Vec<DurableEntry>,
}

const CHECKPOINTS_RETAINED: i64 = 2;

impl SqliteByteStore {
    fn refuse_retired_image(&self) -> Result<(), StoreError> {
        if self.select_record()?.is_some() {
            Err(StoreError::RetiredImage)
        } else {
            Ok(())
        }
    }

    fn durable_seed(&self) -> Result<Option<Vec<u8>>, StoreError> {
        let statement = self
            .database
            .prepare(b"SELECT bytes FROM durable_seed WHERE slot=1\0")?;
        match statement.step()? {
            SQLITE_ROW => Ok(Some(statement.column_blob()?)),
            _ => Ok(None),
        }
    }

    fn durable_head(&self) -> Result<u64, StoreError> {
        let statement = self
            .database
            .prepare(b"SELECT COALESCE(MAX(height),0) FROM durable_log\0")?;
        if statement.step()? != SQLITE_ROW {
            return Err(self.database.error(SQLITE_DONE));
        }
        Ok(statement.column_int64(0) as u64)
    }

    fn durable_entry(&self, height: u64) -> Result<Option<DurableEntry>, StoreError> {
        let statement = self
            .database
            .prepare(b"SELECT record, tag FROM durable_log WHERE height=?1\0")?;
        statement.bind_int64(1, height as i64)?;
        match statement.step()? {
            SQLITE_ROW => Ok(Some(DurableEntry {
                height,
                record: statement.column_blob_at(0)?,
                tag: statement.column_blob_at(1)?,
            })),
            _ => Ok(None),
        }
    }

    /// Install the seed once. The same seed again is `AlreadyPresent`; a
    /// different seed, or any seed over an existing log, is a conflict.
    pub fn durable_init(&self, seed: &[u8]) -> Result<PublishStatus, StoreError> {
        Self::validate_bound(seed)?;
        self.database.exec(b"BEGIN IMMEDIATE\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        self.refuse_retired_image()?;
        match self.durable_seed()? {
            Some(current) if current == seed => {
                transaction.commit()?;
                return Ok(PublishStatus::AlreadyPresent);
            }
            Some(_) => return Err(StoreError::Conflict),
            None => {}
        }
        if self.durable_head()? != 0 {
            return Err(StoreError::Conflict);
        }
        let statement = self
            .database
            .prepare(b"INSERT INTO durable_seed(slot,bytes) VALUES(1,?1)\0")?;
        statement.bind_blob(seed)?;
        if statement.step()? != SQLITE_DONE {
            return Err(self.database.error(SQLITE_DONE));
        }
        drop(statement);
        transaction.commit()?;
        Ok(PublishStatus::Installed)
    }

    /// One consistent read: the head, optionally the seed and the latest
    /// checkpoint, and every entry at `from` or above.
    pub fn durable_read(&self, from: u64, with_base: bool) -> Result<DurableRead, StoreError> {
        self.database.exec(b"BEGIN DEFERRED\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        self.refuse_retired_image()?;
        let seed = self.durable_seed()?.ok_or(StoreError::Missing)?;
        let head = self.durable_head()?;
        let base = if with_base {
            let statement = self.database.prepare(
                b"SELECT height, bytes FROM durable_checkpoint ORDER BY height DESC LIMIT 1\0",
            )?;
            let checkpoint = match statement.step()? {
                SQLITE_ROW => Some((
                    statement.column_int64(0) as u64,
                    statement.column_blob_at(1)?,
                )),
                _ => None,
            };
            Some((seed, checkpoint))
        } else {
            None
        };
        let mut entries = Vec::new();
        {
            let statement = self.database.prepare(
                b"SELECT height, record, tag FROM durable_log WHERE height>=?1 ORDER BY height\0",
            )?;
            statement.bind_int64(1, from.max(1) as i64)?;
            while statement.step()? == SQLITE_ROW {
                entries.push(DurableEntry {
                    height: statement.column_int64(0) as u64,
                    record: statement.column_blob_at(1)?,
                    tag: statement.column_blob_at(2)?,
                });
            }
        }
        transaction.commit()?;
        Ok(DurableRead {
            head,
            base,
            entries,
        })
    }

    /// Append entry `height` iff the head is `height - 1`. The identical entry
    /// already at `height` is `AlreadyPresent`; anything else is a conflict.
    pub fn durable_append(
        &self,
        height: u64,
        record: &[u8],
        tag: &[u8],
    ) -> Result<PublishStatus, StoreError> {
        self.durable_append_with_hook(height, record, tag, |_| {})
    }

    pub fn durable_append_with_hook<F>(
        &self,
        height: u64,
        record: &[u8],
        tag: &[u8],
        mut hook: F,
    ) -> Result<PublishStatus, StoreError>
    where
        F: FnMut(PublishPhase),
    {
        Self::validate_bound(record)?;
        if height == 0 || tag.len() > 4096 {
            return Err(StoreError::Conflict);
        }
        self.database.exec(b"BEGIN IMMEDIATE\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        hook(PublishPhase::Begun);
        self.refuse_retired_image()?;
        if self.durable_seed()?.is_none() {
            return Err(StoreError::Missing);
        }
        if let Some(existing) = self.durable_entry(height)? {
            if existing.record == record && existing.tag == tag {
                transaction.commit()?;
                hook(PublishPhase::Committed);
                return Ok(PublishStatus::AlreadyPresent);
            }
            return Err(StoreError::Conflict);
        }
        if self.durable_head()? != height - 1 {
            return Err(StoreError::Conflict);
        }
        let statement = self
            .database
            .prepare(b"INSERT INTO durable_log(height,record,tag) VALUES(?1,?2,?3)\0")?;
        statement.bind_int64(1, height as i64)?;
        statement.bind_blob_at(2, record)?;
        statement.bind_blob_at(3, tag)?;
        if statement.step()? != SQLITE_DONE {
            return Err(self.database.error(SQLITE_DONE));
        }
        drop(statement);
        hook(PublishPhase::Inserted);
        transaction.commit()?;
        hook(PublishPhase::Committed);
        Ok(PublishStatus::Installed)
    }

    /// Store a checkpoint at `height` (at most the head), replacing one at the
    /// same height (a key rotation re-seals), and keep only the latest two.
    pub fn durable_checkpoint(&self, height: u64, bytes: &[u8]) -> Result<(), StoreError> {
        Self::validate_bound(bytes)?;
        self.database.exec(b"BEGIN IMMEDIATE\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        self.refuse_retired_image()?;
        if height == 0 || height > self.durable_head()? {
            return Err(StoreError::Conflict);
        }
        let statement = self.database.prepare(
            b"INSERT INTO durable_checkpoint(height,bytes) VALUES(?1,?2) ON CONFLICT(height) DO UPDATE SET bytes=excluded.bytes\0",
        )?;
        statement.bind_int64(1, height as i64)?;
        statement.bind_blob_at(2, bytes)?;
        if statement.step()? != SQLITE_DONE {
            return Err(self.database.error(SQLITE_DONE));
        }
        drop(statement);
        let prune = self.database.prepare(
            b"DELETE FROM durable_checkpoint WHERE height NOT IN (SELECT height FROM durable_checkpoint ORDER BY height DESC LIMIT ?1)\0",
        )?;
        prune.bind_int64(1, CHECKPOINTS_RETAINED)?;
        if prune.step()? != SQLITE_DONE {
            return Err(self.database.error(SQLITE_DONE));
        }
        drop(prune);
        transaction.commit()
    }
}

/// The read file Lean parses: big-endian u64 head; u64 base flag (0/1); when
/// 1, the seed blob, a u64 checkpoint flag and, when 1, its u64 height and
/// blob; a u64 entry count; per entry u64 height, record blob, tag blob.
/// A blob is a u64 length and its bytes.
pub fn encode_durable_read(read: &DurableRead) -> Vec<u8> {
    fn blob(out: &mut Vec<u8>, bytes: &[u8]) {
        out.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
        out.extend_from_slice(bytes);
    }
    let mut out = Vec::new();
    out.extend_from_slice(&read.head.to_be_bytes());
    match &read.base {
        None => out.extend_from_slice(&0u64.to_be_bytes()),
        Some((seed, checkpoint)) => {
            out.extend_from_slice(&1u64.to_be_bytes());
            blob(&mut out, seed);
            match checkpoint {
                None => out.extend_from_slice(&0u64.to_be_bytes()),
                Some((height, bytes)) => {
                    out.extend_from_slice(&1u64.to_be_bytes());
                    out.extend_from_slice(&height.to_be_bytes());
                    blob(&mut out, bytes);
                }
            }
        }
    }
    out.extend_from_slice(&(read.entries.len() as u64).to_be_bytes());
    for entry in &read.entries {
        out.extend_from_slice(&entry.height.to_be_bytes());
        blob(&mut out, &entry.record);
        blob(&mut out, &entry.tag);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn old_bounded_table_upgrades_without_rewriting_its_blob() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "dregg-sqlite-upgrade-{}-{nonce}",
            std::process::id()
        ));
        let store = SqliteByteStore::open(&root).unwrap();
        // Build the exact old physical schema in this isolated test database.
        store.database.exec(b"DROP TABLE opaque_record\0").unwrap();
        store.database.exec(b"CREATE TABLE opaque_record (slot INTEGER PRIMARY KEY CHECK(slot=1), bytes BLOB NOT NULL CHECK(length(bytes)<=4096)) WITHOUT ROWID\0").unwrap();
        store.database.exec(b"PRAGMA user_version=0\0").unwrap();
        store.publish(b"exact legacy payload\0\xff").unwrap();
        drop(store);
        let reopened = SqliteByteStore::open(&root).unwrap();
        assert_eq!(reopened.read().unwrap(), b"exact legacy payload\0\xff");
        let larger = vec![17; 8192];
        assert_eq!(
            reopened
                .compare_exchange(Some(b"exact legacy payload\0\xff"), &larger)
                .unwrap(),
            PublishStatus::Installed
        );
        assert_eq!(reopened.read().unwrap(), larger);
        drop(reopened);
        fs::remove_dir_all(root).unwrap();
    }

    fn fresh_root(label: &str) -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        std::env::temp_dir().join(format!(
            "dregg-durable-{label}-{}-{nonce}",
            std::process::id()
        ))
    }

    #[test]
    fn durable_log_appends_only_at_the_head() {
        let root = fresh_root("append");
        let store = SqliteByteStore::open(&root).unwrap();
        assert!(matches!(store.durable_append(1, b"r", b"t"), Err(StoreError::Missing)));
        assert_eq!(store.durable_init(b"seed").unwrap(), PublishStatus::Installed);
        assert_eq!(store.durable_init(b"seed").unwrap(), PublishStatus::AlreadyPresent);
        assert!(matches!(store.durable_init(b"other"), Err(StoreError::Conflict)));
        assert!(matches!(store.durable_append(2, b"r", b"t"), Err(StoreError::Conflict)));
        assert_eq!(store.durable_append(1, b"r1", b"t1").unwrap(), PublishStatus::Installed);
        assert_eq!(store.durable_append(1, b"r1", b"t1").unwrap(), PublishStatus::AlreadyPresent);
        assert!(matches!(store.durable_append(1, b"r1", b"tX"), Err(StoreError::Conflict)));
        assert_eq!(store.durable_append(2, b"r2", b"t2").unwrap(), PublishStatus::Installed);
        assert!(matches!(store.durable_checkpoint(3, b"c"), Err(StoreError::Conflict)));
        store.durable_checkpoint(1, b"c1").unwrap();
        store.durable_checkpoint(2, b"c2").unwrap();
        store.durable_append(3, b"r3", b"t3").unwrap();
        store.durable_checkpoint(3, b"c3").unwrap();
        let read = store.durable_read(2, true).unwrap();
        assert_eq!(read.head, 3);
        assert_eq!(read.base, Some((b"seed".to_vec(), Some((3, b"c3".to_vec())))));
        assert_eq!(read.entries.iter().map(|e| e.height).collect::<Vec<_>>(), vec![2, 3]);
        let tail = store.durable_read(4, false).unwrap();
        assert_eq!((tail.head, tail.base, tail.entries.len()), (3, None, 0));
        drop(store);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn retired_whole_image_store_refuses_the_durable_log() {
        let root = fresh_root("retired");
        let store = SqliteByteStore::open(&root).unwrap();
        store.publish(b"DREGG.DURABLE.IMAGE whole image").unwrap();
        assert!(matches!(store.durable_init(b"seed"), Err(StoreError::RetiredImage)));
        assert!(matches!(store.durable_read(1, true), Err(StoreError::RetiredImage)));
        assert!(matches!(store.durable_append(1, b"r", b"t"), Err(StoreError::RetiredImage)));
        drop(store);
        fs::remove_dir_all(root).unwrap();
    }
}
