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

mod anchor;

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
    AnchorPrepared,
    AnchorRenamed,
    Anchored,
}

#[derive(Debug)]
pub enum StoreError {
    Missing,
    Anchor(&'static str),
    TooLarge {
        actual: usize,
        maximum: usize,
    },
    Conflict,
    /// The Store holds the retired single whole-image record. It is never
    /// reinterpreted as a durable log; the deployment must re-genesis.
    RetiredImage,
    /// A seeded durable Store of an older schema (no history accumulator node
    /// table). Never upgraded in place; the deployment must re-genesis.
    RetiredSchema(i32),
    InvalidRoot(PathBuf),
    InvalidPath,
    Sqlite {
        code: i32,
        message: String,
    },
    Io(io::Error),
}

impl fmt::Display for StoreError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Anchor(reason) => write!(formatter, "durable head anchor refused: {reason}"),
            Self::Missing => formatter.write_str("published byte record is missing"),
            Self::TooLarge { actual, maximum } => {
                write!(formatter, "record has {actual} bytes; maximum is {maximum}")
            }
            Self::Conflict => {
                formatter.write_str("current bytes differ from expected and proposed bytes")
            }
            Self::RetiredImage => formatter
                .write_str("store holds a retired whole-image record; re-genesis (no migration)"),
            Self::RetiredSchema(version) => write!(
                formatter,
                "store schema v{version} predates the durable history accumulator (schema v5: durable_node); re-genesis (no migration)"
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
    anchor_identity: Vec<u8>,
    root: PathBuf,
    database_path: PathBuf,
    database: Database,
}

// Existing link clients use the exact same transport. This alias carries no
// separate publication implementation or semantic store.
pub type SqliteLinkStore = SqliteByteStore;

impl SqliteByteStore {
    pub fn open(root: impl AsRef<Path>) -> Result<Self, StoreError> {
        Self::open_with_identity(root, &[])
    }

    /// Opaque deployment identity supplied by the semantic Host; never parsed here.
    pub fn open_with_identity(root: impl AsRef<Path>, identity: &[u8]) -> Result<Self, StoreError> {
        if identity.len() > 65536 {
            return Err(StoreError::Anchor("identity exceeds 64 KiB"));
        }
        // The Store's directories are its own account's: created owner-private
        // whatever the caller's umask, so the sibling anchor's directory passes
        // its custody check (anchor::custody) by construction.
        {
            use std::os::unix::fs::DirBuilderExt;
            fs::DirBuilder::new().recursive(true).mode(0o700).create(root.as_ref())?;
        }
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
            anchor_identity: identity.to_vec(),
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
                self.database.exec(b"PRAGMA user_version=5\0")?;
            }
            // A v2-v4 Store that holds a durable seed was written without the
            // history accumulator; it refuses by name. An unseeded one (a link
            // store only) gains the durable tables.
            2 | 3 | 4 => {
                if self.holds_durable_seed()? {
                    return Err(StoreError::RetiredSchema(version));
                }
                Self::create_durable_tables(&self.database)?;
                self.database.exec(b"PRAGMA user_version=5\0")?;
            }
            5 => {}
            _ => {
                return Err(StoreError::Sqlite {
                    code: version,
                    message: "unsupported opaque byte-store schema version".to_owned(),
                })
            }
        }
        transaction.commit()
    }

    fn holds_durable_seed(&self) -> Result<bool, StoreError> {
        let statement = self.database.prepare(
            b"SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='durable_seed'\0",
        )?;
        if statement.step()? != SQLITE_ROW {
            return Err(self.database.error(SQLITE_DONE));
        }
        if statement.column_int64(0) == 0 {
            return Ok(false);
        }
        drop(statement);
        Ok(self.durable_seed()?.is_some())
    }

    fn create_durable_tables(database: &Database) -> Result<(), StoreError> {
        // Accumulator nodes (Lean `Compiler.DurableHistory`): opaque, versioned
        // by the height whose append wrote them, written in the same
        // transaction as that entry and never rewritten. Lean verifies every
        // node it reads against its authenticated frontier.
        database.exec(b"CREATE TABLE IF NOT EXISTS durable_node (space INTEGER NOT NULL CHECK(space>=0), key BLOB NOT NULL CHECK(length(key)<=4096), height INTEGER NOT NULL CHECK(height>=1), value BLOB NOT NULL CHECK(length(value)<=4096), PRIMARY KEY(space, key, height)) WITHOUT ROWID\0")?;
        database.exec(b"CREATE TABLE IF NOT EXISTS durable_seed (slot INTEGER PRIMARY KEY CHECK(slot=1), bytes BLOB NOT NULL CHECK(length(bytes)<=67108864)) WITHOUT ROWID\0")?;
        database.exec(b"CREATE TABLE IF NOT EXISTS durable_log (height INTEGER PRIMARY KEY CHECK(height>=1), record BLOB NOT NULL CHECK(length(record)<=67108864), tag BLOB NOT NULL CHECK(length(tag)<=4096))\0")?;
        database.exec(b"CREATE TABLE IF NOT EXISTS durable_checkpoint (height INTEGER PRIMARY KEY CHECK(height>=1), bytes BLOB NOT NULL CHECK(length(bytes)<=67108864))\0")?;
        // The fn archive journal (Lean `Kernel.FnArchiveJournal`): append-only,
        // anchored with the durable log by the same MINIANC2 head.
        database.exec(b"CREATE TABLE IF NOT EXISTS archive_journal (seq INTEGER PRIMARY KEY CHECK(seq>=1), record BLOB NOT NULL CHECK(length(record)<=67108864), tag BLOB NOT NULL CHECK(length(tag)<=4096))\0")
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

/// One fn archive journal entry: Lean-owned record and tag bytes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JournalEntry {
    pub seq: u64,
    pub record: Vec<u8>,
    pub tag: Vec<u8>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct JournalRead {
    pub head: u64,
    pub entries: Vec<JournalEntry>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DurableRead {
    pub head: u64,
    pub base: Option<(Vec<u8>, Option<(u64, Vec<u8>)>)>,
    pub entries: Vec<DurableEntry>,
}

/// One opaque accumulator node written beside a durable log entry.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord)]
pub struct DurableNode {
    pub space: u64,
    pub key: Vec<u8>,
    pub value: Vec<u8>,
}

/// An at-use history read: the head, the requested entries that exist, and
/// for each requested node key its latest version at or below `at`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HistoryRead {
    pub head: u64,
    pub entries: Vec<DurableEntry>,
    pub nodes: Vec<(u64, Vec<u8>, Option<(u64, Vec<u8>)>)>,
}


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

    fn journal_head(&self) -> Result<u64, StoreError> {
        let statement = self
            .database
            .prepare(b"SELECT COALESCE(MAX(seq),0) FROM archive_journal\0")?;
        if statement.step()? != SQLITE_ROW {
            return Err(self.database.error(SQLITE_DONE));
        }
        Ok(statement.column_int64(0) as u64)
    }

    fn journal_entry(&self, seq: u64) -> Result<Option<JournalEntry>, StoreError> {
        let statement = self
            .database
            .prepare(b"SELECT record, tag FROM archive_journal WHERE seq=?1\0")?;
        statement.bind_int64(1, seq as i64)?;
        match statement.step()? {
            SQLITE_ROW => Ok(Some(JournalEntry {
                seq,
                record: statement.column_blob_at(0)?,
                tag: statement.column_blob_at(1)?,
            })),
            _ => Ok(None),
        }
    }

    /// Explicit first enrollment of an existing, separately audited Store.
    /// Never called by ordinary reads: loss of an established anchor must refuse.
    pub fn durable_anchor_enroll(&self) -> Result<(), StoreError> {
        let guard = anchor::Guard::lock(&self.root)?;
        self.database.exec(b"BEGIN IMMEDIATE\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        self.refuse_retired_image()?;
        let seed = self.durable_seed()?.ok_or(StoreError::Missing)?;
        let head = if guard.read()?.is_some() {
            self.anchor_head(&guard, &seed)?
        } else {
            self.current_anchor_head(&seed)?
        };
        transaction.commit()?;
        guard.publish(&head)
    }

    fn current_anchor_head(&self, seed: &[u8]) -> Result<anchor::Head, StoreError> {
        let height = self.durable_head()?;
        let entry = if height == 0 {
            None
        } else {
            self.durable_entry(height)?
        };
        let journal_height = self.journal_head()?;
        let journal = if journal_height == 0 {
            None
        } else {
            self.journal_entry(journal_height)?
        };
        Ok(anchor::Head::new(
            &self.anchor_identity,
            seed,
            entry.as_ref(),
            journal.as_ref(),
        ))
    }

    fn anchor_head(&self, guard: &anchor::Guard, seed: &[u8]) -> Result<anchor::Head, StoreError> {
        let retained = guard.read()?.ok_or(StoreError::Anchor(
            "missing anchor; existing Stores require explicit audited enrollment",
        ))?;
        if self.durable_head()? < retained.height {
            return Err(StoreError::Anchor("Store is behind retained head"));
        }
        if self.journal_head()? < retained.journal_height {
            return Err(StoreError::Anchor("archive journal is behind retained head"));
        }
        let journal = if retained.journal_height == 0 {
            None
        } else {
            Some(
                self.journal_entry(retained.journal_height)?
                    .ok_or(StoreError::Anchor("retained journal entry is missing"))?,
            )
        };
        let entry = if retained.height == 0 {
            None
        } else {
            Some(
                self.durable_entry(retained.height)?
                    .ok_or(StoreError::Anchor("retained entry is missing"))?,
            )
        };
        if retained
            != anchor::Head::new(&self.anchor_identity, seed, entry.as_ref(), journal.as_ref())
        {
            return Err(StoreError::Anchor("genesis or retained head conflicts"));
        }
        self.current_anchor_head(seed)
    }

    /// Install the seed once. The same seed again is `AlreadyPresent`; a
    /// different seed, or any seed over an existing log, is a conflict.
    pub fn durable_init(&self, seed: &[u8]) -> Result<PublishStatus, StoreError> {
        Self::validate_bound(seed)?;
        let guard = anchor::Guard::lock(&self.root)?;
        self.database.exec(b"BEGIN IMMEDIATE\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        self.refuse_retired_image()?;
        match self.durable_seed()? {
            Some(current) if current == seed => {
                let head = self.anchor_head(&guard, seed)?;
                transaction.commit()?;
                guard.publish(&head)?;
                return Ok(PublishStatus::AlreadyPresent);
            }
            Some(_) => return Err(StoreError::Conflict),
            None => {}
        }
        if self.durable_head()? != 0 {
            return Err(StoreError::Conflict);
        }
        let initial = anchor::Head::new(&self.anchor_identity, seed, None, None);
        if guard.read()?.is_some_and(|retained| retained != initial) {
            return Err(StoreError::Anchor(
                "new seed conflicts with retained genesis",
            ));
        }
        // Publish genesis first. An interrupted seed transaction may retry the
        // exact same genesis; it cannot substitute a different one.
        guard.publish(&initial)?;
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

    /// The installed seed bytes alone, without the head anchor: the seed is
    /// written once and never replaced, and Lean reads only its epoch label
    /// from it, so a Store of another epoch refuses by name before the anchor
    /// (whose identity binds that epoch) can only say that it conflicts.
    /// Nothing read here is accepted; every accepting read is `durable_read`.
    pub fn durable_seed_bytes(&self) -> Result<Vec<u8>, StoreError> {
        self.durable_seed()?.ok_or(StoreError::Missing)
    }

    /// One consistent read: the head, optionally the seed and the latest
    /// checkpoint, and every entry at `from` or above.
    pub fn durable_read(&self, from: u64, with_base: bool) -> Result<DurableRead, StoreError> {
        self.durable_read_mode(from, with_base, false)
    }

    /// The open's read: the seed, the latest checkpoint at `c`, and the
    /// entries from `c` (from 1 without a checkpoint) to the head. Entry `c`
    /// is included so its tag binds the checkpoint to the anchored log.
    pub fn durable_read_from_checkpoint(&self) -> Result<DurableRead, StoreError> {
        self.durable_read_mode(1, true, true)
    }

    fn durable_read_mode(
        &self,
        from: u64,
        with_base: bool,
        from_checkpoint: bool,
    ) -> Result<DurableRead, StoreError> {
        let guard = anchor::Guard::lock(&self.root)?;
        self.database.exec(b"BEGIN DEFERRED\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        self.refuse_retired_image()?;
        let seed = self.durable_seed()?.ok_or(StoreError::Missing)?;
        let anchor_head = self.anchor_head(&guard, &seed)?;
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
            let from = match (&base, from_checkpoint) {
                (Some((_, Some((height, _)))), true) => *height,
                _ => from,
            };
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
        guard.publish(&anchor_head)?;
        Ok(DurableRead {
            head,
            base,
            entries,
        })
    }

    /// An at-use history read under the head anchor: the named entries that
    /// exist, and each named node's latest version at or below `at`. Nothing
    /// here is accepted; Lean verifies every byte against its frontier.
    pub fn durable_history(
        &self,
        at: u64,
        heights: &[u64],
        nodes: &[(u64, Vec<u8>)],
    ) -> Result<HistoryRead, StoreError> {
        let guard = anchor::Guard::lock(&self.root)?;
        self.database.exec(b"BEGIN DEFERRED\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        self.refuse_retired_image()?;
        let seed = self.durable_seed()?.ok_or(StoreError::Missing)?;
        let anchor_head = self.anchor_head(&guard, &seed)?;
        let head = self.durable_head()?;
        let mut entries = Vec::new();
        for height in heights {
            if let Some(entry) = self.durable_entry(*height)? {
                entries.push(entry);
            }
        }
        let mut found = Vec::new();
        for (space, key) in nodes {
            let statement = self.database.prepare(
                b"SELECT height, value FROM durable_node WHERE space=?1 AND key=?2 AND height<=?3 ORDER BY height DESC LIMIT 1\0",
            )?;
            statement.bind_int64(1, (*space).min(i64::MAX as u64) as i64)?;
            statement.bind_blob_at(2, key)?;
            statement.bind_int64(3, at.min(i64::MAX as u64) as i64)?;
            let version = match statement.step()? {
                SQLITE_ROW => Some((
                    statement.column_int64(0) as u64,
                    statement.column_blob_at(1)?,
                )),
                _ => None,
            };
            found.push((*space, key.clone(), version));
        }
        transaction.commit()?;
        guard.publish(&anchor_head)?;
        Ok(HistoryRead {
            head,
            entries,
            nodes: found,
        })
    }

    /// Append entry `height` iff the head is `height - 1`. The identical entry
    /// already at `height` is `AlreadyPresent`; anything else is a conflict.
    pub fn durable_append(
        &self,
        height: u64,
        record: &[u8],
        tag: &[u8],
        nodes: &[DurableNode],
    ) -> Result<PublishStatus, StoreError> {
        self.durable_append_with_hook(height, record, tag, nodes, |_| {})
    }

    fn durable_nodes_at(&self, height: u64) -> Result<Vec<DurableNode>, StoreError> {
        let statement = self.database.prepare(
            b"SELECT space, key, value FROM durable_node WHERE height=?1 ORDER BY space, key\0",
        )?;
        statement.bind_int64(1, height as i64)?;
        let mut nodes = Vec::new();
        while statement.step()? == SQLITE_ROW {
            nodes.push(DurableNode {
                space: statement.column_int64(0) as u64,
                key: statement.column_blob_at(1)?,
                value: statement.column_blob_at(2)?,
            });
        }
        Ok(nodes)
    }

    /// Append entry `height` and the accumulator nodes its append completes,
    /// in one transaction. The identical entry with the identical node set is
    /// `AlreadyPresent`; anything else at `height` is a conflict.
    pub fn durable_append_with_hook<F>(
        &self,
        height: u64,
        record: &[u8],
        tag: &[u8],
        nodes: &[DurableNode],
        mut hook: F,
    ) -> Result<PublishStatus, StoreError>
    where
        F: FnMut(PublishPhase),
    {
        Self::validate_bound(record)?;
        if height == 0
            || tag.len() > 4096
            || nodes.len() > 4096
            || nodes.iter().any(|node| node.key.len() > 4096 || node.value.len() > 4096 || node.space > i64::MAX as u64)
        {
            return Err(StoreError::Conflict);
        }
        let mut proposed_nodes = nodes.to_vec();
        proposed_nodes.sort();
        if proposed_nodes.windows(2).any(|pair| pair[0].space == pair[1].space && pair[0].key == pair[1].key) {
            return Err(StoreError::Conflict);
        }
        let guard = anchor::Guard::lock(&self.root)?;
        self.database.exec(b"BEGIN IMMEDIATE\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        hook(PublishPhase::Begun);
        self.refuse_retired_image()?;
        let seed = self.durable_seed()?.ok_or(StoreError::Missing)?;
        let current_head = self.anchor_head(&guard, &seed)?;
        if let Some(existing) = self.durable_entry(height)? {
            if existing.record == record
                && existing.tag == tag
                && self.durable_nodes_at(height)? == proposed_nodes
            {
                transaction.commit()?;
                hook(PublishPhase::Committed);
                guard.publish_with_hook(&current_head, &mut hook)?;
                hook(PublishPhase::Anchored);
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
        for node in &proposed_nodes {
            let insert = self.database.prepare(
                b"INSERT INTO durable_node(space,key,height,value) VALUES(?1,?2,?3,?4)\0",
            )?;
            insert.bind_int64(1, node.space as i64)?;
            insert.bind_blob_at(2, &node.key)?;
            insert.bind_int64(3, height as i64)?;
            insert.bind_blob_at(4, &node.value)?;
            if insert.step()? != SQLITE_DONE {
                return Err(self.database.error(SQLITE_DONE));
            }
        }
        hook(PublishPhase::Inserted);
        transaction.commit()?;
        hook(PublishPhase::Committed);
        let journal_height = self.journal_head()?;
        let journal = if journal_height == 0 {
            None
        } else {
            self.journal_entry(journal_height)?
        };
        let head = anchor::Head::new(
            &self.anchor_identity,
            &seed,
            Some(&DurableEntry {
                height,
                record: record.to_vec(),
                tag: tag.to_vec(),
            }),
            journal.as_ref(),
        );
        guard.publish_with_hook(&head, &mut hook)?;
        hook(PublishPhase::Anchored);
        Ok(PublishStatus::Installed)
    }

    /// Append archive journal entry `seq` iff the journal head is `seq - 1`,
    /// under the same anchor lock as the durable log; the new anchor commits
    /// to both heads. The identical entry already at `seq` is `AlreadyPresent`;
    /// anything else is a conflict. A seeded Store is required.
    pub fn journal_append(
        &self,
        seq: u64,
        record: &[u8],
        tag: &[u8],
    ) -> Result<PublishStatus, StoreError> {
        self.journal_append_with_hook(seq, record, tag, |_| {})
    }

    pub fn journal_append_with_hook<F>(
        &self,
        seq: u64,
        record: &[u8],
        tag: &[u8],
        mut hook: F,
    ) -> Result<PublishStatus, StoreError>
    where
        F: FnMut(PublishPhase),
    {
        Self::validate_bound(record)?;
        if seq == 0 || tag.len() > 4096 {
            return Err(StoreError::Conflict);
        }
        let guard = anchor::Guard::lock(&self.root)?;
        self.database.exec(b"BEGIN IMMEDIATE\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        hook(PublishPhase::Begun);
        self.refuse_retired_image()?;
        let seed = self.durable_seed()?.ok_or(StoreError::Missing)?;
        let current_head = self.anchor_head(&guard, &seed)?;
        if let Some(existing) = self.journal_entry(seq)? {
            if existing.record == record && existing.tag == tag {
                transaction.commit()?;
                hook(PublishPhase::Committed);
                guard.publish_with_hook(&current_head, &mut hook)?;
                hook(PublishPhase::Anchored);
                return Ok(PublishStatus::AlreadyPresent);
            }
            return Err(StoreError::Conflict);
        }
        if self.journal_head()? != seq - 1 {
            return Err(StoreError::Conflict);
        }
        let statement = self
            .database
            .prepare(b"INSERT INTO archive_journal(seq,record,tag) VALUES(?1,?2,?3)\0")?;
        statement.bind_int64(1, seq as i64)?;
        statement.bind_blob_at(2, record)?;
        statement.bind_blob_at(3, tag)?;
        if statement.step()? != SQLITE_DONE {
            return Err(self.database.error(SQLITE_DONE));
        }
        drop(statement);
        hook(PublishPhase::Inserted);
        transaction.commit()?;
        hook(PublishPhase::Committed);
        let height = self.durable_head()?;
        let entry = if height == 0 { None } else { self.durable_entry(height)? };
        let head = anchor::Head::new(
            &self.anchor_identity,
            &seed,
            entry.as_ref(),
            Some(&JournalEntry {
                seq,
                record: record.to_vec(),
                tag: tag.to_vec(),
            }),
        );
        guard.publish_with_hook(&head, &mut hook)?;
        hook(PublishPhase::Anchored);
        Ok(PublishStatus::Installed)
    }

    /// One consistent read of the archive journal from `from`, after the same
    /// anchor check as `durable_read`.
    pub fn journal_read(&self, from: u64) -> Result<JournalRead, StoreError> {
        let guard = anchor::Guard::lock(&self.root)?;
        self.database.exec(b"BEGIN DEFERRED\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        self.refuse_retired_image()?;
        let seed = self.durable_seed()?.ok_or(StoreError::Missing)?;
        let anchor_head = self.anchor_head(&guard, &seed)?;
        let head = self.journal_head()?;
        let mut entries = Vec::new();
        {
            let statement = self.database.prepare(
                b"SELECT seq, record, tag FROM archive_journal WHERE seq>=?1 ORDER BY seq\0",
            )?;
            statement.bind_int64(1, from.max(1) as i64)?;
            while statement.step()? == SQLITE_ROW {
                entries.push(JournalEntry {
                    seq: statement.column_int64(0) as u64,
                    record: statement.column_blob_at(1)?,
                    tag: statement.column_blob_at(2)?,
                });
            }
        }
        transaction.commit()?;
        guard.publish(&anchor_head)?;
        Ok(JournalRead { head, entries })
    }

    /// Store a checkpoint at `height` (at most the head), replacing one at the
    /// same height (a key rotation re-seals). Every checkpoint is retained:
    /// a state read at a past height (`durable-checkpoint-at`) resumes from the
    /// latest one at or below it.
    pub fn durable_checkpoint(&self, height: u64, bytes: &[u8]) -> Result<(), StoreError> {
        Self::validate_bound(bytes)?;
        let guard = anchor::Guard::lock(&self.root)?;
        self.database.exec(b"BEGIN IMMEDIATE\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        self.refuse_retired_image()?;
        let seed = self.durable_seed()?.ok_or(StoreError::Missing)?;
        let head = self.anchor_head(&guard, &seed)?;
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
        transaction.commit()?;
        guard.publish(&head)
    }

    /// The latest checkpoint at or below `height`, under the head anchor.
    pub fn durable_checkpoint_at(&self, height: u64) -> Result<Option<(u64, Vec<u8>)>, StoreError> {
        let guard = anchor::Guard::lock(&self.root)?;
        self.database.exec(b"BEGIN DEFERRED\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        self.refuse_retired_image()?;
        let seed = self.durable_seed()?.ok_or(StoreError::Missing)?;
        let anchor_head = self.anchor_head(&guard, &seed)?;
        let statement = self.database.prepare(
            b"SELECT height, bytes FROM durable_checkpoint WHERE height<=?1 ORDER BY height DESC LIMIT 1\0",
        )?;
        statement.bind_int64(1, height.min(i64::MAX as u64) as i64)?;
        let found = match statement.step()? {
            SQLITE_ROW => Some((statement.column_int64(0) as u64, statement.column_blob_at(1)?)),
            _ => None,
        };
        drop(statement);
        transaction.commit()?;
        guard.publish(&anchor_head)?;
        Ok(found)
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

/// The history read file Lean parses: u64 head; u64 entry count; per entry
/// u64 height, record blob, tag blob; u64 node count; per requested node u64
/// space, key blob, u64 flag (0 absent, 1 present) and when present u64
/// version height and value blob.
pub fn encode_history_read(read: &HistoryRead) -> Vec<u8> {
    fn blob(out: &mut Vec<u8>, bytes: &[u8]) {
        out.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
        out.extend_from_slice(bytes);
    }
    let mut out = Vec::new();
    out.extend_from_slice(&read.head.to_be_bytes());
    out.extend_from_slice(&(read.entries.len() as u64).to_be_bytes());
    for entry in &read.entries {
        out.extend_from_slice(&entry.height.to_be_bytes());
        blob(&mut out, &entry.record);
        blob(&mut out, &entry.tag);
    }
    out.extend_from_slice(&(read.nodes.len() as u64).to_be_bytes());
    for (space, key, version) in &read.nodes {
        out.extend_from_slice(&space.to_be_bytes());
        blob(&mut out, key);
        match version {
            None => out.extend_from_slice(&0u64.to_be_bytes()),
            Some((height, value)) => {
                out.extend_from_slice(&1u64.to_be_bytes());
                out.extend_from_slice(&height.to_be_bytes());
                blob(&mut out, value);
            }
        }
    }
    out
}

/// Parse a node list file (append) or a history request: big-endian u64
/// fields and u64-length blobs, nothing trailing.
pub struct Reader<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Reader<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }
    pub fn u64(&mut self) -> Result<u64, StoreError> {
        let end = self.position.checked_add(8).ok_or(StoreError::InvalidPath)?;
        let slice = self.bytes.get(self.position..end).ok_or(StoreError::InvalidPath)?;
        self.position = end;
        Ok(u64::from_be_bytes(slice.try_into().map_err(|_| StoreError::InvalidPath)?))
    }
    pub fn blob(&mut self) -> Result<Vec<u8>, StoreError> {
        let length = usize::try_from(self.u64()?).map_err(|_| StoreError::InvalidPath)?;
        if length > 4096 {
            return Err(StoreError::InvalidPath);
        }
        let end = self.position.checked_add(length).ok_or(StoreError::InvalidPath)?;
        let slice = self.bytes.get(self.position..end).ok_or(StoreError::InvalidPath)?;
        self.position = end;
        Ok(slice.to_vec())
    }
    pub fn finish(self) -> Result<(), StoreError> {
        if self.position == self.bytes.len() {
            Ok(())
        } else {
            Err(StoreError::InvalidPath)
        }
    }
}

/// NODES file: u64 count, then per node u64 space, key blob, value blob.
pub fn decode_nodes(bytes: &[u8]) -> Result<Vec<DurableNode>, StoreError> {
    let mut reader = Reader::new(bytes);
    let count = reader.u64()?;
    if count > 4096 {
        return Err(StoreError::InvalidPath);
    }
    let mut nodes = Vec::new();
    for _ in 0..count {
        let space = reader.u64()?;
        let key = reader.blob()?;
        let value = reader.blob()?;
        nodes.push(DurableNode { space, key, value });
    }
    reader.finish()?;
    Ok(nodes)
}

/// REQUEST file: u64 at; u64 height count, heights; u64 node count, per node
/// u64 space and key blob.
pub fn decode_history_request(bytes: &[u8]) -> Result<(u64, Vec<u64>, Vec<(u64, Vec<u8>)>), StoreError> {
    let mut reader = Reader::new(bytes);
    let at = reader.u64()?;
    let count = reader.u64()?;
    if count > 4096 {
        return Err(StoreError::InvalidPath);
    }
    let mut heights = Vec::new();
    for _ in 0..count {
        heights.push(reader.u64()?);
    }
    let count = reader.u64()?;
    if count > 65536 {
        return Err(StoreError::InvalidPath);
    }
    let mut nodes = Vec::new();
    for _ in 0..count {
        let space = reader.u64()?;
        nodes.push((space, reader.blob()?));
    }
    reader.finish()?;
    Ok((at, heights, nodes))
}

/// The journal read file Lean parses: big-endian u64 head; u64 entry count;
/// per entry u64 seq, record blob, tag blob (u64 length and bytes).
pub fn encode_journal_read(read: &JournalRead) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&read.head.to_be_bytes());
    out.extend_from_slice(&(read.entries.len() as u64).to_be_bytes());
    for entry in &read.entries {
        out.extend_from_slice(&entry.seq.to_be_bytes());
        out.extend_from_slice(&(entry.record.len() as u64).to_be_bytes());
        out.extend_from_slice(&entry.record);
        out.extend_from_slice(&(entry.tag.len() as u64).to_be_bytes());
        out.extend_from_slice(&entry.tag);
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

    /// The seed read answers before (and whatever) the head anchor would say:
    /// a Store opened under another anchor identity still reports its seed
    /// bytes, while every accepting read under that identity refuses.
    #[test]
    fn durable_seed_reads_without_the_anchor_and_accepts_nothing() {
        let root = fresh_root("seed-peek");
        let store = SqliteByteStore::open_with_identity(&root, b"epoch-a").unwrap();
        assert!(matches!(store.durable_seed_bytes(), Err(StoreError::Missing)));
        store.durable_init(b"seed").unwrap();
        drop(store);
        let other = SqliteByteStore::open_with_identity(&root, b"epoch-b").unwrap();
        assert_eq!(other.durable_seed_bytes().unwrap(), b"seed");
        assert!(matches!(other.durable_read(1, true), Err(StoreError::Anchor(_))));
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn archive_journal_appends_at_its_head_under_the_shared_anchor() {
        let root = fresh_root("journal");
        let store = SqliteByteStore::open(&root).unwrap();
        assert!(matches!(store.journal_append(1, b"j", b"t"), Err(StoreError::Missing)));
        store.durable_init(b"seed").unwrap();
        assert!(matches!(store.journal_append(2, b"j", b"t"), Err(StoreError::Conflict)));
        assert_eq!(store.journal_append(1, b"j1", b"t1").unwrap(), PublishStatus::Installed);
        assert_eq!(store.journal_append(1, b"j1", b"t1").unwrap(), PublishStatus::AlreadyPresent);
        assert!(matches!(store.journal_append(1, b"jX", b"t1"), Err(StoreError::Conflict)));
        // The two logs advance independently; each append re-anchors both heads.
        store.durable_append(1, b"r1", b"t1", &[]).unwrap();
        assert_eq!(store.journal_append(2, b"j2", b"t2").unwrap(), PublishStatus::Installed);
        let read = store.journal_read(1).unwrap();
        assert_eq!(read.head, 2);
        assert_eq!(
            read.entries.iter().map(|e| (e.seq, e.record.clone())).collect::<Vec<_>>(),
            vec![(1, b"j1".to_vec()), (2, b"j2".to_vec())]
        );
        assert_eq!(store.durable_read(1, false).unwrap().head, 1);
        // Truncating the journal below the anchored head refuses every read,
        // the durable log's included: one anchor binds both.
        store.database.exec(b"DELETE FROM archive_journal WHERE seq=2\0").unwrap();
        assert!(matches!(
            store.journal_read(1),
            Err(StoreError::Anchor("archive journal is behind retained head"))
        ));
        assert!(matches!(
            store.durable_read(1, false),
            Err(StoreError::Anchor("archive journal is behind retained head"))
        ));
    }

    #[test]
    fn archive_journal_entry_rewrite_under_the_anchor_refuses() {
        let root = fresh_root("journal-rewrite");
        let store = SqliteByteStore::open(&root).unwrap();
        store.durable_init(b"seed").unwrap();
        store.journal_append(1, b"j1", b"t1").unwrap();
        store.database.exec(b"UPDATE archive_journal SET record=x'00' WHERE seq=1\0").unwrap();
        assert!(matches!(
            store.journal_read(1),
            Err(StoreError::Anchor("genesis or retained head conflicts"))
        ));
    }

    #[test]
    fn retired_minianc1_anchor_is_refused_by_name() {
        let root = fresh_root("anc1");
        let store = SqliteByteStore::open(&root).unwrap();
        store.durable_init(b"seed").unwrap();
        let path = anchor::path(store.root());
        let mut old = b"MINIANC1".to_vec();
        old.resize(80, 7);
        fs::write(&path, &old).unwrap();
        assert!(matches!(
            store.durable_read(1, false),
            Err(StoreError::Anchor(
                "retired MINIANC1 anchor (durable log only); re-genesis (no migration)"
            ))
        ));
    }

    #[test]
    fn durable_log_appends_only_at_the_head() {
        let root = fresh_root("append");
        let store = SqliteByteStore::open(&root).unwrap();
        assert!(matches!(
            store.durable_append(1, b"r", b"t", &[]),
            Err(StoreError::Missing)
        ));
        assert_eq!(
            store.durable_init(b"seed").unwrap(),
            PublishStatus::Installed
        );
        assert_eq!(
            store.durable_init(b"seed").unwrap(),
            PublishStatus::AlreadyPresent
        );
        assert!(matches!(
            store.durable_init(b"other"),
            Err(StoreError::Conflict)
        ));
        assert!(matches!(
            store.durable_append(2, b"r", b"t", &[]),
            Err(StoreError::Conflict)
        ));
        assert_eq!(
            store.durable_append(1, b"r1", b"t1", &[]).unwrap(),
            PublishStatus::Installed
        );
        assert_eq!(
            store.durable_append(1, b"r1", b"t1", &[]).unwrap(),
            PublishStatus::AlreadyPresent
        );
        assert!(matches!(
            store.durable_append(1, b"r1", b"tX", &[]),
            Err(StoreError::Conflict)
        ));
        assert_eq!(
            store.durable_append(2, b"r2", b"t2", &[]).unwrap(),
            PublishStatus::Installed
        );
        assert!(matches!(
            store.durable_checkpoint(3, b"c"),
            Err(StoreError::Conflict)
        ));
        store.durable_checkpoint(1, b"c1").unwrap();
        store.durable_checkpoint(2, b"c2").unwrap();
        store.durable_append(3, b"r3", b"t3", &[]).unwrap();
        store.durable_checkpoint(3, b"c3").unwrap();
        let read = store.durable_read(2, true).unwrap();
        assert_eq!(read.head, 3);
        assert_eq!(
            read.base,
            Some((b"seed".to_vec(), Some((3, b"c3".to_vec()))))
        );
        assert_eq!(
            read.entries.iter().map(|e| e.height).collect::<Vec<_>>(),
            vec![2, 3]
        );
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
        assert!(matches!(
            store.durable_init(b"seed"),
            Err(StoreError::RetiredImage)
        ));
        assert!(matches!(
            store.durable_read(1, true),
            Err(StoreError::RetiredImage)
        ));
        assert!(matches!(
            store.durable_append(1, b"r", b"t", &[]),
            Err(StoreError::RetiredImage)
        ));
        drop(store);
        fs::remove_dir_all(root).unwrap();
    }
}

#[cfg(test)]
mod anchor_tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};
    fn store() -> SqliteByteStore {
        let path = std::env::temp_dir().join(format!(
            "mini-anchor-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let store = SqliteByteStore::open(path.join("store")).unwrap();
        store.durable_init(b"domain-and-genesis").unwrap();
        store.durable_append(1, b"one", b"tag-one", &[]).unwrap();
        store.durable_checkpoint(1, b"checkpoint-one").unwrap();
        store.durable_append(2, b"two", b"tag-two", &[]).unwrap();
        store
    }
    /// A read of a Store whose anchor is current changes no byte of the anchor, the lock or the
    /// database file, and no modification time. (A read that finds the anchor BEHIND the head
    /// — a crash between an append's commit and its anchor publish — still ratchets it forward:
    /// `durable_read_repairs_an_anchor_that_lags_the_head` pins that, deliberately.)
    #[test]
    fn a_durable_read_of_a_current_anchor_writes_nothing() {
        use std::os::unix::fs::MetadataExt;
        let s = store();
        let anchor_path = anchor::path(s.root());
        let lock_path = {
            let mut p = anchor_path.as_os_str().to_owned();
            p.push(".lock");
            PathBuf::from(p)
        };
        let snapshot = |path: &Path| {
            let m = fs::metadata(path).unwrap();
            (fs::read(path).unwrap(), m.mtime(), m.mtime_nsec(), m.ino())
        };
        let before = (snapshot(&anchor_path), snapshot(&lock_path), snapshot(s.database_path()));
        std::thread::sleep(std::time::Duration::from_millis(30));
        for _ in 0..3 {
            let read = s.durable_read(1, true).unwrap();
            assert_eq!(read.head, 2);
        }
        let after = (snapshot(&anchor_path), snapshot(&lock_path), snapshot(s.database_path()));
        assert_eq!(before, after, "a read must leave the anchor, its lock and the database untouched");
    }
    /// The crash-repair half: the anchor lags the head by one entry; the next read ratchets it.
    #[test]
    fn durable_read_repairs_an_anchor_that_lags_the_head() {
        let s = store();
        let anchor_path = anchor::path(s.root());
        let at_head = fs::read(&anchor_path).unwrap();
        s.database
            .exec(b"INSERT INTO durable_log(height,record,tag) VALUES(3,x'7468726565',x'7461672d7468726565')\0")
            .unwrap();
        assert_eq!(fs::read(&anchor_path).unwrap(), at_head, "setup: the anchor lags");
        assert_eq!(s.durable_read(1, true).unwrap().head, 3);
        assert_ne!(fs::read(&anchor_path).unwrap(), at_head, "the read ratcheted the lagging anchor");
        assert_eq!(s.durable_read(1, true).unwrap().head, 3);
    }
    #[test]
    fn explicit_deployment_identity_changes_refuse_at_genesis_and_head() {
        let s = store();
        let root = s.root().to_owned();
        drop(s);
        let foreign = SqliteByteStore::open_with_identity(&root, b"another-domain").unwrap();
        assert!(matches!(
            foreign.durable_read(1, true),
            Err(StoreError::Anchor(_))
        ));
        let initial = root.parent().unwrap().join("initial");
        let s =
            SqliteByteStore::open_with_identity(&initial, b"domain:1;semantics:2;seed:3").unwrap();
        s.durable_init(b"same-seed").unwrap();
        drop(s);
        let s =
            SqliteByteStore::open_with_identity(initial, b"domain:2;semantics:2;seed:3").unwrap();
        assert!(matches!(
            s.durable_read(1, true),
            Err(StoreError::Anchor(_))
        ));
    }
    #[test]
    fn truncation_above_checkpoint_refuses_reads_and_writes() {
        let s = store();
        s.database
            .exec(b"DELETE FROM durable_log WHERE height=2\0")
            .unwrap();
        assert!(matches!(
            s.durable_read(1, true),
            Err(StoreError::Anchor("Store is behind retained head"))
        ));
        assert!(matches!(
            s.durable_append(2, b"other", b"tag-other", &[]),
            Err(StoreError::Anchor(_))
        ));
        assert!(matches!(
            s.durable_checkpoint(1, b"cp"),
            Err(StoreError::Anchor(_))
        ));
        assert!(matches!(
            s.durable_anchor_enroll(),
            Err(StoreError::Anchor(_))
        ));
    }
    #[test]
    fn same_height_record_and_genesis_conflicts_refuse() {
        let s = store();
        s.database
            .exec(b"UPDATE durable_log SET record=X'00' WHERE height=2\0")
            .unwrap();
        assert!(matches!(
            s.durable_read(1, true),
            Err(StoreError::Anchor(_))
        ));
        let s = store();
        s.database
            .exec(b"UPDATE durable_seed SET bytes=X'00'\0")
            .unwrap();
        assert!(matches!(
            s.durable_read(1, true),
            Err(StoreError::Anchor(_))
        ));
    }
    #[test]
    fn anchor_loss_refuses_until_explicit_enrollment_and_foreign_anchor_refuses() {
        let a = store();
        let b = store();
        b.durable_append(3, b"third", b"tag-three", &[]).unwrap();
        fs::copy(anchor::path(b.root()), anchor::path(a.root())).unwrap();
        assert!(matches!(
            a.durable_read(1, true),
            Err(StoreError::Anchor(_))
        ));
        fs::rename(
            anchor::path(a.root()),
            a.root().join("retained-test-anchor"),
        )
        .unwrap();
        assert!(matches!(
            a.durable_read(1, true),
            Err(StoreError::Anchor(_))
        ));
        assert!(matches!(
            a.durable_init(b"domain-and-genesis"),
            Err(StoreError::Anchor(_))
        ));
        a.durable_anchor_enroll().unwrap();
        assert_eq!(a.durable_read(3, false).unwrap().head, 2);
    }
    #[test]
    fn anchor_custody_refuses_a_foreign_owner_and_a_shared_directory() {
        use std::os::unix::fs::PermissionsExt;
        let s = store();
        let anchor_path = anchor::path(s.root());
        let directory = anchor_path.parent().unwrap().to_owned();
        let me = unsafe { libc::geteuid() };
        let file = fs::metadata(&anchor_path).unwrap();
        let dir = fs::metadata(&directory).unwrap();
        assert!(anchor::custody(Some(&file), &dir, me).is_ok());
        // The same bytes held by another account: refused, whoever wrote them.
        assert!(matches!(
            anchor::custody(Some(&file), &dir, me.wrapping_add(1)),
            Err(StoreError::Anchor(_))
        ));
        // A directory another account may write (rename a forged anchor in): refused.
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o770)).unwrap();
        assert!(matches!(
            s.durable_read(1, true),
            Err(StoreError::Anchor("anchor directory is writable by another account"))
        ));
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o757)).unwrap();
        assert!(matches!(s.durable_read(1, true), Err(StoreError::Anchor(_))));
        // Sticky: only the owner may rename or unlink its files there.
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o1777)).unwrap();
        assert_eq!(s.durable_read(1, true).unwrap().head, 2);
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        assert_eq!(s.durable_read(1, true).unwrap().head, 2);
        // A loose mode on the anchor itself refuses as before.
        fs::set_permissions(&anchor_path, fs::Permissions::from_mode(0o640)).unwrap();
        assert!(matches!(s.durable_read(1, true), Err(StoreError::Anchor(_))));
    }

    /// Two real uids (Linux, `sudo -n setpriv`):
    /// MINI_TEST_FOREIGN_UID=65534 cargo nextest run --run-ignored all -E 'test(anchor_rewritten_by_a_session_uid)'
    /// A session account cannot write the Store's anchor in place, cannot rename
    /// over it in a sticky directory, and a forged anchor it does manage to
    /// install (a misdeployed, other-writable directory) refuses every read.
    #[test]
    #[ignore]
    fn anchor_rewritten_by_a_session_uid_refuses() {
        use std::os::unix::fs::PermissionsExt;
        use std::process::Command;
        let foreign: u32 = std::env::var("MINI_TEST_FOREIGN_UID").expect("MINI_TEST_FOREIGN_UID").parse().unwrap();
        let s = store();
        let anchor_path = anchor::path(s.root());
        let directory = anchor_path.parent().unwrap().to_owned();
        let older = fs::read(&anchor_path).unwrap();
        s.durable_append(3, b"third", b"tag-three", &[]).unwrap();
        // The session account's attempt: write the older head in place, else
        // rename a forged copy over the anchor. Prints what happened.
        let attempt = |label: &str| -> String {
            let script = "import os,sys\npath,older=sys.argv[1],bytes.fromhex(sys.argv[2])\ntry:\n  open(path,'r+b').write(older); print('WROTE'); sys.exit(0)\nexcept PermissionError: pass\ntry:\n  forged=path+'.forged.'+str(os.getpid())\n  f=os.open(forged,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600); os.write(f,older); os.close(f)\n  os.rename(forged,path); print('RENAMED')\nexcept PermissionError: print('EACCES')";
            let hex: String = older.iter().map(|b| format!("{b:02x}")).collect();
            let output = Command::new("sudo")
                .args(["-n", "setpriv", &format!("--reuid={foreign}"), &format!("--regid={foreign}"), "--clear-groups", "--", "python3", "-c", script, anchor_path.to_str().unwrap(), &hex])
                .output()
                .unwrap();
            assert!(output.status.success(), "{label}: {}", String::from_utf8_lossy(&output.stderr));
            String::from_utf8(output.stdout).unwrap().trim().to_owned()
        };
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        assert_eq!(attempt("private directory"), "EACCES");
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o1777)).unwrap();
        assert_eq!(attempt("sticky directory"), "EACCES");
        assert_eq!(s.durable_read(1, true).unwrap().head, 3);
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o777)).unwrap();
        assert_eq!(attempt("misdeployed directory"), "RENAMED");
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        // The forged anchor (the session's older head, the session's file)
        // refuses: by custody, or before it by being unreadable to the Store.
        let forged = fs::symlink_metadata(&anchor_path).unwrap();
        assert_eq!(std::os::unix::fs::MetadataExt::uid(&forged), foreign);
        assert!(matches!(
            anchor::custody(Some(&forged), &fs::metadata(&directory).unwrap(), unsafe { libc::geteuid() }),
            Err(StoreError::Anchor("anchor is not owned by the Store's user"))
        ));
        assert!(s.durable_read(1, true).is_err());
        assert!(s.durable_append(4, b"four", b"tag-four", &[]).is_err());
    }
    #[test]
    fn whole_database_replacement_is_detected_by_sibling_anchor() {
        let s = store();
        let backup = s.root().join("earlier.sqlite3");
        fs::copy(s.database_path(), &backup).unwrap();
        s.durable_append(3, b"third", b"tag-three", &[]).unwrap();
        let root = s.root().to_owned();
        let database = s.database_path().to_owned();
        drop(s);
        fs::copy(&backup, &database).unwrap();
        let reopened = SqliteByteStore::open(root).unwrap();
        assert!(matches!(
            reopened.durable_read(1, true),
            Err(StoreError::Anchor(_))
        ));
    }

    fn kn2_root(label: &str) -> std::path::PathBuf {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        std::env::temp_dir().join(format!("dregg-kn2-{label}-{}-{nonce}", std::process::id()))
    }

    fn node(space: u64, key: &[u8], value: &[u8]) -> DurableNode {
        DurableNode { space, key: key.to_vec(), value: value.to_vec() }
    }

    /// KN2-STORE-OPEN: an append writes its accumulator nodes in the same
    /// transaction; a retry must carry the identical node set; a history read
    /// returns each node's latest version at or below `at`.
    #[test]
    fn durable_nodes_are_written_with_their_entry_and_read_by_version() {
        let root = kn2_root("nodes");
        let store = SqliteByteStore::open(&root).unwrap();
        store.durable_init(b"seed").unwrap();
        let first = [node(1, b"leaf-1", b"d1"), node(2, b"path", b"v1")];
        assert_eq!(store.durable_append(1, b"r1", b"t1", &first).unwrap(), PublishStatus::Installed);
        assert_eq!(store.durable_append(1, b"r1", b"t1", &first).unwrap(), PublishStatus::AlreadyPresent);
        assert!(matches!(
            store.durable_append(1, b"r1", b"t1", &[node(1, b"leaf-1", b"forged")]),
            Err(StoreError::Conflict)
        ));
        assert!(matches!(
            store.durable_append(2, b"r2", b"t2", &[node(2, b"k", b"a"), node(2, b"k", b"b")]),
            Err(StoreError::Conflict)
        ));
        store.durable_append(2, b"r2", b"t2", &[node(2, b"path", b"v2")]).unwrap();
        let request = vec![(1, b"leaf-1".to_vec()), (2, b"path".to_vec()), (2, b"absent".to_vec())];
        let at1 = store.durable_history(1, &[1], &request).unwrap();
        assert_eq!(at1.head, 2);
        assert_eq!(at1.entries.len(), 1);
        assert_eq!(at1.nodes[0].2, Some((1, b"d1".to_vec())));
        assert_eq!(at1.nodes[1].2, Some((1, b"v1".to_vec())));
        assert_eq!(at1.nodes[2].2, None);
        let at2 = store.durable_history(2, &[1, 2, 9], &request).unwrap();
        assert_eq!(at2.entries.iter().map(|e| e.height).collect::<Vec<_>>(), vec![1, 2]);
        assert_eq!(at2.nodes[1].2, Some((2, b"v2".to_vec())));
        let encoded = encode_history_read(&at2);
        assert_eq!(&encoded[..8], &2u64.to_be_bytes());
        drop(store);
        fs::remove_dir_all(root).unwrap();
    }

    /// The open reads from the latest checkpoint, not from genesis.
    #[test]
    fn durable_read_from_checkpoint_starts_at_the_checkpoint() {
        let root = kn2_root("from-checkpoint");
        let store = SqliteByteStore::open(&root).unwrap();
        store.durable_init(b"seed").unwrap();
        assert_eq!(store.durable_read_from_checkpoint().unwrap().entries.len(), 0);
        for h in 1..=5u64 {
            store.durable_append(h, &[h as u8], b"t", &[]).unwrap();
        }
        assert_eq!(store.durable_read_from_checkpoint().unwrap().entries.len(), 5);
        store.durable_checkpoint(3, b"c3").unwrap();
        let read = store.durable_read_from_checkpoint().unwrap();
        assert_eq!(read.head, 5);
        assert_eq!(read.entries.iter().map(|e| e.height).collect::<Vec<_>>(), vec![3, 4, 5]);
        assert_eq!(read.base.unwrap().1, Some((3, b"c3".to_vec())));
        drop(store);
        fs::remove_dir_all(root).unwrap();
    }

    /// A seeded v4 Store (no accumulator) refuses by name; it is never upgraded.
    #[test]
    fn seeded_schema_v4_store_refuses_by_name() {
        let root = kn2_root("v4");
        let store = SqliteByteStore::open(&root).unwrap();
        store.durable_init(b"seed").unwrap();
        store.database.exec(b"DROP TABLE durable_node\0").unwrap();
        store.database.exec(b"PRAGMA user_version=4\0").unwrap();
        drop(store);
        let refused = SqliteByteStore::open(&root);
        assert!(matches!(refused, Err(StoreError::RetiredSchema(4))));
        let message = format!("{}", refused.err().unwrap());
        assert!(message.contains("schema v4") && message.contains("re-genesis"), "{message}");
        fs::remove_dir_all(root).unwrap();
    }

    /// Every checkpoint is retained; a past-height read finds the latest at or below it.
    #[test]
    fn every_checkpoint_is_retained_and_found_at_or_below() {
        let root = kn2_root("checkpoint-at");
        let store = SqliteByteStore::open(&root).unwrap();
        store.durable_init(b"seed").unwrap();
        for h in 1..=9u64 {
            store.durable_append(h, &[h as u8], b"t", &[]).unwrap();
            if h % 3 == 0 {
                store.durable_checkpoint(h, &[b'c', h as u8]).unwrap();
            }
        }
        assert_eq!(store.durable_checkpoint_at(2).unwrap(), None);
        assert_eq!(store.durable_checkpoint_at(3).unwrap(), Some((3, vec![b'c', 3])));
        assert_eq!(store.durable_checkpoint_at(5).unwrap(), Some((3, vec![b'c', 3])));
        assert_eq!(store.durable_checkpoint_at(8).unwrap(), Some((6, vec![b'c', 6])));
        assert_eq!(store.durable_checkpoint_at(100).unwrap(), Some((9, vec![b'c', 9])));
        drop(store);
        fs::remove_dir_all(root).unwrap();
    }
}
