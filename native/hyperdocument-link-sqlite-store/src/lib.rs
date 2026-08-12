//! Opaque, fallible SQLite transport for one bounded Lean-authored byte record.
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

pub const MAX_RECORD_BYTES: usize = 4096;
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
            Self::Conflict => formatter.write_str("a different byte record already exists"),
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

    fn column_blob(&self) -> Result<Vec<u8>, StoreError> {
        // SAFETY: this is called only while the statement is on SQLITE_ROW.
        let length = unsafe { sqlite3_column_bytes(self.raw.as_ptr(), 0) };
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
        let pointer = unsafe { sqlite3_column_blob(self.raw.as_ptr(), 0) }.cast::<u8>();
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
    store: &'store SqliteLinkStore,
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

pub struct SqliteLinkStore {
    root: PathBuf,
    database_path: PathBuf,
    database: Database,
}

impl SqliteLinkStore {
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
        database.exec(
            b"CREATE TABLE IF NOT EXISTS opaque_record (slot INTEGER PRIMARY KEY CHECK(slot=1), bytes BLOB NOT NULL CHECK(length(bytes)<=4096)) WITHOUT ROWID\0",
        )?;
        Ok(Self {
            root,
            database_path,
            database,
        })
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn database_path(&self) -> &Path {
        &self.database_path
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
        self.publish_with_hook(bytes, |_| {})
    }

    pub fn publish_with_hook<F>(
        &self,
        bytes: &[u8],
        mut hook: F,
    ) -> Result<PublishStatus, StoreError>
    where
        F: FnMut(PublishPhase),
    {
        Self::validate_bound(bytes)?;
        self.database.exec(b"BEGIN IMMEDIATE\0")?;
        let transaction = Transaction {
            store: self,
            active: true,
        };
        hook(PublishPhase::Begun);

        if let Some(current) = self.select_record()? {
            if current != bytes {
                return Err(StoreError::Conflict);
            }
            transaction.commit()?;
            hook(PublishPhase::Committed);
            return Ok(PublishStatus::AlreadyPresent);
        }

        let statement = self
            .database
            .prepare(b"INSERT INTO opaque_record(slot,bytes) VALUES(1,?1)\0")?;
        statement.bind_blob(bytes)?;
        debug_assert_eq!(statement.step()?, SQLITE_DONE);
        drop(statement);
        hook(PublishPhase::Inserted);
        transaction.commit()?;
        hook(PublishPhase::Committed);
        Ok(PublishStatus::Installed)
    }
}
