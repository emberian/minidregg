//! Fallible bounded filesystem transport for one Lean-authored recovery record.
//!
//! This crate has no Hyperdocument, WAL, authorization, replay, or acceptance
//! semantics. It stores and returns opaque bytes. Lean owns the exact fixture,
//! decoding, guarded replay, and endpoint response.
//!
//! A successful call observes `write_all`, file `sync_all`, a no-overwrite
//! `hard_link`, and directory `sync_all` returning successfully on that host.
//! It is not a proof of POSIX behavior, atomic visibility, stable media,
//! power-loss survival, or safety under adversarial concurrent mutation.

use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

pub const MAX_RECORD_BYTES: usize = 4096;
const PUBLISHED_NAME: &str = "forward-link.recovery";
const STAGED_NAME: &str = "forward-link.recovery.staged";

#[derive(Debug)]
pub enum StoreError {
    Missing,
    TooLarge { actual: usize, maximum: usize },
    Conflict,
    NotRegular(PathBuf),
    Io(io::Error),
}

impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Missing => f.write_str("published recovery record is missing"),
            Self::TooLarge { actual, maximum } => {
                write!(f, "record has {actual} bytes; maximum is {maximum}")
            }
            Self::Conflict => f.write_str("a different recovery record already exists"),
            Self::NotRegular(path) => {
                write!(f, "storage leaf is not a regular file: {}", path.display())
            }
            Self::Io(error) => write!(f, "filesystem error: {error}"),
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StageStatus {
    Staged,
    AlreadyPresent,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PublishStatus {
    Installed,
    AlreadyPresent,
}

#[derive(Clone, Debug)]
pub struct LocalLinkStore {
    root: PathBuf,
}

impl LocalLinkStore {
    pub fn open(root: impl AsRef<Path>) -> Result<Self, StoreError> {
        fs::create_dir_all(root.as_ref())?;
        let root = root.as_ref().to_path_buf();
        let metadata = fs::symlink_metadata(&root)?;
        if !metadata.file_type().is_dir() || metadata.file_type().is_symlink() {
            return Err(StoreError::NotRegular(root));
        }
        Ok(Self { root })
    }

    fn published_path(&self) -> PathBuf {
        self.root.join(PUBLISHED_NAME)
    }

    fn staged_path(&self) -> PathBuf {
        self.root.join(STAGED_NAME)
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

    fn read_bounded(path: &Path) -> Result<Vec<u8>, StoreError> {
        let file = match File::open(path) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                return Err(StoreError::Missing)
            }
            Err(error) => return Err(StoreError::Io(error)),
        };
        let metadata = file.metadata()?;
        if !metadata.is_file() {
            return Err(StoreError::NotRegular(path.to_path_buf()));
        }
        if metadata.len() > MAX_RECORD_BYTES as u64 {
            return Err(StoreError::TooLarge {
                actual: usize::try_from(metadata.len()).unwrap_or(usize::MAX),
                maximum: MAX_RECORD_BYTES,
            });
        }
        let mut bytes = Vec::with_capacity(metadata.len() as usize);
        file.take((MAX_RECORD_BYTES + 1) as u64)
            .read_to_end(&mut bytes)?;
        Self::validate_bound(&bytes)?;
        Ok(bytes)
    }

    fn sync_directory(&self) -> Result<(), StoreError> {
        File::open(&self.root)?.sync_all()?;
        Ok(())
    }

    pub fn read(&self) -> Result<Vec<u8>, StoreError> {
        Self::read_bounded(&self.published_path())
    }

    pub fn stage(&self, bytes: &[u8]) -> Result<StageStatus, StoreError> {
        Self::validate_bound(bytes)?;

        match self.read() {
            Ok(current) if current == bytes => return Ok(StageStatus::AlreadyPresent),
            Ok(_) => return Err(StoreError::Conflict),
            Err(StoreError::Missing) => {}
            Err(error) => return Err(error),
        }

        match Self::read_bounded(&self.staged_path()) {
            Ok(current) if current == bytes => return Ok(StageStatus::Staged),
            Ok(_) => return Err(StoreError::Conflict),
            Err(StoreError::Missing) => {}
            Err(error) => return Err(error),
        }

        let mut staged = match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(self.staged_path())
        {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                let current = Self::read_bounded(&self.staged_path())?;
                return if current == bytes {
                    Ok(StageStatus::Staged)
                } else {
                    Err(StoreError::Conflict)
                };
            }
            Err(error) => return Err(StoreError::Io(error)),
        };
        staged.write_all(bytes)?;
        staged.sync_all()?;
        Ok(StageStatus::Staged)
    }

    pub fn install_staged(&self) -> Result<PublishStatus, StoreError> {
        let staged_path = self.staged_path();
        let published_path = self.published_path();
        let candidate = Self::read_bounded(&staged_path)?;

        match fs::hard_link(&staged_path, &published_path) {
            Ok(()) => {
                // The visible name has been installed without replacing an
                // existing record. The directory-sync return is observed,
                // not treated as a theorem about hardware durability.
                self.sync_directory()?;
                fs::remove_file(&staged_path)?;
                self.sync_directory()?;
                Ok(PublishStatus::Installed)
            }
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                let current = Self::read_bounded(&published_path)?;
                if current != candidate {
                    return Err(StoreError::Conflict);
                }
                fs::remove_file(&staged_path)?;
                self.sync_directory()?;
                Ok(PublishStatus::AlreadyPresent)
            }
            Err(error) => Err(StoreError::Io(error)),
        }
    }

    pub fn publish(&self, bytes: &[u8]) -> Result<PublishStatus, StoreError> {
        match self.stage(bytes)? {
            StageStatus::AlreadyPresent => Ok(PublishStatus::AlreadyPresent),
            StageStatus::Staged => self.install_staged(),
        }
    }

    pub fn discard_staged(&self) -> Result<(), StoreError> {
        match fs::remove_file(self.staged_path()) {
            Ok(()) => self.sync_directory(),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
            Err(error) => Err(StoreError::Io(error)),
        }
    }
}
