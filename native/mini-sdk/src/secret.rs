//! The ONE loader of secret key material from a file.
//!
//! Custody is checked on the OPENED descriptor (a rename between check and read cannot
//! substitute another file): a regular file owned by this euid with no group/other permission
//! bits. A secret is never read through a symlink. [`Custody`] says whether the containing
//! directory must be owner-private too. Bytes come back in `Zeroizing` buffers.
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};

use zeroize::Zeroizing;

/// How much of the path's custody is checked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Custody {
    /// The file itself, never reached through a symlink.
    FileNoFollow,
    /// No symlink, and the file's parent directory must be an owner-private directory.
    FileAndDirectory,
}

/// Why a secret was not loaded.
#[derive(Debug)]
pub struct SecretError {
    pub path: PathBuf,
    pub kind: SecretErrorKind,
}

#[derive(Debug)]
pub enum SecretErrorKind {
    Unreadable(io::Error),
    /// Custody refused; the text names which rule.
    Custody(&'static str),
    /// The file is empty or longer than the bound.
    Size { limit: usize },
    /// A seed must be exactly this many bytes.
    Width { wanted: usize },
}

impl std::fmt::Display for SecretError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let path = self.path.display();
        match &self.kind {
            SecretErrorKind::Unreadable(e) => write!(f, "cannot read key file {path}: {e}"),
            SecretErrorKind::Custody(why) => write!(f, "key file {path} {why}"),
            SecretErrorKind::Size { limit } => write!(f, "key file {path} has an unacceptable size (at most {limit} bytes)"),
            SecretErrorKind::Width { wanted } => write!(f, "key file {path} must contain exactly {wanted} raw bytes"),
        }
    }
}
impl std::error::Error for SecretError {}
impl From<SecretError> for String {
    fn from(e: SecretError) -> String {
        e.to_string()
    }
}

/// Read a private file of `1..=limit` bytes.
pub fn read_private(path: &Path, limit: usize, custody: Custody) -> Result<Zeroizing<Vec<u8>>, SecretError> {
    read_bounded(path, 1, limit, custody)
}

/// Read a private file of `0..=limit` bytes (an empty marker file is a valid answer).
pub fn read_private_or_empty(path: &Path, limit: usize, custody: Custody) -> Result<Zeroizing<Vec<u8>>, SecretError> {
    read_bounded(path, 0, limit, custody)
}

fn read_bounded(path: &Path, min: usize, limit: usize, custody: Custody) -> Result<Zeroizing<Vec<u8>>, SecretError> {
    let fail = |kind| SecretError { path: path.to_owned(), kind };
    let euid = crate::private::euid();
    if custody == Custody::FileAndDirectory {
        let parent = match path.parent() {
            Some(p) if p.as_os_str().is_empty() => Path::new("."),
            Some(p) => p,
            None => return Err(fail(SecretErrorKind::Custody("has no parent directory"))),
        };
        let directory = fs::symlink_metadata(parent).map_err(|e| fail(SecretErrorKind::Unreadable(e)))?;
        if !crate::private::dir_ok(&directory) {
            return Err(fail(SecretErrorKind::Custody("is not in an owner-private directory")));
        }
    }
    let mut file: File = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(path)
        .map_err(|e| fail(SecretErrorKind::Unreadable(e)))?;
    let meta = file.metadata().map_err(|e| fail(SecretErrorKind::Unreadable(e)))?;
    if !meta.is_file() {
        return Err(fail(SecretErrorKind::Custody("is not a regular file")));
    }
    if meta.uid() != euid {
        return Err(fail(SecretErrorKind::Custody("is not owned by this user")));
    }
    if meta.mode() & 0o077 != 0 {
        return Err(fail(SecretErrorKind::Custody("is readable or writable by group or others (owner-private 0600 required)")));
    }
    let mut bytes = Zeroizing::new(Vec::with_capacity(limit.min(4096) + 1));
    (&mut file).take(limit as u64 + 1).read_to_end(&mut bytes).map_err(|e| fail(SecretErrorKind::Unreadable(e)))?;
    if bytes.len() < min || bytes.len() > limit {
        return Err(fail(SecretErrorKind::Size { limit }));
    }
    Ok(bytes)
}

/// Read a 32-byte seed file (an Ed25519 signing seed, a symmetric key): exactly 32 raw bytes.
pub fn read_seed(path: &Path, custody: Custody) -> Result<Zeroizing<[u8; 32]>, SecretError> {
    let bytes = read_private(path, 33, custody)?;
    let seed: [u8; 32] = bytes.as_slice().try_into().map_err(|_| SecretError {
        path: path.to_owned(),
        kind: SecretErrorKind::Width { wanted: 32 },
    })?;
    Ok(Zeroizing::new(seed))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    fn scratch(tag: &str, mode: u32) -> PathBuf {
        let p = std::env::temp_dir().join(format!("mini-sdk-secret-{tag}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&p);
        fs::create_dir_all(&p).unwrap();
        fs::set_permissions(&p, fs::Permissions::from_mode(mode)).unwrap();
        p
    }
    fn key(dir: &Path, name: &str, bytes: &[u8], mode: u32) -> PathBuf {
        let p = dir.join(name);
        fs::write(&p, bytes).unwrap();
        fs::set_permissions(&p, fs::Permissions::from_mode(mode)).unwrap();
        p
    }

    #[test]
    fn a_private_32_byte_seed_loads_and_every_other_shape_refuses() {
        let dir = scratch("seed", 0o700);
        assert_eq!(*read_seed(&key(&dir, "ok", &[9; 32], 0o600), Custody::FileNoFollow).unwrap(), [9u8; 32]);
        let short = read_seed(&key(&dir, "short", &[9; 31], 0o600), Custody::FileNoFollow).unwrap_err().to_string();
        assert!(short.contains("exactly 32"), "{short}");
        assert!(read_seed(&key(&dir, "long", &[9; 33], 0o600), Custody::FileNoFollow).unwrap_err().to_string().contains("exactly 32"));
        assert!(matches!(read_seed(&key(&dir, "empty", b"", 0o600), Custody::FileNoFollow).unwrap_err().kind, SecretErrorKind::Size { .. }));
        assert!(read_seed(&key(&dir, "wide", &[9; 32], 0o640), Custody::FileNoFollow).unwrap_err().to_string().contains("group or others"));
        assert!(read_seed(&key(&dir, "world", &[9; 32], 0o604), Custody::FileNoFollow).is_err());
        let link = dir.join("link");
        std::os::unix::fs::symlink(dir.join("ok"), &link).unwrap();
        assert!(read_seed(&link, Custody::FileNoFollow).is_err(), "no-follow custody never reads through a link");
        assert!(read_seed(&link, Custody::FileAndDirectory).is_err());
        assert!(read_seed(&dir, Custody::FileNoFollow).is_err(), "a directory is not a key");
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn directory_custody_is_checked_only_when_asked() {
        let open = scratch("open-dir", 0o755);
        let path = key(&open, "k", &[1; 32], 0o600);
        assert!(read_seed(&path, Custody::FileNoFollow).is_ok());
        assert!(read_seed(&path, Custody::FileAndDirectory).unwrap_err().to_string().contains("owner-private directory"));
        fs::set_permissions(&open, fs::Permissions::from_mode(0o700)).unwrap();
        assert!(read_seed(&path, Custody::FileAndDirectory).is_ok());
        fs::remove_dir_all(open).unwrap();
    }

    #[test]
    fn read_private_bounds_the_file() {
        let dir = scratch("bound", 0o700);
        assert_eq!(read_private(&key(&dir, "a", b"abc", 0o600), 3, Custody::FileNoFollow).unwrap().as_slice(), b"abc");
        assert!(matches!(read_private(&key(&dir, "b", b"abcd", 0o600), 3, Custody::FileNoFollow).unwrap_err().kind, SecretErrorKind::Size { limit: 3 }));
        assert!(read_private(&key(&dir, "e", b"", 0o600), 3, Custody::FileNoFollow).is_err(), "a secret is never empty");
        assert!(read_private_or_empty(&key(&dir, "m", b"", 0o600), 0, Custody::FileNoFollow).unwrap().is_empty(), "an empty marker is");
        fs::remove_dir_all(dir).unwrap();
    }
}
