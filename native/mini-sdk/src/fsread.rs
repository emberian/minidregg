//! The ONE bounded reader of a regular file.
//!
//! The file is opened without following a symlink and without blocking, and every check runs on
//! the OPENED descriptor: it must be a regular file whose size is within `min..=limit`, and the
//! bytes read must be exactly that size (a file that changed under the read refuses). Nothing
//! beyond `limit` bytes is ever buffered.
use std::fs::OpenOptions;
use std::io::{self, Read};
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub struct ReadError {
    pub path: PathBuf,
    pub kind: ReadErrorKind,
}

#[derive(Debug)]
pub enum ReadErrorKind {
    Io(io::Error),
    NotRegular,
    Size { min: usize, limit: usize },
    Changed,
}

impl ReadError {
    /// The path does not exist.
    pub fn is_not_found(&self) -> bool {
        matches!(&self.kind, ReadErrorKind::Io(e) if e.kind() == io::ErrorKind::NotFound)
    }
}

impl std::fmt::Display for ReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let path = self.path.display();
        match &self.kind {
            ReadErrorKind::Io(e) => write!(f, "cannot read {path}: {e}"),
            ReadErrorKind::NotRegular => write!(f, "{path} must be a regular file (a symlink is never followed)"),
            ReadErrorKind::Size { min, limit } => write!(f, "{path} must contain {min}..={limit} bytes"),
            ReadErrorKind::Changed => write!(f, "{path} changed during read"),
        }
    }
}
impl std::error::Error for ReadError {}
impl From<ReadError> for String {
    fn from(e: ReadError) -> String {
        e.to_string()
    }
}

/// Read the regular file at `path`, which must hold `min..=limit` bytes.
pub fn read_regular(path: &Path, min: usize, limit: usize) -> Result<Vec<u8>, ReadError> {
    let fail = |kind| ReadError { path: path.to_owned(), kind };
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK | libc::O_CLOEXEC)
        .open(path)
        .map_err(|e| fail(ReadErrorKind::Io(e)))?;
    let meta = file.metadata().map_err(|e| fail(ReadErrorKind::Io(e)))?;
    if !meta.is_file() {
        return Err(fail(ReadErrorKind::NotRegular));
    }
    let size = meta.len();
    if size < min as u64 || size > limit as u64 {
        return Err(fail(ReadErrorKind::Size { min, limit }));
    }
    let mut bytes = Vec::with_capacity(size as usize);
    (&mut file).take(limit as u64 + 1).read_to_end(&mut bytes).map_err(|e| fail(ReadErrorKind::Io(e)))?;
    if bytes.len() as u64 != size {
        return Err(fail(ReadErrorKind::Changed));
    }
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn scratch(tag: &str) -> PathBuf {
        let p = std::env::temp_dir().join(format!("mini-sdk-fsread-{tag}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&p);
        fs::create_dir_all(&p).unwrap();
        p
    }

    #[test]
    fn the_bounds_are_inclusive_and_checked_before_any_read() {
        let dir = scratch("bounds");
        let file = dir.join("f");
        fs::write(&file, b"abc").unwrap();
        assert_eq!(read_regular(&file, 1, 3).unwrap(), b"abc");
        assert_eq!(read_regular(&file, 3, 3).unwrap(), b"abc");
        assert!(matches!(read_regular(&file, 1, 2).unwrap_err().kind, ReadErrorKind::Size { min: 1, limit: 2 }));
        assert!(matches!(read_regular(&file, 4, 9).unwrap_err().kind, ReadErrorKind::Size { .. }));
        let empty = dir.join("e");
        fs::write(&empty, b"").unwrap();
        assert!(read_regular(&empty, 1, 9).is_err(), "empty refuses when a byte is required");
        assert!(read_regular(&empty, 0, 9).unwrap().is_empty(), "and is accepted when it is not");
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn only_a_regular_file_is_read_never_through_a_link_and_never_a_pipe_or_directory() {
        let dir = scratch("kind");
        let file = dir.join("f");
        fs::write(&file, b"abc").unwrap();
        let link = dir.join("l");
        std::os::unix::fs::symlink(&file, &link).unwrap();
        assert!(read_regular(&link, 0, 9).is_err(), "a symlink is never followed");
        assert!(read_regular(&dir, 0, 9).is_err(), "a directory is not a file");
        let fifo = dir.join("p");
        let c = std::ffi::CString::new(fifo.to_str().unwrap()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(c.as_ptr(), 0o600) }, 0);
        assert!(matches!(read_regular(&fifo, 0, 9).unwrap_err().kind, ReadErrorKind::NotRegular), "a pipe refuses without blocking");
        assert!(read_regular(&dir.join("absent"), 0, 9).unwrap_err().is_not_found());
        fs::remove_dir_all(dir).unwrap();
    }
}
