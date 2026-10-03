//! Argument confinement for session reads. This is not same-UID process isolation.
//! The session root is an operator-selected anchor; child paths are opened relative
//! to its held descriptor, never followed through a symlink or reopened by name.
use std::ffi::CString;
use std::fs::{File, OpenOptions};
use std::io::Read;
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Component, Path};

fn component(value: &std::ffi::OsStr) -> Result<CString, String> {
    CString::new(value.as_bytes()).map_err(|_| "session path contains NUL".into())
}

fn parent(root: &Path, path: &Path) -> Result<(File, CString), String> {
    let relative = path.strip_prefix(root).map_err(|_| "file must belong to this session".to_owned())?;
    let parts = relative.components().map(|c| match c {
        Component::Normal(n) => component(n),
        _ => Err("session path contains traversal".into()),
    }).collect::<Result<Vec<_>, _>>()?;
    if parts.is_empty() { return Err("session path names no file".into()); }
    let mut directory = OpenOptions::new().read(true)
        .custom_flags(libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(root).map_err(|e| format!("cannot anchor session directory: {e}"))?;
    for part in &parts[..parts.len()-1] {
        let fd = unsafe { libc::openat(directory.as_raw_fd(), part.as_ptr(),
            libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC) };
        if fd < 0 { return Err(format!("cannot open session directory: {}", std::io::Error::last_os_error())); }
        directory = unsafe { File::from_raw_fd(fd) };
    }
    Ok((directory, parts.last().unwrap().clone()))
}

pub(crate) fn read(root: &Path, path: &Path, limit: usize) -> Result<Vec<u8>, String> {
    let (directory, name) = parent(root, path)?;
    let fd = unsafe { libc::openat(directory.as_raw_fd(), name.as_ptr(),
        libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC | libc::O_NONBLOCK) };
    if fd < 0 { return Err(format!("cannot open session file: {}", std::io::Error::last_os_error())); }
    let file = unsafe { File::from_raw_fd(fd) };
    let metadata = file.metadata().map_err(|e| e.to_string())?;
    if !metadata.is_file() || metadata.len() > limit as u64 {
        return Err("session input must be a bounded regular file".into());
    }
    let mut bytes = Vec::new();
    file.take(limit as u64 + 1).read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    if bytes.len() > limit { return Err("session input exceeds bound".into()); }
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::symlink;
    #[test]
    fn atomic_replacement_retains_foreign_bytes_during_leaf_swap() {
        let root = std::env::temp_dir().join(format!("mini-session-replace-{}", std::process::id()));
        std::fs::create_dir(&root).unwrap();
        let external = root.join("external");
        let record = root.join("record");
        std::fs::write(&external, b"foreign retained bytes").unwrap();
        replace(&root, &record, b"first").unwrap();
        assert_eq!(read(&root, &record, 32).unwrap(), b"first");
        replace(&root, &record, b"second").unwrap();
        assert_eq!(read(&root, &record, 32).unwrap(), b"second");
        std::fs::remove_file(&record).unwrap();
        symlink(&external, &record).unwrap();
        assert!(replace(&root, &record, b"bad").is_err());
        std::fs::remove_file(&record).unwrap();
        let thread_root = root.clone();
        let attacker = std::thread::spawn(move || {
            for _ in 0..256 {
                let leaf = thread_root.join("record");
                let _ = std::fs::remove_file(&leaf);
                let _ = symlink(thread_root.join("external"), &leaf);
                std::thread::yield_now();
            }
        });
        for _ in 0..256 { let _ = replace(&root, &record, b"safe replacement"); }
        attacker.join().unwrap();
        assert_eq!(std::fs::read(&external).unwrap(), b"foreign retained bytes");
        assert!(!std::fs::read_dir(&root).unwrap().filter_map(Result::ok).any(|e| e.file_name().to_string_lossy().starts_with(".mini-replace-")));
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn anchored_reads_refuse_escape_symlinks_fifo_and_oversize() {
        let root = std::env::temp_dir().join(format!("mini-session-fs-{}", std::process::id()));
        std::fs::create_dir(&root).unwrap();
        std::fs::create_dir(root.join("requests")).unwrap();
        std::fs::write(root.join("requests/good.json"), b"{}").unwrap();
        assert_eq!(read(&root, &root.join("requests/good.json"), 2).unwrap(), b"{}");
        assert!(read(&root, &root.join("requests/good.json"), 1).is_err());
        assert!(read(&root, &root.join("requests/../requests/good.json"), 2).is_err());
        assert!(read(&root, Path::new("/etc/passwd"), 1024).is_err());
        symlink("good.json", root.join("requests/link.json")).unwrap();
        symlink("requests", root.join("alias")).unwrap();
        assert!(read(&root, &root.join("requests/link.json"), 2).is_err());
        assert!(read(&root, &root.join("alias/good.json"), 2).is_err());
        let fifo = component(root.join("requests/fifo").as_os_str()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(fifo.as_ptr(), 0o600) }, 0);
        assert!(read(&root, &root.join("requests/fifo"), 2).is_err());
        std::fs::remove_dir_all(&root).unwrap();
    }
}

/// Publish complete bytes under the held parent descriptor. Existing symlink or
/// special-file records refuse; rename never follows a leaf that changes later.
/// The previous record remains intact until the replacement is fsynced.
pub(crate) fn replace(root: &Path, path: &Path, bytes: &[u8]) -> Result<(), String> {
    use std::io::Write;
    let (directory, name) = parent(root, path)?;
    let mut status = std::mem::MaybeUninit::<libc::stat>::uninit();
    let found = unsafe { libc::fstatat(directory.as_raw_fd(), name.as_ptr(), status.as_mut_ptr(), libc::AT_SYMLINK_NOFOLLOW) };
    if found == 0 {
        let status = unsafe { status.assume_init() };
        if status.st_mode & libc::S_IFMT != libc::S_IFREG { return Err("record must be a regular file".into()); }
    } else if std::io::Error::last_os_error().kind() != std::io::ErrorKind::NotFound {
        return Err(std::io::Error::last_os_error().to_string());
    }
    let mut nonce = [0u8; 16];
    File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut nonce)).map_err(|e| e.to_string())?;
    let nonce = nonce.iter().map(|b| format!("{b:02x}")).collect::<String>();
    let temporary = CString::new(format!(".mini-replace-{}-{nonce}", std::process::id())).unwrap();
    let fd = unsafe { libc::openat(directory.as_raw_fd(), temporary.as_ptr(),
        libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC, 0o600) };
    if fd < 0 { return Err(std::io::Error::last_os_error().to_string()); }
    let mut file = unsafe { File::from_raw_fd(fd) };
    let result = file.write_all(bytes).and_then(|()| file.sync_all()).map_err(|e| e.to_string())
        .and_then(|()| {
            if unsafe { libc::renameat(directory.as_raw_fd(), temporary.as_ptr(), directory.as_raw_fd(), name.as_ptr()) } != 0 {
                return Err(std::io::Error::last_os_error().to_string());
            }
            directory.sync_all().map_err(|e| e.to_string())
        });
    // This name was created exclusively by this call; no foreign cleanup.
    if result.is_err() { unsafe { libc::unlinkat(directory.as_raw_fd(), temporary.as_ptr(), 0); } }
    result
}
