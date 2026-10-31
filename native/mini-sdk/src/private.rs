//! Owner-private custody checks and directory creation: the ONE definition of what "owner-private"
//! means for a directory, a regular file, and an operator socket.
//!
//! A path is owner-private when it is not reached through a symlink (the metadata is
//! `symlink_metadata`, or the opened descriptor's), is owned by this effective uid, and grants
//! nothing to group or others. A custody FILE additionally has a single link (a second name for
//! it is another way in).
use std::fs::{self, Metadata};
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt};
use std::path::Path;

use crate::{Error, Result};

/// This process's effective uid.
pub fn euid() -> u32 {
    // SAFETY: geteuid has no preconditions and cannot fail.
    unsafe { libc::geteuid() }
}

/// Owned by this euid (nothing is said of its mode).
pub fn owned(meta: &Metadata) -> bool {
    meta.uid() == euid()
}

/// An owner-only directory owned by this euid.
pub fn dir_ok(meta: &Metadata) -> bool {
    meta.is_dir() && owned(meta) && meta.mode() & 0o077 == 0
}

/// An owner-only regular file owned by this euid with exactly one link.
pub fn file_ok(meta: &Metadata) -> bool {
    meta.is_file() && owned(meta) && meta.mode() & 0o077 == 0 && meta.nlink() == 1
}

/// An owner-only socket node owned by this euid.
pub fn socket_ok(meta: &Metadata) -> bool {
    meta.file_type().is_socket() && owned(meta) && meta.mode() & 0o077 == 0
}

/// Refuse unless `path` itself (not through a symlink) is an owner-private directory.
pub fn check_dir(path: &Path) -> Result<()> {
    let meta = fs::symlink_metadata(path).map_err(|e| Error(format!("cannot inspect {}: {e}", path.display())))?;
    if !dir_ok(&meta) {
        return Err(Error(format!("{} must be an owner-private directory", path.display())));
    }
    Ok(())
}

/// Refuse unless `path` itself (not through a symlink) is an owner-private regular file with one link.
pub fn check_file(path: &Path) -> Result<()> {
    let meta = fs::symlink_metadata(path).map_err(|e| Error(format!("cannot inspect {}: {e}", path.display())))?;
    if !file_ok(&meta) {
        return Err(Error(format!("{} must be an owner-private regular file with one link", path.display())));
    }
    Ok(())
}

/// Refuse unless `socket` is an owner-private socket node under an owner-private directory.
pub fn check_socket(socket: &Path) -> Result<()> {
    let parent = socket.parent().ok_or_else(|| Error(format!("{} has no parent directory", socket.display())))?;
    check_dir(parent)?;
    let meta = fs::symlink_metadata(socket).map_err(|e| Error(format!("cannot inspect {}: {e}", socket.display())))?;
    if !socket_ok(&meta) {
        return Err(Error(format!("{} must be an owner-private socket", socket.display())));
    }
    Ok(())
}

/// Create (0700) or accept an owner-private directory: an existing directory is accepted only if
/// it passes [`check_dir`].
pub fn ensure_dir(path: &Path) -> Result<()> {
    match fs::DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => {}
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
        Err(e) => return Err(Error(format!("cannot create {}: {e}", path.display()))),
    }
    check_dir(path)
}

/// [`ensure_dir`] with missing ancestors created (0700) too. The ancestors that already exist
/// are the caller's; only `path` itself is checked.
pub fn ensure_dir_all(path: &Path) -> Result<()> {
    fs::DirBuilder::new()
        .recursive(true)
        .mode(0o700)
        .create(path)
        .map_err(|e| Error(format!("cannot create {}: {e}", path.display())))?;
    check_dir(path)
}

/// Create an owner-private directory that must not already exist.
pub fn create_dir(path: &Path) -> Result<()> {
    fs::DirBuilder::new()
        .mode(0o700)
        .create(path)
        .map_err(|e| Error(format!("cannot create {}: {e}", path.display())))?;
    check_dir(path)
}

/// The uid of a connected Unix socket's peer, from the kernel (never from the peer's words).
/// Wait until `fd` is readable (a listener has a connection), at most `timeout`: the wait an
/// accept loop on a non-blocking listener does between accepts, instead of sleeping past the
/// connection that just arrived.
pub fn wait_readable(fd: std::os::fd::RawFd, timeout: std::time::Duration) {
    let mut ready = libc::pollfd { fd, events: libc::POLLIN, revents: 0 };
    let millis = timeout.as_millis().clamp(1, i32::MAX as u128) as i32;
    unsafe { libc::poll(&mut ready, 1, millis) };
}

#[cfg(any(target_os = "macos", target_os = "freebsd", target_os = "openbsd", target_os = "netbsd"))]
pub fn peer_uid(stream: &std::os::unix::net::UnixStream) -> Result<u32> {
    use std::os::unix::io::AsRawFd;
    let (mut uid, mut gid) = (0, 0);
    if unsafe { libc::getpeereid(stream.as_raw_fd(), &mut uid, &mut gid) } != 0 {
        return Err(Error(format!("operator peer credential: {}", std::io::Error::last_os_error())));
    }
    Ok(uid)
}

/// The uid of a connected Unix socket's peer, from the kernel (never from the peer's words).
#[cfg(target_os = "linux")]
pub fn peer_uid(stream: &std::os::unix::net::UnixStream) -> Result<u32> {
    use std::os::unix::io::AsRawFd;
    let mut credential = libc::ucred { pid: 0, uid: 0, gid: 0 };
    let mut length = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
    let status = unsafe {
        libc::getsockopt(stream.as_raw_fd(), libc::SOL_SOCKET, libc::SO_PEERCRED,
            (&mut credential as *mut libc::ucred).cast(), &mut length)
    };
    if status != 0 || length as usize != std::mem::size_of::<libc::ucred>() {
        return Err(Error(format!("operator peer credential: {}", std::io::Error::last_os_error())));
    }
    Ok(credential.uid)
}

#[cfg(not(any(target_os = "linux", target_os = "macos", target_os = "freebsd", target_os = "openbsd", target_os = "netbsd")))]
pub fn peer_uid(_stream: &std::os::unix::net::UnixStream) -> Result<u32> {
    Err("operator peer credentials are unavailable on this platform".into())
}

/// Remove a socket file no service listens on any more, before binding it again. Only an owned
/// socket that refuses connections is removed, and only while it is still the same file.
pub fn clear_stale_socket(path: &Path) -> Result<()> {
    let metadata = match fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(Error(format!("cannot inspect socket {}: {error}", path.display()))),
    };
    if !metadata.file_type().is_socket() || !owned(&metadata) {
        return Err("socket path is not an owned Unix socket".into());
    }
    match std::os::unix::net::UnixStream::connect(path) {
        Ok(_) => Err("another service still listens on socket".into()),
        Err(error) if error.kind() == std::io::ErrorKind::ConnectionRefused => {
            let current = fs::symlink_metadata(path).map_err(|error| Error(format!("cannot recheck stale socket: {error}")))?;
            if !current.file_type().is_socket() || (current.dev(), current.ino()) != (metadata.dev(), metadata.ino()) {
                return Err("socket path changed during stale recovery".into());
            }
            fs::remove_file(path).map_err(|error| Error(format!("cannot remove stale socket: {error}")))
        }
        Err(error) => Err(Error(format!("cannot prove socket stale: {error}"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;
    use std::os::unix::net::UnixListener;

    fn scratch(tag: &str) -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!("mini-sdk-private-{tag}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&p);
        fs::create_dir_all(&p).unwrap();
        fs::set_permissions(&p, fs::Permissions::from_mode(0o700)).unwrap();
        p
    }
    fn mode(path: &Path, bits: u32) {
        fs::set_permissions(path, fs::Permissions::from_mode(bits)).unwrap();
    }

    #[test]
    fn a_directory_is_private_only_when_owner_only_and_not_a_link() {
        let dir = scratch("dir");
        check_dir(&dir).unwrap();
        for bits in [0o750, 0o705, 0o770, 0o755, 0o777] {
            mode(&dir, bits);
            assert!(check_dir(&dir).is_err(), "{bits:o} must refuse");
        }
        mode(&dir, 0o700);
        let link = dir.join("link");
        std::os::unix::fs::symlink(&dir, &link).unwrap();
        assert!(check_dir(&link).is_err(), "a symlink to a private directory is not one");
        let file = dir.join("f");
        fs::write(&file, b"x").unwrap();
        assert!(check_dir(&file).is_err(), "a file is not a directory");
        assert!(check_dir(&dir.join("absent")).is_err());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_file_is_private_only_when_owner_only_regular_and_singly_linked() {
        let dir = scratch("file");
        let file = dir.join("f");
        fs::write(&file, b"x").unwrap();
        mode(&file, 0o600);
        check_file(&file).unwrap();
        for bits in [0o640, 0o604, 0o660, 0o644] {
            mode(&file, bits);
            assert!(check_file(&file).is_err(), "{bits:o} must refuse");
        }
        mode(&file, 0o600);
        fs::hard_link(&file, dir.join("second-name")).unwrap();
        assert!(check_file(&file).is_err(), "a second link refuses");
        let target = dir.join("t");
        fs::write(&target, b"x").unwrap();
        mode(&target, 0o600);
        let link = dir.join("l");
        std::os::unix::fs::symlink(&target, &link).unwrap();
        assert!(check_file(&link).is_err(), "a symlink is not a regular file");
        assert!(check_file(&dir).is_err(), "a directory is not a file");
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_socket_is_private_only_under_a_private_directory_and_itself_owner_only() {
        let dir = scratch("socket");
        let socket = dir.join("s");
        let _listener = UnixListener::bind(&socket).unwrap();
        mode(&socket, 0o600);
        check_socket(&socket).unwrap();
        mode(&socket, 0o660);
        assert!(check_socket(&socket).is_err(), "a group-accessible socket refuses");
        mode(&socket, 0o600);
        mode(&dir, 0o750);
        assert!(check_socket(&socket).is_err(), "an open parent refuses");
        mode(&dir, 0o700);
        let plain = dir.join("plain");
        fs::write(&plain, b"x").unwrap();
        mode(&plain, 0o600);
        assert!(check_socket(&plain).is_err(), "a regular file is not a socket");
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn ensure_creates_accepts_and_refuses_what_it_did_not_make_private() {
        let dir = scratch("ensure");
        let child = dir.join("a");
        ensure_dir(&child).unwrap();
        assert_eq!(fs::metadata(&child).unwrap().permissions().mode() & 0o777, 0o700);
        ensure_dir(&child).unwrap();
        mode(&child, 0o755);
        assert!(ensure_dir(&child).is_err(), "an existing open directory is refused, not tightened");
        assert!(ensure_dir(&dir.join("missing/deeper")).is_err(), "no ancestors are made");
        let deep = dir.join("x/y/z");
        ensure_dir_all(&deep).unwrap();
        assert_eq!(fs::metadata(dir.join("x/y")).unwrap().permissions().mode() & 0o777, 0o700);
        mode(&deep, 0o755);
        assert!(ensure_dir_all(&deep).is_err());
        let fresh = dir.join("fresh");
        create_dir(&fresh).unwrap();
        assert!(create_dir(&fresh).is_err(), "create_dir never accepts an existing directory");
        fs::remove_dir_all(dir).unwrap();
    }
}
