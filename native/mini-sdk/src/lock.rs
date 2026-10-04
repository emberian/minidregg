//! The ONE advisory-lock implementation: an exclusive, non-blocking `flock` on an owner-private
//! regular file, held by a [`Lease`].
//!
//! The lock file is opened without following symlinks and its custody is checked on the opened
//! descriptor (regular, owned by this euid, no group/other bits, a single link), so a planted or
//! shared file never silently becomes a lock. The lease releases on drop, but only in the process
//! that took it: a forked child that inherited the descriptor and drops its copy must not unlock
//! the parent.
use std::fs::{File, OpenOptions};
use std::io;
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::Path;
use std::time::Duration;

/// Why a lock was not taken.
#[derive(Debug)]
pub enum LockError {
    /// Another descriptor (any process, or another open description in this one) holds it.
    Busy,
    /// The path is not an owner-private, regular, single-link file.
    Unsafe,
    Io(io::Error),
}

impl std::fmt::Display for LockError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LockError::Busy => f.write_str("the lock is held elsewhere"),
            LockError::Unsafe => f.write_str("the lock file is not an owner-private regular single-link file"),
            LockError::Io(e) => e.fmt(f),
        }
    }
}

/// Whether the lock file may be created.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Create {
    /// Create it (0600) when absent.
    Yes,
    /// It must already exist.
    No,
}

/// How long to wait for a busy lock before reporting [`LockError::Busy`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Wait {
    /// Fail at once.
    No,
    /// Retry `tries` more times, `interval` apart.
    Poll { tries: u32, interval: Duration },
}

/// A held lock. Dropping it (in the owning process) releases it.
#[derive(Debug)]
pub struct Lease {
    file: File,
    owner_pid: libc::pid_t,
}

impl Lease {
    /// Take the exclusive lock at `path`.
    pub fn acquire(path: &Path, create: Create, wait: Wait) -> Result<Lease, LockError> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(create == Create::Yes)
            .truncate(false)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(path)
            .map_err(LockError::Io)?;
        let meta = file.metadata().map_err(LockError::Io)?;
        // SAFETY: geteuid has no preconditions and cannot fail.
        if !meta.is_file() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o077 != 0 || meta.nlink() != 1 {
            return Err(LockError::Unsafe);
        }
        let mut remaining = match wait {
            Wait::No => 0,
            Wait::Poll { tries, .. } => tries,
        };
        loop {
            // SAFETY: a valid open descriptor; flock has no memory preconditions.
            if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } == 0 {
                // SAFETY: getpid has no preconditions and cannot fail.
                return Ok(Lease { file, owner_pid: unsafe { libc::getpid() } });
            }
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::WouldBlock {
                return Err(LockError::Io(error));
            }
            match wait {
                Wait::Poll { interval, .. } if remaining > 0 => {
                    remaining -= 1;
                    std::thread::sleep(interval);
                }
                _ => return Err(LockError::Busy),
            }
        }
    }

    /// Release now (idempotent; a no-op in a process that merely inherited the descriptor).
    pub fn release(&self) {
        // SAFETY: getpid/flock on a valid descriptor have no memory preconditions.
        if unsafe { libc::getpid() } == self.owner_pid {
            unsafe { libc::flock(self.file.as_raw_fd(), libc::LOCK_UN) };
        }
    }
}

impl Drop for Lease {
    fn drop(&mut self) {
        self.release();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

    fn scratch(tag: &str) -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!("mini-sdk-lock-{tag}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&p);
        fs::create_dir_all(&p).unwrap();
        p
    }

    #[test]
    fn exclusive_across_descriptors_and_recoverable_after_drop() {
        let dir = scratch("excl");
        let path = dir.join("l");
        let first = Lease::acquire(&path, Create::Yes, Wait::No).unwrap();
        assert!(matches!(Lease::acquire(&path, Create::Yes, Wait::No), Err(LockError::Busy)));
        drop(first);
        let second = Lease::acquire(&path, Create::No, Wait::No).unwrap();
        second.release();
        drop(Lease::acquire(&path, Create::No, Wait::No).unwrap());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn polling_wins_the_lock_when_the_holder_lets_go() {
        let dir = scratch("poll");
        let path = dir.join("l");
        let held = Lease::acquire(&path, Create::Yes, Wait::No).unwrap();
        let waiter = {
            let path = path.clone();
            std::thread::spawn(move || Lease::acquire(&path, Create::No, Wait::Poll { tries: 200, interval: Duration::from_millis(10) }).is_ok())
        };
        std::thread::sleep(Duration::from_millis(50));
        drop(held);
        assert!(waiter.join().unwrap());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn unsafe_lock_files_refuse() {
        let dir = scratch("unsafe");
        let readable = dir.join("readable");
        fs::write(&readable, b"").unwrap();
        fs::set_permissions(&readable, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(matches!(Lease::acquire(&readable, Create::Yes, Wait::No), Err(LockError::Unsafe)));
        let target = dir.join("target");
        fs::write(&target, b"").unwrap();
        fs::set_permissions(&target, fs::Permissions::from_mode(0o600)).unwrap();
        let link = dir.join("link");
        std::os::unix::fs::symlink(&target, &link).unwrap();
        assert!(matches!(Lease::acquire(&link, Create::Yes, Wait::No), Err(LockError::Io(_))), "a symlink is never followed");
        let hard = dir.join("hard");
        fs::hard_link(&target, &hard).unwrap();
        assert!(matches!(Lease::acquire(&hard, Create::Yes, Wait::No), Err(LockError::Unsafe)), "a second link refuses");
        assert!(matches!(Lease::acquire(&dir.join("absent"), Create::No, Wait::No), Err(LockError::Io(_))));
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn a_forked_child_dropping_the_inherited_lease_does_not_unlock_the_parent() {
        let dir = scratch("fork");
        let path = dir.join("l");
        let lease = Lease::acquire(&path, Create::Yes, Wait::No).unwrap();
        // SAFETY: the child only drops its copy and `_exit`s.
        let pid = unsafe { libc::fork() };
        assert!(pid >= 0);
        if pid == 0 {
            drop(lease);
            unsafe { libc::_exit(0) };
        }
        let mut status = 0;
        assert_eq!(unsafe { libc::waitpid(pid, &mut status, 0) }, pid);
        assert!(matches!(Lease::acquire(&path, Create::No, Wait::No), Err(LockError::Busy)), "the parent still holds it");
        drop(lease);
        fs::remove_dir_all(dir).unwrap();
    }
}
