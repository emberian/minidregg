//! Bounded, inode-pinned fork/exec handshake for a future app-generation unit.
//!
//! This is an internal physical primitive, never a socket command. Only the
//! native-admitted lifecycle adapter may choose its SPK image, app UID/GID,
//! exact bubblewrap image and fd3/4/5 bindings. The caller must hold the
//! operation journal's flock throughout `spawn_bounded` and its Running fsync.
#![allow(dead_code)] // Staged until the native BEGIN adapter can call it; no public launch path.

use crate::sandbox::open_protected_directory;
use sha2::{Digest, Sha256};
use std::ffi::{CString, OsStr};
use std::fs::File;
use std::io::{self, Read};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::MetadataExt;
use std::path::PathBuf;
use std::time::{Duration, Instant};

const MAX_ELF_BYTES: u64 = 64 * 1024 * 1024;
const MAX_ARG_ENV_BYTES: usize = 128 * 1024;
const MAX_HANDSHAKE: Duration = Duration::from_secs(10);

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

/// Pre-opened app-side descriptors. Sources must be >=10; targets are exactly
/// fd3 (Cap'n Proto), fd4 (read-only package root), fd5 (bounded /var).
#[derive(Clone, Copy, Debug)]
pub(crate) struct AppFds {
    pub rpc: RawFd,
    pub image: RawFd,
    pub persistent_var: RawFd,
}

#[derive(Debug)]
pub(crate) struct SpawnSpec {
    pub program: PathBuf,
    pub sha256: String,
    pub args: Vec<String>,
    pub env: Vec<(String, String)>,
    pub app_uid: u32,
    pub app_gid: u32,
    pub fds: Option<AppFds>,
}

fn valid_env_key(value: &str) -> bool {
    let mut chars = value.bytes();
    matches!(chars.next(), Some(b'A'..=b'Z' | b'a'..=b'z' | b'_'))
        && chars.all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

fn validate(spec: &SpawnSpec, test_mode: bool) -> io::Result<()> {
    if !spec.program.is_absolute()
        || spec.app_uid == 0
        || spec.app_gid == 0
        || (!test_mode && spec.program.file_name() != Some(OsStr::new("bwrap")))
        || spec.sha256.len() != 64
        || !spec
            .sha256
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        || spec.args.len() > 256
        || spec.env.len() > 128
    {
        return Err(invalid("invalid pinned app launch shape"));
    }
    let bytes: usize = spec.args.iter().map(String::len).sum::<usize>()
        + spec
            .env
            .iter()
            .map(|(k, v)| k.len() + v.len() + 1)
            .sum::<usize>();
    if bytes > MAX_ARG_ENV_BYTES
        || spec.args.iter().any(|v| v.as_bytes().contains(&0))
        || spec
            .env
            .iter()
            .any(|(k, v)| !valid_env_key(k) || v.as_bytes().contains(&0))
    {
        return Err(invalid("invalid or oversized app argv/environment"));
    }
    if let Some(fds) = spec.fds {
        let sources = [fds.rpc, fds.image, fds.persistent_var];
        if sources
            .iter()
            .any(|fd| *fd < 10 || unsafe { libc::fcntl(*fd, libc::F_GETFD) } < 0)
            || sources[0] == sources[1]
            || sources[0] == sources[2]
            || sources[1] == sources[2]
        {
            return Err(invalid("invalid fd3/4/5 source mapping"));
        }
    } else if !test_mode {
        return Err(invalid("SPK launch requires fd3/4/5"));
    }
    Ok(())
}

fn pinned_executable(spec: &SpawnSpec) -> io::Result<OwnedFd> {
    let parent = spec
        .program
        .parent()
        .ok_or_else(|| invalid("executable has no parent"))?;
    let directory = open_protected_directory(parent, spec.app_uid, false)?;
    let name = CString::new(
        spec.program
            .file_name()
            .ok_or_else(|| invalid("missing executable"))?
            .as_bytes(),
    )
    .map_err(|_| invalid("NUL executable name"))?;
    let raw = unsafe {
        libc::openat(
            directory.as_raw_fd(),
            name.as_ptr(),
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    let file = unsafe { File::from_raw_fd(raw) };
    let meta = file.metadata()?;
    if !meta.is_file()
        || meta.uid() == spec.app_uid
        || meta.mode() & 0o022 != 0
        || meta.mode() & 0o111 == 0
        || meta.len() > MAX_ELF_BYTES
    {
        return Err(invalid(
            "launch executable is writable, untrusted or oversized",
        ));
    }
    let mut hash = Sha256::new();
    let mut reader = &file;
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let n = reader.read(&mut buffer)?;
        if n == 0 {
            break;
        }
        hash.update(&buffer[..n]);
    }
    if format!("{:x}", hash.finalize()) != spec.sha256 {
        return Err(invalid("launch executable SHA-256 pin mismatch"));
    }
    let duplicate = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 16) };
    if duplicate < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { OwnedFd::from_raw_fd(duplicate) })
}

fn duplicate_high(fd: RawFd) -> io::Result<OwnedFd> {
    let duplicate = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 16) };
    if duplicate < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { OwnedFd::from_raw_fd(duplicate) })
}

unsafe fn fail(write_fd: RawFd) -> ! {
    let errno = *libc::__errno_location();
    let bytes = errno.to_le_bytes();
    let _ = libc::write(write_fd, bytes.as_ptr().cast(), bytes.len());
    libc::_exit(127)
}

unsafe fn close_unlisted(keep: &[u32]) -> bool {
    let mut first = 3_u32;
    for &fd in keep {
        if fd > first && libc::syscall(libc::SYS_close_range, first, fd - 1, 0_u32) < 0 {
            return false;
        }
        first = fd.saturating_add(1);
    }
    libc::syscall(libc::SYS_close_range, first, u32::MAX, 0_u32) >= 0
}

/// Runs after fork with all C strings and keep-list allocated in the parent.
/// No Rust destructor or allocation is used in this child branch.
struct ChildExecInput<'a> {
    spec: &'a SpawnSpec,
    executable: RawFd,
    dev_null: RawFd,
    read_fd: RawFd,
    write_fd: RawFd,
    argv: &'a [*const libc::c_char],
    environ: &'a [*const libc::c_char],
    keep: &'a [u32],
}

unsafe fn child_exec(input: ChildExecInput<'_>) -> ! {
    let ChildExecInput {
        spec,
        executable,
        dev_null,
        read_fd,
        write_fd,
        argv,
        environ,
        keep,
    } = input;
    libc::close(read_fd);
    #[cfg(test)]
    if spec.args.first().map(String::as_str) == Some("--mini-spk-test-hang-before-exec") {
        // Fault injection lives only in the libtest image. The parent must
        // SIGKILL/reap this child before the journal lock can be released.
        libc::sleep(15);
    }
    #[cfg(test)]
    if spec.args.first().map(String::as_str) == Some("--mini-spk-test-exit-before-exec") {
        libc::_exit(42);
    }
    if let Some(fds) = spec.fds {
        for (source, target) in [(fds.rpc, 3), (fds.image, 4), (fds.persistent_var, 5)] {
            if libc::dup2(source, target) != target {
                fail(write_fd);
            }
        }
        for target in [3, 4, 5] {
            if libc::fcntl(target, libc::F_SETFD, 0) != 0 {
                fail(write_fd);
            }
        }
    }
    if libc::dup2(dev_null, 0) != 0 {
        fail(write_fd);
    }
    if !close_unlisted(keep) {
        fail(write_fd);
    }
    if libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0 {
        fail(write_fd);
    }
    if libc::geteuid() == 0 {
        if libc::setgroups(0, std::ptr::null()) != 0
            || libc::setresgid(spec.app_gid, spec.app_gid, spec.app_gid) != 0
            || libc::setresuid(spec.app_uid, spec.app_uid, spec.app_uid) != 0
        {
            fail(write_fd);
        }
    } else if libc::geteuid() != spec.app_uid || libc::getegid() != spec.app_gid {
        fail(write_fd);
    }
    if libc::geteuid() != spec.app_uid || libc::getegid() != spec.app_gid {
        fail(write_fd);
    }
    let empty = b"\0";
    libc::syscall(
        libc::SYS_execveat,
        executable,
        empty.as_ptr().cast::<libc::c_char>(),
        argv.as_ptr(),
        environ.as_ptr(),
        libc::AT_EMPTY_PATH,
    );
    fail(write_fd)
}

fn wait_reap(pid: libc::pid_t) -> io::Result<i32> {
    let mut status = 0;
    loop {
        let result = unsafe { libc::waitpid(pid, &mut status, 0) };
        if result == pid {
            return Ok(status);
        }
        if result < 0 && io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
            return Err(io::Error::last_os_error());
        }
    }
}

fn kill_reap(pid: libc::pid_t) -> bool {
    unsafe {
        libc::kill(pid, libc::SIGKILL);
    }
    let deadline = Instant::now() + Duration::from_secs(5);
    loop {
        let result = unsafe { libc::waitpid(pid, std::ptr::null_mut(), libc::WNOHANG) };
        if result == pid
            || result < 0 && io::Error::last_os_error().raw_os_error() == Some(libc::ECHILD)
        {
            return true;
        }
        if result < 0 && io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
            return false;
        }
        if Instant::now() >= deadline {
            return false;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

fn abort_handshake(pid: libc::pid_t, error: io::Error) -> io::Error {
    if kill_reap(pid) {
        error
    } else {
        io::Error::other(format!(
            "{error}; direct child death unconfirmed; fence exact unit"
        ))
    }
}

/// The caller retains this handle for the whole application unit lifetime.
/// Dropping it kills the direct bwrap child; systemd KillMode=control-group
/// additionally closes every descendant on service stop or controller crash.
#[derive(Debug)]
pub(crate) struct BoundedChild {
    pid: libc::pid_t,
    reaped: bool,
}

impl BoundedChild {
    pub fn pid(&self) -> u32 {
        self.pid as u32
    }
    pub fn kill_and_reap(&mut self) -> bool {
        if !self.reaped {
            self.reaped = kill_reap(self.pid);
        }
        self.reaped
    }
    pub fn wait(&mut self) -> io::Result<i32> {
        if !self.reaped {
            let status = wait_reap(self.pid)?;
            self.reaped = true;
            return Ok(status);
        }
        Err(invalid("child already reaped"))
    }
}

impl Drop for BoundedChild {
    fn drop(&mut self) {
        let _ = self.kill_and_reap();
    }
}

fn spawn_inner(spec: &SpawnSpec, test_mode: bool) -> io::Result<BoundedChild> {
    validate(spec, test_mode)?;
    let executable = pinned_executable(spec)?;
    let dev_null = File::open("/dev/null")?;
    let dev_null = duplicate_high(dev_null.as_raw_fd())?;
    let mut pipe = [0_i32; 2];
    if unsafe { libc::pipe2(pipe.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let read_fd = unsafe { OwnedFd::from_raw_fd(pipe[0]) };
    let write_fd = duplicate_high(pipe[1]);
    unsafe {
        libc::close(pipe[1]);
    }
    let write_fd = write_fd?;
    let argv_strings: Vec<CString> = std::iter::once(spec.program.as_os_str().as_bytes())
        .chain(spec.args.iter().map(|arg| arg.as_bytes()))
        .map(|bytes| CString::new(bytes).map_err(|_| invalid("NUL launch argument")))
        .collect::<io::Result<_>>()?;
    let env_strings: Vec<CString> = spec
        .env
        .iter()
        .map(|(key, value)| {
            CString::new(format!("{key}={value}")).map_err(|_| invalid("NUL launch environment"))
        })
        .collect::<io::Result<_>>()?;
    let mut argv: Vec<*const libc::c_char> = argv_strings.iter().map(|arg| arg.as_ptr()).collect();
    argv.push(std::ptr::null());
    let mut environ: Vec<*const libc::c_char> =
        env_strings.iter().map(|value| value.as_ptr()).collect();
    environ.push(std::ptr::null());
    let mut keep = vec![executable.as_raw_fd() as u32, write_fd.as_raw_fd() as u32];
    if spec.fds.is_some() {
        keep.extend([3, 4, 5]);
    }
    keep.sort_unstable();
    keep.dedup();
    let pid = unsafe { libc::fork() };
    if pid < 0 {
        return Err(io::Error::last_os_error());
    }
    if pid == 0 {
        unsafe {
            child_exec(ChildExecInput {
                spec,
                executable: executable.as_raw_fd(),
                dev_null: dev_null.as_raw_fd(),
                read_fd: read_fd.as_raw_fd(),
                write_fd: write_fd.as_raw_fd(),
                argv: &argv,
                environ: &environ,
                keep: &keep,
            })
        }
    }
    drop(write_fd);
    let deadline = Instant::now() + MAX_HANDSHAKE;
    let mut failure = [0_u8; 4];
    let mut count = 0;
    loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(abort_handshake(
                pid,
                io::Error::new(io::ErrorKind::TimedOut, "bounded exec handshake"),
            ));
        }
        let mut poll = libc::pollfd {
            fd: read_fd.as_raw_fd(),
            events: libc::POLLIN | libc::POLLHUP,
            revents: 0,
        };
        let millis = remaining.as_millis().min(100) as i32;
        let ready = unsafe { libc::poll(&mut poll, 1, millis) };
        if ready < 0 {
            if io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            let error = io::Error::last_os_error();
            return Err(abort_handshake(pid, error));
        }
        if ready == 0 {
            continue;
        }
        let n = unsafe {
            libc::read(
                read_fd.as_raw_fd(),
                failure[count..].as_mut_ptr().cast(),
                4 - count,
            )
        };
        if n == 0 {
            if count == 0 {
                // A child dying before exec also closes the status pipe. Do
                // not publish Running for a child already known dead. A live
                // child here is still not proof of application readiness.
                let mut status = 0;
                let reaped = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
                if reaped == pid {
                    return Err(invalid("launch child died at exec handshake"));
                }
                if reaped < 0 {
                    return Err(abort_handshake(pid, io::Error::last_os_error()));
                }
                return Ok(BoundedChild { pid, reaped: false });
            }
            return Err(abort_handshake(pid, invalid("partial exec status")));
        }
        if n < 0 {
            if io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            let error = io::Error::last_os_error();
            return Err(abort_handshake(pid, error));
        }
        count += n as usize;
        if count == 4 {
            return Err(abort_handshake(
                pid,
                io::Error::from_raw_os_error(i32::from_le_bytes(failure)),
            ));
        }
    }
}

pub(crate) fn spawn_bounded(spec: &SpawnSpec) -> io::Result<BoundedChild> {
    if unsafe { libc::geteuid() } != 0 {
        return Err(invalid("production SPK gate must run as root"));
    }
    spawn_inner(spec, false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    fn sha(path: &str) -> String {
        let mut file = File::open(path).unwrap();
        let mut hasher = Sha256::new();
        let mut bytes = [0_u8; 8192];
        loop {
            let n = file.read(&mut bytes).unwrap();
            if n == 0 {
                break;
            }
            hasher.update(&bytes[..n]);
        }
        format!("{:x}", hasher.finalize())
    }

    fn harmless_elf() -> PathBuf {
        std::fs::canonicalize("/usr/bin/sleep").unwrap()
    }

    #[test]
    fn rejects_unpinned_or_ambient_launch() {
        let current = unsafe { libc::geteuid() };
        if current == 0 {
            return;
        }
        let spec = SpawnSpec {
            program: harmless_elf(),
            sha256: "0".repeat(64),
            args: vec!["1".into()],
            env: vec![],
            app_uid: current,
            app_gid: unsafe { libc::getegid() },
            fds: None,
        };
        assert!(spawn_inner(&spec, true).is_err());
        assert!(spawn_bounded(&spec).is_err());
        assert_eq!(
            std::fs::metadata(harmless_elf())
                .unwrap()
                .permissions()
                .mode()
                & 0o111,
            0o111
        );
    }

    #[test]
    fn bounded_exec_of_pinned_harmless_elf_reaps() {
        let uid = unsafe { libc::geteuid() };
        if uid == 0 {
            return;
        }
        let harmless = harmless_elf();
        let spec = SpawnSpec {
            program: harmless.clone(),
            sha256: sha(harmless.to_str().unwrap()),
            args: vec!["1".into()],
            env: vec![],
            app_uid: uid,
            app_gid: unsafe { libc::getegid() },
            fds: None,
        };
        let mut child = spawn_inner(&spec, true).unwrap();
        assert!(child.pid() > 0);
        let status = child.wait().unwrap();
        assert!(libc::WIFEXITED(status));
        assert_eq!(libc::WEXITSTATUS(status), 0);
        assert!(child.reaped);
    }

    #[test]
    fn root_gate_drops_to_unprivileged_uid_before_exec() {
        if unsafe { libc::geteuid() } != 0 {
            return;
        }
        let harmless = harmless_elf();
        let spec = SpawnSpec {
            program: harmless.clone(),
            sha256: sha(harmless.to_str().unwrap()),
            args: vec!["1".into()],
            env: vec![],
            app_uid: 65534,
            app_gid: 65534,
            fds: None,
        };
        let mut child = spawn_inner(&spec, true).unwrap();
        let status = child.wait().unwrap();
        assert!(libc::WIFEXITED(status));
        assert_eq!(libc::WEXITSTATUS(status), 0);
    }

    #[test]
    fn hung_preexec_is_killed_at_handshake_deadline() {
        let uid = unsafe { libc::geteuid() };
        if uid == 0 {
            return;
        }
        let harmless = harmless_elf();
        let spec = SpawnSpec {
            program: harmless.clone(),
            sha256: sha(harmless.to_str().unwrap()),
            args: vec!["--mini-spk-test-hang-before-exec".into()],
            env: vec![],
            app_uid: uid,
            app_gid: unsafe { libc::getegid() },
            fds: None,
        };
        let start = Instant::now();
        let result = spawn_inner(&spec, true);
        assert_eq!(result.unwrap_err().kind(), io::ErrorKind::TimedOut);
        assert!(start.elapsed() >= MAX_HANDSHAKE);
        assert!(start.elapsed() < Duration::from_secs(17));
        let mut status = 0;
        assert_eq!(unsafe { libc::waitpid(-1, &mut status, libc::WNOHANG) }, -1);
        assert_eq!(
            io::Error::last_os_error().raw_os_error(),
            Some(libc::ECHILD)
        );
    }

    #[test]
    fn preexec_death_can_close_handshake_without_readiness() {
        let uid = unsafe { libc::geteuid() };
        if uid == 0 {
            return;
        }
        let harmless = harmless_elf();
        let spec = SpawnSpec {
            program: harmless.clone(),
            sha256: sha(harmless.to_str().unwrap()),
            args: vec!["--mini-spk-test-exit-before-exec".into()],
            env: vec![],
            app_uid: uid,
            app_gid: unsafe { libc::getegid() },
            fds: None,
        };
        // The EOF and child exit can race. Either an immediate dead-child
        // refusal or a returned handle whose first wait reports the exit is
        // valid. Neither outcome grants an application-ready signal.
        if let Ok(mut child) = spawn_inner(&spec, true) {
            let status = child.wait().unwrap();
            assert!(libc::WIFEXITED(status));
            assert_eq!(libc::WEXITSTATUS(status), 42);
        }
        let mut status = 0;
        assert_eq!(unsafe { libc::waitpid(-1, &mut status, libc::WNOHANG) }, -1);
        assert_eq!(io::Error::last_os_error().raw_os_error(), Some(libc::ECHILD));
    }
}
