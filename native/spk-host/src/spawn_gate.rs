//! Bounded, inode-pinned fork/exec handshake for a future app-generation unit.
//!
//! This is an internal physical primitive, never a socket command. Only the
//! native-admitted lifecycle adapter may choose its SPK image, app UID/GID,
//! exact bubblewrap image and fd3/4/5 bindings. The caller must hold the
//! operation journal's flock throughout `spawn_bounded` and its Running write.

use crate::sandbox::{
    open_protected_directory, IMAGE_FD, MAX_BWRAP_ARGS, MAX_BWRAP_ARG_BYTES, RPC_FD, SECCOMP_FD,
    VAR_FD, PUBLIC_DATA_FD, SHIM_FD,
};
use crate::io_context::IoContext;
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
const MAX_HANDSHAKE: Duration = Duration::from_secs(10);
/// RLIMIT_NOFILE for the app generation (bubblewrap and everything under it).
pub(crate) const APP_MAX_FILES: libc::rlim_t = 1024;
// Linux's maximum extended-attribute value size. The shared launcher can have
// an entry for every operator-provisioned app identity, not merely 64 entries.
const MAX_ACCESS_ACL_BYTES: usize = 64 * 1024;

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

/// Pre-opened app-side descriptors. Sources must be >=10; targets are exactly
/// fd3 (Cap'n Proto), fd4 (read-only package root), fd5 (bounded /var), fd6
/// (sealed seccomp program), and fd1+fd2 (the app's private output pipe).
#[derive(Clone, Copy, Debug)]
pub(crate) struct AppFds {
    pub rpc: RawFd,
    pub image: RawFd,
    pub persistent_var: RawFd,
    pub seccomp: RawFd,
    pub output: RawFd,
    pub public_data: Option<RawFd>,
}

#[derive(Debug)]
pub(crate) struct SpawnSpec {
    pub program: PathBuf,
    pub sha256: String,
    /// bubblewrap's argv after the program. bubblewrap itself runs with an empty
    /// environment; the app's environment travels as `--setenv` arguments.
    pub args: Vec<String>,
    pub app_uid: u32,
    pub app_gid: u32,
    pub fds: Option<AppFds>,
}

fn validate(spec: &SpawnSpec, test_mode: bool) -> io::Result<()> {
    if !spec.program.is_absolute()
        || spec.app_uid == 0
        || spec.app_gid == 0
        // Some hosts confine user namespaces by an executable-specific
        // AppArmor attachment. Both names remain subject to the same
        // protected inode, configured SHA, native admission and fd gates.
        || (!test_mode
            && !matches!(
                spec.program.file_name().and_then(OsStr::to_str),
                Some("bwrap" | "mini-grain-bwrap")
            ))
        || !crate::canonical::hex64(&spec.sha256)
        || spec.args.len() > MAX_BWRAP_ARGS
    {
        return Err(invalid("invalid pinned app launch shape"));
    }
    // Bounds derived from the one launch-command profile in `sandbox`.
    let bytes: usize = spec.args.iter().map(String::len).sum();
    if bytes > MAX_BWRAP_ARG_BYTES || spec.args.iter().any(|v| v.as_bytes().contains(&0)) {
        return Err(invalid("invalid or oversized bubblewrap arguments"));
    }
    if let Some(fds) = spec.fds {
        let mut sources = vec![fds.rpc, fds.image, fds.persistent_var, fds.seccomp, fds.output];
        sources.extend(fds.public_data);
        if crate::sandbox::has_public_data_args(&spec.args) != fds.public_data.is_some() {
            return Err(invalid("public data mount and descriptor differ"));
        }
        let distinct = sources
            .iter()
            .enumerate()
            .all(|(i, a)| sources[i + 1..].iter().all(|b| a != b));
        if !distinct
            || sources
                .iter()
                .any(|fd| *fd < 10 || unsafe { libc::fcntl(*fd, libc::F_GETFD) } < 0)
        {
            return Err(invalid("invalid fd1/2/3/4/5/6 source mapping"));
        }
    } else if !test_mode {
        return Err(invalid("SPK launch requires fd1-6"));
    }
    if spec.fds.is_none() && crate::sandbox::has_ifaddrs_shim_args(&spec.args) {
        return Err(invalid("platform shim mount without descriptors"));
    }
    Ok(())
}

/// The gate clears supplementary groups before execveat. Check the execute
/// class of that exact UID/GID, rather than accepting any inode execute bit.
/// The kernel still checks ACLs and LSM policy at the final exec boundary.
pub(crate) fn execute_mode_permits(owner: u32, group: u32, mode: u32, uid: u32, gid: u32) -> bool {
    let bit = if owner == uid { 0o100 } else if group == gid { 0o010 } else { 0o001 };
    mode & bit != 0
}

/// The execute decision of the kernel's discretionary check for exactly
/// `uid`/`gid` with no supplementary groups, from the file's POSIX access ACL
/// (`system.posix_acl_access`, the kernel's own v2 encoding) when it has one:
/// owner entry; else a named-user entry under the mask; else the owning-group
/// or a named-group entry for `gid` under the mask (a matching group class that
/// grants nothing denies); else other. Without an ACL it is the mode bits.
/// LSM policy is still decided only at the exec boundary.
pub(crate) fn acl_execute_permits(acl: Option<&[u8]>, owner: u32, group: u32, mode: u32, uid: u32, gid: u32) -> Option<bool> {
    let Some(acl) = acl else { return Some(execute_mode_permits(owner, group, mode, uid, gid)); };
    if owner == uid {
        return Some(mode & 0o100 != 0);
    }
    if acl.len() < 4 || (acl.len() - 4) % 8 != 0 || u32::from_le_bytes(acl[..4].try_into().ok()?) != 2 {
        return None;
    }
    let entries: Vec<(u16, u16, u32)> = acl[4..]
        .chunks_exact(8)
        .map(|e| (u16::from_le_bytes([e[0], e[1]]), u16::from_le_bytes([e[2], e[3]]), u32::from_le_bytes([e[4], e[5], e[6], e[7]])))
        .collect();
    const USER: u16 = 0x02; const GROUP_OBJ: u16 = 0x04; const GROUP: u16 = 0x08; const MASK: u16 = 0x10; const OTHER: u16 = 0x20;
    let mask = entries.iter().find(|e| e.0 == MASK).map_or(7, |e| e.1);
    if let Some(e) = entries.iter().find(|e| e.0 == USER && e.2 == uid) {
        return Some(e.1 & mask & 1 != 0);
    }
    let groups: Vec<u16> = entries
        .iter()
        .filter(|e| (e.0 == GROUP_OBJ && group == gid) || (e.0 == GROUP && e.2 == gid))
        .map(|e| e.1)
        .collect();
    if !groups.is_empty() {
        return Some(groups.iter().any(|p| p & mask & 1 != 0));
    }
    entries.iter().find(|e| e.0 == OTHER).map(|e| e.1 & 1 != 0)
}

fn access_acl(file: &File) -> io::Result<Option<Vec<u8>>> {
    let name = c"system.posix_acl_access";
    let mut buffer = vec![0_u8; MAX_ACCESS_ACL_BYTES];
    let n = unsafe { libc::fgetxattr(file.as_raw_fd(), name.as_ptr(), buffer.as_mut_ptr().cast(), buffer.len()) };
    if n < 0 {
        let e = io::Error::last_os_error();
        return match e.raw_os_error() {
            Some(libc::ENODATA) | Some(libc::EOPNOTSUPP) => Ok(None),
            Some(libc::ERANGE) => Err(invalid("launch executable access ACL exceeds 64 KiB bound")),
            _ => Err(e),
        };
    }
    buffer.truncate(n as usize);
    Ok(Some(buffer))
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
    if !meta.is_file() {
        return Err(invalid("launch executable is not a regular file"));
    }
    if meta.uid() == spec.app_uid {
        return Err(invalid("launch executable is owned by the app identity"));
    }
    if meta.mode() & 0o022 != 0 {
        return Err(invalid("launch executable is group- or other-writable"));
    }
    if meta.len() > MAX_ELF_BYTES {
        return Err(invalid("launch executable is oversized"));
    }
    match acl_execute_permits(access_acl(&file)?.as_deref(), meta.uid(), meta.gid(), meta.mode(), spec.app_uid, spec.app_gid) {
        Some(true) => {}
        Some(false) => return Err(invalid("launch executable is not executable by the app identity after identity drop (mode/ACL)")),
        None => return Err(invalid("launch executable access ACL is malformed")),
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

/// A sealed memfd holding the platform shim, for bubblewrap's `--ro-bind-data` on fd 8. The bytes are
/// the spk-host binary's own (`sandbox::IFADDRS_SHIM`); nothing is read from the host filesystem.
fn shim_memfd() -> io::Result<OwnedFd> {
    let raw = unsafe { libc::memfd_create(c"mini-ifaddrs-shim".as_ptr(), libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING) };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    let fd = unsafe { OwnedFd::from_raw_fd(raw) };
    let bytes = crate::sandbox::IFADDRS_SHIM;
    let mut written = 0;
    while written < bytes.len() {
        let n = unsafe { libc::write(fd.as_raw_fd(), bytes[written..].as_ptr().cast(), bytes.len() - written) };
        if n < 0 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
        written += n as usize;
    }
    let seals = libc::F_SEAL_SEAL | libc::F_SEAL_SHRINK | libc::F_SEAL_GROW | libc::F_SEAL_WRITE;
    if bytes.is_empty()
        || unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_ADD_SEALS, seals) } != 0
        || unsafe { libc::lseek(fd.as_raw_fd(), 0, libc::SEEK_SET) } != 0
    {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "platform shim is empty or cannot be sealed"));
    }
    duplicate_high(fd.as_raw_fd())
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
    /// Source of fd 8 when the arguments carry the platform shim mount.
    shim: Option<RawFd>,
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
        shim,
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
    // stdout/stderr never pass through from the launcher: the app's private
    // output pipe in production, /dev/null for the harmless test ELF.
    let output = spec.fds.map_or(dev_null, |fds| fds.output);
    if let Some(fds) = spec.fds {
        for (source, target) in [
            (fds.rpc, RPC_FD),
            (fds.image, IMAGE_FD),
            (fds.persistent_var, VAR_FD),
            (fds.seccomp, SECCOMP_FD),
        ] {
            if libc::dup2(source, target) != target {
                fail(write_fd);
            }
        }
        if let Some(source) = fds.public_data {
            if libc::dup2(source, PUBLIC_DATA_FD) != PUBLIC_DATA_FD || libc::fcntl(PUBLIC_DATA_FD, libc::F_SETFD, 0) != 0 {
                fail(write_fd);
            }
        }
        if let Some(source) = shim {
            if libc::dup2(source, SHIM_FD) != SHIM_FD || libc::fcntl(SHIM_FD, libc::F_SETFD, 0) != 0 {
                fail(write_fd);
            }
        }
        for target in [RPC_FD, IMAGE_FD, VAR_FD, SECCOMP_FD] {
            if libc::fcntl(target, libc::F_SETFD, 0) != 0 {
                fail(write_fd);
            }
        }
    }
    if libc::dup2(dev_null, 0) != 0 || libc::dup2(output, 1) != 1 || libc::dup2(output, 2) != 2 {
        fail(write_fd);
    }
    if !close_unlisted(keep) {
        fail(write_fd);
    }
    if libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0 {
        fail(write_fd);
    }
    // The app's descriptor bound (Sandstorm's supervisor sets one; the unit's
    // inherited limit is the resident's, not the app's). Hard and soft, so the
    // app cannot raise it.
    let mut files = libc::rlimit {
        rlim_cur: 0,
        rlim_max: 0,
    };
    if libc::getrlimit(libc::RLIMIT_NOFILE, &mut files) != 0 {
        fail(write_fd);
    }
    // Never above the inherited hard limit: only lowering needs no privilege.
    let bound = files.rlim_max.min(APP_MAX_FILES);
    files.rlim_cur = bound;
    files.rlim_max = bound;
    if libc::setrlimit(libc::RLIMIT_NOFILE, &files) != 0 {
        fail(write_fd);
    }
    if !crate::os::child_assume_app_identity(spec.app_uid, spec.app_gid) {
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

#[cfg(test)]
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
    remote: Option<crate::resident_privilege::Client>,
}

impl BoundedChild {
    pub(crate) fn remote(pid: libc::pid_t, client: crate::resident_privilege::Client) -> Self {
        Self {pid, reaped:false, remote:Some(client)}
    }
    pub(crate) fn try_wait(&mut self) -> io::Result<Option<i32>> {
        if self.reaped || self.remote.is_some() { return Err(invalid("direct child already reaped or remote")); }
        let mut status=0;
        let result=unsafe {libc::waitpid(self.pid, &mut status, libc::WNOHANG)};
        if result==self.pid {self.reaped=true; Ok(Some(status))}
        else if result==0 {Ok(None)} else {Err(io::Error::last_os_error())}
    }
    pub fn pid(&self) -> u32 {
        self.pid as u32
    }
    /// The app's published tree, through the remote launch worker (the only
    /// process with the app's identity outside the sandbox).
    pub(crate) fn open_www_file(&mut self, components: &[String]) -> io::Result<crate::resident_privilege::WwwFile> {
        match &mut self.remote {
            Some(client) if !self.reaped => client.open_www_file(self.pid as u32, components),
            _ => Err(invalid("published tree needs the live remote launch worker")),
        }
    }
    pub fn kill_and_reap(&mut self) -> bool {
        if !self.reaped {
            self.reaped = if let Some(client)=&mut self.remote {client.kill_and_reap(self.pid as u32).unwrap_or(false)} else {kill_reap(self.pid)};
        }
        self.reaped
    }
    #[cfg(test)]
    pub fn wait(&mut self) -> io::Result<i32> {
        if !self.reaped {
            let status = if let Some(client)=&mut self.remote {client.wait(self.pid as u32)?} else {wait_reap(self.pid)?};
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
    let dev_null = File::open("/dev/null").ctx("open", &"/dev/null")?;
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
    let mut argv: Vec<*const libc::c_char> = argv_strings.iter().map(|arg| arg.as_ptr()).collect();
    argv.push(std::ptr::null());
    let environ: [*const libc::c_char; 1] = [std::ptr::null()];
    let shim = if spec.fds.is_some() && crate::sandbox::has_ifaddrs_shim_args(&spec.args) { Some(shim_memfd()?) } else { None };
    let mut keep = vec![executable.as_raw_fd() as u32, write_fd.as_raw_fd() as u32];
    if spec.fds.is_some() {
        keep.extend([RPC_FD, IMAGE_FD, VAR_FD, SECCOMP_FD].map(|fd| fd as u32));
    }
    if spec.fds.is_some_and(|fds| fds.public_data.is_some()) {
        keep.push(PUBLIC_DATA_FD as u32);
    }
    if shim.is_some() {
        keep.push(SHIM_FD as u32);
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
                shim: shim.as_ref().map(AsRawFd::as_raw_fd),
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
                return Ok(BoundedChild { pid, reaped: false, remote:None });
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

pub(crate) fn spawn_as_self(spec: &SpawnSpec) -> io::Result<BoundedChild> {
    crate::resident_privilege::require_app_identity(spec.app_uid,spec.app_gid)?;
    spawn_inner(spec,false)
}

#[cfg(test)]
pub(crate) fn spawn_privilege_audit(spec: &SpawnSpec) -> io::Result<BoundedChild> {
    crate::resident_privilege::require_app_identity(spec.app_uid,spec.app_gid)?;
    spawn_inner(spec,true)
}

pub(crate) fn spawn_bounded(spec: &SpawnSpec) -> io::Result<BoundedChild> {
    if let Some(child)=crate::resident_privilege::launch(spec)? {return Ok(child)}
    Err(invalid("production SPK gate requires trusted bootstrap channel"))
}

#[cfg(test)]
mod tests {
    #[test]
    fn public_data_fd_must_match_fixed_mount_arguments() {
        let opened: Vec<_> = (0..6).map(|_| {
            let file = std::fs::File::open("/dev/null").unwrap();
            crate::sandbox::inherited_fd(file.as_raw_fd()).unwrap()
        }).collect();
        let sandbox = crate::sandbox::SandboxSpec {
            bwrap: "/usr/bin/bwrap".into(), image_root: "/image".into(), persistent_var: "/var-test".into(),
            persistent_var_max_bytes: 1024, argv: vec!["/app".into()], environ: vec![], app_output: "/private/output".into(),
            ifaddrs_shim: false,
        };
        let mut spec = SpawnSpec {
            program: sandbox.bwrap.clone(), sha256: "0".repeat(64),
            args: crate::sandbox::bwrap_args_with_public_data(&sandbox, true).unwrap(), app_uid: 1001, app_gid: 1001,
            fds: Some(AppFds {rpc:opened[0].as_raw_fd(),image:opened[1].as_raw_fd(),persistent_var:opened[2].as_raw_fd(),
                seccomp:opened[3].as_raw_fd(),output:opened[4].as_raw_fd(),public_data:None}),
        };
        assert!(validate(&spec, false).is_err());
        spec.fds.as_mut().unwrap().public_data = Some(opened[5].as_raw_fd());
        validate(&spec, false).unwrap();
        spec.args = crate::sandbox::bwrap_args(&sandbox).unwrap();
        assert!(validate(&spec, false).is_err());
        spec.fds.as_mut().unwrap().public_data = None;
        validate(&spec, false).unwrap();
    }

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
    fn launch_mode_uses_exact_post_drop_identity_without_operator_groups() {
        // The observed root:hbox 0750 launcher opens as the operator but may
        // not execute as app64010 after setgroups(0) and setresgid/setresuid.
        assert!(!execute_mode_permits(0, 1000, 0o750, 64010, 64010));
        assert!(execute_mode_permits(0, 64010, 0o754, 64010, 64010));
        assert!(!execute_mode_permits(0, 64010, 0o754, 64011, 64011));
        assert!(execute_mode_permits(0, 0, 0o755, 64010, 64010));
        // Unix owner/group classes take precedence over other execute bits.
        assert!(!execute_mode_permits(64010, 0, 0o655, 64010, 64010));
        assert!(!execute_mode_permits(0, 64010, 0o705, 64010, 64010));
    }

    fn acl(entries: &[(u16, u16, u32)]) -> Vec<u8> {
        let mut b = 2_u32.to_le_bytes().to_vec();
        for (tag, perm, id) in entries {
            b.extend(tag.to_le_bytes()); b.extend(perm.to_le_bytes()); b.extend(id.to_le_bytes());
        }
        b
    }

    #[test]
    fn launch_acl_named_app_entry_under_mask_decides_execute() {
        let u = u32::MAX;
        // root:hbox 0750 + user:165536:r-x + mask r-x (hbox's profiled bwrap).
        let a = acl(&[(1, 7, u), (2, 5, 165536), (4, 5, u), (0x10, 5, u), (0x20, 0, u)]);
        assert_eq!(acl_execute_permits(Some(&a), 0, 1000, 0o750, 165536, 165536), Some(true));
        assert_eq!(acl_execute_permits(Some(&a), 0, 1000, 0o750, 165552, 165552), Some(false));
        assert_eq!(acl_execute_permits(None, 0, 1000, 0o750, 165536, 165536), Some(false));
        // The mask limits a named entry; a matching group class that grants nothing denies.
        let m = acl(&[(1, 7, u), (2, 5, 165536), (4, 5, u), (0x10, 4, u), (0x20, 5, u)]);
        assert_eq!(acl_execute_permits(Some(&m), 0, 1000, 0o745, 165536, 165536), Some(false));
        let g = acl(&[(1, 7, u), (4, 5, u), (8, 4, 165536), (0x10, 5, u), (0x20, 1, u)]);
        assert_eq!(acl_execute_permits(Some(&g), 0, 1000, 0o751, 165536, 165536), Some(false));
        assert_eq!(acl_execute_permits(Some(&g), 0, 1000, 0o751, 165552, 165552), Some(true));
        // The owner class is the mode's owner bits, never a named entry.
        assert_eq!(acl_execute_permits(Some(&a), 165536, 1000, 0o650, 165536, 165536), Some(false));
        assert_eq!(acl_execute_permits(Some(&a[..7]), 0, 1000, 0o750, 165536, 165536), None);
    }

    #[test]
    fn launch_acl_reads_more_than_64_entries_from_actual_inode() {
        use std::os::unix::fs::OpenOptionsExt;
        let path = std::env::temp_dir().join(format!("mini-launch-acl-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let file = std::fs::OpenOptions::new().read(true).write(true).create_new(true).mode(0o700).open(&path).unwrap();
        // The inode remains held, while even a failed assertion leaves no path.
        std::fs::remove_file(&path).unwrap();
        let u = u32::MAX;
        let mut entries = vec![(1, 7, u)];
        for uid in 200000..200128 {
            entries.push((2, if uid == 200127 { 4 } else { 5 }, uid));
        }
        entries.extend([(4, 5, u), (0x10, 5, u), (0x20, 0, u)]);
        let expected = acl(&entries);
        assert!(expected.len() > 4 + 8 * 64);
        let rc = unsafe { libc::fsetxattr(file.as_raw_fd(), c"system.posix_acl_access".as_ptr(),
            expected.as_ptr().cast(), expected.len(), 0) };
        assert_eq!(rc, 0, "{}", io::Error::last_os_error());
        let actual = access_acl(&file).unwrap().unwrap();
        assert_eq!(actual, expected);
        let meta = file.metadata().unwrap();
        for (uid, expected) in [(200000, true), (200126, true), (200127, false), (200128, false)] {
            assert_eq!(acl_execute_permits(Some(&actual), meta.uid(), meta.gid(), meta.mode(), uid, uid), Some(expected));
        }
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
    fn production_shape_accepts_scoped_bwrap_name_without_bypassing_fd_gate() {
        let mut spec = SpawnSpec {
            program: "/usr/local/libexec/mini-grain-bwrap".into(),
            sha256: "0".repeat(64),
            args: vec![],
            app_uid: 994,
            app_gid: 994,
            fds: None,
        };
        for path in ["/usr/bin/bwrap", "/usr/local/libexec/mini-grain-bwrap"] {
            spec.program = path.into();
            assert_eq!(
                validate(&spec, false).unwrap_err().to_string(),
                "SPK launch requires fd1-6"
            );
        }
        for path in ["/usr/bin/true", "/tmp/bwrap-other", "mini-grain-bwrap"] {
            spec.program = path.into();
            assert_eq!(
                validate(&spec, false).unwrap_err().to_string(),
                "invalid pinned app launch shape"
            );
        }
        spec.program = "/usr/local/libexec/mini-grain-bwrap".into();
        spec.sha256 = "not-a-pin".into();
        assert!(validate(&spec, false).is_err());
        spec.sha256 = "0".repeat(64);
        spec.app_uid = 0;
        assert!(validate(&spec, false).is_err());
    }

    #[test]
    fn gate_bounds_are_the_profile_derived_ones() {
        let uid = unsafe { libc::geteuid() };
        let spec = |args: Vec<String>| SpawnSpec {
            program: "/usr/bin/bwrap".into(),
            sha256: "0".repeat(64),
            args,
            app_uid: uid.max(1),
            app_gid: 1,
            fds: None,
        };
        let per = MAX_BWRAP_ARG_BYTES / MAX_BWRAP_ARGS;
        let mut args = vec!["a".repeat(per); MAX_BWRAP_ARGS];
        args[0].push_str(&"a".repeat(MAX_BWRAP_ARG_BYTES - per * MAX_BWRAP_ARGS));
        assert!(validate(&spec(args.clone()), true).is_ok());
        let mut longer = args.clone();
        longer.push(String::new());
        assert!(validate(&spec(longer), true).is_err());
        args[1].push('a');
        assert!(validate(&spec(args), true).is_err());
    }

    /// The launched process's stdout and stderr are the gate's choice, never the
    /// launcher's own (under nextest those are capture pipes, not /dev/null).
    #[test]
    fn child_never_inherits_launcher_stdout_or_stderr() {
        let uid = unsafe { libc::geteuid() };
        if uid == 0 {
            return;
        }
        let shell = std::fs::canonicalize("/usr/bin/sh").unwrap();
        let spec = SpawnSpec {
            program: shell.clone(),
            sha256: sha(shell.to_str().unwrap()),
            args: vec![
                "-c".into(),
                // The sleep keeps the child alive past the handshake so the exit
                // status, not the EOF/exit race, carries the verdict.
                "sleep 1; [ /proc/self/fd/1 -ef /dev/null ] && [ /proc/self/fd/2 -ef /dev/null ]"
                    .into(),
            ],
            app_uid: uid,
            app_gid: unsafe { libc::getegid() },
            fds: None,
        };
        let status = spawn_inner(&spec, true).unwrap().wait().unwrap();
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
