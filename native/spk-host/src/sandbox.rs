//! Linux namespace launch for an already verified, materialized SPK image.
//!
//! The caller must first obtain Mini's app-lifecycle admission. This module does
//! not decide whether an app may start or whether an RPC request may be delivered.

use std::ffi::{CString, OsStr};
use std::io;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::path::{Component, Path, PathBuf};
use std::process::{Child, Command};

const TMP_BYTES: u64 = 128 * 1024 * 1024;

/// Exact physical input to a launch. `argv` and `environ` must come from the
/// verified package manifest (create action or continue command, respectively).
#[derive(Clone, Debug)]
pub struct SandboxSpec {
    pub bwrap: PathBuf,
    pub image_root: PathBuf,
    pub persistent_var: PathBuf,
    /// Hard upper size of the separately mounted persistent filesystem.
    pub persistent_var_max_bytes: u64,
    pub argv: Vec<String>,
    pub environ: Vec<(String, String)>,
}

/// The connected host-side RPC stream and the contained process. The app process,
/// packaged bridge, and any local database children all remain in this child cgroup.
pub struct SandboxedChild {
    pub process: Child,
    pub rpc: UnixStream,
}

/// Open each directory component without following a symlink. Every ancestor is
/// required to be outside the app UID's ownership and non-writable by its group
/// or other; a task cannot then replace a supposedly immutable path by rename.
pub(crate) fn open_protected_directory(path: &Path, app_uid: u32, leaf_owned_by_app: bool) -> io::Result<OwnedFd> {
    if !path.is_absolute() {
        return Err(invalid("path must be absolute"));
    }
    let parts: Vec<_> = path.components().collect();
    if parts.len() < 2 || !matches!(parts.first(), Some(Component::RootDir)) {
        return Err(invalid("path must name a directory below /"));
    }
    let root = CString::new("/").expect("constant");
    let fd = unsafe { libc::open(root.as_ptr(), libc::O_PATH | libc::O_DIRECTORY | libc::O_CLOEXEC) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    let mut current = unsafe { OwnedFd::from_raw_fd(fd) };
    for (index, part) in parts.iter().enumerate().skip(1) {
        let Component::Normal(name) = part else {
            return Err(invalid("path contains . or .."));
        };
        let name = CString::new(name.as_bytes()).map_err(|_| invalid("NUL in path"))?;
        let fd = unsafe {
            libc::openat(
                current.as_raw_fd(),
                name.as_ptr(),
                libc::O_PATH | libc::O_NOFOLLOW | libc::O_DIRECTORY | libc::O_CLOEXEC,
            )
        };
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }
        current = unsafe { OwnedFd::from_raw_fd(fd) };
        let mut stat = unsafe { std::mem::zeroed::<libc::stat>() };
        if unsafe { libc::fstat(current.as_raw_fd(), &mut stat) } != 0 {
            return Err(io::Error::last_os_error());
        }
        let leaf = index == parts.len() - 1;
        if leaf && leaf_owned_by_app {
            if stat.st_uid != app_uid || stat.st_mode & 0o777 != 0o700 {
                return Err(invalid("persistent /var must be task-owned mode 0700"));
            }
        } else if stat.st_uid == app_uid || stat.st_mode & 0o022 != 0 {
            return Err(invalid("image or ancestor is task-owned or group/world writable"));
        }
    }
    Ok(current)
}

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message)
}

fn directory_entry(root: RawFd, name: &str) -> io::Result<()> {
    let name = CString::new(name).expect("constant");
    let fd = unsafe {
        libc::openat(root, name.as_ptr(), libc::O_PATH | libc::O_NOFOLLOW | libc::O_DIRECTORY | libc::O_CLOEXEC)
    };
    if fd < 0 {
        return Err(invalid("SPK mountpoint missing or symlinked"));
    }
    unsafe { libc::close(fd) };
    Ok(())
}

fn stat_fd(fd: RawFd) -> io::Result<libc::stat> {
    let mut stat = unsafe { std::mem::zeroed::<libc::stat>() };
    if unsafe { libc::fstat(fd, &mut stat) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(stat)
}

fn verify_var_volume(path: &Path, var_fd: RawFd, max_bytes: u64, app_uid: u32) -> io::Result<()> {
    if max_bytes == 0 || max_bytes > 16 * 1024 * 1024 * 1024 {
        return Err(invalid("persistent /var size outside configured cap"));
    }
    let parent = path.parent().ok_or_else(|| invalid("persistent /var has no parent"))?;
    let parent_fd = open_protected_directory(parent, app_uid, false)?;
    if stat_fd(parent_fd.as_raw_fd())?.st_dev == stat_fd(var_fd)?.st_dev {
        return Err(invalid("persistent /var is not a separate mounted filesystem"));
    }
    let mut volume = unsafe { std::mem::zeroed::<libc::statvfs>() };
    if unsafe { libc::fstatvfs(var_fd, &mut volume) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let total = (volume.f_blocks as u128) * (volume.f_frsize as u128);
    if total == 0 || total > max_bytes as u128 {
        return Err(invalid("persistent /var filesystem exceeds configured cap"));
    }
    Ok(())
}

fn verify_executable(path: &Path, app_uid: u32) -> io::Result<()> {
    let parent = path.parent().ok_or_else(|| invalid("bubblewrap has no parent"))?;
    let parent_fd = open_protected_directory(parent, app_uid, false)?;
    let name = path.file_name().ok_or_else(|| invalid("bubblewrap has no filename"))?;
    let name = CString::new(name.as_bytes()).map_err(|_| invalid("NUL in bubblewrap path"))?;
    let fd = unsafe {
        libc::openat(parent_fd.as_raw_fd(), name.as_ptr(), libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC)
    };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    let fd = unsafe { OwnedFd::from_raw_fd(fd) };
    let stat = stat_fd(fd.as_raw_fd())?;
    if stat.st_mode & libc::S_IFMT != libc::S_IFREG || stat.st_uid == app_uid
        || stat.st_mode & 0o022 != 0 || stat.st_mode & 0o111 == 0
    {
        return Err(invalid("bubblewrap executable is task-owned, writable, or not executable"));
    }
    Ok(())
}

fn inherited_fd(fd: RawFd) -> io::Result<OwnedFd> {
    let duplicate = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 10) };
    if duplicate < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { OwnedFd::from_raw_fd(duplicate) })
}

fn valid_env_key(key: &str) -> bool {
    let mut bytes = key.bytes();
    matches!(bytes.next(), Some(b'A'..=b'Z' | b'a'..=b'z' | b'_'))
        && bytes.all(|c| c.is_ascii_alphanumeric() || c == b'_')
}

fn validate_command(argv: &[String], environ: &[(String, String)]) -> io::Result<()> {
    let Some(program) = argv.first() else { return Err(invalid("empty SPK command")); };
    if !program.starts_with('/') || program.as_bytes().contains(&0) {
        return Err(invalid("SPK command must use an absolute executable path"));
    }
    for arg in argv {
        if arg.as_bytes().contains(&0) {
            return Err(invalid("NUL in SPK argv"));
        }
    }
    for (key, value) in environ {
        if !valid_env_key(key) || value.as_bytes().contains(&0) {
            return Err(invalid("invalid SPK environment entry"));
        }
    }
    Ok(())
}

/// Spawn a package's real command in a package-rooted namespace. The child end of
/// a private Unix socketpair becomes fd 3 in the packaged bridge. The returned
/// host end must be passed to `spk-rpc`; it is never mounted as a pathname.
pub fn spawn_sandbox(spec: &SandboxSpec) -> io::Result<SandboxedChild> {
    validate_command(&spec.argv, &spec.environ)?;
    let app_uid = unsafe { libc::geteuid() };
    let image = open_protected_directory(&spec.image_root, app_uid, false)?;
    let persistent_var = open_protected_directory(&spec.persistent_var, app_uid, true)?;
    if spec.persistent_var.starts_with(&spec.image_root)
        || spec.image_root.starts_with(&spec.persistent_var)
    {
        return Err(invalid("image and persistent /var overlap"));
    }
    for mountpoint in ["var", "tmp", "proc", "dev"] {
        directory_entry(image.as_raw_fd(), mountpoint)?;
    }
    verify_var_volume(&spec.persistent_var, persistent_var.as_raw_fd(), spec.persistent_var_max_bytes, app_uid)?;
    verify_executable(&spec.bwrap, app_uid)?;

    let (host_rpc, child_rpc) = UnixStream::pair()?;
    let child_rpc = inherited_fd(child_rpc.as_raw_fd())?;
    let image = inherited_fd(image.as_raw_fd())?;
    let persistent_var = inherited_fd(persistent_var.as_raw_fd())?;

    let mut command = Command::new(&spec.bwrap);
    command.env_clear();
    command.args([
        "--die-with-parent", "--new-session", "--unshare-user", "--unshare-pid", "--unshare-ipc",
        "--unshare-uts", "--unshare-cgroup", "--unshare-net", "--clearenv",
        "--ro-bind-fd", "4", "/", "--bind-fd", "5", "/var",
        "--size", &TMP_BYTES.to_string(), "--tmpfs", "/tmp",
        "--proc", "/proc", "--dev", "/dev", "--chdir", "/",
        "--setenv", "HOME", "/var", "--setenv", "TMPDIR", "/tmp",
        "--setenv", "PATH", "/usr/bin:/bin",
    ]);
    // The package declares an ordered environment, including any deliberate
    // override of the three fixed defaults above. Do not sort or coalesce it.
    for (key, value) in &spec.environ {
        command.arg("--setenv").arg(key).arg(value);
    }
    command.arg("--");
    for arg in &spec.argv {
        command.arg(OsStr::new(arg));
    }
    unsafe {
        command.pre_exec(move || {
            for (source, target) in [
                (child_rpc.as_raw_fd(), 3),
                (image.as_raw_fd(), 4),
                (persistent_var.as_raw_fd(), 5),
            ] {
                if libc::dup2(source, target) != target {
                    return Err(io::Error::last_os_error());
                }
            }
            Ok(())
        });
    }
    let process = command.spawn()?;
    Ok(SandboxedChild { process, rpc: host_rpc })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_ambiguous_or_unusable_command() {
        assert!(validate_command(&[], &[]).is_err());
        assert!(validate_command(&["relative".into()], &[]).is_err());
        assert!(validate_command(&["/start".into()], &[("BAD=KEY".into(), "v".into())]).is_err());
        assert!(validate_command(&["/start".into()], &[("OK".into(), "x\0y".into())]).is_err());
        assert!(validate_command(&["/start".into()], &[("A".into(), "1".into()), ("A".into(), "2".into())]).is_ok());
    }

    #[test]
    fn denies_symlinked_or_world_writable_ancestor() {
        assert!(open_protected_directory(Path::new("/tmp"), unsafe { libc::geteuid() }, false).is_err());
        assert!(open_protected_directory(Path::new("/tmp/../etc"), unsafe { libc::geteuid() }, false).is_err());
    }
}
