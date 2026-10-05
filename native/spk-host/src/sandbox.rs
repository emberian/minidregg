//! Linux namespace launch for an already verified, materialized SPK image.
//!
//! The caller must first obtain Mini's app-lifecycle admission. This module does
//! not decide whether an app may start or whether an RPC request may be delivered.

use std::ffi::CString;
use std::fs::{File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::path::{Component, Path, PathBuf};
use std::process::{Child, Command};
use std::thread::JoinHandle;

/// The one launch-command profile. `launch_descriptor_native` refuses a signed
/// package that exceeds it at qualification, before any BEGIN; the sandbox and
/// the spawn gate apply the same numbers, and the gate's argument bounds are
/// derived from them below, so an admitted command always fits the gate.
pub(crate) const MAX_ARGV: usize = 64;
pub(crate) const MAX_ARG_BYTES: usize = 4096;
pub(crate) const MAX_ENV: usize = 128;
pub(crate) const MAX_ENV_KEY_BYTES: usize = 256;
pub(crate) const MAX_ENV_VALUE_BYTES: usize = 4096;
/// Sum of argv bytes plus `key` + `=` + `value` per environment entry.
pub(crate) const MAX_COMMAND_BYTES: usize = 128 * 1024;

/// Fixed descriptor numbers inside bubblewrap: fd3 is the Cap'n Proto socket the
/// app keeps; bubblewrap consumes and closes 4 (image), 5 (/var) and 6 (seccomp)
/// before exec (bubblewrap 0.11.0 bubblewrap.c:1256-1277, 260-272).
pub(crate) const RPC_FD: RawFd = 3;
pub(crate) const IMAGE_FD: RawFd = 4;
pub(crate) const VAR_FD: RawFd = 5;
pub(crate) const SECCOMP_FD: RawFd = 6;

/// Every token before the package's environment, in order. `--disable-userns`
/// follows `--unshare-user` (it requires it); `--seccomp 6` is the compiled
/// `seccomp/resident-web.policy`.
const FIXED_ARGS: [&str; 39] = [
    "--die-with-parent", "--new-session",
    "--unshare-user", "--disable-userns", "--unshare-pid", "--unshare-ipc", "--unshare-uts",
    "--unshare-cgroup", "--unshare-net",
    "--cap-drop", "ALL",
    "--seccomp", "6",
    "--clearenv", "--ro-bind-fd", "4", "/", "--bind-fd", "5", "/var",
    // /tmp is a 128 MiB tmpfs.
    "--size", "134217728", "--tmpfs", "/tmp", "--proc", "/proc",
    "--dev", "/dev", "--chdir", "/", "--setenv", "HOME", "/var",
    "--setenv", "TMPDIR", "/tmp", "--setenv", "PATH", "/usr/bin:/bin",
];

const fn fixed_bytes() -> usize {
    let mut total = 0;
    let mut i = 0;
    while i < FIXED_ARGS.len() {
        total += FIXED_ARGS[i].len();
        i += 1;
    }
    total
}

/// Largest bubblewrap argument vector an admitted command can produce.
pub(crate) const MAX_BWRAP_ARGS: usize = FIXED_ARGS.len() + 3 * MAX_ENV + 1 + MAX_ARGV;
/// Largest total argument bytes an admitted command can produce.
pub(crate) const MAX_BWRAP_ARG_BYTES: usize =
    fixed_bytes() + MAX_ENV * "--setenv".len() + "--".len() + MAX_COMMAND_BYTES;

/// Per-generation cap on retained app stdout/stderr. Bytes past the cap are read
/// and dropped (so the app never blocks on a full pipe) and counted in a trailer.
pub const APP_OUTPUT_MAX_BYTES: u64 = 16 * 1024 * 1024;

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
    /// New, host-private file receiving the app's stdout and stderr. The app never
    /// inherits the launcher's own stdout/stderr.
    pub app_output: PathBuf,
}

/// The connected host-side RPC stream and the contained process. This module
/// creates no cgroup: `--unshare-cgroup` only namespaces the app's view. Memory,
/// task and CPU bounds are those of the systemd unit that runs the launcher; the
/// resident journal records that unit's control group (hostd `Entered`).
pub struct SandboxedChild {
    pub process: Child,
    pub rpc: UnixStream,
    pub output: AppOutput,
}

/// Totals of one app generation's stdout/stderr capture.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AppOutputSummary {
    pub kept: u64,
    pub discarded: u64,
}

/// Host-side pump from the app's stdout/stderr pipe into its private log file.
pub struct AppOutput {
    pump: JoinHandle<io::Result<AppOutputSummary>>,
}

impl AppOutput {
    /// Waits for every app-side writer to close (the app and its descendants exit),
    /// then returns what was kept and dropped.
    pub fn finish(self) -> io::Result<AppOutputSummary> {
        self.pump
            .join()
            .map_err(|_| io::Error::other("app output pump panicked"))?
    }
}

/// Create `path` (absolute, new, mode 0600, never through a symlink) and a pipe
/// whose write end becomes the app's fd1 and fd2. The returned write end is
/// close-on-exec; the launcher must drop its copy after spawning.
pub(crate) fn app_output(path: &Path) -> io::Result<(OwnedFd, AppOutput)> {
    if !path.is_absolute() {
        return Err(invalid("app output path must be absolute"));
    }
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)?;
    let mut pipe = [0_i32; 2];
    if unsafe { libc::pipe2(pipe.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let mut reader = unsafe { File::from_raw_fd(pipe[0]) };
    let writer = unsafe { OwnedFd::from_raw_fd(pipe[1]) };
    let pump = std::thread::Builder::new()
        .name("spk-app-output".into())
        .spawn(move || {
            let mut summary = AppOutputSummary { kept: 0, discarded: 0 };
            let mut buffer = [0_u8; 64 * 1024];
            loop {
                let n = match reader.read(&mut buffer) {
                    Ok(0) => break,
                    Ok(n) => n,
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                    Err(error) => return Err(error),
                };
                let room = APP_OUTPUT_MAX_BYTES.saturating_sub(summary.kept);
                let keep = (n as u64).min(room) as usize;
                file.write_all(&buffer[..keep])?;
                summary.kept += keep as u64;
                summary.discarded += (n - keep) as u64;
            }
            if summary.discarded > 0 {
                writeln!(
                    file,
                    "\n[spk-host: {} further bytes of app output discarded at the {} byte cap]",
                    summary.discarded, APP_OUTPUT_MAX_BYTES
                )?;
            }
            file.sync_all()?;
            Ok(summary)
        })?;
    Ok((writer, AppOutput { pump }))
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
            if !crate::os::app_owner(stat.st_uid, app_uid) || stat.st_mode & 0o777 != 0o700 {
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

pub(crate) fn directory_entry(root: RawFd, name: &str) -> io::Result<()> {
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

pub(crate) fn verify_var_volume(path: &Path, var_fd: RawFd, max_bytes: u64, app_uid: u32) -> io::Result<()> {
    if max_bytes == 0 || max_bytes > 16 * 1024 * 1024 * 1024 {
        return Err(invalid("persistent /var size outside configured cap"));
    }
    let parent = path.parent().ok_or_else(|| invalid("persistent /var has no parent"))?;
    let parent_fd = open_protected_directory(parent, app_uid, false)?;
    let (separate, total) = crate::os::var_filesystem(path, parent_fd.as_raw_fd(), var_fd)?;
    if !separate {
        return Err(invalid("persistent /var is not a separate mounted filesystem"));
    }
    if total == 0 || total > max_bytes as u128 {
        return Err(invalid("persistent /var filesystem exceeds configured cap"));
    }
    Ok(())
}

pub(crate) fn verify_executable(path: &Path, app_uid: u32) -> io::Result<()> {
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

pub(crate) fn inherited_fd(fd: RawFd) -> io::Result<OwnedFd> {
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

/// The launch-command profile, applied at qualification, at sandbox preparation
/// and (through the derived bounds) at the spawn gate.
pub(crate) fn validate_command(argv: &[String], environ: &[(String, String)]) -> io::Result<()> {
    let Some(program) = argv.first() else { return Err(invalid("empty SPK command")); };
    if !program.starts_with('/') {
        return Err(invalid("SPK command must use an absolute executable path"));
    }
    if argv.len() > MAX_ARGV || environ.len() > MAX_ENV {
        return Err(invalid("SPK command has too many arguments or environment entries"));
    }
    for arg in argv {
        if arg.len() > MAX_ARG_BYTES || arg.as_bytes().contains(&0) {
            return Err(invalid("SPK argv entry is oversized or contains NUL"));
        }
    }
    for (key, value) in environ {
        if key.len() > MAX_ENV_KEY_BYTES
            || !valid_env_key(key)
            || value.len() > MAX_ENV_VALUE_BYTES
            || value.as_bytes().contains(&0)
        {
            return Err(invalid("invalid SPK environment entry"));
        }
    }
    let bytes = argv.iter().map(String::len).sum::<usize>()
        + environ.iter().map(|(key, value)| key.len() + 1 + value.len()).sum::<usize>();
    if bytes > MAX_COMMAND_BYTES {
        return Err(invalid("SPK command exceeds the total byte bound"));
    }
    Ok(())
}

/// One exact argument sequence for both the private compatibility smoke and
/// the operator resident gate. The package's ordered environment is retained.
pub(crate) fn bwrap_args(spec: &SandboxSpec) -> io::Result<Vec<String>> {
    validate_command(&spec.argv, &spec.environ)?;
    let mut args: Vec<String> = FIXED_ARGS
        .iter()
        .map(|token| (*token).to_owned())
        .collect();
    for (key, value) in &spec.environ {
        args.push("--setenv".into());
        args.push(key.clone());
        args.push(value.clone());
    }
    args.push("--".into());
    args.extend(spec.argv.iter().cloned());
    Ok(args)
}

/// Spawn a package's real command in a package-rooted namespace. The child end of
/// a private Unix socketpair becomes fd 3 in the packaged bridge. The returned
/// host end must be passed to `spk-rpc`; it is never mounted as a pathname.
pub fn spawn_sandbox(spec: &SandboxSpec) -> io::Result<SandboxedChild> {
    let args = bwrap_args(spec)?;
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
    let seccomp = inherited_fd(crate::seccomp::resident_filter_fd()?.as_raw_fd())?;
    let (output_writer, output) = app_output(&spec.app_output)?;
    let output_writer = inherited_fd(output_writer.as_raw_fd())?;

    let mut command = Command::new(&spec.bwrap);
    command.env_clear();
    command.args(args);
    command.stdin(std::process::Stdio::null());
    unsafe {
        command.pre_exec(move || {
            for (source, target) in [
                (child_rpc.as_raw_fd(), RPC_FD),
                (image.as_raw_fd(), IMAGE_FD),
                (persistent_var.as_raw_fd(), VAR_FD),
                (seccomp.as_raw_fd(), SECCOMP_FD),
                (output_writer.as_raw_fd(), 1),
                (output_writer.as_raw_fd(), 2),
            ] {
                if libc::dup2(source, target) != target {
                    return Err(io::Error::last_os_error());
                }
            }
            Ok(())
        });
    }
    // The closure (and with it every inherited source fd) is dropped with
    // `command` at return, so the app's EOF on stdout/stderr ends the pump.
    let process = command.spawn()?;
    Ok(SandboxedChild { process, rpc: host_rpc, output })
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

    fn spec(argv: Vec<String>, environ: Vec<(String, String)>) -> SandboxSpec {
        SandboxSpec {
            bwrap: "/usr/bin/bwrap".into(),
            image_root: "/image".into(),
            persistent_var: "/volume".into(),
            persistent_var_max_bytes: 1024,
            argv,
            environ,
            app_output: "/journal/app-output.log".into(),
        }
    }

    /// The whole argument list, token for token. A change to the sandbox floor
    /// must change this test.
    #[test]
    fn bwrap_args_are_token_exact() {
        let args = bwrap_args(&spec(
            vec!["/bin/sh".into(), "continue.sh".into()],
            vec![("A".into(), "first".into()), ("A".into(), "last".into())],
        ))
        .unwrap();
        let expected = [
            "--die-with-parent", "--new-session",
            "--unshare-user", "--disable-userns", "--unshare-pid", "--unshare-ipc",
            "--unshare-uts", "--unshare-cgroup", "--unshare-net",
            "--cap-drop", "ALL",
            "--seccomp", "6",
            "--clearenv", "--ro-bind-fd", "4", "/", "--bind-fd", "5", "/var",
            "--size", "134217728", "--tmpfs", "/tmp", "--proc", "/proc",
            "--dev", "/dev", "--chdir", "/", "--setenv", "HOME", "/var",
            "--setenv", "TMPDIR", "/tmp", "--setenv", "PATH", "/usr/bin:/bin",
            "--setenv", "A", "first", "--setenv", "A", "last",
            "--", "/bin/sh", "continue.sh",
        ];
        assert_eq!(args, expected);
        assert_eq!((128_u64 * 1024 * 1024).to_string(), "134217728");
        assert_eq!(
            [RPC_FD, IMAGE_FD, VAR_FD, SECCOMP_FD].map(|fd| fd.to_string()),
            ["3", "4", "5", "6"]
        );
    }

    #[test]
    fn floor_flags_are_present_and_ordered() {
        let args = bwrap_args(&spec(vec!["/start".into()], vec![])).unwrap();
        let at = |token: &str| args.iter().position(|a| a == token).unwrap();
        assert!(at("--unshare-user") < at("--disable-userns"));
        assert_eq!(args[at("--cap-drop") + 1], "ALL");
        assert_eq!(args[at("--seccomp") + 1], SECCOMP_FD.to_string());
        assert!(at("--seccomp") < at("--"));
    }

    fn maximal_command() -> (Vec<String>, Vec<(String, String)>) {
        let mut budget = MAX_COMMAND_BYTES;
        let environ: Vec<(String, String)> = (0..MAX_ENV)
            .map(|i| {
                let key = format!("K{i:03}");
                let value = "v".repeat(256);
                budget -= key.len() + 1 + value.len();
                (key, value)
            })
            .collect();
        let mut argv = vec!["/start".to_owned()];
        budget -= argv[0].len();
        while argv.len() < MAX_ARGV {
            let take = budget.div_ceil(MAX_ARGV - argv.len()).min(MAX_ARG_BYTES);
            argv.push("a".repeat(take));
            budget -= take;
        }
        assert_eq!(budget, 0, "the maximal command sits exactly on the byte bound");
        (argv, environ)
    }

    /// One set of numbers: the largest command the profile admits produces a
    /// bubblewrap vector inside the gate's derived bounds, and one past any
    /// profile bound is refused before a gate is reached.
    #[test]
    fn profile_admits_exactly_what_the_gate_accepts() {
        let (argv, environ) = maximal_command();
        validate_command(&argv, &environ).unwrap();
        let args = bwrap_args(&spec(argv.clone(), environ.clone())).unwrap();
        assert!(args.len() <= MAX_BWRAP_ARGS);
        assert!(args.iter().map(String::len).sum::<usize>() <= MAX_BWRAP_ARG_BYTES);

        let mut long = argv.clone();
        long.push("x".into());
        assert!(validate_command(&long, &environ).is_err());
        let mut wide = environ.clone();
        wide.push(("EXTRA".into(), "1".into()));
        assert!(validate_command(&argv, &wide).is_err());
        let mut heavy = argv.clone();
        heavy[1].push_str(&"b".repeat(MAX_ARG_BYTES));
        assert!(validate_command(&heavy, &environ).is_err());
        let mut total = argv;
        total[1] = "c".repeat(MAX_ARG_BYTES);
        assert!(validate_command(&total, &environ).is_err());
        assert!(validate_command(&["/s".into()], &[("K".repeat(MAX_ENV_KEY_BYTES + 1), "".into())]).is_err());
        assert!(validate_command(&["/s".into()], &[("K".into(), "v".repeat(MAX_ENV_VALUE_BYTES + 1))]).is_err());
    }

    #[test]
    fn app_output_is_new_private_and_capped() {
        let dir = std::env::temp_dir().join(format!("spk-app-output-{}", std::process::id()));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("app.log");
        let (writer, output) = app_output(&path).unwrap();
        assert!(app_output(&path).is_err(), "an existing log is never reused");
        let mut writer = File::from(writer);
        let chunk = vec![b'x'; 1024 * 1024];
        for _ in 0..17 {
            writer.write_all(&chunk).unwrap();
        }
        drop(writer);
        let summary = output.finish().unwrap();
        assert_eq!(summary, AppOutputSummary { kept: APP_OUTPUT_MAX_BYTES, discarded: 1024 * 1024 });
        let meta = std::fs::metadata(&path).unwrap();
        assert_eq!(std::os::unix::fs::PermissionsExt::mode(&meta.permissions()) & 0o777, 0o600);
        assert!(meta.len() > APP_OUTPUT_MAX_BYTES && meta.len() < APP_OUTPUT_MAX_BYTES + 256);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn denies_symlinked_or_world_writable_ancestor() {
        assert!(open_protected_directory(Path::new("/tmp"), unsafe { libc::geteuid() }, false).is_err());
        assert!(open_protected_directory(Path::new("/tmp/../etc"), unsafe { libc::geteuid() }, false).is_err());
    }
}
