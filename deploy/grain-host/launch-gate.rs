//! Durable Linux per-operation systemd ExecStart gate for Mini grain workers.
//! `run` is the unit MainPID: exec for legacy same-manager gates, or a pidfd
//! supervisor for controller-incarnation-bound gates.
use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

const O_NOFOLLOW: i32 = 0o400000;
const LOCK_EX: i32 = 2;
const LOCK_UN: i32 = 8;
unsafe extern "C" {
    fn flock(fd: i32, operation: i32) -> i32;
    fn geteuid() -> u32;
}

fn lock(file: &File, operation: i32) -> Result<(), String> {
    if unsafe { flock(file.as_raw_fd(), operation) } == 0 {
        Ok(())
    } else {
        Err(format!("flock: {}", std::io::Error::last_os_error()))
    }
}

fn private_dir(path: &Path) -> Result<(), String> {
    if !path.is_absolute() {
        return Err("state dir must be absolute".into());
    }
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.file_type().is_dir()
        || meta.uid() != unsafe { geteuid() }
        || meta.permissions().mode() & 0o077 != 0
    {
        return Err("state dir must be an owned, real, private directory".into());
    }
    Ok(())
}

fn gate_path(dir: &Path, unit: &str) -> Result<PathBuf, String> {
    let Some(rest) = unit.strip_prefix("mini-grain-t") else {
        return Err("bad unit".into());
    };
    let Some((task, operation)) = rest.split_once("-o") else {
        return Err("bad unit".into());
    };
    if task.is_empty()
        || operation.is_empty()
        || !task.bytes().all(|b| b.is_ascii_digit())
        || !operation.bytes().all(|b| b.is_ascii_digit())
    {
        return Err("bad unit".into());
    }
    Ok(dir.join(format!("{unit}.gate")))
}

fn open_gate(path: &Path, create: bool) -> Result<File, String> {
    let mut options = OpenOptions::new();
    options
        .read(true)
        .write(true)
        .custom_flags(O_NOFOLLOW)
        .mode(0o600);
    if create {
        options.create(true);
    }
    let file = options.open(path).map_err(|e| format!("gate open: {e}"))?;
    let meta = file.metadata().map_err(|e| e.to_string())?;
    if !meta.file_type().is_file()
        || meta.uid() != unsafe { geteuid() }
        || meta.permissions().mode() & 0o077 != 0
    {
        return Err("gate must be an owned private regular file".into());
    }
    Ok(file)
}

fn read_state(file: &mut File) -> Result<String, String> {
    file.seek(SeekFrom::Start(0)).map_err(|e| e.to_string())?;
    let mut state = String::new();
    file.take(1024)
        .read_to_string(&mut state)
        .map_err(|e| e.to_string())?;
    Ok(state)
}

fn write_state(file: &mut File, state: &str) -> Result<(), String> {
    file.set_len(0).map_err(|e| e.to_string())?;
    file.seek(SeekFrom::Start(0)).map_err(|e| e.to_string())?;
    file.write_all(state.as_bytes())
        .and_then(|_| file.sync_all())
        .map_err(|e| e.to_string())
}

// The system and user managers have independent unit namespaces. A pidfd is
// the lifetime capability for exactly one controller incarnation; a restarted
// unit (even with a recycled numeric PID) can never adopt an old operation.
#[derive(Clone, Debug)]
struct Controller {
    manager: String,
    unit: String,
    pid: u32,
    invocation: String,
    start: String,
}
impl Controller {
    fn from_env(unit: &str) -> Result<Option<Self>, String> {
        let manager = env::var("MINI_GRAIN_CONTROLLER_MANAGER").unwrap_or_else(|_| "user".into());
        if manager != "system" && manager != "user" {
            return Err("invalid controller manager".into());
        }
        let pid = match env::var("MINI_GRAIN_CONTROLLER_PID") {
            Ok(pid) => pid.parse::<u32>().map_err(|_| "invalid controller PID")?,
            Err(_) if manager == "user" => return Ok(None),
            Err(_) => return Err("system controller lifetime identity is required".into()),
        };
        if pid <= 1 {
            return Err("invalid controller PID".into());
        }
        let task = unit
            .strip_prefix("mini-grain-t")
            .and_then(|x| x.split_once("-o"))
            .ok_or("invalid worker unit")?
            .0;
        let expected = format!("mini-grain-controller@{task}.service");
        if env::var("MINI_GRAIN_CONTROLLER_UNIT").ok().as_deref() != Some(&expected) {
            return Err("controller unit mismatch".into());
        }
        let invocation = env::var("MINI_GRAIN_CONTROLLER_INVOCATION_ID")
            .map_err(|_| "controller invocation absent")?;
        if invocation.len() != 32
            || !invocation
                .bytes()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            return Err("invalid invocation ID".into());
        }
        let value = Self {
            manager,
            unit: expected,
            pid,
            invocation,
            start: process_start(pid)?,
        };
        value.verify()?;
        Ok(Some(value))
    }
    fn encode(&self) -> String {
        format!(
            "{} {} {} {} {}",
            self.manager, self.unit, self.pid, self.invocation, self.start
        )
    }
    fn decode(text: &str, worker: &str) -> Result<Self, String> {
        let words: Vec<_> = text.split(' ').collect();
        if words.len() != 5 || !matches!(words[0], "system" | "user") {
            return Err("invalid retained controller identity".into());
        }
        let task = worker
            .strip_prefix("mini-grain-t")
            .and_then(|x| x.split_once("-o"))
            .ok_or("invalid worker unit")?
            .0;
        if words[1] != format!("mini-grain-controller@{task}.service")
            || words[3].len() != 32
            || !words[3]
                .bytes()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
            || !words[4].bytes().all(|b| b.is_ascii_digit())
        {
            return Err("retained controller identity mismatch".into());
        }
        let pid = words[2].parse().map_err(|_| "invalid retained PID")?;
        if pid <= 1 {
            return Err("invalid retained PID".into());
        }
        Ok(Self {
            manager: words[0].into(),
            unit: words[1].into(),
            pid,
            invocation: words[3].into(),
            start: words[4].into(),
        })
    }
    fn verify(&self) -> Result<(), String> {
        let out = Command::new("/usr/bin/systemctl")
            .args([
                &format!("--{}", self.manager),
                "show",
                "--no-pager",
                "-p",
                "MainPID",
                "-p",
                "InvocationID",
                "-p",
                "ActiveState",
                &self.unit,
            ])
            .output()
            .map_err(|e| e.to_string())?;
        if !out.status.success() {
            return Err("controller observation failed".into());
        }
        let text = String::from_utf8(out.stdout).map_err(|e| e.to_string())?;
        let field = |name: &str| text.lines().find_map(|line| line.strip_prefix(name));
        if field("MainPID=") != Some(self.pid.to_string().as_str())
            || field("InvocationID=") != Some(&self.invocation)
            || field("ActiveState=") != Some("active")
            || process_start(self.pid)? != self.start
        {
            return Err("controller incarnation changed or stopped".into());
        }
        let meta = fs::metadata(format!("/proc/{}", self.pid)).map_err(|e| e.to_string())?;
        if meta.uid() != unsafe { geteuid() } {
            return Err("controller process UID differs from worker".into());
        }
        Ok(())
    }
    fn open(&self) -> Result<File, String> {
        self.verify()?;
        let fd = unsafe {
            syscall(
                434,
                self.pid as std::os::raw::c_long,
                0 as std::os::raw::c_long,
            )
        };
        if fd < 0 {
            return Err(format!(
                "controller pidfd: {}",
                std::io::Error::last_os_error()
            ));
        }
        let file = unsafe { File::from_raw_fd(fd as i32) };
        self.verify()?;
        if ready(&file, 0)? {
            return Err("controller exited before launch".into());
        }
        Ok(file)
    }
}
fn process_start(pid: u32) -> Result<String, String> {
    let text = fs::read_to_string(format!("/proc/{pid}/stat")).map_err(|e| e.to_string())?;
    text.rsplit_once(')')
        .and_then(|(_, tail)| tail.split_whitespace().nth(19))
        .map(str::to_owned)
        .ok_or("invalid process stat".into())
}
#[repr(C)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}
unsafe extern "C" {
    fn syscall(number: std::os::raw::c_long, ...) -> std::os::raw::c_long;
    fn poll(fds: *mut PollFd, count: usize, timeout: i32) -> i32;
    fn prctl(option: i32, ...) -> i32;
    fn getppid() -> i32;
}
fn ready(file: &File, timeout: i32) -> Result<bool, String> {
    let mut p = PollFd {
        fd: file.as_raw_fd(),
        events: 1,
        revents: 0,
    };
    let n = unsafe { poll(&mut p, 1, timeout) };
    if n < 0 {
        let e = std::io::Error::last_os_error();
        if e.kind() == std::io::ErrorKind::Interrupted {
            return Ok(false);
        }
        return Err(e.to_string());
    }
    Ok(p.revents != 0)
}
fn supervise(controller: File, mut command: Command, mut gate: File) -> Result<(), String> {
    let monitor = std::process::id() as i32;
    unsafe {
        command.pre_exec(move || {
            // A monitor crash also kills bwrap, whose --die-with-parent and PID
            // namespace kill all sandbox descendants, including setsid children.
            if prctl(
                1,
                9 as std::os::raw::c_ulong,
                0 as std::os::raw::c_ulong,
                0 as std::os::raw::c_ulong,
                0 as std::os::raw::c_ulong,
            ) != 0
                || getppid() != monitor
            {
                return Err(std::io::Error::other("worker monitor disappeared"));
            }
            Ok(())
        });
    }
    if ready(&controller, 0)? {
        return Err("controller exited before worker spawn".into());
    }
    let mut child = command.spawn().map_err(|e| format!("worker spawn: {e}"))?;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                return if status.success() {
                    Ok(())
                } else {
                    Err(format!("worker exited: {status}"))
                }
            }
            Ok(None) => {}
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(error.to_string());
            }
        }
        match ready(&controller, 100) {
            Ok(false) => {}
            result => {
                // `started` already forbids replay. Kill before any potentially
                // blocking gate lock/fsync: storage contention must not extend
                // the sandbox lifetime after its controller has exited.
                let _ = child.kill();
                let _ = child.wait();
                let fenced = lock(&gate, LOCK_EX).and_then(|_| write_state(&mut gate, "fenced\n"));
                let _ = lock(&gate, LOCK_UN);
                return Err(format!(
                    "controller lifetime ended; worker killed ({result:?}; fence {fenced:?})"
                ));
            }
        }
    }
}

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args_os().collect();
    if args.len() == 2 && args[1] == "--controller-manager-protocol" {
        println!("mini-controller-manager-v1");
        return Ok(());
    }
    if args.len() == 2 && args[1] == "--launch-gate-protocol" {
        println!("mini-grain-launch-gate-v1");
        return Ok(());
    }
    if args.len() < 4 {
        return Err("usage: launch-gate init|fence|run STATE_DIR UNIT [-- ABS_COMMAND ...]".into());
    }
    let mode = args[1].to_str().ok_or("mode must be UTF-8")?;
    let dir = Path::new(&args[2]);
    private_dir(dir)?;
    let unit = args[3].to_str().ok_or("unit must be UTF-8")?;
    let path = gate_path(dir, unit)?;
    match mode {
        "init" if args.len() == 4 => {
            let mut file = OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .custom_flags(O_NOFOLLOW)
                .mode(0o600)
                .open(&path)
                .map_err(|e| format!("gate init: {e}"))?;
            lock(&file, LOCK_EX)?;
            if !read_state(&mut file)?.is_empty() {
                return Err("gate was fenced during init".into());
            }
            let controller = Controller::from_env(unit)?;
            let state = controller
                .map(|c| format!("armed\n{}\n", c.encode()))
                .unwrap_or_else(|| "armed\n".into());
            write_state(&mut file, &state)?;
            File::open(dir)
                .and_then(|f| f.sync_all())
                .map_err(|e| format!("gate directory sync: {e}"))?;
            lock(&file, LOCK_UN)?;
            println!("armed {unit}");
        }
        "check-lifetime" if args.len() == 4 => {
            let mut file = open_gate(&path, false)?;
            lock(&file, LOCK_EX)?;
            let state = read_state(&mut file)?;
            let identity = state
                .strip_prefix("armed\n")
                .and_then(|s| s.strip_suffix('\n'))
                .ok_or("cross-manager worker requires retained controller identity")?;
            let controller = Controller::decode(identity, unit)?;
            if controller.manager != "system" {
                return Err("cross-manager gate is not system-bound".into());
            }
            controller.open()?;
            lock(&file, LOCK_UN)?;
        }
        "fence" if args.len() == 4 => {
            let mut file = open_gate(&path, true)?;
            lock(&file, LOCK_EX)?;
            write_state(&mut file, "fenced\n")?;
            File::open(dir)
                .and_then(|f| f.sync_all())
                .map_err(|e| e.to_string())?;
            lock(&file, LOCK_UN)?;
            println!("fenced {unit}");
        }
        "run" if args.len() >= 6 && args[4] == "--" => {
            let command = Path::new(&args[5]);
            if !command.is_absolute() {
                return Err("worker command must be absolute".into());
            }
            let mut file = open_gate(&path, false)?;
            lock(&file, LOCK_EX)?;
            let state = read_state(&mut file)?;
            let controller = if state == "armed\n" {
                None
            } else if let Some(identity) = state
                .strip_prefix("armed\n")
                .and_then(|s| s.strip_suffix('\n'))
            {
                Some(Controller::decode(identity, unit)?.open()?)
            } else {
                return Err("worker launch fenced or already started".into());
            };
            write_state(&mut file, &state.replacen("armed", "started", 1))?;
            lock(&file, LOCK_UN)?;
            // This process remains the systemd unit MainPID. Recovery fences first,
            // then kills/audits that unique unit. If it races after unlock but
            // before exec, SIGKILL still prevents the exec.
            let mut command = Command::new(command);
            command.args(&args[6..]);
            if let Some(controller) = controller {
                return supervise(controller, command, file);
            }
            let error = command.exec();
            return Err(format!("worker exec: {error}"));
        }
        _ => return Err("invalid launch-gate command".into()),
    }
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("launch-gate: {error}");
            ExitCode::FAILURE
        }
    }
}
