//! The modeled operating system of a `fixture-os` build (disposable test
//! fixtures; never a release). It implements exactly the calls of `os.rs`, and
//! nothing above them changes: the broker, grain CLI, resident, supervisor and
//! custodian run their ordinary code against a real Mini Host.
//!
//! The model, rooted at `$MINI_FIXTURE_OS` (an owner-private directory):
//! * Identity. One unprivileged principal (the real euid) stands in for root
//!   and for the operator; app accounts are the broker's pool UIDs, by name
//!   only. The app runs as the principal, still inside bubblewrap.
//! * Units. `units/` is the runtime unit directory the broker renders into.
//!   `systemctl` (`spk-host fixture-systemctl`) reads it; `start` hands a unit to a detached manager
//!   (`fixture-unit-run`) that records `state/<unit>.json` (ActiveState,
//!   MainPID, InvocationID, ControlGroup) before the main process execs,
//!   waits for it, kills the rest of its session (KillMode=control-group),
//!   records `failed` with the InvocationID retained, and starts `OnFailure=`.
//! * Cgroups. A unit's cgroup is `/fixture.slice/<unit>`; its members are the
//!   processes of the main process's session. `populated` is whether any is
//!   alive.
//! * Mounts. `mounts/<name>` registers a directory the fixture volume helper
//!   stands up as a mounted `/var` of a given size.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

const ROOT_ENV: &str = "MINI_FIXTURE_OS";
const CGROUP_ENV: &str = "MINI_FIXTURE_CGROUP";
const SLICE: &str = "/fixture.slice";

fn invalid(reason: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason.into())
}

fn euid() -> u32 {
    unsafe { libc::geteuid() }
}

/// The model root: absolute, a directory, owned by the principal, mode 0700.
pub(crate) fn root() -> io::Result<PathBuf> {
    let root = PathBuf::from(
        std::env::var_os(ROOT_ENV).ok_or_else(|| invalid("fixture OS root unset ($MINI_FIXTURE_OS)"))?,
    );
    let meta = fs::symlink_metadata(&root)?;
    if !root.is_absolute()
        || !meta.is_dir()
        || meta.uid() != euid()
        || meta.permissions().mode() & 0o777 != 0o700
    {
        return Err(invalid("fixture OS root must be an absolute principal-owned 0700 directory"));
    }
    Ok(root)
}

pub(crate) fn root_uid() -> u32 {
    euid()
}

pub(crate) fn root_group(gid: u32) -> bool {
    gid == 0 || gid == unsafe { libc::getegid() }
}

pub(crate) fn privileged() -> bool {
    true
}

pub(crate) fn app_owner(uid: u32, app_uid: u32) -> bool {
    uid == app_uid || uid == euid()
}

pub(crate) fn runtime_units() -> PathBuf {
    root()
        .map(|root| root.join("units"))
        .unwrap_or_else(|_| PathBuf::from("/nonexistent/fixture-os/units"))
}

pub(crate) fn host_identity_path() -> PathBuf {
    root()
        .map(|root| root.join("host-identity"))
        .unwrap_or_else(|_| PathBuf::from("/nonexistent/fixture-os/host-identity"))
}

/// The model's unit manager client, `$MINI_FIXTURE_OS/systemctl` (the fixture
/// journey installs it as `spk-host fixture-systemctl`).
pub(crate) fn systemctl() -> Command {
    Command::new(
        root()
            .map(|root| root.join("systemctl"))
            .unwrap_or_else(|_| PathBuf::from("/nonexistent/fixture-os/systemctl")),
    )
}

/// The modeled identity switch keeps the principal's credentials, so the process
/// that executes the launcher is the principal: judge the execute bit for it.
pub(crate) fn executes_as_app(owner: u32, group: u32, mode: u32, _app_uid: u32, _app_gid: u32) -> bool {
    crate::spawn_gate::execute_mode_permits(owner, group, mode, euid(), unsafe { libc::getegid() })
}

/// Every pool UID names an account whose primary group has the same number.
pub(crate) fn account_gid(uid: u32) -> Option<u32> {
    (uid != 0 && uid != euid()).then_some(uid)
}

pub(crate) fn self_cgroup() -> io::Result<String> {
    Ok(match std::env::var(CGROUP_ENV) {
        Ok(group) => format!("0::{group}\n"),
        Err(_) => "0::/user.slice/fixture-principal\n".to_owned(),
    })
}

/// The session id of a live process (`/proc/<pid>/stat` field 6).
fn session_of(pid: u32) -> io::Result<u32> {
    let stat = fs::read_to_string(format!("/proc/{pid}/stat"))?;
    let tail = stat
        .rsplit_once(')')
        .map(|(_, tail)| tail)
        .ok_or_else(|| invalid("process stat malformed"))?;
    // state ppid pgrp session
    tail.split_whitespace()
        .nth(3)
        .and_then(|value| value.parse().ok())
        .ok_or_else(|| invalid("process stat session malformed"))
}

fn session_alive(sid: u32) -> bool {
    if sid == 0 {
        return false;
    }
    let Ok(entries) = fs::read_dir("/proc") else {
        return false;
    };
    entries.flatten().any(|entry| {
        entry
            .file_name()
            .to_str()
            .and_then(|name| name.parse::<u32>().ok())
            .is_some_and(|pid| session_of(pid).ok() == Some(sid))
    })
}

pub(crate) fn pid_cgroup(pid: u32) -> io::Result<String> {
    let session = session_of(pid)?;
    for (_, state) in states()? {
        if state.active_state == "active" && state.sid != 0 && state.sid == session {
            return Ok(format!("0::{}\n", state.control_group));
        }
    }
    Ok("0::/user.slice/fixture-principal\n".to_owned())
}

pub(crate) fn cgroup_events(group: &str) -> io::Result<String> {
    for (_, state) in states()? {
        if !state.control_group.is_empty() && state.control_group == group {
            let populated = u8::from(session_alive(state.sid));
            return Ok(format!("populated {populated}\nfrozen 0\n"));
        }
    }
    Err(io::Error::new(io::ErrorKind::NotFound, "fixture cgroup absent"))
}

pub(crate) fn var_filesystem(
    path: &Path,
    _parent_fd: std::os::fd::RawFd,
    _var_fd: std::os::fd::RawFd,
) -> io::Result<(bool, u128)> {
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| invalid("fixture mount name"))?;
    let registry = root()?.join("mounts").join(name);
    let text = match fs::read_to_string(&registry) {
        Ok(text) => text,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok((false, 0)),
        Err(error) => return Err(error),
    };
    let mut mount = None;
    let mut bytes = None;
    for line in text.lines() {
        if let Some(value) = line.strip_prefix("mount=") {
            mount = Some(PathBuf::from(value));
        } else if let Some(value) = line.strip_prefix("bytes=") {
            bytes = value.parse::<u128>().ok();
        }
    }
    match (mount, bytes) {
        (Some(mount), Some(bytes)) if mount == path => Ok((true, bytes)),
        _ => Ok((false, 0)),
    }
}

/// The principal cannot switch accounts: the drop is the part an unprivileged
/// process can make (no_new_privs, not dumpable), and the identity a role
/// holds is the account its unit names, by name.
pub(crate) fn drop_to_identity(_uid: u32, _gid: u32) -> io::Result<()> {
    if unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) } != 0
        || unsafe { libc::prctl(libc::PR_SET_DUMPABLE, 0, 0, 0, 0) } != 0
    {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

pub(crate) fn holds_exactly_identity(_uid: u32, _gid: u32) -> io::Result<bool> {
    Ok(unsafe { libc::prctl(libc::PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0) } == 1)
}

pub(crate) unsafe fn child_assume_app_identity(_uid: u32, _gid: u32) -> bool {
    true
}

// ---------------------------------------------------------------- unit model

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
struct UnitState {
    active_state: String,
    result: String,
    main_pid: u32,
    sid: u32,
    invocation_id: String,
    control_group: String,
    starts: u64,
}

struct UnitFile {
    environment: Vec<(String, String)>,
    exec_start: Vec<String>,
    on_failure: Option<String>,
    slice: String,
}

fn unit_name_ok(name: &str) -> bool {
    !name.is_empty()
        && name.len() < 256
        && name
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"-_.@".contains(&b))
        && !name.starts_with('.')
}

fn state_path(root: &Path, unit: &str) -> PathBuf {
    root.join("state").join(format!("{unit}.json"))
}

fn read_state(root: &Path, unit: &str) -> io::Result<UnitState> {
    match fs::read(state_path(root, unit)) {
        Ok(bytes) => Ok(serde_json::from_slice(&bytes)?),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(UnitState {
            active_state: "inactive".into(),
            result: "success".into(),
            ..UnitState::default()
        }),
        Err(error) => Err(error),
    }
}

fn write_state(root: &Path, unit: &str, state: &UnitState) -> io::Result<()> {
    let dir = root.join("state");
    fs::create_dir_all(&dir)?;
    let temp = dir.join(format!(".{unit}.{}.tmp", std::process::id()));
    {
        let mut file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .mode(0o600)
            .open(&temp)?;
        file.write_all(&serde_json::to_vec(state)?)?;
        file.sync_all()?;
    }
    fs::rename(&temp, state_path(root, unit))
}

fn states() -> io::Result<Vec<(String, UnitState)>> {
    let root = root()?;
    let mut out = Vec::new();
    let dir = root.join("state");
    let entries = match fs::read_dir(&dir) {
        Ok(entries) => entries,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(out),
        Err(error) => return Err(error),
    };
    for entry in entries {
        let entry = entry?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if let Some(unit) = name.strip_suffix(".json").filter(|n| !n.starts_with('.')) {
            out.push((unit.to_owned(), read_state(&root, unit)?));
        }
    }
    Ok(out)
}

/// The unit's file, or the template `prefix@.service` instantiated with `%i`.
fn load_unit(root: &Path, unit: &str) -> io::Result<Option<UnitFile>> {
    let units = root.join("units");
    let (text, instance) = match fs::read_to_string(units.join(unit)) {
        Ok(text) => (text, None),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            let Some((prefix, rest)) = unit.split_once('@') else {
                return Ok(None);
            };
            let Some(instance) = rest.strip_suffix(".service") else {
                return Ok(None);
            };
            match fs::read_to_string(units.join(format!("{prefix}@.service"))) {
                Ok(text) => (text, Some(instance.to_owned())),
                Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
                Err(error) => return Err(error),
            }
        }
        Err(error) => return Err(error),
    };
    let text = match &instance {
        Some(instance) => text.replace("%i", instance),
        None => text,
    };
    let mut file = UnitFile {
        environment: Vec::new(),
        exec_start: Vec::new(),
        on_failure: None,
        slice: String::new(),
    };
    for line in text.lines() {
        if let Some(value) = line.strip_prefix("Environment=") {
            for pair in value.split_whitespace() {
                let (key, value) = pair
                    .split_once('=')
                    .ok_or_else(|| invalid("fixture unit Environment= pair"))?;
                file.environment.push((key.to_owned(), value.to_owned()));
            }
        } else if let Some(value) = line.strip_prefix("ExecStart=") {
            file.exec_start = value.split_whitespace().map(str::to_owned).collect();
        } else if let Some(value) = line.strip_prefix("OnFailure=") {
            file.on_failure = Some(value.trim().to_owned()).filter(|v| !v.is_empty());
        } else if let Some(value) = line.strip_prefix("Slice=") {
            file.slice = value.trim().to_owned();
        }
    }
    if file.exec_start.is_empty() {
        return Err(invalid(format!("fixture unit {unit} has no ExecStart=")));
    }
    Ok(Some(file))
}

fn show(root: &Path, unit: &str, properties: &[String], value_only: bool) -> io::Result<String> {
    let file = load_unit(root, unit)?;
    let state = read_state(root, unit)?;
    let active = state.active_state == "active";
    let mut out = String::new();
    for property in properties {
        let value = match property.as_str() {
            "Id" => unit.to_owned(),
            "LoadState" => if file.is_some() { "loaded" } else { "not-found" }.to_owned(),
            "ActiveState" => state.active_state.clone(),
            "SubState" => match state.active_state.as_str() {
                "active" => "running",
                "failed" => "failed",
                _ => "dead",
            }
            .to_owned(),
            "Result" => state.result.clone(),
            "MainPID" => if active { state.main_pid } else { 0 }.to_string(),
            "Job" => String::new(),
            "ControlPID" => "0".to_owned(),
            "InvocationID" => state.invocation_id.clone(),
            "ControlGroup" => state.control_group.clone(),
            "Slice" => file.as_ref().map(|f| f.slice.clone()).unwrap_or_default(),
            _ => String::new(),
        };
        if value_only {
            out.push_str(&value);
        } else {
            out.push_str(property);
            out.push('=');
            out.push_str(&value);
        }
        out.push('\n');
    }
    Ok(out)
}

fn start(root: &Path, unit: &str) -> io::Result<()> {
    if read_state(root, unit)?.active_state == "active" {
        return Ok(());
    }
    if load_unit(root, unit)?.is_none() {
        return Err(invalid(format!("Unit {unit} not found.")));
    }
    fs::create_dir_all(root.join("logs"))?;
    let log = OpenOptions::new()
        .append(true)
        .create(true)
        .mode(0o600)
        .open(root.join("logs").join(format!("{unit}.manager.log")))?;
    let before = read_state(root, unit)?.starts;
    let mut manager = Command::new(std::env::current_exe()?);
    manager
        .arg("fixture-unit-run")
        .arg(unit)
        .env(ROOT_ENV, root)
        .stdin(std::process::Stdio::null())
        .stdout(log.try_clone()?)
        .stderr(log);
    unsafe {
        use std::os::unix::process::CommandExt;
        manager.pre_exec(|| {
            if libc::setsid() < 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let _detached = manager.spawn()?;
    // Type=exec: `start` returns once the main process has been handed its exec.
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        let state = read_state(root, unit)?;
        if state.starts > before && state.active_state != "activating" {
            return Ok(());
        }
        if Instant::now() > deadline {
            return Err(invalid(format!("fixture unit {unit} start timed out")));
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn stop(root: &Path, unit: &str) -> io::Result<()> {
    let state = read_state(root, unit)?;
    if state.active_state != "active" {
        return Ok(());
    }
    unsafe {
        libc::kill(-(state.sid as i32), libc::SIGTERM);
    }
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        let now = read_state(root, unit)?;
        if now.active_state != "active" {
            // A requested stop ends inactive with the invocation cleared.
            write_state(
                root,
                unit,
                &UnitState {
                    active_state: "inactive".into(),
                    result: "success".into(),
                    main_pid: 0,
                    sid: 0,
                    invocation_id: String::new(),
                    control_group: String::new(),
                    starts: now.starts,
                },
            )?;
            return Ok(());
        }
        if Instant::now() > deadline {
            unsafe {
                libc::kill(-(state.sid as i32), libc::SIGKILL);
            }
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

fn reset_failed(root: &Path, unit: &str) -> io::Result<()> {
    let state = read_state(root, unit)?;
    if state.active_state == "failed" {
        write_state(
            root,
            unit,
            &UnitState {
                active_state: "inactive".into(),
                result: "success".into(),
                main_pid: 0,
                sid: 0,
                invocation_id: String::new(),
                control_group: String::new(),
                starts: state.starts,
            },
        )?;
    }
    Ok(())
}

/// `spk-host fixture-systemctl [--system] VERB ...`: the unit manager client.
pub fn systemctl_main(args: &[String]) -> i32 {
    let result = (|| -> io::Result<String> {
        let root = root()?;
        let mut args: Vec<&str> = args.iter().map(String::as_str).collect();
        if args.first() == Some(&"--system") {
            args.remove(0);
        }
        let (verb, rest) = args
            .split_first()
            .ok_or_else(|| invalid("fixture systemctl: verb required"))?;
        match *verb {
            "daemon-reload" => Ok(String::new()),
            "show" => {
                let mut unit = None;
                let mut properties = Vec::new();
                let mut value_only = false;
                for arg in rest {
                    if let Some(list) = arg.strip_prefix("--property=") {
                        properties.extend(list.split(',').map(str::to_owned));
                    } else if *arg == "--value" {
                        value_only = true;
                    } else if *arg == "--no-pager" {
                    } else if unit.is_none() && unit_name_ok(arg) {
                        unit = Some(*arg);
                    } else {
                        return Err(invalid(format!("fixture systemctl show: {arg}")));
                    }
                }
                let unit = unit.ok_or_else(|| invalid("fixture systemctl show: unit"))?;
                show(&root, unit, &properties, value_only)
            }
            "start" | "stop" | "reset-failed" => {
                let [unit] = rest else {
                    return Err(invalid(format!("fixture systemctl {verb}: one unit")));
                };
                if !unit_name_ok(unit) {
                    return Err(invalid("fixture systemctl: unit name"));
                }
                match *verb {
                    "start" => start(&root, unit)?,
                    "stop" => stop(&root, unit)?,
                    _ => reset_failed(&root, unit)?,
                }
                Ok(String::new())
            }
            other => Err(invalid(format!("fixture systemctl: unsupported verb {other}"))),
        }
    })();
    match result {
        Ok(out) => {
            print!("{out}");
            0
        }
        Err(error) => {
            eprintln!("fixture-systemctl: {error}");
            1
        }
    }
}

/// `spk-host fixture-unit-run UNIT`: the detached manager of one unit start.
pub fn unit_run_main(args: &[String]) -> i32 {
    let result = (|| -> io::Result<()> {
        let [unit] = args else {
            return Err(invalid("fixture-unit-run UNIT"));
        };
        let root = root()?;
        let file = load_unit(&root, unit)?.ok_or_else(|| invalid("fixture unit vanished"))?;
        let prior = read_state(&root, unit)?;
        let starts = prior.starts + 1;
        let mut digest = Sha256::new();
        digest.update(b"DREGG/FIXTURE-OS/INVOCATION/v1\0");
        digest.update(unit.as_bytes());
        digest.update(starts.to_le_bytes());
        let invocation: String = digest.finalize()[..16]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        let group = format!("{SLICE}/{unit}");
        write_state(
            &root,
            unit,
            &UnitState {
                active_state: "activating".into(),
                result: "success".into(),
                starts,
                ..UnitState::default()
            },
        )?;
        let log = OpenOptions::new()
            .append(true)
            .create(true)
            .mode(0o600)
            .open(root.join("logs").join(format!("{unit}.{starts}.log")))?;
        let mut gate = [0i32; 2];
        if unsafe { libc::pipe2(gate.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
            return Err(io::Error::last_os_error());
        }
        let mut env: Vec<(String, String)> = vec![
            ("PATH".into(), "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin".into()),
            ("INVOCATION_ID".into(), invocation.clone()),
            (ROOT_ENV.into(), root.to_string_lossy().into_owned()),
            (CGROUP_ENV.into(), group.clone()),
        ];
        env.extend(file.environment.iter().cloned());
        let c = |s: &str| std::ffi::CString::new(s).map_err(|_| invalid("NUL in fixture unit"));
        let argv = file
            .exec_start
            .iter()
            .map(|a| c(a))
            .collect::<io::Result<Vec<_>>>()?;
        let envp = env
            .iter()
            .map(|(k, v)| c(&format!("{k}={v}")))
            .collect::<io::Result<Vec<_>>>()?;
        let mut argv_ptr: Vec<*const libc::c_char> = argv.iter().map(|a| a.as_ptr()).collect();
        argv_ptr.push(std::ptr::null());
        let mut envp_ptr: Vec<*const libc::c_char> = envp.iter().map(|a| a.as_ptr()).collect();
        envp_ptr.push(std::ptr::null());
        let devnull = File::open("/dev/null")?;
        let pid = unsafe { libc::fork() };
        if pid < 0 {
            return Err(io::Error::last_os_error());
        }
        if pid == 0 {
            unsafe {
                libc::setsid();
                let mut byte = 0u8;
                libc::close(gate[1]);
                if libc::read(gate[0], (&mut byte as *mut u8).cast(), 1) != 1 {
                    libc::_exit(126);
                }
                libc::dup2(std::os::fd::AsRawFd::as_raw_fd(&devnull), 0);
                libc::dup2(std::os::fd::AsRawFd::as_raw_fd(&log), 1);
                libc::dup2(std::os::fd::AsRawFd::as_raw_fd(&log), 2);
                libc::umask(0o022);
                libc::execve(argv_ptr[0], argv_ptr.as_ptr(), envp_ptr.as_ptr());
                libc::_exit(127);
            }
        }
        unsafe {
            libc::close(gate[0]);
        }
        let pid = pid as u32;
        write_state(
            &root,
            unit,
            &UnitState {
                active_state: "active".into(),
                result: "success".into(),
                main_pid: pid,
                sid: pid,
                invocation_id: invocation.clone(),
                control_group: group.clone(),
                starts,
            },
        )?;
        let one = 1u8;
        if unsafe { libc::write(gate[1], (&one as *const u8).cast(), 1) } != 1 {
            return Err(io::Error::last_os_error());
        }
        unsafe {
            libc::close(gate[1]);
        }
        let mut status = 0;
        loop {
            let reaped = unsafe { libc::waitpid(pid as i32, &mut status, 0) };
            if reaped == pid as i32 {
                break;
            }
            if reaped < 0 && io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
                return Err(io::Error::last_os_error());
            }
        }
        // KillMode=control-group: the rest of the unit's session goes with it.
        unsafe {
            libc::kill(-(pid as i32), libc::SIGKILL);
        }
        let deadline = Instant::now() + Duration::from_secs(20);
        while session_alive(pid) && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(20));
        }
        let clean = libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0;
        let now = read_state(&root, unit)?;
        if now.starts != starts || now.active_state != "active" {
            // A concurrent `stop` already recorded the end of this start.
            return Ok(());
        }
        let ended = if clean {
            UnitState {
                active_state: "inactive".into(),
                result: "success".into(),
                starts,
                ..UnitState::default()
            }
        } else {
            // systemd keeps a failed unit's InvocationID and cgroup path while
            // its OnFailure= job runs; the main process is gone.
            UnitState {
                active_state: "failed".into(),
                result: "exit-code".into(),
                main_pid: 0,
                sid: pid,
                invocation_id: invocation,
                control_group: group,
                starts,
            }
        };
        write_state(&root, unit, &ended)?;
        if !clean {
            if let Some(next) = &file.on_failure {
                start(&root, next)?;
            }
        }
        Ok(())
    })();
    match result {
        Ok(()) => 0,
        Err(error) => {
            eprintln!("fixture-unit-run: {error}");
            1
        }
    }
}
