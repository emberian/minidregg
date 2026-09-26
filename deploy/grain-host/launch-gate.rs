//! Durable Linux per-operation systemd ExecStart gate for Mini grain workers.
//! The real worker must be launched through `run` as the unit's MainPID.
use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

const O_NOFOLLOW: i32 = 0o400000;
const LOCK_EX: i32 = 2;
const LOCK_UN: i32 = 8;
unsafe extern "C" { fn flock(fd: i32, operation: i32) -> i32; fn geteuid() -> u32; }

fn lock(file: &File, operation: i32) -> Result<(), String> {
    if unsafe { flock(file.as_raw_fd(), operation) } == 0 { Ok(()) }
    else { Err(format!("flock: {}", std::io::Error::last_os_error())) }
}

fn private_dir(path: &Path) -> Result<(), String> {
    if !path.is_absolute() { return Err("state dir must be absolute".into()); }
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.file_type().is_dir() || meta.uid() != unsafe { geteuid() }
        || meta.permissions().mode() & 0o077 != 0 {
        return Err("state dir must be an owned, real, private directory".into());
    }
    Ok(())
}

fn gate_path(dir: &Path, unit: &str) -> Result<PathBuf, String> {
    let Some(rest) = unit.strip_prefix("mini-grain-t") else { return Err("bad unit".into()) };
    let Some((task, operation)) = rest.split_once("-o") else { return Err("bad unit".into()) };
    if task.is_empty() || operation.is_empty() || !task.bytes().all(|b| b.is_ascii_digit())
        || !operation.bytes().all(|b| b.is_ascii_digit()) {
        return Err("bad unit".into());
    }
    Ok(dir.join(format!("{unit}.gate")))
}

fn open_gate(path: &Path, create: bool) -> Result<File, String> {
    let mut options = OpenOptions::new();
    options.read(true).write(true).custom_flags(O_NOFOLLOW).mode(0o600);
    if create { options.create(true); }
    let file = options.open(path).map_err(|e| format!("gate open: {e}"))?;
    let meta = file.metadata().map_err(|e| e.to_string())?;
    if !meta.file_type().is_file() || meta.uid() != unsafe { geteuid() }
        || meta.permissions().mode() & 0o077 != 0 {
        return Err("gate must be an owned private regular file".into());
    }
    Ok(file)
}

fn read_state(file: &mut File) -> Result<String, String> {
    file.seek(SeekFrom::Start(0)).map_err(|e| e.to_string())?;
    let mut state = String::new();
    file.take(32).read_to_string(&mut state).map_err(|e| e.to_string())?;
    Ok(state)
}

fn write_state(file: &mut File, state: &str) -> Result<(), String> {
    file.set_len(0).map_err(|e| e.to_string())?;
    file.seek(SeekFrom::Start(0)).map_err(|e| e.to_string())?;
    file.write_all(state.as_bytes()).and_then(|_| file.sync_all()).map_err(|e| e.to_string())
}

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args_os().collect();
    if args.len() == 2 && args[1] == "--launch-gate-protocol" {
        println!("mini-grain-launch-gate-v1");
        return Ok(());
    }
    if args.len() < 4 { return Err("usage: launch-gate init|fence|run STATE_DIR UNIT [-- ABS_COMMAND ...]".into()); }
    let mode = args[1].to_str().ok_or("mode must be UTF-8")?;
    let dir = Path::new(&args[2]);
    private_dir(dir)?;
    let unit = args[3].to_str().ok_or("unit must be UTF-8")?;
    let path = gate_path(dir, unit)?;
    match mode {
        "init" if args.len() == 4 => {
            let mut file = OpenOptions::new().read(true).write(true).create_new(true)
                .custom_flags(O_NOFOLLOW).mode(0o600).open(&path)
                .map_err(|e| format!("gate init: {e}"))?;
            lock(&file, LOCK_EX)?;
            if !read_state(&mut file)?.is_empty() { return Err("gate was fenced during init".into()); }
            write_state(&mut file, "armed\n")?;
            File::open(dir).and_then(|f| f.sync_all()).map_err(|e| format!("gate directory sync: {e}"))?;
            lock(&file, LOCK_UN)?;
            println!("armed {unit}");
        }
        "fence" if args.len() == 4 => {
            let mut file = open_gate(&path, true)?;
            lock(&file, LOCK_EX)?;
            write_state(&mut file, "fenced\n")?;
            File::open(dir).and_then(|f| f.sync_all()).map_err(|e| e.to_string())?;
            lock(&file, LOCK_UN)?;
            println!("fenced {unit}");
        }
        "run" if args.len() >= 6 && args[4] == "--" => {
            let command = Path::new(&args[5]);
            if !command.is_absolute() { return Err("worker command must be absolute".into()); }
            let mut file = open_gate(&path, false)?;
            lock(&file, LOCK_EX)?;
            if read_state(&mut file)? != "armed\n" { return Err("worker launch fenced or already started".into()); }
            write_state(&mut file, "started\n")?;
            lock(&file, LOCK_UN)?;
            // This process is the systemd unit MainPID. Recovery fences first,
            // then kills/audits that unique unit. If it races after unlock but
            // before exec, SIGKILL still prevents the exec.
            let error = Command::new(command).args(&args[6..]).exec();
            return Err(format!("worker exec: {error}"));
        }
        _ => return Err("invalid launch-gate command".into()),
    }
    Ok(())
}

fn main() -> ExitCode {
    match run() { Ok(()) => ExitCode::SUCCESS,
        Err(error) => { eprintln!("launch-gate: {error}"); ExitCode::FAILURE } }
}
