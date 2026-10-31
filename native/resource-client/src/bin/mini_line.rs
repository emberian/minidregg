//! `mini-line MINI ARG...`: one ssh line, run by the member's resident shell (`mini line-resident`)
//! instead of a fresh `mini`.
//!
//! `ARG...` is exactly the `mini` argument vector the forced command would exec (it carries
//! `--call-slots DIR`). This takes the member's call slot itself, as `mini shell --call-slots`
//! would (an exclusive non-blocking flock on DIR/1, then DIR/2, close-on-exec, held for the call's
//! life; the third call is refused by name with exit 75), then hands the line, without
//! `--call-slots`, and its own standard input, output and error to the resident serving that
//! slot, starting it when none listens. The exit code is the line's.
//!
//! Every resident is keyed by everything that shapes its commands: the `mini` file's identity,
//! the arguments other than the line, the `MINI_*` environment, `HOME`, `PATH` and the umask, so
//! two sessions that would run differently never share one. Anything that keeps the resident from
//! being used (no slot directory, a socket path too long, a resident that does not come up) execs
//! `MINI ARG...` as before.
// A closed standard error drops the message instead of panicking (`streams`, shared with `mini`).
#[allow(dead_code)]
#[macro_use]
#[path = "../streams.rs"]
mod streams;
use std::ffi::{OsStr, OsString};
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::time::{Duration, Instant};

fn exec(mini: &OsStr, args: &[OsString]) -> ExitCode {
    let error = Command::new(mini).args(args).exec();
    eprintln!("mini-shell-ssh: cannot run {}: {error}", Path::new(mini).display());
    ExitCode::from(70)
}

fn slot(dir: &Path) -> Option<Option<(u8, File)>> {
    match std::fs::create_dir(dir) {
        Ok(()) => {
            let _ = std::fs::set_permissions(dir, std::os::unix::fs::PermissionsExt::from_mode(0o700));
        }
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
        Err(_) => return None,
    }
    for n in [1u8, 2] {
        let file = OpenOptions::new().append(true).create(true).mode(0o600).open(dir.join(n.to_string())).ok()?;
        if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } == 0 {
            return Some(Some((n, file)));
        }
    }
    Some(None)
}

/// FNV-1a over the key's parts, twice with different bases: a name, not a secret.
fn key(parts: &[&[u8]]) -> String {
    let mut out = String::new();
    for basis in [0xcbf2_9ce4_8422_2325u64, 0x8422_2325_cbf2_9ce4] {
        let mut hash = basis;
        for part in parts {
            for byte in (part.len() as u64).to_le_bytes().iter().chain(part.iter()) {
                hash ^= u64::from(*byte);
                hash = hash.wrapping_mul(0x0100_0000_01b3);
            }
        }
        out.push_str(&format!("{hash:016x}"));
    }
    out
}

fn send(stream: &UnixStream, body: &[u8]) -> std::io::Result<()> {
    let fds = [0i32, 1, 2];
    let space = unsafe { libc::CMSG_SPACE(12) } as usize;
    let mut control = vec![0u8; space];
    let mut iov = libc::iovec { iov_base: body.as_ptr() as *mut _, iov_len: body.len() };
    let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
    message.msg_iov = &mut iov;
    message.msg_iovlen = 1;
    message.msg_control = control.as_mut_ptr().cast();
    message.msg_controllen = space as _;
    let sent = unsafe {
        let header = libc::CMSG_FIRSTHDR(&message);
        (*header).cmsg_level = libc::SOL_SOCKET;
        (*header).cmsg_type = libc::SCM_RIGHTS;
        (*header).cmsg_len = libc::CMSG_LEN(12) as _;
        std::ptr::copy_nonoverlapping(fds.as_ptr(), libc::CMSG_DATA(header) as *mut i32, 3);
        libc::sendmsg(stream.as_raw_fd(), &message, 0)
    };
    if sent < 0 {
        return Err(std::io::Error::last_os_error());
    }
    let mut rest = &body[sent as usize..];
    let mut stream = stream;
    while !rest.is_empty() {
        let n = stream.write(rest)?;
        rest = &rest[n..];
    }
    Ok(())
}

fn main() -> ExitCode {
    let mut argv = std::env::args_os().skip(1);
    let Some(mini) = argv.next() else {
        eprintln!("usage: mini-line MINI ARG...");
        return ExitCode::from(64);
    };
    let args: Vec<OsString> = argv.collect();
    let Some(at) = args.iter().position(|a| a == "--call-slots") else { return exec(&mini, &args) };
    let Some(dir) = args.get(at + 1).map(PathBuf::from) else { return exec(&mini, &args) };
    let rest: Vec<OsString> = args.iter().enumerate().filter(|(i, _)| *i != at && *i != at + 1).map(|(_, a)| a.clone()).collect();
    let (n, held) = match slot(&dir) {
        None => return exec(&mini, &args),
        Some(None) => {
            eprintln!("mini-shell-ssh: two calls already running for this member; wait for one to finish");
            return ExitCode::from(75);
        }
        Some(Some(taken)) => taken,
    };
    let Ok(meta) = std::fs::metadata(&mini) else { return exec(&mini, &args) };
    let identity = format!("{} {} {} {} {} {}", meta.dev(), meta.ino(), meta.size(), meta.mtime(), meta.mtime_nsec(), meta.ctime());
    let umask = unsafe { let m = libc::umask(0o077); libc::umask(m); m };
    let mut env: Vec<(OsString, OsString)> = std::env::vars_os()
        .filter(|(k, _)| k.as_bytes().starts_with(b"MINI_") || k == "HOME" || k == "PATH").collect();
    env.sort();
    let line_at = rest.iter().position(|a| a == "--line");
    let mut parts: Vec<Vec<u8>> = vec![identity.into_bytes(), umask.to_string().into_bytes()];
    for (i, a) in rest.iter().enumerate() {
        if line_at.is_some_and(|l| i == l + 1) {
            continue;
        }
        parts.push(a.as_bytes().to_vec());
    }
    for (k, v) in &env {
        parts.push([k.as_bytes(), b"=", v.as_bytes()].concat());
    }
    let refs: Vec<&[u8]> = parts.iter().map(Vec::as_slice).collect();
    let socket = dir.join(format!("r{n}-{}.sock", key(&refs)));
    if socket.as_os_str().len() > 100 {
        drop(held);
        return exec(&mini, &args);
    }
    let config = rest.iter().position(|a| a == "--config").and_then(|i| rest.get(i + 1)).cloned().unwrap_or_default();
    let stream = match UnixStream::connect(&socket) {
        Ok(stream) => Some(stream),
        Err(_) => {
            let started = Command::new(&mini).arg("line-resident").arg(&socket).arg(&config)
                .stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::null())
                .process_group(0).status();
            let deadline = Instant::now() + Duration::from_secs(5);
            let mut connected = None;
            while started.as_ref().is_ok_and(|s| s.success()) && Instant::now() < deadline {
                if let Ok(stream) = UnixStream::connect(&socket) {
                    connected = Some(stream);
                    break;
                }
                std::thread::sleep(Duration::from_millis(1));
            }
            connected
        }
    };
    let Some(mut stream) = stream else {
        drop(held);
        return exec(&mini, &args);
    };
    let mut body = (rest.len() as u32).to_be_bytes().to_vec();
    for a in &rest {
        body.extend((a.len() as u32).to_be_bytes());
        body.extend(a.as_bytes());
    }
    if send(&stream, &body).is_err() {
        drop(held);
        return exec(&mini, &args);
    }
    let mut code = [0u8; 1];
    match stream.read(&mut code) {
        Ok(1) => {
            drop(held);
            ExitCode::from(code[0])
        }
        _ => {
            eprintln!("mini-shell-ssh: the member's resident shell ended during this line; whether it took effect is unknown (`history` shows what was kept)");
            ExitCode::from(70)
        }
    }
}
