//! `mini line-resident LISTEN CONFIG`: one member's resident shell for the ssh forced command.
//!
//! The wrapper used to exec a fresh `mini` for every `ssh member@box 'VERB ...'`: a process
//! start, dynamic loading, relocation and page faults, a workspace load and new connections to
//! the member's consent and codec residents, every time. `mini-line` (`src/bin/mini_line.rs`)
//! instead holds the member's call slot itself and hands the line to the resident for that slot:
//! its `mini` argument vector, and its standard input, output and error as descriptors
//! (`SCM_RIGHTS`). The resident runs the command in this process (`capture::argv`) with those
//! descriptors as its streams, so output streams to the member as it is printed, and answers
//! with the exit code.
//!
//! One resident per call slot (two per member), each serving one line at a time: the slot the
//! client holds is the resident it may use. It never idles out. It ends when its socket is
//! unlinked or replaced, when the Store its settings name (`storageRoot`) is removed, or when it
//! is superseded: another file at its executable path or other bytes at its settings path.
use std::ffi::OsString;
use std::fs::{self, File};
use std::io::{Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::ffi::OsStringExt;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::time::Duration;

const ARGS_MAX: u32 = 4096;
const BYTES_MAX: usize = 4 << 20;

type Identity = (u64, u64, u64, i64, i64, i64, i64);

fn identity(meta: &fs::Metadata) -> Identity {
    (meta.dev(), meta.ino(), meta.size(), meta.mtime(), meta.mtime_nsec(), meta.ctime(), meta.ctime_nsec())
}

fn null_streams() -> crate::Result<()> {
    let null = fs::OpenOptions::new().read(true).write(true).open("/dev/null").map_err(|e| e.to_string())?;
    for fd in 0..3 {
        if unsafe { libc::dup2(null.as_raw_fd(), fd) } < 0 {
            return Err(std::io::Error::last_os_error().to_string());
        }
    }
    Ok(())
}

/// One request: the descriptors for standard input, output and error, then the argument vector
/// (a count, then each argument; every number a big-endian u32).
fn receive(stream: &mut UnixStream) -> crate::Result<([OwnedFd; 3], Vec<OsString>)> {
    let mut first = [0u8; 4];
    let mut control = [0u8; 64];
    let mut iov = libc::iovec { iov_base: first.as_mut_ptr().cast(), iov_len: first.len() };
    let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
    message.msg_iov = &mut iov;
    message.msg_iovlen = 1;
    message.msg_control = control.as_mut_ptr().cast();
    message.msg_controllen = control.len() as _;
    let read = unsafe { libc::recvmsg(stream.as_raw_fd(), &mut message, 0) };
    if read < 0 {
        return Err(format!("line-resident: {}", std::io::Error::last_os_error()));
    }
    let mut fds = Vec::new();
    let mut header = unsafe { libc::CMSG_FIRSTHDR(&message) };
    while !header.is_null() {
        let (level, kind) = unsafe { ((*header).cmsg_level, (*header).cmsg_type) };
        if level == libc::SOL_SOCKET && kind == libc::SCM_RIGHTS {
            let data = unsafe { libc::CMSG_DATA(header) } as *const i32;
            let count = (unsafe { (*header).cmsg_len } as usize - unsafe { libc::CMSG_LEN(0) } as usize) / 4;
            for index in 0..count {
                let fd = unsafe { *data.add(index) };
                unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) };
                fds.push(unsafe { OwnedFd::from_raw_fd(fd) });
            }
        }
        header = unsafe { libc::CMSG_NXTHDR(&message, header) };
    }
    let fds: [OwnedFd; 3] = fds.try_into().map_err(|_| "line-resident: a request carries exactly three descriptors")?;
    let mut got = read as usize;
    while got < 4 {
        let more = stream.read(&mut first[got..]).map_err(|e| e.to_string())?;
        if more == 0 {
            return Err("line-resident: truncated request".into());
        }
        got += more;
    }
    let word = |stream: &mut UnixStream| -> crate::Result<u32> {
        let mut bytes = [0u8; 4];
        stream.read_exact(&mut bytes).map_err(|e| e.to_string())?;
        Ok(u32::from_be_bytes(bytes))
    };
    let count = u32::from_be_bytes(first);
    if count == 0 || count > ARGS_MAX {
        return Err("line-resident: argument count out of bounds".into());
    }
    let mut argv = Vec::with_capacity(count as usize);
    let mut total = 0usize;
    for _ in 0..count {
        let length = word(stream)? as usize;
        total += length;
        if total > BYTES_MAX {
            return Err("line-resident: request exceeds 4 MiB".into());
        }
        let mut bytes = vec![0u8; length];
        stream.read_exact(&mut bytes).map_err(|e| e.to_string())?;
        argv.push(OsString::from_vec(bytes));
    }
    Ok((fds, argv))
}

/// Run one request with its own streams; the exit code, or None when it could not be run.
fn run(fds: [OwnedFd; 3], argv: Vec<OsString>) -> Option<u8> {
    let [input, output, error] = fds;
    if unsafe { libc::dup2(input.as_raw_fd(), 0) } < 0 {
        return None;
    }
    drop(input);
    let ended = crate::capture::argv(argv, Some((File::from(output), File::from(error))));
    let _ = null_streams();
    ended.ok().map(|(code, _, _)| code)
}

fn settings(config: &Path) -> (Option<Vec<u8>>, Option<PathBuf>) {
    let Ok(bytes) = fs::read(config) else { return (None, None) };
    let root = serde_json::from_slice::<serde_json::Value>(&bytes).ok()
        .and_then(|v| v.get("storageRoot").and_then(|r| r.as_str()).map(PathBuf::from))
        .filter(|root| root.is_absolute() && fs::symlink_metadata(root).is_ok());
    (Some(bytes), root)
}

#[cfg(unix)]
pub(crate) fn serve(listen: PathBuf, config: PathBuf) -> crate::Result<()> {
    if !listen.is_absolute() || !(config.as_os_str().is_empty() || config.is_absolute()) {
        return Err("line-resident: LISTEN and CONFIG must be absolute".into());
    }
    let executable = std::env::args_os().next().map(PathBuf::from).filter(|p| p.is_absolute())
        .ok_or("line-resident: start it by its absolute path")?;
    let started = identity(&fs::metadata(&executable).map_err(|e| format!("{}: {e}", executable.display()))?);
    // The starter waits for this process's exit 0, then for the socket.
    if !mini_sdk::consent::daemonize()? {
        return Ok(());
    }
    null_streams()?;
    let lock_path = listen.with_extension("lock");
    let lock = fs::OpenOptions::new().create(true).append(true).open(&lock_path)
        .map_err(|e| format!("{}: {e}", lock_path.display()))?;
    fs::set_permissions(&lock_path, fs::Permissions::from_mode(0o600)).map_err(|e| e.to_string())?;
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Ok(()); // another resident serves this slot
    }
    mini_sdk::private::clear_stale_socket(&listen)?;
    let (config_bytes, store_root) = if config.as_os_str().is_empty() { (None, None) } else { settings(&config) };
    let listener = UnixListener::bind(&listen).map_err(|e| format!("line-resident {}: {e}", listen.display()))?;
    fs::set_permissions(&listen, fs::Permissions::from_mode(0o600)).map_err(|e| e.to_string())?;
    let socket = fs::symlink_metadata(&listen).map_err(|e| e.to_string())?;
    let socket = (socket.dev(), socket.ino());
    let pid_path = listen.with_extension("pid");
    fs::write(&pid_path, format!("{}\n", std::process::id())).map_err(|e| format!("{}: {e}", pid_path.display()))?;
    let ours = |path: &Path| fs::symlink_metadata(path).is_ok_and(|m| (m.dev(), m.ino()) == socket);
    let ended = || -> crate::Result<()> {
        if ours(&listen) {
            let _ = fs::remove_file(&listen);
            let _ = fs::remove_file(&pid_path);
        }
        Ok(())
    };
    loop {
        let mut ready = libc::pollfd { fd: listener.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        if unsafe { libc::poll(&mut ready, 1, 1000) } == 0 {
            let superseded = fs::metadata(&executable).map_or(true, |m| identity(&m) != started)
                || config_bytes.as_ref().is_some_and(|bytes| fs::read(&config).is_ok_and(|now| &now != bytes))
                || store_root.as_ref().is_some_and(|root| fs::symlink_metadata(root).is_err());
            if !ours(&listen) || superseded {
                return ended();
            }
            continue;
        }
        let Ok((mut stream, _)) = listener.accept() else { continue };
        let _ = stream.set_read_timeout(Some(Duration::from_secs(10)));
        let Ok((fds, argv)) = receive(&mut stream) else { continue };
        let _ = stream.set_read_timeout(None);
        if let Some(code) = run(fds, argv) {
            let _ = stream.write_all(&[code]);
        }
    }
}

/// The resident's own path and its settings, from `mini line-resident LISTEN CONFIG`.
pub(crate) fn main_args() -> crate::Result<(PathBuf, PathBuf)> {
    let mut args = std::env::args_os().skip(2);
    match (args.next(), args.next(), args.next()) {
        (Some(listen), Some(config), None) => Ok((PathBuf::from(listen), PathBuf::from(config))),
        _ => Err("usage: mini line-resident LISTEN CONFIG".into()),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn a_request_carries_three_descriptors_and_its_arguments() {
        use std::os::fd::AsRawFd;
        let (mut client, mut server) = std::os::unix::net::UnixStream::pair().unwrap();
        let argv = ["shell", "--line", "whoami"];
        let mut body = (argv.len() as u32).to_be_bytes().to_vec();
        for word in argv {
            body.extend((word.len() as u32).to_be_bytes());
            body.extend(word.as_bytes());
        }
        send(&mut client, &body, [0, 1, 2]);
        let (fds, received) = super::receive(&mut server).unwrap();
        assert_eq!(received, argv.iter().map(std::ffi::OsString::from).collect::<Vec<_>>());
        assert!(fds.iter().all(|fd| fd.as_raw_fd() > 2));
    }

    pub(super) fn send(stream: &mut std::os::unix::net::UnixStream, body: &[u8], fds: [i32; 3]) {
        use std::os::fd::AsRawFd;
        let space = unsafe { libc::CMSG_SPACE(12) } as usize;
        let mut control = vec![0u8; space];
        let mut iov = libc::iovec { iov_base: body.as_ptr() as *mut _, iov_len: body.len() };
        let mut message: libc::msghdr = unsafe { std::mem::zeroed() };
        message.msg_iov = &mut iov;
        message.msg_iovlen = 1;
        message.msg_control = control.as_mut_ptr().cast();
        message.msg_controllen = space as _;
        unsafe {
            let header = libc::CMSG_FIRSTHDR(&message);
            (*header).cmsg_level = libc::SOL_SOCKET;
            (*header).cmsg_type = libc::SCM_RIGHTS;
            (*header).cmsg_len = libc::CMSG_LEN(12) as _;
            std::ptr::copy_nonoverlapping(fds.as_ptr(), libc::CMSG_DATA(header) as *mut i32, 3);
            assert_eq!(libc::sendmsg(stream.as_raw_fd(), &message, 0), body.len() as isize);
        }
    }
}
