//! The wire of `mini command-resident` (resource-client `capture::serve`): one client process
//! that runs many `mini` commands for one caller, each a frame instead of a fresh process. This
//! is the one encoding of a request and the one reader of a reply; the grain controller's custody
//! gate and the web body's shell pool are its callers.
//!
//! Request (big-endian u32 lengths): the argument count, each argument's length and bytes; the
//! command's standard input as a length and bytes; then the path the command's stdout goes to and
//! the path its stderr goes to, each a length and bytes (empty: captured and carried back in the
//! reply). A named file is opened for appending (created 0600, never through a symlink), so its
//! caller can read what was printed so far while the command still runs, and both may name one
//! file. Reply: the exit code (one byte), then stdout and stderr, each a length and bytes (empty
//! for a stream that went to a named file).
use std::ffi::OsStr;
use std::io::{self, Read};
use std::os::fd::AsRawFd;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::process::{ExitStatus, Output};
use std::time::{Duration, Instant};

/// One command for the resident.
pub struct Request<'a> {
    pub arguments: &'a [&'a OsStr],
    pub stdin: &'a [u8],
    pub stdout: Option<&'a Path>,
    pub stderr: Option<&'a Path>,
}

fn field(frame: &mut Vec<u8>, bytes: &[u8]) {
    frame.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
    frame.extend_from_slice(bytes);
}

/// The request frame.
pub fn frame(request: &Request<'_>) -> Vec<u8> {
    let mut frame = Vec::new();
    frame.extend_from_slice(&(request.arguments.len() as u32).to_be_bytes());
    for argument in request.arguments {
        field(&mut frame, argument.as_bytes());
    }
    field(&mut frame, request.stdin);
    field(&mut frame, request.stdout.map(|p| p.as_os_str().as_bytes()).unwrap_or(b""));
    field(&mut frame, request.stderr.map(|p| p.as_os_str().as_bytes()).unwrap_or(b""));
    frame
}

/// The resident's reply, waiting on the pipe itself (poll) until `deadline`; each carried stream
/// at most `bound` bytes. A timeout is `TimedOut`, a pipe that ends first `UnexpectedEof`.
pub fn read_reply(pipe: &mut impl ReadFd, deadline: Instant, bound: usize) -> io::Result<Output> {
    let mut bytes = Vec::new();
    loop {
        if let Some(output) = parse_reply(&bytes, bound)? {
            return Ok(output);
        }
        let left = deadline.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err(io::Error::new(io::ErrorKind::TimedOut, "the resident client did not answer before its deadline"));
        }
        let mut poll = libc::pollfd { fd: pipe.raw_fd(), events: libc::POLLIN, revents: 0 };
        let wait = left.as_millis().min(i32::MAX as u128) as i32;
        match unsafe { libc::poll(&mut poll, 1, wait.max(1)) } {
            0 => continue,
            n if n < 0 => {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            _ => {}
        }
        let mut chunk = [0u8; 65536];
        match pipe.read(&mut chunk) {
            Ok(0) => return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "the resident client ended before its reply")),
            Ok(count) => bytes.extend_from_slice(&chunk[..count]),
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
    }
}

/// A pipe `read_reply` can wait on.
pub trait ReadFd: Read {
    fn raw_fd(&self) -> i32;
}
impl<T: Read + AsRawFd> ReadFd for T {
    fn raw_fd(&self) -> i32 {
        self.as_raw_fd()
    }
}

fn parse_reply(bytes: &[u8], bound: usize) -> io::Result<Option<Output>> {
    let Some((&code, mut rest)) = bytes.split_first() else { return Ok(None) };
    let mut streams = Vec::with_capacity(2);
    for _ in 0..2 {
        let Some(length) = rest.get(..4) else { return Ok(None) };
        let length = u32::from_be_bytes(length.try_into().expect("four bytes")) as usize;
        if length > bound {
            return Err(io::Error::other("the resident client's reply exceeded its capture bound"));
        }
        let Some(stream) = rest.get(4..4 + length) else { return Ok(None) };
        streams.push(stream.to_vec());
        rest = &rest[4 + length..];
    }
    if !rest.is_empty() {
        return Err(io::Error::other("the resident client wrote past its reply"));
    }
    let stderr = streams.pop().expect("two streams");
    let stdout = streams.pop().expect("two streams");
    Ok(Some(Output { status: ExitStatus::from_raw(i32::from(code) << 8), stdout, stderr }))
}

/// Kill a resident's process group (it leads its own) and its leader.
pub fn kill_group(child: &mut std::process::Child) {
    unsafe {
        libc::kill(-(child.id() as libc::pid_t), libc::SIGKILL);
    }
    let _ = child.kill();
}

/// End an idle resident: its input closes, it exits at the frame boundary, and it is reaped,
/// killed with its group after `grace`.
pub fn retire(mut child: std::process::Child, requests: std::process::ChildStdin, grace: Duration) -> io::Result<()> {
    drop(requests);
    let start = Instant::now();
    while child.try_wait()?.is_none() {
        if start.elapsed() >= grace {
            kill_group(&mut child);
            child.wait()?;
            break;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frames_and_replies_are_exact() {
        let f = frame(&Request { arguments: &[OsStr::new("a"), OsStr::new("bc")], stdin: b"in", stdout: Some(Path::new("/o")), stderr: None });
        assert_eq!(f, [&2u32.to_be_bytes()[..], &1u32.to_be_bytes(), b"a", &2u32.to_be_bytes(), b"bc",
            &2u32.to_be_bytes(), b"in", &2u32.to_be_bytes(), b"/o", &0u32.to_be_bytes()].concat());
        let reply = [&[3u8][..], &2u32.to_be_bytes(), b"ok", &0u32.to_be_bytes()].concat();
        let output = parse_reply(&reply, 16).unwrap().unwrap();
        assert_eq!((output.status.code(), output.stdout, output.stderr), (Some(3), b"ok".to_vec(), Vec::new()));
        assert!(parse_reply(&reply[..4], 16).unwrap().is_none());
        assert!(parse_reply(&reply, 1).is_err());
    }
}
