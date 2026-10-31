//! A `mini` that runs another process's client commands in itself, one at a time
//! (`mini client-resident`): the apps worker's route binds, enrollments and share issues
//! are about a dozen client commands each, and a `mini` process per command started a
//! process, re-pinned the Host image, reconnected its consent and codec sessions and re-read
//! the workspace every time.
//!
//! The channel is the stream end the parent hands over as standard input (a socketpair): it is
//! moved off fd 0 at once and fd 0 becomes /dev/null, so no command can read the channel. Each
//! request is one frame of a JSON array of arguments (the command line after `mini`); each reply
//! is the exit code and the stdout and stderr `capture::argv` returns, byte for byte what the
//! child `mini` would have ended with. Commands run on this one thread (the descriptor swap of
//! `capture` is process-wide). A resident serves one Host socket pin (`main` refuses a second
//! one in a process serving several commands), so its parent keeps one resident per socket.
use std::ffi::OsString;
use std::io::{Read, Write};
use std::os::fd::FromRawFd;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};

/// A request or reply frame larger than this is refused (the worker's commands print a few KiB).
const MAX_FRAME: usize = 16 * 1024 * 1024;

fn read_frame(stream: &mut UnixStream) -> std::io::Result<Option<Vec<u8>>> {
    let mut width = [0u8; 4];
    match stream.read_exact(&mut width) {
        Err(error) if error.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(None),
        other => other?,
    }
    let size = u32::from_le_bytes(width) as usize;
    if size > MAX_FRAME {
        return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, "client resident frame exceeds bound"));
    }
    let mut body = vec![0; size];
    stream.read_exact(&mut body)?;
    Ok(Some(body))
}

fn write_frame(stream: &mut UnixStream, body: &[u8]) -> std::io::Result<()> {
    let size = u32::try_from(body.len()).ok().filter(|size| *size as usize <= MAX_FRAME)
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::InvalidData, "client resident frame exceeds bound"))?;
    stream.write_all(&size.to_le_bytes())?;
    stream.write_all(body)?;
    stream.flush()
}

/// The reply body: code, stdout length, stdout, stderr.
fn reply(code: u8, stdout: &[u8], stderr: &[u8]) -> Vec<u8> {
    let mut body = Vec::with_capacity(5 + stdout.len() + stderr.len());
    body.push(code);
    body.extend_from_slice(&(stdout.len() as u32).to_le_bytes());
    body.extend_from_slice(stdout);
    body.extend_from_slice(stderr);
    body
}

fn parse_reply(body: &[u8]) -> Result<(u8, Vec<u8>, Vec<u8>), String> {
    if body.len() < 5 {
        return Err("client resident reply is short".into());
    }
    let width = u32::from_le_bytes(body[1..5].try_into().expect("four bytes")) as usize;
    if 5 + width > body.len() {
        return Err("client resident reply stdout overruns".into());
    }
    Ok((body[0], body[5..5 + width].to_vec(), body[5 + width..].to_vec()))
}

/// `mini client-resident`: serve the parent's commands until it closes the channel.
pub(crate) fn serve() -> crate::Result<()> {
    // SAFETY: fd 0 is the parent's channel; it is duplicated above the standard streams with
    // close-on-exec, and fd 0 is pointed at /dev/null before any command runs.
    let channel = unsafe { libc::fcntl(0, libc::F_DUPFD_CLOEXEC, 3) };
    if channel < 0 {
        return Err(format!("client resident has no channel: {}", std::io::Error::last_os_error()));
    }
    let null = std::fs::File::open("/dev/null").map_err(|e| format!("cannot open /dev/null: {e}"))?;
    if unsafe { libc::dup2(std::os::fd::AsRawFd::as_raw_fd(&null), 0) } < 0 {
        return Err(format!("cannot detach standard input: {}", std::io::Error::last_os_error()));
    }
    let mut stream = unsafe { UnixStream::from_raw_fd(channel) };
    while let Some(request) = read_frame(&mut stream).map_err(|e| format!("client resident channel: {e}"))? {
        let body = match serde_json::from_slice::<Vec<String>>(&request) {
            Ok(argv) if !argv.is_empty() => {
                match crate::capture::argv(argv.into_iter().map(OsString::from).collect(), None) {
                    Ok((code, stdout, stderr)) => reply(code, &stdout, &stderr),
                    Err(error) => reply(1, b"", format!("mini: client resident could not run the command: {error}\n").as_bytes()),
                }
            }
            _ => reply(2, b"", b"mini: client resident request is not a nonempty JSON array of strings\n"),
        };
        write_frame(&mut stream, &body).map_err(|e| format!("client resident channel: {e}"))?;
    }
    Ok(())
}

/// The parent's side: one resident child and its channel. A command whose reply is lost is
/// reported as an error (never re-sent: its outcome is the command's own attempt record's, as a
/// child `mini` that died was), and the resident is dropped; the next command starts a fresh one.
pub(crate) struct Resident {
    mini: PathBuf,
    live: Option<(Child, UnixStream)>,
}

impl Resident {
    pub(crate) fn new(mini: &Path) -> Self {
        Resident { mini: mini.to_path_buf(), live: None }
    }

    fn start(&self) -> Result<(Child, UnixStream), String> {
        let (ours, theirs) = UnixStream::pair().map_err(|e| format!("client resident channel: {e}"))?;
        let child = Command::new(&self.mini)
            .arg("client-resident")
            .stdin(Stdio::from(std::os::fd::OwnedFd::from(theirs)))
            .stdout(Stdio::null())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|e| format!("cannot start {} client-resident: {e}", self.mini.display()))?;
        Ok((child, ours))
    }

    /// `mini ARGS...` in the resident: (exit code, stdout, stderr).
    pub(crate) fn run(&mut self, args: &[&str]) -> Result<(u8, Vec<u8>, Vec<u8>), String> {
        if self.live.is_none() {
            self.live = Some(self.start()?);
        }
        let (_, stream) = self.live.as_mut().expect("resident started");
        let request = serde_json::to_vec(args).map_err(|e| e.to_string())?;
        let answered = write_frame(stream, &request).and_then(|_| read_frame(stream));
        match answered {
            Ok(Some(body)) => parse_reply(&body),
            Ok(None) => {
                self.stop();
                Err(format!("client resident ended during `mini {}`; its outcome is the command's own attempt record", args.first().unwrap_or(&"")))
            }
            Err(error) => {
                self.stop();
                Err(format!("client resident lost `mini {}`: {error}; its outcome is the command's own attempt record", args.first().unwrap_or(&"")))
            }
        }
    }

    fn stop(&mut self) {
        if let Some((mut child, stream)) = self.live.take() {
            drop(stream);
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

impl Drop for Resident {
    fn drop(&mut self) {
        self.stop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn client_resident_replies_round_trip_code_and_both_streams() {
        let body = reply(3, b"{\"a\":1}\n", b"mini: refused\n");
        assert_eq!(parse_reply(&body).unwrap(), (3, b"{\"a\":1}\n".to_vec(), b"mini: refused\n".to_vec()));
        assert_eq!(parse_reply(&reply(0, b"", b"")).unwrap(), (0, Vec::new(), Vec::new()));
        assert!(parse_reply(&[0, 9, 0, 0, 0, b'x']).is_err());
    }
}
