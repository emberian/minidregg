//! Bounded framing shared by the local socket and the Lean host's stdio service.
use std::fs;
use std::fs::OpenOptions;
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const MAX_FRAME: usize = 1_048_576;

fn read_config(path: &Path) -> Result<Vec<u8>, String> {
    let file = fs::File::open(path)
        .map_err(|e| format!("cannot read host config {}: {e}", path.display()))?;
    let mut bytes = Vec::new();
    file.take(65_537)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("cannot read host config {}: {e}", path.display()))?;
    if bytes.len() > 65_536 {
        return Err("host config exceeds socket pin bound".to_owned());
    }
    Ok(bytes)
}

fn read_frame<R: Read>(reader: &mut R) -> io::Result<Option<Vec<u8>>> {
    let mut prefix = [0u8; 4];
    let mut read = 0;
    while read < prefix.len() {
        match reader.read(&mut prefix[read..])? {
            0 if read == 0 => return Ok(None),
            0 => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "truncated frame length",
                ))
            }
            n => read += n,
        }
    }
    let size = u32::from_le_bytes(prefix) as usize;
    if !(1..=MAX_FRAME).contains(&size) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid frame length",
        ));
    }
    let mut frame = vec![0; size];
    reader.read_exact(&mut frame)?;
    Ok(Some(frame))
}

fn write_frame<W: Write>(writer: &mut W, frame: &[u8]) -> io::Result<()> {
    if !(1..=MAX_FRAME).contains(&frame.len()) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "invalid frame length",
        ));
    }
    writer.write_all(&(frame.len() as u32).to_le_bytes())?;
    writer.write_all(frame)?;
    writer.flush()
}

struct DeadlineRead<'a> {
    stream: &'a mut UnixStream,
    deadline: Instant,
}

#[repr(C)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}

#[cfg(target_os = "macos")]
unsafe extern "C" {
    fn poll(fds: *mut PollFd, count: u32, timeout: i32) -> i32;
}
#[cfg(not(target_os = "macos"))]
unsafe extern "C" {
    fn poll(fds: *mut PollFd, count: usize, timeout: i32) -> i32;
}
unsafe extern "C" {
    fn fcntl(fd: i32, command: i32, ...) -> i32;
}

fn set_nonblocking<F: AsRawFd>(file: &F) -> io::Result<()> {
    const F_GETFL: i32 = 3;
    const F_SETFL: i32 = 4;
    #[cfg(target_os = "macos")]
    const O_NONBLOCK: i32 = 0x0004;
    #[cfg(not(target_os = "macos"))]
    const O_NONBLOCK: i32 = 0x0800;
    let flags = unsafe { fcntl(file.as_raw_fd(), F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    if unsafe { fcntl(file.as_raw_fd(), F_SETFL, flags | O_NONBLOCK) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

struct DeadlinePipe<'a, R: Read + AsRawFd> {
    reader: &'a mut R,
    deadline: Instant,
}

impl<R: Read + AsRawFd> Read for DeadlinePipe<'_, R> {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        loop {
            let remaining = self.deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "host reply deadline",
                ));
            }
            let mut fd = PollFd {
                fd: self.reader.as_raw_fd(),
                events: 1,
                revents: 0,
            };
            let milliseconds = remaining.as_millis().min(i32::MAX as u128) as i32;
            let result = unsafe { poll(&mut fd, 1, milliseconds.max(1)) };
            if result > 0 {
                return self.reader.read(bytes);
            }
            if result < 0 {
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::Interrupted {
                    return Err(error);
                }
            }
        }
    }
}

struct DeadlinePipeWrite<'a, W: Write + AsRawFd> {
    writer: &'a mut W,
    deadline: Instant,
}

impl<W: Write + AsRawFd> Write for DeadlinePipeWrite<'_, W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        loop {
            let remaining = self.deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "host request write deadline",
                ));
            }
            let mut fd = PollFd {
                fd: self.writer.as_raw_fd(),
                events: 4,
                revents: 0,
            };
            let milliseconds = remaining.as_millis().min(i32::MAX as u128) as i32;
            let result = unsafe { poll(&mut fd, 1, milliseconds.max(1)) };
            if result > 0 {
                match self.writer.write(bytes) {
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => continue,
                    other => return other,
                }
            }
            if result < 0 {
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::Interrupted {
                    return Err(error);
                }
            }
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

impl Read for DeadlineRead<'_> {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        let remaining = self.deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "socket frame deadline",
            ));
        }
        self.stream.set_read_timeout(Some(remaining))?;
        self.stream.read(bytes)
    }
}

/// A failed write or read leaves the request's execution status unknown. Callers
/// retain the original signed call and use historical lookup before resubmission.
pub fn invoke(
    socket: &Path,
    config: &Path,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>, String> {
    let config = read_config(config)?;
    let mut stream = UnixStream::connect(socket)
        .map_err(|e| format!("cannot connect to {}: {e}", socket.display()))?;
    stream
        .set_write_timeout(Some(Duration::from_secs(10)))
        .map_err(|e| format!("cannot set socket write deadline: {e}"))?;
    let mut frame = Vec::with_capacity(payload.len() + config.len() + 6);
    frame.push(1); // local socket envelope version
    frame.extend_from_slice(&(config.len() as u32).to_le_bytes());
    frame.extend_from_slice(&config);
    frame.push(operation);
    frame.extend_from_slice(payload);
    write_frame(&mut stream, &frame).map_err(|e| format!("uncertain host request write: {e}"))?;
    let reply = read_frame(&mut DeadlineRead {
        stream: &mut stream,
        deadline: Instant::now() + Duration::from_secs(600),
    })
    .map_err(|e| format!("uncertain host response read: {e}"))?
    .ok_or_else(|| "uncertain host response: connection closed".to_owned())?;
    if reply[0] == 254 {
        return Err(format!(
            "socket rejected request: {}",
            String::from_utf8_lossy(&reply[1..])
        ));
    }
    if reply[0] != operation && reply[0] != 255 {
        return Err(format!(
            "uncertain host response: unexpected operation {}",
            reply[0]
        ));
    }
    Ok(reply)
}

/// The socket directory must be owned by this account and inaccessible to
/// others. This closes the interval between bind and chmod on the socket.
pub fn serve(socket: &Path, host: &Path, config: &Path) -> Result<(), String> {
    let config_bytes = read_config(config)?;
    let parent = socket
        .parent()
        .ok_or("socket requires a parent directory")?;
    let metadata = fs::metadata(parent)
        .map_err(|e| format!("cannot inspect socket directory {}: {e}", parent.display()))?;
    if !metadata.is_dir() || metadata.uid() != effective_uid() || metadata.mode() & 0o077 != 0 {
        return Err(format!(
            "socket directory {} must be owned by this user with mode 0700",
            parent.display()
        ));
    }
    if socket.exists() {
        return Err(format!("refusing to replace socket {}", socket.display()));
    }
    let listener =
        UnixListener::bind(socket).map_err(|e| format!("cannot bind {}: {e}", socket.display()))?;
    struct SocketGuard<'a>(&'a Path);
    impl Drop for SocketGuard<'_> {
        fn drop(&mut self) {
            let _ = fs::remove_file(self.0);
        }
    }
    let _guard = SocketGuard(socket);
    fs::set_permissions(socket, fs::Permissions::from_mode(0o600))
        .map_err(|e| format!("cannot protect socket {}: {e}", socket.display()))?;
    let pinned_config = socket.with_extension("config");
    let mut config_file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&pinned_config)
        .map_err(|e| {
            format!(
                "cannot create pinned config {}: {e}",
                pinned_config.display()
            )
        })?;
    struct ConfigGuard<'a>(&'a Path);
    impl Drop for ConfigGuard<'_> {
        fn drop(&mut self) {
            let _ = fs::remove_file(self.0);
        }
    }
    let _config_guard = ConfigGuard(&pinned_config);
    config_file
        .write_all(&config_bytes)
        .and_then(|()| config_file.sync_all())
        .map_err(|e| {
            format!(
                "cannot write pinned config {}: {e}",
                pinned_config.display()
            )
        })?;
    let child = Command::new(host)
        .arg(&pinned_config)
        .arg("stdio")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot start host {}: {e}", host.display()))?;
    struct HostGuard(std::process::Child);
    impl Drop for HostGuard {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let mut host_guard = HostGuard(child);
    let mut input = host_guard.0.stdin.take().ok_or("host stdin unavailable")?;
    let mut output = host_guard
        .0
        .stdout
        .take()
        .ok_or("host stdout unavailable")?;
    set_nonblocking(&input).map_err(|e| format!("cannot bound host input pipe: {e}"))?;
    eprintln!(
        "mini: serving {} with host process {}",
        socket.display(),
        host_guard.0.id()
    );
    for accepted in listener.incoming() {
        let mut stream = accepted.map_err(|e| format!("socket accept failed: {e}"))?;
        stream
            .set_write_timeout(Some(Duration::from_secs(10)))
            .map_err(|e| format!("cannot set client write deadline: {e}"))?;
        let envelope = match read_frame(&mut DeadlineRead {
            stream: &mut stream,
            deadline: Instant::now() + Duration::from_secs(10),
        }) {
            Ok(Some(frame)) => frame,
            Ok(None) => continue,
            Err(e) => {
                eprintln!("mini: discarded invalid socket frame: {e}");
                continue;
            }
        };
        let config_length = if envelope.len() >= 5 && envelope[0] == 1 {
            u32::from_le_bytes(envelope[1..5].try_into().unwrap()) as usize
        } else {
            usize::MAX
        };
        let end = config_length.checked_add(5);
        if config_length != config_bytes.len()
            || end.and_then(|end| envelope.get(5..end)) != Some(config_bytes.as_slice())
            || end.is_none_or(|end| envelope.len() <= end)
        {
            let _ = write_frame(
                &mut stream,
                b"\xfeconfig pin mismatch or invalid socket envelope",
            );
            continue;
        }
        let request = &envelope[end.unwrap()..];
        if request[0] > 11 {
            let _ = write_frame(&mut stream, b"\xfeoperation unavailable on public socket");
            continue;
        }
        write_frame(
            &mut DeadlinePipeWrite {
                writer: &mut input,
                deadline: Instant::now() + Duration::from_secs(30),
            },
            &request,
        )
        .map_err(|e| format!("host request status uncertain: {e}"))?;
        let reply = read_frame(&mut DeadlinePipe {
            reader: &mut output,
            deadline: Instant::now() + Duration::from_secs(600),
        })
        .map_err(|e| format!("host request status uncertain: {e}"))?
        .ok_or_else(|| "host closed during request; status uncertain".to_owned())?;
        if let Err(error) = write_frame(&mut stream, &reply) {
            eprintln!("mini: client lost host reply; status uncertain: {error}");
        }
    }
    Ok(())
}

fn effective_uid() -> u32 {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    unsafe { geteuid() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    struct SmallReader<'a> {
        bytes: &'a [u8],
    }
    impl Read for SmallReader<'_> {
        fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
            let count = out.len().min(1).min(self.bytes.len());
            out[..count].copy_from_slice(&self.bytes[..count]);
            self.bytes = &self.bytes[count..];
            Ok(count)
        }
    }

    #[test]
    fn fragmented_frames_are_reassembled_and_truncation_is_uncertain() {
        let mut wire = Vec::new();
        write_frame(&mut wire, &[2, 0, 255, 7]).unwrap();
        assert_eq!(
            read_frame(&mut SmallReader { bytes: &wire }).unwrap(),
            Some(vec![2, 0, 255, 7])
        );
        assert_eq!(
            read_frame(&mut SmallReader { bytes: &wire[..6] })
                .unwrap_err()
                .kind(),
            io::ErrorKind::UnexpectedEof
        );
        assert!(read_frame(&mut SmallReader {
            bytes: &[0, 0, 0, 0]
        })
        .is_err());
    }

    #[test]
    fn socket_invocation_handles_fragmented_reply_and_marks_lost_reply_uncertain() {
        let directory = std::env::temp_dir().join(format!(
            "mini-transport-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let socket = directory.join("test.sock");
        let config = directory.join("config.json");
        fs::write(&config, b"config").unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        let thread = thread::spawn(move || {
            let (mut first, _) = listener.accept().unwrap();
            assert_eq!(
                read_frame(&mut first).unwrap(),
                Some([vec![1, 6, 0, 0, 0], b"config".to_vec(), vec![2, 42]].concat())
            );
            let mut reply = Vec::new();
            write_frame(&mut reply, &[2, 7, 8]).unwrap();
            for byte in reply {
                first.write_all(&[byte]).unwrap();
            }
            let (mut second, _) = listener.accept().unwrap();
            assert_eq!(
                read_frame(&mut second).unwrap(),
                Some([vec![1, 6, 0, 0, 0], b"config".to_vec(), vec![2, 42]].concat())
            );
        });
        assert_eq!(invoke(&socket, &config, 2, &[42]).unwrap(), vec![2, 7, 8]);
        assert!(invoke(&socket, &config, 2, &[42])
            .unwrap_err()
            .contains("uncertain"));
        thread.join().unwrap();
        fs::remove_file(socket).unwrap();
        fs::remove_file(config).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn host_pipe_deadline_bounds_missing_reply() {
        let (mut receiver, _writer) = UnixStream::pair().unwrap();
        let error = read_frame(&mut DeadlinePipe {
            reader: &mut receiver,
            deadline: Instant::now() + Duration::from_millis(20),
        })
        .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    }

    #[test]
    fn host_pipe_deadline_bounds_stalled_request_write() {
        let (mut writer, _reader) = UnixStream::pair().unwrap();
        set_nonblocking(&writer).unwrap();
        let error = write_frame(
            &mut DeadlinePipeWrite {
                writer: &mut writer,
                deadline: Instant::now() + Duration::from_millis(20),
            },
            &vec![7; MAX_FRAME],
        )
        .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    }
}
