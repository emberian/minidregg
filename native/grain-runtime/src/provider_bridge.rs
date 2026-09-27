//! Worker-local HTTP bridge. The worker has a private network namespace and
//! receives only a bind-mounted controller Unix socket, never provider egress.
use std::fs;
use std::io::{self, Read, Write};
use std::net::{Shutdown, TcpListener, TcpStream};
use std::os::unix::fs::FileTypeExt;
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

const MAX_HEADER: usize = 16_384;
const MAX_REQUEST: usize = 1_048_576 + MAX_HEADER;
const MAX_RESPONSE: usize = 8_388_608 + MAX_HEADER;
const MAX_CONNECTIONS: usize = 5;

#[derive(Clone, Copy)]
enum MessageKind {
    Request,
    Response,
}

fn header_name_valid(name: &str) -> bool {
    !name.is_empty()
        && name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"!#$%&'*+-.^_`|~".contains(&byte))
}

fn read_message<R: Read>(
    stream: &mut R,
    max_bytes: usize,
    deadline: Instant,
    kind: MessageKind,
) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    let header_end = loop {
        if Instant::now() >= deadline {
            return Err(io::Error::new(io::ErrorKind::TimedOut, "bridge deadline"));
        }
        let mut chunk = [0u8; 4096];
        match stream.read(&mut chunk) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "bridge header truncated",
                ))
            }
            Ok(n) => bytes.extend_from_slice(&chunk[..n]),
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
                ) =>
            {
                continue
            }
            Err(error) => return Err(error),
        }
        if bytes.len() > max_bytes
            || bytes.len() > MAX_HEADER && !bytes.windows(4).any(|w| w == b"\r\n\r\n")
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "bridge header bound",
            ));
        }
        if let Some(offset) = bytes.windows(4).position(|w| w == b"\r\n\r\n") {
            break offset + 4;
        }
    };
    if header_end > MAX_HEADER {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "bridge header bound",
        ));
    }
    let header = std::str::from_utf8(&bytes[..header_end])
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "bridge header encoding"))?;
    let mut lines = header[..header.len() - 4].split("\r\n");
    let first = lines.next().unwrap_or("");
    if match kind {
        MessageKind::Request => first != "POST /v1/chat/completions HTTP/1.1",
        MessageKind::Response => !first.starts_with("HTTP/1.1 "),
    } {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "bridge HTTP line",
        ));
    }
    let mut length = None;
    for line in lines {
        let Some((name, value)) = line.split_once(':') else {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "bridge header"));
        };
        if !header_name_valid(name) || value.bytes().any(|b| b == 0 || b == b'\r' || b == b'\n') {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "bridge header syntax",
            ));
        }
        if name.eq_ignore_ascii_case("transfer-encoding")
            || name.eq_ignore_ascii_case("content-encoding")
            || name.eq_ignore_ascii_case("expect")
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "bridge encoded message",
            ));
        }
        if name.eq_ignore_ascii_case("content-length") {
            if length.is_some()
                || value.trim().is_empty()
                || !value.trim().bytes().all(|b| b.is_ascii_digit())
            {
                return Err(io::Error::new(io::ErrorKind::InvalidData, "bridge length"));
            }
            length = Some(
                value
                    .trim()
                    .parse::<usize>()
                    .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "bridge length"))?,
            );
        }
    }
    let length =
        length.ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "bridge length absent"))?;
    let total = header_end
        .checked_add(length)
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "bridge length overflow"))?;
    if total > max_bytes || bytes.len() > total {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "bridge message bound",
        ));
    }
    while bytes.len() < total {
        if Instant::now() >= deadline {
            return Err(io::Error::new(io::ErrorKind::TimedOut, "bridge deadline"));
        }
        let mut chunk = [0u8; 16_384];
        let wanted = (total - bytes.len()).min(chunk.len());
        match stream.read(&mut chunk[..wanted]) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "bridge body truncated",
                ))
            }
            Ok(n) => bytes.extend_from_slice(&chunk[..n]),
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
                ) =>
            {
                continue
            }
            Err(error) => return Err(error),
        }
    }
    Ok(bytes)
}

fn write_bounded<W: Write>(stream: &mut W, bytes: &[u8], deadline: Instant) -> io::Result<()> {
    for chunk in bytes.chunks(16_384) {
        if Instant::now() >= deadline {
            return Err(io::Error::new(io::ErrorKind::TimedOut, "bridge deadline"));
        }
        stream.write_all(chunk)?;
    }
    Ok(())
}

fn proxy_one(mut client: TcpStream, socket: &Path, deadline: Instant) -> io::Result<()> {
    client.set_read_timeout(Some(Duration::from_secs(1)))?;
    client.set_write_timeout(Some(Duration::from_secs(1)))?;
    let request = read_message(&mut client, MAX_REQUEST, deadline, MessageKind::Request)?;
    let mut gateway = UnixStream::connect(socket)?;
    gateway.set_read_timeout(Some(Duration::from_secs(1)))?;
    gateway.set_write_timeout(Some(Duration::from_secs(1)))?;
    write_bounded(&mut gateway, &request, deadline)?;
    let response = read_message(&mut gateway, MAX_RESPONSE, deadline, MessageKind::Response)?;
    write_bounded(&mut client, &response, deadline)?;
    write_bounded(&mut gateway, b"1", deadline)?;
    let _ = client.shutdown(Shutdown::Both);
    Ok(())
}

fn run() -> Result<i32, String> {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    let [socket_flag, socket, port_flag, port, seconds_flag, seconds, separator, program, tail @ ..] =
        args.as_slice()
    else {
        return Err("bridge requires --socket PATH --port PORT --seconds N -- PROGRAM".into());
    };
    if socket_flag != "--socket"
        || port_flag != "--port"
        || seconds_flag != "--seconds"
        || separator != "--"
        || !program.starts_with("/agent/")
    {
        return Err("bridge arguments invalid".into());
    }
    let path = Path::new(socket);
    if path != Path::new("/run/mini-provider.sock")
        || !fs::symlink_metadata(path).is_ok_and(|meta| meta.file_type().is_socket())
    {
        return Err("bridge has no mounted provider socket".into());
    }
    let port: u16 = port.parse().map_err(|_| "invalid bridge port")?;
    let seconds: u64 = seconds.parse().map_err(|_| "invalid bridge lifetime")?;
    if port == 0 || !(1..=1800).contains(&seconds) {
        return Err("bridge port or lifetime outside profile".into());
    }
    let listener =
        TcpListener::bind(("127.0.0.1", port)).map_err(|e| format!("bridge loopback bind: {e}"))?;
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let deadline = Instant::now() + Duration::from_secs(seconds);
    let mut child = Command::new(program)
        .args(tail)
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn()
        .map_err(|e| format!("bridge worker spawn: {e}"))?;
    let active = Arc::new(AtomicUsize::new(0));
    loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|e| format!("bridge child wait: {e}"))?
        {
            return Ok(status.code().unwrap_or(128));
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            return Err("bridge worker deadline".into());
        }
        match listener.accept() {
            Ok((client, _)) => {
                if active.fetch_add(1, Ordering::SeqCst) >= MAX_CONNECTIONS {
                    active.fetch_sub(1, Ordering::SeqCst);
                    let _ = client.shutdown(Shutdown::Both);
                    continue;
                }
                let socket = path.to_path_buf();
                let active = active.clone();
                thread::spawn(move || {
                    let _ = proxy_one(client, &socket, deadline);
                    active.fetch_sub(1, Ordering::SeqCst);
                });
            }
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                thread::sleep(Duration::from_millis(20));
            }
            Err(error) => return Err(format!("bridge accept: {error}")),
        }
    }
}

fn main() {
    match run() {
        Ok(code) => std::process::exit(code),
        Err(error) => {
            eprintln!("grain provider bridge: {error}");
            std::process::exit(74);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bridge_requires_complete_bounded_content_length_frame() {
        let deadline = Instant::now() + Duration::from_secs(1);
        let bytes = b"POST /v1/chat/completions HTTP/1.1\r\nContent-Length: 3\r\n\r\nabc";
        assert_eq!(
            read_message(&mut &bytes[..], MAX_REQUEST, deadline, MessageKind::Request).unwrap(),
            bytes
        );
        for mut invalid in [
            b"POST / HTTP/1.1\r\nContent-Length: 4\r\n\r\nabc".as_slice(),
            b"POST / HTTP/1.1\r\nContent-Length: 3\r\nContent-Length: 3\r\n\r\nabc".as_slice(),
            b"POST / HTTP/1.1\r\nContent-Length: 999999999\r\n\r\n".as_slice(),
            b"POST /v1/chat/completions HTTP/1.1\r\nContent-Length: 0\r\nTransfer-Encoding: chunked\r\n\r\n".as_slice(),
        ] {
            assert!(read_message(&mut invalid, MAX_REQUEST, deadline, MessageKind::Request).is_err());
        }
    }
}
