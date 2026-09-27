//! Private, bounded operator endpoint for physical SPK host status.
//!
//! Version 1 deliberately exposes no launch or dispatch method while Mini's
//! special native lifecycle and checked-dispatch receivers are unfinished.
//! Requests contain no caller-supplied "accepted" flag or authority shortcut.

use crate::hostd::{Journal, Phase};
use serde::{Deserialize, Serialize};
use std::fs::{self, OpenOptions};
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

const PROTOCOL: &str = "mini-spk-hostd-v1";
// Native resource-client currently bounds one Host frame at 12,102,760 bytes.
// A future ingress method must check its own native bound before this envelope;
// this endpoint rejects oversize frames rather than truncating them.
const MAX_FRAME: usize = 12_102_760 + 4096;
const IO_DEADLINE: Duration = Duration::from_secs(10);

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    protocol: String,
    request_id: String,
    app: u64,
    generation: u64,
    op: String,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
struct Response {
    protocol: &'static str,
    request_id: String,
    outcome: &'static str,
    detail: &'static str,
    phase: Option<Phase>,
    unit: Option<String>,
    transaction_id: Option<String>,
    event_id: Option<String>,
}

fn valid_request_id(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn respond(journal: &Journal, bytes: &[u8]) -> io::Result<Vec<u8>> {
    let request: Request = serde_json::from_slice(bytes)?;
    if request.protocol != PROTOCOL || !valid_request_id(&request.request_id) {
        return Err(invalid("invalid hostd protocol or exact request identity"));
    }
    let mut response = Response {
        protocol: PROTOCOL,
        request_id: request.request_id,
        outcome: "unavailable",
        detail: "native lifecycle/dispatch route unavailable",
        phase: None,
        unit: None,
        transaction_id: None,
        event_id: None,
    };
    if request.op == "status" {
        match journal.read()? {
            Some(record)
                if record.app() == request.app && record.generation() == request.generation =>
            {
                response.outcome = "ok";
                response.detail = "exact durable physical state";
                response.phase = Some(record.phase);
                response.unit = Some(record.unit().to_owned());
                response.transaction_id = Some(record.transaction_id().to_owned());
                response.event_id = Some(record.event_id().to_owned());
            }
            Some(_) => {
                response.detail = "journal identity differs from request";
            }
            None => {
                response.detail = "no native-verified BEGIN recorded";
            }
        }
    } else if request.op != "begin" && request.op != "dispatch" {
        return Err(invalid("unknown hostd operation"));
    }
    serde_json::to_vec(&response).map_err(Into::into)
}

fn transfer(
    stream: &mut UnixStream,
    bytes: &mut [u8],
    write: bool,
    deadline: Instant,
) -> io::Result<()> {
    let mut offset = 0;
    stream.set_nonblocking(true)?;
    while offset < bytes.len() {
        if Instant::now() >= deadline {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "hostd frame deadline",
            ));
        }
        let result = if write {
            stream.write(&bytes[offset..])
        } else {
            stream.read(&mut bytes[offset..])
        };
        match result {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "hostd frame closed",
                ))
            }
            Ok(n) => offset += n,
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(2));
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
    }
    Ok(())
}

fn serve_connection(mut stream: UnixStream, journal: &Journal) -> io::Result<()> {
    let mut credential = unsafe { std::mem::zeroed::<libc::ucred>() };
    let mut length = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
    if unsafe {
        libc::getsockopt(
            stream.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            (&mut credential as *mut libc::ucred).cast(),
            &mut length,
        )
    } != 0
        || length as usize != std::mem::size_of::<libc::ucred>()
        || credential.uid != unsafe { libc::geteuid() }
    {
        return Err(io::Error::new(
            io::ErrorKind::PermissionDenied,
            "hostd peer UID refused",
        ));
    }
    let deadline = Instant::now() + IO_DEADLINE;
    let mut prefix = [0_u8; 4];
    transfer(&mut stream, &mut prefix, false, deadline)?;
    let size = u32::from_le_bytes(prefix) as usize;
    if size == 0 || size > MAX_FRAME {
        return Err(invalid("hostd request frame size refused"));
    }
    let mut payload = vec![0; size];
    transfer(&mut stream, &mut payload, false, deadline)?;
    let reply = respond(journal, &payload)?;
    if reply.len() > MAX_FRAME {
        return Err(invalid("hostd reply frame too large"));
    }
    let mut frame = Vec::with_capacity(reply.len() + 4);
    frame.extend_from_slice(&(reply.len() as u32).to_le_bytes());
    frame.extend_from_slice(&reply);
    transfer(&mut stream, &mut frame, true, deadline)
}

/// A same-UID, 0600 Unix socket inside an owner-private, protected directory.
/// An existing socket is never unlinked automatically: a second instance or
/// stale identity requires an explicit operator audit, not a path swap.
pub struct PrivateEndpoint {
    listener: UnixListener,
    socket: PathBuf,
    socket_dev: u64,
    socket_ino: u64,
    _lock: std::fs::File,
}

impl PrivateEndpoint {
    pub fn bind(directory: &Path, journal: &Journal) -> io::Result<Self> {
        // Journal::open validates protected ancestors, owner and 0700 leaf.
        if directory != journal.directory() {
            return Err(invalid("hostd socket/journal directory differs"));
        }
        let _ = Journal::open(directory)?;
        let _ = journal.read()?;
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(directory.join(".endpoint.lock"))?;
        let meta = lock.metadata()?;
        if !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
        {
            return Err(invalid("hostd endpoint lock identity drift"));
        }
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "hostd endpoint already active",
            ));
        }
        let socket = directory.join("hostd.sock");
        if fs::symlink_metadata(&socket).is_ok() {
            return Err(invalid("hostd socket already exists"));
        }
        let listener = UnixListener::bind(&socket)?;
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o600))?;
        let meta = fs::symlink_metadata(&socket)?;
        if !meta.file_type().is_socket() || meta.uid() != unsafe { libc::geteuid() } {
            return Err(invalid("hostd socket identity drift"));
        }
        Ok(Self {
            listener,
            socket,
            socket_dev: meta.dev(),
            socket_ino: meta.ino(),
            _lock: lock,
        })
    }

    pub fn serve(&self, journal: &Journal) -> io::Result<()> {
        loop {
            let (stream, _) = self.listener.accept()?;
            // Malformed or slow private peers cannot grant authority and must
            // not terminate the service. The deadline bounds each connection.
            let _ = serve_connection(stream, journal);
        }
    }
}

impl Drop for PrivateEndpoint {
    fn drop(&mut self) {
        if let Ok(meta) = fs::symlink_metadata(&self.socket) {
            if meta.dev() == self.socket_dev && meta.ino() == self.socket_ino {
                let _ = fs::remove_file(&self.socket);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::DirBuilderExt;

    fn scratch() -> PathBuf {
        let runtime = std::env::var("XDG_RUNTIME_DIR").expect("Linux user runtime dir");
        let path = Path::new(&runtime).join(format!("mini-spk-endpoint-{}", std::process::id()));
        fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
        path
    }

    #[test]
    fn request_id_and_exact_protocol_are_strict() {
        assert!(valid_request_id(&"a".repeat(64)));
        assert!(!valid_request_id(&"A".repeat(64)));
        assert!(!valid_request_id("short"));
        let valid = br#"{"protocol":"mini-spk-hostd-v1","request_id":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","app":91,"generation":2,"op":"status"}"#;
        let request: Request = serde_json::from_slice(valid).unwrap();
        assert_eq!(request.app, 91);
        assert!(serde_json::from_slice::<Request>(br#"{"op":"status","accepted":true}"#).is_err());
        let zero = br#"{"protocol":"mini-spk-hostd-v1","request_id":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","app":0,"generation":0,"op":"status"}"#;
        let zero: Request = serde_json::from_slice(zero).unwrap();
        assert_eq!((zero.app, zero.generation), (0, 0));
    }

    #[test]
    fn private_socket_refuses_second_instance_and_returns_exact_request_id() {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        let endpoint = PrivateEndpoint::bind(&path, &journal).unwrap();
        let original = fs::symlink_metadata(path.join("hostd.sock")).unwrap();
        assert_eq!(original.permissions().mode() & 0o777, 0o600);
        assert!(PrivateEndpoint::bind(&path, &journal).is_err());
        assert_eq!(
            fs::symlink_metadata(path.join("hostd.sock")).unwrap().ino(),
            original.ino()
        );
        let mut client = UnixStream::connect(path.join("hostd.sock")).unwrap();
        let server = std::thread::spawn(move || {
            let (peer, _) = endpoint.listener.accept().unwrap();
            serve_connection(peer, &journal).unwrap();
            endpoint
        });
        let request = format!("{{\"protocol\":\"{PROTOCOL}\",\"request_id\":\"{}\",\"app\":91,\"generation\":2,\"op\":\"status\"}}", "a".repeat(64));
        client
            .write_all(&(request.len() as u32).to_le_bytes())
            .unwrap();
        client.write_all(request.as_bytes()).unwrap();
        let mut prefix = [0_u8; 4];
        client.read_exact(&mut prefix).unwrap();
        let mut reply = vec![0; u32::from_le_bytes(prefix) as usize];
        client.read_exact(&mut reply).unwrap();
        let value: serde_json::Value = serde_json::from_slice(&reply).unwrap();
        assert_eq!(value["requestId"], "a".repeat(64));
        assert_eq!(value["outcome"], "unavailable");
        drop(server.join().unwrap());
        assert!(!path.join("hostd.sock").exists());
        fs::remove_dir_all(path).unwrap();
    }
}
