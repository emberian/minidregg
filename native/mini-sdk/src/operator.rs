//! Client of the operator socket (`transport.rs` `invoke_inner`, `exchange_unix`).
//!
//! Request frame: `u32(len) ‖ version(1 | 2) ‖ u32(len(config)) ‖ config ‖ hostSha256[32] (v2) ‖
//! op ‖ payload`. Reply frame: `u32(len) ‖ op | 255 (Host refusal, encoded outcome) | 254
//! (the socket never forwarded the request)`. Every failure is classified as certainly-unsent
//! or uncertain; nothing in between is invented.
use std::io::{Read, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::Result;

pub const HOST_MAX_FRAME: usize = 12_102_760;
pub const MAX_CONFIG: usize = 65_536;

/// Operator-socket operations the SDK drives (`main.rs` `socket_process`).
pub mod op {
    pub const PREPARE: u8 = 1;
    pub const SUBMIT: u8 = 2;
    pub const LOOKUP: u8 = 3;
    pub const CHALLENGE: u8 = 4;
    pub const QUERY: u8 = 5;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Reply {
    /// The Host answered `op` with this body.
    Answer(Vec<u8>),
    /// The Host refused; the body is its encoded outcome (decode with `inspect outcome`).
    Refused(Vec<u8>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Failure {
    /// Certainly never reached the Host: connect failed, or the socket answered 254.
    Unsent(String),
    /// The request may have reached the Host; its decision is unknown.
    Uncertain(String),
}

pub struct Operator {
    pub socket: PathBuf,
    config: Vec<u8>,
    host_sha256: Option<[u8; 32]>,
    pub read_deadline: Duration,
}

/// Build the request frame body (without the outer length prefix).
pub fn request(config: &[u8], host_sha256: Option<&[u8; 32]>, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
    if config.len() > MAX_CONFIG {
        return Err("host config exceeds socket pin bound".into());
    }
    if payload.len() >= HOST_MAX_FRAME {
        return Err("host request exceeds frame bound before transmission".into());
    }
    let mut frame = Vec::with_capacity(payload.len() + config.len() + 38);
    frame.push(if host_sha256.is_some() { 2 } else { 1 });
    frame.extend_from_slice(&(config.len() as u32).to_le_bytes());
    frame.extend_from_slice(config);
    if let Some(sha) = host_sha256 {
        frame.extend_from_slice(sha);
    }
    frame.push(operation);
    frame.extend_from_slice(payload);
    Ok(frame)
}

fn read_frame(stream: &mut UnixStream) -> std::io::Result<Vec<u8>> {
    let mut prefix = [0u8; 4];
    stream.read_exact(&mut prefix)?;
    let size = u32::from_le_bytes(prefix) as usize;
    if size == 0 || size > HOST_MAX_FRAME + 1 {
        return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, "invalid frame length"));
    }
    let mut frame = Vec::new();
    stream.take(size as u64).read_to_end(&mut frame)?;
    if frame.len() != size {
        return Err(std::io::Error::new(std::io::ErrorKind::UnexpectedEof, "truncated frame"));
    }
    Ok(frame)
}

impl Operator {
    /// `config` is the deployment config file the socket pins; `host_sha256`, when given,
    /// requires the image serving the socket to be exactly that Host (version 2).
    pub fn new(socket: &Path, config: &Path, host_sha256: Option<[u8; 32]>) -> Result<Self> {
        let config = std::fs::read(config).map_err(|e| format!("host config {}: {e}", config.display()))?;
        Ok(Operator { socket: socket.into(), config, host_sha256, read_deadline: Duration::from_secs(600) })
    }

    pub fn call(&self, operation: u8, payload: &[u8]) -> std::result::Result<Reply, Failure> {
        let frame = request(&self.config, self.host_sha256.as_ref(), operation, payload)
            .map_err(|e| Failure::Unsent(e.0))?;
        let mut stream = UnixStream::connect(&self.socket)
            .map_err(|e| Failure::Unsent(format!("cannot connect to {}: {e}", self.socket.display())))?;
        let _ = stream.set_write_timeout(Some(Duration::from_secs(10)));
        let written = stream
            .write_all(&(frame.len() as u32).to_le_bytes())
            .and_then(|_| stream.write_all(&frame))
            .and_then(|_| stream.flush());
        if let Err(error) = written {
            // Only the socket's own 254 makes a failed write certain.
            let _ = stream.set_read_timeout(Some(Duration::from_secs(1)));
            if let Ok(reply) = read_frame(&mut stream) {
                if reply.first() == Some(&254) {
                    return Err(Failure::Unsent(format!("socket rejected request: {}", String::from_utf8_lossy(&reply[1..]))));
                }
            }
            return Err(Failure::Uncertain(format!("uncertain host request write: {error}")));
        }
        let _ = stream.set_read_timeout(Some(self.read_deadline));
        let reply = read_frame(&mut stream).map_err(|e| Failure::Uncertain(format!("uncertain host response read: {e}")))?;
        classify_reply(operation, reply)
    }
}

/// Classify a reply frame for `operation`.
pub fn classify_reply(operation: u8, mut reply: Vec<u8>) -> std::result::Result<Reply, Failure> {
    match reply.first().copied() {
        Some(254) => Err(Failure::Unsent(format!("socket rejected request: {}", String::from_utf8_lossy(&reply[1..])))),
        Some(255) => {
            reply.remove(0);
            Ok(Reply::Refused(reply))
        }
        Some(tag) if tag == operation => {
            reply.remove(0);
            Ok(Reply::Answer(reply))
        }
        Some(tag) => Err(Failure::Uncertain(format!("uncertain host response: unexpected operation {tag}"))),
        None => Err(Failure::Uncertain("empty host response".into())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn request_frames_are_transport_rs_frames() {
        let v1 = request(b"cfg", None, 3, b"call").unwrap();
        assert_eq!(v1, [&[1u8][..], &3u32.to_le_bytes(), b"cfg", &[3], b"call"].concat());
        let v2 = request(b"cfg", Some(&[7; 32]), 2, b"c").unwrap();
        assert_eq!(v2, [&[2u8][..], &3u32.to_le_bytes(), b"cfg", &[7; 32], &[2], b"c"].concat());
        assert!(request(&vec![0; MAX_CONFIG + 1], None, 2, b"").is_err());
    }

    #[test]
    fn replies_classify_into_answer_refusal_unsent_uncertain() {
        assert_eq!(classify_reply(2, vec![2, 9]), Ok(Reply::Answer(vec![9])));
        assert_eq!(classify_reply(2, vec![255, 9]), Ok(Reply::Refused(vec![9])));
        assert!(matches!(classify_reply(2, vec![254, b'b']), Err(Failure::Unsent(_))));
        assert!(matches!(classify_reply(2, vec![3]), Err(Failure::Uncertain(_))));
    }

    #[test]
    fn a_dead_socket_is_certainly_unsent_and_a_hangup_after_write_is_uncertain() {
        let dir = std::env::temp_dir().join(format!("mini-sdk-sock-{}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        std::fs::write(dir.join("config.json"), b"{}").unwrap();
        let sock = dir.join("world.sock");
        let _ = std::fs::remove_file(&sock);
        let op = Operator::new(&sock, &dir.join("config.json"), None).unwrap();
        assert!(matches!(op.call(2, b"call"), Err(Failure::Unsent(_))));
        let listener = std::os::unix::net::UnixListener::bind(&sock).unwrap();
        let server = std::thread::spawn(move || {
            let (mut s, _) = listener.accept().unwrap();
            let mut prefix = [0u8; 4];
            s.read_exact(&mut prefix).unwrap();
            let mut body = vec![0; u32::from_le_bytes(prefix) as usize];
            s.read_exact(&mut body).unwrap();
            body // drop the stream: the Host may have the call, the client has no answer
        });
        assert!(matches!(op.call(2, b"call"), Err(Failure::Uncertain(_))));
        let seen = server.join().unwrap();
        assert_eq!(seen, request(b"{}", None, 2, b"call").unwrap());
        let _ = std::fs::remove_dir_all(&dir);
    }
}
