//! The wire between the web gateway (uid `mini-web`, no privilege) and the root helper
//! `mini-web-spawn` (docs/WEB-FRONTEND-2026-10-27.md §2). One connection carries one request:
//! one line in, one line out, and for `shell` and `body` one file descriptor by `SCM_RIGHTS`
//! on the answer. This module is the whole protocol; both binaries link it, so there is one
//! parser and one fd-passing routine.
//!
//! ```text
//! mini-web-spawn-v1 login CODE            → ok SID NAME CSRF EXPIRES
//! mini-web-spawn-v1 who SID               → ok NAME CSRF EXPIRES
//! mini-web-spawn-v1 shell SID COLS ROWS   → ok PID            + the pty master fd
//! mini-web-spawn-v1 body SID|public       → ok                + a connected stream to that body
//! mini-web-spawn-v1 logout SID            → ok
//! mini-web-spawn-v1 sessions SID          → ok N, then N lines: PREFIX CREATED LASTSEEN CURRENT
//! mini-web-spawn-v1 revoke SID PREFIX     → ok
//! anything else                           → refused REASON      (policy: the request is not allowed)
//!                                         → error REASON        (the helper could not do it: spawn, connect)
//! ```
//!
//! A token (CODE, SID) is 43 characters of base64url (32 random bytes); the helper stores
//! tokens only by their SHA-256. CSRF is the same shape. Times are Unix seconds.

// print!/println!/eprint!/eprintln!: a closed standard output ends the command with 141, never a
// panic (`mini_streams`).
#[macro_use]
extern crate mini_streams;
pub mod spawn;
pub mod store;

use std::io::{self, IoSlice, IoSliceMut, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::time::Duration;

pub const HELLO: &str = "mini-web-spawn-v1";
pub const TOKEN_LEN: usize = 43;
/// The longest request or answer line.
pub const MAX_LINE: usize = 1024;
pub const MAX_SHELLS_PER_SESSION: usize = 8;

#[derive(Debug, Clone, PartialEq)]
pub enum Request {
    Login { code: String },
    Who { sid: String },
    Shell { sid: String, cols: u16, rows: u16 },
    Body { sid: Option<String> },
    Logout { sid: String },
    Sessions { sid: String },
    Revoke { sid: String, prefix: String },
}

pub fn is_token(s: &str) -> bool {
    s.len() == TOKEN_LEN && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
}

pub fn parse_request(line: &str) -> Result<Request, String> {
    let line = line.strip_suffix('\n').unwrap_or(line);
    if line.len() > MAX_LINE || line.bytes().any(|b| b.is_ascii_control()) {
        return Err("line too long or contains a control character".into());
    }
    let words: Vec<&str> = line.split(' ').collect();
    if words.first() != Some(&HELLO) {
        return Err(format!("not a {HELLO} request"));
    }
    let token = |i: usize, what: &str| -> Result<String, String> {
        match words.get(i) {
            Some(t) if is_token(t) => Ok((*t).to_owned()),
            _ => Err(format!("{what} is not a token")),
        }
    };
    match (words.get(1).copied(), words.len()) {
        (Some("login"), 3) => Ok(Request::Login { code: token(2, "CODE")? }),
        (Some("who"), 3) => Ok(Request::Who { sid: token(2, "SID")? }),
        (Some("shell"), 5) => {
            let size = |i: usize| words[i].parse::<u16>().ok().filter(|n| (1..=500).contains(n)).ok_or("COLS/ROWS must be 1..=500");
            Ok(Request::Shell { sid: token(2, "SID")?, cols: size(3)?, rows: size(4)? })
        }
        (Some("body"), 3) if words[2] == "public" => Ok(Request::Body { sid: None }),
        (Some("body"), 3) => Ok(Request::Body { sid: Some(token(2, "SID")?) }),
        (Some("logout"), 3) => Ok(Request::Logout { sid: token(2, "SID")? }),
        (Some("sessions"), 3) => Ok(Request::Sessions { sid: token(2, "SID")? }),
        (Some("revoke"), 4) => {
            let prefix = words[3];
            if prefix.len() != 12 || !prefix.bytes().all(|b| b.is_ascii_hexdigit()) {
                return Err("PREFIX is 12 hex digits".into());
            }
            Ok(Request::Revoke { sid: token(2, "SID")?, prefix: prefix.to_owned() })
        }
        _ => Err("unknown verb or wrong arity".into()),
    }
}

impl Request {
    pub fn line(&self) -> String {
        match self {
            Request::Login { code } => format!("{HELLO} login {code}\n"),
            Request::Who { sid } => format!("{HELLO} who {sid}\n"),
            Request::Shell { sid, cols, rows } => format!("{HELLO} shell {sid} {cols} {rows}\n"),
            Request::Body { sid: None } => format!("{HELLO} body public\n"),
            Request::Body { sid: Some(sid) } => format!("{HELLO} body {sid}\n"),
            Request::Logout { sid } => format!("{HELLO} logout {sid}\n"),
            Request::Sessions { sid } => format!("{HELLO} sessions {sid}\n"),
            Request::Revoke { sid, prefix } => format!("{HELLO} revoke {sid} {prefix}\n"),
        }
    }
}

/// The helper's answer: the words after `ok`, any further lines, and the passed fd.
#[derive(Debug)]
pub struct Answer {
    pub words: Vec<String>,
    pub lines: Vec<String>,
    pub fd: Option<OwnedFd>,
}

#[derive(Debug)]
pub enum Error {
    /// The helper said `refused REASON`: policy, not a fault.
    Refused(String),
    /// The helper said `error REASON`: it could not spawn or connect.
    Failed(String),
    /// The socket, or a malformed answer.
    Transport(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Refused(why) => write!(f, "refused: {why}"),
            Error::Failed(why) => write!(f, "helper could not: {why}"),
            Error::Transport(why) => write!(f, "helper: {why}"),
        }
    }
}

/// The gateway's side: connect, send one request, read the answer and its fd.
pub struct Client {
    path: std::path::PathBuf,
    timeout: Duration,
}

impl Client {
    pub fn new(path: &Path) -> Self {
        Client { path: path.to_path_buf(), timeout: Duration::from_secs(20) }
    }

    pub fn call(&self, request: &Request) -> Result<Answer, Error> {
        let transport = |e: io::Error| Error::Transport(e.to_string());
        let mut stream = UnixStream::connect(&self.path).map_err(transport)?;
        stream.set_read_timeout(Some(self.timeout)).map_err(transport)?;
        stream.set_write_timeout(Some(self.timeout)).map_err(transport)?;
        stream.write_all(request.line().as_bytes()).map_err(transport)?;
        let (bytes, fd) = recv_with_fd(&stream, MAX_LINE * 64).map_err(transport)?;
        let text = String::from_utf8(bytes).map_err(|_| Error::Transport("answer is not UTF-8".into()))?;
        let mut lines = text.split('\n').filter(|l| !l.is_empty()).map(str::to_owned);
        let first = lines.next().ok_or_else(|| Error::Transport("empty answer".into()))?;
        let mut words = first.split(' ').map(str::to_owned);
        match words.next().as_deref() {
            Some("ok") => Ok(Answer { words: words.collect(), lines: lines.collect(), fd }),
            Some("refused") => Err(Error::Refused(words.collect::<Vec<_>>().join(" "))),
            Some("error") => Err(Error::Failed(words.collect::<Vec<_>>().join(" "))),
            _ => Err(Error::Transport(format!("malformed answer {first:?}"))),
        }
    }
}

/// Send `bytes` and, if given, one fd in the same message.
pub fn send_with_fd(stream: &UnixStream, bytes: &[u8], fd: Option<RawFd>) -> io::Result<()> {
    let iov = [IoSlice::new(bytes)];
    let space = unsafe { libc::CMSG_SPACE(std::mem::size_of::<RawFd>() as u32) } as usize;
    let mut control = vec![0u8; space];
    let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
    msg.msg_iov = iov.as_ptr() as *mut libc::iovec;
    msg.msg_iovlen = 1 as _;
    if let Some(fd) = fd {
        msg.msg_control = control.as_mut_ptr() as *mut _;
        msg.msg_controllen = space as _;
        unsafe {
            let cmsg = libc::CMSG_FIRSTHDR(&msg);
            (*cmsg).cmsg_level = libc::SOL_SOCKET;
            (*cmsg).cmsg_type = libc::SCM_RIGHTS;
            (*cmsg).cmsg_len = libc::CMSG_LEN(std::mem::size_of::<RawFd>() as u32) as _;
            std::ptr::write_unaligned(libc::CMSG_DATA(cmsg) as *mut RawFd, fd);
        }
    }
    let sent = unsafe { libc::sendmsg(stream.as_raw_fd(), &msg, 0) };
    if sent < 0 {
        return Err(io::Error::last_os_error());
    }
    if (sent as usize) < bytes.len() {
        // The fd travelled with the first part; the rest is plain bytes.
        (&*stream).write_all(&bytes[sent as usize..])?;
    }
    Ok(())
}

/// Read until EOF (the peer answers and closes), collecting at most one passed fd.
pub fn recv_with_fd(stream: &UnixStream, limit: usize) -> io::Result<(Vec<u8>, Option<OwnedFd>)> {
    let mut out = Vec::new();
    let mut fd = None;
    let mut buffer = vec![0u8; 4096];
    loop {
        let space = unsafe { libc::CMSG_SPACE(std::mem::size_of::<RawFd>() as u32) } as usize;
        let mut control = vec![0u8; space];
        let mut iov = [IoSliceMut::new(&mut buffer)];
        let mut msg: libc::msghdr = unsafe { std::mem::zeroed() };
        msg.msg_iov = iov.as_mut_ptr() as *mut libc::iovec;
        msg.msg_iovlen = 1 as _;
        msg.msg_control = control.as_mut_ptr() as *mut _;
        msg.msg_controllen = space as _;
        let got = unsafe { libc::recvmsg(stream.as_raw_fd(), &mut msg, 0) };
        if got < 0 {
            let error = io::Error::last_os_error();
            if error.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
        if msg.msg_controllen as usize >= unsafe { libc::CMSG_LEN(0) } as usize {
            let cmsg = unsafe { libc::CMSG_FIRSTHDR(&msg) };
            if !cmsg.is_null() {
                let (level, kind) = unsafe { ((*cmsg).cmsg_level, (*cmsg).cmsg_type) };
                if level == libc::SOL_SOCKET && kind == libc::SCM_RIGHTS {
                    let raw = unsafe { std::ptr::read_unaligned(libc::CMSG_DATA(cmsg) as *const RawFd) };
                    let owned = unsafe { OwnedFd::from_raw_fd(raw) };
                    if fd.is_none() {
                        fd = Some(owned);
                    }
                }
            }
        }
        if got == 0 {
            return Ok((out, fd));
        }
        out.extend_from_slice(&buffer[..got as usize]);
        if out.len() > limit {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "answer exceeds the limit"));
        }
    }
}

/// Read one line (up to `MAX_LINE`) from the request side.
pub fn read_line(stream: &mut UnixStream) -> io::Result<String> {
    let mut out = Vec::new();
    let mut byte = [0u8; 1];
    loop {
        if stream.read(&mut byte)? == 0 {
            break;
        }
        if byte[0] == b'\n' {
            break;
        }
        out.push(byte[0]);
        if out.len() > MAX_LINE {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "line too long"));
        }
    }
    String::from_utf8(out).map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "line is not UTF-8"))
}

pub fn sha256_hex(bytes: &[u8]) -> String {
    use sha2::Digest;
    let digest = sha2::Sha256::digest(bytes);
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for b in digest {
        out.push(DIGITS[usize::from(b >> 4)] as char);
        out.push(DIGITS[usize::from(b & 15)] as char);
    }
    out
}

/// 32 bytes from the kernel, as 43 base64url characters.
pub fn new_token() -> io::Result<String> {
    let mut bytes = [0u8; 32];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut bytes)?;
    Ok(base64url(&bytes))
}

pub fn base64url(bytes: &[u8]) -> String {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
    let mut out = String::new();
    for chunk in bytes.chunks(3) {
        let mut n = 0u32;
        for (i, b) in chunk.iter().enumerate() {
            n |= (*b as u32) << (16 - 8 * i);
        }
        for i in 0..4 {
            if i <= chunk.len() {
                out.push(ALPHABET[((n >> (18 - 6 * i)) & 63) as usize] as char);
            }
        }
    }
    out
}

pub fn now() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use super::*;

    const T: &str = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA";

    #[test]
    fn requests_round_trip_and_refuse_malformed() {
        for r in [
            Request::Login { code: T.into() },
            Request::Who { sid: T.into() },
            Request::Shell { sid: T.into(), cols: 80, rows: 24 },
            Request::Body { sid: None },
            Request::Body { sid: Some(T.into()) },
            Request::Logout { sid: T.into() },
            Request::Sessions { sid: T.into() },
            Request::Revoke { sid: T.into(), prefix: "0123456789ab".into() },
        ] {
            assert_eq!(parse_request(&r.line()).unwrap(), r);
        }
        for bad in [
            "hello login x",
            &format!("{HELLO} login short"),
            &format!("{HELLO} shell {T} 0 24"),
            &format!("{HELLO} shell {T} 80 9999"),
            &format!("{HELLO} body {T} extra"),
            &format!("{HELLO} revoke {T} zz"),
            &format!("{HELLO} login {T}\x07"),
            &format!("{HELLO} spawn {T}"),
        ] {
            assert!(parse_request(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn tokens_are_43_base64url_and_base64url_matches_rfc4648() {
        let t = new_token().unwrap();
        assert!(is_token(&t), "{t}");
        assert_eq!(base64url(b"hello"), "aGVsbG8");
        assert_eq!(base64url(&[0xfb, 0xff]), "-_8");
        assert_eq!(sha256_hex(b"abc"), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
    }

    #[test]
    fn an_fd_travels_with_the_answer() {
        let (a, b) = UnixStream::pair().unwrap();
        let (x, y) = UnixStream::pair().unwrap();
        send_with_fd(&a, b"ok 42\n", Some(x.as_raw_fd())).unwrap();
        drop(a);
        let (bytes, fd) = recv_with_fd(&b, 1024).unwrap();
        assert_eq!(bytes, b"ok 42\n");
        let fd = fd.expect("an fd");
        let mut passed = UnixStream::from(fd);
        passed.write_all(b"through").unwrap();
        drop(passed);
        drop(x);
        let mut got = String::new();
        (&y).read_to_string(&mut got).unwrap();
        assert_eq!(got, "through");
    }
}
