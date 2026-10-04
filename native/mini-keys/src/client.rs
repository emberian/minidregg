//! The client side: find the broker, check that the account answering on its
//! socket is the broker's, and make one call.
//!
//! The box names the broker in one root-owned file, [`CLIENT_CONFIG`]:
//! `{"type":"mini-keys-client-v1","socket":"/run/mini-keys/broker.sock","uid":N}`.
//! A client refuses an answer from any other uid (`broker-identity`), so an
//! account that could replace the socket still cannot impersonate the broker
//! to a member handing it a provider key.
use crate::{peer, wire};
use serde_json::{json, Value};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::MetadataExt;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

pub const CLIENT_CONFIG: &str = "/etc/mini/keys-client.json";
pub const CLIENT_TYPE: &str = "mini-keys-client-v1";
const MAX_CLIENT_CONFIG: u64 = 4096;

/// A refusal the broker named, or one this client named before or after the call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Refused {
    pub code: String,
    pub detail: String,
}

impl std::fmt::Display for Refused {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "mini-keys refused {}: {}", self.code, self.detail)
    }
}

impl From<Refused> for String {
    fn from(r: Refused) -> String {
        r.to_string()
    }
}

fn local(code: &str, detail: impl Into<String>) -> Refused {
    Refused { code: code.into(), detail: detail.into() }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Broker {
    pub socket: PathBuf,
    /// The only uid whose answer this client accepts.
    pub uid: u32,
}

/// A path whose file and every ancestor directory belong to `owner` or root and
/// are writable by nobody else (a sticky directory, like /tmp, is allowed as an
/// ancestor: only an entry's owner may rename or unlink in it).
pub fn custody_file(path: &Path, owner: u32, bound: u64) -> Result<Vec<u8>, String> {
    if !path.is_absolute() {
        return Err(format!("{} must be an absolute path", path.display()));
    }
    for (index, entry) in path.ancestors().enumerate() {
        let meta = std::fs::symlink_metadata(entry)
            .map_err(|_| format!("{} is unavailable", entry.display()))?;
        let mode = meta.mode();
        let trusted = meta.uid() == owner || meta.uid() == 0;
        let ok = if index == 0 {
            meta.file_type().is_file() && trusted && mode & 0o022 == 0 && meta.len() <= bound
        } else {
            meta.file_type().is_dir() && trusted && (mode & 0o022 == 0 || mode & 0o1000 != 0)
        };
        if !ok {
            return Err(format!(
                "{} must be owned by uid {owner} or root and writable by no other account",
                entry.display()
            ));
        }
    }
    std::fs::read(path).map_err(|_| format!("{} is unavailable", path.display()))
}

impl Broker {
    pub fn new(socket: impl Into<PathBuf>, uid: u32) -> Self {
        Broker { socket: socket.into(), uid }
    }

    /// Load the box's pointer to the broker. On a box the file is root's
    /// (`owner` = 0); a test names its own uid.
    pub fn load(path: &Path, owner: u32) -> Result<Self, Refused> {
        let bytes = custody_file(path, owner, MAX_CLIENT_CONFIG)
            .map_err(|e| local("client-config", e))?;
        let value: Value = serde_json::from_slice(&bytes)
            .map_err(|_| local("client-config", "the broker client config is not JSON"))?;
        let object = value
            .as_object()
            .filter(|m| m.keys().all(|k| ["type", "socket", "uid"].contains(&k.as_str())))
            .ok_or_else(|| local("client-config", "the broker client config has unknown fields"))?;
        if object.get("type").and_then(Value::as_str) != Some(CLIENT_TYPE) {
            return Err(local("client-config", format!("the broker client config is not {CLIENT_TYPE}")));
        }
        let socket = object
            .get("socket")
            .and_then(Value::as_str)
            .filter(|s| s.starts_with('/'))
            .ok_or_else(|| local("client-config", "socket must be an absolute path"))?;
        let uid = object
            .get("uid")
            .and_then(Value::as_u64)
            .filter(|u| *u <= u32::MAX as u64)
            .ok_or_else(|| local("client-config", "uid must be the broker's numeric uid"))?;
        Ok(Broker::new(socket, uid as u32))
    }

    /// The box default ([`CLIENT_CONFIG`], root-owned).
    pub fn default_box() -> Result<Self, Refused> {
        Self::load(Path::new(CLIENT_CONFIG), 0)
    }

    /// Connect before `end` and check the answering account.
    pub fn connect(&self, end: Instant) -> Result<UnixStream, Refused> {
        let stream = connect(&self.socket, end).map_err(|e| local("broker-unavailable", e))?;
        let peer = peer::of(&stream).map_err(|e| local("broker-identity", e))?;
        if peer.uid != self.uid {
            return Err(local(
                "broker-identity",
                format!(
                    "{} answered as uid {}, not the broker's uid {}",
                    self.socket.display(),
                    peer.uid,
                    self.uid
                ),
            ));
        }
        Ok(stream)
    }

    /// One request, one response.
    pub fn call(&self, request: &Value, timeout: Duration) -> Result<Value, Refused> {
        let end = Instant::now() + timeout;
        let mut stream = self.connect(end)?;
        wire::send(&mut stream, request, end).map_err(|e| local("broker-io", e))?;
        let response = wire::recv(&mut stream, wire::MAX_FRAME, end).map_err(|e| local("broker-io", e))?;
        answer(response)
    }
}

/// A broker response: `ok` or its named refusal.
pub fn answer(response: Value) -> Result<Value, Refused> {
    if response.get("ok") == Some(&Value::Bool(true)) {
        return Ok(response);
    }
    match (response.get("refused").and_then(Value::as_str), response.get("detail").and_then(Value::as_str)) {
        (Some(code), detail) => Err(Refused { code: code.into(), detail: detail.unwrap_or("").into() }),
        _ => Err(local("broker-io", "the broker answered neither ok nor a named refusal")),
    }
}

/// `{"op":"hello"}`: which roles this account holds at the broker.
pub fn hello(broker: &Broker) -> Result<Value, Refused> {
    broker.call(&json!({"op":"hello"}), Duration::from_secs(10))
}

/// A Unix connect that cannot block past `end`, even when the listener's
/// backlog is full.
pub fn connect(socket: &Path, end: Instant) -> Result<UnixStream, String> {
    use std::os::unix::ffi::OsStrExt;
    let bytes = socket.as_os_str().as_bytes();
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if bytes.is_empty() || bytes.len() >= address.sun_path.len() || bytes.contains(&0) {
        return Err("broker socket path refused".into());
    }
    address.sun_family = libc::AF_UNIX as _;
    #[cfg(any(target_os = "macos", target_os = "ios", target_os = "freebsd", target_os = "openbsd", target_os = "netbsd", target_os = "dragonfly"))]
    {
        address.sun_len = std::mem::size_of_val(&address) as _;
    }
    for (dst, src) in address.sun_path.iter_mut().zip(bytes) {
        *dst = *src as _;
    }
    loop {
        if Instant::now() >= end {
            return Err("broker admission timed out".into());
        }
        let fd = unsafe { libc::socket(libc::AF_UNIX, libc::SOCK_STREAM, 0) };
        if fd < 0 {
            return Err("broker unavailable".into());
        }
        let stream = unsafe { UnixStream::from_raw_fd(fd) };
        if unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } < 0 {
            return Err("broker unavailable".into());
        }
        stream.set_nonblocking(true).map_err(|_| "broker unavailable")?;
        let rc = unsafe {
            libc::connect(fd, &address as *const _ as *const libc::sockaddr, std::mem::size_of_val(&address) as _)
        };
        let connected = if rc == 0 {
            true
        } else {
            let error = std::io::Error::last_os_error();
            if error.raw_os_error() == Some(libc::EINPROGRESS) {
                let left = end.saturating_duration_since(Instant::now());
                let mut p = libc::pollfd { fd: stream.as_raw_fd(), events: libc::POLLOUT, revents: 0 };
                let ready = unsafe { libc::poll(&mut p, 1, left.as_millis().min(i32::MAX as u128) as i32) };
                let mut result: libc::c_int = 0;
                let mut length = std::mem::size_of_val(&result) as libc::socklen_t;
                ready > 0
                    && unsafe {
                        libc::getsockopt(fd, libc::SOL_SOCKET, libc::SO_ERROR, &mut result as *mut _ as *mut libc::c_void, &mut length)
                    } == 0
                    && result == 0
            } else if matches!(error.kind(), std::io::ErrorKind::WouldBlock | std::io::ErrorKind::Interrupted) {
                drop(stream);
                std::thread::sleep(Duration::from_millis(5).min(end.saturating_duration_since(Instant::now())));
                continue;
            } else {
                return Err(format!("broker unavailable at {}", socket.display()));
            }
        };
        if !connected {
            return Err(format!("broker unavailable at {}", socket.display()));
        }
        stream.set_nonblocking(false).map_err(|_| "broker unavailable")?;
        return Ok(stream);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    fn dir(tag: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("mini-keys-client-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&d);
        std::fs::create_dir(&d).unwrap();
        std::fs::set_permissions(&d, std::fs::Permissions::from_mode(0o700)).unwrap();
        d.canonicalize().unwrap()
    }

    #[test]
    fn client_config_is_custody_checked_and_exact() {
        let d = dir("config");
        let path = d.join("keys-client.json");
        std::fs::write(&path, r#"{"type":"mini-keys-client-v1","socket":"/run/mini-keys/broker.sock","uid":991}"#).unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o644)).unwrap();
        let me = peer::euid();
        assert_eq!(Broker::load(&path, me).unwrap(), Broker::new("/run/mini-keys/broker.sock", 991));
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o666)).unwrap();
        assert_eq!(Broker::load(&path, me).unwrap_err().code, "client-config");
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o644)).unwrap();
        std::fs::write(&path, r#"{"type":"mini-keys-client-v1","socket":"/s","uid":1,"extra":1}"#).unwrap();
        assert!(Broker::load(&path, me).unwrap_err().detail.contains("unknown fields"));
        std::fs::write(&path, r#"{"type":"mini-keys-client-v1","socket":"relative","uid":1}"#).unwrap();
        assert!(Broker::load(&path, me).is_err());
        std::fs::remove_dir_all(&d).unwrap();
    }

    #[test]
    fn an_answer_from_another_uid_is_not_the_broker() {
        let d = dir("identity");
        let socket = d.join("s.sock");
        let listener = std::os::unix::net::UnixListener::bind(&socket).unwrap();
        let t = std::thread::spawn(move || {
            let _ = listener.accept();
        });
        let wrong = Broker::new(&socket, peer::euid().wrapping_add(1));
        let refused = wrong.connect(Instant::now() + Duration::from_secs(2)).unwrap_err();
        assert_eq!(refused.code, "broker-identity");
        t.join().unwrap();
        std::fs::remove_dir_all(&d).unwrap();
    }

    #[test]
    fn answers_are_ok_or_named() {
        assert!(answer(json!({"ok":true,"x":1})).is_ok());
        assert_eq!(answer(json!({"refused":"op-not-granted","detail":"d"})).unwrap_err().code, "op-not-granted");
        assert_eq!(answer(json!({"x":1})).unwrap_err().code, "broker-io");
    }
}
