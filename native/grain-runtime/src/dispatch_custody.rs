//! Private, bounded agent-dispatch purse RPC. Only the fixed SPK host UID may
//! connect; this socket never exposes the task signing key or a delivery permit.
use serde::Deserialize;
use serde_json::{json, Value};
use std::fs;
use std::io::{self, Read, Write};
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
#[cfg(target_os = "linux")]
use std::process::Command as ProcessCommand;
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::mpsc::{self, Receiver, SyncSender};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

const MAX_REQUEST: usize = 22 * 1024 * 1024;
const MAX_RESPONSE: usize = 16 * 1024;

#[derive(Debug, Deserialize)]
#[serde(tag = "type", rename_all = "kebab-case", deny_unknown_fields)]
pub enum Command {
    Reserve {
        http_operation_id: String,
        source_request_digest: String,
        canonical_request_hex: String,
    },
    MarkSend {
        attempt_id: String,
        request_sha256: String,
        transaction_id: String,
        event_id: String,
        permit_sha256: String,
    },
    SettleDefinite {
        attempt_id: String,
        response_sha256: String,
    },
    AbortNoSend {
        attempt_id: String,
    },
    Inspect {
        attempt_id: String,
    },
}

pub struct Request {
    pub command: Command,
    pub reply: mpsc::Sender<Value>,
    pub deadline: Instant,
    pub phase: Arc<AtomicU8>,
}

pub struct Server {
    pub requests: Receiver<Request>,
    stop: Arc<AtomicBool>,
    path: PathBuf,
    socket_identity: (u64, u64),
}

// Startup can fail after bind (mode, ACL or listener setup). Remove only the
// socket inode this process bound, leaving a replaced path untouched.
struct BoundSocket {
    path: PathBuf,
    identity: (u64, u64),
    armed: bool,
}

impl Drop for BoundSocket {
    fn drop(&mut self) {
        if self.armed {
            if let Ok(meta) = fs::symlink_metadata(&self.path) {
                if meta.file_type().is_socket() && (meta.dev(), meta.ino()) == self.identity {
                    let _ = fs::remove_file(&self.path);
                }
            }
        }
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::SeqCst);
        if let Ok(meta) = fs::symlink_metadata(&self.path) {
            if meta.file_type().is_socket() && (meta.dev(), meta.ino()) == self.socket_identity {
                let _ = fs::remove_file(&self.path);
            }
        }
    }
}

#[cfg(target_os = "linux")]
fn peer_uid(stream: &UnixStream) -> io::Result<u32> {
    use std::mem::{size_of, MaybeUninit};
    use std::os::fd::AsRawFd;
    let mut credential = MaybeUninit::<libc::ucred>::uninit();
    let mut len = size_of::<libc::ucred>() as libc::socklen_t;
    let rc = unsafe {
        libc::getsockopt(
            stream.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            credential.as_mut_ptr().cast(),
            &mut len,
        )
    };
    if rc != 0 || len as usize != size_of::<libc::ucred>() {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { credential.assume_init() }.uid)
}

#[cfg(not(target_os = "linux"))]
fn peer_uid(_stream: &UnixStream) -> io::Result<u32> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "dispatch custody requires Linux SO_PEERCRED",
    ))
}

fn read_frame(stream: &mut UnixStream) -> io::Result<Vec<u8>> {
    let mut len = [0u8; 4];
    stream.read_exact(&mut len)?;
    let len = u32::from_be_bytes(len) as usize;
    if len == 0 || len > MAX_REQUEST {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "dispatch RPC request bound",
        ));
    }
    let mut bytes = vec![0u8; len];
    stream.read_exact(&mut bytes)?;
    Ok(bytes)
}

fn write_frame(stream: &mut UnixStream, response: &Value) -> io::Result<()> {
    let bytes = serde_json::to_vec(response).map_err(io::Error::other)?;
    if bytes.len() > MAX_RESPONSE {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "dispatch RPC response bound",
        ));
    }
    stream.write_all(&(bytes.len() as u32).to_be_bytes())?;
    stream.write_all(&bytes)?;
    stream.flush()
}

fn serve_connection(mut stream: UnixStream, host_uid: u32, tx: SyncSender<Request>) {
    let _ = stream.set_read_timeout(Some(Duration::from_secs(10)));
    let _ = stream.set_write_timeout(Some(Duration::from_secs(10)));
    let response = if peer_uid(&stream).ok() != Some(host_uid) {
        json!({"type":"refused","detail":"dispatch RPC peer UID differs"})
    } else {
        match read_frame(&mut stream)
            .and_then(|bytes| serde_json::from_slice::<Command>(&bytes).map_err(io::Error::other))
        {
            Err(error) => json!({"type":"refused","detail":format!("dispatch RPC input: {error}")}),
            Ok(command) => {
                let (reply, recv) = mpsc::channel();
                let phase = Arc::new(AtomicU8::new(0));
                let deadline = Instant::now() + Duration::from_secs(300);
                if tx
                    .try_send(Request {
                        command,
                        reply,
                        deadline,
                        phase: phase.clone(),
                    })
                    .is_err()
                {
                    json!({"type":"refused","detail":"dispatch RPC queue full"})
                } else {
                    match recv.recv_timeout(Duration::from_secs(300)) {
                        Ok(value) => value,
                        Err(_)
                            if phase
                                .compare_exchange(0, 3, Ordering::SeqCst, Ordering::SeqCst)
                                .is_ok() =>
                        {
                            json!({"type":"refused","detail":"dispatch RPC expired before execution"})
                        }
                        Err(_) => {
                            json!({"type":"uncertain","detail":"dispatch RPC may have begun; inspect exact attempt"})
                        }
                    }
                }
            }
        }
    };
    let _ = write_frame(&mut stream, &response);
}

pub fn start(path: &Path, host_uid: u32) -> Result<Server, String> {
    if !path.is_absolute() {
        return Err("dispatch socket path must be absolute".into());
    }
    let listener = UnixListener::bind(path).map_err(|e| format!("dispatch bind: {e}"))?;
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    let mut bound = BoundSocket {
        path: path.to_owned(),
        identity: (meta.dev(), meta.ino()),
        armed: true,
    };
    fs::set_permissions(path, fs::Permissions::from_mode(0o600))
        .map_err(|e| format!("dispatch socket mode: {e}"))?;
    install_host_acl(path, host_uid)?;
    let after_acl = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !after_acl.file_type().is_socket()
        || (meta.dev(), meta.ino()) != (after_acl.dev(), after_acl.ino())
    {
        return Err("dispatch socket changed while installing host ACL".into());
    }
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let (tx, requests) = mpsc::sync_channel(8);
    let stop = Arc::new(AtomicBool::new(false));
    let thread_stop = stop.clone();
    let active = Arc::new(AtomicUsize::new(0));
    thread::spawn(move || {
        while !thread_stop.load(Ordering::SeqCst) {
            match listener.accept() {
                Ok((stream, _)) => {
                    if active.fetch_add(1, Ordering::SeqCst) >= 4 {
                        active.fetch_sub(1, Ordering::SeqCst);
                        continue;
                    }
                    let tx = tx.clone();
                    let active = active.clone();
                    thread::spawn(move || {
                        serve_connection(stream, host_uid, tx);
                        active.fetch_sub(1, Ordering::SeqCst);
                    });
                }
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    thread::sleep(Duration::from_millis(20))
                }
                Err(_) => break,
            }
        }
    });
    bound.armed = false;
    Ok(Server {
        requests,
        stop,
        path: path.to_owned(),
        socket_identity: (meta.dev(), meta.ino()),
    })
}

#[cfg(target_os = "linux")]
fn install_host_acl(path: &Path, host_uid: u32) -> Result<(), String> {
    let grant = format!("u:{host_uid}:rw");
    let status = ProcessCommand::new("/usr/bin/setfacl")
        .args(["-m", &grant])
        .arg(path)
        .status()
        .map_err(|e| format!("dispatch socket ACL install: {e}"))?;
    if !status.success() {
        return Err("dispatch socket ACL install refused".into());
    }
    let output = ProcessCommand::new("/usr/bin/getfacl")
        .args(["-cpn"])
        .arg(path)
        .output()
        .map_err(|e| format!("dispatch socket ACL inspect: {e}"))?;
    if !output.status.success() {
        return Err("dispatch socket ACL inspection refused".into());
    }
    let listing = String::from_utf8(output.stdout)
        .map_err(|_| "dispatch socket ACL inspection is not UTF-8")?;
    let mut allowed = false;
    let mut owner = false;
    let mut group = false;
    let mut mask = false;
    let mut other = false;
    for line in listing.lines().filter(|line| !line.is_empty()) {
        match line {
            "user::rw-" => owner = true,
            "group::---" => group = true,
            "mask::rw-" => mask = true,
            "other::---" => other = true,
            line if line == format!("user:{host_uid}:rw-") => allowed = true,
            _ => return Err(format!("dispatch socket has unexpected ACL entry: {line}")),
        }
    }
    if !allowed || !owner || !group || !mask || !other {
        return Err("dispatch socket ACL lacks exact owner/host-only entries".into());
    }
    Ok(())
}

#[cfg(not(target_os = "linux"))]
fn install_host_acl(_path: &Path, _host_uid: u32) -> Result<(), String> {
    Err("dispatch custody requires Linux socket ACL".into())
}

pub fn decode_hex(bytes: &str) -> Result<Vec<u8>, String> {
    if bytes.is_empty() || bytes.len() > MAX_REQUEST || bytes.len() % 2 != 0 {
        return Err("dispatch request hex bound".into());
    }
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.as_bytes().chunks_exact(2) {
        let nibble = |byte: u8| match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            _ => None,
        };
        out.push(
            (nibble(pair[0]).ok_or("noncanonical request hex")? << 4)
                | nibble(pair[1]).ok_or("noncanonical request hex")?,
        );
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonical_request_hex_refuses_uppercase_and_odd_bytes() {
        assert_eq!(decode_hex("00aaff").unwrap(), [0, 170, 255]);
        assert!(decode_hex("AA").is_err());
        assert!(decode_hex("0").is_err());
        assert!(decode_hex("").is_err());
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn custody_socket_installs_narrow_acl_and_refuses_other_peer_uid() {
        let dir = std::env::temp_dir().join(format!(
            "mini-dispatch-custody-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&dir).unwrap();
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o711)).unwrap();
        let socket = dir.join("dispatch.sock");
        let peer = unsafe { libc::geteuid() } + 1;
        let server = start(&socket, peer).unwrap();
        let acl = ProcessCommand::new("/usr/bin/getfacl")
            .args(["-cpn"])
            .arg(&socket)
            .output()
            .unwrap();
        assert!(acl.status.success());
        assert!(String::from_utf8(acl.stdout)
            .unwrap()
            .contains(&format!("user:{peer}:rw-")));
        let mut stream = UnixStream::connect(&socket).unwrap();
        let request = br#"{"type":"inspect","attempt_id":"1"}"#;
        stream
            .write_all(&(request.len() as u32).to_be_bytes())
            .unwrap();
        stream.write_all(request).unwrap();
        let mut len = [0u8; 4];
        stream.read_exact(&mut len).unwrap();
        let mut response = vec![0u8; u32::from_be_bytes(len) as usize];
        stream.read_exact(&mut response).unwrap();
        let outcome: Value = serde_json::from_slice(&response).unwrap();
        assert_eq!(outcome["type"], "refused");
        assert!(outcome["detail"].as_str().unwrap().contains("peer UID"));
        drop(server);
        fs::remove_dir(&dir).unwrap();
    }
}
