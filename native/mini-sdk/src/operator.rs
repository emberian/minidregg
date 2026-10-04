//! Client of the operator socket (`transport.rs` `invoke_inner`, `exchange_unix`), over either
//! route:
//!
//! * [`Route::Unix`] — the deployment's unix socket, one connection per request.
//! * [`Route::Ssh`] — `ssh:DEST`: one `ssh -T DEST` session per [`Operator`], whose stdio is the
//!   byte proxy `mini socket-proxy` on the box (the only command the member's ssh key may run;
//!   `native/resource-client/src/proxy.rs`), carrying exactly the frames the unix socket would,
//!   one reply per request. The member's signing key never leaves this machine.
//!
//! Request frame: `u32(len) ‖ version(1 | 2) ‖ u32(len(config)) ‖ config ‖ hostSha256[32] (v2) ‖
//! op ‖ payload`. Reply frame: `u32(len) ‖ op | 255 (Host refusal, encoded outcome) | 254
//! (the socket never forwarded the request)`. Every failure is classified as certainly-unsent
//! or uncertain; nothing in between is invented.
//!
//! # The ssh route
//!
//! The SDK builds the ssh command itself, so a user's ssh config cannot weaken it:
//! `-T -v -o BatchMode=yes -o StrictHostKeyChecking=yes -o ClearAllForwardings=yes
//! -o ControlPath=none -o ConnectTimeout=N [-i ID -o IdentitiesOnly=yes] [-F CONFIG] -- DEST`.
//! Host key checking is ON (an unknown or changed host key is a refusal, never a prompt and never
//! silently accepted), no prompt can block (BatchMode), nothing is forwarded.
//!
//! Classification. The request is written only after ssh reports `Entering interactive session`
//! (its `-v` stderr), i.e. after the connection, host-key check and authentication succeeded and
//! the channel opened. Everything that fails BEFORE that line fails with no request byte having
//! left this process: [`Failure::Unsent`], and the refusal is named (`host key verification
//! failed`, `authentication refused`, `destination unreachable`, `session not established within
//! Ns`). Everything after the write — a hangup, a malformed or missing reply, a deadline — is
//! [`Failure::Uncertain`], the session is closed, and the exact request is NEVER resent: a lost
//! reply is answered by `lookup` of the same call bytes, as with the unix socket.
//!
//! `MINI_SSH` names another OpenSSH-compatible ssh program (as `GIT_SSH` does); ports and
//! jump hosts belong in ssh config.
use std::ffi::OsString;
use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use crate::{Error, Result};

pub const HOST_MAX_FRAME: usize = 12_102_760;
pub const MAX_CONFIG: usize = 65_536;
/// The address prefix of the ssh route.
pub const SSH_PREFIX: &str = "ssh:";

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

/// Where operator requests go.
#[derive(Debug, Clone)]
pub enum Route {
    Unix(PathBuf),
    Ssh(Ssh),
}

/// The ssh route's settings. See the module docs for the command the SDK builds from them.
#[derive(Debug, Clone)]
pub struct Ssh {
    /// `user@host` or an ssh config Host alias; passed after `--`, so never an ssh option.
    pub destination: String,
    /// The ssh program and any fixed leading arguments. Default: `MINI_SSH` if set, else `ssh`.
    pub command: Vec<OsString>,
    /// `-i`: a workspace credential, with `IdentitiesOnly=yes`.
    pub identity: Option<PathBuf>,
    /// `-F`: an ssh config file other than the user's default.
    pub config: Option<PathBuf>,
    /// How long ssh may take to connect, check the host key, authenticate and open the channel.
    pub connect_timeout: Duration,
    /// How long writing one request into the session may take.
    pub write_deadline: Duration,
}

/// An ssh destination as `ssh` itself takes it: `user@host` or a Host alias from ssh config.
pub fn check_destination(destination: &str) -> Result<()> {
    if destination.is_empty()
        || destination.len() > 255
        || destination.starts_with('-')
        || !destination.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'-' | b'@' | b'%' | b'+'))
    {
        return Err("ssh destination must be one of user@host or an ssh config Host alias (letters, digits and . _ - @ % +, not starting with -)".into());
    }
    Ok(())
}

impl Ssh {
    pub fn new(destination: &str) -> Result<Self> {
        check_destination(destination)?;
        let program = std::env::var_os("MINI_SSH").filter(|p| !p.is_empty()).unwrap_or_else(|| "ssh".into());
        Ok(Ssh { destination: destination.to_owned(), command: vec![program], identity: None, config: None,
            connect_timeout: Duration::from_secs(30), write_deadline: Duration::from_secs(60) })
    }

    /// The argument list after the program (and its fixed leading arguments).
    pub fn arguments(&self) -> Vec<OsString> {
        let mut a: Vec<OsString> = ["-T", "-v", "-o", "BatchMode=yes", "-o", "StrictHostKeyChecking=yes", "-o", "ClearAllForwardings=yes",
            "-o", "ControlPath=none"].iter().map(OsString::from).collect();
        a.push("-o".into());
        a.push(format!("ConnectTimeout={}", self.connect_timeout.as_secs().max(1)).into());
        if let Some(config) = &self.config {
            a.push("-F".into());
            a.push(config.into());
        }
        if let Some(identity) = &self.identity {
            a.extend(["-i".into(), identity.into(), "-o".into(), "IdentitiesOnly=yes".into()]);
        }
        a.push("--".into());
        a.push(self.destination.clone().into());
        a
    }
}

impl Route {
    /// `ssh:DEST` or the absolute path of a unix socket. Anything else refuses by name.
    pub fn parse(address: &str) -> Result<Route> {
        match address.strip_prefix(SSH_PREFIX) {
            Some(destination) => Ssh::new(destination).map(Route::Ssh),
            None if Path::new(address).is_absolute() => Ok(Route::Unix(address.into())),
            None => Err(Error(format!("operator address {address:?} is neither an absolute unix socket path nor ssh:DEST"))),
        }
    }
}

/// Why an ssh session was not established. Each variant means NO request byte left this process.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SshRefusal {
    HostKey(String),
    Authentication(String),
    Unreachable(String),
    NotEstablished(String),
}
impl std::fmt::Display for SshRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SshRefusal::HostKey(d) => write!(f, "ssh: host key verification failed; host key checking is on, so the host key must already be in known_hosts: {d}"),
            SshRefusal::Authentication(d) => write!(f, "ssh: authentication refused: {d}"),
            SshRefusal::Unreachable(d) => write!(f, "ssh: destination unreachable: {d}"),
            SshRefusal::NotEstablished(d) => write!(f, "ssh: session not established: {d}"),
        }
    }
}

/// Name the refusal from what ssh said (its non-debug stderr lines).
pub fn name_refusal(lines: &[String]) -> SshRefusal {
    let said = lines.join(" | ");
    let has = |needle: &str| lines.iter().any(|l| l.contains(needle));
    if has("Host key verification failed") || has("REMOTE HOST IDENTIFICATION HAS CHANGED") || has("No ED25519 host key is known")
        || has("host key is known for") {
        SshRefusal::HostKey(said)
    } else if has("Permission denied") || has("Too many authentication failures") || has("no mutual signature") {
        SshRefusal::Authentication(said)
    } else if has("Could not resolve hostname") || has("Connection refused") || has("Connection timed out") || has("No route to host")
        || has("Network is unreachable") || has("Operation timed out") || has("Connection closed by") || has("Connection reset") {
        SshRefusal::Unreachable(said)
    } else {
        SshRefusal::NotEstablished(if said.is_empty() { "ssh exited before opening the session".into() } else { said })
    }
}

/// What the stderr reader learned.
#[derive(Default)]
struct Notes {
    lines: Vec<String>,
}

/// One live `ssh -T DEST` session: the proxy's stdio.
struct Session {
    child: Child,
    stdin: Option<ChildStdin>,
    frames: Receiver<std::io::Result<Vec<u8>>>,
    notes: Arc<Mutex<Notes>>,
}

impl Session {
    fn close(mut self) {
        drop(self.stdin.take());
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
    fn said(&self) -> Vec<String> {
        self.notes.lock().map(|n| n.lines.clone()).unwrap_or_default()
    }
}

fn open_ssh(ssh: &Ssh) -> std::result::Result<Session, Failure> {
    let (program, leading) = ssh.command.split_first().ok_or_else(|| Failure::Unsent("ssh command is empty".into()))?;
    let mut child = Command::new(program)
        .args(leading)
        .args(ssh.arguments())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| Failure::Unsent(format!("cannot start {}: {e}", program.to_string_lossy())))?;
    let stdin = child.stdin.take().expect("piped");
    let stdout = child.stdout.take().expect("piped");
    let stderr = child.stderr.take().expect("piped");
    let notes = Arc::new(Mutex::new(Notes::default()));
    // stderr: watch for the marker, keep the few lines that are not ssh's debug chatter.
    let (ready_tx, ready_rx) = mpsc::channel::<()>();
    let seen = notes.clone();
    std::thread::spawn(move || {
        let mut ready = Some(ready_tx);
        for line in BufReader::new(stderr).split(b'\n').map_while(|l| l.ok()) {
            let line = String::from_utf8_lossy(&line).trim_end().to_owned();
            if line.contains("Entering interactive session") {
                if let Some(tx) = ready.take() {
                    let _ = tx.send(());
                }
            } else if !(line.starts_with("debug") || line.starts_with("OpenSSH_") || line.starts_with("Authenticated to ")
                || line.starts_with("Warning: Permanently added") || line.is_empty()) {
                if let Ok(mut n) = seen.lock() {
                    if n.lines.len() < 12 {
                        n.lines.push(line.chars().take(300).collect());
                    }
                }
            }
        }
    });
    // stdout: one frame per reply.
    let (frames_tx, frames) = mpsc::channel();
    std::thread::spawn(move || {
        let mut stdout = stdout;
        loop {
            match read_frame(&mut stdout) {
                Ok(frame) => {
                    if frames_tx.send(Ok(frame)).is_err() {
                        return;
                    }
                }
                Err(e) => {
                    let _ = frames_tx.send(Err(e));
                    return;
                }
            }
        }
    });
    let session = Session { child, stdin: Some(stdin), frames, notes };
    match ready_rx.recv_timeout(ssh.connect_timeout) {
        Ok(()) => Ok(session),
        Err(RecvTimeoutError::Disconnected) => {
            // ssh exited before the channel opened; give the stderr reader a moment to finish.
            std::thread::sleep(Duration::from_millis(100));
            let refusal = name_refusal(&session.said());
            session.close();
            Err(Failure::Unsent(refusal.to_string()))
        }
        Err(RecvTimeoutError::Timeout) => {
            // Still no channel after the deadline: whatever ssh has said so far names it, else
            // the timeout itself is the named refusal. Nothing was written.
            let said = session.said();
            session.close();
            Err(Failure::Unsent(match name_refusal(&said) {
                SshRefusal::NotEstablished(d) => SshRefusal::NotEstablished(
                    format!("not within {}s{}", ssh.connect_timeout.as_secs(), if said.is_empty() { String::new() } else { format!(": {d}") })),
                named => named,
            }.to_string()))
        }
    }
}

pub struct Operator {
    pub route: Route,
    config: Vec<u8>,
    host_sha256: Option<[u8; 32]>,
    pub read_deadline: Duration,
    session: Mutex<Option<Session>>,
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

fn read_frame<R: Read>(stream: &mut R) -> std::io::Result<Vec<u8>> {
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

impl Drop for Operator {
    fn drop(&mut self) {
        if let Ok(mut s) = self.session.lock() {
            if let Some(session) = s.take() {
                session.close();
            }
        }
    }
}

impl Operator {
    /// `config` is the deployment config file the socket pins; `host_sha256`, when given,
    /// requires the image serving the socket to be exactly that Host (version 2).
    pub fn new(route: Route, config: &Path, host_sha256: Option<[u8; 32]>) -> Result<Self> {
        let config = std::fs::read(config).map_err(|e| format!("host config {}: {e}", config.display()))?;
        Ok(Operator { route, config, host_sha256, read_deadline: Duration::from_secs(600), session: Mutex::new(None) })
    }

    pub fn call(&self, operation: u8, payload: &[u8]) -> std::result::Result<Reply, Failure> {
        let frame = request(&self.config, self.host_sha256.as_ref(), operation, payload)
            .map_err(|e| Failure::Unsent(e.0))?;
        let reply = match &self.route {
            Route::Unix(socket) => self.call_unix(socket, &frame)?,
            Route::Ssh(ssh) => self.call_ssh(ssh, &frame)?,
        };
        classify_reply(operation, reply)
    }

    fn call_unix(&self, socket: &Path, frame: &[u8]) -> std::result::Result<Vec<u8>, Failure> {
        let mut stream = UnixStream::connect(socket)
            .map_err(|e| Failure::Unsent(format!("cannot connect to {}: {e}", socket.display())))?;
        let _ = stream.set_write_timeout(Some(Duration::from_secs(10)));
        let written = stream
            .write_all(&(frame.len() as u32).to_le_bytes())
            .and_then(|_| stream.write_all(frame))
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
        read_frame(&mut stream).map_err(|e| Failure::Uncertain(format!("uncertain host response read: {e}")))
    }

    fn call_ssh(&self, ssh: &Ssh, frame: &[u8]) -> std::result::Result<Vec<u8>, Failure> {
        let mut guard = self.session.lock().map_err(|_| Failure::Unsent("ssh session table poisoned".into()))?;
        // A session that has said anything unasked, or has ended, is not reused: nothing has been
        // written yet, so opening a fresh one is certainly-unsent territory.
        if let Some(live) = guard.as_ref() {
            let stale = !matches!(live.frames.try_recv(), Err(mpsc::TryRecvError::Empty));
            if stale {
                guard.take().expect("present").close();
            }
        }
        if guard.is_none() {
            *guard = Some(open_ssh(ssh)?);
        }
        let session = guard.as_mut().expect("opened");
        let mut wire = (frame.len() as u32).to_le_bytes().to_vec();
        wire.extend_from_slice(frame);
        // Write under a deadline: a stalled pipe must not hang the caller.
        let stdin = session.stdin.take().expect("session has stdin");
        let (done_tx, done_rx) = mpsc::channel();
        std::thread::spawn(move || {
            let mut stdin = stdin;
            let r = stdin.write_all(&wire).and_then(|_| stdin.flush());
            let _ = done_tx.send((r, stdin));
        });
        match done_rx.recv_timeout(ssh.write_deadline) {
            Ok((Ok(()), stdin)) => session.stdin = Some(stdin),
            Ok((Err(e), _)) => {
                let said = session.said().join(" | ");
                guard.take().expect("opened").close();
                return Err(Failure::Uncertain(format!("uncertain host request write: {e} {said}")));
            }
            Err(_) => {
                guard.take().expect("opened").close();
                return Err(Failure::Uncertain(format!("uncertain host request write: not complete within {}s", ssh.write_deadline.as_secs())));
            }
        }
        match session.frames.recv_timeout(self.read_deadline) {
            Ok(Ok(reply)) => Ok(reply),
            Ok(Err(e)) => {
                let said = session.said().join(" | ");
                guard.take().expect("opened").close();
                Err(Failure::Uncertain(format!("uncertain host response read: {e} {said}").trim_end().to_owned()))
            }
            Err(_) => {
                guard.take().expect("opened").close();
                Err(Failure::Uncertain(format!("uncertain host response: none within {}s", self.read_deadline.as_secs())))
            }
        }
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
    use std::path::PathBuf;

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
        let op = Operator::new(Route::Unix(sock.clone()), &dir.join("config.json"), None).unwrap();
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

    // ---- the ssh route, against the `ssh` stand-in (`frame::fake::SSH_STANDIN`) ----

    fn standin(dest: &str) -> (Operator, PathBuf) {
        let (sh, script) = crate::frame::fake::script("ssh", crate::frame::fake::SSH_STANDIN);
        let dir = std::env::temp_dir().join(format!("mini-sdk-ssh-cfg-{}-{dest}", std::process::id()));
        let _ = std::fs::create_dir_all(&dir);
        std::fs::write(dir.join("config.json"), b"{}").unwrap();
        let mut ssh = Ssh::new(dest).unwrap();
        ssh.command = vec![sh.into(), script.into()];
        ssh.connect_timeout = Duration::from_secs(2);
        ssh.write_deadline = Duration::from_secs(5);
        let mut op = Operator::new(Route::Ssh(ssh), &dir.join("config.json"), None).unwrap();
        op.read_deadline = Duration::from_secs(2);
        let req = std::env::temp_dir().join(format!("mini-sdk-ssh-{dest}.req"));
        let _ = std::fs::remove_file(&req);
        (op, req)
    }

    fn unsent(r: std::result::Result<Reply, Failure>) -> String {
        match r {
            Err(Failure::Unsent(d)) => d,
            other => panic!("expected certainly-unsent, got {other:?}"),
        }
    }

    #[test]
    fn addresses_parse_to_routes_and_bad_destinations_refuse_by_name() {
        assert!(matches!(Route::parse("/run/mini/world.sock").unwrap(), Route::Unix(_)));
        let Route::Ssh(s) = Route::parse("ssh:member@box.example").unwrap() else { panic!() };
        assert_eq!(s.destination, "member@box.example");
        for bad in ["relative.sock", "", "ssh:", "ssh:-oProxyCommand=sh", "ssh:mini@host;id", "ssh:a b", "ssh:mini@host:22"] {
            assert!(Route::parse(bad).is_err(), "{bad:?}");
        }
        // The destination follows `--`, so it can never be read as an ssh option, and the hardening
        // options are part of the command whatever the user's ssh config says.
        let args: Vec<String> = s.arguments().iter().map(|a| a.to_string_lossy().into_owned()).collect();
        assert_eq!(&args[args.len() - 2..], ["--", "member@box.example"]);
        for want in ["BatchMode=yes", "StrictHostKeyChecking=yes", "ClearAllForwardings=yes", "ControlPath=none", "ConnectTimeout=30"] {
            assert!(args.iter().any(|a| a == want), "{want} missing from {args:?}");
        }
        let mut with_identity = s.clone();
        with_identity.identity = Some("/keys/member".into());
        let args: Vec<String> = with_identity.arguments().iter().map(|a| a.to_string_lossy().into_owned()).collect();
        assert!(args.windows(3).any(|w| w == ["-i", "/keys/member", "-o"]) && args.contains(&"IdentitiesOnly=yes".to_string()));
    }

    #[test]
    fn ssh_failures_before_the_channel_opens_are_certainly_unsent_and_named() {
        for (dest, named) in [("hostkey", "host key verification failed"), ("denied", "authentication refused"),
            ("refused", "destination unreachable"), ("garbled", "session not established")] {
            let (op, req) = standin(dest);
            let said = unsent(op.call(2, b"call"));
            assert!(said.contains(named), "{dest}: {said}");
            assert!(!req.exists(), "{dest}: a request reached the stand-in");
        }
        let (op, _) = standin("hostkey");
        assert!(unsent(op.call(2, b"call")).contains("known_hosts"), "the host-key refusal says what to do");
    }

    #[test]
    fn a_session_that_never_opens_times_out_as_certainly_unsent() {
        let (op, req) = standin("silent");
        let started = std::time::Instant::now();
        let said = unsent(op.call(2, b"call"));
        assert!(said.contains("not within 2s"), "{said}");
        assert!(started.elapsed() < Duration::from_secs(10));
        assert!(!req.exists());
    }

    #[test]
    fn requests_round_trip_over_one_reused_ssh_session_with_the_unix_frames() {
        let (op, req) = standin("serve-answer");
        assert_eq!(op.call(2, b"first"), Ok(Reply::Answer(b"ok".to_vec())));
        assert_eq!(op.call(2, b"second"), Ok(Reply::Answer(b"ok".to_vec())));
        // Both requests arrived, byte-for-byte the frames the unix socket would carry, length-prefixed
        // by the transport (the stand-in strips the length), over ONE session.
        let seen = std::fs::read(&req).unwrap();
        let expect = [request(b"{}", None, 2, b"first").unwrap(), request(b"{}", None, 2, b"second").unwrap()].concat();
        assert_eq!(seen, expect);
        assert!(op.session.lock().unwrap().is_some(), "the session is kept for the next request");
    }

    #[test]
    fn an_ssh_refusal_and_a_socket_rejection_classify_like_the_unix_socket() {
        let (op, _) = standin("serve-refuse");
        assert_eq!(op.call(2, b"c"), Ok(Reply::Refused(b"no".to_vec())));
        let (op, _) = standin("serve-reject");
        assert!(matches!(op.call(2, b"c"), Err(Failure::Unsent(d)) if d.contains("socket rejected request")));
    }

    #[test]
    fn a_hangup_after_the_write_is_uncertain_closes_the_session_and_is_never_resent() {
        let (op, req) = standin("serve-hangup");
        assert!(matches!(op.call(2, b"call"), Err(Failure::Uncertain(_))));
        assert!(op.session.lock().unwrap().is_none(), "the dead session is closed");
        // The stand-in saw the request exactly once: the SDK did not resend it on a new session.
        assert_eq!(std::fs::read(&req).unwrap(), request(b"{}", None, 2, b"call").unwrap());
        // A later, explicit call opens a NEW session (and is itself a new request).
        assert!(matches!(op.call(2, b"call"), Err(Failure::Uncertain(_))));
    }

    #[test]
    fn a_garbled_or_missing_reply_is_uncertain_not_unsent() {
        let (op, _) = standin("serve-garbage");
        assert!(matches!(op.call(2, b"c"), Err(Failure::Uncertain(d)) if d.contains("response read")));
        let (op, _) = standin("serve-mute");
        let started = std::time::Instant::now();
        assert!(matches!(op.call(2, b"c"), Err(Failure::Uncertain(d)) if d.contains("none within 2s")));
        assert!(started.elapsed() < Duration::from_secs(10));
    }

    #[test]
    fn a_session_that_ended_between_requests_is_replaced_before_anything_is_written() {
        let (op, req) = standin("serve-oneshot");
        assert_eq!(op.call(2, b"one"), Ok(Reply::Answer(b"ok".to_vec())));
        std::thread::sleep(Duration::from_millis(300)); // the stand-in has exited; its pipe is closed
        assert_eq!(op.call(2, b"two"), Ok(Reply::Answer(b"ok".to_vec())), "a fresh session served the second request");
        let expect = [request(b"{}", None, 2, b"one").unwrap(), request(b"{}", None, 2, b"two").unwrap()].concat();
        assert_eq!(std::fs::read(&req).unwrap(), expect, "each request was written exactly once");
    }
}
