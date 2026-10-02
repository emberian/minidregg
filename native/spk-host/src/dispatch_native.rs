//! One private, no-retry Mini author/submit operation for the resident SPK
//! supervisor. Op34's callback bytes are retained before source inspection;
//! an uncertain write/read leaves a durable marker and cannot be repeated.
#![allow(dead_code)] // Resident authorized supervisor is not enabled yet.

use crate::dispatch_author::FixedAuthoring;
use crate::dispatch_inspection::{
    match_inspection, FixedCustody, HttpProjection, MatchedInspection,
};
use crate::hostd::{DispatchIdentity, Journal};
use crate::native_dispatch::{parse_op34_response, Op34Reply};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const HOST_MAX_FRAME: usize = 12_102_760;
const MAX_CONFIG: usize = 65_536;
const MAX_INSPECTION: usize = 96_822_080;
const MAX_AUTHOR_JSON: u64 = 22 * 1024 * 1024;
const RESPONSE_DEADLINE: Duration = Duration::from_secs(600);

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn hex(bytes: &[u8]) -> String {
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(result, "{byte:02x}").expect("writing to String");
    }
    result
}

fn read_bounded(path: &Path, bound: usize) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(path)?
        .take(bound as u64 + 1)
        .read_to_end(&mut bytes)?;
    if bytes.is_empty() || bytes.len() > bound {
        return Err(invalid("private native artifact size refused"));
    }
    Ok(bytes)
}

pub(crate) fn write_new(directory: &Path, name: &str, bytes: &[u8]) -> io::Result<PathBuf> {
    if bytes.is_empty() || bytes.len() > MAX_INSPECTION {
        return Err(invalid("private native artifact size refused"));
    }
    let path = directory.join(name);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    File::open(directory)?.sync_all()?;
    Ok(path)
}

pub(crate) fn private_dir(path: &Path) -> io::Result<()> {
    let metadata = fs::symlink_metadata(path)?;
    if !path.is_absolute()
        || !metadata.is_dir()
        || metadata.uid() != unsafe { libc::geteuid() }
        || metadata.permissions().mode() & 0o777 != 0o700
    {
        return Err(invalid("native attempt directory is not owner-private"));
    }
    Ok(())
}

/// Establish transport before sending any operation bytes. Linux AF_UNIX can
/// block indefinitely on a full listener backlog even with later IO timeouts.
/// EAGAIN is not an in-progress connection: polling that socket reports HUP
/// immediately, so retry it with bounded local backoff instead of busy polling.
pub(crate) fn connect_deadline(path: &Path, deadline: Instant) -> io::Result<UnixStream> {
    use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
    use std::os::unix::ffi::OsStrExt;
    let timeout = || io::Error::new(io::ErrorKind::TimedOut, "Mini operator connect deadline");
    let bytes = path.as_os_str().as_bytes();
    // Zero initializes the unused sun_path tail and supplies its NUL terminator.
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if bytes.is_empty() || bytes.len() >= address.sun_path.len() || bytes.contains(&0) {
        return Err(invalid("Mini operator socket path refused"));
    }
    address.sun_family = libc::AF_UNIX as libc::sa_family_t;
    for (dst, src) in address.sun_path.iter_mut().zip(bytes) {
        *dst = *src as libc::c_char;
    }
    let length =
        (std::mem::offset_of!(libc::sockaddr_un, sun_path) + bytes.len() + 1) as libc::socklen_t;
    if Instant::now() >= deadline {
        return Err(timeout());
    }
    let raw = unsafe {
        libc::socket(
            libc::AF_UNIX,
            libc::SOCK_STREAM | libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC,
            0,
        )
    };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    // Owned immediately so every failure closes this attempt's fd.
    let fd = unsafe { OwnedFd::from_raw_fd(raw) };
    loop {
        let left = deadline.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err(timeout());
        }
        let result = unsafe {
            libc::connect(
                fd.as_raw_fd(),
                &address as *const _ as *const libc::sockaddr,
                length,
            )
        };
        if result == 0 {
            break;
        }
        let error = io::Error::last_os_error();
        match error.raw_os_error() {
            Some(libc::EISCONN) => break,
            Some(libc::EINTR) => continue,
            Some(libc::EAGAIN) => {
                std::thread::sleep(left.min(Duration::from_millis(10)));
            }
            Some(libc::EINPROGRESS) | Some(libc::EALREADY) => {
                let mut pollfd = libc::pollfd {
                    fd: fd.as_raw_fd(),
                    events: libc::POLLOUT,
                    revents: 0,
                };
                loop {
                    let left = deadline.saturating_duration_since(Instant::now());
                    if left.is_zero() {
                        return Err(timeout());
                    }
                    let ms = left.as_millis().saturating_add(1).min(i32::MAX as u128) as i32;
                    let result = unsafe { libc::poll(&mut pollfd, 1, ms) };
                    if result < 0 {
                        let error = io::Error::last_os_error();
                        if error.kind() == io::ErrorKind::Interrupted {
                            continue;
                        }
                        return Err(error);
                    }
                    if result == 0 {
                        continue;
                    }
                    let mut socket_error: libc::c_int = 0;
                    let mut length = std::mem::size_of_val(&socket_error) as libc::socklen_t;
                    if unsafe {
                        libc::getsockopt(
                            fd.as_raw_fd(),
                            libc::SOL_SOCKET,
                            libc::SO_ERROR,
                            &mut socket_error as *mut _ as *mut libc::c_void,
                            &mut length,
                        )
                    } < 0
                    {
                        return Err(io::Error::last_os_error());
                    }
                    if socket_error != 0 {
                        return Err(io::Error::from_raw_os_error(socket_error));
                    }
                    break;
                }
                break;
            }
            _ => return Err(error),
        }
    }
    if Instant::now() >= deadline {
        return Err(timeout());
    }
    let stream = UnixStream::from(fd);
    stream.set_nonblocking(false)?;
    Ok(stream)
}

fn read_exact_deadline(
    stream: &mut UnixStream,
    bytes: &mut [u8],
    deadline: Instant,
) -> io::Result<()> {
    let mut received = 0;
    while received < bytes.len() {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "Mini Host response deadline",
            ));
        }
        stream.set_read_timeout(Some(remaining))?;
        let count = stream.read(&mut bytes[received..])?;
        if count == 0 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "Mini Host response closed",
            ));
        }
        received += count;
    }
    Ok(())
}

/// The socket belongs to the separately started operator broker, never a
/// tenant frontend. Version 2 pins the exact Host ELF and full config bytes.
#[derive(Clone)]
pub(crate) struct PrivateOperator {
    pub host: PathBuf,
    pub config: PathBuf,
    pub socket: PathBuf,
    pub host_sha256: String,
    pub config_sha256: String,
}

/// Opaque bytes returned by our pinned private op152 invocation and source
/// inspector. Public only for the package's standalone fd3 smoke binary;
/// callers cannot construct this from HTTP or an arbitrary JSON document.
pub struct PrivateContinuityReply {
    payload: Vec<u8>,
    inspection: Vec<u8>,
    challenge: Vec<u8>,
}

impl PrivateContinuityReply {
    pub fn payload(&self) -> &[u8] {
        &self.payload
    }
    pub fn inspection(&self) -> &[u8] {
        &self.inspection
    }
    pub fn challenge(&self) -> &[u8] {
        &self.challenge
    }
}

impl PrivateOperator {
    pub(crate) fn pinned_config(&self) -> io::Result<Vec<u8>> {
        self.check_pin()
    }

    fn check_pin(&self) -> io::Result<Vec<u8>> {
        let host = fs::symlink_metadata(&self.host)?;
        if !self.host.is_absolute() || !host.is_file() || host.permissions().mode() & 0o022 != 0 {
            return Err(invalid("selected Mini Host image identity refused"));
        }
        let mut reader = File::open(&self.host)?;
        let mut digest = Sha256::new();
        let mut chunk = [0u8; 64 * 1024];
        loop {
            let count = reader.read(&mut chunk)?;
            if count == 0 {
                break;
            }
            digest.update(&chunk[..count]);
        }
        if self.host_sha256 != hex(&digest.finalize()) {
            return Err(invalid("selected Mini Host SHA-256 drift"));
        }
        let config = read_bounded(&self.config, MAX_CONFIG)?;
        if self.config_sha256 != hex(&Sha256::digest(&config)) {
            return Err(invalid("selected Mini Host config SHA-256 drift"));
        }
        let parent = self
            .socket
            .parent()
            .ok_or_else(|| invalid("operator socket lacks parent"))?;
        private_dir(parent)?;
        let socket = fs::symlink_metadata(&self.socket)?;
        if !socket.file_type().is_socket()
            || socket.uid() != unsafe { libc::geteuid() }
            || socket.permissions().mode() & 0o077 != 0
        {
            return Err(invalid("Mini operator socket identity refused"));
        }
        Ok(config)
    }

    pub(crate) fn tool(
        &self,
        command: &str,
        kind: &str,
        input: &Path,
        output: &Path,
    ) -> io::Result<Vec<u8>> {
        self.tool_until(
            command,
            kind,
            input,
            output,
            Instant::now() + RESPONSE_DEADLINE,
        )
    }

    pub(crate) fn tool_until(
        &self,
        command: &str,
        kind: &str,
        input: &Path,
        output: &Path,
        deadline: Instant,
    ) -> io::Result<Vec<u8>> {
        let _ = self.check_pin()?;
        let cap = match command {
            "author" => MAX_AUTHOR_JSON,
            "inspect" => (HOST_MAX_FRAME - 1) as u64,
            "signatures" => 1024 * 1024,
            "profile" => 1024,
            _ => return Err(invalid("Mini Host helper command unavailable")),
        };
        private_dir(
            input
                .parent()
                .ok_or_else(|| invalid("helper input parent absent"))?,
        )?;
        let meta = fs::symlink_metadata(input)?;
        if !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
            || meta.len() == 0
            || meta.len() > cap
        {
            return Err(invalid("Mini Host helper input identity or size refused"));
        }
        let mut process = Command::new(&self.host);
        process.arg(&self.config).arg(command);
        if command == "profile" {
            let output_file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW)
                .open(output)?;
            process.stdout(Stdio::from(output_file));
        } else {
            if !kind.is_empty() {
                process.arg(kind);
            }
            process.arg(input).arg(output).stdout(Stdio::null());
        }
        process.stdin(Stdio::null()).stderr(Stdio::null());
        if Instant::now() >= deadline {
            return Err(invalid("Mini helper deadline"));
        }
        let mut child = process.spawn()?;
        let status = loop {
            match child.try_wait() {
                Ok(Some(status)) => break status,
                Ok(None) => {}
                Err(error) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(error);
                }
            }
            if Instant::now() >= deadline {
                let _ = child.kill();
                let _ = child.wait();
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "Mini helper deadline",
                ));
            }
            // Bounded local child wait, never a Mini authority poll.
            std::thread::sleep(Duration::from_millis(10));
        };
        if !status.success() {
            return Err(invalid("pinned Mini Host helper refused"));
        }
        read_bounded(
            output,
            if command == "inspect" {
                MAX_INSPECTION
            } else {
                HOST_MAX_FRAME - 1
            },
        )
    }

    pub(crate) fn invoke(&self, operation: u8, payload: &[u8]) -> io::Result<Vec<u8>> {
        self.invoke_until(operation, payload, Instant::now() + RESPONSE_DEADLINE)
    }

    pub(crate) fn invoke_until(
        &self,
        operation: u8,
        payload: &[u8],
        deadline: Instant,
    ) -> io::Result<Vec<u8>> {
        let config = self.check_pin()?;
        if Instant::now() >= deadline {
            return Err(invalid("Mini operator deadline"));
        }
        if payload.is_empty() || payload.len() >= HOST_MAX_FRAME {
            return Err(invalid("Mini operator request size refused"));
        }
        let host_sha = self.host_sha256.as_bytes();
        if host_sha.len() != 64 {
            return Err(invalid("Mini Host SHA-256 pin malformed"));
        }
        let mut sha = [0u8; 32];
        for (index, byte) in sha.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&self.host_sha256[index * 2..index * 2 + 2], 16)
                .map_err(|_| invalid("Mini Host SHA-256 pin malformed"))?;
        }
        let mut envelope = Vec::with_capacity(1 + 4 + config.len() + 32 + 1 + payload.len());
        envelope.push(2);
        envelope.extend_from_slice(&(config.len() as u32).to_le_bytes());
        envelope.extend_from_slice(&config);
        envelope.extend_from_slice(&sha);
        envelope.push(operation);
        envelope.extend_from_slice(payload);
        let mut stream = connect_deadline(&self.socket, deadline)?;
        let write_deadline = deadline.min(Instant::now() + Duration::from_secs(10));
        let mut framed = Vec::with_capacity(envelope.len() + 4);
        framed.extend_from_slice(&(envelope.len() as u32).to_le_bytes());
        framed.extend_from_slice(&envelope);
        let mut sent = 0;
        while sent < framed.len() {
            let remaining = write_deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "uncertain Mini Host request write",
                ));
            }
            stream.set_write_timeout(Some(remaining))?;
            let count = stream.write(&framed[sent..])?;
            if count == 0 {
                return Err(io::Error::new(
                    io::ErrorKind::WriteZero,
                    "uncertain Mini Host request write",
                ));
            }
            sent += count;
        }
        stream.flush()?;
        let mut prefix = [0u8; 4];
        read_exact_deadline(&mut stream, &mut prefix, deadline)?;
        let length = u32::from_le_bytes(prefix) as usize;
        if !(2..=HOST_MAX_FRAME).contains(&length) {
            return Err(invalid("Mini operator reply frame size refused"));
        }
        let mut reply = vec![0u8; length + 4];
        reply[..4].copy_from_slice(&prefix);
        read_exact_deadline(&mut stream, &mut reply[4..], deadline)?;
        if reply[4] != operation && reply[4] != 255 {
            return Err(invalid("Mini operator reply opcode mismatch"));
        }
        Ok(reply)
    }
}

/// Every directory is freshly created under the resident's private journal.
/// Renewal artifacts have no ledger effect and are removed after inspection;
/// active storage is bounded by one attempt per open stream.
struct ContinuityAttemptDir(PathBuf);
impl ContinuityAttemptDir {
    fn create(parent: &Path) -> io::Result<Self> {
        private_dir(parent)?;
        let mut nonce = [0u8; 32];
        File::open("/dev/urandom")?.read_exact(&mut nonce)?;
        let path = parent.join(format!("continuity-{}", hex(&nonce)));
        DirBuilder::new().mode(0o700).create(&path)?;
        Ok(Self(path))
    }
}
impl Drop for ContinuityAttemptDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

impl PrivateOperator {
    /// Pinned executable metadata, not a current-authority grant.
    pub(crate) fn continuity_namespace(&self, parent: &Path) -> io::Result<(String, String)> {
        let attempt = ContinuityAttemptDir::create(parent)?;
        let input = write_new(&attempt.0, "request.json", b"{}")?;
        let bytes = self.tool("profile", "", &input, &attempt.0.join("profile.json"))?;
        let value: serde_json::Value = serde_json::from_slice(&bytes)?;
        let field = |name| {
            value
                .get(name)
                .and_then(serde_json::Value::as_str)
                .map(str::to_owned)
                .ok_or_else(|| invalid("pinned source namespace missing"))
        };
        Ok((field("domain")?, field("semantics")?))
    }

    /// Only this function constructs the opaque transport-provenance wrapper.
    /// It never calls op34, writes an active-dispatch marker, or reaches app fd3.
    pub(crate) fn probe_continuity(
        &self,
        custody: &FixedAuthoring,
        challenge: &crate::web_socket::RenewalChallenge,
        parent: &Path,
    ) -> io::Result<PrivateContinuityReply> {
        challenge.check()?;
        let deadline = challenge.response_deadline();
        let attempt = ContinuityAttemptDir::create(parent)?;
        let b = challenge.binding();
        let tip = challenge.minimum_tip();
        let value = json!({"domain":b.domain,"semantics":b.semantics,
            "app":b.app,"appGeneration":b.app_generation,"session":b.session,
            "sessionGeneration":b.session_generation,"subject":b.subject,
            "ticketResource":b.ticket_resource,"sessionFingerprintHex":hex(&b.session_fingerprint),
            "streamNonceHex":challenge.stream_nonce_hex(),"attemptNonceHex":challenge.attempt_nonce_hex(),
            "minimumHeight":tip.height,"minimumWorldRoot":tip.world_root});
        let input = write_new(&attempt.0, "challenge.json", &serde_json::to_vec(&value)?)?;
        let challenge_bytes = self.tool_until(
            "author",
            "application-stream-continuity-challenge",
            &input,
            &attempt.0.join("challenge.bin"),
            deadline,
        )?;
        let path = format!("?{}", hex(&challenge_bytes));
        let headers = vec![(
            "sec-websocket-protocol".to_owned(),
            "dregg.authority.continuity.v1".to_owned(),
        )];
        let http = HttpProjection {
            method: "WEBSOCKET",
            path_and_query: &path,
            ordered_headers: &headers,
            body: &[],
            route: crate::dispatch_inspection::Route::Browser,
        };
        let ingress = author_signed_ingress(
            self,
            custody,
            &http,
            "0",
            &attempt.0.join("signed"),
            deadline,
        )?;
        challenge.check()?;
        let request = json!({"challengeHex":hex(&challenge_bytes),"ingressHex":hex(&ingress)});
        let request_json = write_new(
            &attempt.0,
            "continuity.json",
            &serde_json::to_vec(&request)?,
        )?;
        let request_bytes = self.tool_until(
            "author",
            "application-stream-continuity-request",
            &request_json,
            &attempt.0.join("continuity.bin"),
            deadline,
        )?;
        let response = self.invoke_until(152, &request_bytes, deadline)?;
        let payload = response
            .get(5..)
            .ok_or_else(|| invalid("short continuity reply"))?;
        if response.get(4) != Some(&152)
            || !payload.starts_with(b"DREGG/APPLICATION/STREAM-CONTINUITY-ATTESTATION/v1")
        {
            return Err(invalid("Mini refused current stream continuity"));
        }
        let response_path = write_new(&attempt.0, "attestation.bin", payload)?;
        let inspection = self.tool_until(
            "inspect",
            "application-stream-continuity-attestation",
            &response_path,
            &attempt.0.join("inspection.json"),
            deadline,
        )?;
        challenge.check()?;
        Ok(PrivateContinuityReply {
            payload: payload.to_vec(),
            inspection,
            challenge: challenge_bytes,
        })
    }
}

#[derive(Clone)]
pub(crate) struct ContinuityCustody {
    pub operator: PrivateOperator,
    pub custody: FixedAuthoring,
    pub attempt_parent: PathBuf,
}

/// At most one native probe is outstanding per live stream. Timers run on
/// the existing fd3 LocalSet; bounded blocking helper IO runs off that thread.
pub(crate) async fn renew_stream(
    lease: crate::web_socket::StreamLease,
    custody: ContinuityCustody,
) {
    loop {
        let delay = match lease.renewal_delay() {
            Ok(delay) => delay,
            Err(_) => return,
        };
        tokio::select! {
            biased;
            _ = lease.ended() => return,
            _ = tokio::time::sleep(delay) => {},
        }
        let challenge = match lease.begin_renewal() {
            Ok(c) => c,
            Err(_) => {
                lease.revoke();
                return;
            }
        };
        let custody = custody.clone();
        let result = tokio::select! {
            biased;
            _ = lease.ended() => return,
            result = tokio::task::spawn_blocking(move || {
                let reply = custody.operator.probe_continuity(&custody.custody, &challenge, &custody.attempt_parent)?;
                crate::stream_continuity::verify_reply(challenge, &reply)
            }) => result.map_err(io::Error::other).and_then(|result| result),
        };
        if result.and_then(|grant| lease.renew(grant)).is_err() {
            lease.revoke();
            eprintln!("spk-host: stream continuity refused or unavailable; lease ended");
            return;
        }
    }
}

pub(crate) struct CommittedDispatch {
    pub payload: Vec<u8>,
    pub matched: MatchedInspection,
    active_marker: PathBuf,
    active_bytes: Vec<u8>,
}

pub(crate) struct RecordedDispatch {
    pub identity: DispatchIdentity,
    active_marker: PathBuf,
    active_bytes: Vec<u8>,
}

impl RecordedDispatch {
    /// Only a definite RPC result while the same app generation is Running
    /// releases the global native-submit marker. Timeout, EOF, or a concurrent
    /// fence leaves both physical and native attempt records for audit.
    pub(crate) fn finish(self, journal: &Journal, delivered: bool) -> io::Result<()> {
        journal.finish_dispatch(&self.identity, delivered)?;
        if fs::read(&self.active_marker)? != self.active_bytes {
            return Err(invalid(
                "native submit marker drift after physical completion",
            ));
        }
        fs::remove_file(&self.active_marker)?;
        File::open(
            self.active_marker
                .parent()
                .ok_or_else(|| invalid("marker parent absent"))?,
        )?
        .sync_all()
    }
}

impl CommittedDispatch {
    /// The native op34 marker is only cleared after hostd has fsynced its
    /// separate DeliveryRequested tombstone. A crash in either interval
    /// blocks new native submissions until an operator audits exact records.
    pub(crate) fn record_delivery_requested(
        self,
        journal: &Journal,
    ) -> io::Result<RecordedDispatch> {
        if fs::read(&self.active_marker)? != self.active_bytes {
            return Err(invalid("native submit marker drift"));
        }
        let record = journal
            .read()?
            .ok_or_else(|| invalid("app journal absent"))?;
        let invocation_id = record
            .invocation_id()
            .ok_or_else(|| invalid("app unit invocation absent"))?;
        let identity = DispatchIdentity {
            permit_sha256: hex(&Sha256::digest(&self.payload)),
            request_digest: self.matched.physical_request_digest,
            app: self.matched.app,
            app_generation: self.matched.app_generation,
            invocation_id: invocation_id.to_owned(),
            operation_id: self.matched.operation_id,
            session_resource: self.matched.session_resource,
            session_generation: self.matched.session_generation,
            dispatch_transaction: self.matched.dispatch_transaction,
            dispatch_event: self.matched.dispatch_event,
        };
        journal.request_dispatch(identity.clone(), &self.payload)?;
        Ok(RecordedDispatch {
            identity,
            active_marker: self.active_marker,
            active_bytes: self.active_bytes,
        })
    }
}

/// The attempt directory is new and durable before any mutation. A marker is
/// fsynced before op34; once present, this function refuses to run again for
/// the same attempt even if the Host response was lost. Historical op35 may
/// inform an audit, but it can never mint a fresh physical delivery permit.
fn author_signed_ingress(
    operator: &PrivateOperator,
    custody: &FixedAuthoring,
    http: &HttpProjection<'_>,
    operation_id: &str,
    attempt_dir: &Path,
    deadline: Instant,
) -> io::Result<Vec<u8>> {
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("attempt parent missing"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let request = custody.request_json(operation_id, http)?;
    let request_json = write_new(attempt_dir, "request.json", &serde_json::to_vec(&request)?)?;
    let request_bin = attempt_dir.join("request.bin");
    let request_bytes = operator.tool_until(
        "author",
        "application-dispatch-request",
        &request_json,
        &request_bin,
        deadline,
    )?;
    let plan_reply = operator.invoke_until(36, &request_bytes, deadline)?;
    if plan_reply[4] != 36 {
        return Err(invalid("Mini dispatch authoring refused"));
    }
    let plan_bytes = &plan_reply[5..];
    let plan_bin = write_new(attempt_dir, "plan.bin", plan_bytes)?;
    let plan_json_path = attempt_dir.join("plan.json");
    let plan_json = operator.tool_until(
        "inspect",
        "application-dispatch-plan",
        &plan_bin,
        &plan_json_path,
        deadline,
    )?;
    let signatures = custody.sign_plan(plan_bytes, &plan_json, &request_bytes, &request)?;
    let signatures_json = write_new(
        attempt_dir,
        "signatures.json",
        &serde_json::to_vec(&signatures)?,
    )?;
    let signatures_bin_path = attempt_dir.join("signatures.bin");
    let signatures_bin = operator.tool_until(
        "signatures",
        "",
        &signatures_json,
        &signatures_bin_path,
        deadline,
    )?;
    let mut pair = Vec::with_capacity(4 + plan_bytes.len() + signatures_bin.len());
    pair.extend_from_slice(&(plan_bytes.len() as u32).to_le_bytes());
    pair.extend_from_slice(plan_bytes);
    pair.extend_from_slice(&signatures_bin);
    let ingress_reply = operator.invoke_until(37, &pair, deadline)?;
    if ingress_reply[4] != 37 {
        return Err(invalid("Mini dispatch assembly refused"));
    }
    let ingress = &ingress_reply[5..];
    write_new(attempt_dir, "ingress.bin", ingress)?;
    Ok(ingress.to_vec())
}

pub(crate) fn author_and_submit(
    operator: &PrivateOperator,
    custody: &FixedAuthoring,
    http: &HttpProjection<'_>,
    operation_id: &str,
    attempt_dir: &Path,
) -> io::Result<CommittedDispatch> {
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("attempt parent missing"))?;
    let ingress = author_signed_ingress(
        operator,
        custody,
        http,
        operation_id,
        attempt_dir,
        Instant::now() + RESPONSE_DEADLINE,
    )?;
    let marker = json!({"protocol":"mini-spk-dispatch-submit-requested-v1",
        "operationId":operation_id,"ingressSha256":hex(&Sha256::digest(&ingress))});
    write_new(
        attempt_dir,
        "submit-requested.json",
        &serde_json::to_vec(&marker)?,
    )?;
    let active_marker = parent.join("native-dispatch-active.json");
    let active_bytes = serde_json::to_vec(&marker)?;
    // The global marker is separate from the attempt so a new operation ID
    // cannot bypass an earlier uncertain op34 by choosing a different dir.
    let mut active_file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&active_marker)?;
    active_file.write_all(&active_bytes)?;
    active_file.sync_all()?;
    File::open(parent)?.sync_all()?;
    let reply = operator.invoke(34, &ingress)?;
    write_new(attempt_dir, "op34-frame.bin", &reply)?;
    let payload = match parse_op34_response(&reply)? {
        Op34Reply::CommittedBytes(payload) => payload.to_vec(),
        Op34Reply::OutcomeBytes(_) => {
            return Err(invalid("Mini op34 did not commit a delivery permit"))
        }
    };
    let payload_path = write_new(attempt_dir, "committed-payload.bin", &payload)?;
    let inspection_path = attempt_dir.join("inspection.json");
    let inspection = operator.tool(
        "inspect",
        "application-dispatch-committed",
        &payload_path,
        &inspection_path,
    )?;
    let fixed = FixedCustody {
        app: &custody.app,
        subject: &custody.subject,
        session: &custody.session,
        ticket: &custody.ticket_resource,
    };
    let matched = match_inspection(&payload, &inspection, http, &fixed)?;
    if matched.operation_id != operation_id {
        return Err(invalid("committed physical operation ID drift"));
    }
    Ok(CommittedDispatch {
        payload,
        matched,
        active_marker,
        active_bytes,
    })
}

/// Unforgeable outside this native pipeline: exact retained private op154 bytes.
pub(crate) struct PrivateRouteAdmissionReply {
    payload: Vec<u8>,
    inspection: Vec<u8>,
    challenge: Vec<u8>,
}
impl PrivateRouteAdmissionReply {
    pub(crate) fn payload(&self) -> &[u8] {
        &self.payload
    }
    pub(crate) fn inspection(&self) -> &[u8] {
        &self.inspection
    }
    pub(crate) fn challenge(&self) -> &[u8] {
        &self.challenge
    }
}

impl PrivateOperator {
    /// Register a new binding without submitting an app request or altering any
    /// existing lease. All source/helper/transport work shares one deadline.
    pub(crate) fn admit_resident_route(
        &self,
        custody: &FixedAuthoring,
        expected_app_generation: &str,
        expected_session_generation: &str,
        registration_nonce_hex: &str,
        parent: &Path,
    ) -> io::Result<crate::route_admission::VerifiedRouteAdmission> {
        custody.validate()?;
        let deadline = Instant::now() + Duration::from_secs(60);
        let attempt = ContinuityAttemptDir::create(parent)?;
        let profile_input = write_new(&attempt.0, "profile-input.json", b"{}")?;
        let profile_bytes = self.tool_until(
            "profile",
            "",
            &profile_input,
            &attempt.0.join("profile.json"),
            deadline,
        )?;
        let profile: serde_json::Value = serde_json::from_slice(&profile_bytes)?;
        let field = |name| {
            profile
                .get(name)
                .and_then(serde_json::Value::as_str)
                .map(str::to_owned)
                .ok_or_else(|| invalid("pinned route namespace missing"))
        };
        let expected = crate::route_admission::RouteAdmissionExpectation {
            binding: crate::stream_continuity::ContinuityBinding {
                domain: field("domain")?,
                semantics: field("semantics")?,
                app: custody.app.clone(),
                app_generation: expected_app_generation.to_owned(),
                session: custody.session.clone(),
                session_generation: expected_session_generation.to_owned(),
                subject: custody.subject.clone(),
                ticket_resource: custody.ticket_resource.clone(),
                session_fingerprint: [0; 32],
            },
            session_kind: custody.session_kind.clone(),
            registration_nonce_hex: registration_nonce_hex.to_owned(),
        };
        expected.validate()?;
        let b = &expected.binding;
        let challenge_input = json!({"domain":b.domain,"semantics":b.semantics,
            "app":b.app,"appGeneration":b.app_generation,"session":b.session,
            "sessionGeneration":b.session_generation,"subject":b.subject,"ticketResource":b.ticket_resource,
            "sessionKind":expected.session_kind,"registrationNonceHex":expected.registration_nonce_hex});
        let input = write_new(
            &attempt.0,
            "challenge.json",
            &serde_json::to_vec(&challenge_input)?,
        )?;
        let challenge = self.tool_until(
            "author",
            "application-route-admission-challenge",
            &input,
            &attempt.0.join("challenge.bin"),
            deadline,
        )?;
        let path = format!("?{}", hex(&challenge));
        let headers = vec![(
            "sec-websocket-protocol".to_owned(),
            "dregg.authority.route-admission.v1".to_owned(),
        )];
        // This is a reserved source-only probe, never an app path/RPC. An API
        // probe uses the empty relative root; actual deliveries still use the
        // signature-verified package prefix in dispatch_delivery.
        let route = if custody.session_kind == "web" {
            crate::dispatch_inspection::Route::Browser
        } else {
            crate::dispatch_inspection::Route::Api { signed_path: "/" }
        };
        let http = HttpProjection {
            method: "WEBSOCKET",
            path_and_query: &path,
            ordered_headers: &headers,
            body: &[],
            route,
        };
        let ingress = author_signed_ingress(
            self,
            custody,
            &http,
            "0",
            &attempt.0.join("signed"),
            deadline,
        )?;
        let request = json!({"challengeHex":hex(&challenge),"ingressHex":hex(&ingress)});
        let request_json = write_new(&attempt.0, "request.json", &serde_json::to_vec(&request)?)?;
        let request_bytes = self.tool_until(
            "author",
            "application-route-admission-request",
            &request_json,
            &attempt.0.join("request.bin"),
            deadline,
        )?;
        let response = self.invoke_until(154, &request_bytes, deadline)?;
        let payload = response
            .get(5..)
            .ok_or_else(|| invalid("short route admission reply"))?;
        if response.get(4) != Some(&154)
            || !payload.starts_with(b"DREGG/APPLICATION/ROUTE-ADMISSION-ATTESTATION/v1")
        {
            return Err(invalid("Mini refused current route admission"));
        }
        let response_path = write_new(&attempt.0, "attestation.bin", payload)?;
        let inspection = self.tool_until(
            "inspect",
            "application-route-admission-attestation",
            &response_path,
            &attempt.0.join("inspection.json"),
            deadline,
        )?;
        if Instant::now() >= deadline {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "route admission deadline",
            ));
        }
        crate::route_admission::verify_reply(
            &expected,
            &PrivateRouteAdmissionReply {
                payload: payload.to_vec(),
                inspection,
                challenge,
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::net::UnixListener;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn full_unix_backlog_obeys_connect_deadline_and_recovers() {
        use std::os::fd::AsRawFd;
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root =
            std::env::temp_dir().join(format!("mini-spk-connect-{}-{nonce}", std::process::id()));
        DirBuilder::new().mode(0o700).create(&root).unwrap();
        let path = root.join("socket");
        let listener = UnixListener::bind(&path).unwrap();
        assert_eq!(unsafe { libc::listen(listener.as_raw_fd(), 1) }, 0);
        let first = connect_deadline(&path, Instant::now() + Duration::from_secs(1)).unwrap();
        let second = connect_deadline(&path, Instant::now() + Duration::from_secs(1)).unwrap();
        let started = Instant::now();
        assert_eq!(
            connect_deadline(&path, started + Duration::from_millis(40))
                .unwrap_err()
                .kind(),
            io::ErrorKind::TimedOut
        );
        assert!(started.elapsed() < Duration::from_millis(500));
        let (accepted, _) = listener.accept().unwrap();
        let recovered = connect_deadline(&path, Instant::now() + Duration::from_secs(1)).unwrap();
        drop((accepted, first, second, recovered, listener));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn private_v2_operator_frame_pins_host_config_and_socket() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root =
            std::env::temp_dir().join(format!("mini-spk-operator-{}-{nonce}", std::process::id()));
        DirBuilder::new().mode(0o700).create(&root).unwrap();
        let host = root.join("host");
        fs::copy("/usr/bin/true", &host).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o755)).unwrap();
        let config = root.join("config.json");
        fs::write(&config, b"{\"fixture\":true}").unwrap();
        let socket = root.join("operator.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o600)).unwrap();
        let operator = PrivateOperator {
            host: host.clone(),
            config: config.clone(),
            socket: socket.clone(),
            host_sha256: hex(&Sha256::digest(fs::read(&host).unwrap())),
            config_sha256: hex(&Sha256::digest(fs::read(&config).unwrap())),
        };
        let server = std::thread::spawn(move || {
            let (mut peer, _) = listener.accept().unwrap();
            let mut prefix = [0u8; 4];
            peer.read_exact(&mut prefix).unwrap();
            let mut envelope = vec![0; u32::from_le_bytes(prefix) as usize];
            peer.read_exact(&mut envelope).unwrap();
            assert_eq!(envelope[0], 2);
            let config_len = u32::from_le_bytes(envelope[1..5].try_into().unwrap()) as usize;
            assert_eq!(&envelope[5..5 + config_len], b"{\"fixture\":true}");
            assert_eq!(envelope[5 + config_len + 32], 36);
            assert_eq!(&envelope[5 + config_len + 33..], b"source request");
            peer.write_all(&[5, 0, 0, 0, 36, b'p', b'l', b'a', b'n'])
                .unwrap();
        });
        assert_eq!(
            operator.invoke(36, b"source request").unwrap(),
            [5, 0, 0, 0, 36, b'p', b'l', b'a', b'n']
        );
        server.join().unwrap();
        let input = root.join("oversized-author.json");
        let file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&input)
            .unwrap();
        file.set_len(MAX_AUTHOR_JSON + 1).unwrap();
        assert!(operator
            .tool(
                "author",
                "application-dispatch-request",
                &input,
                &root.join("out.bin")
            )
            .is_err());
        fs::write(&config, b"{\"fixture\":false}").unwrap();
        assert!(operator.invoke(36, b"source request").is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn native_submit_marker_is_create_new_and_blocks_a_second_attempt() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root =
            std::env::temp_dir().join(format!("mini-spk-submit-{}-{nonce}", std::process::id()));
        DirBuilder::new().mode(0o700).create(&root).unwrap();
        let marker = root.join("native-dispatch-active.json");
        write_new(&root, "native-dispatch-active.json", b"first").unwrap();
        assert!(write_new(&root, "native-dispatch-active.json", b"second").is_err());
        assert_eq!(fs::read(marker).unwrap(), b"first");
        fs::remove_dir_all(root).unwrap();
    }
}
