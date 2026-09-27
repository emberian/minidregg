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
pub(crate) struct PrivateOperator {
    pub host: PathBuf,
    pub config: PathBuf,
    pub socket: PathBuf,
    pub host_sha256: String,
    pub config_sha256: String,
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
        let _ = self.check_pin()?;
        let cap = match command {
            "author" => MAX_AUTHOR_JSON,
            "inspect" => (HOST_MAX_FRAME - 1) as u64,
            "signatures" => 1024 * 1024,
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
        if !kind.is_empty() {
            process.arg(kind);
        }
        let status = process
            .arg(input)
            .arg(output)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()?;
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
        let config = self.check_pin()?;
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
        let mut stream = UnixStream::connect(&self.socket)?;
        let write_deadline = Instant::now() + Duration::from_secs(10);
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
        let deadline = Instant::now() + RESPONSE_DEADLINE;
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
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let request = custody.request_json(operation_id, http)?;
    let request_json = write_new(attempt_dir, "request.json", &serde_json::to_vec(&request)?)?;
    let request_bin = attempt_dir.join("request.bin");
    let request_bytes = operator.tool(
        "author",
        "application-dispatch-request",
        &request_json,
        &request_bin,
    )?;
    let plan_reply = operator.invoke(36, &request_bytes)?;
    if plan_reply[4] != 36 {
        return Err(invalid("Mini dispatch authoring refused"));
    }
    let plan_bytes = &plan_reply[5..];
    let plan_bin = write_new(attempt_dir, "plan.bin", plan_bytes)?;
    let plan_json_path = attempt_dir.join("plan.json");
    let plan_json = operator.tool(
        "inspect",
        "application-dispatch-plan",
        &plan_bin,
        &plan_json_path,
    )?;
    let signatures = custody.sign_plan(plan_bytes, &plan_json, &request_bytes, &request)?;
    let signatures_json = write_new(
        attempt_dir,
        "signatures.json",
        &serde_json::to_vec(&signatures)?,
    )?;
    let signatures_bin_path = attempt_dir.join("signatures.bin");
    let signatures_bin = operator.tool("signatures", "", &signatures_json, &signatures_bin_path)?;
    let mut pair = Vec::with_capacity(4 + plan_bytes.len() + signatures_bin.len());
    pair.extend_from_slice(&(plan_bytes.len() as u32).to_le_bytes());
    pair.extend_from_slice(plan_bytes);
    pair.extend_from_slice(&signatures_bin);
    let ingress_reply = operator.invoke(37, &pair)?;
    if ingress_reply[4] != 37 {
        return Err(invalid("Mini dispatch assembly refused"));
    }
    let ingress = &ingress_reply[5..];
    write_new(attempt_dir, "ingress.bin", ingress)?;
    let marker = json!({"protocol":"mini-spk-dispatch-submit-requested-v1",
        "operationId":operation_id,"ingressSha256":hex(&Sha256::digest(ingress))});
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
    let reply = operator.invoke(34, ingress)?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::net::UnixListener;
    use std::time::{SystemTime, UNIX_EPOCH};

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
