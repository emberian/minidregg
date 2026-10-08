//! Exact event21 authoring and one-shot native submit in the resident process.
//! Only op46's freshly returned committed frame can cross into physical RPC.
#![allow(dead_code)] // Resident listener is enabled only with the reverse v2 reserve client.

use crate::agent_api_custody::AgentCustody;
use crate::agent_api_wire::Request;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use serde::Deserialize;
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{DirBuilder, File};
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

const COMMITTED: &[u8] = b"DREGG/APPLICATION/AGENT-DISPATCH-COMMITTED-PERMIT/v2";
const OUTCOME: &[u8] = b"DREGG/NATIVE-HOST/OUTCOME/v5";

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn lower_hex(value: &str) -> bool {
    value.len().is_multiple_of(2)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

pub(crate) fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn str_field<'a>(value: &'a Value, name: &str) -> io::Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("source inspection field absent"))
}

fn reply(frame: &[u8], opcode: u8) -> io::Result<&[u8]> {
    if frame.len() < 6
        || u32::from_le_bytes(frame[..4].try_into().unwrap()) as usize + 4 != frame.len()
        || frame[4] != opcode
    {
        return Err(invalid("private Host opcode/frame mismatch"));
    }
    Ok(&frame[5..])
}

fn pair(left: &[u8], right: &[u8]) -> io::Result<Vec<u8>> {
    let length = u32::try_from(left.len()).map_err(|_| invalid("native pair left size"))?;
    let mut paired = Vec::with_capacity(left.len() + right.len() + 4);
    paired.extend_from_slice(&length.to_le_bytes());
    paired.extend_from_slice(left);
    paired.extend_from_slice(right);
    Ok(paired)
}

fn source_bytes(
    operator: &PrivateOperator,
    dir: &Path,
    name: &str,
    kind: &str,
    request: &Value,
) -> io::Result<Vec<u8>> {
    let input = write_new(dir, &format!("{name}.json"), &serde_json::to_vec(request)?)?;
    operator.tool("author", kind, &input, &dir.join(format!("{name}.bin")))
}

fn source_inspect(
    operator: &PrivateOperator,
    dir: &Path,
    name: &str,
    kind: &str,
    bytes: &[u8],
) -> io::Result<Value> {
    let input = write_new(dir, &format!("{name}.bin"), bytes)?;
    let raw = operator.tool("inspect", kind, &input, &dir.join(format!("{name}.json")))?;
    serde_json::from_slice(&raw).map_err(Into::into)
}

fn signatures(
    operator: &PrivateOperator,
    dir: &Path,
    name: &str,
    values: &Value,
) -> io::Result<Vec<u8>> {
    let input = write_new(dir, &format!("{name}.json"), &serde_json::to_vec(values)?)?;
    operator.tool("signatures", "", &input, &dir.join(format!("{name}.bin")))
}

/// The reverse controller owns the dispatch purse signer. It allocates a fresh
/// reserve ID, asks Mini for op58/59, submits that exact signed command once,
/// and retains the original admitted reserve receipt. It never returns a v1
/// digest-only nonce or re-sends after an uncertain result.
#[derive(Serialize)]
pub(crate) struct RetainedReserve {
    pub attempt_id: String,
    pub operation_id: String,
    pub fixed_request_hex: String,
    pub context_hex: String,
    pub reserve_index: String,
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub world_root: String,
}

/// Concrete BE32 controller custody client. It never receives a private key
/// and never retries a request after writing any byte to the reverse socket.
pub(crate) struct ReverseCustodyClient {
    pub socket: PathBuf,
    pub controller_uid: u32,
    pub route_name: String,
    attempt_id: Option<String>,
    forward_operation_id: Option<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ReserveReceipt {
    transaction_id: String,
    event_id: String,
    accepted_count: String,
    world_root: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ReservedReply {
    #[serde(rename = "type")]
    kind: String,
    attempt_id: String,
    http_operation_id: String,
    reserve_operation_id: String,
    fixed_request_hex: String,
    context_hex: String,
    reserve_index: String,
    reserve_receipt: ReserveReceipt,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PayerReply {
    #[serde(rename = "type")]
    kind: String,
    attempt_id: String,
    plan_sha256: String,
    signatures: Vec<String>,
}

impl ReverseCustodyClient {
    pub(crate) fn new(
        socket: PathBuf,
        controller_uid: u32,
        route_name: String,
    ) -> io::Result<Self> {
        if !socket.is_absolute()
            || controller_uid == 0
            || route_name.is_empty()
            || route_name.len() > 64
            || !route_name.ends_with("-app")
            || !route_name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'-')
        {
            return Err(invalid("reverse custody route pin refused"));
        }
        Ok(Self {
            socket,
            controller_uid,
            route_name,
            attempt_id: None,
            forward_operation_id: None,
        })
    }

    pub(crate) fn exchange(&self, request: &Value, cancelled: &AtomicBool) -> io::Result<Value> {
        self.exchange_until(request, cancelled, Instant::now() + Duration::from_secs(30))
    }

    /// A caller-supplied absolute deadline permits long source/native v3
    /// work without weakening the short v2 exchange. Cancellation remains
    /// polled throughout and no request is retried after any write.
    pub(crate) fn exchange_until(
        &self,
        request: &Value,
        cancelled: &AtomicBool,
        deadline: Instant,
    ) -> io::Result<Value> {
        if cancelled.load(Ordering::Acquire) {
            return Err(invalid("caller cancelled before reverse custody"));
        }
        let bytes = serde_json::to_vec(request)?;
        if bytes.is_empty() || bytes.len() > 22 * 1024 * 1024 {
            return Err(invalid("reverse custody request bound"));
        }
        for (depth, ancestor) in self
            .socket
            .parent()
            .ok_or_else(|| invalid("reverse socket parent"))?
            .ancestors()
            .enumerate()
        {
            let meta = std::fs::symlink_metadata(ancestor)?;
            let sticky_root = depth > 0 && meta.uid() == 0 && meta.mode() & 0o1000 != 0;
            if !meta.is_dir()
                || meta.mode() & 0o022 != 0 && !sticky_root
                || !matches!(meta.uid(), 0)
                    && meta.uid() != self.controller_uid
                    && meta.uid() != unsafe { libc::geteuid() }
            {
                return Err(invalid("reverse socket ancestor not protected"));
            }
        }
        let before = std::fs::symlink_metadata(&self.socket)?;
        if !before.file_type().is_socket() || before.uid() != self.controller_uid {
            return Err(invalid("reverse custody socket owner/type drift"));
        }
        let mut stream = connect_cancelled(&self.socket, deadline, cancelled)?;
        let mut credentials: libc::ucred = unsafe { std::mem::zeroed() };
        let mut size = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
        if unsafe {
            libc::getsockopt(
                stream.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_PEERCRED,
                (&mut credentials as *mut libc::ucred).cast(),
                &mut size,
            )
        } != 0
            || size as usize != std::mem::size_of::<libc::ucred>()
            || credentials.uid != self.controller_uid
        {
            return Err(invalid("reverse custody peer UID drift"));
        }
        let after = std::fs::symlink_metadata(&self.socket)?;
        if !after.file_type().is_socket()
            || (before.dev(), before.ino()) != (after.dev(), after.ino())
        {
            return Err(invalid("reverse custody socket inode drift"));
        }
        let mut frame = Vec::with_capacity(bytes.len() + 4);
        frame.extend_from_slice(&(bytes.len() as u32).to_be_bytes());
        frame.extend_from_slice(&bytes);
        let mut sent = 0;
        while sent < frame.len() {
            if cancelled.load(Ordering::Acquire) {
                return Err(invalid("caller cancelled during reverse custody send"));
            }
            let left = deadline.saturating_duration_since(Instant::now());
            if left.is_zero() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "reverse custody write deadline",
                ));
            }
            stream.set_write_timeout(Some(left.min(Duration::from_millis(100))))?;
            match stream.write(&frame[sent..]) {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "reverse custody write zero",
                    ))
                }
                Ok(count) => sent += count,
                Err(error)
                    if matches!(
                        error.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                    ) => {}
                Err(error) => return Err(error),
            }
        }
        let mut length = [0u8; 4];
        read_cancelled(&mut stream, &mut length, deadline, cancelled)?;
        let length = u32::from_be_bytes(length) as usize;
        // V3 also returns the exact op80 ReservePlan frame. A bounded Git
        // body can appear twice as hex (Request and Plan), so keep the
        // response bound separate from the smaller forward HTTP frame.
        if length == 0 || length > 1_048_576 {
            return Err(invalid("reverse custody reply bound"));
        }
        let mut reply = vec![0u8; length];
        read_cancelled(&mut stream, &mut reply, deadline, cancelled)?;
        serde_json::from_slice(&reply).map_err(Into::into)
    }

    fn inspect_reserve_v2(&self, operation_id: &str, cancelled: &AtomicBool) -> io::Result<Value> {
        // Read-only lookup by the controller's durable forward operation ID.
        // This never repeats a reserve command after an uncertain response.
        self.exchange(
            &json!({"type":"inspect-v2","route_name":self.route_name,
                "forward_operation_id":operation_id}),
            cancelled,
        )
    }

    fn accept_reserved_reply(
        &mut self,
        reply: Value,
        operation_id: &str,
    ) -> io::Result<RetainedReserve> {
        let reply: ReservedReply = serde_json::from_value(reply)?;
        if reply.kind != "dispatch-reserved-v2"
            || reply.http_operation_id != operation_id
            || !decimal(&reply.attempt_id)
            || !decimal(&reply.reserve_operation_id)
            || !decimal(&reply.reserve_index)
            || !lower_hex(&reply.fixed_request_hex)
            || reply.fixed_request_hex.is_empty()
            || !lower_hex(&reply.context_hex)
            || reply.context_hex.is_empty()
        {
            return Err(invalid(
                "reverse reserve reply differs from forward operation",
            ));
        }
        self.attempt_id = Some(reply.attempt_id.clone());
        self.forward_operation_id = Some(operation_id.to_owned());
        Ok(RetainedReserve {
            attempt_id: reply.attempt_id,
            operation_id: reply.reserve_operation_id,
            fixed_request_hex: reply.fixed_request_hex,
            context_hex: reply.context_hex,
            reserve_index: reply.reserve_index,
            transaction_id: reply.reserve_receipt.transaction_id,
            event_id: reply.reserve_receipt.event_id,
            accepted_count: reply.reserve_receipt.accepted_count,
            world_root: reply.reserve_receipt.world_root,
        })
    }
}

fn connect_cancelled(
    path: &Path,
    deadline: Instant,
    cancelled: &AtomicBool,
) -> io::Result<UnixStream> {
    let path = path.as_os_str().as_bytes();
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if path.is_empty() || path.contains(&0) || path.len() >= address.sun_path.len() {
        return Err(invalid("reverse custody socket address bound"));
    }
    address.sun_family = libc::AF_UNIX as libc::sa_family_t;
    for (slot, byte) in address.sun_path.iter_mut().zip(path) {
        *slot = *byte as libc::c_char;
    }
    let raw = unsafe {
        libc::socket(
            libc::AF_UNIX,
            libc::SOCK_STREAM | libc::SOCK_CLOEXEC | libc::SOCK_NONBLOCK,
            0,
        )
    };
    if raw < 0 {
        return Err(io::Error::last_os_error());
    }
    let fd = unsafe { OwnedFd::from_raw_fd(raw) };
    let length =
        (std::mem::offset_of!(libc::sockaddr_un, sun_path) + path.len() + 1) as libc::socklen_t;
    let status = unsafe {
        libc::connect(
            fd.as_raw_fd(),
            (&address as *const libc::sockaddr_un).cast(),
            length,
        )
    };
    if status < 0 {
        let error = io::Error::last_os_error();
        if error.raw_os_error() == Some(libc::EAGAIN) {
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "reverse custody connect backlog full before send",
            ));
        }
        if !matches!(error.raw_os_error(), Some(libc::EINPROGRESS | libc::EINTR)) {
            return Err(error);
        }
        loop {
            if cancelled.load(Ordering::Acquire) {
                return Err(invalid("caller cancelled before reverse connect"));
            }
            if deadline <= Instant::now() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "reverse custody connect deadline",
                ));
            }
            let mut pollfd = libc::pollfd {
                fd: fd.as_raw_fd(),
                events: libc::POLLOUT,
                revents: 0,
            };
            let polled = unsafe { libc::poll(&mut pollfd, 1, 100) };
            if polled < 0 {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            if polled == 0 {
                continue;
            }
            let mut socket_error = 0i32;
            let mut len = std::mem::size_of::<i32>() as libc::socklen_t;
            if unsafe {
                libc::getsockopt(
                    fd.as_raw_fd(),
                    libc::SOL_SOCKET,
                    libc::SO_ERROR,
                    (&mut socket_error as *mut i32).cast(),
                    &mut len,
                )
            } != 0
            {
                return Err(io::Error::last_os_error());
            }
            if len as usize != std::mem::size_of::<i32>() {
                return Err(invalid("reverse custody connect result size"));
            }
            if socket_error != 0 {
                return Err(io::Error::from_raw_os_error(socket_error));
            }
            let mut peer: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
            let mut peer_len = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
            if unsafe {
                libc::getpeername(
                    fd.as_raw_fd(),
                    (&mut peer as *mut libc::sockaddr_storage).cast::<libc::sockaddr>(),
                    &mut peer_len,
                )
            } == 0
            {
                break;
            }
            let error = io::Error::last_os_error();
            if error.raw_os_error() != Some(libc::ENOTCONN) {
                return Err(error);
            }
            std::thread::sleep(Duration::from_millis(20));
        }
    }
    let stream = UnixStream::from(fd);
    stream.set_nonblocking(false)?;
    Ok(stream)
}

fn read_cancelled(
    stream: &mut UnixStream,
    bytes: &mut [u8],
    deadline: Instant,
    cancelled: &AtomicBool,
) -> io::Result<()> {
    let mut received = 0;
    while received < bytes.len() {
        if cancelled.load(Ordering::Acquire) {
            return Err(invalid("caller cancelled during reverse custody reply"));
        }
        let left = deadline.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "reverse custody reply deadline",
            ));
        }
        stream.set_read_timeout(Some(left.min(Duration::from_millis(100))))?;
        match stream.read(&mut bytes[received..]) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "reverse custody reply EOF",
                ))
            }
            Ok(count) => received += count,
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                ) => {}
            Err(error) => return Err(error),
        }
    }
    Ok(())
}

impl ReserveSubmit for ReverseCustodyClient {
    fn reserve_once(
        &mut self,
        fixed_request: &Value,
        cancelled: &AtomicBool,
    ) -> io::Result<RetainedReserve> {
        let operation_id = fixed_request
            .get("base")
            .and_then(|v| v.get("http"))
            .and_then(|v| v.get("operationId"))
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("reverse fixed HTTP operation absent"))?;
        let reply = self.exchange(
            &json!({"type":"reserve-v2","route_name":self.route_name,
            "forward_operation_id":operation_id,"fixed_request":fixed_request}),
            cancelled,
        );
        let reply = match reply {
            Ok(reply) => reply,
            Err(original) => {
                if cancelled.load(Ordering::Acquire) {
                    return Err(original);
                }
                match self.inspect_reserve_v2(operation_id, cancelled) {
                    Ok(confirmed) => confirmed,
                    Err(_) => return Err(original),
                }
            }
        };
        self.accept_reserved_reply(reply, operation_id)
    }

    fn sign_payer_once(
        &mut self,
        paid_plan: &[u8],
        inspection: &Value,
        cancelled: &AtomicBool,
    ) -> io::Result<Value> {
        let attempt_id = self
            .attempt_id
            .as_deref()
            .ok_or_else(|| invalid("payer signing lacks reserve"))?;
        let operation_id = self
            .forward_operation_id
            .as_deref()
            .ok_or_else(|| invalid("payer signing lacks forward operation"))?;
        let plan_sha256 = hex(&Sha256::digest(paid_plan));
        let reply = self.exchange(
            &json!({"type":"sign-payer-v2","route_name":self.route_name,
            "forward_operation_id":operation_id,"attempt_id":attempt_id,
            "paid_plan_hex":hex(paid_plan),"source_inspection_json":inspection}),
            cancelled,
        )?;
        let reply: PayerReply = serde_json::from_value(reply)?;
        if reply.kind != "payer-signatures-v2"
            || reply.attempt_id != attempt_id
            || reply.plan_sha256 != plan_sha256
        {
            return Err(invalid("reverse payer reply differs from exact paid plan"));
        }
        Ok(Value::Array(
            reply.signatures.into_iter().map(Value::String).collect(),
        ))
    }

    fn mark_send_once(
        &mut self,
        request_sha256: &str,
        transaction_id: &str,
        event_id: &str,
        permit_sha256: &str,
        cancelled: &AtomicBool,
    ) -> io::Result<()> {
        let attempt_id = self
            .attempt_id
            .as_deref()
            .ok_or_else(|| invalid("send marker lacks reserve"))?;
        if [request_sha256, permit_sha256]
            .iter()
            .any(|digest| digest.len() != 64 || !lower_hex(digest))
            || !decimal(transaction_id)
            || !decimal(event_id)
        {
            return Err(invalid("send marker coordinate refused"));
        }
        let response = self.exchange(
            &json!({"type":"mark-send","attempt_id":attempt_id,
                "request_sha256":request_sha256,"transaction_id":transaction_id,
                "event_id":event_id,"permit_sha256":permit_sha256}),
            cancelled,
        )?;
        if str_field(&response, "type")? != "dispatch-send-marked-v1"
            || str_field(&response, "attemptId")? != attempt_id
            || str_field(&response, "requestSha256")? != request_sha256
            || str_field(&response, "transactionId")? != transaction_id
            || str_field(&response, "eventId")? != event_id
            || str_field(&response, "permitSha256")? != permit_sha256
        {
            return Err(invalid("controller send marker ACK drift"));
        }
        Ok(())
    }
}

pub(crate) trait ReserveSubmit {
    fn reserve_once(
        &mut self,
        fixed_request: &Value,
        cancelled: &AtomicBool,
    ) -> io::Result<RetainedReserve>;
    /// Sign only payerSlots from this exact source-authored op48 plan. The
    /// controller must compare the plan/context with its retained reserve and
    /// fixed dispatchTask signer before releasing signatures.
    fn sign_payer_once(
        &mut self,
        paid_plan: &[u8],
        inspection: &Value,
        cancelled: &AtomicBool,
    ) -> io::Result<Value>;

    /// Controller saves the sole send boundary after the fresh event21 permit
    /// is matched and before the resident may queue fd3 delivery.
    fn mark_send_once(
        &mut self,
        request_sha256: &str,
        transaction_id: &str,
        event_id: &str,
        permit_sha256: &str,
        cancelled: &AtomicBool,
    ) -> io::Result<()>;
}

pub(crate) struct CommittedAgent {
    pub permit: Vec<u8>,
    pub inspection: Value,
    pub reserve: RetainedReserve,
    pub canonical_http_sha256: String,
    pub attempt_dir: PathBuf,
    active_marker: PathBuf,
    active_bytes: Vec<u8>,
    active_identity: (u64, u64),
}

impl CommittedAgent {
    pub(crate) fn clear_committed_submit_marker(&self) -> io::Result<()> {
        let metadata = std::fs::symlink_metadata(&self.active_marker)?;
        if !metadata.is_file()
            || (metadata.dev(), metadata.ino()) != self.active_identity
            || std::fs::read(&self.active_marker)? != self.active_bytes
        {
            return Err(invalid("agent native submit marker drift"));
        }
        std::fs::remove_file(&self.active_marker)?;
        File::open(
            self.active_marker
                .parent()
                .ok_or_else(|| invalid("marker parent absent"))?,
        )?
        .sync_all()
    }
}

/// Caller supplies an already allocated, durable HTTP operation ID and a
/// distinct reserve operation ID. A new attempt directory is created before
/// any Host or resource mutation. This route's marker prevents another
/// attempt on the same agent route after an uncertain op46 reply, even if
/// the caller changes operation IDs. Other routes have separate parents.
pub(crate) fn authorize_once(
    operator: &PrivateOperator,
    custody: &AgentCustody,
    request: &Request,
    app_path: &str,
    attempt_dir: &Path,
    reserve: &mut dyn ReserveSubmit,
    cancelled: &AtomicBool,
) -> io::Result<CommittedAgent> {
    if cancelled.load(Ordering::Acquire) {
        return Err(invalid("agent caller cancelled before reserve"));
    }
    custody.validate()?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("agent attempt parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let fixed_json = custody.reserve_request(request, "0", app_path)?;
    let retained = reserve.reserve_once(&fixed_json, cancelled)?;
    if cancelled.load(Ordering::Acquire) {
        return Err(invalid("agent caller cancelled after reserve"));
    }
    if [
        &retained.operation_id,
        &retained.reserve_index,
        &retained.transaction_id,
        &retained.event_id,
        &retained.accepted_count,
        &retained.world_root,
    ]
    .iter()
    .any(|v| {
        v.is_empty()
            || v.starts_with('0') && *v != "0"
            || !v.bytes().all(|byte| byte.is_ascii_digit())
    }) {
        return Err(invalid("reverse reserve index noncanonical"));
    }
    let count = retained
        .accepted_count
        .parse::<u128>()
        .map_err(|_| invalid("reserve count outside physical range"))?;
    let index = retained
        .reserve_index
        .parse::<u128>()
        .map_err(|_| invalid("reserve index outside physical range"))?;
    if count == 0 || index != count - 1 {
        return Err(invalid("reserve index differs from receipt count"));
    }
    let reserve_json = custody.reserve_request(request, &retained.operation_id, app_path)?;
    let reserve_request = source_bytes(
        operator,
        attempt_dir,
        "reserve-request",
        "application-agent-reserve-request",
        &reserve_json,
    )?;
    if retained.fixed_request_hex != hex(&reserve_request) {
        return Err(invalid(
            "controller retained reserve differs from fixed HTTP request",
        ));
    }
    write_new(
        attempt_dir,
        "original-reserve.json",
        &serde_json::to_vec(&retained)?,
    )?;
    let paid_json = json!({"fixedRequestHex":retained.fixed_request_hex,
        "contextHex":retained.context_hex,"reserveIndex":retained.reserve_index});
    let paid_request = source_bytes(
        operator,
        attempt_dir,
        "paid-request",
        "application-agent-paid-request",
        &paid_json,
    )?;
    let paid_plan = reply(&operator.invoke(48, &paid_request)?, 48)?.to_vec();
    let paid_view = source_inspect(
        operator,
        attempt_dir,
        "paid-plan",
        "application-agent-paid-dispatch-plan",
        &paid_plan,
    )?;
    if str_field(&paid_view, "type")? != "application-agent-paid-dispatch-plan-v2"
        || str_field(
            paid_view
                .get("context")
                .ok_or_else(|| invalid("paid context absent"))?,
            "canonicalHex",
        )? != retained.context_hex
        || str_field(&paid_view, "reserveIndex")? != retained.reserve_index
    {
        return Err(invalid("paid plan differs from original reserve"));
    }
    let canonical_http_hex = str_field(&paid_view, "canonicalHttpHex")?;
    if canonical_http_hex.is_empty() || !lower_hex(canonical_http_hex) {
        return Err(invalid("paid canonical HTTP is not source hex"));
    }
    let canonical_http = canonical_http_hex
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16)
                .map_err(|_| invalid("paid canonical HTTP hex byte"))
        })
        .collect::<io::Result<Vec<_>>>()?;
    let canonical_http_sha256 = hex(&Sha256::digest(&canonical_http));
    let app = custody.sign_slots(&paid_view, &paid_plan, "appSlots", &custody.app_signers)?;
    let payer = reserve.sign_payer_once(&paid_plan, &paid_view, cancelled)?;
    if cancelled.load(Ordering::Acquire) {
        return Err(invalid("agent caller cancelled before paid assembly"));
    }
    custody.verify_payer_slots(&paid_view, &paid_plan, &payer)?;
    let app_bytes = signatures(operator, attempt_dir, "app-signatures", &app)?;
    let payer_bytes = signatures(operator, attempt_dir, "payer-signatures", &payer)?;
    let paid_signatures = pair(&app_bytes, &payer_bytes)?;
    let ingress = reply(
        &operator.invoke(49, &pair(&paid_plan, &paid_signatures)?)?,
        49,
    )?
    .to_vec();
    write_new(attempt_dir, "paid-ingress.bin", &ingress)?;
    let marker = json!({"protocol":"mini-spk-agent-submit-requested-v2",
        "operationId":match request { Request::Dispatch { operation_id, .. } => operation_id,
            _ => return Err(invalid("dispatch required")) },
        "ingressSha256":hex(&Sha256::digest(&ingress))});
    let marker_bytes = serde_json::to_vec(&marker)?;
    write_new(attempt_dir, "submit-requested.json", &marker_bytes)?;
    let active_marker = parent.join("native-agent-dispatch-active.json");
    let mut active = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&active_marker)?;
    active.write_all(&marker_bytes)?;
    active.sync_all()?;
    let active_metadata = active.metadata()?;
    let active_identity = (active_metadata.dev(), active_metadata.ino());
    File::open(parent)?.sync_all()?;
    if cancelled.load(Ordering::Acquire) {
        if std::fs::read(&active_marker)? != marker_bytes {
            return Err(invalid("agent marker drift before cancelled op46"));
        }
        std::fs::remove_file(&active_marker)?;
        File::open(parent)?.sync_all()?;
        return Err(invalid("agent caller cancelled before op46"));
    }
    let frame = operator.invoke(46, &ingress)?;
    write_new(attempt_dir, "op46-frame.bin", &frame)?;
    let permit = reply(&frame, 46)?;
    if !permit.starts_with(COMMITTED)
        || permit.len() <= COMMITTED.len()
        || permit.starts_with(OUTCOME)
    {
        return Err(invalid("op46 did not return fresh committed permit"));
    }
    let permit = permit.to_vec();
    let inspection = source_inspect(
        operator,
        attempt_dir,
        "committed",
        "application-agent-dispatch-committed",
        &permit,
    )?;
    if str_field(&inspection, "type")? != "application-agent-dispatch-committed-inspection-v2"
        || str_field(&inspection, "frameHex")? != hex(&permit)
    {
        return Err(invalid(
            "source committed inspection differs from private op46 bytes",
        ));
    }
    Ok(CommittedAgent {
        permit,
        inspection,
        reserve: retained,
        canonical_http_sha256,
        attempt_dir: attempt_dir.to_owned(),
        active_marker,
        active_bytes: marker_bytes,
        active_identity,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;
    use std::os::unix::net::UnixListener;
    use std::sync::atomic::AtomicUsize;
    use std::thread;

    static NEXT_SOCKET: AtomicUsize = AtomicUsize::new(1);
    fn frame(op: u8, payload: &[u8]) -> Vec<u8> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&((payload.len() + 1) as u32).to_le_bytes());
        bytes.push(op);
        bytes.extend_from_slice(payload);
        bytes
    }
    #[test]
    fn committed_agent_requires_exact_op46_and_distinct_tag() {
        let mut permit = COMMITTED.to_vec();
        permit.push(1);
        assert_eq!(reply(&frame(46, &permit), 46).unwrap(), permit);
        assert!(reply(&frame(47, &permit), 46).is_err());
        assert!(!OUTCOME.starts_with(COMMITTED));
        assert!(pair(b"abc", b"def")
            .unwrap()
            .starts_with(&3u32.to_le_bytes()));
    }

    #[test]
    fn concrete_reverse_client_preserves_forward_and_paid_plan_identity() {
        let directory = std::env::temp_dir().join(format!(
            "mini-agent-reverse-{}-{}",
            std::process::id(),
            NEXT_SOCKET.fetch_add(1, Ordering::SeqCst)
        ));
        std::fs::create_dir(&directory).unwrap();
        std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700)).unwrap();
        let socket = directory.join("reverse.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        let server = thread::spawn(move || {
            for expected in ["reserve-v2", "sign-payer-v2", "mark-send"] {
                let (mut stream, _) = listener.accept().unwrap();
                let mut size = [0u8; 4];
                stream.read_exact(&mut size).unwrap();
                let mut bytes = vec![0u8; u32::from_be_bytes(size) as usize];
                stream.read_exact(&mut bytes).unwrap();
                let request: Value = serde_json::from_slice(&bytes).unwrap();
                assert_eq!(request["type"], expected);
                if expected != "mark-send" {
                    assert_eq!(request["forward_operation_id"], "17");
                    assert_eq!(request["route_name"], "workroom-app");
                }
                let reply = if expected == "reserve-v2" {
                    json!({"type":"dispatch-reserved-v2","attemptId":"41",
                        "httpOperationId":"17","reserveOperationId":"53",
                        "fixedRequestHex":"aa".repeat(65_536),
                        "contextHex":"bb","reserveIndex":"4",
                        "reserveReceipt":{"transactionId":"71","eventId":"72",
                            "acceptedCount":"5","worldRoot":"73"}})
                } else if expected == "sign-payer-v2" {
                    assert_eq!(request["attempt_id"], "41");
                    assert_eq!(request["paid_plan_hex"], "0102");
                    json!({"type":"payer-signatures-v2","attemptId":"41",
                        "planSha256":hex(&Sha256::digest([1,2])),"signatures":["ab"]})
                } else {
                    assert_eq!(request["attempt_id"], "41");
                    assert_eq!(request["transaction_id"], "81");
                    assert_eq!(request["event_id"], "82");
                    json!({"type":"dispatch-send-marked-v1","attemptId":"41",
                        "requestSha256":request["request_sha256"],
                        "transactionId":"81","eventId":"82",
                        "permitSha256":request["permit_sha256"]})
                };
                let bytes = serde_json::to_vec(&reply).unwrap();
                stream
                    .write_all(&(bytes.len() as u32).to_be_bytes())
                    .unwrap();
                stream.write_all(&bytes).unwrap();
            }
        });
        let mut client = ReverseCustodyClient::new(
            socket.clone(),
            unsafe { libc::geteuid() },
            "workroom-app".into(),
        )
        .unwrap();
        let cancelled = AtomicBool::new(false);
        let reserved = client
            .reserve_once(&json!({"base":{"http":{"operationId":"17"}}}), &cancelled)
            .unwrap();
        assert_eq!(
            (
                reserved.operation_id.as_str(),
                reserved.reserve_index.as_str()
            ),
            ("53", "4")
        );
        assert_eq!(reserved.fixed_request_hex.len(), 131_072);
        let signatures = client
            .sign_payer_once(&[1, 2], &json!({"type":"plan"}), &cancelled)
            .unwrap();
        assert_eq!(signatures, json!(["ab"]));
        client
            .mark_send_once(&"a".repeat(64), "81", "82", &"b".repeat(64), &cancelled)
            .unwrap();
        server.join().unwrap();
        std::fs::remove_file(&socket).unwrap();
        std::fs::remove_dir(&directory).unwrap();
    }

    #[test]
    fn saturated_reverse_listener_fails_before_send_without_waiting_for_deadline() {
        let directory = std::env::temp_dir().join(format!(
            "mini-agent-backlog-{}-{}",
            std::process::id(),
            NEXT_SOCKET.fetch_add(1, Ordering::SeqCst)
        ));
        std::fs::create_dir(&directory).unwrap();
        let socket = directory.join("reverse.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        assert_eq!(unsafe { libc::listen(listener.as_raw_fd(), 0) }, 0);
        let cancelled = AtomicBool::new(false);
        let mut occupied = Vec::new();
        let mut saturated = false;
        for _ in 0..64 {
            let start = Instant::now();
            match connect_cancelled(&socket, start + Duration::from_secs(2), &cancelled) {
                Ok(stream) => occupied.push(stream),
                Err(_) => {
                    saturated = true;
                    assert!(start.elapsed() < Duration::from_millis(300));
                    break;
                }
            }
        }
        assert!(saturated, "fixture did not fill the reverse Unix backlog");
        drop(occupied);
        drop(listener);
        std::fs::remove_file(socket).unwrap();
        std::fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn lost_reserve_reply_uses_only_read_only_inspect_v2() {
        let directory = std::env::temp_dir().join(format!(
            "mini-agent-inspect-reserve-{}-{}",
            std::process::id(),
            NEXT_SOCKET.fetch_add(1, Ordering::SeqCst)
        ));
        std::fs::create_dir(&directory).unwrap();
        std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700)).unwrap();
        let socket = directory.join("reverse.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        let server = thread::spawn(move || {
            for expected in ["reserve-v2", "inspect-v2"] {
                let (mut stream, _) = listener.accept().unwrap();
                let mut size = [0u8; 4];
                stream.read_exact(&mut size).unwrap();
                let mut bytes = vec![0u8; u32::from_be_bytes(size) as usize];
                stream.read_exact(&mut bytes).unwrap();
                let request: Value = serde_json::from_slice(&bytes).unwrap();
                assert_eq!(request["type"], expected);
                assert_eq!(request["forward_operation_id"], "17");
                if expected == "reserve-v2" {
                    continue; // Original reply lost after controller confirmation.
                }
                assert!(request.get("fixed_request").is_none());
                let reply = json!({"type":"dispatch-reserved-v2","attemptId":"41",
                    "httpOperationId":"17","reserveOperationId":"53",
                    "fixedRequestHex":"aa","contextHex":"bb","reserveIndex":"4",
                    "reserveReceipt":{"transactionId":"71","eventId":"72",
                        "acceptedCount":"5","worldRoot":"73"}});
                let bytes = serde_json::to_vec(&reply).unwrap();
                stream
                    .write_all(&(bytes.len() as u32).to_be_bytes())
                    .unwrap();
                stream.write_all(&bytes).unwrap();
            }
        });
        let mut client = ReverseCustodyClient::new(
            socket.clone(),
            unsafe { libc::geteuid() },
            "workroom-app".into(),
        )
        .unwrap();
        let reserved = client
            .reserve_once(
                &json!({"base":{"http":{"operationId":"17"}}}),
                &AtomicBool::new(false),
            )
            .unwrap();
        assert_eq!(
            (reserved.operation_id.as_str(), reserved.attempt_id.as_str()),
            ("53", "41")
        );
        server.join().unwrap();
        std::fs::remove_file(socket).unwrap();
        std::fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn committed_marker_clear_refuses_replaced_inode_with_same_bytes() {
        let directory = std::env::temp_dir().join(format!(
            "mini-agent-active-marker-{}-{}",
            std::process::id(),
            NEXT_SOCKET.fetch_add(1, Ordering::SeqCst)
        ));
        std::fs::create_dir(&directory).unwrap();
        let marker = directory.join("native-agent-dispatch-active.json");
        std::fs::write(&marker, b"exact marker").unwrap();
        let metadata = std::fs::symlink_metadata(&marker).unwrap();
        let committed = CommittedAgent {
            permit: Vec::new(),
            inspection: json!({}),
            reserve: RetainedReserve {
                attempt_id: "1".into(),
                operation_id: "2".into(),
                fixed_request_hex: String::new(),
                context_hex: String::new(),
                reserve_index: "0".into(),
                transaction_id: "3".into(),
                event_id: "4".into(),
                accepted_count: "1".into(),
                world_root: "5".into(),
            },
            canonical_http_sha256: String::new(),
            attempt_dir: directory.clone(),
            active_marker: marker.clone(),
            active_bytes: b"exact marker".to_vec(),
            active_identity: (metadata.dev(), metadata.ino()),
        };
        std::fs::rename(&marker, directory.join("old-marker")).unwrap();
        std::fs::write(&marker, b"exact marker").unwrap();
        assert!(committed.clear_committed_submit_marker().is_err());
        assert!(marker.exists());
        std::fs::remove_file(&marker).unwrap();
        std::fs::remove_file(directory.join("old-marker")).unwrap();
        std::fs::remove_dir(directory).unwrap();
    }
}
