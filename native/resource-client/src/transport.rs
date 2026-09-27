//! Bounded framing shared by the local socket and the Lean host's stdio service.
use sha2::{Digest, Sha256};
use std::fs;
use std::fs::OpenOptions;
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

// Mirrors FnEvidenceCodec.maxHostFrameBytes; the host's length includes op byte.
pub(crate) const HOST_MAX_FRAME: usize = 12_102_760;
const MAX_CONFIG: usize = 65_536;
const MAX_FRAME: usize = HOST_MAX_FRAME + 5 + MAX_CONFIG + 32;

fn host_image_sha256(path: &Path) -> Result<[u8; 32], String> {
    let mut file = fs::File::open(path)
        .map_err(|e| format!("cannot open host image {}: {e}", path.display()))?;
    let mut hash = Sha256::new();
    let mut chunk = [0u8; 64 * 1024];
    loop {
        let count = file
            .read(&mut chunk)
            .map_err(|e| format!("cannot hash host image {}: {e}", path.display()))?;
        if count == 0 {
            return Ok(hash.finalize().into());
        }
        hash.update(&chunk[..count]);
    }
}

fn parse_host_sha256(value: &str) -> Result<[u8; 32], String> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("expected host SHA-256 must be 64 lowercase hex digits".to_owned());
    }
    let mut bytes = [0u8; 32];
    for (index, byte) in bytes.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[2 * index..2 * index + 2], 16)
            .map_err(|_| "invalid expected host SHA-256")?;
    }
    Ok(bytes)
}

fn request_from_envelope<'a>(
    envelope: &'a [u8],
    config: &[u8],
    host_sha256: &[u8; 32],
) -> Result<&'a [u8], &'static str> {
    if envelope.len() < 5 || !matches!(envelope[0], 1 | 2) {
        return Err("invalid socket envelope");
    }
    let config_length = u32::from_le_bytes(envelope[1..5].try_into().unwrap()) as usize;
    let config_end = config_length
        .checked_add(5)
        .ok_or("invalid socket envelope")?;
    if config_length != config.len() || envelope.get(5..config_end) != Some(config) {
        return Err("config pin mismatch");
    }
    let request_start = if envelope[0] == 2 {
        let sha_end = config_end
            .checked_add(32)
            .ok_or("invalid socket envelope")?;
        if envelope.get(config_end..sha_end) != Some(host_sha256.as_slice()) {
            return Err("host image pin mismatch");
        }
        sha_end
    } else {
        config_end
    };
    let request = envelope
        .get(request_start..)
        .ok_or("invalid socket envelope")?;
    if request.is_empty() {
        return Err("invalid socket envelope");
    }
    Ok(request)
}

fn allowed_operation(request: &[u8], catalog_enabled: bool) -> bool {
    match request {
        [0..=11, ..] => true,
        [12 | 14] => true,
        [13 | 15, digits @ ..] => {
            !digits.is_empty()
                && digits.len() <= 80
                && digits.iter().all(u8::is_ascii_digit)
                && (digits.len() == 1 || digits[0] != b'0')
        }
        [16, carrier @ ..] => catalog_enabled && !carrier.is_empty() && carrier.len() <= 1_516_384,
        [17, pair @ ..] if pair.len() >= 6 => {
            let call_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            call_length > 0 && call_length < pair.len() - 4 && pair.len() - 4 - call_length <= 1024
        }
        [18, digits @ ..] => {
            catalog_enabled
                && !digits.is_empty()
                && digits.len() <= 80
                && digits.iter().all(u8::is_ascii_digit)
                && (digits.len() == 1 || digits[0] != b'0')
        }
        [19, payload @ ..] if payload.len() >= 10 => {
            let metadata_length = u32::from_le_bytes(payload[..4].try_into().unwrap()) as usize;
            if metadata_length == 0 || metadata_length > 4096 || payload.len() < metadata_length + 9
            {
                return false;
            }
            let request_prefix = metadata_length + 4;
            let request_length = u32::from_le_bytes(
                payload[request_prefix..request_prefix + 4]
                    .try_into()
                    .unwrap(),
            ) as usize;
            if request_length == 0 || request_length > 1_048_576 {
                return false;
            }
            let response_prefix = request_prefix + 4 + request_length;
            response_prefix < payload.len() && payload.len() - response_prefix <= 8_388_608
        }
        [20 | 21, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [28 | 29, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [30 | 31, payload @ ..] => {
            !payload.is_empty()
                && payload.len() <= 256 * 1024
                && serde_json::from_slice::<serde_json::Value>(payload)
                    .is_ok_and(|value| value.is_object())
        }
        _ => false,
    }
}

// These lifecycle, dispatch, share-issue, and fn namespace routes carry operator custody
// selectors or may commit writes. They are available only on the separately
// started owner-private operator socket, never on the public service socket.
fn allowed_operator_operation(request: &[u8]) -> bool {
    match request {
        [22 | 23 | 26 | 27 | 34 | 35 | 38 | 39 | 44 | 50 | 52, payload @ ..] => {
            !payload.is_empty() && payload.len() < HOST_MAX_FRAME
        }
        [40 | 41, payload @ ..] => !payload.is_empty() && payload.len() <= 8192,
        // Op42 obtains all selectors from pinned operator settings and a live
        // local fn status/position call. No caller field enters its plan.
        [42] => true,
        // Custody signs the source header and returns exactly one raw Ed25519
        // signature. Lean constructs the canonical credential envelope.
        [43, pair @ ..] if pair.len() >= 4 + 1 + 64 && pair.len() <= 4 + 8192 + 64 => {
            let plan_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            plan_length > 0
                && plan_length <= 8192
                && plan_length < pair.len() - 4
                && pair.len() - 4 - plan_length == 64
        }
        [28 | 29, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [32, payload @ ..] => !payload.is_empty() && payload.len() <= 256 * 1024,
        [33, pair @ ..] if pair.len() >= 6 && pair.len() < HOST_MAX_FRAME => {
            let plan_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            plan_length > 0 && plan_length < pair.len() - 4
        }
        // The source request codec can carry an admitted 8 MiB HTTP body.
        // Only the complete native Host frame limits this private author route.
        [36, payload @ ..] => !payload.is_empty() && payload.len() < HOST_MAX_FRAME,
        [37, pair @ ..] if pair.len() >= 6 && pair.len() < HOST_MAX_FRAME => {
            let plan_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            plan_length > 0 && plan_length < pair.len() - 4
        }
        [45 | 51 | 53, pair @ ..] if pair.len() >= 6 && pair.len() < HOST_MAX_FRAME => {
            let plan_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            plan_length > 0 && plan_length < pair.len() - 4
        }
        _ => false,
    }
}

fn read_config(path: &Path) -> Result<Vec<u8>, String> {
    let file = fs::File::open(path)
        .map_err(|e| format!("cannot read host config {}: {e}", path.display()))?;
    let mut bytes = Vec::new();
    file.take((MAX_CONFIG + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("cannot read host config {}: {e}", path.display()))?;
    if bytes.len() > MAX_CONFIG {
        return Err("host config exceeds socket pin bound".to_owned());
    }
    Ok(bytes)
}

fn read_frame<R: Read>(reader: &mut R) -> io::Result<Option<Vec<u8>>> {
    let mut prefix = [0u8; 4];
    let mut read = 0;
    while read < prefix.len() {
        match reader.read(&mut prefix[read..])? {
            0 if read == 0 => return Ok(None),
            0 => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "truncated frame length",
                ))
            }
            n => read += n,
        }
    }
    let size = u32::from_le_bytes(prefix) as usize;
    if !(1..=MAX_FRAME).contains(&size) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid frame length",
        ));
    }
    let mut frame = vec![0; size];
    reader.read_exact(&mut frame)?;
    Ok(Some(frame))
}

fn write_frame<W: Write>(writer: &mut W, frame: &[u8]) -> io::Result<()> {
    if !(1..=MAX_FRAME).contains(&frame.len()) {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "invalid frame length",
        ));
    }
    writer.write_all(&(frame.len() as u32).to_le_bytes())?;
    writer.write_all(frame)?;
    writer.flush()
}

#[repr(C)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}

#[cfg(target_os = "macos")]
unsafe extern "C" {
    fn poll(fds: *mut PollFd, count: u32, timeout: i32) -> i32;
}
#[cfg(not(target_os = "macos"))]
unsafe extern "C" {
    fn poll(fds: *mut PollFd, count: usize, timeout: i32) -> i32;
}
unsafe extern "C" {
    fn fcntl(fd: i32, command: i32, ...) -> i32;
    fn flock(fd: i32, operation: i32) -> i32;
}

pub(crate) fn service_lock(path: &Path) -> Result<fs::File, String> {
    let file = match OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
    {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => OpenOptions::new()
            .write(true)
            .open(path)
            .map_err(|error| format!("cannot open service lock {}: {error}", path.display()))?,
        Err(error) => {
            return Err(format!(
                "cannot create service lock {}: {error}",
                path.display()
            ))
        }
    };
    let named = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect service lock {}: {error}", path.display()))?;
    let opened = file
        .metadata()
        .map_err(|error| format!("cannot inspect opened service lock: {error}"))?;
    if !named.file_type().is_file()
        || named.uid() != effective_uid()
        || named.mode() & 0o077 != 0
        || (named.dev(), named.ino()) != (opened.dev(), opened.ino())
    {
        return Err("service lock is not an owner-private regular file".to_owned());
    }
    const LOCK_EX: i32 = 2;
    const LOCK_NB: i32 = 4;
    if unsafe { flock(file.as_raw_fd(), LOCK_EX | LOCK_NB) } < 0 {
        return Err(format!(
            "another service owns {}: {}",
            path.display(),
            io::Error::last_os_error()
        ));
    }
    Ok(file)
}

fn pin_config(path: &Path, bytes: &[u8]) -> Result<(), String> {
    match fs::symlink_metadata(path) {
        Ok(metadata) => {
            if !metadata.file_type().is_file()
                || metadata.uid() != effective_uid()
                || metadata.mode() & 0o077 != 0
            {
                return Err("retained host config is not an owner-private regular file".to_owned());
            }
            if read_config(path)? != bytes {
                return Err("retained host config differs from requested service config".to_owned());
            }
        }
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(path)
                .map_err(|error| {
                    format!("cannot create pinned config {}: {error}", path.display())
                })?;
            file.write_all(bytes)
                .and_then(|()| file.sync_all())
                .map_err(|error| {
                    format!("cannot write pinned config {}: {error}", path.display())
                })?;
            fs::File::open(path.parent().ok_or("pinned config has no parent")?)
                .and_then(|directory| directory.sync_all())
                .map_err(|error| format!("cannot sync pinned config directory: {error}"))?;
        }
        Err(error) => {
            return Err(format!(
                "cannot inspect pinned config {}: {error}",
                path.display()
            ))
        }
    }
    Ok(())
}

fn pin_service_mode(path: &Path, operator: bool, legacy_config_exists: bool) -> Result<(), String> {
    if operator && !path.exists() && legacy_config_exists {
        return Err("existing public service pin cannot be upgraded to operator mode".into());
    }
    pin_config(
        path,
        if operator {
            b"operator-v1"
        } else {
            b"public-v1"
        },
    )
}

fn clear_stale_socket(path: &Path) -> Result<(), String> {
    let metadata = match fs::symlink_metadata(path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(format!("cannot inspect socket {}: {error}", path.display())),
    };
    if !metadata.file_type().is_socket() || metadata.uid() != effective_uid() {
        return Err("socket path is not an owned Unix socket".to_owned());
    }
    match UnixStream::connect(path) {
        Ok(_) => Err("another service still listens on socket".to_owned()),
        Err(error) if error.kind() == io::ErrorKind::ConnectionRefused => {
            let current = fs::symlink_metadata(path)
                .map_err(|error| format!("cannot recheck stale socket: {error}"))?;
            if !current.file_type().is_socket()
                || (current.dev(), current.ino()) != (metadata.dev(), metadata.ino())
            {
                return Err("socket path changed during stale recovery".to_owned());
            }
            fs::remove_file(path).map_err(|error| format!("cannot remove stale socket: {error}"))
        }
        Err(error) => Err(format!("cannot prove socket stale: {error}")),
    }
}

fn set_nonblocking<F: AsRawFd>(file: &F) -> io::Result<()> {
    const F_GETFL: i32 = 3;
    const F_SETFL: i32 = 4;
    #[cfg(target_os = "macos")]
    const O_NONBLOCK: i32 = 0x0004;
    #[cfg(not(target_os = "macos"))]
    const O_NONBLOCK: i32 = 0x0800;
    let flags = unsafe { fcntl(file.as_raw_fd(), F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    if unsafe { fcntl(file.as_raw_fd(), F_SETFL, flags | O_NONBLOCK) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

struct DeadlinePipe<'a, R: Read + AsRawFd> {
    reader: &'a mut R,
    deadline: Instant,
}

impl<R: Read + AsRawFd> Read for DeadlinePipe<'_, R> {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        loop {
            let remaining = self.deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "frame read deadline",
                ));
            }
            let mut fd = PollFd {
                fd: self.reader.as_raw_fd(),
                events: 1,
                revents: 0,
            };
            let milliseconds = remaining.as_millis().min(i32::MAX as u128) as i32;
            let result = unsafe { poll(&mut fd, 1, milliseconds.max(1)) };
            if result > 0 {
                return self.reader.read(bytes);
            }
            if result < 0 {
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::Interrupted {
                    return Err(error);
                }
            }
        }
    }
}

struct DeadlinePipeWrite<'a, W: Write + AsRawFd> {
    writer: &'a mut W,
    deadline: Instant,
}

impl<W: Write + AsRawFd> Write for DeadlinePipeWrite<'_, W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        loop {
            let remaining = self.deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "host request write deadline",
                ));
            }
            let mut fd = PollFd {
                fd: self.writer.as_raw_fd(),
                events: 4,
                revents: 0,
            };
            let milliseconds = remaining.as_millis().min(i32::MAX as u128) as i32;
            let result = unsafe { poll(&mut fd, 1, milliseconds.max(1)) };
            if result > 0 {
                match self.writer.write(bytes) {
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => continue,
                    other => return other,
                }
            }
            if result < 0 {
                let error = io::Error::last_os_error();
                if error.kind() != io::ErrorKind::Interrupted {
                    return Err(error);
                }
            }
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }
}

/// A failed write or read leaves the request's execution status unknown. Callers
/// retain the original signed call and use historical lookup before resubmission.
pub fn invoke(
    socket: &Path,
    config: &Path,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>, String> {
    invoke_inner(socket, config, None, operation, payload)
}

/// An upgraded worker requires the executable image actually serving the
/// socket to match its durable host pin. Version 2 is mandatory on this path:
/// an older service rejects the envelope before it can forward the request.
pub fn invoke_pinned(
    socket: &Path,
    config: &Path,
    expected_host_sha256: &str,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>, String> {
    let expected = parse_host_sha256(expected_host_sha256)?;
    invoke_inner(socket, config, Some(&expected), operation, payload)
}

fn invoke_inner(
    socket: &Path,
    config: &Path,
    expected_host_sha256: Option<&[u8; 32]>,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>, String> {
    let config = read_config(config)?;
    if payload.len() >= HOST_MAX_FRAME {
        return Err("host request exceeds frame bound before transmission".to_owned());
    }
    let mut stream = UnixStream::connect(socket)
        .map_err(|e| format!("cannot connect to {}: {e}", socket.display()))?;
    stream
        .set_write_timeout(Some(Duration::from_secs(10)))
        .map_err(|e| format!("cannot set socket write deadline: {e}"))?;
    let mut frame = Vec::with_capacity(payload.len() + config.len() + 38);
    frame.push(if expected_host_sha256.is_some() { 2 } else { 1 });
    frame.extend_from_slice(&(config.len() as u32).to_le_bytes());
    frame.extend_from_slice(&config);
    if let Some(expected) = expected_host_sha256 {
        frame.extend_from_slice(expected);
    }
    frame.push(operation);
    frame.extend_from_slice(payload);
    write_frame(&mut stream, &frame).map_err(|e| format!("uncertain host request write: {e}"))?;
    let reply = read_frame(&mut DeadlinePipe {
        reader: &mut stream,
        deadline: Instant::now() + Duration::from_secs(600),
    })
    .map_err(|e| format!("uncertain host response read: {e}"))?
    .ok_or_else(|| "uncertain host response: connection closed".to_owned())?;
    if reply.len() > HOST_MAX_FRAME {
        return Err("uncertain host response exceeds host frame bound".to_owned());
    }
    if reply[0] == 254 {
        return Err(format!(
            "socket rejected request: {}",
            String::from_utf8_lossy(&reply[1..])
        ));
    }
    if reply[0] != operation && reply[0] != 255 {
        return Err(format!(
            "uncertain host response: unexpected operation {}",
            reply[0]
        ));
    }
    Ok(reply)
}

/// The socket directory must be owned by this account and inaccessible to
/// others. This closes the interval between bind and chmod on the socket.
pub fn serve(socket: &Path, host: &Path, config: &Path) -> Result<(), String> {
    serve_with_mode(socket, host, config, false)
}

pub fn serve_operator(socket: &Path, host: &Path, config: &Path) -> Result<(), String> {
    serve_with_mode(socket, host, config, true)
}

fn serve_with_mode(
    socket: &Path,
    host: &Path,
    config: &Path,
    operator: bool,
) -> Result<(), String> {
    let host_sha256 = host_image_sha256(host)?;
    let config_bytes = read_config(config)?;
    let catalog_enabled = serde_json::from_slice::<serde_json::Value>(&config_bytes)
        .map_err(|e| format!("invalid operator config JSON: {e}"))?
        .get("fnReplyCatalog")
        .is_some_and(serde_json::Value::is_object);
    let parent = socket
        .parent()
        .ok_or("socket requires a parent directory")?;
    let metadata = fs::metadata(parent)
        .map_err(|e| format!("cannot inspect socket directory {}: {e}", parent.display()))?;
    if !metadata.is_dir() || metadata.uid() != effective_uid() || metadata.mode() & 0o077 != 0 {
        return Err(format!(
            "socket directory {} must be owned by this user with mode 0700",
            parent.display()
        ));
    }
    let _service_lock = service_lock(&socket.with_extension("lock"))?;
    let pinned_config = socket.with_extension("config");
    pin_service_mode(
        &socket.with_extension("mode"),
        operator,
        pinned_config.exists(),
    )?;
    clear_stale_socket(socket)?;
    pin_config(&pinned_config, &config_bytes)?;
    let listener =
        UnixListener::bind(socket).map_err(|e| format!("cannot bind {}: {e}", socket.display()))?;
    let socket_metadata = fs::symlink_metadata(socket)
        .map_err(|e| format!("cannot inspect new socket {}: {e}", socket.display()))?;
    struct SocketGuard<'a>(&'a Path, u64, u64);
    impl Drop for SocketGuard<'_> {
        fn drop(&mut self) {
            if let Ok(metadata) = fs::symlink_metadata(self.0) {
                if metadata.file_type().is_socket()
                    && (metadata.dev(), metadata.ino()) == (self.1, self.2)
                {
                    let _ = fs::remove_file(self.0);
                }
            }
        }
    }
    let _guard = SocketGuard(socket, socket_metadata.dev(), socket_metadata.ino());
    fs::set_permissions(socket, fs::Permissions::from_mode(0o600))
        .map_err(|e| format!("cannot protect socket {}: {e}", socket.display()))?;
    let child = Command::new(host)
        .arg(&pinned_config)
        .arg("stdio")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot start host {}: {e}", host.display()))?;
    struct HostGuard(std::process::Child);
    impl Drop for HostGuard {
        fn drop(&mut self) {
            let _ = self.0.kill();
            let _ = self.0.wait();
        }
    }
    let mut host_guard = HostGuard(child);
    let mut input = host_guard.0.stdin.take().ok_or("host stdin unavailable")?;
    let mut output = host_guard
        .0
        .stdout
        .take()
        .ok_or("host stdout unavailable")?;
    set_nonblocking(&input).map_err(|e| format!("cannot bound host input pipe: {e}"))?;
    eprintln!(
        "mini: serving {} with host process {}",
        socket.display(),
        host_guard.0.id()
    );
    for accepted in listener.incoming() {
        let mut stream = accepted.map_err(|e| format!("socket accept failed: {e}"))?;
        if operator && peer_uid(&stream)? != effective_uid() {
            let _ = write_frame(&mut stream, b"\xfeoperator peer UID mismatch");
            continue;
        }
        stream
            .set_write_timeout(Some(Duration::from_secs(10)))
            .map_err(|e| format!("cannot set client write deadline: {e}"))?;
        let envelope = match read_frame(&mut DeadlinePipe {
            reader: &mut stream,
            deadline: Instant::now() + Duration::from_secs(10),
        }) {
            Ok(Some(frame)) => frame,
            Ok(None) => continue,
            Err(e) => {
                eprintln!("mini: discarded invalid socket frame: {e}");
                continue;
            }
        };
        let request = match request_from_envelope(&envelope, &config_bytes, &host_sha256) {
            Ok(request) => request,
            Err(reason) => {
                let mut refusal = vec![254];
                refusal.extend_from_slice(reason.as_bytes());
                let _ = write_frame(&mut stream, &refusal);
                continue;
            }
        };
        if request.len() > HOST_MAX_FRAME {
            let _ = write_frame(&mut stream, b"\xfehost frame exceeds bound");
            continue;
        }
        if !(if operator {
            allowed_operator_operation(request)
        } else {
            allowed_operation(request, catalog_enabled)
        }) {
            let _ = write_frame(&mut stream, b"\xfeoperation unavailable on selected socket");
            continue;
        }
        write_frame(
            &mut DeadlinePipeWrite {
                writer: &mut input,
                deadline: Instant::now() + Duration::from_secs(30),
            },
            request,
        )
        .map_err(|e| format!("host request status uncertain: {e}"))?;
        let reply = read_frame(&mut DeadlinePipe {
            reader: &mut output,
            deadline: Instant::now() + Duration::from_secs(600),
        })
        .map_err(|e| format!("host request status uncertain: {e}"))?
        .ok_or_else(|| "host closed during request; status uncertain".to_owned())?;
        if reply.len() > HOST_MAX_FRAME {
            return Err("host response exceeds bounded native frame; status uncertain".to_owned());
        }
        if let Err(error) = write_frame(&mut stream, &reply) {
            eprintln!("mini: client lost host reply; status uncertain: {error}");
        }
    }
    Ok(())
}

#[cfg(any(
    target_os = "macos",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd"
))]
fn peer_uid(stream: &UnixStream) -> Result<u32, String> {
    unsafe extern "C" {
        fn getpeereid(socket: i32, uid: *mut u32, gid: *mut u32) -> i32;
    }
    let mut uid = 0;
    let mut gid = 0;
    if unsafe { getpeereid(stream.as_raw_fd(), &mut uid, &mut gid) } != 0 {
        return Err(format!(
            "operator peer credential: {}",
            io::Error::last_os_error()
        ));
    }
    Ok(uid)
}

#[cfg(target_os = "linux")]
fn peer_uid(stream: &UnixStream) -> Result<u32, String> {
    #[repr(C)]
    struct Ucred {
        pid: i32,
        uid: u32,
        gid: u32,
    }
    unsafe extern "C" {
        fn getsockopt(fd: i32, level: i32, name: i32, value: *mut Ucred, length: *mut u32) -> i32;
    }
    let mut credential = Ucred {
        pid: 0,
        uid: 0,
        gid: 0,
    };
    let mut length = std::mem::size_of::<Ucred>() as u32;
    if unsafe { getsockopt(stream.as_raw_fd(), 1, 17, &mut credential, &mut length) } != 0
        || length as usize != std::mem::size_of::<Ucred>()
    {
        return Err(format!(
            "operator peer credential: {}",
            io::Error::last_os_error()
        ));
    }
    Ok(credential.uid)
}

#[cfg(not(any(
    target_os = "linux",
    target_os = "macos",
    target_os = "freebsd",
    target_os = "openbsd",
    target_os = "netbsd"
)))]
fn peer_uid(_stream: &UnixStream) -> Result<u32, String> {
    Err("operator peer credentials are unavailable on this platform".into())
}

fn effective_uid() -> u32 {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    unsafe { geteuid() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    #[test]
    fn pinned_envelope_checks_config_and_host_before_exposing_request() {
        let host = [7u8; 32];
        let other_host = [8u8; 32];
        let request = [13, b'4'];
        let v2 = [
            vec![2, 6, 0, 0, 0],
            b"config".to_vec(),
            host.to_vec(),
            request.to_vec(),
        ]
        .concat();
        assert_eq!(
            request_from_envelope(&v2, b"config", &host),
            Ok(request.as_slice())
        );
        assert_eq!(
            request_from_envelope(&v2, b"changed", &host),
            Err("config pin mismatch")
        );
        assert_eq!(
            request_from_envelope(&v2, b"config", &other_host),
            Err("host image pin mismatch")
        );
        assert_eq!(
            request_from_envelope(&v2[..v2.len() - 2], b"config", &host),
            Err("invalid socket envelope")
        );
        let v1 = [vec![1, 6, 0, 0, 0], b"config".to_vec(), request.to_vec()].concat();
        assert_eq!(
            request_from_envelope(&v1, b"config", &host),
            Ok(request.as_slice())
        );
        assert_ne!(v2[0], 1); // A prior v1-only service refuses rather than forwarding v2.
    }

    #[test]
    fn pinned_invocation_sends_v2_without_fallback() {
        let directory = Path::new("/tmp").join(format!(
            "mip-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let socket = directory.join("test.sock");
        let config = directory.join("config.json");
        fs::write(&config, b"config").unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        let host = [7u8; 32];
        let host_hex = "07".repeat(32);
        let thread = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let envelope = read_frame(&mut stream).unwrap().unwrap();
            assert_eq!(envelope[0], 2);
            assert_eq!(
                request_from_envelope(&envelope, b"config", &host),
                Ok(&[13, b'4'][..])
            );
            write_frame(&mut stream, &[13, 1]).unwrap();
        });
        assert_eq!(
            invoke_pinned(&socket, &config, &host_hex, 13, b"4").unwrap(),
            vec![13, 1]
        );
        thread.join().unwrap();
        assert!(invoke_pinned(&socket, &config, &"AB".repeat(32), 13, b"4").is_err());
        fs::remove_file(socket).unwrap();
        fs::remove_file(config).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    struct SmallReader<'a> {
        bytes: &'a [u8],
    }
    impl Read for SmallReader<'_> {
        fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
            let count = out.len().min(1).min(self.bytes.len());
            out[..count].copy_from_slice(&self.bytes[..count]);
            self.bytes = &self.bytes[count..];
            Ok(count)
        }
    }

    #[test]
    fn fragmented_frames_are_reassembled_and_truncation_is_uncertain() {
        let mut wire = Vec::new();
        write_frame(&mut wire, &[2, 0, 255, 7]).unwrap();
        assert_eq!(
            read_frame(&mut SmallReader { bytes: &wire }).unwrap(),
            Some(vec![2, 0, 255, 7])
        );
        assert_eq!(
            read_frame(&mut SmallReader { bytes: &wire[..6] })
                .unwrap_err()
                .kind(),
            io::ErrorKind::UnexpectedEof
        );
        assert!(read_frame(&mut SmallReader {
            bytes: &[0, 0, 0, 0]
        })
        .is_err());
    }

    #[test]
    fn socket_invocation_handles_fragmented_reply_and_marks_lost_reply_uncertain() {
        let directory = std::env::temp_dir().join(format!(
            "mini-transport-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let socket = directory.join("test.sock");
        let config = directory.join("config.json");
        fs::write(&config, b"config").unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        let thread = thread::spawn(move || {
            let (mut first, _) = listener.accept().unwrap();
            assert_eq!(
                read_frame(&mut first).unwrap(),
                Some([vec![1, 6, 0, 0, 0], b"config".to_vec(), vec![2, 42]].concat())
            );
            let mut reply = Vec::new();
            write_frame(&mut reply, &[2, 7, 8]).unwrap();
            for byte in reply {
                first.write_all(&[byte]).unwrap();
            }
            let (mut second, _) = listener.accept().unwrap();
            assert_eq!(
                read_frame(&mut second).unwrap(),
                Some([vec![1, 6, 0, 0, 0], b"config".to_vec(), vec![2, 42]].concat())
            );
        });
        assert_eq!(invoke(&socket, &config, 2, &[42]).unwrap(), vec![2, 7, 8]);
        assert!(invoke(&socket, &config, 2, &[42])
            .unwrap_err()
            .contains("uncertain"));
        thread.join().unwrap();
        fs::remove_file(socket).unwrap();
        fs::remove_file(config).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn host_pipe_deadline_bounds_missing_reply() {
        let (mut receiver, _writer) = UnixStream::pair().unwrap();
        let error = read_frame(&mut DeadlinePipe {
            reader: &mut receiver,
            deadline: Instant::now() + Duration::from_millis(20),
        })
        .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    }

    #[test]
    fn host_pipe_deadline_bounds_stalled_request_write() {
        let (mut writer, _reader) = UnixStream::pair().unwrap();
        set_nonblocking(&writer).unwrap();
        let error = write_frame(
            &mut DeadlinePipeWrite {
                writer: &mut writer,
                deadline: Instant::now() + Duration::from_millis(20),
            },
            &vec![7; MAX_FRAME],
        )
        .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
    }

    #[test]
    fn public_fn_operations_have_no_path_payload() {
        assert!(allowed_operation(&[12], false));
        assert!(!allowed_operation(&[12, b'/'], false));
        assert!(allowed_operation(&[13, b'0'], false));
        assert!(allowed_operation(&[13, b'1', b'2', b'3'], false));
        assert!(!allowed_operation(&[13], false));
        assert!(!allowed_operation(&[13, b'0', b'1'], false));
        assert!(!allowed_operation(&[13, b'1', b'/'], false));
        assert!(allowed_operation(&[14], false));
        assert!(!allowed_operation(&[14, b'/'], false));
        assert!(allowed_operation(&[15, b'2'], false));
        assert!(!allowed_operation(&[15, b'0', b'2'], false));
        assert!(!allowed_operation(&[16, b'R'], false));
        assert!(!allowed_operation(&[16], true));
        assert!(allowed_operation(&[16, b'R'], true));
        assert!(allowed_operation(&[18, b'1'], true));
        assert!(!allowed_operation(&[18, b'1'], false));
        assert!(!allowed_operation(&[18, b'/'], true));
        assert!(allowed_operation(&[17, 1, 0, 0, 0, b'C', b'O'], false));
        assert!(!allowed_operation(&[17, 0, 0, 0, 0, b'O'], false));
        assert!(!allowed_operation(&[17, 1, 0, 0, 0, b'C'], false));
        let mut oversized = vec![b'R'; 1_516_386];
        oversized[0] = 16;
        assert!(!allowed_operation(&oversized, true));
    }

    #[test]
    fn metering_requires_complete_bounded_byte_triple() {
        let mut frame = vec![19];
        frame.extend(2u32.to_le_bytes());
        frame.extend(b"{}");
        frame.extend(3u32.to_le_bytes());
        frame.extend(b"req");
        frame.extend(b"response");
        assert!(allowed_operation(&frame, false));
        assert!(!allowed_operation(&frame[..frame.len() - 8], false));
        let mut oversized = frame.clone();
        oversized[1..5].copy_from_slice(&4097u32.to_le_bytes());
        assert!(!allowed_operation(&oversized, false));
        let mut missing_request = frame;
        missing_request[7..11].copy_from_slice(&0u32.to_le_bytes());
        assert!(!allowed_operation(&missing_request, false));
        assert!(allowed_operation(&[20, 1], false));
        assert!(allowed_operation(&[21, 1], false));
        assert!(!allowed_operation(&[20], false));
        assert!(!allowed_operation(&[21], false));
    }

    #[test]
    fn current_birth_authoring_accepts_only_bounded_json_objects() {
        assert!(allowed_operation(&[30, b'{', b'}'], false));
        assert!(allowed_operation(&[31, b'{', b'}'], false));
        assert!(!allowed_operation(&[30, b'[', b']'], false));
        assert!(!allowed_operation(&[31, b'{'], false));
        let mut oversized = vec![b' '; 256 * 1024 + 2];
        oversized[0] = 30;
        oversized[1] = b'{';
        *oversized.last_mut().unwrap() = b'}';
        assert!(!allowed_operation(&oversized, false));
    }

    #[test]
    fn unsigned_share_issue_plan_stays_off_public_socket() {
        let mut assembly = vec![33];
        assembly.extend(1u32.to_le_bytes());
        assembly.extend(*b"PS");
        for request in [&[32, 1][..], assembly.as_slice()] {
            assert!(!allowed_operation(request, false));
            assert!(allowed_operator_operation(request));
        }
        assert!(!allowed_operator_operation(&[32]));
        assert!(!allowed_operator_operation(&[33, 1, 0, 0, 0, b'P']));
        assert!(!allowed_operator_operation(&[30, b'{', b'}']));
    }

    #[test]
    fn lifecycle_and_dispatch_routes_are_bounded_and_operator_only() {
        for operation in [22, 23, 26, 27, 34, 35, 38, 39] {
            assert!(allowed_operator_operation(&[operation, 1]));
            assert!(!allowed_operation(&[operation, 1], true));
            assert!(!allowed_operator_operation(&[operation]));
        }
        let oversized = vec![1; HOST_MAX_FRAME];
        for operation in [22, 23, 26, 27, 34, 35, 38, 39] {
            let mut request = vec![operation];
            request.extend_from_slice(&oversized);
            assert!(!allowed_operator_operation(&request));
        }

        let author = [36, 1];
        assert!(allowed_operator_operation(&author));
        assert!(!allowed_operation(&author, true));
        assert!(!allowed_operator_operation(&[36]));
        // ApplicationDispatchAdmission admits an 8 MiB HTTP body. Its
        // source-owned request envelope must fit above that body size.
        let mut large_author = vec![36];
        large_author.extend(vec![1; 8 * 1024 * 1024 + 4096]);
        assert!(allowed_operator_operation(&large_author));
        assert!(!allowed_operation(&large_author, true));
        large_author.resize(HOST_MAX_FRAME, 1);
        assert!(allowed_operator_operation(&large_author));
        large_author.push(1);
        assert!(!allowed_operator_operation(&large_author));

        let mut assembly = vec![37];
        assembly.extend(1u32.to_le_bytes());
        assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&assembly));
        assert!(!allowed_operation(&assembly, true));
        assert!(!allowed_operator_operation(&[37, 1, 0, 0, 0, b'P']));
        let mut empty_plan = assembly.clone();
        empty_plan[1..5].copy_from_slice(&0u32.to_le_bytes());
        assert!(!allowed_operator_operation(&empty_plan));
        let mut missing_signatures = assembly;
        missing_signatures[1..5].copy_from_slice(&2u32.to_le_bytes());
        assert!(!allowed_operator_operation(&missing_signatures));

        // A private operator service is not a generic tunnel into the public
        // authoring, observation, or selected-release receiver operations.
        for operation in [0, 1, 7, 8, 20, 21, 24, 25, 30, 31] {
            assert!(!allowed_operator_operation(&[operation, 1]));
        }
    }

    #[test]
    fn namespace_and_lifecycle_authoring_routes_stay_private_and_bounded() {
        for operation in [40, 41] {
            assert!(allowed_operator_operation(&[operation, 1]));
            assert!(!allowed_operation(&[operation, 1], true));
            assert!(!allowed_operator_operation(&[operation]));
            let mut too_large = vec![operation];
            too_large.extend(vec![1; 8193]);
            assert!(!allowed_operator_operation(&too_large));
        }

        assert!(allowed_operator_operation(&[42]));
        assert!(!allowed_operator_operation(&[42, 1]));
        assert!(!allowed_operation(&[42], true));

        let mut namespace_assembly = vec![43];
        namespace_assembly.extend(1u32.to_le_bytes());
        namespace_assembly.extend(b"P");
        namespace_assembly.extend([0x5a; 64]);
        assert!(allowed_operator_operation(&namespace_assembly));
        assert!(!allowed_operation(&namespace_assembly, true));
        assert!(!allowed_operator_operation(&[43, 1, 0, 0, 0, b'P', 0x5a]));
        let mut empty_plan = namespace_assembly.clone();
        empty_plan[1..5].copy_from_slice(&0u32.to_le_bytes());
        assert!(!allowed_operator_operation(&empty_plan));
        let mut wrong_signature_length = namespace_assembly;
        wrong_signature_length[1..5].copy_from_slice(&2u32.to_le_bytes());
        assert!(!allowed_operator_operation(&wrong_signature_length));
        let mut oversized_plan_length = wrong_signature_length;
        oversized_plan_length[1..5].copy_from_slice(&8192u32.to_le_bytes());
        assert!(!allowed_operator_operation(&oversized_plan_length));

        assert!(allowed_operator_operation(&[44, 1]));
        assert!(!allowed_operator_operation(&[44]));
        assert!(!allowed_operation(&[44, 1], true));
        let mut completion_assembly = vec![45];
        completion_assembly.extend(1u32.to_le_bytes());
        completion_assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&completion_assembly));
        assert!(!allowed_operation(&completion_assembly, true));
        assert!(!allowed_operator_operation(&[45, 1, 0, 0, 0, b'P']));

        assert!(allowed_operator_operation(&[50, 1]));
        assert!(!allowed_operator_operation(&[50]));
        assert!(!allowed_operation(&[50, 1], true));
        let mut begin_assembly = vec![51];
        begin_assembly.extend(1u32.to_le_bytes());
        begin_assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&begin_assembly));
        assert!(!allowed_operation(&begin_assembly, true));
        assert!(!allowed_operator_operation(&[51, 1, 0, 0, 0, b'P']));

        assert!(allowed_operator_operation(&[52, 1]));
        assert!(!allowed_operator_operation(&[52]));
        assert!(!allowed_operation(&[52, 1], true));
        let mut claim_assembly = vec![53];
        claim_assembly.extend(1u32.to_le_bytes());
        claim_assembly.extend(*b"PS");
        assert!(allowed_operator_operation(&claim_assembly));
        assert!(!allowed_operation(&claim_assembly, true));
        assert!(!allowed_operator_operation(&[53, 1, 0, 0, 0, b'P']));
    }

    #[test]
    fn service_mode_pin_refuses_public_to_operator_restart() {
        let directory = std::env::temp_dir().join(format!(
            "mini-service-mode-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        let mode = directory.join("socket.mode");
        pin_service_mode(&mode, false, false).unwrap();
        pin_service_mode(&mode, false, true).unwrap();
        assert!(pin_service_mode(&mode, true, true).is_err());
        fs::remove_file(&mode).unwrap();
        assert!(pin_service_mode(&mode, true, true).is_err());
        pin_service_mode(&mode, true, false).unwrap();
        assert!(pin_service_mode(&mode, false, true).is_err());
        fs::remove_file(mode).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn service_restart_reuses_exact_pin_and_only_recovers_a_stale_socket() {
        let directory = std::env::temp_dir().join(format!(
            "mini-restart-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        let lock_path = directory.join("host.lock");
        let first_lock = service_lock(&lock_path).unwrap();
        assert!(service_lock(&lock_path).is_err());
        drop(first_lock);
        let second_lock = service_lock(&lock_path).unwrap();
        let config = directory.join("host.config");
        pin_config(&config, b"fixed\n").unwrap();
        pin_config(&config, b"fixed\n").unwrap();
        assert!(pin_config(&config, b"drift\n").is_err());
        assert_eq!(fs::read(&config).unwrap(), b"fixed\n");

        let socket = directory.join("host.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        assert!(clear_stale_socket(&socket).is_err());
        drop(listener);
        clear_stale_socket(&socket).unwrap();
        assert!(!socket.exists());
        drop(second_lock);
        fs::remove_file(config).unwrap();
        fs::remove_file(lock_path).unwrap();
        fs::remove_dir(directory).unwrap();
    }
}
