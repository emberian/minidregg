//! One private, no-retry Mini author/submit operation for the resident SPK
//! supervisor. Op34's callback bytes are retained before source inspection;
//! an uncertain write/read leaves a durable marker and cannot be repeated.

use crate::io_context::IoContext;
use crate::dispatch_author::FixedAuthoring;
use crate::dispatch_inspection::{
    match_inspection, FixedCustody, HttpProjection, MatchedInspection,
};
use crate::hostd::{DispatchIdentity, Journal};
use crate::native_dispatch::{parse_op34_response, Op34Reply};
use crate::stream_continuity::ContinuityBinding;
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
use crate::host_operations::{RESPONSE_HOST_OUTCOME, RESPONSE_NO_RECORD, RESPONSE_PRIVATE_DISPATCH_NO_RECORD};
use crate::canonical::hex;
const ROUTE_BOUND_DISPATCH_OPCODE: u8 = crate::host_operations::APPLICATION_ROUTE_BOUND_DISPATCH;
const NO_RECORD_REFUSAL: &[u8] = b"DREGG/APPLICATION/DISPATCH-NO-RECORD-REFUSAL/v1";
const MAX_CONFIG: usize = 65_536;
const MAX_INSPECTION: usize = 96_822_080;
const MAX_AUTHOR_JSON: u64 = 22 * 1024 * 1024;
const RESPONSE_DEADLINE: Duration = Duration::from_secs(600);
const STOP_INSPECTION_DEADLINE: Duration = Duration::from_secs(300);
const MAX_HELPER_STDERR: u64 = 64 * 1024;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn read_bounded(path: &Path, bound: usize) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(&path).ctx("open", &path)?
        .take(bound as u64 + 1)
        .read_to_end(&mut bytes)?;
    if bytes.is_empty() || bytes.len() > bound {
        return Err(invalid("private native artifact size refused"));
    }
    Ok(bytes)
}

/// Read a READ-ONLY pinned input (the Host config) from a parent `pinned_input_dir` admits, through ONE descriptor: opened O_NOFOLLOW, then
/// fstat'ed on that same descriptor (a regular file owned by this user or root and writable by
/// neither group nor others), then read from it. A symlink, a directory or a file a non-owner can
/// alter is refused by name. The bytes returned are the bytes of that descriptor, so a digest taken
/// over them (check_pin) pins the content the check saw; with a parent `pinned_input_dir` has
/// admitted, no non-owner can swap the path between this check and the Host helper's own read.
pub(crate) fn read_pinned_input(path: &Path, bound: usize) -> io::Result<Vec<u8>> {
    read_pinned_input_fingerprinted(path, bound).map(|(bytes, _)| bytes)
}

/// As `read_pinned_input`, also returning the fingerprint of the descriptor the bytes came from.
fn read_pinned_input_fingerprinted(
    path: &Path,
    bound: usize,
) -> io::Result<(Vec<u8>, ImageFingerprint)> {
    let refuse = |property: &str| {
        Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("pinned input {} refused: {property}", path.display()),
        ))
    };
    pinned_input_dir(path.parent().ok_or_else(|| invalid("pinned input parent absent"))?)?;
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
        .ctx("open", &path)?;
    let metadata = file.metadata().ctx("inspect", &path)?;
    if !metadata.is_file() {
        return refuse("not a regular file (a symlink or directory is refused)");
    }
    let uid = metadata.uid();
    if uid != unsafe { libc::geteuid() } && uid != 0 {
        return refuse("owned by neither this user nor root");
    }
    if metadata.permissions().mode() & 0o022 != 0 {
        return refuse("writable by group or others");
    }
    let fingerprint = ImageFingerprint::of(&metadata);
    let mut bytes = Vec::new();
    file.take(bound as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.is_empty() || bytes.len() > bound {
        return Err(invalid("private native artifact size refused"));
    }
    Ok((bytes, fingerprint))
}

/// Create-new, owner-private, unsynced. For SCRATCH only: a helper's input that the very next step
/// hands to a child process (visible through the page cache) and that no recovery path reads back
/// (the dispatch attempt's copies are removed by `dispatch_fence::strip` at settlement). Nothing
/// recovery relies on may be written this way; use `write_new`.
pub(crate) fn write_new_unsynced(directory: &Path, name: &str, bytes: &[u8]) -> io::Result<PathBuf> {
    if bytes.is_empty() || bytes.len() > MAX_INSPECTION {
        return Err(invalid("private native artifact size refused"));
    }
    let path = directory.join(name);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&path).ctx("open", &path)?;
    file.write_all(bytes)?;
    Ok(path)
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
        .open(&path).ctx("open", &path)?;
    file.write_all(bytes)?;
    Ok(path)
}

pub(crate) fn private_dir(path: &Path) -> io::Result<()> {
    let metadata = fs::symlink_metadata(&path).ctx("inspect", &path)?;
    if !path.is_absolute()
        || !metadata.is_dir()
        || metadata.uid() != unsafe { libc::geteuid() }
        || metadata.permissions().mode() & 0o777 != 0o700
    {
        return Err(invalid("native attempt directory is not owner-private"));
    }
    Ok(())
}

/// A directory that holds a READ-ONLY pinned input (the operator socket's directory): absolute, a
/// real directory (not a symlink), owned by this user or by root, and writable by neither group
/// nor others. Unlike `private_dir`, group or other READ and SEARCH are allowed: on the hosted
/// frame the Host's deployment directory is 0710 for the `mini-sessions` group, because every
/// member's shell must read the pinned config there. Directories spk-host WRITES (attempt dirs,
/// journals) keep `private_dir`. The refusal names the path and the failed property.
pub(crate) fn pinned_input_dir(path: &Path) -> io::Result<()> {
    let refuse = |property: &str| {
        Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("pinned input directory {} refused: {property}", path.display()),
        ))
    };
    if !path.is_absolute() {
        return refuse("not an absolute path");
    }
    let metadata = fs::symlink_metadata(path).ctx("inspect", &path)?;
    if !metadata.is_dir() {
        return refuse("not a directory (a symlink or file is refused)");
    }
    let uid = metadata.uid();
    if uid != unsafe { libc::geteuid() } && uid != 0 {
        return refuse("owned by neither this user nor root");
    }
    if metadata.permissions().mode() & 0o022 != 0 {
        return refuse("writable by group or others");
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

use crate::file_identity::ImageFingerprint;

struct VerifiedImage {
    path: PathBuf,
    sha256: String,
    file: std::sync::Arc<File>,
    fingerprint: ImageFingerprint,
}

/// Holds the verified descriptor open for as long as the caller may execute
/// it; the `/proc/self/fd` path is valid only while this value lives.
#[derive(Debug)]
pub(crate) struct VerifiedExecutable(std::sync::Arc<File>);

impl VerifiedExecutable {
    pub(crate) fn path(&self) -> PathBuf {
        use std::os::fd::AsRawFd;
        PathBuf::from(format!("/proc/self/fd/{}", self.0.as_raw_fd()))
    }
}
impl std::os::fd::AsRawFd for VerifiedExecutable {
    fn as_raw_fd(&self) -> std::os::fd::RawFd {
        self.0.as_raw_fd()
    }
}

static VERIFIED_IMAGES: std::sync::Mutex<Vec<VerifiedImage>> = std::sync::Mutex::new(Vec::new());

fn image_path_metadata(path: &Path) -> io::Result<fs::Metadata> {
    let meta = fs::symlink_metadata(&path).ctx("inspect", &path)?;
    if !path.is_absolute() || !meta.is_file() || meta.permissions().mode() & 0o022 != 0 {
        return Err(invalid("selected Mini Host image identity refused"));
    }
    Ok(meta)
}

/// Returns the retained descriptor of exactly the verified inode.
pub(crate) fn verified_image(path: &Path, expected_sha256: &str) -> io::Result<VerifiedExecutable> {
    verified_image_hashing(path, expected_sha256).map(|(image, _)| image)
}

/// As `verified_image`, also saying whether this call hashed the bytes.
fn verified_image_hashing(
    path: &Path,
    expected_sha256: &str,
) -> io::Result<(VerifiedExecutable, bool)> {
    let named = ImageFingerprint::of(&image_path_metadata(path)?);
    let mut cache = VERIFIED_IMAGES
        .lock()
        .map_err(|_| invalid("Mini Host image cache poisoned"))?;
    if let Some(entry) = cache
        .iter()
        .find(|entry| entry.path == path && entry.sha256 == expected_sha256)
    {
        if entry.fingerprint == named
            && ImageFingerprint::of(&entry.file.metadata()?) == entry.fingerprint
        {
            return Ok((VerifiedExecutable(std::sync::Arc::clone(&entry.file)), false));
        }
    }
    cache.retain(|entry| entry.path != path);
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(&path).ctx("open", &path)?;
    let opened = ImageFingerprint::of(&file.metadata()?);
    if opened != named {
        return Err(invalid("selected Mini Host image changed while opened"));
    }
    let mut digest = Sha256::new();
    let mut chunk = vec![0u8; 1024 * 1024];
    loop {
        let count = file.read(&mut chunk)?;
        if count == 0 {
            break;
        }
        digest.update(&chunk[..count]);
    }
    if ImageFingerprint::of(&file.metadata()?) != opened {
        return Err(invalid("selected Mini Host image changed while hashed"));
    }
    if expected_sha256 != hex(&digest.finalize()) {
        return Err(invalid("selected Mini Host SHA-256 drift"));
    }
    let file = std::sync::Arc::new(file);
    cache.push(VerifiedImage {
        path: path.to_path_buf(),
        sha256: expected_sha256.to_owned(),
        file: std::sync::Arc::clone(&file),
        fingerprint: opened,
    });
    Ok((VerifiedExecutable(file), true))
}

struct VerifiedConfig {
    path: PathBuf,
    sha256: String,
    bytes: Vec<u8>,
    fingerprint: ImageFingerprint,
}

static VERIFIED_CONFIGS: std::sync::Mutex<Vec<VerifiedConfig>> = std::sync::Mutex::new(Vec::new());

/// The pinned config bytes, hashed once per inode. Every call still re-checks the parent
/// directory (`pinned_input_dir`) and that the path names a regular file with the fingerprint
/// (dev, ino, size, mode, owner, mtime, ctime) the bytes were read and hashed under; any
/// difference drops the entry and re-reads through `read_pinned_input`, re-hashing. A writer
/// cannot restore ctime, so an in-place edit is always seen.
fn verified_config(path: &Path, expected_sha256: &str) -> io::Result<Vec<u8>> {
    let parent = path.parent().ok_or_else(|| invalid("pinned input parent absent"))?;
    pinned_input_dir(parent)?;
    let named = fs::symlink_metadata(path).ctx("inspect", &path)?;
    let named = named.is_file().then(|| ImageFingerprint::of(&named));
    let mut cache = VERIFIED_CONFIGS
        .lock()
        .map_err(|_| invalid("Mini Host config cache poisoned"))?;
    if let Some(named) = named {
        if let Some(entry) = cache
            .iter()
            .find(|entry| entry.path == path && entry.sha256 == expected_sha256)
        {
            if entry.fingerprint == named {
                return Ok(entry.bytes.clone());
            }
        }
    }
    cache.retain(|entry| entry.path != path);
    let (bytes, fingerprint) = read_pinned_input_fingerprinted(path, MAX_CONFIG)?;
    if expected_sha256 != hex(&Sha256::digest(&bytes)) {
        return Err(invalid("selected Mini Host config SHA-256 drift"));
    }
    cache.push(VerifiedConfig {
        path: path.to_path_buf(),
        sha256: expected_sha256.to_owned(),
        bytes: bytes.clone(),
        fingerprint,
    });
    Ok(bytes)
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
        self.verified_host()?;
        let config = verified_config(&self.config, &self.config_sha256)?;
        let parent = self
            .socket
            .parent()
            .ok_or_else(|| invalid("operator socket lacks parent"))?;
        pinned_input_dir(parent)?;
        let socket = fs::symlink_metadata(&self.socket).ctx("inspect", &self.socket)?;
        if !socket.file_type().is_socket()
            || socket.uid() != unsafe { libc::geteuid() }
            || socket.permissions().mode() & 0o077 != 0
        {
            return Err(invalid("Mini operator socket identity refused"));
        }
        Ok(config)
    }

    /// The pinned Host image, verified once per inode. The first use hashes
    /// the bytes of an opened descriptor; later uses re-check that the path
    /// still names that inode and that neither has changed size, mode, owner,
    /// mtime or ctime, re-hashing on any difference. Helpers execute the
    /// verified descriptor itself, so the bytes run are the bytes hashed.
    fn verified_host(&self) -> io::Result<VerifiedExecutable> {
        verified_image(&self.host, &self.host_sha256)
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
        let pin_began = Instant::now();
        let _ = self.check_pin()?;
        let executable = self.verified_host()?;
        let pin_ms = pin_began.elapsed().as_millis();
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
        let meta = fs::symlink_metadata(&input).ctx("inspect", &input)?;
        if !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
            || meta.len() == 0
            || meta.len() > cap
        {
            return Err(invalid("Mini Host helper input identity or size refused"));
        }
        if let Some(bytes) = self.tool_in_session(command, kind, input, output, deadline)? {
            eprintln!("spk-host: tool-timing {command} {kind} pin_ms={pin_ms} session=1");
            return Ok(bytes);
        }
        let mut process = Command::new(executable.path());
        process.arg(&self.config).arg(command);
        if command == "profile" {
            let output_file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW)
                .open(&output).ctx("open", &output)?;
            process.stdout(Stdio::from(output_file));
        } else {
            if !kind.is_empty() {
                process.arg(kind);
            }
            process.arg(input).arg(output).stdout(Stdio::null());
        }
        let run_began = Instant::now();
        run_pinned(process, output, deadline)?;
        eprintln!("spk-host: tool-timing {command} {kind} pin_ms={pin_ms} host_ms={}", run_began.elapsed().as_millis());
        read_bounded(
            output,
            if command == "inspect" {
                MAX_INSPECTION
            } else {
                HOST_MAX_FRAME - 1
            },
        )
    }

    /// The detached `author`/`inspect`/`signatures` verb as one call on the operator socket (the
    /// Host's TOOL_AUTHOR, TOOL_INSPECT and TOOL_SIGNATURES operations), instead of a fresh Host
    /// process. The input file was written (and its identity checked) by the caller and stays as
    /// the audit copy; the output file and a refusal's `<output>.stderr` are written here as the
    /// detached verb writes them, and the bytes returned are the output file's. `None` means the
    /// session cannot answer and the caller runs the detached verb: no listener on the socket, a
    /// request or an output that does not fit one frame, or a command without a session operation.
    fn tool_in_session(
        &self,
        command: &str,
        kind: &str,
        input: &Path,
        output: &Path,
        deadline: Instant,
    ) -> io::Result<Option<Vec<u8>>> {
        use crate::host_operations::{TOOL_AUTHOR, TOOL_INSPECT, TOOL_SIGNATURES};
        let (operation, with_kind) = match command {
            "author" => (TOOL_AUTHOR, true),
            "inspect" => (TOOL_INSPECT, true),
            "signatures" => (TOOL_SIGNATURES, false),
            _ => return Ok(None),
        };
        if with_kind && (kind.is_empty() || kind.len() > u16::MAX as usize) {
            return Ok(None);
        }
        let mut payload = Vec::new();
        if with_kind {
            payload.extend_from_slice(&(kind.len() as u16).to_le_bytes());
            payload.extend_from_slice(kind.as_bytes());
        }
        File::open(input).ctx("open", &input)?.take(HOST_MAX_FRAME as u64).read_to_end(&mut payload)?;
        if payload.len() >= HOST_MAX_FRAME - 1 {
            return Ok(None);
        }
        let reply = match self.invoke_until(operation, &payload, deadline) {
            Ok(reply) => reply,
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::ConnectionRefused
                        | io::ErrorKind::NotFound
                        | io::ErrorKind::ConnectionReset
                        | io::ErrorKind::BrokenPipe
                        | io::ErrorKind::UnexpectedEof
                ) =>
            {
                return Ok(None)
            }
            Err(error) => return Err(error),
        };
        // `invoke_until` has checked the length prefix; byte 4 is the answering operation or a
        // response marker (a refusal of the call itself), then the tool status and its bytes.
        if reply[4] != operation || reply.len() < 6 {
            return Err(invalid("Mini Host tool call was refused"));
        }
        let data = &reply[6..];
        match reply[5] {
            0 => {
                let bound = if command == "inspect" { MAX_INSPECTION } else { HOST_MAX_FRAME - 1 };
                if data.is_empty() || data.len() > bound {
                    return Err(invalid("private native artifact size refused"));
                }
                let mut file = OpenOptions::new()
                    .write(true)
                    .create(true)
                    .truncate(true)
                    .mode(0o600)
                    .custom_flags(libc::O_NOFOLLOW)
                    .open(output).ctx("open", &output)?;
                file.write_all(data)?;
                Ok(Some(data.to_vec()))
            }
            1 => {
                let reason = String::from_utf8_lossy(data);
                if let Some(name) = output.file_name() {
                    let mut stderr_name = name.to_owned();
                    stderr_name.push(".stderr");
                    let _ = OpenOptions::new()
                        .write(true)
                        .create_new(true)
                        .mode(0o600)
                        .custom_flags(libc::O_NOFOLLOW)
                        .open(output.with_file_name(stderr_name))
                        .and_then(|mut file| file.write_all(&data[..data.len().min(MAX_HELPER_STDERR as usize)]));
                }
                let first = reason.lines().next().unwrap_or("").trim();
                eprintln!("spk-host: pinned Mini Host helper refused: {first}");
                Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("pinned Mini Host helper refused: {first}"),
                ))
            }
            _ => Ok(None),
        }
    }

    /// `inspect-stop-claim PLAN COMMITTED OUTPUT`: the current-image STOP
    /// claim inspection, run from the verified descriptor (never the path)
    /// under a deadline, its refusal reason retained beside `output`.
    pub(crate) fn inspect_stop_claim(
        &self,
        plan: &Path,
        committed: &Path,
        output: &Path,
        max: u64,
    ) -> io::Result<Vec<u8>> {
        let _ = self.pinned_config()?;
        let executable = self.verified_host()?;
        let mut process = Command::new(executable.path());
        process
            .arg(&self.config)
            .arg("inspect-stop-claim")
            .arg(plan)
            .arg(committed)
            .arg(output)
            .stdout(Stdio::null());
        run_pinned(process, output, Instant::now() + STOP_INSPECTION_DEADLINE)?;
        let _ = self.pinned_config()?;
        read_bounded(output, max as usize)
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
        let sha: [u8; 32] = crate::canonical::unhex_array(&self.host_sha256)
            .ok_or_else(|| invalid("Mini Host SHA-256 pin malformed"))?;
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
        let dispatch_reply = (operation == ROUTE_BOUND_DISPATCH_OPCODE && reply[4] == 34)
            || (operation == 34
                && reply[4] == RESPONSE_PRIVATE_DISPATCH_NO_RECORD
                && &reply[5..] == NO_RECORD_REFUSAL);
        // The Host's response markers are a namespace apart from requests:
        // NO_RECORD carries a receiver's decided refusal, contention or
        // unavailability (proven no-append), HOST_OUTCOME an undecided one.
        // Both answer the operation; the fence reads them apart.
        let marked = reply[4] == RESPONSE_NO_RECORD || reply[4] == RESPONSE_HOST_OUTCOME;
        if reply[4] != operation && !marked && !dispatch_reply {
            return Err(invalid("Mini operator reply opcode mismatch"));
        }
        Ok(reply)
    }
}

/// Block until `child` has exited or `deadline` passes, whichever is first, without reaping it: the
/// caller `try_wait`s afterwards. A pidfd turns the exit into a readable event, so a helper that
/// finishes is noticed at once instead of at the next 10 ms tick. Where `pidfd_open` is
/// unavailable the wait degrades to a 2 ms sleep, still bounded by the caller's loop.
pub(crate) fn wait_for_exit(child: &std::process::Child, deadline: Instant) {
    let fd = unsafe { libc::syscall(libc::SYS_pidfd_open, child.id() as libc::pid_t, 0) } as libc::c_int;
    if fd < 0 {
        std::thread::sleep(Duration::from_millis(2));
        return;
    }
    let remaining = deadline.saturating_duration_since(Instant::now());
    let millis = remaining.as_micros().div_ceil(1000).min(1000) as libc::c_int;
    let mut entry = libc::pollfd { fd, events: libc::POLLIN, revents: 0 };
    unsafe {
        libc::poll(&mut entry, 1, millis);
        libc::close(fd);
    }
}

/// Run one pinned Host helper to completion under `deadline`. Its stderr is
/// retained as `<output>.stderr` (at most `MAX_HELPER_STDERR` bytes, removed
/// when empty), and a refusal carries the first line of it: Lean's refusal
/// reason is never dropped.
fn run_pinned(mut process: Command, output: &Path, deadline: Instant) -> io::Result<()> {
    let mut stderr_name = output
        .file_name()
        .ok_or_else(|| invalid("helper output name absent"))?
        .to_owned();
    stderr_name.push(".stderr");
    let stderr_path = output.with_file_name(stderr_name);
    let stderr_file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&stderr_path).ctx("open", &stderr_path)?;
    process
        .stdin(Stdio::null())
        .stderr(Stdio::from(stderr_file.try_clone()?));
    if Instant::now() >= deadline {
        return Err(invalid("Mini helper deadline"));
    }
    let mut child = process.spawn()?;
    drop(process);
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
        wait_for_exit(&child, deadline);
    };
    if stderr_file.metadata()?.len() > MAX_HELPER_STDERR {
        stderr_file.set_len(MAX_HELPER_STDERR)?;
    }
    let mut reason = String::new();
    File::open(&stderr_path).ctx("open", &stderr_path)?
        .take(MAX_HELPER_STDERR)
        .read_to_string(&mut reason)
        .ok();
    if reason.is_empty() {
        let _ = fs::remove_file(&stderr_path).ctx("remove", &stderr_path);
    }
    if !status.success() {
        let first = reason.lines().next().unwrap_or("").trim();
        eprintln!("spk-host: pinned Mini Host helper refused: {first}");
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("pinned Mini Host helper refused: {first}"),
        ));
    }
    Ok(())
}

/// Every directory is freshly created under the resident's private journal.
/// Renewal artifacts have no ledger effect and are removed after inspection;
/// active storage is bounded by one attempt per open stream.
struct ContinuityAttemptDir(PathBuf);
impl ContinuityAttemptDir {
    fn create(parent: &Path) -> io::Result<Self> {
        private_dir(parent)?;
        let mut nonce = [0u8; 32];
        File::open("/dev/urandom").ctx("open", &"/dev/urandom")?.read_exact(&mut nonce)?;
        let path = parent.join(format!("continuity-{}", hex(&nonce)));
        DirBuilder::new().mode(0o700).create(&path)?;
        Ok(Self(path))
    }
}
impl Drop for ContinuityAttemptDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0).ctx("remove", &self.0);
    }
}

impl PrivateOperator {
    /// The pinned Host's Store key: `storeTag` in its `profile` output, Mini's
    /// tag of the Store identity, the genesis seed at the Store's root
    /// (`NativeHost.Config.storeIdentity`, `ApplicationLifecycleResidentProfile.storeTag`).
    /// Resident unit names,
    /// volumes, slices and the Store's state root all carry it; the physical
    /// host reads it from Mini and never derives its own.
    pub(crate) fn store_tag(&self, parent: &Path) -> io::Result<String> {
        let attempt = ContinuityAttemptDir::create(parent)?;
        let input = write_new(&attempt.0, "request.json", b"{}")?;
        let bytes = self.tool("profile", "", &input, &attempt.0.join("profile.json"))?;
        let value: serde_json::Value = serde_json::from_slice(&bytes)?;
        value
            .get("storeTag")
            .and_then(serde_json::Value::as_str)
            .filter(|tag| crate::broker::store_key(tag))
            .map(str::to_owned)
            .ok_or_else(|| invalid("pinned Host profile lacks a canonical Store tag"))
    }

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
        let response = self.invoke_until(crate::host_operations::APPLICATION_STREAM_RENEW, &request_bytes, deadline)?;
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
    pub matched: MatchedInspection,
    active_marker: PathBuf,
    active_bytes: Vec<u8>,
}

impl RecordedDispatch {
    #[cfg(test)]
    pub(crate) fn test_new(
        identity: DispatchIdentity,
        matched: MatchedInspection,
        active_marker: PathBuf,
        active_bytes: Vec<u8>,
    ) -> Self {
        Self {
            identity,
            matched,
            active_marker,
            active_bytes,
        }
    }

    /// Only a definite RPC result while the same app generation is Running
    /// settles this call's submit marker. Timeout, EOF, or a concurrent
    /// fence leaves both physical and native attempt records for audit.
    pub(crate) fn finish(self, journal: &Journal, delivered: bool) -> io::Result<()> {
        journal.finish_dispatch(&self.identity, delivered)?;
        let status = if delivered { "delivered" } else { "recorded-undelivered" };
        settle_committed(&self.active_marker, &self.active_bytes, status)
    }

    /// The worker fence proves this exact command is no longer held (or was
    /// never enqueued). The journal keeps its operation terminally Uncertain
    /// and never dispatchable again; the native outcome itself was definite
    /// (committed and inspected) before DeliveryRequested, so once the journal
    /// has taken that custody this call's submit marker is settled with the
    /// shared slot. Without a matching fence nothing is released.
    pub(crate) fn release_uncertain(
        self,
        journal: &Journal,
        fence: crate::rpc_adapter::DispatchFence,
    ) -> io::Result<()> {
        journal.finish_dispatch_uncertain_released(&self.identity, fence)?;
        settle_committed(&self.active_marker, &self.active_bytes, "delivery-uncertain-released")
    }
}

impl CommittedDispatch {
    /// The call's submit marker is only settled after hostd has written its
    /// separate DeliveryRequested tombstone. A crash in either interval
    /// leaves this one call undecided (it counts toward the journal's bound
    /// and is never looked up as absent: its permit was committed).
    pub(crate) fn record_delivery_requested(
        self,
        journal: &Journal,
    ) -> io::Result<RecordedDispatch> {
        if fs::read(&self.active_marker).ctx("read", &self.active_marker)? != self.active_bytes {
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
            request_digest: self.matched.physical_request_digest.clone(),
            app: self.matched.app,
            app_generation: self.matched.app_generation,
            invocation_id: invocation_id.to_owned(),
            operation_id: self.matched.operation_id.clone(),
            session_resource: self.matched.session_resource.clone(),
            session_generation: self.matched.session_generation.clone(),
            dispatch_transaction: self.matched.dispatch_transaction.clone(),
            dispatch_event: self.matched.dispatch_event.clone(),
        };
        journal.request_dispatch(identity.clone(), &self.payload)?;
        Ok(RecordedDispatch {
            identity,
            matched: self.matched,
            active_marker: self.active_marker,
            active_bytes: self.active_bytes,
        })
    }
}

/// The attempt directory is new and durable before any mutation. A marker is
/// written before op34/164; once present, submission refuses to run again for
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
    let request_json = write_new_unsynced(attempt_dir, "request.json", &serde_json::to_vec(&request)?)?;
    let request_bin = attempt_dir.join("request.bin");
    let request_bytes = operator.tool_until(
        "author",
        "application-dispatch-request",
        &request_json,
        &request_bin,
        deadline,
    )?;
    let plan_reply = operator.invoke_until(crate::host_operations::APPLICATION_DISPATCH_PLAN, &request_bytes, deadline)?;
    if plan_reply[4] != 36 {
        return Err(crate::dispatch_fence::refused_before_submit(
            operator,
            attempt_dir,
            operation_id,
            crate::host_operations::APPLICATION_DISPATCH_PLAN,
            &plan_reply,
        ));
    }
    let plan_bytes = &plan_reply[5..];
    let plan_bin = write_new_unsynced(attempt_dir, "plan.bin", plan_bytes)?;
    let plan_json_path = attempt_dir.join("plan.json");
    let plan_json = operator.tool_until(
        "inspect",
        "application-dispatch-plan",
        &plan_bin,
        &plan_json_path,
        deadline,
    )?;
    let signatures = custody.sign_plan(plan_bytes, &plan_json, &request_bytes, &request)?;
    let signatures_json = write_new_unsynced(
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
    let ingress_reply = operator.invoke_until(crate::host_operations::APPLICATION_DISPATCH_ASSEMBLE, &pair, deadline)?;
    if ingress_reply[4] != 37 {
        return Err(crate::dispatch_fence::refused_before_submit(
            operator,
            attempt_dir,
            operation_id,
            crate::host_operations::APPLICATION_DISPATCH_ASSEMBLE,
            &ingress_reply,
        ));
    }
    let ingress = &ingress_reply[5..];
    write_new(attempt_dir, "ingress.bin", ingress)?;
    Ok(ingress.to_vec())
}

fn validate_route_binding(
    custody: &FixedAuthoring,
    binding: Option<&ContinuityBinding>,
    namespace: &(String, String),
) -> io::Result<()> {
    if let Some(binding) = binding {
        binding.validate()?;
        if binding.domain != namespace.0
            || binding.semantics != namespace.1
            || binding.app != custody.app
            || binding.session != custody.session
            || binding.subject != custody.subject
            || binding.ticket_resource != custody.ticket_resource
        {
            return Err(invalid(
                "fixed route binding differs from custody or pinned namespace",
            ));
        }
    }
    Ok(())
}

/// Mini represents its 256-bit digests as Nats; Rust retains little-endian bytes.
fn digest_decimal(bytes: &[u8; 32]) -> String {
    let mut digits = vec![0_u8];
    for byte in bytes.iter().rev() {
        let mut carry = u16::from(*byte);
        for digit in &mut digits {
            let value = u16::from(*digit) * 256 + carry;
            *digit = (value % 10) as u8;
            carry = value / 10;
        }
        while carry != 0 {
            digits.push((carry % 10) as u8);
            carry /= 10;
        }
    }
    digits
        .iter()
        .rev()
        .map(|digit| char::from(b'0' + *digit))
        .collect()
}

fn route_bound_dispatch_json(binding: &ContinuityBinding, ingress: &[u8]) -> serde_json::Value {
    json!({"domain":binding.domain,"semantics":binding.semantics,
        "app":binding.app,"appGeneration":binding.app_generation,"session":binding.session,
        "sessionGeneration":binding.session_generation,"subject":binding.subject,
        "ticketResource":binding.ticket_resource,"sessionFingerprint":digest_decimal(&binding.session_fingerprint),
        "ingressHex":hex(ingress)})
}

fn settle_committed(active: &Path, expected: &[u8], status: &str) -> io::Result<()> {
    crate::dispatch_fence::settle(
        active,
        expected,
        &json!({"protocol":"mini-spk-dispatch-resolution-v1","status":status,"by":"committed-permit"}),
    )
}

struct SubmittedDispatch {
    frame: Vec<u8>,
    active_marker: PathBuf,
    active_bytes: Vec<u8>,
}

impl SubmittedDispatch {
    /// A confirmed historical receipt is evidence of a Store record, never a
    /// fresh physical-delivery permit.
    fn committed_payload(&self) -> io::Result<Vec<u8>> {
        match parse_op34_response(&self.frame)? {
            Op34Reply::CommittedBytes(payload) => Ok(payload.to_vec()),
            Op34Reply::OutcomeBytes(_) => {
                Err(invalid("Mini op34 did not commit a delivery permit"))
            }
        }
    }
}

/// What one submit produced.
enum Submit {
    /// A whole reply frame; the call's submit marker is still armed.
    Frame(SubmittedDispatch),
    /// Lean's positive no-record refusal; the call is settled.
    NoRecord(crate::dispatch_fence::DispatchOutcome),
    /// No reply frame; the call's submit marker is still armed.
    Lost {
        error: io::Error,
        active_marker: PathBuf,
        active_bytes: Vec<u8>,
    },
}

/// Only the fresh private response from this call can certify no Store
/// record. The per-call markers are durable before op34/164 and the same
/// attempt can never be submitted twice; no journal-wide marker exists, so
/// another member's call never waits on this one (`dispatch_fence`).
fn submit_once(
    attempt_dir: &Path,
    operation_id: &str,
    ingress: &[u8],
    opcode: u8,
    submission: &[u8],
    invoke: impl FnOnce(u8, &[u8]) -> io::Result<Vec<u8>>,
) -> io::Result<Submit> {
    if !matches!(opcode, 34 | ROUTE_BOUND_DISPATCH_OPCODE) {
        return Err(invalid("native dispatch submit opcode refused"));
    }
    let marker = json!({"protocol":"mini-spk-dispatch-submit-requested-v1",
        "operationId":operation_id,"ingressSha256":hex(&Sha256::digest(ingress)),
        "submitOpcode":opcode,"submissionSha256":hex(&Sha256::digest(submission))});
    let active_bytes = serde_json::to_vec(&marker)?;
    let active_marker = crate::dispatch_fence::arm(attempt_dir, &active_bytes)?;
    let frame = match invoke(opcode, submission) {
        Ok(frame) => frame,
        Err(error) => {
            return Ok(Submit::Lost {
                error,
                active_marker,
                active_bytes,
            })
        }
    };
    write_new(attempt_dir, &format!("op{opcode}-frame.bin"), &frame)?;
    let mut refusal = Vec::with_capacity(NO_RECORD_REFUSAL.len() + 5);
    refusal.extend_from_slice(&((NO_RECORD_REFUSAL.len() + 1) as u32).to_le_bytes());
    refusal.push(ROUTE_BOUND_DISPATCH_OPCODE);
    refusal.extend_from_slice(NO_RECORD_REFUSAL);
    if frame == refusal {
        // Source issues this unique frame only before entering durable submit.
        // Generic outcomes, EOF and malformed frames never reach this branch.
        return Ok(Submit::NoRecord(crate::dispatch_fence::no_record(
            &active_marker,
            &active_bytes,
            operation_id,
        )?));
    }
    Ok(Submit::Frame(SubmittedDispatch {
        frame,
        active_marker,
        active_bytes,
    }))
}

pub(crate) fn dispatch_opcode(binding: Option<&ContinuityBinding>) -> u8 {
    if binding.is_some() {
        ROUTE_BOUND_DISPATCH_OPCODE
    } else {
        34
    }
}

pub(crate) fn author_and_submit(
    operator: &PrivateOperator,
    custody: &FixedAuthoring,
    http: &HttpProjection<'_>,
    operation_id: &str,
    attempt_dir: &Path,
    route_binding: Option<&ContinuityBinding>,
    namespace: &(String, String),
) -> io::Result<CommittedDispatch> {
    // Fail before creating an attempt or entering any native authoring route.
    validate_route_binding(custody, route_binding, namespace)?;
    #[cfg(feature = "integration-qualification")]
    let qualification = qualification::claim(custody, http, operation_id, attempt_dir)?;
    let deadline = Instant::now() + RESPONSE_DEADLINE;
    let began = Instant::now();
    let ingress =
        author_signed_ingress(operator, custody, http, operation_id, attempt_dir, deadline)?;
    let t_author = began.elapsed().as_millis();
    let opcode = dispatch_opcode(route_binding);
    let submission = match route_binding {
        None => ingress.clone(),
        Some(binding) => {
            let input = write_new(
                attempt_dir,
                "route-bound-dispatch.json",
                &serde_json::to_vec(&route_bound_dispatch_json(binding, &ingress))?,
            )?;
            operator.tool_until(
                "author",
                "application-route-bound-dispatch",
                &input,
                &attempt_dir.join("route-bound-dispatch.bin"),
                deadline,
            )?
        }
    };
    let t_route = began.elapsed().as_millis();
    let submitted = submit_once(
        attempt_dir,
        operation_id,
        &ingress,
        opcode,
        &submission,
        |opcode, bytes| {
            #[cfg(feature = "integration-qualification")]
            if let Some(trigger) = &qualification {
                return qualification::run(
                    trigger,
                    operator,
                    custody,
                    http,
                    attempt_dir,
                    opcode,
                    bytes,
                );
            }
            operator.invoke_until(opcode, bytes, deadline)
        },
    )?;
    let t_submit = began.elapsed().as_millis();
    let submitted = match submitted {
        Submit::Frame(submitted) => submitted,
        Submit::NoRecord(outcome) => return Err(outcome.into_error()),
        Submit::Lost {
            error,
            active_marker,
            active_bytes,
        } => {
            eprintln!("spk-host: op{operation_id} submit reply lost: {error}");
            return Err(crate::dispatch_fence::decide(
                operator,
                &active_marker,
                &active_bytes,
                operation_id,
                &ingress,
                crate::dispatch_fence::Reply::Lost,
            )
            .into_error());
        }
    };
    let Ok(payload) = submitted.committed_payload() else {
        return Err(crate::dispatch_fence::decide(
            operator,
            &submitted.active_marker,
            &submitted.active_bytes,
            operation_id,
            &ingress,
            crate::dispatch_fence::Reply::Frame(&submitted.frame),
        )
        .into_error());
    };
    // Lean committed a permit for this exact call. If it cannot be inspected
    // and matched here, the permit is never used: the call is recorded and
    // undelivered, and fd3 was never touched.
    let inspected = (|| {
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
        Ok(matched)
    })();
    eprintln!(
        "spk-host: author-timing op={operation_id} author_ms={t_author} route_ms={} submit_ms={} inspect_ms={}",
        t_route - t_author,
        t_submit - t_route,
        began.elapsed().as_millis() - t_submit
    );
    let matched = match inspected {
        Ok(matched) => matched,
        Err(error) => {
            eprintln!("spk-host: op{operation_id} committed permit refused: {error}");
            let settled = crate::dispatch_fence::settle(
                &submitted.active_marker,
                &submitted.active_bytes,
                &json!({"protocol":"mini-spk-dispatch-resolution-v1",
                    "status":"recorded-undelivered","by":"permit-inspection-refused",
                    "permitSha256":hex(&Sha256::digest(&payload))}),
            );
            return Err(crate::dispatch_fence::DispatchOutcome {
                operation: Some(operation_id.to_owned()),
                status: if settled.is_ok() {
                    crate::dispatch_fence::Status::RecordedUndelivered
                } else {
                    crate::dispatch_fence::Status::Uncertain
                },
                lean: None,
            }
            .into_error());
        }
    };
    Ok(CommittedDispatch {
        payload,
        matched,
        active_marker: submitted.active_marker,
        active_bytes: submitted.active_bytes,
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
        let response = self.invoke_until(crate::host_operations::APPLICATION_ROUTE_INSPECT, &request_bytes, deadline)?;
        let payload = response
            .get(5..)
            .ok_or_else(|| invalid("short route admission reply"))?;
        if response.get(4) != Some(&154)
            || !payload.starts_with(b"DREGG/APPLICATION/ROUTE-ADMISSION-ATTESTATION/v1")
        {
            // Name the Host's answer: its marker byte and the printable part of
            // its outcome frame (a refusal reason is ASCII inside it).
            let text: String = payload.iter().take(512).map(|&b| if (0x20..0x7f).contains(&b) { b as char } else { '.' }).collect();
            let _ = write_new(&attempt.0, "refusal.bin", payload);
            return Err(io::Error::new(io::ErrorKind::InvalidInput, format!(
                "Mini refused current route admission (marker {:?}): {text}", response.get(4))));
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

/// Deliberately absent from ordinary release builds. This qualification path
/// can race only the resident's freshly prepared request, never supplied grants.
#[cfg(feature = "integration-qualification")]
pub(crate) mod qualification {
    use super::*;
    use serde::Deserialize;
    use serde_json::Value;

    #[derive(Deserialize)]
    #[serde(rename_all = "camelCase", deny_unknown_fields)]
    pub(super) struct Trigger {
        protocol: String,
        nonce_hex: String,
        app: String,
        session: String,
        subject: String,
        ticket_resource: String,
        session_kind: String,
        operation_id: String,
        method: String,
        path_and_query: String,
        signed_api_path: Option<String>,
    }
    fn private_read(path: &Path) -> io::Result<Vec<u8>> {
        let mut file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
            .open(&path).ctx("open", &path)?;
        let meta = file.metadata()?;
        if !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
            || meta.len() > MAX_CONFIG as u64
        {
            return Err(invalid("qualification file identity refused"));
        }
        let mut bytes = Vec::new();
        std::io::Read::by_ref(&mut file)
            .take(MAX_CONFIG as u64 + 1)
            .read_to_end(&mut bytes)?;
        if bytes.is_empty() || bytes.len() > MAX_CONFIG || bytes.len() as u64 != meta.len() {
            return Err(invalid("qualification file size refused"));
        }
        Ok(bytes)
    }
    pub(super) fn claim(
        custody: &FixedAuthoring,
        http: &HttpProjection<'_>,
        operation: &str,
        attempt: &Path,
    ) -> io::Result<Option<Trigger>> {
        let parent = attempt
            .parent()
            .ok_or_else(|| invalid("qualification parent absent"))?;
        let bytes = match private_read(&parent.join("dispatch-race-trigger.json")) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(error),
        };
        // Check every ancestor before accepting operator qualification controls.
        let _ = Journal::open(parent)?;
        let trigger: Trigger = serde_json::from_slice(&bytes)?;
        let signed_path = match http.route {
            crate::dispatch_inspection::Route::Browser => None,
            crate::dispatch_inspection::Route::Api { signed_path } => Some(signed_path),
        };
        if trigger.protocol != "mini-spk-dispatch-race-trigger-v1"
            || !crate::canonical::hex64(&trigger.nonce_hex)
            || trigger.app != custody.app
            || trigger.session != custody.session
            || trigger.subject != custody.subject
            || trigger.ticket_resource != custody.ticket_resource
            || trigger.session_kind != custody.session_kind
            || trigger.operation_id != operation
            || trigger.method != "GET"
            || http.method != "GET"
            || !http.body.is_empty()
            || trigger.path_and_query != http.path_and_query
            || trigger.signed_api_path.as_deref() != signed_path
        {
            return Err(invalid(
                "qualification trigger differs from this exact resident request",
            ));
        }
        write_new(parent, "dispatch-race-claimed.json", &bytes)?;
        Ok(Some(trigger))
    }
    #[derive(Deserialize)]
    #[serde(rename_all = "camelCase", deny_unknown_fields)]
    struct Go {
        protocol: String,
        nonce_hex: String,
        submission_sha256: String,
    }
    fn await_go(attempt: &Path, nonce: &str, hash: &str, deadline: Instant) -> io::Result<()> {
        loop {
            if Instant::now() >= deadline {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "qualification go deadline",
                ));
            }
            match private_read(&attempt.join("race-go.json")) {
                Ok(bytes) => {
                    let go: Go = serde_json::from_slice(&bytes)?;
                    if go.protocol != "mini-spk-dispatch-race-go-v1"
                        || go.nonce_hex != nonce
                        || go.submission_sha256 != hash
                    {
                        return Err(invalid("qualification go differs from retained submission"));
                    }
                    return Ok(());
                }
                Err(error) if error.kind() == io::ErrorKind::NotFound => {
                    std::thread::sleep(Duration::from_millis(5))
                }
                Err(error) => return Err(error),
            }
        }
    }
    fn select_winner(
        replies: &[io::Result<Vec<u8>>],
        mut inspect: impl FnMut(usize, bool, &[u8]) -> io::Result<Value>,
    ) -> io::Result<(usize, Value)> {
        if replies.len() != 2 {
            return Err(invalid("qualification requires exactly two responses"));
        }
        let mut winner = None;
        let mut historical = None;
        for (index, response) in replies.iter().enumerate() {
            let frame = response
                .as_ref()
                .map_err(|_| invalid("qualification response lost; outcome uncertain"))?;
            match parse_op34_response(frame)? {
                Op34Reply::CommittedBytes(payload) => {
                    if winner.is_some() {
                        return Err(invalid("qualification returned two fresh permits"));
                    }
                    winner = Some((index, inspect(index, true, payload)?));
                }
                Op34Reply::OutcomeBytes(payload) => {
                    if historical.is_some() {
                        return Err(invalid("qualification returned no fresh permit"));
                    }
                    let outcome = inspect(index, false, payload)?;
                    // Confirmation describes Store provenance, not fresh CAS
                    // authority. An AlreadyPresent loser may say installed.
                    if outcome["type"] != "confirmed"
                        || !matches!(
                            outcome["confirmation"].as_str(),
                            Some("installed" | "replayed" | "recoveredAfterUncertainResponse")
                        )
                    {
                        return Err(invalid(
                            "qualification loser is not a historical confirmed receipt",
                        ));
                    }
                    historical = Some(outcome);
                }
            }
        }
        let (index, permit) = winner.ok_or_else(|| invalid("qualification fresh permit absent"))?;
        let receipt =
            historical.ok_or_else(|| invalid("qualification historical receipt absent"))?;
        for field in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
            let expected = permit["receipt"][field]
                .as_str()
                .ok_or_else(|| invalid("qualification permit receipt field absent"))?;
            if receipt[field].as_str() != Some(expected) {
                return Err(invalid(
                    "qualification historical receipt differs from sole permit",
                ));
            }
        }
        Ok((index, receipt))
    }
    pub(super) fn run(
        trigger: &Trigger,
        operator: &PrivateOperator,
        custody: &FixedAuthoring,
        http: &HttpProjection<'_>,
        attempt: &Path,
        opcode: u8,
        submission: &[u8],
    ) -> io::Result<Vec<u8>> {
        let parent = attempt
            .parent()
            .ok_or_else(|| invalid("qualification parent absent"))?;
        let hash = hex(&Sha256::digest(submission));
        let ready = json!({"protocol":"mini-spk-dispatch-race-ready-v1","nonceHex":trigger.nonce_hex,
            "operationId":trigger.operation_id,"attemptDirectory":attempt,"opcode":opcode,
            "ingressSha256":hex(&Sha256::digest(read_bounded(&attempt.join("ingress.bin"),HOST_MAX_FRAME)?)),
            "submissionSha256":hash});
        // submit_once has written its normal per-attempt and global markers.
        write_new(
            parent,
            "dispatch-race-ready.json",
            &serde_json::to_vec(&ready)?,
        )?;
        let evaluate = || -> io::Result<(Vec<u8>, Value)> {
            await_go(
                attempt,
                &trigger.nonce_hex,
                &hash,
                Instant::now() + Duration::from_secs(60),
            )?;
            let barrier = std::sync::Barrier::new(2);
            let replies = std::thread::scope(|scope| {
                let workers: Vec<_> = (0..2).map(|index| {
                    let barrier = &barrier;
                    scope.spawn(move || -> io::Result<Vec<u8>> {
                        barrier.wait();
                        let response = operator.invoke_until(opcode,submission,Instant::now()+RESPONSE_DEADLINE);
                        match response {
                            Ok(frame) => { write_new(attempt,&format!("race-{index}-frame.bin"),&frame)?; Ok(frame) }
                            Err(error) => {
                                write_new(attempt,&format!("race-{index}-error.json"),&serde_json::to_vec(&json!({"status":"uncertain","error":error.to_string()}))?)?;
                                Err(error)
                            }
                        }
                    })
                }).collect();
                workers
                    .into_iter()
                    .map(|worker| {
                        worker.join().unwrap_or_else(|_| {
                            Err(invalid("qualification worker panicked; outcome uncertain"))
                        })
                    })
                    .collect::<Vec<_>>()
            });
            let (index, receipt) = select_winner(&replies, |index, permit, payload| {
                let payload_path =
                    write_new(attempt, &format!("race-{index}-payload.bin"), payload)?;
                let bytes = operator.tool(
                    "inspect",
                    if permit {
                        "application-dispatch-committed"
                    } else {
                        "outcome"
                    },
                    &payload_path,
                    &attempt.join(format!("race-{index}-inspection.json")),
                )?;
                if permit {
                    let fixed = FixedCustody {
                        app: &custody.app,
                        subject: &custody.subject,
                        session: &custody.session,
                        ticket: &custody.ticket_resource,
                    };
                    let matched = match_inspection(payload, &bytes, http, &fixed)?;
                    if matched.operation_id != trigger.operation_id {
                        return Err(invalid("qualification permit operation drift"));
                    }
                }
                Ok(serde_json::from_slice(&bytes)?)
            })?;
            let selected = json!({"protocol":"mini-spk-dispatch-race-selection-v1","operationId":trigger.operation_id,
                "nonceHex":trigger.nonce_hex,"winnerIndex":index,"historicalIndex":1-index,"receipt":receipt});
            write_new(
                attempt,
                "race-selection.json",
                &serde_json::to_vec(&selected)?,
            )?;
            let frame = replies
                .into_iter()
                .nth(index)
                .ok_or_else(|| invalid("qualification winner absent"))??;
            Ok((frame, selected))
        };
        let evaluated = evaluate();
        let result = match &evaluated {
            Ok((_, selected)) => {
                json!({"status":"winner-forwarded-to-resident","selection":selected})
            }
            Err(error) => json!({"status":"uncertain-or-failed","error":error.to_string()}),
        };
        write_new(
            parent,
            "dispatch-race-result.json",
            &serde_json::to_vec(&json!({
            "protocol":"mini-spk-dispatch-race-result-v1","nonceHex":trigger.nonce_hex,
            "attemptDirectory":attempt,"operationId":trigger.operation_id,"result":result,
            "physicalDeliveries":0,"chargeCountIndependentlyVerified":false,
            "deliveryEvidence":"race-delivery-result.json in attemptDirectory",
            "recovery":"terminal-fixture-checked-stop-new-generation"}))?,
        )?;
        evaluated.map(|(frame, _)| frame)
    }
    /// Evidence is emitted around the real resident RpcDriver call. A transport
    /// error is not proof of zero delivery, and never reports a successful one.
    pub(crate) fn delivery_event(attempt: &Path, response: Option<bool>) -> io::Result<()> {
        match private_read(&attempt.join("race-selection.json")) {
            Ok(_) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
            Err(error) => return Err(error),
        }
        let (name, value) = match response {
            None => (
                "race-delivery-requested.json",
                json!({"status":"rpc-invocation-requested","physicalDeliveries":0}),
            ),
            Some(true) => (
                "race-delivery-result.json",
                json!({"status":"app-response-received","physicalDeliveries":1}),
            ),
            Some(false) => (
                "race-delivery-result.json",
                json!({"status":"rpc-error-delivery-uncertain","physicalDeliveries":null}),
            ),
        };
        write_new(attempt, name, &serde_json::to_vec(&value)?)?;
        Ok(())
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        fn framed(payload: &[u8]) -> Vec<u8> {
            let mut frame = ((payload.len() + 1) as u32).to_le_bytes().to_vec();
            frame.push(34);
            frame.extend_from_slice(payload);
            frame
        }
        fn permit() -> Vec<u8> {
            framed(b"DREGG/APPLICATION/DISPATCH-COMMITTED-PERMIT/v1x")
        }
        fn receipt() -> Vec<u8> {
            framed(b"DREGG/NATIVE-HOST/OUTCOME/v7x")
        }
        fn inspection(permit: bool) -> Value {
            let receipt =
                json!({"transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"});
            if permit {
                json!({"receipt":receipt})
            } else {
                let mut result = receipt;
                result["type"] = json!("confirmed");
                result["confirmation"] = json!("replayed");
                result
            }
        }
        #[test]
        fn race_selects_only_exact_one_permit_and_matching_historical_receipt() {
            for reversed in [false, true] {
                let replies = if reversed {
                    vec![Ok(receipt()), Ok(permit())]
                } else {
                    vec![Ok(permit()), Ok(receipt())]
                };
                assert_eq!(
                    select_winner(&replies, |_, p, _| Ok(inspection(p)))
                        .unwrap()
                        .0,
                    usize::from(reversed)
                );
            }
            for replies in [
                vec![Ok(permit()), Ok(permit())],
                vec![Ok(permit()), Err(invalid("lost"))],
                vec![Ok(receipt()), Ok(receipt())],
                vec![Ok(permit()), Ok(vec![0])],
            ] {
                assert!(select_winner(&replies, |_, p, _| Ok(inspection(p))).is_err());
            }
            for field in [
                "transactionId",
                "eventId",
                "acceptedCount",
                "worldRoot",
                "confirmation",
            ] {
                assert!(select_winner(&[Ok(permit()), Ok(receipt())], |_, p, _| {
                    let mut v = inspection(p);
                    if !p {
                        v[field] = json!("wrong");
                    }
                    Ok(v)
                })
                .is_err());
            }
        }
        #[test]
        fn race_already_present_installed_receipt_is_never_a_second_permit() {
            for confirmation in ["installed", "replayed", "recoveredAfterUncertainResponse"] {
                let (index, _) = select_winner(&[Ok(permit()), Ok(receipt())], |_, p, _| {
                    let mut value = inspection(p);
                    if !p {
                        value["confirmation"] = json!(confirmation);
                    }
                    Ok(value)
                })
                .unwrap();
                assert_eq!(index, 0);
            }
        }
        #[test]
        fn race_private_fifo_refuses_without_waiting_for_writer() {
            use std::os::unix::ffi::OsStrExt;
            let root = super::super::tests::BoundFixture::new();
            let path = root.0.join("fifo");
            let cpath = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
            assert_eq!(unsafe { libc::mkfifo(cpath.as_ptr(), 0o600) }, 0);
            let start = Instant::now();
            assert!(private_read(&path).is_err());
            assert!(start.elapsed() < Duration::from_secs(1));
        }

        #[test]
        fn race_ambiguous_responses_preserve_marker_and_never_forward_a_permit() {
            for mode in ["lost", "multiple", "receipt-drift", "uncertain"] {
                let root = super::super::tests::BoundFixture::new();
                let attempt = root.0.join("attempt");
                DirBuilder::new().mode(0o700).create(&attempt).unwrap();
                let replies = match mode {
                    "lost" => vec![Ok(permit()), Err(invalid("lost response"))],
                    "multiple" => vec![Ok(permit()), Ok(permit())],
                    _ => vec![Ok(permit()), Ok(receipt())],
                };
                let result = submit_once(&attempt, "1", b"ingress", crate::host_operations::APPLICATION_DISPATCH_SUBMIT, b"submission", |_, _| {
                    select_winner(&replies, |_, p, _| {
                        let mut value = inspection(p);
                        if !p && mode == "receipt-drift" {
                            value["transactionId"] = json!("9");
                        }
                        if !p && mode == "uncertain" {
                            value["type"] = json!("uncertain");
                        }
                        Ok(value)
                    })?;
                    panic!("ambiguous race must never forward a permit")
                });
                assert!(matches!(result, Ok(Submit::Lost { .. })));
                assert!(attempt.join("submit-active.json").exists());
                assert!(attempt.join("submit-requested.json").exists());
                assert!(!attempt.join("op34-frame.bin").exists());
                // The undecided attempt is never resent; another call is not
                // fenced by it (dispatch_fence bounds the undecided count).
                assert!(
                    submit_once(&attempt, "1", b"ingress", crate::host_operations::APPLICATION_DISPATCH_SUBMIT, b"submission", |_, _| panic!(
                        "uncertain race must never resubmit its own attempt"
                    ))
                    .is_err()
                );
            }
        }

        #[test]
        fn race_no_go_and_mismatched_go_fail_before_submission() {
            let root = super::super::tests::BoundFixture::new();
            let attempt = root.0.join("attempt");
            DirBuilder::new().mode(0o700).create(&attempt).unwrap();
            let result = submit_once(&attempt, "1", b"ingress", crate::host_operations::APPLICATION_DISPATCH_SUBMIT, b"submission", |_, _| {
                await_go(
                    &attempt,
                    "nonce",
                    "hash",
                    Instant::now() + Duration::from_millis(1),
                )?;
                panic!("missing go must never submit")
            });
            assert!(matches!(result, Ok(Submit::Lost { ref error, .. })
                if error.kind() == io::ErrorKind::TimedOut));
            assert!(attempt.join("submit-active.json").exists());
            assert!(attempt.join("submit-requested.json").exists());
            write_new(&attempt,"race-go.json",br#"{"protocol":"mini-spk-dispatch-race-go-v1","nonceHex":"other","submissionSha256":"hash"}"#).unwrap();
            assert!(await_go(
                &attempt,
                "nonce",
                "hash",
                Instant::now() + Duration::from_secs(1)
            )
            .is_err());
        }
        #[test]
        fn race_claim_pins_exact_route_and_survives_reopen_without_rearming() {
            let nonce = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let path = PathBuf::from(std::env::var_os("HOME").unwrap())
                .join(format!(".spk-race-test-{}-{nonce}", std::process::id()));
            DirBuilder::new().mode(0o700).create(&path).unwrap();
            let root = super::super::tests::BoundFixture(path);
            let (custody, _) = super::super::tests::bound_fixture();
            let http = HttpProjection {
                method: "GET",
                path_and_query: "probe",
                ordered_headers: &[],
                body: &[],
                route: crate::dispatch_inspection::Route::Browser,
            };
            let trigger = json!({"protocol":"mini-spk-dispatch-race-trigger-v1","nonceHex":"a".repeat(64),
                "app":custody.app,"session":custody.session,"subject":custody.subject,
                "ticketResource":custody.ticket_resource,"sessionKind":"web","operationId":"1",
                "method":"GET","pathAndQuery":"probe","signedApiPath":null});
            write_new(
                &root.0,
                "dispatch-race-trigger.json",
                &serde_json::to_vec(&trigger).unwrap(),
            )
            .unwrap();
            let attempt = root.0.join("attempt");
            assert!(claim(&custody, &http, "2", &attempt).is_err());
            assert!(!root.0.join("dispatch-race-claimed.json").exists());
            assert!(claim(&custody, &http, "1", &attempt).unwrap().is_some());
            assert!(claim(&custody, &http, "1", &attempt).is_err());
            Journal::open(&root.0).unwrap();
            assert!(claim(&custody, &http, "1", &attempt).is_err());
            assert_eq!(
                fs::read(root.0.join("dispatch-race-claimed.json")).unwrap(),
                serde_json::to_vec(&trigger).unwrap()
            );
        }

        #[test]
        fn race_absent_trigger_preserves_normal_path_and_delivery_needs_selection() {
            let root = super::super::tests::BoundFixture::new();
            let (custody, _) = super::super::tests::bound_fixture();
            let http = HttpProjection {
                method: "GET",
                path_and_query: "probe",
                ordered_headers: &[],
                body: &[],
                route: crate::dispatch_inspection::Route::Browser,
            };
            assert!(claim(&custody, &http, "1", &root.0.join("attempt"))
                .unwrap()
                .is_none());
            delivery_event(&root.0, None).unwrap();
            assert!(!root.0.join("race-delivery-requested.json").exists());
            write_new(&root.0, "race-selection.json", b"{}").unwrap();
            delivery_event(&root.0, None).unwrap();
            delivery_event(&root.0, Some(true)).unwrap();
            let value: Value = serde_json::from_slice(
                &fs::read(root.0.join("race-delivery-result.json")).unwrap(),
            )
            .unwrap();
            assert_eq!(value["physicalDeliveries"], 1);
            assert!(delivery_event(&root.0, Some(true)).is_err());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::net::UnixListener;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn dir_with_mode(label: &str, mode: u32) -> PathBuf {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let path = std::env::temp_dir().join(format!("pinned-input-{label}-{}-{nonce}", std::process::id()));
        DirBuilder::new().mode(0o700).create(&path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(mode)).unwrap();
        path
    }

    #[test]
    fn read_pinned_input_reads_through_one_descriptor_and_refuses_symlinks_and_writable_files_by_name() {
        let dir = dir_with_mode("input", 0o710);
        let file = dir.join("pinned-config.json");
        fs::write(&file, b"{}").unwrap();
        fs::set_permissions(&file, fs::Permissions::from_mode(0o640)).unwrap();
        assert_eq!(read_pinned_input(&file, 64).unwrap(), b"{}");
        let link = dir.join("link.json");
        std::os::unix::fs::symlink(&file, &link).unwrap();
        let error = read_pinned_input(&link, 64).unwrap_err();
        // O_NOFOLLOW refuses the open itself (ELOOP) and the refusal carries the path.
        assert!(error.to_string().contains("link.json"), "{error}");
        fs::set_permissions(&file, fs::Permissions::from_mode(0o660)).unwrap();
        let error = read_pinned_input(&file, 64).unwrap_err().to_string();
        assert!(error.contains("pinned input") && error.contains("writable by group or others"), "{error}");
        fs::set_permissions(&file, fs::Permissions::from_mode(0o640)).unwrap();
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o770)).unwrap();
        let error = read_pinned_input(&file, 64).unwrap_err().to_string();
        assert!(error.contains("pinned input directory") && error.contains("writable by group or others"), "{error}");
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o710)).unwrap();
        fs::remove_file(&link).unwrap();
        fs::remove_file(&file).unwrap();
        fs::remove_dir(&dir).unwrap();
    }

    #[test]
    fn verified_config_hashes_once_per_inode_and_rehashes_on_any_change() {
        let dir = dir_with_mode("verified-config", 0o710);
        let file = dir.join("config.json");
        fs::write(&file, b"{\"a\":1}").unwrap();
        fs::set_permissions(&file, fs::Permissions::from_mode(0o640)).unwrap();
        let sha = hex(&Sha256::digest(b"{\"a\":1}"));
        assert_eq!(verified_config(&file, &sha).unwrap(), b"{\"a\":1}");
        assert_eq!(verified_config(&file, &sha).unwrap(), b"{\"a\":1}");
        // A same-size in-place edit moves ctime: the entry is dropped and the new bytes drift the pin.
        std::thread::sleep(Duration::from_millis(30));
        fs::write(&file, b"{\"a\":2}").unwrap();
        let error = verified_config(&file, &sha).unwrap_err().to_string();
        assert!(error.contains("config SHA-256 drift"), "{error}");
        // Restoring the pinned bytes verifies again; widening the mode is refused by name.
        std::thread::sleep(Duration::from_millis(30));
        fs::write(&file, b"{\"a\":1}").unwrap();
        assert_eq!(verified_config(&file, &sha).unwrap(), b"{\"a\":1}");
        std::thread::sleep(Duration::from_millis(30));
        fs::set_permissions(&file, fs::Permissions::from_mode(0o660)).unwrap();
        let error = verified_config(&file, &sha).unwrap_err().to_string();
        assert!(error.contains("writable by group or others"), "{error}");
        fs::remove_file(&file).unwrap();
        fs::remove_dir(&dir).unwrap();
    }

    #[test]
    fn pinned_input_dir_accepts_a_group_readable_parent_and_refuses_a_writable_one_by_name() {
        let hosted = dir_with_mode("hosted", 0o710);
        pinned_input_dir(&hosted).unwrap();
        for (mode, label) in [(0o730, "group-write"), (0o777, "world-write"), (0o702, "other-write")] {
            let bad = dir_with_mode(label, mode);
            let error = pinned_input_dir(&bad).unwrap_err().to_string();
            assert!(
                error.contains("pinned input directory") && error.contains(&bad.display().to_string()) && error.contains("writable by group or others"),
                "{label}: {error}"
            );
            fs::remove_dir(&bad).unwrap();
        }
        let link = hosted.with_extension("link");
        std::os::unix::fs::symlink(&hosted, &link).unwrap();
        let error = pinned_input_dir(&link).unwrap_err().to_string();
        assert!(error.contains("not a directory"), "{error}");
        fs::remove_file(&link).unwrap();
        fs::remove_dir(&hosted).unwrap();
    }

    #[test]
    fn pinned_input_dir_does_not_relax_the_private_attempt_directory_rule() {
        let hosted = dir_with_mode("attempt-parent", 0o710);
        let error = private_dir(&hosted).unwrap_err().to_string();
        assert_eq!(error, "native attempt directory is not owner-private");
        fs::remove_dir(&hosted).unwrap();
    }

    pub(super) struct BoundFixture(pub(super) PathBuf);
    impl BoundFixture {
        pub(super) fn new() -> Self {
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let root =
                std::env::temp_dir().join(format!("bound-dispatch-{}-{nonce}", std::process::id()));
            DirBuilder::new().mode(0o700).create(&root).unwrap();
            Self(root)
        }
        fn attempt(&self, name: &str) -> PathBuf {
            let path = self.0.join(name);
            DirBuilder::new().mode(0o700).create(&path).unwrap();
            path
        }
    }
    impl Drop for BoundFixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
    pub(super) fn bound_fixture() -> (FixedAuthoring, ContinuityBinding) {
        let custody = serde_json::from_value(json!({
            "protocol":"mini-spk-human-dispatch-custody-v1","app":"17","subject":"8","session":"27","sessionKind":"web",
            "issueIndex":"1","ticketResource":"37","packageManifest":"40","snapshotManifest":"41","sessionObserveCapability":"42",
            "manifestObserveCapability":"43","enrollmentObserveCapability":"44","signers":[{"role":"0","index":"0","keyId":"9","keyEpoch":"0","publicKeyHex":"00".repeat(32),"seedPath":"/unused/seed"}]
        })).unwrap();
        let binding = ContinuityBinding {
            domain: "1".into(),
            semantics: "2".into(),
            app: "17".into(),
            app_generation: "4".into(),
            session: "27".into(),
            session_generation: "3".into(),
            subject: "8".into(),
            ticket_resource: "37".into(),
            session_fingerprint: [255; 32],
        };
        (custody, binding)
    }
    fn no_record_frame() -> Vec<u8> {
        let mut frame = Vec::new();
        frame.extend_from_slice(&((NO_RECORD_REFUSAL.len() + 1) as u32).to_le_bytes());
        frame.push(ROUTE_BOUND_DISPATCH_OPCODE);
        frame.extend_from_slice(NO_RECORD_REFUSAL);
        frame
    }
    /// The 159 MB Host image is hashed once per inode, not before every
    /// helper and socket call; any change to the named file re-hashes and a
    /// changed image refuses. Helpers run the verified descriptor itself.
    #[test]
    fn host_image_hashed_once_per_inode_and_rehashed_on_any_change() {
        let root = BoundFixture::new();
        let host = root.0.join("host-image");
        fs::copy("/usr/bin/true", &host).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o755)).unwrap();
        let sha = hex(&Sha256::digest(fs::read(&host).unwrap()));
        let (image, hashed) = verified_image_hashing(&host, &sha).unwrap();
        assert!(hashed);
        assert!(Command::new(image.path()).status().unwrap().success());
        let (_, hashed) = verified_image_hashing(&host, &sha).unwrap();
        assert!(!hashed);
        // Same bytes under a new inode: verified again, then cached again.
        let replacement = root.0.join("host-image.new");
        fs::copy("/usr/bin/true", &replacement).unwrap();
        fs::set_permissions(&replacement, fs::Permissions::from_mode(0o755)).unwrap();
        fs::rename(&replacement, &host).unwrap();
        let (_, hashed) = verified_image_hashing(&host, &sha).unwrap();
        assert!(hashed);
        let (_, hashed) = verified_image_hashing(&host, &sha).unwrap();
        assert!(!hashed);
        // An in-place change moves size/mtime/ctime and refuses on re-hash.
        OpenOptions::new()
            .append(true)
            .open(&host)
            .unwrap()
            .write_all(b"x")
            .unwrap();
        assert!(verified_image_hashing(&host, &sha).is_err());
        // The image held by an earlier caller still runs the verified bytes.
        assert!(Command::new(image.path()).status().unwrap().success());
        let link = root.0.join("host-link");
        std::os::unix::fs::symlink(&host, &link).unwrap();
        assert!(verified_image_hashing(&link, &sha).is_err());
        fs::set_permissions(&host, fs::Permissions::from_mode(0o777)).unwrap();
        assert!(verified_image_hashing(&host, &sha).is_err());
    }

    #[test]
    fn bound_dispatch_private_transport_accepts_only_defined_cross_opcode_replies() {
        let root = BoundFixture::new();
        let host = root.0.join("host");
        fs::copy("/usr/bin/true", &host).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o755)).unwrap();
        let config = root.0.join("config.json");
        fs::write(&config, b"{}").unwrap();
        let socket = root.0.join("operator.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o600)).unwrap();
        let operator = PrivateOperator {
            host: host.clone(),
            config: config.clone(),
            socket,
            host_sha256: hex(&Sha256::digest(fs::read(host).unwrap())),
            config_sha256: hex(&Sha256::digest(b"{}")),
        };
        let frame = |opcode: u8, payload: &[u8]| {
            let mut frame = Vec::new();
            frame.extend_from_slice(&((payload.len() + 1) as u32).to_le_bytes());
            frame.push(opcode);
            frame.extend_from_slice(payload);
            frame
        };
        let cases = vec![
            (34, no_record_frame(), true),
            (
                ROUTE_BOUND_DISPATCH_OPCODE,
                frame(crate::host_operations::APPLICATION_DISPATCH_SUBMIT, b"source committed permit"),
                true,
            ),
            (
                34,
                frame(ROUTE_BOUND_DISPATCH_OPCODE, b"not a no-record refusal"),
                false,
            ),
            (36, no_record_frame(), false),
            (
                ROUTE_BOUND_DISPATCH_OPCODE,
                frame(crate::host_operations::APPLICATION_DISPATCH_PLAN, b"wrong operation"),
                false,
            ),
        ];
        let server_cases = cases.clone();
        let server = std::thread::spawn(move || {
            for (expected, response, _) in server_cases {
                let (mut stream, _) = listener.accept().unwrap();
                let mut prefix = [0; 4];
                stream.read_exact(&mut prefix).unwrap();
                let mut request = vec![0; u32::from_le_bytes(prefix) as usize];
                stream.read_exact(&mut request).unwrap();
                let config_len = u32::from_le_bytes(request[1..5].try_into().unwrap()) as usize;
                assert_eq!(request[5 + config_len + 32], expected);
                stream.write_all(&response).unwrap();
            }
        });
        for (opcode, response, accepted) in cases {
            let actual = operator.invoke(opcode, b"request");
            if accepted {
                assert_eq!(actual.unwrap(), response);
            } else {
                assert_eq!(
                    actual.unwrap_err().to_string(),
                    "Mini operator reply opcode mismatch"
                );
            }
        }
        server.join().unwrap();
    }

    #[test]
    fn bound_dispatch_authoring_preserves_exact_binding_and_ingress() {
        let (_, binding) = bound_fixture();
        assert_eq!(
            route_bound_dispatch_json(&binding, &[0, 1, 254, 255]),
            json!({
                "domain":"1","semantics":"2","app":"17","appGeneration":"4","session":"27","sessionGeneration":"3",
                "subject":"8","ticketResource":"37",
                "sessionFingerprint":"115792089237316195423570985008687907853269984665640564039457584007913129639935",
                "ingressHex":"0001feff"
            })
        );
        for bytes in [[0; 32], [255; 32], std::array::from_fn(|n| n as u8)] {
            assert_eq!(
                crate::stream_continuity::digest(&digest_decimal(&bytes)).unwrap(),
                bytes
            );
        }
        assert_eq!(digest_decimal(&[0; 32]), "0");
    }
    #[test]
    fn bound_dispatch_wrong_local_custody_or_namespace_never_enters_native_pipeline() {
        let root = BoundFixture::new();
        let (custody, binding) = bound_fixture();
        let namespace = ("1".into(), "2".into());
        let operator = PrivateOperator {
            host: root.0.join("absent-host"),
            config: root.0.join("absent-config"),
            socket: root.0.join("absent-socket"),
            host_sha256: "00".repeat(32),
            config_sha256: "00".repeat(32),
        };
        let http = HttpProjection {
            method: "GET",
            path_and_query: "",
            ordered_headers: &[],
            body: &[],
            route: crate::dispatch_inspection::Route::Browser,
        };
        for field in ["domain", "semantics", "app", "session", "subject", "ticket"] {
            let mut wrong = binding.clone();
            match field {
                "domain" => wrong.domain = "9".into(),
                "semantics" => wrong.semantics = "9".into(),
                "app" => wrong.app = "9".into(),
                "session" => wrong.session = "9".into(),
                "subject" => wrong.subject = "9".into(),
                _ => wrong.ticket_resource = "9".into(),
            }
            let attempt = root.0.join(field);
            let error = author_and_submit(
                &operator,
                &custody,
                &http,
                "1",
                &attempt,
                Some(&wrong),
                &namespace,
            )
            .err()
            .expect("local mismatch must refuse");
            assert_eq!(
                error.to_string(),
                "fixed route binding differs from custody or pinned namespace"
            );
            assert!(!attempt.exists());
            assert!(!root.0.join("native-dispatch-active.json").exists());
        }
        validate_route_binding(&custody, Some(&binding), &namespace).unwrap();
    }
    #[test]
    fn bound_dispatch_definite_revoked_a_refusal_releases_b_without_replaying_a() {
        for opcode in [34, ROUTE_BOUND_DISPATCH_OPCODE] {
            let root = BoundFixture::new();
            let a = root.attempt("a");
            let refusal = no_record_frame();
            let result = submit_once(
                &a,
                "1",
                b"a ingress",
                opcode,
                b"a submission",
                |op, payload| {
                    assert_eq!(op, opcode);
                    assert_eq!(payload, b"a submission");
                    Ok(refusal.clone())
                },
            )
            .unwrap();
            let Submit::NoRecord(outcome) = result else {
                panic!("the exact no-record frame settles the call");
            };
            assert_eq!(outcome.status, crate::dispatch_fence::Status::Refused);
            assert!(!a.join("submit-active.json").exists());
            assert!(a.join("submit-requested.json").exists());
            assert!(a.join("resolution.json").exists());
            assert!(submit_once(
                &a,
                "1",
                b"a ingress",
                opcode,
                b"a submission",
                |_, _| panic!("same attempt must never be replayed")
            )
            .is_err());
            let b = root.attempt("b");
            let Submit::Frame(submitted) =
                submit_once(&b, "2", b"b ingress", crate::host_operations::APPLICATION_DISPATCH_SUBMIT, b"b submission", |op, bytes| {
                    assert_eq!(op, 34);
                    assert_eq!(bytes, b"b submission");
                    Ok(b"private committed response".to_vec())
                })
                .unwrap()
            else {
                panic!("a reply frame is retained for decoding");
            };
            assert_eq!(submitted.frame, b"private committed response");
            assert_eq!(submitted.active_marker, b.join("submit-active.json"));
            settle_committed(&submitted.active_marker, &submitted.active_bytes, "delivered").unwrap();
            assert!(!submitted.active_marker.exists());
        }
    }
    #[test]
    fn bound_dispatch_historical_confirmed_receipt_never_delivers_and_fences_only_its_call() {
        // NativeHostCodec.outcomeCodec: confirmed (.inl), replayed (.inr false),
        // then receipt(transactionId=11,eventId=12,acceptedCount=13,worldRoot=14).
        // Each positive Nat/Digest is one base-255 digit followed by 255.
        let mut outcome = b"DREGG/NATIVE-HOST/OUTCOME/v8".to_vec();
        outcome.extend_from_slice(&[0, 1, 0, 11, 255, 12, 255, 13, 255, 14, 255]);
        let mut historical = ((outcome.len() + 1) as u32).to_le_bytes().to_vec();
        historical.push(34);
        historical.extend_from_slice(&outcome);
        assert!(matches!(
            parse_op34_response(&historical).unwrap(),
            Op34Reply::OutcomeBytes(bytes) if bytes == outcome
        ));
        for opcode in [34, ROUTE_BOUND_DISPATCH_OPCODE] {
            let root = BoundFixture::new();
            let a = root.attempt("a");
            let Submit::Frame(submitted) =
                submit_once(&a, "1", b"a ingress", opcode, b"a submission", |_, _| {
                    Ok(historical.clone())
                })
                .unwrap()
            else {
                panic!("an outcome frame is retained for decoding");
            };
            // This is the production gate before writing/inspecting a permit
            // or constructing the opaque CommittedDispatch used for delivery.
            assert_eq!(
                submitted.committed_payload().unwrap_err().to_string(),
                "Mini op34 did not commit a delivery permit"
            );
            assert_eq!(
                fs::read(&submitted.active_marker).unwrap(),
                submitted.active_bytes
            );
            assert_eq!(
                fs::read(a.join(format!("op{opcode}-frame.bin"))).unwrap(),
                historical
            );
            assert!(a.join("submit-requested.json").exists());
            assert!(!a.join("committed-payload.bin").exists());
            assert!(!a.join("inspection.json").exists());
            assert!(
                submit_once(&a, "1", b"a ingress", opcode, b"a submission", |_, _| {
                    panic!("historical attempt must never be replayed")
                })
                .is_err()
            );
            // B is a different signed call: A's undecided marker is A's alone.
            let b = root.attempt("b");
            assert!(matches!(
                submit_once(&b, "2", b"b ingress", crate::host_operations::APPLICATION_DISPATCH_SUBMIT, b"b submission", |_, _| Ok(
                    historical.clone()
                ))
                .unwrap(),
                Submit::Frame(_)
            ));
            assert!(!root.0.join("native-dispatch-active.json").exists());
            assert_eq!(
                fs::read(&submitted.active_marker).unwrap(),
                submitted.active_bytes
            );
        }
    }

    #[test]
    fn bound_dispatch_uncertain_or_malformed_reply_keeps_its_call_undecided_only() {
        let valid = no_record_frame();
        let mut wrong_tag = valid.clone();
        wrong_tag[4] = 34;
        let mut trailing = valid.clone();
        trailing.push(0);
        let mut truncated = valid.clone();
        truncated.pop();
        let mut wrong_payload = valid.clone();
        *wrong_payload.last_mut().unwrap() ^= 1;
        for response in [
            wrong_tag,
            trailing,
            truncated,
            wrong_payload,
            b"generic source outcome".to_vec(),
        ] {
            let root = BoundFixture::new();
            let a = root.attempt("a");
            let Submit::Frame(submitted) = submit_once(
                &a,
                "1",
                b"ingress",
                ROUTE_BOUND_DISPATCH_OPCODE,
                b"request",
                |_, _| Ok(response),
            )
            .unwrap() else {
                panic!("a non-exact frame is never a settlement");
            };
            assert!(submitted.active_marker.exists());
            assert!(submitted.committed_payload().is_err());
            let b = root.attempt("b");
            assert!(matches!(
                submit_once(&b, "2", b"ingress", crate::host_operations::APPLICATION_DISPATCH_SUBMIT, b"request", |_, _| Ok(valid.clone()))
                    .unwrap(),
                Submit::NoRecord(_)
            ));
            assert!(submitted.active_marker.exists());
        }
        let root = BoundFixture::new();
        let a = root.attempt("a");
        assert!(matches!(
            submit_once(
                &a,
                "1",
                b"ingress",
                ROUTE_BOUND_DISPATCH_OPCODE,
                b"request",
                |_, _| Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "lost response"
                ))
            )
            .unwrap(),
            Submit::Lost { .. }
        ));
        assert!(a.join("submit-active.json").exists());
        let root = BoundFixture::new();
        let a = root.attempt("a");
        assert!(submit_once(
            &a,
            "1",
            b"ingress",
            ROUTE_BOUND_DISPATCH_OPCODE,
            b"request",
            |_, _| {
                fs::write(a.join("submit-active.json"), b"changed").unwrap();
                Ok(valid)
            }
        )
        .is_err());
        assert_eq!(fs::read(a.join("submit-active.json")).unwrap(), b"changed");
    }

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
            operator.invoke(crate::host_operations::APPLICATION_DISPATCH_PLAN, b"source request").unwrap(),
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
        assert!(operator.invoke(crate::host_operations::APPLICATION_DISPATCH_PLAN, b"source request").is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn native_submit_marker_is_create_new_and_blocks_a_second_attempt() {
        let root = BoundFixture::new();
        let attempt = root.attempt("a");
        crate::dispatch_fence::arm(&attempt, b"first").unwrap();
        assert!(crate::dispatch_fence::arm(&attempt, b"second").is_err());
        assert_eq!(fs::read(attempt.join("submit-active.json")).unwrap(), b"first");
        assert_eq!(fs::read(attempt.join("submit-requested.json")).unwrap(), b"first");
    }
}
