// Operator-owned, per-task Mini socket entrance. The native host remains in its
// private 0700 directory; this process grants exactly one other UID access to
// a separate socket and forwards bounded frames without retrying requests.
#[cfg(not(target_os = "linux"))]
compile_error!("host-frontend requires Linux SO_PEERCRED and POSIX ACLs");

use std::env;
use std::fs::{self, File, OpenOptions, Permissions};
use std::io::{self, Read, Write};
use std::mem::size_of;
use std::os::fd::AsRawFd;
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

const MAX_CONFIG: usize = 65_536;
const HOST_MAX_FRAME: usize = 12_102_760;
const MAX_REQUEST_FRAME: usize = HOST_MAX_FRAME + 5 + MAX_CONFIG + 32;
// Match the native client and broker's per-operation reply cap. Worker wall time
// covers the whole agent run and is a separate budget.
const BACKEND_REPLY_SECONDS: u64 = 600;

unsafe extern "C" {
    fn geteuid() -> u32;
    fn getsockopt(fd: i32, level: i32, option: i32, value: *mut UCred, length: *mut u32) -> i32;
    fn flock(fd: i32, operation: i32) -> i32;
    fn poll(fds: *mut PollFd, count: usize, timeout: i32) -> i32;
}

#[repr(C)]
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}

#[repr(C)]
struct UCred {
    pid: i32,
    uid: u32,
    gid: u32,
}

fn uid() -> u32 {
    unsafe { geteuid() }
}

fn peer_uid(stream: &UnixStream) -> io::Result<u32> {
    let mut cred = UCred {
        pid: 0,
        uid: 0,
        gid: 0,
    };
    let mut size = size_of::<UCred>() as u32;
    let result = unsafe { getsockopt(stream.as_raw_fd(), 1, 17, &mut cred, &mut size) };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    if size as usize != size_of::<UCred>() {
        return Err(io::Error::other("unexpected SO_PEERCRED length"));
    }
    Ok(cred.uid)
}

fn fail(message: impl Into<String>) -> io::Error {
    io::Error::other(message.into())
}

fn canonical_existing(path: &Path) -> io::Result<fs::Metadata> {
    if !path.is_absolute()
        || fs::symlink_metadata(path)?.file_type().is_symlink()
        || fs::canonicalize(path)? != path
    {
        return Err(fail(format!(
            "path must be absolute, canonical and not a symlink: {}",
            path.display()
        )));
    }
    fs::metadata(path)
}

fn owned_private_dir(path: &Path, owner: u32) -> io::Result<()> {
    let metadata = canonical_existing(path)?;
    if !metadata.is_dir() || metadata.uid() != owner || metadata.mode() & 0o027 != 0 {
        return Err(fail(format!(
            "directory must be owned and deny group-write/world access: {}",
            path.display()
        )));
    }
    Ok(())
}

fn acl(path: &Path, rule: &str) -> io::Result<()> {
    let output = Command::new("/usr/bin/setfacl")
        .args(["-m", rule])
        .arg(path)
        .output()?;
    if !output.status.success() {
        return Err(fail(format!(
            "setfacl failed for {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    Ok(())
}

fn reset_acl(path: &Path, mode: u32, directory: bool) -> io::Result<()> {
    if directory {
        let output = Command::new("/usr/bin/setfacl")
            .arg("-k")
            .arg(path)
            .output()?;
        if !output.status.success() {
            return Err(fail(format!(
                "cannot remove default ACL on {}: {}",
                path.display(),
                String::from_utf8_lossy(&output.stderr).trim()
            )));
        }
    }
    let output = Command::new("/usr/bin/setfacl")
        .arg("-b")
        .arg(path)
        .output()?;
    if !output.status.success() {
        return Err(fail(format!(
            "cannot reset ACL on {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    fs::set_permissions(path, Permissions::from_mode(mode))
}

fn read_config(path: &Path) -> io::Result<Vec<u8>> {
    let file = File::open(path)?;
    let mut bytes = Vec::new();
    file.take((MAX_CONFIG + 1) as u64).read_to_end(&mut bytes)?;
    if bytes.is_empty() || bytes.len() > MAX_CONFIG {
        return Err(fail(
            "host config is empty or exceeds the native socket pin bound",
        ));
    }
    Ok(bytes)
}

fn service_lock(path: &Path, owner: u32) -> io::Result<File> {
    let file = match OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
    {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            OpenOptions::new().write(true).open(path)?
        }
        Err(error) => return Err(error),
    };
    let named = fs::symlink_metadata(path)?;
    let opened = file.metadata()?;
    if !named.file_type().is_file()
        || named.uid() != owner
        || named.mode() & 0o077 != 0
        || (named.dev(), named.ino()) != (opened.dev(), opened.ino())
    {
        return Err(fail("frontend lock is not an owner-private regular file"));
    }
    if unsafe { flock(file.as_raw_fd(), 2 | 4) } != 0 {
        return Err(fail(format!(
            "another frontend holds the service lock: {}",
            io::Error::last_os_error()
        )));
    }
    Ok(file)
}

fn clear_stale_socket(path: &Path, owner: u32) -> io::Result<()> {
    let old = match fs::symlink_metadata(path) {
        Ok(old) => old,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    };
    if !old.file_type().is_socket() || old.uid() != owner {
        return Err(fail("frontend socket path is not an owned socket"));
    }
    match UnixStream::connect(path) {
        Ok(_) => return Err(fail("another frontend still listens on socket")),
        Err(error) if error.kind() == io::ErrorKind::ConnectionRefused => {}
        Err(error) => return Err(fail(format!("cannot prove frontend socket stale: {error}"))),
    }
    let now = fs::symlink_metadata(path)?;
    if !now.file_type().is_socket() || (now.dev(), now.ino()) != (old.dev(), old.ino()) {
        return Err(fail("frontend socket changed during stale recovery"));
    }
    fs::remove_file(path)
}

struct DeadlineRead<'a> {
    stream: &'a mut UnixStream,
    deadline: Instant,
}

impl Read for DeadlineRead<'_> {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        loop {
            wait_ready(self.stream.as_raw_fd(), 1, self.deadline)?;
            match self.stream.read(bytes) {
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => continue,
                result => return result,
            }
        }
    }
}

struct DeadlineWrite<'a> {
    stream: &'a mut UnixStream,
    deadline: Instant,
}

impl Write for DeadlineWrite<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        loop {
            wait_ready(self.stream.as_raw_fd(), 4, self.deadline)?;
            match self.stream.write(bytes) {
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => continue,
                result => return result,
            }
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        self.stream.flush()
    }
}

fn wait_ready(fd: i32, events: i16, deadline: Instant) -> io::Result<()> {
    loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "whole-frame deadline",
            ));
        }
        let mut item = PollFd {
            fd,
            events,
            revents: 0,
        };
        let timeout = remaining.as_millis().min(i32::MAX as u128) as i32;
        let result = unsafe { poll(&mut item, 1, timeout.max(1)) };
        if result > 0 {
            return Ok(());
        }
        if result < 0 {
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(error);
            }
        }
    }
}

fn read_frame<R: Read>(stream: &mut R, max: usize) -> io::Result<Option<Vec<u8>>> {
    let mut prefix = [0u8; 4];
    if stream.read(&mut prefix[..1])? == 0 {
        return Ok(None);
    }
    stream.read_exact(&mut prefix[1..])?;
    let len = u32::from_le_bytes(prefix) as usize;
    if len == 0 || len > max {
        return Err(fail("invalid or oversized Mini socket frame"));
    }
    let mut frame = Vec::with_capacity(4 + len);
    frame.extend_from_slice(&prefix);
    frame.resize(4 + len, 0);
    stream.read_exact(&mut frame[4..])?;
    Ok(Some(frame))
}

fn pinned_v2(request: &[u8], config: &[u8], host_sha256: &[u8; 32]) -> bool {
    if request.len() < 4 + 5 + 32 + 1 || request[4] != 2 {
        return false;
    }
    let config_len = u32::from_le_bytes(request[5..9].try_into().unwrap()) as usize;
    let end = match 9usize.checked_add(config_len) {
        Some(end) => end,
        None => return false,
    };
    let operation = request.get(end + 32).copied();
    let allowed = match operation {
        Some(0..=11) => true,
        Some(17) => {
            let Some(pair) = request.get(end + 33..) else {
                return false;
            };
            if pair.len() < 6 {
                return false;
            }
            let call_length = u32::from_le_bytes(pair[..4].try_into().unwrap()) as usize;
            call_length > 0 && call_length < pair.len() - 4 && pair.len() - 4 - call_length <= 1024
        }
        Some(19) => {
            let Some(payload) = request.get(end + 33..) else {
                return false;
            };
            if payload.len() < 10 {
                return false;
            }
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
        _ => false,
    };
    allowed
        && request.get(9..end) == Some(config)
        && request.get(end..end + 32) == Some(host_sha256.as_slice())
        && request.len() > end + 32
}

fn relay(
    mut client: UnixStream,
    private_socket: &Path,
    config: &[u8],
    host_sha256: &[u8; 32],
) -> io::Result<()> {
    client.set_nonblocking(true)?;
    let Some(request) = read_frame(
        &mut DeadlineRead {
            stream: &mut client,
            deadline: Instant::now() + Duration::from_secs(10),
        },
        MAX_REQUEST_FRAME,
    )?
    else {
        return Ok(());
    };
    if !pinned_v2(&request, config, host_sha256) {
        let refusal = b"\xfefrontend requires exact pinned v2 Mini envelope";
        let mut writer = DeadlineWrite {
            stream: &mut client,
            deadline: Instant::now() + Duration::from_secs(10),
        };
        writer.write_all(&(refusal.len() as u32).to_le_bytes())?;
        writer.write_all(refusal)?;
        return Ok(());
    }
    let mut backend = UnixStream::connect(private_socket)?;
    backend.set_nonblocking(true)?;
    DeadlineWrite {
        stream: &mut backend,
        deadline: Instant::now() + Duration::from_secs(10),
    }
    .write_all(&request)?;
    let reply = read_frame(
        &mut DeadlineRead {
            stream: &mut backend,
            deadline: Instant::now() + Duration::from_secs(BACKEND_REPLY_SECONDS),
        },
        HOST_MAX_FRAME,
    )?
    .ok_or_else(|| fail("private Mini host closed without a reply; status uncertain"))?;
    DeadlineWrite {
        stream: &mut client,
        deadline: Instant::now() + Duration::from_secs(10),
    }
    .write_all(&reply)
}

fn run(
    private_socket: PathBuf,
    public_socket: PathBuf,
    public_config: PathBuf,
    task_uid: u32,
    host_sha256: [u8; 32],
) -> io::Result<()> {
    let owner = uid();
    if task_uid == 0 || task_uid == owner {
        return Err(fail("task UID must be a distinct non-root Unix account"));
    }
    let private_dir = private_socket
        .parent()
        .ok_or_else(|| fail("private socket has no parent"))?;
    let public_dir = public_socket
        .parent()
        .ok_or_else(|| fail("public socket has no parent"))?;
    if private_dir == public_dir
        || public_config.parent() != Some(public_dir)
        || private_socket == public_socket
        || public_config == public_socket
        || public_config
            .file_name()
            .is_some_and(|name| name == "host.lock")
        || public_socket
            .file_name()
            .is_some_and(|name| name == "host.lock")
    {
        return Err(fail(
            "frontend socket and config must share a separate dedicated directory",
        ));
    }
    owned_private_dir(private_dir, owner)?;
    owned_private_dir(public_dir, owner)?;
    if canonical_existing(private_dir)?.mode() & 0o077 != 0 {
        return Err(fail("private Mini socket directory must be mode 0700"));
    }
    let lock_path = public_dir.join("host.lock");
    let _lock = service_lock(&lock_path, owner)?;
    for entry in fs::read_dir(public_dir)? {
        let path = entry?.path();
        if path != public_config && path != public_socket && path != lock_path {
            return Err(fail(
                "frontend directory must contain only its config and socket",
            ));
        }
    }
    let private_metadata = canonical_existing(&private_socket)?;
    if !private_metadata.file_type().is_socket()
        || private_metadata.uid() != owner
        || private_metadata.mode() & 0o077 != 0
    {
        return Err(fail("private Mini socket must be owned mode 0600"));
    }
    let public_metadata = canonical_existing(&public_config)?;
    if !public_metadata.is_file()
        || public_metadata.uid() != owner
        || public_metadata.mode() & 0o022 != 0
    {
        return Err(fail(
            "public host config must be an owned nonwritable regular file",
        ));
    }
    let pinned_config = private_socket.with_extension("config");
    let pinned_metadata = canonical_existing(&pinned_config)?;
    if !pinned_metadata.is_file()
        || pinned_metadata.uid() != owner
        || pinned_metadata.mode() & 0o077 != 0
        || (pinned_metadata.dev(), pinned_metadata.ino())
            == (public_metadata.dev(), public_metadata.ino())
        || public_metadata.nlink() != 1
    {
        return Err(fail(
            "private host pin is not private, or public config is hard-linked",
        ));
    }
    let config_bytes = read_config(&public_config)?;
    if config_bytes != read_config(&pinned_config)? {
        return Err(fail(
            "public host config is not byte-identical to the private host pin",
        ));
    }
    reset_acl(public_dir, 0o700, true)?;
    reset_acl(&public_config, 0o600, false)?;
    acl(public_dir, &format!("u:{task_uid}:--x"))?;
    acl(&public_config, &format!("u:{task_uid}:r--"))?;
    clear_stale_socket(&public_socket, owner)?;
    let listener = UnixListener::bind(&public_socket)?;
    struct SocketGuard(PathBuf, u64, u64);
    impl Drop for SocketGuard {
        fn drop(&mut self) {
            if let Ok(metadata) = fs::symlink_metadata(&self.0) {
                if metadata.file_type().is_socket()
                    && (metadata.dev(), metadata.ino()) == (self.1, self.2)
                {
                    let _ = fs::remove_file(&self.0);
                }
            }
        }
    }
    let socket_metadata = fs::symlink_metadata(&public_socket)?;
    let _guard = SocketGuard(
        public_socket.clone(),
        socket_metadata.dev(),
        socket_metadata.ino(),
    );
    fs::set_permissions(&public_socket, Permissions::from_mode(0o600))?;
    acl(&public_socket, &format!("u:{task_uid}:rw-"))?;
    eprintln!(
        "mini host frontend: {} permits UID {}",
        public_socket.display(),
        task_uid
    );
    for accepted in listener.incoming() {
        let client = accepted?;
        match peer_uid(&client) {
            Ok(found) if found == task_uid => {
                if let Err(error) = relay(client, &private_socket, &config_bytes, &host_sha256) {
                    eprintln!("mini host frontend: request failed without retry: {error}");
                }
            }
            Ok(found) => eprintln!("mini host frontend: refused peer UID {found}"),
            Err(error) => eprintln!("mini host frontend: cannot inspect peer UID: {error}"),
        }
    }
    Ok(())
}

fn main() {
    let args: Vec<_> = env::args_os().collect();
    if args.len() != 6 {
        eprintln!(
            "usage: host-frontend PRIVATE_HOST_SOCKET PUBLIC_TASK_SOCKET PUBLIC_CONFIG TASK_UID HOST_SHA256"
        );
        std::process::exit(64);
    }
    let task_uid = match args[4].to_string_lossy().parse::<u32>() {
        Ok(uid) => uid,
        Err(_) => {
            eprintln!("host-frontend: invalid task UID");
            std::process::exit(64);
        }
    };
    let hash_hex = args[5].to_string_lossy();
    if hash_hex.len() != 64
        || !hash_hex
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        eprintln!("host-frontend: HOST_SHA256 must be 64 lowercase hex digits");
        std::process::exit(64);
    }
    let mut host_sha256 = [0u8; 32];
    for (index, byte) in host_sha256.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&hash_hex[index * 2..index * 2 + 2], 16).unwrap();
    }
    if let Err(error) = run(
        PathBuf::from(&args[1]),
        PathBuf::from(&args[2]),
        PathBuf::from(&args[3]),
        task_uid,
        host_sha256,
    ) {
        eprintln!("host-frontend: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::pinned_v2;

    fn envelope(operation: u8, payload: &[u8]) -> Vec<u8> {
        let config = b"config";
        let mut frame = Vec::new();
        frame.extend_from_slice(&[0; 4]);
        frame.push(2);
        frame.extend_from_slice(&(config.len() as u32).to_le_bytes());
        frame.extend_from_slice(config);
        frame.extend_from_slice(&[7; 32]);
        frame.push(operation);
        frame.extend_from_slice(payload);
        let length = (frame.len() - 4) as u32;
        frame[..4].copy_from_slice(&length.to_le_bytes());
        frame
    }

    #[test]
    fn pins_config_host_image_and_version() {
        let mut frame = envelope(0, &[]);
        assert!(pinned_v2(&frame, b"config", &[7; 32]));
        assert!(!pinned_v2(&frame, b"other", &[7; 32]));
        assert!(!pinned_v2(&frame, b"config", &[8; 32]));
        frame[4] = 1;
        assert!(!pinned_v2(&frame, b"config", &[7; 32]));
    }

    #[test]
    fn permits_only_grain_and_bounded_read_only_operator_shapes() {
        for opcode in 0..=11 {
            assert!(pinned_v2(&envelope(opcode, &[]), b"config", &[7; 32]));
        }
        for opcode in 12..=16 {
            assert!(!pinned_v2(&envelope(opcode, &[]), b"config", &[7; 32]));
        }
        assert!(!pinned_v2(&envelope(18, &[]), b"config", &[7; 32]));
        assert!(!pinned_v2(&envelope(255, &[]), b"config", &[7; 32]));
        assert!(pinned_v2(
            &envelope(17, &[1, 0, 0, 0, b'C', b'O']),
            b"config",
            &[7; 32]
        ));
        assert!(!pinned_v2(
            &envelope(17, &[0, 0, 0, 0, b'O']),
            b"config",
            &[7; 32]
        ));
        assert!(pinned_v2(
            &envelope(19, &[1, 0, 0, 0, b'M', 1, 0, 0, 0, b'Q', b'R']),
            b"config",
            &[7; 32]
        ));
        assert!(!pinned_v2(
            &envelope(19, &[0, 0, 0, 0, b'Q', b'R']),
            b"config",
            &[7; 32]
        ));
    }
}
