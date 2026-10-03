//! One authenticated credential action per SSH service exchange. No secret
//! reaches argv, errors, audit files, native Store data, or returned metadata.
use super::*;
use crate::{transport, workspace};
use ed25519_dalek::{Signature, Signer, VerifyingKey};
use sha2::{Digest, Sha256};
use std::io::{Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};
const LIMIT: usize = 32768;
const COMMAND: &str = "mini-provider-credentials-v1";
fn hash(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}
fn unhex(value: &str, width: usize) -> Result<Vec<u8>> {
    if value.len() != width * 2
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("invalid authentication encoding".into());
    }
    crate::decode_hex(value)
}
fn ready(fd: i32, events: i16, end: Instant) -> Result<()> {
    loop {
        let left = end.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err("credential service exchange timed out".into());
        }
        let mut p = libc::pollfd {
            fd,
            events,
            revents: 0,
        };
        let rc = unsafe { libc::poll(&mut p, 1, left.as_millis().min(i32::MAX as u128) as i32) };
        if rc < 0 && std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted {
            continue;
        }
        if rc <= 0 {
            return Err("credential service exchange unavailable or timed out".into());
        }
        return Ok(());
    }
}
// Unix backlog admission can block too; keep connection inside the SSH deadline.
fn connect(socket: &Path, end: Instant) -> Result<std::os::unix::net::UnixStream> {
    use std::os::unix::ffi::OsStrExt;
    let bytes = socket.as_os_str().as_bytes();
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if bytes.is_empty() || bytes.len() >= address.sun_path.len() || bytes.contains(&0) {
        return Err("native credential authority socket refused".into());
    }
    address.sun_family = libc::AF_UNIX as _;
    #[cfg(any(target_os = "macos", target_os = "ios", target_os = "freebsd", target_os = "openbsd", target_os = "netbsd", target_os = "dragonfly"))]
    { address.sun_len = std::mem::size_of_val(&address) as _; }
    for (dst, src) in address.sun_path.iter_mut().zip(bytes) {
        *dst = *src as _;
    }
    loop {
        if Instant::now() >= end {
            return Err("native credential authority admission timed out".into());
        }
        let fd = unsafe {
            libc::socket(
                libc::AF_UNIX,
                libc::SOCK_STREAM,
                0,
            )
        };
        if fd < 0 {
            return Err("native credential authority unavailable".into());
        }
        let stream = unsafe { std::os::unix::net::UnixStream::from_raw_fd(fd) };
        if unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } < 0 {
            return Err("native credential authority unavailable".into());
        }
        stream.set_nonblocking(true).map_err(|_| "native credential authority unavailable")?;
        let rc = unsafe {
            libc::connect(
                fd,
                &address as *const _ as *const libc::sockaddr,
                std::mem::size_of_val(&address) as _,
            )
        };
        if rc == 0 {
            return Ok(stream);
        }
        let error = std::io::Error::last_os_error();
        if error.raw_os_error() == Some(libc::EINPROGRESS) {
            ready(fd, libc::POLLOUT, end)?;
            let mut result: libc::c_int = 0;
            let mut length = std::mem::size_of_val(&result) as libc::socklen_t;
            if unsafe {
                libc::getsockopt(
                    fd,
                    libc::SOL_SOCKET,
                    libc::SO_ERROR,
                    &mut result as *mut _ as *mut libc::c_void,
                    &mut length,
                )
            } == 0
                && result == 0
            {
                return Ok(stream);
            }
            return Err("native credential authority unavailable".into());
        }
        if !matches!(
            error.kind(),
            std::io::ErrorKind::WouldBlock | std::io::ErrorKind::Interrupted
        ) {
            return Err("native credential authority unavailable".into());
        }
        drop(stream);
        std::thread::sleep(
            Duration::from_millis(5).min(end.saturating_duration_since(Instant::now())),
        );
    }
}

// poll only promises some capacity. Nonblocking syscalls preserve the same
// deadline when a peer stops reading midway through a larger frame.
struct Nonblocking {
    fd: i32,
    flags: i32,
}
impl Nonblocking {
    fn new(fd: i32) -> Result<Self> {
        let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
        if flags < 0 || unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
            return Err("credential descriptor unavailable".into());
        }
        Ok(Self { fd, flags })
    }
}
impl Drop for Nonblocking {
    fn drop(&mut self) {
        unsafe {
            libc::fcntl(self.fd, libc::F_SETFL, self.flags);
        }
    }
}
fn transient(error: &std::io::Error) -> bool {
    matches!(
        error.kind(),
        std::io::ErrorKind::Interrupted | std::io::ErrorKind::WouldBlock
    )
}
fn read_exact<R: Read + AsRawFd>(input: &mut R, mut bytes: &mut [u8], end: Instant) -> Result<()> {
    let _mode = Nonblocking::new(input.as_raw_fd())?;
    while !bytes.is_empty() {
        ready(input.as_raw_fd(), libc::POLLIN, end)?;
        let n = match input.read(bytes) {
            Ok(n) => n,
            Err(e) if transient(&e) => continue,
            Err(_) => return Err("credential service read failed".into()),
        };
        if n == 0 {
            return Err("credential service closed an incomplete frame".into());
        }
        bytes = &mut bytes[n..];
    }
    Ok(())
}
fn read<R: Read + AsRawFd>(input: &mut R, end: Instant) -> Result<Vec<u8>> {
    let mut header = [0u8; 4];
    read_exact(input, &mut header, end)?;
    let size = u32::from_le_bytes(header) as usize;
    if size == 0 || size > LIMIT {
        return Err("credential service frame exceeds bound".into());
    }
    let mut bytes = vec![0; size];
    if let Err(error) = read_exact(input, &mut bytes, end) {
        bytes.fill(0);
        return Err(error);
    }
    Ok(bytes)
}
fn write<W: Write + AsRawFd>(output: &mut W, bytes: &[u8], end: Instant) -> Result<()> {
    if bytes.is_empty() || bytes.len() > LIMIT {
        return Err("credential service frame exceeds bound".into());
    }
    let _mode = Nonblocking::new(output.as_raw_fd())?;
    let mut frame = (bytes.len() as u32).to_le_bytes().to_vec();
    frame.extend_from_slice(bytes);
    let result = (|| {
        let mut rest = frame.as_slice();
        while !rest.is_empty() {
            ready(output.as_raw_fd(), libc::POLLOUT, end)?;
            let n = match output.write(rest) {
                Ok(n) => n,
                Err(e) if transient(&e) => continue,
                Err(_) => return Err("credential service write failed".into()),
            };
            if n == 0 {
                return Err("credential service write closed".into());
            }
            rest = &rest[n..];
        }
        // Every production caller uses an unbuffered descriptor.
        Ok(())
    })();
    frame.fill(0);
    result
}
fn json(bytes: &[u8]) -> Result<Value> {
    serde_json::from_slice(bytes).map_err(|_| "invalid credential service JSON".into())
}
fn signing_bytes(request: &Value) -> Result<Vec<u8>> {
    let mut out = b"mini/member-provider-action/v1\0".to_vec();
    out.extend_from_slice(
        &serde_json::to_vec(request).map_err(|_| "credential action encode failed")?,
    );
    Ok(out)
}
fn authenticate(challenge: &Value, request: &Value) -> Result<(Owner, Value, String)> {
    action_fields(request, &["challenge", "owner", "action", "signature"])?;
    if request.get("challenge") != Some(challenge) {
        return Err("credential challenge differs or was replayed".into());
    }
    let owner = request.get("owner").ok_or("credential owner absent")?;
    action_fields(owner, &["subject", "publicKey"])?;
    let owner = Owner::new(required(owner, "subject")?, required(owner, "publicKey")?)?;
    let signature = unhex(required(request, "signature")?, 64)?;
    let key = VerifyingKey::from_bytes(
        &unhex(&owner.public_key, 32)?
            .try_into()
            .map_err(|_| "key width")?,
    )
    .map_err(|_| "invalid member signing key")?;
    let mut unsigned = request.clone();
    unsigned.as_object_mut().unwrap().remove("signature");
    let mut bytes = signing_bytes(&unsigned)?;
    let verified = key
        .verify_strict(
            &bytes,
            &Signature::from_slice(&signature).map_err(|_| "signature width")?,
        )
        .map_err(|_| "credential action signature refused");
    let digest = hash(&bytes);
    bytes.fill(0);
    super::scrub_request(&mut unsigned["action"]);
    verified?;
    let action = request
        .get("action")
        .filter(|v| v.is_object())
        .ok_or("credential action absent")?
        .clone();
    Ok((owner, action, digest))
}
pub(super) fn verify_current(view: &Value, owner: &Owner) -> Result<()> {
    if view["type"] != "subject-key-status-v1"
        || view["subject"] != owner.subject
        || view["isCurrent"] != true
        || view["currentRevoked"] != false
        || view["keyEpoch"].as_str().is_none()
    {
        return Err("native current-key authority refused credential action".into());
    }
    Ok(())
}
// The configured path itself and every ancestor are operator custody. Reject
// symlink spellings rather than silently changing the authority named by sshd.
fn operator_config(path: &Path) -> Result<Vec<u8>> {
    if !path.is_absolute() || std::fs::canonicalize(path).ok().as_deref() != Some(path) {
        return Err("credential service config must have a canonical absolute path".into());
    }
    for (index, entry) in path.ancestors().enumerate() {
        let meta = std::fs::symlink_metadata(entry)
            .map_err(|_| "credential service config unavailable")?;
        if meta.uid() != 0
            || meta.permissions().mode() & 0o022 != 0
            || (index == 0 && (!meta.is_file() || meta.len() > LIMIT as u64))
            || (index != 0 && !meta.is_dir())
        {
            return Err("credential service config and ancestors require root custody".into());
        }
    }
    std::fs::read(path).map_err(|_| "credential service config unavailable".into())
}
/// Emit the same public service policy consumed by the authenticated endpoint.
/// No seal or provider secret is read while generating operator configuration.
pub(super) fn service_configuration(paths: &[PathBuf]) -> Result<Value> {
    if paths.len() != 7 || paths.iter().any(|p| !p.is_absolute()) {
        return Err("credential service paths must be pinned absolute paths".into());
    }
    crate::host_image_sha256(&paths[0])?;
    transport::read_config(&paths[1])?;
    ProviderTable::load(&paths[3], 0)?;
    credentials::namespace_path(&paths[4], Namespace::Pool)?;
    if paths[5].starts_with(&paths[4]) {
        return Err("credential seal must remain outside credential root".into());
    }
    let helper_hash = hash(&operator_config(&paths[6])?);
    let value = json!({"type":"mini-member-provider-service-v1", "host":paths[0],
        "hostConfig":paths[1],"socket":paths[2],"providers":paths[3],
        "credentials":paths[4],"credentialsKey":paths[5],
        "namespaceHelper":paths[6],"namespaceHelperSha256":helper_hash});
    namespace_helper(&value)?;
    Ok(value)
}

/// Public metadata only. The root allocator calls this using its fixed service
/// config; this does not read a master key or assert native member authority.
pub(super) fn namespace_description(service_path: &Path, owner: &Owner) -> Result<Value> {
    let bytes = operator_config(service_path)?;
    let cfg = json(&bytes)?;
    if cfg["type"] != "mini-member-provider-service-v1" {
        return Err("credential service config version refused".into());
    }
    let root = PathBuf::from(required(&cfg, "credentials")?);
    let namespace = credentials::namespace_path(&root, Namespace::Owner(owner))?;
    Ok(
        json!({"type":"mini-credential-namespace-v1", "owner":{"subject":owner.subject,"publicKey":owner.public_key},
        "serviceConfigSha256":hash(&bytes),"credentialsRoot":root,
        "subjectDirectory":namespace.parent(),"namespace":namespace,
        "serviceLockDirectory":root.join("_service")}),
    )
}
fn namespace_helper(cfg: &Value) -> Result<Option<(PathBuf, String)>> {
    match (cfg.get("namespaceHelper"), cfg.get("namespaceHelperSha256")) {
        (None, None) => Ok(None),
        (Some(path), Some(expected)) => {
            let path = PathBuf::from(
                path.as_str()
                    .ok_or("namespace helper path must be a string")?,
            );
            let expected = expected
                .as_str()
                .ok_or("namespace helper hash must be a string")?
                .to_owned();
            unhex(&expected, 32)?;
            if hash(&operator_config(&path)?) != expected
                || std::fs::metadata(&path)
                    .map_err(|_| "namespace helper unavailable")?
                    .permissions()
                    .mode()
                    & 0o111
                    == 0
            {
                return Err("namespace helper root custody or image pin refused".into());
            }
            Ok(Some((path, expected)))
        }
        _ => Err("namespace helper path and hash must be pinned together".into()),
    }
}
fn provision_namespace(helper: &Path, owner: &Owner, end: Instant) -> Result<()> {
    let mut child = Command::new("/usr/bin/sudo")
        .args(["-n", "--"])
        .arg(helper)
        .arg(&owner.subject)
        .arg(&owner.public_key)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|_| "credential namespace provisioning unavailable")?;
    loop {
        match child
            .try_wait()
            .map_err(|_| "credential namespace provisioning unavailable")?
        {
            Some(status) => {
                return if status.success() {
                    Ok(())
                } else {
                    Err("credential namespace provisioning refused".into())
                }
            }
            None if Instant::now() >= end => {
                let _ = child.kill();
                let _ = child.try_wait();
                return Err("credential namespace provisioning timed out".into());
            }
            None => std::thread::sleep(Duration::from_millis(10)),
        }
    }
}
struct Binding {
    service_path: PathBuf,
    service: Vec<u8>,
    host: PathBuf,
    host_sha: String,
    config_path: PathBuf,
    config: Vec<u8>,
    table_path: PathBuf,
    table_sha: String,
    key_path: PathBuf,
    key_sha: String,
    namespace_helper: Option<(PathBuf, String)>,
}
impl Binding {
    fn current(&self) -> Result<()> {
        if let Some((path, expected)) = &self.namespace_helper {
            if hash(&operator_config(path)?) != *expected {
                return Err("credential namespace helper binding changed during exchange".into());
            }
        }
        if operator_config(&self.service_path)? != self.service
            || crate::host_image_sha256(&self.host)? != self.host_sha
            || transport::read_config(&self.config_path)? != self.config
            || ProviderTable::load(&self.table_path, 0)?.sha256 != self.table_sha
            || hash(
                &std::fs::read(&self.key_path).map_err(|_| "credential service key unavailable")?,
            ) != self.key_sha
        {
            return Err("credential service binding changed during exchange".into());
        }
        Ok(())
    }
    fn current_owner(&self, socket: &Path, owner: &Owner, end: Instant) -> Result<Value> {
        // Send the captured bytes, never reread a possibly upgraded config into
        // an envelope authorized by an earlier challenge.
        let mut frame = vec![2];
        frame.extend_from_slice(&(self.config.len() as u32).to_le_bytes());
        frame.extend_from_slice(&self.config);
        frame.extend_from_slice(&unhex(&self.host_sha, 32)?);
        frame.push(144);
        frame.extend_from_slice(
            &serde_json::to_vec(&json!({"subject":owner.subject,"publicKey":owner.public_key}))
                .unwrap(),
        );
        // The credential endpoint has one deadline; do not inherit the generic
        // transport's ten-minute execution wait while holding member custody.
        let mut stream = connect(socket, end)?;
        write(&mut stream, &frame, end)?;
        let reply = read(&mut stream, end)?;
        match reply.split_first() {
            Some((144, body)) => json(body),
            _ => Err("native key-status query refused credential action".into()),
        }
    }
}
pub(super) fn serve(service_path: &Path) -> Result<()> {
    let service = operator_config(service_path)?;
    let cfg = json(&service)?;
    action_fields(
        &cfg,
        &[
            "type",
            "host",
            "hostConfig",
            "socket",
            "providers",
            "credentials",
            "credentialsKey",
            "namespaceHelper",
            "namespaceHelperSha256",
        ],
    )?;
    if cfg["type"] != "mini-member-provider-service-v1" {
        return Err("credential service config version refused".into());
    }
    let path = |field: &str| -> Result<PathBuf> {
        let p = PathBuf::from(required(&cfg, field)?);
        if !p.is_absolute() {
            return Err("credential service paths must be pinned absolute paths".into());
        }
        Ok(p)
    };
    let host = path("host")?;
    let config_path = path("hostConfig")?;
    let socket = path("socket")?;
    let table_path = path("providers")?;
    let table = ProviderTable::load(&table_path, 0)?;
    let credentials_path = path("credentials")?;
    let key_path = path("credentialsKey")?;
    let store = CredentialStore::open(&credentials_path, &key_path)?;
    let binding = Binding {
        service_path: service_path.to_owned(),
        service,
        host_sha: crate::host_image_sha256(&host)?,
        host,
        config: transport::read_config(&config_path)?,
        config_path,
        table_sha: table.sha256.clone(),
        table_path,
        key_sha: hash(&std::fs::read(&key_path).map_err(|_| "credential service key unavailable")?),
        key_path,
        namespace_helper: namespace_helper(&cfg)?,
    };
    let mut nonce = [0u8; 32];
    std::fs::File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut nonce))
        .map_err(|_| "challenge entropy unavailable")?;
    let challenge = json!({"type":"mini-member-provider-challenge-v1","nonce":hex(&nonce),
        "hostSha256":binding.host_sha,"configSha256":hash(&binding.config),"tableSha256":table.sha256});
    let end = Instant::now() + Duration::from_secs(30);
    // Raw descriptors avoid stdio read-ahead hiding bytes from poll, and
    // stdout line buffering delaying the challenge until a newline.
    let duplicate = |fd| -> Result<std::fs::File> {
        let copied = unsafe { libc::dup(fd) };
        if copied < 0 {
            return Err("credential service descriptor unavailable".into());
        }
        Ok(unsafe { std::fs::File::from_raw_fd(copied) })
    };
    let mut input = duplicate(0)?;
    let mut output = duplicate(1)?;
    write(&mut output, &serde_json::to_vec(&challenge).unwrap(), end)?;
    let mut bytes = read(&mut input, end)?;
    let decoded = json(&bytes);
    bytes.fill(0);
    let mut request = decoded?;
    let answer: Result<Value> = (|| {
        let (owner, mut action, digest) = authenticate(&challenge, &request)?;
        let response: Result<Value> = (|| {
            // Serialize each authenticated member independently, including the final binding check.
            // This is a native authority snapshot, not an atomic kernel custody
            // transaction; provider use must independently recheck current owner.
            let _custody = store.member_service_lock_until(&owner, end)?;
            binding.current()?;
            let view = binding.current_owner(&socket, &owner, end)?;
            verify_current(&view, &owner)?;
            binding.current()?;
            if let Some((helper, _)) = &binding.namespace_helper {
                provision_namespace(helper, &owner, end)?;
                binding.current()?;
            }
            // Provisioning creates metadata only; recheck native signing-key
            // authority immediately before any credential mutation.
            let view = binding.current_owner(&socket, &owner, end)?;
            verify_current(&view, &owner)?;
            binding.current()?;
            let result = super::member_action(
                &store,
                &owner,
                &table,
                &action,
                required(&view, "keyEpoch")?,
            )?;
            binding.current()?;
            Ok(
                json!({"type":"mini-member-provider-result-v1","result":result,
                "authentication":{"requestSha256":digest,"keyEpoch":view["keyEpoch"],"subject":owner.subject,"publicKey":owner.public_key}}),
            )
        })();
        super::scrub_request(&mut action);
        response
    })();
    super::scrub_request(&mut request["action"]);
    let result = match answer {
        Ok(result) => result,
        Err(error) => json!({"type":"mini-member-provider-refused-v1","error":error}),
    };
    write(&mut output, &serde_json::to_vec(&result).unwrap(), end)
}
pub(super) fn client(
    workspace: &Path,
    ws: &Value,
    owner: &Owner,
    destination: &str,
    action: &mut Value,
) -> Result<Value> {
    transport::remote_destination(destination)?;
    let program = std::env::var_os("MINI_SSH")
        .filter(|p| !p.is_empty())
        .unwrap_or_else(|| "ssh".into());
    let mut child = Command::new(program)
        .args(["-T", "-o", "BatchMode=yes", "--", destination, COMMAND])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::inherit())
        .spawn()
        .map_err(|_| "cannot start authenticated credential transport")?;
    let result = (|| {
        let end = Instant::now() + Duration::from_secs(30);
        let mut input = child.stdout.take().ok_or("credential ssh stdout absent")?;
        let mut output = child.stdin.take().ok_or("credential ssh stdin absent")?;
        let challenge = json(&read(&mut input, end)?)?;
        action_fields(
            &challenge,
            &["type", "nonce", "hostSha256", "configSha256", "tableSha256"],
        )?;
        if challenge["type"] != "mini-member-provider-challenge-v1"
            || challenge["hostSha256"] != crate::host_image_sha256(&workspace::workspace_host(ws)?)?
            || challenge["configSha256"]
                != hash(&transport::read_config(&workspace::member_path(
                    ws, "config",
                )?)?)
        {
            return Err("credential service differs from the pinned Mini deployment".into());
        }
        unhex(required(&challenge, "nonce")?, 32)?;
        unhex(required(&challenge, "tableSha256")?, 32)?;
        super::sign_choice(
            workspace,
            owner,
            required(&challenge, "tableSha256")?,
            action,
        )?;
        let key = crate::participant_enrollment::key(&workspace::member_path(ws, "key")?)?;
        let mut request = json!({"challenge":challenge,"owner":{"subject":owner.subject,"publicKey":owner.public_key},"action":action});
        let mut signed = signing_bytes(&request)?;
        let signature = key.sign(&signed);
        signed.fill(0);
        request["signature"] = json!(hex(&signature.to_bytes()));
        let mut bytes =
            serde_json::to_vec(&request).map_err(|_| "credential request encode failed")?;
        let sent = write(&mut output, &bytes, end);
        bytes.fill(0);
        super::scrub_request(&mut request["action"]);
        sent?;
        let result = json(&read(&mut input, end)?)?;
        if result["type"] == "mini-member-provider-result-v1" {
            Ok(result)
        } else {
            Err(result["error"]
                .as_str()
                .unwrap_or("credential service refused")
                .to_owned())
        }
    })();
    let _ = child.kill();
    let _ = child.wait();
    result
}
#[cfg(test)]
mod tests {
    use super::*;
    fn signed(action: Value) -> (Value, Value, Owner) {
        let key = ed25519_dalek::SigningKey::from_bytes(&[41; 32]);
        let owner = Owner::new("20", &hex(key.verifying_key().as_bytes())).unwrap();
        let challenge = json!({"type":"mini-member-provider-challenge-v1","nonce":"a".repeat(64),"hostSha256":"b".repeat(64),"configSha256":"c".repeat(64),"tableSha256":"d".repeat(64)});
        let mut request = json!({"challenge":challenge,"owner":{"subject":owner.subject,"publicKey":owner.public_key},"action":action});
        request["signature"] = json!(hex(&key.sign(&signing_bytes(&request).unwrap()).to_bytes()));
        (challenge, request, owner)
    }
    #[test]
    fn action_signature_binds_secret_grant_route_owner_and_single_session_challenge() {
        let (challenge, request, _) =
            signed(json!({"action":"set","provider":"chutes","secret":"synthetic-wire-only"}));
        assert!(authenticate(&challenge, &request).is_ok());
        for (path, value) in [
            ("secret", "other"),
            ("provider", "openrouter"),
            ("action", "revoke"),
        ] {
            let mut changed = request.clone();
            changed["action"][path] = json!(value);
            assert!(authenticate(&challenge, &changed).is_err());
        }
        let mut next = challenge.clone();
        next["nonce"] = json!("f".repeat(64));
        assert!(authenticate(&next, &request).is_err());
        let mut other = request.clone();
        other["owner"]["subject"] = json!("21");
        assert!(authenticate(&challenge, &other).is_err());
    }
    #[test]
    fn bounded_frames_round_trip_and_refuse_length_before_body() {
        use std::os::unix::net::UnixStream;
        let (mut a, mut b) = UnixStream::pair().unwrap();
        let end = Instant::now() + Duration::from_secs(1);
        write(&mut a, b"single framed request", end).unwrap();
        assert_eq!(read(&mut b, end).unwrap(), b"single framed request");
        a.write_all(&((LIMIT + 1) as u32).to_le_bytes()).unwrap();
        assert!(read(&mut b, end).unwrap_err().contains("exceeds bound"));
        assert!(read(&mut b, Instant::now())
            .unwrap_err()
            .contains("timed out"));
    }

    #[test]
    fn partially_saturated_pipe_stalled_reader_obeys_deadline() {
        let mut fds = [0; 2];
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
        let _reader = unsafe { std::fs::File::from_raw_fd(fds[0]) };
        let mut writer = unsafe { std::fs::File::from_raw_fd(fds[1]) };
        // Reduce pipe capacity so poll reports writable but a full frame cannot fit.
        assert!(unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_SETPIPE_SZ, 4096) } > 0);
        let started = Instant::now();
        let error = write(
            &mut writer,
            &vec![b'x'; LIMIT],
            started + Duration::from_millis(80),
        )
        .unwrap_err();
        assert!(error.contains("timed out"));
        assert!(started.elapsed() < Duration::from_secs(1));
    }

    #[test]
    fn native_authority_backlog_obeys_exchange_deadline() {
        use std::os::unix::net::{UnixListener, UnixStream};
        let path = std::env::temp_dir().join(format!("mini-key-backlog-{}", std::process::id()));
        let listener = UnixListener::bind(&path).unwrap();
        assert_eq!(unsafe { libc::listen(listener.as_raw_fd(), 1) }, 0);
        let a = UnixStream::connect(&path).unwrap();
        let b = UnixStream::connect(&path).unwrap();
        let start = Instant::now();
        assert!(connect(&path, start + Duration::from_millis(40)).is_err());
        assert!(start.elapsed() < Duration::from_secs(1));
        drop(a);
        drop(b);
        drop(listener);
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn namespace_allocator_requires_complete_root_image_pin() {
        assert!(namespace_helper(&json!({})).unwrap().is_none());
        assert!(
            namespace_helper(&json!({"namespaceHelper":"/usr/local/lib/mini/helper"})).is_err()
        );
        assert!(namespace_helper(&json!({"namespaceHelperSha256":"00".repeat(32)})).is_err());
        assert!(namespace_helper(
            &json!({"namespaceHelper":"../helper","namespaceHelperSha256":"00".repeat(32)})
        )
        .is_err());
        assert!(namespace_helper(
            &json!({"namespaceHelper":"/not-present/helper","namespaceHelperSha256":"bad"})
        )
        .is_err());
    }

    #[test]
    fn native_identity_must_be_current_unrevoked_and_exact() {
        let (_, _, owner) = signed(json!({"action":"ls"}));
        let good = json!({"type":"subject-key-status-v1","subject":"20","keyEpoch":"1","isCurrent":true,"currentRevoked":false});
        assert!(verify_current(&good, &owner).is_ok());
        for field in ["isCurrent", "currentRevoked", "subject", "keyEpoch"] {
            let mut bad = good.clone();
            bad.as_object_mut().unwrap().remove(field);
            assert!(verify_current(&bad, &owner).is_err());
        }
        let mut revoked = good.clone();
        revoked["currentRevoked"] = json!(true);
        assert!(verify_current(&revoked, &owner).is_err());
    }
}
