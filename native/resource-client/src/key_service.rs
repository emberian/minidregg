//! The member side of the key broker's signed exchange (`member-action`).
//! The broker (native/mini-keys) is the only process that holds the seal key;
//! this client proves which member is asking, never sees a stored key, and
//! talks to the broker one of two ways:
//!
//! * hosted (a session on the box): the broker's Unix socket directly, after
//!   checking the answering uid is the broker's (`mini_keys::client`);
//! * remote (`mini --remote`): ssh to the box's forced command
//!   `mini-provider-credentials-v1`, which is `mini-keys relay`, a byte splice
//!   to the same socket.
//!
//! No secret reaches argv, errors, audit files, native Store data, or returned metadata.
use super::*;
use crate::{transport, workspace};
use ed25519_dalek::Signer;
use sha2::{Digest, Sha256};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::time::{Duration, Instant};
const LIMIT: usize = mini_keys::wire::MEMBER_FRAME;
const COMMAND: &str = "mini-provider-credentials-v1";
fn hash(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}
fn unhex(value: &str, width: usize) -> Result<Vec<u8>> {
    if !mini_sdk::hex::is_canonical_len(value, width) {
        return Err("invalid authentication encoding".into());
    }
    mini_sdk::hex::decode(value).map_err(|e| e.0)
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
/// The broker's first frame is its challenge, or a named refusal: the broker
/// refused this account (`{"refused":CODE}`), or the exchange
/// (`mini-member-provider-refused-v1`).
fn refusal_of(frame: &Value) -> Option<String> {
    if let Some(code) = frame.get("refused").and_then(Value::as_str) {
        return Some(format!(
            "mini-keys refused {code}: {}",
            frame["detail"].as_str().unwrap_or("")
        ));
    }
    if frame["type"] == "mini-member-provider-refused-v1" {
        return Some(
            frame["error"]
                .as_str()
                .unwrap_or("credential service refused")
                .to_owned(),
        );
    }
    None
}
/// One signed exchange over any pair of descriptors.
fn exchange<R: Read + AsRawFd, W: Write + AsRawFd>(
    input: &mut R,
    output: &mut W,
    workspace: &Path,
    ws: &Value,
    owner: &Owner,
    action: &mut Value,
    end: Instant,
) -> Result<Value> {
    let challenge = json(&read(input, end)?)?;
    if let Some(refused) = refusal_of(&challenge) {
        return Err(refused);
    }
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
    let sent = write(output, &bytes, end);
    bytes.fill(0);
    super::scrub_request(&mut request["action"]);
    sent?;
    let result = json(&read(input, end)?)?;
    if result["type"] == "mini-member-provider-result-v1" {
        Ok(result)
    } else {
        Err(refusal_of(&result).unwrap_or_else(|| "credential service refused".into()))
    }
}
/// A hosted session: the box's broker socket.
pub(super) fn local(
    broker: &mini_keys::client::Broker,
    workspace: &Path,
    ws: &Value,
    owner: &Owner,
    action: &mut Value,
) -> Result<Value> {
    let end = Instant::now() + Duration::from_secs(30);
    let mut stream = broker.connect(end).map_err(String::from)?;
    mini_keys::wire::send(&mut stream, &json!({"op":"member-action"}), end)?;
    let mut input = stream
        .try_clone()
        .map_err(|_| "key broker socket unavailable")?;
    exchange(&mut input, &mut stream, workspace, ws, owner, action, end)
}
/// A remote workspace: ssh to the box's forced command, which relays to its broker.
pub(super) fn client(
    workspace: &Path,
    ws: &Value,
    owner: &Owner,
    destination: &str,
    action: &mut Value,
) -> Result<Value> {
    transport::remote_destination(destination)?;
    let mut ssh = mini_sdk::operator::Ssh::new(destination)?;
    ssh.remote_command = Some(COMMAND.to_owned());
    let mut stream = mini_sdk::operator::open_stream(&ssh).map_err(|failure| match failure {
        mini_sdk::operator::Failure::Unsent(why) | mini_sdk::operator::Failure::Uncertain(why) => why,
    })?;
    let end = Instant::now() + Duration::from_secs(30);
    exchange(&mut stream.stdout, &mut stream.stdin, workspace, ws, owner, action, end)
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::os::fd::FromRawFd;
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
    fn a_broker_refusal_in_place_of_the_challenge_is_named() {
        assert_eq!(
            refusal_of(&json!({"refused":"peer-not-allowed","detail":"uid 7 holds no role"})).unwrap(),
            "mini-keys refused peer-not-allowed: uid 7 holds no role"
        );
        assert_eq!(
            refusal_of(&json!({"type":"mini-member-provider-refused-v1","error":"owner-not-current"})).unwrap(),
            "owner-not-current"
        );
        assert!(refusal_of(&json!({"type":"mini-member-provider-challenge-v1"})).is_none());
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

    /// The real `mini key` member exchange against the real broker, over its
    /// socket, as one uid (the broker config says singleAccount): the signing
    /// bytes, the challenge pins and the result agree across the two crates.
    #[test]
    fn hosted_key_set_reaches_the_broker_and_the_secret_stays_there() {
        use mini_keys::{peer, server, wire as w};
        use std::os::unix::fs::PermissionsExt;
        use std::os::unix::net::UnixListener;
        let dir = std::env::temp_dir().join(format!("rc-broker-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let mk = |p: &Path| {
            std::fs::create_dir_all(p).unwrap();
            std::fs::set_permissions(p, std::fs::Permissions::from_mode(0o700)).unwrap();
        };
        mk(&dir);
        let dir = dir.canonicalize().unwrap();
        for sub in ["etc", "keys", "run", "state", "credentials", "ws"] {
            mk(&dir.join(sub));
        }
        let put = |p: &Path, b: &[u8], mode: u32| {
            std::fs::write(p, b).unwrap();
            std::fs::set_permissions(p, std::fs::Permissions::from_mode(mode)).unwrap();
        };
        put(&dir.join("keys/credentials.key"), &[9u8; 32], 0o600);
        put(&dir.join("etc/host"), b"host image", 0o755);
        put(&dir.join("etc/config.json"), br#"{"pinned":true}"#, 0o644);
        put(&dir.join("ws/member.key"), &[41u8; 32], 0o600);
        put(&dir.join("etc/providers.json"), br#"{"type":"mini-provider-table-v2","providers":[{"name":"openrouter","endpoint":"https://example.test/v1/chat/completions","kind":"openai-compatible","models":["m1"],"credential":"user"}]}"#, 0o644);
        let seed = ed25519_dalek::SigningKey::from_bytes(&[41u8; 32]);
        let owner = Owner::new("20", &hex(seed.verifying_key().as_bytes())).unwrap();
        let store = UnixListener::bind(dir.join("run/public.sock")).unwrap();
        std::thread::spawn(move || {
            for s in store.incoming() {
                let mut s = s.unwrap();
                let end = Instant::now() + Duration::from_secs(5);
                let _ = w::read_frame(&mut s, 1 << 20, end).unwrap();
                let mut reply = vec![144u8];
                reply.extend_from_slice(br#"{"type":"subject-key-status-v1","subject":"20","keyEpoch":"4","isCurrent":true,"currentRevoked":false}"#);
                w::write_frame(&mut s, &reply, end).unwrap();
            }
        });
        let config = json!({"type":"mini-keys-broker-v1","socket":dir.join("run/broker.sock"),"audit":dir.join("state/audit.jsonl"),
            "spool":dir.join("state/spool"),"singleAccount":true,"peers":[{"role":"member","gids":[peer::egid()]}],
            "credentials":{"host":dir.join("etc/host"),"hostConfig":dir.join("etc/config.json"),"publicSocket":dir.join("run/public.sock"),
                "providers":dir.join("etc/providers.json"),"root":dir.join("credentials"),"key":dir.join("keys/credentials.key")}});
        put(&dir.join("etc/broker.json"), config.to_string().as_bytes(), 0o644);
        let (b, listener) = server::Broker::start(server::Config::load(&dir.join("etc/broker.json"), peer::euid()).unwrap()).unwrap();
        std::thread::spawn(move || b.serve(listener));
        let broker = mini_keys::client::Broker::new(dir.join("run/broker.sock"), peer::euid());
        let ws = json!({"host":dir.join("etc/host"),"config":dir.join("etc/config.json"),"key":dir.join("ws/member.key")});
        let secret = "sk-hosted-member-0123456789";
        let mut action = json!({"action":"set","provider":"openrouter","secret":secret});
        let result = local(&broker, &dir.join("ws"), &ws, &owner, &mut action).unwrap();
        assert_eq!(result["result"]["stored"], "sealed");
        assert_eq!(result["authentication"]["keyEpoch"], "4");
        let mut ls = json!({"action":"ls"});
        let listed = local(&broker, &dir.join("ws"), &ws, &owner, &mut ls).unwrap();
        assert_eq!(listed["result"]["credentials"][0]["provider"], "openrouter");
        assert!(!listed.to_string().contains(secret));
        // A broker answering as another uid is refused before any byte of the request.
        let impostor = mini_keys::client::Broker::new(dir.join("run/broker.sock"), peer::euid().wrapping_add(1));
        let mut again = json!({"action":"set","provider":"openrouter","secret":secret});
        assert!(local(&impostor, &dir.join("ws"), &ws, &owner, &mut again).unwrap_err().contains("broker-identity"));
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn native_identity_must_be_current_unrevoked_and_exact() {
        let owner = Owner::new("20", &"ab".repeat(32)).unwrap();
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
