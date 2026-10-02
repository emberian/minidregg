//! Key pre-rotation (KERI): `mini keygen` makes the daily key and the NEXT key;
//! enrollment commits to the next key's digest; `mini rotate-key` rotates the
//! subject to the committed next key, signed by that key alone, and commits to a
//! freshly generated key after it; `mini key-status` shows where a subject is.
//!
//! The client never hashes and never encodes a Lean value: the digest, the
//! command bytes and the possession frame all come from the Host. Whoever holds
//! the current daily key cannot rotate -- the Host refuses a key whose digest is
//! not the commitment, whatever the current key signed.
use crate::participant_enrollment::{json_private, key, member_path, pair, pinned};
use crate::*;
use ed25519_dalek::Signer;
use serde_json::{json, Value};
use std::os::unix::fs::DirBuilderExt;

pub(crate) const PREROTATION_NOTICE: &str = "\
Your NEXT key is the only thing that can rotate this identity. If the daily key
is lost or stolen, `mini rotate-key --next-key NEXT` moves your subject to it and
the daily key stops signing; a thief holding only the daily key cannot rotate.
Keep the next key OFF this machine (other media, paper): if it sits beside the
daily key, whoever takes one takes both and pre-rotation protects nothing.";

pub(crate) const HOSTED_PREROTATION_NOTICE: &str = "\
hosted shell: this next key is a file on this box, beside your daily key; root can
read both, so pre-rotation protects you only once the next key is NOT on the box.
Move it off (`--next-to` other media, or copy it home and delete it here).";

/// One Host session call; a refusal frame is decoded by the Host's own
/// `outcome` inspection and returned as the error text, by name.
pub(crate) fn call(host: &Path, socket: &Path, config: &Path, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
    let frame = session_invoke(host, socket, config, operation, payload)?;
    match frame.as_slice() {
        [byte @ (255 | 254), encoded @ ..] => {
            let decoded = inspect_bytes(host, socket, config, "outcome", encoded).ok();
            note_host_decision(HostDecision::RefusedFrame {
                command: format!("rotate-key op{operation}"),
                byte: *byte,
                encoded: encoded.to_vec(),
                decoded,
            });
            Err(format!("host refused rotate-key op{operation}"))
        }
        [actual, body @ ..] if *actual == operation && !body.is_empty() => Ok(body.to_vec()),
        _ => Err(format!("Host op{operation} returned an invalid frame")),
    }
}

fn kind_payload(kind: &str, body: &[u8]) -> Result<Vec<u8>> {
    let length: u16 = kind.len().try_into().map_err(|_| "Host kind too long")?;
    let mut payload = length.to_le_bytes().to_vec();
    payload.extend_from_slice(kind.as_bytes());
    payload.extend_from_slice(body);
    Ok(payload)
}

fn author(host: &Path, socket: &Path, config: &Path, kind: &str, value: &Value) -> Result<Vec<u8>> {
    let source = serde_json::to_vec(value).map_err(|error| error.to_string())?;
    call(host, socket, config, 7, &kind_payload(kind, &source)?)
}

fn inspect_bytes(host: &Path, socket: &Path, config: &Path, kind: &str, bytes: &[u8]) -> Result<Value> {
    let body = call(host, socket, config, 8, &kind_payload(kind, bytes)?)?;
    serde_json::from_slice(&body).map_err(|error| format!("invalid Host inspection: {error}"))
}

/// The Host's pre-rotation commitment to one public key (canonical decimal).
pub(crate) fn next_key_digest(host: &Path, socket: &Path, config: &Path, public: &[u8; 32]) -> Result<String> {
    let body = author(host, socket, config, "signing-key-next-digest", &json!({"publicKey":hex(public)}))?;
    let text = String::from_utf8(body).map_err(|_| "next-key digest is not UTF-8")?;
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err("next-key digest is not a canonical decimal".into());
    }
    Ok(text)
}

fn status(host: &Path, socket: &Path, config: &Path, subject: &str, public: &[u8; 32]) -> Result<Value> {
    let query = serde_json::to_vec(&json!({"subject":subject,"publicKey":hex(public)}))
        .map_err(|error| error.to_string())?;
    let body = call(host, socket, config, 144, &query)?;
    serde_json::from_slice(&body).map_err(|error| format!("invalid key status: {error}"))
}

fn public_file(path: &Path) -> Result<[u8; 32]> {
    fs::read(path)
        .map_err(|error| format!("cannot read public key {}: {error}", path.display()))?
        .try_into()
        .map_err(|_| format!("public key {} must contain exactly 32 raw bytes", path.display()))
}

/// The public half of a secret key file's next key, by the keygen convention.
pub(crate) fn conventional_next_public(secret: &Path) -> PathBuf {
    let mut name = secret.as_os_str().to_owned();
    name.push(".next.pub");
    PathBuf::from(name)
}

struct Workspace {
    host: PathBuf,
    config: PathBuf,
    socket: PathBuf,
    key: PathBuf,
    subject: String,
}

fn workspace(root: &Path) -> Result<Workspace> {
    let pin = json_private(&root.join("workspace.json"))?;
    pinned(&pin, "type", "minidregg-participant-workspace-v1")?;
    let socket = match SOCKET.get() {
        Some(socket) => absolute(socket)?,
        None => member_path(&pin, "socket")?,
    };
    Ok(Workspace {
        host: member_path(&pin, "host")?,
        config: member_path(&pin, "config")?,
        socket,
        key: member_path(&pin, "key")?,
        subject: pin
            .get("subject")
            .and_then(Value::as_str)
            .ok_or("workspace lacks subject")?
            .to_owned(),
    })
}

fn random_seed() -> Result<[u8; 32]> {
    let mut seed = [0u8; 32];
    File::open("/dev/urandom")
        .and_then(|mut source| source.read_exact(&mut seed))
        .map_err(|error| format!("cannot obtain operating-system randomness: {error}"))?;
    Ok(seed)
}

/// Replace `path` atomically with private `bytes`.
fn replace_private(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut staged = path.as_os_str().to_owned();
    staged.push(".rotating");
    let staged = PathBuf::from(staged);
    let _ = fs::remove_file(&staged);
    create_private(&staged, bytes)?;
    fs::rename(&staged, path).map_err(|error| format!("cannot install {}: {error}", path.display()))
}

fn replace_public(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut staged = path.as_os_str().to_owned();
    staged.push(".rotating");
    let staged = PathBuf::from(staged);
    let _ = fs::remove_file(&staged);
    create_public(&staged, bytes)?;
    fs::rename(&staged, path).map_err(|error| format!("cannot install {}: {error}", path.display()))
}

/// `mini key-status --workspace WS [--next-public-key PUB]`
pub(crate) fn key_status(mut args: Args) -> Result<()> {
    let root = absolute(&path(args.required("workspace")?))?;
    let next_public = args.optional("next-public-key").map(path);
    args.finish()?;
    let ws = workspace(&root)?;
    let daily = key(&ws.key)?.verifying_key().to_bytes();
    let mut view = status(&ws.host, &ws.socket, &ws.config, &ws.subject, &daily)?;
    let next_public = next_public.or_else(|| {
        let conventional = conventional_next_public(&ws.key);
        conventional.exists().then_some(conventional)
    });
    if let Some(next) = next_public {
        let next = public_file(&next)?;
        let next_view = status(&ws.host, &ws.socket, &ws.config, &ws.subject, &next)?;
        view["nextKeyMatchesCommitment"] = next_view["isCommittedNext"].clone();
    }
    println!("{}", serde_json::to_string_pretty(&view).map_err(|error| error.to_string())?);
    Ok(())
}

/// `mini rotate-key --workspace WS --next-key NEXT [--next-to PATH] [--to-public-key PUB]`
///
/// `--to-public-key` names a key other than NEXT's own in the rotation (NEXT
/// still signs). It exists so a journey can show the Host refusing a rotation
/// whose named key is not the one that signs; an honest rotation never uses it.
pub(crate) fn rotate_key(mut args: Args) -> Result<()> {
    let root = absolute(&path(args.required("workspace")?))?;
    let next_key = absolute(&path(args.required("next-key")?))?;
    let next_to = args.optional("next-to").map(|value| absolute(&path(value))).transpose()?;
    let named = args.optional("to-public-key").map(path);
    args.finish()?;
    let ws = workspace(&root)?;
    let signer = key(&next_key)?;
    let signer_public = signer.verifying_key().to_bytes();
    let named_public = match &named {
        Some(file) => public_file(file)?,
        None => signer_public,
    };
    let view = status(&ws.host, &ws.socket, &ws.config, &ws.subject, &named_public)?;
    let field = |name: &str| -> Result<String> {
        view.get(name)
            .and_then(Value::as_str)
            .map(str::to_owned)
            .ok_or_else(|| format!("key status lacks {name}"))
    };
    let epoch: u64 = field("keyEpoch")?.parse().map_err(|_| "key status epoch is not decimal")?;
    let key_id = field("keyId")?;
    let new_epoch = epoch.checked_add(1).ok_or("key epoch overflow")?;
    let attempts = root.join("attempts");
    let attempt = attempts.join(format!("rotate-{new_epoch}"));
    for directory in [&attempts, &attempt] {
        match fs::DirBuilder::new().mode(0o700).create(directory) {
            Ok(()) => (),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => (),
            Err(error) => return Err(format!("cannot create {}: {error}", directory.display())),
        }
    }
    let _lock = transport::service_lock(&attempt.join("rotate.lock"))?;
    let ingress_path = attempt.join("ingress.bin");
    let after_path = attempt.join("after-next.key");
    if !ingress_path.exists() {
        if !after_path.exists() {
            let mut seed = random_seed()?;
            create_private(&after_path, &seed)?;
            seed.fill(0);
        }
        let after_public = key(&after_path)?.verifying_key().to_bytes();
        let digest = next_key_digest(&ws.host, &ws.socket, &ws.config, &after_public)?;
        let request_path = attempt.join("request.json");
        let nonce = if request_path.exists() {
            json_private(&request_path)?
                .get("nonce")
                .and_then(Value::as_str)
                .ok_or("retained rotation request lacks nonce")?
                .to_owned()
        } else {
            let nonce = participant_enrollment::nonce()?;
            participant_enrollment::save_json(&request_path, &json!({"nonce":nonce}))?;
            nonce
        };
        let source = json!({"subject":ws.subject,"nonce":nonce,
            "key":{"keyId":key_id,"keyEpoch":new_epoch.to_string(),"algorithm":"1",
                "subject":ws.subject,"publicKey":hex(&named_public),
                "activeFrom":"0","activeUntil":u64::MAX.to_string(),"nextKeyDigest":digest}});
        let command = author(&ws.host, &ws.socket, &ws.config, "subject-key-rotation", &source)?;
        let plan = call(&ws.host, &ws.socket, &ws.config, 140, &command)?;
        let plan_view = inspect_bytes(&ws.host, &ws.socket, &ws.config, "subject-key-rotation-plan", &plan)?;
        if plan_view.get("commandBytes").and_then(Value::as_str) != Some(hex(&command).as_str()) {
            return Err("rotation plan names a different command".into());
        }
        let header = workspace::private::decode_hex(
            plan_view
                .get("possessionHeader")
                .and_then(Value::as_str)
                .ok_or("rotation plan lacks possession header")?,
        )?;
        let signature = signer.sign(&header).to_bytes();
        let ingress = call(&ws.host, &ws.socket, &ws.config, 141, &pair(&plan, &signature)?)?;
        create_private(&ingress_path, &ingress)?;
    }
    let ingress = fs::read(&ingress_path).map_err(|error| format!("cannot read rotation ingress: {error}"))?;
    let outcome = match call(&ws.host, &ws.socket, &ws.config, 142, &ingress) {
        Ok(frame) => inspect_bytes(&ws.host, &ws.socket, &ws.config, "outcome", &frame)?,
        Err(error) if error.starts_with("host refused") => return Err(error),
        Err(_) => {
            let frame = call(&ws.host, &ws.socket, &ws.config, 143, &ingress)?;
            inspect_bytes(&ws.host, &ws.socket, &ws.config, "outcome", &frame)?
        }
    };
    if outcome.get("type").and_then(Value::as_str) != Some("confirmed") {
        note_host_decision(HostDecision::Outcome(outcome.clone()));
        return Err("host refused rotate-key submit".into());
    }
    // Admitted: the next key is now the daily key. Install it in the workspace,
    // put the key after it where the next key was (or --next-to), and keep
    // nothing secret in the attempt.
    if named.is_none() {
        let next_secret = fs::read(&next_key).map_err(|error| format!("cannot read next key: {error}"))?;
        replace_private(&ws.key, &next_secret)?;
        let after_secret = fs::read(&after_path).map_err(|error| format!("cannot read key after next: {error}"))?;
        let destination = next_to.clone().unwrap_or_else(|| next_key.clone());
        replace_private(&destination, &after_secret)?;
        let after_public = key(&destination)?.verifying_key().to_bytes();
        replace_public(&conventional_next_public(&ws.key), &after_public)?;
        if destination != next_key && next_to.is_some() {
            fs::remove_file(&next_key).map_err(|error| format!("cannot remove used next key: {error}"))?;
        }
        fs::remove_file(&after_path).map_err(|error| format!("cannot remove staged key: {error}"))?;
        let result = json!({"type":"minidregg-key-rotation-result-v1","subject":ws.subject,
            "keyEpoch":new_epoch.to_string(),"keyId":key_id,"publicKey":hex(&signer_public),
            "nextKeyAt":destination,"outcome":outcome});
        participant_enrollment::save_json(&attempt.join("result.json"), &result)?;
        eprintln!("{PREROTATION_NOTICE}");
        println!("{}", serde_json::to_string_pretty(&result).map_err(|error| error.to_string())?);
    } else {
        println!("{}", serde_json::to_string_pretty(&outcome).map_err(|error| error.to_string())?);
    }
    Ok(())
}
