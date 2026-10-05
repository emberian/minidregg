//! Key pre-rotation (KERI): `mini keygen` makes the daily key and the NEXT key;
//! enrollment commits to the next key's digest; `mini rotate-key` rotates the
//! subject to the committed next key, signed by that key alone, and commits to a
//! freshly generated key after it; `mini key-status` shows where a subject is.
//!
//! The client never hashes and never encodes a Lean value: the digest, the
//! command bytes and the possession frame all come from the Host. Whoever holds
//! the current daily key cannot rotate -- the Host refuses a key whose digest is
//! not the commitment, whatever the current key signed.
use crate::participant_enrollment::{json_private, key, member_path, pair};
use crate::*;
use ed25519_dalek::Signer;
use serde_json::{json, Value};
#[path = "key_rotation_custody.rs"]
mod custody;

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
pub(crate) fn call(
    host: &Path,
    socket: &Path,
    config: &Path,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>> {
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

fn inspect_bytes(
    host: &Path,
    socket: &Path,
    config: &Path,
    kind: &str,
    bytes: &[u8],
) -> Result<Value> {
    let body = call(host, socket, config, 8, &kind_payload(kind, bytes)?)?;
    serde_json::from_slice(&body).map_err(|error| format!("invalid Host inspection: {error}"))
}

/// The Host's pre-rotation commitment to one public key (canonical decimal).
pub(crate) fn next_key_digest(
    host: &Path,
    socket: &Path,
    config: &Path,
    public: &[u8; 32],
) -> Result<String> {
    let body = author(
        host,
        socket,
        config,
        "signing-key-next-digest",
        &json!({"publicKey":hex(public)}),
    )?;
    let text = String::from_utf8(body).map_err(|_| "next-key digest is not UTF-8")?;
    if !mini_sdk::decimal::is_digits(&text) {
        return Err("next-key digest is not a canonical decimal".into());
    }
    Ok(text)
}

fn status(
    host: &Path,
    socket: &Path,
    config: &Path,
    subject: &str,
    public: &[u8; 32],
) -> Result<Value> {
    let query = serde_json::to_vec(&json!({"subject":subject,"publicKey":hex(public)}))
        .map_err(|error| error.to_string())?;
    let body = call(host, socket, config, 144, &query)?;
    serde_json::from_slice(&body).map_err(|error| format!("invalid key status: {error}"))
}

/// The key status, or `None` when the Host holds no current key for the
/// subject (not enrolled yet). Any other refusal is an error, by its name.
/// Records no Host decision: a caller that refuses explains itself.
pub(crate) fn status_if_enrolled(
    host: &Path,
    socket: &Path,
    config: &Path,
    subject: &str,
    public: &[u8; 32],
) -> Result<Option<Value>> {
    let query = serde_json::to_vec(&json!({"subject":subject,"publicKey":hex(public)}))
        .map_err(|error| error.to_string())?;
    let frame = session_invoke(host, socket, config, 144, &query)?;
    match frame.as_slice() {
        [144, body @ ..] if !body.is_empty() => serde_json::from_slice(body)
            .map(Some)
            .map_err(|error| format!("invalid key status: {error}")),
        [255 | 254, encoded @ ..] => {
            let decoded = inspect_bytes(host, socket, config, "outcome", encoded)?;
            let detail = decoded
                .get("detail")
                .and_then(Value::as_str)
                .and_then(|text| crate::decode_hex(text).ok())
                .and_then(|bytes| String::from_utf8(bytes).ok())
                .unwrap_or_default();
            let text = format!("{detail} {decoded}");
            if detail == "subject has no current signing key" {
                Ok(None)
            } else {
                Err(format!("the Host refused the key-status query: {text}"))
            }
        }
        _ => Err("Host op144 returned an invalid frame".into()),
    }
}

// ---------------------------------------------------------------- the next key's co-signature

/// What a committed NEXT key signs at enrollment (`Kernel.ParticipantKeyEnrollment.
/// nextPossessionFrame`): its consent to succeed the enrolled key. Fixed layout,
/// so `mini keygen` co-signs offline; `enroll plan` checks these bytes against
/// the Host's own (`participant-key-enrollment-next-possession`) before using a
/// co-signature, so a drift between this copy and the kernel refuses loudly.
pub(crate) const NEXT_POSSESSION_TAG: &[u8] = b"DREGG/PARTICIPANT/KEY-ENROLL/NEXT-POSSESSION/v1";

pub(crate) fn next_possession_frame(public: &[u8; 32], next: &[u8; 32]) -> Vec<u8> {
    [NEXT_POSSESSION_TAG, public, next].concat()
}

/// The co-signature file `mini keygen` writes beside the key: KEY.next.cosign.
pub(crate) fn conventional_next_cosign(secret: &Path) -> PathBuf {
    let mut name = secret.as_os_str().to_owned();
    name.push(".next.cosign");
    PathBuf::from(name)
}

/// The next key's co-signature over the pair (daily public key, next public key).
pub(crate) fn cosign(public: &[u8; 32], next: &ed25519_dalek::SigningKey) -> [u8; 64] {
    next.sign(&next_possession_frame(
        public,
        &next.verifying_key().to_bytes(),
    ))
    .to_bytes()
}

/// A co-signature verifies under the next key over the client's frame.
pub(crate) fn verify_cosign(
    public: &[u8; 32],
    next: &[u8; 32],
    signature: &[u8; 64],
) -> Result<()> {
    ed25519_dalek::VerifyingKey::from_bytes(next)
        .map_err(|_| "the next public key is not a valid Ed25519 point")?
        .verify_strict(&next_possession_frame(public, next), &ed25519_dalek::Signature::from_bytes(signature))
        .map_err(|_| "the co-signature does not verify: it was not made by this next key for this key (`mini enroll --action cosign`)".into())
}

/// The Host's frame for the pair; the client's copy must equal it.
pub(crate) fn host_next_possession_frame(
    host: &Path,
    socket: &Path,
    config: &Path,
    public: &[u8; 32],
    next: &[u8; 32],
) -> Result<Vec<u8>> {
    let frame = author(
        host,
        socket,
        config,
        "participant-key-enrollment-next-possession",
        &json!({"publicKey":hex(public),"nextPublicKey":hex(next)}),
    )?;
    if frame != next_possession_frame(public, next) {
        return Err("the Host's next-possession frame differs from this client's: refusing to co-sign or plan with it".into());
    }
    Ok(frame)
}

// ---------------------------------------------------------------- whose key can rotate this subject

/// How a workspace binds its subject's pre-rotation commitment (FIX-IDENTITY):
/// the next public key it holds, or an explicit statement that it holds none.
pub(crate) enum Commitment {
    Mine([u8; 32]),
    Without,
}

/// The client half of pre-rotation. A subject whose record commits to a next key
/// that is not THIS client's can be rotated -- taken -- by whoever holds that key;
/// a friend must never build on it. Refuses, by name, unless the subject's
/// commitment is the digest of `commitment`'s key (or the subject commits to none
/// and the friend said `--no-prerotation`). `Ok(None)`: the Host knows no current
/// key for the subject yet, so there is nothing to compare.
pub(crate) fn check_commitment(
    host: &Path,
    socket: &Path,
    config: &Path,
    subject: &str,
    daily: &[u8; 32],
    commitment: &Commitment,
) -> Result<Option<Value>> {
    let asked = match commitment {
        Commitment::Mine(next) => next,
        Commitment::Without => daily,
    };
    let Some(view) = status_if_enrolled(host, socket, config, subject, asked)? else {
        return Ok(None);
    };
    let flag = |name: &str| view.get(name).and_then(Value::as_bool);
    let prerotated = flag("prerotated").ok_or("key status lacks prerotated")?;
    let redo = "ask your sponsor to enroll you again, as a NEW name (this subject cannot be repaired): `enroll plan NAME KEYFILE NEXT-PUB COSIGN` with the two hex lines your `keygen` printed (`mini enroll --action cosign --key KEY` prints them again); never use this subject";
    match (commitment, prerotated) {
        (Commitment::Mine(_), true) => {
            if flag("isCommittedNext") != Some(true) {
                return Err(format!(
                    "refused: subject {subject}'s record commits to a next key that is NOT yours: whoever holds that key can rotate this subject to itself and lock your key out. {redo}"
                ));
            }
        }
        (Commitment::Mine(_), false) => {
            return Err(format!(
                "refused: subject {subject}'s record commits to no next key, but you hold one: initialize with --no-prerotation, then explicitly commit it with `mini adopt-next-key --workspace WORKSPACE --next-key NEXT` before rotating"
            ));
        }
        (Commitment::Without, true) => {
            return Err(format!(
                "refused: subject {subject}'s record commits to a next key, and this workspace holds none (--no-prerotation, or no KEY.next.pub): a key you do not hold could replace yours. Pass your next public key (--next-pub), or {redo}"
            ));
        }
        (Commitment::Without, false) => {}
    }
    Ok(Some(view))
}

pub(crate) fn public_file(path: &Path) -> Result<[u8; 32]> {
    fs::read(path)
        .map_err(|error| format!("cannot read public key {}: {error}", path.display()))?
        .try_into()
        .map_err(|_| {
            format!(
                "public key {} must contain exactly 32 raw bytes",
                path.display()
            )
        })
}

/// The public half of a secret key file, by the keygen convention (KEY.pub).
pub(crate) fn conventional_public(secret: &Path) -> PathBuf {
    let mut name = secret.as_os_str().to_owned();
    name.push(".pub");
    PathBuf::from(name)
}

/// The derived public files of a daily key (KEY.pub, KEY.next.cosign) as they stand
/// before a rotation, checked against the secrets they describe. A rotation that
/// would leave a file naming a key pair it cannot verify refuses before the Host
/// advances: it never overwrites a file it does not recognise.
fn derived_public_priors(daily: &Path, next_public: &[u8; 32]) -> Result<(Value, Value)> {
    let daily_public = key(daily)?.verifying_key().to_bytes();
    let public_path = conventional_public(daily);
    let public_prior = if public_path.exists() {
        if public_file(&public_path)? != daily_public {
            return Err(format!("{} does not name the public half of {}; refusing to rotate a key whose public file is not its own (restore it, or remove it and rotate)", public_path.display(), daily.display()));
        }
        json!(hex(&daily_public))
    } else {
        Value::Null
    };
    let cosign_path = conventional_next_cosign(daily);
    let cosign_prior = if cosign_path.exists() {
        let bytes: [u8; 64] = fs::read(&cosign_path)
            .map_err(|e| format!("cannot read {}: {e}", cosign_path.display()))?
            .try_into()
            .map_err(|_| format!("{} must contain exactly 64 raw bytes", cosign_path.display()))?;
        verify_cosign(&daily_public, next_public, &bytes)
            .map_err(|e| format!("{}: {e}; refusing to rotate past a co-signature that is not this pair's", cosign_path.display()))?;
        json!(hex(&bytes))
    } else {
        Value::Null
    };
    Ok((public_prior, cosign_prior))
}

fn retained_prior(state: &Value, field: &str) -> Result<Option<Vec<u8>>> {
    match state.get(field) {
        None => Err(format!("retained rotation lacks {field} (prepared by an older mini): finish it with that mini, or start another with --new-attempt ID")),
        Some(Value::Null) => Ok(None),
        Some(value) => Ok(Some(crate::decode_hex(value.as_str().ok_or_else(|| format!("retained {field} is not hex"))?)?)),
    }
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
    let pin = workspace::load_for_key_transition(root)?;
    let socket = SOCKET
        .get()
        .ok_or("workspace has no pinned key-transition socket")?
        .clone();
    Ok(Workspace {
        host: workspace::workspace_host(&pin)?,
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

/// The workspace subject's current key epoch, as the Host reports it.
pub(crate) fn current_key_epoch(root: &Path) -> Result<String> {
    let ws = workspace(root)?;
    let daily = key(&ws.key)?.verifying_key().to_bytes();
    let view = status(&ws.host, &ws.socket, &ws.config, &ws.subject, &daily)?;
    view.get("keyEpoch")
        .and_then(Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| "key status lacks keyEpoch".to_owned())
}

/// `mini key-status --workspace WS [--next-public-key PUB]`
pub(crate) fn key_status(mut args: Args) -> Result<()> {
    let root = absolute(&path(args.required("workspace")?))?;
    let next_public = args.optional("next-public-key").map(path);
    args.finish()?;
    let ws = workspace(&root)?;
    let daily = key(&ws.key)?.verifying_key().to_bytes();
    let mut view = status(&ws.host, &ws.socket, &ws.config, &ws.subject, &daily)?;
    let next_public = if let Some(file) = next_public {
        Some(public_file(&file)?)
    } else {
        let manifest = participant_enrollment::json_private(&root.join("workspace.json"))?;
        if let Some(text) = manifest.get("nextPublicKey").and_then(Value::as_str) {
            Some(
                crate::decode_hex(text)?
                    .try_into()
                    .map_err(|_| "workspace nextPublicKey is not 32 bytes")?,
            )
        } else {
            let file = conventional_next_public(&ws.key);
            if file.exists() {
                Some(public_file(&file)?)
            } else {
                None
            }
        }
    };
    if let Some(next) = next_public {
        let next_view = status(&ws.host, &ws.socket, &ws.config, &ws.subject, &next)?;
        view["nextKeyMatchesCommitment"] = next_view["isCommittedNext"].clone();
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&view).map_err(|error| error.to_string())?
    );
    Ok(())
}

/// Source-authored command equality always applies. Protected rotations also
/// require a local inspector that reconstructs the role-specific signed frame.
fn check_rotation_plan(view: &Value, command: &[u8], identity: Option<&Value>) -> Result<()> {
    if view.get("commandBytes").and_then(Value::as_str) != Some(hex(command).as_str()) {
        return Err("rotation plan names a different command".into());
    }
    if let Some(identity) = identity {
        if view["type"] != "subject-key-rotation-plan-v1"
            || view["domain"] != identity["domain"]
            || view["semantics"] != identity["semantics"]
        {
            return Err("rotation plan differs from locally pinned identity".into());
        }
        if view["possessionFrameValidated"] != true {
            return Err("pinned verifier does not validate rotation possession frames; explicitly upgrade the same-identity continuity verifier".into());
        }
    }
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
    let next_to = args
        .optional("next-to")
        .map(|value| absolute(&path(value)))
        .transpose()?;
    let named = args.optional("to-public-key").map(path);
    let new_attempt = args
        .optional("new-attempt")
        .map(|v| {
            v.into_string()
                .map_err(|_| "--new-attempt must be ASCII".to_owned())
        })
        .transpose()?;
    if let Some(id) = &new_attempt {
        custody::stable_id(id)?;
    }
    args.finish()?;
    workspace::private_dir(&root)?;
    let _transition = transport::service_lock(&root.join("key-transition.lock"))?;
    let ws = workspace(&root)?;
    let manifest = workspace::load_for_key_transition(&root)?;
    let identity = receipt_continuity::key_transition_identity_if_enabled(&root, &manifest)?;
    let destination = next_to.clone().unwrap_or_else(|| next_key.clone());
    if next_key == ws.key || destination == ws.key {
        return Err("NEXT and its destination must differ from the daily key".into());
    }
    let attempts = root.join("attempts");
    custody::directory(&attempts)?;
    let active_path = root.join("rotation-active.json");
    let active = if active_path.exists() {
        Some(custody::read(&active_path)?)
    } else {
        None
    };
    let active_id = active.as_ref().and_then(|v| v["attempt"].as_str());
    let id = new_attempt.as_deref().or(active_id).unwrap_or("default");
    custody::stable_id(id)?;
    if let Some(prior_id) = active_id {
        if prior_id != id {
            let prior = custody::read(
                &attempts
                    .join(format!("rotate-{prior_id}"))
                    .join("custody.json"),
            )?;
            if prior["phase"] != "completed" && prior["phase"] != "refused" {
                return Err("retained rotation is unresolved; recover its original attempt before a new succession".into());
            }
        }
    }
    // Old pre-fix attempts cannot safely be interpreted as a fresh rotation.
    // Preserve them and refuse rather than advance the Host epoch again.
    if active.is_none() {
        for entry in fs::read_dir(&attempts).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            if entry.file_name().to_string_lossy().starts_with("rotate-")
                && entry.path().join("ingress.bin").exists()
                && !entry.path().join("custody.json").exists()
            {
                return Err(format!("legacy retained rotation at {} requires original-ingress recovery; refusing fresh rotation",entry.path().display()));
            }
        }
    }
    let attempt = attempts.join(format!("rotate-{id}"));
    custody::directory(&attempt)?;
    let _lock = transport::service_lock(&attempt.join("rotate.lock"))?;
    let state_path = attempt.join("custody.json");
    let binding = json!({"operation":id,"subject":ws.subject,"daily":ws.key,"next":next_key,"destination":destination,
        "namedPublic":named.as_ref().map(|p|public_file(p).map(|v|hex(&v))).transpose()?,
        "host":ws.host,"socket":ws.socket,"config":hex(&custody::bytes(&ws.config,transport::HOST_MAX_FRAME)?) });
    let mut state = if state_path.exists() {
        let prior = custody::read(&state_path)?;
        if prior["binding"] != binding {
            return Err(
                "rotation attempt differs from retained original input or destination".into(),
            );
        }
        prior
    } else {
        let signer = key(&next_key)?;
        let signer_public = signer.verifying_key().to_bytes();
        let named_public = match &named {
            Some(p) => public_file(p)?,
            None => signer_public,
        };
        let view = status(&ws.host, &ws.socket, &ws.config, &ws.subject, &named_public)?;
        let epoch = view["keyEpoch"]
            .as_str()
            .ok_or("key status lacks keyEpoch")?
            .parse::<u64>()
            .map_err(|_| "key epoch is not decimal")?;
        let new_epoch = epoch.checked_add(1).ok_or("key epoch overflow")?;
        let key_id = view["keyId"].as_str().ok_or("key status lacks keyId")?;
        custody::immutable(
            &attempt.join("original-next.key"),
            &custody::bytes(&next_key, 32)?,
        )?;
        custody::immutable(
            &attempt.join("original-daily.key"),
            &custody::bytes(&ws.key, 32)?,
        )?;
        let after = attempt.join("after-next.key");
        if !after.exists() {
            let mut seed = crate::fsio::random::<32>()?;
            custody::immutable(&after, &seed)?;
            seed.fill(0);
        }
        let prior_destination = if destination.exists() {
            Some(hex(&custody::bytes(&destination, 32)?))
        } else {
            None
        };
        let public_path = conventional_next_public(&ws.key);
        let prior_public = if public_path.exists() {
            Some(hex(&fs::read(&public_path).map_err(|e| e.to_string())?))
        } else {
            None
        };
        let (daily_public_prior, cosign_prior) = if named.is_none() {
            derived_public_priors(&ws.key, &signer_public)?
        } else {
            (Value::Null, Value::Null)
        };
        let prepared = json!({"type":"minidregg-retained-rotation-v2","binding":binding,"phase":"preparing","epoch":epoch.to_string(),"newEpoch":new_epoch.to_string(),
            "keyId":key_id,"signerPublic":hex(&signer_public),"namedPublic":hex(&named_public),"destinationPrior":prior_destination,"publicPrior":prior_public,
            "dailyPublicPrior":daily_public_prior,"cosignPrior":cosign_prior,"manifestPrior":manifest});
        custody::publish(&state_path, &prepared, None)?;
        prepared
    };
    let pointer = json!({"type":"minidregg-rotation-active-v1","attempt":id});
    custody::publish(&active_path, &pointer, active.as_ref())?;
    if attempt.join("result.json").exists() && state["phase"] == "installed" {
        state = custody::phase(&state_path, &state, "completed")?;
    }
    if state["phase"] == "completed" {
        let mut result = custody::read(&attempt.join("result.json"))?;
        result["replayed"] = json!(true);
        println!(
            "{}",
            serde_json::to_string_pretty(&result).map_err(|e| e.to_string())?
        );
        return Ok(());
    }
    if state["phase"] == "refused" {
        return Err("retained original rotation was explicitly refused; use --new-attempt ID to authorize another request".into());
    }
    let signer = key(&attempt.join("original-next.key"))?;
    let signer_public = signer.verifying_key().to_bytes();
    if Some(hex(&signer_public).as_str()) != state["signerPublic"].as_str() {
        return Err("retained successor fingerprint changed".into());
    }
    let named_public: [u8; 32] = crate::decode_hex(
        state["namedPublic"]
            .as_str()
            .ok_or("retained named public absent")?,
    )?
    .try_into()
    .map_err(|_| "retained named public size")?;
    let epoch = state["epoch"]
        .as_str()
        .ok_or("retained epoch absent")?
        .parse::<u64>()
        .map_err(|_| "retained epoch invalid")?;
    let new_epoch = state["newEpoch"]
        .as_str()
        .ok_or("retained successor epoch absent")?
        .parse::<u64>()
        .map_err(|_| "retained successor epoch invalid")?;
    let key_id = state["keyId"]
        .as_str()
        .ok_or("retained keyId absent")?
        .to_owned();
    let ingress_path = attempt.join("ingress.bin");
    let after_path = attempt.join("after-next.key");
    if state["phase"] == "preparing" {
        // BEFORE the Host advances: a founder of a private room must already have handed
        // the room to the key it is rotating to, or the new key signs what no member pins.
        workspace::roomkey::founder_rotation_gate(&root, &named_public)?;
    }
    if state["phase"] == "preparing" && named.is_none() {
        workspace::private::keyring_remember(&ws.key, &epoch.to_string())?;
        custody::sync_parent(&workspace::private::enc_ring_path(&ws.key))?;
    }
    if !ingress_path.exists() {
        if state["phase"] != "preparing" {
            return Err("retained admitted/uncertain ingress is absent; refusing reauthor".into());
        }
        if !after_path.exists() {
            return Err("retained after-next secret is absent; refusing regeneration".into());
        }
        let after_public = key(&after_path)?.verifying_key().to_bytes();
        let digest = if let Some(identity) = &identity {
            let input = serde_json::to_vec(&json!({"publicKey":hex(&after_public)}))
                .map_err(|e| e.to_string())?;
            let bytes = receipt_continuity::key_source(
                &root,
                &manifest,
                identity,
                receipt_continuity::KeySourceOperation::NextKeyDigest,
                &input,
            )?;
            let digest =
                String::from_utf8(bytes).map_err(|_| "local next-key digest is not UTF-8")?;
            participant_enrollment::decimal(&digest, "local next-key digest")?;
            digest
        } else {
            next_key_digest(&ws.host, &ws.socket, &ws.config, &after_public)?
        };
        let request_path = attempt.join("request.json");
        let nonce = if request_path.exists() {
            json_private(&request_path)?
                .get("nonce")
                .and_then(Value::as_str)
                .ok_or("retained rotation request lacks nonce")?
                .to_owned()
        } else {
            let nonce = crate::fsio::random_nonce()?;
            custody::publish(&request_path, &json!({"nonce":nonce}), None)?;
            nonce
        };
        let source = json!({"subject":ws.subject,"nonce":nonce,
            "key":{"keyId":key_id,"keyEpoch":new_epoch.to_string(),"algorithm":"1",
                "subject":ws.subject,"publicKey":hex(&named_public),
                "activeFrom":"0","activeUntil":u64::MAX.to_string(),"nextKeyDigest":digest}});
        let command = if let Some(identity) = &identity {
            let input = serde_json::to_vec(&source).map_err(|e| e.to_string())?;
            receipt_continuity::key_source(
                &root,
                &manifest,
                identity,
                receipt_continuity::KeySourceOperation::RotationCommand,
                &input,
            )?
        } else {
            author(
                &ws.host,
                &ws.socket,
                &ws.config,
                "subject-key-rotation",
                &source,
            )?
        };
        // A plan or assembly the Host REFUSES signed and submitted nothing: the
        // attempt is recorded refused, so a corrected request runs as a new
        // attempt instead of wedging behind an unresolved one. A transport
        // failure leaves it preparing (re-planning is pure).
        let refuse = |error: String, state: &Value| -> Result<Vec<u8>> {
            if error.starts_with("host refused") {
                let _ = custody::phase(&state_path, state, "refused")?;
            }
            Err(error)
        };
        let plan = match call(&ws.host, &ws.socket, &ws.config, 140, &command) {
            Ok(plan) => plan,
            Err(error) => return refuse(error, &state).map(|_| ()),
        };
        let plan_view = if let Some(identity) = &identity {
            let bytes = receipt_continuity::key_source(
                &root,
                &manifest,
                identity,
                receipt_continuity::KeySourceOperation::RotationPlan,
                &plan,
            )?;
            serde_json::from_slice(&bytes)
                .map_err(|e| format!("invalid local rotation inspection: {e}"))?
        } else {
            inspect_bytes(
                &ws.host,
                &ws.socket,
                &ws.config,
                "subject-key-rotation-plan",
                &plan,
            )?
        };
        check_rotation_plan(&plan_view, &command, identity.as_ref())?;
        let header = crate::decode_hex(
            plan_view
                .get("possessionHeader")
                .and_then(Value::as_str)
                .ok_or("rotation plan lacks possession header")?,
        )?;
        let signature = signer.sign(&header).to_bytes();
        let ingress = match call(
            &ws.host,
            &ws.socket,
            &ws.config,
            141,
            &pair(&plan, &signature)?,
        ) {
            Ok(ingress) => ingress,
            Err(error) => return refuse(error, &state).map(|_| ()),
        };
        custody::immutable(&ingress_path, &ingress)?;
    }
    let ingress = custody::bytes(&ingress_path, transport::HOST_MAX_FRAME)?;
    if state["phase"] == "preparing" {
        state["ingress"] = json!(hex(&ingress));
        let prior = custody::read(&state_path)?;
        state["phase"] = json!("prepared");
        custody::publish(&state_path, &state, Some(&prior))?;
    }
    if state["ingress"].as_str() != Some(hex(&ingress).as_str()) {
        return Err("retained rotation ingress changed".into());
    }
    let ticket = receipt_continuity::begin_attempt(&attempt)?;
    let recovered = state["phase"] != "prepared";
    let outcome = if state["outcome"].is_object() {
        state["outcome"].clone()
    } else {
        let frame = if state["phase"] == "prepared" {
            // Durable responsibility precedes the only semantic submission.
            state = custody::phase(&state_path, &state, "submitted")?;
            match call(&ws.host, &ws.socket, &ws.config, 142, &ingress) {
                Ok(frame) => frame,
                Err(error) if error.starts_with("host refused") => {
                    let _ = custody::phase(&state_path, &state, "refused")?;
                    return Err(error);
                }
                Err(_) => call(&ws.host, &ws.socket, &ws.config, 143, &ingress)?,
            }
        } else {
            // Even an absent/uncertain lookup cannot authorize a second effect.
            call(&ws.host, &ws.socket, &ws.config, 143, &ingress)?
        };
        let outcome = inspect_bytes(&ws.host, &ws.socket, &ws.config, "outcome", &frame)?;
        if outcome["type"] != "confirmed" {
            note_host_decision(HostDecision::Outcome(outcome));
            return Err(
                "retained rotation remains unconfirmed; original lookup only, no resubmission"
                    .into(),
            );
        }
        let prior = state.clone();
        state["outcome"] = outcome.clone();
        state["phase"] = json!("confirmed");
        custody::publish(&state_path, &state, Some(&prior))?;
        outcome
    };
    receipt_continuity::finish_attempt(ticket, &outcome, recovered)?;
    if named.is_none() {
        let original_daily = custody::bytes(&attempt.join("original-daily.key"), 32)?;
        let original_next = custody::bytes(&attempt.join("original-next.key"), 32)?;
        let after = custody::bytes(&after_path, 32)?;
        state = custody::phase(&state_path, &state, "installing")?;
        custody::install(&ws.key, Some(&original_daily), &original_next)?;
        let prior_destination = state["destinationPrior"]
            .as_str()
            .map(crate::decode_hex)
            .transpose()?;
        custody::install(&destination, prior_destination.as_deref(), &after)?;
        let after_public = key(&after_path)?.verifying_key().to_bytes();
        let prior_public = state["publicPrior"]
            .as_str()
            .map(crate::decode_hex)
            .transpose()?;
        custody::install(
            &conventional_next_public(&ws.key),
            prior_public.as_deref(),
            &after_public,
        )?;
        // KEY.pub and KEY.next.cosign are derived from the pair just installed: the
        // new daily key (the old next) and its new next key. Each is installed against
        // its retained prior, so a crash here is finished by the same retained attempt.
        let daily_public = key(&attempt.join("original-next.key"))?.verifying_key().to_bytes();
        custody::install(
            &conventional_public(&ws.key),
            retained_prior(&state, "dailyPublicPrior")?.as_deref(),
            &daily_public,
        )?;
        custody::install(
            &conventional_next_cosign(&ws.key),
            retained_prior(&state, "cosignPrior")?.as_deref(),
            &cosign(&daily_public, &key(&after_path)?),
        )?;
        let prior_manifest = state["manifestPrior"].clone();
        let mut updated = prior_manifest.clone();
        updated["prerotation"] = json!(true);
        updated["nextPublicKey"] = json!(hex(&after_public));
        custody::publish(
            &root.join("workspace.json"),
            &updated,
            Some(&prior_manifest),
        )?;
        state = custody::phase(&state_path, &state, "installed")?;
    }
    // Room publication is an independent fallible outcome; a refused recipient
    // trust gate cannot cause a second native rotation or erase successor keys.
    let rooms = if named.is_none() {
        workspace::roomkey::publish_rotation(&root, &new_epoch.to_string())
    } else {
        json!(null)
    };
    let result = json!({"type":"minidregg-key-rotation-result-v2","attempt":id,"completed":true,"replayed":recovered,
        "subject":ws.subject,"keyEpoch":new_epoch.to_string(),"keyId":key_id,"publicKey":hex(&signer_public),
        "nextKeyAt":destination,"outcome":outcome,"privateRooms":rooms});
    custody::publish(&attempt.join("result.json"), &result, None)?;
    let _ = custody::phase(&state_path, &state, "completed")?;
    eprintln!("{PREROTATION_NOTICE}");
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(|e| e.to_string())?
    );
    Ok(())
}

#[cfg(test)]
mod key_source_tests {
    use super::*;
    #[test]
    fn protected_rotation_requires_local_identity_command_and_frame_validation() {
        let identity = json!({"domain":"1","semantics":"2"});
        let view = json!({"type":"subject-key-rotation-plan-v1","domain":"1","semantics":"2",
            "commandBytes":"0102","possessionFrameValidated":true});
        check_rotation_plan(&view, &[1, 2], Some(&identity)).unwrap();
        for name in [
            "domain",
            "semantics",
            "commandBytes",
            "possessionFrameValidated",
        ] {
            let mut wrong = view.clone();
            wrong[name] = json!("different");
            assert!(check_rotation_plan(&wrong, &[1, 2], Some(&identity)).is_err());
        }
        let mut old = view.clone();
        old.as_object_mut()
            .unwrap()
            .remove("possessionFrameValidated");
        assert!(check_rotation_plan(&old, &[1, 2], Some(&identity))
            .unwrap_err()
            .contains("explicitly upgrade"));
        check_rotation_plan(&old, &[1, 2], None).unwrap();
    }

    /// The derived public files are checked against the secrets before a rotation:
    /// KEY.pub naming another key, or a co-signature over another pair, refuses.
    #[test]
    fn derived_public_priors_refuse_files_that_are_not_this_pair() {
        use std::os::unix::fs::DirBuilderExt;
        let dir = std::env::temp_dir().join(format!(
            "mini-rot-derived-{}-{}",
            std::process::id(),
            hex(&crate::fsio::random::<8>().unwrap())
        ));
        std::fs::DirBuilder::new().mode(0o700).create(&dir).unwrap();
        let daily = dir.join("k.key");
        let daily_signing = ed25519_dalek::SigningKey::from_bytes(&[7; 32]);
        let next_signing = ed25519_dalek::SigningKey::from_bytes(&[9; 32]);
        crate::create_private(&daily, &[7; 32]).unwrap();
        let daily_public = daily_signing.verifying_key().to_bytes();
        let next_public = next_signing.verifying_key().to_bytes();
        // Neither file: nothing to check, both priors absent (install creates them).
        assert_eq!(derived_public_priors(&daily, &next_public).unwrap(), (Value::Null, Value::Null));
        crate::create_public(&conventional_public(&daily), &next_public).unwrap();
        assert!(derived_public_priors(&daily, &next_public).is_err(), "KEY.pub of another key");
        fs::remove_file(conventional_public(&daily)).unwrap();
        crate::create_public(&conventional_public(&daily), &daily_public).unwrap();
        let other = ed25519_dalek::SigningKey::from_bytes(&[11; 32]);
        crate::create_public(&conventional_next_cosign(&daily), &cosign(&daily_public, &other)).unwrap();
        assert!(derived_public_priors(&daily, &next_public).is_err(), "co-signature over another pair");
        fs::remove_file(conventional_next_cosign(&daily)).unwrap();
        let good = cosign(&daily_public, &next_signing);
        crate::create_public(&conventional_next_cosign(&daily), &good).unwrap();
        assert_eq!(
            derived_public_priors(&daily, &next_public).unwrap(),
            (json!(hex(&daily_public)), json!(hex(&good)))
        );
        fs::remove_dir_all(&dir).unwrap();
    }
}
