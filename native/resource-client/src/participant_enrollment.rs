//! Sponsor-backed admission of one new signing principal. The source Host
//! chooses both canonical signing bytes; Rust retains them, signs the sponsor
//! header and the distinct raw possession frame, and never resubmits an
//! uncertain ingress. An admitted key conveys no resource grant.
//!
//! A *home identity* enrollment admits a principal whose key and subject
//! number belong to another Store (a selected-release owner, for example).
//! The sponsor plans with only the public key and the explicit home subject;
//! the principal signs the Host-chosen possession header in its own process
//! (`--action possess`); the sponsor seals with that detached signature. No
//! process ever holds both secrets.
//!
//! A *public-key* enrollment is the same custody for a participant of this
//! Store whose key never leaves their own machine: the sponsor plans from the
//! public key alone (`--new-public-key` without `--home-subject`, so the
//! subject is reserved here), hands the participant an offer (`--action
//! offer`), and seals with the signature `mini join` returns. `mini join` runs
//! on the participant's machine over `--remote`: it checks the offer against
//! the Host itself, signs the possession header, and later turns the sponsor's
//! welcome into a remote workspace.
use crate::agent_reserve::{bounded, digest, field, private_bytes, private_socket};
use ed25519_dalek::{Verifier, VerifyingKey};
use crate::participant_namespace::{self, IdKind, Role};
use crate::*;
use serde_json::{json, Value};
use std::os::unix::fs::DirBuilderExt;

const FORMAT: &str = "minidregg-participant-enrollment-custody-v1";
const COMMAND_KIND: &str = "participant-key-enrollment";
const PLAN_KIND: &str = "participant-key-enrollment-plan";
const INGRESS_KIND: &str = "participant-key-enrollment-ingress";
const LIMIT: usize = transport::HOST_MAX_FRAME - 1;

pub(crate) fn json_private(path: &Path) -> Result<Value> {
    serde_json::from_slice(&private_bytes(path, 256 * 1024)?).map_err(|error| {
        format!(
            "invalid private enrollment JSON {}: {error}",
            path.display()
        )
    })
}

pub(crate) fn member_path(value: &Value, key: &str) -> Result<PathBuf> {
    let path = PathBuf::from(field(value, key)?);
    if !path.is_absolute() {
        return Err(format!("enrollment {key} must be absolute"));
    }
    Ok(path)
}

pub(crate) fn decimal(value: &str, label: &str) -> Result<()> {
    if !mini_sdk::decimal::is_canonical_max(value, 80)
    {
        return Err(format!("{label} must be canonical decimal"));
    }
    Ok(())
}

fn identity_name(value: &str) -> Result<()> {
    if value.is_empty()
        || value.len() > 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
    {
        return Err("enrollment name must contain 1..64 ASCII letters, digits or hyphens".into());
    }
    Ok(())
}

pub(crate) use crate::fsio::read_secret_in_private_dir as key;

pub(crate) use mini_sdk::local::pair_nonempty as pair;

pub(crate) fn reply(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [byte @ (crate::RESPONSE_HOST_OUTCOME | crate::RESPONSE_NO_RECORD | crate::RESPONSE_NEVER_FORWARDED), encoded @ ..] => {
            note_host_decision(HostDecision::Frame {
                command: format!("enrollment op{operation}"),
                byte: *byte,
                encoded: encoded.to_vec(),
                decoded: None,
            });
            Err(format!(
                "enrollment Host refused op{operation}; exact frame retained"
            ))
        }
        [actual, body @ ..] if *actual == operation && !body.is_empty() => Ok(body),
        _ => Err(format!("Host op{operation} returned an invalid frame")),
    }
}

/// Whether an enrollment Host refusal is the Host's own `stale-root`, decoded
/// by the Host itself over the same session (op8 `inspect outcome`).
pub(crate) fn stale_refusal(
    host: &Path,
    socket: &Path,
    config: &Path,
    decision: Option<&HostDecision>,
) -> bool {
    match decision {
        Some(HostDecision::Frame { decoded: None, encoded, .. }) => {
            let kind = b"outcome";
            let mut payload = (kind.len() as u16).to_le_bytes().to_vec();
            payload.extend_from_slice(kind);
            payload.extend_from_slice(encoded);
            session_invoke(host, socket, config, mini_sdk::host_operations::INSPECT, &payload)
                .ok()
                .filter(|frame| frame.first() == Some(&8))
                .and_then(|frame| serde_json::from_slice::<Value>(&frame[1..]).ok())
                .is_some_and(|outcome| crate::replan::outcome_is_stale_root(&outcome))
        }
        decision => crate::replan::is_stale_root(decision),
    }
}

pub(crate) fn save_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    create_private(path, &bytes)?;
    Ok(())
}

pub(crate) fn retain_exact(path: &Path, bytes: &[u8]) -> Result<()> {
    crate::fsio::retain_exact(path, bytes, || {
        format!("retained enrollment source changed: {}", path.display())
    })?;
    Ok(())
}

pub(crate) fn save_json_staged(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    retain_exact(path, &bytes)
}

fn retained_request(directory: &Path, expected: &Value) -> Result<Value> {
    let path = directory.join("request.json");
    let request = if path.exists() {
        json_private(&path)?
    } else {
        if fs::read_dir(directory)
            .map_err(|error| error.to_string())?
            .filter_map(|entry| entry.ok())
            .any(|entry| entry.file_name() != "enrollment.lock")
        {
            return Err("enrollment attempt has artifacts but no durable request".into());
        }
        expected.clone()
    };
    for field_name in [
        "type",
        "name",
        "sponsor",
        "control",
        "factory",
        "observeCapability",
        "newPublicKey",
        "hostSha256",
        "configSha256",
    ] {
        pinned(&request, field_name, field(expected, field_name)?)?;
    }
    if request.get("homeSubject") != expected.get("homeSubject") {
        return Err("enrollment homeSubject pin changed".into());
    }
    decimal(field(&request, "nonce")?, "enrollment nonce")?;
    save_json_staged(&path, &request)?;
    Ok(request)
}

pub(crate) fn transform(
    host: &Path,
    _socket: &Path,
    config: &Path,
    operation: u8,
    kind: Option<&str>,
    input: &Path,
    output: &Path,
) -> Result<()> {
    let input = bounded(input, LIMIT)?;
    let mut payload = Vec::new();
    if let Some(kind) = kind {
        let length: u16 = kind.len().try_into().map_err(|_| "Host kind too long")?;
        payload.extend_from_slice(&length.to_le_bytes());
        payload.extend_from_slice(kind.as_bytes());
    }
    payload.extend_from_slice(&input);
    let frame_path = output.with_file_name(format!(
        "{}.frame",
        output
            .file_name()
            .ok_or("enrollment output lacks file name")?
            .to_string_lossy()
    ));
    let local = crate::client_consent::codec_frame(host, config, operation, &payload)?;
    let frame = if frame_path.exists() {
        let retained = bounded(&frame_path, transport::HOST_MAX_FRAME)?;
        if retained != local {
            return Err("retained enrollment codec frame differs from local native derivation".into());
        }
        retained
    } else {
        if output.exists() {
            return Err("enrollment output exists without its retained Host frame".into());
        }
        let frame = local;
        retain_exact(&frame_path, &frame)?;
        frame
    };
    let body = reply(&frame, operation)?;
    retain_exact(output, body)
}

pub(crate) fn inspect(
    host: &Path,
    socket: &Path,
    config: &Path,
    kind: &str,
    input: &Path,
    output: &Path,
) -> Result<Value> {
    transform(host, socket, config, mini_sdk::host_operations::INSPECT, Some(kind), input, output)?;
    serde_json::from_slice(&bounded(output, 8 * transport::HOST_MAX_FRAME)?)
        .map_err(|error| format!("invalid enrollment Host inspection: {error}"))
}

pub(crate) fn retained_frame(
    directory: &Path,
    stem: &str,
    frame: &[u8],
    operation: u8,
) -> Result<Vec<u8>> {
    retain_exact(&directory.join(format!("{stem}.frame")), frame)?;
    let body = reply(frame, operation)?.to_vec();
    retain_exact(&directory.join(format!("{stem}.bin")), &body)?;
    Ok(body)
}

pub(crate) fn staged_invoke(
    host: &Path,
    socket: &Path,
    config: &Path,
    directory: &Path,
    stem: &str,
    operation: u8,
    payload: &[u8],
) -> Result<Vec<u8>> {
    let frame_path = directory.join(format!("{stem}.frame"));
    let local_codec = matches!(operation, 7 | 8 | 9 | 10 | 11);
    let frame = if frame_path.exists() {
        let retained = bounded(&frame_path, transport::HOST_MAX_FRAME)?;
        if local_codec {
            let current = crate::client_consent::codec_frame(host, config, operation, payload)?;
            if current != retained {
                return Err("retained enrollment codec frame differs from local native derivation".into());
            }
        }
        if operation == 86 || operation == 92 {
            let current =
                session_invoke(host, socket, config, operation, payload).map_err(|error| {
                    format!("retained enrollment plan is stale against the moved source: {error}; `--action plan` with this exact --dir plans the same request again")
                })?;
            if current != retained {
                return Err("retained enrollment plan differs from the current source image; `--action plan` with this exact --dir plans the same request again".into());
            }
        }
        retained
    } else {
        if directory.join(format!("{stem}.bin")).exists() {
            return Err("enrollment body exists without its retained Host frame".into());
        }
        if local_codec {
            crate::client_consent::codec_frame(host, config, operation, payload)?
        } else {
            session_invoke(host, socket, config, operation, payload)?
        }
    };
    retained_frame(directory, stem, &frame, operation)
}

pub(crate) fn pinned(value: &Value, key: &str, expected: &str) -> Result<()> {
    if field(value, key)? != expected {
        return Err(format!("enrollment {key} pin changed"));
    }
    Ok(())
}

struct Pin {
    host: PathBuf,
    config: PathBuf,
    public_socket: PathBuf,
    operation_socket: PathBuf,
    sponsor_key: PathBuf,
    /// `None` for a home-identity enrollment: the new secret never enters
    /// this process and possession arrives as a detached signature.
    new_key: Option<PathBuf>,
    subject: String,
    key_id: String,
    public_key: String,
    plan: Vec<u8>,
    command: Vec<u8>,
    /// The committed next key and its co-signature (both empty without one).
    next_public: Vec<u8>,
    next_cosign: Vec<u8>,
    /// The name's namespace reservation this plan holds (released only on a decided no-record refusal).
    reservation: participant_namespace::Reservation,
    /// The observation height the plan's sponsor deadline is pinned to (`pin-enrollment-plan-height`),
    /// or `None` when the Host that planned it had no pin (the unpinned plan is accepted as before).
    pinned_at: Option<String>,
}

/// The pinned form of an enrollment plan: the Host's `pin-enrollment-plan-height PLAN HEIGHT OUT`
/// moves only the sponsor header's deadline to `height` (Kernel/NativePlanHeight
/// `pinEnrollment_only_sponsor_deadline`), the height of the observation the plan was made over,
/// so the local consent provider re-derives the same pinned bytes (`NativeSpecializedConsent.
/// pinnedExpectedBytes`) and the plan is accepted at that height, however many ticks later it is
/// sealed and submitted. `Ok(None)`: this Host has no such verb (older image); the plan stays
/// unpinned and is accepted exactly as before.
fn pin_plan_height(host: &Path, config: &Path, plan: &Path, height: &str, output: &Path) -> Result<Option<Vec<u8>>> {
    decimal(height, "observation height")?;
    let arguments = [
        OsStr::new("pin-enrollment-plan-height"), plan.as_os_str(), OsStr::new(height), output.as_os_str(),
    ];
    // The Host writes OUTPUT under the inherited umask; custody bytes are
    // owner-private whatever the caller's shell umask (a root shell's 022 left
    // it group-readable and `private_bytes` refused it).
    // SAFETY: umask has no preconditions; it is restored right after the call.
    let previous = unsafe { libc::umask(0o077) };
    let pinned = crate::local_process(host, config, &arguments);
    unsafe { libc::umask(previous) };
    match pinned {
        Ok(_) => Ok(Some(private_bytes(output, LIMIT)?)),
        // A Host without the verb answers an unknown subcommand with its own verb listing
        // (`minidregg-host CONFIG.json profile|describe|...`) and exit 1; a Host that has the verb
        // and refused prints its refusal, never the listing.
        Err(error) if error.contains("minidregg-host CONFIG.json ") && !error.contains("pin-enrollment-plan-height") => Ok(None),
        Err(error) => Err(format!("pin-enrollment-plan-height: {error}")),
    }
}

/// The height of the factory observation retained under `directory` (`Challenge.height`, the
/// height the signer saw).
fn observation_height(directory: &Path) -> Result<String> {
    let challenge = json_private(&directory.join("observation/challenge.json"))?;
    Ok(field(&challenge, "height")?.to_owned())
}

/// The marker a `submit` leaves when the Host refused the sealed plan with NO RECORD (253): the
/// attempt is definitely unadmitted, its namespace binding released, and the next `plan` in this
/// directory retires it and observes again under the same request and reservation.
const SUBMIT_REFUSED: &str = "submit-refused.json";

fn refused_pending(directory: &Path) -> Result<()> {
    if directory.join(SUBMIT_REFUSED).exists() {
        return Err(format!(
            "this plan was refused by the Host with no record (see {}); plan again with `--action plan` and this exact --dir (the same request and reservation) before anything else",
            directory.join(SUBMIT_REFUSED).display()
        ));
    }
    Ok(())
}

/// The plan custody `plan` prints: the same for the plan that was just validated and for a
/// retained plan a later `plan` resumes.
fn plan_custody(subject: &str, key_id: &str, public_key: &str, plan_view: &Value) -> Value {
    json!({"type":"minidregg-participant-enrollment-plan-custody-v1",
        "subject":subject,"keyId":key_id,
        "publicKey":public_key,"plan":plan_view,"authority":"candidate-only"})
}

/// Whether a retained plan is still the Host's plan over the current source: the Host plans the
/// retained observation and command again (op 86) and answers the exact retained frame. A moved
/// source (any commit since the observation) answers a refusal or another plan: the retained plan
/// could not be sealed (the consent provider prepares the same plan over its admitted source and
/// refuses) and is dead.
fn retained_plan_is_current(directory: &Path, pin: &Pin) -> Result<bool> {
    let retained = bounded(&directory.join("plan.frame"), transport::HOST_MAX_FRAME)?;
    let observation = private_bytes(&directory.join("observation/signed-observation.bin"), LIMIT)?;
    let request = pair(&observation, &pin.command)?;
    let current = session_invoke(&pin.host, &pin.operation_socket, &pin.config, mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_PLAN, &request);
    let _ = take_host_decision();
    if current.as_ref().is_ok_and(|frame| *frame == retained) {
        return Ok(true);
    }
    // A pinned plan outlives the source it was planned over: once a commit lands, the Host no longer
    // plans over the retained observation (it refuses it with no record), so the Host cannot vouch
    // for it. The authority is the one `seal` asks before it signs: the local consent provider
    // re-derives the plan at the observation's height and accepts the exact or the pinned form
    // (`NativeSpecializedConsent.checkExactOrPinned`). It judges, it signs nothing. Accepted: the
    // plan is resumed; refused: it is dead and re-planned under the same request.
    if pin.pinned_at.is_none() {
        return Ok(false);
    }
    match crate::client_consent::operator_plan(&pin.host, &pin.config, mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_PLAN, &request, &pin.plan) {
        Ok(()) => Ok(true),
        Err(_) => {
            let _ = crate::client_consent::take_stale_observation();
            Ok(false)
        }
    }
}

/// The next free `replanned/NN` of a directory.
fn next_retirement(directory: &Path) -> Result<u32> {
    let parent = directory.join(crate::replan::REPLANNED);
    if !parent.exists() {
        return Ok(1);
    }
    let mut number = 1;
    while parent.join(format!("{number:02}")).exists() {
        number += 1;
    }
    Ok(number)
}

/// A home identity keeps its origin subject number, so only the Store-local
/// key id is reserved; the Host still refuses any subject already present.
fn enrollment_roles(home: bool) -> Vec<Role> {
    let mut roles = Vec::new();
    if !home {
        roles.push(Role {
            label: "subject".into(),
            kind: IdKind::Subject,
        });
    }
    roles.push(Role {
        label: "keyId".into(),
        kind: IdKind::Key,
    });
    roles
}

fn cosign_file(path: &Path) -> Result<[u8; 64]> {
    bounded(path, 64)?
        .try_into()
        .map_err(|_| format!("the co-signature {} must contain exactly 64 raw bytes", path.display()))
}

/// `mini enroll --action cosign --key KEY [--next-key NEXT] [--output FILE]`
/// (or `--public-key PUB` in place of `--key`): the next key's co-signature of
/// the pair (KEY's public key, NEXT's public key), written to FILE (default
/// KEY.next.cosign) and printed with both public keys -- the three hex lines a
/// sponsor's `enroll plan` takes. Run by whoever holds NEXT.
fn cosign_action(mut args: Args) -> Result<()> {
    let key_path = args.optional("key").map(|value| absolute(&path(value))).transpose()?;
    let public_path = args.optional("public-key").map(|value| absolute(&path(value))).transpose()?;
    let next_path = args.optional("next-key").map(|value| absolute(&path(value))).transpose()?;
    let output = args.optional("output").map(|value| absolute(&path(value))).transpose()?;
    args.finish()?;
    let (public, default_next, default_output) = match (&key_path, &public_path) {
        (Some(secret), None) => {
            let mut next = secret.as_os_str().to_owned();
            next.push(".next");
            (key(secret)?.verifying_key().to_bytes(), Some(PathBuf::from(next)),
                Some(crate::key_rotation::conventional_next_cosign(secret)))
        }
        (None, Some(public)) => (public_key_file(public)?.to_bytes(), None, None),
        _ => return Err("cosign takes --key KEY or --public-key PUB".into()),
    };
    let next_path = next_path.or(default_next).ok_or("cosign needs --next-key NEXT")?;
    let next = key(&next_path)?;
    let output = output.or(default_output).ok_or("cosign with --public-key needs --output")?;
    let signature = crate::key_rotation::cosign(&public, &next);
    let next_public = next.verifying_key().to_bytes();
    crate::key_rotation::verify_cosign(&public, &next_public, &signature)?;
    match bounded(&output, 64) {
        Ok(existing) if existing == signature => {}
        Ok(_) => return Err(format!("{} already holds another co-signature", output.display())),
        Err(_) => crate::create_public(&output, &signature)?,
    }
    print_json(&json!({"type":"minidregg-next-key-cosign-v1","publicKey":hex(&public),
        "nextPublicKey":hex(&next_public),"cosign":hex(&signature),"cosignAt":utf8_path(&output)?,
        "next":"give your sponsor nextPublicKey and cosign: `enroll plan NAME KEYFILE NEXT-PUB COSIGN`"}))
}

fn public_key_file(path: &Path) -> Result<VerifyingKey> {
    let bytes: [u8; 32] = bounded(path, 32)?
        .try_into()
        .map_err(|_| "enrollment public key must contain exactly 32 raw bytes")?;
    VerifyingKey::from_bytes(&bytes).map_err(|_| "enrollment public key is not a valid Ed25519 point".into())
}

/// The plan the custody signs: the pinned form when the Host pinned it (`pin-enrollment-plan-height`),
/// else the Host's plan as answered. Every reader of the signed plan goes through this one name.
fn plan_file(pinned_at: Option<&str>) -> &'static str {
    if pinned_at.is_some() { "plan-pinned.bin" } else { "plan.bin" }
}

fn load_pin(directory: &Path) -> Result<Pin> {
    crate::fsio::ensure_private_dir(directory)?;
    let pin = json_private(&directory.join("pin.json"))?;
    pinned(&pin, "format", FORMAT)?;
    let host = member_path(&pin, "host")?;
    let config = member_path(&pin, "config")?;
    let public_socket = member_path(&pin, "publicSocket")?;
    let operation_socket = member_path(&pin, "operationSocket")?;
    let sponsor_key = member_path(&pin, "sponsorKey")?;
    let home = pin.get("homeSubject").and_then(Value::as_bool) == Some(true);
    let new_key = if pin.get("newKey").is_some_and(Value::is_null) {
        None
    } else if home {
        return Err("home-identity enrollment pin must not name a new secret key".into());
    } else {
        Some(member_path(&pin, "newKey")?)
    };
    let namespace_root = member_path(&pin, "namespaceRoot")?;
    if pin.get("operatorOnly").and_then(Value::as_bool) == Some(true) {
        private_socket(&operation_socket)?;
    } else if operation_socket != public_socket {
        return Err("public enrollment operation socket differs from sponsor workspace".into());
    }
    pinned(&pin, "hostSha256", &host_image_sha256(&host)?)?;
    pinned(&pin, "configSha256", &digest(&bounded(&config, 65_536)?))?;
    let request_bytes = private_bytes(&directory.join("request.json"), 256 * 1024)?;
    pinned(&pin, "requestSha256", &digest(&request_bytes))?;
    let request: Value =
        serde_json::from_slice(&request_bytes).map_err(|error| error.to_string())?;
    pinned(&request, "hostSha256", field(&pin, "hostSha256")?)?;
    pinned(&request, "configSha256", field(&pin, "configSha256")?)?;
    let command = private_bytes(&directory.join("command.bin"), LIMIT)?;
    let pinned_at = match pin.get("pinnedAtHeight") {
        Some(Value::String(height)) => Some(height.clone()),
        _ => None,
    };
    let plan = private_bytes(&directory.join(plan_file(pinned_at.as_deref())), LIMIT)?;
    pinned(&pin, "commandSha256", &digest(&command))?;
    pinned(&pin, "planSha256", &digest(&plan))?;
    let name = field(&pin, "name")?;
    let sponsor = field(&pin, "sponsor")?;
    let subject = field(&pin, "subject")?.to_owned();
    let key_id = field(&pin, "keyId")?.to_owned();
    let public_key = field(&pin, "publicKey")?.to_owned();
    if field(&request, "name")? != name
        || field(&request, "sponsor")? != sponsor
        || field(&request, "newPublicKey")? != public_key
    {
        return Err("enrollment request changed after namespace reservation".into());
    }
    let config_json: Value =
        serde_json::from_slice(&bounded(&config, 65_536)?).map_err(|error| error.to_string())?;
    let domain = config_json
        .get("domain")
        .and_then(|value| {
            value
                .as_str()
                .map(str::to_owned)
                .or_else(|| value.as_u64().map(|number| number.to_string()))
        })
        .ok_or("enrollment config lacks deployment domain")?;
    let roles = enrollment_roles(home);
    let reservation = participant_namespace::reserve(
        &namespace_root,
        &domain,
        sponsor,
        name,
        &request_bytes,
        &roles,
    )?;
    pinned(&pin, "reservationDigest", &reservation.request_digest)?;
    let reserved_subject = if home {
        field(&request, "homeSubject")?
    } else {
        reservation.ids["subject"].as_str()
    };
    if reserved_subject != subject
        || reservation.ids["keyId"] != key_id
        || member_path(&pin, "reservationRecord")? != reservation.record_path
    {
        return Err("enrollment namespace reservation changed".into());
    }
    participant_namespace::bind_attempt(&reservation, directory, &digest(&command))?;
    let next_public = match request.get("nextPublicKey").and_then(Value::as_str) {
        Some(text) => mini_sdk::hex::decode(text).map_err(|e| e.0)?,
        None => Vec::new(),
    };
    let next_cosign = match request.get("nextCosign").and_then(Value::as_str) {
        Some(text) => mini_sdk::hex::decode(text).map_err(|e| e.0)?,
        None => Vec::new(),
    };
    if next_public.is_empty() != next_cosign.is_empty() {
        return Err("enrollment request names a next key without its co-signature".into());
    }
    Ok(Pin {
        next_public,
        next_cosign,
        host,
        config,
        public_socket,
        operation_socket,
        sponsor_key,
        new_key,
        subject,
        key_id,
        public_key,
        plan,
        command,
        reservation,
        pinned_at,
    })
}

/// A sponsor-signed factory resource observation retained under `directory`.
/// Returns the exact signed observation and the factory and authority roots it
/// observed. Every Host frame is retained before its body is used.
pub(crate) struct FactoryObservation<'a> {
    pub(crate) host: &'a Path,
    pub(crate) socket: &'a Path,
    pub(crate) config: &'a Path,
    pub(crate) directory: &'a Path,
    pub(crate) sponsor: &'a str,
    pub(crate) nonce: &'a str,
    pub(crate) factory: &'a str,
    pub(crate) observe: &'a str,
}

pub(crate) fn signed_factory_observation(
    input: &FactoryObservation<'_>,
    signing: &SigningKey,
) -> Result<(Vec<u8>, String, String)> {
    let query = json!({"subject":input.sponsor,"nonce":input.nonce,
        "purpose":{"type":"query","kind":"object","target":input.factory,"view":"resource"},
        "grants":[{"kind":"object","target":input.factory,"capability":input.observe}]});
    save_json_staged(&input.directory.join("query.json"), &query)?;
    transform(
        input.host,
        input.socket,
        input.config,
        mini_sdk::host_operations::AUTHOR,
        Some("intent"),
        &input.directory.join("query.json"),
        &input.directory.join("query.bin"),
    )?;
    let query_bytes = fs::read(input.directory.join("query.bin")).map_err(|e| format!("cannot read enrollment intent: {e}"))?;
    crate::client_consent::intent(input.host, input.config, &query_bytes, signing.verifying_key().as_bytes())?;
    let observation = input.directory.join("observation");
    match fs::DirBuilder::new().mode(0o700).create(&observation) {
        Ok(()) => (),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            crate::fsio::ensure_private_dir(&observation)?;
        }
        Err(error) => return Err(format!("cannot create enrollment observation: {error}")),
    }
    // Op 4 is authenticated before the Host reads the factory: the intent's bytes
    // and the sponsor's signature over them, in the session's pair framing.
    let intent_signature = signing.sign(&query_bytes).to_bytes();
    let intent_signature_path = observation.join("intent-signature.bin");
    retain_exact(&intent_signature_path, &intent_signature)?;
    let length: u32 = query_bytes.len().try_into().map_err(|_| "factory intent too large")?;
    let mut request = length.to_le_bytes().to_vec();
    request.extend_from_slice(&query_bytes);
    request.extend_from_slice(&intent_signature);
    let challenge = staged_invoke(
        input.host,
        input.socket,
        input.config,
        &observation,
        "challenge",
        mini_sdk::host_operations::OBSERVATION_CHALLENGE,
        &request,
    )?;
    let challenge_json = inspect(
        input.host,
        input.socket,
        input.config,
        "challenge",
        &observation.join("challenge.bin"),
        &observation.join("challenge.json"),
    )?;
    let challenge_bin = fs::read(observation.join("challenge.bin")).map_err(|e| format!("cannot read enrollment challenge: {e}"))?;
    let headers = crate::client_consent::observation(input.host, input.config,
        &query_bytes, &intent_signature, &challenge_bin, signing.verifying_key().as_bytes())?;
    if headers.is_empty() {
        return Err("factory observation has no signing header".into());
    }
    let signatures = sign_headers(signing, &headers)?;
    save_json_staged(&observation.join("signatures.json"), &signatures)?;
    transform(
        input.host,
        input.socket,
        input.config,
        mini_sdk::host_operations::SIGNATURES,
        None,
        &observation.join("signatures.json"),
        &observation.join("signatures.bin"),
    )?;
    let signature_bytes = private_bytes(&observation.join("signatures.bin"), 4096)?;
    let signed = staged_invoke(
        input.host,
        input.socket,
        input.config,
        &observation,
        "signed-observation",
        mini_sdk::host_operations::OBSERVATION_ASSEMBLE,
        &pair(&challenge, &signature_bytes)?,
    )?;
    let _view = staged_invoke(
        input.host,
        input.socket,
        input.config,
        &observation,
        "view",
        mini_sdk::host_operations::AUTHORIZED_QUERY,
        &signed,
    )?;
    let view_json = inspect(
        input.host,
        input.socket,
        input.config,
        "view-resource",
        &observation.join("view.bin"),
        &observation.join("view.json"),
    )?;
    pinned(&view_json, "type", "resource")?;
    let factory_root = view_json
        .get("cell")
        .and_then(|cell| cell.get("root"))
        .and_then(Value::as_str)
        .ok_or("signed factory view lacks root")?;
    decimal(factory_root, "factory root")?;
    let authority_root = challenge_json
        .get("authorityRoot")
        .and_then(Value::as_str)
        .ok_or("signed factory challenge lacks authority root")?;
    decimal(authority_root, "authority root")?;
    Ok((signed, factory_root.to_owned(), authority_root.to_owned()))
}

fn plan(mut args: Args) -> Result<()> {
    let workspace = absolute(&path(args.required("sponsor-workspace")?))?;
    let factory_name = args
        .required("factory-ref")?
        .into_string()
        .map_err(|_| "factory reference name must be UTF-8")?;
    let name = args
        .required("name")?
        .into_string()
        .map_err(|_| "enrollment name must be UTF-8")?;
    let new_key = args
        .optional("new-key")
        .map(|value| absolute(&path(value)))
        .transpose()?;
    let new_public = args
        .optional("new-public-key")
        .map(|value| absolute(&path(value)))
        .transpose()?;
    let home_subject = args
        .optional("home-subject")
        .map(|value| {
            value
                .into_string()
                .map_err(|_| "home subject must be UTF-8".to_owned())
        })
        .transpose()?;
    let home = match (&new_key, &new_public, &home_subject) {
        (Some(_), None, None) | (None, Some(_), None) => false,
        (None, Some(_), Some(subject)) => {
            decimal(subject, "home subject")?;
            true
        }
        _ => {
            return Err(
                "enrollment takes either --new-key, or --new-public-key [--home-subject N]".into(),
            )
        }
    };
    // Pre-rotation is the default: the enrolled record commits to the digest of
    // the principal's NEXT public key (keygen writes it at KEY.next.pub). Only
    // an explicit --no-prerotation enrolls a key that can never rotate.
    let next_public_arg = args
        .optional("next-public-key")
        .map(|value| absolute(&path(value)))
        .transpose()?;
    let without_prerotation = args.optional("no-prerotation").is_some();
    let next_public_path = match (next_public_arg, without_prerotation, &new_key) {
        (Some(_), true, _) => {
            return Err("--next-public-key and --no-prerotation exclude each other".into())
        }
        (Some(explicit), false, _) => Some(explicit),
        (None, true, _) => None,
        (None, false, Some(secret)) => {
            let conventional = crate::key_rotation::conventional_next_public(secret);
            if !conventional.is_file() {
                return Err(format!(
                    "enrollment commits to a next key by default: {} is missing (make keys with `mini keygen`), pass --next-public-key, or --no-prerotation to enroll a key that can never rotate",
                    conventional.display()
                ));
            }
            Some(conventional)
        }
        (None, false, None) => {
            return Err("a home-identity enrollment needs --next-public-key or --no-prerotation".into())
        }
    };
    let next_public = next_public_path
        .as_deref()
        .map(public_key_file)
        .transpose()?
        .map(|key| key.to_bytes());
    // FIX-IDENTITY: the committed next key co-signs (Kernel enrollGate). The
    // co-signature comes from whoever holds the next key: `mini keygen` wrote it
    // at KEY.next.cosign, `mini enroll --action cosign` makes it again.
    let next_cosign_arg = args
        .optional("next-cosign")
        .map(|value| absolute(&path(value)))
        .transpose()?;
    let next_cosign: Option<[u8; 64]> = match (&next_public, next_cosign_arg, &new_key) {
        (None, Some(_), _) => return Err("--next-cosign needs a next key (not --no-prerotation)".into()),
        (None, None, _) => None,
        (Some(_), Some(file), _) => Some(cosign_file(&file)?),
        (Some(_), None, Some(secret)) => {
            let conventional = crate::key_rotation::conventional_next_cosign(secret);
            if !conventional.is_file() {
                return Err(format!(
                    "the next key must co-sign this enrollment: {} is missing; whoever holds the next key runs `mini enroll --action cosign --key KEY --next-key NEXT` and passes --next-cosign",
                    conventional.display()
                ));
            }
            Some(cosign_file(&conventional)?)
        }
        (Some(_), None, None) => {
            return Err("a public-key enrollment with a next key needs --next-cosign (the newcomer's `mini join --key` prints it)".into())
        }
    };
    let operator_override = args
        .optional("operator-socket")
        .map(path)
        .map(|value| absolute(&value))
        .transpose()?;
    let directory = absolute(&path(args.required("dir")?))?;
    args.finish()?;
    identity_name(&factory_name)?;
    identity_name(&name)?;
    let workspace_pin = json_private(&workspace.join("workspace.json"))?;
    pinned(&workspace_pin, "type", "minidregg-participant-workspace-v1")?;
    let factory = json_private(&workspace.join("refs").join(format!("{factory_name}.json")))?;
    pinned(&factory, "type", "minidregg-participant-reference-v1")?;
    pinned(&factory, "name", &factory_name)?;
    pinned(&factory, "kind", "object")?;
    let host = member_path(&workspace_pin, "host")?;
    let config = member_path(&workspace_pin, "config")?;
    let public_socket = member_path(&workspace_pin, "socket")?;
    let sponsor_key = member_path(&workspace_pin, "key")?;
    let namespace_root = member_path(&workspace_pin, "namespaceRoot")?;
    let operation_socket = operator_override
        .clone()
        .unwrap_or_else(|| public_socket.clone());
    if operator_override.is_some() {
        private_socket(&operation_socket)?;
    }
    let sponsor = field(&workspace_pin, "subject")?.to_owned();
    let control = field(&factory, "controlCapability")?.to_owned();
    let observe = field(&factory, "observeCapability")?.to_owned();
    let factory_target = field(&factory, "target")?.to_owned();
    for (value, label) in [
        (&sponsor, "sponsor"),
        (&control, "factory control capability"),
        (&observe, "factory observe capability"),
        (&factory_target, "factory target"),
    ] {
        decimal(value, label)?;
    }
    let config_bytes = bounded(&config, 65_536)?;
    let config_json: Value =
        serde_json::from_slice(&config_bytes).map_err(|error| error.to_string())?;
    let deployed_factory = config_json
        .get("factoryId")
        .and_then(|value| {
            value
                .as_str()
                .map(str::to_owned)
                .or_else(|| value.as_u64().map(|number| number.to_string()))
        })
        .ok_or("deployed config lacks factoryId")?;
    let deployment_domain = config_json
        .get("domain")
        .and_then(|value| {
            value
                .as_str()
                .map(str::to_owned)
                .or_else(|| value.as_u64().map(|number| number.to_string()))
        })
        .ok_or("deployed config lacks domain")?;
    if factory_target != deployed_factory {
        return Err("factory reference differs from deployed factory".into());
    }
    let sponsor_signing = key(&sponsor_key)?;
    let public_key = match (&new_key, &new_public) {
        (Some(secret), _) => hex(&key(secret)?.verifying_key().to_bytes()),
        (None, Some(public)) => hex(&public_key_file(public)?.to_bytes()),
        _ => unreachable!("enrollment key inputs validated above"),
    };
    if public_key == hex(&sponsor_signing.verifying_key().to_bytes()) {
        return Err("enrolled key must differ from the sponsor key".into());
    }
    match fs::DirBuilder::new().mode(0o700).create(&directory) {
        Ok(()) => (),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            crate::fsio::ensure_private_dir(&directory)?;
        }
        Err(error) => return Err(format!("cannot create enrollment attempt: {error}")),
    }
    let _lock = transport::service_lock(&directory.join("enrollment.lock"))?;
    if directory.join(SUBMIT_REFUSED).exists() {
        // The sealed plan was refused with no record (`submit`): definitely unadmitted, its binding
        // released. Everything but the request, the retained config and the lock retires under
        // replanned/NN, and the plan below observes again under the SAME request and reservation.
        let number = next_retirement(&directory)?;
        let retired = crate::replan::retire(&directory, number, &["request.json", "config.json", "enrollment.lock"])?;
        eprintln!(
            "mini: enroll plan: the previous plan was refused by the Host with no record; it is retired at {} and this request is planned again",
            retired.display()
        );
    }
    if directory.join("submit-marker.json").exists() {
        return Err(
            "enrollment may have been submitted; use --action lookup with this exact --dir".into(),
        );
    }
    if (directory.join("seal.json").exists() || directory.join("ingress.bin").exists()) && !directory.join("pin.json").exists() {
        return Err(
            "enrollment already sealed; use --action submit or lookup with this exact --dir".into(),
        );
    }
    let request_nonce = if directory.join("request.json").exists() {
        field(&json_private(&directory.join("request.json"))?, "nonce")?.to_owned()
    } else {
        crate::fsio::random_nonce()?
    };
    let mut expected_request = json!({"type":"minidregg-participant-enrollment-request-v1",
        "name":name,"sponsor":sponsor,"control":control,"factory":factory_target,
        "observeCapability":observe,"newPublicKey":public_key,
        "nonce":request_nonce,"hostSha256":host_image_sha256(&host)?,
        "configSha256":digest(&config_bytes)});
    if let Some(subject) = &home_subject {
        if *subject == sponsor {
            return Err("home subject equals the sponsor subject".into());
        }
        expected_request["homeSubject"] = json!(subject);
    }
    if let Some(next) = &next_public {
        if hex(next) == public_key {
            return Err("the next key must differ from the key being enrolled".into());
        }
        let cosign = next_cosign.ok_or("a next key without its co-signature")?;
        let enrolled: [u8; 32] = mini_sdk::hex::decode(&public_key).map_err(|e| e.0)?
            .try_into()
            .map_err(|_| "enrolled public key is not 32 bytes")?;
        crate::key_rotation::verify_cosign(&enrolled, next, &cosign)?;
        expected_request["nextPublicKey"] = json!(hex(next));
        expected_request["nextCosign"] = json!(hex(&cosign));
    }
    let request = retained_request(&directory, &expected_request)?;
    if directory.join("pin.json").exists() {
        // A validated plan is retained here and holds this name's namespace reservation. While it is
        // still the Host's plan over the current source it is RESUMED, never planned again (a second
        // request would strand that reservation): the same custody is printed and the next step
        // named. Once the source has moved under it (a tick, a certify: any commit stales the
        // signed observation it was planned over, and the consent provider refuses to sign it), the
        // plan is definitely dead and nothing of it was submitted, so it retires under replanned/NN,
        // its binding is released, and the SAME request (nonce, reservation, identity) is planned
        // again below. A home-identity member then signs possession over the new plan.
        let pin = load_pin(&directory)?;
        let plan_view = json_private(&directory.join("plan.json"))?;
        validate_plan(&plan_view, &pin.command, &pin.plan)?;
        if retained_plan_is_current(&directory, &pin)? {
            if directory.join("seal.json").exists() || directory.join("ingress.bin").exists() {
                return Err("enrollment already sealed; use --action submit or lookup with this exact --dir".into());
            }
            let next = if pin.new_key.is_some() {
                "`--action seal`, then `--action submit`"
            } else {
                "`--action offer` (the member signs possession with `mini join --sponsor-plan`), `--action seal --possession-signature`, then `--action submit`"
            };
            eprintln!(
                "mini: enroll plan: a validated plan is retained at {}; nothing is planned again. Continue with {next}, all with this exact --dir",
                directory.display()
            );
            return print_json(&plan_custody(&pin.subject, &pin.key_id, &pin.public_key, &plan_view));
        }
        participant_namespace::release_attempt(&pin.reservation, &directory)?;
        let number = next_retirement(&directory)?;
        let retired = crate::replan::retire(&directory, number, &["request.json", "config.json", "enrollment.lock"])?;
        eprintln!(
            "mini: enroll plan: the retained plan is stale against the moved source (a tick or certify since it was planned; nothing of it was submitted); it is retired at {} and the same request is planned again",
            retired.display()
        );
    } else if directory.join("plan.frame").exists() {
        // A plan that never validated (no pin.json: the process ended between the Host's plan and
        // the binding) reserved nothing and binds nothing; it retires and the request is planned again.
        let number = next_retirement(&directory)?;
        crate::replan::retire(&directory, number, &["request.json", "config.json", "enrollment.lock"])?;
    }
    let roles = enrollment_roles(home);
    let request_bytes = private_bytes(&directory.join("request.json"), 256 * 1024)?;
    // The name's reservation may already be a retained plan's, in another directory: that plan is
    // resumed there, never planned again here (one request, one reservation, one identity).
    if let Some(bound) = participant_namespace::bound_attempt(&namespace_root, &deployment_domain, &sponsor, &name)? {
        let here = fs::canonicalize(directory.parent().ok_or("enrollment attempt lacks parent")?)
            .map_err(|error| error.to_string())?
            .join(directory.file_name().ok_or("enrollment attempt lacks filename")?);
        if bound != here {
            return Err(format!(
                "enrollment {name} is already planned at {bound}; resume it there (`mini enroll --action offer|seal|submit --dir {bound}`): a second plan is never made, the name's namespace reservation is that plan's",
                bound = bound.display()
            ));
        }
    }
    let reservation = participant_namespace::reserve(
        &namespace_root,
        &deployment_domain,
        &sponsor,
        &name,
        &request_bytes,
        &roles,
    )?;
    let subject = match &home_subject {
        Some(subject) => subject.clone(),
        None => reservation.ids["subject"].clone(),
    };
    retain_exact(&directory.join("config.json"), &config_bytes)?;
    let retained_config = directory.join("config.json");
    // The factory observation, the command over its roots and the Plan are one
    // re-plannable unit: nothing is bound or submitted until the Plan is
    // validated, so a Host stale-root (a tick, certify or write between the
    // observation and its use) retires them under replanned/ and observes again.
    let (command, plan, plan_view, pinned_at) = crate::replan::replan(
        "enroll plan",
        || {
            let (signed, factory_root, authority_root) = signed_factory_observation(
                &FactoryObservation {
                    host: &host,
                    socket: &public_socket,
                    config: &retained_config,
                    directory: &directory,
                    sponsor: &sponsor,
                    nonce: field(&request, "nonce")?,
                    factory: &factory_target,
                    observe: &observe,
                },
                &sponsor_signing,
            )?;
            let factory_root = factory_root.as_str();
            let authority_root = authority_root.as_str();
            if let Some(next) = &next_public {
                let enrolled: [u8; 32] = mini_sdk::hex::decode(&public_key).map_err(|e| e.0)?
                    .try_into().map_err(|_| "enrolled public key is not 32 bytes")?;
                crate::key_rotation::host_next_possession_frame(
                    &host, &public_socket, &retained_config, &enrolled, next)?;
            }
            let next_key_digest = match &next_public {
                Some(next) => json!(crate::key_rotation::next_key_digest(
                    &host, &public_socket, &retained_config, next
                )?),
                None => Value::Null,
            };
            let command_source = json!({"sponsor":sponsor,"control":control,
                "nonce":field(&request,"nonce")?,"expectedFactoryRoot":factory_root,
                "expectedAuthorityRoot":authority_root,
                "key":{"keyId":reservation.ids["keyId"],"keyEpoch":"1","algorithm":"1",
                    "subject":subject,"publicKey":public_key,
                    "activeFrom":"0","activeUntil":u64::MAX.to_string(),
                    "nextKeyDigest":next_key_digest}});
            save_json_staged(&directory.join("source.json"), &command_source)?;
            transform(
                &host,
                &public_socket,
                &retained_config,
                mini_sdk::host_operations::AUTHOR,
                Some(COMMAND_KIND),
                &directory.join("source.json"),
                &directory.join("command.bin"),
            )?;
            let command = private_bytes(&directory.join("command.bin"), LIMIT)?;
            let command_view = inspect(
                &host,
                &public_socket,
                &retained_config,
                COMMAND_KIND,
                &directory.join("command.bin"),
                &directory.join("command.json"),
            )?;
            if field(&command_view, "type")? != "participant-key-enrollment-v1"
                || field(&command_view, "canonical")? != hex(&command)
                || command_view.get("key") != Some(&command_source["key"])
            {
                return Err("enrollment canonical command differs from reserved source".into());
            }
            let plan = staged_invoke(
                &host,
                &operation_socket,
                &retained_config,
                &directory,
                "plan",
                mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_PLAN,
                &pair(&signed, &command)?,
            )?;
            let plan_view = inspect(
                &host,
                &public_socket,
                &retained_config,
                PLAN_KIND,
                &directory.join("plan.bin"),
                &directory.join("plan-unpinned.json"),
            )?;
            validate_plan(&plan_view, &command, &plan)?;
            // The plan is pinned to the observation's height before anything signs it, so it
            // survives the ticks between plan, possession and seal (`pin_plan_height`).
            let height = observation_height(&directory)?;
            match pin_plan_height(&host, &retained_config, &directory.join("plan.bin"), &height, &directory.join("plan-pinned.bin"))? {
                Some(pinned_plan) => {
                    let pinned_view = inspect(
                        &host,
                        &public_socket,
                        &retained_config,
                        PLAN_KIND,
                        &directory.join("plan-pinned.bin"),
                        &directory.join("plan.json"),
                    )?;
                    validate_plan(&pinned_view, &command, &pinned_plan)?;
                    Ok((command, pinned_plan, pinned_view, Some(height)))
                }
                None => {
                    eprintln!("mini: enroll plan: this Host has no pin-enrollment-plan-height; the plan is unpinned and does not survive a tick before it is sealed");
                    fs::copy(directory.join("plan-unpinned.json"), directory.join("plan.json")).map_err(|error| error.to_string())?;
                    Ok((command, plan, plan_view, None))
                }
            }
        },
        // The Host's own stale-root, or the local consent provider's proven stale observation (the
        // source moved between the Host's challenge and the local check; nothing was signed): both
        // observe again. Any other refusal stays terminal.
        |_, decision| {
            let consent_stale = crate::client_consent::take_stale_observation();
            stale_refusal(&host, &public_socket, &retained_config, decision) || consent_stale
        },
        // The loop counts its own re-plans from 1; the directory may already hold retirements from an
        // earlier resume or a no-record refusal, so the slot is the directory's next free one.
        |_| {
            crate::replan::retire(&directory, next_retirement(&directory)?, &["request.json", "config.json", "enrollment.lock"])
                .map(|_| ())
        },
    )?;
    pinned(&request, "hostSha256", &host_image_sha256(&host)?)?;
    pinned(
        &request,
        "configSha256",
        &digest(&bounded(&config, 65_536)?),
    )?;
    let command_sha = digest(&command);
    participant_namespace::bind_attempt(&reservation, &directory, &command_sha)?;
    save_json_staged(
        &directory.join("pin.json"),
        &json!({"format":FORMAT,
        "host":host,"hostSha256":host_image_sha256(&host)?,
        "config":retained_config,"configSha256":digest(&config_bytes),
        "publicSocket":public_socket,"operationSocket":operation_socket,
        "operatorOnly":operator_override.is_some(),
        "sponsorKey":sponsor_key,"newKey":new_key,"homeSubject":home,"namespaceRoot":namespace_root,
        "name":name,"sponsor":sponsor,"subject":subject,
        "keyId":reservation.ids["keyId"],"publicKey":public_key,
        "requestSha256":digest(&request_bytes),"commandSha256":command_sha,
        "planSha256":digest(&plan),"pinnedAtHeight":pinned_at,"reservationDigest":reservation.request_digest,
        "reservationRecord":reservation.record_path}),
    )?;
    print_json(&plan_custody(&subject, reservation.ids["keyId"].as_str(), &public_key, &plan_view))
}

fn validate_plan(view: &Value, command: &[u8], plan: &[u8]) -> Result<()> {
    if field(view, "type")? != "participant-key-enrollment-plan-v1"
        || field(view, "canonical")? != hex(plan)
        || field(view, "commandBytes")? != hex(command)
        || view
            .get("sponsorHeader")
            .and_then(|header| header.get("decoded"))
            != Some(&Value::Bool(true))
        || view
            .get("sponsorHeader")
            .and_then(|header| header.get("canonical"))
            .and_then(Value::as_str)
            .is_none_or(str::is_empty)
        || view
            .get("possessionHeader")
            .and_then(Value::as_str)
            .is_none_or(str::is_empty)
    {
        return Err("enrollment Plan differs from canonical command or signing headers".into());
    }
    Ok(())
}

/// Run by the enrolled principal, in its own process, over the sponsor's
/// retained Plan and canonical command inspection. It signs only the Host's
/// possession header, and only when the command names this key at the
/// expected home subject. The sponsor's secret is never read.
fn possess(mut args: Args) -> Result<()> {
    let directory = absolute(&path(args.required("dir")?))?;
    let key_path = absolute(&path(args.required("key")?))?;
    let subject = args
        .required("subject")?
        .into_string()
        .map_err(|_| "home subject must be UTF-8")?;
    let output = absolute(&path(args.required("output")?))?;
    args.finish()?;
    print_json(&possess_at(&directory, &key_path, &subject, &output)?)
}

fn possess_at(directory: &Path, key_path: &Path, subject: &str, output: &Path) -> Result<Value> {
    let signing = key(key_path)?;
    decimal(subject, "home subject")?;
    if output.exists() {
        return Err("possession signature output already exists".into());
    }
    let plan_view: Value = serde_json::from_slice(&bounded(&directory.join("plan.json"), 8 * transport::HOST_MAX_FRAME)?)
        .map_err(|error| format!("invalid enrollment Plan inspection: {error}"))?;
    let command_view: Value = serde_json::from_slice(&bounded(&directory.join("command.json"), 8 * transport::HOST_MAX_FRAME)?)
        .map_err(|error| format!("invalid enrollment command inspection: {error}"))?;
    let public_key = hex(&signing.verifying_key().to_bytes());
    let key_record = command_view.get("key").ok_or("enrollment command names no key")?;
    if field(&command_view, "type")? != "participant-key-enrollment-v1"
        || field(&plan_view, "type")? != "participant-key-enrollment-plan-v1"
        || field(&plan_view, "commandBytes")? != field(&command_view, "canonical")?
        || field(key_record, "publicKey")? != public_key
        || field(key_record, "subject")? != subject
    {
        return Err("enrollment Plan does not name this key at the expected home subject".into());
    }
    let candidate = mini_sdk::hex::decode(field(&plan_view, "possessionHeader")?).map_err(|e| e.0)?;
    let command = private_bytes(&directory.join("command.bin"), LIMIT)?;
    if field(&command_view, "canonical")? != hex(&command) {
        return Err("enrollment possession command differs from retained bytes".into());
    }
    let header = crate::client_consent::possession(Path::new(""), &directory.join("config.json"),
        &command, &subject, &signing, &candidate)?;
    // This explicit action accepts the operator's offered command. Retain
    // exactly what custody accepted before producing the possession signature.
    let local = crate::client_consent::configured_record()?
        .ok_or("possession requires independently retained local consent selection")?;
    let local_config = Path::new(field(&local, "config")?);
    let acceptance = json!({"type":"minidregg-participant-possession-acceptance-v1",
        "origin":"operator-offered-command", "action":"possess",
        "subject":subject,"publicKey":public_key,"commandHex":hex(&command),
        "commandSha256":digest(&command),"possessionHeaderSha256":digest(&header),
        "localConsent":local,"localConfigSha256":digest(&private_bytes(local_config,65_536)?) });
    retain_exact(&directory.join("possession-acceptance.json"),
        &serde_json::to_vec_pretty(&acceptance).map_err(|error|error.to_string())?)?;
    let signature = signing.sign(&header).to_bytes();
    create_private(output, &signature)?;
    Ok(json!({"type":"minidregg-participant-possession-signature-v1",
        "subject":subject,"publicKey":public_key,
        "commandSha256":digest(&mini_sdk::hex::decode(field(&command_view, "canonical")?).map_err(|e| e.0)?),
        "possessionHeaderSha256":digest(&header),"signatureSha256":digest(&signature)}))
}

/// The sponsor's half of a public-key enrollment made portable: everything
/// the participant's `mini join` needs to check the Plan against the Host and
/// sign possession, and nothing secret. The config travels whole because a
/// remote client sends it in every envelope; the Host image travels as its
/// digest, which every envelope pins.
fn offer(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    refused_pending(&directory)?;
    let pin = load_pin(&directory)?;
    if pin.new_key.is_some() {
        return Err("this enrollment holds the new secret key; only a public-key enrollment has an offer".into());
    }
    let plan_view = json_private(&directory.join("plan.json"))?;
    validate_plan(&plan_view, &pin.command, &pin.plan)?;
    let command_view = json_private(&directory.join("command.json"))?;
    let config = bounded(&pin.config, 65_536)?;
    print_json(&json!({"type":"minidregg-participant-join-offer-v1",
        "subject":pin.subject,"keyId":pin.key_id,"publicKey":pin.public_key,
        "hostSha256":host_image_sha256(&pin.host)?,
        "configHex":hex(&config),"configSha256":digest(&config),
        "plan":plan_view,"command":command_view}))
}

/// After admission: the participant's admitted enrollment (no key path; the
/// key was never here) and, when the sponsor provisioned them, the birth
/// context their own `workspace create` uses.
fn welcome(directory: &Path, birth_context: Option<&Path>) -> Result<()> {
    let directory = absolute(directory)?;
    let (_pin, ingress) = sealed(&directory)?;
    let enrollment = json_private(&directory.join("enrollment.json"))?;
    pinned(&enrollment, "type", "minidregg-participant-enrollment-result-v1")?;
    pinned(&enrollment, "authority", "admitted-key-only")?;
    if !enrollment.get("keyPath").is_some_and(Value::is_null) {
        return Err("only a public-key enrollment has a welcome; this one holds the secret here".into());
    }
    let context = birth_context
        .map(|path| {
            serde_json::from_slice::<Value>(&bounded(&absolute(path)?, 256 * 1024)?)
                .map_err(|error| format!("invalid birth context: {error}"))
        })
        .transpose()?;
    if let Some(context) = &context {
        pinned(context, "type", "minidregg-participant-birth-context-v1")?;
    }
    print_json(&json!({"type":"minidregg-participant-join-welcome-v1",
        "enrollment":enrollment,"birthContext":context,
        "ingressHex":hex(&ingress),"ingressSha256":digest(&ingress)}))
}

fn join_dir(path: &Path) -> Result<()> {
    match fs::DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => crate::fsio::ensure_private_dir(path),
        Err(error) => Err(format!("cannot create {}: {error}", path.display())),
    }
}

/// `mini join`, run by the participant on their own machine.
///   --key KEY                      make the key and its NEXT key here (or
///                                  show them); send both printed public keys
///                                  to the sponsor (K-PREROTATE: the record
///                                  commits to the next one)
///   --sponsor-plan OFFER --dir R   check the offer against the Host over
///                                  --remote, sign possession; send the
///                                  printed signature to the sponsor
///   --welcome WELCOME --dir R      make R/workspace, a remote workspace
/// The secret is read only by this process; the box never receives it.
pub(crate) fn join(mut args: Args) -> Result<()> {
    let key_path = absolute(&path(args.required("key")?))?;
    let offer = args.optional("sponsor-plan").map(path);
    let welcome = args.optional("welcome").map(path);
    let verifier = args.optional("verifier").map(|value| absolute(&path(value))).transpose()?;
    if verifier.is_some() && welcome.is_none() {
        return Err("join --verifier is used with --welcome".into());
    }
    let root = args.optional("dir").map(|dir| absolute(&path(dir))).transpose()?;
    args.finish()?;
    match (offer, welcome, root) {
        (None, None, None) => {
            if key_path.exists() {
                println!("{}", hex(&key(&key_path)?.verifying_key().to_bytes()));
            } else {
                let parent = key_path.parent().ok_or("key path lacks a parent")?;
                join_dir(parent)?;
                keygen(&key_path, &key_path.with_extension("pub"), None, NextKey::Beside, false)?;
            }
            // The second line: the next key's public half, which the sponsor's
            // plan commits to (absent for a key made with --no-prerotation).
            if let Some(next) = own_next_public(&key_path)? {
                println!("{}", hex(&next));
                // The third line: the next key's co-signature, which the
                // sponsor's plan carries (FIX-IDENTITY).
                let cosign = crate::key_rotation::conventional_next_cosign(&key_path);
                if cosign.is_file() {
                    println!("{}", hex(&cosign_file(&cosign)?));
                }
            }
            Ok(())
        }
        (Some(offer), None, Some(root)) => join_possess(&key_path, &absolute(&offer)?, &root),
        (None, Some(welcome), Some(root)) => join_welcome(&key_path, &absolute(&welcome)?, &root,
            verifier.as_deref().ok_or("join --welcome requires the pinned portable --verifier LOCAL-HOST")?),
        _ => Err("join takes --key alone, or --key with --sponsor-plan or --welcome and --dir".into()),
    }
}

/// The next public key `mini keygen` wrote beside KEY, if any.
fn own_next_public(key_path: &Path) -> Result<Option<[u8; 32]>> {
    let path = crate::key_rotation::conventional_next_public(key_path);
    if !path.exists() {
        return Ok(None);
    }
    let bytes = fs::read(&path).map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let next: [u8; 32] = bytes
        .try_into()
        .map_err(|_| format!("{} must hold exactly 32 raw bytes", path.display()))?;
    Ok(Some(next))
}

fn join_remote() -> Result<PathBuf> {
    let socket = SOCKET.get().ok_or("join talks to the Host: pass --remote DEST")?;
    if !transport::is_remote(socket) {
        return Err("join runs on the participant's own machine: pass --remote DEST".into());
    }
    Ok(socket.clone())
}

fn join_possess(key_path: &Path, offer_path: &Path, root: &Path) -> Result<()> {
    let socket = join_remote()?;
    let offer_bytes = bounded(offer_path, 8 * transport::HOST_MAX_FRAME)?;
    let offer: Value = serde_json::from_slice(&offer_bytes)
        .map_err(|error| format!("invalid sponsor plan: {error}"))?;
    pinned(&offer, "type", "minidregg-participant-join-offer-v1")?;
    let signing = key(key_path)?;
    let public_key = hex(&signing.verifying_key().to_bytes());
    if field(&offer, "publicKey")? != public_key {
        return Err("the sponsor's plan names another key than --key".into());
    }
    let subject = field(&offer, "subject")?.to_owned();
    decimal(&subject, "offered subject")?;
    decimal(field(&offer, "keyId")?, "offered key id")?;
    let config = mini_sdk::hex::decode(field(&offer, "configHex")?).map_err(|e| e.0)?;
    if digest(&config) != field(&offer, "configSha256")? {
        return Err("the sponsor's plan config differs from its digest".into());
    }
    pin_remote_host(field(&offer, "hostSha256")?)?;
    let plan_view = offer.get("plan").ok_or("sponsor plan lacks the Plan")?;
    let command_view = offer.get("command").ok_or("sponsor plan lacks the command")?;
    let plan = mini_sdk::hex::decode(field(plan_view, "canonical")?).map_err(|e| e.0)?;
    let command = mini_sdk::hex::decode(field(command_view, "canonical")?).map_err(|e| e.0)?;
    validate_plan(plan_view, &command, &plan)?;
    join_dir(root)?;
    let state = root.join("join");
    join_dir(&state)?;
    retain_exact(&state.join("offer.json"), &offer_bytes)?;
    retain_exact(&root.join("config.json"), &config)?;
    save_json_staged(&state.join("plan.json"), plan_view)?;
    save_json_staged(&state.join("command.json"), command_view)?;
    retain_exact(&state.join("plan.bin"), &plan)?;
    retain_exact(&state.join("command.bin"), &command)?;
    // The Host itself, over the proxy, decodes the exact bytes the sponsor
    // sent; a sponsor (or a box) that altered a view is caught here.
    let host = Path::new("");
    for (kind, input, output, view) in [
        (PLAN_KIND, "plan.bin", "host-plan.json", plan_view),
        (COMMAND_KIND, "command.bin", "host-command.json", command_view),
    ] {
        let decoded = inspect(host, &socket, &root.join("config.json"), kind, &state.join(input), &state.join(output))?;
        if &decoded != view {
            return Err(format!("the Host decodes the sponsor's {kind} differently from the plan"));
        }
    }
    // K-PREROTATE: the record commits to the key that may later replace this
    // one, and a rotation needs only that key's signature. The plan must commit
    // to MY next key (computed by the Host from my next public half), or to none
    // when I hold none: a sponsor committing a key it holds could rotate my
    // identity to itself.
    let offered = command_view
        .get("key")
        .and_then(|key| key.get("nextKeyDigest"))
        .ok_or("the sponsor's command names no nextKeyDigest")?;
    match (own_next_public(key_path)?, offered.as_str()) {
        (Some(next), Some(digest)) => {
            let mine = crate::key_rotation::next_key_digest(host, &socket, &root.join("config.json"), &next)?;
            if mine != digest {
                return Err("the sponsor's plan commits to a next key that is not yours (KEY.next.pub): refuse it".into());
            }
        }
        (Some(_), None) => {
            return Err("the sponsor's plan commits to no next key, but you hold one (KEY.next.pub): ask for a plan with your next public key".into())
        }
        (None, Some(_)) => {
            return Err("the sponsor's plan commits to a next key, and you hold none: a key you do not hold could replace yours; refuse it".into())
        }
        (None, None) => {}
    }
    let signature_path = state.join("possession-signature.bin");
    let summary = if signature_path.exists() {
        let signature = bounded(&signature_path, 64)?;
        let header = mini_sdk::hex::decode(field(plan_view, "possessionHeader")?).map_err(|e| e.0)?;
        signing
            .verifying_key()
            .verify(&header, &ed25519_dalek::Signature::from_slice(&signature).map_err(|_| "retained possession signature is malformed")?)
            .map_err(|_| "retained possession signature does not verify")?;
        json!({"subject":subject,"publicKey":public_key})
    } else {
        possess_at(&state, key_path, &subject, &signature_path)?
    };
    let signature = bounded(&signature_path, 64)?;
    print_json(&json!({"type":"minidregg-participant-join-possession-v1",
        "subject":summary["subject"],"publicKey":summary["publicKey"],
        "possessionSignature":hex(&signature),
        "next":"give possessionSignature to your sponsor; then run join --welcome with the pinned portable --verifier"}))
}

fn stable_receipt(value: &Value) -> Result<Value> {
    let mut result = json!({});
    for name in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        decimal(field(value, name)?, name)?;
        result[name] = value[name].clone();
    }
    Ok(result)
}

/// Only the source Host decodes semantic bytes. A fresh output prevents a stale
/// successful inspection from surviving a failed verifier invocation.
fn local_join_inspect(verifier: &Path, pin: &Value, config: &Path, kind: &str,
    input: &Path, directory: &Path) -> Result<Value> {
    if host_image_sha256(verifier)? != field(pin, "verifierSha256")? {
        return Err("join local verifier image changed".into());
    }
    let output = directory.join(format!("inspect-{}.json", crate::fsio::random_nonce()?));
    create_private(&output, b"")?;
    let result = Command::new(verifier).arg(config).arg("inspect").arg(kind)
        .arg(input).arg(&output).output().map_err(|error| format!("cannot inspect join evidence: {error}"))?;
    if !result.status.success() {
        return Err(format!("local source verifier refused join {kind}"));
    }
    json_private(&output)
}
fn match_join_ingress(view: &Value, ingress: &[u8], command: &[u8], possession: &[u8], admitted: &Value) -> Result<()> {
    if view["type"] != "participant-key-enrollment-ingress-v2"
        || field(view, "canonical")? != hex(ingress)
        || field(view, "commandBytes")? != hex(command)
        || field(view, "possessionSignature")? != hex(possession)
        || field(view, "possessionSignatureLength")? != "64" {
        return Err("welcome sealed ingress differs from the participant's signed request or possession signature".into());
    }
    for name in ["subject", "keyId", "publicKey"] {
        if view["command"]["key"][name] != admitted[name] {
            return Err(format!("welcome sealed command {name} differs from admitted identity"));
        }
    }
    Ok(())
}
/// The signed command and admitted ingress must name the participant-owned next
/// key, including its real co-signature. Absence is an explicit signed policy.
fn match_join_prerotation(view: &Value, own_next: Option<[u8; 32]>, public: &[u8; 32]) -> Result<bool> {
    let offered = view["command"]["key"].get("nextKeyDigest")
        .ok_or("welcome command lacks nextKeyDigest")?;
    let next = mini_sdk::hex::decode(field(view,"nextPublicKey")?).map_err(|e| e.0)?;
    let cosign = mini_sdk::hex::decode(field(view,"nextPossessionSignature")?).map_err(|e| e.0)?;
    match own_next {
        Some(own) => {
            decimal(offered.as_str().ok_or("welcome removes the participant next-key commitment")?, "next-key digest")?;
            if next != own {
                return Err("welcome next key differs from the participant retained next key".into());
            }
            let signature: [u8; 64] = cosign.try_into().map_err(|_| "welcome next-key co-signature is malformed")?;
            crate::key_rotation::verify_cosign(public, &own, &signature)?;
            Ok(false)
        }
        None if offered.is_null() && next.is_empty() && cosign.is_empty() => Ok(true),
        None => Err("welcome commits to a next key the participant does not hold".into()),
    }
}

fn match_join_receipt(outcome: &Value, admitted: &Value) -> Result<Value> {
    confirmed(outcome)?;
    let receipt = stable_receipt(outcome)?;
    if receipt != stable_receipt(&admitted["receipt"])? {
        return Err("welcome receipt differs from exact read-only enrollment lookup".into());
    }
    Ok(receipt)
}

/// Retain the fact that this join has created custody outside that custody's
/// directory. Losing the whole workspace must not look like another first use.
fn retain_join_workspace_marker(state: &Path, root: &Path, evidence: &Value, manifest: &Value) -> Result<()> {
    let marker = state.join("workspace-created.json");
    let expected = json!({"type":"minidregg-join-workspace-created-v1",
        "evidence":evidence,"freshContinuity":manifest["freshContinuity"]});
    if !marker.exists() {
        let pending = json_private(&root.join("receipt-continuity.pending.json"))?;
        if manifest.get("receiptContinuity").is_some() || root.join("receipt-continuity").exists()
            || pending["state"] != "awaiting-first-read" {
            return Err("join workspace creation marker is missing; restore retained custody".into());
        }
    }
    crate::receipt_continuity::fresh::retain_workspace_creation(state,&expected)
}

fn join_welcome(key_path: &Path, welcome_path: &Path, root: &Path, verifier: &Path) -> Result<()> {
    let socket = join_remote()?;
    let state = root.join("join");
    crate::fsio::ensure_private_dir(&state)?;
    let _lock = transport::service_lock(&state.join("welcome.lock"))?;
    let offer_bytes = bounded(&state.join("offer.json"), 8 * transport::HOST_MAX_FRAME)?;
    let offer: Value = serde_json::from_slice(&offer_bytes).map_err(|error| error.to_string())?;
    pinned(&offer, "type", "minidregg-participant-join-offer-v1")?;
    let possession = private_bytes(&state.join("possession-signature.bin"), 64)?;
    let welcome: Value = serde_json::from_slice(&bounded(welcome_path, 512 * 1024)?)
        .map_err(|error| format!("invalid welcome: {error}"))?;
    pinned(&welcome, "type", "minidregg-participant-join-welcome-v1")?;
    let admitted = welcome.get("enrollment").ok_or("welcome lacks the enrollment")?;
    pinned(admitted, "type", "minidregg-participant-enrollment-result-v1")?;
    pinned(admitted, "authority", "admitted-key-only")?;
    let signing = key(key_path)?;
    let public_key = hex(&signing.verifying_key().to_bytes());
    for name in ["subject", "keyId", "publicKey"] {
        if field(admitted, name)? != field(&offer, name)? {
            return Err(format!("welcome {name} differs from the plan this key signed"));
        }
    }
    if field(admitted, "publicKey")? != public_key {
        return Err("welcome names another key than --key".into());
    }
    let ingress = mini_sdk::hex::decode(field(&welcome, "ingressHex")?).map_err(|e| e.0)?;
    if ingress.is_empty() || ingress.len() > LIMIT || digest(&ingress) != field(&welcome, "ingressSha256")? {
        return Err("welcome ingress exceeds bound or differs from its digest".into());
    }
    let workspace_root = root.join("workspace");
    let evidence_path = state.join("authenticated-receipt.json");
    if !workspace_root.exists() && fs::symlink_metadata(state.join("workspace-created.json")).is_ok() {
        return Err("joined workspace custody is missing; restore it instead of trusting another first baseline".into());
    }
    if workspace_root.exists() {
        // Repeated welcome can only finish this workspace's recorded fresh birth.
        // It cannot adopt legacy state, restore lost anchors or select another head.
        let evidence = json_private(&evidence_path)?;
        if evidence["receipt"] != stable_receipt(&admitted["receipt"])?
            || evidence["ingressSha256"] != digest(&ingress) {
            return Err("welcome differs from authenticated enrollment evidence".into());
        }
        let manifest = crate::workspace::bounded_json(&workspace_root.join("workspace.json"))?;
        if manifest.get("freshContinuity").is_none()
            || field(&manifest,"subject")? != field(admitted,"subject")?
            || crate::workspace::member_path(&manifest,"key")? != key_path {
            return Err("welcome cannot adopt an existing or changed workspace".into());
        }
        let initial = json_private(&workspace_root.join("receipt-continuity.pending.json"))?;
        if initial["admittedReceipt"] != evidence {
            return Err("workspace first trust differs from admitted enrollment evidence".into());
        }
        retain_join_workspace_marker(&state,&workspace_root,&evidence,&manifest)?;
        return print_json(&json!({"type":"minidregg-participant-joined-v1","workspace":workspace_root,
            "continuity":crate::workspace::complete_fresh_onboarding(&workspace_root)?}));
    }
    let config = root.join("config.json");
    let config_bytes = bounded(&config, 65_536)?;
    if digest(&config_bytes) != field(&offer,"configSha256")?
        || config_bytes != mini_sdk::hex::decode(field(&offer,"configHex")?).map_err(|e| e.0)? {
        return Err("join config differs from retained offer".into());
    }
    pin_remote_host(field(&offer, "hostSha256")?)?;
    let verifier_pin = crate::receipt_continuity::fresh::verifier_pin(&config, verifier)?;
    let command = private_bytes(&state.join("command.bin"), LIMIT)?;
    let plan = private_bytes(&state.join("plan.bin"), LIMIT)?;
    save_json_staged(&state.join("welcome-pin.json"), &json!({
        "type":"minidregg-participant-welcome-pin-v1","verifier":verifier_pin,
        "offerSha256":digest(&offer_bytes),"configSha256":digest(&config_bytes),
        "remote":socket,"publicKey":public_key,"ingressSha256":digest(&ingress),
        "commandSha256":digest(&command),"possessionSha256":digest(&possession)}))?;
    retain_exact(&state.join("welcome-ingress.bin"), &ingress)?;
    let plan_view = local_join_inspect(verifier,&verifier_pin,&config,PLAN_KIND,&state.join("plan.bin"),&state)?;
    validate_plan(&plan_view,&command,&plan)?;
    let header = mini_sdk::hex::decode(field(&plan_view,"possessionHeader")?).map_err(|e| e.0)?;
    signing.verifying_key().verify(&header, &ed25519_dalek::Signature::from_slice(&possession)
        .map_err(|_| "retained possession signature is malformed")?)
        .map_err(|_| "retained possession signature does not verify")?;
    let ingress_view = local_join_inspect(verifier,&verifier_pin,&config,INGRESS_KIND,&state.join("welcome-ingress.bin"),&state)?;
    match_join_ingress(&ingress_view,&ingress,&command,&possession,admitted)?;
    let without_prerotation = match_join_prerotation(&ingress_view, own_next_public(key_path)?, &signing.verifying_key().to_bytes())?;
    let evidence = if evidence_path.exists() {
        // The exact confirmed frame is durable before this marker; re-decode it
        // locally rather than depending on another server response after a crash.
        let evidence = json_private(&evidence_path)?;
        let frame = private_bytes(&state.join("welcome-confirmed.frame"), transport::HOST_MAX_FRAME)?;
        if evidence["lookupFrameSha256"] != digest(&frame) || evidence["ingressSha256"] != digest(&ingress) {
            return Err("retained admission frame or ingress changed".into());
        }
        retain_exact(&state.join("welcome-confirmed.bin"), reply(&frame,mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_LOOKUP)?)?;
        let outcome = local_join_inspect(verifier,&verifier_pin,&config,"outcome",&state.join("welcome-confirmed.bin"),&state)?;
        if evidence["receipt"] != match_join_receipt(&outcome,admitted)? {
            return Err("retained admission receipt changed".into());
        }
        evidence
    } else {
        // This path has no submit operation. A transport failure, absent result or
        // refusal leaves retained ingress available for another read-only lookup.
        let frame = session_invoke(Path::new(""),&socket,&config,mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_LOOKUP,&ingress)
            .map_err(|e| format!("join receipt lookup unresolved; retry this exact welcome (no submission): {e}"))?;
        let stem = format!("welcome-lookup-{}",crate::fsio::random_nonce()?);
        retained_frame(&state,&stem,&frame,mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_LOOKUP)?;
        let outcome = local_join_inspect(verifier,&verifier_pin,&config,"outcome",&state.join(format!("{stem}.bin")),&state)?;
        let receipt = match_join_receipt(&outcome,admitted)?;
        retain_exact(&state.join("welcome-confirmed.frame"),&frame)?;
        retain_exact(&state.join("welcome-confirmed.bin"),reply(&frame,mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_LOOKUP)?)?;
        let evidence = json!({"type":"minidregg-authenticated-enrollment-receipt-v1",
            "receipt":receipt,"ingressSha256":digest(&ingress),"lookupFrameSha256":digest(&frame)});
        save_json_staged(&evidence_path,&evidence)?;
        evidence
    };
    save_json_staged(&state.join("welcome.json"),&welcome)?;
    let mut record = admitted.clone();
    record["keyPath"] = json!(utf8_path(key_path)?);
    save_json_staged(&state.join("enrollment.json"), &record)?;
    let context = match welcome.get("birthContext") {
        Some(Value::Null) | None => None,
        Some(context) => {
            save_json_staged(&state.join("birth-context.json"), context)?;
            Some(state.join("birth-context.json"))
        }
    };
    let namespace = root.join("namespace");
    join_dir(&namespace)?;
    crate::workspace::init_fresh_receipt(&workspace_root,None,&config,
        crate::workspace::InitIdentity {key:None,subject:None,enrollment:Some(&state.join("enrollment.json")),next_public:None,without_prerotation},
        context.as_deref(),Some(&namespace),&evidence,verifier)?;
    let manifest = crate::workspace::bounded_json(&workspace_root.join("workspace.json"))?;
    retain_join_workspace_marker(&state,&workspace_root,&evidence,&manifest)?;
    print_json(&json!({"type":"minidregg-participant-joined-v1","workspace":workspace_root,
        "continuity":crate::workspace::complete_fresh_onboarding(&workspace_root)?}))
}

fn seal(directory: &Path, detached: Option<&Path>) -> Result<()> {
    let directory = absolute(directory)?;
    let _lock = transport::service_lock(&directory.join("enrollment.lock"))?;
    refused_pending(&directory)?;
    if directory.join("submit-marker.json").exists() {
        return Err(
            "enrollment may have been submitted; use --action lookup with this exact --dir".into(),
        );
    }
    let pin = load_pin(&directory)?;
    match (&pin.new_key, detached) {
        (Some(new_key), None) => {
            if hex(&key(new_key)?.verifying_key().to_bytes()) != pin.public_key {
                return Err("new enrollment key changed after plan".into());
            }
        }
        (None, Some(_)) => (),
        (Some(_), Some(_)) => {
            return Err("a local-key enrollment signs its own possession header".into())
        }
        (None, None) => {
            return Err("home-identity enrollment requires --possession-signature".into())
        }
    }
    let plan_view = json_private(&directory.join("plan.json"))?;
    validate_plan(&plan_view, &pin.command, &pin.plan)?;
    // Re-inspect the plan this seal signs: the pinned plan when the plan was pinned (plan.json is
    // its inspection), else the Host's plan. Inspecting plan.bin against a pinned plan.json differed
    // whenever the source moved between the observation and the plan (the deadline the pin moves),
    // e.g. the fifth of five members enrolled back to back.
    let signed_plan = directory.join(plan_file(pin.pinned_at.as_deref()));
    let fresh = inspect(
        &pin.host,
        &pin.public_socket,
        &pin.config,
        PLAN_KIND,
        &signed_plan,
        &directory.join("seal-plan.json"),
    )?;
    if fresh != plan_view {
        return Err("enrollment Plan inspection changed before signing".into());
    }
    let observation = private_bytes(&directory.join("observation/signed-observation.bin"), LIMIT)?;
    crate::client_consent::operator_plan(&pin.host, &pin.config, mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_PLAN,
        &pair(&observation, &pin.command)?, &pin.plan).map_err(|error| format!(
            "{error}; a plan the source has moved under (a tick or certify since it was planned) is not signed: `mini enroll --action plan` with this exact --dir retires it and plans the same request again (a home-identity member then signs possession over the new plan)"
        ))?;
    let sponsor_header = mini_sdk::hex::decode(field(&plan_view["sponsorHeader"], "canonical")?).map_err(|e| e.0)?;
    let possession_header = mini_sdk::hex::decode(field(&plan_view, "possessionHeader")?).map_err(|e| e.0)?;
    let sponsor = key(&pin.sponsor_key)?;
    let sponsor_signature = sponsor.sign(&sponsor_header).to_bytes();
    let possession_signature: [u8; 64] = match (&pin.new_key, detached) {
        (Some(new_key), _) => key(new_key)?.sign(&possession_header).to_bytes(),
        (None, Some(file)) => {
            let bytes: [u8; 64] = bounded(&absolute(file)?, 64)?
                .try_into()
                .map_err(|_| "possession signature must contain exactly 64 bytes")?;
            let public: [u8; 32] = mini_sdk::hex::decode(&pin.public_key).map_err(|e| e.0)?
                .try_into()
                .map_err(|_| "pinned enrollment public key is not 32 bytes")?;
            VerifyingKey::from_bytes(&public)
                .map_err(|_| "pinned enrollment public key is invalid")?
                .verify(
                    &possession_header,
                    &ed25519_dalek::Signature::from_bytes(&bytes),
                )
                .map_err(|_| "detached possession signature does not verify for the pinned key")?;
            bytes
        }
        (None, None) => unreachable!("detached input checked above"),
    };
    retain_exact(&directory.join("sponsor-signature.bin"), &sponsor_signature)?;
    retain_exact(
        &directory.join("possession-signature.bin"),
        &possession_signature,
    )?;
    // possession (64), then for a pre-rotated record the next key (32) and its
    // co-signature (64): the second half of the pair is 64 or 160 bytes.
    let signatures = pair(
        &sponsor_signature,
        &[&possession_signature[..], &pin.next_public, &pin.next_cosign].concat(),
    )?;
    let assembly = pair(&pin.plan, &signatures)?;
    let ingress = staged_invoke(
        &pin.host,
        &pin.operation_socket,
        &pin.config,
        &directory,
        "ingress",
        mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_ASSEMBLE,
        &assembly,
    )?;
    let view = inspect(
        &pin.host,
        &pin.public_socket,
        &pin.config,
        INGRESS_KIND,
        &directory.join("ingress.bin"),
        &directory.join("ingress.json"),
    )?;
    if field(&view, "type")? != "participant-key-enrollment-ingress-v2"
        || field(&view, "canonical")? != hex(&ingress)
        || field(&view, "commandBytes")? != hex(&pin.command)
        || field(&view, "possessionSignature")? != hex(&possession_signature)
        || field(&view, "possessionSignatureLength")? != "64"
        || field(&view, "nextPublicKey")? != hex(&pin.next_public)
        || field(&view, "nextPossessionSignature")? != hex(&pin.next_cosign)
    {
        return Err("enrollment assembled ingress differs from signed exact Plan".into());
    }
    save_json_staged(
        &directory.join("seal.json"),
        &json!({"format":FORMAT,
        "planSha256":digest(&pin.plan),"commandSha256":digest(&pin.command),
        "ingressSha256":digest(&ingress),"sponsorSignatureSha256":digest(&sponsor_signature),
        "possessionSignatureSha256":digest(&possession_signature)}),
    )?;
    print_json(&json!({"type":"minidregg-participant-enrollment-sealed-v1",
        "subject":pin.subject,"keyId":pin.key_id,"ingressSha256":digest(&ingress),
        "authority":"awaiting-admission"}))
}

fn sealed(directory: &Path) -> Result<(Pin, Vec<u8>)> {
    let pin = load_pin(directory)?;
    let seal = json_private(&directory.join("seal.json"))?;
    pinned(&seal, "format", FORMAT)?;
    pinned(&seal, "planSha256", &digest(&pin.plan))?;
    pinned(&seal, "commandSha256", &digest(&pin.command))?;
    let ingress = private_bytes(&directory.join("ingress.bin"), LIMIT)?;
    pinned(&seal, "ingressSha256", &digest(&ingress))?;
    let assembly = private_bytes(&directory.join("ingress.frame"), transport::HOST_MAX_FRAME)?;
    if assembly != [vec![87], ingress.clone()].concat() {
        return Err("retained enrollment ingress differs from exact Host assembly".into());
    }
    let view = json_private(&directory.join("ingress.json"))?;
    if field(&view, "canonical")? != hex(&ingress)
        || field(&view, "commandBytes")? != hex(&pin.command)
    {
        return Err("retained enrollment ingress inspection changed".into());
    }
    Ok((pin, ingress))
}

fn outcome(directory: &Path, pin: &Pin, stem: &str, frame: &[u8], operation: u8) -> Result<Value> {
    let _body = retained_frame(directory, stem, frame, operation)?;
    let value = inspect(
        &pin.host,
        &pin.public_socket,
        &pin.config,
        "outcome",
        &directory.join(format!("{stem}.bin")),
        &directory.join(format!("{stem}.json")),
    )?;
    Ok(value)
}

pub(crate) fn confirmed(value: &Value) -> Result<()> {
    if field(value, "type")? != "confirmed"
        || !matches!(field(value, "confirmation")?, "installed" | "replayed" | "recoveredAfterUncertainResponse")
    {
        return Err(format!(
            "enrollment outcome is not a confirmed admitted key (the Host's outcome: type {}, effect {})",
            value.get("type").and_then(Value::as_str).unwrap_or("?"),
            value.get("effect").and_then(Value::as_str).unwrap_or("none")
        ));
    }
    for field_name in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        decimal(field(value, field_name)?, field_name)?;
    }
    Ok(())
}

fn confirmed_lookup(value: &Value) -> Result<()> {
    confirmed(value)?;
    if field(value, "confirmation")? != "replayed" {
        return Err("enrollment lookup did not confirm historical acceptance".into());
    }
    Ok(())
}

fn result(directory: &Path, pin: &Pin, receipt: &Value) -> Result<()> {
    confirmed(receipt)?;
    let path = directory.join("enrollment.json");
    let stable_receipt = json!({
        "transactionId":field(receipt,"transactionId")?,
        "eventId":field(receipt,"eventId")?,
        "acceptedCount":field(receipt,"acceptedCount")?,
        "worldRoot":field(receipt,"worldRoot")?
    });
    let value = json!({"type":"minidregg-participant-enrollment-result-v1",
        "subject":pin.subject,"keyId":pin.key_id,"publicKey":pin.public_key,
        "keyPath":pin.new_key,"receipt":stable_receipt,"authority":"admitted-key-only"});
    if path.exists() {
        if json_private(&path)? != value {
            return Err("prior admitted enrollment result differs from exact receipt".into());
        }
    } else {
        save_json(&path, &value)?;
    }
    print_json(&value)
}

/// `later`: this is a separate invocation after an earlier one ended with the submit marker written
/// (a later `submit` that finds the marker, or `lookup`). The Host's historical lookup answering
/// ABSENT then means the sealed ingress is in no history: the earlier process died before the Host
/// took it (a consent or transport failure), nothing was admitted, and the attempt is retired for a
/// fresh plan under the same request, exactly as a NO_RECORD refusal is (otherwise every retry looks
/// the same absent ingress up again, forever). Within the submitting invocation (`later` false) a
/// broken transport followed at once by ABSENT proves nothing (the Host may still be taking the
/// frame), so it stays an error and the marker stays.
fn lookup_exact(directory: &Path, pin: &Pin, ingress: &[u8], later: bool) -> Result<()> {
    let stem = format!(
        "lookup-{:04}",
        fs::read_dir(directory)
            .map_err(|error| error.to_string())?
            .filter_map(|entry| entry.ok())
            .filter(
                |entry| entry.file_name().to_string_lossy().starts_with("lookup-")
                    && entry.file_name().to_string_lossy().ends_with(".frame")
            )
            .count()
    );
    let frame = session_invoke(&pin.host, &pin.operation_socket, &pin.config, mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_LOOKUP, ingress)?;
    let value = outcome(directory, pin, &stem, &frame, mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_LOOKUP)?;
    if absence_retires(later, &value) {
        return no_record(directory, pin, ingress, frame.first().copied().unwrap_or(0), Some(value));
    }
    confirmed_lookup(&value)?;
    result(directory, pin, &value)
}

/// A historical lookup of a sealed ingress that answers `absent`, in a later invocation, retires the attempt.
pub(crate) fn absence_retires(later: bool, lookup: &Value) -> bool {
    later && lookup.get("type").and_then(Value::as_str) == Some("absent")
}

/// The Host answered the sealed plan's submit with NO RECORD (253): a refusal decided before any
/// append (Host/RequestRefusal.lean), so the attempt is definitely unadmitted. The frame and the
/// Host's own decoding of it are retained, the name's namespace binding is released (the
/// reservation and its ids stay the request's), and the caller is pointed at `plan` in this same
/// directory: the same request, a fresh observation, and the member seals the new plan.
fn refused_without_record(directory: &Path, pin: &Pin, frame: &[u8], ingress: &[u8]) -> Result<()> {
    retain_exact(&directory.join("submit.frame"), frame)?;
    let encoded = &frame[1..];
    let kind = b"outcome";
    let mut payload = (kind.len() as u16).to_le_bytes().to_vec();
    payload.extend_from_slice(kind);
    payload.extend_from_slice(encoded);
    let decoded = session_invoke(&pin.host, &pin.public_socket, &pin.config, mini_sdk::host_operations::INSPECT, &payload)
        .ok()
        .filter(|reply| reply.first() == Some(&8))
        .and_then(|reply| serde_json::from_slice::<Value>(&reply[1..]).ok());
    no_record(directory, pin, ingress, crate::RESPONSE_NO_RECORD, decoded)
}

/// The Host decided the submit refused and left no record: from the NO_RECORD byte (decoded above)
/// or from a decoded outcome that says so (`type: refused, effect: no-record`, e.g. an expired
/// signature, `CredentialSignatureAdmission.Reject.expired`). Either way nothing was admitted.
fn no_record(directory: &Path, pin: &Pin, ingress: &[u8], response: u8, decoded: Option<Value>) -> Result<()> {
    let reason = decoded
        .as_ref()
        .and_then(|outcome| outcome.get("reason").and_then(Value::as_str))
        .or_else(|| {
            decoded
                .as_ref()
                .filter(|outcome| outcome.get("type").and_then(Value::as_str) == Some("absent"))
                .map(|_| "absent from the Host's history: the earlier submit never reached it")
        })
        .unwrap_or("undecoded")
        .to_owned();
    save_json(
        &directory.join(SUBMIT_REFUSED),
        &json!({"format":FORMAT,"operation":88,"ingressSha256":digest(ingress),
            "response":response,"outcome":decoded,"status":"refused-no-record"}),
    )?;
    let released = participant_namespace::release_attempt(&pin.reservation, directory)?;
    Err(format!(
        "enrollment refused by the Host with no record ({reason}); nothing was admitted{}. Plan again with `mini enroll --action plan ... --dir {}` (the same request and reservation; the member seals the new plan), then seal and submit",
        released.map(|path| format!("; the namespace binding is released ({})", path.display())).unwrap_or_default(),
        directory.display()
    ))
}

fn submit(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let _lock = transport::service_lock(&directory.join("enrollment.lock"))?;
    refused_pending(&directory)?;
    let (pin, ingress) = sealed(&directory)?;
    if pin.operation_socket != pin.public_socket {
        private_socket(&pin.operation_socket)?;
    }
    let marker = directory.join("submit-marker.json");
    if marker.exists() {
        let prior = json_private(&marker)?;
        pinned(&prior, "ingressSha256", &digest(&ingress))?;
        return lookup_exact(&directory, &pin, &ingress, true);
    }
    save_json(
        &marker,
        &json!({"format":FORMAT,"operation":88,
        "ingressSha256":digest(&ingress),"status":"may-have-submitted"}),
    )?;
    match session_invoke(&pin.host, &pin.operation_socket, &pin.config, mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_SUBMIT, &ingress) {
        Ok(frame) if frame.first() == Some(&crate::RESPONSE_NO_RECORD) => {
            refused_without_record(&directory, &pin, &frame, &ingress)
        }
        Ok(frame) => {
            let value = outcome(&directory, &pin, "submit", &frame, mini_sdk::host_operations::PARTICIPANT_KEY_ENROLLMENT_SUBMIT)?;
            if confirmed(&value).is_ok() {
                return result(&directory, &pin, &value);
            }
            if value.get("type").and_then(Value::as_str) == Some("refused")
                && value.get("effect").and_then(Value::as_str) == Some("no-record")
            {
                return no_record(&directory, &pin, &ingress, frame.first().copied().unwrap_or(0), Some(value));
            }
            lookup_exact(&directory, &pin, &ingress, false)
        }
        Err(_) => lookup_exact(&directory, &pin, &ingress, false),
    }
}

fn lookup(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let _lock = transport::service_lock(&directory.join("enrollment.lock"))?;
    refused_pending(&directory)?;
    let (pin, ingress) = sealed(&directory)?;
    if !directory.join("submit-marker.json").exists() {
        return Err("enrollment has no submitted or uncertain attempt".into());
    }
    lookup_exact(&directory, &pin, &ingress, true)
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "enrollment action must be UTF-8")?;
    match action.as_str() {
        "plan" => plan(args),
        "possess" => possess(args),
        "cosign" => cosign_action(args),
        "offer" => {
            let directory = path(args.required("dir")?);
            args.finish()?;
            offer(&directory)
        }
        "welcome" => {
            let directory = path(args.required("dir")?);
            let context = args.optional("birth-context").map(path);
            args.finish()?;
            welcome(&directory, context.as_deref())
        }
        "seal" => {
            let directory = path(args.required("dir")?);
            let detached = args.optional("possession-signature").map(path);
            args.finish()?;
            seal(&directory, detached.as_deref())
        }
        "submit" | "lookup" => {
            let directory = path(args.required("dir")?);
            args.finish()?;
            match action.as_str() {
                "submit" => submit(&directory),
                _ => lookup(&directory),
            }
        }
        _ => Err("enrollment action must be plan, possess, offer, seal, submit, lookup or welcome".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(label: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "mini-enrollment-{label}-{}-{}",
            std::process::id(),
            crate::fsio::random_nonce().unwrap()
        ));
        fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        root
    }

    #[test]
    fn only_a_later_absent_lookup_retires_the_attempt() {
        let absent = json!({"type":"absent","effect":"undecided"});
        assert!(absence_retires(true, &absent));
        assert!(!absence_retires(false, &absent), "the submitting invocation proves nothing from a broken transport");
        assert!(!absence_retires(true, &json!({"type":"confirmed","confirmation":"replayed"})));
        assert!(!absence_retires(true, &json!({"type":"refused","effect":"no-record"})));
    }

    #[test]
    fn join_creation_marker_precedes_enablement_and_cannot_be_recreated_afterward() {
        let base=scratch("welcome-marker");
        let state=base.join("join");let root=base.join("workspace");
        crate::workspace::make_private_dir(&state).unwrap();
        crate::workspace::make_private_dir(&root).unwrap();
        save_json(&root.join("receipt-continuity.pending.json"),&json!({"state":"awaiting-first-read"})).unwrap();
        let mut manifest=json!({"freshContinuity":"123"});let evidence=json!({"receipt":"retained"});
        retain_join_workspace_marker(&state,&root,&evidence,&manifest).unwrap();
        manifest["receiptContinuity"]=json!("minidregg-continuity-v1");
        retain_join_workspace_marker(&state,&root,&evidence,&manifest).unwrap();
        fs::remove_file(state.join("workspace-created.json")).unwrap();
        assert!(retain_join_workspace_marker(&state,&root,&evidence,&manifest).is_err());
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn welcome_source_inspection_must_match_exact_participant_preimage() {
        let admitted=json!({"subject":"20","keyId":"30","publicKey":"aa"});
        let ingress=[1,2]; let command=[3,4]; let possession=[7;64];
        let view=json!({"type":"participant-key-enrollment-ingress-v2","canonical":hex(&ingress),
            "commandBytes":hex(&command),"possessionSignature":hex(&possession),"possessionSignatureLength":"64",
            "command":{"key":admitted}});
        match_join_ingress(&view,&ingress,&command,&possession,&admitted).unwrap();
        for field in ["canonical","commandBytes","possessionSignature","possessionSignatureLength"] {
            let mut wrong=view.clone(); wrong[field]=json!("00");
            assert!(match_join_ingress(&wrong,&ingress,&command,&possession,&admitted).is_err(),"{field}");
        }
        for field in ["subject","keyId","publicKey"] {
            let mut wrong=view.clone(); wrong["command"]["key"][field]=json!("999");
            assert!(match_join_ingress(&wrong,&ingress,&command,&possession,&admitted).is_err(),"{field}");
        }
    }
    #[test]
    fn welcome_prerotation_requires_owned_next_key_and_real_cosign() {
        let current=SigningKey::from_bytes(&[11;32]);
        let next=SigningKey::from_bytes(&[12;32]);
        let public=current.verifying_key().to_bytes();
        let own=next.verifying_key().to_bytes();
        let signature=crate::key_rotation::cosign(&public,&next);
        let mut view=json!({"command":{"key":{"nextKeyDigest":"123"}},
            "nextPublicKey":hex(&own),"nextPossessionSignature":hex(&signature)});
        assert!(!match_join_prerotation(&view,Some(own),&public).unwrap());
        assert!(match_join_prerotation(&view,None,&public).is_err());
        assert!(match_join_prerotation(&view,Some([0;32]),&public).is_err());
        view["nextPossessionSignature"]=json!(hex(&[0;64]));
        assert!(match_join_prerotation(&view,Some(own),&public).is_err());
        view=json!({"command":{"key":{"nextKeyDigest":null}},"nextPublicKey":"","nextPossessionSignature":""});
        assert!(match_join_prerotation(&view,None,&public).unwrap());
        assert!(match_join_prerotation(&view,Some(own),&public).is_err());
        view["command"]["key"].as_object_mut().unwrap().remove("nextKeyDigest");
        assert!(match_join_prerotation(&view,None,&public).is_err());
    }
    #[test]
    fn welcome_receipt_requires_confirmed_exact_lookup() {
        let receipt=json!({"transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"});
        let admitted=json!({"receipt":receipt});
        let mut outcome=receipt.clone(); outcome["type"]=json!("confirmed"); outcome["confirmation"]=json!("replayed");
        assert_eq!(match_join_receipt(&outcome,&admitted).unwrap(),receipt);
        for name in ["transactionId","eventId","acceptedCount","worldRoot"] {
            let mut wrong=outcome.clone(); wrong[name]=json!("9");
            assert!(match_join_receipt(&wrong,&admitted).is_err(),"{name}");
        }
        for state in ["absent","uncertain","refused","unavailable"] {
            let mut wrong=outcome.clone(); wrong["type"]=json!(state);
            assert!(match_join_receipt(&wrong,&admitted).is_err(),"{state}");
        }
    }

    #[test]
    fn possession_checks_identity_and_refuses_noncanonical_offered_command() {
        let root = scratch("possess");
        let secret = [7u8; 32];
        create_private(&root.join("owner.key"), &secret).unwrap();
        let other = [9u8; 32];
        create_private(&root.join("other.key"), &other).unwrap();
        let public = hex(&SigningKey::from_bytes(&secret).verifying_key().to_bytes());
        save_json(
            &root.join("command.json"),
            &json!({"type":"participant-key-enrollment-v1","canonical":"abcd",
                "key":{"subject":"7","publicKey":public}}),
        )
        .unwrap();
        save_json(
            &root.join("plan.json"),
            &json!({"type":"participant-key-enrollment-plan-v1","commandBytes":"abcd",
                "possessionHeader":"0102"}),
        )
        .unwrap();
        retain_exact(&root.join("command.bin"), &[0xab, 0xcd]).unwrap();
        save_json(&root.join("config.json"), &json!({})).unwrap();
        let wrong_subject = possess_at(&root, &root.join("owner.key"), "8", &root.join("a.sig"));
        assert!(wrong_subject.unwrap_err().contains("does not name this key"));
        let wrong_key = possess_at(&root, &root.join("other.key"), "7", &root.join("b.sig"));
        assert!(wrong_key.unwrap_err().contains("does not name this key"));
        assert!(!root.join("a.sig").exists() && !root.join("b.sig").exists());
        // A matching key/subject and operator JSON do not authorize the raw
        // two-byte header. A real canonical native command is required too.
        assert!(possess_at(&root, &root.join("owner.key"), "7", &root.join("c.sig")).is_err());
        assert!(!root.join("c.sig").exists());
        assert!(!root.join("possession-acceptance.json").exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn home_identity_reserves_only_a_key_id() {
        assert_eq!(enrollment_roles(true).len(), 1);
        assert_eq!(enrollment_roles(true)[0].label, "keyId");
        assert_eq!(enrollment_roles(false).len(), 2);
    }

    #[test]
    fn empty_attempt_then_retained_request_recovers_without_changing_nonce() {
        let root = scratch("request-retry");
        let first = json!({"type":"minidregg-participant-enrollment-request-v1",
            "name":"bob","sponsor":"1","control":"2","factory":"3",
            "observeCapability":"4","newPublicKey":"abc","hostSha256":"h",
            "configSha256":"c","nonce":"123"});
        assert_eq!(retained_request(&root, &first).unwrap(), first);
        let mut retry = first.clone();
        retry["nonce"] = json!("456");
        assert_eq!(retained_request(&root, &retry).unwrap()["nonce"], "123");
        retry["control"] = json!("5");
        assert!(retained_request(&root, &retry).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn orphaned_artifact_without_request_cannot_pick_new_nonce() {
        let root = scratch("orphan-retry");
        retain_exact(&root.join("source.json"), b"stale").unwrap();
        let request = json!({"type":"minidregg-participant-enrollment-request-v1",
            "name":"bob","sponsor":"1","control":"2","factory":"3",
            "observeCapability":"4","newPublicKey":"abc","hostSha256":"h",
            "configSha256":"c","nonce":"123"});
        assert!(retained_request(&root, &request).is_err());
        assert!(!root.join("request.json").exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn crash_after_host_frame_recovers_exact_body_without_socket_call() {
        let root = scratch("frame-retry");
        retain_exact(&root.join("challenge.frame"), &[4, 9, 8]).unwrap();
        let body = staged_invoke(
            Path::new("/missing-host"),
            Path::new("/missing-socket"),
            Path::new("/missing-config"),
            &root,
            "challenge",
            mini_sdk::host_operations::OBSERVATION_CHALLENGE,
            b"query",
        )
        .unwrap();
        assert_eq!(body, [9, 8]);
        assert_eq!(bounded(&root.join("challenge.bin"), LIMIT).unwrap(), [9, 8]);
        assert!(retain_exact(&root.join("challenge.bin"), &[9, 7]).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn retained_pin_replays_identically_and_refuses_rebinding() {
        let root = scratch("pin-retry");
        let pin = json!({"format":FORMAT,"subject":"9","planSha256":"a"});
        save_json_staged(&root.join("pin.json"), &pin).unwrap();
        save_json_staged(&root.join("pin.json"), &pin).unwrap();
        assert!(save_json_staged(
            &root.join("pin.json"),
            &json!({"format":FORMAT,"subject":"10","planSha256":"a"})
        )
        .is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn raw_possession_and_sponsor_headers_remain_distinct() {
        let sponsor = SigningKey::from_bytes(&[7; 32]);
        let new = SigningKey::from_bytes(&[8; 32]);
        let canonical = [1u8, 2, 3];
        let raw = [4u8, 5, 6];
        assert_ne!(
            sponsor.sign(&canonical).to_bytes(),
            new.sign(&raw).to_bytes()
        );
        let inner = pair(
            &sponsor.sign(&canonical).to_bytes(),
            &new.sign(&raw).to_bytes(),
        )
        .unwrap();
        assert_eq!(u32::from_le_bytes(inner[..4].try_into().unwrap()), 64);
        assert_eq!(inner.len(), 4 + 64 + 64);
    }

    #[test]
    fn candidate_or_rejected_result_never_claims_admitted_key() {
        assert!(confirmed(&json!({"type":"rejected","confirmation":"installed"})).is_err());
        assert!(confirmed(&json!({"type":"confirmed","confirmation":"absent"})).is_err());
        assert!(
            confirmed(&json!({"type":"confirmed","confirmation":"replayed",
            "transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"}))
            .is_ok()
        );
    }

    #[test]
    fn installed_replayed_and_recovered_receipts_have_one_stable_result() {
        let root = std::env::temp_dir().join(format!(
            "mini-enrollment-result-{}-{}",
            std::process::id(),
            crate::fsio::random_nonce().unwrap()
        ));
        fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        let pin = Pin {
            host: PathBuf::new(),
            config: PathBuf::new(),
            public_socket: PathBuf::new(),
            operation_socket: PathBuf::new(),
            sponsor_key: PathBuf::new(),
            new_key: Some(PathBuf::from("/private/new.key")),
            subject: "42".into(),
            key_id: "99".into(),
            public_key: "aa".repeat(32),
            plan: vec![],
            command: vec![],
            next_public: vec![],
            next_cosign: vec![],
            reservation: participant_namespace::Reservation {
                request_digest: "00".repeat(32), ids: Default::default(), record_path: PathBuf::new(),
            },
            pinned_at: None,
        };
        let installed = json!({"type":"confirmed","confirmation":"installed",
            "transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"});
        let replayed = json!({"type":"confirmed","confirmation":"replayed",
            "transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"});
        result(&root, &pin, &installed).unwrap();
        result(&root, &pin, &replayed).unwrap();
        let mut recovered = installed.clone();
        recovered["confirmation"] = json!("recoveredAfterUncertainResponse");
        result(&root, &pin, &recovered).unwrap();
        assert!(confirmed_lookup(&installed).is_err());
        assert!(confirmed_lookup(&recovered).is_err());
        assert!(confirmed_lookup(&replayed).is_ok());
        for name in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
            let mut changed = recovered.clone();
            changed[name] = json!("9");
            assert!(result(&root, &pin, &changed).is_err(), "{name}");
        }

        assert_eq!(
            json_private(&root.join("enrollment.json")).unwrap()["receipt"]["eventId"],
            "2"
        );
        fs::remove_dir_all(root).unwrap();
    }
}
