//! Participant-owned references and custody over the existing Mini client.
//! A reference is a discovery hint. Every read and operation still goes through
//! the signed observation, current Plan, and Lean admission in `main`.

use crate::current_birth;
use crate::receipt_continuity::{self, Mode as ContinuityMode};
use crate::participant_namespace::{self, IdKind, Role};
use crate::{
    absolute, author, hex, inspect, path, print_json, query_retained, retry, submit, Args,
    Result, SOCKET,
};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::ffi::{OsStr, OsString};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use std::sync::Mutex;

const MAX_RECORD: u64 = 256 * 1024;
/// A Nock program birth carries the program (jam + ABI) as hex in its source.
const MAX_PROGRAM_SOURCE: u64 = 4 * 1024 * 1024;

/// Client-side private-cell codec (`PrivateEnvelope/v2`); hooked into `propose`,
/// `read` and `tail` by `--private ROOM` (or a reference born in a private room).
/// See `docs/PRIVATE-CELL.md`.
#[path = "private.rs"]
pub(crate) mod private;
/// The room-key protocol of a private room: wraps in the room's keys cell,
/// rotation on a kick, the cache sync, sealing stream entries.
#[path = "roomkey.rs"]
pub(crate) mod roomkey;
#[path = "content_privacy.rs"]
pub(crate) mod content_privacy;
#[path = "protected_document.rs"]
pub(crate) mod protected_document;

/// `can [NAME] [--all]` (P-AFFORDANCES): the verbs my grants cover, each
/// prepared and dry-run against the current state, never submitted.
#[path = "can.rs"]
mod can;

/// `inspect caps|law|receipt|turn`, `why` (K-INSPECT-VIEWS): Lean renderers
/// over bytes this workspace holds or reads with its own signed views.
#[path = "inspect_views.rs"]
mod inspect_views;
/// `law check`, the install-time check and `can --any` (C-SAT-2, Host op 150).
#[path = "lawsat.rs"]
mod lawsat;

#[path = "world_kind.rs"]
mod world_kind;

#[path = "law_export.rs"]
mod law_export;

pub(crate) fn decimal(value: &str, field: &str) -> Result<()> {
    if value.is_empty()
        || value.len() > 39
        || (value.len() > 1 && value.starts_with('0'))
        || !value.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(format!("{field} must be a canonical bounded decimal"));
    }
    Ok(())
}

fn field_decimal(value: &str, field: &str) -> Result<()> {
    if value.is_empty()
        || value.len() > 80
        || (value.len() > 1 && value.starts_with('0'))
        || !value.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(format!("{field} must be a canonical bounded decimal"));
    }
    Ok(())
}

/// A canonical signed decimal, as the Host's `int` parser accepts it: the
/// declared value is an unbounded `Int` (a subject id above 2^63 is a value).
fn signed_decimal(value: &str, field: &str) -> Result<()> {
    let magnitude = value.strip_prefix('-').unwrap_or(value);
    if magnitude.is_empty()
        || magnitude.len() > 80
        || (magnitude.len() > 1 && magnitude.starts_with('0'))
        || value == "-0"
        || !magnitude.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(format!("{field} must be a canonical signed decimal"));
    }
    Ok(())
}

fn decimal_leq(left: &str, right: &str) -> bool {
    left.len() < right.len() || left.len() == right.len() && left <= right
}

fn decimal_max<'a>(left: &'a str, right: &'a str) -> &'a str {
    if decimal_leq(left, right) {
        right
    } else {
        left
    }
}

fn readable_delegation_verbs(selected: &[Value], parent: &[Value]) -> Result<()> {
    let mut unique = std::collections::BTreeSet::new();
    for verb in selected {
        let verb = verb.as_str().ok_or("delegation verb must be a string")?;
        if !unique.insert(verb) || !parent.iter().any(|value| value.as_str() == Some(verb)) {
            return Err("delegation verbs must be unique and within parent scope".into());
        }
    }
    if !unique.contains("observe") {
        return Err("workspace delegated references require the observe verb".into());
    }
    Ok(())
}

pub(crate) fn validate_name(value: &str) -> Result<()> {
    if value.is_empty()
        || value.len() > 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
    {
        return Err("workspace name must contain 1..64 ASCII letters, digits or hyphens".into());
    }
    Ok(())
}

/// A reference name: one segment (`lab`) or a path of segments under a room
/// (`lab/index`), each segment a `validate_name` word, at most 128 bytes in
/// all. The name is the friend's own local handle; nothing on the wire carries
/// it, and the Host never sees it.
pub(crate) fn validate_ref_name(value: &str) -> Result<()> {
    if value.is_empty() || value.len() > 128 || value.split('/').any(|segment| validate_name(segment).is_err()) {
        return Err("a reference name is 1..128 bytes of segments separated by '/', each 1..64 ASCII letters, digits or hyphens".into());
    }
    Ok(())
}

/// The file stem that holds a reference name (`lab/index` -> `lab.index`).
/// A segment never contains '.', so the spelling is reversible
/// (`ref_name_of_file`) and every per-name file stays one flat directory entry.
pub(crate) fn ref_file(name: &str) -> String {
    name.replace('/', ".")
}

/// The reference name a `ref_file` stem spells.
pub(crate) fn ref_name_of_file(stem: &str) -> String {
    stem.replace('.', "/")
}

pub(crate) fn private_dir(path: &Path) -> Result<()> {
    let named = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    if !named.file_type().is_dir()
        || named.uid() != unsafe { geteuid() }
        || named.mode() & 0o077 != 0
    {
        return Err(format!(
            "{} must be an owner-private directory",
            path.display()
        ));
    }
    Ok(())
}

pub(crate) fn make_private_dir(path: &Path) -> Result<()> {
    let mut builder = fs::DirBuilder::new();
    builder.mode(0o700);
    builder
        .create(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    private_dir(path)
}

pub(crate) fn private_file(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot write {}: {error}", path.display()))?;
    if let Some(parent) = path.parent() {
        File::open(parent)
            .and_then(|directory| directory.sync_all())
            .map_err(|error| format!("cannot sync {}: {error}", parent.display()))?;
    }
    Ok(())
}

pub(crate) fn bounded_json(path: &Path) -> Result<Value> {
    bounded_json_limit(path, MAX_RECORD)
}

fn bounded_json_limit(path: &Path, limit: u64) -> Result<Value> {
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() > limit {
        return Err(format!(
            "{} must be a bounded regular JSON file",
            path.display()
        ));
    }
    let mut bytes = Vec::new();
    File::open(path)
        .and_then(|file| file.take(limit + 1).read_to_end(&mut bytes))
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    if bytes.len() as u64 > limit {
        return Err(format!("{} exceeds workspace JSON bound", path.display()));
    }
    serde_json::from_slice(&bytes).map_err(|error| format!("invalid {}: {error}", path.display()))
}

pub(crate) fn member<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("workspace record lacks {key}"))
}

pub(crate) fn member_path(value: &Value, key: &str) -> Result<PathBuf> {
    let path = PathBuf::from(member(value, key)?);
    if !path.is_absolute() {
        return Err(format!("workspace {key} is not absolute"));
    }
    Ok(path)
}

/// The workspace's Host image, or the empty path of a remote workspace, which
/// holds no Host image and names its Host by the pinned `hostSha256` alone
/// (pinned for this process by `load`).
pub(crate) fn workspace_host(value: &Value) -> Result<PathBuf> {
    match value.get("host") {
        Some(Value::Null) if value.get("socket").and_then(Value::as_str).is_some_and(|socket| {
            crate::transport::is_remote(Path::new(socket))
        }) =>
        {
            Ok(PathBuf::new())
        }
        _ => member_path(value, "host"),
    }
}

/// The identifier namespace this workspace reserves fresh IDs in: the shared
/// root it was initialized with (`--namespace-root`), or else its own private
/// `ROOT/namespace`. Reservations are random 63-bit draws and the Host refuses
/// a collision, so a workspace without a shared root (a newcomer initialized
/// from its enrollment alone) can still create and re-delegate.
pub(crate) fn namespace_root(root: &Path, workspace: &Value) -> Result<PathBuf> {
    match workspace.get("namespaceRoot") {
        Some(Value::String(_)) => member_path(workspace, "namespaceRoot"),
        Some(Value::Null) | None => {
            let own = root.join("namespace");
            if !own.exists() {
                make_private_dir(&own)?;
            }
            Ok(own)
        }
        Some(_) => Err("workspace namespaceRoot is not a path".into()),
    }
}

fn os_string(value: OsString, label: &str) -> Result<String> {
    value
        .into_string()
        .map_err(|_| format!("{label} must be UTF-8"))
}

fn line_number(value: OsString, flag: &str) -> Result<usize> {
    os_string(value, flag)?
        .parse::<usize>()
        .ok()
        .filter(|line| *line > 0)
        .ok_or_else(|| format!("{flag} must be a line number, 1 or more"))
}

/// `Kernel/ContentResource.commandVersion`: the content command grammar v7
/// (createDocument … transclude 6, editElement 7, createContainer 8, unlink 9,
/// mark 10, unmark 11); v1–v6 frames are refused (`retired_command_refused`).
/// An observe-only `read` target is checked under it too.
const CONTENT_COMMAND_VERSION: &str = "7";
/// The declared scalar command version (`Kernel/DeclaredResourceScalar`).
const SCALAR_COMMAND_VERSION: &str = "1";

pub(crate) fn random_nonce() -> Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("cannot obtain workspace nonce: {error}"))?;
    Ok(u128::from_be_bytes(bytes).to_string())
}

pub(crate) fn new_attempt(root: &Path) -> Result<(PathBuf, String)> {
    for _ in 0..8 {
        let nonce = random_nonce()?;
        let attempt = root.join("attempts").join(format!("a-{nonce}"));
        if !attempt.exists() {
            return Ok((attempt, nonce));
        }
    }
    Err("could not allocate a distinct workspace attempt name".into())
}

pub(crate) fn load(root: &Path) -> Result<Value> {
    private_dir(root)?;
    private_dir(&root.join("refs"))?;
    private_dir(&root.join("attempts"))?;
    private_dir(&root.join("sources"))?;
    private_dir(&root.join("proposals"))?;
    let value = bounded_json(&root.join("workspace.json"))?;
    if member(&value, "type")? != "minidregg-participant-workspace-v1" {
        return Err("unknown participant workspace version".into());
    }
    decimal(member(&value, "subject")?, "workspace subject")?;
    let _ = member_path(&value, "config")?;
    let _ = member_path(&value, "key")?;
    if workspace_host(&value)?.as_os_str().is_empty() {
        crate::pin_remote_host(member(&value, "hostSha256")?)?;
    }
    match (value.get("socket").and_then(Value::as_str), SOCKET.get()) {
        (Some(socket), Some(selected)) if Path::new(socket) != selected => {
            return Err("selected socket differs from pinned workspace socket".into());
        }
        (Some(socket), None) => {
            let path = PathBuf::from(socket);
            if !path.is_absolute() && !crate::transport::is_remote(&path) {
                return Err("workspace socket is neither absolute nor a remote address".into());
            }
            SOCKET
                .set(path)
                .map_err(|_| "cannot pin workspace socket")?;
        }
        (None, Some(_)) => return Err("workspace has no pinned socket".into()),
        _ => {}
    }
    recheck_commitment(root, &value)?;
    Ok(value)
}

/// The commitment this workspace recorded at init: its next public key, or
/// `--no-prerotation`. A workspace without the record predates the check and
/// refuses to load.
fn recorded_commitment(value: &Value) -> Result<crate::key_rotation::Commitment> {
    match value.get("prerotation") {
        Some(Value::Bool(false)) => Ok(crate::key_rotation::Commitment::Without),
        Some(Value::Bool(true)) => {
            let next: [u8; 32] = private::decode_hex(member(value, "nextPublicKey")?)?
                .try_into()
                .map_err(|_| "workspace nextPublicKey is not 32 bytes")?;
            Ok(crate::key_rotation::Commitment::Mine(next))
        }
        _ => Err("this workspace records no key commitment (it predates the check that refuses a subject someone else can rotate): run `workspace --action init` again".into()),
    }
}

/// Once per process for each workspace: the subject's commitment is still this
/// workspace's own next key (FIX-IDENTITY). Every verb that loads a workspace
/// passes here; a friend never builds on a subject someone else can rotate.
fn recheck_commitment(root: &Path, value: &Value) -> Result<()> {
    static CHECKED: Mutex<Vec<PathBuf>> = Mutex::new(Vec::new());
    if CHECKED.lock().map_err(|_| "commitment check lock poisoned")?.iter().any(|known| known == root) {
        return Ok(());
    }
    let commitment = recorded_commitment(value)?;
    let socket = SOCKET.get().ok_or("workspace has no socket to check its key commitment over")?;
    let key = member_path(value, "key")?;
    let daily = ed25519_dalek::SigningKey::from_bytes(&*roomkey::seed_of(&key)?).verifying_key().to_bytes();
    crate::key_rotation::check_commitment(
        &workspace_host(value)?,
        socket,
        &member_path(value, "config")?,
        member(value, "subject")?,
        &daily,
        &commitment,
    )?;
    CHECKED.lock().map_err(|_| "commitment check lock poisoned")?.push(root.to_path_buf());
    Ok(())
}

/// After a rotation: the workspace's next key is now the key after next.
pub(crate) fn record_next_public(root: &Path, next: &[u8; 32]) -> Result<()> {
    let path = root.join("workspace.json");
    let mut value = bounded_json(&path)?;
    value["prerotation"] = json!(true);
    value["nextPublicKey"] = json!(hex(next));
    let mut bytes = serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    let staged = root.join(format!(".workspace.json.{}", random_nonce()?));
    private_file(&staged, &bytes)?;
    fs::rename(&staged, &path).map_err(|error| format!("cannot update {}: {error}", path.display()))
}

pub(crate) struct InitIdentity<'a> {
    pub(crate) key: Option<&'a Path>,
    pub(crate) subject: Option<&'a str>,
    pub(crate) enrollment: Option<&'a Path>,
    /// This friend's NEXT public key (default: KEY.next.pub beside the key).
    pub(crate) next_public: Option<&'a Path>,
    /// `--no-prerotation`: the friend holds no next key, knowingly.
    pub(crate) without_prerotation: bool,
}

/// `host` is `None` for a remote workspace: it pins the Host's SHA-256 (from
/// `--host-sha256`) and a remote socket address instead of a Host image.
pub(crate) fn init(
    root: &Path,
    host: Option<&Path>,
    config: &Path,
    identity: InitIdentity<'_>,
    birth_context: Option<&Path>,
    namespace_root: Option<&Path>,
) -> Result<()> {
    init_impl(root, host, config, identity, birth_context, namespace_root, None)
}

/// Fresh product onboarding only: the directory must not already exist.
pub(crate) fn init_fresh(
    root: &Path, host: Option<&Path>, config: &Path, identity: InitIdentity<'_>,
    birth_context: Option<&Path>, namespace_root: Option<&Path>,
    first_ref: &Value, verifier: Option<&Path>,
) -> Result<()> {
    init_impl(root, host, config, identity, birth_context, namespace_root, Some((receipt_continuity::fresh::FreshBaseline::Reference(first_ref), verifier)))
}
/// Used only after join has authenticated an exact enrollment receipt by lookup.
pub(crate) fn init_fresh_receipt(
    root: &Path, host: Option<&Path>, config: &Path, identity: InitIdentity<'_>,
    birth_context: Option<&Path>, namespace_root: Option<&Path>,
    receipt: &Value, verifier: &Path,
) -> Result<()> {
    init_impl(root, host, config, identity, birth_context, namespace_root,
        Some((receipt_continuity::fresh::FreshBaseline::AdmittedReceipt(receipt), Some(verifier))))
}
fn init_impl(
    root: &Path, host: Option<&Path>, config: &Path, identity: InitIdentity<'_>,
    birth_context: Option<&Path>, namespace_root: Option<&Path>,
    fresh: Option<(receipt_continuity::fresh::FreshBaseline<'_>, Option<&Path>)>,
) -> Result<()> {
    let receipt_baseline = matches!(fresh.as_ref(), Some((receipt_continuity::fresh::FreshBaseline::AdmittedReceipt(_), _)));
    let InitIdentity {
        key,
        subject,
        enrollment,
        next_public,
        without_prerotation,
    } = identity;
    let enrolled = enrollment
        .map(|path| {
            if key.is_some() || subject.is_some() {
                return Err("--enrollment cannot be combined with --key or --subject".into());
            }
            let bytes = crate::agent_reserve::private_bytes(path, MAX_RECORD as usize)?;
            let record: Value =
                serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
            if member(&record, "type")? != "minidregg-participant-enrollment-result-v1"
                || member(&record, "authority")? != "admitted-key-only"
            {
                return Err("workspace init requires an admitted enrollment result".into());
            }
            let subject = member(&record, "subject")?;
            decimal(subject, "enrolled subject")?;
            decimal(member(&record, "keyId")?, "enrolled key ID")?;
            let key = member_path(&record, "keyPath")?;
            let key_bytes = crate::agent_reserve::private_bytes(&key, 32)?;
            let seed: [u8; 32] = key_bytes
                .try_into()
                .map_err(|_| "enrolled key must be exactly 32 bytes")?;
            let public = ed25519_dalek::SigningKey::from_bytes(&seed)
                .verifying_key()
                .to_bytes();
            if member(&record, "publicKey")? != hex(&public) {
                return Err("enrollment public key differs from retained private key".into());
            }
            let receipt = record
                .get("receipt")
                .ok_or("enrollment lacks admitted receipt")?;
            for field in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
                field_decimal(member(receipt, field)?, field)?;
            }
            Ok::<_, String>((subject.to_owned(), key, bytes))
        })
        .transpose()?;
    let subject = enrolled
        .as_ref()
        .map(|value| value.0.as_str())
        .or(subject)
        .ok_or("workspace init requires --subject or --enrollment")?;
    let key = enrolled
        .as_ref()
        .map(|value| value.1.as_path())
        .or(key)
        .ok_or("workspace init requires --key or --enrollment")?;
    decimal(subject, "subject")?;
    let socket = SOCKET
        .get()
        .map(|socket| crate::transport::pinned_address(socket))
        .transpose()?;
    let (host, host_sha) = match host {
        Some(host) => {
            let host = absolute(host)?;
            if !host.is_file() {
                return Err("workspace Host must exist as a file".into());
            }
            (Some(host), None)
        }
        None => {
            if !socket.as_deref().is_some_and(|s| crate::transport::is_remote(Path::new(s))) {
                return Err("workspace init requires --host, or --remote with --host-sha256".into());
            }
            (None, Some(crate::host_image_sha256(Path::new(""))?))
        }
    };
    let config = absolute(config)?;
    let key = absolute(key)?;
    if !config.is_file() || !key.is_file() {
        return Err("workspace config and key must exist as files".into());
    }
    let context = birth_context.map(absolute).transpose()?;
    if let Some(context) = &context {
        let _ = bounded_json(context)?;
    }
    let namespace = namespace_root.map(absolute).transpose()?;
    // FIX-IDENTITY: the subject's pre-rotation commitment must be the digest of
    // THIS friend's next key (or none, knowingly), before anything is built on it.
    let next_public = match (next_public, without_prerotation) {
        (Some(_), true) => return Err("--next-pub and --no-prerotation exclude each other".into()),
        (Some(path), false) => Some(absolute(path)?),
        (None, true) => None,
        (None, false) => {
            let conventional = crate::key_rotation::conventional_next_public(&key);
            if !conventional.is_file() {
                return Err(format!(
                    "init checks that your subject commits to YOUR next key: {} is missing; pass --next-pub NEXT.pub, or --no-prerotation if this key has no next key",
                    conventional.display()
                ));
            }
            Some(conventional)
        }
    };
    let commitment = match &next_public {
        Some(path) => {
            let next: [u8; 32] = fs::read(path)
                .map_err(|error| format!("cannot read next public key {}: {error}", path.display()))?
                .try_into()
                .map_err(|_| format!("next public key {} must be 32 raw bytes", path.display()))?;
            crate::key_rotation::Commitment::Mine(next)
        }
        None => crate::key_rotation::Commitment::Without,
    };
    {
        let socket = SOCKET.get().ok_or("workspace init checks the subject's key commitment at the Host: pass --socket or --remote")?;
        let host_path = host.clone().unwrap_or_default();
        let daily = ed25519_dalek::SigningKey::from_bytes(&*roomkey::seed_of(&key)?).verifying_key().to_bytes();
        if crate::key_rotation::check_commitment(&host_path, socket, &config, subject, &daily, &commitment)?.is_none() {
            eprintln!("the Host holds no current key for subject {subject} yet: its commitment is checked when this workspace is next used");
        }
    }
    let root = absolute(root)?;
    make_private_dir(&root)?;
    make_private_dir(&root.join("refs"))?;
    make_private_dir(&root.join("sources"))?;
    make_private_dir(&root.join("attempts"))?;
    make_private_dir(&root.join("proposals"))?;
    let retained_enrollment = if let Some((_, _, bytes)) = &enrolled {
        let destination = root.join("enrollment.json");
        private_file(&destination, bytes)?;
        Some(destination)
    } else {
        None
    };
    let retained_context = if let Some(context) = &context {
        let bytes =
            fs::read(context).map_err(|error| format!("cannot retain birth context: {error}"))?;
        let destination = root.join("birth-context.json");
        private_file(&destination, &bytes)?;
        Some(destination)
    } else {
        None
    };
    let mut value = json!({"type":"minidregg-participant-workspace-v1", "host":host,
        "config":config,"key":key,"subject":subject,"socket":socket,
        "birthContext":retained_context,"namespaceRoot":namespace,
        "enrollment":retained_enrollment});
    match &commitment {
        crate::key_rotation::Commitment::Mine(next) => {
            value["prerotation"] = json!(true);
            value["nextPublicKey"] = json!(hex(next));
        }
        crate::key_rotation::Commitment::Without => value["prerotation"] = json!(false),
    }
    if let Some(sha) = host_sha {
        value["hostSha256"] = json!(sha);
    }
    if let Some((first_ref, verifier)) = fresh {
        receipt_continuity::fresh::prepare(&root, &mut value, first_ref, verifier)?;
    }
    let mut bytes = serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    private_file(&root.join("workspace.json"), &bytes)?;
    if !receipt_baseline { println!("{}", root.display()); }
    Ok(())
}

/// Completes or resumes only a pin created by `init_fresh`; never upgrades legacy.
pub(crate) fn complete_fresh_onboarding(root: &Path) -> Result<Value> {
    let workspace = load(root)?;
    receipt_continuity::fresh::complete(root, &workspace, |reference| {
        Ok(signed_view_unchecked(root, &workspace, reference, "resource")?.1)
    })
}

pub(crate) fn reference(root: &Path, name: &str) -> Result<Value> {
    validate_ref_name(name)?;
    let value = bounded_json(&root.join("refs").join(format!("{}.json", ref_file(name))))?;
    if member(&value, "type")? != "minidregg-participant-reference-v1"
        || member(&value, "name")? != name
    {
        return Err("workspace reference identity differs from its name".into());
    }
    let kind = member(&value, "kind")?;
    if !matches!(kind, "object" | "account" | "program") {
        return Err("workspace reference has unknown resource kind".into());
    }
    decimal(member(&value, "target")?, "reference target")?;
    decimal(
        member(&value, "observeCapability")?,
        "reference observe capability",
    )?;
    if let Some(operation) = value.get("operationCapability").and_then(Value::as_str) {
        decimal(operation, "reference operation capability")?;
    }
    if let Some(control) = value.get("controlCapability").and_then(Value::as_str) {
        decimal(control, "reference control capability")?;
    }
    Ok(value)
}

pub(crate) struct ImportInput<'a> {
    pub(crate) name: &'a str,
    pub(crate) kind: &'a str,
    pub(crate) target: &'a str,
    pub(crate) observe: &'a str,
    pub(crate) operation: Option<&'a str>,
    pub(crate) control: Option<&'a str>,
    pub(crate) provenance: Option<&'a Path>,
    /// The reference is a room: an imported room invite, or a room this
    /// workspace founded (`room new`). Discovery only; the Host decides.
    pub(crate) room: Option<&'a str>,
}

pub(crate) fn import(root: &Path, input: ImportInput<'_>) -> Result<()> {
    import_with_private_context(root, input, None)
}

// Write a newly imported reference once, including its verified sealing
// context. Never leave a temporarily public reference if a second write fails.
pub(crate) fn import_with_private_context(root: &Path, input: ImportInput<'_>, sealed: Option<(&str, &str)>) -> Result<()> {
    import_complete(root, input, sealed, None)
}
fn import_complete(root: &Path, input: ImportInput<'_>, sealed: Option<(&str, &str)>, room_private: Option<&Value>) -> Result<()> {
    let ImportInput {
        name: name_value,
        kind,
        target,
        observe,
        operation,
        control,
        provenance,
        room,
    } = input;
    validate_ref_name(name_value)?;
    if !matches!(kind, "object" | "account" | "program") {
        return Err("resource kind must be object, account or program".into());
    }
    decimal(target, "target")?;
    decimal(observe, "observe capability")?;
    if let Some(operation) = operation {
        decimal(operation, "operation capability")?;
    }
    if let Some(control) = control {
        decimal(control, "control capability")?;
    }
    let provenance = provenance.map(bounded_json).transpose()?;
    let mut value = json!({"type":"minidregg-participant-reference-v1","name":name_value,
        "kind":kind,"target":target,"observeCapability":observe,
        "operationCapability":operation.unwrap_or(observe),"controlCapability":control,
        "provenance":provenance,"authority":"hint-only"});
    if let Some(room) = room {
        value["room"] = json!(room);
    }
    if let Some((room, id)) = sealed {
        value["sealedIn"] = json!(room);
        value["sealedRoom"] = json!(id);
    }
    if let Some(private) = room_private { value["private"] = private.clone(); }
    let mut bytes = serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    private_file(
        &root.join("refs").join(format!("{}.json", ref_file(name_value))),
        &bytes,
    )?;
    println!("{name_value}");
    Ok(())
}

fn import_delegated(root: &Path, workspace: &Value, name: &str, source: &Path) -> Result<()> {
    let value = bounded_json(source)?;
    if member(&value, "type")? != "minidregg-delegated-reference-v1"
        || member(&value, "recipient")? != member(workspace, "subject")?
    {
        return Err("delegated reference is not addressed to this workspace subject".into());
    }
    let receipt = value
        .get("receipt")
        .ok_or("delegated reference lacks receipt")?;
    if member(receipt, "type")? != "confirmed"
        || !matches!(member(receipt, "confirmation")?, "installed" | "replayed")
    {
        return Err("delegated reference lacks confirmed admission receipt".into());
    }
    for field in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        field_decimal(member(receipt, field)?, field)?;
    }
    // A sender's room ID is only a routing hint. Prove membership under the
    // recipient's own room grant before retaining a local sealing context.
    let sealed_room = match value.get("sealedRoom") {
        None => None,
        Some(id) => {
            let id = id.as_str().ok_or("sealedRoom must be a decimal string")?;
            let room = private_room_name(root, id)?;
            let room_ref = reference(root, &room)?;
            let (since, _) = doc_query(root, workspace, &room_ref, "since", Some("0"), "view-since")?;
            require_room_member(&since, member(&value, "target")?)?;
            Some((room, id.to_owned()))
        }
    };
    import_complete(
        root,
        ImportInput {
            name,
            kind: member(&value, "kind")?,
            target: member(&value, "target")?,
            observe: member(&value, "capability")?,
            operation: Some(member(&value, "capability")?),
            control: None,
            provenance: Some(source),
            room: (value.get("room") == Some(&json!(true))).then_some("member"),
        },
        sealed_room.as_ref().map(|(room, id)| (room.as_str(), id.as_str())),
        value.get("private"),
    )
}

/// `since` filters each named cell by both room ancestry and the caller's
/// grant (NativeObservationController.sees). Call only on a signed result.
fn require_room_member(since: &Value, target: &str) -> Result<()> {
    decimal(target, "private document target")?;
    if since.get("entries").and_then(Value::as_array).is_some_and(|rows|
        rows.iter().any(|row| row.get("cells").and_then(Value::as_array)
            .is_some_and(|cells| cells.iter().any(|cell| cell.as_str() == Some(target))))) {
        Ok(())
    } else {
        Err("signed room history does not establish this document's membership".into())
    }
}

/// Resolve a stable room ID to a recipient-local private room, never to a
/// sender's petname. A room grant remains subject to live Host authorization.
fn private_room_name(root: &Path, target: &str) -> Result<String> {
    decimal(target, "private room target")?;
    let mut names = Vec::new();
    for file in fs::read_dir(root.join("refs")).map_err(|e| e.to_string())? {
        let file = file.map_err(|e| e.to_string())?;
        if file.path().extension().is_none_or(|ext| ext != "json") { continue; }
        let Ok(value) = bounded_json(&file.path()) else { continue };
        if value.get("target").and_then(Value::as_str) == Some(target)
            && value.get("kind").and_then(Value::as_str) == Some("object")
            && value.get("private").is_some_and(Value::is_object) {
            names.push(member(&value, "name")?.to_owned());
        }
    }
    names.sort();
    names.into_iter().next().ok_or_else(||
        "import the private room invitation before importing its document".into())
}

fn list(root: &Path) -> Result<()> {
    let mut values = Vec::new();
    for entry in fs::read_dir(root.join("refs")).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let file = entry.file_name();
        let Some(file) = file.to_str() else {
            return Err("non-UTF-8 reference name".into());
        };
        let Some(stem) = file.strip_suffix(".json") else {
            return Err("unknown file in references".into());
        };
        values.push(reference(root, &ref_name_of_file(stem))?);
    }
    values.sort_by(|a, b| a["name"].as_str().cmp(&b["name"].as_str()));
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({"type":"minidregg-workspace-list-v1",
        "references":values,"authority":"discovery-only"}))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

/// Ephemeral reads keep only one line per read in this rotating journal
/// (`unix-time  height  read  outcome  clock-now  reference`).
const READ_JOURNAL: &str = "read-journal.tsv";
const READ_JOURNAL_LIMIT: u64 = 1 << 20;

fn read_journal(root: &Path, height: &str, outcome: &str, now: &str, name: &str) -> Result<()> {
    let path = root.join(READ_JOURNAL);
    if fs::metadata(&path).map(|meta| meta.len() >= READ_JOURNAL_LIMIT).unwrap_or(false) {
        fs::rename(&path, root.join(format!("{READ_JOURNAL}.1")))
            .map_err(|error| format!("cannot rotate {}: {error}", path.display()))?;
    }
    let unix = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|_| "wall clock is before the unix epoch")?
        .as_secs();
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .mode(0o600)
        .open(&path)
        .map_err(|error| format!("cannot open {}: {error}", path.display()))?;
    file.write_all(format!("{unix}\t{height}\tread\t{outcome}\t{now}\t{name}\n").as_bytes())
        .map_err(|error| format!("cannot append {}: {error}", path.display()))
}

/// The coordinates a read was judged at, from its retained challenge: the world root,
/// the height, and the deployment clock the resource's law saw
/// (`NativeObservationController.read_judged_at_named_clock`).
fn judged_at(attempt: &Path) -> Result<Value> {
    let challenge = bounded_json(&attempt.join("challenge.json"))?;
    Ok(json!({"worldRoot": challenge.get("worldRoot"), "height": challenge.get("height"),
        "clock": challenge.get("clock")}))
}

pub(crate) fn read(
    root: &Path,
    workspace: &Value,
    resource_name: &str,
    view: &str,
    window: Option<(&str, &str)>,
    ephemeral: bool,
) -> Result<()> {
    let ticket = receipt_continuity::begin(root, workspace)?;
    let reference = reference(root, resource_name)?;
    let (attempt, nonce) = new_attempt(root)?;
    let mut intent = json!({"subject":member(workspace,"subject")?,"nonce":nonce,
        "purpose":{"type":"query","kind":member(&reference,"kind")?,
            "target":member(&reference,"target")?,"view":view},
        "grants":[{"kind":member(&reference,"kind")?,"target":member(&reference,"target")?,
            "capability":member(&reference,"observeCapability")?}]});
    // A stream window (`tail`): the entries at positions start .. start+count-1.
    if let Some((start, count)) = window {
        field_decimal(start, "tail start")?;
        field_decimal(count, "tail count")?;
        intent["purpose"]["start"] = json!(start);
        intent["purpose"]["count"] = json!(count);
    }
    let mut bytes = serde_json::to_vec_pretty(&intent).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    let source = root.join("sources").join(format!("q-{nonce}.json"));
    private_file(&source, &bytes)?;
    if !ephemeral {
        eprintln!("workspace read attempt: {}", attempt.display());
    }
    let answered = query_retained(
        &workspace_host(workspace)?,
        &member_path(workspace, "config")?,
        &source,
        OsStr::new("intent"),
        &member_path(workspace, "key")?,
        &format!("view-{view}"),
        &attempt,
    );
    let judged = judged_at(&attempt).ok();
    if answered.is_ok() {
        let challenge = bounded_json(&attempt.join("challenge.json"))?;
        receipt_continuity::finish(root, workspace, ticket, &challenge, ContinuityMode::Ordinary)?;
    }
    if ephemeral {
        // A read commits nothing: once its answer (or refusal) is in hand the attempt
        // and its intent source are not needed for any retry. One journal line stays.
        let at = |name: &str| -> String {
            judged
                .as_ref()
                .and_then(|value| value.get(name))
                .and_then(Value::as_str)
                .unwrap_or("-")
                .to_string()
        };
        let now = judged
            .as_ref()
            .and_then(|value| value.pointer("/clock/now"))
            .and_then(Value::as_str)
            .unwrap_or("-")
            .to_string();
        let outcome = if answered.is_ok() { "answered" } else { "refused" };
        read_journal(root, &at("height"), outcome, &now, resource_name)?;
        if attempt.exists() {
            fs::remove_dir_all(&attempt)
                .map_err(|error| format!("cannot remove {}: {error}", attempt.display()))?;
        }
        fs::remove_file(&source)
            .map_err(|error| format!("cannot remove {}: {error}", source.display()))?;
    }
    let mut answered = answered?;
    if let (Some(object), Some(judged)) = (answered.as_object_mut(), judged) {
        object.insert("judgedAt".to_owned(), judged);
    }
    print_json(&answered)
}

/// The workspace's own reference names for a cell, else the cell id.
fn cell_label(root: &Path, cell: &str) -> String {
    let mut names: Vec<String> = fs::read_dir(root.join("refs"))
        .into_iter()
        .flatten()
        .flatten()
        .filter_map(|entry| {
            let file = entry.file_name().to_string_lossy().into_owned();
            let stem = ref_name_of_file(file.strip_suffix(".json")?);
            let value = reference(root, &stem).ok()?;
            (value.get("target").and_then(Value::as_str) == Some(cell)).then_some(stem)
        })
        .collect();
    names.sort();
    if names.is_empty() {
        cell.to_owned()
    } else {
        names.join(",")
    }
}

/// `doc backlinks NAME` / `doc links NAME`: one signed query of the Host's link
/// index (K-DOC-INDEX). Backlinks name only source documents a standing grant
/// of this workspace's subject covers; the Host decides that, not the client.
fn doc_link_view(root: &Path, workspace: &Value, name: &str, view: &str) -> Result<()> {
    let own = reference(root, name)?;
    let (result, challenge, _) = signed_view(root, workspace, &own, view)?;
    let rows = result
        .get("rows")
        .and_then(Value::as_array)
        .ok_or("link view lacks rows")?;
    let document = member(&own, "target")?;
    let height = member(&challenge, "height")?;
    let backlinks = view == "backlinks";
    if backlinks {
        println!(
            "# backlinks to {name} (document {document}) from the documents this workspace can read at height {height}"
        );
    } else {
        println!("# links from {name} (document {document}) at height {height}");
    }
    let mut contexts = std::collections::BTreeMap::<String, Option<crate::render::Rendered>>::new();
    for row in rows {
        if backlinks {
            println!(
                "{} link {} relation {} revision {} since {} target {} {}",
                cell_label(root, member(row, "source")?),
                member(row, "link")?,
                member(row, "relation")?,
                member(row, "revision")?,
                member(row, "height")?,
                member(row, "kind")?,
                member(row, "target")?
            );
            if let Some(context) = backlink_context(root, workspace, &mut contexts, row)? {
                println!("    {context}");
            }
        } else {
            println!(
                "link {} -> {} {} relation {} revision {} since {}",
                member(row, "link")?,
                member(row, "kind")?,
                cell_label(root, member(row, "target")?),
                member(row, "relation")?,
                member(row, "revision")?,
                member(row, "height")?
            );
        }
    }
    println!(
        "# {} {}",
        rows.len(),
        if backlinks { "backlink(s)" } else { "link(s)" }
    );
    Ok(())
}

pub(crate) fn signed_view(
    root: &Path,
    workspace: &Value,
    reference: &Value,
    view: &str,
) -> Result<(Value, Value, PathBuf)> {
    let ticket = receipt_continuity::begin(root, workspace)?;
    let (result, challenge, signed) = signed_view_unchecked(root, workspace, reference, view)?;
    receipt_continuity::finish(root, workspace, ticket, &challenge, ContinuityMode::Ordinary)?;
    Ok((result, challenge, signed))
}

// Only explicit legacy init or durably pinned fresh onboarding may establish first trust.
fn signed_view_unchecked(
    root: &Path,
    workspace: &Value,
    reference: &Value,
    view: &str,
) -> Result<(Value, Value, PathBuf)> {
    let (attempt, nonce) = new_attempt(root)?;
    let intent = json!({"subject":member(workspace,"subject")?,"nonce":nonce,
        "purpose":{"type":"query","kind":member(reference,"kind")?,
            "target":member(reference,"target")?,"view":view},
        "grants":[{"kind":member(reference,"kind")?,"target":member(reference,"target")?,
            "capability":member(reference,"observeCapability")?}]});
    let source = root.join("sources").join(format!("q-{nonce}.json"));
    private_file(
        &source,
        &serde_json::to_vec(&intent).map_err(|error| error.to_string())?,
    )?;
    let inspection = if view == "capability" {
        format!("view-{}-capability", member(reference, "kind")?)
    } else {
        format!("view-{view}")
    };
    let result = query_retained(
        &workspace_host(workspace)?,
        &member_path(workspace, "config")?,
        &source,
        OsStr::new("intent"),
        &member_path(workspace, "key")?,
        &inspection,
        &attempt,
    )?;
    let challenge = bounded_json(&attempt.join("challenge.json"))?;
    Ok((result, challenge, attempt.join("signed-observation.bin")))
}

/// A signed query of a referenced resource with `view` (and `height` for
/// `since`/`at`), retained in a fresh attempt. The Host renders `view.bin`
/// with `inspection`; returns that rendering and the attempt directory.
fn doc_query(
    root: &Path,
    workspace: &Value,
    reference: &Value,
    view: &str,
    height: Option<&str>,
    inspection: &str,
) -> Result<(Value, PathBuf)> {
    let ticket = receipt_continuity::begin(root, workspace)?;
    let (attempt, nonce) = new_attempt(root)?;
    let mut purpose = json!({"type":"query","kind":member(reference,"kind")?,
        "target":member(reference,"target")?,"view":view});
    if let Some(height) = height {
        decimal(height, "height")?;
        purpose["height"] = json!(height);
    }
    let intent = json!({"subject":member(workspace,"subject")?,"nonce":nonce,"purpose":purpose,
        "grants":[{"kind":member(reference,"kind")?,"target":member(reference,"target")?,
            "capability":member(reference,"observeCapability")?}]});
    let source = root.join("sources").join(format!("q-{nonce}.json"));
    private_file(
        &source,
        &serde_json::to_vec(&intent).map_err(|error| error.to_string())?,
    )?;
    eprintln!("workspace read attempt: {}", attempt.display());
    let value = query_retained(
        &workspace_host(workspace)?,
        &member_path(workspace, "config")?,
        &source,
        OsStr::new("intent"),
        &member_path(workspace, "key")?,
        inspection,
        &attempt,
    )?;
    let challenge = bounded_json(&attempt.join("challenge.json"))?;
    let mode = if view == "at" { ContinuityMode::Historical } else { ContinuityMode::Ordinary };
    receipt_continuity::finish(root, workspace, ticket, &challenge, mode)?;
    Ok((value, attempt))
}

/// A signed read of one reference `at` a past height (K-HISTORY-READ), under
/// the grant as it stood at that height: the retained `view.bin` (an
/// `atViewCodec` binary) and its presentation.
fn signed_at(
    root: &Path,
    workspace: &Value,
    reference: &Value,
    height: &str,
) -> Result<(Value, PathBuf)> {
    let (value, attempt) = doc_query(root, workspace, reference, "at", Some(height), "view-at")?;
    Ok((value, attempt.join("view.bin")))
}

/// The referencing line of one backlink, rendered: the line of the source
/// document that carries the link as a mark, read by this workspace's own
/// signed read of the source.  `None` when this workspace holds no reference
/// to the source, its read is refused, or the link is no line's mark (a
/// transclusion's or a range's link).  One read per source document.
fn backlink_context(
    root: &Path,
    workspace: &Value,
    cache: &mut std::collections::BTreeMap<String, Option<crate::render::Rendered>>,
    row: &Value,
) -> Result<Option<String>> {
    let source = member(row, "source")?.to_owned();
    if !cache.contains_key(&source) {
        let rendered = match reference_for_target(root, &source)? {
            Some(reference) => host_document(root, workspace, &reference).ok().and_then(|document| {
                let names = reference_names(root);
                crate::render::render(&crate::render::View {
                    document: &document,
                    entries: &[],
                    names: &names,
                    sources: &std::collections::BTreeMap::new(),
                    me: member(workspace, "subject").unwrap_or(""),
                })
                .ok()
            }),
            None => None,
        };
        cache.insert(source.clone(), rendered);
    }
    let link = member(row, "link")?;
    let Some(Some(rendered)) = cache.get(&source) else {
        return Ok(None);
    };
    Ok(rendered
        .lines
        .iter()
        .find(|line| {
            line.row["marks"]
                .as_array()
                .is_some_and(|marks| marks.iter().any(|mark| mark["link"].as_str() == Some(link)))
        })
        .map(|line| {
            let number = line.line.map_or("-".to_owned(), |n| n.to_string());
            format!("line {number}: {}", crate::render::text::line_notation(line))
        }))
}

fn entries(view: &Value) -> Result<&Vec<Value>> {
    view.get("cell")
        .and_then(|cell| cell.get("entries"))
        .and_then(Value::as_array)
        .ok_or_else(|| "signed view is not a content cell".to_owned())
}

/// The workspace reference naming cell `target`, if this workspace holds one.
fn reference_for_target(root: &Path, target: &str) -> Result<Option<Value>> {
    let dir = root.join("refs");
    let Ok(listing) = fs::read_dir(&dir) else {
        return Ok(None);
    };
    let mut names: Vec<String> = listing
        .filter_map(|entry| entry.ok())
        .filter_map(|entry| entry.file_name().into_string().ok())
        .filter_map(|name| name.strip_suffix(".json").map(ref_name_of_file))
        .collect();
    names.sort();
    for name in names {
        if let Ok(value) = reference(root, &name) {
            if member(&value, "target")? == target {
                return Ok(Some(value));
            }
        }
    }
    Ok(None)
}

/// `transclude`: one transaction that transcludes the atoms FROM..TO of one
/// run of SOURCE into HOST.  HOST's target carries the content action; SOURCE's
/// carries an observe-only `read`, so the admission checks this workspace's
/// own observe grant on SOURCE, and the source's policy, at this height.  The
/// opening (the range's live atoms at their revisions) is what this signed read
/// of SOURCE shows; the Host refuses it `staleOpening` if SOURCE moved since.
fn transclude(
    root: &Path,
    workspace: &Value,
    host: &str,
    source: &str,
    from: &str,
    to: &str,
    live: bool,
    death: &str,
    at: Option<usize>,
) -> Result<()> {
    decimal(from, "first atom")?;
    decimal(to, "last atom")?;
    if !matches!(
        death,
        "invalidate"
            | "keepTombstone"
            | "preferPrevious"
            | "preferNext"
            | "preferPreviousThenNext"
            | "preferNextThenPrevious"
    ) {
        return Err("--death must name an endpoint death policy".into());
    }
    let source_ref = reference(root, source)?;
    let (view, _, _) = signed_view(root, workspace, &source_ref, "resource")?;
    let cell = entries(&view)?;
    let has = |run: &Value, atom: &str| {
        run.get("atoms")
            .and_then(Value::as_array)
            .is_some_and(|atoms| atoms.iter().any(|value| value.as_str() == Some(atom)))
    };
    let run = cell
        .iter()
        .find(|entry| {
            entry.get("type").and_then(Value::as_str) == Some("run") && has(entry, from) && has(entry, to)
        })
        .ok_or("no run of the source holds both endpoints")?;
    let atoms: Vec<&str> = run["atoms"]
        .as_array()
        .ok_or("run lacks atoms")?
        .iter()
        .filter_map(Value::as_str)
        .collect();
    let first = atoms.iter().position(|atom| *atom == from).ok_or("first atom not in run")?;
    let last = atoms.iter().position(|atom| *atom == to).ok_or("last atom not in run")?;
    if first > last {
        return Err("the range's first atom follows its last".into());
    }
    let target = member(&source_ref, "target")?;
    let mut pins = Vec::new();
    for atom in &atoms[first..=last] {
        let record = cell.iter().find(|entry| {
            entry.get("type").and_then(Value::as_str) == Some("atom")
                && entry.get("id").and_then(Value::as_str) == Some(atom)
        });
        if let Some(record) = record {
            if record.get("tombstonedAt").is_some_and(Value::is_null)
                && member(record, "document")? == target
            {
                pins.push(json!({"atom":atom,"revision":member(record,"revision")?}));
            }
        }
    }
    let point = |atom: &str, bias: &str| {
        json!({"run":run["id"],"neighbor":atom,"bias":bias,"death":death})
    };
    let id = random_nonce()?;
    let mut actions = vec![json!({"type":"transclude",
        "transclusion":id,"link":random_nonce()?,
        "request":{"source":target,"range":{"start":point(from,"before"),"finish":point(to,"after")},
            "mode":if live {"live"} else {"snapshot"},"pins":pins}})];
    if let Some(at) = at {
        let host_ref = reference(root, host)?;
        actions.extend(place_new_leaf(&host_document(root, workspace, &host_ref)?, &id, at)?);
    }
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[
        {"name":host,"payload":{"type":"content","actions":actions}},
        {"name":source,"payload":{"type":"read"}}]});
    let proposal_id = format!("transclude-{id}");
    let request_path = root.join("sources").join(format!("{proposal_id}.json"));
    private_file(
        &request_path,
        &serde_json::to_vec(&request).map_err(|error| error.to_string())?,
    )?;
    propose(root, workspace, &request_path, &proposal_id, None)?;
    eprintln!("workspace transclusion: {id}");
    let attempt = root.join("attempts").join(&proposal_id);
    submit_intent(
        root,
        workspace,
        &root.join("proposals").join(&proposal_id).join("intent.json"),
        "intent",
        false,
        Some(attempt.as_path()),
    )
}

/// HOST's document as the kernel orders it (`inspect view-document`: the
/// pre-order walk of its element tree), with its transclusions rendered over
/// this workspace's own source reads: a current read of each source this
/// workspace can read (a refused read contributes nothing, so the transclusion
/// renders `unavailable` with its shape only), and, for a snapshot whose pins
/// moved, a read of the source `at` the opening's height.  With `only`, that one
/// transclusion, and its source read must succeed (`follow`: re-resolve at the
/// current height).  Returns HOST's target, the kernel's document view, and the
/// rendered transclusions, each with its `text`.
/// What one `doc show` read: HOST's reference target, the host page's
/// presentation (a resource view; at a past height the `at` view's `resource`,
/// null when the cell was not live then), the attempt directory of the host
/// read (its `challenge.json`), the kernel's `view-document` (transclusions
/// re-read `at` their opening height where they `moved`), the host cell's
/// signed entries, the rendered transclusions each with its `text`, and, per
/// source this workspace could read, the source's own live line numbers.
pub(crate) struct DocumentRead {
    pub host: String,
    pub view: Value,
    pub attempt: PathBuf,
    pub document: Value,
    pub entries: Vec<Value>,
    pub shown: Vec<Value>,
    pub sources: std::collections::BTreeMap<String, std::collections::BTreeMap<String, usize>>,
}

/// Open a separate presentation copy. The signed raw view remains unchanged
/// and is the only source of mutation guards.
pub(crate) fn opened_entries(root: &Path, workspace: &Value, reference: &Value, view: &Value) -> Result<Vec<Value>> {
    if view.is_null() { return Ok(Vec::new()); }
    let mut display = view.clone();
    if entries(view)?.iter().any(|entry| protected_document::is_kind(&entry["kind"])) {
        display["cell"]["entries"] = json!(protected_document::opened_entries(root, reference, view)?);
    }
    let has_private = entries(view)?.iter().any(|entry| entry["type"] == "atom"
        && entry["kind"] == json!({"type":"inlineObject","schema":private::schema_decimal()}));
    if has_private {
        match sealing_room(None, root, reference)? {
            Some(room) => {
                let (room_id, keys) = roomkey::reader_keys(root, workspace, &room)?;
                private::open_view(&mut display, &room_id, member(reference,"target")?, keys.as_ref());
            }
            None => { private::open_view(&mut display, "", member(reference,"target")?, None); }
        }
    }
    Ok(entries(&display)?.clone())
}

pub(crate) fn rendered_document(
    root: &Path,
    workspace: &Value,
    host_name: &str,
    only: Option<&str>,
    at: Option<&str>,
) -> Result<DocumentRead> {
    let host_ref = reference(root, host_name)?;
    // The host page: current, or `at` a past height under the grant as it stood
    // then (the Host refuses the read otherwise; that refusal is the answer).
    let (host_view, host_bin) = match at {
        None => {
            let (view, _, signed) = signed_view(root, workspace, &host_ref, "resource")?;
            (view, signed.with_file_name("view.bin"))
        }
        Some(height) => {
            let (view, bin) = signed_at(root, workspace, &host_ref, height)?;
            (view["resource"].clone(), bin)
        }
    };
    let host_attempt = host_bin
        .parent()
        .ok_or("host read lacks its attempt directory")?
        .to_path_buf();
    let host_bin = fs::read(host_bin).map_err(|error| error.to_string())?;
    let host_entries: Vec<Value> = if at.is_some() && host_view.is_null() {
        Vec::new()
    } else {
        entries(&host_view)?.clone()
    };
    let records: Vec<&Value> = host_entries
        .iter()
        .filter(|entry| entry.get("type").and_then(Value::as_str) == Some("transclusion"))
        .filter(|entry| only.is_none_or(|id| entry.get("id").and_then(Value::as_str) == Some(id)))
        .collect();
    if let Some(id) = only {
        if records.is_empty() {
            return Err(format!("{host_name} holds no transclusion {id}"));
        }
    }
    let mut sources = Vec::new();
    let mut source_bins = std::collections::BTreeMap::<String, Vec<u8>>::new();
    let mut readable = std::collections::BTreeMap::new();
    for record in &records {
        let source = member(&record["opening"], "source")?.to_owned();
        if readable.contains_key(&source) {
            continue;
        }
        // A page at height H reads each source `at` H too: what the reader
        // could see then, under its grants as they stood then.
        let attempt = |reference: &Value| -> Result<(Value, Vec<u8>)> {
            match at {
                None => {
                    let (_, _, signed) = signed_view(root, workspace, reference, "resource")?;
                    let bin = fs::read(signed.with_file_name("view.bin")).map_err(|error| error.to_string())?;
                    Ok((json!({"target":source,"view":hex(&bin)}), bin))
                }
                Some(height) => {
                    let (view, bin) = signed_at(root, workspace, reference, height)?;
                    if view["state"] != "live" {
                        return Err(format!("source {source} is not live at height {height}"));
                    }
                    let bin = fs::read(bin).map_err(|error| error.to_string())?;
                    Ok((json!({"target":source,"at":hex(&bin)}), bin))
                }
            }
        };
        let read = match reference_for_target(root, &source)? {
            Some(reference) => match attempt(&reference) {
                Ok((read, bin)) => {
                    sources.push(read);
                    source_bins.insert(source.clone(), bin);
                    Some(reference)
                }
                Err(error) if only.is_some() => {
                    return Err(format!("follow refused: no read of source {source}: {error}"))
                }
                Err(_) => None,
            },
            None if only.is_some() => {
                return Err(format!("follow refused: no reference to source {source}"))
            }
            None => None,
        };
        readable.insert(source, read);
    }
    let render = |host: &[u8], sources: &Vec<Value>| -> Result<Value> {
        let (attempt, _) = new_attempt(root)?;
        make_private_dir(&attempt)?;
        let input = attempt.join("transclusions-in.json");
        private_file(
            &input,
            &serde_json::to_vec(&json!({"host":hex(host),"sources":sources}))
                .map_err(|error| error.to_string())?,
        )?;
        inspect(
            &workspace_host(workspace)?,
            &member_path(workspace, "config")?,
            "view-document",
            &input,
            &attempt.join("transclusions.json"),
        )
    };
    let mut current = render(&host_bin, &sources)?;
    // Each readable source placed in its own order, so a transclusion's header
    // names the source lines it covers.  A source cell with no document has no
    // lines to name; its header says `?`.
    let mut source_lines = std::collections::BTreeMap::new();
    for (source, bin) in &source_bins {
        if let Ok(view) = render(bin, &Vec::new()) {
            source_lines.insert(source.clone(), crate::render::line_numbers(&view));
        }
    }
    let names = reference_names(root);
    let mut shown = Vec::new();
    let items = current["transclusions"].as_array().ok_or("Host rendered no transclusions")?.clone();
    let mut resolved = Vec::new();
    for item in items {
        let mut item = item.clone();
        let source = member(&item["opening"], "source")?.to_owned();
        if member(&item["render"], "view")? == "moved" {
            if let Some(Some(reference)) = readable.get(&source) {
                let height = member(&item["opening"], "height")?.to_owned();
                // The snapshot is rendered by a read of the source `at` its
                // opening height, which the Host answers only when this
                // reader's grant stood then. A reader granted later keeps the
                // `moved` placeholder: it is told the lines moved, not shown them.
                match signed_at(root, workspace, reference, &height) {
                    Ok((_, bin)) => {
                        let at = fs::read(&bin).map_err(|error| error.to_string())?;
                        let again = render(&host_bin, &vec![json!({"target":source,"at":hex(&at)})])?;
                        if let Some(found) = again["transclusions"].as_array().and_then(|all| {
                            all.iter().find(|other| other.get("id") == item.get("id"))
                        }) {
                            item["render"] = found["render"].clone();
                            item["at"] = json!(height);
                        }
                    }
                    Err(_) if history_refused() => item["atRefused"] = json!(height),
                    Err(error) => return Err(error),
                }
            }
        }
        resolved.push(item.clone());
        if only.is_some_and(|id| item.get("id").and_then(Value::as_str) != Some(id)) {
            continue;
        }
        let t = crate::render::transcluded(&names, &source_lines, &item);
        let mut text = t.header.clone();
        for line in &t.lines {
            text.push('\n');
            text.push_str(line);
        }
        item["text"] = json!(text);
        shown.push(item);
    }
    current["transclusions"] = Value::Array(resolved);
    let display_entries = opened_entries(root, workspace, &host_ref, &host_view)?;
    Ok(DocumentRead {
        host: member(&host_ref, "target")?.to_owned(),
        view: host_view,
        attempt: host_attempt,
        document: current,
        entries: display_entries,
        shown,
        sources: source_lines,
    })
}

/// `transclusions` / `follow`: HOST's rendered transclusions.
fn transclusions(root: &Path, workspace: &Value, host_name: &str, only: Option<&str>) -> Result<()> {
    let read = rendered_document(root, workspace, host_name, only, None)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({"type":"transclusions","host":read.host,
            "transclusions":read.shown}))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

/// The kernel's document view of one reference, without rendering any
/// transclusion: what placement needs (the order, each element's parent, each
/// container's revision).
fn host_document(root: &Path, workspace: &Value, host_ref: &Value) -> Result<Value> {
    let (_, _, signed) = signed_view(root, workspace, host_ref, "resource")?;
    let host_bin = fs::read(signed.with_file_name("view.bin")).map_err(|error| error.to_string())?;
    let (attempt, _) = new_attempt(root)?;
    make_private_dir(&attempt)?;
    let input = attempt.join("document-in.json");
    private_file(
        &input,
        &serde_json::to_vec(&json!({"host":hex(&host_bin),"sources":[]}))
            .map_err(|error| error.to_string())?,
    )?;
    inspect(
        &workspace_host(workspace)?,
        &member_path(workspace, "config")?,
        "view-document",
        &input,
        &attempt.join("document.json"),
    )
}

/// The document's lines: the leaves of the kernel's order that a reader reads
/// as a line — a live atom or a transclusion.  A struck atom stands in the order
/// but is no line, so line numbers, `doc show`'s and a refusal's, agree.
fn live_lines(document: &Value) -> Result<Vec<&Value>> {
    Ok(document["order"]
        .as_array()
        .ok_or("document view has no order")?
        .iter()
        .filter(|entry| match entry["kind"].as_str() {
            Some("atom") => entry["struck"] != true,
            Some("embed") => true,
            _ => false,
        })
        .collect())
}

/// Where element ELEMENT stands: its container, that container's revision as
/// this view read it, and its index among the container's children (struck
/// lines and sections included: they are children too).
fn place_of(document: &Value, element: &str) -> Result<(String, String, usize)> {
    let order = document["order"].as_array().ok_or("document view has no order")?;
    let entry = order
        .iter()
        .find(|entry| entry["element"].as_str() == Some(element))
        .ok_or("element is not in the document's order")?;
    let parent = member(entry, "parent")?.to_owned();
    let index = order
        .iter()
        .filter(|other| other["parent"].as_str() == Some(parent.as_str()))
        .position(|other| other["element"].as_str() == Some(element))
        .ok_or("element is not among its parent's children")?;
    Ok((parent.clone(), container_revision(document, &parent)?, index))
}

fn container_revision(document: &Value, container: &str) -> Result<String> {
    if document["root"].as_str() == Some(container) {
        return Ok(member(document, "rootRevision")?.to_owned());
    }
    let order = document["order"].as_array().ok_or("document view has no order")?;
    order
        .iter()
        .find(|entry| entry["element"].as_str() == Some(container) && entry["kind"] == "container")
        .map(|entry| member(entry, "revision").map(str::to_owned))
        .ok_or_else(|| "no such section".to_owned())?
}

/// The element of line N (1-based).
fn line_element(document: &Value, line: usize) -> Result<String> {
    let lines = live_lines(document)?;
    if line == 0 || line > lines.len() {
        return Err(format!("the document has {} lines; there is no line {line}", lines.len()));
    }
    Ok(member(lines[line - 1], "element")?.to_owned())
}

fn edit_element(container: &str, revision: &str, op: Value) -> Value {
    json!({"type":"editElement","element":container,"revision":revision,"op":op})
}

/// The edits that place LEAF — appended to the root by the action that creates
/// it, in the same command — at line AT: where the line now numbered AT stands,
/// in that line's container, which shifts it and every later line down by one.
/// AT one past the last line is the append itself: no edit.  Each edit names
/// the revision of its container this view read, so a container whose children
/// moved since is refused `staleElement` and nothing lands.  This replaces
/// minting an identifier between two neighbours (K-DOC-ORDER): an insert costs
/// one edit however many inserts went to the same spot before it.
fn place_new_leaf(document: &Value, leaf: &str, at: usize) -> Result<Vec<Value>> {
    let lines = live_lines(document)?;
    if at == lines.len() + 1 {
        return Ok(Vec::new());
    }
    let root = member(document, "root")?;
    let (parent, revision, index) = place_of(document, &line_element(document, at)?)?;
    if parent == root {
        Ok(vec![edit_element(&parent, &revision, json!({"type":"move","child":leaf,"index":index.to_string()}))])
    } else {
        Ok(vec![
            edit_element(root, member(document, "rootRevision")?, json!({"type":"remove","child":leaf})),
            edit_element(&parent, &revision, json!({"type":"splice","index":index.to_string(),"child":leaf})),
        ])
    }
}

/// The edits that move line FROM to stand where line TO stands now.
fn move_line(document: &Value, from: usize, to: usize) -> Result<Vec<Value>> {
    let element = line_element(document, from)?;
    let (source, source_revision, _) = place_of(document, &element)?;
    let (target, target_revision, index) = place_of(document, &line_element(document, to)?)?;
    if from == to {
        return Err("a line moved to where it stands is no edit".into());
    }
    if source == target {
        Ok(vec![edit_element(&source, &source_revision, json!({"type":"move","child":element,"index":index.to_string()}))])
    } else {
        Ok(vec![
            edit_element(&source, &source_revision, json!({"type":"remove","child":element})),
            edit_element(&target, &target_revision, json!({"type":"splice","index":index.to_string(),"child":element})),
        ])
    }
}

/// One content command on NAME, proposed and submitted.
fn submit_content(root: &Path, workspace: &Value, name: &str, actions: Vec<Value>, label: &str) -> Result<()> {
    let id = random_nonce()?;
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[
        {"name":name,"payload":{"type":"content","actions":actions}}]});
    let proposal_id = format!("{label}-{id}");
    let request_path = root.join("sources").join(format!("{proposal_id}.json"));
    private_file(
        &request_path,
        &serde_json::to_vec(&request).map_err(|error| error.to_string())?,
    )?;
    propose(root, workspace, &request_path, &proposal_id, None)?;
    let attempt = root.join("attempts").join(&proposal_id);
    submit_intent(
        root,
        workspace,
        &root.join("proposals").join(&proposal_id).join("intent.json"),
        "intent",
        false,
        Some(attempt.as_path()),
    )
}

/// The atoms of live lines FROM..TO of NAME (`doc show`'s numbering), each a
/// text line: a transclusion line is the source's lines, not this document's.
fn line_atoms(document: &Value, name: &str, from: usize, to: usize) -> Result<Vec<String>> {
    let lines = live_lines(document)?;
    if from > to || to > lines.len() {
        return Err(format!("{name} has {} lines; lines {from}..{to} are not a range of them", lines.len()));
    }
    lines[from - 1..to]
        .iter()
        .enumerate()
        .map(|(offset, line)| match line["kind"].as_str() {
            Some("atom") => member(line, "atom").map(str::to_owned),
            _ => Err(format!("line {} of {name} is a transclusion, not a line of {name}", from + offset)),
        })
        .collect()
}

/// `transclude --from-line --to-line`: the first and last atom of SOURCE's
/// lines FROM..TO, as this workspace reads SOURCE now.
fn source_line_atoms(root: &Path, workspace: &Value, source: &str, from: usize, to: usize) -> Result<(String, String)> {
    let reference = reference(root, source)?;
    let atoms = line_atoms(&host_document(root, workspace, &reference)?, source, from, to)?;
    match (atoms.first(), atoms.last()) {
        (Some(first), Some(last)) => Ok((first.clone(), last.clone())),
        _ => Err("an empty range".into()),
    }
}

/// `doc-range`: publish lines FROM..TO of NAME as one run (`createRun`), the
/// unit a transclusion's range is cut from. Whoever may write NAME may publish
/// a range of it; a reader transcludes from it under the source's own law.
fn doc_range(root: &Path, workspace: &Value, name: &str, from: usize, to: usize) -> Result<()> {
    let reference = reference(root, name)?;
    let atoms = line_atoms(&host_document(root, workspace, &reference)?, name, from, to)?;
    let run = random_nonce()?;
    eprintln!("workspace range: {run}");
    submit_content(root, workspace, name, vec![json!({"type":"createRun","run":run,"atoms":atoms})], "range")
}

/// `doc-insert`: a new text line, at line AT or (absent) after the last line.
fn doc_insert(root: &Path, workspace: &Value, name: &str, text: &str, at: Option<usize>) -> Result<()> {
    if text.contains('\n') {
        return Err("a line holds no newline".into());
    }
    let atom = random_nonce()?;
    let mut actions = vec![json!({"type":"createAtom","atom":atom,"kind":{"type":"text"},
        "payload":hex(text.as_bytes())})];
    if let Some(at) = at {
        let reference = reference(root, name)?;
        actions.extend(place_new_leaf(&host_document(root, workspace, &reference)?, &atom, at)?);
    }
    eprintln!("workspace line: {atom}");
    submit_content(root, workspace, name, actions, "insert")
}

/// `doc-move`: line FROM moves to stand where line TO stands.
fn doc_move(root: &Path, workspace: &Value, name: &str, from: usize, to: usize) -> Result<()> {
    let reference = reference(root, name)?;
    let actions = move_line(&host_document(root, workspace, &reference)?, from, to)?;
    submit_content(root, workspace, name, actions, "move")
}

/// `doc-remove`: line N leaves the document's order; its atom record stays.
fn doc_remove(root: &Path, workspace: &Value, name: &str, line: usize) -> Result<()> {
    let reference = reference(root, name)?;
    let document = host_document(root, workspace, &reference)?;
    let element = line_element(&document, line)?;
    let (parent, revision, _) = place_of(&document, &element)?;
    submit_content(root, workspace, name,
        vec![edit_element(&parent, &revision, json!({"type":"remove","child":element}))], "remove")
}

/// The mark kind `--kind` names, as the Host's `kind` object.  A link mark
/// carries a fresh link identifier and the document reference NAME (`--to`)
/// names; the kernel writes that link as an ordinary link record.
fn mark_kind(root: &Path, kind: &str, to: Option<&str>) -> Result<(Value, Option<String>)> {
    match kind {
        "bold" | "italic" | "code" | "heading" => {
            if to.is_some() {
                return Err("--to is only for a link mark".into());
            }
            Ok((json!({"type": kind}), None))
        }
        "link" => {
            let to = to.ok_or("a link mark needs --to NAME")?;
            let target = reference(root, to)?;
            let link = random_nonce()?;
            Ok((
                json!({"type":"link","link":link,
                    "target":{"type":"document","id":member(&target, "target")?}}),
                Some(link),
            ))
        }
        other => Err(format!(
            "unknownKind: {other} (expected bold, italic, code, heading or link)"
        )),
    }
}

/// What line N is to a mark: its atom, or (a transclusion) its element, at the
/// revision this view read.  A later edit of the line makes the mark stale.
fn mark_target(document: &Value, line: usize) -> Result<(Value, String)> {
    let lines = live_lines(document)?;
    if line == 0 || line > lines.len() {
        return Err(format!(
            "noSuchTarget: the document has {} lines; there is no line {line}",
            lines.len()
        ));
    }
    let entry = lines[line - 1];
    let target = match entry["kind"].as_str() {
        Some("atom") => json!({"type":"atom","atom":member(entry, "atom")?}),
        _ => json!({"type":"element","element":member(entry, "element")?}),
    };
    Ok((target, member(entry, "revision")?.to_owned()))
}

/// `mark`: lay a KIND mark on line N as this workspace reads the document now.
fn doc_mark(
    root: &Path,
    workspace: &Value,
    name: &str,
    line: usize,
    kind: &str,
    to: Option<&str>,
) -> Result<()> {
    let reference = reference(root, name)?;
    let document = host_document(root, workspace, &reference)?;
    let (target, revision) = mark_target(&document, line)?;
    let (kind, link) = mark_kind(root, kind, to)?;
    let mark = random_nonce()?;
    eprintln!("workspace mark: {mark}");
    if let Some(link) = link {
        eprintln!("workspace mark link: {link}");
    }
    submit_content(
        root,
        workspace,
        name,
        vec![json!({"type":"mark","mark":mark,"target":target,"revision":revision,"kind":kind})],
        "mark",
    )
}

/// `unmark`: retire mark ID, or the one live mark (of KIND) on line N.  The
/// kernel admits it only from the mark's author or the document's owner.
fn doc_unmark(
    root: &Path,
    workspace: &Value,
    name: &str,
    mark: Option<&str>,
    line: Option<usize>,
    kind: Option<&str>,
) -> Result<()> {
    let mark = match (mark, line) {
        (Some(mark), None) if kind.is_none() => {
            decimal(mark, "mark")?;
            mark.to_owned()
        }
        (None, Some(line)) => {
            let reference = reference(root, name)?;
            let document = host_document(root, workspace, &reference)?;
            let lines = live_lines(&document)?;
            if line == 0 || line > lines.len() {
                return Err(format!(
                    "the document has {} lines; there is no line {line}",
                    lines.len()
                ));
            }
            let found: Vec<&Value> = lines[line - 1]["marks"]
                .as_array()
                .map(|marks| {
                    marks
                        .iter()
                        .filter(|mark| kind.is_none_or(|kind| mark["kind"] == kind))
                        .collect()
                })
                .unwrap_or_default();
            match found.as_slice() {
                [one] => member(one, "mark")?.to_owned(),
                [] => {
                    return Err(format!(
                        "markNotFound: no {} mark on line {line}",
                        kind.unwrap_or("live")
                    ))
                }
                many => {
                    let ids: Vec<&str> = many.iter().filter_map(|mark| mark["mark"].as_str()).collect();
                    return Err(format!(
                        "line {line} has {} such marks; name one with --mark ({})",
                        many.len(),
                        ids.join(", ")
                    ));
                }
            }
        }
        _ => return Err("unmark needs --mark ID, or --line N [--kind K]".into()),
    };
    submit_content(root, workspace, name, vec![json!({"type":"unmark","mark":mark})], "unmark")
}

/// This workspace's names for reference targets: what a link mark points at is
/// shown by the name the reader knows it by.  Two names for one target: the
/// first in byte order, so a rendering does not depend on directory order.
fn reference_names(root: &Path) -> std::collections::BTreeMap<String, String> {
    let mut stems: Vec<String> = fs::read_dir(root.join("refs"))
        .into_iter()
        .flatten()
        .flatten()
        .filter_map(|entry| entry.file_name().to_str()?.strip_suffix(".json").map(ref_name_of_file))
        .collect();
    stems.sort();
    let mut names = std::collections::BTreeMap::new();
    for stem in stems {
        if let Ok(value) = reference(root, &stem) {
            if let Some(target) = value["target"].as_str() {
                names.entry(target.to_owned()).or_insert(stem);
            }
        }
    }
    names
}

/// How `doc show` prints: the text notation (default), the document's own
/// atoms byte-exact (`raw`), the `Rendered` struct (`json`), or `html`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ShowFormat {
    Text,
    Raw,
    Json,
    Html,
}

fn show_format(value: Option<OsString>) -> Result<ShowFormat> {
    match value.as_deref().map(OsStr::to_str) {
        None | Some(Some("text")) => Ok(ShowFormat::Text),
        Some(Some("raw")) => Ok(ShowFormat::Raw),
        Some(Some("json")) => Ok(ShowFormat::Json),
        Some(Some("html")) => Ok(ShowFormat::Html),
        _ => Err("--format must be text, raw, json or html".into()),
    }
}

/// The document as this workspace reads it: one `view-document` over this
/// workspace's own reads, rendered by `crate::render`.
pub(crate) fn read_rendered(
    root: &Path,
    workspace: &Value,
    name: &str,
    at: Option<&str>,
) -> Result<(DocumentRead, crate::render::Rendered)> {
    let read = rendered_document(root, workspace, name, None, at)?;
    let names = reference_names(root);
    let rendered = crate::render::render(&crate::render::View {
        document: &read.document,
        entries: &read.entries,
        names: &names,
        sources: &read.sources,
        me: member(workspace, "subject")?,
    })?;
    Ok((read, rendered))
}

/// `doc-show`: the document in the kernel's order (nothing is sorted here).
/// Live lines are numbered, a struck line is `-`, a section `§`; marks render
/// in the notation of `render::text`; annotations sit under their line; a
/// transclusion is rendered over this workspace's own read of its source.
fn doc_show(root: &Path, workspace: &Value, name: &str, at: Option<&str>, format: ShowFormat) -> Result<()> {
    let (read, rendered) = read_rendered(root, workspace, name, at)?;
    if at.is_none() {
        // What `doc edit` and `doc push` name a line against: this read, in the
        // kernel's order.
        let challenge = bounded_json(&read.attempt.join("challenge.json")).unwrap_or(Value::Null);
        retain_seen_value(root, name, &seen_read_value(name, &read, &challenge))?;
    }
    let mut out = std::io::stdout().lock();
    let bytes = match format {
        ShowFormat::Text => rendered.text().into_bytes(),
        ShowFormat::Raw => rendered.raw(),
        ShowFormat::Html => rendered.html(name).into_bytes(),
        ShowFormat::Json => {
            let mut value = rendered.json(&read.host);
            // The page's height (null for the current page) and lifecycle state.
            value["height"] = read.document["height"].clone();
            value["state"] = read.document["state"].clone();
            let mut text = serde_json::to_string_pretty(&value).map_err(|error| error.to_string())?;
            text.push('\n');
            text.into_bytes()
        }
    };
    out.write_all(&bytes).and_then(|()| out.flush()).map_err(|error| error.to_string())
}

/// `doc history` / `doc diff` output: the one renderer's text (default) or
/// HTML, or the Host's JSON.  `raw` names a document's own bytes and has no
/// meaning for a list of changes.
fn print_changes(
    format: ShowFormat,
    value: &Value,
    text: fn(&Value) -> String,
    html: impl Fn(&Value) -> String,
) -> Result<()> {
    match format {
        ShowFormat::Text => {
            print!("{}", text(value));
            Ok(())
        }
        ShowFormat::Html => {
            print!("{}", html(value));
            Ok(())
        }
        ShowFormat::Json => print_json(value),
        ShowFormat::Raw => Err("--format raw shows a document's own bytes; history and diff take text, json or html".into()),
    }
}

/// `doc-outline`: the heading lines (a fresh heading mark), nested by depth.
fn doc_outline(root: &Path, workspace: &Value, name: &str, json_out: bool) -> Result<()> {
    let (_, rendered) = read_rendered(root, workspace, name, None)?;
    if json_out {
        println!(
            "{}",
            serde_json::to_string_pretty(&rendered.json("")["outline"]).map_err(|error| error.to_string())?
        );
    } else {
        print!("{}", crate::render::text::outline(&rendered));
    }
    Ok(())
}

fn view_hex(attempt: &Path) -> Result<String> {
    let path = attempt.join("view.bin");
    fs::read(&path)
        .map(|bytes| hex(&bytes))
        .map_err(|error| format!("cannot read {}: {error}", path.display()))
}

/// Render `input` with the Host's `kind` inspection, retained beside `attempt`.
fn doc_render(workspace: &Value, attempt: &Path, kind: &str, input: &Value) -> Result<Value> {
    let input_path = attempt.join(format!("{kind}-input.json"));
    private_file(
        &input_path,
        &serde_json::to_vec(input).map_err(|error| error.to_string())?,
    )?;
    let rendered = inspect(
        &workspace_host(workspace)?,
        &member_path(workspace, "config")?,
        kind,
        &input_path,
        &attempt.join(format!("{kind}.json")),
    )?;
    Ok(rendered)
}

/// Whether the `at` read that just failed was refused `no-grant`: the grant did
/// not stand over the cell at that height (`NativeObservationController.atCovered`).
/// Read from the Host's own decoding of its refusal frame (`HostDecision`),
/// never from text. Every other failure (a height above the head, a malformed
/// read, a transport error) stays an error, not a placeholder.
fn history_refused() -> bool {
    match crate::take_host_decision() {
        Some(crate::HostDecision::RefusedFrame { decoded: Some(outcome), .. })
        | Some(crate::HostDecision::Outcome(outcome)) => reason_is_no_grant(&outcome),
        _ => false,
    }
}

fn reason_is_no_grant(outcome: &Value) -> bool {
    outcome.get("type").and_then(Value::as_str) == Some("refused")
        && outcome.get("reason").and_then(Value::as_str) == Some("no-grant")
}

/// The heights whose `at` reads render a document's history: for each `since`
/// entry that wrote `target`, its height and the height below it, ascending.
fn history_heights(since: &Value, target: &str) -> Result<Vec<u64>> {
    let entries = since
        .get("entries")
        .and_then(Value::as_array)
        .ok_or_else(|| "since view lacks entries".to_owned())?;
    let mut heights = Vec::new();
    for entry in entries {
        let wrote = entry
            .get("cells")
            .and_then(Value::as_array)
            .is_some_and(|cells| cells.iter().any(|cell| cell.as_str() == Some(target)));
        if !wrote {
            continue;
        }
        let height: u64 = member(entry, "height")?
            .parse()
            .map_err(|_| "since entry height is not a decimal".to_owned())?;
        if height > 0 {
            heights.push(height - 1);
        }
        heights.push(height);
    }
    heights.sort_unstable();
    heights.dedup();
    Ok(heights)
}

/// `doc history NAME`: `since 0` cut to the document, and the `at` reads at
/// each row's height and the one below it; a height the grant did not cover
/// contributes no read. The Host renders the rows and their atom changes.
pub(crate) fn doc_history(root: &Path, workspace: &Value, name: &str) -> Result<Value> {
    let reference = reference(root, name)?;
    let target = member(&reference, "target")?;
    let (since, attempt) = doc_query(
        root,
        workspace,
        &reference,
        "since",
        Some("0"),
        "view-since",
    )?;
    let mut reads = Vec::new();
    for height in history_heights(&since, target)? {
        match doc_query(
            root,
            workspace,
            &reference,
            "at",
            Some(&height.to_string()),
            "view-at",
        ) {
            Ok((_, read)) => reads.push(view_hex(&read)?),
            Err(error) if history_refused() => {
                eprintln!("doc history: no read at height {height}: {error}");
            }
            Err(error) => return Err(error),
        }
    }
    let input = json!({"target": target, "since": view_hex(&attempt)?, "at": reads});
    doc_render(workspace, &attempt, "view-history", &input)
}

/// `doc diff NAME H1 H2`: the atom changes between the two `at` reads.
pub(crate) fn doc_diff(root: &Path, workspace: &Value, name: &str, from: &str, to: &str) -> Result<Value> {
    let reference = reference(root, name)?;
    let (_, left) = doc_query(root, workspace, &reference, "at", Some(from), "view-at")?;
    let (_, right) = doc_query(root, workspace, &reference, "at", Some(to), "view-at")?;
    let input = json!({"left": view_hex(&left)?, "right": view_hex(&right)?});
    doc_render(workspace, &right, "view-diff", &input)
}

/// Historical signed view used by room lineage resolution, sharing the document
/// query path and its authenticated retained request/response contract.
pub(crate) fn signed_view_at(root: &Path, workspace: &Value, reference: &Value, height: &str) -> Result<Value> {
    doc_query(root, workspace, reference, "at", Some(height), "view-at").map(|(view, _)| view)
}

fn signed_authority_root(challenge: &Value) -> Result<&str> {
    let root = challenge
        .get("authorityRoot")
        .and_then(Value::as_str)
        .ok_or("signed query challenge lacks authority root")?;
    field_decimal(root, "signed authority root")?;
    Ok(root)
}

/// One K-FIELDS field name: a decimal slot, `balance:N`, `code`, `body` or
/// `annotations` (the Host's `cellFieldOfName`).
fn delegation_field(value: &Value) -> Result<Value> {
    let name = value.as_str().ok_or("delegation field must be a string")?;
    let ok = matches!(name, "code" | "body" | "annotations")
        || name
            .strip_prefix("balance:")
            .map_or_else(|| decimal(name, "field").is_ok(), |n| decimal(n, "field").is_ok());
    if !ok {
        return Err(format!("unknown delegation field {name}").into());
    }
    Ok(json!(name))
}

fn delegation_fields(fields: &Value) -> Result<Value> {
    let fields = fields
        .as_array()
        .ok_or("delegation fields must be an array")?;
    if fields.is_empty() || fields.len() > 64 {
        return Err("delegation names 1..64 fields".into());
    }
    Ok(Value::Array(
        fields.iter().map(delegation_field).collect::<Result<Vec<_>>>()?,
    ))
}

fn delegation_bounds(bounds: &Value) -> Result<Value> {
    let bounds = bounds
        .as_array()
        .ok_or("delegation maxDelta must be an array")?;
    if bounds.is_empty() || bounds.len() > 64 {
        return Err("delegation sets 1..64 maxDelta bounds".into());
    }
    let mut out = Vec::new();
    for bound in bounds {
        let obj = bound
            .as_object()
            .ok_or("maxDelta bound must be an object")?;
        if obj.len() != 2 {
            return Err("maxDelta bound has exactly field and max".into());
        }
        let field = delegation_field(bound.get("field").ok_or("maxDelta bound lacks field")?)?;
        let max = member(bound, "max")?;
        decimal(max, "maxDelta max")?;
        out.push(json!({"field": field, "max": max}));
    }
    Ok(Value::Array(out))
}

fn scalar_actions(actions: &Value, target: &str) -> Result<Value> {
    let actions = actions
        .as_array()
        .ok_or("scalar actions must be an array")?;
    if actions.is_empty() || actions.len() > 64 {
        return Err("scalar proposal requires 1..64 actions".into());
    }
    let mut lowered = Vec::new();
    for action in actions {
        let obj = action
            .as_object()
            .ok_or("scalar action must be an object")?;
        let tag = member(action, "type")?;
        if !matches!(tag, "create" | "write") || obj.len() != if tag == "create" { 3 } else { 4 } {
            return Err("workspace scalar proposal supports create/write only".into());
        }
        let key = action
            .get("key")
            .and_then(Value::as_object)
            .ok_or("scalar action needs a local key")?;
        if key.len() != 2 || key.get("type").and_then(Value::as_str) != Some("object") {
            return Err("scalar key must contain only type=object and field".into());
        }
        let field = key
            .get("field")
            .and_then(Value::as_str)
            .ok_or("scalar key lacks field")?;
        decimal(field, "scalar field")?;
        let value = member(action, "value")?;
        signed_decimal(value, "scalar value")?;
        let mut lowered_action = json!({"type":tag,
            "key":{"type":"object","resource":target,"field":field},"value":value});
        if tag == "write" {
            let expected = action
                .get("expected")
                .ok_or("write action lacks expected")?;
            if !expected.is_null() {
                signed_decimal(
                    expected.as_str().ok_or("write expected must be null or a string")?,
                    "write expected",
                )?;
            }
            lowered_action["expected"] = expected.clone();
        }
        lowered.push(lowered_action);
    }
    Ok(json!({"type":"scalar","actions":lowered}))
}

/// Check content actions against the Host's content grammar. Every action the
/// grammar has may be proposed directly (the Host checks an edit's `before` and
/// an annotation's `revision` against the stored atom). A payload `sealed`
/// under `--private` passes one strict action classifier before payload sealing.
/// Structural edits carry no body bytes; edits retain ciphertext stale guards.
fn content_actions(actions: &Value, sealed: bool) -> Result<Value> {
    crate::workspace::content_privacy::actions(actions, sealed)
}

fn legacy_private_content(lowered: Value, room: &str, target: &str, key: &private::RoomKey) -> Result<Value> {
    protected_document::reject_fresh_legacy(&lowered["actions"])?;
    private::seal_content(lowered, room, target, key)
}

fn unhex(text: &str) -> Result<Vec<u8>> {
    crate::decode_hex(text)
}

fn to_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

/// One stream append: `{"type":"append","topic":TEXT,"text":TEXT[,"to":SUBJECT][,"ref":{cell,sequence}]}`.
/// Raw bytes ride as `"topicHex"` / `"payloadHex"` in place of `"topic"` / `"text"` (a channel epoch
/// record, CH-EPOCH, is binary). The Host derives the sequence position and the payload digest; the
/// bytes ride in the signed command.
fn stream_append(payload: &Value) -> Result<Value> {
    let obj = payload
        .as_object()
        .ok_or("append payload must be an object")?;
    let has = |key: &str| obj.contains_key(key);
    if obj.keys().any(|key| {
        !matches!(
            key.as_str(),
            "type" | "topic" | "topicHex" | "text" | "payloadHex" | "to" | "ref"
        )
    }) || has("topic") == has("topicHex")
        || has("text") == has("payloadHex")
    {
        return Err(
            "append payload has type, one of topic/topicHex, one of text/payloadHex, and optional to, ref"
                .into(),
        );
    }
    let topic = if has("topic") {
        member(payload, "topic")?.as_bytes().to_vec()
    } else {
        unhex(member(payload, "topicHex")?)?
    };
    let text = if has("text") {
        member(payload, "text")?.as_bytes().to_vec()
    } else {
        unhex(member(payload, "payloadHex")?)?
    };
    if topic.len() > 64 {
        return Err("append topic exceeds 64 bytes".into());
    }
    if text.len() > 4096 {
        return Err("append text exceeds 4096 bytes".into());
    }
    let to = match obj.get("to") {
        None | Some(Value::Null) => Value::Null,
        Some(value) => {
            let subject = value.as_str().ok_or("append to must be a decimal string")?;
            field_decimal(subject, "append to")?;
            json!(subject)
        }
    };
    let reference = match obj.get("ref") {
        None | Some(Value::Null) => Value::Null,
        Some(value) => json!({"cell":member(value,"cell")?,"sequence":member(value,"sequence")?}),
    };
    Ok(json!({"type":"append","topic":to_hex(&topic),
        "payload":to_hex(&text),"to":to,"ref":reference}))
}

/// Private intent follows the document reference. Browser and shell writers
/// cannot silently drop sealing by omitting an optional command-line flag.
fn sealing_room(explicit: Option<&str>, root: &Path, reference: &Value) -> Result<Option<String>> {
    let mut rooms = std::collections::BTreeSet::new();
    if let Some(room) = reference.get("sealedIn").and_then(Value::as_str) { rooms.insert(room.to_owned()); }
    // Sealing follows the cell, not one petname. Importing a second reference
    // cannot make the same sealed content become a public mutation target.
    if let Ok(refs) = fs::read_dir(root.join("refs")) {
        for file in refs.flatten() {
            if file.path().extension().is_none_or(|ext| ext != "json") { continue; }
            if let Ok(other) = bounded_json(&file.path()) {
                if other.get("target") == reference.get("target") && other.get("kind") == reference.get("kind") {
                    if let Some(room) = other.get("sealedIn").and_then(Value::as_str) { rooms.insert(room.to_owned()); }
                }
            }
        }
    }
    if let Some(id) = reference.get("sealedRoom") {
        rooms.insert(private_room_name(root, id.as_str().ok_or("sealedRoom must be a decimal string")?)?);
    }
    if let Some(room) = explicit { rooms.insert(room.to_owned()); }
    // Room aliases are equivalent only when they resolve to the same cell.
    let mut identity = None;
    for room in &rooms {
        let id = member(&self::reference(root, room)?, "target")?.to_owned();
        if identity.as_ref().is_some_and(|other| other != &id) {
            return Err("conflicting private rooms for the same document reference".into());
        }
        identity = Some(id);
    }
    Ok(rooms.into_iter().next())
}

fn read_private(root: &Path, workspace: &Value, resource_name: &str, room: &str) -> Result<()> {
    let (room_id, keys) = roomkey::reader_keys(root, workspace, room)?;
    let reference = reference(root, resource_name)?;
    let (mut view, _, _) = signed_view(root, workspace, &reference, "resource")?;
    let count = private::open_view(
        &mut view,
        &room_id,
        member(&reference, "target")?,
        keys.as_ref(),
    );
    eprintln!("workspace read: {count} private atom(s) under room {room}");
    println!(
        "{}",
        serde_json::to_string_pretty(&view).map_err(|error| error.to_string())?
    );
    Ok(())
}

/// The private room a CELL is sealed under, as this workspace knows it: the
/// `sealedIn` mark of this reference, or of any other reference to the same
/// cell (AUDIT-ROOMS, client defect 3: the mark was per reference name, so a
/// second import of a sealed doc wrote plaintext into the private room).
pub(crate) fn sealed_room(root: &Path, reference: &Value) -> Option<String> {
    if let Some(room) = reference.get("sealedIn").and_then(Value::as_str) {
        return Some(room.to_owned());
    }
    let target = reference.get("target").and_then(Value::as_str)?;
    let kind = reference.get("kind").and_then(Value::as_str);
    let mut names: Vec<String> = fs::read_dir(root.join("refs"))
        .ok()?
        .flatten()
        .filter_map(|entry| entry.file_name().to_str()?.strip_suffix(".json").map(ref_name_of_file))
        .collect();
    names.sort();
    names.into_iter().find_map(|name| {
        let other = crate::workspace::reference(root, &name).ok()?;
        (other.get("target").and_then(Value::as_str) == Some(target)
            && other.get("kind").and_then(Value::as_str) == kind)
            .then(|| other.get("sealedIn").and_then(Value::as_str).map(str::to_owned))
            .flatten()
    })
}

/// Whether a signed view holds a private-cell envelope (`DREGG/PRIVATE-CELL`
/// atoms of the private schema).
fn holds_sealed(view: &Value, target: &str) -> bool {
    private::open_view(&mut view.clone(), "", target, None) > 0
        || view["cell"]["entries"].as_array().is_some_and(|rows| rows.iter().any(|row| protected_document::is_kind(&row["kind"])))
}

/// The client's own observations of one plan named different world or
/// authority roots: another admission landed between them. Nothing was
/// authored or sent; the plan is made again from fresh reads (`replan`).
const OBSERVATIONS_MOVED: &str =
    "the plan's signed reads saw the Host state move between them (another admission landed)";

/// Author a proposal from fresh signed reads. A Host `stale-root` on one read
/// is re-observed inside that read; reads that disagree with each other are
/// re-planned here, all of them, under the same `--replan-max` bound.
pub(crate) fn propose(
    root: &Path,
    workspace: &Value,
    request_path: &Path,
    proposal_id: &str,
    private_room_name: Option<&str>,
) -> Result<()> {
    let summary = propose_summary(root, workspace, request_path, proposal_id, private_room_name, false)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&summary).map_err(|error| error.to_string())?
    );
    Ok(())
}

/// Author and retain one proposal (`proposals/ID/`) from a request value; the
/// summary is what `propose` prints.
/// Author and retain one proposal from a request value. `fresh` makes a
/// document action name its line from this proposal's own signed read instead
/// of the last `doc show` / `doc pull` (`can`'s probes; `doc edit` keeps the
/// read the friend saw).
fn propose_summary(root: &Path, workspace: &Value, request_path: &Path,
    proposal_id: &str, private_room_name: Option<&str>, fresh: bool) -> Result<Value> {
    let request = bounded_json(request_path)?;
    propose_request(root, workspace, &request, proposal_id, private_room_name, fresh)
}

fn propose_request(
    root: &Path,
    workspace: &Value,
    request: &Value,
    proposal_id: &str,
    private_room_name: Option<&str>,
    fresh: bool,
) -> Result<Value> {
    crate::replan::replan(
        "propose",
        || propose_summary_once(root, workspace, request, proposal_id, private_room_name, fresh),
        |error, _| error == OBSERVATIONS_MOVED,
        |_| Ok(()),
    )
}

fn propose_summary_once(
    root: &Path,
    workspace: &Value,
    request: &Value,
    proposal_id: &str,
    private_room_name: Option<&str>,
    fresh: bool,
) -> Result<Value> {
    validate_name(proposal_id)?;
    let request = request.clone();
    if member(&request, "type")? != "minidregg-workspace-proposal-v1" {
        return Err("unknown workspace proposal version".into());
    }
    if member(&request, "action")? == "install-export" {
        if let Some(summary) = law_export::retained(root, proposal_id, &request)? { return Ok(summary); }
    }
    if private_room_name.is_some() && member(&request, "action")? != "invoke" {
        return Err("--private applies to invoke proposals only".into());
    }
    // One sync per private room this proposal seals under.
    let mut room_keys: std::collections::BTreeMap<String, (String, private::RoomKey)> =
        std::collections::BTreeMap::new();
    let nonce = random_nonce()?;
    let mut delegation = None::<Value>;
    let mut renounce = None::<Value>;
    let intent = match member(&request, "action")? {
        "invoke" => {
            let obj = request.as_object().ok_or("proposal must be an object")?;
            let claimed = obj.contains_key("run");
            if obj.len() != 3 + usize::from(claimed) || !obj.contains_key("targets") {
                return Err("invoke proposal may contain only type, action, targets, run".into());
            }
            // K-RAN: a Nock run claim rides inside the signed command; the Host
            // parses it exactly (programId, sample, output, steps) and re-executes.
            let run = match request.get("run") {
                None => None,
                Some(claim) => {
                    let fields = claim.as_object().ok_or("run claim must be an object")?;
                    if fields.len() != 4 {
                        return Err("run claim may contain only programId, sample, output, steps".into());
                    }
                    field_decimal(member(claim, "programId")?, "run programId")?;
                    field_decimal(member(claim, "steps")?, "run steps")?;
                    for key in ["sample", "output"] {
                        let hex = member(claim, key)?;
                        if hex.len() % 2 != 0 || !hex.bytes().all(|b| b.is_ascii_hexdigit()) {
                            return Err("run claim jams must be hex".into());
                        }
                    }
                    Some(claim.clone())
                }
            };
            let selected = request
                .get("targets")
                .and_then(Value::as_array)
                .ok_or("invoke targets must be an array")?;
            if selected.is_empty() || selected.len() > 16 {
                return Err("invoke proposal needs 1..16 targets".into());
            }
            let mut target_rows = Vec::new();
            let mut grants = Vec::new();
            let command_nonce = random_nonce()?;
            let mut image = None::<String>;
            let mut seen = std::collections::BTreeSet::new();
            for entry in selected {
                let obj = entry
                    .as_object()
                    .ok_or("proposal target must be an object")?;
                if obj.len() != 2 || !obj.contains_key("name") || !obj.contains_key("payload") {
                    return Err("proposal target may contain only name and payload".into());
                }
                let local_name = member(entry, "name")?;
                if !seen.insert(local_name.to_owned()) {
                    return Err("duplicate named target".into());
                }
                let reference = reference(root, local_name)?;
                let protected = reference.get("protectedDocument").is_some();
                let (view, challenge, signed) = signed_view(root, workspace, &reference, "resource")?;
                let audience = if protected { Some(protected_document::observe(root,workspace,&reference,&signed)?) } else { None };
                let current_image = member(&challenge, "worldRoot")?.to_owned();
                if let Some(previous) = &image {
                    if previous != &current_image {
                        return Err(OBSERVATIONS_MOVED.into());
                    }
                }
                image = Some(current_image.clone());
                let target = member(&reference, "target")?;
                let kind = member(&reference, "kind")?;
                let root_value = view
                    .get("cell")
                    .and_then(|page| page.get("root"))
                    .and_then(Value::as_str)
                    .ok_or("signed resource view lacks page root")?;
                field_decimal(root_value, "signed resource root")?;
                let payload = entry.get("payload").ok_or("target payload absent")?;
                let payload_obj = payload
                    .as_object()
                    .ok_or("target payload must be an object")?;
                let read_only = payload.get("type").and_then(Value::as_str) == Some("read");
                let sealing = match if protected || read_only { None } else { sealing_room(private_room_name, root, &reference)? } {
                    // A cell that already holds sealed lines is a private room's,
                    // whatever this reference is called: refuse to write plaintext
                    // into it when the room is not known here.
                    None if !protected && !read_only && holds_sealed(&view, target) => {
                        return Err(format!(
                            "{local_name} holds sealed lines (a private room's cell) and this workspace does not know \
                             its room: name it with --private ROOM, or read and write it through the reference it was born under"
                        ))
                    }
                    None => None,
                    Some(room) => {
                        if !room_keys.contains_key(&room) {
                            let key = roomkey::current_key(root, workspace, &room)?;
                            room_keys.insert(room.clone(), key);
                        }
                        let (room_id, key) = room_keys.get(&room).expect("inserted");
                        Some((room_id.as_str(), key))
                    }
                };
                let lowered = if member(payload, "type")? == "append" {
                    let mut lowered = stream_append(payload)?;
                    if let Some((room, key)) = &sealing {
                        // The topic is a kernel field the operator reads: a sealed
                        // entry carries none (put it inside the sealed text).
                        if !member(&lowered, "topic")?.is_empty() {
                            return Err("a topic is plaintext the operator reads: a sealed append has an empty topic".into());
                        }
                        let sequence = view
                            .get("cell")
                            .and_then(|page| page.get("nextSeq"))
                            .and_then(Value::as_str)
                            .ok_or("signed stream view lacks nextSeq")?;
                        field_decimal(sequence, "stream nextSeq")?;
                        // Seal the normalized bytes so binary append proposals retain
                        // the same room privacy as text proposals.
                        let plain = zeroize::Zeroizing::new(unhex(member(&lowered, "payload")?)?);
                        lowered["payload"] = json!(hex(&roomkey::seal_for_room(
                            key, room, target, sequence, &plain
                        )?));
                    }
                    lowered
                } else if member(payload, "type")? == "computeFunding" && sealing.is_none() {
                    if kind != "account" || protected {return Err("compute funding requires an ordinary account".into());}
                    world_kind::validate_funding_payload(payload)?;
                    payload.clone()
                } else if member(payload, "type")? == "kindDefinition" && sealing.is_none() {
                    world_kind::revise(payload, &view, target)?
                } else if read_only {
                    // An observe-only read of a content cell (K-TRANSCLUDE): the
                    // source a `transclude` of another target names.
                    if payload_obj.len() != 1 {
                        return Err("a read payload may contain only type".into());
                    }
                    if sealing.is_some() {
                        return Err("--private seals content payloads only".into());
                    }
                    json!({"type":"read"})
                } else {
                    if payload_obj.len() != 2
                        || !payload_obj.contains_key("type")
                        || !payload_obj.contains_key("actions")
                    {
                        return Err("payload may contain only type and actions".into());
                    }
                    match (member(payload, "type")?, &sealing) {
                        ("worldNamed", None) => world_kind::named_actions(root, local_name, &view, &payload["actions"], fresh)?,
                        ("scalar", None) => scalar_actions(&payload["actions"], target)?,
                        ("content", None) => content_actions(&payload["actions"], false)?,
                        ("content", Some((room, key))) => legacy_private_content(
                            content_actions(&payload["actions"], true)?,
                            room,
                            target,
                            key,
                        )?,
                        ("document", None) => content_actions(
                            &document_actions(root, workspace, local_name, &view, fresh,
                                &payload["actions"])?,
                            false,
                        )?,
                        ("document", Some((room, key))) => legacy_private_content(
                            content_actions(&document_actions(root, workspace, local_name, &view,
                                fresh, &payload["actions"])?, true)?, room, target, key)?,
                        ("scalar", Some(_)) => {
                            return Err("--private seals content and stream payloads only".into())
                        }
                        _ => return Err("unsupported workspace payload type".into()),
                    }
                };
                let lowered = if let Some(audience) = &audience {
                    if lowered["type"] != "content" { return Err("protected document accepts content actions only".into()); }
                    protected_document::seal(root,workspace,audience,lowered,&command_nonce)?
                } else { lowered };
                // A read target's authorization leg is checked under the observe
                // verb, so it carries the observe capability.
                let capability = if read_only {
                    member(&reference, "observeCapability")?
                } else {
                    member(&reference, "operationCapability")?
                };
                let observe = member(&reference, "observeCapability")?;
                // The command version the Host checks per payload: a content
                // command and an observe-only read are `ContentResource.commandVersion`
                // (7); a scalar command is 1.
                let schema_version = match lowered.get("type").and_then(Value::as_str) {
                    Some("content") | Some("read") => CONTENT_COMMAND_VERSION,
                    _ => SCALAR_COMMAND_VERSION,
                };
                let mut target_row = json!({"kind":kind,"target":target,"capability":capability,
                    "observeCapability":observe,"schemaVersion":schema_version,
                    "expectedTargetRoot":root_value,"payload":lowered});
                if let Some(audience) = &audience { audience.bind_target(&mut target_row,&current_image)?; }
                target_rows.push(target_row);
                grants.push(json!({"kind":kind,"target":target,"capability":observe}));
            }
            let mut command = json!({"subject":member(workspace,"subject")?,
                "nonce":command_nonce,"targets":target_rows});
            if let Some(claim) = run {
                command["run"] = claim;
            }
            json!({"subject":member(workspace,"subject")?,"nonce":nonce,
                "purpose":{"type":"prepare","draft":{"type":"invoke","command":command}},
                "grants":grants})
        }
        "install-policy" | "install-export" => {
            let exporting = member(&request, "action")? == "install-export";
            let body = if exporting { "component" } else { "predicate" };
            let obj = request.as_object().ok_or("proposal must be an object")?;
            if obj.len() != 4 || !obj.contains_key("name") || !obj.contains_key(body) {
                return Err(format!("law proposal may contain only type, action, name, {body}"));
            }
            let reference = reference(root, member(&request, "name")?)?;
            let control = member(&reference, "controlCapability")?;
            let (policy, challenge, _) = signed_view(root, workspace, &reference, "policy")?;
            let target = member(&reference, "target")?;
            let source = law_export::source(&policy, &request)?;
            json!({"subject":member(workspace,"subject")?,"nonce":nonce,
                "purpose":{"type":"prepare","draft":{"type":"install-source",
                    "subject":member(workspace,"subject")?,"control":control,
                    "declaration":{"expectedPreRoot":signed_authority_root(&challenge)?,
                        "expected":{"version":member(&policy,"version")?,"address":member(&policy,"address")?},
                        "nonce":random_nonce()?,"source":source}}},
                "grants":[{"kind":member(&reference,"kind")?,"target":target,
                    "capability":member(&reference,"observeCapability")?}]})
        }
        "delegate" => {
            let obj = request.as_object().ok_or("proposal must be an object")?;
            // Optional `"room": true`: a room invite, whose child is `under` the
            // named resource instead of the resource alone.
            let room_invite = match obj.get("room") {
                None => false,
                Some(Value::Bool(value)) => *value,
                Some(_) => return Err("delegate proposal room must be a boolean".into()),
            };
            // Optional K-FIELDS narrowing: `"fields": ["1","annotations",...]`
            // (absent = the parent's fields) and `"maxDelta": [{"field":"7","max":"50"}]`
            // (absent = the parent's bounds). The Host decides narrowing.
            // Optional `"notAfter": H`: the child's window ends at height H
            // (absent = the parent's end); a concierge issues a member's week
            // this way, and the Host's `Admissible.validUntil` enforces it.
            let optional_keys = ["room", "fields", "maxDelta", "notAfter"]
                .iter()
                .filter(|key| obj.contains_key(**key))
                .count();
            if obj.len() != 6 + optional_keys
                || ["name", "recipient", "verbs", "maxCost"]
                    .iter()
                    .any(|field| !obj.contains_key(*field))
            {
                return Err(
                    "delegate proposal requires type, action, name, recipient, verbs, maxCost"
                        .into(),
                );
            }
            let reference = reference(root, member(&request, "name")?)?;
            let target = member(&reference, "target")?;
            let kind = member(&reference, "kind")?;
            let parent_id = member(&reference, "operationCapability")?;
            let recipient = member(&request, "recipient")?;
            decimal(recipient, "delegate recipient")?;
            let maximum = member(&request, "maxCost")?;
            field_decimal(maximum, "delegation maxCost")?;
            let selected_verbs = request
                .get("verbs")
                .and_then(Value::as_array)
                .ok_or("delegation verbs must be an array")?;
            if selected_verbs.is_empty() || selected_verbs.len() > 8 {
                return Err("delegation needs 1..8 narrowed verbs".into());
            }
            let (resource, resource_challenge, _) =
                signed_view(root, workspace, &reference, "resource")?;
            let (policy, policy_challenge, _) = signed_view(root, workspace, &reference, "policy")?;
            let mut parent_ref = reference.clone();
            parent_ref["observeCapability"] = json!(parent_id);
            let (capability, cap_challenge, _) =
                signed_view(root, workspace, &parent_ref, "capability")?;
            let image = member(&resource_challenge, "worldRoot")?;
            let authority = signed_authority_root(&resource_challenge)?;
            for challenge in [&policy_challenge, &cap_challenge] {
                if member(challenge, "worldRoot")? != image
                    || signed_authority_root(challenge)? != authority
                {
                    return Err(OBSERVATIONS_MOVED.into());
                }
            }
            let head = capability
                .get("head")
                .ok_or("typed capability view lacks head")?;
            if member(&capability, "kind")? != kind || member(head, "id")? != parent_id {
                return Err("signed capability head differs from selected parent reference".into());
            }
            // A scope is exactly one of `targets` (explicit) or `room` (`under R`).
            // Whether a room scope covers the target depends on the parent chain
            // in the authority cell; the Host decides that at submission.
            match (head.get("targets"), head.get("room")) {
                (Some(targets), None) => {
                    let targets = targets
                        .as_array()
                        .ok_or("parent capability targets are not a list")?;
                    if !targets.iter().any(|value| value.as_str() == Some(target)) {
                        return Err("parent capability does not cover named target".into());
                    }
                }
                (None, Some(room)) => {
                    decimal(
                        room.as_str().ok_or("parent capability room is not decimal")?,
                        "parent capability room",
                    )?;
                }
                _ => return Err("parent capability scope must be exactly one of targets or room".into()),
            }
            let parent_verbs = head
                .get("verbs")
                .and_then(Value::as_array)
                .ok_or("parent capability lacks verbs")?;
            if !parent_verbs
                .iter()
                .any(|value| value.as_str() == Some("delegate"))
            {
                return Err("parent capability lacks delegation verb".into());
            }
            readable_delegation_verbs(selected_verbs, parent_verbs)?;
            let parent_max = member(head, "maxCost")?;
            field_decimal(parent_max, "parent maxCost")?;
            if !decimal_leq(maximum, parent_max) {
                return Err("delegation maxCost exceeds parent".into());
            }
            let parent_before = member(head, "notBefore")?;
            let parent_after = member(head, "notAfter")?;
            let height = member(&resource_challenge, "height")?;
            for (value, label) in [
                (parent_before, "parent notBefore"),
                (parent_after, "parent notAfter"),
                (height, "current height"),
            ] {
                field_decimal(value, label)?;
            }
            let child_before = decimal_max(parent_before, height);
            if !decimal_leq(child_before, parent_after) {
                return Err("parent capability is outside its effective lifetime".into());
            }
            let child_after = match obj.get("notAfter") {
                None => parent_after,
                Some(Value::String(requested)) => {
                    field_decimal(requested, "delegation notAfter")?;
                    if !decimal_leq(requested, parent_after) {
                        return Err("delegation notAfter exceeds the parent's window".into());
                    }
                    if !decimal_leq(child_before, requested) {
                        return Err("delegation notAfter is already past (below the current height)".into());
                    }
                    requested.as_str()
                }
                Some(_) => return Err("delegation notAfter must be a decimal string".into()),
            };
            let mut ancestors = head
                .get("ancestors")
                .and_then(Value::as_array)
                .ok_or("parent capability lacks ancestors")?
                .clone();
            if !ancestors
                .iter()
                .any(|value| value.as_str() == Some(parent_id))
            {
                ancestors.push(json!(parent_id));
            }
            let namespace = namespace_root(root, workspace)?;
            let fingerprint = serde_json::to_vec(&json!({"request":request,"reference":reference,
                "subject":member(workspace,"subject")?}))
            .map_err(|error| error.to_string())?;
            let reservation = participant_namespace::reserve(
                &namespace,
                member(&policy, "domain")?,
                member(workspace, "subject")?,
                &format!("delegate-{proposal_id}"),
                &fingerprint,
                &[Role {
                    label: "childCapability".into(),
                    kind: IdKind::Capability,
                }],
            )?;
            let child_id = reservation
                .ids
                .get("childCapability")
                .ok_or("namespace omitted delegated capability")?;
            let target_root = resource
                .get("cell")
                .and_then(|page| page.get("root"))
                .and_then(Value::as_str)
                .ok_or("signed resource view lacks page root")?;
            field_decimal(target_root, "delegation target root")?;
            let mut child = json!({"id":child_id,"root":member(head,"root")?,"parent":parent_id,
                "issuer":member(head,"issuer")?,"holder":{"type":"subject","subject":recipient},
                "targets":[target],"verbs":selected_verbs,"maxCost":maximum,
                "notBefore":child_before,"notAfter":child_after,
                "issuerEpoch":member(head,"issuerEpoch")?,"policyId":member(head,"policyId")?,
                "policyEpoch":member(head,"policyEpoch")?,"ancestors":ancestors,
                "channels":head.get("channels").ok_or("parent capability lacks channels")?});
            if room_invite {
                let scope = child.as_object_mut().ok_or("child capability is not an object")?;
                scope.remove("targets");
                scope.insert("room".into(), json!(target));
            }
            let child_fields = match obj.get("fields") {
                Some(fields) => Some(delegation_fields(fields)?),
                None => head.get("fields").cloned(),
            };
            let child_bounds = match obj.get("maxDelta") {
                Some(bounds) => Some(delegation_bounds(bounds)?),
                None => head.get("maxDelta").cloned(),
            };
            {
                let scope = child.as_object_mut().ok_or("child capability is not an object")?;
                if let Some(fields) = child_fields {
                    scope.insert("fields".into(), fields);
                }
                if let Some(bounds) = child_bounds {
                    scope.insert("maxDelta".into(), bounds);
                }
            }
            delegation = Some(json!({"recipient":recipient,"kind":kind,"target":target,
                "childCapability":child_id,"reservation":reservation.request_digest,
                "domain":member(&policy,"domain")?,"name":member(&request,"name")?}));
            if let Some(room) = sealing_room(None, root, &reference)? {
                let id = member(&self::reference(root, &room)?, "target")?.to_owned();
                delegation.as_mut().unwrap()["sealedRoom"] = json!(id);
            }
            json!({"subject":member(workspace,"subject")?,"nonce":nonce,
                "purpose":{"type":"prepare","draft":{"type":"delegate-source",
                    "command":{"kind":kind,"domain":member(&policy,"domain")?,
                    "semantics":member(&policy,"semantics")?,"subject":member(workspace,"subject")?,
                    "nonce":random_nonce()?,"expectedTargetRoot":target_root,
                    "parentId":parent_id,"target":target,"expectedPreRoot":authority,
                    "child":child}}},
                "grants":[{"kind":kind,"target":target,"capability":parent_id}]})
        }
        "revoke" => {
            // `capability` (optional): the grant to revoke, by number (`room
            // kick` names each standing grant the recipient holds under the
            // room); absent, the one this workspace delegated to the recipient.
            let obj = request.as_object().ok_or("proposal must be an object")?;
            let explicit = obj.contains_key("capability");
            if obj.len() != 4 + usize::from(explicit) || !obj.contains_key("name") || !obj.contains_key("recipient") {
                return Err("revoke proposal may contain only type, action, name, recipient [capability]".into());
            }
            let reference = reference(root, member(&request, "name")?)?;
            let recipient = member(&request, "recipient")?;
            decimal(recipient, "revoke recipient")?;
            let kind = member(&reference, "kind")?;
            let target = member(&reference, "target")?;
            let control = member(&reference, "controlCapability")?;
            let victim = if explicit {
                let named = member(&request, "capability")?;
                decimal(named, "revoked capability")?;
                named.to_owned()
            } else {
                delegated_capability(root, member(&request, "name")?, target, recipient)?
            };
            let (resource, challenge, _) = signed_view(root, workspace, &reference, "resource")?;
            let target_root = resource
                .get("cell")
                .and_then(|cell| cell.get("root"))
                .and_then(Value::as_str)
                .ok_or("signed resource view lacks cell root")?;
            field_decimal(target_root, "revocation target root")?;
            json!({"subject":member(workspace,"subject")?,"nonce":nonce,
                "purpose":{"type":"prepare","draft":{"type":"revoke-source",
                    "command":{"kind":kind,"subject":member(workspace,"subject")?,
                    "nonce":random_nonce()?,"target":target,"victimKind":kind,
                    "capability":victim,"controlCapability":control,
                    "expectedTargetRoot":target_root,
                    "expectedAuthorityRoot":signed_authority_root(&challenge)?}}},
                "grants":[{"kind":kind,"target":target,
                    "capability":member(&reference,"observeCapability")?}]})
        }
        "renounce" => {
            // K-RENOUNCE: the holder revokes a capability it holds. Named by a
            // reference (its operation capability) or by number with its kind.
            // `leave: true` (the shell's `room leave`) requires the reference
            // to be a room this workspace joined, not one it founded.
            let obj = request.as_object().ok_or("proposal must be an object")?;
            let leave = obj.get("leave") == Some(&json!(true));
            let extra = usize::from(obj.contains_key("leave"));
            let (kind, capability) = if obj.len() == 3 + extra && obj.contains_key("name") {
                let name = member(&request, "name")?;
                let reference = reference(root, name)?;
                if leave && reference.get("room").and_then(Value::as_str) != Some("member") {
                    return Err(format!(
                        "{name} is not a room you joined (leaving one you founded would renounce your owner grant; use renounce explicitly)"
                    ));
                }
                (
                    member(&reference, "kind")?.to_owned(),
                    member(&reference, "operationCapability")?.to_owned(),
                )
            } else if !leave
                && obj.len() == 4
                && obj.contains_key("capability")
                && obj.contains_key("kind")
            {
                let capability = member(&request, "capability")?;
                decimal(capability, "renounced capability")?;
                let kind = member(&request, "kind")?;
                if !matches!(kind, "object" | "account" | "program") {
                    return Err("renounce kind must be object, account or program".into());
                }
                (kind.to_owned(), capability.to_owned())
            } else {
                return Err(
                    "renounce proposal may contain only type, action, and name [leave] or capability and kind"
                        .into(),
                );
            };
            renounce = Some(json!({"capability":capability,"kind":kind,
                "alsoEnds":delegations_from(root, &capability)}));
            json!({"subject":member(workspace,"subject")?,"nonce":nonce,
                "purpose":{"type":"prepare","draft":{"type":"renounce-source",
                    "command":{"subject":member(workspace,"subject")?,"nonce":random_nonce()?,
                        "kind":kind,"capability":capability}}},
                "grants":[]})
        }
        _ => {
            return Err(
                "proposal action must be invoke, install-policy, install-export, delegate, revoke, or renounce"
                    .into(),
            )
        }
    };
    let intent_bytes = serde_json::to_vec_pretty(&intent).map_err(|error| error.to_string())?;
    let intent_sha = format!("{:x}", Sha256::digest(&intent_bytes));
    let proposal_dir = root.join("proposals").join(proposal_id);
    make_private_dir(&proposal_dir)?;
    private_file(
        &proposal_dir.join("request.json"),
        &serde_json::to_vec_pretty(&request).map_err(|error| error.to_string())?,
    )?;
    private_file(&proposal_dir.join("intent.json"), &intent_bytes)?;
    author(
        &workspace_host(workspace)?,
        &member_path(workspace, "config")?,
        OsStr::new("intent"),
        &proposal_dir.join("intent.json"),
        &proposal_dir.join("intent.bin"),
    )?;
    let summary = json!({"type":"minidregg-workspace-proposal-result-v1",
        "proposalId":proposal_id,"intentPath":proposal_dir.join("intent.json"),
        "intentSha256":intent_sha,"effect":"none","authority":"requires-current-admission",
        "delegation":delegation,"renounce":renounce});
    let bytes = serde_json::to_vec_pretty(&summary).map_err(|error| error.to_string())?;
    private_file(&proposal_dir.join("proposal.json"), &bytes)?;
    Ok(summary)
}

pub(crate) fn submit_intent(
    root: &Path,
    workspace: &Value,
    source: &Path,
    kind: &str,
    prepare_only: bool,
    explicit_attempt: Option<&Path>,
) -> Result<()> {
    let attempt = if let Some(explicit) = explicit_attempt {
        let candidate = absolute(explicit)?;
        let parent = fs::canonicalize(root.join("attempts")).map_err(|error| error.to_string())?;
        let candidate_parent = candidate
            .parent()
            .map(fs::canonicalize)
            .transpose()
            .map_err(|error| error.to_string())?;
        if candidate_parent.as_deref() != Some(parent.as_path()) || candidate.exists() {
            return Err("new attempt must be an unused direct child of workspace attempts".into());
        }
        candidate
    } else {
        new_attempt(root)?.0
    };
    let source = absolute(source)?;
    if kind == "intent" {
        bind_delegation_attempt(root, workspace, &source, &attempt)?;
    }
    eprintln!("workspace attempt: {}", attempt.display());
    submit(
        &workspace_host(workspace)?,
        &member_path(workspace, "config")?,
        &source,
        OsStr::new(kind),
        &member_path(workspace, "key")?,
        &attempt,
        prepare_only,
    )?;
    if !prepare_only {
        renounce_note(&source);
    }
    Ok(())
}

/// The grants this workspace delegated from `capability`, transitively, as
/// its retained proposals record them: `[{capability, recipient, proposal}]`.
/// They end with it (the Host's lineage rule); this is discovery only.
fn delegations_from(root: &Path, capability: &str) -> Vec<Value> {
    let mut records = Vec::new();
    if let Ok(entries) = fs::read_dir(root.join("proposals")) {
        for entry in entries.flatten() {
            let Ok(intent) = bounded_json(&entry.path().join("intent.json")) else {
                continue;
            };
            let command = &intent["purpose"]["draft"]["command"];
            if intent["purpose"]["draft"]["type"] != json!("delegate-source") {
                continue;
            }
            if let (Some(parent), Some(child)) = (
                command["parentId"].as_str(),
                command["child"]["id"].as_str(),
            ) {
                let recipient = command["child"]["holder"]["subject"].clone();
                let proposal = entry.file_name().to_string_lossy().into_owned();
                records.push((parent.to_owned(), child.to_owned(), recipient, proposal));
            }
        }
    }
    let mut ended = Vec::new();
    let mut frontier = vec![capability.to_owned()];
    while let Some(parent) = frontier.pop() {
        for (from, child, recipient, proposal) in &records {
            if from == &parent && !ended.iter().any(|v: &Value| v["capability"] == json!(child)) {
                ended.push(json!({"capability":child,"recipient":recipient,"proposal":proposal}));
                frontier.push(child.clone());
            }
        }
    }
    ended
}

/// After an admitted renounce proposal: say what was renounced and what
/// ended with it.
fn renounce_note(source: &Path) {
    let Some(dir) = source.parent() else { return };
    if source.file_name() != Some(OsStr::new("intent.json")) {
        return;
    }
    let Ok(summary) = bounded_json(&dir.join("proposal.json")) else {
        return;
    };
    let Some(renounced) = summary.get("renounce").filter(|value| value.is_object()) else {
        return;
    };
    let ended: Vec<String> = renounced["alsoEnds"]
        .as_array()
        .map(|list| {
            list.iter()
                .map(|v| {
                    format!(
                        "{} (delegated to {})",
                        v["capability"].as_str().unwrap_or("?"),
                        v["recipient"].as_str().unwrap_or("?")
                    )
                })
                .collect()
        })
        .unwrap_or_default();
    eprintln!(
        "renounced capability {} ({}); ended with it: {}",
        renounced["capability"].as_str().unwrap_or("?"),
        renounced["kind"].as_str().unwrap_or("?"),
        if ended.is_empty() { "nothing this workspace delegated".to_owned() } else { ended.join(", ") }
    );
}

fn bind_delegation_attempt(
    root: &Path,
    workspace: &Value,
    source: &Path,
    attempt: &Path,
) -> Result<()> {
    let source = fs::canonicalize(source).map_err(|error| error.to_string())?;
    if source.file_name() != Some(OsStr::new("intent.json")) {
        return Ok(());
    }
    let proposal_dir = source.parent().ok_or("proposal intent lacks parent")?;
    let proposals = fs::canonicalize(root.join("proposals")).map_err(|error| error.to_string())?;
    if proposal_dir.parent() != Some(proposals.as_path()) {
        return Ok(());
    }
    let proposal_id = proposal_dir
        .file_name()
        .and_then(OsStr::to_str)
        .ok_or("proposal ID is not UTF-8")?;
    validate_name(proposal_id)?;
    let summary = bounded_json(&proposal_dir.join("proposal.json"))?;
    let Some(delegation) = summary.get("delegation").filter(|value| value.is_object()) else {
        return Ok(());
    };
    if member(&summary, "proposalId")? != proposal_id {
        return Err("delegation proposal ID differs from retained path".into());
    }
    let request = bounded_json(&proposal_dir.join("request.json"))?;
    if member(&request, "action")? != "delegate"
        || member(&request, "name")? != member(delegation, "name")?
    {
        return Err("delegation request differs from retained proposal".into());
    }
    let reference = reference(root, member(&request, "name")?)?;
    let fingerprint = serde_json::to_vec(&json!({"request":request,"reference":reference,
        "subject":member(workspace,"subject")?}))
    .map_err(|error| error.to_string())?;
    let namespace = namespace_root(root, workspace)?;
    let reservation = participant_namespace::reserve(
        &namespace,
        member(delegation, "domain")?,
        member(workspace, "subject")?,
        &format!("delegate-{proposal_id}"),
        &fingerprint,
        &[Role {
            label: "childCapability".into(),
            kind: IdKind::Capability,
        }],
    )?;
    if reservation.request_digest != member(delegation, "reservation")?
        || reservation.ids.get("childCapability").map(String::as_str)
            != Some(member(delegation, "childCapability")?)
    {
        return Err("delegation proposal differs from namespace reservation".into());
    }
    let intent = fs::read(&source).map_err(|error| error.to_string())?;
    let source_sha = format!("{:x}", Sha256::digest(&intent));
    if source_sha != member(&summary, "intentSha256")? {
        return Err("delegation intent differs from retained proposal digest".into());
    }
    let binding = participant_namespace::bind_attempt(&reservation, attempt, &source_sha)?;
    let canonical_attempt = fs::canonicalize(attempt.parent().ok_or("attempt lacks parent")?)
        .map_err(|error| error.to_string())?
        .join(attempt.file_name().ok_or("attempt lacks filename")?);
    if binding.attempt_path != canonical_attempt || binding.source_sha256 != source_sha {
        return Err("delegation attempt binding differs from requested exact attempt".into());
    }
    Ok(())
}

pub(crate) fn recover(root: &Path, attempt: &Path) -> Result<()> {
    let attempt = absolute(attempt)?;
    let attempts = fs::canonicalize(root.join("attempts")).map_err(|error| error.to_string())?;
    let candidate = fs::canonicalize(&attempt).map_err(|error| error.to_string())?;
    if candidate.parent() != Some(attempts.as_path()) {
        return Err("recovery attempt must belong directly to this workspace".into());
    }
    retry(&candidate, "lookup", false)
}

pub(crate) fn accepted_outcome(attempt: &Path) -> Result<Option<Value>> {
    let continuity = receipt_continuity::begin_attempt(attempt)?;
    let mut names = Vec::new();
    for entry in fs::read_dir(attempt).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let file = entry.file_name();
        let Some(file) = file.to_str() else { continue };
        if file == "outcome.json" || (file.starts_with("retry-") && file.ends_with(".json")) {
            names.push(file.to_owned());
        }
    }
    names.sort();
    for name in names.iter().rev() {
        let value = bounded_json(&attempt.join(name))?;
        if value.get("type").and_then(Value::as_str) == Some("confirmed")
            && matches!(
                value.get("confirmation").and_then(Value::as_str),
                Some("installed" | "replayed")
            )
        {
            receipt_continuity::finish_attempt(continuity, &value, true)?;
            return Ok(Some(value));
        }
    }
    Ok(None)
}

pub(crate) fn publish_delegation(root: &Path, proposal_id: &str, attempt: &Path) -> Result<()> {
    validate_name(proposal_id)?;
    let proposal_dir = root.join("proposals").join(proposal_id);
    private_dir(&proposal_dir)?;
    let summary = bounded_json(&proposal_dir.join("proposal.json"))?;
    if member(&summary, "type")? != "minidregg-workspace-proposal-result-v1"
        || member(&summary, "proposalId")? != proposal_id
    {
        return Err("delegation proposal identity differs".into());
    }
    let delegation = summary
        .get("delegation")
        .filter(|value| value.is_object())
        .ok_or("proposal is not a delegation")?;
    let source = proposal_dir.join("intent.json");
    let bytes = fs::read(&source).map_err(|error| error.to_string())?;
    if format!("{:x}", Sha256::digest(&bytes)) != member(&summary, "intentSha256")? {
        return Err("retained delegation intent differs from proposal digest".into());
    }
    let source_value: Value = serde_json::from_slice(&bytes).map_err(|error| error.to_string())?;
    let child = &source_value["purpose"]["draft"]["command"]["child"];
    if member(&source_value["purpose"]["draft"], "type")? != "delegate-source"
        || member(child, "id")? != member(delegation, "childCapability")?
        || member(&child["holder"], "subject")? != member(delegation, "recipient")?
        || member(&source_value["purpose"]["draft"]["command"], "kind")?
            != member(delegation, "kind")?
        || member(&source_value["purpose"]["draft"]["command"], "target")?
            != member(delegation, "target")?
    {
        return Err("delegation reference differs from retained source command".into());
    }
    let attempt = fs::canonicalize(attempt).map_err(|error| error.to_string())?;
    let attempts = fs::canonicalize(root.join("attempts")).map_err(|error| error.to_string())?;
    if attempt.parent() != Some(attempts.as_path())
        || !attempt.join("call.bin").is_file()
        || fs::read(attempt.join("intent.json")).map_err(|error| error.to_string())? != bytes
    {
        return Err("delegation attempt lacks this exact retained proposal call".into());
    }
    retry(&attempt, "lookup", false)?;
    let receipt = accepted_outcome(&attempt)?
        .ok_or("delegation historical lookup did not confirm admission")?;
    let mut value = json!({"type":"minidregg-delegated-reference-v1",
        "recipient":member(delegation,"recipient")?,"kind":member(delegation,"kind")?,
        "target":member(delegation,"target")?,
        "capability":member(delegation,"childCapability")?,
        "receipt":receipt,"proposalSha256":member(&summary,"intentSha256")?,
        "authority":"hint-only"});
    // A room invite (the child is `under` the target): the recipient's
    // reference says so, and `room list` shows it.
    if child.get("room").is_some() {
        value["room"] = json!(true);
        // A private room's invite tells the invitee where the wraps are.
        if let Ok(room) = reference(root, member(delegation, "name")?) {
            if let Some(private) = room.get("private") {
                value["private"] = private.clone();
            }
        }
    }
    if let Some(room) = delegation.get("sealedRoom") {
        decimal(room.as_str().ok_or("sealedRoom must be a decimal string")?, "private room target")?;
        value["sealedRoom"] = room.clone();
    }
    let path = proposal_dir.join("recipient-reference.json");
    if path.exists() {
        if bounded_json(&path)? != value {
            return Err("prior delegated reference differs from exact receipt".into());
        }
    } else {
        private_file(
            &path,
            &serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())?,
        )?;
    }
    println!("{}", path.display());
    Ok(())
}

fn complete_birth(
    root: &Path,
    name_value: &str,
    source: &Value,
    receipt: &Value,
    reservation: &participant_namespace::Reservation,
    program_cell: Option<&str>,
    room_template: Option<&str>,
) -> Result<Value> {
    let birth = source.get("birth").ok_or("retained birth source absent")?;
    let parts = birth
        .get("resources")
        .and_then(Value::as_array)
        .and_then(|values| values.first())
        .ok_or("retained birth source lacks resource")?;
    // A Nock program is born at its content address: the Host derives its
    // target, so the reservation holds only the two capability identifiers.
    let target = match program_cell {
        Some(cell) => cell,
        None => member(parts, "target")?,
    };
    let kind = member(parts, "kind")?;
    let owner = member(parts, "ownerCapability")?;
    let control = member(parts, "controlCapability")?;
    if (program_cell.is_none() && reservation.ids.get("target").map(String::as_str) != Some(target))
        || reservation.ids.get("ownerCapability").map(String::as_str) != Some(owner)
        || reservation.ids.get("controlCapability").map(String::as_str) != Some(control)
    {
        return Err("birth source no longer matches durable namespace reservation".into());
    }
    let reference_path = root.join("refs").join(format!("{}.json", ref_file(name_value)));
    if reference_path.exists() {
        let prior = reference(root, name_value)?;
        if member(&prior, "target")? == target && member(&prior, "observeCapability")? == owner {
            return Ok(prior);
        }
        return Err("confirmed birth conflicts with existing workspace reference".into());
    }
    let mut value = json!({"type":"minidregg-participant-reference-v1","name":name_value,
        "kind":kind,"target":target,"observeCapability":owner,
        "operationCapability":owner,"controlCapability":control,
        "provenance":{"birthReceipt":receipt,"reservationDigest":reservation.request_digest,
            "reservationRecord":reservation.record_path},"authority":"hint-only"});
    if let Some(template) = room_template {
        value["room"] = json!(template);
    }
    private_file(
        &reference_path,
        &serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())?,
    )?;
    println!(
        "{}",
        serde_json::to_string_pretty(&value).map_err(|error| error.to_string())?
    );
    Ok(value)
}

/// The shape of one newborn resource. `owner` receives both root grants;
/// it need not be the creator. `funding` moves that amount from the context's
/// fee payer into the newborn, which the Host admits only for an account.
struct BirthShape<'a> {
    kind: &'a str,
    storage: &'a str,
    owner: &'a str,
    predicate: &'a Value,
    funding: Option<&'a str>,
    /// `--in ROOM`: the workspace reference name of the room the resource is
    /// born in (its parent cell); `None` births at the root.
    room: Option<&'a str>,
    /// `storage: "nock"`: the program's canonical DREGG/PROGRAM/v1 record bytes (hex)
    /// from the Host's own nock-check verdict and, when admissible, its cell id.
    /// A program is born at its content address, so no target is reserved.
    program: Option<(String, Option<String>)>,
    /// `storage: "declared"`: the fields the cell may ever hold (K-FIELD-CLOSURE),
    /// `["0","1",…]` or `"open"`. `None` declares none: the cell can hold no field.
    fields: Option<Value>,
    /// Source JSON, encoded and admitted only by Lean.
    world: Option<Value>,
}

/// `--fields`: `open`, or a comma list of field numbers and inclusive ranges
/// (`0-15,20`). The Host refuses a write to any field a cell did not declare.
pub(crate) fn parse_fields(text: &str) -> Result<Value> {
    if text == "open" {
        return Ok(json!("open"));
    }
    let mut fields: Vec<u64> = Vec::new();
    for part in text.split(',') {
        let (low, high) = match part.split_once('-') {
            Some((low, high)) => (low, high),
            None => (part, part),
        };
        let low: u64 = low.parse().map_err(|_| format!("--fields: bad field number {part:?}"))?;
        let high: u64 = high.parse().map_err(|_| format!("--fields: bad field number {part:?}"))?;
        if high < low || high - low > 4096 {
            return Err(format!("--fields: bad range {part:?}").into());
        }
        for field in low..=high {
            if !fields.contains(&field) {
                fields.push(field);
            }
        }
    }
    Ok(Value::Array(fields.into_iter().map(|f| json!(f.to_string())).collect()))
}

/// Immutable authoring generations of one reserved birth request, in order.
fn authoring_generations(base: &Path) -> Result<Vec<PathBuf>> {
    let mut numbers = Vec::new();
    for entry in fs::read_dir(base).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let name = entry.file_name();
        let name = name.to_str().ok_or("non-UTF-8 authoring generation")?;
        let number = name
            .strip_prefix('g')
            .filter(|digits| digits.len() == 4 && digits.bytes().all(|b| b.is_ascii_digit()))
            .and_then(|digits| digits.parse::<u32>().ok())
            .filter(|number| *number > 0)
            .ok_or_else(|| format!("unknown entry in authoring generations: {name}"))?;
        numbers.push(number);
    }
    numbers.sort_unstable();
    for (index, number) in numbers.iter().enumerate() {
        if *number != index as u32 + 1 {
            return Err("authoring generations are not contiguous".into());
        }
    }
    Ok(numbers
        .into_iter()
        .map(|number| base.join(format!("g{number:04}")))
        .collect())
}

/// A retained Host reply that is an explicit refusal, never an intent.
fn authoring_refused(generation: &Path) -> Result<bool> {
    let reply = generation.join("reply.frame");
    if !reply.exists() {
        return Ok(false);
    }
    let bytes = fs::read(&reply).map_err(|error| error.to_string())?;
    Ok(bytes.first() == Some(&255))
}

/// A generation whose intent belonged to an attempt that was definitely
/// unadmitted and released (`release_unadmitted_attempt`). Like a refusal, it
/// is superseded by a fresh generation; unlike a refusal, it holds an intent.
fn authoring_released(generation: &Path) -> bool {
    generation.join("released.json").exists()
}

/// Whether a retained exact-custody attempt is DEFINITELY unadmitted: it never
/// assembled an exact call (so nothing was ever submitted), or the newest Host
/// outcome for its exact call is a final `refused`. A confirmed, uncertain,
/// unavailable, contended or absent outcome is not definite and keeps custody.
fn attempt_definitely_unadmitted(attempt: &Path) -> Result<bool> {
    if !attempt.join("call.bin").is_file() {
        return Ok(true);
    }
    if accepted_outcome(attempt)?.is_some() {
        return Ok(false);
    }
    let mut names = Vec::new();
    for entry in fs::read_dir(attempt).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let file = entry.file_name();
        let Some(file) = file.to_str() else { continue };
        if file == "outcome.json" || (file.starts_with("retry-") && file.ends_with(".json")) {
            names.push(file.to_owned());
        }
    }
    names.sort();
    let Some(newest) = names.last() else {
        return Ok(false);
    };
    let value = bounded_json(&attempt.join(newest))?;
    Ok(value.get("type").and_then(Value::as_str) == Some("refused"))
}

/// Release a definitely unadmitted birth attempt so the same name can be
/// authored again: mark the generation that authored its intent released,
/// release the namespace binding, and retire the attempt directory (kept as
/// `NAME.released-N` with all its evidence). Each step is idempotent and the
/// retirement, which removes the trigger, is last.
fn release_unadmitted_attempt(
    authoring: &Path,
    attempt: &Path,
    reservation: &participant_namespace::Reservation,
) -> Result<PathBuf> {
    if authoring.exists() {
        if let Some(generation) = authoring_generations(authoring)?.last() {
            if !authoring_released(generation) && !authoring_refused(generation)? {
                let marker = json!({"type":"minidregg-birth-generation-released-v1",
                    "attempt":attempt});
                private_file(
                    &generation.join("released.json"),
                    &serde_json::to_vec(&marker).map_err(|error| error.to_string())?,
                )?;
            }
        }
    }
    participant_namespace::release_attempt(reservation, attempt)?;
    retire_attempt_dir(attempt)
}

/// Move an attempt directory aside as `NAME.released-N`, keeping every byte of
/// its evidence, so the attempt path can hold a new attempt.
fn retire_attempt_dir(attempt: &Path) -> Result<PathBuf> {
    let name = attempt
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or("birth attempt lacks a UTF-8 filename")?;
    let mut index = 1u32;
    let retired = loop {
        let candidate = attempt.with_file_name(format!("{name}.released-{index:04}"));
        if !candidate.exists() {
            break candidate;
        }
        index += 1;
        if index >= 10_000 {
            return Err("released birth attempts exhausted for this name".into());
        }
    };
    fs::rename(attempt, &retired).map_err(|error| error.to_string())?;
    File::open(attempt.parent().ok_or("birth attempt lacks parent")?)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| error.to_string())?;
    Ok(retired)
}

/// Author the reserved source through op91 in versioned generations.
///
/// A generation retains exactly one signed factory observation and at most one
/// Host reply; it is never rewritten. Once a generation holds an intent, it is
/// final. A refused generation (or one whose attempt was released as definitely
/// unadmitted, `release_unadmitted_attempt`) is superseded by a new generation that authors
/// the SAME source with a fresh observation, and only while no custody attempt
/// is bound for this request: a refusal retained from an earlier call, or a
/// retained observation from an earlier call refused now, is superseded once;
/// a generation observed in this call is superseded only when `stale` finds
/// the Host answering its own `stale-root` to that observation (the timer race
/// at birth), at most `replan::max()` times (the shared `replan` loop).
fn author_generations(
    base: &Path,
    reservation: &participant_namespace::Reservation,
    mut observe: impl FnMut() -> Result<PathBuf>,
    mut author_one: impl FnMut(&Path, Option<&Path>) -> Result<()>,
    mut stale: impl FnMut(&Path) -> bool,
) -> Result<PathBuf> {
    if !base.exists() {
        make_private_dir(base)?;
    }
    private_dir(base)?;
    let latest = || -> Result<PathBuf> {
        match authoring_generations(base)?.last() {
            Some(current) => Ok(current.clone()),
            None => {
                let first = base.join("g0001");
                make_private_dir(&first)?;
                Ok(first)
            }
        }
    };
    let supersede = || -> Result<()> {
        if participant_namespace::is_bound(reservation)? {
            return Err(
                "refused authoring generation has a bound attempt; exact custody only".into(),
            );
        }
        let next = authoring_generations(base)?.len() + 1;
        make_private_dir(&base.join(format!("g{next:04}")))
    };
    let current = latest()?;
    if authoring_refused(&current)? || authoring_released(&current) {
        supersede()?;
    }
    let observed_now = std::cell::Cell::new(false);
    let authored = crate::replan::replan(
        "birth authoring",
        || {
            let current = latest()?;
            private_dir(&current)?;
            if current.join("reply.frame").exists() && !authoring_refused(&current)? {
                return Ok(current);
            }
            let observation = if current.join("factory-observation.bin").exists() {
                observed_now.set(false);
                None
            } else {
                observed_now.set(true);
                Some(observe()?)
            };
            match author_one(&current, observation.as_deref()) {
                Ok(()) => Ok(current),
                Err(error) => {
                    if authoring_refused(&current)? {
                        eprintln!(
                            "workspace birth authoring refused in {}: {error}",
                            current.display()
                        );
                    }
                    Err(error)
                }
            }
        },
        |_, _| match latest() {
            Ok(current) if authoring_refused(&current).unwrap_or(false) => {
                !observed_now.get() || stale(&current)
            }
            _ => false,
        },
        |_| supersede(),
    );
    authored.map_err(|error| match latest() {
        Ok(current) if authoring_refused(&current).unwrap_or(false) => format!(
            "current birth authoring refused with a fresh factory observation ({error}); retained {}",
            current.join("reply.frame").display()
        ),
        _ => error,
    })
}

/// Reserve, author and submit one birth under a workspace name. Returns the
/// retained source, the confirmed receipt and the namespace reservation.
fn birth(
    root: &Path,
    workspace: &Value,
    name_value: &str,
    shape: &BirthShape<'_>,
) -> Result<(Value, Value, participant_namespace::Reservation)> {
    validate_ref_name(name_value)?;
    // `--in ROOM`: the new resource is born in the room a workspace reference
    // names. The Host refuses a room that is not a present resource cell.
    // The creator's placing capability is the room reference's operation
    // capability (its observe capability when it holds no other): the Host's
    // birth gate requires it to cover the room with `place` (or `mutate`), held
    // by the creator, and the room's law to accept the placement.
    let room = match shape.room {
        Some(room_name) => {
            let room_ref = reference(root, room_name)?;
            let placement = room_ref
                .get("operationCapability")
                .and_then(Value::as_str)
                .map_or_else(|| member(&room_ref, "observeCapability"), Ok)?
                .to_string();
            Some((member(&room_ref, "target")?.to_string(), placement))
        }
        None => None,
    };
    if !matches!(shape.storage, "content" | "declared" | "stream" | "nock" | "world-kind" | "world-instance") {
        return Err("supported storage is content, declared, stream, nock, world-kind or world-instance".into());
    }
    if shape.fields.is_some() && shape.storage != "declared" {
        return Err("--fields is only for declared storage".into());
    }
    decimal(shape.owner, "birth owner")?;
    // An account (a realm well, or a holder's purse) is declared storage only.
    if !matches!((shape.kind, shape.storage), ("object", _) | ("account", "declared")) {
        return Err("resource kind is object, or account with declared storage".into());
    }
    if matches!(shape.storage, "world-kind" | "world-instance") != shape.world.is_some() {
        return Err("world storage requires source definition or signed kind selection".into());
    }
    let program = shape.program.clone();
    match (shape.storage, &program) {
        ("nock", None) => return Err("nock storage requires --program".into()),
        (storage, Some(_)) if storage != "nock" => {
            return Err("--program is only for nock storage".into())
        }
        _ => {}
    }
    let context_path = member_path(workspace, "birthContext")?;
    let namespace_root = namespace_root(root, workspace)?;
    let context = bounded_json(&context_path)?;
    if member(&context, "type")? != "minidregg-participant-birth-context-v1" {
        return Err("unknown birth context version".into());
    }
    let request_path = root
        .join("sources")
        .join(format!("create-{}.request.json", ref_file(name_value)));
    let mut requested_core = json!({"type":"minidregg-workspace-create-request-v2",
        "name":name_value,"kind":shape.kind,"storage":shape.storage,"owner":shape.owner,
        "funding":shape.funding,"predicate":shape.predicate,"context":context,
        "subject":member(workspace,"subject")?});
    if let Some((room, placement)) = &room {
        requested_core["room"] = json!(room);
        requested_core["placement"] = json!(placement);
    }
    if let Some((hex, _)) = &program {
        requested_core["programSha256"] = json!(format!("{:x}", Sha256::digest(hex.as_bytes())));
    }
    if let Some(fields) = &shape.fields {
        requested_core["fields"] = fields.clone();
    }
    if let Some(world) = &shape.world {
        requested_core["world"] = world.clone();
    }
    let request = if request_path.exists() {
        let saved = bounded_json(&request_path)?;
        let nonce = member(&saved, "nonce")?;
        decimal(nonce, "retained birth nonce")?;
        let mut expected = requested_core.clone();
        expected["nonce"] = json!(nonce);
        if saved != expected {
            return Err("existing create request differs; use a new name".into());
        }
        saved
    } else {
        let mut requested = requested_core;
        requested["nonce"] = json!(random_nonce()?);
        let requested_bytes = serde_json::to_vec(&requested).map_err(|error| error.to_string())?;
        private_file(&request_path, &requested_bytes)?;
        requested
    };
    let stable_request = serde_json::to_vec(&request).map_err(|error| error.to_string())?;
    let mut roles = vec![
        Role {
            label: "target".into(),
            kind: IdKind::Resource,
        },
        Role {
            label: "ownerCapability".into(),
            kind: IdKind::Capability,
        },
        Role {
            label: "controlCapability".into(),
            kind: IdKind::Capability,
        },
    ];
    if program.is_some() {
        roles.remove(0);
    }
    let reservation = participant_namespace::reserve(
        &namespace_root,
        member(&context["genesis"], "domain")?,
        member(workspace, "subject")?,
        name_value,
        &stable_request,
        &roles,
    )?;
    let (funding, source_capabilities) = match shape.funding {
        None => (
            context["funding"].clone(),
            context["sourceCapabilities"].clone(),
        ),
        Some(amount) => {
            field_decimal(amount, "funding amount")?;
            if context["funding"]
                .as_array()
                .is_none_or(|moves| !moves.is_empty())
            {
                return Err("funded birth requires a context without prior funding".into());
            }
            let payer = member(&context, "feePayer")?;
            let payer_capability = context["grants"]
                .as_array()
                .and_then(|grants| {
                    grants.iter().find(|grant| {
                        grant.get("kind").and_then(Value::as_str) == Some("account")
                            && grant.get("target").and_then(Value::as_str) == Some(payer)
                    })
                })
                .and_then(|grant| grant.get("capability").cloned())
                .ok_or("birth context lacks the fee payer's account grant")?;
            let mut capabilities = vec![payer_capability];
            capabilities.extend(
                context["sourceCapabilities"]
                    .as_array()
                    .ok_or("birth context lacks source capabilities")?
                    .iter()
                    .cloned(),
            );
            (
                json!([{"source":payer,"destination":reservation.ids["target"],
                    "asset":member(&context["genesis"],"asset")?,"amount":amount}]),
                Value::Array(capabilities),
            )
        }
    };
    let source_path = root
        .join("sources")
        .join(format!("create-{}.json", ref_file(name_value)));
    let nonce = member(&request, "nonce")?;
    let resource = match &program {
        Some((hex, _)) => json!({"kind":shape.kind,"storage":shape.storage,"program":hex,
            "owner":shape.owner,
            "ownerCapability":reservation.ids["ownerCapability"],
            "controlCapability":reservation.ids["controlCapability"],
            "predicate":shape.predicate}),
        None => json!({"kind":shape.kind,"storage":shape.storage,
            "target":reservation.ids["target"],"owner":shape.owner,
            "ownerCapability":reservation.ids["ownerCapability"],
            "controlCapability":reservation.ids["controlCapability"],
            "predicate":shape.predicate}),
    };
    // K-NARROW-HIDE: a declared or content cell is born blinded, with a
    // blinding this workspace's key derives for this cell id, so its owner
    // recomputes every salt and no reader of a subset of fields holds an
    // unsalted commitment to the rest.
    let mut resource = resource;
    if let Some(world) = &shape.world {
        for (key, value) in world.as_object().ok_or("world birth source must be an object")? {
            resource[key] = value.clone();
        }
        if shape.storage == "world-kind" {
            resource["definition"] = world_kind::definition(&resource["definition"], Some(&reservation.ids["target"]))?;
        }
    }
    if matches!(shape.storage, "declared" | "content" | "grain") && program.is_none() {
        let seed = crate::hiding::read_seed(&member_path(workspace, "key")?)?;
        let target = reservation.ids["target"].as_str();
        resource["blinding"] = json!(crate::hiding::cell_blinding(
            &crate::hiding::blinding_key(&seed),
            target
        )?);
    }
    // K-FIELD-CLOSURE: a declared cell names the fields it may hold.
    if let Some(fields) = &shape.fields {
        resource["fields"] = fields.clone();
    }
    let mut expected_source = json!({"subject":member(workspace,"subject")?,"nonce":nonce,
            "birth":{"genesis":context["genesis"],"template":context["template"],
                "creator":member(workspace,"subject")?,"nonce":nonce,
                "resources":[resource],
                "sourceCapabilities":source_capabilities,
                "funding":funding,"feePayer":context["feePayer"]},
            "grants":context["grants"]});
    if let Some((room, placement)) = &room {
        expected_source["birth"]["resources"][0]["room"] = json!(room);
        expected_source["birth"]["resources"][0]["placement"] = json!(placement);
    }
    let source = if source_path.exists() {
        let saved = bounded_json_limit(&source_path, MAX_PROGRAM_SOURCE)?;
        if saved != expected_source {
            return Err("retained birth source differs from reservation request".into());
        }
        saved
    } else {
        private_file(
            &source_path,
            &serde_json::to_vec_pretty(&expected_source).map_err(|error| error.to_string())?,
        )?;
        expected_source
    };
    let parts = source["birth"]["resources"]
        .as_array()
        .and_then(|values| values.first())
        .ok_or("retained birth source lacks resource")?;
    for role in ["target", "ownerCapability", "controlCapability"] {
        if role == "target" && program.is_some() {
            continue;
        }
        if parts.get(role).and_then(Value::as_str) != reservation.ids.get(role).map(String::as_str)
        {
            return Err("retained birth source differs from namespace reservation".into());
        }
    }
    let socket = SOCKET
        .get()
        .ok_or("workspace create requires a pinned persistent Host socket")?;
    let authoring = root
        .join("sources")
        .join(format!("create-{}.authoring", ref_file(name_value)));
    let attempt = root.join("attempts").join(format!("create-{}", ref_file(name_value)));
    let host = workspace_host(workspace)?;
    let config = member_path(workspace, "config")?;
    // A definitely unadmitted attempt (no exact call, or a final refusal)
    // holds nothing that can install: release it, and this call authors the
    // same name afresh. An uncertain attempt keeps exact custody below.
    if attempt.exists() && attempt_definitely_unadmitted(&attempt)? {
        let retired = release_unadmitted_attempt(&authoring, &attempt, &reservation)?;
        eprintln!(
            "workspace birth attempt definitely unadmitted; retained as {}",
            retired.display()
        );
    }
    let author_dir = if attempt.exists() {
        authoring_generations(&authoring)?
            .last()
            .cloned()
            .ok_or("birth attempt exists without an authoring generation")?
    } else {
        let factory = member(&context["genesis"], "factoryId")?;
        let grants = context
            .get("grants")
            .and_then(Value::as_array)
            .ok_or("birth context lacks grants")?;
        let matching: Vec<_> = grants
            .iter()
            .filter(|grant| {
                grant.get("kind").and_then(Value::as_str) == Some("object")
                    && grant.get("target").and_then(Value::as_str) == Some(factory)
            })
            .collect();
        if matching.len() != 1 {
            return Err("birth context needs one factory resource observation grant".into());
        }
        let factory_ref = json!({"kind":"object","target":factory,
            "observeCapability":member(matching[0],"capability")?});
        author_generations(
            &authoring,
            &reservation,
            || Ok(signed_view(root, workspace, &factory_ref, "resource")?.2),
            |generation, observation| {
                current_birth::author(
                    &host,
                    &config,
                    socket,
                    &source_path,
                    observation,
                    generation,
                    current_birth::Route::Resource,
                )
            },
            |generation| crate::observation_stale(&host, &config, generation),
        )?
    };
    let intent_path = current_birth::retained_intent(&author_dir, current_birth::Route::Resource)?;
    if fs::read(author_dir.join("source.json")).map_err(|error| error.to_string())?
        != fs::read(&source_path).map_err(|error| error.to_string())?
    {
        return Err("current birth author source differs from reserved workspace source".into());
    }
    let source_sha = format!(
        "{:x}",
        Sha256::digest(
            fs::read(&intent_path)
                .map_err(|error| format!("cannot hash retained current birth intent: {error}"))?
        )
    );
    let binding = participant_namespace::bind_attempt(&reservation, &attempt, &source_sha)?;
    let canonical_attempt = fs::canonicalize(attempt.parent().ok_or("birth attempt lacks parent")?)
        .map_err(|error| error.to_string())?
        .join(attempt.file_name().ok_or("birth attempt lacks filename")?);
    if binding.attempt_path != canonical_attempt || binding.source_sha256 != source_sha {
        return Err("namespace attempt binding differs from workspace create".into());
    }
    if attempt.exists() {
        if !attempt.join("call.bin").is_file() {
            return Err(format!(
                "create preparation interrupted before exact call; inspect {}",
                attempt.display()
            ));
        }
        if let Some(receipt) = accepted_outcome(&attempt)? {
            return Ok((source, receipt, reservation));
        }
        retry(&attempt, "lookup", false)?;
        let receipt = accepted_outcome(&attempt)?
            .ok_or("historical create lookup did not confirm installed birth")?;
        return Ok((source, receipt, reservation));
    }
    eprintln!("workspace birth attempt: {}", attempt.display());
    // A Host `stale-root` between the signed observation and prepare (or a
    // signed plan the state moved under) is re-planned inside `submit`: the
    // authored window (`notBefore` + birthSlack) is still open, so the SAME
    // intent is planned again in the same bound attempt path.
    submit(
        &host,
        &config,
        &intent_path,
        OsStr::new("binary"),
        &member_path(workspace, "key")?,
        &attempt,
        false,
    )?;
    let receipt = accepted_outcome(&attempt)?.ok_or("birth returned without installed receipt")?;
    Ok((source, receipt, reservation))
}

pub(crate) fn create(
    root: &Path,
    workspace: &Value,
    name_value: &str,
    storage: &str,
    predicate_path: &Path,
    room: Option<&str>,
    kind: &str,
    owner: Option<&str>,
    program_path: Option<&Path>,
    fields: Option<&str>,
) -> Result<()> {
    create_with_template(root, workspace, name_value, storage, predicate_path, room, kind,
        owner, program_path, fields, None)
}

fn create_with_template(
    root: &Path,
    workspace: &Value,
    name_value: &str,
    storage: &str,
    predicate_path: &Path,
    room: Option<&str>,
    kind: &str,
    owner: Option<&str>,
    program_path: Option<&Path>,
    fields: Option<&str>,
    room_template: Option<&str>,
) -> Result<()> {
    let predicate = bounded_json(predicate_path)?;
    let fields = fields.map(parse_fields).transpose()?;
    // A private room's key goes into the encrypted cache: refuse before the
    // birth, not after it.
    if room_template == Some("private") {
        if std::env::var_os(private::KEYCACHE_PASSPHRASE_ENV).is_none() {
            return Err(format!(
                "a private room's keys live in this workspace's encrypted key cache: set {}",
                private::KEYCACHE_PASSPHRASE_ENV
            ));
        }
        roomkey::keys_name(name_value)?;
    }
    // A cell born in a private room is sealed under it by default.
    let sealed_in = match room {
        Some(parent) => reference(root, parent)?
            .get("private")
            .is_some()
            .then(|| parent.to_owned()),
        None => None,
    };
    // `--program VERDICT.json`: the Host's own nock-check verdict (op 131): its
    // canonical DREGG/PROGRAM/v1 record bytes and, when admissible, its cell id.
    let program = match program_path {
        Some(path) => {
            let verdict = bounded_json_limit(path, MAX_PROGRAM_SOURCE)?;
            if verdict.get("type").and_then(Value::as_str) != Some("nock-check") {
                return Err("--program must be a Host nock-check verdict".into());
            }
            Some((
                member(&verdict, "program")?.to_owned(),
                verdict.get("cellId").and_then(Value::as_str).map(str::to_owned),
            ))
        }
        None => None,
    };
    // `--owner SUBJECT`: the creator pays for and births a resource owned by
    // another subject (a room founder birthing a member's stream); the owner
    // and control grants are issued to that subject, not to the creator.
    let subject = match owner {
        Some(owner) => owner.to_owned(),
        None => member(workspace, "subject")?.to_owned(),
    };
    let (source, receipt, reservation) = birth(
        root,
        workspace,
        name_value,
        &BirthShape {
            kind,
            storage,
            owner: &subject,
            predicate: &predicate,
            funding: None,
            room,
            program: program.clone(),
            fields,
            world: None,
        },
    )?;
    let program_cell = program.as_ref().and_then(|(_, cell)| cell.as_deref());
    let mut born =
        complete_birth(root, name_value, &source, &receipt, &reservation, program_cell, room_template)?;
    if let Some(parent) = sealed_in {
        born["sealedIn"] = json!(parent);
        roomkey::rewrite_reference(root, name_value, &born)?;
    }
    if room_template == Some("private") {
        roomkey::found(root, workspace, name_value)?;
    }
    Ok(())
}

/// `doc-new`: a content cell and its document in one verb: the birth, then
/// `createDocument` (an empty root container). Without the document a cell
/// holds atoms in no tree: an appended line would stand in no order and `doc
/// show` would print nothing (K-ELEMENT-TREE `appendLeaf`).
fn doc_new(root: &Path, workspace: &Value, name: &str, predicate_path: &Path, room: Option<&str>) -> Result<()> {
    create(root, workspace, name, "content", predicate_path, room, "object", None, None, None)?;
    let element = random_nonce()?;
    submit_content(
        root,
        workspace,
        name,
        vec![json!({"type":"createDocument","rootElement":element,"schema":"0"})],
        "document",
    )
}

/// A declared account the sponsor births for another admitted subject, funded
/// from the context fee payer (the shape `provision` uses). The owner holds
/// both root grants, so this workspace retains only a hint-only handoff record
/// for that owner, never a reference it cannot use.
pub(crate) fn create_funded_account(
    root: &Path,
    workspace: &Value,
    name_value: &str,
    predicate: &Value,
    owner: &str,
    amount: &str,
) -> Result<Value> {
    let (source, receipt, reservation) = birth(
        root,
        workspace,
        name_value,
        &BirthShape {
            kind: "account",
            storage: "declared",
            owner,
            predicate,
            funding: Some(amount),
            room: None,
            program: None,
            fields: None,
            world: None,
        },
    )?;
    let resource = &source["birth"]["resources"][0];
    let target = member(resource, "target")?;
    let owner_capability = member(resource, "ownerCapability")?;
    let control = member(resource, "controlCapability")?;
    let value = json!({"type":"minidregg-fleet-account-handoff-v1","name":name_value,
        "owner":owner,"kind":"account","target":target,"observeCapability":owner_capability,
        "operationCapability":owner_capability,"controlCapability":control,"funding":amount,
        "provenance":{"birthReceipt":receipt,"reservationDigest":reservation.request_digest,
            "reservationRecord":reservation.record_path},"authority":"hint-only"});
    retain_or_compare(
        &root
            .join("sources")
            .join(format!("create-{}.handoff.json", ref_file(name_value))),
        &value,
    )?;
    Ok(value)
}

fn retain_or_compare(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    if path.exists() {
        if bounded_json(path)? != *value {
            return Err(format!("retained {} differs", path.display()));
        }
        return Ok(());
    }
    private_file(path, &bytes)
}

struct Provision<'a> {
    name: &'a str,
    holder: &'a str,
    funding: &'a str,
    predicate: &'a Path,
    factory_ref: &'a str,
}

/// Sponsor-side provisioning of an enrolled subject for independent creation:
/// (1) the source-owned factory-observation grant, which the Host refuses for
/// a subject that is not enrolled; (2) an ordinary birth of an account OWNED by
/// that subject, funded from the sponsor's payer. Both are admitted by the Host
/// under current authority. The emitted birth context is a discovery hint for
/// the holder, not a grant.
fn provision(root: &Path, workspace: &Value, request: &Provision<'_>) -> Result<()> {
    validate_name(request.name)?;
    decimal(request.holder, "provisioned holder")?;
    if request.holder == member(workspace, "subject")? {
        return Err("a sponsor does not provision itself".into());
    }
    let predicate = bounded_json(request.predicate)?;
    let provisions = root.join("provisions");
    if !provisions.exists() {
        make_private_dir(&provisions)?;
    }
    let directory = provisions.join(request.name);
    if !directory.exists() {
        make_private_dir(&directory)?;
    }
    private_dir(&directory)?;
    let factory = reference(root, request.factory_ref)?;
    let context = bounded_json(&member_path(workspace, "birthContext")?)?;
    if member(&factory, "target")? != member(&context["genesis"], "factoryId")? {
        return Err("factory reference differs from the birth context factory".into());
    }
    let control = factory
        .get("controlCapability")
        .and_then(Value::as_str)
        .ok_or("factory reference lacks a control capability")?;
    let observed = crate::participant_provisioning::observe_grant(
        &crate::participant_provisioning::ObserveGrant {
            host: &workspace_host(workspace)?,
            config: &member_path(workspace, "config")?,
            socket: SOCKET
                .get()
                .ok_or("provisioning requires a pinned persistent Host socket")?,
            sponsor_key: &member_path(workspace, "key")?,
            namespace_root: &namespace_root(root, workspace)?,
            domain: member(&context["genesis"], "domain")?,
            name: request.name,
            sponsor: member(workspace, "subject")?,
            control,
            observe: member(&factory, "observeCapability")?,
            factory: member(&factory, "target")?,
            holder: request.holder,
            directory: &directory.join("observe"),
        },
    )?;
    let account_name = format!("account-{}", request.name);
    let (source, account_receipt, _) = birth(
        root,
        workspace,
        &account_name,
        &BirthShape {
            kind: "account",
            storage: "declared",
            owner: request.holder,
            predicate: &predicate,
            funding: Some(request.funding),
            room: None,
            program: None,
            fields: None,
            world: None,
        },
    )?;
    let account = &source["birth"]["resources"][0];
    let account_target = member(account, "target")?;
    let account_owner = member(account, "ownerCapability")?;
    let holder_context = json!({"type":"minidregg-participant-birth-context-v1",
        "genesis":context["genesis"],"template":context["template"],
        "sourceCapabilities":[account_owner],"funding":[],"feePayer":account_target,
        "grants":[{"kind":"object","target":member(&factory,"target")?,
                "capability":member(&observed,"capability")?},
            {"kind":"account","target":account_target,"capability":account_owner}]});
    let context_path = directory.join("birth-context.json");
    retain_or_compare(&context_path, &holder_context)?;
    let summary = json!({"type":"minidregg-participant-provisioning-v1",
        "name":request.name,"holder":request.holder,
        "account":{"target":account_target,"ownerCapability":account_owner,
            "controlCapability":member(account,"controlCapability")?,
            "funded":request.funding,"birthReceipt":account_receipt,
            "attempt":root.join("attempts").join(format!("create-{account_name}"))},
        "factoryObservation":observed,"birthContext":context_path,
        "authority":"hint-only; the Host checks every grant at use"});
    retain_or_compare(&directory.join("provision.json"), &summary)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&summary).map_err(|error| error.to_string())?
    );
    Ok(())
}

/// Receipt-only replay of both provisioning operations after a restart.
fn provision_lookup(root: &Path, workspace: &Value, name: &str, factory_ref: &str) -> Result<()> {
    validate_name(name)?;
    let directory = root.join("provisions").join(name);
    let summary = bounded_json(&directory.join("provision.json"))?;
    let factory = reference(root, factory_ref)?;
    let context = bounded_json(&member_path(workspace, "birthContext")?)?;
    retry(
        &member_path(&summary["account"], "attempt")?,
        "lookup",
        false,
    )?;
    let observed = crate::participant_provisioning::observe_lookup(
        &crate::participant_provisioning::ObserveGrant {
            host: &workspace_host(workspace)?,
            config: &member_path(workspace, "config")?,
            socket: SOCKET
                .get()
                .ok_or("provisioning requires a pinned persistent Host socket")?,
            sponsor_key: &member_path(workspace, "key")?,
            namespace_root: &namespace_root(root, workspace)?,
            domain: member(&context["genesis"], "domain")?,
            name,
            sponsor: member(workspace, "subject")?,
            control: factory
                .get("controlCapability")
                .and_then(Value::as_str)
                .ok_or("factory reference lacks a control capability")?,
            observe: member(&factory, "observeCapability")?,
            factory: member(&factory, "target")?,
            holder: member(&summary, "holder")?,
            directory: &directory.join("observe"),
        },
    )?;
    println!(
        "{}",
        serde_json::to_string_pretty(
            &json!({"type":"minidregg-participant-provisioning-lookup-v1",
            "factoryObservation":observed})
        )
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

// ---------------------------------------------------------------- documents
//
// A document is a content cell (`storage: content`). Its page is what the Host
// shows in a signed `view-resource`: every entry, spelled by Lean's
// `contentEntryJson`. The client never decodes an entry's canonical bytes; it
// reads the Host's JSON, and it lowers line-level document actions into the
// Host's own content grammar (`Kernel/ContentResource.lean` `Action`).
//
// Lines follow the kernel's element-tree order. `doc show` retains the signed
// ciphertext view and its separate opened presentation under
// `seen/NAME.json`; an edit carries the line exactly as that read saw it, so an
// edit of a line someone else changed since is refused by the Host (`staleAtom`)
// rather than silently overwritten.

/// The cell of a signed content view, or an error naming what the resource is.
/// A content cell's entries are typed hyperdocument records (`type`); a declared
/// cell's are `key`/`value` fields. The document a content cell holds is
/// `documentOf target`, the resource's own id, so it is not read from the cell.
fn content_page<'a>(view: &'a Value, name: &str) -> Result<&'a Value> {
    let cell = view.get("cell").ok_or("signed resource view lacks cell")?;
    match cell_storage(cell)? {
        "content" => Ok(cell),
        storage => Err(format!("{name} is not a document (its storage is {storage}, not content)")),
    }
}

/// Which storage a signed resource view's cell is, read from the shape the
/// Host spells it in (`Host/Json.lean` `resourceJson`): a stream cell carries
/// `nextSeq`; a declared cell's entries are `key`/`value` fields; a content
/// cell's entries are typed hyperdocument records. An empty stream has no
/// entries, so `nextSeq` is what tells it from a document.
fn cell_storage(cell: &Value) -> Result<&'static str> {
    if cell.get("worldKind").is_some() { return Ok("world-kind"); }
    if cell.get("worldInstance").is_some() { return Ok("world-instance"); }
    // A stream read shows its HEAD (nextSeq, count, tail, binding; no
    // entries: they are their own cells, read with `tail`), FLEET-TOPIC-ON-STREAM.
    if cell.get("nextSeq").is_some() || cell.get("head").is_some() {
        return Ok("stream");
    }
    let entries = cell
        .get("entries")
        .and_then(Value::as_array)
        .ok_or("signed resource view lacks cell entries")?;
    if entries.iter().any(|entry| entry.get("key").is_some()) {
        return Ok("declared");
    }
    if entries.iter().any(|entry| entry.get("type").is_none()) {
        return Ok("unknown");
    }
    Ok("content")
}

/// The URI scheme of a link from a document to a resource that is not a
/// document (a stream, a declared cell). The hyperdocument's `LinkTarget` has
/// no resource constructor, so such a link is `external mini:KIND/ID` with an
/// empty authority (this node): the resource's kind and id, nothing else.
const RESOURCE_LINK_SCHEME: &str = "mini";

fn resource_link_target(kind: &str, target: &str) -> Value {
    json!({"type":"external","scheme":crate::hex(RESOURCE_LINK_SCHEME.as_bytes()),
        "authority":"","path":crate::hex(format!("{kind}/{target}").as_bytes())})
}

/// `(kind, id)` of a link target that names a resource on this node
/// (`resource_link_target`), as the Host spells it back.
fn resource_link_of(target: &Value) -> Option<(String, String)> {
    if target.get("type").and_then(Value::as_str) != Some("external") {
        return None;
    }
    let text = |key: &str| {
        unhex(target.get(key)?.as_str()?).ok().and_then(|bytes| String::from_utf8(bytes).ok())
    };
    if text("scheme")? != RESOURCE_LINK_SCHEME || !text("authority")?.is_empty() {
        return None;
    }
    let path = text("path")?;
    let (kind, id) = path.split_once('/')?;
    (matches!(kind, "object" | "account" | "program") && decimal(id, "id").is_ok())
        .then(|| (kind.to_owned(), id.to_owned()))
}

fn page_entries(page: &Value) -> Result<&Vec<Value>> {
    page.get("entries")
        .and_then(Value::as_array)
        .ok_or_else(|| "content cell lacks entries".to_owned())
}

/// The exact `AtomRecord` an `editAtom` names as `before`: the Host's atom
/// entry without its address and canonical bytes.
/// The atom record an `editAtom.before` names, exactly as the signed view spelled
/// it (K-CONTENT: the record carries its `revision`, so an edit or annotation
/// made from a stale read is refused `staleAtom`).
fn atom_record(atom: &Value) -> Result<Value> {
    let mut record = serde_json::Map::new();
    for key in ["document", "kind", "payload", "createdBy", "createdAt", "revision", "tombstonedAt"] {
        record.insert(
            key.to_owned(),
            atom.get(key)
                .cloned()
                .ok_or_else(|| format!("atom entry lacks {key}"))?,
        );
    }
    Ok(Value::Object(record))
}

fn seen_path(root: &Path, name: &str) -> Result<PathBuf> {
    validate_ref_name(name)?;
    Ok(root.join("seen").join(format!("{}.json", ref_file(name))))
}

/// Test fixture wrapper for a raw-only retained view.
#[cfg(test)]
fn retain_seen(root: &Path, name: &str, view: &Value, document: &Value, challenge: &Value) -> Result<()> {
    retain_seen_value(root, name, &seen_value(name, view, document, challenge))
}

fn retain_seen_value(root: &Path, name: &str, value: &Value) -> Result<()> {
    let dir = root.join("seen");
    if !dir.exists() {
        make_private_dir(&dir)?;
    }
    private_dir(&dir)?;
    let path = seen_path(root, name)?;
    let staged = dir.join(format!(".{}.{}", ref_file(name), random_nonce()?));
    private_file(
        &staged,
        &serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?,
    )?;
    fs::rename(&staged, &path).map_err(|error| format!("cannot retain {}: {error}", path.display()))
}

fn text_argument(action: &Value) -> Result<String> {
    let text = member(action, "text")?;
    if text.is_empty() || text.len() > 4096 {
        return Err("document text must be 1..4096 bytes".into());
    }
    Ok(hex(text.as_bytes()))
}

fn line_argument(action: &Value) -> Result<usize> {
    let line = member(action, "line")?;
    decimal(line, "document line")?;
    line.parse::<usize>()
        .ok()
        .filter(|value| *value >= 1)
        .ok_or_else(|| "document line must be 1 or more".to_owned())
}

/// Lower line-level document actions into the Host's content grammar.
/// `append {text}` · `edit {line,text}` · `link {to,relation}`.
fn document_actions(
    root: &Path,
    workspace: &Value,
    name: &str,
    view: &Value,
    fresh: bool,
    actions: &Value,
) -> Result<Value> {
    let actions = actions
        .as_array()
        .ok_or("document actions must be an array")?;
    if actions.is_empty() || actions.len() > 16 {
        return Err("document proposal requires 1..16 actions".into());
    }
    content_page(view, name)?;
    let mut lowered = Vec::new();
    for action in actions {
        let obj = action
            .as_object()
            .ok_or("document action must be an object")?;
        let keys: &[&str] = match member(action, "type")? {
            "append" => &["type", "text"],
            "edit" => &["type", "line", "text"],
            "link" => &["type", "to", "relation"],
            "annotate" => &["type", "line", "text"],
            "push" => &["type", "bytes"],
            _ => return Err("document action must be append, edit, annotate, link or push".into()),
        };
        if obj.len() != keys.len() || keys.iter().any(|key| !obj.contains_key(*key)) {
            return Err(format!("document action {} has unexpected fields", member(action, "type")?));
        }
        if member(action, "type")? == "push" {
            let seen = seen_for(root, workspace, name, view, fresh, "a push is a diff against your last read")?;
            let file = crate::decode_hex(member(action, "bytes")?)?;
            lowered.extend(push_actions(&seen, &file)?.actions);
            continue;
        }
        lowered.push(match member(action, "type")? {
            // A created atom joins the end of the document's root (K-ELEMENT-TREE).
            "append" => json!({"type":"createAtom","atom":random_nonce()?,
                "kind":{"type":"text"},"payload":text_argument(action)?}),
            "edit" => {
                let line = line_argument(action)?;
                let seen = seen_for(root, workspace, name, view, fresh, "an edit names a line as you last read it")?;
                let seen_page = content_page(&seen["view"], name)?;
                // Line N is the Nth line of the kernel's order as `doc show`
                // numbered it (`live_lines`), never an order of atom ids.
                let lines = live_lines(&seen["document"]).map_err(|_| {
                    format!("doc show {name} first: an edit names a line as you last read it")
                })?;
                let line_entry = lines.get(line - 1).ok_or_else(|| {
                    format!("{name} had {} line(s) when you last read it", lines.len())
                })?;
                if line_entry["kind"] != "atom" {
                    return Err(format!("line {line} of {name} is a transclusion; edit its source"));
                }
                let element = member(line_entry, "element")?;
                let atom = page_entries(seen_page)?
                    .iter()
                    .find(|entry| entry["type"] == "atom" && entry["id"].as_str() == Some(element))
                    .ok_or_else(|| format!("line {line} of {name} names no atom of the page you read"))?;
                let before = atom_record(atom)?;
                json!({"type":"editAtom","atom":member(atom,"id")?,"before":before,
                    "kind":before["kind"],"payload":text_argument(action)?,"tombstone":false})
            }
            "annotate" => {
                let line = line_argument(action)?;
                let seen = seen_for(root, workspace, name, view, fresh, "an annotation names a line as you last read it")?;
                let lines = live_lines(&seen["document"])?;
                let line_entry = lines.get(line - 1).ok_or_else(|| {
                    format!("{name} had {} line(s) when you last read it", lines.len())
                })?;
                if line_entry["kind"] != "atom" {
                    return Err(format!("line {line} of {name} is a transclusion; annotate its source"));
                }
                let atom = member(line_entry, "atom")?;
                let record = page_entries(content_page(&seen["view"], name)?)?
                    .iter()
                    .find(|entry| entry["type"] == "atom" && entry["id"].as_str() == Some(atom))
                    .ok_or_else(|| format!("line {line} of {name} names no atom of the page you read"))?;
                json!({"type":"annotate","annotation":random_nonce()?,"atom":atom,
                    "revision":member(record,"revision")?,"body":text_argument(action)?})
            }
            "link" => {
                let to = member(action, "to")?;
                let relation = member(action, "relation")?;
                decimal(relation, "link relation")?;
                // The link names what the target IS, read from a signed view
                // of it now (which also shows this workspace may observe it):
                // a document is a `document` target, any other resource a
                // `mini:KIND/ID` link.
                let target_ref = reference(root, to)?;
                let (target_view, _, _) = signed_view(root, workspace, &target_ref, "resource")?;
                let cell = target_view.get("cell").ok_or("signed resource view lacks cell")?;
                let id = member(&target_ref, "target")?;
                let target = match cell_storage(cell)? {
                    "content" => json!({"type":"document","id":id}),
                    _ => resource_link_target(member(&target_ref, "kind")?, id),
                };
                json!({"type":"link","link":random_nonce()?,"source":null,
                    "target":target,"relation":relation})
            }
            _ => unreachable!("document action tags were checked"),
        });
    }
    Ok(Value::Array(lowered))
}

/// Local names for one target. Names are hints; every use is independently authorized.
pub(crate) fn names_for_target(root: &Path, document: &str) -> Vec<String> {
    let mut names = Vec::new();
    if let Ok(entries) = fs::read_dir(root.join("refs")) {
        for entry in entries.flatten() {
            let file = entry.file_name().to_string_lossy().into_owned();
            if let Some(stem) = file.strip_suffix(".json") {
                let name = ref_name_of_file(stem);
                if let Ok(value) = reference(root, &name) {
                    if value.get("target").and_then(Value::as_str) == Some(document) { names.push(name); }
                }
            }
        }
    }
    names.sort();
    names
}

// `doc pull` / `doc push`: a friend writes in their own editor and the kernel
// still judges per line (P-DOC-WRITE), over the element tree (K-ELEMENT-TREE).
//
// The file is the document's LIVE lines in the kernel's order (`live_lines` of
// the retained `view-document`, the numbering `doc show` prints): a text atom's
// payload bytes, or, for a transclusion, the marker `⟦transclusion ID⟧`; each
// followed by one `\n`. A file's line N is the Nth live line, which is how a
// refusal names it. Reading a file back, one final `\n` ends the last line and
// is not content; every other byte is content, so trailing spaces, `\r` and
// blank lines are lines exactly as written.
//
// `doc push` diffs the file against `seen/NAME.json` (the last pull or show)
// with the Wagner–Fischer edit-distance recurrence over whole lines. An
// unchanged line is no action; a changed line is one `editAtom` pinned to the
// record as the pull saw it; a deleted line is one `editAtom` with `tombstone:
// true` (a transclusion: one `editElement remove`); a new line is one
// `createAtom` (which appends it to the root) and, unless it ends the document,
// the `editElement` that places it before the line it precedes: a `move` in the
// root, or a `remove` from the root and a `splice` into a section. Each edit
// names the revision of its container as the pull read it, so a container whose
// children moved since is refused `staleElement`. There is no identifier to mint
// between two neighbours (K-DOC-ORDER): a thousand inserts at one place cost a
// thousand placements, never a renumbering. The actions go in ONE content
// command, which the kernel folds all-or-nothing: a stale edit refuses the whole
// push and nothing of it lands.

/// The most a pushed file may hold, and the most lines either side of a diff.
const PUSH_MAX_BYTES: usize = 64 * 1024;
const PUSH_MAX_LINES: usize = 2048;
/// A content proposal carries at most this many actions (`content_actions`).
const PUSH_MAX_ACTIONS: usize = 64;
const LINE_MAX_BYTES: usize = 4096;
const SEEN_TYPE: &str = "minidregg-workspace-seen-document-v2";

/// The line a pulled file carries for a transclusion: it may be kept, moved
/// away (a strike), never edited.
fn transclusion_marker(id: &str) -> Vec<u8> {
    format!("⟦transclusion {id}⟧").into_bytes()
}

/// The retained "as I last read it" record of one document: the host page, the
/// kernel's `view-document` of it, and the read's height and world root.
fn seen_value(name: &str, view: &Value, document: &Value, challenge: &Value) -> Value {
    json!({"type":SEEN_TYPE,"name":name,
        "height":challenge.get("height"),"worldRoot":challenge.get("worldRoot"),
        "view":view,"document":document})
}

/// Local edit-session snapshot: ciphertext guards and opened diff text live
/// in distinct fields. Only raw atom records are ever sent back to the Host.
fn seen_read_value(name: &str, read: &DocumentRead, challenge: &Value) -> Value {
    let mut seen = seen_value(name, &read.view, &read.document, challenge);
    seen["openedEntries"] = json!(read.entries);
    seen
}

/// A retained read holds the whole page and its view-document: it grows with the
/// document (a hundred-line document's is past 256 KiB), so it has its own bound.
const MAX_SEEN: u64 = 16 * 1024 * 1024;

fn read_seen(root: &Path, name: &str, why: &str) -> Result<Value> {
    let path = seen_path(root, name)?;
    if !path.exists() {
        return Err(format!("doc show {name} (or doc pull {name}) first: {why}"));
    }
    let seen = bounded_json_limit(&path, MAX_SEEN)?;
    if seen.get("type").and_then(Value::as_str) != Some(SEEN_TYPE) {
        return Err(format!("doc pull {name} again: the retained read predates the element tree"));
    }
    Ok(seen)
}

/// The read a document action names its lines against: the retained one, or,
/// `fresh`, this proposal's own signed read in the kernel's order.
fn seen_for(root: &Path, workspace: &Value, name: &str, view: &Value, fresh: bool, why: &str) -> Result<Value> {
    if fresh {
        let document = host_document(root, workspace, &reference(root, name)?)?;
        let mut seen = seen_value(name, view, &document, &Value::Null);
        seen["openedEntries"] = json!(opened_entries(root, workspace, &reference(root, name)?, view)?);
        Ok(seen)
    } else {
        read_seen(root, name, why)
    }
}

/// One live line of a retained read: its order row, its atom record (a text
/// line) and the bytes a file holds for it.
struct PulledLine<'a> {
    row: &'a Value,
    atom: Option<&'a Value>,
    bytes: Vec<u8>,
}

fn pulled_lines(seen: &Value) -> Result<Vec<PulledLine<'_>>> {
    let name = member(seen, "name")?;
    let entries = page_entries(content_page(&seen["view"], name)?)?;
    let mut lines = Vec::new();
    for (index, row) in live_lines(&seen["document"])?.into_iter().enumerate() {
        let line = index + 1;
        lines.push(match row["kind"].as_str() {
            Some("embed") => PulledLine { row, atom: None, bytes: transclusion_marker(member(row, "transclusion")?) },
            _ => {
                let id = member(row, "atom")?;
                let atom = entries
                    .iter()
                    .find(|entry| entry["type"] == "atom" && entry["id"].as_str() == Some(id))
                    .ok_or_else(|| format!("line {line} names atom {id}, which the page you read does not hold"))?;
                let opened = seen.get("openedEntries").and_then(Value::as_array)
                    .and_then(|all| all.iter().find(|entry| entry["type"] == "atom" && entry["id"].as_str() == Some(id)))
                    .unwrap_or(atom);
                let bytes = match private::opened_text(opened)? {
                    Some(bytes) => bytes,
                    None if atom.get("kind") == Some(&json!({"type":"text"})) =>
                        crate::decode_hex(member(atom, "payload")?)?,
                    None => return Err(format!("line {line} is not a text atom; a file cannot carry it")),
                };
                if bytes.contains(&b'\n') {
                    return Err(format!("line {line} holds a newline; a file cannot carry it as one line"));
                }
                PulledLine { row, atom: Some(atom), bytes }
            }
        });
    }
    Ok(lines)
}

/// The file `doc pull` prints for a retained read.
fn pull_text(seen: &Value) -> Result<Vec<u8>> {
    let mut out = Vec::new();
    for line in pulled_lines(seen)? {
        out.extend(line.bytes);
        out.push(b'\n');
    }
    Ok(out)
}

/// A file's lines: split at `\n`, the one final `\n` ending the last line.
fn file_lines(bytes: &[u8]) -> Vec<&[u8]> {
    if bytes.is_empty() {
        return Vec::new();
    }
    let body = bytes.strip_suffix(b"\n").unwrap_or(bytes);
    body.split(|byte| *byte == b'\n').collect()
}

/// A file as `doc pull` would print its lines (one final `\n` per line).
fn normalized_file(bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::new();
    for line in file_lines(bytes) {
        out.extend_from_slice(line);
        out.push(b'\n');
    }
    out
}

/// A signed read of NAME, its `view-document`, retained as `seen/NAME.json`.
fn doc_read(root: &Path, workspace: &Value, name: &str) -> Result<Value> {
    let read = rendered_document(root, workspace, name, None, None)?;
    content_page(&read.view, name)?;
    let challenge = bounded_json(&read.attempt.join("challenge.json")).unwrap_or(Value::Null);
    let seen = seen_read_value(name, &read, &challenge);
    retain_seen_value(root, name, &seen)?;
    Ok(seen)
}

fn doc_pull(root: &Path, workspace: &Value, name: &str) -> Result<()> {
    let seen = doc_read(root, workspace, name)?;
    let text = pull_text(&seen)?;
    let mut out = std::io::stdout().lock();
    out.write_all(&text)
        .and_then(|()| out.flush())
        .map_err(|error| format!("cannot write the pulled document: {error}"))
}

/// One step of a line diff. Indices are 0-based into the old (pulled) and new
/// (file) line lists.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LineOp {
    Keep(usize, usize),
    Edit(usize, usize),
    Insert(usize),
    Strike(usize),
}

/// The minimal line diff: Wagner–Fischer (1974) edit distance over lines,
/// O(N·M). Ties are traced back (from the end) preferring keep, then insert,
/// then strike, then edit, so an edit pairs a changed line with the earliest
/// position it can: "a b" → "a B c" edits b and adds c.
fn line_diff(old: &[&[u8]], new: &[&[u8]]) -> Result<Vec<LineOp>> {
    if old.len() > PUSH_MAX_LINES || new.len() > PUSH_MAX_LINES {
        return Err(format!("doc push diffs at most {PUSH_MAX_LINES} lines a side"));
    }
    let (n, m) = (old.len(), new.len());
    let width = m + 1;
    let mut d = vec![0u32; (n + 1) * width];
    for i in 0..=n {
        for j in 0..=m {
            d[i * width + j] = if i == 0 {
                j as u32
            } else if j == 0 {
                i as u32
            } else {
                let substitute = d[(i - 1) * width + j - 1] + u32::from(old[i - 1] != new[j - 1]);
                substitute
                    .min(d[(i - 1) * width + j] + 1)
                    .min(d[i * width + j - 1] + 1)
            };
        }
    }
    let mut ops = Vec::new();
    let (mut i, mut j) = (n, m);
    while i > 0 || j > 0 {
        let here = d[i * width + j];
        if i > 0 && j > 0 && old[i - 1] == new[j - 1] && here == d[(i - 1) * width + j - 1] {
            ops.push(LineOp::Keep(i - 1, j - 1));
            i -= 1;
            j -= 1;
        } else if j > 0 && here == d[i * width + j - 1] + 1 {
            ops.push(LineOp::Insert(j - 1));
            j -= 1;
        } else if i > 0 && here == d[(i - 1) * width + j] + 1 {
            ops.push(LineOp::Strike(i - 1));
            i -= 1;
        } else {
            ops.push(LineOp::Edit(i - 1, j - 1));
            i -= 1;
            j -= 1;
        }
    }
    ops.reverse();
    Ok(ops)
}

/// The element tree as the pull read it, kept current while a push's actions
/// are planned: each container's children, each element's parent, and the
/// revision each container's edits name (the one the pull read; a container
/// this push already moved is current for it, `openContainer`).
struct TreeModel {
    root: String,
    children: std::collections::BTreeMap<String, Vec<String>>,
    parent: std::collections::BTreeMap<String, String>,
    revision: std::collections::BTreeMap<String, String>,
}

impl TreeModel {
    fn of(document: &Value) -> Result<Self> {
        let root = member(document, "root")?.to_owned();
        let mut model = TreeModel {
            root: root.clone(),
            children: std::collections::BTreeMap::from([(root.clone(), Vec::new())]),
            parent: std::collections::BTreeMap::new(),
            revision: std::collections::BTreeMap::from([(root, member(document, "rootRevision")?.to_owned())]),
        };
        for row in document["order"].as_array().ok_or("document view has no order")? {
            let element = member(row, "element")?.to_owned();
            let parent = member(row, "parent")?.to_owned();
            model.children.entry(parent.clone()).or_default().push(element.clone());
            model.parent.insert(element.clone(), parent);
            if row["kind"] == "container" {
                model.children.entry(element.clone()).or_default();
                model.revision.insert(element, member(row, "revision")?.to_owned());
            }
        }
        Ok(model)
    }

    fn edit(&self, container: &str, op: Value) -> Result<Value> {
        let revision = self.revision.get(container).ok_or("a container the pull did not read")?;
        Ok(edit_element(container, revision, op))
    }

    fn index_of(&self, container: &str, element: &str) -> Result<usize> {
        self.children
            .get(container)
            .and_then(|children| children.iter().position(|child| child == element))
            .ok_or_else(|| "an element is not among its container's children".to_owned())
    }

    /// `createAtom LEAF` (appended to the root), then the edits that put it
    /// immediately before BEFORE; none when it ends the document.
    fn insert(&mut self, leaf: &str, before: Option<&str>) -> Result<Vec<Value>> {
        let root = self.root.clone();
        self.children.get_mut(&root).ok_or("the root has no children list")?.push(leaf.to_owned());
        self.parent.insert(leaf.to_owned(), root.clone());
        let Some(before) = before else {
            return Ok(Vec::new());
        };
        let container = self.parent.get(before).ok_or("a line has no container")?.clone();
        if container == root {
            let children = self.children.get_mut(&root).ok_or("the root has no children list")?;
            children.retain(|child| child != leaf);
            let index = children.iter().position(|child| child == before).ok_or("a line left the root")?;
            children.insert(index, leaf.to_owned());
            Ok(vec![self.edit(&root, json!({"type":"move","child":leaf,"index":index.to_string()}))?])
        } else {
            let remove = self.edit(&root, json!({"type":"remove","child":leaf}))?;
            self.children.get_mut(&root).ok_or("the root has no children list")?.retain(|child| child != leaf);
            let index = self.index_of(&container, before)?;
            let splice = self.edit(&container, json!({"type":"splice","index":index.to_string(),"child":leaf}))?;
            self.children.get_mut(&container).ok_or("a container has no children list")?.insert(index, leaf.to_owned());
            self.parent.insert(leaf.to_owned(), container);
            Ok(vec![remove, splice])
        }
    }

    /// `editElement remove`: ELEMENT leaves the order (its record stays stored).
    fn remove(&mut self, element: &str) -> Result<Value> {
        let container = self.parent.remove(element).ok_or("a line has no container")?;
        let edit = self.edit(&container, json!({"type":"remove","child":element}))?;
        self.children.get_mut(&container).ok_or("a container has no children list")?.retain(|child| child != element);
        Ok(edit)
    }
}

/// What a push of `file` against a retained seen record submits.
struct PushPlan {
    actions: Vec<Value>,
    edits: usize,
    inserts: usize,
    strikes: usize,
    /// The pulled lines an action pins (edit or strike): (file line, atom id).
    pinned: Vec<(usize, String)>,
    pulled_at: String,
}

fn push_actions(seen: &Value, file: &[u8]) -> Result<PushPlan> {
    let pulled_at = seen.get("height").and_then(Value::as_str).unwrap_or("?").to_owned();
    if file.len() > PUSH_MAX_BYTES {
        return Err(format!("doc push takes a file of at most {PUSH_MAX_BYTES} bytes"));
    }
    let lines = pulled_lines(seen)?;
    let old: Vec<&[u8]> = lines.iter().map(|line| line.bytes.as_slice()).collect();
    let new = file_lines(file);
    if let Some(index) = new.iter().position(|line| line.len() > LINE_MAX_BYTES) {
        return Err(format!("line {} is longer than {LINE_MAX_BYTES} bytes", index + 1));
    }
    let markers: Vec<&[u8]> = lines.iter().filter(|line| line.atom.is_none()).map(|line| line.bytes.as_slice()).collect();
    let ops = line_diff(&old, &new)?;
    let mut model = TreeModel::of(&seen["document"])?;
    let mut plan = PushPlan { actions: Vec::new(), edits: 0, inserts: 0, strikes: 0, pinned: Vec::new(), pulled_at };
    for (position, op) in ops.iter().enumerate() {
        match *op {
            LineOp::Keep(..) => {}
            LineOp::Edit(o, n) => {
                let Some(atom) = lines[o].atom else {
                    return Err(format!("line {} is a transclusion; a file cannot edit it (doc follow, doc move)", o + 1));
                };
                let before = atom_record(atom)?;
                plan.actions.push(json!({"type":"editAtom","atom":member(atom,"id")?,
                    "before":before,"kind":before["kind"],"payload":hex(new[n]),"tombstone":false}));
                plan.pinned.push((o + 1, member(atom, "id")?.to_owned()));
                plan.edits += 1;
            }
            LineOp::Strike(o) => match lines[o].atom {
                Some(atom) => {
                    let before = atom_record(atom)?;
                    plan.actions.push(json!({"type":"editAtom","atom":member(atom,"id")?,
                        "before":before,"kind":before["kind"],"payload":before["payload"],"tombstone":true}));
                    plan.pinned.push((o + 1, member(atom, "id")?.to_owned()));
                    plan.strikes += 1;
                }
                None => {
                    plan.actions.push(model.remove(member(lines[o].row, "element")?)?);
                    plan.strikes += 1;
                }
            },
            LineOp::Insert(n) => {
                if markers.contains(&new[n]) {
                    return Err(format!(
                        "line {} names a transclusion where the pull did not have it; move it with doc move",
                        n + 1
                    ));
                }
                // Before the next pulled line the diff keeps, edits or strikes;
                // after the last one, the insert ends the document.
                let next = ops[position + 1..].iter().find_map(|op| match *op {
                    LineOp::Keep(o, _) | LineOp::Edit(o, _) | LineOp::Strike(o) => Some(o),
                    LineOp::Insert(_) => None,
                });
                let before = next.map(|o| member(lines[o].row, "element")).transpose()?;
                let leaf = random_nonce()?;
                plan.actions.push(json!({"type":"createAtom","atom":leaf,"kind":{"type":"text"},"payload":hex(new[n])}));
                plan.actions.extend(model.insert(&leaf, before)?);
                plan.inserts += 1;
            }
        }
    }
    if plan.actions.len() > PUSH_MAX_ACTIONS {
        return Err(format!(
            "this push is {} actions; one proposal carries at most {PUSH_MAX_ACTIONS} (push in parts, pulling between)",
            plan.actions.len()
        ));
    }
    Ok(plan)
}

/// After a refused push: which of the lines it pinned changed since the pull,
/// read again now (the retained seen record is left as it was).
fn stale_lines(root: &Path, workspace: &Value, name: &str, seen: &Value, plan: &PushPlan) -> Result<Option<String>> {
    let reference = reference(root, name)?;
    let (view, challenge, _) = signed_view(root, workspace, &reference, "resource")?;
    let now = member(&challenge, "height")?.to_owned();
    let atom_of = |entries: &[Value], id: &str| -> Option<Value> {
        entries.iter().find(|entry| entry["type"] == "atom" && entry["id"].as_str() == Some(id)).cloned()
    };
    let was_entries = page_entries(content_page(&seen["view"], name)?)?.clone();
    let now_entries = page_entries(content_page(&view, name)?)?.clone();
    let displayed = opened_entries(root, workspace, &reference, &view)?;
    let mut changed = Vec::new();
    for (line, id) in &plan.pinned {
        let was = atom_of(&was_entries, id).ok_or("a pinned line is missing from the seen record")?;
        let how = match atom_of(&now_entries, id) {
            None => "is gone".to_owned(),
            Some(atom) if atom_record(&atom)? == atom_record(&was)? => continue,
            Some(atom) if atom.get("tombstonedAt").is_some_and(|value| !value.is_null()) => "was struck".to_owned(),
            Some(atom) => {
                let opened = atom_of(&displayed, id).unwrap_or_else(|| atom.clone());
                let bytes = match private::opened_text(&opened) {
                    Ok(Some(bytes)) => bytes,
                    Ok(None) => crate::decode_hex(atom["payload"].as_str().unwrap_or("")).unwrap_or_default(),
                    Err(_) => { changed.push(format!("line {line} changed (private text unavailable)")); continue; }
                };
                let mut text = String::from_utf8_lossy(&bytes).into_owned();
                if text.chars().count() > 60 {
                    text = text.chars().take(57).collect::<String>() + "...";
                }
                format!("changed (now {text:?})")
            }
        };
        changed.push(format!("line {line} {how}"));
    }
    if changed.is_empty() {
        return Ok(None);
    }
    Ok(Some(format!(
        "{} since you pulled {name} at {} (read again at {now}; the store records who created a line, not who edited it); nothing of this push landed: doc pull {name}, merge, push again",
        changed.join(", "),
        plan.pulled_at
    )))
}

fn doc_push(root: &Path, workspace: &Value, name: &str, file: &Path, proposal_id: &str, attempt: &Path) -> Result<()> {
    validate_name(proposal_id)?;
    let seen = read_seen(root, name, "a push is a diff against your last read")?;
    let mut bytes = Vec::new();
    let limit = PUSH_MAX_BYTES as u64 + 1;
    if file == Path::new("-") {
        std::io::stdin().lock().take(limit).read_to_end(&mut bytes)
    } else {
        File::open(file).and_then(|handle| handle.take(limit).read_to_end(&mut bytes))
    }
    .map_err(|error| format!("cannot read {}: {error}", file.display()))?;
    let plan = push_actions(&seen, &bytes)?;
    if plan.actions.is_empty() {
        println!("doc push {name}: the file matches your pull at height {}; nothing submitted", plan.pulled_at);
        return Ok(());
    }
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":name,"payload":{"type":"document",
            "actions":[{"type":"push","bytes":hex(&bytes)}]}}]});
    propose_request(root, workspace, &request, proposal_id, None, false)?;
    println!(
        "doc push {name}: proposal {proposal_id}: {} action(s) against your pull at height {}: {} edit(s), {} new line(s), {} struck",
        plan.actions.len(),
        plan.pulled_at,
        plan.edits,
        plan.inserts,
        plan.strikes
    );
    let intent = root.join("proposals").join(proposal_id).join("intent.json");
    if let Err(refused) = submit_intent(root, workspace, &intent, "intent", false, Some(attempt)) {
        let Some(decision) = crate::take_host_decision() else {
            return Err(refused);
        };
        let stale = stale_lines(root, workspace, name, &seen, &plan);
        crate::note_host_decision(decision);
        return match stale {
            Ok(Some(lines)) => {
                crate::note_line_refusal(lines.clone());
                Err(format!("{lines}; {refused}"))
            }
            Ok(None) => Err(refused),
            Err(why) => Err(format!("{refused}; and the read after it failed: {why}")),
        };
    }
    // Admitted. When the document now reads exactly as the file, that read is
    // the new seen record; otherwise someone else changed it too, and the old
    // record is retired so a second push cannot re-create these lines.
    let now = doc_read(root, workspace, name)?;
    let height = now.get("height").and_then(Value::as_str).unwrap_or("?").to_owned();
    if pull_text(&now).ok().as_deref() == Some(normalized_file(&bytes).as_slice()) {
        println!("doc push {name}: admitted; at height {height} the document reads exactly as your file");
    } else {
        let retired = root.join("seen").join(format!(".{}.pushed.{}", ref_file(name), random_nonce()?));
        fs::rename(seen_path(root, name)?, &retired).map_err(|error| format!("cannot retire the seen record: {error}"))?;
        println!("doc push {name}: admitted; at height {height} {name} also holds others' changes: doc pull {name} before your next push");
    }
    Ok(())
}

/// The child capability this workspace delegated on `name` to `recipient`,
/// from its own retained delegation proposals.
/// A law that admits nothing, on a ROOM cell (a reference this workspace
/// founded or joined as a room, or a chat room the shell names), freezes its
/// membership forever: every kick and invite is a request on that cell.
/// Refused unless the founder says `--freeze-roster`. A plain resource keeps
/// `--allow-unsatisfiable` alone (J8's deny-all).
fn sealing_a_room(root: &Path, workspace: &Value, name: &str, room_cell: bool) -> Result<()> {
    if !room_cell && reference(root, name)?.get("room").is_none() {
        return Ok(());
    }
    let me = member(workspace, "subject")?;
    let others: Vec<String> = match reference(root, name).and_then(|r| signed_view(root, workspace, &r, "who")) {
        Ok((who, _, _)) => who
            .get("members")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(|m| m.get("subject").and_then(Value::as_str))
            .filter(|subject| *subject != me)
            .map(str::to_owned)
            .collect(),
        Err(_) => Vec::new(),
    };
    let holders = if others.is_empty() { "no one yet".to_owned() } else { others.join(", ") };
    Err(format!(
        "{name} is a room (members now: {holders}): a law that admits nothing freezes its membership forever. \
         Every invite and every kick is a request on {name}, and this law refuses them all, so no one could \
         ever be added or removed while members keep the cells under it. To seal it anyway, repeat the line \
         with --freeze-roster."
    ))
}

/// A refusal on a sealed room cell, said as what it means: the room cell's law
/// is `sealed`, which refuses every request on it, kick and invite included.
pub(crate) fn frozen_roster(room: &str, error: String) -> String {
    if error.contains("law-denied") && error.contains("sealed") {
        format!(
            "this room's membership is frozen: {room}'s law is `sealed`, which refuses every request on the room cell, \
             so no one can be invited or kicked (sealing a room freezes its roster forever) [{error}]"
        )
    } else {
        error
    }
}

/// Every live grant `subject` holds anywhere in room `name` (on the room or
/// on a cell under it), as (capability, policy), by the Host's signed `who`
/// view: the founder's invite, a concierge's window, a grant on one cell under
/// the room, whoever issued it.
pub(crate) fn standing_grants(root: &Path, workspace: &Value, name: &str, subject: &str) -> Result<Vec<(String, String)>> {
    let reference = reference(root, name)?;
    let (who, _, _) = signed_view(root, workspace, &reference, "who").map_err(|error| frozen_roster(name, error))?;
    let mut held = Vec::new();
    for entry in who.get("holders").and_then(Value::as_array).into_iter().flatten() {
        if entry.get("subject").and_then(Value::as_str) == Some(subject) {
            for grant in entry.get("grants").and_then(Value::as_array).into_iter().flatten() {
                held.push((member(grant, "capability")?.to_owned(), member(grant, "policy")?.to_owned()));
            }
        }
    }
    Ok(held)
}

/// The reference through which this workspace revokes a grant whose policy is
/// `policy`: the room itself, or a cell under it whose control grant this
/// workspace holds (a cell it bore, such as a private room's keys cell).
fn controlling_reference(root: &Path, room: &str, room_target: &str, policy: &str) -> Result<String> {
    if policy == room_target {
        return Ok(room.to_owned());
    }
    let mut found = Vec::new();
    if let Ok(entries) = fs::read_dir(root.join("refs")) {
        for entry in entries.flatten() {
            let file = entry.file_name().to_string_lossy().into_owned();
            let Some(stem) = file.strip_suffix(".json") else { continue };
            let Ok(value) = bounded_json(&entry.path()) else { continue };
            if value.get("target").and_then(Value::as_str) == Some(policy)
                && value.get("controlCapability").and_then(Value::as_str).is_some()
            {
                found.push(ref_name_of_file(stem));
            }
        }
    }
    found.sort();
    found.into_iter().next().ok_or_else(|| {
        format!("a grant under {room} is governed by cell {policy}, whose control this workspace does not hold: its owner revokes it")
    })
}

/// `room kick`: one revoke proposal per standing grant `subject` holds under
/// room `name` (the founder's invite, a concierge's window, any other grant
/// under the room), enumerated from the Host's signed `who` view, never
/// guessed. The first is `proposal_id`; the rest `proposal_id-cN`, listed in
/// the first's `companions.json`, so `submit proposal_id` submits them all.
/// Each revoke names the authority root it was authored against, so a
/// companion is proposed only when its turn comes (after the one before it
/// landed), never ahead. `submit_now` proposes and submits each here, in turn
/// (the private-room kick rotates after).
pub(crate) fn room_kick(
    root: &Path,
    workspace: &Value,
    name: &str,
    subject: &str,
    proposal_id: &str,
    submit_now: bool,
) -> Result<Vec<String>> {
    validate_name(proposal_id)?;
    decimal(subject, "kicked member")?;
    if member(workspace, "subject")? == subject {
        return Err("you cannot kick yourself (room leave renounces your own grant)".into());
    }
    let held = standing_grants(root, workspace, name, subject)?;
    if held.is_empty() {
        return Err(format!("{subject} holds no live grant in {name}: there is nothing to kick"));
    }
    let room_target = member(&reference(root, name)?, "target")?.to_owned();
    // A grant whose policy this workspace controls is revoked here (the room,
    // or a cell under it this workspace bore). Any other is the member's own
    // (a doc it bore, its delegations): it carries a revoked grant among its
    // ancestors and falls with the kick, which `kick_remaining` confirms.
    let mut ids = Vec::new();
    let mut named = Vec::new();
    let mut falls = Vec::new();
    for (capability, policy) in &held {
        let via = match controlling_reference(root, name, &room_target, policy) {
            Ok(via) => via,
            Err(_) => {
                falls.push(json!({"capability":capability,"policy":policy}));
                continue;
            }
        };
        let id = if ids.is_empty() { proposal_id.to_owned() } else { format!("{proposal_id}-c{}", ids.len()) };
        validate_name(&id)?;
        named.push(json!({"capability":capability,"policy":policy,"via":via,"proposal":id}));
        let request = json!({"type":"minidregg-workspace-proposal-v1","action":"revoke",
            "name":via,"recipient":subject,"capability":capability});
        let source = root.join("sources").join(format!("kick-{id}.json"));
        let mut bytes = serde_json::to_vec_pretty(&request).map_err(|error| error.to_string())?;
        bytes.push(b'\n');
        private_file(&source, &bytes)?;
        let first = ids.is_empty();
        ids.push(id.clone());
        if !first && !submit_now {
            continue;
        }
        propose_summary(root, workspace, &source, &id, None, false).map_err(|error| frozen_roster(name, error))?;
        if submit_now {
            submit_intent(root, workspace, &root.join("proposals").join(&id).join("intent.json"), "intent", false,
                Some(&root.join("attempts").join(&id)))?;
        }
    }
    if ids.is_empty() {
        return Err(format!(
            "{subject} holds live grants in {name} ({}), none of them on a resource whose control this workspace holds",
            falls.iter().filter_map(|g| g["capability"].as_str()).collect::<Vec<_>>().join(", ")
        ));
    }
    if !submit_now {
        let companions = json!({"type":"minidregg-proposal-companions-v1","room":name,"member":subject,
            "proposals":&ids[1..]});
        private_file(
            &root.join("proposals").join(proposal_id).join("companions.json"),
            &serde_json::to_vec_pretty(&companions).map_err(|error| error.to_string())?,
        )?;
    }
    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-room-kick-v1","room":name,
        "member":subject,"capabilities":named,"fallsWithTheKick":falls,"proposals":ids,"submitted":submit_now,
        "note":if submit_now { "every grant the member held in the room is revoked" }
            else { "submit the first proposal: it submits every one of them, then checks the member holds nothing live in the room" }}))
        .map_err(|error| error.to_string())?);
    if submit_now {
        kick_remaining(root, workspace, name, subject)?;
    }
    Ok(ids)
}

/// After a kick: the member must hold no live grant anywhere in the room (the
/// Host's signed `who` view). A grant still standing is named, with whose it
/// is to revoke.
pub(crate) fn kick_remaining(root: &Path, workspace: &Value, name: &str, subject: &str) -> Result<()> {
    let left = standing_grants(root, workspace, name, subject)?;
    if left.is_empty() {
        eprintln!("kick: {subject} holds no live grant in {name}");
        return Ok(());
    }
    Err(format!(
        "the kick left {subject} holding live grants in {name}: {} (each is revoked by the holder of its policy's control grant)",
        left.iter().map(|(cap, policy)| format!("{cap} (policy {policy})")).collect::<Vec<_>>().join(", ")
    ))
}

fn delegated_capability(root: &Path, name: &str, target: &str, recipient: &str) -> Result<String> {
    let mut found = std::collections::BTreeSet::new();
    if let Ok(entries) = fs::read_dir(root.join("proposals")) {
        for entry in entries.flatten() {
            let Ok(summary) = bounded_json(&entry.path().join("proposal.json")) else {
                continue;
            };
            let delegation = &summary["delegation"];
            if delegation.get("name").and_then(Value::as_str) == Some(name)
                && delegation.get("target").and_then(Value::as_str) == Some(target)
                && delegation.get("recipient").and_then(Value::as_str) == Some(recipient)
            {
                found.insert(member(delegation, "childCapability")?.to_owned());
            }
        }
    }
    match found.len() {
        0 => Err(format!("this workspace delegated nothing on {name} to {recipient}")),
        1 => Ok(found.into_iter().next().expect("one element")),
        _ => Err(format!(
            "several delegations on {name} to {recipient} ({}); revoke is one capability",
            found.into_iter().collect::<Vec<_>>().join(", ")
        )),
    }
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = os_string(args.required("action")?, "workspace action")?;
    let root = absolute(&path(args.required("dir")?))?;
    if action == "init" {
        let host = args.optional("host").map(path);
        let config = path(args.required("config")?);
        let key = args.optional("key").map(path);
        let subject = args
            .optional("subject")
            .map(|value| os_string(value, "subject"))
            .transpose()?;
        let enrollment = args.optional("enrollment").map(path);
        let context = args.optional("birth-context").map(path);
        let namespace = args.optional("namespace-root").map(path);
        let next_public = args.optional("next-pub").map(path);
        let without_prerotation = args.optional("no-prerotation").is_some();
        let first_ref = args.optional("continuity-ref").map(|value| {
            serde_json::from_str::<Value>(&os_string(value, "continuity reference")?)
                .map_err(|error| error.to_string())
        }).transpose()?;
        let verifier = args.optional("verifier").map(path);
        if verifier.is_some() && first_ref.is_none() {
            return Err("init --verifier requires --continuity-ref".into());
        }
        args.finish()?;
        let identity = InitIdentity { key: key.as_deref(), subject: subject.as_deref(), enrollment: enrollment.as_deref(), next_public: next_public.as_deref(), without_prerotation };
        return match first_ref.as_ref() {
            Some(reference) => init_fresh(&root, host.as_deref(), &config, identity,
                context.as_deref(), namespace.as_deref(), reference, verifier.as_deref()),
            None => init(&root, host.as_deref(), &config, identity,
                context.as_deref(), namespace.as_deref()),
        };
    }
    let workspace = load(&root)?;
    match action.as_str() {
        "onboard" => {
            args.finish()?;
            print_json(&complete_fresh_onboarding(&root)?)
        }
        "continuity-init" => {
            let name = os_string(args.required("name")?, "reference name")?;
            let verifier = args.optional("verifier").map(path);
            args.finish()?;
            let reference = reference(&root, &name)?;
            let result = receipt_continuity::initialize(&root, &workspace, verifier.as_deref(), || {
                Ok(signed_view_unchecked(&root, &workspace, &reference, "resource")?.1)
            })?;
            print_json(&result)
        }
        "continuity-verifier" => {
            let verifier = path(args.required("verifier")?);
            args.finish()?;
            print_json(&receipt_continuity::replace_verifier(&root, &workspace, &verifier)?)
        }
        "continuity-check" => {
            let attempt = path(args.required("attempt")?);
            let historical = match args.optional("historical").as_deref() {
                None => false,
                Some(value) if value == OsStr::new("false") => false,
                Some(value) if value == OsStr::new("true") => true,
                _ => return Err("--historical must be true or false".into()),
            };
            args.finish()?;
            print_json(&receipt_continuity::check_retained(&root, &workspace, &attempt, historical)?)
        }
        "import" => {
            if let Some(from) = args.optional("from-ref") {
                let name = os_string(args.required("name")?, "reference name")?;
                args.finish()?;
                return import_delegated(&root, &workspace, &name, &path(from));
            }
            let name = os_string(args.required("name")?, "reference name")?;
            let kind = os_string(args.required("kind")?, "resource kind")?;
            let target = os_string(args.required("target")?, "resource target")?;
            let observe = os_string(args.required("observe-capability")?, "observe capability")?;
            let operation = args
                .optional("operation-capability")
                .map(|value| os_string(value, "operation capability"))
                .transpose()?;
            let control = args
                .optional("control-capability")
                .map(|value| os_string(value, "control capability"))
                .transpose()?;
            let provenance = args.optional("provenance").map(path);
            args.finish()?;
            import(
                &root,
                ImportInput {
                    name: &name,
                    kind: &kind,
                    target: &target,
                    observe: &observe,
                    operation: operation.as_deref(),
                    control: control.as_deref(),
                    provenance: provenance.as_deref(),
                    room: None,
                },
            )
        }
        "list" => {
            args.finish()?;
            list(&root)
        }
        "doc-backlinks" | "doc-links" => {
            let name = os_string(args.required("name")?, "reference name")?;
            args.finish()?;
            doc_link_view(
                &root,
                &workspace,
                &name,
                if action == "doc-backlinks" {
                    "backlinks"
                } else {
                    "links"
                },
            )
        }
        "describe" | "read" => {
            let name = os_string(args.required("name")?, "reference name")?;
            let room = args
                .optional("private")
                .map(|value| os_string(value, "private room"))
                .transpose()?;
            let ephemeral = match args.optional("ephemeral").as_deref() {
                None => false,
                Some(value) if value == OsStr::new("false") => false,
                Some(value) if value == OsStr::new("true") => true,
                _ => return Err("--ephemeral must be true or false".into()),
            };
            args.finish()?;
            if let Some(room) = room {
                if action == "describe" {
                    return Err("--private applies to read only".into());
                }
                return read_private(&root, &workspace, &name, &room);
            }
            // A cell born in a private room is read through its room's keys,
            // as `tail` does (AUDIT-ROOMS, client defect 2).
            if action == "read" {
                if let Some(room) = sealed_room(&root, &reference(&root, &name)?) {
                    return read_private(&root, &workspace, &name, &room);
                }
            }
            read(
                &root,
                &workspace,
                &name,
                if action == "describe" {
                    "policy"
                } else {
                    "resource"
                },
                None,
                ephemeral,
            )
        }
        // `who`: the room's members as the Host's who view lists them — the
        // subjects holding a standing capability that covers the room — read
        // with this workspace's own grant (so only a member may ask).
        "who" => {
            let name = os_string(args.required("name")?, "reference name")?;
            args.finish()?;
            read(&root, &workspace, &name, "who", None, false)
        }
        "tail" => {
            let name = os_string(args.required("name")?, "reference name")?;
            let start = os_string(args.required("from")?, "tail start")?;
            let count = os_string(args.required("count")?, "tail count")?;
            let room = args
                .optional("private")
                .map(|value| os_string(value, "private room"))
                .transpose()?;
            args.finish()?;
            let room = room.or_else(|| reference(&root, &name).ok().and_then(|r| sealed_room(&root, &r)));
            match room {
                Some(room) => roomkey::tail(&root, &workspace, &name, &start, &count, &room),
                None => read(&root, &workspace, &name, "tail", Some((&start, &count)), false),
            }
        }
        // The room-key protocol of a private room (`roomkey.rs`).
        "room-key" => {
            let op = os_string(args.required("op")?, "room-key op")?;
            let name = os_string(args.required("name")?, "room name")?;
            let flag = |args: &mut Args, key: &str| -> Result<bool> {
                match args.optional(key).as_deref() {
                    None => Ok(false),
                    Some(value) if value == OsStr::new("true") => Ok(true),
                    Some(value) if value == OsStr::new("false") => Ok(false),
                    _ => Err(format!("--{key} must be true or false")),
                }
            };
            match op.as_str() {
                "found" => {
                    args.finish()?;
                    roomkey::found(&root, &workspace, &name)
                }
                "sync" => {
                    args.finish()?;
                    let synced = roomkey::sync(&root, &workspace, &name)?;
                    println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-room-sync-v1",
                        "room":name,"epoch":synced.epoch(),"learned":synced.learned,
                        "held":synced.ring.epochs(&synced.room)})).map_err(|e| e.to_string())?);
                    Ok(())
                }
                "invite" => {
                    let member_subject = os_string(args.required("member")?, "invitee")?;
                    let enc = os_string(args.required("enc-pub")?, "invitee encryption key")?;
                    let proposal_id = os_string(args.required("proposal-id")?, "proposal ID")?;
                    let request = args.optional("request").map(path);
                    let past = flag(&mut args, "past")?;
                    let i_know = flag(&mut args, "i-know")?;
                    args.finish()?;
                    roomkey::check_invitee(&member_subject, i_know)?;
                    // The grant: K-ROOM's delegation proposal, spelled by the
                    // caller and proposed here (submit and publish as ever).
                    if let Some(request) = &request {
                        let value = roomkey::request(&request)?;
                        if member(&value, "action")? != "delegate"
                            || member(&value, "name")? != name
                            || member(&value, "recipient")? != member_subject
                        {
                            return Err("the invite request must delegate this room to this invitee".into());
                        }
                    }
                    // The keys write (and, for a new member, the keys grant) lands
                    // first: a delegation proposed before it would carry a stale
                    // authority root.
                    roomkey::invite(&root, &workspace, &name, &member_subject, &enc, past, i_know,
                        &format!("{proposal_id}-keys"))?;
                    if let Some(request) = request {
                        propose(&root, &workspace, &request, &proposal_id, None)?;
                    }
                    Ok(())
                }
                "rotate" => {
                    let proposal_id = os_string(args.required("proposal-id")?, "proposal ID")?;
                    let drop = args
                        .optional("drop")
                        .map(|value| os_string(value, "dropped member"))
                        .transpose()?;
                    args.finish()?;
                    roomkey::rotate(&root, &workspace, &name, drop.as_deref(), &proposal_id)
                }
                "kick" => {
                    let subject = os_string(args.required("member")?, "kicked member")?;
                    let proposal_id = os_string(args.required("proposal-id")?, "proposal ID")?;
                    args.finish()?;
                    roomkey::kick(&root, &workspace, &name, &subject, &proposal_id)
                }
                "list" => {
                    args.finish()?;
                    roomkey::list(&root, &name)
                }
                "open" => {
                    let stream = os_string(args.required("stream")?, "stream cell")?;
                    let sequence = os_string(args.required("sequence")?, "sequence")?;
                    let payload = os_string(args.required("payload")?, "payload hex")?;
                    args.finish()?;
                    roomkey::open_local(&root, &name, &stream, &sequence, &payload)
                }
                "forget" => {
                    let epoch = args
                        .optional("epoch")
                        .map(|value| {
                            os_string(value, "epoch")?
                                .parse::<u32>()
                                .map_err(|_| "--epoch is a decimal epoch".to_owned())
                        })
                        .transpose()?;
                    args.finish()?;
                    roomkey::forget(&root, &name, epoch)
                }
                "register" => {
                    let proposal_id = os_string(args.required("proposal-id")?, "proposal ID")?;
                    args.finish()?;
                    let epoch = crate::key_rotation::current_key_epoch(&root)?;
                    let done = roomkey::register(&root, &workspace, &name, &epoch, &proposal_id)?;
                    println!("{}", serde_json::to_string_pretty(&done).map_err(|e| e.to_string())?);
                    Ok(())
                }
                "rewrap" => {
                    let subject = os_string(args.required("member")?, "member")?;
                    let proposal_id = os_string(args.required("proposal-id")?, "proposal ID")?;
                    args.finish()?;
                    roomkey::rewrap(&root, &workspace, &name, &subject, &proposal_id)
                }
                _ => Err("room-key --op is found, sync, invite, rotate, kick, register, rewrap, list, open or forget".into()),
            }
        }
        "submit" => {
            let source = path(args.required("intent")?);
            let attempt = args.optional("attempt").map(path);
            let kind = args
                .optional("intent-kind")
                .map(|value| os_string(value, "intent kind"))
                .transpose()?
                .unwrap_or_else(|| "intent".into());
            let prepare_only = match args.optional("prepare-only").as_deref() {
                None => false,
                Some(value) if value == OsStr::new("false") => false,
                Some(value) if value == OsStr::new("true") => true,
                _ => return Err("--prepare-only must be true or false".into()),
            };
            args.finish()?;
            submit_intent(
                &root,
                &workspace,
                &source,
                &kind,
                prepare_only,
                attempt.as_deref(),
            )?;
            // A kick's companions (`room_kick`): every other grant the member
            // held in the room, each proposed now (against the authority root
            // the previous revoke left) and submitted, in turn.
            let companions = source.parent().map(|dir| dir.join("companions.json"));
            if let (false, Some(companions)) = (prepare_only, companions.filter(|path| path.exists())) {
                let listed = bounded_json(&companions)?;
                for id in listed.get("proposals").and_then(Value::as_array).into_iter().flatten() {
                    let id = id.as_str().ok_or("companion proposal id")?;
                    validate_name(id)?;
                    let attempt = root.join("attempts").join(id);
                    if attempt.exists() {
                        continue;
                    }
                    if !root.join("proposals").join(id).join("intent.json").exists() {
                        propose_summary(&root, &workspace, &root.join("sources").join(format!("kick-{id}.json")),
                            id, None, false)?;
                    }
                    submit_intent(&root, &workspace, &root.join("proposals").join(id).join("intent.json"),
                        "intent", false, Some(&attempt))?;
                }
                if let (Some(room), Some(kicked)) =
                    (listed.get("room").and_then(Value::as_str), listed.get("member").and_then(Value::as_str))
                {
                    kick_remaining(&root, &workspace, room, kicked)?;
                }
            }
            Ok(())
        }
        "room-kick" => {
            let name = os_string(args.required("name")?, "room name")?;
            let subject = os_string(args.required("member")?, "kicked member")?;
            let proposal_id = os_string(args.required("proposal-id")?, "proposal ID")?;
            args.finish()?;
            room_kick(&root, &workspace, &name, &subject, &proposal_id, false).map(|_| ())
        }
        "transclude" => {
            let host = os_string(args.required("name")?, "host name")?;
            let source = os_string(args.required("source")?, "source name")?;
            // The source's range: its atom ids (`--from --to`), or its live line
            // numbers as `doc show SOURCE` prints them (`--from-line --to-line`).
            let lines = match (args.optional("from-line"), args.optional("to-line")) {
                (Some(from), Some(to)) => Some((line_number(from, "--from-line")?, line_number(to, "--to-line")?)),
                (None, None) => None,
                _ => return Err("--from-line and --to-line go together".into()),
            };
            let (from, to) = match lines {
                Some((from, to)) => source_line_atoms(&root, &workspace, &source, from, to)?,
                None => (
                    os_string(args.required("from")?, "first atom")?,
                    os_string(args.required("to")?, "last atom")?,
                ),
            };
            let live = match args.optional("mode").as_deref() {
                None => false,
                Some(value) if value == OsStr::new("snapshot") => false,
                Some(value) if value == OsStr::new("live") => true,
                _ => return Err("--mode must be snapshot or live".into()),
            };
            let death = match args.optional("death") {
                Some(value) => os_string(value, "death policy")?,
                None => "keepTombstone".to_owned(),
            };
            let at = args.optional("at").map(|value| line_number(value, "--at")).transpose()?;
            args.finish()?;
            transclude(&root, &workspace, &host, &source, &from, &to, live, &death, at)
        }
        "doc-show" => {
            let name = os_string(args.required("name")?, "document name")?;
            let at = args
                .optional("at")
                .map(|value| os_string(value, "height"))
                .transpose()?;
            let format = show_format(args.optional("format"))?;
            args.finish()?;
            doc_show(&root, &workspace, &name, at.as_deref(), format)
        }
        "doc-outline" => {
            let name = os_string(args.required("name")?, "document name")?;
            let format = show_format(args.optional("format"))?;
            if !matches!(format, ShowFormat::Text | ShowFormat::Json) {
                return Err("doc-outline --format must be text or json".into());
            }
            args.finish()?;
            doc_outline(&root, &workspace, &name, format == ShowFormat::Json)
        }
        "doc-insert" => {
            let name = os_string(args.required("name")?, "document name")?;
            let text = os_string(args.required("text")?, "line text")?;
            let at = args.optional("at").map(|value| line_number(value, "--at")).transpose()?;
            args.finish()?;
            doc_insert(&root, &workspace, &name, &text, at)
        }
        "doc-move" => {
            let name = os_string(args.required("name")?, "document name")?;
            let from = line_number(args.required("from")?, "--from")?;
            let to = line_number(args.required("to")?, "--to")?;
            args.finish()?;
            doc_move(&root, &workspace, &name, from, to)
        }
        "mark" => {
            let name = os_string(args.required("name")?, "document name")?;
            let line = line_number(args.required("line")?, "--line")?;
            let kind = os_string(args.required("kind")?, "mark kind")?;
            let to = args.optional("to").map(|value| os_string(value, "link target name")).transpose()?;
            args.finish()?;
            doc_mark(&root, &workspace, &name, line, &kind, to.as_deref())
        }
        "unmark" => {
            let name = os_string(args.required("name")?, "document name")?;
            let mark = args.optional("mark").map(|value| os_string(value, "mark")).transpose()?;
            let line = args.optional("line").map(|value| line_number(value, "--line")).transpose()?;
            let kind = args.optional("kind").map(|value| os_string(value, "mark kind")).transpose()?;
            args.finish()?;
            doc_unmark(&root, &workspace, &name, mark.as_deref(), line, kind.as_deref())
        }
        "doc-remove" => {
            let name = os_string(args.required("name")?, "document name")?;
            let line = line_number(args.required("line")?, "--line")?;
            args.finish()?;
            doc_remove(&root, &workspace, &name, line)
        }
        "transclusions" | "follow" => {
            let host = os_string(args.required("name")?, "host name")?;
            let only = if action == "follow" {
                Some(os_string(args.required("transclusion")?, "transclusion")?)
            } else {
                None
            };
            args.finish()?;
            transclusions(&root, &workspace, &host, only.as_deref())
        }
        "can" => {
            let name = args
                .optional("name")
                .map(|value| os_string(value, "resource name"))
                .transpose()?;
            let all = match args.optional("all").as_deref().and_then(OsStr::to_str) {
                None | Some("false") => false,
                Some("true") => true,
                _ => return Err("--all must be true or false".into()),
            };
            let any = matches!(args.optional("any").as_deref().and_then(OsStr::to_str), Some("true"));
            args.finish()?;
            if any {
                let name = name.as_deref().ok_or("can --any needs a name")?;
                return lawsat::can_any(&root, &workspace, name);
            }
            can::can(&root, &workspace, name.as_deref(), all)
        }
        "inspect" => {
            let view = os_string(args.required("view")?, "inspect view")?;
            let name = args
                .optional("name")
                .map(|value| os_string(value, "inspect name"))
                .transpose()?;
            let refusals = args.optional("refusals").map(path);
            let json_out = match args.optional("json").as_deref().and_then(OsStr::to_str) {
                None | Some("false") => false,
                Some("true") => true,
                _ => return Err("--json must be true or false".into()),
            };
            args.finish()?;
            inspect_views::run(&root, &workspace, &view, name.as_deref(), refusals.as_deref(), json_out)
        }
        "law-check" => {
            let predicate = path(args.required("predicate")?);
            args.finish()?;
            lawsat::law_check(&root, &workspace, &predicate)
        }
        "propose" => {
            let request = path(args.required("request")?);
            let proposal_id = os_string(args.required("proposal-id")?, "proposal ID")?;
            let room = args
                .optional("private")
                .map(|value| os_string(value, "private room"))
                .transpose()?;
            let allow = matches!(
                args.optional("allow-unsatisfiable").as_deref().and_then(OsStr::to_str),
                Some("true")
            );
            let allow_lockout = matches!(
                args.optional("i-lock-myself-out").as_deref().and_then(OsStr::to_str),
                Some("true")
            );
            let freeze = matches!(
                args.optional("freeze-roster").as_deref().and_then(OsStr::to_str),
                Some("true")
            );
            let room_cell = matches!(
                args.optional("room-cell").as_deref().and_then(OsStr::to_str),
                Some("true")
            );
            args.finish()?;
            let source = bounded_json(&request)?;
            let action = source.get("action").and_then(Value::as_str).unwrap_or("");
            if action == "install-policy" {
                let unsat = lawsat::install_check(&root, &workspace, &source["predicate"], allow || freeze, allow_lockout)?;
                if unsat && !freeze {
                    sealing_a_room(&root, &workspace, member(&source, "name")?, room_cell)?;
                }
            }
            let roster_act = action == "revoke" || (action == "delegate" && source.get("room") == Some(&json!(true)));
            let result = propose(&root, &workspace, &request, &proposal_id, room.as_deref());
            match (roster_act, source.get("name").and_then(Value::as_str)) {
                (true, Some(name)) => result.map_err(|error| frozen_roster(name, error)),
                _ => result,
            }
        }
        "law-export-show" => {
            let name = os_string(args.required("name")?, "resource name")?;
            args.finish()?;
            law_export::show(&root, &workspace, &name)
        }
        "program-create" => {
            let name = os_string(args.required("name")?, "program name")?;
            let source = path(args.required("source")?);
            let predicate = path(args.required("predicate")?);
            let room = args.optional("in").map(|value|os_string(value,"room name")).transpose()?;
            args.finish()?;
            world_kind::program_create(&root,&workspace,&name,&source,&predicate,room.as_deref())
        }
        "instance-call" => {
            let name = os_string(args.required("name")?, "instance name")?;
            let method = os_string(args.required("method")?, "method name")?;
            let id = os_string(args.required("proposal-id")?, "proposal ID")?;
            let funding = args.optional("fund").map(|value|os_string(value,"funding account")).transpose()?;
            let maximum = args.optional("max-compute-credits").map(|value|os_string(value,"maximum compute credits")).transpose()?;
            args.finish()?;
            world_kind::call(&root,&workspace,&id,&name,&method,funding.as_deref(),maximum.as_deref())
        }
        "kind-show" | "instance-show" => {
            let name = os_string(args.required("name")?, "resource name")?;
            args.finish()?;
            world_kind::show(&root, &workspace, &name,
                if action == "kind-show" { "worldKind" } else { "worldInstance" })
        }
        "kind-create" | "instance-create" => {
            let name = os_string(args.required("name")?, "resource name")?;
            let predicate = path(args.required("predicate")?);
            let definition = args.optional("definition").map(path);
            let from = args.optional("from").map(|value| os_string(value, "kind reference")).transpose()?;
            let room = args.optional("in").map(|value| os_string(value, "room name")).transpose()?;
            args.finish()?;
            if (action == "kind-create") != definition.is_some() { return Err("kind-create needs definition; instance-create needs from".into()); }
            world_kind::create(&root, &workspace, &name, &predicate, room.as_deref(), definition.as_deref(), from.as_deref())
        }
        "create" => {
            let name = os_string(args.required("name")?, "resource name")?;
            let storage = os_string(args.required("storage")?, "storage")?;
            let predicate = path(args.required("predicate")?);
            let program = args.optional("program").map(path);
            let room = match args.optional("in") {
                Some(value) => Some(os_string(value, "room name")?),
                None => None,
            };
            let kind = match args.optional("kind") {
                Some(value) => os_string(value, "resource kind")?,
                None => "object".to_owned(),
            };
            let owner = match args.optional("owner") {
                Some(value) => Some(os_string(value, "resource owner")?),
                None => None,
            };
            let fields = match args.optional("fields") {
                Some(value) => Some(os_string(value, "declared fields")?),
                None => None,
            };
            // `--room-template T`: this resource is a room this workspace
            // founds (`room new`); its reference records the template.
            let room_template = match args.optional("room-template") {
                Some(value) => Some(os_string(value, "room template")?),
                None => None,
            };
            args.finish()?;
            create_with_template(
                &root,
                &workspace,
                &name,
                &storage,
                &predicate,
                room.as_deref(),
                &kind,
                owner.as_deref(),
                program.as_deref(),
                fields.as_deref(),
                room_template.as_deref(),
            )
        }
        "provision" => {
            let name = os_string(args.required("name")?, "provision name")?;
            let holder = os_string(args.required("holder")?, "holder subject")?;
            let funding = os_string(args.required("funding")?, "funding amount")?;
            let predicate = path(args.required("account-predicate")?);
            let factory_ref = os_string(args.required("factory-ref")?, "factory reference")?;
            args.finish()?;
            provision(
                &root,
                &workspace,
                &Provision {
                    name: &name,
                    holder: &holder,
                    funding: &funding,
                    predicate: &predicate,
                    factory_ref: &factory_ref,
                },
            )
        }
        "provision-lookup" => {
            let name = os_string(args.required("name")?, "provision name")?;
            let factory_ref = os_string(args.required("factory-ref")?, "factory reference")?;
            args.finish()?;
            provision_lookup(&root, &workspace, &name, &factory_ref)
        }
        "recover" => {
            let attempt = path(args.required("attempt")?);
            args.finish()?;
            recover(&root, &attempt)
        }
        "publish-delegation" => {
            let proposal_id = os_string(args.required("proposal-id")?, "proposal ID")?;
            let attempt = path(args.required("attempt")?);
            args.finish()?;
            publish_delegation(&root, &proposal_id, &attempt)
        }
        "doc-history" => {
            let name = os_string(args.required("name")?, "reference name")?;
            let format = show_format(args.optional("format"))?;
            args.finish()?;
            let history = doc_history(&root, &workspace, &name)?;
            print_changes(format, &history, crate::render::history::history_text, |value| {
                crate::render::history::history_html(value, &|_| String::new())
            })
        }
        "doc-diff" => {
            let name = os_string(args.required("name")?, "reference name")?;
            let from = os_string(args.required("from")?, "height")?;
            let to = os_string(args.required("to")?, "height")?;
            let format = show_format(args.optional("format"))?;
            args.finish()?;
            let diff = doc_diff(&root, &workspace, &name, &from, &to)?;
            print_changes(format, &diff, crate::render::history::diff_text, crate::render::history::diff_html)
        }
        "doc-device" => {
            args.finish()?;
            println!("{}", serde_json::to_string_pretty(&protected_document::device(&root)?).map_err(|e|e.to_string())?);
            Ok(())
        }
        "doc-epoch-export" => {
            let name = os_string(args.required("name")?, "document name")?;
            let output = path(args.required("output")?);
            args.finish()?;
            protected_document::export_epoch(&root, &workspace, &name, &output)
        }
        "doc-epoch-import" => {
            let name = os_string(args.required("name")?, "document name")?;
            let catalog = os_string(args.required("catalog")?, "device catalog reference")?;
            let input = path(args.required("bundle")?);
            args.finish()?;
            protected_document::import_epoch(&root, &workspace, &name, &catalog, &input)
        }
        "doc-protect-recover" => {
            let name = os_string(args.required("name")?, "document name")?;
            args.finish()?;
            protected_document::recover(&root, &workspace, &name)
        }
        "doc-protect" => {
            let name = os_string(args.required("name")?, "document name")?;
            args.finish()?;
            protected_document::protect_empty(&root, &workspace, &name)
        }
        "doc-new" => {
            let name = os_string(args.required("name")?, "document name")?;
            let predicate = path(args.required("predicate")?);
            let room = args.optional("in").map(|value| os_string(value, "room name")).transpose()?;
            args.finish()?;
            doc_new(&root, &workspace, &name, &predicate, room.as_deref())
        }
        "doc-range" => {
            let name = os_string(args.required("name")?, "document name")?;
            let from = line_number(args.required("from")?, "--from")?;
            let to = line_number(args.required("to")?, "--to")?;
            args.finish()?;
            doc_range(&root, &workspace, &name, from, to)
        }
        "doc-pull" => {
            let name = os_string(args.required("name")?, "reference name")?;
            args.finish()?;
            doc_pull(&root, &workspace, &name)
        }
        "doc-push" => {
            let name = os_string(args.required("name")?, "reference name")?;
            let file = path(args.required("file")?);
            let proposal_id = os_string(args.required("proposal-id")?, "proposal ID")?;
            let attempt = path(args.required("attempt")?);
            args.finish()?;
            doc_push(&root, &workspace, &name, &file, &proposal_id, &attempt)
        }
        "law-show" => {
            let name = os_string(args.required("name")?, "reference name")?;
            args.finish()?;
            crate::market::law_show(&root, &workspace, &name)
        }
        "market-open" => {
            let name = os_string(args.required("name")?, "market name")?;
            let close = os_string(args.required("close")?, "close height")?;
            let reveal_end = os_string(args.required("reveal-end")?, "reveal end height")?;
            let supply = os_string(args.required("supply")?, "supply")?;
            let deposit = args
                .optional("deposit")
                .map(|value| os_string(value, "deposit"))
                .transpose()?
                .unwrap_or_else(|| "0".into());
            args.finish()?;
            crate::market::open(&root, &workspace, &name, &close, &reveal_end, &supply, &deposit)
        }
        "market-bid" => {
            let name = os_string(args.required("name")?, "market name")?;
            let price = os_string(args.required("price")?, "price")?;
            let qty = os_string(args.required("qty")?, "quantity")?;
            let id = os_string(args.required("proposal-id")?, "proposal ID")?;
            args.finish()?;
            validate_name(&id)?;
            crate::market::bid(&root, &workspace, &name, &price, &qty, &id)
        }
        "market-reveal" | "market-settle" => {
            let name = os_string(args.required("name")?, "market name")?;
            let id = os_string(args.required("proposal-id")?, "proposal ID")?;
            args.finish()?;
            validate_name(&id)?;
            if action == "market-reveal" {
                crate::market::reveal(&root, &workspace, &name, &id)
            } else {
                crate::market::settle(&root, &workspace, &name, &id)
            }
        }
        "market-bids" => {
            let name = os_string(args.required("name")?, "market name")?;
            args.finish()?;
            crate::market::show(&root, &workspace, &name)
        }
        _ => Err(
            "workspace action must be init, onboard, continuity-init, continuity-verifier, continuity-check, import, list, describe, read, submit, propose, create, provision, provision-lookup, recover, publish-delegation, doc-show, doc-outline, doc-history, doc-diff, doc-insert, doc-move, doc-remove, doc-backlinks, doc-links, mark, unmark, transclude, transclusions, follow, doc-new, doc-range, doc-pull, doc-push, law-show, market-open, market-bid, market-reveal, market-bids or market-settle".into(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn atom(id: &str, text: &str, by: &str) -> Value {
        json!({"type":"atom","id":id,"document":"900","kind":{"type":"text"},
            "payload":hex(text.as_bytes()),
            "createdBy":{"subject":by,"capabilityKind":"object","capability":"31"},
            "createdAt":"55","revision":"56","tombstonedAt":null,"canonical":"00"})
    }

    fn page(entries: Vec<Value>) -> Value {
        json!({"type":"resource","cell":{"root":"77","entries":entries},"balances":[]})
    }

    /// A retained read of a document: atoms (id, text, struck) in the kernel's
    /// order under root "1"; `section` puts the ids it names in a section "5"
    /// placed after the first atom; `embed` adds a transclusion line at the end.
    fn seen_doc(lines: &[(&str, &str, bool)], section: &[&str], embed: bool) -> Value {
        let row = |id: &str, text: &str, struck: bool, parent: &str| {
            json!({"element":id,"atom":id,"kind":"atom","payload":hex(text.as_bytes()),
                "struck":struck,"parent":parent})
        };
        let mut entries = Vec::new();
        let mut order = Vec::new();
        for (index, (id, text, struck)) in lines.iter().enumerate() {
            let mut entry = atom(id, text, "7");
            if *struck {
                entry["tombstonedAt"] = json!("12");
            }
            entries.push(entry);
            if section.contains(id) {
                continue;
            }
            order.push(row(id, text, *struck, "1"));
            if index == 0 && !section.is_empty() {
                order.push(json!({"element":"5","kind":"container","parent":"1","revision":"61"}));
                for (inner, text, struck) in lines.iter().filter(|line| section.contains(&line.0)) {
                    order.push(row(inner, text, *struck, "5"));
                }
            }
        }
        if embed {
            order.push(json!({"element":"8001","kind":"embed","transclusion":"8001","parent":"1"}));
        }
        json!({"type":SEEN_TYPE,"name":"paper","height":"40","worldRoot":"41","view":page(entries),
            "document":{"root":"1","rootRevision":"60","order":order}})
    }

    /// Apply a push's actions to the retained read as the kernel would
    /// (`createAtom` appends to the root; move, remove and splice as
    /// `editElementStep`; an edit rewrites the payload or strikes), and return
    /// the pulled file of the result.
    fn applied(seen: &Value, plan: &PushPlan) -> Vec<u8> {
        let mut model = TreeModel::of(&seen["document"]).unwrap();
        let mut text: std::collections::BTreeMap<String, (Vec<u8>, bool)> = std::collections::BTreeMap::new();
        for row in seen["document"]["order"].as_array().unwrap() {
            if row["kind"] == "atom" {
                text.insert(row["element"].as_str().unwrap().into(),
                    (crate::decode_hex(row["payload"].as_str().unwrap()).unwrap(), row["struck"] == true));
            } else if row["kind"] == "embed" {
                let id = row["transclusion"].as_str().unwrap();
                text.insert(row["element"].as_str().unwrap().into(), (transclusion_marker(id), false));
            }
        }
        for action in &plan.actions {
            match action["type"].as_str().unwrap() {
                "createAtom" => {
                    let id = action["atom"].as_str().unwrap().to_owned();
                    model.children.get_mut("1").unwrap().push(id.clone());
                    model.parent.insert(id.clone(), "1".into());
                    text.insert(id, (crate::decode_hex(action["payload"].as_str().unwrap()).unwrap(), false));
                }
                "editAtom" => {
                    let entry = text.get_mut(action["atom"].as_str().unwrap()).unwrap();
                    *entry = (crate::decode_hex(action["payload"].as_str().unwrap()).unwrap(), action["tombstone"] == true);
                }
                "editElement" => {
                    let container = action["element"].as_str().unwrap().to_owned();
                    let op = &action["op"];
                    let child = op["child"].as_str().unwrap().to_owned();
                    let children = model.children.get_mut(&container).unwrap();
                    match op["type"].as_str().unwrap() {
                        "move" => {
                            children.retain(|c| *c != child);
                            children.insert(op["index"].as_str().unwrap().parse().unwrap(), child);
                        }
                        "remove" => children.retain(|c| *c != child),
                        "splice" => children.insert(op["index"].as_str().unwrap().parse().unwrap(), child),
                        other => panic!("{other}"),
                    }
                }
                other => panic!("{other}"),
            }
        }
        fn walk(model: &TreeModel, at: &str, out: &mut Vec<String>) {
            for child in model.children.get(at).cloned().unwrap_or_default() {
                out.push(child.clone());
                walk(model, &child, out);
            }
        }
        let mut order = Vec::new();
        walk(&model, "1", &mut order);
        let mut out = Vec::new();
        for element in order {
            if let Some((bytes, struck)) = text.get(&element) {
                if !struck {
                    out.extend_from_slice(bytes);
                    out.push(b'\n');
                }
            }
        }
        out
    }

    fn kinds(plan: &PushPlan) -> Vec<(String, bool)> {
        plan.actions
            .iter()
            .map(|a| (a["type"].as_str().unwrap().to_owned(), a.get("tombstone") == Some(&json!(true))))
            .collect()
    }

    #[test]
    fn private_document_alias_cannot_drop_or_change_its_room() {
        let root = std::env::temp_dir().join(format!("mini-private-alias-{}", random_nonce().unwrap()));
        make_private_dir(&root).unwrap(); make_private_dir(&root.join("refs")).unwrap();
        let hint = |name: &str, target: &str| json!({"type":"minidregg-participant-reference-v1",
            "name":name,"kind":"object","target":target,"observeCapability":"1"});
        for (name,target) in [("lab","71"),("alias-lab","71"),("other","99")] {
            private_file(&root.join("refs").join(format!("{name}.json")), &serde_json::to_vec(&hint(name,target)).unwrap()).unwrap();
        }
        let mut marked = hint("original", "72"); marked["sealedIn"] = json!("lab");
        private_file(&root.join("refs/original.json"), &serde_json::to_vec(&marked).unwrap()).unwrap();
        let alias = hint("second-name", "72");
        assert_eq!(sealing_room(None, &root, &alias).unwrap(), Some("lab".to_owned()));
        assert!(sealing_room(Some("alias-lab"), &root, &alias).unwrap().is_some());
        assert!(sealing_room(Some("other"), &root, &alias).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn private_import_context_requires_recipient_room_and_signed_membership() {
        let root = std::env::temp_dir().join(format!("mini-private-import-{}", random_nonce().unwrap()));
        make_private_dir(&root).unwrap(); make_private_dir(&root.join("refs")).unwrap();
        let public = json!({"name":"wrong","kind":"object","target":"71"});
        private_file(&root.join("refs/wrong.json"), &serde_json::to_vec(&public).unwrap()).unwrap();
        assert!(private_room_name(&root, "71").is_err());
        let own_room = json!({"name":"my-local-room","kind":"object","target":"71","private":{"protocol":"room-key"}});
        private_file(&root.join("refs/my-local-room.json"), &serde_json::to_vec(&own_room).unwrap()).unwrap();
        assert_eq!(private_room_name(&root, "71").unwrap(), "my-local-room");
        assert!(private_room_name(&root, "99").is_err());
        import_with_private_context(&root, ImportInput {name:"paper", kind:"object", target:"72",
            observe:"63", operation:Some("63"), control:None, provenance:None, room:None},
            Some(("my-local-room", "71"))).unwrap();
        let paper = reference(&root, "paper").unwrap();
        assert_eq!(paper["sealedIn"], "my-local-room");
        assert_eq!(paper["sealedRoom"], "71");
        assert!(require_room_member(&json!({"entries":[{"cells":["72","73"]}]}), "72").is_ok());
        assert!(require_room_member(&json!({"entries":[{"cells":["99"]}]}), "72").is_err());
        assert!(require_room_member(&json!({"entries":null}), "72").is_err());
        assert!(require_room_member(&json!({"entries":[{"cells":["72"]}]}), "072").is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn doc_push_private_diff_uses_opened_text_but_preserves_ciphertext_guard() {
        let key = private::RoomKey::generate(0).unwrap();
        let sealed = private::seal_content(json!({"type":"content","actions":[
            {"type":"createAtom","atom":"10","kind":{"type":"text"},"payload":hex(b"private old")}
        ]}), "71", "72", &key).unwrap();
        let mut seen = seen_doc(&[("10", "private old", false)], &[], false);
        seen["view"]["cell"]["entries"][0]["kind"] = sealed["actions"][0]["kind"].clone();
        seen["view"]["cell"]["entries"][0]["payload"] = sealed["actions"][0]["payload"].clone();
        seen["document"]["order"][0]["payload"] = sealed["actions"][0]["payload"].clone();
        assert!(pull_text(&seen).is_err());
        let mut display = seen["view"].clone();
        let mut keys = private::Keyring::default(); keys.insert("71", &key);
        private::open_view(&mut display, "71", "72", Some(&keys));
        seen["openedEntries"] = display["cell"]["entries"].clone();
        assert_eq!(pull_text(&seen).unwrap(), b"private old\n");
        let names = std::collections::BTreeMap::new();
        let sources = std::collections::BTreeMap::new();
        let render = |entries: &[Value]| crate::render::render(&crate::render::View {
            document: &seen["document"], entries, names: &names, sources: &sources, me: "7"
        }).unwrap();
        assert_eq!(render(seen["openedEntries"].as_array().unwrap()).raw(), b"private old\n");
        let locked = render(seen["view"]["cell"]["entries"].as_array().unwrap()).text();
        assert!(locked.contains("private: locked"));
        assert!(!locked.contains("private old"));
        let plan = push_actions(&seen, b"private new\n").unwrap();
        assert_eq!(plan.actions.len(), 1);
        assert_eq!(plan.actions[0]["before"], atom_record(&seen["view"]["cell"]["entries"][0]).unwrap());
        assert_eq!(plan.actions[0]["payload"], hex(b"private new"));
        assert_eq!(plan.actions[0]["before"]["payload"], sealed["actions"][0]["payload"]);
        let new = private::seal_content(json!({"type":"content","actions":plan.actions}), "71", "72", &key).unwrap();
        assert_eq!(new["actions"][0]["before"]["revision"], "56");
        assert_ne!(new["actions"][0]["payload"], plan.actions[0]["payload"]);
        let inserted = push_actions(&seen, b"first\nprivate old\n").unwrap();
        assert!(inserted.actions.iter().any(|a| a["type"] == "editElement"));
        assert!(private::seal_content(json!({"type":"content","actions":inserted.actions}), "71", "72", &key).is_ok());
    }

    #[test]
    fn doc_push_diff_is_minimal_edit_distance() {
        let l = |t: &str| t.as_bytes().to_vec();
        let old = [l("a"), l("b"), l("c")];
        let old: Vec<&[u8]> = old.iter().map(Vec::as_slice).collect();
        let ops = line_diff(&old, &old).unwrap();
        assert!(ops.iter().all(|op| matches!(op, LineOp::Keep(..))));
        // a replaced line is ONE edit, not strike + insert
        let new: Vec<&[u8]> = vec![b"a", b"B", b"c"];
        assert_eq!(line_diff(&old, &new).unwrap()[1], LineOp::Edit(1, 1));
        let new: Vec<&[u8]> = vec![b"A", b"b", b"C", b"d"];
        let ops = line_diff(&old, &new).unwrap();
        assert_eq!(ops.iter().filter(|op| !matches!(op, LineOp::Keep(..))).count(), 3);
        let new: Vec<&[u8]> = vec![b"a", b"c"];
        assert_eq!(line_diff(&old, &new).unwrap(), vec![LineOp::Keep(0, 0), LineOp::Strike(1), LineOp::Keep(2, 1)]);
        let new: Vec<&[u8]> = vec![b"z", b"a", b"b", b"c"];
        assert_eq!(line_diff(&old, &new).unwrap()[0], LineOp::Insert(0));
        let k: Vec<&[u8]> = "kitten".as_bytes().chunks(1).collect();
        let t: Vec<&[u8]> = "sitting".as_bytes().chunks(1).collect();
        assert_eq!(line_diff(&k, &t).unwrap().iter().filter(|op| !matches!(op, LineOp::Keep(..))).count(), 3);
    }

    #[test]
    fn doc_push_trailing_newline_rule_and_pull_round_trip() {
        let seen = seen_doc(&[("100", "one", false), ("200", "two ", false)], &[], false);
        assert_eq!(pull_text(&seen).unwrap(), b"one\ntwo \n");
        for same in [&b"one\ntwo \n"[..], &b"one\ntwo "[..]] {
            assert!(push_actions(&seen, same).unwrap().actions.is_empty());
        }
        let plan = push_actions(&seen, b"one\ntwo\n").unwrap();
        assert_eq!(kinds(&plan), vec![("editAtom".into(), false)]);
        assert_eq!(plan.pinned, vec![(2, "200".to_owned())]);
        // an extra final newline is a blank last line: appended, no placement
        let plan = push_actions(&seen, b"one\ntwo \n\n").unwrap();
        assert_eq!(kinds(&plan), vec![("createAtom".into(), false)]);
        assert_eq!(plan.actions[0]["payload"], "");
        let plan = push_actions(&seen, b"").unwrap();
        assert_eq!(plan.strikes, 2);
        assert_eq!(plan.actions[0]["payload"], seen["view"]["cell"]["entries"][0]["payload"]);
    }

    /// Inserts are placed by the element tree (K-DOC-ORDER closed): before the
    /// line they precede, in the root or inside a section, at the start, and
    /// appended at the end; the result reads back as the file, in order.
    #[test]
    fn doc_push_places_inserts_by_the_element_tree() {
        let seen = seen_doc(&[("100", "a", false), ("300", "gone", true), ("101", "b", false), ("102", "c", false)],
            &["101"], false);
        // the kernel's order: a, gone (struck), section{ b }, c — the file is a, b, c
        assert_eq!(pull_text(&seen).unwrap(), b"a\nb\nc\n");
        let file = b"x\na\ny\nb\nz\nc\nw\n";
        let plan = push_actions(&seen, file).unwrap();
        assert_eq!(plan.inserts, 4);
        assert_eq!(applied(&seen, &plan), file);
        // y precedes b, which stands in the section: removed from the root, spliced in
        let splices = plan.actions.iter().filter(|a| a["op"]["type"] == "splice").count();
        assert_eq!(splices, 1);
        // w ends the document: its createAtom is all it takes
        assert_eq!(plan.actions.last().unwrap()["type"], "createAtom");
        // every edit names a revision the pull read
        assert!(plan.actions.iter().filter(|a| a["type"] == "editElement")
            .all(|a| a["revision"] == "60" || a["revision"] == "61"));
    }

    /// Adjacent lines have no identifier space between them to exhaust: thirty
    /// lines inserted between two neighbours land in file order.
    #[test]
    fn doc_push_inserts_between_adjacent_lines_without_bisection() {
        let seen = seen_doc(&[("100", "a", false), ("101", "b", false)], &[], false);
        let mut file = b"a\n".to_vec();
        for i in 0..30 {
            file.extend(format!("new {i}\n").into_bytes());
        }
        file.extend(b"b\n");
        let plan = push_actions(&seen, &file).unwrap();
        assert_eq!(plan.inserts, 30);
        assert_eq!(applied(&seen, &plan), file);
    }

    #[test]
    fn doc_push_refuses_what_it_cannot_say() {
        let seen = seen_doc(&[("100", "a\nb", false)], &[], false);
        assert!(pull_text(&seen).unwrap_err().contains("line 1"));
        let seen = seen_doc(&[], &[], false);
        let big: Vec<u8> = (0..65).flat_map(|i| format!("{i}\n").into_bytes()).collect();
        assert!(push_actions(&seen, &big).err().unwrap().contains("at most 64"));
        // a transclusion line is a marker: kept as is, struck by remove, never edited
        let seen = seen_doc(&[("100", "a", false)], &[], true);
        assert_eq!(pull_text(&seen).unwrap(), "a\n⟦transclusion 8001⟧\n".as_bytes());
        assert!(push_actions(&seen, "a\n⟦transclusion 8001⟧\n".as_bytes()).unwrap().actions.is_empty());
        assert!(push_actions(&seen, b"a\nedited\n").err().unwrap().contains("is a transclusion"));
        let plan = push_actions(&seen, b"a\n").unwrap();
        assert_eq!(plan.actions, vec![edit_element("1", "60", json!({"type":"remove","child":"8001"}))]);
        // a second copy of the marker would be a transclusion the pull did not have
        assert!(push_actions(&seen, "a\n⟦transclusion 8001⟧\n⟦transclusion 8001⟧\n".as_bytes())
            .err().unwrap().contains("doc move"));
    }

    #[test]
    fn doc_push_lowers_through_the_document_payload() {
        let root = std::env::temp_dir().join(format!("pdw-{}", random_nonce().unwrap()));
        fs::create_dir_all(&root).unwrap();
        let seen = seen_doc(&[("100", "a", false), ("200", "b", false)], &[], false);
        retain_seen(&root, "paper", &seen["view"], &seen["document"], &json!({"height":"40","worldRoot":"41"})).unwrap();
        let actions = json!([{"type":"push","bytes":hex(b"a\nB\nc\n")}]);
        let lowered = document_actions(&root, &json!({}), "paper", &seen["view"], false, &actions).unwrap();
        let types: Vec<&str> = lowered.as_array().unwrap().iter().map(|a| a["type"].as_str().unwrap()).collect();
        assert_eq!(types, ["editAtom", "createAtom"]);
        assert_eq!(lowered[0]["before"]["payload"], hex(b"b"));
        assert!(content_actions(&lowered, false).is_ok());
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn scalar_values_are_the_hosts_signed_integers() {
        for good in ["0", "-1", "11033321548135836207", "-9223372036854775809"] {
            assert!(signed_decimal(good, "v").is_ok(), "{good}");
        }
        for bad in ["", "-", "-0", "01", "+1", "1.0", "x"] {
            assert!(signed_decimal(bad, "v").is_err(), "{bad}");
        }
        let lowered = scalar_actions(
            &json!([{"type":"create","key":{"type":"object","field":"1"},"value":"11033321548135836207"}]),
            "12",
        )
        .unwrap();
        assert_eq!(lowered["actions"][0]["value"], "11033321548135836207");
    }

    #[test]
    fn stream_append_carries_text_or_raw_bytes() {
        let text = stream_append(&json!({"type":"append","topic":"t","text":"hi"})).unwrap();
        assert_eq!(text["topic"], "74");
        assert_eq!(text["payload"], "6869");
        let raw = stream_append(&json!({"type":"append","topicHex":"00ff","payloadHex":"80"})).unwrap();
        assert_eq!(raw["topic"], "00ff");
        assert_eq!(raw["payload"], "80");
        for bad in [
            json!({"type":"append","topic":"t","topicHex":"00","text":"x"}),
            json!({"type":"append","topic":"t","text":"x","payloadHex":"00"}),
            json!({"type":"append","topic":"t"}),
            json!({"type":"append","topicHex":"0","text":"x"}),
            json!({"type":"append","topicHex":"zz","text":"x"}),
        ] {
            assert!(stream_append(&bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn sealed_content_validates_shape_then_seals_at_one_boundary() {
        let edit = json!([{"type":"editAtom","atom":"1","before":{},"kind":{"type":"text"},
            "payload":"61","tombstone":false}]);
        assert!(content_actions(&edit, false).is_ok());
        let validated = content_actions(&edit, true).unwrap();
        let key = private::RoomKey::generate(0).unwrap();
        assert!(private::seal_content(validated, "71", "72", &key).is_err());
        assert!(content_actions(&json!([{"type":"createAtom","atom":"1","kind":{"type":"text"},
            "payload":"61"}]), true).is_ok());
        assert!(content_actions(&json!([{"type":"transclude","id":"1"}]), false).is_err());
        assert!(content_actions(&json!([{"type":"editAtom","atom":"1"}]), false).is_err());
    }

    #[test]
    fn document_lines_lower_to_the_hosts_content_grammar() {
        let root = std::env::temp_dir().join(format!(
            "mini-doc-{}-{}",
            std::process::id(),
            random_nonce().unwrap()
        ));
        fs::create_dir_all(root.join("refs")).unwrap();
        let workspace = json!({"subject":"7"});
        let current = page(vec![atom("401", "first", "7"), atom("402", "second", "1103")]);
        let lowered =
            document_actions(&root, &workspace, "paper", &current, false, &json!([{"type":"append","text":"hi"}]))
                .unwrap();
        assert_eq!(lowered[0]["type"], "createAtom");
        assert_eq!(lowered[0]["payload"], "6869");
        assert_eq!(lowered[0]["kind"], json!({"type":"text"}));
        assert!(content_actions(&lowered, false).is_ok());
        // An edit names the line as this workspace last read it.
        let edit = json!([{"type":"edit","line":"2","text":"better"}]);
        assert!(document_actions(&root, &workspace, "paper", &current, false, &edit)
            .unwrap_err()
            .contains("doc show paper (or doc pull paper) first"));
        let seen = page(vec![atom("401", "first", "7"), atom("402", "old second", "1103")]);
        let order = json!({"order":[{"kind":"atom","element":"401"},{"kind":"atom","element":"402"}]});
        retain_seen(&root, "paper", &seen, &order, &json!({"height":"3","worldRoot":"4"})).unwrap();
        let lowered = document_actions(&root, &workspace, "paper", &current, false, &edit).unwrap();
        assert_eq!(lowered[0]["type"], "editAtom");
        assert_eq!(lowered[0]["atom"], "402");
        assert_eq!(lowered[0]["payload"], hex(b"better"));
        assert_eq!(lowered[0]["before"]["payload"], hex(b"old second"));
        assert_eq!(lowered[0]["before"]["createdBy"]["subject"], "1103");
        assert!(lowered[0]["before"].get("id").is_none() && lowered[0]["before"].get("canonical").is_none());
        assert!(content_actions(&lowered, false).is_ok());
        let past = json!([{"type":"edit","line":"3","text":"x"}]);
        assert!(document_actions(&root, &workspace, "paper", &current, false, &past)
            .unwrap_err()
            .contains("had 2 line(s)"));
        // Rereading replaces what an edit names.
        retain_seen(&root, "paper", &current, &order, &json!({"height":"5","worldRoot":"6"})).unwrap();
        let lowered = document_actions(&root, &workspace, "paper", &current, false, &edit).unwrap();
        assert_eq!(lowered[0]["before"]["payload"], hex(b"second"));
        let declared = json!({"type":"resource","cell":{"root":"1",
            "entries":[{"key":{"type":"object","field":"0"},"value":"1"}]}});
        assert!(document_actions(&root, &workspace, "shared", &declared, false, &edit)
            .unwrap_err()
            .contains("not a document"));
        // Line N is the kernel's order, not atom-id order: a reorder of the
        // retained order renames the line an edit names.
        let swapped = json!({"order":[{"kind":"atom","element":"402"},{"kind":"atom","element":"401"}]});
        retain_seen(&root, "paper", &current, &swapped, &json!({"height":"7","worldRoot":"8"})).unwrap();
        let first = json!([{"type":"edit","line":"1","text":"x"}]);
        let lowered = document_actions(&root, &workspace, "paper", &current, false, &first).unwrap();
        assert_eq!(lowered[0]["atom"], "402");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn revoke_names_the_capability_this_workspace_delegated() {
        let root = std::env::temp_dir().join(format!(
            "mini-revoke-{}-{}",
            std::process::id(),
            random_nonce().unwrap()
        ));
        for (id, recipient, child) in [("g1", "42", "901"), ("g2", "43", "902")] {
            fs::create_dir_all(root.join("proposals").join(id)).unwrap();
            fs::write(
                root.join("proposals").join(id).join("proposal.json"),
                serde_json::to_vec(&json!({"delegation":{"name":"shared","target":"12",
                    "recipient":recipient,"childCapability":child}}))
                .unwrap(),
            )
            .unwrap();
        }
        assert_eq!(delegated_capability(&root, "shared", "12", "42").unwrap(), "901");
        assert!(delegated_capability(&root, "shared", "12", "44").unwrap_err().contains("delegated nothing"));
        assert!(delegated_capability(&root, "other", "12", "42").is_err());
        fs::create_dir_all(root.join("proposals").join("g3")).unwrap();
        fs::write(
            root.join("proposals").join("g3").join("proposal.json"),
            br#"{"delegation":{"name":"shared","target":"12","recipient":"42","childCapability":"903"}}"#,
        )
        .unwrap();
        assert!(delegated_capability(&root, "shared", "12", "42").unwrap_err().contains("901, 903"));
        fs::remove_dir_all(root).unwrap();
    }

    fn generation_fixture(label: &str) -> (PathBuf, PathBuf, participant_namespace::Reservation) {
        let root = std::env::temp_dir().join(format!(
            "mini-generations-{label}-{}-{}",
            std::process::id(),
            random_nonce().unwrap()
        ));
        make_private_dir(&root).unwrap();
        let namespace = root.join("namespace");
        make_private_dir(&namespace).unwrap();
        let reservation = participant_namespace::Reservation {
            request_digest: "d".repeat(64),
            ids: Default::default(),
            record_path: namespace.join(format!("request-{}.json", "d".repeat(64))),
        };
        (root.clone(), root.join("create-x.authoring"), reservation)
    }

    fn observation_file(root: &Path, count: &std::cell::Cell<u32>) -> Result<PathBuf> {
        count.set(count.get() + 1);
        let path = root.join(format!("observation-{}.bin", count.get()));
        fs::write(&path, format!("signed observation {}", count.get())).unwrap();
        Ok(path)
    }

    /// A fake op91 that refuses any generation authored from `stale`.
    fn fake_author(generation: &Path, observation: Option<&Path>, stale: &[u8]) -> Result<()> {
        let retained = generation.join("factory-observation.bin");
        if !retained.exists() {
            fs::copy(
                observation.expect("fresh generation needs observation"),
                &retained,
            )
            .unwrap();
        }
        let bytes = fs::read(&retained).unwrap();
        let reply: Vec<u8> = if bytes == stale {
            vec![255, 1]
        } else {
            vec![91, 7]
        };
        fs::write(generation.join("reply.frame"), &reply).unwrap();
        if reply[0] == 255 {
            Err("current resource birth authoring refused".into())
        } else {
            Ok(())
        }
    }

    #[test]
    fn retained_stale_observation_is_superseded_once_and_prior_generation_kept() {
        let (root, base, reservation) = generation_fixture("stale");
        make_private_dir(&base).unwrap();
        make_private_dir(&base.join("g0001")).unwrap();
        fs::write(base.join("g0001/factory-observation.bin"), b"stale").unwrap();
        let observed = std::cell::Cell::new(0);
        let chosen = author_generations(
            &base,
            &reservation,
            || observation_file(&root, &observed),
            |generation, observation| fake_author(generation, observation, b"stale"),
            |_| false,
        )
        .unwrap();
        assert_eq!(chosen, base.join("g0002"));
        assert_eq!(observed.get(), 1);
        assert_eq!(fs::read(base.join("g0001/reply.frame")).unwrap(), [255, 1]);
        assert_eq!(
            fs::read(base.join("g0001/factory-observation.bin")).unwrap(),
            b"stale"
        );
        assert_eq!(fs::read(base.join("g0002/reply.frame")).unwrap(), [91, 7]);
        // A final generation is reused without another observation or authoring.
        let again = author_generations(
            &base,
            &reservation,
            || panic!("no observation after an intent"),
            |_, _| panic!("no authoring after an intent"),
            |_| panic!("no probe after an intent"),
        )
        .unwrap();
        assert_eq!(again, base.join("g0002"));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn declared_fields_parse_lists_ranges_and_open() {
        assert_eq!(parse_fields("open").unwrap(), json!("open"));
        assert_eq!(parse_fields("2,3").unwrap(), json!(["2", "3"]));
        assert_eq!(parse_fields("0-3,2,7").unwrap(), json!(["0", "1", "2", "3", "7"]));
        assert!(parse_fields("").is_err());
        assert!(parse_fields("3-1").is_err());
        assert!(parse_fields("a").is_err());
    }

    #[test]
    fn retained_refusal_before_any_call_no_longer_blocks_same_name_create() {
        let (root, base, reservation) = generation_fixture("refused");
        make_private_dir(&base).unwrap();
        make_private_dir(&base.join("g0001")).unwrap();
        fs::write(base.join("g0001/factory-observation.bin"), b"stale").unwrap();
        fs::write(base.join("g0001/reply.frame"), [255, 1]).unwrap();
        let observed = std::cell::Cell::new(0);
        let chosen = author_generations(
            &base,
            &reservation,
            || observation_file(&root, &observed),
            |generation, observation| fake_author(generation, observation, b"stale"),
            |_| false,
        )
        .unwrap();
        assert_eq!(chosen, base.join("g0002"));
        assert_eq!(authoring_generations(&base).unwrap().len(), 2);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn refusal_with_fresh_observation_is_reported_not_retried_in_a_loop() {
        let (root, base, reservation) = generation_fixture("fresh-refusal");
        let observed = std::cell::Cell::new(0);
        let refused = author_generations(
            &base,
            &reservation,
            || observation_file(&root, &observed),
            |generation, _| {
                fs::write(generation.join("reply.frame"), [255, 3]).unwrap();
                Err("refused".into())
            },
            |_| false,
        );
        // A refusal the Host does not answer stale-root is reported after one
        // observation (the race is re-planned: replan_birth_authoring_*).
        assert!(refused.is_err());
        assert_eq!(observed.get(), 1);
        assert_eq!(authoring_generations(&base).unwrap().len(), 1);
        // The next call supersedes that refusal exactly once.
        let chosen = author_generations(
            &base,
            &reservation,
            || observation_file(&root, &observed),
            |generation, observation| fake_author(generation, observation, b"never"),
            |_| false,
        )
        .unwrap();
        assert_eq!(chosen, base.join("g0002"));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn released_generation_is_superseded_with_a_fresh_observation() {
        let (root, base, reservation) = generation_fixture("released");
        make_private_dir(&base).unwrap();
        make_private_dir(&base.join("g0001")).unwrap();
        fs::write(base.join("g0001/factory-observation.bin"), b"old").unwrap();
        fs::write(base.join("g0001/reply.frame"), [91, 7]).unwrap();
        // An intent is final until its attempt is released.
        let kept = author_generations(
            &base,
            &reservation,
            || panic!("no observation for a final intent"),
            |_, _| panic!("no authoring for a final intent"),
            |_| panic!("no probe for a final intent"),
        )
        .unwrap();
        assert_eq!(kept, base.join("g0001"));
        fs::write(base.join("g0001/released.json"), b"{}").unwrap();
        let observed = std::cell::Cell::new(0);
        let chosen = author_generations(
            &base,
            &reservation,
            || observation_file(&root, &observed),
            |generation, observation| fake_author(generation, observation, b"never"),
            |_| false,
        )
        .unwrap();
        assert_eq!(chosen, base.join("g0002"));
        assert_eq!(observed.get(), 1);
        assert_eq!(fs::read(base.join("g0001/reply.frame")).unwrap(), [91, 7]);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn only_a_definite_refusal_or_a_missing_call_is_unadmitted() {
        let (root, _, _) = generation_fixture("definite");
        let attempt = root.join("create-x");
        make_private_dir(&attempt).unwrap();
        // No exact call: nothing was submitted.
        assert!(attempt_definitely_unadmitted(&attempt).unwrap());
        fs::write(attempt.join("call.bin"), b"call").unwrap();
        // A call with no outcome is uncertain.
        assert!(!attempt_definitely_unadmitted(&attempt).unwrap());
        fs::write(
            attempt.join("outcome.json"),
            br#"{"type":"refused","reason":"undisclosed"}"#,
        )
        .unwrap();
        assert!(attempt_definitely_unadmitted(&attempt).unwrap());
        // A newer uncertain retry outranks the older refusal.
        fs::write(attempt.join("retry-0001.json"), br#"{"type":"uncertain"}"#).unwrap();
        assert!(!attempt_definitely_unadmitted(&attempt).unwrap());
        // An installed confirmation is never unadmitted.
        fs::write(
            attempt.join("retry-0002.json"),
            br#"{"type":"confirmed","confirmation":"installed"}"#,
        )
        .unwrap();
        assert!(!attempt_definitely_unadmitted(&attempt).unwrap());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_raced_fresh_observation_is_reobserved_within_the_call() {
        let _guard = crate::replan::TEST_LOCK.lock().unwrap_or_else(|p| p.into_inner());
        crate::replan::set_max(crate::replan::DEFAULT_MAX);
        let (root, base, reservation) = generation_fixture("raced");
        let observed = std::cell::Cell::new(0);
        // The first fresh observation is raced by another admission (the Host
        // answers the probe stale-root); the second is not.
        let chosen = author_generations(
            &base,
            &reservation,
            || observation_file(&root, &observed),
            |generation, observation| fake_author(generation, observation, b"signed observation 1"),
            |_| true,
        )
        .unwrap();
        assert_eq!(chosen, base.join("g0002"));
        assert_eq!(observed.get(), 2);
        assert_eq!(fs::read(base.join("g0001/reply.frame")).unwrap(), [255, 1]);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn replan_propose_reads_that_disagree_are_made_again_and_nothing_else_is() {
        let _guard = crate::replan::TEST_LOCK.lock().unwrap_or_else(|p| p.into_inner());
        crate::replan::set_max(5);
        let race = |error: &str, _: Option<&crate::HostDecision>| error == OBSERVATIONS_MOVED;
        let calls = std::cell::Cell::new(0);
        let made = crate::replan::replan(
            "propose",
            || {
                calls.set(calls.get() + 1);
                if calls.get() < 3 { Err(OBSERVATIONS_MOVED.to_owned()) } else { Ok(calls.get()) }
            },
            race,
            |_| Ok(()),
        );
        assert_eq!(made, Ok(3));
        calls.set(0);
        let refused = crate::replan::replan(
            "propose",
            || {
                calls.set(calls.get() + 1);
                Err::<(), _>("parent capability lacks delegation verb".to_owned())
            },
            race,
            |_| Ok(()),
        );
        assert_eq!(refused, Err("parent capability lacks delegation verb".into()));
        assert_eq!(calls.get(), 1);
        let _ = crate::take_host_decision();
    }

    #[test]
    fn replan_birth_authoring_stale_observation_reobserves_until_it_lands() {
        let _guard = crate::replan::TEST_LOCK.lock().unwrap_or_else(|p| p.into_inner());
        crate::replan::set_max(5);
        let (root, base, reservation) = generation_fixture("stale-race");
        let observed = std::cell::Cell::new(0);
        let probed = std::cell::Cell::new(0);
        // The first two fresh observations are raced (the Host refuses them and
        // answers stale-root to a probe); the third lands.
        let chosen = author_generations(
            &base,
            &reservation,
            || observation_file(&root, &observed),
            |generation, observation| {
                fake_author(generation, observation, b"never")?;
                if observed.get() <= 2 {
                    fs::write(generation.join("reply.frame"), [255, 1]).unwrap();
                    return Err("current resource birth authoring refused".into());
                }
                Ok(())
            },
            |_| {
                probed.set(probed.get() + 1);
                true
            },
        )
        .unwrap();
        assert_eq!(chosen, base.join("g0003"));
        assert_eq!((observed.get(), probed.get()), (3, 2));
        assert_eq!(fs::read(base.join("g0001/reply.frame")).unwrap(), [255, 1]);
        assert_eq!(fs::read(base.join("g0003/reply.frame")).unwrap(), [91, 7]);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn replan_birth_authoring_is_bounded_and_names_the_attempts() {
        let _guard = crate::replan::TEST_LOCK.lock().unwrap_or_else(|p| p.into_inner());
        crate::replan::set_max(5);
        let (root, base, reservation) = generation_fixture("stale-bound");
        let observed = std::cell::Cell::new(0);
        let refused = author_generations(
            &base,
            &reservation,
            || observation_file(&root, &observed),
            |generation, observation| fake_author(generation, observation, b"never").and_then(|()| {
                fs::write(generation.join("reply.frame"), [255, 1]).unwrap();
                Err("current resource birth authoring refused".into())
            }),
            |_| true,
        )
        .unwrap_err();
        assert_eq!(observed.get(), 6);
        assert_eq!(authoring_generations(&base).unwrap().len(), 6);
        assert!(refused.contains("all 6 attempts (5 re-plans"), "{refused}");
        assert!(refused.contains("g0006/reply.frame"), "{refused}");
        // --replan-max 0: one observation, reported, the old behaviour.
        crate::replan::set_max(0);
        let (root0, base0, reservation0) = generation_fixture("stale-zero");
        let observed0 = std::cell::Cell::new(0);
        assert!(author_generations(
            &base0,
            &reservation0,
            || observation_file(&root0, &observed0),
            |generation, _| {
                fs::write(generation.join("reply.frame"), [255, 1]).unwrap();
                Err("refused".into())
            },
            |_| true,
        )
        .is_err());
        assert_eq!(observed0.get(), 1);
        crate::replan::set_max(crate::replan::DEFAULT_MAX);
        fs::remove_dir_all(root).unwrap();
        fs::remove_dir_all(root0).unwrap();
    }

    #[test]
    fn bound_attempt_forbids_superseding_a_refused_generation() {
        let (root, base, reservation) = generation_fixture("bound");
        make_private_dir(&base).unwrap();
        make_private_dir(&base.join("g0001")).unwrap();
        fs::write(base.join("g0001/reply.frame"), [255, 1]).unwrap();
        fs::write(
            reservation
                .record_path
                .parent()
                .unwrap()
                .join(format!("binding-{}.json", reservation.request_digest)),
            b"{}",
        )
        .unwrap();
        let refused = author_generations(
            &base,
            &reservation,
            || panic!("no observation under bound custody"),
            |_, _| panic!("no authoring under bound custody"),
            |_| panic!("no probe under bound custody"),
        );
        assert!(refused.is_err());
        assert_eq!(authoring_generations(&base).unwrap().len(), 1);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn generation_names_are_contiguous_and_closed() {
        let (root, base, _) = generation_fixture("names");
        make_private_dir(&base).unwrap();
        make_private_dir(&base.join("g0001")).unwrap();
        make_private_dir(&base.join("g0003")).unwrap();
        assert!(authoring_generations(&base).is_err());
        fs::remove_dir_all(base.join("g0003")).unwrap();
        fs::write(base.join("notes"), b"x").unwrap();
        assert!(authoring_generations(&base).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn doc_history_reads_each_row_and_the_height_below() {
        let since = json!({"entries":[
            {"height":"12","cells":["7","9"]},
            {"height":"13","cells":["9"]},
            {"height":"15","cells":["7"]},
            {"height":"16","cells":["7"]}]});
        assert_eq!(
            history_heights(&since, "7").unwrap(),
            vec![11, 12, 14, 15, 16]
        );
        assert_eq!(history_heights(&since, "8").unwrap(), Vec::<u64>::new());
        assert!(history_heights(&json!({}), "7").is_err());
        // The placeholder keys on the Host's named reason, never its text.
        assert!(reason_is_no_grant(&json!({"type":"refused","reason":"no-grant"})));
        assert!(!reason_is_no_grant(&json!({"type":"refused","reason":"operation-rejected",
            "detail":hex(b"history read refused")})));
        assert!(!reason_is_no_grant(&json!({"type":"confirmed"})));
    }

    #[test]
    fn untrusted_reference_cannot_escape_scoped_workspace_or_replace_existing_name() {
        let root = std::env::temp_dir().join(format!(
            "mini-workspace-{}-{}",
            std::process::id(),
            random_nonce().unwrap()
        ));
        make_private_dir(&root).unwrap();
        make_private_dir(&root.join("refs")).unwrap();
        let named = |name, target| ImportInput {
            name,
            kind: "object",
            target,
            observe: "456",
            operation: None,
            control: None,
            provenance: None,
            room: None,
        };
        assert!(import(&root, named("../escape", "123")).is_err());
        assert!(import(&root, named("one", "01")).is_err());
        import(&root, named("one", "123")).unwrap();
        assert!(import(&root, named("one", "999")).is_err());
        assert_eq!(
            member(&reference(&root, "one").unwrap(), "target").unwrap(),
            "123"
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn named_proposal_blocks_nested_resource_and_capability_injection() {
        assert!(scalar_actions(
            &json!([{"type":"create","key":
            {"type":"object","resource":"999","field":"0"},"value":"1"}]),
            "123"
        )
        .is_err());
        let lowered = scalar_actions(
            &json!([{"type":"write","key":
            {"type":"object","field":"0"},"expected":"1","value":"2"}]),
            "123",
        )
        .unwrap();
        assert_eq!(lowered["actions"][0]["key"]["resource"], "123");
        assert!(content_actions(&json!([{"type":"tombstoneDocument","document":"1"}]), false).is_err());
        assert!(content_actions(&json!([{"type":"annotate","annotation":"1","atom":"2",
            "revision":"3","body":"00","extra":"4"}]), false).is_err());
        assert!(content_actions(&json!([{"type":"annotate","annotation":"1","atom":"2",
            "revision":"3","body":"00"}]), false).is_ok());
    }

    #[test]
    fn scalar_value_is_a_canonical_signed_decimal_of_any_width() {
        let action = |value: &str| {
            scalar_actions(
                &json!([{"type":"create","key":{"type":"object","field":"2"},"value":value}]),
                "123",
            )
        };
        // A hashEq commitment: a 256-bit integer, past i64.
        let commit = "14088966009597722056427368520402764894210252134876007857874900863984935149567";
        assert_eq!(action(commit).unwrap()["actions"][0]["value"], commit);
        assert!(action("-5").is_ok());
        assert!(action("0").is_ok());
        for bad in ["", "-", "+1", "01", "-0", "-01", "1.0", " 1", &"9".repeat(81)] {
            assert!(action(bad).is_err(), "{bad:?} accepted");
        }
        let write = |expected: &str| {
            scalar_actions(
                &json!([{"type":"write","key":{"type":"object","field":"2"},
                    "value":"1","expected":expected}]),
                "123",
            )
        };
        assert!(write(commit).is_ok());
        assert!(write("01").is_err());

    }

    #[test]
    fn docuverse_content_grammar() {
        assert!(content_actions(&json!([{"type":"createAtom","atom":"1","kind":{"type":"text"},"payload":"00"}]), false).is_ok());
        assert!(content_actions(&json!([{"type":"quote","element":"1","link":"2",
            "reference":{}}]), false).is_err());
        assert!(content_actions(&json!([{"type":"transclude","transclusion":"1","link":"2",
            "request":{}}]), false).is_ok());
        assert!(content_actions(&json!([{"type":"unlink","link":"9"}]), false).is_ok());
        assert!(content_actions(&json!([{"type":"unlink","link":"9","before":"1"}]), false).is_err());
        assert!(content_actions(&json!([{"type":"mark","mark":"1","target":{"type":"atom","atom":"2"},
            "revision":"3","kind":{"type":"bold"}}]), false).is_ok());
        assert!(content_actions(&json!([{"type":"mark","mark":"1","target":{"type":"atom","atom":"2"},
            "revision":"3","kind":{"type":"bold"},"payload":"00"}]), false).is_err());
        assert!(content_actions(&json!([{"type":"unmark","mark":"1"}]), false).is_ok());
    }

    #[test]
    fn marks_render_inline() {
        use crate::render::{decos, text::decorate};
        let names = std::collections::BTreeMap::from([("77".to_owned(), "target".to_owned())]);
        let marks = json!([{"kind":"bold","fresh":false},{"kind":"bold","fresh":true},
            {"kind":"link","fresh":true,"target":{"type":"document","id":"77"}},
            {"kind":"italic","fresh":false}]);
        assert_eq!(decorate("two", &decos(&names, &marks, 1)), "[**~~_two_~~**](→ target)");
        let heading = json!([{"kind":"heading","fresh":true},{"kind":"code","fresh":true}]);
        assert_eq!(decorate("x", &decos(&names, &heading, 1)), "# `x`");
        let unknown = json!([{"kind":"link","fresh":false,"target":{"type":"document","id":"5"}}]);
        assert_eq!(decorate("y", &decos(&names, &unknown, 1)), "~~[y](→ doc:5)~~");
        assert_eq!(decorate("z", &decos(&names, &Value::Null, 1)), "z");
    }

    #[test]
    fn exact_lookup_replay_completes_an_interrupted_birth() {
        let root = std::env::temp_dir().join(format!(
            "mini-replayed-birth-{}-{}",
            std::process::id(),
            random_nonce().unwrap()
        ));
        make_private_dir(&root).unwrap();
        private_file(
            &root.join("retry-0001.json"),
            br#"{"type":"confirmed","confirmation":"replayed","transactionId":"3"}"#,
        )
        .unwrap();
        assert_eq!(
            accepted_outcome(&root).unwrap().unwrap()["transactionId"],
            "3"
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn field_roots_and_resource_ids_have_distinct_decimal_bounds() {
        let root =
            "12345678901234567890123456789012345678901234567890123456789012345678901234567890";
        field_decimal(root, "root").unwrap();
        assert!(decimal(root, "resource ID").is_err());
        assert!(field_decimal("01", "root").is_err());
    }

    #[test]
    fn workspace_delegation_refuses_operation_only_child() {
        let parent = json!(["observe", "mutate", "delegate"]);
        let parent = parent.as_array().unwrap();
        assert!(readable_delegation_verbs(json!(["mutate"]).as_array().unwrap(), parent).is_err());
        readable_delegation_verbs(json!(["observe", "mutate"]).as_array().unwrap(), parent)
            .unwrap();
    }

    #[test]
    fn delegated_reference_is_recipient_scoped_and_only_a_hint() {
        let root = std::env::temp_dir().join(format!(
            "mini-delegated-reference-{}-{}",
            std::process::id(),
            random_nonce().unwrap()
        ));
        make_private_dir(&root).unwrap();
        make_private_dir(&root.join("refs")).unwrap();
        let path = root.join("share.json");
        private_file(
            &path,
            br#"{"type":"minidregg-delegated-reference-v1",
            "recipient":"8","kind":"object","target":"600","capability":"63",
            "receipt":{"type":"confirmed","confirmation":"installed",
                "transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"}}"#,
        )
        .unwrap();
        assert!(import_delegated(&root, &json!({"subject":"7"}), "shared", &path).is_err());
        import_delegated(&root, &json!({"subject":"8"}), "shared", &path).unwrap();
        let imported = reference(&root, "shared").unwrap();
        assert_eq!(imported["observeCapability"], "63");
        assert_eq!(imported["authority"], "hint-only");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn delegated_child_id_is_bound_to_one_exact_attempt_before_submit() {
        let root = std::env::temp_dir().join(format!(
            "mini-delegate-bind-{}-{}",
            std::process::id(),
            random_nonce().unwrap()
        ));
        make_private_dir(&root).unwrap();
        for folder in ["refs", "proposals", "attempts"] {
            make_private_dir(&root.join(folder)).unwrap();
        }
        import(
            &root,
            ImportInput {
                name: "shared",
                kind: "object",
                target: "600",
                observe: "61",
                operation: Some("61"),
                control: None,
                provenance: None,
                room: None,
            },
        )
        .unwrap();
        let namespace = root.join("namespace");
        let workspace = json!({"subject":"7","namespaceRoot":namespace});
        let proposal = root.join("proposals/to-bob");
        make_private_dir(&proposal).unwrap();
        let request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
            "name":"shared","recipient":"8","verbs":["observe"],"maxCost":"10"});
        private_file(
            &proposal.join("request.json"),
            &serde_json::to_vec(&request).unwrap(),
        )
        .unwrap();
        let reference = reference(&root, "shared").unwrap();
        let fingerprint = serde_json::to_vec(&json!({"request":request,"reference":reference,
            "subject":"7"}))
        .unwrap();
        let reservation = participant_namespace::reserve(
            &namespace,
            "8501",
            "7",
            "delegate-to-bob",
            &fingerprint,
            &[Role {
                label: "childCapability".into(),
                kind: IdKind::Capability,
            }],
        )
        .unwrap();
        let source = proposal.join("intent.json");
        private_file(&source, b"{\"proposal\":true}").unwrap();
        let sha = format!("{:x}", Sha256::digest(fs::read(&source).unwrap()));
        let summary = json!({"proposalId":"to-bob","intentSha256":sha,
            "delegation":{"name":"shared","domain":"8501",
                "reservation":reservation.request_digest,
                "childCapability":reservation.ids["childCapability"]}});
        private_file(
            &proposal.join("proposal.json"),
            &serde_json::to_vec(&summary).unwrap(),
        )
        .unwrap();
        let first = root.join("attempts/first");
        bind_delegation_attempt(&root, &workspace, &source, &first).unwrap();
        bind_delegation_attempt(&root, &workspace, &source, &first).unwrap();
        assert!(
            bind_delegation_attempt(&root, &workspace, &source, &root.join("attempts/second"))
                .is_err()
        );
        fs::remove_dir_all(root).unwrap();
    }

    fn document_fixture() -> Value {
        // root 1: line a, struck b, section s (line c inside), transclusion t, line d
        json!({"type":"document","root":"1","rootRevision":"70","order":[
            {"element":"10","parent":"1","kind":"atom","atom":"10","payload":"61","struck":false},
            {"element":"11","parent":"1","kind":"atom","atom":"11","payload":"62","struck":true},
            {"element":"5","parent":"1","kind":"container","revision":"71","children":"1"},
            {"element":"12","parent":"5","kind":"atom","atom":"12","payload":"63","struck":false},
            {"element":"13","parent":"1","kind":"embed","transclusion":"13"},
            {"element":"14","parent":"1","kind":"atom","atom":"14","payload":"64","struck":false}]})
    }

    #[test]
    fn element_tree_lines_are_the_kernel_order_without_struck_lines() {
        let document = document_fixture();
        let lines: Vec<&str> = live_lines(&document)
            .unwrap()
            .iter()
            .map(|line| line["element"].as_str().unwrap())
            .collect();
        assert_eq!(lines, ["10", "12", "13", "14"]);
        assert_eq!(place_of(&document, "13").unwrap(), ("1".to_owned(), "70".to_owned(), 3));
        assert_eq!(place_of(&document, "12").unwrap(), ("5".to_owned(), "71".to_owned(), 0));
    }

    #[test]
    fn element_tree_insert_is_one_edit_at_the_lines_place() {
        let document = document_fixture();
        // line 3 is the transclusion, index 3 among the root's children (the struck line counts)
        assert_eq!(
            place_new_leaf(&document, "99", 3).unwrap(),
            vec![json!({"type":"editElement","element":"1","revision":"70",
                "op":{"type":"move","child":"99","index":"3"}})]
        );
        // one past the last line: the append is the place
        assert!(place_new_leaf(&document, "99", 5).unwrap().is_empty());
        // line 2 stands in a section: out of the root, into the section
        assert_eq!(
            place_new_leaf(&document, "99", 2).unwrap(),
            vec![
                json!({"type":"editElement","element":"1","revision":"70",
                    "op":{"type":"remove","child":"99"}}),
                json!({"type":"editElement","element":"5","revision":"71",
                    "op":{"type":"splice","index":"0","child":"99"}}),
            ]
        );
        assert!(place_new_leaf(&document, "99", 6).is_err());
    }

    #[test]
    fn element_tree_move_names_both_places() {
        let document = document_fixture();
        assert_eq!(
            move_line(&document, 4, 1).unwrap(),
            vec![json!({"type":"editElement","element":"1","revision":"70",
                "op":{"type":"move","child":"14","index":"0"}})]
        );
        assert_eq!(move_line(&document, 1, 2).unwrap().len(), 2);
        assert!(move_line(&document, 2, 2).is_err());
    }

}
