//! Participant-owned references and custody over the existing Mini client.
//! A reference is a discovery hint. Every read and operation still goes through
//! the signed observation, current Plan, and Lean admission in `main`.

use crate::current_birth;
use crate::participant_namespace::{self, IdKind, Role};
use crate::{
    absolute, author, hex, path, query, query_retained, retry, submit, Args, Result, SOCKET,
};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::ffi::{OsStr, OsString};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};

const MAX_RECORD: u64 = 256 * 1024;

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

fn private_dir(path: &Path) -> Result<()> {
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
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() > MAX_RECORD {
        return Err(format!(
            "{} must be a bounded regular JSON file",
            path.display()
        ));
    }
    let mut bytes = Vec::new();
    File::open(path)
        .and_then(|file| file.take(MAX_RECORD + 1).read_to_end(&mut bytes))
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    if bytes.len() as u64 > MAX_RECORD {
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

fn os_string(value: OsString, label: &str) -> Result<String> {
    value
        .into_string()
        .map_err(|_| format!("{label} must be UTF-8"))
}

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
    let _ = member_path(&value, "host")?;
    let _ = member_path(&value, "config")?;
    let _ = member_path(&value, "key")?;
    match (value.get("socket").and_then(Value::as_str), SOCKET.get()) {
        (Some(socket), Some(selected)) if Path::new(socket) != selected => {
            return Err("selected socket differs from pinned workspace socket".into());
        }
        (Some(socket), None) => {
            let path = PathBuf::from(socket);
            if !path.is_absolute() {
                return Err("workspace socket is not absolute".into());
            }
            SOCKET
                .set(path)
                .map_err(|_| "cannot pin workspace socket")?;
        }
        (None, Some(_)) => return Err("workspace has no pinned socket".into()),
        _ => {}
    }
    Ok(value)
}

pub(crate) struct InitIdentity<'a> {
    pub(crate) key: Option<&'a Path>,
    pub(crate) subject: Option<&'a str>,
    pub(crate) enrollment: Option<&'a Path>,
}

pub(crate) fn init(
    root: &Path,
    host: &Path,
    config: &Path,
    identity: InitIdentity<'_>,
    birth_context: Option<&Path>,
    namespace_root: Option<&Path>,
) -> Result<()> {
    let InitIdentity {
        key,
        subject,
        enrollment,
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
    let host = absolute(host)?;
    let config = absolute(config)?;
    let key = absolute(key)?;
    if !host.is_file() || !config.is_file() || !key.is_file() {
        return Err("workspace Host, config and key must exist as files".into());
    }
    let socket = SOCKET.get().map(|socket| absolute(socket)).transpose()?;
    let context = birth_context.map(absolute).transpose()?;
    if let Some(context) = &context {
        let _ = bounded_json(context)?;
    }
    let namespace = namespace_root.map(absolute).transpose()?;
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
    let value = json!({"type":"minidregg-participant-workspace-v1", "host":host,
        "config":config,"key":key,"subject":subject,"socket":socket,
        "birthContext":retained_context,"namespaceRoot":namespace,
        "enrollment":retained_enrollment});
    let mut bytes = serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    private_file(&root.join("workspace.json"), &bytes)?;
    println!("{}", root.display());
    Ok(())
}

pub(crate) fn reference(root: &Path, name: &str) -> Result<Value> {
    validate_name(name)?;
    let value = bounded_json(&root.join("refs").join(format!("{name}.json")))?;
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
}

pub(crate) fn import(root: &Path, input: ImportInput<'_>) -> Result<()> {
    let ImportInput {
        name: name_value,
        kind,
        target,
        observe,
        operation,
        control,
        provenance,
    } = input;
    validate_name(name_value)?;
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
    let value = json!({"type":"minidregg-participant-reference-v1","name":name_value,
        "kind":kind,"target":target,"observeCapability":observe,
        "operationCapability":operation.unwrap_or(observe),"controlCapability":control,
        "provenance":provenance,"authority":"hint-only"});
    let mut bytes = serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    private_file(
        &root.join("refs").join(format!("{name_value}.json")),
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
    import(
        root,
        ImportInput {
            name,
            kind: member(&value, "kind")?,
            target: member(&value, "target")?,
            observe: member(&value, "capability")?,
            operation: Some(member(&value, "capability")?),
            control: None,
            provenance: Some(source),
        },
    )
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
        values.push(reference(root, stem)?);
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

fn read(root: &Path, workspace: &Value, resource_name: &str, view: &str) -> Result<()> {
    let reference = reference(root, resource_name)?;
    let (attempt, nonce) = new_attempt(root)?;
    let intent = json!({"subject":member(workspace,"subject")?,"nonce":nonce,
        "purpose":{"type":"query","kind":member(&reference,"kind")?,
            "target":member(&reference,"target")?,"view":view},
        "grants":[{"kind":member(&reference,"kind")?,"target":member(&reference,"target")?,
            "capability":member(&reference,"observeCapability")?}]});
    let mut bytes = serde_json::to_vec_pretty(&intent).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    let source = root.join("sources").join(format!("q-{nonce}.json"));
    private_file(&source, &bytes)?;
    eprintln!("workspace read attempt: {}", attempt.display());
    query(
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
        &source,
        OsStr::new("intent"),
        &member_path(workspace, "key")?,
        &format!("view-{view}"),
        &attempt,
    )
}

pub(crate) fn signed_view(
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
        &member_path(workspace, "host")?,
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

fn signed_authority_root(challenge: &Value) -> Result<&str> {
    let root = challenge
        .get("authorityRoot")
        .and_then(Value::as_str)
        .ok_or("signed query challenge lacks authority root")?;
    field_decimal(root, "signed authority root")?;
    Ok(root)
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
        if value.parse::<i64>().is_err() {
            return Err("scalar value must be a signed integer".into());
        }
        let mut lowered_action = json!({"type":tag,
            "key":{"type":"object","resource":target,"field":field},"value":value});
        if tag == "write" {
            let expected = action
                .get("expected")
                .ok_or("write action lacks expected")?;
            if !expected.is_null()
                && expected
                    .as_str()
                    .and_then(|value| value.parse::<i64>().ok())
                    .is_none()
            {
                return Err("write expected must be null or signed integer".into());
            }
            lowered_action["expected"] = expected.clone();
        }
        lowered.push(lowered_action);
    }
    Ok(json!({"type":"scalar","actions":lowered}))
}

fn content_actions(actions: &Value) -> Result<Value> {
    let actions = actions
        .as_array()
        .ok_or("content actions must be an array")?;
    if actions.is_empty() || actions.len() > 64 {
        return Err("content proposal requires 1..64 actions".into());
    }
    for action in actions {
        let obj = action
            .as_object()
            .ok_or("content action must be an object")?;
        let (tag, fields): (&str, &[&str]) = match member(action, "type")? {
            "createAtom" => ("createAtom", &["type", "atom", "kind", "payload"]),
            "createDocument" => ("createDocument", &["type", "rootElement", "schema", "body"]),
            "createRun" => ("createRun", &["type", "run", "atoms"]),
            _ => {
                return Err(
                    "workspace content proposal supports local creation actions only".into(),
                )
            }
        };
        if obj.len() != fields.len() || fields.iter().any(|field| !obj.contains_key(*field)) {
            return Err(format!("{tag} has unexpected fields"));
        }
    }
    Ok(json!({"type":"content","actions":actions}))
}

fn propose(root: &Path, workspace: &Value, request_path: &Path, proposal_id: &str) -> Result<()> {
    validate_name(proposal_id)?;
    let request = bounded_json(request_path)?;
    if member(&request, "type")? != "minidregg-workspace-proposal-v1" {
        return Err("unknown workspace proposal version".into());
    }
    let nonce = random_nonce()?;
    let mut delegation = None::<Value>;
    let intent = match member(&request, "action")? {
        "invoke" => {
            let obj = request.as_object().ok_or("proposal must be an object")?;
            if obj.len() != 3 || !obj.contains_key("targets") {
                return Err("invoke proposal may contain only type, action, targets".into());
            }
            let selected = request
                .get("targets")
                .and_then(Value::as_array)
                .ok_or("invoke targets must be an array")?;
            if selected.is_empty() || selected.len() > 16 {
                return Err("invoke proposal needs 1..16 targets".into());
            }
            let mut target_rows = Vec::new();
            let mut grants = Vec::new();
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
                let (view, challenge, _) = signed_view(root, workspace, &reference, "resource")?;
                let current_image = member(&challenge, "worldRoot")?.to_owned();
                if let Some(previous) = &image {
                    if previous != &current_image {
                        return Err("target reads have different image boundaries".into());
                    }
                }
                image = Some(current_image);
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
                if payload_obj.len() != 2
                    || !payload_obj.contains_key("type")
                    || !payload_obj.contains_key("actions")
                {
                    return Err("payload may contain only type and actions".into());
                }
                let lowered = match member(payload, "type")? {
                    "scalar" => scalar_actions(&payload["actions"], target)?,
                    "content" => content_actions(&payload["actions"])?,
                    _ => return Err("unsupported workspace payload type".into()),
                };
                let capability = member(&reference, "operationCapability")?;
                let observe = member(&reference, "observeCapability")?;
                target_rows.push(json!({"kind":kind,"target":target,"capability":capability,
                    "observeCapability":observe,"schemaVersion":"1",
                    "expectedTargetRoot":root_value,"payload":lowered}));
                grants.push(json!({"kind":kind,"target":target,"capability":observe}));
            }
            json!({"subject":member(workspace,"subject")?,"nonce":nonce,
                "purpose":{"type":"prepare","draft":{"type":"invoke",
                    "command":{"subject":member(workspace,"subject")?,
                    "nonce":random_nonce()?,"targets":target_rows}}},"grants":grants})
        }
        "install-policy" => {
            let obj = request.as_object().ok_or("proposal must be an object")?;
            if obj.len() != 4 || !obj.contains_key("name") || !obj.contains_key("predicate") {
                return Err(
                    "install-policy proposal may contain only type, action, name, predicate".into(),
                );
            }
            let reference = reference(root, member(&request, "name")?)?;
            let control = member(&reference, "controlCapability")?;
            let (policy, challenge, _) = signed_view(root, workspace, &reference, "policy")?;
            let version = member(&policy, "version")?
                .parse::<u64>()
                .map_err(|_| "signed policy version exceeds client range")?;
            let next = version
                .checked_add(1)
                .ok_or("policy version overflow")?
                .to_string();
            let prior = member(&policy, "address")?;
            let target = member(&reference, "target")?;
            json!({"subject":member(workspace,"subject")?,"nonce":nonce,
                "purpose":{"type":"prepare","draft":{"type":"install-source",
                    "subject":member(workspace,"subject")?,"control":control,
                    "declaration":{"expectedPreRoot":signed_authority_root(&challenge)?,
                        "expected":{"version":version.to_string(),"address":prior},
                        "nonce":random_nonce()?,"source":{"policyId":member(&policy,"policyId")?,
                            "version":next,"domain":member(&policy,"domain")?,
                            "semantics":member(&policy,"semantics")?,"previous":prior,
                            "predicate":request["predicate"]}}}},
                "grants":[{"kind":member(&reference,"kind")?,"target":target,
                    "capability":member(&reference,"observeCapability")?}]})
        }
        "delegate" => {
            let obj = request.as_object().ok_or("proposal must be an object")?;
            if obj.len() != 6
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
                    return Err(
                        "delegation observations disagree on current image or authority".into(),
                    );
                }
            }
            let head = capability
                .get("head")
                .ok_or("typed capability view lacks head")?;
            if member(&capability, "kind")? != kind || member(head, "id")? != parent_id {
                return Err("signed capability head differs from selected parent reference".into());
            }
            let targets = head
                .get("targets")
                .and_then(Value::as_array)
                .ok_or("parent capability lacks targets")?;
            if !targets.iter().any(|value| value.as_str() == Some(target)) {
                return Err("parent capability does not cover named target".into());
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
            let namespace = member_path(workspace, "namespaceRoot")?;
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
            let child = json!({"id":child_id,"root":member(head,"root")?,"parent":parent_id,
                "issuer":member(head,"issuer")?,"holder":{"type":"subject","subject":recipient},
                "targets":[target],"verbs":selected_verbs,"maxCost":maximum,
                "notBefore":child_before,"notAfter":parent_after,
                "issuerEpoch":member(head,"issuerEpoch")?,"policyId":member(head,"policyId")?,
                "policyEpoch":member(head,"policyEpoch")?,"ancestors":ancestors,
                "channels":head.get("channels").ok_or("parent capability lacks channels")?});
            delegation = Some(json!({"recipient":recipient,"kind":kind,"target":target,
                "childCapability":child_id,"reservation":reservation.request_digest,
                "domain":member(&policy,"domain")?,"name":member(&request,"name")?}));
            json!({"subject":member(workspace,"subject")?,"nonce":nonce,
                "purpose":{"type":"prepare","draft":{"type":"delegate-source",
                    "command":{"kind":kind,"domain":member(&policy,"domain")?,
                    "semantics":member(&policy,"semantics")?,"subject":member(workspace,"subject")?,
                    "nonce":random_nonce()?,"expectedTargetRoot":target_root,
                    "parentId":parent_id,"target":target,"expectedPreRoot":authority,
                    "child":child}}},
                "grants":[{"kind":kind,"target":target,"capability":parent_id}]})
        }
        _ => return Err("proposal action must be invoke, install-policy, or delegate".into()),
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
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
        OsStr::new("intent"),
        &proposal_dir.join("intent.json"),
        &proposal_dir.join("intent.bin"),
    )?;
    let summary = json!({"type":"minidregg-workspace-proposal-result-v1",
        "proposalId":proposal_id,"intentPath":proposal_dir.join("intent.json"),
        "intentSha256":intent_sha,"effect":"none","authority":"requires-current-admission",
        "delegation":delegation});
    let bytes = serde_json::to_vec_pretty(&summary).map_err(|error| error.to_string())?;
    private_file(&proposal_dir.join("proposal.json"), &bytes)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&summary).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn submit_intent(
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
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
        &source,
        OsStr::new(kind),
        &member_path(workspace, "key")?,
        &attempt,
        prepare_only,
    )
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
    let namespace = member_path(workspace, "namespaceRoot")?;
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

fn recover(root: &Path, attempt: &Path) -> Result<()> {
    let attempt = absolute(attempt)?;
    let attempts = fs::canonicalize(root.join("attempts")).map_err(|error| error.to_string())?;
    let candidate = fs::canonicalize(&attempt).map_err(|error| error.to_string())?;
    if candidate.parent() != Some(attempts.as_path()) {
        return Err("recovery attempt must belong directly to this workspace".into());
    }
    retry(&candidate, "lookup", false)
}

pub(crate) fn accepted_outcome(attempt: &Path) -> Result<Option<Value>> {
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
            return Ok(Some(value));
        }
    }
    Ok(None)
}

fn publish_delegation(root: &Path, proposal_id: &str, attempt: &Path) -> Result<()> {
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
    let value = json!({"type":"minidregg-delegated-reference-v1",
        "recipient":member(delegation,"recipient")?,"kind":member(delegation,"kind")?,
        "target":member(delegation,"target")?,
        "capability":member(delegation,"childCapability")?,
        "receipt":receipt,"proposalSha256":member(&summary,"intentSha256")?,
        "authority":"hint-only"});
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
) -> Result<Value> {
    let birth = source.get("birth").ok_or("retained birth source absent")?;
    let parts = birth
        .get("resources")
        .and_then(Value::as_array)
        .and_then(|values| values.first())
        .ok_or("retained birth source lacks resource")?;
    let target = member(parts, "target")?;
    let owner = member(parts, "ownerCapability")?;
    let control = member(parts, "controlCapability")?;
    if reservation.ids.get("target").map(String::as_str) != Some(target)
        || reservation.ids.get("ownerCapability").map(String::as_str) != Some(owner)
        || reservation.ids.get("controlCapability").map(String::as_str) != Some(control)
    {
        return Err("birth source no longer matches durable namespace reservation".into());
    }
    let reference_path = root.join("refs").join(format!("{name_value}.json"));
    if reference_path.exists() {
        let prior = reference(root, name_value)?;
        if member(&prior, "target")? == target && member(&prior, "observeCapability")? == owner {
            return Ok(prior);
        }
        return Err("confirmed birth conflicts with existing workspace reference".into());
    }
    let value = json!({"type":"minidregg-participant-reference-v1","name":name_value,
        "kind":"object","target":target,"observeCapability":owner,
        "operationCapability":owner,"controlCapability":control,
        "provenance":{"birthReceipt":receipt,"reservationDigest":reservation.request_digest,
            "reservationRecord":reservation.record_path},"authority":"hint-only"});
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

/// Author the reserved source through op91 in versioned generations.
///
/// A generation retains exactly one signed factory observation and at most one
/// Host reply; it is never rewritten. When the latest generation's retained
/// reply is a refusal, and no custody attempt is bound for this request, a new
/// generation authors the SAME source with a fresh observation. At most one
/// generation is superseded per call, and never one whose observation was
/// taken in this same call. Once a generation holds an intent, it is final.
fn author_generations(
    base: &Path,
    reservation: &participant_namespace::Reservation,
    mut observe: impl FnMut() -> Result<PathBuf>,
    mut author_one: impl FnMut(&Path, Option<&Path>) -> Result<()>,
) -> Result<PathBuf> {
    if !base.exists() {
        make_private_dir(base)?;
    }
    private_dir(base)?;
    let mut superseded = false;
    let mut observed_now = false;
    loop {
        let generations = authoring_generations(base)?;
        let current = match generations.last() {
            Some(current) => current.clone(),
            None => {
                let first = base.join("g0001");
                make_private_dir(&first)?;
                first
            }
        };
        private_dir(&current)?;
        if authoring_refused(&current)? {
            if observed_now || superseded {
                return Err(format!(
                    "current birth authoring refused with a fresh factory observation; retained {}",
                    current.join("reply.frame").display()
                ));
            }
            if participant_namespace::is_bound(reservation)? {
                return Err(
                    "refused authoring generation has a bound attempt; exact custody only".into(),
                );
            }
            make_private_dir(&base.join(format!("g{:04}", generations.len() + 1)))?;
            superseded = true;
            continue;
        }
        if current.join("reply.frame").exists() {
            return Ok(current);
        }
        let observation = if current.join("factory-observation.bin").exists() {
            None
        } else {
            observed_now = true;
            Some(observe()?)
        };
        match author_one(&current, observation.as_deref()) {
            Ok(()) => return Ok(current),
            Err(error) if authoring_refused(&current)? => {
                eprintln!(
                    "workspace birth authoring refused in {}: {error}",
                    current.display()
                );
            }
            Err(error) => return Err(error),
        }
    }
}

/// Reserve, author and submit one birth under a workspace name. Returns the
/// retained source, the confirmed receipt and the namespace reservation.
fn birth(
    root: &Path,
    workspace: &Value,
    name_value: &str,
    shape: &BirthShape<'_>,
) -> Result<(Value, Value, participant_namespace::Reservation)> {
    validate_name(name_value)?;
    if !matches!(shape.storage, "content" | "declared") {
        return Err("supported resource storage is content or declared".into());
    }
    decimal(shape.owner, "birth owner")?;
    let context_path = member_path(workspace, "birthContext")?;
    let namespace_root = member_path(workspace, "namespaceRoot")?;
    let context = bounded_json(&context_path)?;
    if member(&context, "type")? != "minidregg-participant-birth-context-v1" {
        return Err("unknown birth context version".into());
    }
    let request_path = root
        .join("sources")
        .join(format!("create-{name_value}.request.json"));
    let requested_core = json!({"type":"minidregg-workspace-create-request-v2",
        "name":name_value,"kind":shape.kind,"storage":shape.storage,"owner":shape.owner,
        "funding":shape.funding,"predicate":shape.predicate,"context":context,
        "subject":member(workspace,"subject")?});
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
    let roles = [
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
        .join(format!("create-{name_value}.json"));
    let nonce = member(&request, "nonce")?;
    let expected_source = json!({"subject":member(workspace,"subject")?,"nonce":nonce,
            "birth":{"genesis":context["genesis"],"template":context["template"],
                "creator":member(workspace,"subject")?,"nonce":nonce,
                "resources":[{"kind":shape.kind,"storage":shape.storage,
                    "target":reservation.ids["target"],"owner":shape.owner,
                    "ownerCapability":reservation.ids["ownerCapability"],
                    "controlCapability":reservation.ids["controlCapability"],
                    "predicate":shape.predicate}],
                "sourceCapabilities":source_capabilities,
                "funding":funding,"feePayer":context["feePayer"]},
            "grants":context["grants"]});
    let source = if source_path.exists() {
        let saved = bounded_json(&source_path)?;
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
        .join(format!("create-{name_value}.authoring"));
    let attempt = root.join("attempts").join(format!("create-{name_value}"));
    let host = member_path(workspace, "host")?;
    let config = member_path(workspace, "config")?;
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

fn create(
    root: &Path,
    workspace: &Value,
    name_value: &str,
    storage: &str,
    predicate_path: &Path,
) -> Result<()> {
    let predicate = bounded_json(predicate_path)?;
    let subject = member(workspace, "subject")?.to_owned();
    let (source, receipt, reservation) = birth(
        root,
        workspace,
        name_value,
        &BirthShape {
            kind: "object",
            storage,
            owner: &subject,
            predicate: &predicate,
            funding: None,
        },
    )?;
    complete_birth(root, name_value, &source, &receipt, &reservation).map(|_| ())
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
            .join(format!("create-{name_value}.handoff.json")),
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
            host: &member_path(workspace, "host")?,
            config: &member_path(workspace, "config")?,
            socket: SOCKET
                .get()
                .ok_or("provisioning requires a pinned persistent Host socket")?,
            sponsor_key: &member_path(workspace, "key")?,
            namespace_root: &member_path(workspace, "namespaceRoot")?,
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
            host: &member_path(workspace, "host")?,
            config: &member_path(workspace, "config")?,
            socket: SOCKET
                .get()
                .ok_or("provisioning requires a pinned persistent Host socket")?,
            sponsor_key: &member_path(workspace, "key")?,
            namespace_root: &member_path(workspace, "namespaceRoot")?,
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

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = os_string(args.required("action")?, "workspace action")?;
    let root = absolute(&path(args.required("dir")?))?;
    if action == "init" {
        let host = path(args.required("host")?);
        let config = path(args.required("config")?);
        let key = args.optional("key").map(path);
        let subject = args
            .optional("subject")
            .map(|value| os_string(value, "subject"))
            .transpose()?;
        let enrollment = args.optional("enrollment").map(path);
        let context = args.optional("birth-context").map(path);
        let namespace = args.optional("namespace-root").map(path);
        args.finish()?;
        return init(
            &root,
            &host,
            &config,
            InitIdentity {
                key: key.as_deref(),
                subject: subject.as_deref(),
                enrollment: enrollment.as_deref(),
            },
            context.as_deref(),
            namespace.as_deref(),
        );
    }
    let workspace = load(&root)?;
    match action.as_str() {
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
                },
            )
        }
        "list" => {
            args.finish()?;
            list(&root)
        }
        "describe" | "read" => {
            let name = os_string(args.required("name")?, "reference name")?;
            args.finish()?;
            read(
                &root,
                &workspace,
                &name,
                if action == "describe" {
                    "policy"
                } else {
                    "resource"
                },
            )
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
            )
        }
        "propose" => {
            let request = path(args.required("request")?);
            let proposal_id = os_string(args.required("proposal-id")?, "proposal ID")?;
            args.finish()?;
            propose(&root, &workspace, &request, &proposal_id)
        }
        "create" => {
            let name = os_string(args.required("name")?, "resource name")?;
            let storage = os_string(args.required("storage")?, "storage")?;
            let predicate = path(args.required("predicate")?);
            args.finish()?;
            create(&root, &workspace, &name, &storage, &predicate)
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
        _ => Err(
            "workspace action must be init, import, list, describe, read, submit, propose, create, provision, provision-lookup, recover or publish-delegation".into(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        )
        .unwrap();
        assert_eq!(again, base.join("g0002"));
        fs::remove_dir_all(root).unwrap();
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
        );
        assert!(refused.is_err());
        assert_eq!(observed.get(), 1);
        assert_eq!(authoring_generations(&base).unwrap().len(), 1);
        // The next call supersedes that refusal exactly once.
        let chosen = author_generations(
            &base,
            &reservation,
            || observation_file(&root, &observed),
            |generation, observation| fake_author(generation, observation, b"never"),
        )
        .unwrap();
        assert_eq!(chosen, base.join("g0002"));
        fs::remove_dir_all(root).unwrap();
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
        assert!(content_actions(&json!([{"type":"link","link":"1","source":null,
            "target":{"type":"document","page":{"contentDomain":"9","pageNumber":"1","expectedRoot":"3"},"id":"2"},
            "relation":"0"}])).is_err());
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
}
