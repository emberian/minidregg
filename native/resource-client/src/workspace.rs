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

fn decimal(value: &str, field: &str) -> Result<()> {
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

fn validate_name(value: &str) -> Result<()> {
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

fn make_private_dir(path: &Path) -> Result<()> {
    let mut builder = fs::DirBuilder::new();
    builder.mode(0o700);
    builder
        .create(path)
        .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    private_dir(path)
}

fn private_file(path: &Path, bytes: &[u8]) -> Result<()> {
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

fn bounded_json(path: &Path) -> Result<Value> {
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

fn member<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("workspace record lacks {key}"))
}

fn member_path(value: &Value, key: &str) -> Result<PathBuf> {
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

fn random_nonce() -> Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("cannot obtain workspace nonce: {error}"))?;
    Ok(u128::from_be_bytes(bytes).to_string())
}

fn new_attempt(root: &Path) -> Result<(PathBuf, String)> {
    for _ in 0..8 {
        let nonce = random_nonce()?;
        let attempt = root.join("attempts").join(format!("a-{nonce}"));
        if !attempt.exists() {
            return Ok((attempt, nonce));
        }
    }
    Err("could not allocate a distinct workspace attempt name".into())
}

fn load(root: &Path) -> Result<Value> {
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

struct InitIdentity<'a> {
    key: Option<&'a Path>,
    subject: Option<&'a str>,
    enrollment: Option<&'a Path>,
}

fn init(
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
            for field in ["transactionId", "eventId", "acceptedCount", "imageBoundary"] {
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

fn reference(root: &Path, name: &str) -> Result<Value> {
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

struct ImportInput<'a> {
    name: &'a str,
    kind: &'a str,
    target: &'a str,
    observe: &'a str,
    operation: Option<&'a str>,
    control: Option<&'a str>,
    provenance: Option<&'a Path>,
}

fn import(root: &Path, input: ImportInput<'_>) -> Result<()> {
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

fn signed_view(
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
    let result = query_retained(
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
        &source,
        OsStr::new("intent"),
        &member_path(workspace, "key")?,
        &format!("view-{view}"),
        &attempt,
    )?;
    let challenge = bounded_json(&attempt.join("challenge.json"))?;
    Ok((result, challenge, attempt.join("signed-observation.bin")))
}

fn signed_authority_root(challenge: &Value) -> Result<&str> {
    let root = challenge
        .get("signing")
        .and_then(Value::as_array)
        .and_then(|values| values.first())
        .and_then(|value| value.get("authorityRoot"))
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
            let mut authority = None::<String>;
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
                let current_authority = signed_authority_root(&challenge)?.to_owned();
                if let Some(previous) = &authority {
                    if previous != &current_authority {
                        return Err("target reads have different authority roots".into());
                    }
                }
                authority = Some(current_authority);
                let current_image = member(&challenge, "imageBoundary")?.to_owned();
                if let Some(previous) = &image {
                    if previous != &current_image {
                        return Err("target reads have different image boundaries".into());
                    }
                }
                image = Some(current_image);
                let target = member(&reference, "target")?;
                let kind = member(&reference, "kind")?;
                let root_value = view
                    .get("page")
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
                    "expectedAuthorityRoot":authority.ok_or("no authority root")?,
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
        _ => return Err("proposal action must be invoke or install-policy".into()),
    };
    let intent_bytes = serde_json::to_vec_pretty(&intent).map_err(|error| error.to_string())?;
    let intent_sha = format!("{:x}", Sha256::digest(&intent_bytes));
    let proposal_dir = root.join("proposals").join(proposal_id);
    make_private_dir(&proposal_dir)?;
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
        "intentSha256":intent_sha,"effect":"none","authority":"requires-current-admission"});
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

fn recover(root: &Path, attempt: &Path) -> Result<()> {
    let attempt = absolute(attempt)?;
    let attempts = fs::canonicalize(root.join("attempts")).map_err(|error| error.to_string())?;
    let candidate = fs::canonicalize(&attempt).map_err(|error| error.to_string())?;
    if candidate.parent() != Some(attempts.as_path()) {
        return Err("recovery attempt must belong directly to this workspace".into());
    }
    retry(&candidate, "lookup", false)
}

fn accepted_outcome(attempt: &Path) -> Result<Option<Value>> {
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

fn complete_birth(
    root: &Path,
    name_value: &str,
    source: &Value,
    receipt: &Value,
    reservation: &participant_namespace::Reservation,
) -> Result<()> {
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
            return Ok(());
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
    Ok(())
}

fn create(
    root: &Path,
    workspace: &Value,
    name_value: &str,
    storage: &str,
    predicate_path: &Path,
) -> Result<()> {
    validate_name(name_value)?;
    if !matches!(storage, "content" | "declared") {
        return Err("supported resource storage is content or declared".into());
    }
    let context_path = member_path(workspace, "birthContext")?;
    let namespace_root = member_path(workspace, "namespaceRoot")?;
    let context = bounded_json(&context_path)?;
    if member(&context, "type")? != "minidregg-participant-birth-context-v1" {
        return Err("unknown birth context version".into());
    }
    let predicate = bounded_json(predicate_path)?;
    let request_path = root
        .join("sources")
        .join(format!("create-{name_value}.request.json"));
    let requested_core = json!({"type":"minidregg-workspace-create-request-v1",
        "name":name_value,"storage":storage,"predicate":predicate,"context":context,
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
    let source_path = root
        .join("sources")
        .join(format!("create-{name_value}.json"));
    let nonce = member(&request, "nonce")?;
    let expected_source = json!({"subject":member(workspace,"subject")?,"nonce":nonce,
            "birth":{"genesis":context["genesis"],"template":context["template"],
                "creator":member(workspace,"subject")?,"nonce":nonce,
                "resources":[{"kind":"object","storage":storage,
                    "target":reservation.ids["target"],"owner":member(workspace,"subject")?,
                    "ownerCapability":reservation.ids["ownerCapability"],
                    "controlCapability":reservation.ids["controlCapability"],
                    "predicate":predicate}],
                "sourceCapabilities":context["sourceCapabilities"],
                "funding":context["funding"],"feePayer":context["feePayer"]},
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
    let author_dir = root
        .join("sources")
        .join(format!("create-{name_value}.current"));
    let attempt = root.join("attempts").join(format!("create-{name_value}"));
    if !attempt.exists() {
        let signed_factory = if author_dir.join("factory-observation.bin").exists() {
            None
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
            let (_, _, signed_factory) = signed_view(root, workspace, &factory_ref, "resource")?;
            Some(signed_factory)
        };
        current_birth::author(
            &member_path(workspace, "host")?,
            &member_path(workspace, "config")?,
            socket,
            &source_path,
            signed_factory.as_deref(),
            &author_dir,
            current_birth::Route::Resource,
        )?;
    }
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
            return complete_birth(root, name_value, &source, &receipt, &reservation);
        }
        retry(&attempt, "lookup", false)?;
        let receipt = accepted_outcome(&attempt)?
            .ok_or("historical create lookup did not confirm installed birth")?;
        return complete_birth(root, name_value, &source, &receipt, &reservation);
    }
    eprintln!("workspace birth attempt: {}", attempt.display());
    submit(
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
        &intent_path,
        OsStr::new("binary"),
        &member_path(workspace, "key")?,
        &attempt,
        false,
    )?;
    let receipt = accepted_outcome(&attempt)?.ok_or("birth returned without installed receipt")?;
    complete_birth(root, name_value, &source, &receipt, &reservation)
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
        "recover" => {
            let attempt = path(args.required("attempt")?);
            args.finish()?;
            recover(&root, &attempt)
        }
        _ => Err(
            "workspace action must be init, import, list, describe, read, submit or recover".into(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
