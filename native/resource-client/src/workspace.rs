//! Participant-owned references and custody over the existing Mini client.
//! A reference is a discovery hint. Every read and operation still goes through
//! the signed observation, current Plan, and Lean admission in `main`.

use crate::current_birth;
use crate::participant_namespace::{self, IdKind, Role};
use crate::{
    absolute, author, hex, inspect, path, print_json, query, query_retained, retry, submit, Args,
    Result, SOCKET,
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

fn line_number(value: OsString, flag: &str) -> Result<usize> {
    os_string(value, flag)?
        .parse::<usize>()
        .ok()
        .filter(|line| *line > 0)
        .ok_or_else(|| format!("{flag} must be a line number, 1 or more"))
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

/// The workspace's own reference names for a cell, else the cell id.
fn cell_label(root: &Path, cell: &str) -> String {
    let mut names: Vec<String> = fs::read_dir(root.join("refs"))
        .into_iter()
        .flatten()
        .flatten()
        .filter_map(|entry| {
            let file = entry.file_name().to_string_lossy().into_owned();
            let stem = file.strip_suffix(".json")?.to_owned();
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
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
        &source,
        OsStr::new("intent"),
        &member_path(workspace, "key")?,
        inspection,
        &attempt,
    )?;
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
        .filter_map(|name| name.strip_suffix(".json").map(str::to_owned))
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
    propose(root, workspace, &request_path, &proposal_id)?;
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
fn rendered_document(
    root: &Path,
    workspace: &Value,
    host_name: &str,
    only: Option<&str>,
    at: Option<&str>,
) -> Result<(String, Value, Vec<Value>)> {
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
    let host_bin = fs::read(host_bin).map_err(|error| error.to_string())?;
    let no_entries = Vec::new();
    let host_entries = if at.is_some() && host_view.is_null() {
        &no_entries
    } else {
        entries(&host_view)?
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
    let mut readable = std::collections::BTreeMap::new();
    for record in &records {
        let source = member(&record["opening"], "source")?.to_owned();
        if readable.contains_key(&source) {
            continue;
        }
        // A page at height H reads each source `at` H too: what the reader
        // could see then, under its grants as they stood then.
        let attempt = |reference: &Value| -> Result<Value> {
            match at {
                None => {
                    let (_, _, signed) = signed_view(root, workspace, reference, "resource")?;
                    let bin = fs::read(signed.with_file_name("view.bin")).map_err(|error| error.to_string())?;
                    Ok(json!({"target":source,"view":hex(&bin)}))
                }
                Some(height) => {
                    let (view, bin) = signed_at(root, workspace, reference, height)?;
                    if view["state"] != "live" {
                        return Err(format!("source {source} is not live at height {height}"));
                    }
                    let bin = fs::read(bin).map_err(|error| error.to_string())?;
                    Ok(json!({"target":source,"at":hex(&bin)}))
                }
            }
        };
        let read = match reference_for_target(root, &source)? {
            Some(reference) => match attempt(&reference) {
                Ok(read) => {
                    sources.push(read);
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
    let render = |sources: &Vec<Value>| -> Result<Value> {
        let (attempt, _) = new_attempt(root)?;
        make_private_dir(&attempt)?;
        let input = attempt.join("transclusions-in.json");
        private_file(
            &input,
            &serde_json::to_vec(&json!({"host":hex(&host_bin),"sources":sources}))
                .map_err(|error| error.to_string())?,
        )?;
        inspect(
            &member_path(workspace, "host")?,
            &member_path(workspace, "config")?,
            "view-document",
            &input,
            &attempt.join("transclusions.json"),
        )
    };
    let current = render(&sources)?;
    let mut shown = Vec::new();
    for item in current["transclusions"].as_array().ok_or("Host rendered no transclusions")? {
        if only.is_some_and(|id| item.get("id").and_then(Value::as_str) != Some(id)) {
            continue;
        }
        let mut item = item.clone();
        let source = member(&item["opening"], "source")?.to_owned();
        if member(&item["render"], "view")? == "moved" {
            if let Some(Some(reference)) = readable.get(&source) {
                let height = member(&item["opening"], "height")?.to_owned();
                let (_, bin) = signed_at(root, workspace, reference, &height)?;
                let at = fs::read(&bin).map_err(|error| error.to_string())?;
                let again = render(&vec![json!({"target":source,"at":hex(&at)})])?;
                if let Some(found) = again["transclusions"].as_array().and_then(|all| {
                    all.iter().find(|other| other.get("id") == item.get("id"))
                }) {
                    item["render"] = found["render"].clone();
                    item["at"] = json!(height);
                }
            }
        }
        let atoms = member(&item["opening"], "atoms")?.to_owned();
        let text = match member(&item["render"], "view")? {
            "unavailable" => format!("[transclusion: {atoms} atoms of {source}, not readable by you]"),
            "snapshot" | "live" => {
                let lines: Vec<String> = item["render"]["lines"]
                    .as_array()
                    .map(|lines| {
                        lines
                            .iter()
                            .filter_map(Value::as_str)
                            .map(|line| {
                                String::from_utf8_lossy(&crate::decode_hex(line).unwrap_or_default()).into_owned()
                            })
                            .collect()
                    })
                    .unwrap_or_default();
                let mark = if item["render"]["view"] == "snapshot" {
                    match item.get("at") {
                        Some(height) => format!("snapshot at {}", height.as_str().unwrap_or("?")),
                        None => "snapshot".to_owned(),
                    }
                } else if item["render"]["revised"] == true {
                    "live, revised".to_owned()
                } else {
                    "live".to_owned()
                };
                format!("[{mark} of {source}]\n{}", lines.join("\n"))
            }
            other => format!("[transclusion of {source}: {other}]"),
        };
        item["text"] = json!(text);
        shown.push(item);
    }
    Ok((member(&host_ref, "target")?.to_owned(), current, shown))
}

/// `transclusions` / `follow`: HOST's rendered transclusions.
fn transclusions(root: &Path, workspace: &Value, host_name: &str, only: Option<&str>) -> Result<()> {
    let (host, _, shown) = rendered_document(root, workspace, host_name, only, None)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({"type":"transclusions","host":host,
            "transclusions":shown}))
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
        &member_path(workspace, "host")?,
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
    propose(root, workspace, &request_path, &proposal_id)?;
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

/// `doc-show`: the document in the kernel's order.  Each live line is numbered;
/// a struck line shows as `-`; a transclusion is one line, shown as this
/// workspace's own read of its source renders it; a section is a heading.
/// Nothing is sorted here: the order is the kernel's.
fn doc_show(root: &Path, workspace: &Value, name: &str, at: Option<&str>) -> Result<()> {
    let (host, document, shown) = rendered_document(root, workspace, name, None, at)?;
    let order = document["order"].as_array().ok_or("document view has no order")?;
    let mut depth = std::collections::BTreeMap::<String, usize>::new();
    if let Some(root_element) = document["root"].as_str() {
        depth.insert(root_element.to_owned(), 0);
    }
    let mut lines = Vec::new();
    let mut text = Vec::new();
    let mut number = 0usize;
    for entry in order {
        let element = member(entry, "element")?.to_owned();
        let level = entry["parent"].as_str().and_then(|parent| depth.get(parent)).map_or(1, |d| d + 1);
        depth.insert(element.clone(), level);
        let indent = "  ".repeat(level.saturating_sub(1));
        let (n, body) = match entry["kind"].as_str() {
            Some("atom") => {
                let bytes = crate::decode_hex(entry["payload"].as_str().unwrap_or("")).unwrap_or_default();
                let body = String::from_utf8_lossy(&bytes).into_owned();
                if entry["struck"] == true {
                    (None, body)
                } else {
                    number += 1;
                    (Some(number), body)
                }
            }
            Some("embed") => {
                number += 1;
                let id = member(entry, "transclusion")?;
                let body = shown
                    .iter()
                    .find(|item| item["id"].as_str() == Some(id))
                    .and_then(|item| item["text"].as_str())
                    .unwrap_or("[transclusion]")
                    .to_owned();
                (Some(number), body)
            }
            Some("container") => (None, format!("[section {element}]")),
            Some(other) => (None, format!("[{other}]")),
            None => (None, String::new()),
        };
        text.push(match n {
            Some(n) => format!("{indent}{n:>3}  {body}"),
            None if entry["kind"] == "atom" => format!("{indent}  -  {body} (struck)"),
            None => format!("{indent}     {body}"),
        });
        let mut line = entry.clone();
        line["line"] = n.map_or(Value::Null, |n| json!(n));
        line["text"] = json!(body);
        lines.push(line);
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({"type":"document","host":host,
            "height":document["height"],"state":document["state"],
            "root":document["root"],"rootRevision":document["rootRevision"],
            "lines":lines,"text":text.join("\n")}))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn view_hex(attempt: &Path) -> Result<String> {
    let path = attempt.join("view.bin");
    fs::read(&path)
        .map(|bytes| hex(&bytes))
        .map_err(|error| format!("cannot read {}: {error}", path.display()))
}

/// Render `input` with the Host's `kind` inspection, retained beside `attempt`.
fn doc_render(workspace: &Value, attempt: &Path, kind: &str, input: &Value) -> Result<()> {
    let input_path = attempt.join(format!("{kind}-input.json"));
    private_file(
        &input_path,
        &serde_json::to_vec(input).map_err(|error| error.to_string())?,
    )?;
    let rendered = inspect(
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
        kind,
        &input_path,
        &attempt.join(format!("{kind}.json")),
    )?;
    print_json(&rendered)
}

/// Whether a client error is the Host's `at` refusal (its reason travels hex
/// encoded in the refusal outcome).
fn history_refused(error: &str) -> bool {
    let reason = error
        .split("encoded refusal: ")
        .nth(1)
        .map(|rest| {
            let digits: String = rest.chars().take_while(char::is_ascii_hexdigit).collect();
            (0..digits.len() / 2)
                .filter_map(|index| u8::from_str_radix(&digits[2 * index..2 * index + 2], 16).ok())
                .collect::<Vec<u8>>()
        })
        .unwrap_or_default();
    String::from_utf8_lossy(&reason).contains("history read refused")
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
fn doc_history(root: &Path, workspace: &Value, name: &str) -> Result<()> {
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
            Err(error) if history_refused(&error) => {
                eprintln!("doc history: no read at height {height}: {error}");
            }
            Err(error) => return Err(error),
        }
    }
    let input = json!({"target": target, "since": view_hex(&attempt)?, "at": reads});
    doc_render(workspace, &attempt, "view-history", &input)
}

/// `doc diff NAME H1 H2`: the atom changes between the two `at` reads.
fn doc_diff(root: &Path, workspace: &Value, name: &str, from: &str, to: &str) -> Result<()> {
    let reference = reference(root, name)?;
    let (_, left) = doc_query(root, workspace, &reference, "at", Some(from), "view-at")?;
    let (_, right) = doc_query(root, workspace, &reference, "at", Some(to), "view-at")?;
    let input = json!({"left": view_hex(&left)?, "right": view_hex(&right)?});
    doc_render(workspace, &right, "view-diff", &input)
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
            "createDocument" => ("createDocument", &["type", "rootElement", "schema"]),
            "createContainer" => ("createContainer", &["type", "element"]),
            "editElement" => ("editElement", &["type", "element", "revision", "op"]),
            "createRun" => ("createRun", &["type", "run", "atoms"]),
            "editAtom" => (
                "editAtom",
                &["type", "atom", "before", "kind", "payload", "tombstone"],
            ),
            "link" => ("link", &["type", "link", "source", "target", "relation"]),
            "annotate" => (
                "annotate",
                &["type", "annotation", "atom", "revision", "body"],
            ),
            "transclude" => ("transclude", &["type", "transclusion", "link", "request"]),
            "unlink" => ("unlink", &["type", "link"]),
            _ => return Err("unknown workspace content action".into()),
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
                let read_only = payload.get("type").and_then(Value::as_str) == Some("read");
                if read_only {
                    if payload_obj.len() != 1 {
                        return Err("a read payload may contain only type".into());
                    }
                } else if payload_obj.len() != 2
                    || !payload_obj.contains_key("type")
                    || !payload_obj.contains_key("actions")
                {
                    return Err("payload may contain only type and actions".into());
                }
                // The action grammar version the Host's controller requires per
                // payload: the scalar declaration (1) or the content command
                // grammar (`ContentResource.commandVersion`, 6), which an
                // observe-only `read` of a content cell is checked under too.
                let (lowered, schema_version) = match member(payload, "type")? {
                    "scalar" => (scalar_actions(&payload["actions"], target)?, "1"),
                    "content" => (content_actions(&payload["actions"])?, "6"),
                    "read" => (json!({"type":"read"}), "6"),
                    _ => return Err("unsupported workspace payload type".into()),
                };
                // A read target's authorization leg is checked under the observe
                // verb, so it carries the observe capability.
                let capability = if read_only {
                    member(&reference, "observeCapability")?
                } else {
                    member(&reference, "operationCapability")?
                };
                let observe = member(&reference, "observeCapability")?;
                target_rows.push(json!({"kind":kind,"target":target,"capability":capability,
                    "observeCapability":observe,"schemaVersion":schema_version,
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
            // Optional `"room": true`: a room invite, whose child is `under` the
            // named resource instead of the resource alone.
            let room_invite = match obj.get("room") {
                None => false,
                Some(Value::Bool(value)) => *value,
                Some(_) => return Err("delegate proposal room must be a boolean".into()),
            };
            if obj.len() != 6 + usize::from(obj.contains_key("room"))
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
            let mut child = json!({"id":child_id,"root":member(head,"root")?,"parent":parent_id,
                "issuer":member(head,"issuer")?,"holder":{"type":"subject","subject":recipient},
                "targets":[target],"verbs":selected_verbs,"maxCost":maximum,
                "notBefore":child_before,"notAfter":parent_after,
                "issuerEpoch":member(head,"issuerEpoch")?,"policyId":member(head,"policyId")?,
                "policyEpoch":member(head,"policyEpoch")?,"ancestors":ancestors,
                "channels":head.get("channels").ok_or("parent capability lacks channels")?});
            if room_invite {
                let scope = child.as_object_mut().ok_or("child capability is not an object")?;
                scope.remove("targets");
                scope.insert("room".into(), json!(target));
            }
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
    room_name: Option<&str>,
) -> Result<()> {
    validate_name(name_value)?;
    // `--in ROOM`: the new resource is born in the room a workspace reference
    // names. The Host refuses a room that is not a present resource cell.
    let room = match room_name {
        Some(room_name) => Some(member(&reference(root, room_name)?, "target")?.to_string()),
        None => None,
    };
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
    let mut requested_core = json!({"type":"minidregg-workspace-create-request-v1",
        "name":name_value,"storage":storage,"predicate":predicate,"context":context,
        "subject":member(workspace,"subject")?});
    if let Some(room) = &room {
        requested_core["room"] = json!(room);
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
    let mut expected_source = json!({"subject":member(workspace,"subject")?,"nonce":nonce,
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
    if let Some(room) = &room {
        expected_source["birth"]["resources"][0]["room"] = json!(room);
    }
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
        "transclude" => {
            let host = os_string(args.required("name")?, "host name")?;
            let source = os_string(args.required("source")?, "source name")?;
            let from = os_string(args.required("from")?, "first atom")?;
            let to = os_string(args.required("to")?, "last atom")?;
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
            let room = match args.optional("in") {
                Some(value) => Some(os_string(value, "room name")?),
                None => None,
            };
            args.finish()?;
            create(&root, &workspace, &name, &storage, &predicate, room.as_deref())
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
        "doc-show" => {
            let name = os_string(args.required("name")?, "reference name")?;
            let at = args
                .optional("at")
                .map(|value| os_string(value, "height"))
                .transpose()?;
            args.finish()?;
            doc_show(&root, &workspace, &name, at.as_deref())
        }
        "doc-history" => {
            let name = os_string(args.required("name")?, "reference name")?;
            args.finish()?;
            doc_history(&root, &workspace, &name)
        }
        "doc-diff" => {
            let name = os_string(args.required("name")?, "reference name")?;
            let from = os_string(args.required("from")?, "height")?;
            let to = os_string(args.required("to")?, "height")?;
            args.finish()?;
            doc_diff(&root, &workspace, &name, &from, &to)
        }
        _ => Err(
            "workspace action must be init, import, list, describe, read, doc-backlinks, doc-links, doc-show, doc-history, doc-diff, doc-insert, doc-move, doc-remove, transclude, transclusions, follow, submit or recover".into(),
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let refusal = format!(
            "mini: host refused query; encoded refusal: 00ff{}",
            hex(b"history read refused: x")
        );
        assert!(history_refused(&refusal));
        assert!(!history_refused(
            "mini: host refused query; encoded refusal: 6f62736572766174696f6e"
        ));
        assert!(!history_refused("cannot run host"));
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
        assert!(content_actions(&json!([{"type":"tombstoneDocument","document":"1"}])).is_err());
        assert!(content_actions(&json!([{"type":"annotate","annotation":"1","atom":"2",
            "revision":"3","body":"00","extra":"4"}])).is_err());
        assert!(content_actions(&json!([{"type":"annotate","annotation":"1","atom":"2",
            "revision":"3","body":"00"}])).is_ok());
        assert!(content_actions(&json!([{"type":"quote","element":"1","link":"2",
            "reference":{}}])).is_err());
        assert!(content_actions(&json!([{"type":"transclude","transclusion":"1","link":"2",
            "request":{}}])).is_ok());
        assert!(content_actions(&json!([{"type":"unlink","link":"9"}])).is_ok());
        assert!(content_actions(&json!([{"type":"unlink","link":"9","before":"1"}])).is_err());
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
