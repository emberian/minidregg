//! Read-only proof that one retained ordinary room say was accepted.
//! Re-authoring and assembly use retained public bytes; this module never
//! loads a signing key, prepares a new plan, or submits a call. Cached JSON
//! inspections and receipts are deliberately not authorities.
use crate::{agent_reserve, fleet, workspace, Args, Result, SOCKET};
use serde_json::{json, Value};
use std::{collections::BTreeMap, ffi::OsStr, fs, path::Path};

const LIMIT: usize = crate::transport::HOST_MAX_FRAME - 1;

fn decode(bytes: &[u8]) -> Result<Value> {
    serde_json::from_slice(bytes).map_err(|e| e.to_string())
}
fn field<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    workspace::member(value, key)
}
fn decimal(value: &Value, key: &str) -> Result<String> {
    let text = field(value, key)?;
    if text.is_empty()
        || text.len() > 80
        || (text.starts_with('0') && text != "0")
        || !text.bytes().all(|b| b.is_ascii_digit())
    {
        return Err(format!("append proof {key} is not canonical decimal"));
    }
    Ok(text.to_owned())
}
fn only<'a>(value: &'a Value, key: &str) -> Result<&'a Value> {
    match value.get(key).and_then(Value::as_array).map(Vec::as_slice) {
        Some([one]) => Ok(one),
        _ => Err(format!("append proof requires exactly one {key}")),
    }
}
fn same(actual: &[u8], expected: &[u8], what: &str) -> Result<()> {
    if actual != expected {
        return Err(format!("append proof {what} differs from retained bytes"));
    }
    Ok(())
}

fn identity(record: &Value, root: &Path, ws: &Value, config: &[u8]) -> Result<()> {
    if record["type"] != "minidregg-exact-operation-v1"
        || record["kind"] != "workspace"
        || record["identity"]
            != json!({"workspace":root,"participant":ws,
            "configSha256":fleet::digest(config)})
    {
        return Err("append proof differs from current workspace identity/config".into());
    }
    Ok(())
}

/// Link the recorded user request to the command that the Host will encode.
/// Unknown/private plaintext is refused, rather than guessed from displayed text.
fn statement(record: &Value, intent: &Value, subject: &str) -> Result<Value> {
    let binding = &record["binding"];
    if !binding.get("privateRoom").is_some_and(Value::is_null) {
        return Err("append proof cannot establish opaque private-room plaintext".into());
    }
    let reference = &binding["reference"];
    let request = &binding["request"];
    if request["type"] != "minidregg-workspace-proposal-v1"
        || request["action"] != "invoke"
        || reference["type"] != "minidregg-participant-reference-v1"
        || reference["kind"] != "object"
    {
        return Err("append proof is not a recorded object invocation".into());
    }
    let requested = only(request, "targets")?;
    let payload = &requested["payload"];
    if requested["name"] != reference["name"] || payload["type"] != "append" {
        return Err("append proof request/reference mismatch".into());
    }
    let text_bytes = field(payload, "text")?.as_bytes();
    let say = decode(text_bytes)?;
    if say["type"] != "say" {
        return Err("append proof payload is not an ordinary say".into());
    }
    let text = field(&say, "text")?;
    let to = decimal(payload, "to")?;
    let reply = &payload["ref"];
    let cell = decimal(reply, "cell")?;
    let sequence = decimal(reply, "sequence")?;
    let command = &intent["purpose"]["draft"]["command"];
    if intent["subject"] != subject
        || command["subject"] != subject
        || intent["purpose"]["type"] != "prepare"
        || intent["purpose"]["draft"]["type"] != "invoke"
    {
        return Err("append proof intent subject or purpose mismatch".into());
    }
    let target = only(command, "targets")?;
    let actual = &target["payload"];
    if target["kind"] != "object"
        || target["schemaVersion"] != "1"
        || target["target"] != reference["target"]
        || target["capability"] != reference["operationCapability"]
        || target["observeCapability"] != reference["observeCapability"]
        || actual["type"] != "append"
        || actual["to"] != payload["to"]
        || actual["ref"] != payload["ref"]
        || actual["topic"] != payload["topic"]
    {
        return Err("append proof command differs from recorded stream/authority/reply".into());
    }
    let encoded = field(actual, "payload")?;
    let decoded = crate::decode_hex(encoded)?;
    if crate::hex(&decoded) != encoded {
        return Err("append proof payload hex is not canonical".into());
    }
    same(&decoded, text_bytes, "say payload")?;
    Ok(
        json!({"subject":subject,"stream":decimal(reference,"target")?,"to":to,
        "reply":{"cell":cell,"sequence":sequence},"text":text}),
    )
}

fn transport_binding(ws: &Value, manifest: &Value, attempt: &Path, selected: &Path) -> Result<()> {
    if manifest["format"] != "minidregg-resource-client-attempt-v1"
        || manifest["operation"] != "submit"
        || manifest["host"] != ws["host"]
        || manifest.get("hostSha256") != ws.get("hostSha256")
        || manifest["socket"] != ws["socket"]
        || field(manifest, "socket")? != selected.to_str().ok_or("socket is not UTF-8")?
        || workspace::member_path(manifest, "config")? != attempt.join("config.json")
    {
        return Err(
            "append proof immutable attempt transport differs from selected workspace".into(),
        );
    }
    Ok(())
}

fn receipt(outcome: &Value) -> Result<Value> {
    if !fleet::confirmed(outcome) {
        return Err("exact append lookup did not confirm acceptance".into());
    }
    let mut result = serde_json::Map::new();
    for key in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        result.insert(key.into(), json!(decimal(outcome, key)?));
    }
    Ok(Value::Object(result))
}

/// A new operation-owned evidence directory never changes the original attempt.
/// Preserve both successful and interrupted/failed proofs for later inspection.
fn sync_evidence(directory: &Path) -> Result<()> {
    for entry in fs::read_dir(directory).map_err(|e| e.to_string())? {
        let path = entry.map_err(|e| e.to_string())?.path();
        if !fs::symlink_metadata(&path)
            .map_err(|e| e.to_string())?
            .file_type()
            .is_file()
        {
            return Err("append proof evidence contains a non-regular file".into());
        }
        fs::File::open(&path)
            .and_then(|file| file.sync_all())
            .map_err(|e| e.to_string())?;
    }
    crate::sync_directory_ancestors(directory)
}

pub(crate) fn prove(root: &Path, record_path: &Path) -> Result<Value> {
    if !record_path.is_absolute() {
        return Err("operation-record must be absolute".into());
    }
    let root = fs::canonicalize(root).map_err(|e| e.to_string())?;
    if fs::canonicalize(record_path).map_err(|e| e.to_string())? != record_path {
        return Err("operation-record must be canonical and not a symlink".into());
    }
    let ws = workspace::load(&root)?;
    let host = workspace::workspace_host(&ws)?;
    let selected = SOCKET
        .get()
        .ok_or("append proof requires pinned Host socket")?;
    let host_sha = crate::host_image_sha256(&host)?;
    let config_path = workspace::member_path(&ws, "config")?;
    let config = agent_reserve::bounded(&config_path, LIMIT)?;
    let record_bytes = agent_reserve::private_bytes(record_path, LIMIT)?;
    let record = decode(&record_bytes)?;
    identity(&record, &root, &ws, &config)?;
    let attempt = workspace::member_path(&record, "attempt")?;
    let attempts = fs::canonicalize(root.join("attempts")).map_err(|e| e.to_string())?;
    if attempt.parent() != Some(attempts.as_path())
        || fs::canonicalize(&attempt).map_err(|e| e.to_string())? != attempt
    {
        return Err("append proof attempt is outside workspace custody".into());
    }
    if attempt.file_name().and_then(|n| n.to_str())
        != Some(format!("a-{}", decimal(&record, "nonce")?).as_str())
    {
        return Err("append proof attempt does not match operation nonce".into());
    }
    workspace::private_dir(&attempt)?;
    let mut originals = BTreeMap::new();
    for name in [
        "attempt.json",
        "config.json",
        "intent.json",
        "plan.bin",
        "transaction-signatures.bin",
        "call.bin",
    ] {
        originals.insert(
            name,
            agent_reserve::private_bytes(&attempt.join(name), LIMIT)?,
        );
    }
    let manifest = decode(&originals["attempt.json"])?;
    transport_binding(&ws, &manifest, &attempt, selected)?;
    same(&originals["config.json"], &config, "attempt config")?;
    let intent = decode(&originals["intent.json"])?;
    let statement = statement(&record, &intent, field(&ws, "subject")?)?;
    let name = record_path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or("operation record filename is not UTF-8")?;
    let evidence =
        record_path.with_file_name(format!("{name}.proof-{}", workspace::random_nonce()?));
    workspace::make_private_dir(&evidence)?;
    let result = (|| -> Result<Value> {
        crate::create_private(&evidence.join("operation-record.json"), &record_bytes)?;
        crate::create_private(
            &evidence.join("workspace.json"),
            &serde_json::to_vec_pretty(&ws).map_err(|e| e.to_string())?,
        )?;
        for (name, bytes) in &originals {
            crate::create_private(&evidence.join(name), bytes)?;
        }
        let command_json = evidence.join("command.json");
        crate::create_private(
            &command_json,
            &serde_json::to_vec(&intent["purpose"]["draft"]["command"])
                .map_err(|e| e.to_string())?,
        )?;
        let command_bin = evidence.join("command.bin");
        let pinned_config = evidence.join("config.json");
        crate::author(
            &host,
            &pinned_config,
            OsStr::new("resource"),
            &command_json,
            &command_bin,
        )?;
        let command_bytes = agent_reserve::bounded(&command_bin, LIMIT)?;
        let plan = crate::inspect(
            &host,
            &pinned_config,
            "plan",
            &evidence.join("plan.bin"),
            &evidence.join("fresh-plan.json"),
        )?;
        if plan["finalizedDraft"]["type"] != "invoke"
            || plan["finalizedDraft"]["command"] != crate::hex(&command_bytes)
        {
            return Err(
                "fresh plan does not contain the exact re-authored retained command".into(),
            );
        }
        let assembled = evidence.join("reassembled-call.bin");
        crate::host_files(
            &host,
            &pinned_config,
            &[
                Path::new("assemble"),
                &evidence.join("plan.bin"),
                &evidence.join("transaction-signatures.bin"),
                &assembled,
            ],
        )?;
        same(
            &agent_reserve::bounded(&assembled, LIMIT)?,
            &originals["call.bin"],
            "reassembled signed call",
        )?;
        let lookup_bin = evidence.join("lookup.bin");
        crate::host_files(
            &host,
            &pinned_config,
            &[Path::new("lookup"), &evidence.join("call.bin"), &lookup_bin],
        )?;
        let outcome = crate::inspect(
            &host,
            &pinned_config,
            "outcome",
            &lookup_bin,
            &evidence.join("fresh-lookup.json"),
        )?;
        let receipt = receipt(&outcome)?;
        // A caller never receives a proof over inputs that changed during its run.
        same(
            &agent_reserve::private_bytes(record_path, LIMIT)?,
            &record_bytes,
            "operation record",
        )?;
        if workspace::load(&root)? != ws || crate::host_image_sha256(&host)? != host_sha {
            return Err("append proof workspace or selected Host changed during proof".into());
        }
        same(
            &agent_reserve::bounded(&config_path, LIMIT)?,
            &config,
            "current config",
        )?;
        for (name, bytes) in &originals {
            same(
                &agent_reserve::private_bytes(&attempt.join(name), LIMIT)?,
                bytes,
                name,
            )?;
        }
        let mut hashes = serde_json::Map::new();
        for (name, bytes) in &originals {
            hashes.insert((*name).into(), json!(fleet::digest(bytes)));
        }
        hashes.insert(
            "operationRecord".into(),
            json!(fleet::digest(&record_bytes)),
        );
        hashes.insert("command".into(), json!(fleet::digest(&command_bytes)));
        hashes.insert(
            "lookup".into(),
            json!(fleet::digest(&agent_reserve::bounded(&lookup_bin, LIMIT)?)),
        );
        for name in [
            "operation-record.json",
            "workspace.json",
            "command.json",
            "command.bin",
            "fresh-plan.json",
            "reassembled-call.bin",
            "lookup.bin",
            "fresh-lookup.json",
        ] {
            hashes.insert(
                name.into(),
                json!(fleet::digest(&agent_reserve::bounded(
                    &evidence.join(name),
                    8 * crate::transport::HOST_MAX_FRAME
                )?)),
            );
        }
        let mut result = statement;
        let object = result.as_object_mut().ok_or("invalid proof statement")?;
        object.insert("type".into(), json!("minidregg-append-operation-proof-v1"));
        object.insert("operationRecord".into(), json!(record_path));
        object.insert("attempt".into(), json!(attempt));
        object.insert("evidenceDirectory".into(), json!(evidence));
        object.insert("receipt".into(), receipt);
        object.insert("artifactSha256".into(), Value::Object(hashes));
        object.insert("hostSha256".into(), json!(host_sha));
        object.insert("socket".into(), json!(selected));
        object.insert(
            "authority".into(),
            json!("exact-retained-signed-call-lookup"),
        );
        crate::create_private(
            &evidence.join("proof.json"),
            &serde_json::to_vec_pretty(&result).map_err(|e| e.to_string())?,
        )?;
        Ok(result)
    })();
    if let Err(error) = &result {
        let failure = json!({"type":"minidregg-append-operation-proof-failure-v1", "operationRecord":record_path,
            "evidenceDirectory":evidence, "error":error});
        crate::create_private(
            &evidence.join("failure.json"),
            &serde_json::to_vec_pretty(&failure).map_err(|e| e.to_string())?,
        )?;
    }
    sync_evidence(&evidence)?;
    result.map_err(|error| format!("{error}; retained proof evidence: {}", evidence.display()))
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let root = crate::path(args.required("dir")?);
    let record = crate::path(args.required("operation-record")?);
    args.finish()?;
    crate::print_json(&prove(&root, &record)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> (Value, Value) {
        let text = r#"{"type":"say","text":"done"}"#;
        let payload = json!({"type":"append","text":text,"to":"20","ref":{"cell":"99","sequence":"2"},"topic":""});
        let reference = json!({"type":"minidregg-participant-reference-v1","kind":"object","name":"lab-me","target":"77","operationCapability":"78","observeCapability":"79"});
        let record = json!({"binding":{"privateRoom":null,"reference":reference,"request":{"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"lab-me","payload":payload}]}}});
        let mut native_payload = payload.clone();
        native_payload.as_object_mut().unwrap().remove("text");
        native_payload["payload"] = json!(crate::hex(text.as_bytes()));
        let intent = json!({"subject":"8","purpose":{"type":"prepare","draft":{"type":"invoke","command":{"subject":"8","targets":[{"kind":"object","schemaVersion":"1","target":"77","capability":"78","observeCapability":"79","payload":native_payload}]}}}});
        (record, intent)
    }
    #[test]
    fn stable_identity_requires_command_agreement_not_numeric_feed_position() {
        let (record, intent) = fixture();
        let proof = statement(&record, &intent, "8").unwrap();
        assert_eq!(proof["reply"], json!({"cell":"99","sequence":"2"}));
        for pointer in [
            "/subject",
            "/purpose/draft/command/subject",
            "/purpose/draft/command/targets/0/target",
            "/purpose/draft/command/targets/0/capability",
            "/purpose/draft/command/targets/0/observeCapability",
            "/purpose/draft/command/targets/0/payload/to",
            "/purpose/draft/command/targets/0/payload/ref/cell",
            "/purpose/draft/command/targets/0/payload/ref/sequence",
        ] {
            let mut changed = intent.clone();
            *changed.pointer_mut(pointer).unwrap() = json!("100");
            assert!(statement(&record, &changed, "8").is_err(), "{pointer}");
        }
    }
    #[test]
    fn altered_plaintext_opaque_room_or_multiple_targets_cannot_prove_say() {
        let (record, intent) = fixture();
        let mut changed = intent.clone();
        changed["purpose"]["draft"]["command"]["targets"][0]["payload"]["payload"] =
            json!(crate::hex(br#"{"type":"say","text":"different"}"#));
        assert!(statement(&record, &changed, "8").is_err());
        let mut private = record.clone();
        private["binding"]["privateRoom"] = json!("sealed");
        assert!(statement(&private, &intent, "8").is_err());
        let mut multi = intent.clone();
        let target = multi["purpose"]["draft"]["command"]["targets"][0].clone();
        multi["purpose"]["draft"]["command"]["targets"]
            .as_array_mut()
            .unwrap()
            .push(target);
        assert!(statement(&record, &multi, "8").is_err());
    }
    #[test]
    fn identity_transport_and_receipt_fail_closed() {
        let ws = json!({"host":"/host","socket":"/socket","subject":"8"});
        let mut record = json!({"type":"minidregg-exact-operation-v1","kind":"workspace","identity":{"workspace":"/workspace","participant":ws,"configSha256":fleet::digest(b"config")}});
        assert!(identity(&record, Path::new("/workspace"), &ws, b"config").is_ok());
        assert!(identity(&record, Path::new("/workspace"), &ws, b"other").is_err());
        record["identity"]["participant"]["subject"] = json!("9");
        assert!(identity(&record, Path::new("/workspace"), &ws, b"config").is_err());
        let manifest = json!({"format":"minidregg-resource-client-attempt-v1","operation":"submit","host":"/host","socket":"/socket","config":"/attempt/config.json"});
        assert!(
            transport_binding(&ws, &manifest, Path::new("/attempt"), Path::new("/socket")).is_ok()
        );
        assert!(
            transport_binding(&ws, &manifest, Path::new("/attempt"), Path::new("/other")).is_err()
        );
        assert!(same(b"signed old", b"signed new", "call").is_err());
        assert!(receipt(&json!({"type":"confirmed","confirmation":"replayed"})).is_err());
        assert!(receipt(&json!({"type":"absent"})).is_err());
        assert!(receipt(&json!({"type":"confirmed","confirmation":"replayed","transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"})).is_ok());
    }
}
