//! Agent-fleet surface. One participant workspace is one agent, and its
//! account reference names the paying account and the grant that spends and
//! observes it. Every verb is a source-owned Mini operation: the Host plans a
//! fleet turn behind a signed observation of that account, custody signs the
//! exact header, the Host assembles and admits it, and the receipt is looked up
//! exactly. Topic events are read from the account's typed append-only event
//! stream by cursor. Nothing here decides admission or interprets a name.

use crate::workspace::{self, ImportInput, InitIdentity};
use crate::{
    absolute, decode_hex, hex, path, print_json, read_secret, session_invoke,
    sync_directory_ancestors, transport, Args, Result, SOCKET,
};
use ed25519_dalek::Signer;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::ffi::{OsStr, OsString};
use std::fs;
use std::path::{Path, PathBuf};

const FORMAT: &str = "minidregg-fleet-turn-custody-v1";
const LIMIT: usize = transport::HOST_MAX_FRAME - 1;
const MAX_TOPIC: usize = 64;
const MAX_PAYLOAD: usize = 16_384;

pub(crate) fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn text(value: OsString, label: &str) -> Result<String> {
    value
        .into_string()
        .map_err(|_| format!("{label} must be UTF-8"))
}

fn canonical_decimal(value: &str, label: &str) -> Result<()> {
    if value.is_empty()
        || value.len() > 80
        || value.starts_with('0') && value != "0"
        || !value.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(format!("{label} must be canonical decimal"));
    }
    Ok(())
}

pub(crate) fn field<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("fleet record lacks {key}"))
}

fn pair(first: &[u8], second: &[u8]) -> Result<Vec<u8>> {
    let length: u32 = first
        .len()
        .try_into()
        .map_err(|_| "fleet pair exceeds u32")?;
    let mut bytes = length.to_le_bytes().to_vec();
    bytes.extend_from_slice(first);
    bytes.extend_from_slice(second);
    if first.is_empty() || second.is_empty() || bytes.len() >= transport::HOST_MAX_FRAME {
        return Err("fleet pair exceeds Host bound or has an empty component".into());
    }
    Ok(bytes)
}

/// The Host's refusal frame is retained byte-exact; its text is shown only as
/// a diagnostic, never parsed into a decision.
fn reply(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [255, body @ ..] => {
            // The refusal frame is the Host's own encoded outcome; it is kept
            // as the Host's decision (the shell renders it through the Host),
            // never parsed here.
            crate::note_host_decision(crate::HostDecision::RefusedFrame {
                command: format!("fleet op{operation}"),
                byte: 255,
                encoded: body.to_vec(),
                decoded: None,
            });
            Err(format!("Host refused op{operation}: {}", String::from_utf8_lossy(body)))
        }
        [actual, body @ ..] if *actual == operation && !body.is_empty() => Ok(body),
        _ => Err(format!("fleet op{operation} returned an invalid frame")),
    }
}

fn retain_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    retain(path, &bytes)
}

fn retain(path: &Path, bytes: &[u8]) -> Result<()> {
    crate::fsio::retain_exact(path, bytes, || format!("retained fleet artifact changed: {}", path.display()))?;
    sync_directory_ancestors(path.parent().ok_or("fleet artifact lacks parent")?)
}


pub(crate) fn read_json(path: &Path) -> Result<Value> {
    workspace::bounded_json(path)
}

/// One Host session call whose exact frame is retained before its body is
/// interpreted.
fn invoke(agent: &Agent, directory: &Path, stem: &str, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
    let frame = session_invoke(&agent.host, &agent.socket, &agent.config, operation, payload)?;
    retain(&directory.join(format!("{stem}.frame")), &frame)?;
    let body = reply(&frame, operation)?.to_vec();
    retain(&directory.join(format!("{stem}.bin")), &body)?;
    Ok(body)
}

fn inspect(agent: &Agent, kind: &str, input: &Path, output: &Path) -> Result<Value> {
    if output.exists() {
        return read_json(output);
    }
    crate::inspect(&agent.host, &agent.config, kind, input, output)
}

pub(crate) struct Agent {
    pub(crate) root: PathBuf,
    workspace: Value,
    host: PathBuf,
    config: PathBuf,
    socket: PathBuf,
    subject: String,
}

pub(crate) fn agent(root: &Path) -> Result<Agent> {
    let root = absolute(root)?;
    let workspace = workspace::load(&root)?;
    let socket = SOCKET
        .get()
        .ok_or("fleet verbs require a workspace pinned to a persistent Host socket")?
        .clone();
    Ok(Agent {
        host: workspace::member_path(&workspace, "host")?,
        config: workspace::member_path(&workspace, "config")?,
        subject: workspace::member(&workspace, "subject")?.to_owned(),
        socket,
        workspace,
        root,
    })
}

/// The account reference: a discovery hint naming the paying account and the
/// grant the agent presents. Admission rechecks the grant and current law.
pub(crate) fn account(agent: &Agent, name: &str) -> Result<Value> {
    let reference = workspace::reference(&agent.root, name)?;
    if field(&reference, "kind")? != "account" {
        return Err(format!("reference {name} is not an account"));
    }
    Ok(reference)
}

/// A signed current observation of `reference` by this agent, retained in its
/// own workspace attempt. Returns the Host's account view and the signed bytes.
pub(crate) fn observe(agent: &Agent, reference: &Value) -> Result<(Value, Vec<u8>)> {
    let (view, _, signed) =
        workspace::signed_view(&agent.root, &agent.workspace, reference, "resource")?;
    let bytes = crate::agent_reserve::bounded(&signed, LIMIT)?;
    Ok((view, bytes))
}

/// The account view lists `[asset, balance]` pairs for the observed account.
pub(crate) fn balance(view: &Value, asset: &str) -> Option<String> {
    view.get("balances")?.as_array()?.iter().find_map(|entry| {
        let entry = entry.as_array()?;
        (entry.first()?.as_str()? == asset)
            .then(|| entry.get(1)?.as_str().map(str::to_owned))
            .flatten()
    })
}

pub(crate) fn tariff(agent: &Agent) -> Result<(String, String)> {
    let config: Value = serde_json::from_slice(&crate::agent_reserve::bounded(&agent.config, 65_536)?)
        .map_err(|error| error.to_string())?;
    let read = |key: &str| {
        config.get(key).and_then(|value| {
            value
                .as_str()
                .map(str::to_owned)
                .or_else(|| value.as_u64().map(|number| number.to_string()))
        })
    };
    Ok((
        read("tariffBase").ok_or("pinned config lacks tariffBase")?,
        read("asset").unwrap_or_else(|| "0".into()),
    ))
}

/// The finalized command may differ from the draft only in the fee the Host
/// fills from the pinned tariff and, when the draft left it zero, the next
/// topic position. Every other field is exactly what this agent drafted.
fn validate_plan(draft: &Value, plan: &Value, plan_bytes: &[u8], base: &str) -> Result<()> {
    if field(plan, "type")? != "fleet-turn-plan-v1" || field(plan, "canonical")? != hex(plan_bytes)
    {
        return Err("fleet Plan inspection differs from its exact bytes".into());
    }
    let command = &plan["command"];
    for key in ["subject", "payer", "spend", "nonce"] {
        if command.get(key) != draft.get(key) {
            return Err(format!("fleet Plan changed the drafted {key}"));
        }
    }
    if command.get("transfer") != draft.get("transfer") {
        return Err("fleet Plan changed the drafted transfer".into());
    }
    if field(command, "fee")? != base {
        return Err("fleet Plan fee differs from the pinned tariff base".into());
    }
    match (draft.get("publication"), command.get("publication")) {
        (Some(Value::Null), Some(Value::Null)) => {}
        (Some(drafted), Some(planned)) if drafted.is_object() && planned.is_object() => {
            for key in ["topic", "payload"] {
                if drafted.get(key) != planned.get(key) {
                    return Err(format!("fleet Plan changed the drafted publication {key}"));
                }
            }
            let sequence = field(planned, "sequence")?;
            canonical_decimal(sequence, "planned sequence")?;
            if field(drafted, "sequence")? != "0" && field(drafted, "sequence")? != sequence {
                return Err("fleet Plan changed the drafted sequence".into());
            }
            if sequence == "0" {
                return Err("fleet Plan left the topic position unassigned".into());
            }
        }
        _ => return Err("fleet Plan changed whether the turn publishes".into()),
    }
    let signing = &plan["signing"];
    if signing.get("decoded") != Some(&Value::Bool(true))
        || signing.get("canonical").and_then(Value::as_str) != plan.get("header").and_then(Value::as_str)
    {
        return Err("fleet Plan lacks one decoded canonical signing header".into());
    }
    Ok(())
}

pub(crate) fn confirmed(value: &Value) -> bool {
    value.get("type").and_then(Value::as_str) == Some("confirmed")
        && matches!(
            value.get("confirmation").and_then(Value::as_str),
            Some("installed" | "replayed" | "recoveredAfterUncertainResponse")
        )
}

fn receipt_of(value: &Value) -> Result<Value> {
    let mut receipt = serde_json::Map::new();
    for key in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        let item = field(value, key)?;
        canonical_decimal(item, key)?;
        receipt.insert(key.into(), json!(item));
    }
    Ok(Value::Object(receipt))
}

fn result(
    directory: &Path,
    verb: &str,
    plan: &Value,
    outcome: &Value,
    superseded: &[PathBuf],
) -> Result<Value> {
    let command = &plan["command"];
    let value = json!({"type":"minidregg-fleet-turn-result-v1","verb":verb,
        "replans":superseded.len().to_string(),"supersededAttempts":superseded,
        "confirmation":field(outcome,"confirmation")?,
        "receipt":receipt_of(outcome)?,
        "subject":command["subject"],"payer":command["payer"],"fee":command["fee"],
        "transfer":command["transfer"],
        "publication":command.get("publication").cloned().map(|p| if p.is_object() {
            json!({"topic":p["topic"],"sequence":p["sequence"],"payloadBytes":p["payloadBytes"]})
        } else { Value::Null }),
        "attempt":directory,"authority":"admitted-fleet-turn"});
    retain_json(&directory.join("result.json"), &value)?;
    Ok(value)
}

fn lookup_exact(agent: &Agent, directory: &Path, ingress: &[u8]) -> Result<Value> {
    let count = fs::read_dir(directory)
        .map_err(|error| error.to_string())?
        .filter_map(|entry| entry.ok())
        .filter(|entry| {
            let name = entry.file_name().to_string_lossy().into_owned();
            name.starts_with("lookup-") && name.ends_with(".frame")
        })
        .count();
    let stem = format!("lookup-{count:04}");
    invoke(agent, directory, &stem, 99, ingress)?;
    inspect(
        agent,
        "outcome",
        &directory.join(format!("{stem}.bin")),
        &directory.join(format!("{stem}.json")),
    )
}

/// The Host's own decoding of this attempt's plan refusal (op 96 answered
/// 255), or `None` when the plan frame is not a refusal. A `stale-root`
/// reason means the signed observation it was given is no longer current;
/// nothing was signed yet, so the attempt is decided and a fresh observation
/// re-plans it. The reason is read from the decoding, never from the text.
fn plan_refusal(agent: &Agent, directory: &Path) -> Result<Option<Value>> {
    let frame = crate::agent_reserve::bounded(&directory.join("plan.frame"), LIMIT)?;
    let [255, body @ ..] = frame.as_slice() else {
        return Ok(None);
    };
    retain(&directory.join("plan-refusal.bin"), body)?;
    let outcome = inspect(
        agent,
        "outcome",
        &directory.join("plan-refusal.bin"),
        &directory.join("plan-refusal.json"),
    )?;
    Ok((outcome.get("type").and_then(Value::as_str) == Some("refused")).then_some(outcome))
}

/// Did the Host refuse this attempt's signed observation `stale-root` (a
/// commit landed between its challenge and the signed query)? Read from the
/// decision the session recorded with the Host's own decoding. Only the read
/// was signed, so the turn re-plans. Any other decision is put back for the
/// caller's report.
fn observation_stale() -> bool {
    match crate::take_host_decision() {
        Some(crate::HostDecision::RefusedFrame { decoded: Some(outcome), .. })
            if outcome.get("reason").and_then(Value::as_str) == Some("stale-root") =>
        {
            true
        }
        Some(other) => {
            crate::note_host_decision(other);
            false
        }
        None => false,
    }
}

/// How many times a turn is re-planned after the Host reports contention.
const MAX_REPLANS: usize = 8;

/// A caller operation is an immutable, fsynced pointer into the existing
/// attempt store, not another submission journal. Creation wins exactly once.
/// A second invocation may look up this attempt but must never submit again.
pub(crate) fn operation_record(
    root: &Path, path: &Path, kind: &str, binding: Value,
) -> Result<(Value, bool)> {
    let root = fs::canonicalize(root).map_err(|e| e.to_string())?;
    let path = absolute(path)?;
    workspace::private_dir(path.parent().ok_or("operation record has no parent")?)?;
    // Every verb that reaches an operation record loaded this workspace (and
    // rechecked its key commitment) first; the record binds the same bytes.
    let ws = workspace::load_retained(&root)?.snapshot().clone();
    let config = fs::read(workspace::member_path(&ws, "config")?).map_err(|e| e.to_string())?;
    let identity = json!({"workspace":root,"participant":ws,"configSha256":digest(&config)});
    if path.exists() {
        let value = workspace::bounded_json(&path)?;
        validate_operation_binding(&value, kind, &identity, &binding)?;
        return Ok((value, false));
    }
    let (attempt, nonce) = workspace::new_attempt(&root)?;
    let value = json!({"type":"minidregg-exact-operation-v1","kind":kind,
        "identity":identity,"binding":binding,"attempt":attempt,"nonce":nonce});
    // create_new, file fsync and parent fsync: concurrent callers cannot both win.
    crate::create_private(&path, &serde_json::to_vec_pretty(&value).map_err(|e| e.to_string())?)?;
    sync_directory_ancestors(path.parent().ok_or("operation record has no parent")?)?;
    Ok((value, true))
}

fn validate_operation_binding(value: &Value, kind: &str, identity: &Value, binding: &Value) -> Result<()> {
    if value["type"] != "minidregg-exact-operation-v1" || value["kind"] != kind
        || value["identity"] != *identity || value["binding"] != *binding {
        return Err("operation record reuse differs in request, workspace, subject, authority or payer".into());
    }
    Ok(())
}

fn recovery_value(path: &Path, record: &Value, status: &str, outcome: Value) -> Value {
    json!({"type":"minidregg-operation-recovery-v1","operationRecord":path,
        "attempt":record["attempt"],"status":status,"outcome":outcome,
        "requiresSubmitterStopped":status == "not-submitted"})
}

fn retained_file(path: &Path) -> Result<bool> {
    match fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_file() => Ok(true),
        Ok(_) => Err(format!("{} is not a regular retained file", path.display())),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error.to_string()),
    }
}

fn exact_status(outcome: &Value) -> &'static str {
    if confirmed(outcome) && receipt_of(outcome).is_ok() { "confirmed" }
    else if matches!(outcome.get("type").and_then(Value::as_str), Some("refused" | "contention")) { "refused" }
    else { "uncertain" }
}

fn decided_outcome(path: &Path) -> Result<Option<Value>> {
    if !retained_file(path)? { return Ok(None); }
    let value = workspace::bounded_json(path)?;
    Ok((exact_status(&value) != "uncertain").then_some(value))
}

/// Resume a balance-derived operation before reading a new balance. The
/// caller's stable request context must still match; the original amount stays
/// in the immutable binding and is never recomputed for an existing record.
pub(crate) fn recover_bound_operation(root: &Path, path: &Path, context: &Value) -> Result<Option<Value>> {
    if !retained_file(path)? { return Ok(None); }
    let record = workspace::bounded_json(path)?;
    if record["binding"]["context"] != *context {
        return Err("operation record reuse differs in action, destination, room or account authority".into());
    }
    recover_operation(root, path).map(Some)
}

/// Read-only exact recovery. Absence of a retained signed call only proves
/// no submission AFTER the caller has stopped/reaped the original submitter.
/// A missing receipt never licenses a new payment or write.
pub(crate) fn recover_operation(root: &Path, path: &Path) -> Result<Value> {
    let record = workspace::bounded_json(path)?;
    let kind = field(&record, "kind")?;
    // Revalidate the pinned workspace/participant/config before contacting a host.
    operation_record(root, path, kind, record["binding"].clone())?;
    let attempt = PathBuf::from(field(&record, "attempt")?);
    let attempts = fs::canonicalize(root.join("attempts")).map_err(|e| e.to_string())?;
    if attempt.parent() != Some(attempts.as_path()) {
        return Err("operation attempt does not belong to the pinned workspace".into());
    }
    if kind == "no-effect" {
        let outcome = record["binding"].get("result").cloned()
            .unwrap_or_else(|| json!({"paid":false,"price":"0"}));
        return Ok(recovery_value(path, &record, "confirmed", outcome));
    }
    let present = match kind {
        "fleet" => retained_file(&attempt.join("submit-marker.json"))?,
        "workspace" => retained_file(&attempt.join("call.bin"))?,
        _ => return Err("unknown exact operation kind".into()),
    };
    if !present {
        return Ok(recovery_value(path, &record, "not-submitted", Value::Null));
    }
    let (outcome, submit_decision) = if kind == "fleet" {
        let (_, ingress) = retained_ingress_at(root, &attempt)?;
        // A received checked refusal/confirmation is already decisive. Otherwise
        // op 99 asks only about the exact retained ingress, never the text/memo.
        if let Some(value) = decided_outcome(&attempt.join("submit.json"))? { (value, true) }
        else {
            let agent = agent(root)?;
            (lookup_exact(&agent, &attempt, &ingress).unwrap_or(Value::Null), false)
        }
    } else {
        // recover uses lookup only, never retry/submit. Keep its signed call and
        // outcomes in the original attempt rather than searching any room feed.
        if let Some(value) = decided_outcome(&attempt.join("outcome.json"))? { (value, true) }
        else if let Some(value) = workspace::accepted_outcome(&attempt)? { (value, false) }
        else {
            let _ = workspace::recover(root, &attempt);
            let mut names = fs::read_dir(&attempt).map_err(|e| e.to_string())?
                .filter_map(|e| e.ok().map(|e| e.file_name().to_string_lossy().into_owned()))
                .filter(|n| n.starts_with("retry-") && n.ends_with(".json")).collect::<Vec<_>>();
            names.sort();
            (names.last().map(|n| workspace::bounded_json(&attempt.join(n))).transpose()?.unwrap_or(Value::Null), false)
        }
    };
    // A refusal of a lookup is not proof that the original submit was refused.
    let status = match exact_status(&outcome) {
        "refused" if !submit_decision => "uncertain",
        status => status,
    };
    Ok(recovery_value(path, &record, status, outcome))
}

/// Plan, sign, assemble and submit one fleet turn in a new private attempt.
/// The submit marker is durable before the one submission; after it, only the
/// read-only exact lookup of the same ingress is ever sent. `Ok(None)` is a
/// decided attempt that moved nothing: the Host's typed contention at submit,
/// or its `stale-root` refusal of the observation or the plan before the turn
/// was signed.
fn attempt(
    agent: &Agent,
    reference: &Value,
    verb: &str,
    transfer: &Value,
    publication: &Value,
    base: &str,
    pinned: Option<&Value>,
) -> Result<(PathBuf, Option<(Value, Value)>)> {
    let (directory, nonce) = match pinned {
        Some(record) => (PathBuf::from(field(record, "attempt")?), field(record, "nonce")?.to_owned()),
        None => workspace::new_attempt(&agent.root)?,
    };
    workspace::make_private_dir(&directory)?;
    let draft = json!({"subject":agent.subject,"payer":field(reference,"target")?,
        "spend":field(reference,"operationCapability")?,"nonce":nonce,"fee":"0",
        "transfer":transfer,"publication":publication});
    retain_json(&directory.join("draft.json"), &draft)?;
    crate::author(
        &agent.host,
        &agent.config,
        OsStr::new("fleet-turn"),
        &directory.join("draft.json"),
        &directory.join("draft.bin"),
    )?;
    let draft_bytes = crate::agent_reserve::bounded(&directory.join("draft.bin"), LIMIT)?;
    let draft_view = inspect(agent, "fleet-turn", &directory.join("draft.bin"), &directory.join("draft-inspected.json"))?;
    // A decision left by an earlier request must not be read as this one's.
    let _ = crate::take_host_decision();
    let (view, signed) = match observe(agent, reference) {
        Ok(observed) => observed,
        Err(error) => {
            if observation_stale() {
                retain_json(
                    &directory.join("superseded.json"),
                    &json!({"format":FORMAT,"reason":"stale-root-at-observation",
                        "status":"decided-nothing-signed"}),
                )?;
                return Ok((directory, None));
            }
            return Err(error);
        }
    };
    retain(&directory.join("signed-observation.bin"), &signed)?;
    retain_json(&directory.join("account-view.json"), &view)?;
    let plan = match invoke(agent, &directory, "plan", 96, &pair(&signed, &draft_bytes)?) {
        Ok(plan) => plan,
        Err(error) => match plan_refusal(agent, &directory)? {
            Some(refusal) if refusal.get("reason").and_then(Value::as_str) == Some("stale-root") => {
                retain_json(
                    &directory.join("superseded.json"),
                    &json!({"format":FORMAT,"reason":"stale-root-at-plan",
                        "status":"decided-nothing-signed"}),
                )?;
                return Ok((directory, None));
            }
            Some(refusal) => {
                return Err(format!(
                    "fleet {verb} {}; exact refusal retained in {}",
                    crate::refusal_line(&refusal).unwrap_or(error),
                    directory.display()
                ))
            }
            None => return Err(error),
        },
    };
    let plan_view = inspect(agent, "fleet-turn-plan", &directory.join("plan.bin"), &directory.join("plan.json"))?;
    validate_plan(&draft_view, &plan_view, &plan, base)?;
    let header = decode_hex(field(&plan_view, "header")?)?;
    let signing = read_secret(&workspace::member_path(&agent.workspace, "key")?)?;
    let signature = signing.sign(&header).to_bytes();
    retain(&directory.join("signature.bin"), &signature)?;
    let ingress = invoke(agent, &directory, "ingress", 97, &pair(&plan, &signature)?)?;
    let ingress_view = inspect(agent, "fleet-turn-ingress", &directory.join("ingress.bin"), &directory.join("ingress.json"))?;
    if field(&ingress_view, "canonical")? != hex(&ingress)
        || field(&ingress_view, "commandBytes")? != field(&plan_view, "commandBytes")?
    {
        return Err("assembled fleet ingress differs from the signed Plan".into());
    }
    retain_json(
        &directory.join("submit-marker.json"),
        &json!({"format":FORMAT,"operation":98,"verb":verb,
            "ingressSha256":digest(&ingress),"status":"may-have-submitted"}),
    )?;
    let outcome = match invoke(agent, &directory, "submit", 98, &ingress) {
        Ok(_) => inspect(agent, "outcome", &directory.join("submit.bin"), &directory.join("submit.json"))?,
        Err(error) => {
            eprintln!("fleet submit uncertain ({error}); exact lookup follows");
            lookup_exact(agent, &directory, &ingress)?
        }
    };
    if field(&outcome, "type")? == "contention" {
        retain_json(
            &directory.join("superseded.json"),
            &json!({"format":FORMAT,"reason":"contention","ingressSha256":digest(&ingress),
                "status":"decided-nothing-moved"}),
        )?;
        return Ok((directory, None));
    }
    let outcome = if confirmed(&outcome) {
        outcome
    } else if matches!(field(&outcome, "type")?, "uncertain" | "unavailable") {
        lookup_exact(agent, &directory, &ingress)?
    } else {
        outcome
    };
    if !confirmed(&outcome) {
        crate::note_host_decision(crate::HostDecision::Outcome(outcome.clone()));
        let detail = outcome
            .get("detail")
            .and_then(Value::as_str)
            .and_then(|value| decode_hex(value).ok())
            .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
            .unwrap_or_default();
        return Err(format!(
            "fleet {verb} not admitted ({}; {detail}); exact outcome retained in {}",
            field(&outcome, "type")?,
            directory.display()
        ));
    }
    Ok((directory, Some((plan_view, outcome))))
}

/// One fleet turn, re-planned in a fresh attempt only after typed contention.
/// Every superseded attempt is named in the result.
pub(crate) fn turn(agent: &Agent, reference: &Value, verb: &str, transfer: Value, publication: Value) -> Result<Value> {
    let (base, _) = tariff(agent)?;
    let mut superseded = Vec::new();
    for _ in 0..=MAX_REPLANS {
        let (directory, admitted) = attempt(agent, reference, verb, &transfer, &publication, &base, None)?;
        let Some((plan_view, outcome)) = admitted else {
            eprintln!("fleet {verb}: superseded (stale plan or contention); re-planning against the new image");
            superseded.push(directory);
            continue;
        };
        let value = result(&directory, verb, &plan_view, &outcome, &superseded)?;
        print_json(&value)?;
        return Ok(value);
    }
    Err(format!(
        "fleet {verb} still contended after {MAX_REPLANS} re-plans; each superseded attempt was decided and moved nothing"
    ))
}

pub(crate) fn topic_bytes(topic: &str) -> Result<Vec<u8>> {
    if topic.is_empty() || topic.len() > MAX_TOPIC {
        return Err("topic must be 1..64 bytes".into());
    }
    Ok(topic.as_bytes().to_vec())
}

fn payload_bytes(args: &mut Args) -> Result<Vec<u8>> {
    let bytes = match (args.optional("payload"), args.optional("payload-hex")) {
        (Some(text_value), None) => text(text_value, "payload")?.into_bytes(),
        (None, Some(hex_value)) => decode_hex(&text(hex_value, "payload hex")?)?,
        _ => return Err("give exactly one of --payload or --payload-hex".into()),
    };
    if bytes.len() > MAX_PAYLOAD {
        return Err("payload exceeds 16384 bytes".into());
    }
    Ok(bytes)
}

pub(crate) fn transfer_value(to: &str, amount: &str, asset: &str) -> Result<Value> {
    canonical_decimal(to, "--to account")?;
    canonical_decimal(amount, "--amount")?;
    canonical_decimal(asset, "--asset")?;
    if amount == "0" {
        return Err("a transfer moves a positive amount".into());
    }
    Ok(json!({"destination":to,"asset":asset,"amount":amount}))
}

/// The retained exact ingress of one of this workspace's attempts, checked
/// against the digest its submit marker recorded before the one submission.
fn retained_ingress(agent: &Agent, directory: &Path) -> Result<(PathBuf, Vec<u8>)> {
    retained_ingress_at(&agent.root, directory)
}

fn retained_ingress_at(root: &Path, directory: &Path) -> Result<(PathBuf, Vec<u8>)> {
    let directory = absolute(directory)?;
    let attempts = fs::canonicalize(root.join("attempts")).map_err(|error| error.to_string())?;
    let canonical = fs::canonicalize(&directory).map_err(|error| error.to_string())?;
    if canonical.parent() != Some(attempts.as_path()) {
        return Err("fleet attempt must belong to this workspace".into());
    }
    let marker = read_json(&canonical.join("submit-marker.json"))?;
    let ingress = crate::agent_reserve::bounded(&canonical.join("ingress.bin"), LIMIT)?;
    if field(&marker, "ingressSha256")? != digest(&ingress) {
        return Err("retained fleet ingress differs from its submit marker".into());
    }
    Ok((canonical, ingress))
}

/// Exact resubmission: the SAME retained ingress bytes go to the checked
/// submit (op 98) again. The receiver looks the operation identity up before
/// admission, so an accepted original answers `replayed` with its original
/// receipt and nothing moves twice; a never-accepted one is admitted now.
pub(crate) fn resubmit(agent: &Agent, directory: &Path) -> Result<Value> {
    let (canonical, ingress) = retained_ingress(agent, directory)?;
    let count = fs::read_dir(&canonical)
        .map_err(|error| error.to_string())?
        .filter_map(|entry| entry.ok())
        .filter(|entry| {
            let name = entry.file_name().to_string_lossy().into_owned();
            name.starts_with("resubmit-") && name.ends_with(".frame")
        })
        .count();
    let stem = format!("resubmit-{count:04}");
    invoke(agent, &canonical, &stem, 98, &ingress)?;
    inspect(
        agent,
        "outcome",
        &canonical.join(format!("{stem}.bin")),
        &canonical.join(format!("{stem}.json")),
    )
}

/// Receipt-only exact lookup of one retained fleet attempt.
fn lookup(agent: &Agent, directory: &Path) -> Result<()> {
    let (canonical, ingress) = retained_ingress(agent, directory)?;
    let outcome = lookup_exact(agent, &canonical, &ingress)?;
    print_json(&outcome)?;
    if !confirmed(&outcome) {
        return Err(format!("fleet lookup found {}", field(&outcome, "type")?));
    }
    Ok(())
}

/// The Host's answer to op 102 for one transaction id, uninterpreted.
pub(crate) fn receipt_by_transaction(agent: &Agent, transaction: &str) -> Result<Value> {
    canonical_decimal(transaction, "--transaction")?;
    let frame = session_invoke(&agent.host, &agent.socket, &agent.config, 102, transaction.as_bytes())?;
    let body = reply(&frame, 102)?;
    serde_json::from_slice(body).map_err(|error| error.to_string())
}

fn by_transaction(agent: &Agent, transaction: &str) -> Result<()> {
    let value = receipt_by_transaction(agent, transaction)?;
    print_json(&value)?;
    match field(&value, "type")? {
        "confirmed" if field(&value["receipt"], "transactionId")? == transaction => Ok(()),
        "confirmed" => Err("receipt lookup answered for another transaction".into()),
        other => Err(format!("no accepted transaction {transaction} ({other})")),
    }
}

/// The agent head (op 101) of `reference`, behind this agent's signed observation.
pub(crate) fn head_of(agent: &Agent, reference: &Value) -> Result<Value> {
    let (_, signed) = observe(agent, reference)?;
    let frame = session_invoke(&agent.host, &agent.socket, &agent.config, 101, &signed)?;
    let value: Value =
        serde_json::from_slice(reply(&frame, 101)?).map_err(|error| error.to_string())?;
    if field(&value, "payer")? != field(reference, "target")? {
        return Err("agent head answered for another account".into());
    }
    Ok(value)
}

fn head(agent: &Agent, reference: &Value) -> Result<()> {
    print_json(&head_of(agent, reference)?)
}

/// Events of one account topic after `since`. Each event's payload is present
/// only when the accepted ingress reproduces the digest its entry committed; an
/// event without one is reported and fails the poll rather than being skipped.
fn poll(agent: &Agent, reference: &Value, topic: &str, since: &str, limit: &str) -> Result<()> {
    let (value, unreadable) = poll_value(agent, reference, topic, since, limit)?;
    print_json(&value)?;
    if unreadable > 0 {
        return Err(format!("{unreadable} topic event(s) lack a payload matching their committed digest"));
    }
    Ok(())
}

/// One topic, several authors, ONE ordered feed. Each account's topic is its
/// own stream (its writers never contend with another account's); the Host
/// stamps every event with its admission height, unique per accepted record, so
/// the streams merge into one total order by `(height, sequence)`. Every stream
/// is read from its start, page by page, behind this agent's own signed
/// observation of that account.
fn feed(agent: &Agent, names: &[String], topic: &str) -> Result<()> {
    let mut events = Vec::new();
    let mut streams = Vec::new();
    let mut unreadable = 0usize;
    for name in names {
        let reference = account(agent, name)?;
        let mut since = "0".to_owned();
        loop {
            let (page, missing) = poll_value(agent, &reference, topic, &since, "64")?;
            unreadable += missing;
            let next = field(&page, "nextCursor")?.to_owned();
            let batch = page["events"].as_array().cloned().unwrap_or_default();
            for mut event in batch {
                event["account"] = json!(name);
                event["payer"] = page["payer"].clone();
                events.push(event);
            }
            if next == since {
                streams.push(json!({"account":name,"payer":page["payer"],"stream":page["stream"],
                    "head":page["head"],"tail":page["tail"]}));
                break;
            }
            since = next;
        }
    }
    let key = |event: &Value| -> Result<(u128, u128)> {
        Ok((
            field(event, "height")?.parse::<u128>().map_err(|error| error.to_string())?,
            field(event, "sequence")?.parse::<u128>().map_err(|error| error.to_string())?,
        ))
    };
    let mut keyed = events.into_iter().map(|event| key(&event).map(|k| (k, event))).collect::<Result<Vec<_>>>()?;
    keyed.sort_by(|left, right| left.0.cmp(&right.0));
    if keyed.windows(2).any(|pair| pair[0].0 .0 == pair[1].0 .0) {
        return Err("two topic events claim one admission height".into());
    }
    print_json(&json!({"type":"minidregg-fleet-topic-feed-v1","topic":hex(&topic_bytes(topic)?),
        "topicText":topic,"streams":streams,
        "events":keyed.into_iter().map(|(_, event)| event).collect::<Vec<_>>()}))?;
    if unreadable > 0 {
        return Err(format!("{unreadable} topic event(s) lack a payload matching their committed digest"));
    }
    Ok(())
}

fn poll_value(agent: &Agent, reference: &Value, topic: &str, since: &str, limit: &str) -> Result<(Value, usize)> {
    canonical_decimal(since, "--since")?;
    canonical_decimal(limit, "--limit")?;
    let topic = topic_bytes(topic)?;
    let (_, signed) = observe(agent, reference)?;
    let request = serde_json::to_vec(&json!({"topic":hex(&topic),"cursor":since,"limit":limit}))
        .map_err(|error| error.to_string())?;
    let frame = session_invoke(&agent.host, &agent.socket, &agent.config, 100, &pair(&signed, &request)?)?;
    let mut value: Value =
        serde_json::from_slice(reply(&frame, 100)?).map_err(|error| error.to_string())?;
    if field(&value, "payer")? != field(reference, "target")? || field(&value, "topic")? != hex(&topic)
    {
        return Err("topic poll answered for another stream".into());
    }
    let events = value["events"].as_array().cloned().unwrap_or_default();
    let first: u128 = since.parse::<u128>().map_err(|error| error.to_string())? + 1;
    let mut unreadable = 0usize;
    let mut rendered = Vec::new();
    for (expected, mut event) in (first..).zip(events) {
        let sequence = field(&event, "sequence")?.parse::<u128>().map_err(|error| error.to_string())?;
        if sequence != expected {
            return Err("topic poll returned a non-contiguous sequence".into());
        }
        match event.get("payload").and_then(Value::as_str) {
            Some(payload) => {
                let bytes = decode_hex(payload)?;
                if let Ok(text_value) = String::from_utf8(bytes) {
                    event["payloadText"] = json!(text_value);
                }
            }
            None => unreadable += 1,
        }
        rendered.push(event);
    }
    let next = rendered
        .last()
        .map(|event| field(event, "sequence").map(str::to_owned))
        .transpose()?
        .unwrap_or_else(|| since.to_owned());
    value["events"] = Value::Array(rendered);
    value["nextCursor"] = json!(next);
    value["topicText"] = json!(String::from_utf8_lossy(&topic));
    Ok((value, unreadable))
}

// ---------------------------------------------------------------- for `mini credit`

/// One paid fleet turn from this workspace's account reference `name`:
/// `amount` of `asset` (the pinned tariff asset when `None`) to account `to`,
/// publishing `payload` on `topic` of the paying account when given. The
/// result is the fleet turn result (`minidregg-fleet-turn-result-v1`), printed.
pub(crate) fn pay_turn(
    root: &Path,
    name: &str,
    to: &str,
    amount: &str,
    asset: Option<&str>,
    publication: Option<(&str, &[u8])>,
) -> Result<Value> {
    pay_turn_recorded(root, name, to, amount, asset, publication, None, Value::Null)
}

pub(crate) fn pay_turn_recorded(
    root: &Path, name: &str, to: &str, amount: &str, asset: Option<&str>,
    publication: Option<(&str, &[u8])>, operation: Option<&Path>, context: Value,
) -> Result<Value> {
    let agent = agent(root)?;
    let reference = account(&agent, name)?;
    let asset = match asset {
        Some(asset) => asset.to_owned(),
        None => tariff(&agent)?.1,
    };
    let transfer = transfer_value(to, amount, &asset)?;
    let publication = match publication {
        Some((topic, payload)) => {
            if payload.len() > MAX_PAYLOAD {
                return Err("payload exceeds 16384 bytes".into());
            }
            json!({"topic":hex(&topic_bytes(topic)?),"sequence":"0","payload":hex(payload)})
        }
        None => Value::Null,
    };
    let verb = if publication.is_null() { "transfer" } else { "send" };
    if let Some(path) = operation {
        let binding = json!({"reference":reference,"verb":verb,"transfer":transfer,"publication":publication,"context":context});
        let (record, fresh) = operation_record(root, path, "fleet", binding)?;
        if !fresh {
            let recovered = recover_operation(root, path)?;
            print_json(&recovered)?;
            if recovered["status"] != "confirmed" {
                return Err("recorded payment is not confirmed; exact recovery only".into());
            }
            let directory = PathBuf::from(field(&record, "attempt")?);
            if retained_file(&directory.join("result.json"))? {
                return read_json(&directory.join("result.json"));
            }
            let plan = read_json(&directory.join("plan.json"))?;
            return result(&directory, verb, &plan, &recovered["outcome"], &[]);
        }
        let base = tariff(&agent)?.0;
        match attempt(&agent, &reference, verb, &transfer, &publication, &base, Some(&record)) {
            Ok((directory, Some((plan, outcome)))) => {
                let value = result(&directory, verb, &plan, &outcome, &[])?;
                print_json(&value)?;
                Ok(value)
            }
            Ok(_) => Err("recorded payment was superseded without admission; exact recovery only".into()),
            Err(error) => Err(error),
        }
    } else {
        turn(&agent, &reference, verb, transfer, publication)
    }
}

/// The pinned tariff's per-turn fee (`tariffBase`).
pub(crate) fn tariff_base(root: &Path) -> Result<String> {
    Ok(tariff(&agent(root)?)?.0)
}

/// A signed current read of account reference `name`: (balance of the pinned
/// asset, the asset, the signed view's height, the account id).
pub(crate) fn account_balance(root: &Path, name: &str) -> Result<(String, String, String, String)> {
    let agent = agent(root)?;
    let reference = account(&agent, name)?;
    let (_, asset) = tariff(&agent)?;
    let (view, challenge, _) =
        workspace::signed_view(&agent.root, &agent.workspace, &reference, "resource")?;
    let height = field(&challenge, "height")?.to_owned();
    Ok((
        balance(&view, &asset).unwrap_or_else(|| "0".into()),
        asset,
        height,
        field(&reference, "target")?.to_owned(),
    ))
}

/// The incoming ledger of account reference `name` (Host op 180): accepted
/// fleet turns that paid it above `since`, on `topic` (empty = every topic),
/// behind this reader's signed observation of the account. Each entry gains
/// `payloadText` when its payload is UTF-8.
pub(crate) fn incoming(root: &Path, name: &str, topic: &str, since: &str, limit: &str) -> Result<Value> {
    canonical_decimal(since, "--since")?;
    canonical_decimal(limit, "--limit")?;
    if topic.len() > MAX_TOPIC {
        return Err("topic must be 0..64 bytes".into());
    }
    let agent = agent(root)?;
    let reference = account(&agent, name)?;
    let (_, signed) = observe(&agent, &reference)?;
    let request = serde_json::to_vec(&json!({"topic":hex(topic.as_bytes()),"cursor":since,"limit":limit}))
        .map_err(|error| error.to_string())?;
    let frame = session_invoke(&agent.host, &agent.socket, &agent.config, 180, &pair(&signed, &request)?)?;
    let mut value: Value =
        serde_json::from_slice(reply(&frame, 180)?).map_err(|error| error.to_string())?;
    if field(&value, "account")? != field(&reference, "target")? || field(&value, "topic")? != hex(topic.as_bytes()) {
        return Err("incoming ledger answered for another account or topic".into());
    }
    let floor: u128 = since.parse().map_err(|_| "--since out of range")?;
    let mut previous = floor;
    let mut entries = value["entries"].as_array().cloned().unwrap_or_default();
    for entry in &mut entries {
        let height: u128 = field(entry, "height")?.parse().map_err(|_| "ledger height out of range")?;
        if height <= previous {
            return Err("incoming ledger is not strictly ascending above the cursor".into());
        }
        previous = height;
        if let Ok(text_value) = String::from_utf8(decode_hex(field(entry, "payload")?)?) {
            entry["payloadText"] = json!(text_value);
        }
    }
    value["nextCursor"] = json!(previous.to_string());
    value["entries"] = Value::Array(entries);
    Ok(value)
}

/// Sponsor-backed join: admit the new key, open its workspace, and have the
/// sponsor create one account owned by the new subject and funded by a Book
/// posting from the sponsor's fee payer. Each step is resumable from its
/// retained artifacts; a completed step is never repeated.
pub(crate) fn join(mut args: Args) -> Result<()> {
    let sponsor_root = absolute(&path(args.required("sponsor-workspace")?))?;
    let factory_ref = text(args.required("factory-ref")?, "factory reference")?;
    let name = text(args.required("name")?, "join name")?;
    let new_key = absolute(&path(args.required("new-key")?))?;
    let enrollment_dir = absolute(&path(args.required("enroll-dir")?))?;
    let agent_root = absolute(&path(args.required("dir")?))?;
    let fund = text(args.required("fund")?, "--fund")?;
    let account_name = args
        .optional("account-name")
        .map(|value| text(value, "account name"))
        .transpose()?
        .unwrap_or_else(|| "account".into());
    args.finish()?;
    canonical_decimal(&fund, "--fund")?;
    let enrollment = enrollment_dir.join("enrollment.json");
    if !enrollment.exists() {
        let owned = |values: &[(&str, &OsStr)]| Args {
            command: OsString::from("enroll"),
            values: values
                .iter()
                .map(|(key, value)| (OsString::from(format!("--{key}")), value.to_os_string()))
                .collect(),
        };
        if !enrollment_dir.join("seal.json").exists() {
            crate::participant_enrollment::run(owned(&[
                ("action", OsStr::new("plan")),
                ("sponsor-workspace", sponsor_root.as_os_str()),
                ("factory-ref", OsStr::new(&factory_ref)),
                ("name", OsStr::new(&name)),
                ("new-key", new_key.as_os_str()),
                ("dir", enrollment_dir.as_os_str()),
            ]))?;
            crate::participant_enrollment::run(owned(&[
                ("action", OsStr::new("seal")),
                ("dir", enrollment_dir.as_os_str()),
            ]))?;
        }
        let action = if enrollment_dir.join("submit-marker.json").exists() {
            "lookup"
        } else {
            "submit"
        };
        crate::participant_enrollment::run(owned(&[
            ("action", OsStr::new(action)),
            ("dir", enrollment_dir.as_os_str()),
        ]))?;
    }
    let admitted = read_json(&enrollment)?;
    let subject = field(&admitted, "subject")?.to_owned();
    let sponsor_workspace = workspace::load(&sponsor_root)?;
    if !agent_root.join("workspace.json").exists() {
        workspace::init(
            &agent_root,
            Some(&workspace::member_path(&sponsor_workspace, "host")?),
            &workspace::member_path(&sponsor_workspace, "config")?,
            InitIdentity {
                key: None,
                subject: None,
                enrollment: Some(&enrollment),
                next_public: None,
                without_prerotation: false,
            },
            None,
            Some(&workspace::member_path(&sponsor_workspace, "namespaceRoot")?),
        )?;
    }
    let handoff = workspace::create_funded_account(
        &sponsor_root,
        &sponsor_workspace,
        &format!("{name}-account"),
        &json!({"type":"all","predicates":[]}),
        &subject,
        &fund,
    )?;
    if field(&handoff, "owner")? != subject {
        return Err("account handoff names another owner".into());
    }
    let agent_workspace = workspace::load(&agent_root)?;
    if !agent_root.join("refs").join(format!("{account_name}.json")).exists() {
        let provenance = sponsor_root
            .join("sources")
            .join(format!("create-{name}-account.handoff.json"));
        workspace::import(
            &agent_root,
            ImportInput {
                name: &account_name,
                kind: "account",
                target: field(&handoff, "target")?,
                observe: field(&handoff, "observeCapability")?,
                operation: Some(field(&handoff, "operationCapability")?),
                control: Some(field(&handoff, "controlCapability")?),
                provenance: Some(&provenance),
                room: None,
            },
        )?;
    }
    let reference = workspace::reference(&agent_root, &account_name)?;
    let joined = Agent {
        host: workspace::member_path(&agent_workspace, "host")?,
        config: workspace::member_path(&agent_workspace, "config")?,
        subject: subject.clone(),
        socket: SOCKET.get().ok_or("join requires a persistent Host socket")?.clone(),
        workspace: agent_workspace,
        root: agent_root.clone(),
    };
    let (view, _) = observe(&joined, &reference)?;
    let (_, asset) = tariff(&joined)?;
    let joined_record = json!({"type":"minidregg-fleet-join-v1","joined":true,
        "subject":subject,"publicKey":admitted["publicKey"],"workspace":agent_root,
        "account":field(&reference,"target")?,"spendCapability":field(&reference,"operationCapability")?,
        "controlCapability":reference["controlCapability"],
        "balance":balance(&view, &asset),
        "enrollmentReceipt":admitted["receipt"],
        "fundingReceipt":handoff["provenance"]["birthReceipt"],
        "authority":"admitted-key-and-owned-funded-account"});
    // The join record is retained beside the agent's workspace; the balance it
    // reports is the signed account view at join time.
    retain_json(&agent_root.join(format!("join-{account_name}.json")), &joined_record)?;
    print_json(&joined_record)
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = text(args.required("action")?, "fleet action")?;
    if action == "join" {
        return join(args);
    }
    let root = path(args.required("dir")?);
    let agent = agent(&root)?;
    match action.as_str() {
        "send" | "publish" => {
            let name = text(args.required("account")?, "account reference")?;
            let topic = text(args.required("topic")?, "topic")?;
            let payload = payload_bytes(&mut args)?;
            let to = args.optional("to").map(|value| text(value, "--to")).transpose()?;
            let amount = args
                .optional("amount")
                .map(|value| text(value, "--amount"))
                .transpose()?;
            let asset = args
                .optional("asset")
                .map(|value| text(value, "--asset"))
                .transpose()?;
            args.finish()?;
            let reference = account(&agent, &name)?;
            let transfer = match (to, amount) {
                (None, None) => Value::Null,
                (Some(to), Some(amount)) => {
                    let asset = match asset {
                        Some(asset) => asset,
                        None => tariff(&agent)?.1,
                    };
                    transfer_value(&to, &amount, &asset)?
                }
                _ => return Err("a paid send needs both --to and --amount".into()),
            };
            let publication = json!({"topic":hex(&topic_bytes(&topic)?),"sequence":"0",
                "payload":hex(&payload)});
            turn(&agent, &reference, &action, transfer, publication).map(|_| ())
        }
        "transfer" => {
            let name = text(args.required("account")?, "account reference")?;
            let to = text(args.required("to")?, "--to")?;
            let amount = text(args.required("amount")?, "--amount")?;
            let asset = args
                .optional("asset")
                .map(|value| text(value, "--asset"))
                .transpose()?;
            args.finish()?;
            let reference = account(&agent, &name)?;
            let asset = match asset {
                Some(asset) => asset,
                None => tariff(&agent)?.1,
            };
            let transfer = transfer_value(&to, &amount, &asset)?;
            turn(&agent, &reference, "transfer", transfer, Value::Null).map(|_| ())
        }
        "lookup" => {
            let attempt = path(args.required("attempt")?);
            args.finish()?;
            lookup(&agent, &attempt)
        }
        "receipt" => {
            let transaction = args
                .optional("transaction")
                .map(|value| text(value, "--transaction"))
                .transpose()?;
            let head_of = args
                .optional("head-of")
                .map(|value| text(value, "--head-of"))
                .transpose()?;
            args.finish()?;
            match (transaction, head_of) {
                (Some(transaction), None) => by_transaction(&agent, &transaction),
                (None, Some(name)) => head(&agent, &account(&agent, &name)?),
                _ => Err("receipt needs exactly one of --transaction or --head-of".into()),
            }
        }
        "poll" => {
            let name = text(args.required("account")?, "account reference")?;
            let topic = text(args.required("topic")?, "topic")?;
            let since = args
                .optional("since")
                .map(|value| text(value, "--since"))
                .transpose()?
                .unwrap_or_else(|| "0".into());
            let limit = args
                .optional("limit")
                .map(|value| text(value, "--limit"))
                .transpose()?
                .unwrap_or_else(|| "64".into());
            args.finish()?;
            poll(&agent, &account(&agent, &name)?, &topic, &since, &limit)
        }
        "incoming" => {
            let name = text(args.required("account")?, "account reference")?;
            let topic = args
                .optional("topic")
                .map(|value| text(value, "topic"))
                .transpose()?
                .unwrap_or_default();
            let since = args
                .optional("since")
                .map(|value| text(value, "--since"))
                .transpose()?
                .unwrap_or_else(|| "0".into());
            let limit = args
                .optional("limit")
                .map(|value| text(value, "--limit"))
                .transpose()?
                .unwrap_or_else(|| "64".into());
            args.finish()?;
            print_json(&incoming(&agent.root, &name, &topic, &since, &limit)?)
        }
        "feed" => {
            let names = text(args.required("accounts")?, "account references")?;
            let topic = text(args.required("topic")?, "topic")?;
            args.finish()?;
            let names: Vec<String> = names.split(',').map(str::to_owned).collect();
            if names.iter().any(String::is_empty) {
                return Err("--accounts is a comma-separated list of account references".into());
            }
            feed(&agent, &names, &topic)
        }
        _ => Err("fleet action must be join, send, publish, transfer, lookup, receipt, poll, incoming or feed".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn draft() -> Value {
        json!({"subject":"7","payer":"7","spend":"41","nonce":"9","fee":"0",
            "transfer":null,"publication":{"topic":"6e657773","sequence":"0","payload":"6869"}})
    }

    fn plan(command: Value) -> Value {
        json!({"type":"fleet-turn-plan-v1","canonical":"aa","command":command,
            "header":"bb","signing":{"decoded":true,"canonical":"bb"}})
    }

    #[test]
    fn plan_may_fill_only_fee_and_next_position() {
        let mut command = draft();
        command["fee"] = json!("3");
        command["publication"]["sequence"] = json!("4");
        assert!(validate_plan(&draft(), &plan(command.clone()), &[0xaa], "3").is_ok());
        let mut changed = command.clone();
        changed["payer"] = json!("8");
        assert!(validate_plan(&draft(), &plan(changed), &[0xaa], "3").is_err());
        let mut payload = command.clone();
        payload["publication"]["payload"] = json!("00");
        assert!(validate_plan(&draft(), &plan(payload), &[0xaa], "3").is_err());
        assert!(validate_plan(&draft(), &plan(command.clone()), &[0xaa], "4").is_err());
        let mut unassigned = command;
        unassigned["publication"]["sequence"] = json!("0");
        assert!(validate_plan(&draft(), &plan(unassigned), &[0xaa], "3").is_err());
    }

    #[test]
    fn refusal_frames_never_read_as_success() {
        assert!(reply(&[255, b'x'], 98).is_err());
        assert!(reply(&[99, 1], 98).is_err());
        assert_eq!(reply(&[98, 1, 2], 98).unwrap(), &[1, 2]);
    }

    #[test]
    fn transfer_arguments_are_canonical_and_positive() {
        assert!(transfer_value("12", "0", "0").is_err());
        assert!(transfer_value("012", "5", "0").is_err());
        assert!(transfer_value("12", "5", "0").is_ok());
    }
}

#[cfg(test)]
mod exact_operation_tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    struct Fixture(PathBuf);
    impl Fixture {
        fn new() -> Self {
            let root = std::env::temp_dir().join(format!("mini-exact-operation-{}-{}", std::process::id(), workspace::random_nonce().unwrap()));
            workspace::make_private_dir(&root).unwrap();
            for name in ["refs", "attempts", "sources", "proposals", "operations"] {
                workspace::make_private_dir(&root.join(name)).unwrap();
            }
            crate::create_private(&root.join("config.json"), b"{}").unwrap();
            crate::create_private(&root.join("workspace.json"), &serde_json::to_vec(&json!({
                "type":"minidregg-participant-workspace-v1","subject":"7",
                "host":root.join("host"),"config":root.join("config.json"),"key":root.join("key"),
                "prerotation":false
            })).unwrap()).unwrap();
            Self(root)
        }
        fn record(&self, name: &str, kind: &str, binding: Value) -> (PathBuf, Value) {
            let path = self.0.join("operations").join(name);
            let (record, fresh) = operation_record(&self.0, &path, kind, binding).unwrap();
            assert!(fresh);
            (path, record)
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) { let _ = fs::remove_dir_all(&self.0); }
    }
    fn receipt() -> Value {
        json!({"type":"confirmed","confirmation":"replayed","transactionId":"31",
            "eventId":"32","acceptedCount":"1","worldRoot":"33"})
    }

    #[test]
    fn exact_operation_reuse_rejects_content_authority_and_payer_changes() {
        let f = Fixture::new();
        let binding = json!({"text":"same text","reference":{"target":"10","operationCapability":"11"},"payer":"12"});
        let (path, record) = f.record("write", "workspace", binding.clone());
        let (again, fresh) = operation_record(&f.0, &path, "workspace", binding.clone()).unwrap();
        assert!(!fresh);
        assert_eq!(record, again);
        for changed in [
            json!({"text":"different text","reference":{"target":"10","operationCapability":"11"},"payer":"12"}),
            json!({"text":"same text","reference":{"target":"10","operationCapability":"99"},"payer":"12"}),
            json!({"text":"same text","reference":{"target":"10","operationCapability":"11"},"payer":"99"}),
        ] {
            assert!(operation_record(&f.0, &path, "workspace", changed).is_err());
        }
        assert!(operation_record(&f.0, &path, "fleet", binding).is_err());
        assert_eq!(workspace::bounded_json(&path).unwrap(), record);
    }

    #[test]
    fn exact_operation_prior_same_text_receipt_does_not_confirm_new_write() {
        let f = Fixture::new();
        let binding = json!({"text":"same text","payer":"12"});
        let (_, old) = f.record("old", "workspace", binding.clone());
        let old_attempt = PathBuf::from(field(&old, "attempt").unwrap());
        workspace::make_private_dir(&old_attempt).unwrap();
        crate::create_private(&old_attempt.join("call.bin"), b"old signed call").unwrap();
        retain_json(&old_attempt.join("outcome.json"), &receipt()).unwrap();
        let (path, new) = f.record("new", "workspace", binding);
        let answer = recover_operation(&f.0, &path).unwrap();
        assert_ne!(new["attempt"], old["attempt"]);
        assert_eq!(answer["status"], "not-submitted");
        assert_eq!(answer["requiresSubmitterStopped"], true);
        assert!(answer["outcome"].is_null());
    }

    #[test]
    fn exact_operation_payment_and_write_have_separate_submission_boundaries() {
        let f = Fixture::new();
        let (payment, p) = f.record("payment", "fleet", json!({"memo":"g7","payer":"12"}));
        let payment_attempt = PathBuf::from(field(&p, "attempt").unwrap());
        workspace::make_private_dir(&payment_attempt).unwrap();
        // Even an unrelated workspace call file cannot mark a fleet submit.
        crate::create_private(&payment_attempt.join("call.bin"), b"not fleet ingress").unwrap();
        assert_eq!(recover_operation(&f.0, &payment).unwrap()["status"], "not-submitted");
        crate::create_private(&payment_attempt.join("ingress.bin"), b"signed payment ingress").unwrap();
        retain_json(&payment_attempt.join("submit-marker.json"), &json!({"status":"may-have-submitted","ingressSha256":digest(b"signed payment ingress")})).unwrap();
        retain_json(&payment_attempt.join("submit.json"), &receipt()).unwrap();
        assert_eq!(recover_operation(&f.0, &payment).unwrap()["status"], "confirmed");
        let (write, _) = f.record("write", "workspace", json!({"text":"g7"}));
        assert_eq!(recover_operation(&f.0, &write).unwrap()["status"], "not-submitted");
    }

    #[test]
    fn exact_operation_lost_reply_recovers_only_retained_call_without_resubmit() {
        let f = Fixture::new();
        let host = f.0.join("host");
        // The fake transport refuses every operation except lookup/inspect and
        // verifies the exact original call; no feed or text matching is possible.
        let script = r##"#!/bin/sh
case "$2" in
 lookup)
  test "$(cat "$3")" = 'signed-call-for-g7' || exit 70
  printf 'lookup\n' >> "$1.calls"
  printf '%s' '{"type":"confirmed","confirmation":"replayed","transactionId":"31","eventId":"32","acceptedCount":"1","worldRoot":"33"}' > "$4" ;;
 inspect) test "$3" = outcome || exit 71; cp "$4" "$5" ;;
 *) exit 72 ;;
esac
"##;
        crate::create_private(&host, script.as_bytes()).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let (path, record) = f.record("lost-reply", "workspace", json!({"text":"repeated text"}));
        let attempt = PathBuf::from(field(&record, "attempt").unwrap());
        workspace::make_private_dir(&attempt).unwrap();
        crate::create_private(&attempt.join("call.bin"), b"signed-call-for-g7").unwrap();
        retain_json(&attempt.join("attempt.json"), &json!({"format":"minidregg-resource-client-attempt-v1",
            "host":host,"config":f.0.join("config.json")})).unwrap();
        let answer = recover_operation(&f.0, &path).unwrap();
        assert_eq!(answer["status"], "confirmed");
        assert_eq!(answer["outcome"], receipt());
        assert_eq!(fs::read_to_string(f.0.join("config.json.calls")).unwrap(), "lookup\n");
        assert_eq!(fs::read(attempt.join("call.bin")).unwrap(), b"signed-call-for-g7");
        assert_eq!(recover_operation(&f.0, &path).unwrap()["status"], "confirmed");
        // The retained exact receipt answers a second recovery without another RPC.
        assert_eq!(fs::read_to_string(f.0.join("config.json.calls")).unwrap(), "lookup\n");
    }

    #[test]
    fn exact_operation_lookup_refusal_does_not_decide_original_submission() {
        let f = Fixture::new();
        let (path, record) = f.record("lookup-refused", "workspace", json!({"text":"g8"}));
        let attempt = PathBuf::from(field(&record, "attempt").unwrap());
        workspace::make_private_dir(&attempt).unwrap();
        crate::create_private(&attempt.join("call.bin"), b"signed call").unwrap();
        let refused = json!({"type":"refused","reason":"lookup-not-authorized"});
        // A prior lookup failed, and the next lookup is unavailable (no
        // transport manifest). Neither says whether the original call landed.
        retain_json(&attempt.join("retry-0001.json"), &refused).unwrap();
        assert_eq!(recover_operation(&f.0, &path).unwrap()["status"], "uncertain");
        // The same typed decision received from the original submit is decisive.
        retain_json(&attempt.join("outcome.json"), &refused).unwrap();
        assert_eq!(recover_operation(&f.0, &path).unwrap()["status"], "refused");
    }

    #[test]
    fn exact_operation_return_reuses_fixed_amount_and_bound_destination() {
        let f = Fixture::new();
        let context = json!({"action":"return","account":{"target":"12","operationCapability":"13"},"to":"14","room":null});
        let (path, record) = f.record("return", "fleet", json!({"context":context,"transfer":{"amount":"7","destination":"14"}}));
        // No balance lookup or recalculation: the host need not even be running.
        assert_eq!(recover_bound_operation(&f.0, &path, &context).unwrap().unwrap()["status"], "not-submitted");
        assert_eq!(workspace::bounded_json(&path).unwrap(), record);
        let mut changed = context.clone();
        changed["to"] = json!("99");
        assert!(recover_bound_operation(&f.0, &path, &changed).is_err());
        let outcome = json!({"type":"minidregg-hermes-return-v1","returned":"0","reason":"balance-does-not-cover-fee"});
        let (empty, _) = f.record("empty-return", "no-effect", json!({"context":context,"result":outcome}));
        assert_eq!(recover_bound_operation(&f.0, &empty, &context).unwrap().unwrap()["outcome"], outcome);
    }

    #[test]
    fn exact_operation_missing_or_malformed_receipt_stays_uncertain() {
        assert_eq!(exact_status(&json!({"type":"confirmed"})), "uncertain");
        assert_eq!(exact_status(&json!({"type":"confirmed","confirmation":"replayed"})), "uncertain");
        assert_eq!(exact_status(&json!({"type":"absent"})), "uncertain");
        assert_eq!(exact_status(&json!({"type":"unavailable"})), "uncertain");
        assert_eq!(exact_status(&json!({"type":"refused","reason":"stale-root"})), "refused");
    }
}
