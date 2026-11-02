//! `mini activity` — the kernel activity as signed native commands
//! (ops 210-214, `Kernel/ObjectiveActivityReceiver.lean`).
//!
//! `mini activity --action submit --workspace DIR --command FILE.json --out NEW_DIR
//!   [--prepare-only true]`
//!   FILE.json is the command's `turn` (`{"kind": "publish" | "create" | "birth" | "resolve" |
//!   "deliver" | "topUp" | "exhaust" | "abandon", ...}`,
//!   `Host/ObjectiveActivityJson.lean`).
//!   The workspace's subject signs; the nonce is fresh; the authority root is the
//!   one the public view (op 214) shows now. The Host authors the command (op 7
//!   `objective-activity`), plans it (op 210: the header binds the command and the
//!   outcome the kernel decides now, checked by the local consent provider), the
//!   workspace key signs the header, the Host assembles the ingress (op 211), and
//!   the ingress is retained under NEW_DIR before it is submitted (op 212). With
//!   `--prepare-only true` it is retained and not submitted.
//! `mini activity --action resubmit --workspace DIR --ingress FILE` submits the exact
//!   retained bytes again (a retry replays; another ingress of the same await conflicts).
//! `mini activity --action lookup --workspace DIR --ingress FILE` is the receipt-only
//!   lookup (op 213); absence never submits.
//! `mini activity --action view --workspace DIR [--request JSON]` prints the public
//!   view (op 214): `{cells: [id..], accounts: [id..], objects: [id..], pins: [pin..],
//!   births: [{object, transaction}..]}`.
//!
//! Every refusal is the Host's, by name (the kernel's reason, `notObjectHolder`,
//! `notAccountOwner`, a signature refusal).
use crate::agent_reserve::field;
use crate::*;
use serde_json::{json, Value};

pub(crate) struct Ws {
    pub(crate) root: PathBuf,
    pub(crate) host: PathBuf,
    socket: PathBuf,
    pub(crate) config: PathBuf,
    key: PathBuf,
    pub(crate) subject: String,
}

pub(crate) fn ws(root: PathBuf) -> Result<Ws> {
    let bytes = fs::read(root.join("workspace.json"))
        .map_err(|error| format!("activity: cannot read workspace.json: {error}"))?;
    if bytes.len() > 64 * 1024 {
        return Err("activity: workspace.json exceeds 64 KiB".into());
    }
    let pin: Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("activity: invalid workspace.json: {error}"))?;
    let host = PathBuf::from(field(&pin, "host")?);
    if let Some(sha) = pin.get("hostSha256").and_then(Value::as_str) {
        crate::pin_workspace_host(&host, sha)?;
    }
    let key = pin
        .get("key")
        .and_then(Value::as_str)
        .filter(|s| !s.is_empty())
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join("client.key"));
    Ok(Ws {
        host,
        socket: PathBuf::from(field(&pin, "socket")?),
        config: PathBuf::from(field(&pin, "config")?),
        key,
        subject: field(&pin, "subject")?.to_string(),
        root,
    })
}

/// One Host frame. For submit (212) and lookup (213) a marker reply (`NO_RECORD` 253 or
/// `HOST_OUTCOME` 255) IS the Host's encoded outcome: it is returned for the local codec to decode;
/// the decoded type is reported, never a refusal read from the byte. 254 is certain: never
/// forwarded. Elsewhere (authoring, planning, assembly: no state change) a marker stops the turn.
fn invoke(ws: &Ws, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
    let frame = session_invoke(&ws.host, &ws.socket, &ws.config, operation, payload)?;
    match frame.split_first() {
        Some((actual, body)) if *actual == operation && !body.is_empty() => Ok(body.to_vec()),
        Some((byte, body)) if crate::is_outcome_frame(*byte) && matches!(operation, 212 | 213) && !body.is_empty() => Ok(body.to_vec()),
        Some((254, body)) => Err(format!(
            "never forwarded: op{operation}: {}",
            String::from_utf8_lossy(&body[body.len().saturating_sub(600)..]).split_whitespace().collect::<Vec<_>>().join(" ")
        )),
        Some((byte, body)) if crate::is_outcome_frame(*byte) => Err(format!(
            "refused: op{operation}: {}",
            String::from_utf8_lossy(&body[body.len().saturating_sub(600)..])
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ")
        )),
        _ => Err(format!("activity: op{operation} returned an invalid frame")),
    }
}

fn with_kind(kind: &str, body: &[u8]) -> Vec<u8> {
    let mut payload = (kind.len() as u16).to_le_bytes().to_vec();
    payload.extend_from_slice(kind.as_bytes());
    payload.extend_from_slice(body);
    payload
}

fn author(ws: &Ws, kind: &str, value: &Value) -> Result<Vec<u8>> {
    invoke(ws, mini_sdk::host_operations::AUTHOR, &with_kind(kind, value.to_string().as_bytes()))
}

pub(crate) fn inspect(ws: &Ws, kind: &str, bytes: &[u8]) -> Result<Value> {
    serde_json::from_slice(&invoke(ws, mini_sdk::host_operations::INSPECT, &with_kind(kind, bytes))?)
        .map_err(|error| format!("activity: invalid Host inspection of {kind}: {error}"))
}

pub(crate) fn view(ws: &Ws, request: &Value) -> Result<Value> {
    serde_json::from_slice(&invoke(ws, mini_sdk::host_operations::ACTIVITY_VIEW, request.to_string().as_bytes())?)
        .map_err(|error| format!("activity: invalid view: {error}"))
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    crate::create_private(path, bytes)
}

fn authority_root(ws: &Ws) -> Result<String> {
    let current = view(ws, &json!({}))?;
    Ok(current.get("authorityRoot").and_then(Value::as_str).ok_or("activity: view lacks authorityRoot")?.to_owned())
}

/// The signed command for `turn` against `authority`. A non-invoke turn's `nonce` is its record's
/// (`turn_nonce`), never minted per attempt.
fn command_for(ws: &Ws, turn: &Value, authority: &str, nonce: Option<&str>) -> Result<Value> {
    // An invoke's nonce is its operation id, `turn.opId`: the caller names the operation in the turn it
    // writes before the first submit, and a retry resubmits the same turn. Minting one here, per attempt,
    // would make every retry a second invocation.
    Ok(if turn.get("kind").and_then(Value::as_str) == Some("invoke") {
        if turn.get("opId").and_then(Value::as_str).is_none() {
            return Err("activity: an invoke turn names its operation: turn.opId (a decimal string, minted once \
                        per operation and reused on every retry)".into());
        }
        json!({"subject": ws.subject, "expectedAuthorityRoot": authority, "turn": turn})
    } else {
        let nonce = nonce.ok_or("activity: a non-invoke turn is signed only under its record's nonce")?;
        json!({"subject": ws.subject, "nonce": nonce, "expectedAuthorityRoot": authority, "turn": turn})
    })
}

/// The nonce a non-invoke `turn` is signed under, from its record `WS/activity-operations/KEY-N.json`
/// (KEY the digest of the turn): a rerun of the same turn reuses the record, so it is never a
/// second operation (`topUp` twice, review §5.3). A record whose `out` retains a TRANSMITTED
/// ingress (the `submitted` marker, written before the send, or an outcome) is not signed again: an
/// undecided one is looked up or resubmitted exactly by its ingress; a decided one is followed only
/// by the member's decision (`again`). A record that never reached an ingress, or whose ingress was
/// assembled with `--prepare-only` and never submitted by this client, reuses its nonce: nothing
/// was sent, so there is nothing to decide, and the same nonce makes any later send of either
/// ingress one operation (the Host replays, it never charges twice).
fn turn_nonce(ws: &Ws, turn: &Value, out: &Path, again: bool) -> Result<Option<String>> {
    if turn.get("kind").and_then(Value::as_str) == Some("invoke") {
        return Ok(None);
    }
    let dir = ws.root.join("activity-operations");
    crate::fsio::ensure_private_dir(&dir)?;
    let key = &crate::fleet::digest(turn.to_string().as_bytes())[..16];
    let name = |n: u32| dir.join(format!("{key}-{n}.json"));
    let mut n = 0;
    while name(n + 1).exists() {
        n += 1;
    }
    let fresh = |n: u32| -> Result<Option<String>> {
        let nonce = crate::fsio::random_nonce()?;
        crate::fsio::retain_json(&name(n), &json!({"type":"minidregg-activity-operation-v1","turn":turn,"nonce":nonce,"out":out}))?;
        Ok(Some(nonce))
    };
    if n == 0 {
        return fresh(1);
    }
    let record: Value = serde_json::from_slice(&fs::read(name(n)).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
    let previous = PathBuf::from(field(&record, "out")?);
    let nonce = field(&record, "nonce")?.to_owned();
    if !previous.join("ingress.bin").is_file() {
        return Ok(Some(nonce));
    }
    if !previous.join(SUBMITTED).is_file() && !previous.join("outcome.json").is_file() {
        return Ok(Some(nonce));
    }
    let decided = fs::read(previous.join("outcome.json")).ok()
        .and_then(|b| serde_json::from_slice::<Value>(&b).ok())
        .and_then(|o| o.get("type").and_then(Value::as_str).map(str::to_owned));
    match (decided.as_deref(), again) {
        (Some("confirmed" | "refused"), true) => fresh(n + 1),
        (Some(kind @ ("confirmed" | "refused")), false) => Err(format!(
            "activity: this turn was already submitted ({kind}; {}); a second one is your decision: --again true",
            previous.display())),
        _ => Err(format!(
            "undecided: this turn's exact ingress is retained at {} and may have been admitted; nothing new is signed: \
             `mini activity --action lookup --workspace WS --ingress {}` (or `--action resubmit`, the same bytes)",
            previous.display(), previous.join("ingress.bin").display())),
    }
}

/// Author and plan `command` (frame 210) and inspect the plan; retains command.json, command.bin and
/// plan.bin under `out`.
fn plan_command(ws: &Ws, command: &Value, out: &Path) -> Result<(Vec<u8>, Value)> {
    write_new(&out.join("command.json"), command.to_string().as_bytes())?;
    let command_bytes = author(ws, "objective-activity", command)?;
    write_new(&out.join("command.bin"), &command_bytes)?;
    let plan = invoke(ws, mini_sdk::host_operations::ACTIVITY_PLAN, &command_bytes)?;
    write_new(&out.join("plan.bin"), &plan)?;
    let inspected = inspect(ws, "objective-activity-plan", &plan)?;
    Ok((plan, inspected))
}

/// How an invoke learns the front-end work it declares (GPT-6 row E): plan it with an affordable
/// budget in its envelope and postage, doubling while the plan runs out of it, up to the ceiling; then
/// declare the plan's `frontEnd` in the envelope and `postageLoads` times its postage figures in the
/// postage. The caller (activity_world.py `front_end_quote`) chooses the start, ceiling and loads.
pub(crate) struct FrontEndQuote {
    start: (u128, u128),
    ceiling: (u128, u128),
    loads: u128,
}

fn decimal_member(value: &Value, key: &str) -> Result<u128> {
    match value.get(key) {
        Some(Value::String(text)) => text.parse().map_err(|_| format!("activity: {key} is not a decimal")),
        Some(Value::Number(number)) => number.as_u64().map(u128::from).ok_or(format!("activity: {key} is not a natural")),
        _ => Err(format!("activity: {key} missing")),
    }
}

impl FrontEndQuote {
    fn parse(text: &str) -> Result<Self> {
        let value: Value = serde_json::from_str(text).map_err(|error| format!("activity: invalid front-end quote: {error}"))?;
        Ok(Self {
            start: (decimal_member(&value, "replayBytes")?, decimal_member(&value, "coreBytes")?),
            ceiling: (decimal_member(&value, "ceilingReplayBytes")?, decimal_member(&value, "ceilingCoreBytes")?),
            loads: decimal_member(&value, "postageLoads")?,
        })
    }
}

/// Plans `turn` under the quote's budgets until the plan no longer runs out of front end (or the budget
/// is the ceiling), then writes the declaration into `turn`. Each plan is retained under
/// `out/front-end-plan-N`; the declared turn and the planned front end are retained as
/// `out/declared.json` and `out/front-end.json` before anything else is attempted, so a caller sees
/// them even when the submission that follows fails. Returns (planned frontEnd, plans made).
fn quote_front_end(ws: &Ws, turn: &mut Value, authority: &str, quote: &FrontEndQuote, out: &Path) -> Result<(Value, usize)> {
    let mut budget = quote.start;
    let mut attempt = 0;
    let planned = loop {
        let mut probe = turn.clone();
        for key in ["envelope", "postage"] {
            if let Some(slot) = probe.get_mut(key).and_then(Value::as_object_mut) {
                slot.insert("replayBytes".into(), json!(budget.0.to_string()));
                slot.insert("coreBytes".into(), json!(budget.1.to_string()));
            }
        }
        let directory = out.join(format!("front-end-plan-{attempt}"));
        fs::create_dir(&directory).map_err(|error| format!("activity: cannot create {}: {error}", directory.display()))?;
        let (_, inspected) = plan_command(ws, &command_for(ws, &probe, authority, None)?, &directory)?;
        let planned = inspected.get("frontEnd").filter(|value| value.is_object()).cloned()
            .ok_or_else(|| format!("activity: the plan reported no front end: {inspected}"))?;
        let verdict = inspected.get("verdict").map(Value::to_string).unwrap_or_default();
        let short = verdict.contains("frontEndExhausted") || verdict.contains("postageFrontEnd");
        if !short || budget == quote.ceiling {
            break planned;
        }
        budget = ((2 * budget.0).min(quote.ceiling.0), (2 * budget.1).min(quote.ceiling.1));
        attempt += 1;
    };
    let envelope = turn.get_mut("envelope").and_then(Value::as_object_mut).ok_or("activity: an invoke carries an envelope")?;
    envelope.insert("replayBytes".into(), json!(decimal_member(&planned, "replayBytes")?.to_string()));
    envelope.insert("coreBytes".into(), json!(decimal_member(&planned, "coreBytes")?.to_string()));
    if let Some(postage) = turn.get_mut("postage").and_then(Value::as_object_mut) {
        postage.insert("replayBytes".into(), json!((quote.loads * decimal_member(&planned, "postageReplayBytes")?).to_string()));
        postage.insert("coreBytes".into(), json!((quote.loads * decimal_member(&planned, "postageCoreBytes")?).to_string()));
    }
    write_new(&out.join("declared.json"), turn.to_string().as_bytes())?;
    write_new(&out.join("front-end.json"), planned.to_string().as_bytes())?;
    Ok((planned, attempt + 1))
}

fn create_out(out: &Path) -> Result<()> {
    fs::create_dir(out).map_err(|error| format!("activity: cannot create {}: {error}", out.display()))
}

/// The attempt's pre-send marker: written (durably) before its ingress is first submitted, by
/// `submit` or by a `resubmit` of the attempt's own `ingress.bin`, so a crash after the send leaves
/// an attempt that reads as transmitted (undecided until looked up), and an attempt without it was
/// never sent by this client (`turn_nonce`).
const SUBMITTED: &str = "submitted";

fn mark_submitted(dir: &Path) -> Result<()> {
    if dir.join(SUBMITTED).exists() {
        return Ok(());
    }
    write_new(&dir.join(SUBMITTED), b"")
}

/// Quote only: the declaration an invoke would carry (`quote_front_end`), nothing signed or submitted.
fn quote(ws: &Ws, turn: &Value, out: &Path, front_end: &FrontEndQuote) -> Result<Value> {
    create_out(out)?;
    let authority = authority_root(ws)?;
    let mut turn = turn.clone();
    let (planned, plans) = quote_front_end(ws, &mut turn, &authority, front_end, out)?;
    Ok(json!({"type": "quoted", "declared": turn, "planned": planned, "plans": plans}))
}

/// With `front_end`, the invoke is first quoted (`quote_front_end`) in this same process and the
/// declared turn is what is signed and submitted.
pub(crate) fn submit(ws: &Ws, turn: &Value, out: &Path, prepare_only: bool, front_end: Option<&FrontEndQuote>, again: bool) -> Result<Value> {
    let nonce = turn_nonce(ws, turn, out, again)?;
    create_out(out)?;
    let authority = authority_root(ws)?;
    let mut turn = turn.clone();
    let quoted = match front_end {
        Some(front_end) => Some(quote_front_end(ws, &mut turn, &authority, front_end, out)?),
        None => None,
    };
    let (plan, inspected) = plan_command(ws, &command_for(ws, &turn, &authority, nonce.as_deref())?, out)?;
    let canonical = inspected.pointer("/header/canonical").and_then(Value::as_str)
        .ok_or("activity: plan lacks a header")?;
    let header = mini_sdk::hex::decode(canonical).map_err(|error| format!("activity: {error}"))?;
    let signature = crate::fsio::read_secret_in_private_dir(&ws.key)?.sign(&header).to_bytes();
    let ingress = invoke(ws, mini_sdk::host_operations::ACTIVITY_ASSEMBLE, &mini_sdk::local::pair(&plan, &signature)?)?;
    write_new(&out.join("ingress.bin"), &ingress)?;
    let transaction = inspected.pointer("/command/transaction").cloned().unwrap_or(Value::Null);
    // What the decided turn returns (an invocation's result), shown before signing; null otherwise.
    let report = inspected.get("report").cloned().unwrap_or(Value::Null);
    // What a submission at the planning snapshot commits: null when admitted, `charged failure: ...`
    // (only the envelope's price is posted) or `refused: ...` (GPT-6 row E).
    let verdict = inspected.get("verdict").cloned().unwrap_or(Value::Null);
    // The front-end work the decided turn's replays drew (`{replayBytes, coreBytes}`): what an
    // invocation declares (plan over a generous envelope, declare this, plan again; GPT-6 row E).
    let front_end = inspected.get("frontEnd").cloned().unwrap_or(Value::Null);
    let mut outcome = if prepare_only {
        json!({"type": "prepared", "ingress": out.join("ingress.bin"), "transaction": transaction,
            "report": report, "verdict": verdict, "frontEnd": front_end})
    } else {
        mark_submitted(out)?;
        let mut outcome = inspect(ws, "outcome", &invoke(ws, mini_sdk::host_operations::ACTIVITY_SUBMIT, &ingress)?)?;
        write_new(&out.join("outcome.json"), outcome.to_string().as_bytes())?;
        outcome["transaction"] = transaction;
        outcome["report"] = report;
        outcome["verdict"] = verdict;
        outcome["frontEnd"] = front_end;
        outcome["ingress"] = json!(out.join("ingress.bin"));
        outcome
    };
    if let Some((planned, plans)) = quoted {
        outcome["declared"] = turn;
        outcome["planned"] = planned;
        outcome["plans"] = json!(plans);
    }
    Ok(outcome)
}

fn read_ingress(path: &Path) -> Result<Vec<u8>> {
    fs::read(path).map_err(|error| format!("activity: cannot read {}: {error}", path.display()))
}

/// Whether `ingress` is an attempt's OWN `ingress.bin` (its `plan.bin` beside it): a copy or a
/// forged ingress elsewhere neither marks nor decides any attempt.
fn own_attempt(ingress: &Path) -> Option<&Path> {
    let dir = ingress.parent()?;
    (ingress.file_name() == Some(std::ffi::OsStr::new("ingress.bin")) && dir.join("plan.bin").is_file()).then_some(dir)
}

/// A `resubmit` or `lookup` by an attempt's own ingress decides that attempt: `turn_nonce` reads the
/// attempt's `outcome.json` to tell a decided record (followed only by `--again true`) from an
/// undecided one, so a turn prepared with `--prepare-only` and then resubmitted or looked up would
/// stay "undecided" forever unless the decided answer is retained where the record looks. Only a
/// decided answer is retained (confirmed or refused), only once.
fn retain_decision(ingress: &Path, outcome: &Value) -> Result<()> {
    let Some(dir) = own_attempt(ingress) else { return Ok(()) };
    let decided = matches!(outcome.get("type").and_then(Value::as_str), Some("confirmed" | "refused"));
    if decided && !dir.join("outcome.json").exists() {
        write_new(&dir.join("outcome.json"), outcome.to_string().as_bytes())?;
    }
    Ok(())
}

/// The exact retained bytes submitted again (op 212): a retry replays, never a new nonce. An attempt's
/// own `ingress.bin` is marked transmitted first, and a decided answer is retained beside it.
pub(crate) fn resubmit(ws: &Ws, retained: &Path) -> Result<Value> {
    let ingress = read_ingress(retained)?;
    if let Some(dir) = own_attempt(retained) {
        mark_submitted(dir)?;
    }
    let outcome = inspect(ws, "outcome", &invoke(ws, mini_sdk::host_operations::ACTIVITY_SUBMIT, &ingress)?)?;
    retain_decision(retained, &outcome)?;
    Ok(outcome)
}

/// The receipt-only lookup (op 213) of the retained ingress; absence never submits.
pub(crate) fn lookup(ws: &Ws, retained: &Path) -> Result<Value> {
    let ingress = read_ingress(retained)?;
    let outcome = inspect(ws, "outcome", &invoke(ws, mini_sdk::host_operations::ACTIVITY_LOOKUP, &ingress)?)?;
    retain_decision(retained, &outcome)?;
    Ok(outcome)
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args.required("action")?.into_string().map_err(|_| "activity action must be UTF-8")?;
    let ws = ws(path(args.required("workspace")?))?;
    let value = match action.as_str() {
        "submit" | "quote" => {
            let command = path(args.required("command")?);
            let out = path(args.required("out")?);
            let prepare_only = match args.optional("prepare-only").as_deref().map(|v| v.to_str()) {
                None | Some(Some("false")) => false,
                Some(Some("true")) => true,
                _ => return Err("--prepare-only must be true or false".into()),
            };
            let front_end = args.optional(if action == "quote" { "quote" } else { "quote-front-end" })
                .map(|text| FrontEndQuote::parse(text.to_str().ok_or("activity: the front-end quote must be UTF-8")?))
                .transpose()?;
            let again = match args.optional("again").as_deref().map(|v| v.to_str()) {
                None | Some(Some("false")) => false,
                Some(Some("true")) => true,
                _ => return Err("--again must be true or false".into()),
            };
            args.finish()?;
            let turn: Value = serde_json::from_slice(&fs::read(&command).map_err(|e| e.to_string())?)
                .map_err(|error| format!("activity: invalid command JSON: {error}"))?;
            if action == "quote" {
                quote(&ws, &turn, &out, front_end.as_ref().ok_or("activity quote requires --quote")?)?
            } else {
                submit(&ws, &turn, &out, prepare_only, front_end.as_ref(), again)?
            }
        }
        "resubmit" | "lookup" => {
            let retained = path(args.required("ingress")?);
            args.finish()?;
            if action == "resubmit" { resubmit(&ws, &retained)? } else { lookup(&ws, &retained)? }
        }
        "view" => {
            let request = match args.optional("request") {
                None => json!({}),
                Some(text) => serde_json::from_str(&text.into_string().map_err(|_| "--request must be UTF-8")?)
                    .map_err(|error| format!("activity: invalid --request JSON: {error}"))?,
            };
            args.finish()?;
            view(&ws, &request)?
        }
        _ => return Err("activity action must be submit, quote, resubmit, lookup or view".into()),
    };
    let _ = &ws.root;
    println!("{}", serde_json::to_string(&value).map_err(|e| e.to_string())?);
    Ok(())
}
