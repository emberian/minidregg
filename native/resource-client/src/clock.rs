//! `mini clock` — the v1 time source of a deployment's one clock (K-CLOCK), run by
//! the deployment's dedicated clock subject (CLOCK-SUBJECT).
//!
//! `mini clock --action init --dir DIR --host HOST --config CONFIG --socket SOCKET
//!   --key KEY --subject SUBJECT --capability C_TICK` writes the clock subject's own
//! workspace (`minidregg-clock-workspace-v1`): no references, no birth context, only
//! what a tick needs. Its `C_tick` is issued at genesis (`clockTickers`).
//!
//! `mini clock --action tick --workspace DIR [--capability CAP] [--now SECONDS]
//!   [--slot SLOT]` reads the wall clock (unless `--now` is given), asks the Host for the
//! clock view (op 129), has the Host author the tick (`author clock-tick`), obtains the
//! signing plan (op 126), signs its header with the workspace key, assembles (op 127)
//! and submits (op 128). The slot is carried forward from the view unless `--slot` is
//! given. The Host decides the rest: the capability and the clock law, the pinned roots,
//! and that time only moves forward (`ClockTickReceiver.clock_monotone`).
//!
//! Attempts are ephemeral. The signed ingress is written to `DIR/clock-attempts/` before
//! it is submitted, and deleted once its outcome is definite (confirmed or refused);
//! each resolution appends one line to the rotating journal `DIR/clock-journal.tsv`
//! (`unix-time  height  verb  outcome  now  slot`). An attempt whose reply was lost
//! (contention, unavailable, uncertain, or a killed process) stays and is resubmitted
//! byte-for-byte at the start of the next run, so it resolves as `replayed` if it
//! committed: exact retry survives, and a steady ticker leaves no attempt behind.
//! `--abandon-after-submit true` submits and exits without reading the reply (the
//! lost-reply probe).
//!
//! `mini clock --action view --workspace DIR` prints the clock view.

use crate::agent_reserve::{field, private_bytes};
use crate::workspace::{make_private_dir, private_file};
use crate::*;
use serde_json::{json, Value};
use std::os::unix::fs::OpenOptionsExt;
use std::time::{SystemTime, UNIX_EPOCH};

const CLOCK_WORKSPACE: &str = "minidregg-clock-workspace-v1";
const PARTICIPANT_WORKSPACE: &str = "minidregg-participant-workspace-v1";
const ATTEMPTS: &str = "clock-attempts";
const JOURNAL: &str = "clock-journal.tsv";
/// The journal rotates to `clock-journal.tsv.1` past this size (one generation kept).
const JOURNAL_LIMIT: u64 = 1 << 20;

struct Workspace {
    dir: PathBuf,
    host: PathBuf,
    socket: PathBuf,
    config: PathBuf,
    key: PathBuf,
    subject: String,
    capability: Option<String>,
}

fn workspace(directory: &Path) -> Result<Workspace> {
    let bytes = fs::read(directory.join("workspace.json"))
        .map_err(|error| format!("cannot read workspace.json: {error}"))?;
    if bytes.len() > 64 * 1024 {
        return Err("workspace.json exceeds 64 KiB".into());
    }
    let value: Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("invalid workspace.json: {error}"))?;
    let capability = match field(&value, "type")? {
        CLOCK_WORKSPACE => Some(field(&value, "capability")?.to_string()),
        PARTICIPANT_WORKSPACE => None,
        _ => return Err("unknown workspace version".into()),
    };
    Ok(Workspace {
        dir: directory.to_path_buf(),
        host: PathBuf::from(field(&value, "host")?),
        socket: PathBuf::from(field(&value, "socket")?),
        config: PathBuf::from(field(&value, "config")?),
        key: PathBuf::from(field(&value, "key")?),
        subject: field(&value, "subject")?.to_string(),
        capability,
    })
}

fn reply(frame: Vec<u8>, operation: u8) -> Result<Vec<u8>> {
    match frame.split_first() {
        Some((actual, body)) if *actual == operation && !body.is_empty() => Ok(body.to_vec()),
        Some((255 | 254, body)) => Err(format!(
            "clock: Host refused op{operation}: {}",
            String::from_utf8_lossy(&body[body.len().saturating_sub(300)..])
        )),
        _ => Err(format!("clock: op{operation} returned an invalid frame")),
    }
}

fn invoke(ws: &Workspace, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
    reply(session_invoke(&ws.host, &ws.socket, &ws.config, operation, payload)?, operation)
}

fn with_kind(kind: &str, body: &[u8]) -> Vec<u8> {
    let mut payload = (kind.len() as u16).to_le_bytes().to_vec();
    payload.extend_from_slice(kind.as_bytes());
    payload.extend_from_slice(body);
    payload
}

/// Host op 7: source-owned authoring of a JSON value into canonical bytes.
fn author(ws: &Workspace, kind: &str, value: &Value) -> Result<Vec<u8>> {
    invoke(ws, 7, &with_kind(kind, &serde_json::to_vec(value).map_err(|e| e.to_string())?))
}

/// Host op 8: source-owned inspection of canonical bytes as JSON.
fn inspect(ws: &Workspace, kind: &str, bytes: &[u8]) -> Result<Value> {
    serde_json::from_slice(&invoke(ws, 8, &with_kind(kind, bytes))?)
        .map_err(|error| format!("clock: invalid Host inspection of {kind}: {error}"))
}

fn pair(first: &[u8], second: &[u8]) -> Vec<u8> {
    let mut bytes = (first.len() as u32).to_le_bytes().to_vec();
    bytes.extend_from_slice(first);
    bytes.extend_from_slice(second);
    bytes
}

fn unhex(text: &str) -> Option<Vec<u8>> {
    if text.len() % 2 != 0 {
        return None;
    }
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(text.get(i..i + 2)?, 16).ok())
        .collect()
}

fn nonce() -> Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("cannot obtain clock nonce: {error}"))?;
    Ok(u128::from_be_bytes(bytes).to_string())
}

fn decimal_arg(args: &mut Args, name: &str) -> Result<Option<String>> {
    match args.optional(name) {
        None => Ok(None),
        Some(value) => {
            let text = value.into_string().map_err(|_| format!("--{name} must be UTF-8"))?;
            if text.is_empty()
                || !text.bytes().all(|b| b.is_ascii_digit())
                || (text.len() > 1 && text.starts_with('0'))
            {
                return Err(format!("--{name} must be a canonical unsigned decimal"));
            }
            Ok(Some(text))
        }
    }
}

fn bool_arg(args: &mut Args, name: &str) -> Result<bool> {
    match args.optional(name).as_deref().map(|value| value.to_str()) {
        None => Ok(false),
        Some(Some("true")) => Ok(true),
        Some(Some("false")) => Ok(false),
        _ => Err(format!("--{name} must be true or false")),
    }
}

fn view(ws: &Workspace) -> Result<Value> {
    let bytes = invoke(ws, 129, &[])?;
    inspect(ws, "clock-view", &bytes)
}

fn unix_now() -> Result<u64> {
    Ok(SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|_| "wall clock is before the unix epoch")?
        .as_secs())
}

/// One journal line per resolved attempt: `unix-time height verb outcome now slot`.
fn journal(ws: &Workspace, outcome: &Value, now: &str, slot: &str) -> Result<()> {
    let path = ws.dir.join(JOURNAL);
    if fs::metadata(&path).map(|meta| meta.len() >= JOURNAL_LIMIT).unwrap_or(false) {
        fs::rename(&path, ws.dir.join(format!("{JOURNAL}.1")))
            .map_err(|error| format!("cannot rotate {}: {error}", path.display()))?;
    }
    let height = outcome.get("acceptedCount").and_then(Value::as_str).unwrap_or("-");
    let verdict = match outcome.get("type").and_then(Value::as_str) {
        Some("confirmed") => outcome
            .get("confirmation")
            .and_then(Value::as_str)
            .unwrap_or("confirmed")
            .to_string(),
        Some(other) => other.to_string(),
        None => "unknown".to_string(),
    };
    let line = format!("{}\t{height}\ttick\t{verdict}\t{now}\t{slot}\n", unix_now()?);
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .mode(0o600)
        .open(&path)
        .map_err(|error| format!("cannot open {}: {error}", path.display()))?;
    file.write_all(line.as_bytes())
        .and_then(|()| file.sync_data())
        .map_err(|error| format!("cannot append {}: {error}", path.display()))
}

/// Confirmed (installed or replayed) and refused are definite; anything else may
/// still commit, so the attempt is kept for an exact retry.
fn definite(outcome: &Value) -> bool {
    matches!(outcome.get("type").and_then(Value::as_str), Some("confirmed" | "refused"))
}

fn attempts(ws: &Workspace) -> Result<PathBuf> {
    let dir = ws.dir.join(ATTEMPTS);
    if !dir.exists() {
        make_private_dir(&dir)?;
    }
    Ok(dir)
}

fn submit(ws: &Workspace, attempt: &Path) -> Result<Value> {
    let ingress = fs::read(attempt.join("ingress.bin"))
        .map_err(|error| format!("cannot read {}: {error}", attempt.display()))?;
    let outcome = invoke(ws, 128, &ingress)?;
    inspect(ws, "outcome", &outcome)
}

/// Resolve one retained attempt: resubmit its exact ingress; journal and delete it when
/// the outcome is definite.
fn resolve(ws: &Workspace, attempt: &Path) -> Result<Value> {
    let asserted: Value = serde_json::from_slice(
        &fs::read(attempt.join("tick.json")).map_err(|error| error.to_string())?,
    )
    .map_err(|error| format!("invalid {}: {error}", attempt.display()))?;
    let mut outcome = submit(ws, attempt)?;
    if definite(&outcome) {
        journal(ws, &outcome, field(&asserted, "now")?, field(&asserted, "slot")?)?;
        fs::remove_dir_all(attempt)
            .map_err(|error| format!("cannot remove {}: {error}", attempt.display()))?;
    }
    outcome["asserted"] = asserted;
    Ok(outcome)
}

/// Every attempt a previous run left (its reply was lost), resolved before a new tick.
fn resolve_pending(ws: &Workspace) -> Result<Vec<Value>> {
    let dir = attempts(ws)?;
    let mut pending: Vec<PathBuf> = fs::read_dir(&dir)
        .map_err(|error| format!("cannot list {}: {error}", dir.display()))?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.join("ingress.bin").is_file())
        .collect();
    pending.sort();
    let mut resolved = Vec::new();
    for attempt in pending {
        let outcome = resolve(ws, &attempt)?;
        if !definite(&outcome) {
            return Err(format!("retained clock attempt unresolved: {outcome}"));
        }
        resolved.push(outcome);
    }
    Ok(resolved)
}

fn tick(
    ws: &Workspace,
    capability: &str,
    now: Option<String>,
    slot: Option<String>,
    abandon: bool,
) -> Result<Value> {
    let resolved = resolve_pending(ws)?;
    let current = view(ws)?;
    let now = match now {
        Some(now) => now,
        None => unix_now()?.to_string(),
    };
    let slot = slot.unwrap_or(field(&current, "slot")?.to_string());
    let command = author(
        ws,
        "clock-tick",
        &json!({
            "sponsor": ws.subject, "capability": capability, "nonce": nonce()?,
            "expectedAuthorityRoot": field(&current, "authorityRoot")?,
            "expectedClockRoot": field(&current, "clockRoot")?,
            "now": now, "slot": slot,
        }),
    )?;
    let plan = invoke(ws, 126, &command)?;
    let header = inspect(ws, "clock-plan", &plan)?;
    let canonical = header
        .get("header")
        .and_then(|h| h.get("canonical"))
        .and_then(Value::as_str)
        .ok_or("clock plan lacks a canonical header")?;
    let header_bytes = unhex(canonical).ok_or("clock plan header is not hex")?;
    let seed: [u8; 32] = private_bytes(&ws.key, 32)?
        .try_into()
        .map_err(|_| "workspace key must contain exactly 32 raw bytes")?;
    let signature = SigningKey::from_bytes(&seed).sign(&header_bytes).to_bytes();
    let ingress = invoke(ws, 127, &pair(&plan, &signature))?;
    // Retained before submission: a lost reply is resolved by the next run.
    let attempt = attempts(ws)?.join(format!("t-{}", nonce()?));
    make_private_dir(&attempt)?;
    let asserted = json!({"now": now, "slot": slot});
    private_file(&attempt.join("tick.json"), asserted.to_string().as_bytes())?;
    private_file(&attempt.join("ingress.bin"), &ingress)?;
    if abandon {
        let _ = invoke(ws, 128, &ingress)?;
        return Ok(json!({"type": "abandoned", "attempt": attempt, "asserted": asserted}));
    }
    let mut value = resolve(ws, &attempt)?;
    if !resolved.is_empty() {
        value["resolvedRetained"] = json!(resolved);
    }
    Ok(value)
}

fn init(mut args: Args) -> Result<Value> {
    let dir = path(args.required("dir")?);
    let mut text = |name: &str| -> Result<String> {
        args.required(name)?
            .into_string()
            .map_err(|_| format!("--{name} must be UTF-8"))
    };
    let host = absolute(Path::new(&text("host")?))?;
    let config = absolute(Path::new(&text("config")?))?;
    // `--socket` is the client's global option (`run` keeps it in SOCKET).
    let socket = absolute(SOCKET.get().ok_or("clock init requires --socket")?)?;
    let key = absolute(Path::new(&text("key")?))?;
    let subject = text("subject")?;
    let capability = text("capability")?;
    args.finish()?;
    for (name, value) in [("subject", &subject), ("capability", &capability)] {
        if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
            return Err(format!("--{name} must be a canonical unsigned decimal"));
        }
    }
    if !dir.exists() {
        make_private_dir(&dir)?;
    }
    let value = json!({"type": CLOCK_WORKSPACE, "host": host, "socket": socket,
        "config": config, "key": key, "subject": subject, "capability": capability});
    let mut bytes = serde_json::to_vec_pretty(&value).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    private_file(&dir.join("workspace.json"), &bytes)?;
    make_private_dir(&dir.join(ATTEMPTS))?;
    Ok(value)
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "clock action must be UTF-8")?;
    if action == "init" {
        let value = init(args)?;
        println!("{}", serde_json::to_string(&value).map_err(|e| e.to_string())?);
        return Ok(());
    }
    let ws = workspace(&path(args.required("workspace")?))?;
    let value = match action.as_str() {
        "view" => {
            args.finish()?;
            view(&ws)?
        }
        "tick" => {
            let capability = match (decimal_arg(&mut args, "capability")?, &ws.capability) {
                (Some(given), _) => given,
                (None, Some(own)) => own.clone(),
                (None, None) => return Err("--capability is required outside a clock workspace".into()),
            };
            let now = decimal_arg(&mut args, "now")?;
            let slot = decimal_arg(&mut args, "slot")?;
            let abandon = bool_arg(&mut args, "abandon-after-submit")?;
            args.finish()?;
            tick(&ws, &capability, now, slot, abandon)?
        }
        _ => return Err("clock action must be init, tick or view".into()),
    };
    println!("{}", serde_json::to_string(&value).map_err(|e| e.to_string())?);
    if action == "tick"
        && !matches!(value.get("type").and_then(Value::as_str), Some("confirmed" | "abandoned"))
    {
        return Err(format!("clock tick not confirmed: {value}").into());
    }
    Ok(())
}
