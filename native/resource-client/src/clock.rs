//! `mini clock` — the v1 time source of a deployment's one clock (K-CLOCK).
//!
//! `mini clock --action tick --workspace DIR --control CAP [--now SECONDS] [--slot SLOT]`
//! reads the operator's wall clock (unless `--now` is given), asks the Host for the
//! current clock view (op 129), has the Host author the tick command (`author
//! clock-tick`), obtains the signing plan (op 126), signs its header with the
//! workspace key, assembles (op 127) and submits (op 128). The slot is carried
//! forward from the view unless `--slot` is given: the wall-clock ticker never
//! asserts a chain slot. The Host decides everything else — the capability, the
//! pinned roots, and that time only moves forward (`ClockTickReceiver.clock_monotone`).
//!
//! `mini clock --action view --workspace DIR` prints the clock view.
//!
//! This time source is the operator's wall clock, trusted as the operator is. PAY's
//! chain observer can tick the same cell under its own capability; it replaces this
//! source by asserting chain time.

use crate::agent_reserve::{field, private_bytes};
use crate::*;
use serde_json::{json, Value};
use std::time::{SystemTime, UNIX_EPOCH};

struct Workspace {
    host: PathBuf,
    socket: PathBuf,
    config: PathBuf,
    key: PathBuf,
    subject: String,
}

fn workspace(directory: &Path) -> Result<Workspace> {
    let bytes = fs::read(directory.join("workspace.json"))
        .map_err(|error| format!("cannot read workspace.json: {error}"))?;
    if bytes.len() > 64 * 1024 {
        return Err("workspace.json exceeds 64 KiB".into());
    }
    let value: Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("invalid workspace.json: {error}"))?;
    if field(&value, "type")? != "minidregg-participant-workspace-v1" {
        return Err("unknown participant workspace version".into());
    }
    Ok(Workspace {
        host: PathBuf::from(field(&value, "host")?),
        socket: PathBuf::from(field(&value, "socket")?),
        config: PathBuf::from(field(&value, "config")?),
        key: PathBuf::from(field(&value, "key")?),
        subject: field(&value, "subject")?.to_string(),
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
            if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) || (text.len() > 1 && text.starts_with('0')) {
                return Err(format!("--{name} must be a canonical unsigned decimal"));
            }
            Ok(Some(text))
        }
    }
}

fn view(ws: &Workspace) -> Result<Value> {
    let bytes = invoke(ws, 129, &[])?;
    inspect(ws, "clock-view", &bytes)
}

fn tick(ws: &Workspace, control: &str, now: Option<String>, slot: Option<String>) -> Result<Value> {
    let current = view(ws)?;
    let now = match now {
        Some(now) => now,
        None => SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|_| "wall clock is before the unix epoch")?
            .as_secs()
            .to_string(),
    };
    let slot = slot.unwrap_or(field(&current, "slot")?.to_string());
    let command = author(
        ws,
        "clock-tick",
        &json!({
            "sponsor": ws.subject, "control": control, "nonce": nonce()?,
            "expectedFactoryRoot": field(&current, "factoryRoot")?,
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
    let outcome = invoke(ws, 128, &ingress)?;
    let mut value = inspect(ws, "outcome", &outcome)?;
    value["asserted"] = json!({"now": now, "slot": slot});
    Ok(value)
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "clock action must be UTF-8")?;
    let ws = workspace(&path(args.required("workspace")?))?;
    let value = match action.as_str() {
        "view" => {
            args.finish()?;
            view(&ws)?
        }
        "tick" => {
            let control = decimal_arg(&mut args, "control")?.ok_or("--control is required")?;
            let now = decimal_arg(&mut args, "now")?;
            let slot = decimal_arg(&mut args, "slot")?;
            args.finish()?;
            tick(&ws, &control, now, slot)?
        }
        _ => return Err("clock action must be tick or view".into()),
    };
    println!("{}", serde_json::to_string(&value).map_err(|e| e.to_string())?);
    if action == "tick" && value.get("type").and_then(Value::as_str) != Some("confirmed") {
        return Err(format!("clock tick not confirmed: {value}").into());
    }
    Ok(())
}
