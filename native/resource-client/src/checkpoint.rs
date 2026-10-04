//! `mini checkpoint` — the operator's checkpoint path for the tail bound (C14).
//!
//! `mini checkpoint --action certify --workspace DIR --control CAP` asks the Host for
//! the public system view (op 173): the certified head, the tail bound `L`, the current
//! head and its log-chain value. It has the Host author a certify command naming that
//! head and chain (`author certify`), obtains the signing plan (op 170), signs its header
//! with the workspace key, assembles (op 171) and submits (op 172). The Host decides
//! everything else: the capability, the pinned roots, that the head and chain are the
//! current ones and that the head advances (`CertifyReceiver.certified_advances`), and
//! again at the durable boundary that the system cell moves only by certification
//! (`TailBound.certified_written_only_by_checkpoint`).
//!
//! `--min-tail N` certifies only when the uncertified tail (head − certified) is at least
//! N, and otherwise prints the view and succeeds: the timer's cadence is then a height
//! cadence, and an idle node does not accrue one certify record per tick.
//!
//! `mini checkpoint --action view --workspace DIR` prints the system view, including
//! `tail` (head − certified) and `remaining` (heights left before the bound refuses).
//!
//! Today the certifier is the operator, trusted as the operator is; a timer runs this
//! verb (deploy/checkpoint). After SURPASS N1 the certificate is a witness quorum's.

use crate::agent_reserve::field;
use crate::*;
use serde_json::{json, Value};

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
            "checkpoint: Host refused op{operation}: {}",
            String::from_utf8_lossy(&body[body.len().saturating_sub(300)..])
        )),
        _ => Err(format!("checkpoint: op{operation} returned an invalid frame")),
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
        .map_err(|error| format!("checkpoint: invalid Host inspection of {kind}: {error}"))
}

fn pair(first: &[u8], second: &[u8]) -> Vec<u8> {
    let mut bytes = (first.len() as u32).to_le_bytes().to_vec();
    bytes.extend_from_slice(first);
    bytes.extend_from_slice(second);
    bytes
}

fn decimal_arg(args: &mut Args, name: &str) -> Result<Option<String>> {
    match args.optional(name) {
        None => Ok(None),
        Some(value) => {
            let text = value.into_string().map_err(|_| format!("--{name} must be UTF-8"))?;
            if !mini_sdk::decimal::is_canonical(&text) {
                return Err(format!("--{name} must be a canonical unsigned decimal"));
            }
            Ok(Some(text))
        }
    }
}

fn view(ws: &Workspace) -> Result<Value> {
    let bytes = invoke(ws, 173, &[])?;
    inspect(ws, "certify-view", &bytes)
}

fn certify(ws: &Workspace, control: &str, min_tail: Option<String>) -> Result<Value> {
    let current = view(ws)?;
    if let Some(min_tail) = min_tail {
        let tail: u128 = field(&current, "tail")?.parse().map_err(|_| "view tail is not decimal")?;
        let wanted: u128 = min_tail.parse().map_err(|_| "--min-tail is not decimal")?;
        if tail < wanted {
            let mut value = current.clone();
            value["type"] = json!("not-due");
            return Ok(value);
        }
    }
    let command = author(
        ws,
        "certify",
        &json!({
            "sponsor": ws.subject, "control": control, "nonce": crate::fsio::random_nonce()?,
            "expectedFactoryRoot": field(&current, "factoryRoot")?,
            "expectedAuthorityRoot": field(&current, "authorityRoot")?,
            "expectedSystemRoot": field(&current, "systemRoot")?,
            "height": field(&current, "head")?,
            "digest": field(&current, "chain")?,
        }),
    )?;
    let plan = invoke(ws, 170, &command)?;
    let header = inspect(ws, "certify-plan", &plan)?;
    let canonical = header
        .get("header")
        .and_then(|h| h.get("canonical"))
        .and_then(Value::as_str)
        .ok_or("certify plan lacks a canonical header")?;
    let header_bytes = decode_hex(canonical).map_err(|_| "certify plan header is not hex")?;
    let signature = crate::fsio::read_secret_in_private_dir(&ws.key)?.sign(&header_bytes).to_bytes();
    let ingress = invoke(ws, 171, &pair(&plan, &signature))?;
    let outcome = invoke(ws, 172, &ingress)?;
    let mut value = inspect(ws, "outcome", &outcome)?;
    value["certified"] = json!({"height": field(&current, "head")?, "digest": field(&current, "chain")?});
    Ok(value)
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "checkpoint action must be UTF-8")?;
    let ws = workspace(&path(args.required("workspace")?))?;
    let value = match action.as_str() {
        "view" => {
            args.finish()?;
            view(&ws)?
        }
        "certify" => {
            let control = decimal_arg(&mut args, "control")?.ok_or("--control is required")?;
            let min_tail = decimal_arg(&mut args, "min-tail")?;
            args.finish()?;
            certify(&ws, &control, min_tail)?
        }
        _ => return Err("checkpoint action must be certify or view".into()),
    };
    println!("{}", serde_json::to_string(&value).map_err(|e| e.to_string())?);
    if action == "certify"
        && !matches!(value.get("type").and_then(Value::as_str), Some("confirmed" | "not-due"))
    {
        return Err(format!("certify not confirmed: {value}").into());
    }
    Ok(())
}
