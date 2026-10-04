//! `mini activity` — the kernel activity as signed native commands
//! (ops 210-214, `Kernel/ObjectiveActivityReceiver.lean`).
//!
//! `mini activity --action submit --workspace DIR --command FILE.json --out NEW_DIR
//!   [--prepare-only true]`
//!   FILE.json is the command's `turn` (`{"kind": "publish" | "create" | "birth" | "resolve" |
//!   "deliver" | "topUp" | "writeState" | "exhaust" | "abandon", ...}`,
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

struct Ws {
    root: PathBuf,
    host: PathBuf,
    socket: PathBuf,
    config: PathBuf,
    key: PathBuf,
    subject: String,
}

fn ws(root: PathBuf) -> Result<Ws> {
    let bytes = fs::read(root.join("workspace.json"))
        .map_err(|error| format!("activity: cannot read workspace.json: {error}"))?;
    if bytes.len() > 64 * 1024 {
        return Err("activity: workspace.json exceeds 64 KiB".into());
    }
    let pin: Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("activity: invalid workspace.json: {error}"))?;
    Ok(Ws {
        host: PathBuf::from(field(&pin, "host")?),
        socket: PathBuf::from(field(&pin, "socket")?),
        config: PathBuf::from(field(&pin, "config")?),
        key: PathBuf::from(field(&pin, "key")?),
        subject: field(&pin, "subject")?.to_string(),
        root,
    })
}

fn invoke(ws: &Ws, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
    let frame = session_invoke(&ws.host, &ws.socket, &ws.config, operation, payload)?;
    match frame.split_first() {
        Some((actual, body)) if *actual == operation && !body.is_empty() => Ok(body.to_vec()),
        Some((255 | 254, body)) => Err(format!(
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
    invoke(ws, 7, &with_kind(kind, value.to_string().as_bytes()))
}

fn inspect(ws: &Ws, kind: &str, bytes: &[u8]) -> Result<Value> {
    serde_json::from_slice(&invoke(ws, 8, &with_kind(kind, bytes))?)
        .map_err(|error| format!("activity: invalid Host inspection of {kind}: {error}"))
}

fn pair(first: &[u8], second: &[u8]) -> Vec<u8> {
    let mut bytes = (first.len() as u32).to_le_bytes().to_vec();
    bytes.extend_from_slice(first);
    bytes.extend_from_slice(second);
    bytes
}

fn nonce() -> Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("activity: cannot obtain a nonce: {error}"))?;
    Ok(u128::from_be_bytes(bytes).to_string())
}

fn view(ws: &Ws, request: &Value) -> Result<Value> {
    serde_json::from_slice(&invoke(ws, 214, request.to_string().as_bytes())?)
        .map_err(|error| format!("activity: invalid view: {error}"))
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    crate::create_private(path, bytes)
}

fn submit(ws: &Ws, turn: &Value, out: &Path, prepare_only: bool) -> Result<Value> {
    fs::create_dir(out).map_err(|error| format!("activity: cannot create {}: {error}", out.display()))?;
    let current = view(ws, &json!({}))?;
    let authority = current.get("authorityRoot").and_then(Value::as_str).ok_or("activity: view lacks authorityRoot")?;
    let command = json!({"subject": ws.subject, "nonce": nonce()?, "expectedAuthorityRoot": authority, "turn": turn});
    write_new(&out.join("command.json"), command.to_string().as_bytes())?;
    let command_bytes = author(ws, "objective-activity", &command)?;
    write_new(&out.join("command.bin"), &command_bytes)?;
    let plan = invoke(ws, 210, &command_bytes)?;
    write_new(&out.join("plan.bin"), &plan)?;
    let inspected = inspect(ws, "objective-activity-plan", &plan)?;
    let canonical = inspected.pointer("/header/canonical").and_then(Value::as_str)
        .ok_or("activity: plan lacks a header")?;
    let header = crate::decode_hex(canonical).map_err(|error| format!("activity: {error}"))?;
    let signature = crate::fsio::read_secret_in_private_dir(&ws.key)?.sign(&header).to_bytes();
    let ingress = invoke(ws, 211, &pair(&plan, &signature))?;
    write_new(&out.join("ingress.bin"), &ingress)?;
    let transaction = inspected.pointer("/command/transaction").cloned().unwrap_or(Value::Null);
    if prepare_only {
        return Ok(json!({"type": "prepared", "ingress": out.join("ingress.bin"), "transaction": transaction}));
    }
    let mut outcome = inspect(ws, "outcome", &invoke(ws, 212, &ingress)?)?;
    write_new(&out.join("outcome.json"), outcome.to_string().as_bytes())?;
    outcome["transaction"] = transaction;
    outcome["ingress"] = json!(out.join("ingress.bin"));
    Ok(outcome)
}

fn read_ingress(path: &Path) -> Result<Vec<u8>> {
    fs::read(path).map_err(|error| format!("activity: cannot read {}: {error}", path.display()))
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args.required("action")?.into_string().map_err(|_| "activity action must be UTF-8")?;
    let ws = ws(path(args.required("workspace")?))?;
    let value = match action.as_str() {
        "submit" => {
            let command = path(args.required("command")?);
            let out = path(args.required("out")?);
            let prepare_only = match args.optional("prepare-only").as_deref().map(|v| v.to_str()) {
                None | Some(Some("false")) => false,
                Some(Some("true")) => true,
                _ => return Err("--prepare-only must be true or false".into()),
            };
            args.finish()?;
            let turn: Value = serde_json::from_slice(&fs::read(&command).map_err(|e| e.to_string())?)
                .map_err(|error| format!("activity: invalid command JSON: {error}"))?;
            submit(&ws, &turn, &out, prepare_only)?
        }
        "resubmit" => {
            let ingress = read_ingress(&path(args.required("ingress")?))?;
            args.finish()?;
            inspect(&ws, "outcome", &invoke(&ws, 212, &ingress)?)?
        }
        "lookup" => {
            let ingress = read_ingress(&path(args.required("ingress")?))?;
            args.finish()?;
            inspect(&ws, "outcome", &invoke(&ws, 213, &ingress)?)?
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
        _ => return Err("activity action must be submit, resubmit, lookup or view".into()),
    };
    let _ = &ws.root;
    println!("{}", serde_json::to_string(&value).map_err(|e| e.to_string())?);
    Ok(())
}
