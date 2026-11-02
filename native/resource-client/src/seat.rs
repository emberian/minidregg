//! `mini seat` — seats and invitations as signed native commands
//! (ops 215-219, `Kernel/SeatReceiver.lean`).
//!
//! `mini seat --action submit --workspace DIR --command FILE.json --out NEW_DIR
//!   [--prepare-only true]`
//!   FILE.json is `{"turn": {"kind": "publish" | "create" | "handOver" | "offer" |
//!   "invoke" | "exit", ...}, "objectCapability"?: id, "accountCapability"?: id}`
//!   (`Host/SeatJson.lean`). The workspace's subject signs; the nonce is fresh; the
//!   authority root is the one the public view (op 219) shows now. The Host authors
//!   the command (op 7 `seat`), plans it (op 215: the header binds the command and
//!   the outcome the kernel decides now, checked by the local consent provider), the
//!   workspace key signs the header, the Host assembles the ingress (op 216), and the
//!   ingress is retained under NEW_DIR before it is submitted (op 217). With
//!   `--prepare-only true` it is retained and not submitted. The result names the
//!   turn's transaction and, for an offer, the seat's account (its protected coordinate).
//! `mini seat --action resubmit --workspace DIR --ingress FILE` submits the exact
//!   retained bytes again (a retry replays).
//! `mini seat --action lookup --workspace DIR --ingress FILE` is the receipt-only
//!   lookup (op 218); absence never submits.
//! `mini seat --action view --workspace DIR [--request JSON]` prints the public view
//!   (op 219): `{instances, invitations, seats, holdings, pins, accounts, assets}`.
//!
//! Every refusal is the Host's, by name (the kernel's reason, `notObjectHolder`,
//! `notAccountOwner`, `notActivityPayer`, a signature refusal).
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
        .map_err(|error| format!("seat: cannot read workspace.json: {error}"))?;
    if bytes.len() > 64 * 1024 {
        return Err("seat: workspace.json exceeds 64 KiB".into());
    }
    let pin: Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("seat: invalid workspace.json: {error}"))?;
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
        Some((&(crate::RESPONSE_HOST_OUTCOME | crate::RESPONSE_NO_RECORD | crate::RESPONSE_NEVER_FORWARDED), body)) => Err(format!(
            "refused: op{operation}: {}",
            String::from_utf8_lossy(&body[body.len().saturating_sub(600)..])
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ")
        )),
        _ => Err(format!("seat: op{operation} returned an invalid frame")),
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

fn inspect(ws: &Ws, kind: &str, bytes: &[u8]) -> Result<Value> {
    serde_json::from_slice(&invoke(ws, mini_sdk::host_operations::INSPECT, &with_kind(kind, bytes))?)
        .map_err(|error| format!("seat: invalid Host inspection of {kind}: {error}"))
}

fn nonce() -> Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("seat: cannot obtain a nonce: {error}"))?;
    Ok(u128::from_be_bytes(bytes).to_string())
}

fn view(ws: &Ws, request: &Value) -> Result<Value> {
    serde_json::from_slice(&invoke(ws, mini_sdk::host_operations::SEAT_VIEW, request.to_string().as_bytes())?)
        .map_err(|error| format!("seat: invalid view: {error}"))
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    crate::create_private(path, bytes)
}

fn submit(ws: &Ws, file: &Value, out: &Path, prepare_only: bool) -> Result<Value> {
    let turn = file.get("turn").ok_or("seat: the command file lacks a turn")?;
    fs::create_dir(out).map_err(|error| format!("seat: cannot create {}: {error}", out.display()))?;
    let current = view(ws, &json!({}))?;
    let authority = current.get("authorityRoot").and_then(Value::as_str).ok_or("seat: view lacks authorityRoot")?;
    let mut command = json!({"subject": ws.subject, "nonce": nonce()?, "expectedAuthorityRoot": authority, "turn": turn});
    for grant in ["objectCapability", "accountCapability"] {
        if let Some(value) = file.get(grant) {
            command[grant] = value.clone();
        }
    }
    write_new(&out.join("command.json"), command.to_string().as_bytes())?;
    let command_bytes = author(ws, "seat", &command)?;
    write_new(&out.join("command.bin"), &command_bytes)?;
    let plan = invoke(ws, mini_sdk::host_operations::SEAT_PLAN, &command_bytes)?;
    write_new(&out.join("plan.bin"), &plan)?;
    let inspected = inspect(ws, "seat-plan", &plan)?;
    let canonical = inspected.pointer("/header/canonical").and_then(Value::as_str)
        .ok_or("seat: plan lacks a header")?;
    let header = mini_sdk::hex::decode(canonical).map_err(|error| format!("seat: {error}"))?;
    let donation = donation_gate(&inspected, file)?;
    let signature = crate::fsio::read_secret_in_private_dir(&ws.key)?.sign(&header).to_bytes();
    let ingress = invoke(ws, mini_sdk::host_operations::SEAT_ASSEMBLE, &mini_sdk::local::pair(&plan, &signature)?)?;
    write_new(&out.join("ingress.bin"), &ingress)?;
    let transaction = inspected.pointer("/command/transaction").cloned().unwrap_or(Value::Null);
    let seat = inspected.pointer("/command/seatAccount").cloned().unwrap_or(Value::Null);
    let minted = inspected.pointer("/command/mintIds").cloned().unwrap_or(Value::Null);
    if prepare_only {
        return Ok(json!({"type": "prepared", "ingress": out.join("ingress.bin"), "transaction": transaction,
            "seatAccount": seat, "mintIds": minted, "donation": donation}));
    }
    let mut outcome = inspect(ws, "outcome", &invoke(ws, mini_sdk::host_operations::SEAT_SUBMIT, &ingress)?)?;
    write_new(&out.join("outcome.json"), outcome.to_string().as_bytes())?;
    outcome["transaction"] = transaction;
    outcome["seatAccount"] = seat;
    outcome["mintIds"] = minted;
    outcome["donation"] = json!(donation);
    outcome["ingress"] = json!(out.join("ingress.bin"));
    Ok(outcome)
}

/// An offer that wants nothing carries the donation marker (`Seats.Proposal.donate`): the contract
/// may take its whole `give`. The signer sees it in the Host's plan inspection and the client
/// refuses to sign one unless the command file says `"confirmDonation": true`.
fn donation_gate(inspected: &Value, file: &Value) -> Result<bool> {
    let donates = inspected.pointer("/command/turn/proposal/donate").and_then(Value::as_bool).unwrap_or(false);
    if donates && file.get("confirmDonation").and_then(Value::as_bool) != Some(true) {
        let give = inspected.pointer("/command/turn/proposal/give").map(Value::to_string).unwrap_or_default();
        return Err(format!(
            "seat: this offer is a DONATION: it wants nothing, so the contract may take its whole give {give}; \
             add \"confirmDonation\": true to the command file to sign it"
        ));
    }
    Ok(donates)
}

fn read_ingress(path: &Path) -> Result<Vec<u8>> {
    fs::read(path).map_err(|error| format!("seat: cannot read {}: {error}", path.display()))
}

pub(crate) fn positional_flag(name: &str) -> &'static str {
    match name {
        "OBJECT" => "object",
        "PACKAGE" => "package",
        "ARTIFACT" => "artifact",
        "PAYER" => "payer",
        "SEAT" => "seat",
        "ROLE" => "role",
        "HOLDER" => "holder",
        "GIVE-JSON" => "give",
        "WANT-JSON" => "want",
        "ACTION-JSON" => "input",
        "ORDERS-JSON" => "orders",
        _ => "object",
    }
}

fn read_json_or_file(raw: &str, home: Option<&Path>, label: &str) -> Result<Value> {
    let trimmed = raw.trim();
    if let Some(rel) = trimmed.strip_prefix('@') {
        let path = match home {
            Some(h) => h.join("requests").join(rel),
            None => PathBuf::from(rel),
        };
        let bytes = fs::read(&path).map_err(|e| format!("seat: cannot read {label} {}: {e}", path.display()))?;
        return serde_json::from_slice(&bytes).map_err(|e| format!("seat: invalid {label} JSON in {}: {e}", path.display()));
    }
    if (trimmed.starts_with('{') || trimmed.starts_with('['))
        || serde_json::from_str::<Value>(trimmed).is_ok()
    {
        return serde_json::from_str(trimmed).map_err(|e| format!("seat: invalid {label} JSON: {e}"));
    }
    let path = Path::new(trimmed);
    if path.is_file() {
        let bytes = fs::read(path).map_err(|e| format!("seat: cannot read {label} {}: {e}", path.display()))?;
        return serde_json::from_slice(&bytes).map_err(|e| format!("seat: invalid {label} JSON in {}: {e}", path.display()));
    }
    Err(format!("seat: invalid {label} JSON `{trimmed}`"))
}

fn parse_legs_json(raw: &str, home: Option<&Path>, label: &str) -> Result<Vec<Value>> {
    let trimmed = raw.trim();
    if trimmed.is_empty() || trimmed == "[]" || trimmed == "none" {
        return Ok(Vec::new());
    }
    // Support compact `asset:amount` (or comma-separated `asset:amount,asset:amount`) shorthand.
    if !trimmed.starts_with('[') && !trimmed.starts_with('{') && !trimmed.starts_with('@') && trimmed.contains(':') {
        let mut legs = Vec::new();
        for part in trimmed.split(',').map(str::trim).filter(|s| !s.is_empty()) {
            let (asset, amount) = part
                .split_once(':')
                .ok_or_else(|| format!("seat: invalid {label} leg `{part}` (expected `asset:amount` or JSON)"))?;
            legs.push(json!({"asset": asset.trim(), "amount": amount.trim()}));
        }
        return Ok(legs);
    }
    let val = read_json_or_file(trimmed, home, label)?;
    match val {
        Value::Array(items) => {
            let mut normalized = Vec::with_capacity(items.len());
            for item in items {
                if let Some(pair) = item.as_array() {
                    if pair.len() == 2 {
                        normalized.push(json!({"asset": pair[0], "amount": pair[1]}));
                        continue;
                    }
                }
                normalized.push(item);
            }
            Ok(normalized)
        }
        obj @ Value::Object(_) => Ok(vec![obj]),
        _ => Err(format!("seat: {label} must be a JSON object or array of asset legs")),
    }
}

pub(crate) fn to_data_json(v: &Value) -> Value {
    if let Value::Object(map) = v {
        if map.get("tag").and_then(Value::as_str).is_some() {
            return v.clone();
        }
        let entries: Vec<Value> = map
            .iter()
            .map(|(k, val)| {
                json!({
                    "key": {"tag": "symbol", "value": k},
                    "value": to_data_json(val),
                })
            })
            .collect();
        return json!({"tag": "map", "entries": entries});
    }
    match v {
        Value::Null => json!({"tag": "unit"}),
        Value::Bool(b) => json!({"tag": "boolean", "value": b}),
        Value::Number(n) => {
            if let Some(u) = n.as_u64() {
                json!({"tag": "natural", "value": u.to_string()})
            } else if let Some(i) = n.as_i64() {
                json!({"tag": "integer", "value": i.to_string()})
            } else {
                json!({"tag": "symbol", "value": n.to_string()})
            }
        }
        Value::String(s) => {
            if !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) {
                json!({"tag": "natural", "value": s})
            } else {
                json!({"tag": "symbol", "value": s})
            }
        }
        Value::Array(items) => {
            json!({"tag": "list", "items": items.iter().map(to_data_json).collect::<Vec<_>>()})
        }
        Value::Object(_) => unreachable!(),
    }
}

pub(crate) fn build_high_level_command(
    action: &str,
    args: &mut Args,
    home: Option<&Path>,
) -> Result<Value> {
    match action {
        "publish" => {
            let package = args.required("package")?.into_string().map_err(|_| "--package must be UTF-8")?;
            let artifact = args.required("artifact")?.into_string().map_err(|_| "--artifact must be UTF-8")?;
            let payer = args.required("payer")?.into_string().map_err(|_| "--payer must be UTF-8")?;
            Ok(json!({
                "turn": {
                    "kind": "publish",
                    "package": package,
                    "artifact": artifact,
                    "payer": payer,
                }
            }))
        }
        "create" => {
            let object = args.required("object")?.into_string().map_err(|_| "--object must be UTF-8")?;
            let package = args.required("package")?.into_string().map_err(|_| "--package must be UTF-8")?;
            let payer = args.required("payer")?.into_string().map_err(|_| "--payer must be UTF-8")?;
            let invitations = match args.optional("invitations") {
                Some(raw) => {
                    let s = raw.into_string().map_err(|_| "--invitations must be UTF-8")?;
                    read_json_or_file(&s, home, "invitations")?
                }
                None => json!([]),
            };
            let clause = match args.optional("clause") {
                Some(raw) => {
                    let s = raw.into_string().map_err(|_| "--clause must be UTF-8")?;
                    read_json_or_file(&s, home, "clause")
                        .or_else(|_| crate::shell::law::parse(&s))?
                }
                None => json!({"type": "all", "predicates": []}),
            };
            Ok(json!({
                "turn": {
                    "kind": "create",
                    "instance": object,
                    "pin": package,
                    "payer": payer,
                    "clause": clause,
                    "invitations": invitations,
                }
            }))
        }
        "offer" => {
            let object = args.required("object")?.into_string().map_err(|_| "--object must be UTF-8")?;
            let package = args.required("package")?.into_string().map_err(|_| "--package must be UTF-8")?;
            let seat = args.required("seat")?.into_string().map_err(|_| "--seat must be UTF-8")?;
            let role = args.required("role")?.into_string().map_err(|_| "--role must be UTF-8")?;
            let holder = args.required("holder")?.into_string().map_err(|_| "--holder must be UTF-8")?;
            let give_raw = args.required("give")?.into_string().map_err(|_| "--give must be UTF-8")?;
            let want_raw = args.required("want")?.into_string().map_err(|_| "--want must be UTF-8")?;
            let funding = match args.optional("funding") {
                Some(v) => v.into_string().map_err(|_| "--funding must be UTF-8")?,
                None => holder.clone(),
            };
            let payee = match args.optional("payee") {
                Some(v) => v.into_string().map_err(|_| "--payee must be UTF-8")?,
                None => holder.clone(),
            };
            let give = parse_legs_json(&give_raw, home, "give")?;
            let want = parse_legs_json(&want_raw, home, "want")?;
            let donate = !give.is_empty() && want.is_empty();
            Ok(json!({
                "turn": {
                    "kind": "offer",
                    "invitation": seat,
                    "expect": {
                        "instance": object,
                        "package": package,
                        "role": role,
                    },
                    "funding": funding,
                    "payee": payee,
                    "proposal": {
                        "give": give,
                        "want": want,
                        "donate": donate,
                    },
                    "holder": holder,
                }
            }))
        }
        "invoke" => {
            let object = args.required("object")?.into_string().map_err(|_| "--object must be UTF-8")?;
            let package = args.required("package")?.into_string().map_err(|_| "--package must be UTF-8")?;
            let payer = args.required("payer")?.into_string().map_err(|_| "--payer must be UTF-8")?;
            let input_raw = args.required("input")?.into_string().map_err(|_| "--input must be UTF-8")?;
            let raw_val = read_json_or_file(&input_raw, home, "action")?;
            let data_val = to_data_json(&raw_val);
            let envelope = match args.optional("envelope") {
                Some(raw) => {
                    let s = raw.into_string().map_err(|_| "--envelope must be UTF-8")?;
                    read_json_or_file(&s, home, "envelope")?
                }
                None => json!({
                    "maxInstructions": 100000,
                    "maxStack": 1024,
                    "maxHeap": 4096,
                    "maxFrames": 64,
                }),
            };
            Ok(json!({
                "turn": {
                    "kind": "invoke",
                    "instance": object,
                    "package": package,
                    "account": payer,
                    "payer": payer,
                    "input": data_val,
                    "action": raw_val,
                    "envelope": envelope,
                }
            }))
        }
        "exit" => {
            let object = args.required("object")?.into_string().map_err(|_| "--object must be UTF-8")?;
            let package = args.required("package")?.into_string().map_err(|_| "--package must be UTF-8")?;
            let seat = args.required("seat")?.into_string().map_err(|_| "--seat must be UTF-8")?;
            Ok(json!({
                "turn": {
                    "kind": "exit",
                    "instance": object,
                    "package": package,
                    "seat": seat,
                }
            }))
        }
        other => Err(format!("seat: unknown high-level action {other}")),
    }
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args.required("action")?.into_string().map_err(|_| "seat action must be UTF-8")?;
    let home = args.optional("home").map(path);

    if action == "clear-cert" {
        let _ = args.optional("workspace").or_else(|| args.optional("dir"));
        let orders_raw = args
            .required("orders")?
            .into_string()
            .map_err(|_| "--orders must be UTF-8")?;
        let currency = args
            .optional("currency")
            .map(|v| {
                v.into_string()
                    .map_err(|_| "--currency must be UTF-8".to_string())
                    .and_then(|s| s.parse::<u64>().map_err(|_| "invalid --currency".to_string()))
            })
            .transpose()?;
        let goods = args
            .optional("goods")
            .map(|v| {
                v.into_string()
                    .map_err(|_| "--goods must be UTF-8".to_string())
                    .and_then(|s| s.parse::<u64>().map_err(|_| "invalid --goods".to_string()))
            })
            .transpose()?;
        let epsilon = args
            .optional("epsilon")
            .map(|v| {
                v.into_string()
                    .map_err(|_| "--epsilon must be UTF-8".to_string())
                    .and_then(|s| s.parse::<u128>().map_err(|_| "invalid --epsilon".to_string()))
            })
            .transpose()?;
        let out = args.optional("out").map(path);
        args.finish()?;

        let orders_text = if let Some(rel) = orders_raw.trim().strip_prefix('@') {
            let p = match &home {
                Some(h) => h.join("requests").join(rel),
                None => PathBuf::from(rel),
            };
            fs::read_to_string(&p).map_err(|e| format!("seat clear-cert: cannot read {}: {e}", p.display()))?
        } else {
            orders_raw
        };
        let (mut market, orders) = crate::clearing_solver::parse_orders_json(&orders_text)?;
        if let Some(c) = currency {
            market.currency = c;
        }
        if let Some(g) = goods {
            market.goods = g;
        }
        if let Some(e) = epsilon {
            market.epsilon = e;
        }
        let solution = crate::clearing_solver::solve_clearing(&market, &orders)?;
        let out_json = solution.to_json();
        if let Some(out_path) = out {
            write_new(&out_path, out_json.to_string().as_bytes())?;
        }
        println!("{}", serde_json::to_string(&out_json).map_err(|e| e.to_string())?);
        return Ok(());
    }

    let ws_dir = args
        .optional("workspace")
        .or_else(|| args.optional("dir"))
        .ok_or("missing required option --workspace")?;
    let ws_path = path(ws_dir);

    let value = match action.as_str() {
        "submit" => {
            let ws = ws(ws_path)?;
            let command = path(args.required("command")?);
            let out = path(args.required("out")?);
            let prepare_only = match args.optional("prepare-only").as_deref().map(|v| v.to_str()) {
                None | Some(Some("false")) => false,
                Some(Some("true")) => true,
                _ => return Err("--prepare-only must be true or false".into()),
            };
            args.finish()?;
            let file: Value = serde_json::from_slice(&fs::read(&command).map_err(|e| e.to_string())?)
                .map_err(|error| format!("seat: invalid command JSON: {error}"))?;
            submit(&ws, &file, &out, prepare_only)?
        }
        "resubmit" => {
            let ws = ws(ws_path)?;
            let ingress = read_ingress(&path(args.required("ingress")?))?;
            args.finish()?;
            inspect(&ws, "outcome", &invoke(&ws, mini_sdk::host_operations::SEAT_SUBMIT, &ingress)?)?
        }
        "lookup" => {
            let ws = ws(ws_path)?;
            let ingress = read_ingress(&path(args.required("ingress")?))?;
            args.finish()?;
            inspect(&ws, "outcome", &invoke(&ws, mini_sdk::host_operations::SEAT_LOOKUP, &ingress)?)?
        }
        "view" => {
            let object = args
                .optional("object")
                .map(|v| v.into_string().map_err(|_| "--object must be UTF-8".to_string()))
                .transpose()?;
            let package = args
                .optional("package")
                .map(|v| v.into_string().map_err(|_| "--package must be UTF-8".to_string()))
                .transpose()?;
            let out = args.optional("out").map(path);
            let request = match (object, args.optional("request")) {
                (Some(obj), _) => {
                    let mut req = json!({"instance": obj});
                    if let Some(pkg) = package {
                        req["package"] = json!(pkg);
                    }
                    req
                }
                (None, None) => json!({}),
                (None, Some(text)) => serde_json::from_str(&text.into_string().map_err(|_| "--request must be UTF-8")?)
                    .map_err(|error| format!("seat: invalid --request JSON: {error}"))?,
            };
            args.finish()?;
            let ws = ws(ws_path)?;
            let res = view(&ws, &request)?;
            if let Some(out_path) = out {
                write_new(&out_path, res.to_string().as_bytes())?;
            }
            res
        }
        "publish" | "create" | "offer" | "invoke" | "exit" => {
            let out_opt = args.optional("out").map(path);
            let prepare_only = match args.optional("prepare-only").as_deref().map(|v| v.to_str()) {
                None | Some(Some("false")) => false,
                Some(Some("true")) => true,
                _ => return Err("--prepare-only must be true or false".into()),
            };
            let file = build_high_level_command(&action, &mut args, home.as_deref())?;
            args.finish()?;
            let out = match out_opt {
                Some(p) => p,
                None => {
                    let base = ws_path.join("seat-turns");
                    let _ = crate::fsio::ensure_private_dir_all(&base);
                    base.join(format!("seat-{action}-{}", nonce()?))
                }
            };
            match ws(ws_path.clone()) {
                Ok(ws_loaded) if ws_loaded.socket.exists() && ws_loaded.host.is_file() => {
                    submit(&ws_loaded, &file, &out, prepare_only)?
                }
                Ok(_) | Err(_) if prepare_only => {
                    if let Some(parent) = out.parent() {
                        let _ = crate::fsio::ensure_private_dir_all(parent);
                    }
                    let _ = fs::create_dir_all(&out);
                    write_new(&out.join("command.json"), file.to_string().as_bytes())?;
                    json!({
                        "type": "prepared",
                        "action": action,
                        "command": file,
                        "out": out,
                    })
                }
                Ok(ws_loaded) => submit(&ws_loaded, &file, &out, prepare_only)?,
                Err(e) => return Err(e),
            }
        }
        _ => {
            return Err(
                "seat action must be publish, create, offer, invoke, exit, view, clear-cert, submit, resubmit or lookup"
                    .into(),
            )
        }
    };
    println!("{}", serde_json::to_string(&value).map_err(|e| e.to_string())?);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn plan(donate: bool) -> Value {
        json!({"command": {"turn": {"kind": "offer", "proposal": {"give": [{"asset": "1", "amount": "10"}],
            "want": [], "donate": donate}}}})
    }

    #[test]
    fn donation_gate_refuses_an_unconfirmed_donation() {
        let error = donation_gate(&plan(true), &json!({"turn": {}})).unwrap_err();
        assert!(error.contains("DONATION") && error.contains("confirmDonation"), "{error}");
    }

    #[test]
    fn donation_gate_passes_a_confirmed_donation_and_an_ordinary_offer() {
        assert_eq!(donation_gate(&plan(true), &json!({"confirmDonation": true})).unwrap(), true);
        assert_eq!(donation_gate(&plan(false), &json!({})).unwrap(), false);
    }

    #[test]
    fn high_level_seat_commands_build_expected_turns() {
        let mut create_args = Args::parse_from(
            ["seat", "create", "9101", "101", "7", "--invitations", r#"[{"role":"bid","holder":"10"}]"#]
                .into_iter()
                .map(OsString::from),
        )
        .unwrap();
        let _ = create_args.required("action").unwrap();
        let create_cmd = build_high_level_command("create", &mut create_args, None).unwrap();
        assert_eq!(create_cmd["turn"]["kind"], "create");
        assert_eq!(create_cmd["turn"]["instance"], "9101");
        assert_eq!(create_cmd["turn"]["pin"], "101");
        assert_eq!(create_cmd["turn"]["payer"], "7");
        assert_eq!(create_cmd["turn"]["invitations"][0]["role"], "bid");

        let mut offer_args = Args::parse_from(
            [
                "seat",
                "offer",
                "9101",
                "101",
                "501",
                "bid",
                "10",
                r#"{"asset":"1","amount":"15"}"#,
                r#"{"asset":"2","amount":"3"}"#,
            ]
            .into_iter()
            .map(OsString::from),
        )
        .unwrap();
        let _ = offer_args.required("action").unwrap();
        let offer_cmd = build_high_level_command("offer", &mut offer_args, None).unwrap();
        assert_eq!(offer_cmd["turn"]["kind"], "offer");
        assert_eq!(offer_cmd["turn"]["invitation"], "501");
        assert_eq!(offer_cmd["turn"]["expect"]["instance"], "9101");
        assert_eq!(offer_cmd["turn"]["expect"]["package"], "101");
        assert_eq!(offer_cmd["turn"]["expect"]["role"], "bid");
        assert_eq!(offer_cmd["turn"]["holder"], "10");
        assert_eq!(offer_cmd["turn"]["proposal"]["give"][0]["asset"], "1");
        assert_eq!(offer_cmd["turn"]["proposal"]["want"][0]["amount"], "3");
    }
}

