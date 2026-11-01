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
//! The command names the head and chain it observed and pins the factory, authority and
//! system roots (`CertifyReceiver.prepare`). Since the certify-prefix rule
//! (`Kernel.ChainHistory.certifiable`) a held prefix stays certifiable after later
//! writes; a moved root still refuses it stale. Certifying the newer head is the same act, so such a refusal is run
//! again through the client's one re-plan loop (`replan::replan`, `--replan-max`):
//! nothing was admitted and nothing is retained, so a fresh observation authors a
//! fresh command. The reply lists each raced refusal under `racedRefusals`; when the
//! re-plans are spent the last one fails the run. A killed run likewise leaves nothing
//! behind: the next run observes afresh.
//!
//! `mini checkpoint --action view --workspace DIR` prints the system view, including
//! `tail` (head − certified) and `remaining` (heights left before the bound refuses).
//!
//! Today the certifier is the operator, trusted as the operator is; a timer runs this
//! verb (the deployed certifier (dregg-infra edge/mini/mini-certify.timer)). A witness quorum's certificate is not built.

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
    let host = PathBuf::from(field(&value, "host")?);
    if let Some(sha) = value.get("hostSha256").and_then(Value::as_str) {
        crate::pin_workspace_host(&host, sha)?;
    }
    Ok(Workspace {
        host,
        socket: PathBuf::from(field(&value, "socket")?),
        config: PathBuf::from(field(&value, "config")?),
        key: PathBuf::from(field(&value, "key")?),
        subject: field(&value, "subject")?.to_string(),
    })
}

fn reply(frame: Vec<u8>, operation: u8) -> Result<Vec<u8>> {
    match frame.split_first() {
        Some((actual, body)) if *actual == operation && !body.is_empty() => Ok(body.to_vec()),
        Some((&(crate::RESPONSE_HOST_OUTCOME | crate::RESPONSE_NO_RECORD | crate::RESPONSE_NEVER_FORWARDED), body)) => Err(format!(
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
    invoke(ws, mini_sdk::host_operations::AUTHOR, &with_kind(kind, &serde_json::to_vec(value).map_err(|e| e.to_string())?))
}

/// Host op 8: source-owned inspection of canonical bytes as JSON.
fn inspect(ws: &Workspace, kind: &str, bytes: &[u8]) -> Result<Value> {
    serde_json::from_slice(&invoke(ws, mini_sdk::host_operations::INSPECT, &with_kind(kind, bytes))?)
        .map_err(|error| format!("checkpoint: invalid Host inspection of {kind}: {error}"))
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
    let bytes = invoke(ws, mini_sdk::host_operations::CERTIFY_VIEW, &[])?;
    inspect(ws, "certify-view", &bytes)
}

/// Refusals that name only a race with another admission between the view and the
/// submit, read from the Host's rendering of `CertifyReceiver.Reject` at phase `certify`.
/// `factoryUnavailable` is how `prepare` answers a moved factory root
/// (`ResourceTargetAdmission.observe` at the pinned root); `notAdvancing` with the
/// observed head means another certify landed first, and the re-observation is then
/// `not-due`.
const RACED: [&str; 4] = ["staleAuthority", "staleSystem", "factoryUnavailable", "notAdvancing"];
const RACED_PREFIX: &str = "certify refused raced ";

fn raced(outcome: &Value) -> Option<&'static str> {
    if outcome.get("type").and_then(Value::as_str) != Some("refused") {
        return None;
    }
    let text = |name: &str| {
        outcome
            .get(name)
            .and_then(Value::as_str)
            .and_then(|hex| mini_sdk::hex::decode(hex).ok())
            .map(|bytes| String::from_utf8_lossy(&bytes).trim().to_string())
    };
    if text("phase").as_deref() != Some("certify") {
        return None;
    }
    let detail = text("detail")?;
    let name = detail.strip_prefix("Minidregg.Kernel.CertifyReceiver.Reject.")?;
    RACED.into_iter().find(|raced| *raced == name)
}

fn raced_error(error: &str) -> Option<&'static str> {
    if error.starts_with("local consent refused before signing:") {
        return Some("staleConsent");
    }
    for name in RACED {
        if error.contains(&format!("Minidregg.Kernel.CertifyReceiver.Reject.{name}")) {
            return Some(name);
        }
    }
    None
}

fn certify(ws: &Workspace, control: &str, min_tail: Option<String>) -> Result<Value> {
    let mut races = Vec::new();
    let mut last = None;
    let replanned = crate::replan::replan(
        "certify",
        || {
            let value = match certify_once(ws, control, min_tail.as_deref()) {
                Ok(value) => value,
                Err(error) => match raced_error(&error) {
                    Some(reason) => {
                        races.push(json!({"reason": reason, "detail": error}));
                        return Err(format!("{RACED_PREFIX}{reason}: {error}"));
                    }
                    None => return Err(error),
                },
            };
            match raced(&value) {
                Some(reason) => {
                    races.push(json!({"reason": reason, "certified": value.get("certified")}));
                    let error = format!("{RACED_PREFIX}{reason}: {value}");
                    last = Some(value);
                    Err(error)
                }
                None => Ok(value),
            }
        },
        |error, _| error.starts_with(RACED_PREFIX),
        |_| Ok(()),
    );
    let mut value = match (replanned, last) {
        (Ok(value), _) => value,
        // Exhausted: the last raced refusal is the run's answer, and fails it.
        (Err(error), Some(value)) if error.contains(RACED_PREFIX) => value,
        (Err(error), _) => return Err(error),
    };
    if !races.is_empty() {
        value["racedRefusals"] = json!(races);
    }
    Ok(value)
}

fn certify_once(ws: &Workspace, control: &str, min_tail: Option<&str>) -> Result<Value> {
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
    let plan = invoke(ws, mini_sdk::host_operations::CERTIFY_PLAN, &command)?;
    let header = inspect(ws, "certify-plan", &plan)?;
    let canonical = header
        .get("header")
        .and_then(|h| h.get("canonical"))
        .and_then(Value::as_str)
        .ok_or("certify plan lacks a canonical header")?;
    let header_bytes = mini_sdk::hex::decode(canonical).map_err(|_| "certify plan header is not hex")?;
    let signature = crate::fsio::read_secret_in_private_dir(&ws.key)?.sign(&header_bytes).to_bytes();
    let ingress = invoke(ws, mini_sdk::host_operations::CERTIFY_ASSEMBLE, &mini_sdk::local::pair(&plan, &signature)?)?;
    let outcome = invoke(ws, mini_sdk::host_operations::CERTIFY_SUBMIT, &ingress)?;
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

#[cfg(test)]
mod tests {
    use super::*;

    fn refused(phase: &str, detail: &str) -> Value {
        json!({"type": "refused", "reason": "operation-rejected",
            "phase": mini_sdk::hex::encode(phase.as_bytes()),
            "detail": mini_sdk::hex::encode(detail.as_bytes())})
    }

    #[test]
    fn raced_refusals_are_read_from_the_certify_receivers_rendering_only() {
        let reject = |name: &str| format!("Minidregg.Kernel.CertifyReceiver.Reject.{name}");
        for name in RACED {
            assert_eq!(raced(&refused("certify", &reject(name))), Some(name));
        }
        // Teeth: a refusal that is not a race is final for the run.
        // A held prefix's chain value is permanent: chainMismatch and heightUnavailable are final.
        for other in ["capabilityRejected", "replayedMarker", "validation", "systemUnavailable", "policyRejected",
            "chainMismatch", "heightUnavailable"] {
            assert_eq!(raced(&refused("certify", &reject(other))), None, "{other}");
        }
        assert_eq!(raced(&refused("clock-tick", &reject("staleSystem"))), None);
        assert_eq!(raced(&refused("certify", "Minidregg.Kernel.ClockTickReceiver.Reject.staleAuthority")), None);
        assert_eq!(raced(&refused("certify", &format!("{} extra", reject("staleSystem")))), None);
        assert_eq!(raced(&json!({"type": "not-due"})), None);
        assert_eq!(raced(&json!({"type": "contention"})), None);
    }
}
