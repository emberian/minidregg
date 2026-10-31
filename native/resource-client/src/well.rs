//! Realm wells (lane K-WELL), minimal client. A well is an account born in a
//! realm (`well new` = `workspace create --kind account --in REALM`); its law is
//! the predicate it is born with. `well mint|burn|floor` authors the command with the
//! Host (`author well-command`), asks the Host for the exact header to sign
//! (op 123), signs it with the workspace key, has the Host assemble the ingress
//! (op 124) and submits it (op 125). The Host decides everything; this module
//! only retains the bytes. `well ledger` is the operator-local `well-ledger`.
//!
//! Custody: one request (op, well, account, amount, capability) is one attempt chain
//! `attempts/well-OP-KEY-N`. A rerun of the same request never authors a second command (a
//! fresh nonce would be a second mint): it finds the chain's newest attempt and reports it. An
//! attempt whose exact ingress is retained without a decided outcome is resubmitted only by name
//! (`--action resubmit --attempt A`: the SAME ingress bytes, so the same nonce); there is no
//! receipt-only lookup for op 125 (review Q6). Every 255 reply is decoded by the local codec,
//! and only a decoded `refused` is reported as a refusal. A further operation of a decided
//! request is the member's decision: `--again`.

use crate::workspace;
use crate::{absolute, hex, path, process, session_invoke, Args, Result, SOCKET};
use ed25519_dalek::Signer;
use serde_json::{json, Value};
use std::ffi::{OsStr, OsString};
use std::fs::{self};
use std::path::{Path, PathBuf};

fn text(value: OsString, label: &str) -> Result<String> {
    value
        .into_string()
        .map_err(|_| format!("{label} is not UTF-8"))
}

fn member<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("missing string field {key}"))
}


/// A workspace reference name, or a decimal resource id.
fn resolve(root: &Path, name: &str) -> Result<(String, Option<Value>)> {
    if mini_sdk::decimal::is_canonical_max(name, 80) {
        return Ok((name.to_owned(), None));
    }
    let reference = workspace::reference(root, name)?;
    Ok((member(&reference, "target")?.to_owned(), Some(reference)))
}

fn reference_capability(reference: &Option<Value>, label: &str) -> Result<String> {
    let reference = reference
        .as_ref()
        .ok_or_else(|| format!("{label} is a bare id; pass --capability"))?;
    reference
        .get("operationCapability")
        .or_else(|| reference.get("observeCapability"))
        .and_then(Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| format!("{label} reference names no capability"))
}

fn pair(first: &[u8], second: &[u8]) -> Result<Vec<u8>> {
    let length: u32 = first
        .len()
        .try_into()
        .map_err(|_| "well pair exceeds u32")?;
    let mut bytes = length.to_le_bytes().to_vec();
    bytes.extend_from_slice(first);
    bytes.extend_from_slice(second);
    Ok(bytes)
}

fn retain(path: &Path, bytes: &[u8]) -> Result<()> {
    crate::create_public(path, bytes)
}

/// One host operation over the pinned session socket. A 255 reply is a
/// refusal whose encoded outcome is reported verbatim.
fn invoke(
    host: &Path,
    socket: &Path,
    config: &Path,
    operation: u8,
    payload: &[u8],
    label: &str,
) -> Result<Vec<u8>> {
    let reply = session_invoke(host, socket, config, operation, payload)?;
    match reply.split_first() {
        Some((&code, body)) if code == operation => Ok(body.to_vec()),
        Some((byte, body)) if crate::is_outcome_frame(*byte) => Err(format!(
            "host refused {label}; encoded refusal: {}",
            hex(body)
        )),
        _ => Err(format!("host returned an invalid frame for {label}")),
    }
}

/// The decoded outcome of an attempt's retained `outcome.bin`, if any (written to `outcome.json`).
fn decoded(host: &Path, config: &Path, attempt: &Path) -> Result<Option<Value>> {
    let bin = attempt.join("outcome.bin");
    if !bin.is_file() {
        return Ok(None);
    }
    let json = attempt.join("outcome.json");
    if !json.exists() {
        process(host, config, &[OsStr::new("inspect"), OsStr::new("outcome"), bin.as_os_str(), json.as_os_str()])?;
    }
    serde_json::from_slice(&fs::read(&json).map_err(|e| e.to_string())?).map(Some).map_err(|e| e.to_string())
}

/// How an answer was framed, retained as `outcome.class` beside it: `answer` (op 125's own byte),
/// `no-record` (`NO_RECORD` 253: decided before any append) or `undecided` (`HOST_OUTCOME` 255,
/// whatever it decodes to).
fn class_of(code: u8) -> &'static str {
    if code == crate::RESPONSE_NO_RECORD { "no-record" } else if code == crate::RESPONSE_HOST_OUTCOME { "undecided" } else { "answer" }
}

/// Whether a retained attempt is decided (a further command is the member's decision): an
/// `answer` that confirmed or refused, or a `no-record`. An `undecided` class, or none, is not.
fn decided(attempt: &Path, kind: Option<&str>) -> bool {
    match fs::read_to_string(attempt.join("outcome.class")).as_deref() {
        Ok("no-record") => true,
        Ok("answer") => matches!(kind, Some("confirmed" | "refused")),
        _ => false,
    }
}

/// Submit (op 125) the attempt's retained exact ingress and report the Host's decoded outcome.
/// A marker frame is retained as the outcome too and decoded; its class is the marker's.
fn submit_ingress(host: &Path, socket: &Path, config: &Path, attempt: &Path, report: Value) -> Result<()> {
    let ingress = fs::read(attempt.join("ingress.bin")).map_err(|e| e.to_string())?;
    let bin = attempt.join("outcome.bin");
    let _ = fs::remove_file(attempt.join("outcome.json"));
    let _ = fs::remove_file(attempt.join("outcome.class"));
    let reply = session_invoke(host, socket, config, mini_sdk::host_operations::REALM_WELL_SUBMIT, &ingress)?;
    let class = match reply.split_first() {
        Some((&code, body)) if code == 125 || crate::is_outcome_frame(code) => {
            if bin.exists() {
                fs::remove_file(&bin).map_err(|e| e.to_string())?;
            }
            retain(&bin, body)?;
            retain(&attempt.join("outcome.class"), class_of(code).as_bytes())?;
            class_of(code)
        }
        _ => return Err(format!("host returned an invalid frame for well submit; the exact ingress is retained: \
            `mini well --action resubmit --attempt {}`", attempt.display())),
    };
    let outcome = decoded(host, config, attempt)?.ok_or("well outcome was not retained")?;
    println!("{}", merge(report, json!({"attempt":attempt,"outcome":outcome})));
    match (class, outcome.get("type").and_then(Value::as_str)) {
        ("answer", Some("confirmed")) if crate::charged_line(&outcome).is_none() => Ok(()),
        ("no-record", _) => {
            crate::note_host_decision(crate::HostDecision::Frame { command: "well submit".into(),
                byte: crate::RESPONSE_NO_RECORD, encoded: fs::read(&bin).map_err(|e| e.to_string())?, decoded: Some(outcome) });
            Err("the Host answered this well command with no record: nothing happened".into())
        }
        ("answer", Some("refused")) => {
            crate::note_host_decision(crate::HostDecision::Outcome(outcome));
            Err("the Host refused this well command".into())
        }
        _ => {
            crate::note_host_decision(crate::HostDecision::Outcome(outcome.clone()));
            Err(format!("undecided: well submit answered {}; the exact ingress is retained: \
                `mini well --action resubmit --dir WS --attempt {}`", crate::outcome_type(Some(&outcome)), attempt.display()))
        }
    }
}

fn merge(mut base: Value, extra: Value) -> Value {
    if let (Some(base), Value::Object(extra)) = (base.as_object_mut(), extra) {
        base.extend(extra);
    }
    base
}

/// The newest attempt of this request's chain and the next free one.
fn chain(root: &Path, op: &str, request: &Value) -> Result<(Option<PathBuf>, PathBuf)> {
    let key = &crate::fleet::digest(&serde_json::to_vec(request).map_err(|e| e.to_string())?)[..16];
    let name = |n: u32| root.join("attempts").join(format!("well-{op}-{key}-{n}"));
    let mut n = 0;
    while name(n + 1).exists() {
        n += 1;
    }
    Ok(((n > 0).then(|| name(n)), name(n + 1)))
}

fn command(root: &Path, mut args: Args, op: &str) -> Result<()> {
    let workspace = workspace::load(root)?;
    let (well, well_ref) = resolve(root, &text(args.required("well")?, "well")?)?;
    let (account, account_ref) = resolve(root, &text(args.required("account")?, "account")?)?;
    let amount = text(args.required("amount")?, "amount")?;
    if !mini_sdk::decimal::is_canonical_max(&amount, 80) {
        return Err("amount must be decimal".into());
    }
    let capability = match args.optional("capability") {
        Some(value) => text(value, "capability")?,
        None if op == "mint" || op == "floor" => reference_capability(&well_ref, "well")?,
        None => reference_capability(&account_ref, "account")?,
    };
    if !mini_sdk::decimal::is_canonical_max(&capability, 80) {
        return Err("capability must be decimal".into());
    }
    let named = args.optional("attempt").map(|value| absolute(&path(value))).transpose()?;
    let again = match args.optional("again").as_deref().map(|v| v.to_str()) {
        None | Some(Some("false")) => false,
        Some(Some("true")) => true,
        _ => return Err("--again must be true or false".into()),
    };
    args.finish()?;
    let host = PathBuf::from(member(&workspace, "host")?);
    let config = PathBuf::from(member(&workspace, "config")?);
    let socket = SOCKET
        .get()
        .ok_or("well commands require a pinned persistent Host socket")?
        .clone();
    let request = json!({"op":op,"well":well,"account":account,"amount":amount,"capability":capability});
    let attempt = match named {
        Some(attempt) => attempt,
        None => {
            let (latest, next) = chain(root, op, &request)?;
            if let Some(latest) = latest {
                let outcome = decoded(&host, &config, &latest)?;
                let kind = outcome.as_ref().and_then(|o| o.get("type")).and_then(Value::as_str).map(str::to_owned);
                if latest.join("ingress.bin").is_file() && !again {
                    let state = kind.unwrap_or_else(|| "not decided (no retained outcome)".into());
                    return Err(format!(
                        "a previous well {op} of this request is retained at {} ({state}); nothing new is authored. \
                         An undecided one is resubmitted exactly with `mini well --action resubmit --dir WS --attempt {}`; \
                         a decided one is followed only by your decision: --again",
                        latest.display(), latest.display()));
                }
                if again && latest.join("ingress.bin").is_file() && !decided(&latest, kind.as_deref()) {
                    return Err(format!("undecided: the previous well {op} at {} may have been admitted; resubmit it exactly \
                        (`mini well --action resubmit --dir WS --attempt {}`) before another", latest.display(), latest.display()));
                }
            }
            next
        }
    };
    if attempt.exists() {
        return Err(format!("refusing to reuse {}", attempt.display()));
    }
    fs::create_dir_all(&attempt).map_err(|error| error.to_string())?;
    let source = json!({"subject":member(&workspace, "subject")?,"capability":capability,
        "well":well,"op":op,"account":account,"amount":amount,"nonce":crate::fsio::random_nonce()?});
    let source_path = attempt.join("command.json");
    retain(
        &source_path,
        &serde_json::to_vec_pretty(&source).map_err(|error| error.to_string())?,
    )?;
    let command_path = attempt.join("command.bin");
    process(
        &host,
        &config,
        &[
            OsStr::new("author"),
            OsStr::new("well-command"),
            source_path.as_os_str(),
            command_path.as_os_str(),
        ],
    )?;
    let command = fs::read(&command_path).map_err(|error| error.to_string())?;
    let plan = invoke(&host, &socket, &config, mini_sdk::host_operations::REALM_WELL_PLAN, &command, "well plan")?;
    retain(&attempt.join("plan.bin"), &plan)?;
    let plan_json = attempt.join("plan.json");
    process(
        &host,
        &config,
        &[
            OsStr::new("inspect"),
            OsStr::new("well-plan"),
            attempt.join("plan.bin").as_os_str(),
            plan_json.as_os_str(),
        ],
    )?;
    let view: Value = serde_json::from_slice(&fs::read(&plan_json).map_err(|e| e.to_string())?)
        .map_err(|error| error.to_string())?;
    if member(&view, "commandBytes")? != hex(&command) {
        return Err("well plan names a different command".into());
    }
    let header = mini_sdk::hex::decode(member(&view, "header")?).map_err(|e| e.0)?;
    let key = crate::read_secret(Path::new(member(&workspace, "key")?))?;
    let signature = key.sign(&header).to_bytes();
    let ingress = invoke(
        &host,
        &socket,
        &config,
        mini_sdk::host_operations::REALM_WELL_ASSEMBLE,
        &pair(&plan, &signature)?,
        "well assembly",
    )?;
    retain(&attempt.join("ingress.bin"), &ingress)?;
    submit_ingress(&host, &socket, &config, &attempt,
        json!({"type":"minidregg-well-outcome-v1","op":op,"well":well,"account":account,"amount":amount}))
}

/// `well --action resubmit --attempt A`: the SAME retained ingress again (the same nonce: never a
/// second command).
fn resubmit(root: &Path, mut args: Args) -> Result<()> {
    let attempt = absolute(&path(args.required("attempt")?))?;
    args.finish()?;
    let workspace = workspace::load(root)?;
    let host = PathBuf::from(member(&workspace, "host")?);
    let config = PathBuf::from(member(&workspace, "config")?);
    let socket = SOCKET.get().ok_or("well commands require a pinned persistent Host socket")?.clone();
    let attempts = fs::canonicalize(root.join("attempts")).map_err(|e| e.to_string())?;
    if fs::canonicalize(&attempt).map_err(|e| e.to_string())?.parent() != Some(attempts.as_path()) {
        return Err("well attempt must belong directly to this workspace".into());
    }
    if !attempt.join("ingress.bin").is_file() {
        return Err(format!("{} retains no exact ingress: nothing was submitted", attempt.display()));
    }
    submit_ingress(&host, &socket, &config, &attempt, json!({"type":"minidregg-well-outcome-v1","resubmitted":true}))
}

fn ledger(root: &Path, mut args: Args) -> Result<()> {
    let output = absolute(&path(args.required("output")?))?;
    args.finish()?;
    let workspace = workspace::load(root)?;
    let host = PathBuf::from(member(&workspace, "host")?);
    let config = PathBuf::from(member(&workspace, "config")?);
    let result = std::process::Command::new(&host)
        .arg(&config)
        .arg("well-ledger")
        .arg(&output)
        .output()
        .map_err(|error| format!("cannot run {}: {error}", host.display()))?;
    if !result.status.success() {
        return Err(format!(
            "well-ledger failed: {}",
            String::from_utf8_lossy(&result.stderr).trim()
        ));
    }
    print!(
        "{}",
        fs::read_to_string(&output).map_err(|error| error.to_string())?
    );
    Ok(())
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = text(args.required("action")?, "well action")?;
    let root = absolute(&path(args.required("dir")?))?;
    match action.as_str() {
        "new" => {
            let name = text(args.required("name")?, "well name")?;
            let realm = text(args.required("in")?, "realm name")?;
            let law = path(args.required("law")?);
            args.finish()?;
            let workspace = workspace::load(&root)?;
            workspace::create(
                &root,
                &workspace,
                &name,
                "declared",
                &law,
                Some(&realm),
                "account",
                None,
                None,
                // An account holds no object field: its balances are the Book's.
                None,
            )
        }
        "mint" | "burn" | "floor" => command(&root, args, &action),
        "resubmit" => resubmit(&root, args),
        "ledger" => ledger(&root, args),
        _ => Err("well action must be new, mint, burn, floor, resubmit or ledger".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pair_prefixes_first_length() {
        assert_eq!(pair(&[1, 2], &[3]).unwrap(), vec![2, 0, 0, 0, 1, 2, 3]);
    }

    #[test]
    fn decimal_names_are_ids() {
        assert!(mini_sdk::decimal::is_canonical_max("0", 80));
        assert!(mini_sdk::decimal::is_canonical_max("1234", 80));
        assert!(!mini_sdk::decimal::is_canonical_max("01", 80));
        assert!(!mini_sdk::decimal::is_canonical_max("gold", 80));
    }
}
