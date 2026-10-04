//! A signed member invocation of a published Objective method.
//!
//! From the member's own retained request (source and input signed queries
//! already inside it) the LOCAL native Host derives the final command
//! (`objective-quote`: one command-free evaluation, layout, the receiver's full
//! gate). The member signs a prepare intent for exactly that command, the
//! serving Host prepares the signing plan, and the local consent provider's
//! endpoint 227 re-derives the command from the same retained request and
//! compares the whole plan before any transaction header is signed. The call
//! is assembled, retained durably and submitted; a lost reply is recovered by
//! `mini retry --attempt DIR --mode lookup` on the retained call, never by
//! re-submitting.
use super::*;

pub(crate) fn submit(host: &Path, config: &Path, request: &Path, intent_nonce: &str, key: &Path,
    directory: &Path, prepare_only: bool) -> Result<()> {
    if host.as_os_str().is_empty() || !host.is_absolute() {
        return Err("objective-invoke derives its command on a local native Host: pass an absolute --host".into());
    }
    if !mini_sdk::decimal::is_canonical(intent_nonce) {
        return Err("--intent-nonce must be canonical decimal".into());
    }
    create_dir(directory)?;
    let retained_config = directory.join("config.json");
    copy_new(config, &retained_config)?;
    write_manifest(directory, host, &retained_config, "submit")?;
    let retained_request = directory.join("request.json");
    copy_new(request, &retained_request)?;
    let request_bin = directory.join("request.bin");
    let quote_json = directory.join("quote.json");
    local_process(host, &retained_config, &[OsStr::new("author"), OsStr::new("objective-request"),
        retained_request.as_os_str(), request_bin.as_os_str()])?;
    local_process(host, &retained_config, &[OsStr::new("objective-quote"), request_bin.as_os_str(),
        OsStr::new(intent_nonce), quote_json.as_os_str()])?;
    let quote: Value = serde_json::from_slice(&fs::read(&quote_json).map_err(|e| e.to_string())?)
        .map_err(|e| format!("objective quote: {e}"))?;
    let field = |name: &str| -> Result<Vec<u8>> {
        decode_hex(quote.get(name).and_then(Value::as_str).ok_or_else(|| format!("quote has no {name}"))?)
    };
    let intent_bin = directory.join("prepare-intent.bin");
    write_new(&intent_bin, &field("intent")?)?;
    write_new(&directory.join("command.bin"), &field("command")?)?;
    let signing = read_secret(key)?;
    let observed = authorize_observation(host, &retained_config, &intent_bin, OsStr::new("binary"),
        &signing, directory)?;
    let plan_bin = directory.join("plan.bin");
    host_files(host, &retained_config, &[Path::new("prepare"), &observed.signed, &plan_bin])?;
    inspect(host, &retained_config, "plan", &plan_bin, &directory.join("plan.json"))?;
    let request_bytes = fs::read(&request_bin).map_err(|e| e.to_string())?;
    let plan_bytes = fs::read(&plan_bin).map_err(|e| e.to_string())?;
    let headers = client_consent::objective_headers(host, &retained_config, &request_bytes,
        signing.verifying_key().as_bytes(), "invoker", &plan_bytes)?;
    if headers.is_empty() || headers.len() > 32 {
        return Err("Objective native consent returned an invalid signing slot count".into());
    }
    let signatures_json = directory.join("transaction-signatures.json");
    let signatures_bin = directory.join("transaction-signatures.bin");
    encode_signatures(host, &retained_config, &signing, headers, &signatures_json, &signatures_bin)?;
    let call = directory.join("call.bin");
    host_files(host, &retained_config, &[Path::new("assemble"), &plan_bin, &signatures_bin, &call])?;
    sync_retained_call(directory, &call)?;
    if prepare_only {
        return Ok(());
    }
    let outcome_bin = directory.join("outcome.bin");
    host_files(host, &retained_config, &[Path::new("submit"), &call, &outcome_bin])?;
    let outcome = inspect(host, &retained_config, "outcome", &outcome_bin, &directory.join("outcome.json"))?;
    confirmed_outcome(&outcome, true)
}
