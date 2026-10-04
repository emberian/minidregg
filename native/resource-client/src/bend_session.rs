//! Objective source-owned custody signing.
//! Independently retained intent and selected key/role go to mandatory local
//! consent endpoint 227. Only its native-derived ordered headers are signed.
//! An older provider refuses; no offered-plan inspection fallback exists.
use super::*;
use std::collections::BTreeMap;
const CAP: usize = 2_000_000;
pub(crate) fn run(arguments: &[String]) -> Result<()> {
    let (kind, args) = arguments.split_first().ok_or("expected native or return plan kind")?;
    if kind != "native" && kind != "return" {
        return Err("unsupported Objective plan kind".into());
    }
    if args.len() != 14 {
        return Err("expected --host --config --intent --role --plan --key --dir".into());
    }
    let mut options = BTreeMap::new();
    for pair in args.chunks_exact(2) {
        if !["--host", "--config", "--intent", "--role", "--plan", "--key", "--dir"]
            .contains(&pair[0].as_str())
            || options.insert(pair[0].as_str(), pair[1].as_str()).is_some() {
            return Err("unknown or duplicate Objective signer option".into());
        }
    }
    let get = |name: &str| -> Result<&Path> {
        options.get(name).map(|s| Path::new(s)).ok_or_else(|| format!("missing {name}"))
    };
    let host = get("--host")?;
    let config = get("--config")?;
    let intent = get("--intent")?;
    let plan = get("--plan")?;
    let key = get("--key")?;
    let directory = get("--dir")?;
    let role = *options.get("--role").ok_or("missing --role")?;
    if role.is_empty() || role.len() > 128 {
        return Err("Objective custody role must contain 1..128 bytes".into());
    }
    if directory.exists() {
        return Err("Objective signer directory already exists".into());
    }
    mini_sdk::private::check_file(key)?;
    let intended = crate::fsio::read_bounded(intent, CAP)?;
    let candidate = crate::fsio::read_bounded(plan, CAP)?;
    let signing = read_secret(key)?;
    #[cfg(unix)] {
        crate::fsio::create_private_dir(directory)?;
    }
    #[cfg(not(unix))]
    fs::create_dir(directory).map_err(|e| e.to_string())?;
    let retained_intent = directory.join("intent.bin");
    let retained_plan = directory.join("plan.bin");
    write_new(&retained_intent, &intended)?;
    write_new(&retained_plan, &candidate)?;
    // This call must derive expected whole-plan equality and current custody
    // authorization from a Verified frontier and the independent intent.
    // These byte snapshots alone establish neither property.
    let headers = client_consent::objective_headers(host, config, &intended,
        signing.verifying_key().as_bytes(), role, &candidate)?;
    if headers.is_empty() || headers.len() > 32 || (kind == "return" && headers.len() != 1) {
        return Err("Objective native consent returned invalid signing slot count".into());
    }
    if crate::fsio::read_bounded(&retained_intent, CAP)? != intended || crate::fsio::read_bounded(&retained_plan, CAP)? != candidate {
        return Err("retained Objective intent/plan changed".into());
    }
    let signatures = sign_headers(&signing, &headers)?;
    write_json_new(&directory.join("signatures.json"), &signatures)?;
    if kind == "native" {
        encode_signatures(host, config, &signing, headers,
            &directory.join("native-signatures.json"), &directory.join("signatures.bin"))?;
    } else {
        let sig = signatures.as_array().and_then(|v| v.first()).and_then(Value::as_str)
            .ok_or("return detached signature missing")?;
        write_new(&directory.join("signature.bin"), &decode_hex(sig)?)?;
    }
    Ok(())
}
