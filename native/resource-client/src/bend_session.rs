//! Objective source-owned custody signing.
//! Independently retained intent and selected key/role go to mandatory local
//! consent endpoint 227. Only its native-derived ordered headers are signed.
//! An older provider refuses; no offered-plan inspection fallback exists.
use super::*;
use std::collections::BTreeMap;
const CAP: usize = 2_000_000;
fn bounded(path: &Path) -> Result<Vec<u8>> {
    use std::io::Read;
    let mut bytes = Vec::new();
    fs::File::open(path).map_err(|e| e.to_string())?.take((CAP + 1) as u64)
        .read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    if bytes.is_empty() || bytes.len() > CAP {
        return Err("Objective intent/plan must be nonempty and within capacity".into());
    }
    Ok(bytes)
}
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
    let metadata = fs::symlink_metadata(key).map_err(|e| e.to_string())?;
    if !metadata.file_type().is_file() {
        return Err("Objective custody key is not a regular file".into());
    }
    #[cfg(unix)] {
        use std::os::unix::fs::PermissionsExt;
        if metadata.permissions().mode() & 0o077 != 0 {
            return Err("Objective custody key must exclude group/other access".into());
        }
    }
    let intended = bounded(intent)?;
    let candidate = bounded(plan)?;
    let signing = read_secret(key)?;
    #[cfg(unix)] {
        use std::os::unix::fs::DirBuilderExt;
        fs::DirBuilder::new().mode(0o700).create(directory).map_err(|e| e.to_string())?;
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
    if bounded(&retained_intent)? != intended || bounded(&retained_plan)? != candidate {
        return Err("retained Objective intent/plan changed".into());
    }
    let signatures = sign_headers(&signing, &headers);
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
