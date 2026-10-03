//! Custody for exact current source-owned Bend native/release signing plans.
//! The configured Host re-prepares and inspects the whole canonical plan on its
//! current image. No arbitrary-header signing entry point is exposed here.
//! Additive source WIP: Host route/module dispatch must join the next cohort.
use super::*;
use std::collections::BTreeMap;
const CAP: usize = 2_000_000;
fn bounded(path:&Path)->Result<Vec<u8>> {
    use std::io::Read;
    let mut bytes=Vec::new();
    fs::File::open(path).map_err(|e|e.to_string())?.take((CAP+1) as u64)
        .read_to_end(&mut bytes).map_err(|e|e.to_string())?;
    if bytes.len()>CAP { return Err("Bend signing plan capacity exceeded".into()); }
    Ok(bytes)
}
pub(crate) fn run(arguments:&[String])->Result<()> {
    let (kind,args)=arguments.split_first().ok_or("expected native or return plan kind")?;
    if kind!="native" && kind!="return" { return Err("unsupported Bend plan kind".into()); }
    if args.len()!=10 { return Err("expected --host --config --plan --key --dir".into()); }
    let mut options=BTreeMap::new();
    for pair in args.chunks_exact(2) {
        if !["--host","--config","--plan","--key","--dir"].contains(&pair[0].as_str())
            || options.insert(pair[0].as_str(),pair[1].as_str()).is_some() {
            return Err("unknown or duplicate Bend signer option".into());
        }
    }
    let get=|name:&str|->Result<&Path> {
        options.get(name).map(|s|Path::new(s)).ok_or_else(||format!("missing {name}"))
    };
    let host=get("--host")?;
    let config=get("--config")?;
    let plan=get("--plan")?;
    let key=get("--key")?;
    let directory=get("--dir")?;
    if directory.exists() { return Err("Bend signer directory already exists".into()); }
    let metadata=fs::symlink_metadata(key).map_err(|e|e.to_string())?;
    if !metadata.file_type().is_file() { return Err("Bend custody key is not a regular file".into()); }
    #[cfg(unix)] {
        use std::os::unix::fs::{PermissionsExt,DirBuilderExt};
        if metadata.permissions().mode() & 0o077 != 0 {
            return Err("Bend custody key must exclude group/other access".into());
        }
        fs::DirBuilder::new().mode(0o700).create(directory).map_err(|e|e.to_string())?;
    }
    #[cfg(not(unix))]
    fs::create_dir(directory).map_err(|e|e.to_string())?;
    let bytes=bounded(plan)?;
    let retained=directory.join("plan.bin");
    write_new(&retained,&bytes)?;
    let presentation=directory.join("checked-plan.json");
    // This source-owned route compares the whole plan with current re-preparation;
    // an ordinary structural inspect/JSON success marker does not suffice.
    process(host,config,&[
        OsStr::new("bend-session-signing-check"),OsStr::new(kind),
        retained.as_os_str(),presentation.as_os_str()
    ])?;
    let shown:Value=serde_json::from_slice(&bounded(&presentation)?).map_err(|e|e.to_string())?;
    if shown.get("canonical").and_then(Value::as_str)!=Some(hex(&bytes).as_str()) {
        return Err("Host checked a different canonical Bend signing plan".into());
    }
    if bounded(&retained)?!=bytes { return Err("retained Bend signing plan changed".into()); }
    let headers=match kind.as_str() {
        "native" if shown.get("type").and_then(Value::as_str)==Some("bend-current-native-plan-v1") =>
            plan_headers(&shown)?,
        "return" if shown.get("type").and_then(Value::as_str)==Some("bend-current-return-plan-v1") =>
            vec![decode_hex(shown.get("header").and_then(Value::as_str)
                .ok_or("current return plan lacks source header")?)?],
        _=>return Err("Host returned unexpected Bend current-plan inspection".into())
    };
    if headers.is_empty() || headers.len()>32 { return Err("Bend signer slot capacity".into()); }
    let signing=read_secret(key)?;
    // Reuse exact existing resource-client Ed25519 signing implementation.
    let signatures=sign_headers(&signing,&headers);
    write_json_new(&directory.join("signatures.json"),&signatures)?;
    if kind=="native" {
        encode_signatures(host,config,&signing,headers,
            &directory.join("native-signatures.json"),&directory.join("signatures.bin"))?;
    } else {
        let sig=signatures.as_array().and_then(|v|v.first()).and_then(Value::as_str)
            .ok_or("return detached signature missing")?;
        write_new(&directory.join("signature.bin"),&decode_hex(sig)?)?;
    }
    Ok(())
}
