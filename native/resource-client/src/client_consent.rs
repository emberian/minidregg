//! Local native consent over a warm independently admitted source prefix.
//! The remote transport never supplies this executable or its settings.
use super::*;
use std::process::{Child, ChildStdin, ChildStdout, Stdio};

const CAP: usize = 12_102_760;
struct Session {
    child: Child,
    input: ChildStdin,
    output: ChildStdout,
    executable: PathBuf,
    settings_bytes: Vec<u8>,
}
impl Drop for Session {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}
static SESSION: Mutex<Option<Session>> = Mutex::new(None);

/// Pure codec operations always use a separately selected local native image.
/// A remote Host digest is not an executable or a local semantic authority.
pub(crate) fn pure_host(host: &Path) -> Result<PathBuf> {
    let selected = PINS.get().map(|pins|pins.semantic.clone()).or_else(||std::env::var_os("MINI_LOCAL_HOST").map(PathBuf::from))
        .or_else(|| (!host.as_os_str().is_empty()).then(|| host.to_path_buf()))
        .ok_or("local author/inspect/signatures/assembly requires MINI_LOCAL_HOST")?;
    if !selected.is_absolute() { return Err("local semantic Host must be an absolute path".into()); }
    let metadata = fs::metadata(&selected).map_err(|e| format!("local semantic Host: {e}"))?;
    if !metadata.is_file() { return Err("local semantic Host must be a regular file".into()); }
    Ok(selected)
}

fn bounded(path: &Path) -> Result<Vec<u8>> {
    let mut bytes=Vec::new();
    File::open(path).map_err(|e|format!("consent input {}: {e}",path.display()))?
        .take((CAP+1) as u64).read_to_end(&mut bytes).map_err(|e|e.to_string())?;
    if bytes.len()>CAP { return Err("local consent input exceeds frame bound".into()); }
    Ok(bytes)
}
fn pair(left: &[u8], right: &[u8]) -> Result<Vec<u8>> {
    let length:u32=left.len().try_into().map_err(|_|"consent pair exceeds bound")?;
    let mut bytes=length.to_le_bytes().to_vec();bytes.extend_from_slice(left);bytes.extend_from_slice(right);
    if bytes.len()>=CAP { return Err("local consent pair exceeds frame bound".into()); }
    Ok(bytes)
}
fn round_trip(session: &mut Session, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
    let size:u32=(payload.len()+1).try_into().map_err(|_|"consent frame exceeds bound")?;
    if size as usize>CAP {return Err("consent frame exceeds bound".into());}
    session.input.write_all(&size.to_le_bytes()).and_then(|_|session.input.write_all(&[operation]))
        .and_then(|_|session.input.write_all(payload)).and_then(|_|session.input.flush())
        .map_err(|e|format!("local consent request failed: {e}"))?;
    let mut width=[0u8;4];session.output.read_exact(&mut width)
        .map_err(|e|format!("local consent provider ended before consent: {e}"))?;
    let size=u32::from_le_bytes(width) as usize;
    if size==0||size>CAP {return Err("local consent response frame refused".into());}
    let mut frame=vec![0;size];session.output.read_exact(&mut frame).map_err(|e|e.to_string())?;
    if frame[0]!=operation {return Err(format!("local consent refused before signing: {}",String::from_utf8_lossy(&frame[1..])));}
    Ok(frame[1..].to_vec())
}
fn invoke(host: &Path, config: &Path, operation:u8, payload:&[u8]) -> Result<Vec<u8>> {
    let executable=PINS.get().map(|pins|pins.consent.clone()).or_else(||std::env::var_os("MINI_CONSENT_HOST").map(PathBuf::from))
        .or_else(||(!host.as_os_str().is_empty()).then(||host.with_file_name("minidregg-client-consent")))
        .ok_or("signing requires an independently selected MINI_CONSENT_HOST")?;
    let settings=PINS.get().map(|pins|pins.config.clone()).or_else(||std::env::var_os("MINI_CONSENT_CONFIG").map(PathBuf::from))
        .unwrap_or_else(||config.to_path_buf());
    if !executable.is_absolute()||!settings.is_absolute() {return Err("local consent executable/settings must be absolute".into());}
    let settings_bytes=bounded(&settings)?;
    let mut slot=SESSION.lock().map_err(|_|"local consent session lock poisoned")?;
    if let Some(session)=slot.as_ref() {
        if session.executable!=executable||session.settings_bytes!=settings_bytes {
            return Err("local consent executable or settings changed within signing session".into());
        }
    } else {
        let mut child=Command::new(&executable).arg(&settings).arg("stdio")
            .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit())
            .spawn().map_err(|e|format!("cannot start local consent provider {}: {e}",executable.display()))?;
        let input=child.stdin.take().ok_or("local consent stdin missing")?;
        let output=child.stdout.take().ok_or("local consent stdout missing")?;
        *slot=Some(Session{child,input,output,executable,settings_bytes});
    }
    // Keep the same provider after candidate refusal; restarting would discard
    // its independently verified frontier. A dead provider remains failed for
    // this process rather than silently verifying an older source from genesis.
    round_trip(slot.as_mut().unwrap(),operation,payload)
}
fn headers(bytes:&[u8])->Result<Vec<Vec<u8>>> {
    let value:Value=serde_json::from_slice(bytes).map_err(|e|format!("local consent headers: {e}"))?;
    let rows=value.as_array().ok_or("local consent headers are not a list")?;
    rows.iter().map(|row|decode_hex(row.as_str().ok_or("local consent header is not hex")?)).collect()
}
pub(crate) fn intent(host:&Path,config:&Path,intent:&Path,signing:&SigningKey)->Result<Vec<u8>> {
    let bytes=bounded(intent)?;
    let checked=invoke(host,config,220,&pair(&bytes,&pair(signing.verifying_key().as_bytes(),&[])?)?)?;
    if checked!=bytes {return Err("local consent returned a different retained intent".into());}
    Ok(bytes)
}
pub(crate) fn observation(host:&Path,config:&Path,intent:&Path,signature:&Path,challenge:&Path,signing:&SigningKey)->Result<Vec<Vec<u8>>> {
    let payload=pair(&bounded(intent)?,&pair(signing.verifying_key().as_bytes(),&pair(&bounded(signature)?,&bounded(challenge)?)?)?)?;
    headers(&invoke(host,config,221,&payload)?)
}
pub(crate) fn plan(host:&Path,config:&Path,intent:&Path,plan:&Path,signing:&SigningKey)->Result<Vec<Vec<u8>>> {
    headers(&invoke(host,config,222,&pair(&bounded(intent)?,&pair(signing.verifying_key().as_bytes(),&bounded(plan)?)?)?)?)
}

#[derive(Clone, PartialEq, Eq)]
struct Pins { semantic:PathBuf, consent:PathBuf, config:PathBuf }
static PINS: OnceLock<Pins> = OnceLock::new();
/// Private local workspace/attempt custody record; never filled from an
/// operator response or a remotely inspected JSON object.
pub(crate) fn pin_record(value:&Value)->Result<()> {
    let path=|name:&str|->Result<PathBuf>{
        let path=PathBuf::from(value.get(name).and_then(Value::as_str).ok_or("local consent pin is missing a path")?);
        if !path.is_absolute(){return Err("local consent pin path must be absolute".into());}Ok(path)
    };
    let pins=Pins{semantic:path("semanticHost")?,consent:path("consentHost")?,config:path("config")?};
    match PINS.get(){Some(old) if old!=&pins=>Err("local consent pins differ within one process".into()),Some(_)=>Ok(()),None=>PINS.set(pins).map_err(|_|"cannot pin local consent custody".into())}
}
pub(crate) fn configured_record()->Result<Option<Value>> {
    if let Some(pins)=PINS.get(){return Ok(Some(json!({"semanticHost":pins.semantic,"consentHost":pins.consent,"config":pins.config})));}
    let paths=["MINI_LOCAL_HOST","MINI_CONSENT_HOST","MINI_CONSENT_CONFIG"].map(std::env::var_os);
    if paths.iter().all(Option::is_none){return Ok(None);}
    let [Some(semantic),Some(consent),Some(config)]=paths else {return Err("durable local consent selection requires MINI_LOCAL_HOST, MINI_CONSENT_HOST and MINI_CONSENT_CONFIG together".into());};
    let value=json!({"semanticHost":PathBuf::from(semantic),"consentHost":PathBuf::from(consent),"config":PathBuf::from(config)});
    pin_record(&value)?;Ok(Some(value))
}

/// The full-peer provider also serves its own pure native codecs. This keeps
/// retained authoring, inspection and assembly on the exact consent source.
pub(crate) fn codec_process(host:&Path,config:&Path,args:&[&OsStr])->Result<Option<Output>> {
    if PINS.get().is_none() && std::env::var_os("MINI_CONSENT_HOST").is_none(){return Ok(None);}
    let verb=args.first().and_then(|s|s.to_str()).ok_or("missing local codec command")?;
    let read=|index:usize|->Result<Vec<u8>>{bounded(Path::new(args.get(index).ok_or("missing local codec input")?))};
    let kind=|label:&OsStr,bytes:Vec<u8>|->Result<Vec<u8>>{
        let label=label.to_str().ok_or("local codec kind is not UTF-8")?.as_bytes();
        let width:u16=label.len().try_into().map_err(|_|"local codec kind exceeds bound")?;
        let mut payload=width.to_le_bytes().to_vec();payload.extend_from_slice(label);payload.extend(bytes);Ok(payload)
    };
    let (op,payload,destination)=match verb {
        "author" | "inspect" if args.len()==4 => (if verb=="author" {7} else {8},kind(args[1],read(2)?)?,args[3]),
        "signatures" if args.len()==3 => (9,read(1)?,args[2]),
        "observe-assemble" | "assemble" if args.len()==4 => (if verb=="assemble" {11} else {10},pair(&read(1)?,&read(2)?)?,args[3]),
        _=>return Err("unsupported local native codec arguments".into())
    };
    let frame=codec_frame(host,config,op,&payload)?;
    let bytes=frame[1..].to_vec();write_new(Path::new(destination),&bytes)?;
    #[cfg(unix)] {use std::os::unix::process::ExitStatusExt;
        Ok(Some(Output{status:std::process::ExitStatus::from_raw(0),stdout:bytes,stderr:Vec::new()}))}
    #[cfg(not(unix))] {Err("local native consent codecs currently require Unix".into())}
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn consent_pair_preserves_exact_order_and_bounds() {
        assert_eq!(pair(b"intent",b"plan").unwrap(),[6u32.to_le_bytes().as_slice(),b"intent",b"plan"].concat());
        assert!(pair(&vec![0;CAP],b"plan").is_err());
    }
    #[test]
    fn consent_headers_preserve_duplicates_order_and_reject_unframed_values() {
        assert_eq!(headers(br#"["aabb","ff","aabb"]"#).unwrap(),vec![vec![170,187],vec![255],vec![170,187]]);
        for bad in [br#"{"headers":["aabb"]}"#.as_slice(),br#"[true]"#,br#"["zz"]"#] { assert!(headers(bad).is_err()); }
    }
    #[test]
    fn consent_round_trip_refusal_never_returns_header_bytes() {
        let mut child=Command::new("/bin/sh").args(["-c","printf '\\015\\000\\000\\000\\377changed-plan'"])
            .stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
        let input=child.stdin.take().unwrap();let output=child.stdout.take().unwrap();
        let mut session=Session{child,input,output,executable:"/bin/sh".into(),settings_bytes:vec![]};
        assert!(round_trip(&mut session,222,b"retained").is_err());
    }

    // A friend's client reaches the box over `--remote` (an `ssh:DEST` socket
    // address relayed by `mini socket-proxy`). The box answers a plan request;
    // the client's independently selected consent provider reconstructs the
    // plan it expects. One changed byte in the served plan must refuse before
    // any signing consumer receives the bytes.
    const STUB_PLAN: &[u8] = b"DREGG/PLAN/stub-transfer-10";
    const STUB_OPERATION: u8 = 32;
    fn stub_dir(label: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("mini-remote-consent-{label}-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&dir).unwrap();
        dir
    }
    fn framed(body: &[u8]) -> Vec<u8> {
        [(body.len() as u32).to_le_bytes().as_slice(), body].concat()
    }
    /// One frame in (exact-length reads: dd bs=1), one canned frame out, until EOF.
    fn frame_stub(path: &Path, reply: &Path) {
        use std::os::unix::fs::PermissionsExt;
        fs::write(path, format!("#!/bin/sh\nwhile :; do\n  n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \\n')\n  [ -n \"$n\" ] || exit 0\n  dd bs=1 count=\"$n\" of=/dev/null 2>/dev/null\n  cat '{}'\ndone\n", reply.display())).unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(0o700)).unwrap();
    }
    fn remote_plan_run(served_plan: &[u8]) -> std::process::Output {
        let dir = stub_dir("run");
        // Box side: the ssh program the client starts is a stub serving `served_plan`.
        fs::write(dir.join("socket-reply"), framed(&[[STUB_OPERATION].as_slice(), served_plan].concat())).unwrap();
        frame_stub(&dir.join("ssh"), &dir.join("socket-reply"));
        // Friend side: the local consent provider derives the exact expected plan.
        fs::write(dir.join("consent-reply"), framed(&[[224u8].as_slice(), STUB_PLAN].concat())).unwrap();
        frame_stub(&dir.join("consent"), &dir.join("consent-reply"));
        fs::write(dir.join("consent.json"), br#"{"stub":"consent settings"}"#).unwrap();
        fs::write(dir.join("host.json"), br#"{"domain":"7"}"#).unwrap();
        let output = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "client_consent::tests::remote_plan_stub_worker", "--ignored", "--nocapture", "--test-threads=1"])
            .env("MINI_SSH", dir.join("ssh"))
            .env("MINI_CONSENT_HOST", dir.join("consent"))
            .env("MINI_CONSENT_CONFIG", dir.join("consent.json"))
            .env_remove("MINI_LOCAL_HOST")
            .env("MINI_REMOTE_CONSENT_STUB_CONFIG", dir.join("host.json"))
            .output().unwrap();
        let _ = fs::remove_dir_all(&dir);
        output
    }
    #[test]
    #[ignore = "worker for remote_signing_plan_with_one_changed_byte_is_refused_before_signing"]
    fn remote_plan_stub_worker() {
        let config = PathBuf::from(std::env::var_os("MINI_REMOTE_CONSENT_STUB_CONFIG").expect("stub config"));
        match crate::transport::invoke(Path::new("ssh:plan-stub"), &config, STUB_OPERATION, b"retained request") {
            Ok(reply) => println!("REMOTE-PLAN-ACCEPTED {}", hex(&reply)),
            Err(error) => println!("REMOTE-PLAN-REFUSED {error}"),
        }
    }
    #[test]
    fn remote_signing_plan_with_one_changed_byte_is_refused_before_signing() {
        // Control: the served plan equals the local reconstruction and passes.
        let honest = remote_plan_run(STUB_PLAN);
        let text = String::from_utf8_lossy(&honest.stdout);
        assert!(honest.status.success(), "{text}");
        let expected = hex(&[[STUB_OPERATION].as_slice(), STUB_PLAN].concat());
        assert!(text.contains(&format!("REMOTE-PLAN-ACCEPTED {expected}")), "{text}");
        // One plan byte changed by the box: refused, and no plan bytes returned.
        let mut changed = STUB_PLAN.to_vec();
        let last = changed.len() - 1;
        changed[last] ^= 0x01;
        let forged = remote_plan_run(&changed);
        let text = String::from_utf8_lossy(&forged.stdout);
        assert!(forged.status.success(), "{text}");
        assert!(!text.contains("REMOTE-PLAN-ACCEPTED"), "{text}");
        assert!(text.contains("REMOTE-PLAN-REFUSED local native specialized consent returned a different plan"), "{text}");
    }
}

/// Local producer for wrappers retaining native session frames themselves.
/// Existing retained frames must be compared with this local derivation before
/// reuse; the frame's original remote origin is not consent authority.
pub(crate) fn codec_frame(host:&Path,config:&Path,operation:u8,payload:&[u8])->Result<Vec<u8>> {
    if !(7..=11).contains(&operation){return Err("not a local codec opcode".into());}
    local_frame(host, config, operation, payload)
}

/// Full native pure codec authority is selected independently of the remote
/// operator. Specialized grammars remain authored/decoded by that real image.
/// This process never receives keys, and these operations never mutate source.
fn local_frame(host:&Path,config:&Path,operation:u8,payload:&[u8])->Result<Vec<u8>> {
    let executable=pure_host(host)?;
    let settings=PINS.get().map(|pins|pins.config.clone())
        .or_else(||std::env::var_os("MINI_CONSENT_CONFIG").map(PathBuf::from))
        .unwrap_or_else(||config.to_path_buf());
    if !settings.is_absolute(){return Err("local native settings must be absolute".into());}
    let settings_bytes=bounded(&settings)?;
    let mut child=Command::new(&executable).arg(&settings).arg("stdio")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit())
        .spawn().map_err(|e|format!("cannot start local native codec: {e}"))?;
    let input=child.stdin.take().ok_or("local codec stdin missing")?;
    let output=child.stdout.take().ok_or("local codec stdout missing")?;
    let mut session=Session{child,input,output,executable,settings_bytes:settings_bytes.clone()};
    let body=round_trip(&mut session,operation,payload)?;
    if bounded(&settings)?!=settings_bytes{return Err("local native settings changed during codec operation".into());}
    Ok([vec![operation],body].concat())
}

pub(crate) fn plan_operation(operation:u8)->bool {
    matches!(operation,32|36|44|48|50|52|58|66|68|70|74|78|80|82|86|92|96|103|108|113|117|123|126|140|160|170|183|201|206)
}
/// Always check adapted operator-authored plans before returning bytes to any
/// signing consumer. A native refusal or dead verifier never falls back to the
/// remotely proposed plan.
pub(crate) fn operator_plan(host:&Path,config:&Path,operation:u8,request:&[u8],candidate:&[u8])->Result<()> {
    let request=[vec![operation],request.to_vec()].concat();
    let expected=invoke(host,config,224,&pair(&request,candidate)?)?;
    if expected!=candidate{return Err("local native specialized consent returned a different plan".into());}
    Ok(())
}


/// Enrollment possession is a source-independent native domain frame over the
/// complete retained command, with the selected new custody key and subject.
pub(crate) fn possession(host:&Path,config:&Path,command:&[u8],subject:&str,key:&SigningKey,candidate:&[u8])->Result<Vec<u8>> {
    if subject.is_empty() || !subject.bytes().all(|b|b.is_ascii_digit()) || (subject.len()>1 && subject.starts_with('0')) {return Err("possession subject must be canonical decimal".into());}
    let selected=serde_json::to_vec(&json!({"subject":subject.to_string(),"publicKey":hex(key.verifying_key().as_bytes())})).map_err(|e|e.to_string())?;
    let checked=invoke(host,config,226,&pair(command,&pair(&selected,candidate)?)?)?;
    if checked!=candidate{return Err("native possession frame changed".into());}Ok(checked)
}

/// Objective-only source WIP. Endpoint 227 must reconstruct the complete
/// expected typed plan from independently retained intent and Verified source,
/// bind the selected custody key to this role, and return its own ordered
/// headers after whole-plan equality. An older provider refuses this endpoint;
/// callers must never fall back to the offered plan's inspected headers.
pub(crate) fn objective_headers(host: &Path, config: &Path, retained_intent: &[u8],
    selected_public_key: &[u8], role: &str, candidate_plan: &[u8]) -> Result<Vec<Vec<u8>>> {
    if selected_public_key.len() != 32 || role.is_empty() || role.len() > 128 {
        return Err("invalid local Objective custody selection".into());
    }
    let selection = serde_json::to_vec(&json!({"publicKey":hex(selected_public_key),"role":role}))
        .map_err(|error|error.to_string())?;
    let payload = pair(retained_intent, &pair(&selection, candidate_plan)?)?;
    headers(&invoke(host, config, 227, &payload)?)
}
