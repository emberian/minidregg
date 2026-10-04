//! Local native consent over a warm independently admitted source prefix.
//! The remote transport never supplies this executable or its settings.
//!
//! The provider admits the Store's history before its first consent frame. What
//! it admitted is kept as a retained anchor (`Kernel.ConsentAnchor`) in a private
//! file under `~/.mini/consent-anchors/` (or `$MINI_CONSENT_ANCHOR_DIR`), named by
//! and bound to the exact provider file and settings bytes (callers retain the
//! settings in per-attempt copies, so the name is the binding, not a path). The next process offers it (frame 228) before admission, so
//! the provider admits only the records after it, and refuses a Store that
//! rolled back or rewrote the anchored prefix. Another provider build, a
//! replaced provider file or changed settings never see the anchor: they admit
//! from genesis.
use super::*;
use std::process::{Child, ChildStdin, ChildStdout, Stdio};

const CAP: usize = 12_102_760;
/// Custody framing of a retained anchor: this tag, a 32-byte binding of the
/// provider file and settings bytes, then the provider's own anchor bytes.
const ANCHOR_TAG: &[u8] = b"MINI-CONSENT-ANCHOR-CUSTODY/v1\n";
const ANCHOR_CAP: u64 = 4096;
struct Session {
    child: Child,
    input: ChildStdin,
    output: ChildStdout,
    executable: PathBuf,
    settings_bytes: Vec<u8>,
    /// Where this provider's anchor is retained and what it is bound to; `None`
    /// for a codec-only process.
    anchor: Option<AnchorCustody>,
}
struct AnchorCustody {
    path: PathBuf,
    binding: [u8; 32],
    retained: Option<Vec<u8>>,
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
    let settings_bytes=crate::fsio::read_bounded_or_empty(&settings, CAP)?;
    let mut slot=SESSION.lock().map_err(|_|"local consent session lock poisoned")?;
    if let Some(session)=slot.as_ref() {
        if session.executable!=executable||session.settings_bytes!=settings_bytes {
            return Err("local consent executable or settings changed within signing session".into());
        }
    } else {
        *slot=Some(start(executable,&settings,settings_bytes)?);
    }
    // Keep the same provider after candidate refusal; restarting would discard
    // its independently verified frontier. A dead provider remains failed for
    // this process rather than silently verifying an older source from genesis.
    let session=slot.as_mut().unwrap();
    let answer=round_trip(session,operation,payload);
    retain_anchor(session);
    answer
}

/// Start a provider and offer it this binding's retained anchor before any
/// admission. A refusal of the offer (another epoch, noncanonical bytes) is
/// reported, never silently replaced by a genesis admission.
fn start(executable:PathBuf,settings:&Path,settings_bytes:Vec<u8>)->Result<Session> {
    start_in(&anchor_dir()?,executable,settings,settings_bytes)
}
fn start_in(anchors:&Path,executable:PathBuf,settings:&Path,settings_bytes:Vec<u8>)->Result<Session> {
    let binding=anchor_binding(&executable,&settings_bytes)?;
    let path=anchor_path(anchors,&binding);
    let retained=read_anchor(&path,&binding)?;
    let mut child=Command::new(&executable).arg(settings).arg("stdio")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit())
        .spawn().map_err(|e|format!("cannot start local consent provider {}: {e}",executable.display()))?;
    let input=child.stdin.take().ok_or("local consent stdin missing")?;
    let output=child.stdout.take().ok_or("local consent stdout missing")?;
    let mut session=Session{child,input,output,executable,settings_bytes,
        anchor:Some(AnchorCustody{path:path.clone(),binding,retained:retained.clone()})};
    if let Some(anchor)=retained {
        round_trip(&mut session,228,&anchor)
            .map_err(|e|format!("retained consent anchor {}: {e}",path.display()))?;
    }
    Ok(session)
}

/// The private directory of retained anchors.
fn anchor_dir()->Result<PathBuf> {
    if let Some(dir)=std::env::var_os("MINI_CONSENT_ANCHOR_DIR") {
        let dir=PathBuf::from(dir);
        if !dir.is_absolute() {return Err("MINI_CONSENT_ANCHOR_DIR must be absolute".into());}
        return Ok(dir);
    }
    Ok(PathBuf::from(std::env::var_os("HOME").ok_or("retained consent anchors need $HOME or MINI_CONSENT_ANCHOR_DIR")?)
        .join(".mini/consent-anchors"))
}
/// One file per binding: a provider admits only under its own.
fn anchor_path(anchors:&Path,binding:&[u8;32])->PathBuf {
    anchors.join(format!("{}.anchor",hex(binding)))
}
/// The provider file (path and inode identity, size and both times) and the
/// exact settings bytes. A rebuilt, replaced or moved provider, or any settings
/// change, binds differently and admits from genesis.
fn anchor_binding(executable:&Path,settings_bytes:&[u8])->Result<[u8;32]> {
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::MetadataExt;
    let meta=fs::metadata(executable).map_err(|e|format!("local consent provider {}: {e}",executable.display()))?;
    let mut digest=sha2::Sha256::new();
    digest.update(b"MINI-CONSENT-ANCHOR-BINDING/v1\0");
    digest.update((executable.as_os_str().len() as u64).to_le_bytes());
    digest.update(executable.as_os_str().as_bytes());
    for value in [meta.dev(),meta.ino(),meta.size(),meta.mtime() as u64,meta.mtime_nsec() as u64,
        meta.ctime() as u64,meta.ctime_nsec() as u64] {
        digest.update(value.to_le_bytes());
    }
    digest.update(sha2::Sha256::digest(settings_bytes));
    Ok(digest.finalize().into())
}
/// The retained anchor bytes for this binding: `None` when there is no file or
/// it was written under another binding. A file that is not owner-private and
/// regular, or not this custody format, refuses.
fn read_anchor(path:&Path,binding:&[u8;32])->Result<Option<Vec<u8>>> {
    use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
    let file=match OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(path) {
        Ok(file)=>file,
        Err(e) if e.kind()==io::ErrorKind::NotFound=>return Ok(None),
        Err(e)=>return Err(format!("retained consent anchor {}: {e}",path.display())),
    };
    let meta=file.metadata().map_err(|e|e.to_string())?;
    if !meta.is_file()||meta.uid()!=unsafe{libc::geteuid()}||meta.mode()&0o077!=0 {
        return Err(format!("retained consent anchor {} must be an owner-private regular file",path.display()));
    }
    let mut bytes=Vec::new();
    file.take(ANCHOR_CAP+1).read_to_end(&mut bytes).map_err(|e|e.to_string())?;
    if bytes.len() as u64>ANCHOR_CAP {return Err(format!("retained consent anchor {} exceeds its bound",path.display()));}
    let Some(rest)=bytes.strip_prefix(ANCHOR_TAG) else {
        return Err(format!("retained consent anchor {} is not MINI-CONSENT-ANCHOR-CUSTODY/v1",path.display()));
    };
    if rest.len()<=32 {return Err(format!("retained consent anchor {} is truncated",path.display()));}
    if rest[..32]!=binding[..] {return Ok(None);}
    Ok(Some(rest[32..].to_vec()))
}
fn anchor_file(binding:&[u8;32],anchor:&[u8])->Vec<u8> {
    [ANCHOR_TAG,binding.as_slice(),anchor].concat()
}
/// Ask the provider for the anchor of what it admitted and retain it when it
/// moved. Complete or absent (`mini_sdk::durable::replace`): a crash leaves the
/// previous anchor, from which the next provider admits a longer suffix. A
/// failure here costs only that; it is reported, not fatal to the consent.
fn retain_anchor(session:&mut Session) {
    retain_anchor_with(session,&mut |_|Ok(()))
}
fn retain_anchor_with(session:&mut Session,observe:&mut dyn FnMut(mini_sdk::durable::Stage)->io::Result<()>) {
    if session.anchor.is_none() {return;}
    let anchor=match round_trip(session,229,&[]) {
        Ok(anchor)=>anchor,
        Err(_)=>return, // nothing admitted yet (a refused first admission ends the provider)
    };
    let custody=session.anchor.as_mut().unwrap();
    if custody.retained.as_deref()==Some(anchor.as_slice()) {return;}
    if let Some(parent)=custody.path.parent() {
        use std::os::unix::fs::DirBuilderExt;
        if let Err(e)=fs::DirBuilder::new().recursive(true).mode(0o700).create(parent) {
            eprintln!("mini: warning: cannot create {}: {e}",parent.display());
            return;
        }
    }
    match mini_sdk::durable::replace_with(&custody.path,&anchor_file(&custody.binding,&anchor),
        mini_sdk::durable::Perm::Private,observe) {
        Ok(())=>custody.retained=Some(anchor),
        Err(e)=>eprintln!("mini: warning: cannot retain the consent anchor {}: {e}",custody.path.display()),
    }
}
fn headers(bytes:&[u8])->Result<Vec<Vec<u8>>> {
    let value:Value=serde_json::from_slice(bytes).map_err(|e|format!("local consent headers: {e}"))?;
    let rows=value.as_array().ok_or("local consent headers are not a list")?;
    rows.iter().map(|row|decode_hex(row.as_str().ok_or("local consent header is not hex")?)).collect()
}
pub(crate) fn intent(host:&Path,config:&Path,intent:&Path,signing:&SigningKey)->Result<Vec<u8>> {
    let bytes=crate::fsio::read_bounded_or_empty(intent, CAP)?;
    let checked=invoke(host,config,220,&pair(&bytes,&pair(signing.verifying_key().as_bytes(),&[])?)?)?;
    if checked!=bytes {return Err("local consent returned a different retained intent".into());}
    Ok(bytes)
}
pub(crate) fn observation(host:&Path,config:&Path,intent:&Path,signature:&Path,challenge:&Path,signing:&SigningKey)->Result<Vec<Vec<u8>>> {
    let payload=pair(&crate::fsio::read_bounded_or_empty(intent, CAP)?,&pair(signing.verifying_key().as_bytes(),&pair(&crate::fsio::read_bounded_or_empty(signature, CAP)?,&crate::fsio::read_bounded_or_empty(challenge, CAP)?)?)?)?;
    headers(&invoke(host,config,221,&payload)?)
}
pub(crate) fn plan(host:&Path,config:&Path,intent:&Path,plan:&Path,signing:&SigningKey)->Result<Vec<Vec<u8>>> {
    headers(&invoke(host,config,222,&pair(&crate::fsio::read_bounded_or_empty(intent, CAP)?,&pair(signing.verifying_key().as_bytes(),&crate::fsio::read_bounded_or_empty(plan, CAP)?)?)?)?)
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
    let read=|index:usize|->Result<Vec<u8>>{crate::fsio::read_bounded_or_empty(Path::new(args.get(index).ok_or("missing local codec input")?), CAP)};
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
        let mut session=Session{child,input,output,executable:"/bin/sh".into(),settings_bytes:vec![],anchor:None};
        assert!(round_trip(&mut session,222,b"retained").is_err());
    }

    /// A provider stub that logs each request's opcode and answers every frame
    /// with that opcode and the fixed body in `reply_229` for frame 229 (the
    /// retained anchor) or an empty body otherwise.
    fn opcode_stub(dir: &Path, anchor: &[u8]) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        fs::write(dir.join("anchor-body"), anchor).unwrap();
        let path = dir.join("provider");
        fs::write(&path, format!(concat!(
            "#!/bin/sh\n",
            "while :; do\n",
            "  n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \\n')\n",
            "  [ -n \"$n\" ] || exit 0\n",
            "  dd bs=1 count=\"$n\" of='{frame}' 2>/dev/null\n",
            "  op=$(od -An -tu1 -N1 '{frame}' | tr -d ' \\n')\n",
            "  echo \"$op\" >> '{log}'\n",
            "  if [ \"$op\" = 229 ]; then\n",
            "    m=$(( $(wc -c < '{body}') + 1 ))\n",
            "    printf \"$(printf '\\\\%03o\\\\000\\\\000\\\\000\\\\%03o' \"$m\" 229)\"; cat '{body}'\n",
            "  else\n",
            "    printf \"$(printf '\\\\001\\\\000\\\\000\\\\000\\\\%03o' \"$op\")\"\n",
            "  fi\n",
            "done\n"), log = dir.join("opcodes").display(), body = dir.join("anchor-body").display(),
            frame = dir.join("frame").display())).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        path
    }
    fn opcodes(dir: &Path) -> Vec<u8> {
        fs::read_to_string(dir.join("opcodes")).unwrap_or_default().lines()
            .map(|line| line.trim().parse().unwrap()).collect()
    }

    #[test]
    fn retained_anchor_is_offered_only_under_its_exact_binding() {
        let dir = stub_dir("anchor-offer");
        let provider = opcode_stub(&dir, b"ANCHOR-AFTER");
        let settings = dir.join("consent.json");
        fs::write(&settings, b"{}").unwrap();
        // No retained anchor: admission from genesis (no 228), then the anchor
        // of what was admitted is retained.
        let mut session = start_in(&dir.join("anchors"), provider.clone(), &settings, b"{}".to_vec()).unwrap();
        round_trip(&mut session, 220, b"intent").unwrap();
        retain_anchor(&mut session);
        drop(session);
        assert_eq!(opcodes(&dir), vec![220, 229]);
        let binding = anchor_binding(&provider, b"{}").unwrap();
        assert_eq!(read_anchor(&anchor_path(&dir.join("anchors"), &binding), &binding).unwrap().as_deref(), Some(&b"ANCHOR-AFTER"[..]));
        // The next provider is offered it first.
        fs::remove_file(dir.join("opcodes")).unwrap();
        let mut session = start_in(&dir.join("anchors"), provider.clone(), &settings, b"{}".to_vec()).unwrap();
        round_trip(&mut session, 220, b"intent").unwrap();
        drop(session);
        assert_eq!(opcodes(&dir), vec![228, 220]);
        // Changed settings bytes: another binding, so no offer.
        fs::remove_file(dir.join("opcodes")).unwrap();
        let mut session = start_in(&dir.join("anchors"), provider.clone(), &settings, b"{ }".to_vec()).unwrap();
        round_trip(&mut session, 220, b"intent").unwrap();
        drop(session);
        assert_eq!(opcodes(&dir), vec![220]);
        // A replaced provider file (new inode) binds differently too.
        let copy = dir.join("provider-copy");
        fs::copy(&provider, &copy).unwrap();
        fs::rename(&copy, &provider).unwrap();
        assert_ne!(anchor_binding(&provider, b"{}").unwrap(), binding);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn retained_anchor_file_refuses_foreign_or_exposed_bytes() {
        use std::os::unix::fs::PermissionsExt;
        let dir = stub_dir("anchor-file");
        let path = dir.join("consent.json.consent-anchor");
        let binding = [7u8; 32];
        mini_sdk::durable::replace(&path, &anchor_file(&binding, b"A"), mini_sdk::durable::Perm::Private).unwrap();
        assert_eq!(read_anchor(&path, &binding).unwrap().as_deref(), Some(&b"A"[..]));
        assert_eq!(read_anchor(&path, &[8u8; 32]).unwrap(), None);
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(read_anchor(&path, &binding).is_err());
        mini_sdk::durable::replace(&path, b"MINI-CONSENT-ANCHOR-CUSTODY/v0\nxxxx", mini_sdk::durable::Perm::Private).unwrap();
        assert!(read_anchor(&path, &binding).is_err());
        mini_sdk::durable::replace(&path, &anchor_file(&binding, b""), mini_sdk::durable::Perm::Private).unwrap();
        assert!(read_anchor(&path, &binding).is_err());
        let _ = fs::remove_dir_all(&dir);
    }

    /// Crash consistency of the retained anchor: a crash at every durable stage
    /// of retaining a new anchor leaves either the previous anchor or the new
    /// one, whole, under the same binding. Both are admissible offers: an older
    /// anchor only makes the next provider admit a longer suffix.
    #[test]
    fn retained_anchor_survives_a_crash_at_every_stage() {
        use mini_sdk::durable::Stage;
        for stage in [Stage::MidWrite, Stage::BeforeFileSync, Stage::BeforeCommit,
            Stage::AfterCommit, Stage::AfterDirectorySync] {
            let dir = stub_dir("anchor-crash");
            let provider = opcode_stub(&dir, b"NEW-ANCHOR");
            let settings = dir.join("consent.json");
            fs::write(&settings, b"{}").unwrap();
            let binding = anchor_binding(&provider, b"{}").unwrap();
            let path = anchor_path(&dir.join("anchors"), &binding);
            fs::create_dir(dir.join("anchors")).unwrap();
            mini_sdk::durable::replace(&path, &anchor_file(&binding, b"OLD-ANCHOR"), mini_sdk::durable::Perm::Private).unwrap();
            let mut session = start_in(&dir.join("anchors"), provider.clone(), &settings, b"{}".to_vec()).unwrap();
            round_trip(&mut session, 220, b"intent").unwrap();
            retain_anchor_with(&mut session, &mut |at| if at == stage {
                Err(io::Error::other("crash"))
            } else { Ok(()) });
            drop(session);
            let survived = read_anchor(&path, &binding).unwrap().unwrap();
            assert!(survived == b"OLD-ANCHOR" || survived == b"NEW-ANCHOR", "{stage:?}: {survived:?}");
            if matches!(stage, Stage::MidWrite | Stage::BeforeFileSync | Stage::BeforeCommit) {
                assert_eq!(survived, b"OLD-ANCHOR", "{stage:?}");
            } else {
                assert_eq!(survived, b"NEW-ANCHOR", "{stage:?}");
            }
            let _ = fs::remove_dir_all(&dir);
        }
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
        fs::write(path, format!("#!/bin/sh\necho 'debug1: Entering interactive session.' >&2\nwhile :; do\n  n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \\n')\n  [ -n \"$n\" ] || exit 0\n  dd bs=1 count=\"$n\" of=/dev/null 2>/dev/null\n  cat '{}'\ndone\n", reply.display())).unwrap();
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
    let settings_bytes=crate::fsio::read_bounded_or_empty(&settings, CAP)?;
    let mut child=Command::new(&executable).arg(&settings).arg("stdio")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit())
        .spawn().map_err(|e|format!("cannot start local native codec: {e}"))?;
    let input=child.stdin.take().ok_or("local codec stdin missing")?;
    let output=child.stdout.take().ok_or("local codec stdout missing")?;
    let mut session=Session{child,input,output,executable,settings_bytes:settings_bytes.clone(),anchor:None};
    let body=round_trip(&mut session,operation,payload)?;
    if crate::fsio::read_bounded_or_empty(&settings, CAP)?!=settings_bytes{return Err("local native settings changed during codec operation".into());}
    Ok([vec![operation],body].concat())
}

pub(crate) fn plan_operation(operation:u8)->bool {
    matches!(operation,32|36|44|48|50|52|58|66|68|70|74|78|80|82|86|92|96|103|108|113|117|123|126|140|160|170|183|201|206|210|215)
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
    if !mini_sdk::decimal::is_canonical(subject) {return Err("possession subject must be canonical decimal".into());}
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
