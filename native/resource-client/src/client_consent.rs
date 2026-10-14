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
use std::process::{Child, Stdio};

const CAP: usize = 12_102_760;
/// Custody framing of a retained anchor: this tag, a 32-byte binding of the
/// provider file and settings bytes, then the provider's own anchor bytes.
const ANCHOR_TAG: &[u8] = b"MINI-CONSENT-ANCHOR-CUSTODY/v1\n";
const ANCHOR_CAP: u64 = 4096;
struct Session {
    /// The provider child this process started; `None` when the frames go to
    /// this workspace binding's resident provider (`connect_resident`).
    child: Option<Child>,
    input: Box<dyn Write + Send>,
    output: Box<dyn Read + Send>,
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
        if let Some(child) = self.child.as_mut() {
            let _ = child.kill();
            let _ = child.wait();
        }
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
    let (answer,body)=exchange(session,operation,payload)?;
    if answer!=operation {
        let detail=String::from_utf8_lossy(&body);
        if operation==221&&answer==255&&detail.starts_with(STALE_OBSERVATION_TAG) {
            STALE_OBSERVATION.store(true,std::sync::atomic::Ordering::Relaxed);
        }
        return Err(format!("local consent refused before signing: {detail}"));
    }
    Ok(body)
}
/// One frame out, one frame in: the reply's operation byte and its body, unjudged.
fn exchange(session: &mut Session, operation: u8, payload: &[u8]) -> Result<(u8, Vec<u8>)> {
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
    let body=frame.split_off(1);
    Ok((frame[0],body))
}

/// `Kernel.NativeClientConsent.staleObservationTag`: the provider's refusal of an
/// observation challenge that answers this exact retained intent and signature at
/// another source height than the one it admitted (the source moved between the
/// Host's challenge and the local check). Every other refusal stays terminal.
pub(crate) const STALE_OBSERVATION_TAG: &str = "stale observation:";
/// Set only from a provider's observation (221) refusal frame carrying the tag.
static STALE_OBSERVATION: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// Whether the last observation consent was refused as stale; clears the record.
pub(crate) fn take_stale_observation() -> bool {
    STALE_OBSERVATION.swap(false, std::sync::atomic::Ordering::Relaxed)
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
    } else if resident_enabled() {
        *slot=Some(connect_resident(&executable,&settings,settings_bytes)?);
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
    let mut session=Session{child:Some(child),input:Box::new(input),output:Box::new(output),executable,settings_bytes,
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
    let checked=invoke(host,config,if thin_mode(){230}else{220},&pair(&bytes,&pair(signing.verifying_key().as_bytes(),&[])?)?)?;
    if checked!=bytes {return Err("local consent returned a different retained intent".into());}
    Ok(bytes)
}
pub(crate) fn observation(host:&Path,config:&Path,intent:&Path,signature:&Path,challenge:&Path,signing:&SigningKey)->Result<Vec<Vec<u8>>> {
    let payload=pair(&crate::fsio::read_bounded_or_empty(intent, CAP)?,&pair(signing.verifying_key().as_bytes(),&pair(&crate::fsio::read_bounded_or_empty(signature, CAP)?,&crate::fsio::read_bounded_or_empty(challenge, CAP)?)?)?)?;
    headers(&invoke(host,config,if thin_mode(){231}else{221},&payload)?)
}
pub(crate) fn plan(host:&Path,config:&Path,intent:&Path,plan:&Path,signing:&SigningKey)->Result<Vec<Vec<u8>>> {
    if thin_mode() { return thin_plan(host,config,intent,plan,signing); }
    headers(&invoke(host,config,222,&pair(&crate::fsio::read_bounded_or_empty(intent, CAP)?,&pair(signing.verifying_key().as_bytes(),&crate::fsio::read_bounded_or_empty(plan, CAP)?)?)?)?)
}

/// Thin consent (`MINI_THIN_CONSENT=1`): frames 230-232, which read no Store.
/// The provider checks what custody signs against its own command and the
/// target views the Host served under the member's observe grants
/// (`Kernel.NativeThinConsent`). A turn it cannot display is refused with the
/// unsigned input named; nothing falls back to a replay or to signing unchecked.
pub(crate) fn thin_mode()->bool { std::env::var("MINI_THIN_CONSENT").as_deref()==Ok("1") }

static THIN_VIEWS: std::sync::Mutex<Option<Vec<PathBuf>>> = std::sync::Mutex::new(None);

/// The served resource views of the next thin plan's targets, in target order.
pub(crate) fn set_thin_views(views:Vec<PathBuf>)->Result<()> {
    *THIN_VIEWS.lock().map_err(|_|"thin view slot poisoned")?=Some(views);
    Ok(())
}

/// `StreamCodec.nat`: base-255 little-endian digits, then the terminator 255.
fn stream_nat(mut value:usize)->Vec<u8> {
    let mut out=Vec::new();
    while value>0 { out.push((value%255) as u8); value/=255; }
    out.push(255);
    out
}
/// `StreamCodec.list bytesStream`.
fn stream_byte_list(items:&[Vec<u8>])->Vec<u8> {
    let mut out=stream_nat(items.len());
    for item in items { out.extend(stream_nat(item.len())); out.extend_from_slice(item); }
    out
}

fn thin_plan(host:&Path,config:&Path,intent:&Path,plan:&Path,signing:&SigningKey)->Result<Vec<Vec<u8>>> {
    let paths=THIN_VIEWS.lock().map_err(|_|"thin view slot poisoned")?.clone()
        .ok_or("thin consent has no served target views; nothing signed")?;
    let mut views=Vec::new();
    for path in &paths { views.push(crate::fsio::read_bounded_or_empty(path, CAP)?); }
    let payload=pair(&crate::fsio::read_bounded_or_empty(intent, CAP)?,&pair(signing.verifying_key().as_bytes(),
        &pair(&crate::fsio::read_bounded_or_empty(plan, CAP)?,&stream_byte_list(&views))?)?)?;
    let reply=invoke(host,config,232,&payload)?;
    let value:Value=serde_json::from_slice(&reply).map_err(|e|format!("thin consent reply: {e}"))?;
    let display=value.get("display").cloned().ok_or("thin consent reply lacks display")?;
    if let Some(directory)=plan.parent() {
        write_json_new(&directory.join("thin-display.json"),&display)?;
    }
    eprintln!("thin consent shows: {}",display);
    let rows=value.get("headers").and_then(Value::as_array).ok_or("thin consent reply lacks headers")?;
    rows.iter().map(|row|decode_hex(row.as_str().ok_or("thin consent header is not hex")?)).collect()
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

/// Authoring, inspection and assembly (the pure codec verbs) go through this process's one local
/// storeless codec child (`local_frame`), never a Host process per verb.
pub(crate) fn codec_process(host:&Path,config:&Path,args:&[&OsStr])->Result<Output> {
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
        Ok(Output{status:std::process::ExitStatus::from_raw(0),stdout:bytes,stderr:Vec::new()})}
    #[cfg(not(unix))] {Err("local native consent codecs currently require Unix".into())}
}

/// One provider per workspace binding, kept across `mini` processes.
///
/// A `mini` process used to start its own provider, which admitted the Store
/// again from the retained anchor (a full Store open, the image cut and
/// validated at the anchor, the records after it re-executed) before its first
/// frame, and dropped that warm frontier on exit. The resident provider is that
/// same in-process provider, kept: `mini consent-resident` holds ONE provider
/// child for a binding (`anchor_binding`: provider file identity and settings
/// bytes), started exactly as `start_in` starts one (the retained anchor is
/// offered first), and relays each client's frames to it one at a time. Every
/// frame still refreshes against the Store and admits the exact new suffix
/// natively; nothing is signed that the provider did not derive.
///
/// What a per-process start also checked, each client connection still checks:
/// the first frame of a connection is preceded by frame 233
/// (`ConsentAnchor.recheckStore`), the anchor comparison of a resume against the
/// held admission, so a rolled-back or rewritten Store refuses the next command
/// as a new provider would. A refusal there, or a provider that dies, ends the
/// resident provider; the next command starts a new one from the retained
/// anchor. The socket lives in the owner-private anchor directory and both ends
/// check that the peer is this user. It is the client's own process: the
/// serving Host never sees it. `MINI_CONSENT_RESIDENT=0` keeps the provider in
/// the `mini` process.
fn resident_enabled()->bool { std::env::var("MINI_CONSENT_RESIDENT").as_deref()!=Ok("0") }
const RESIDENT_IDLE_S: u64 = 600;
/// `r-<first 16 bytes of the binding>.<suffix>`: a Unix socket path must fit `sun_path` (108 bytes).
fn resident_path(dir:&Path,binding:&[u8;32],suffix:&str)->PathBuf { dir.join(format!("r-{}.{suffix}",hex(&binding[..16]))) }
/// The anchor directory, created owner-private, refused when it is not.
fn private_anchor_dir()->Result<PathBuf> {
    use std::os::unix::fs::{DirBuilderExt, MetadataExt};
    let dir=anchor_dir()?;
    fs::DirBuilder::new().recursive(true).mode(0o700).create(&dir).map_err(|e|format!("{}: {e}",dir.display()))?;
    let meta=fs::symlink_metadata(&dir).map_err(|e|format!("{}: {e}",dir.display()))?;
    if !meta.is_dir()||meta.uid()!=unsafe{libc::geteuid()}||meta.mode()&0o077!=0 {
        return Err(format!("consent anchor directory {} must be an owner-private directory",dir.display()));
    }
    Ok(dir)
}
/// A connection to a listening resident provider of this user, or an error.
fn resident_stream(socket:&Path)->Result<std::os::unix::net::UnixStream> {
    use std::os::unix::fs::FileTypeExt;
    let meta=fs::symlink_metadata(socket).map_err(|e|e.to_string())?;
    if !meta.file_type().is_socket()||!mini_sdk::private::owned(&meta) {
        return Err(format!("{} is not this user's socket",socket.display()));
    }
    let stream=std::os::unix::net::UnixStream::connect(socket).map_err(|e|e.to_string())?;
    if crate::transport::peer_uid(&stream)?!=unsafe{libc::geteuid()} {
        return Err("resident consent provider runs as another user".into());
    }
    Ok(stream)
}
/// Connect to this binding's resident provider, starting it when none listens.
fn connect_resident(executable:&Path,settings:&Path,settings_bytes:Vec<u8>)->Result<Session> {
    use std::os::unix::fs::OpenOptionsExt;
    use std::os::unix::process::CommandExt;
    let dir=private_anchor_dir()?;
    let binding=anchor_binding(executable,&settings_bytes)?;
    let socket=resident_path(&dir,&binding,"sock");
    let stream=match resident_stream(&socket) {
        Ok(stream)=>stream,
        Err(_)=>{
            let log=resident_path(&dir,&binding,"log");
            let errors=OpenOptions::new().create(true).append(true).mode(0o600).custom_flags(libc::O_NOFOLLOW)
                .open(&log).map_err(|e|format!("{}: {e}",log.display()))?;
            let mini=std::env::current_exe().map_err(|e|format!("resident consent provider: {e}"))?;
            let mut command=Command::new(mini);
            command.arg("consent-resident").arg("--consent").arg(executable).arg("--settings").arg(settings)
                .stdin(Stdio::null()).stdout(Stdio::null()).stderr(errors);
            // Its own session: it outlives this process and never takes its terminal signals.
            unsafe { command.pre_exec(|| if libc::setsid()<0 {Err(io::Error::last_os_error())} else {Ok(())}); }
            let mut daemon=command.spawn().map_err(|e|format!("cannot start the resident consent provider: {e}"))?;
            let began=std::time::Instant::now();
            loop {
                if let Ok(stream)=resident_stream(&socket) {break stream;}
                if let Some(status)=daemon.try_wait().map_err(|e|e.to_string())? {
                    // Exit 0 without a socket: another start holds the binding's lock and is
                    // still starting; keep waiting for its socket.
                    if !status.success() {
                        return Err(format!("resident consent provider failed to start ({status}); see {}",log.display()));
                    }
                }
                if began.elapsed()>std::time::Duration::from_secs(300) {
                    return Err(format!("resident consent provider did not listen within 300 s; see {}",log.display()));
                }
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
        }
    };
    let input=stream.try_clone().map_err(|e|e.to_string())?;
    Ok(Session{child:None,input:Box::new(input),output:Box::new(stream),executable:executable.to_path_buf(),settings_bytes,anchor:None})
}

/// Removes the resident provider's socket and PID file when it ends, if they are still its own.
struct ResidentFiles { socket: PathBuf, pid: PathBuf, identity: (u64,u64) }
impl Drop for ResidentFiles {
    fn drop(&mut self) {
        use std::os::unix::fs::MetadataExt;
        if fs::symlink_metadata(&self.socket).is_ok_and(|m|(m.dev(),m.ino())==self.identity) {
            let _=fs::remove_file(&self.socket);
        }
        let _=fs::remove_file(&self.pid);
    }
}
struct Resident { session: Session, ended: bool }

/// `mini consent-resident --consent EXECUTABLE --settings SETTINGS`: hold one
/// provider for this binding and serve its frames on the binding's socket until
/// the provider ends or no frame arrives for `MINI_CONSENT_IDLE_S` (600) seconds.
pub(crate) fn resident(executable:PathBuf,settings:PathBuf)->Result<()> {
    let idle=std::time::Duration::from_secs(std::env::var("MINI_CONSENT_IDLE_S").ok()
        .and_then(|v|v.parse().ok()).unwrap_or(RESIDENT_IDLE_S));
    resident_in(&private_anchor_dir()?,executable,settings,idle)
}
fn resident_in(dir:&Path,executable:PathBuf,settings:PathBuf,idle:std::time::Duration)->Result<()> {
    use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
    use std::os::unix::io::AsRawFd;
    use std::sync::{Arc, atomic::{AtomicBool, AtomicUsize}};
    if !executable.is_absolute()||!settings.is_absolute() {return Err("local consent executable/settings must be absolute".into());}
    let settings_bytes=crate::fsio::read_bounded_or_empty(&settings, CAP)?;
    let dir=dir.to_path_buf();
    let binding=anchor_binding(&executable,&settings_bytes)?;
    let lock_path=resident_path(&dir,&binding,"lock");
    let lock=OpenOptions::new().create(true).read(true).write(true).mode(0o600).custom_flags(libc::O_NOFOLLOW)
        .open(&lock_path).map_err(|e|format!("{}: {e}",lock_path.display()))?;
    if unsafe{libc::flock(lock.as_raw_fd(),libc::LOCK_EX|libc::LOCK_NB)}!=0 {
        return Ok(()); // another resident provider holds this binding
    }
    let socket=resident_path(&dir,&binding,"sock");
    crate::transport::clear_stale_socket(&socket)?;
    let session=start_in(&dir,executable,&settings,settings_bytes)?;
    let listener=std::os::unix::net::UnixListener::bind(&socket)
        .map_err(|e|format!("resident consent socket {}: {e}",socket.display()))?;
    fs::set_permissions(&socket,fs::Permissions::from_mode(0o600)).map_err(|e|e.to_string())?;
    let meta=fs::symlink_metadata(&socket).map_err(|e|e.to_string())?;
    let pid=resident_path(&dir,&binding,"pid");
    let _files=ResidentFiles{socket:socket.clone(),pid:pid.clone(),identity:(meta.dev(),meta.ino())};
    mini_sdk::durable::replace(&pid,format!("{}\n",std::process::id()).as_bytes(),mini_sdk::durable::Perm::Private)
        .map_err(|e|format!("{}: {e}",pid.display()))?;
    listener.set_nonblocking(true).map_err(|e|e.to_string())?;
    let shared=Arc::new(Mutex::new(Resident{session,ended:false}));
    let last=Arc::new(Mutex::new(std::time::Instant::now()));
    let active=Arc::new(AtomicUsize::new(0));
    let ended=Arc::new(AtomicBool::new(false));
    loop {
        if ended.load(std::sync::atomic::Ordering::Acquire) {return Ok(());}
        match listener.accept() {
            Ok((stream,_))=>{
                active.fetch_add(1,std::sync::atomic::Ordering::AcqRel);
                let (shared,last,active,ended)=(shared.clone(),last.clone(),active.clone(),ended.clone());
                std::thread::spawn(move||{
                    serve_resident(stream,&shared,&last,&ended);
                    active.fetch_sub(1,std::sync::atomic::Ordering::AcqRel);
                });
            }
            Err(e) if e.kind()==io::ErrorKind::WouldBlock=>{
                let quiet=last.lock().map(|t|t.elapsed()).unwrap_or_default();
                if active.load(std::sync::atomic::Ordering::Acquire)==0&&quiet>idle {return Ok(());}
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
            Err(e)=>return Err(format!("resident consent provider accept: {e}")),
        }
    }
}
/// One client connection: frames in, the provider's answers out, one frame at a
/// time across all connections. The connection's first frame is preceded by the
/// Store re-check (233); 228, 229 and 233 are the resident provider's own.
fn serve_resident(stream:std::os::unix::net::UnixStream,shared:&Mutex<Resident>,
        last:&Mutex<std::time::Instant>,ended:&std::sync::atomic::AtomicBool) {
    if stream.set_nonblocking(false).is_err() {return;}
    if crate::transport::peer_uid(&stream).ok()!=Some(unsafe{libc::geteuid()}) {return;}
    let (mut input,mut output)=match stream.try_clone() {Ok(reader)=>(reader,stream),Err(_)=>return};
    let mut rechecked=false;
    loop {
        let mut width=[0u8;4];
        if input.read_exact(&mut width).is_err() {return;}
        let size=u32::from_le_bytes(width) as usize;
        if size==0||size>CAP {return;}
        let mut frame=vec![0;size];
        if input.read_exact(&mut frame).is_err() {return;}
        if let Ok(mut t)=last.lock() {*t=std::time::Instant::now();}
        let operation=frame[0];
        let (answer,body)=match shared.lock() {
            Err(_)=>(255,b"resident consent provider lock poisoned".to_vec()),
            Ok(mut resident)=>{
                if resident.ended {
                    (255,b"the resident consent provider ended; the next command starts a new one".to_vec())
                } else if matches!(operation,228|229|233) {
                    (255,format!("frame {operation} is reserved to the resident consent provider").into_bytes())
                } else {
                    let checked=if rechecked {Ok(())} else {
                        match exchange(&mut resident.session,233,&[]) {
                            Ok((233,_))=>Ok(()),
                            Ok((_,detail))=>Err(String::from_utf8_lossy(&detail).into_owned()),
                            Err(e)=>Err(e),
                        }
                    };
                    rechecked=true;
                    match checked.and_then(|_|exchange(&mut resident.session,operation,&frame[1..])) {
                        Ok(reply)=>{retain_anchor(&mut resident.session);reply}
                        Err(e)=>{
                            resident.ended=true;
                            ended.store(true,std::sync::atomic::Ordering::Release);
                            (255,e.into_bytes())
                        }
                    }
                }
            }
        };
        let reply=[(body.len() as u32+1).to_le_bytes().as_slice(),&[answer],&body].concat();
        if output.write_all(&reply).and_then(|_|output.flush()).is_err() {return;}
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn thin_view_list_is_the_lean_byte_list_codec() {
        // StreamCodec.nat: base-255 little-endian digits then 255; list = count then items.
        assert_eq!(stream_nat(0), vec![255]);
        assert_eq!(stream_nat(254), vec![254, 255]);
        assert_eq!(stream_nat(255), vec![0, 1, 255]);
        assert_eq!(stream_byte_list(&[]), vec![255]);
        assert_eq!(stream_byte_list(&[vec![7, 8], vec![]]), vec![2, 255, 2, 255, 7, 8, 255]);
    }
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
        let mut session=Session{child:Some(child),input:Box::new(input),output:Box::new(output),executable:"/bin/sh".into(),settings_bytes:vec![],anchor:None};
        assert!(round_trip(&mut session,222,b"retained").is_err());
    }

    /// A provider stub answering one refusal frame (255) carrying `detail`.
    fn refusing(detail:&str)->Session {
        let mut body=vec![255u8];body.extend_from_slice(detail.as_bytes());
        let mut frame=(body.len() as u32).to_le_bytes().to_vec();frame.extend_from_slice(&body);
        // Read the whole request (4 + 1 + 8 bytes) first, so the answer never races a closed pipe.
        let script=format!("dd bs=1 count=13 >/dev/null 2>&1; printf '{}'",frame.iter().map(|b|format!("\\{b:03o}")).collect::<String>());
        let mut child=Command::new("/bin/sh").args(["-c",&script])
            .stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
        let input=child.stdin.take().unwrap();let output=child.stdout.take().unwrap();
        Session{child:Some(child),input:Box::new(input),output:Box::new(output),executable:"/bin/sh".into(),settings_bytes:vec![],anchor:None}
    }
    #[test]
    fn only_a_provider_stale_observation_refusal_is_recorded_as_stale() {
        let _guard=crate::replan::TEST_LOCK.lock().unwrap_or_else(|e|e.into_inner());
        let _=take_stale_observation();
        let stale="stale observation: the remote challenge answers this intent at source height 36; the locally admitted source is at height 37";
        let error=round_trip(&mut refusing(stale),221,b"retained").unwrap_err();
        assert!(error.contains(stale),"{error}");
        assert!(take_stale_observation());
        assert!(!take_stale_observation());
        // A changed intent is refused by name and is never stale.
        let error=round_trip(&mut refusing("remote challenge differs from locally prepared intent"),221,b"retained").unwrap_err();
        assert!(error.ends_with("remote challenge differs from locally prepared intent"),"{error}");
        assert!(!take_stale_observation());
        // The tag counts only on an observation frame.
        let _=round_trip(&mut refusing(stale),222,b"retained").unwrap_err();
        assert!(!take_stale_observation());
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

    /// The resident provider: one provider for every connection of its binding; each
    /// connection's first frame is preceded by the Store re-check (233); the anchor is
    /// retained (229) after every frame; 228/229/233 from a client never reach the
    /// provider; an idle provider ends and removes its socket and PID file.
    #[test]
    fn resident_provider_rechecks_each_connection_and_serves_all_of_them() {
        // A short directory: the socket path must fit sun_path.
        let dir = PathBuf::from(format!("/tmp/mcr-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir(&dir).unwrap();
        let provider = opcode_stub(&dir, b"ANCHOR-R");
        let settings = dir.join("consent.json");
        fs::write(&settings, b"{}").unwrap();
        let anchors = dir.join("anchors");
        fs::create_dir(&anchors).unwrap();
        let binding = anchor_binding(&provider, b"{}").unwrap();
        let socket = resident_path(&anchors, &binding, "sock");
        let (a, p, s) = (anchors.clone(), provider.clone(), settings.clone());
        let daemon = std::thread::spawn(move || resident_in(&a, p, s, std::time::Duration::from_millis(400)));
        let connect = || {
            for _ in 0..2000 {
                if let Ok(stream) = resident_stream(&socket) {
                    let input = stream.try_clone().unwrap();
                    return Session{child:None,input:Box::new(input),output:Box::new(stream),
                        executable:provider.clone(),settings_bytes:b"{}".to_vec(),anchor:None};
                }
                std::thread::sleep(std::time::Duration::from_millis(5));
            }
            panic!("resident provider never listened");
        };
        let mut first = connect();
        assert_eq!(round_trip(&mut first, 220, b"intent").unwrap(), Vec::<u8>::new());
        assert_eq!(round_trip(&mut first, 221, b"observe").unwrap(), Vec::<u8>::new());
        let mut second = connect();
        assert_eq!(round_trip(&mut second, 222, b"plan").unwrap(), Vec::<u8>::new());
        for reserved in [228u8, 229, 233] {
            let error = round_trip(&mut second, reserved, b"x").unwrap_err();
            assert!(error.contains("reserved to the resident consent provider"), "{error}");
        }
        assert_eq!(opcodes(&dir), vec![233, 220, 229, 221, 229, 233, 222, 229]);
        assert_eq!(read_anchor(&anchor_path(&anchors, &binding), &binding).unwrap().as_deref(), Some(&b"ANCHOR-R"[..]));
        assert!(resident_path(&anchors, &binding, "pid").exists());
        drop(first); drop(second);
        daemon.join().unwrap().unwrap();
        assert!(!socket.exists() && !resident_path(&anchors, &binding, "pid").exists());
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
    /// A stand-in `codec` loop: counts its starts, answers frame i with `reply-i` (else `reply`).
    fn codec_stub(dir: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let path = dir.join("codec-host");
        fs::write(&path, format!("#!/bin/sh\necho start >> '{d}/starts'\ni=0\nwhile :; do\n  n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \\n')\n  [ -n \"$n\" ] || exit 0\n  dd bs=1 count=\"$n\" of=/dev/null 2>/dev/null\n  i=$((i+1))\n  if [ -f '{d}/reply-'$i ]; then cat '{d}/reply-'$i; else cat '{d}/reply'; fi\ndone\n", d = dir.display())).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        path
    }
    /// One storeless codec loop answers every codec frame of the same image and
    /// settings; changed settings bytes or a replaced image file start another.
    #[test]
    fn codec_loop_is_reused_only_for_the_same_image_and_settings() {
        use std::os::unix::fs::PermissionsExt;
        let _codec = codec_test_lock();
        let dir = stub_dir("codec-reuse");
        let inner = opcode_stub(&dir, b"");
        let host = dir.join("host");
        fs::write(&host, format!("#!/bin/sh\necho start >> '{}'\nexec '{}'\n",
            dir.join("starts").display(), inner.display())).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let settings = dir.join("settings.json");
        fs::write(&settings, b"{}").unwrap();
        let starts = || fs::read_to_string(dir.join("starts")).unwrap_or_default().lines().count();
        for operation in [7u8, 8, 9, 10, 11] {
            assert_eq!(local_frame(&host, &settings, operation, b"payload").unwrap(), vec![operation]);
        }
        assert_eq!((starts(), opcodes(&dir)), (1, vec![7, 8, 9, 10, 11]));
        fs::write(&settings, b"{ }").unwrap();
        local_frame(&host, &settings, 7, b"payload").unwrap();
        assert_eq!(starts(), 2);
        let copy = dir.join("host-copy");
        fs::copy(&host, &copy).unwrap();
        fs::rename(&copy, &host).unwrap();
        local_frame(&host, &settings, 7, b"payload").unwrap();
        assert_eq!(starts(), 3);
        *CODEC.lock().unwrap() = None;
        let _ = fs::remove_dir_all(&dir);
    }
    /// One codec child serves every pure frame of a process, a refusal included: the refusal is
    /// named by the child's own `inspect outcome` decode, and the same child answers the next frame.
    #[test]
    fn one_codec_child_serves_the_process_and_names_its_refusals() {
        let dir = stub_dir("codec");
        let _codec = codec_test_lock();
        fs::write(dir.join("settings.json"), b"{}").unwrap();
        fs::write(dir.join("reply"), framed(b"\x07ok")).unwrap();
        let host = codec_stub(&dir);
        let settings = dir.join("settings.json");
        for _ in 0..3 {
            assert_eq!(local_frame(&host, &settings, 7, b"intent").unwrap(), b"\x07ok");
        }
        assert_eq!(fs::read_to_string(dir.join("starts")).unwrap().lines().count(), 1);
        let other = stub_dir("codec-refusal");
        fs::write(other.join("settings.json"), b"{}").unwrap();
        fs::write(other.join("reply-1"), framed(&[255, 0xff, 0x00])).unwrap();
        fs::write(other.join("reply-2"), framed(&[b"\x08".as_slice(), br#"{"type":"refused","reason":"malformed","phase":"6f702037","detail":"243a206d697373696e67206669656c64206e6f6e6365"}"#.as_slice()].concat())).unwrap();
        fs::write(other.join("reply"), framed(b"\x07again")).unwrap();
        let refusing = codec_stub(&other);
        let settings = other.join("settings.json");
        let error = local_frame(&refusing, &settings, 7, b"intent").unwrap_err();
        assert!(error.starts_with("host refused author: refused: malformed: $: missing field nonce (phase op 7)"), "{error}");
        assert!(matches!(crate::take_host_decision(), Some(crate::HostDecision::RefusedFrame { byte: 255, .. })));
        assert_eq!(local_frame(&refusing, &settings, 7, b"intent").unwrap(), b"\x07again");
        assert_eq!(fs::read_to_string(other.join("starts")).unwrap().lines().count(), 1);
        *CODEC.lock().unwrap() = None;
        let _ = fs::remove_dir_all(&dir);
        let _ = fs::remove_dir_all(&other);
    }
    /// The same settings bytes at another path keep the child: `workspace create` renames its
    /// attempt directory, settings included, between two frames of one process.
    #[test]
    fn codec_child_is_kept_across_a_renamed_settings_directory() {
        let _codec = codec_test_lock();
        let dir = stub_dir("codec-rename");
        fs::write(dir.join("reply"), framed(b"\x07ok")).unwrap();
        let host = codec_stub(&dir);
        fs::create_dir(dir.join("a-attempt")).unwrap();
        fs::write(dir.join("a-attempt/config.json"), b"{}").unwrap();
        assert_eq!(local_frame(&host, &dir.join("a-attempt/config.json"), 7, b"intent").unwrap(), b"\x07ok");
        fs::rename(dir.join("a-attempt"), dir.join("create-attempt")).unwrap();
        assert_eq!(local_frame(&host, &dir.join("create-attempt/config.json"), 7, b"intent").unwrap(), b"\x07ok");
        assert_eq!(fs::read_to_string(dir.join("starts")).unwrap().lines().count(), 1);
        *CODEC.lock().unwrap() = None;
        let _ = fs::remove_dir_all(&dir);
    }
    /// A child that refuses a frame and then dies cannot decode its refusal: the refusal is still
    /// reported (undecoded), and the dead child is not kept, so the next frame starts a fresh one.
    #[test]
    fn codec_child_that_dies_decoding_its_refusal_is_replaced() {
        use std::os::unix::fs::PermissionsExt;
        let _codec = codec_test_lock();
        let dir = stub_dir("codec-dies");
        let settings = dir.join("settings.json");
        fs::write(&settings, b"{}").unwrap();
        let host = dir.join("codec-host");
        fs::write(&host, format!("#!/bin/sh\necho start >> '{d}/starts'\nn=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \\n')\ndd bs=1 count=\"$n\" of=/dev/null 2>/dev/null\ncat '{d}/reply'\n",
            d = dir.display())).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(dir.join("reply"), framed(&[255, 0xff, 0x00])).unwrap();
        let error = local_frame(&host, &settings, 7, b"intent").unwrap_err();
        assert!(error.starts_with("host refused author"), "{error}");
        assert!(matches!(crate::take_host_decision(), Some(crate::HostDecision::RefusedFrame { byte: 255, decoded: None, .. })));
        fs::write(dir.join("reply"), framed(b"\x07ok")).unwrap();
        assert_eq!(local_frame(&host, &settings, 7, b"intent").unwrap(), b"\x07ok");
        assert_eq!(fs::read_to_string(dir.join("starts")).unwrap().lines().count(), 2);
        *CODEC.lock().unwrap() = None;
        let _ = fs::remove_dir_all(&dir);
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
/// operator: the local Host image's storeless `codec` loop (`Host.Main.serveCodec`)
/// answers frames 7-11 and never opens a Store, so a member's own machine needs
/// none. This process never receives keys, and these operations never mutate
/// source.
///
/// The loop answers every frame, a refusal included (as a 255 frame), and keeps serving, so ONE child
/// serves this whole `mini` process (`CODEC`). It holds no state between frames, so a child is
/// reused only under the same `anchor_binding` (image path and inode identity, settings bytes): a
/// Host image replaced in place, or other settings bytes, start a new child. The settings PATH is
/// not in the key: the child parses the bytes once at start and never reads the file again, and
/// `workspace create` renames its attempt directory (settings included) between frames.
/// A child that failed a frame, answered out of turn, or could not decode its own refusal is
/// dropped, and the next call starts a fresh one.
fn local_frame(host:&Path,config:&Path,operation:u8,payload:&[u8])->Result<Vec<u8>> {
    let executable=pure_host(host)?;
    let settings=PINS.get().map(|pins|pins.config.clone())
        .or_else(||std::env::var_os("MINI_CONSENT_CONFIG").map(PathBuf::from))
        .unwrap_or_else(||config.to_path_buf());
    if !settings.is_absolute(){return Err("local native settings must be absolute".into());}
    let settings_bytes=crate::fsio::read_bounded_or_empty(&settings, CAP)?;
    let binding=anchor_binding(&executable,&settings_bytes)?;
    let mut slot=CODEC.lock().map_err(|_|"local codec lock poisoned")?;
    if slot.as_ref().is_some_and(|(bound,_)|bound!=&binding) {
        *slot=None;
    }
    if slot.is_none() {
        let mut child=Command::new(&executable).arg(&settings).arg("codec")
            .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit())
            .spawn().map_err(|e|format!("cannot start local native codec: {e}"))?;
        let input=child.stdin.take().ok_or("local codec stdin missing")?;
        let output=child.stdout.take().ok_or("local codec stdout missing")?;
        *slot=Some((binding,Session{child:Some(child),input:Box::new(input),output:Box::new(output),executable,settings_bytes:settings_bytes.clone(),anchor:None}));
    }
    let session=&mut slot.as_mut().unwrap().1;
    let (answer,body)=match exchange(session,operation,payload) {
        Ok(reply)=>reply,
        Err(error)=>{*slot=None;return Err(format!("local native codec: {error}"));}
    };
    if crate::fsio::read_bounded_or_empty(&settings, CAP)?!=settings_bytes {
        *slot=None;return Err("local native settings changed during codec operation".into());
    }
    if answer==operation {return Ok([vec![operation],body].concat());}
    if answer!=255 {*slot=None;return Err(format!("local native codec answered frame {answer} to frame {operation}"));}
    // A refusal: the same child decodes its own frame (`inspect outcome`), as the session path does;
    // the client never decodes it itself.
    let mut request=(b"outcome".len() as u16).to_le_bytes().to_vec();
    request.extend_from_slice(b"outcome");request.extend_from_slice(&body);
    // A decode exchange that fails, or is answered out of turn, leaves a child that cannot be trusted
    // with the next frame: drop it, and report the refusal undecoded.
    let decoded=match exchange(session,8,&request) {
        Ok((8,json))=>serde_json::from_slice::<Value>(&json).ok(),
        Ok((255,_))=>None,
        _=>{*slot=None;None}
    };
    let line=decoded.as_ref().and_then(crate::refusal_line);
    let command=match operation {7=>"author",8=>"inspect",9=>"signatures",10=>"observe-assemble",_=>"assemble"};
    crate::note_host_decision(crate::HostDecision::RefusedFrame{command:command.to_owned(),byte:255,encoded:body.clone(),decoded});
    Err(crate::refused_frame_message(command,&body,line))
}
/// The storeless codec child of this process (`local_frame`) and the `anchor_binding` it was
/// started under.
static CODEC: Mutex<Option<([u8;32],Session)>> = Mutex::new(None);

/// Test stand-in for the local Host's storeless codec loop (`HOST SETTINGS codec`,
/// `Host.Main.serveCodec`): a `codec)` arm for a fixture's `case "$2" in` script. Every pure verb
/// reaches the Host this way (`process` -> `codec_process` -> `local_frame`); no client path runs a
/// one-shot `HOST CONFIG inspect` any more. Frame 8 (inspect) runs `inspect` (a shell snippet
/// reading the kind in `$kind` and the bytes in file `$body`, writing the decoded JSON to file
/// `$out`) and answers `[8] ++ out`; a failing snippet, or any other frame, answers a 255 refusal
/// whose bytes this loop decodes itself on `inspect outcome`, as the Host does.
#[cfg(test)]
pub(crate) fn codec_loop_arm(inspect: &str) -> String {
    r#"  codec)
    d="$1.codec.$$"; mkdir -p "$d"
    while :; do
      n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \n')
      [ -n "$n" ] || exit 0
      dd bs=1 count="$n" of="$d/frame" 2>/dev/null
      op=$(od -An -tu1 -N1 "$d/frame" | tr -d ' \n')
      k=$(od -An -tu2 -j1 -N2 "$d/frame" | tr -d ' \n')
      kind=$(dd if="$d/frame" bs=1 skip=3 count="$k" 2>/dev/null)
      body="$d/body"; out="$d/out"
      tail -c +$((4+k)) "$d/frame" > "$body"; : > "$out"
      if [ "$op" = 8 ] && [ "$kind" = outcome ] && [ "$(cat "$body")" = FIXTURE-REFUSAL ]; then
        a=8; printf '%s' '{"type":"refused","reason":"fixture"}' > "$out"
      elif [ "$op" = 8 ] && ( INSPECT ); then a=8
      else a=255; printf FIXTURE-REFUSAL > "$out"; fi
      m=$(( $(wc -c < "$out") + 1 ))
      printf "$(printf '\\%03o\\%03o\\%03o\\%03o\\%03o' $((m%256)) $((m/256%256)) $((m/65536%256)) 0 "$a")"
      cat "$out"
    done ;;
"#.replace("INSPECT", inspect)
}
/// `CODEC` is one slot per process and `cargo test` runs tests on parallel threads: every test that
/// drives `local_frame` (directly or through a pure verb) holds this lock, so no test replaces
/// another's child mid-count. Resets the slot on entry.
#[cfg(test)]
pub(crate) fn codec_test_lock() -> std::sync::MutexGuard<'static, ()> {
    static CODEC_TESTS: Mutex<()> = Mutex::new(());
    let guard = CODEC_TESTS.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    *CODEC.lock().unwrap_or_else(|poisoned| poisoned.into_inner()) = None;
    guard
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
