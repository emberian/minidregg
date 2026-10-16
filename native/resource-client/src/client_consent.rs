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
    /// The provider this process started; `None` when the frames go to a
    /// consent holder's provider (`hold`), which keeps its own custody.
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
        *slot=Some(match hold_socket()? {
            Some(socket)=>match attach(&socket,&executable,&settings,&settings_bytes)? {
                Some(session)=>session,
                None=>{
                    eprintln!("mini: warning: no consent holder listens on {}; starting a provider for this process",socket.display());
                    start(executable,&settings,settings_bytes)?
                }
            },
            None=>start(executable,&settings,settings_bytes)?,
        });
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

/// A consent holder (`mini consent-hold`) keeps one provider warm across `mini`
/// processes, so each request admits only the records appended since the
/// previous one (`ClientConsentCore.refresh`) instead of re-opening the whole
/// Store. It is selected by `MINI_CONSENT_SOCKET`, an owner-private socket.
fn hold_socket()->Result<Option<PathBuf>> {
    let Some(socket)=std::env::var_os("MINI_CONSENT_SOCKET") else {return Ok(None)};
    let socket=PathBuf::from(socket);
    if !socket.is_absolute() {return Err("MINI_CONSENT_SOCKET must be absolute".into());}
    Ok(Some(socket))
}
const HOLD_TAG: &[u8] = b"MINI-CONSENT-HOLD/v1\n";
const HOLD_PATH_CAP: usize = 4096;
fn write_field(out:&mut dyn Write,bytes:&[u8])->io::Result<()> {
    out.write_all(&(bytes.len() as u32).to_le_bytes())?;out.write_all(bytes)
}
fn read_field(input:&mut dyn Read,cap:usize)->Result<Vec<u8>> {
    let mut width=[0u8;4];input.read_exact(&mut width).map_err(|e|format!("consent holder frame: {e}"))?;
    let size=u32::from_le_bytes(width) as usize;
    if size>cap {return Err("consent holder field exceeds bound".into());}
    let mut bytes=vec![0;size];input.read_exact(&mut bytes).map_err(|e|format!("consent holder frame: {e}"))?;
    Ok(bytes)
}
/// Attach to the holder on `socket`. `None` when nothing listens there (the
/// caller starts its own provider). A holder of another user, or one whose
/// provider is not bound to exactly this executable file and these settings
/// bytes (`anchor_binding`), refuses: frames go only to the provider this
/// process selected.
fn attach(socket:&Path,executable:&Path,settings:&Path,settings_bytes:&[u8])->Result<Option<Session>> {
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::net::UnixStream;
    let mut stream=match UnixStream::connect(socket) {
        Ok(stream)=>stream,
        Err(e) if matches!(e.kind(),io::ErrorKind::NotFound|io::ErrorKind::ConnectionRefused)=>return Ok(None),
        Err(e)=>return Err(format!("consent holder {}: {e}",socket.display())),
    };
    if crate::transport::peer_uid(&stream)?!=unsafe{libc::geteuid()} {
        return Err(format!("consent holder {} runs as another user",socket.display()));
    }
    let binding=anchor_binding(executable,settings_bytes)?;
    let mut hello=HOLD_TAG.to_vec();
    write_field(&mut hello,executable.as_os_str().as_bytes()).and_then(|_|write_field(&mut hello,settings.as_os_str().as_bytes()))
        .map_err(|e|e.to_string())?;
    stream.write_all(&hello).map_err(|e|format!("consent holder {}: {e}",socket.display()))?;
    let answer=read_field(&mut stream,HOLD_PATH_CAP)?;
    match answer.split_first() {
        Some((0,held)) if held==binding.as_slice()=>{}
        Some((0,_))=>return Err(format!("consent holder {} holds a provider bound to another file or settings",socket.display())),
        Some((_,detail))=>return Err(format!("consent holder {}: {}",socket.display(),String::from_utf8_lossy(detail))),
        None=>return Err(format!("consent holder {} answered nothing",socket.display())),
    }
    let output=stream.try_clone().map_err(|e|e.to_string())?;
    Ok(Some(Session{child:None,input:Box::new(stream),output:Box::new(output),executable:executable.to_path_buf(),
        settings_bytes:settings_bytes.to_vec(),anchor:None}))
}

/// `mini consent-hold --socket PATH`: serve one warm provider per binding to
/// this user's `mini` processes, one connection at a time.
///
/// The holder is the custody the per-process path already is, kept alive: the
/// provider it starts is offered this binding's retained anchor exactly as
/// `start` does, every relayed frame first makes the provider admit what the
/// Store appended (`extendFrom`: the chain continues from the held one, every
/// new tag verifies, every new record replays), and after each answer the
/// holder retains the provider's new anchor. Anchor frames (228, 229) are the
/// holder's alone. A provider that refused an admission has ended; the next
/// connection starts a new one from the retained anchor, as the next `mini`
/// process would. A changed provider file or settings bytes binds differently
/// and gets a new provider.
pub(crate) fn hold(socket:&Path)->Result<()> {
    hold_in(socket,&anchor_dir()?)
}
fn hold_in(socket:&Path,anchors:&Path)->Result<()> {
    use std::os::unix::fs::PermissionsExt;
    use std::os::unix::net::UnixListener;
    let parent=socket.parent().ok_or("consent holder socket needs a parent directory")?;
    crate::fsio::check_private_dir(parent)?;
    let _lock=crate::transport::service_lock(&socket.with_extension("lock"))?;
    crate::transport::clear_stale_socket(socket)?;
    let listener=UnixListener::bind(socket).map_err(|e|format!("cannot bind {}: {e}",socket.display()))?;
    fs::set_permissions(socket,fs::Permissions::from_mode(0o600)).map_err(|e|format!("cannot protect socket {}: {e}",socket.display()))?;
    eprintln!("mini: holding consent on {}",socket.display());
    let mut held:Option<([u8;32],Session)>=None;
    for stream in listener.incoming() {
        let stream=match stream {Ok(stream)=>stream,Err(e)=>{eprintln!("mini: consent holder accept: {e}");continue}};
        if let Err(e)=serve_holder_connection(stream,anchors,&mut held) {
            eprintln!("mini: consent holder: {e}");
        }
    }
    Ok(())
}
fn serve_holder_connection(mut stream:std::os::unix::net::UnixStream,anchors:&Path,
    held:&mut Option<([u8;32],Session)>)->Result<()> {
    use std::os::unix::ffi::OsStrExt;
    stream.set_read_timeout(Some(std::time::Duration::from_secs(HOLD_IDLE_SECS))).map_err(|e|e.to_string())?;
    if crate::transport::peer_uid(&stream)?!=unsafe{libc::geteuid()} {return Err("refused a peer of another user".into());}
    let mut tag=vec![0;HOLD_TAG.len()];
    stream.read_exact(&mut tag).map_err(|e|format!("hello: {e}"))?;
    if tag!=HOLD_TAG {return Err("hello is not MINI-CONSENT-HOLD/v1".into());}
    let executable=PathBuf::from(OsStr::from_bytes(&read_field(&mut stream,HOLD_PATH_CAP)?));
    let settings=PathBuf::from(OsStr::from_bytes(&read_field(&mut stream,HOLD_PATH_CAP)?));
    let binding=match select_held(anchors,&executable,&settings,held) {
        Ok(binding)=>binding,
        Err(e)=>{
            let mut answer=Vec::new();write_field(&mut answer,&[[1u8].as_slice(),e.as_bytes()].concat()).map_err(|e|e.to_string())?;
            let _=stream.write_all(&answer);
            return Err(e);
        }
    };
    let mut answer=Vec::new();
    write_field(&mut answer,&[[0u8].as_slice(),binding.as_slice()].concat()).map_err(|e|e.to_string())?;
    stream.write_all(&answer).map_err(|e|e.to_string())?;
    loop {
        let mut width=[0u8;4];
        match stream.read_exact(&mut width) {
            Ok(())=>{}
            Err(e) if e.kind()==io::ErrorKind::UnexpectedEof=>return Ok(()),
            Err(e)=>return Err(format!("request: {e}")),
        }
        let size=u32::from_le_bytes(width) as usize;
        if size==0||size>CAP {return Err("request frame exceeds bound".into());}
        let mut body=vec![0;size];stream.read_exact(&mut body).map_err(|e|format!("request: {e}"))?;
        let operation=body[0];
        let reply=if operation==228||operation==229 {
            [[255u8].as_slice(),b"the consent holder keeps the retained anchor".as_slice()].concat()
        } else {
            let session=&mut held.as_mut().ok_or("no held provider")?.1;
            match relay(session,&body) {
                Ok(reply)=>{retain_anchor(session);reply}
                Err(e)=>{*held=None;return Err(e)}
            }
        };
        let mut framed=(reply.len() as u32).to_le_bytes().to_vec();framed.extend(reply);
        stream.write_all(&framed).map_err(|e|format!("answer: {e}"))?;
    }
}
/// The live provider for this executable and settings, started (with this
/// binding's retained anchor offered) when there is none, its file or settings
/// changed, or it ended.
fn select_held(anchors:&Path,executable:&Path,settings:&Path,held:&mut Option<([u8;32],Session)>)->Result<[u8;32]> {
    if !executable.is_absolute()||!settings.is_absolute() {return Err("local consent executable/settings must be absolute".into());}
    let settings_bytes=crate::fsio::read_bounded_or_empty(settings,CAP)?;
    let binding=anchor_binding(executable,&settings_bytes)?;
    let live=match held.as_mut() {
        Some((bound,session)) if *bound==binding=>session.child.as_mut().is_some_and(|child|matches!(child.try_wait(),Ok(None))),
        _=>false,
    };
    if !live {
        *held=None;
        *held=Some((binding,start_in(anchors,executable.to_path_buf(),settings,settings_bytes)?));
    }
    Ok(binding)
}
/// One request frame to the provider and its whole answer frame back, unread:
/// the attached process checks it (`round_trip`).
fn relay(session:&mut Session,body:&[u8])->Result<Vec<u8>> {
    session.input.write_all(&(body.len() as u32).to_le_bytes()).and_then(|_|session.input.write_all(body))
        .and_then(|_|session.input.flush()).map_err(|e|format!("held provider request: {e}"))?;
    let mut width=[0u8;4];session.output.read_exact(&mut width).map_err(|e|format!("held provider ended: {e}"))?;
    let size=u32::from_le_bytes(width) as usize;
    if size==0||size>CAP {return Err("held provider answer frame refused".into());}
    let mut frame=vec![0;size];session.output.read_exact(&mut frame).map_err(|e|format!("held provider ended: {e}"))?;
    Ok(frame)
}
/// How long an attached process may leave the holder waiting for its next frame.
const HOLD_IDLE_SECS: u64 = 600;

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

/// With local consent selected, retained authoring, inspection and assembly go
/// through the local Host's storeless codec loop (`local_frame`).
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

    /// A provider stub that logs each request's opcode and answers every frame
    /// with that opcode and the fixed body in `reply_229` for frame 229 (the
    /// retained anchor) or an empty body otherwise.
    fn opcode_stub(dir: &Path, anchor: &[u8]) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        fs::write(dir.join("anchor-body"), anchor).unwrap();
        let path = dir.join("provider");
        fs::write(&path, format!(concat!(
            "#!/bin/sh\n",
            "echo start >> '{starts}'; echo $$ > '{pid}'\n",
            "while :; do\n",
            "  n=$(dd bs=1 count=4 2>/dev/null | od -An -tu4 | tr -d ' \\n')\n",
            "  [ -n \"$n\" ] || exit 0\n",
            "  dd bs=1 count=\"$n\" of='{frame}' 2>/dev/null\n",
            "  op=$(od -An -tu1 -N1 '{frame}' | tr -d ' \\n')\n",
            "  echo \"$op\" >> '{log}'\n",
            "  [ \"$op\" = 221 ] && exit 3\n",
            "  if [ \"$op\" = 229 ]; then\n",
            "    m=$(( $(wc -c < '{body}') + 1 ))\n",
            "    printf \"$(printf '\\\\%03o\\\\000\\\\000\\\\000\\\\%03o' \"$m\" 229)\"; cat '{body}'\n",
            "  else\n",
            "    printf \"$(printf '\\\\001\\\\000\\\\000\\\\000\\\\%03o' \"$op\")\"\n",
            "  fi\n",
            "done\n"), log = dir.join("opcodes").display(), body = dir.join("anchor-body").display(),
            frame = dir.join("frame").display(), starts = dir.join("starts").display(),
            pid = dir.join("pid").display())).unwrap();
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


    fn starts(dir: &Path) -> usize {
        fs::read_to_string(dir.join("starts")).unwrap_or_default().lines().count()
    }
    /// A holder on a private socket in `dir`, serving from a background thread.
    fn holder(dir: &Path) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let private = dir.join("run");
        fs::create_dir(&private).unwrap();
        fs::set_permissions(&private, fs::Permissions::from_mode(0o700)).unwrap();
        let socket = private.join("consent.sock");
        let (anchors, bound) = (dir.join("anchors"), socket.clone());
        std::thread::spawn(move || hold_in(&bound, &anchors));
        for _ in 0..200 {
            if std::os::unix::net::UnixStream::connect(&socket).is_ok() { break; }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        socket
    }

    /// The holder keeps ONE provider across attached processes: the second
    /// process's frame reaches the provider the first one warmed (no new start,
    /// no anchor offer), and the holder retains the anchor after each frame.
    #[test]
    fn consent_holder_keeps_one_provider_across_processes() {
        let dir = stub_dir("hold-warm");
        let provider = opcode_stub(&dir, b"ANCHOR-AFTER");
        let settings = dir.join("consent.json");
        fs::write(&settings, b"{}").unwrap();
        let socket = holder(&dir);
        for _ in 0..3 {
            let mut session = attach(&socket, &provider, &settings, b"{}").unwrap().expect("holder listens");
            assert!(session.anchor.is_none() && session.child.is_none());
            round_trip(&mut session, 220, b"intent").unwrap();
        }
        assert_eq!(starts(&dir), 1);
        assert_eq!(opcodes(&dir), vec![220, 229, 220, 229, 220, 229]);
        let binding = anchor_binding(&provider, b"{}").unwrap();
        assert_eq!(read_anchor(&anchor_path(&dir.join("anchors"), &binding), &binding).unwrap().as_deref(), Some(&b"ANCHOR-AFTER"[..]));
        // Anchor custody is the holder's: an attached process cannot offer or read one.
        let mut session = attach(&socket, &provider, &settings, b"{}").unwrap().unwrap();
        assert!(round_trip(&mut session, 228, b"forged").is_err());
        assert!(round_trip(&mut session, 229, b"").is_err());
        assert_eq!(opcodes(&dir), vec![220, 229, 220, 229, 220, 229]);
        let _ = fs::remove_dir_all(&dir);
    }

    /// A provider that ended (an admission refusal ends it) is not revived for
    /// the refused process; the next process gets a new provider offered the
    /// retained anchor, exactly as a new `mini` process would.
    #[test]
    fn consent_holder_restarts_an_ended_provider_from_the_retained_anchor() {
        let dir = stub_dir("hold-ended");
        let provider = opcode_stub(&dir, b"ANCHOR-AFTER");
        let settings = dir.join("consent.json");
        fs::write(&settings, b"{}").unwrap();
        let socket = holder(&dir);
        let mut session = attach(&socket, &provider, &settings, b"{}").unwrap().unwrap();
        round_trip(&mut session, 220, b"intent").unwrap();
        assert!(round_trip(&mut session, 221, b"refused").is_err());
        let mut session = attach(&socket, &provider, &settings, b"{}").unwrap().unwrap();
        round_trip(&mut session, 220, b"intent").unwrap();
        assert_eq!(starts(&dir), 2);
        assert_eq!(opcodes(&dir), vec![220, 229, 221, 228, 220, 229]);
        let _ = fs::remove_dir_all(&dir);
    }

    /// A held provider that died while idle (killed, crashed) is not relayed to:
    /// the next process gets a new provider offered the retained anchor.
    #[test]
    fn consent_holder_replaces_a_provider_that_died_idle() {
        let dir = stub_dir("hold-died");
        let provider = opcode_stub(&dir, b"ANCHOR-AFTER");
        let settings = dir.join("consent.json");
        fs::write(&settings, b"{}").unwrap();
        let socket = holder(&dir);
        round_trip(&mut attach(&socket, &provider, &settings, b"{}").unwrap().unwrap(), 220, b"intent").unwrap();
        let pid: i32 = fs::read_to_string(dir.join("pid")).unwrap().trim().parse().unwrap();
        unsafe { libc::kill(pid, libc::SIGKILL); }
        for _ in 0..200 {
            let state = fs::read_to_string(format!("/proc/{pid}/stat")).unwrap_or_default();
            if state.is_empty() || state.contains(") Z ") { break; }
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
        round_trip(&mut attach(&socket, &provider, &settings, b"{}").unwrap().unwrap(), 220, b"intent").unwrap();
        assert_eq!(starts(&dir), 2);
        assert_eq!(opcodes(&dir), vec![220, 229, 228, 220, 229]);
        let _ = fs::remove_dir_all(&dir);
    }

    /// Frames go only to a provider bound to exactly the selected file and
    /// settings: the holder reads the settings itself, so bytes that differ
    /// from the attaching process's refuse; a changed settings file gets a new
    /// provider; nothing listening leaves the process to start its own.
    #[test]
    fn consent_holder_serves_only_the_selected_binding() {
        let dir = stub_dir("hold-binding");
        let provider = opcode_stub(&dir, b"ANCHOR-AFTER");
        let settings = dir.join("consent.json");
        fs::write(&settings, b"{}").unwrap();
        assert!(attach(&dir.join("absent.sock"), &provider, &settings, b"{}").unwrap().is_none());
        let socket = holder(&dir);
        assert!(attach(&socket, &provider, &settings, b"{ }").is_err());
        round_trip(&mut attach(&socket, &provider, &settings, b"{}").unwrap().unwrap(), 220, b"intent").unwrap();
        fs::write(&settings, b"{ }").unwrap();
        round_trip(&mut attach(&socket, &provider, &settings, b"{ }").unwrap().unwrap(), 220, b"intent").unwrap();
        assert_eq!(starts(&dir), 2);
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
/// operator: the local Host image's storeless `codec` loop (`Host.Main.serveCodec`)
/// answers frames 7-11 and never opens a Store, so a member's own machine needs
/// none. This process never receives keys, and these operations never mutate
/// source.
fn local_frame(host:&Path,config:&Path,operation:u8,payload:&[u8])->Result<Vec<u8>> {
    let executable=pure_host(host)?;
    let settings=PINS.get().map(|pins|pins.config.clone())
        .or_else(||std::env::var_os("MINI_CONSENT_CONFIG").map(PathBuf::from))
        .unwrap_or_else(||config.to_path_buf());
    if !settings.is_absolute(){return Err("local native settings must be absolute".into());}
    let settings_bytes=crate::fsio::read_bounded_or_empty(&settings, CAP)?;
    let mut child=Command::new(&executable).arg(&settings).arg("codec")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit())
        .spawn().map_err(|e|format!("cannot start local native codec: {e}"))?;
    let input=child.stdin.take().ok_or("local codec stdin missing")?;
    let output=child.stdout.take().ok_or("local codec stdout missing")?;
    let mut session=Session{child:Some(child),input:Box::new(input),output:Box::new(output),executable,settings_bytes:settings_bytes.clone(),anchor:None};
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
