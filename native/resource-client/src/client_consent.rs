//! Local consent and the local codec, selected by local custody: the remote transport never
//! supplies these executables or their settings. The processes themselves, the retained consent
//! anchors and the residents are `mini_sdk::consent` and `mini_sdk::local`; this module selects
//! them (`--local-host`/pins, `MINI_LOCAL_HOST`, `MINI_CONSENT_HOST`, `MINI_CONSENT_CONFIG`),
//! keeps one of each per process (or this user's one resident of each per binding: `mini
//! consent-resident`, `mini codec-resident`), and reports their refusals as Host decisions.
use super::*;
use mini_sdk::consent::{Consent, ConsentError, ResidentKind};
use mini_sdk::local::{Codec, CodecError};

const CAP: usize = mini_sdk::local::CAP;
static SESSION: Mutex<Option<Consent>> = Mutex::new(None);
/// The provider connection's liveness (delegated worker or resident), beside the session it belongs to (same lock order: SESSION first).
static LIFELINE: Mutex<Option<crate::consent_proxy::Lifeline>> = Mutex::new(None);
static DELEGATED_SESSION: OnceLock<Option<crate::consent_proxy::Selection>> = OnceLock::new();

/// Pure codec operations always use a separately selected local native image.
/// A remote Host digest is not an executable or a local semantic authority.
pub(crate) fn pure_host(host: &Path) -> Result<PathBuf> {
    let environment = std::env::var_os("MINI_LOCAL_HOST");
    Ok(mini_sdk::host_selection::select_semantic_host(
        PINS.get().map(|pins| pins.semantic.as_path()),
        environment.as_deref(),
        host,
    )?)
}

/// Set only from a provider's observation (221) refusal carrying
/// `mini_sdk::consent::STALE_OBSERVATION_TAG` (the source moved between the Host's challenge and
/// the local check); every other refusal stays terminal.
static STALE_OBSERVATION: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// Whether the last observation consent was refused as stale; clears the record.
pub(crate) fn take_stale_observation() -> bool {
    STALE_OBSERVATION.swap(false, std::sync::atomic::Ordering::Relaxed)
}

// A resident is `mini` itself (`current_exe`); a unit-test binary is not `mini` and cannot start
// one (`<test binary> consent-resident` is refused by the harness), so its tests keep the provider
// and the codec in process. The resident path is the journeys' and the shell's, with the binary.
fn resident_enabled()->bool { !cfg!(test) && std::env::var("MINI_CONSENT_RESIDENT").as_deref()!=Ok("0") }
/// HOT-PATH 2a: the storeless codec Host is resident the same way (`mini codec-resident`), ONE per
/// `pure_host` binding for every `mini` process of this user instead of one 159 MB Lean image per
/// process. `MINI_CODEC_RESIDENT=0` keeps the per-process child.
fn codec_resident_enabled()->bool { !cfg!(test) && std::env::var("MINI_CODEC_RESIDENT").as_deref()!=Ok("0") }
/// A resident with no frame for `$variable` seconds (default `RESIDENT_IDLE_S`, 600) ends.
fn resident_idle(variable:&str)->std::time::Duration {
    std::time::Duration::from_secs(std::env::var(variable).ok().and_then(|v|v.parse().ok()).unwrap_or(mini_sdk::consent::RESIDENT_IDLE_S))
}

/// The selected consent provider of this process, started (or reached as this binding's resident
/// provider) on first use and kept: restarting would discard its independently verified frontier.
/// A dead provider remains failed for this process rather than silently verifying an older source
/// from genesis. `MINI_CONSENT_RESIDENT=0` keeps the provider in this process.
fn with_consent<T>(host: &Path, config: &Path, frame: impl FnOnce(&mut Consent) -> std::result::Result<T, ConsentError>) -> Result<T> {
    let executable=PINS.get().map(|pins|pins.consent.clone()).or_else(||std::env::var_os("MINI_CONSENT_HOST").map(PathBuf::from))
        .or_else(||(!host.as_os_str().is_empty()).then(||host.with_file_name("minidregg-client-consent")))
        .ok_or("signing requires an independently selected MINI_CONSENT_HOST")?;
    let settings=PINS.get().map(|pins|pins.config.clone()).or_else(||std::env::var_os("MINI_CONSENT_CONFIG").map(PathBuf::from))
        .unwrap_or_else(||config.to_path_buf());
    if !executable.is_absolute()||!settings.is_absolute() {return Err("local consent executable/settings must be absolute".into());}
    let settings_bytes=crate::fsio::read_bounded_or_empty(&settings, CAP)?;
    let delegated=match PINS.get(){Some(p)=>p.delegated.clone(),None=>crate::consent_proxy::Selection::from_env()?};
    if let Some(selected)=DELEGATED_SESSION.get(){
        if selected!=&delegated{return Err("consent transport selection changed within signing session".into());}
    } else {DELEGATED_SESSION.set(delegated.clone()).map_err(|_|"consent transport selection raced")?;}
    let mut slot=SESSION.lock().map_err(|_|"local consent session lock poisoned")?;
    let mut lifeline=LIFELINE.lock().map_err(|_|"consent lifeline lock poisoned")?;
    drop_dead_session(&mut slot,&mut lifeline);
    if let Some(consent)=slot.as_ref() {
        if consent.0.executable()!=executable||consent.0.settings()!=settings_bytes {
            return Err("local consent executable or settings changed within signing session".into());
        }
    } else if let Some(selection)=delegated {
        let (input,output,live)=crate::consent_proxy::connect_with_lifeline(&selection,&settings_bytes)?;
        *slot=Some(Consent(mini_sdk::local::Session::over(input,output,executable,settings_bytes)));
        *lifeline=Some(live);
    } else if resident_enabled() {
        let mini=std::env::current_exe().map_err(|e|format!("resident consent provider: {e}"))?;
        let mut launch=Command::new(mini);
        launch.arg("consent-resident").arg("--consent").arg(&executable).arg("--settings").arg(&settings);
        let (session,watch)=mini_sdk::consent::connect_resident_watched(&executable,settings_bytes,launch)?;
        *slot=Some(Consent(session));
        *lifeline=Some(crate::consent_proxy::Lifeline::watching(watch));
    } else {
        let anchors=mini_sdk::consent::anchor_dir()?;
        *slot=Some(Consent(mini_sdk::consent::start(&anchors,executable,&settings,settings_bytes)?));
    }
    let answer=frame(slot.as_mut().unwrap());
    // A request that met a dead provider connection is undecided: it is never replayed here, and the
    // next request opens a fresh connection (the socket-activated unit's, or a new resident's).
    let lost=answer.is_err()&&drop_dead_session(&mut slot,&mut lifeline);
    answer.map_err(|error| {
        if error.is_stale_observation() {
            STALE_OBSERVATION.store(true,std::sync::atomic::Ordering::Relaxed);
        }
        if lost {format!("{error} (consent transport lost before an answer: this request is undecided and was not replayed; the next request reconnects)")} else {error.to_string()}
    })
}

/// Drop a session whose provider connection can no longer carry a request, so the next request
/// reconnects instead of failing for ever: a delegated worker that idled out or restarted, or a
/// resident provider that ended (both keep the frontier in their retained anchor, so the next one
/// resumes it). True when it dropped one. An in-process provider has no lifeline and is never
/// dropped: its frontier is in this process.
pub(crate) fn drop_dead_session(slot:&mut Option<Consent>,lifeline:&mut Option<crate::consent_proxy::Lifeline>)->bool {
    if lifeline.as_ref().is_some_and(|live|!live.alive()) {
        *slot=None;
        *lifeline=None;
        return true;
    }
    false
}

/// `mini consent-resident --consent EXECUTABLE --settings SETTINGS`: hold one provider for this
/// binding and serve its frames until the provider ends or no frame arrives for
/// `MINI_CONSENT_IDLE_S` (600) seconds.
pub(crate) fn resident(executable:PathBuf,settings:PathBuf)->Result<()> {
    let idle=resident_idle("MINI_CONSENT_IDLE_S");
    if !mini_sdk::consent::daemonize()? { return Ok(()); }
    Ok(mini_sdk::consent::serve_resident(&mini_sdk::consent::private_anchor_dir()?,executable,settings,idle)?)
}
/// `mini codec-resident --host EXECUTABLE --settings SETTINGS` (HOT-PATH 2a): hold ONE storeless
/// codec Host (`HOST SETTINGS codec`, `Host.Main.serveCodec`) for this binding and serve every
/// `mini` process's codec frames (7-11) on the binding's socket, one frame at a time, until the
/// Host ends or no frame arrives for `MINI_CODEC_IDLE_S` (600) seconds. The codec is pure and
/// holds no state between frames, so sharing one across processes changes no reply; it removes
/// one 159 MB Lean image start per `mini` process. The image is the client's own selected
/// semantic Host (`pure_host`), never the serving Store's.
pub(crate) fn codec_resident(executable:PathBuf,settings:PathBuf)->Result<()> {
    let idle=resident_idle("MINI_CODEC_IDLE_S");
    if !mini_sdk::consent::daemonize()? { return Ok(()); }
    Ok(mini_sdk::consent::serve_resident_kind(ResidentKind::Codec,&mini_sdk::consent::private_anchor_dir()?,executable,settings,idle)?)
}

fn read(path:&Path)->Result<Vec<u8>> { crate::fsio::read_bounded_or_empty(path, CAP) }

/// Negotiate with the selected local executable before sending the new frame.
/// Old providers refuse the storeless feature command; this never treats their
/// ordinary anchored readiness as full verification.
pub(crate) fn full_ready(host: &Path, config: &Path) -> Result<()> {
    let executable = PINS.get().map(|pins|pins.consent.clone())
        .or_else(||std::env::var_os("MINI_CONSENT_HOST").map(PathBuf::from))
        .unwrap_or_else(||host.with_file_name("minidregg-client-consent"));
    let settings = PINS.get().map(|pins|pins.config.clone())
        .or_else(||std::env::var_os("MINI_CONSENT_CONFIG").map(PathBuf::from))
        .unwrap_or_else(||config.to_path_buf());
    if !executable.is_absolute() || !settings.is_absolute() {
        return Err("local consent executable/settings must be absolute".into());
    }
    let delegated = match PINS.get() {
        Some(pins) => pins.delegated.clone(),
        None => crate::consent_proxy::Selection::from_env()?,
    };
    if delegated.is_none() && !resident_enabled() {
        return Err("full consent readiness requires a retained resident or delegated provider".into());
    }
    let features = Command::new(&executable).arg(&settings).arg("features").output()
        .map_err(|e|format!("consent readiness feature probe: {e}"))?;
    if !features.status.success() || features.stdout != b"mini-consent-full-ready-v1\n" {
        return Err("selected consent provider does not support explicit full readiness".into());
    }
    with_consent(host, config, |consent| consent.full_ready())
}

/// Consent 220 (thin: 230; a thin birth: 234, with the member's retained source) for the retained intent at `intent` and the signer's public `key`;
/// the retained bytes the provider confirmed.
pub(crate) fn intent(host:&Path,config:&Path,intent:&Path,key:&[u8])->Result<Vec<u8>> {
    let bytes=read(intent)?;
    if thin_mode() {
        if let Some(source)=thin_birth_source()? {
            with_consent(host,config,|c|c.thin_birth_intent(&bytes,key,&source))?;
            return Ok(bytes);
        }
    }
    with_consent(host,config,|c|c.intent(&bytes,key,thin_mode()))?;
    Ok(bytes)
}
/// Consent 221 (thin: 231): the challenge headers the intent permits `key` to sign.
pub(crate) fn observation(host:&Path,config:&Path,intent:&Path,signature:&Path,challenge:&Path,key:&[u8])->Result<Vec<Vec<u8>>> {
    let (intent,signature,challenge)=(read(intent)?,read(signature)?,read(challenge)?);
    with_consent(host,config,|c|c.observation(&intent,key,&signature,&challenge,thin_mode()))
}
/// Consent 222 (thin: 232): the plan headers the intent permits `key` to sign.
pub(crate) fn plan(host:&Path,config:&Path,intent:&Path,plan:&Path,key:&[u8])->Result<Vec<Vec<u8>>> {
    if thin_mode() {
        if let Some(source)=thin_birth_source()? { return thin_birth_plan(host,config,intent,plan,key,&source); }
        return thin_plan(host,config,intent,plan,key);
    }
    let (intent,plan)=(read(intent)?,read(plan)?);
    with_consent(host,config,|c|c.plan(&intent,key,&plan))
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

static THIN_BIRTH_SOURCE: std::sync::Mutex<Option<PathBuf>> = std::sync::Mutex::new(None);

/// Thin birth consent (frames 234/235, `Kernel.NativeThinBirth`): the member's own retained
/// birth source, which the provider re-authors at the coordinates the Host's draft carries.
pub(crate) fn set_thin_birth_source(source:Option<PathBuf>)->Result<()> {
    *THIN_BIRTH_SOURCE.lock().map_err(|_|"thin birth source slot poisoned")?=source;
    Ok(())
}

fn thin_birth_source()->Result<Option<Vec<u8>>> {
    let path=THIN_BIRTH_SOURCE.lock().map_err(|_|"thin birth source slot poisoned")?.clone();
    path.map(|path|read(&path)).transpose()
}

fn thin_birth_plan(host:&Path,config:&Path,intent:&Path,plan:&Path,key:&[u8],source:&[u8])->Result<Vec<Vec<u8>>> {
    let (intent_bytes,plan_bytes)=(read(intent)?,read(plan)?);
    let (display,headers)=with_consent(host,config,|c|c.thin_birth_plan(&intent_bytes,key,&plan_bytes,source))?;
    if let Some(directory)=plan.parent() {
        write_json_new(&directory.join("thin-display.json"),&display)?;
    }
    eprintln!("thin consent shows: {}",display);
    Ok(headers)
}

fn thin_plan(host:&Path,config:&Path,intent:&Path,plan:&Path,key:&[u8])->Result<Vec<Vec<u8>>> {
    let paths=THIN_VIEWS.lock().map_err(|_|"thin view slot poisoned")?.clone()
        .ok_or("thin consent has no served target views; nothing signed")?;
    let mut views=Vec::new();
    for path in &paths { views.push(read(path)?); }
    let (intent_bytes,plan_bytes)=(read(intent)?,read(plan)?);
    let (display,headers)=with_consent(host,config,|c|c.thin_plan(&intent_bytes,key,&plan_bytes,&views))?;
    if let Some(directory)=plan.parent() {
        write_json_new(&directory.join("thin-display.json"),&display)?;
    }
    eprintln!("thin consent shows: {}",display);
    Ok(headers)
}

#[derive(Clone, PartialEq, Eq)]
struct Pins { semantic:PathBuf, consent:PathBuf, config:PathBuf, delegated:Option<crate::consent_proxy::Selection> }
static PINS: OnceLock<Pins> = OnceLock::new();
/// Private local workspace/attempt custody record; never filled from an
/// operator response or a remotely inspected JSON object.
pub(crate) fn pin_record(value:&Value)->Result<()> {
    let path=|name:&str|->Result<PathBuf>{
        let path=PathBuf::from(value.get(name).and_then(Value::as_str).ok_or("local consent pin is missing a path")?);
        if !path.is_absolute(){return Err("local consent pin path must be absolute".into());}Ok(path)
    };
    let pins=Pins{semantic:path("semanticHost")?,consent:path("consentHost")?,config:path("config")?,delegated:crate::consent_proxy::Selection::from_record(value)?};
    if let Some(selected)=crate::consent_proxy::Selection::from_env()? {
        if pins.delegated.as_ref()!=Some(&selected){return Err("retained consent transport pins differ from explicit selection".into());}
    }
    match PINS.get(){Some(old) if old!=&pins=>Err("local consent pins differ within one process".into()),Some(_)=>Ok(()),None=>PINS.set(pins).map_err(|_|"cannot pin local consent custody".into())}
}
pub(crate) fn configured_record()->Result<Option<Value>> {
    if let Some(pins)=PINS.get(){
        let mut value=json!({"semanticHost":pins.semantic,"consentHost":pins.consent,"config":pins.config});
        if let Some(p)=&pins.delegated{value["delegatedConsent"]=p.record();}
        return Ok(Some(value));
    }
    let paths=["MINI_LOCAL_HOST","MINI_CONSENT_HOST","MINI_CONSENT_CONFIG"].map(std::env::var_os);
    let delegated=crate::consent_proxy::Selection::from_env()?;
    if paths.iter().all(Option::is_none)&&delegated.is_none(){return Ok(None);}
    let [Some(semantic),Some(consent),Some(config)]=paths else {return Err("durable local consent selection requires MINI_LOCAL_HOST, MINI_CONSENT_HOST and MINI_CONSENT_CONFIG together".into());};
    let mut value=json!({"semanticHost":PathBuf::from(semantic),"consentHost":PathBuf::from(consent),"config":PathBuf::from(config)});
    if let Some(p)=delegated{value["delegatedConsent"]=p.record();}
    pin_record(&value)?;Ok(Some(value))
}

/// Authoring, inspection and assembly (the pure codec verbs) go through this process's one local
/// storeless codec child (`local_frame`), never a Host process per verb.
pub(crate) fn codec_process(host:&Path,config:&Path,args:&[&OsStr])->Result<Output> {
    let verb=args.first().and_then(|s|s.to_str()).ok_or("missing local codec command")?;
    let read=|index:usize|->Result<Vec<u8>>{crate::fsio::read_bounded_or_empty(Path::new(args.get(index).ok_or("missing local codec input")?), CAP)};
    let kind=|label:&OsStr,bytes:Vec<u8>|->Result<Vec<u8>>{
        Ok(mini_sdk::local::kind(label.to_str().ok_or("local codec kind is not UTF-8")?,&bytes)?)
    };
    let (op,payload,destination)=match verb {
        "author" | "inspect" if args.len()==4 => (if verb=="author" {mini_sdk::host_operations::AUTHOR} else {mini_sdk::host_operations::INSPECT},kind(args[1],read(2)?)?,args[3]),
        "signatures" if args.len()==3 => (mini_sdk::host_operations::SIGNATURES,read(1)?,args[2]),
        "observe-assemble" | "assemble" if args.len()==4 => (if verb=="assemble" {mini_sdk::host_operations::CALL_ASSEMBLE} else {mini_sdk::host_operations::OBSERVATION_ASSEMBLE},mini_sdk::local::pair(&read(1)?,&read(2)?)?,args[3]),
        _=>return Err("unsupported local native codec arguments".into())
    };
    let frame=codec_frame(host,config,op,&payload)?;
    let bytes=frame[1..].to_vec();write_new(Path::new(destination),&bytes)?;
    #[cfg(unix)] {use std::os::unix::process::ExitStatusExt;
        Ok(Output{status:std::process::ExitStatus::from_raw(0),stdout:bytes,stderr:Vec::new()})}
    #[cfg(not(unix))] {Err("local native consent codecs currently require Unix".into())}
}

/// A source custody wrapper's detached Host verb (`HOST CONFIG VERB ...`), answered by this
/// process's codec session when the verb is a pure one (`author`, `inspect`, `signatures`): the
/// same frame the detached verb computes, without a Host process per call. The destination is
/// replaced, as the detached verb's write replaced it. `false`: not a pure verb; the caller runs
/// the image.
pub(crate) fn pure_source(host:&Path,config:&Path,args:&[&OsStr])->Result<bool> {
    let pure=args.first().and_then(|word|word.to_str()).is_some_and(|verb|matches!(verb,"author"|"inspect"|"signatures"));
    if !pure {return Ok(false);}
    if let Some(destination)=args.last().map(Path::new) {
        match fs::symlink_metadata(destination) {
            Ok(meta) if meta.file_type().is_file() => fs::remove_file(destination).map_err(|e|format!("cannot replace {}: {e}",destination.display()))?,
            _ => {}
        }
    }
    codec_process(host,config,args).map(|_|true)
}

/// Local producer for wrappers retaining native session frames themselves.
/// Existing retained frames must be compared with this local derivation before
/// reuse; the frame's original remote origin is not consent authority.
pub(crate) fn codec_frame(host:&Path,config:&Path,operation:u8,payload:&[u8])->Result<Vec<u8>> {
    if !(7..=11).contains(&operation){return Err("not a local codec opcode".into());}
    local_frame(host, config, operation, payload)
}

/// One frame to this process's storeless codec session (`mini_sdk::local::Codec`), as
/// `[operation] ++ body`: this binding's resident codec Host (one `HOST SETTINGS codec` child for
/// every `mini` process of this user, started by the first that finds none listening), or this
/// process's own child under `MINI_CODEC_RESIDENT=0`. A refusal is the Host's own: it decodes its
/// frame (`inspect outcome`), the decision is noted as the Host's, and the client never decodes
/// it itself.
fn local_frame(host:&Path,config:&Path,operation:u8,payload:&[u8])->Result<Vec<u8>> {
    let executable=pure_host(host)?;
    let settings=PINS.get().map(|pins|pins.config.clone())
        .or_else(||std::env::var_os("MINI_CONSENT_CONFIG").map(PathBuf::from))
        .unwrap_or_else(||config.to_path_buf());
    let mut codec=CODEC.lock().map_err(|_|"local codec lock poisoned")?;
    let answer=if codec_resident_enabled() {
        codec.frame_with(&executable,&settings,operation,payload,&|executable,settings,settings_bytes|{
            let mini=std::env::current_exe().map_err(|e|format!("{}: {e}",ResidentKind::Codec.name()))?;
            let mut launch=Command::new(mini);
            launch.arg("codec-resident").arg("--host").arg(&executable).arg("--settings").arg(settings);
            mini_sdk::consent::connect_resident_kind(ResidentKind::Codec,&executable,settings_bytes,launch)
        })
    } else {
        codec.frame(&executable,&settings,operation,payload)
    };
    match answer {
        Ok(body)=>Ok([vec![operation],body].concat()),
        Err(CodecError::Failed(error))=>Err(error),
        Err(CodecError::Refused{marker,encoded,decoded})=>{
            let line=Some(crate::no_record_line(decoded.as_ref()));
            let command=match operation {mini_sdk::host_operations::AUTHOR=>"author",mini_sdk::host_operations::INSPECT=>"inspect",mini_sdk::host_operations::SIGNATURES=>"signatures",mini_sdk::host_operations::OBSERVATION_ASSEMBLE=>"observe-assemble",_=>"assemble"};
            let decision=crate::HostDecision::Frame{command:command.to_owned(),byte:marker,encoded:encoded.clone(),decoded};
            let kind=crate::outcome_type(decision.outcome()).to_owned();
            let refusal=decision.is_refusal();
            crate::note_host_decision(decision);
            // A pure codec frame changes nothing either way; the class is still the marker's.
            if !refusal {
                return Err(crate::undecided_frame_message(command,&kind,None,&encoded));
            }
            Err(crate::refused_frame_message(command,&encoded,line))
        }
    }
}
/// The storeless codec session of this process (its own child, or its connection to the resident).
static CODEC: Mutex<Codec> = Mutex::new(Codec::new());

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
    // These tests count this process's own child; the resident is tested on its own
    // (`mini_sdk::consent` and tests/codec_resident.rs), and a test binary has no `codec-resident` verb.
    std::env::set_var("MINI_CODEC_RESIDENT", "0");
    CODEC.lock().unwrap_or_else(|poisoned| poisoned.into_inner()).reset();
    guard
}

/// The registry's `consent_plans` (`protocol/host-operations.json`).
pub(crate) fn plan_operation(operation:u8)->bool {
    mini_sdk::host_operations::CONSENT_PLANS.contains(&operation)
}
/// Always check adapted operator-authored plans before returning bytes to any
/// signing consumer. A native refusal or dead verifier never falls back to the
/// remotely proposed plan.
pub(crate) fn operator_plan(host:&Path,config:&Path,operation:u8,request:&[u8],candidate:&[u8])->Result<()> {
    with_consent(host,config,|c|c.operator_plan(operation,request,candidate))
}

/// Enrollment possession (frame 226) over the complete retained command, with the selected new
/// custody key and subject.
pub(crate) fn possession(host:&Path,config:&Path,command:&[u8],subject:&str,key:&SigningKey,candidate:&[u8])->Result<Vec<u8>> {
    with_consent(host,config,|c|c.possession(command,subject,key.verifying_key().as_bytes(),candidate))
}

/// Objective-only source WIP (frame 227): the provider reconstructs the complete expected typed
/// plan and returns its own ordered headers; an older provider refuses, and callers never fall
/// back to the offered plan's inspected headers.
pub(crate) fn objective_headers(host: &Path, config: &Path, retained_intent: &[u8],
    selected_public_key: &[u8], role: &str, candidate_plan: &[u8]) -> Result<Vec<Vec<u8>>> {
    with_consent(host,config,|c|c.objective(retained_intent,selected_public_key,role,candidate_plan))
}

#[cfg(test)]
mod tests {
    use super::*;
    // A friend's client reaches the box over `--remote` (an `ssh:DEST` socket
    // address relayed by `mini socket-proxy`). The box answers a plan request;
    // the client's independently selected consent provider reconstructs the
    // plan it expects. One changed byte in the served plan must refuse before
    // any signing consumer receives the bytes.
    const STUB_PLAN: &[u8] = b"DREGG/PLAN/stub-transfer-10";
    const STUB_OPERATION: u8 = mini_sdk::host_operations::APPLICATION_SHARE_ISSUE_PLAN;
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
        // The worker is this test binary, not `mini`: it cannot be a resident consent
        // provider (`connect_resident` would start `<test binary> consent-resident`, which
        // the test harness refuses with exit 101). The resident is not under test here, so
        // the provider runs in the worker process; anchors and HOME stay in the stub dir.
        let output = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "client_consent::tests::remote_plan_stub_worker", "--ignored", "--nocapture", "--test-threads=1"])
            .env("MINI_CONSENT_RESIDENT", "0")
            .env("HOME", &dir)
            .env("MINI_CONSENT_ANCHOR_DIR", dir.join("anchors"))
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
        match crate::transport::invoke_pinned(Path::new("ssh:plan-stub"), &config, &"00".repeat(32), STUB_OPERATION, b"retained request") {
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
            assert_eq!(local_frame(&host, &settings, mini_sdk::host_operations::AUTHOR, b"intent").unwrap(), b"\x07ok");
        }
        assert_eq!(fs::read_to_string(dir.join("starts")).unwrap().lines().count(), 1);
        let other = stub_dir("codec-refusal");
        fs::write(other.join("settings.json"), b"{}").unwrap();
        fs::write(other.join("reply-1"), framed(&[253, 0xff, 0x00])).unwrap();
        fs::write(other.join("reply-2"), framed(&[b"\x08".as_slice(), br#"{"type":"refused","reason":"malformed","phase":"6f702037","detail":"243a206d697373696e67206669656c64206e6f6e6365"}"#.as_slice()].concat())).unwrap();
        fs::write(other.join("reply"), framed(b"\x07again")).unwrap();
        let refusing = codec_stub(&other);
        let settings = other.join("settings.json");
        let error = local_frame(&refusing, &settings, mini_sdk::host_operations::AUTHOR, b"intent").unwrap_err();
        assert!(error.starts_with("host refused author: refused: malformed: $: missing field nonce (phase op 7)"), "{error}");
        assert!(matches!(crate::take_host_decision(), Some(crate::HostDecision::Frame { byte: 253, .. })));
        assert_eq!(local_frame(&refusing, &settings, mini_sdk::host_operations::AUTHOR, b"intent").unwrap(), b"\x07again");
        assert_eq!(fs::read_to_string(other.join("starts")).unwrap().lines().count(), 1);
        CODEC.lock().unwrap().reset();
        let _ = fs::remove_dir_all(&dir);
        let _ = fs::remove_dir_all(&other);
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
        let error = local_frame(&host, &settings, mini_sdk::host_operations::AUTHOR, b"intent").unwrap_err();
        // Under the 255 envelope and undecoded: undecided, never "refused".
        assert!(error.starts_with("undecided: Host answered author with reply byte 255 and outcome undecoded"), "{error}");
        assert!(matches!(crate::take_host_decision(), Some(crate::HostDecision::Frame { byte: 255, decoded: None, .. })));
        fs::write(dir.join("reply"), framed(b"\x07ok")).unwrap();
        assert_eq!(local_frame(&host, &settings, mini_sdk::host_operations::AUTHOR, b"intent").unwrap(), b"\x07ok");
        assert_eq!(fs::read_to_string(dir.join("starts")).unwrap().lines().count(), 2);
        CODEC.lock().unwrap().reset();
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

