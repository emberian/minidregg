//! Document authoring on source-owned object audiences. This module never turns
//! a room key or local cache epoch into authority. Its Audience is built from
//! the Host's separately authorized source/catalog check; final content admission
//! must run the matching all-keyholder receiver gate over the exact post.
use crate::{object_keys::{AdmittedAnchor, Store}, object_messages::{self, Context}, Result};
use super::{content_privacy::{self, Exposure}, private};
use ed25519_dalek::SigningKey;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use zeroize::Zeroizing;

const FRAME: &[u8] = b"MINI/PROTECTED-DOCUMENT-ATOM/v1";
const MESSAGE_FRAME: &[u8] = b"MINI/OBJECT-MESSAGE/v1";
const OP_FRAME: &[u8] = b"MINI/PROTECTED-DOCUMENT-ATOM-OP/v1";

fn nat32(text: &str) -> Result<[u8; 32]> {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0')) {
        return Err("protected document identifier must be a canonical Nat".into());
    }
    let mut out = [0u8; 32];
    for digit in text.bytes() {
        let mut carry = (digit - b'0') as u16;
        for byte in out.iter_mut().rev() {
            carry += (*byte as u16) * 10; *byte = carry as u8; carry >>= 8;
        }
        if carry != 0 { return Err("protected document identifier exceeds 256 bits".into()); }
    }
    Ok(out)
}
fn text<'a>(v: &'a Value, key: &str) -> Result<&'a str> {
    v[key].as_str().ok_or_else(|| format!("protected document lacks {key}"))
}
fn decimal(bytes: &[u8]) -> String {
    let mut digits = vec![0u8];
    for byte in bytes {
        let mut carry = *byte as u16;
        for digit in &mut digits { carry += (*digit as u16) * 256; *digit = (carry % 10) as u8; carry /= 10; }
        while carry > 0 { digits.push((carry % 10) as u8); carry /= 10; }
    }
    digits.iter().rev().map(|d| (b'0' + d) as char).collect()
}
pub(crate) fn schema() -> String { decimal(&Sha256::digest(FRAME)) }
pub(crate) fn is_kind(kind: &Value) -> bool {
    kind == &json!({"type":"inlineObject","schema":schema()})
}
fn atom_operation(object: &[u8;32], atom: &[u8;32], operation: &[u8;32]) -> [u8;32] {
    let mut hash = Sha256::new();
    hash.update(OP_FRAME); hash.update(object); hash.update(atom); hash.update(operation);
    hash.finalize().into()
}

/// The arguments must be returned by actual Host calls, never imported JSON:
/// `object-audience` and `object-audience-roster` with independently authorized
/// document/catalog signed observations. The constructor checks their join.
pub(crate) struct Audience {
    anchor: AdmittedAnchor,
    law: [u8;32],
    roster: Value,
    object: String,
    root: String,
    world: String,
}
impl Audience {
    pub(crate) fn from_checked(source: &Value, checked: &Value, target: &str) -> Result<Self> {
        if source["type"] != "minidregg-object-audience-v1"
            || source["object"] != target || source["active"] != true {
            return Err("fresh active source-owned document audience required".into());
        }
        if checked["type"] != "minidregg-checked-object-roster-v1"
            || checked["audienceState"] != source["audienceState"] {
            return Err("document audience differs from the checked complete roster".into());
        }
        let roster = &checked["roster"];
        if roster["object"] != source["object"] || roster["epoch"] != source["epoch"]
            || roster["transition"] != source["transition"]
            || roster["entries"].as_array().is_none_or(|e| e.is_empty()) {
            return Err("document roster identity differs from admitted audience".into());
        }
        let epoch = text(source,"epoch")?.parse::<u64>().map_err(|_| "document epoch exceeds u64")?;
        let object = nat32(target)?;
        Ok(Self { anchor: AdmittedAnchor { object, epoch,
            transition:nat32(text(source,"transition")?)?, active:true },
            law:nat32(text(source,"policyAddress")?)?, roster:roster.clone(), object:target.into(),
            root:text(source,"currentObjectRoot")?.into(), world:text(source,"worldRoot")?.into() })
    }
    /// Bind BOTH fields in the exact signed target. The matching receiver guards
    /// source/authority/clock/device roots and rechecks every holder's post-view.
    pub(crate) fn bind_target(&self, target: &mut Value, world: &str) -> Result<()> {
        if target["target"] != self.object || target["expectedTargetRoot"] != self.root || world != self.world {
            return Err("document and audience observations disagree on the exact image".into());
        }
        for (field, expected) in [("audienceEpoch",json!(self.anchor.epoch.to_string())),("audienceRoster",self.roster.clone())] {
            if target.get(field).is_some_and(|old| !old.is_null() && old != &expected) {
                return Err(format!("document target has a different {field}"));
            }
            target[field] = expected;
        }
        Ok(())
    }
    /// Each atom has a stable operation derived from the retained command nonce.
    /// Custody persists exact cipher bytes before they become eligible for a call.
    pub(crate) fn seal_actions(&self, actions: &Value, operation: &[u8;32],
        store: &mut Store, writer: &SigningKey) -> Result<Value> {
        let mut result = content_privacy::actions(actions, true)?;
        for action in result["actions"].as_array_mut().expect("validated actions") {
            match content_privacy::classify(action)? {
                Exposure::Structure => {},
                Exposure::Unsupported => return Err("protected document action has no disclosure contract".into()),
                Exposure::CreateText | Exposure::EditText => {
                    let atom = nat32(text(action,"atom")?)?;
                    if action["type"] == "editAtom" {
                        let before = &action["before"];
                        let fields = ["document","kind","payload","createdBy","createdAt","revision","tombstonedAt"];
                        let record = before.as_object().ok_or("protected edit lacks raw before record")?;
                        if record.len()!=fields.len() || fields.iter().any(|f| !record.contains_key(*f)) {
                            return Err("protected edit before record has unexpected fields".into());
                        }
                        if action["tombstone"] == true {
                            if action["payload"] != before["payload"] || action["kind"] != before["kind"] {
                                return Err("protected tombstone must preserve exact old ciphertext".into());
                            }
                            continue;
                        }
                        if action["tombstone"] != false { return Err("protected edit needs tombstone flag".into()); }
                    }
                    if action["kind"] != json!({"type":"text"}) && !is_kind(&action["kind"]) {
                        return Err("protected document seals text atoms only".into());
                    }
                    let context = Context { object:self.anchor.object, epoch:self.anchor.epoch,
                        transition:self.anchor.transition, law:self.law,
                        operation:atom_operation(&self.anchor.object,&atom,operation) };
                    let plain = Zeroizing::new(private::decode_hex(text(action,"payload")?)?);
                    let cipher = store.prepare(&self.anchor, &context, writer, &plain)?;
                    let bytes = [FRAME, &atom, operation, &cipher].concat();
                    action["kind"] = json!({"type":"inlineObject","schema":schema()});
                    action["payload"] = json!(crate::hex(&bytes));
                }
            }
        }
        Ok(result)
    }
}

/// Workspace-owned custody uses the same private-file requirements as signing
/// keys. These paths are derived locally, never accepted from an imported hint.
fn custody_paths(root: &std::path::Path) -> (std::path::PathBuf,std::path::PathBuf) {
    let home=root.join("protected-documents");
    (home.join("keys.json"),home.join("storage.key"))
}
fn custody(root: &std::path::Path) -> Result<Store> {
    let (state,key)=custody_paths(root);
    Store::open(&state,crate::read_secret(&key)?.to_bytes())
}
pub(crate) fn ensure_custody(root: &std::path::Path) -> Result<(std::path::PathBuf,std::path::PathBuf)> {
    use ring::rand::{SecureRandom,SystemRandom};
    let home=root.join("protected-documents");
    if home.exists() { super::private_dir(&home)?; } else { super::make_private_dir(&home)?; }
    let (state,key)=custody_paths(root);
    let metadata=home.join("custody.json");
    if (metadata.exists() && (!state.exists() || !key.exists())) || (state.exists() && !key.exists()) {
        return Err("protected document custody is incomplete; restore keys.json and storage.key together; no replacement key was created".into());
    }
    if !key.exists() {
        let mut seed=Zeroizing::new([0u8;32]);
        SystemRandom::new().fill(&mut *seed).map_err(|_| "private document randomness unavailable")?;
        super::private_file(&key,&*seed)?;
    }
    let storage=crate::read_secret(&key)?.to_bytes();
    drop(Store::initialize(&state,storage)?);
    if !metadata.exists() {
        super::private_file(&metadata,&serde_json::to_vec_pretty(&json!({
            "type":"mini-protected-document-custody-v1","version":"1",
            "required":["keys.json","storage.key"],"includeTree":true,
            "scope":"participant-workspace","restore":"quiesce the owning writer and restore the entire WORKSPACE together",
            "hostedBackup":"include the entire WORKSPACE in statePaths with its owning writer quiesced; /var/lib/mini/sessions has default recursive encrypted coverage",
            "history":"keys.json and storage.key preserve retained content epoch keys; they are not reenrollable provider credentials"})).map_err(|e|e.to_string())?)?;
    }
    Ok((state,key))
}

/// Join custody hints by exact target, without replacing the selected shared
/// reference's authority or snapshot pin. Hints are read only from local files;
/// current source/catalog authorization still validates their meaning later.
pub(crate) fn reference_context(root:&std::path::Path,mut reference:Value)->Result<Value> {
    let mut hints=Vec::new();
    if let Some(hint)=reference.get("protectedDocument") {hints.push(hint.clone());}
    for file in std::fs::read_dir(root.join("refs")).map_err(|e|e.to_string())? {
        let file=file.map_err(|e|e.to_string())?;
        if file.path().extension().is_none_or(|ext|ext!="json") {continue;}
        let Ok(other)=super::bounded_json(&file.path()) else {continue};
        if other["type"]=="minidregg-participant-reference-v1" && other["target"]==reference["target"] && other["kind"]==reference["kind"] {
            if let Some(hint)=other.get("protectedDocument") {hints.push(hint.clone());}
        }
    }
    let mut identity=None;
    for hint in hints {
        if hint["version"]!="1" {return Err("unsupported protected document custody hint".into());}
        let catalog=super::local_reference(root,text(&hint,"catalog")?)?;
        let target=super::member(&catalog,"target")?.to_owned();
        if identity.as_ref().is_some_and(|old|old!=&target) {return Err("local protected document aliases disagree on their device catalog".into());}
        identity=Some(target);
        if reference.get("protectedDocument").is_none() {reference["protectedDocument"]=hint;}
    }
    Ok(reference)
}

/// Join a current document observation to its separately authorized catalog.
/// Importing a path, room name, roster JSON, or epoch never calls this constructor
/// by itself. The Host validates the canonical roster and current catalog bytes.
pub(crate) fn observe(root:&std::path::Path, workspace:&Value, reference:&Value,
    signed:&std::path::Path) -> Result<Audience> {
    use std::path::Path;
    let target=super::member(reference,"target")?;
    let hint=&reference["protectedDocument"];
    if hint["version"] != "1" { return Err("unsupported protected document reference".into()); }
    let dir=signed.parent().ok_or("document observation has no retained directory")?;
    let host=super::workspace_host(workspace)?;
    let config=super::member_path(workspace,"config")?;
    let source_path=dir.join("protected-audience.json");
    crate::host_files(&host,&config,&[Path::new("object-audience"),signed,&source_path])?;
    let source=super::bounded_json(&source_path)?;
    if source["active"] != true { return Err("protected document is frozen; finish its recorded audience transition".into()); }
    let catalog=super::local_reference(root,text(hint,"catalog")?)?;
    let (_,_,catalog_signed)=super::signed_view(root,workspace,&catalog,"resource")?;
    let roster=root.join("protected-documents").join(target).join("roster.bin");
    let state=dir.join("current-audience-state.json");
    super::private_file(&state,&serde_json::to_vec(&source["audienceState"]).map_err(|e|e.to_string())?)?;
    let checked_path=dir.join("checked-document-roster.json");
    crate::host_files(&host,&config,&[Path::new("object-audience-roster"),signed,&catalog_signed,
        &state,&roster,&checked_path])?;
    Audience::from_checked(&source,&super::bounded_json(&checked_path)?,target)
}

pub(crate) fn seal(root:&std::path::Path,workspace:&Value,audience:&Audience,
    lowered:Value,command_nonce:&str) -> Result<Value> {
    let mut store=custody(root)?;
    let writer=crate::read_secret(&super::member_path(workspace,"key")?)?;
    audience.seal_actions(&lowered["actions"],&nat32(command_nonce)?,&mut store,&writer)
}

/// Only used after current signed read authorization. Keep the original view
/// immutable and add authenticated display annotations to a separate projection.
pub(crate) fn opened_entries(root:&std::path::Path,reference:&Value,view:&Value) -> Result<Vec<Value>> {
    let mut entries=super::entries(view)?.clone();
    let (state,key)=custody_paths(root);
    let store=if state.exists() && key.exists() {Some(custody(root)?)} else {None};
    for atom in &mut entries {
        if atom["type"]!="atom" || !is_kind(&atom["kind"]) {continue;}
        let opened=store.as_ref().ok_or_else(||"protected document epoch key is not held".to_owned())
            .and_then(|store|open_atom(super::member(reference,"target")?,text(atom,"id")?,text(atom,"payload")?,store));
        atom["private"]=match opened {
            Ok(bytes)=>match String::from_utf8(bytes) {
                Ok(text)=>json!({"text":text}), Err(error)=>json!({"hex":crate::hex(error.as_bytes())})
            },
            Err(_)=>json!("[private: protected epoch is locked or unreadable]"),
        };
    }
    Ok(entries)
}

/// Publish a stable participant device from durable custody; exporting this file
/// exports only its public encryption identity, never the retained secret.
pub(crate) fn device(root:&std::path::Path) -> Result<Value> {
    let (state,key)=ensure_custody(root)?;
    let output=root.join("protected-documents/device.json");
    if !output.exists() { crate::object_epoch_cli::device(&state,&key,&output)?; }
    super::bounded_json(&output)
}

fn rewrite_reference(root:&std::path::Path,name:&str,value:&Value)->Result<()> {
    super::validate_ref_name(name)?;
    let refs=root.join("refs");
    let temporary=refs.join(format!(".{name}.protected-{}",super::random_nonce()?));
    super::private_file(&temporary,&serde_json::to_vec_pretty(value).map_err(|e|e.to_string())?)?;
    std::fs::rename(&temporary,refs.join(format!("{}.json",super::ref_file(name)))).map_err(|e|e.to_string())?;
    std::fs::File::open(&refs).and_then(|f|f.sync_all()).map_err(|e|e.to_string())
}

/// Publish an immutable complete record before performing any operation it names.
/// Interrupted temporary files are never interpreted as committed enrollment state.
fn retain_record(path:&std::path::Path,bytes:&[u8])->Result<()> {
    use std::fs;
    if path.exists() { return write_same(path,bytes); }
    let parent=path.parent().ok_or("retained record lacks a parent")?;
    let temporary=parent.join(format!(".enrollment-{}",super::random_nonce()?));
    super::private_file(&temporary,bytes)?;
    match fs::hard_link(&temporary,path) {
        Ok(()) => {},
        Err(error) if error.kind()==std::io::ErrorKind::AlreadyExists => write_same(path,bytes)?,
        Err(error) => return Err(error.to_string()),
    }
    fs::File::open(parent).and_then(|f|f.sync_all()).map_err(|e|e.to_string())?;
    fs::remove_file(&temporary).map_err(|e|e.to_string())?;
    Ok(())
}
fn retain_json(path:&std::path::Path,value:&Value)->Result<()> {
    retain_record(path,&serde_json::to_vec_pretty(value).map_err(|e|e.to_string())?)
}
fn retain_authored(host:&std::path::Path,config:&std::path::Path,kind:&str,
    source:&std::path::Path,output:&std::path::Path)->Result<()> {
    if output.exists() {return Ok(());}
    let parent=output.parent().ok_or("authored enrollment artifact lacks a parent")?;
    let temporary=parent.join(format!(".authoring-{}",super::random_nonce()?));
    crate::author(host,config,std::ffi::OsStr::new(kind),source,&temporary)?;
    retain_record(output,&std::fs::read(&temporary).map_err(|e|e.to_string())?)?;
    std::fs::remove_file(&temporary).map_err(|e|e.to_string())
}
fn stage_path(root:&std::path::Path,target:&str)->Result<std::path::PathBuf> {
    nat32(target)?;
    Ok(root.join("protected-documents").join(format!("enrollment-{target}.json")))
}
fn enrollment_identity(reference:&Value,workspace:&Value,name:&str)->Result<Value> {
    Ok(json!({"name":name,"object":super::member(reference,"target")?,
        "subject":super::member(workspace,"subject")?,
        "observeCapability":super::member(reference,"observeCapability")?,
        "controlCapability":super::member(reference,"controlCapability")?}))
}
fn validate_stage(stage:&Value,identity:&Value)->Result<()> {
    if stage["type"]!="mini-protected-document-stage-v1" || stage["identity"]!=*identity {
        return Err("retained enrollment differs from this document, subject, or capabilities".into());
    }
    super::validate_ref_name(text(stage,"catalog")?)?;
    nat32(text(stage,"transition")?)?;
    nat32(text(stage,"catalogNonce")?)?;
    nat32(text(stage,"catalogQueryNonce")?)?;
    let operation=private::decode_hex(text(stage,"operation")?)?;
    if operation.len()!=32 {return Err("retained enrollment operation must be 32 bytes".into());}
    if !stage["device"].is_object() {return Err("retained enrollment lacks its device publication".into());}
    Ok(())
}
/// A call is persisted before emission. An interrupted preparation with no call
/// can use a new attempt directory around the SAME retained intent, never a new
/// catalog write or nonce. An emitted call always wins over later preparation.
fn retained_attempt(root:&std::path::Path,label:&str)->Result<(std::path::PathBuf,bool)> {
    super::validate_ref_name(label)?;
    for generation in 0..1000 {
        let attempt=root.join("attempts").join(format!("{label}-{generation}"));
        if attempt.join("call.bin").is_file() {return Ok((attempt,true));}
        if !attempt.exists() {return Ok((attempt,false));}
    }
    Err("retained enrollment exhausted preparation attempts".into())
}
fn submit_retained(root:&std::path::Path,workspace:&Value,intent:&std::path::Path,label:&str)->Result<()> {
    let (attempt,emitted)=retained_attempt(root,label)?;
    if emitted {crate::retry(&attempt,"submit",true)} else {
        super::submit_intent(root,workspace,intent,"intent",false,Some(&attempt))
    }
}

/// Source-owned owner-only enrollment for a new empty document. A complete
/// immutable stage is durable before the catalog birth or any source mutation.
pub(crate) fn protect_empty(root:&std::path::Path,workspace:&Value,name:&str) -> Result<()> {
    use std::path::Path;
    let reference=super::local_reference(root,name)?;
    let target=super::member(&reference,"target")?.to_owned();
    let retained=stage_path(root,&target)?;
    if retained.exists() {return recover(root,workspace,name);}
    if reference.get("protectedDocument").is_some() {return Err("document already has protected custody".into());}
    let (view,_,signed)=super::signed_view(root,workspace,&reference,"resource")?;
    if super::entries(&view)?.iter().any(|entry| entry["type"]=="atom") {
        return Err("existing document text is retained; protect-empty requires an empty document, not implicit historical disclosure".into());
    }
    let host=super::workspace_host(workspace)?;
    let config=super::member_path(workspace,"config")?;
    let supported=signed.parent().ok_or("missing observation directory")?.join("audience-supported.json");
    crate::host_files(&host,&config,&[Path::new("object-audience"),&signed,&supported])?;
    let initial=super::bounded_json(&supported)?;
    if !initial["audienceState"].is_null() {return Err("document audience already enrolled; recover its retained enrollment".into());}
    ensure_custody(root)?;
    let public=device(root)?;
    let home=root.join("protected-documents").join(&target);
    if home.exists() {return Err(format!("older enrollment retained at {}; recover its exact artifacts",home.display()));}
    let stage=json!({"type":"mini-protected-document-stage-v1",
        "identity":enrollment_identity(&reference,workspace,name)?,
        "catalog":format!("pd-catalog-{}",super::random_nonce()?),
        "transition":super::random_nonce()?,"operation":crate::hex(&nat32(&super::random_nonce()?)?),
        "catalogNonce":super::random_nonce()?,"catalogQueryNonce":super::random_nonce()?,"device":public});
    retain_json(&retained,&stage)?;
    continue_enrollment(root,workspace,name,&stage)
}

/// Resume pre-phase construction from retained identities. Every existing birth,
/// catalog command, roster and phase request is reused, never replaced.
fn continue_enrollment(root:&std::path::Path,workspace:&Value,name:&str,stage:&Value)->Result<()> {
    use std::path::Path;
    let reference=super::reference(root,name)?;
    validate_stage(stage,&enrollment_identity(&reference,workspace,name)?)?;
    let target=super::member(&reference,"target")?;
    let home=root.join("protected-documents").join(target);
    if home.exists() {super::private_dir(&home)?;} else {super::make_private_dir(&home)?;}
    if home.join("enrollment.json").exists() {return recover_phase(root,workspace,name,&home);}
    let (state,storage)=ensure_custody(root)?;
    let public=&stage["device"];
    // Reopen the exact retained device; losing it is not permission to keygen.
    let generation: [u8;32]=private::decode_hex(text(public,"generation")?)?.try_into().map_err(|_|"invalid retained device generation")?;
    let store=custody(root)?;
    let (_,retained_public)=store.load_device(&generation)?;
    if public["kemPublic"]!=crate::hex(&retained_public.kem) || public["dhPublic"]!=crate::hex(&retained_public.dh) {
        return Err("retained enrollment device differs from durable custody".into());
    }
    drop(store);
    let (view,_,_)=super::signed_view(root,workspace,&reference,"resource")?;
    if super::entries(&view)?.iter().any(|entry|entry["type"]=="atom") {
        return Err("document gained text before enrollment; retained empty-document request cannot disclose it".into());
    }
    let host=super::workspace_host(workspace)?;
    let config=super::member_path(workspace,"config")?;
    let writer=super::member_path(workspace,"key")?;
    let catalog_name=text(stage,"catalog")?;
    let predicate=home.join("catalog-law.json");
    retain_record(&predicate,br#"{"type":"all","predicates":[]}"#)?;
    // create reopens the same namespace reservation, birth source and exact call.
    super::create(root,workspace,catalog_name,"content",&predicate,None,"object",None,None,None)?;
    let catalog=super::local_reference(root,catalog_name)?;
    let catalog_id=super::member(&catalog,"target")?;
    let me=super::member(workspace,"subject")?;
    let roster=json!({"object":target,"epoch":"0","transition":stage["transition"],"entries":[{
        "subject":me,"capability":super::member(&reference,"observeCapability")?,"deviceSource":catalog_id,
        "deviceGeneration":public["deviceGeneration"],"keyCommitment":public["keyCommitment"]}]});
    let roster_json=home.join("roster.json");retain_json(&roster_json,&roster)?;
    let roster_bin=home.join("roster.bin");
    retain_authored(&host,&config,"object-audience-roster",&roster_json,&roster_bin)?;
    let catalog_bin=home.join("catalog.bin");
    retain_authored(&host,&config,"object-device-catalog",&roster_json,&catalog_bin)?;
    let catalog_write=home.join("catalog-write-intent.json");
    if !catalog_write.exists() {
        let (view,_,_)=super::signed_view(root,workspace,&catalog,"resource")?;
        let payload=crate::hex(&std::fs::read(&catalog_bin).map_err(|e|e.to_string())?);
        let nonce=text(stage,"catalogNonce")?;
        retain_json(&catalog_write,&json!({"subject":me,"nonce":nonce,"purpose":{"type":"prepare",
            "draft":{"type":"invoke","command":{"subject":me,"nonce":nonce,"targets":[{
                "kind":"object","target":catalog_id,"capability":super::member(&catalog,"operationCapability")?,
                "observeCapability":super::member(&catalog,"observeCapability")?,"schemaVersion":super::CONTENT_COMMAND_VERSION,
                "expectedTargetRoot":text(&view["cell"],"root")?,"payload":{"type":"content","actions":[{
                    "type":"createAtom","atom":"0","kind":{"type":"text"},"payload":payload}]}}]}}},
            "grants":[{"kind":"object","target":catalog_id,"capability":super::member(&catalog,"observeCapability")?}]}))?;
    }
    submit_retained(root,workspace,&catalog_write,text(stage,"operation")?)?;
    let catalog_intent=home.join("catalog-intent.json");
    retain_json(&catalog_intent,&json!({"subject":me,"nonce":stage["catalogQueryNonce"],
        "purpose":{"type":"query","kind":"object","target":catalog_id,"view":"resource"},
        "grants":[{"kind":"object","target":catalog_id,"capability":super::member(&catalog,"observeCapability")?}]}))?;
    let request=json!({"phase":"enroll","control":super::member(&reference,"controlCapability")?,
        "operation":stage["operation"],"transition":stage["transition"],"audience":"0","devices":"0","history":"0",
        "dealerGeneration":public["generation"],"rosterBytes":crate::hex(&std::fs::read(&roster_bin).map_err(|e|e.to_string())?),
        "catalogIntent":catalog_intent,"recipients":[{"subject":me,"capability":super::member(&reference,"observeCapability")?,
        "deviceSource":catalog_id,"generation":public["generation"],"keyCommitment":public["keyCommitment"],
        "kemPublic":public["kemPublic"],"dhPublic":public["dhPublic"]}],
        "grants":[{"kind":"object","target":target,"capability":super::member(&reference,"observeCapability")?}]});
    let request_path=home.join("enrollment-request.json");retain_json(&request_path,&request)?;
    let (_,_,signed)=super::signed_view(root,workspace,&reference,"resource")?;
    let phase_root=signed.parent().ok_or("missing phase observation")?;
    let source_path=phase_root.join("protected-audience.json");
    crate::host_files(&host,&config,&[Path::new("object-audience"),&signed,&source_path])?;
    let source=super::bounded_json(&source_path)?;
    if !source["audienceState"].is_null() {return Err("document audience changed before retained enrollment phase".into());}
    let phase_dir=phase_root.join("epoch");
    retain_json(&home.join("enrollment.json"),&json!({
        "type":"mini-protected-document-enrollment-v1","name":name,"object":target,"catalog":catalog_name,
        "operation":stage["operation"],"phaseDirectory":phase_dir.strip_prefix(root).map_err(|_|"phase must remain inside participant workspace")?,
        "custody":"protected-documents"}))?;
    crate::object_epoch_cli::run(&source,&request_path,&host,&config,&writer,&state,&storage,&phase_dir)?;
    finish_enrollment(root,workspace,name,&home)
}

/// Pre-phase recovery reuses retained catalog identities and writes. Once epoch
/// custody exists, only its exact phase command and package manifest may proceed.
pub(crate) fn recover(root:&std::path::Path,workspace:&Value,name:&str)->Result<()> {
    let reference=super::local_reference(root,name)?;
    let target=super::member(&reference,"target")?;
    let home=root.join("protected-documents").join(target);
    if home.join("enrollment.json").exists() {return recover_phase(root,workspace,name,&home);}
    let stage=super::bounded_json(&stage_path(root,target)?)?;
    continue_enrollment(root,workspace,name,&stage)
}
fn recover_phase(root:&std::path::Path,workspace:&Value,name:&str,home:&std::path::Path)->Result<()> {
    let reference=super::local_reference(root,name)?;
    let meta=super::bounded_json(&home.join("enrollment.json"))?;
    if meta["object"]!=reference["target"] {return Err("retained enrollment names another document".into());}
    let phase=retained_phase(root,&meta)?;
    let (_,_,signed)=super::signed_view(root,workspace,&reference,"resource")?;
    let source=audience_source(workspace,&signed)?;
    let (state,key)=custody_paths(root);
    if !phase.exists() {
        // Metadata was durable, but epoch construction had not begun. Reuse its
        // immutable request and original signed observation directory.
        if !source["audienceState"].is_null() {return Err("document audience changed before retained phase began".into());}
        let original=super::bounded_json(&phase.parent().ok_or("phase has no parent")?.join("protected-audience.json"))?;
        crate::object_epoch_cli::run(&original,&home.join("enrollment-request.json"),
            &super::workspace_host(workspace)?,&super::member_path(workspace,"config")?,
            &super::member_path(workspace,"key")?,&state,&key,&phase)?;
        return finish_enrollment(root,workspace,name,home);
    }
    if !crate::object_epoch_cli::restore_phase(&phase,&state,&key,text(&meta,"operation")?)? {
        // Preparation stopped before any key/phase was durably chosen. The
        // original immutable request can resume; run refuses orphaned final
        // artifacts instead of interpreting missing custody as a new operation.
        if !source["audienceState"].is_null() {return Err("source changed before epoch custody was staged".into());}
        let original=super::bounded_json(&phase.parent().ok_or("phase has no parent")?.join("protected-audience.json"))?;
        crate::object_epoch_cli::run(&original,&home.join("enrollment-request.json"),
            &super::workspace_host(workspace)?,&super::member_path(workspace,"config")?,
            &super::member_path(workspace,"key")?,&state,&key,&phase)?;
        return finish_enrollment(root,workspace,name,home);
    }
    let operation: [u8;32]=private::decode_hex(text(&meta,"operation")?)?.try_into().map_err(|_|"invalid enrollment operation")?;
    let store=custody(root)?;
    let staged=store.pending_epoch(&operation);
    drop(store);
    if let Ok((manifest,command))=&staged {
        retain_record(&phase.join("phase-intent.bin"),command)?;
        retain_record(&phase.join("epoch-manifest.bin"),manifest)?;
    }
    let intent=super::bounded_json(&phase.join("phase-intent.json")).map_err(|error|
        format!("epoch preparation has no recoverable intent; retained request and catalog are preserved, no replacement keys created: {error}"))?;
    let expected=&intent["purpose"]["draft"]["declaration"]["source"]["audience"];
    if expected.is_null() {return Err("retained enrollment has no exact audience".into());}
    if !source["audienceState"].is_null() && source["audienceState"]!=*expected {
        return Err("document audience has moved; retained enrollment cannot replace it".into());
    }
    if staged.is_ok() {
        // Even an already admitted source must settle the pending key journal.
        crate::object_epoch_cli::retry(&phase,&state,&key,text(&meta,"operation")?,
            Some(&super::member_path(workspace,"key")?))?;
    } else {
        let epoch=text(expected,"epoch")?.parse().map_err(|_|"retained epoch exceeds u64")?;
        let anchor=AdmittedAnchor {object:nat32(text(expected,"object")?)?,epoch,
            transition:nat32(text(expected,"transition")?)?,active:true};
        custody(root)?.historical_key(&anchor).map_err(|error|
            format!("epoch has no durable staged or accepted key; retained artifacts preserved, refusing replacement material: {error}"))?;
        if source["audienceState"]!=*expected {return Err("source does not confirm retained accepted enrollment".into());}
    }
    finish_enrollment(root,workspace,name,home)
}
fn retained_phase(root:&std::path::Path,meta:&Value)->Result<std::path::PathBuf> {
    let relative=std::path::Path::new(text(meta,"phaseDirectory")?);
    if relative.as_os_str().is_empty() || relative.components().any(|part| !matches!(part,std::path::Component::Normal(_))) {
        return Err("retained phase must be a relative path inside this participant workspace".into());
    }
    Ok(root.join(relative))
}
fn audience_source(workspace:&Value,signed:&std::path::Path)->Result<Value> {
    let output=signed.parent().ok_or("missing observation directory")?.join("recovered-audience.json");
    crate::host_files(&super::workspace_host(workspace)?,&super::member_path(workspace,"config")?,
        &[std::path::Path::new("object-audience"),signed,&output])?;
    super::bounded_json(&output)
}
fn finish_enrollment(root:&std::path::Path,workspace:&Value,name:&str,home:&std::path::Path)->Result<()> {
    let meta=super::bounded_json(&home.join("enrollment.json"))?;
    let phase=retained_phase(root,&meta)?;
    let mut reference=super::local_reference(root,name)?;
    if reference["target"]!=meta["object"] {return Err("retained enrollment names another document".into());}
    let (_,_,signed)=super::signed_view(root,workspace,&reference,"resource")?;
    let source=audience_source(workspace,&signed)?;
    let intent=super::bounded_json(&phase.join("phase-intent.json"))?;
    let expected=&intent["purpose"]["draft"]["declaration"]["source"]["audience"];
    let manifest=std::fs::read(phase.join("epoch-manifest.bin")).map_err(|e|e.to_string())?;
    if expected.is_null() || source["audienceState"]!=*expected || source["active"]!=true
        || source["audienceState"]["manifest"]!=decimal(&Sha256::digest(&manifest)) {
        return Err("current source does not confirm this exact enrollment manifest".into());
    }
    reference["protectedDocument"]=json!({"version":"1","catalog":meta["catalog"]});
    rewrite_reference(root,name,&reference)?;
    // This retained structural post runs the complete current-entitlement gate.
    // It authorizes only this enrollment's exact empty-document handout.
    let ready_id=text(&meta,"operation")?.to_owned();
    let request_path=home.join("ready-request.json");
    if !request_path.exists() {
        let request=json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{
            "name":name,"payload":{"type":"content","actions":[{
                "type":"createContainer","element":super::random_nonce()?}]}}]});
        super::private_file(&request_path,&serde_json::to_vec(&request).map_err(|e|e.to_string())?)?;
    }
    let attempt=root.join("attempts").join(&ready_id);
    if attempt.join("call.bin").exists() {crate::retry(&attempt,"submit",true)?;} else {
        let intent_path=root.join("proposals").join(&ready_id).join("intent.json");
        if !intent_path.exists() {super::propose(root,workspace,&request_path,&ready_id,None)?;}
        super::submit_intent(root,workspace,&intent_path,"intent",false,Some(&attempt))?;
    }
    let public_manifest=home.join("epoch-manifest.bin");
    if public_manifest.exists() {
        if std::fs::read(&public_manifest).map_err(|e|e.to_string())?!=manifest {
            return Err("retained published manifest differs".into());
        }
    } else {super::private_file(&public_manifest,&manifest)?;}
    println!("{name}: protected audience enrolled; document edits use its admitted object epoch");
    Ok(())
}

/// Export only the retained manifest whose initial handout passed the actual
/// protected readiness transaction. Current source and catalog reads are still
/// required; this command never exports content keys or device private material.
pub(crate) fn export_epoch(root:&std::path::Path,workspace:&Value,name:&str,output:&std::path::Path)->Result<()> {
    let reference=super::local_reference(root,name)?;
    let target=super::member(&reference,"target")?;
    let (_,_,signed)=super::signed_view(root,workspace,&reference,"resource")?;
    let audience=observe(root,workspace,&reference,&signed)?;
    let source=audience_source(workspace,&signed)?;
    let home=root.join("protected-documents").join(target);
    let meta=super::bounded_json(&home.join("enrollment.json"))?;
    let manifest=std::fs::read(home.join("epoch-manifest.bin")).map_err(|_|"document has no admitted manifest handout; finish protected enrollment first")?;
    if source["audienceState"]["manifest"]!=decimal(&Sha256::digest(&manifest)) {
        return Err("retained manifest is not this source's current committed epoch".into());
    }
    let writer=crate::read_secret(&super::member_path(workspace,"key")?)?;
    let bundle=json!({"type":"mini-protected-document-epoch-v1","object":target,
        "epoch":audience.anchor.epoch.to_string(),"manifest":crate::hex(&manifest),
        "operation":meta["operation"],"writer":crate::hex(&writer.verifying_key().to_bytes()),
        "rosterBytes":crate::hex(&std::fs::read(home.join("roster.bin")).map_err(|e|e.to_string())?)});
    super::private_file(output,&serde_json::to_vec_pretty(&bundle).map_err(|e|e.to_string())?)
}

/// Import a source-committed package using this participant's durable device.
/// The document and separate catalog references must already be authorized;
/// imported bundle metadata cannot create either authority grant.
pub(crate) fn import_epoch(root:&std::path::Path,workspace:&Value,name:&str,catalog:&str,input:&std::path::Path)->Result<()> {
    let bundle=super::bounded_json(input)?;
    let mut reference=super::local_reference(root,name)?;
    let target=super::member(&reference,"target")?.to_owned();
    if bundle["type"]!="mini-protected-document-epoch-v1" || bundle["object"]!=target {
        return Err("epoch bundle names another document or format".into());
    }
    let (_,_,signed)=super::signed_view(root,workspace,&reference,"resource")?;
    let source=audience_source(workspace,&signed)?;
    let catalog_ref=super::local_reference(root,catalog)?;
    let (_,_,catalog_signed)=super::signed_view(root,workspace,&catalog_ref,"resource")?;
    let attempt=signed.parent().ok_or("missing import observation directory")?;
    let roster_bytes=crate::decode_hex(text(&bundle,"rosterBytes")?)?;
    let roster=attempt.join("import-roster.bin");
    super::private_file(&roster,&roster_bytes)?;
    let state_path=attempt.join("import-audience.json");
    super::private_file(&state_path,&serde_json::to_vec(&source["audienceState"]).map_err(|e|e.to_string())?)?;
    let checked_path=attempt.join("import-roster-checked.json");
    crate::host_files(&super::workspace_host(workspace)?,&super::member_path(workspace,"config")?,
        &[std::path::Path::new("object-audience-roster"),&signed,&catalog_signed,&state_path,&roster,&checked_path])?;
    let audience=Audience::from_checked(&source,&super::bounded_json(&checked_path)?,&target)?;
    if bundle["epoch"]!=audience.anchor.epoch.to_string() {return Err("epoch bundle is not current source epoch".into());}
    let (state,storage)=ensure_custody(root)?;
    let public=device(root)?;
    let request_path=attempt.join("receive-epoch.json");
    let request=json!({"generation":public["generation"],"manifest":bundle["manifest"],
        "operation":bundle["operation"],"writer":bundle["writer"]});
    super::private_file(&request_path,&serde_json::to_vec(&request).map_err(|e|e.to_string())?)?;
    crate::object_cli::receive_epoch(&source,&request_path,&state,&storage)?;
    let home=root.join("protected-documents").join(&target);
    if !home.exists() {super::make_private_dir(&home)?;} else {super::private_dir(&home)?;}
    let epoch_home=home.join(format!("epoch-{}-{}",audience.anchor.epoch,decimal(&audience.anchor.transition)));
    if !epoch_home.exists() {super::make_private_dir(&epoch_home)?;} else {super::private_dir(&epoch_home)?;}
    write_same(&epoch_home.join("roster.bin"),&roster_bytes)?;
    write_same(&epoch_home.join("received-epoch.json"),&serde_json::to_vec_pretty(&bundle).map_err(|e|e.to_string())?)?;
    let next_roster=home.join(format!(".roster-{}",super::random_nonce()?));
    super::private_file(&next_roster,&roster_bytes)?;
    std::fs::rename(&next_roster,home.join("roster.bin")).map_err(|e|e.to_string())?;
    std::fs::File::open(&home).and_then(|f|f.sync_all()).map_err(|e|e.to_string())?;
    reference["protectedDocument"]=json!({"version":"1","catalog":catalog});
    rewrite_reference(root,name,&reference)?;
    println!("{name}: admitted epoch retained in this participant's document custody");
    Ok(())
}
fn write_same(path:&std::path::Path,bytes:&[u8])->Result<()> {
    if path.exists() {
        if std::fs::read(path).map_err(|e|e.to_string())?!=bytes {return Err(format!("{} already records different epoch material",path.display()));}
        Ok(())
    } else {super::private_file(path,bytes)}
}

fn fixed<const N:usize>(bytes:&[u8]) -> Result<[u8;N]> {
    bytes.try_into().map_err(|_| "malformed protected atom envelope".into())
}
/// Current document observation authority must already have succeeded. Historical
/// epoch keys open historical atoms; current epoch is not substituted into them.
pub(crate) fn open_atom(object:&str, atom:&str, payload:&str, store:&Store) -> Result<Vec<u8>> {
    let bytes = private::decode_hex(payload)?;
    let prefix = FRAME.len();
    let min = prefix+64+MESSAGE_FRAME.len()+32+8+32+32+32+32+24+16+64;
    if bytes.len()<min || !bytes.starts_with(FRAME) { return Err("malformed protected atom envelope".into()); }
    let atom_id=nat32(atom)?;
    if bytes[prefix..prefix+32]!=atom_id { return Err("protected atom address differs".into()); }
    let operation=fixed::<32>(&bytes[prefix+32..prefix+64])?;
    let record=&bytes[prefix+64..];
    if !record.starts_with(MESSAGE_FRAME) { return Err("wrong protected message frame".into()); }
    let mut offset=MESSAGE_FRAME.len();
    let object_id=fixed::<32>(&record[offset..offset+32])?; offset+=32;
    let epoch=u64::from_be_bytes(fixed(&record[offset..offset+8])?); offset+=8;
    let transition=fixed::<32>(&record[offset..offset+32])?; offset+=32;
    let bound_op=fixed::<32>(&record[offset..offset+32])?; offset+=32;
    let law=fixed::<32>(&record[offset..offset+32])?; offset+=32;
    let writer=fixed::<32>(&record[offset..offset+32])?;
    if object_id!=nat32(object)? || bound_op!=atom_operation(&object_id,&atom_id,&operation) {
        return Err("protected atom object or operation differs".into());
    }
    let context=Context {object:object_id,epoch,transition,operation:bound_op,law};
    let anchor=AdmittedAnchor {object:object_id,epoch,transition,active:false};
    let key=store.historical_key(&anchor)?;
    object_messages::open(&context,&key,&writer,record)
}

/// Legacy room epochs do not establish current entitlement. Structural changes
/// and exact tombstones add no new plaintext; fresh text needs the protected path.
pub(crate) fn reject_fresh_legacy(actions:&Value) -> Result<()> {
    for action in actions.as_array().ok_or("content actions must be an array")? {
        match content_privacy::classify(action)? {
            Exposure::CreateText => return Err("fresh private text requires protected-document audience enrollment; existing data and drafts are retained".into()),
            Exposure::EditText if action["tombstone"] != true => return Err("fresh private text requires protected-document audience enrollment; existing data and drafts are retained".into()),
            Exposure::Unsupported => return Err("private document action has no disclosure contract".into()),
            _ => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn source(epoch:u64,transition:u64)->(Value,Value) {
        let state=json!({"object":"72","epoch":epoch.to_string(),"transition":transition.to_string(),"mode":"active"});
        let view=json!({"type":"minidregg-object-audience-v1","object":"72","epoch":epoch.to_string(),
            "transition":transition.to_string(),"active":true,"audienceState":state,
            "policyAddress":"400","currentObjectRoot":"500","worldRoot":"600"});
        let checked=json!({"type":"minidregg-checked-object-roster-v1","audienceState":state,
            "roster":{"object":"72","epoch":epoch.to_string(),"transition":transition.to_string(),
                "entries":[{"subject":"7","capability":"8","deviceSource":"99","deviceGeneration":"10","keyCommitment":"11"}]}});
        (view,checked)
    }
    fn store()->(std::path::PathBuf,Store) {
        let root=std::env::temp_dir().join(format!("mini-protected-doc-{}",super::super::random_nonce().unwrap()));
        super::super::make_private_dir(&root).unwrap();
        let store=Store::open(&root.join("state"),[3;32]).unwrap();
        (root,store)
    }
    #[test]
    fn protected_target_binds_complete_roster_and_exact_observation_cut() {
        let (v,c)=source(7,9);
        let a=Audience::from_checked(&v,&c,"72").unwrap();
        let mut target=json!({"target":"72","expectedTargetRoot":"500"});
        a.bind_target(&mut target,"600").unwrap();
        assert_eq!(target["audienceEpoch"],"7");assert_eq!(target["audienceRoster"],c["roster"]);
        assert!(a.bind_target(&mut target,"601").is_err());
        target["audienceEpoch"]=json!("6");assert!(a.bind_target(&mut target,"600").is_err());
        let mut bad=c.clone();bad["roster"]["object"]=json!("73");
        assert!(Audience::from_checked(&v,&bad,"72").is_err());
        let mut frozen=v.clone();frozen["active"]=json!(false);
        assert!(Audience::from_checked(&frozen,&c,"72").is_err());
    }
    #[test]
    fn protected_atoms_have_distinct_stable_operations_and_historical_context() {
        let (v,c)=source(7,9);let a=Audience::from_checked(&v,&c,"72").unwrap();
        let (root,mut store)=store();store.retain(&a.anchor,&[8;32]).unwrap();
        let writer=SigningKey::from_bytes(&[7;32]);
        let actions=json!([
            {"type":"createAtom","atom":"10","kind":{"type":"text"},"payload":crate::hex(b"one")},
            {"type":"createAtom","atom":"11","kind":{"type":"text"},"payload":crate::hex(b"two")}]);
        let sealed=a.seal_actions(&actions,&[4;32],&mut store,&writer).unwrap();
        assert_eq!(sealed,a.seal_actions(&actions,&[4;32],&mut store,&writer).unwrap());
        let first=sealed["actions"][0]["payload"].as_str().unwrap();
        assert_eq!(open_atom("72","10",first,&store).unwrap(),b"one");
        assert_eq!(open_atom("72","11",sealed["actions"][1]["payload"].as_str().unwrap(),&store).unwrap(),b"two");
        assert!(open_atom("73","10",first,&store).is_err());assert!(open_atom("72","11",first,&store).is_err());
        // Rewriting the unsigned outer address cannot change the signed operation binding.
        let mut forged=private::decode_hex(first).unwrap();
        forged[FRAME.len()..FRAME.len()+32].copy_from_slice(&nat32("11").unwrap());
        assert!(open_atom("72","11",&crate::hex(&forged),&store).is_err());
        let mut changed=actions.clone();changed[0]["payload"]=json!(crate::hex(b"changed"));
        assert!(a.seal_actions(&changed,&[4;32],&mut store,&writer).is_err());
        let (newv,newc)=source(8,12);let newer=Audience::from_checked(&newv,&newc,"72").unwrap();
        store.retain(&newer.anchor,&[9;32]).unwrap();store.reconcile_anchor(&newer.anchor).unwrap();
        assert_eq!(open_atom("72","10",first,&store).unwrap(),b"one");
        drop(store);std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn legacy_confidentiality_cannot_be_upgraded_by_an_epoch_hint() {
        let write=json!([{"type":"createAtom","atom":"1","kind":{"type":"text"},"payload":"6869"}]);
        assert!(reject_fresh_legacy(&write).is_err());
        let move_line=json!([{"type":"editElement","element":"1","revision":"2",
            "op":{"type":"move","index":"0","child":"4"}}]);
        reject_fresh_legacy(&move_line).unwrap();
    }

    fn custody_workspace()->std::path::PathBuf {
        let root=std::env::temp_dir().join(format!("mini-protected-custody-{}",super::super::random_nonce().unwrap()));
        super::super::make_private_dir(&root).unwrap();
        ensure_custody(&root).unwrap();
        root
    }
    #[test]
    fn custody_reopen_preserves_historical_document_key() {
        let root=custody_workspace();
        let (v,c)=source(7,9);let old=Audience::from_checked(&v,&c,"72").unwrap();
        let mut retained=custody(&root).unwrap();
        retained.retain(&old.anchor,&[8;32]).unwrap();
        let sealed=old.seal_actions(&json!([{"type":"createAtom","atom":"10",
            "kind":{"type":"text"},"payload":crate::hex(b"retained history")}]),
            &[4;32],&mut retained,&SigningKey::from_bytes(&[7;32])).unwrap();
        let (v,c)=source(8,12);let current=Audience::from_checked(&v,&c,"72").unwrap();
        retained.retain(&current.anchor,&[9;32]).unwrap();
        retained.reconcile_anchor(&current.anchor).unwrap();
        drop(retained);
        ensure_custody(&root).unwrap();
        let reopened=custody(&root).unwrap();
        assert_eq!(&*reopened.historical_key(&old.anchor).unwrap(),&[8;32]);
        assert_eq!(&*reopened.historical_key(&current.anchor).unwrap(),&[9;32]);
        assert_eq!(open_atom("72","10",sealed["actions"][0]["payload"].as_str().unwrap(),&reopened).unwrap(),b"retained history");
        drop(reopened);std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn custody_missing_storage_key_refuses_without_replacement() {
        let root=custody_workspace();
        let (state,key)=custody_paths(&root);
        let journal=std::fs::read(&state).unwrap();
        let original_key=std::fs::read(&key).unwrap();
        let saved=key.with_extension("test-saved");
        std::fs::rename(&key,&saved).unwrap();
        let refused=ensure_custody(&root);
        assert!(refused.unwrap_err().contains("custody is incomplete"));
        assert!(!key.exists(),"missing storage key must not be replaced");
        assert_eq!(std::fs::read(&state).unwrap(),journal);
        assert_eq!(std::fs::read(&saved).unwrap(),original_key);
        std::fs::rename(&saved,&key).unwrap();
        ensure_custody(&root).unwrap();
        drop(custody(&root).unwrap());std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn custody_metadata_with_missing_journal_refuses_blank_reinitialization() {
        let root=custody_workspace();
        let (state,key)=custody_paths(&root);
        let metadata=root.join("protected-documents/custody.json");
        assert!(metadata.is_file());
        let original_key=std::fs::read(&key).unwrap();
        let journal=std::fs::read(&state).unwrap();
        let saved=state.with_extension("test-saved");
        std::fs::rename(&state,&saved).unwrap();
        let refused=ensure_custody(&root);
        assert!(refused.unwrap_err().contains("custody is incomplete"));
        assert!(!state.exists(),"retained custody metadata must prevent a blank journal");
        assert_eq!(std::fs::read(&key).unwrap(),original_key);
        assert_eq!(std::fs::read(&saved).unwrap(),journal);
        std::fs::rename(&saved,&state).unwrap();
        ensure_custody(&root).unwrap();
        drop(custody(&root).unwrap());std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn enrollment_stage_survives_before_home_and_refuses_replacement_identity() {
        let root=custody_workspace();
        let reference=json!({"target":"72","observeCapability":"8","controlCapability":"9"});
        let workspace=json!({"subject":"7"});
        let identity=enrollment_identity(&reference,&workspace,"paper").unwrap();
        let stage=json!({"type":"mini-protected-document-stage-v1","identity":identity,
            "catalog":"pd-catalog-123","transition":"5","operation":crate::hex(&[6;32]),
            "catalogNonce":"7","catalogQueryNonce":"8","device":{"generation":crate::hex(&[9;32])}});
        let path=stage_path(&root,"72").unwrap();
        let bytes=serde_json::to_vec_pretty(&stage).unwrap();
        // A crash before atomic publication leaves only an uninterpreted orphan.
        super::super::private_file(&root.join("protected-documents/.enrollment-interrupted"),b"{partial").unwrap();
        assert!(!path.exists());
        retain_json(&path,&stage).unwrap();
        assert!(!root.join("protected-documents/72").exists());
        // Reopen before home/catalog creation uses exactly the same device,
        // operation, transition and catalog name without a second allocation.
        let reopened=super::super::bounded_json(&path).unwrap();
        validate_stage(&reopened,&identity).unwrap();
        assert_eq!(reopened,stage);
        super::super::make_private_dir(&root.join("protected-documents/72")).unwrap();
        retain_json(&path,&reopened).unwrap();
        let mut replacement=stage.clone();replacement["catalog"]=json!("pd-catalog-other");
        assert!(retain_json(&path,&replacement).is_err());
        assert_eq!(std::fs::read(&path).unwrap(),bytes);
        let mut changed_identity=identity.clone();changed_identity["controlCapability"]=json!("10");
        assert!(validate_stage(&reopened,&changed_identity).is_err());
        assert!(stage_path(&root,"../72").is_err());
        std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn catalog_recovery_reuses_immutable_intent_and_exact_emitted_call() {
        let root=custody_workspace();
        super::super::make_private_dir(&root.join("attempts")).unwrap();
        let operation=crate::hex(&[6;32]);
        super::super::validate_name(&operation).unwrap();
        let intent=root.join("protected-documents/catalog-write-intent.json");
        let request=json!({"nonce":"777","payload":"exact retained catalog"});
        retain_json(&intent,&request).unwrap();
        let bytes=std::fs::read(&intent).unwrap();
        let (first,emitted)=retained_attempt(&root,&operation).unwrap();
        assert!(!emitted);
        super::super::make_private_dir(&first).unwrap();
        super::super::private_file(&first.join("config.json"),b"retained preparation").unwrap();
        // Crash during preparation cannot have emitted without call.bin.
        let (next,emitted)=retained_attempt(&root,&operation).unwrap();
        assert!(!emitted);assert_ne!(first,next);
        super::super::make_private_dir(&next).unwrap();
        super::super::private_file(&next.join("call.bin"),b"exact signed catalog call").unwrap();
        // Lost response after emission must select those exact call bytes,
        // regardless of whether an outcome file was ever written.
        assert_eq!(retained_attempt(&root,&operation).unwrap(),(next.clone(),true));
        super::super::private_file(&next.join("outcome.json"),br#"{"type":"confirmed"}"#).unwrap();
        assert_eq!(retained_attempt(&root,&operation).unwrap(),(next.clone(),true));
        assert_eq!(std::fs::read(next.join("call.bin")).unwrap(),b"exact signed catalog call");
        assert_eq!(std::fs::read(&intent).unwrap(),bytes);
        let mut replacement=request.clone();replacement["nonce"]=json!("778");
        assert!(retain_json(&intent,&replacement).is_err());
        assert_eq!(std::fs::read(&intent).unwrap(),bytes);
        std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn staged_epoch_recovers_missing_manifest_without_new_key_material() {
        let root=custody_workspace();
        let (state,key)=custody_paths(&root);
        let (v,c)=source(7,9);let audience=Audience::from_checked(&v,&c,"72").unwrap();
        let operation=[6;32];
        let prepared=crate::object_epoch_packages::PreparedEpoch {key:Zeroizing::new([8;32]),
            manifest:b"exact retained epoch manifest".to_vec(),commitment:[9;32]};
        let command=b"exact source phase command";
        let mut store=Store::open(&state,crate::read_secret(&key).unwrap().to_bytes()).unwrap();
        store.stage_epoch(&audience.anchor,&operation,&prepared,command).unwrap();
        drop(store);
        // The process died after journal fsync, before either outward artifact.
        let phase=root.join("protected-documents/phase");
        super::super::make_private_dir(&phase).unwrap();
        let reopened=custody(&root).unwrap();
        let (manifest,retained_command)=reopened.pending_epoch(&operation).unwrap();
        drop(reopened);
        retain_record(&phase.join("phase-intent.bin"),&retained_command).unwrap();
        retain_record(&phase.join("epoch-manifest.bin"),&manifest).unwrap();
        assert_eq!(std::fs::read(phase.join("phase-intent.bin")).unwrap(),command);
        assert_eq!(std::fs::read(phase.join("epoch-manifest.bin")).unwrap(),prepared.manifest);
        let mut reopened=custody(&root).unwrap();
        assert!(reopened.stage_epoch(&audience.anchor,&operation,&prepared,command).is_err());
        reopened.settle(&operation,true).unwrap();drop(reopened);
        let reopened=custody(&root).unwrap();
        assert_eq!(*reopened.historical_key(&audience.anchor).unwrap(),*prepared.key);
        drop(reopened);std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn shared_alias_joins_only_custody_hints_without_replacing_authority() {
        let root=std::env::temp_dir().join(format!("mini-protected-alias-{}",super::super::random_nonce().unwrap()));
        super::super::make_private_dir(&root).unwrap();
        super::super::make_private_dir(&root.join("refs")).unwrap();
        let put=|name:&str,target:&str,hint:Option<&str>| {
            let mut value=json!({"type":"minidregg-participant-reference-v1","name":name,"kind":"object",
                "target":target,"observeCapability":"8","operationCapability":"9","controlCapability":null});
            if let Some(catalog)=hint {value["protectedDocument"]=json!({"version":"1","catalog":catalog});}
            super::super::private_file(&root.join("refs").join(format!("{name}.json")),&serde_json::to_vec(&value).unwrap()).unwrap();
        };
        put("catalog","99",None);put("local-paper","72",Some("catalog"));
        let selected=json!({"type":"minidregg-participant-reference-v1","name":"commons/paper","kind":"object",
            "target":"72","observeCapability":"123","operationCapability":"124","sharedName":{"worldRoot":"555"}});
        let joined=reference_context(&root,selected.clone()).unwrap();
        assert_eq!(joined["protectedDocument"]["catalog"],"catalog");
        assert_eq!(joined["observeCapability"],"123");assert_eq!(joined["operationCapability"],"124");
        assert_eq!(joined["sharedName"],selected["sharedName"]);
        put("wrong-catalog","100",None);put("conflicting-paper","72",Some("wrong-catalog"));
        assert!(reference_context(&root,selected).is_err());
        std::fs::remove_dir_all(root).unwrap();
    }

}
