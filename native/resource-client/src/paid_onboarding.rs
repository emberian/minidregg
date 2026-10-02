//! Current-owner recovery for paid workspace custody. Payment/claim origins and
//! initial receipt provenance are immutable; only verified key custody changes.
use super::*;
use serde_json::json;
use sha2::Sha256;

const ACTIVE: &str = "paid-onboarding-recovery.json";
const TYPE: &str = "minidregg-paid-onboarding-recovery-v1";

fn selection(record:&Value)->Value {
    json!({"miniKeyFile":record["miniKeyFile"],"authorizingKey":record["authorizingKey"],
        "authorityEpoch":record["authorityEpoch"],"nextPublicFile":record["nextPublicFile"]})
}
fn selection_name(record:&Value)->Result<String> {
    let memo=record["memo"].as_str().ok_or("paid recovery memo missing")?;
    Ok(format!("onboarding-{}.json",hex(&Sha256::digest(memo.as_bytes()))))
}
fn stable_setup(setup:&Value)->Result<Value> {
    let mut value=setup.clone();
    let object=value.as_object_mut().ok_or("paid setup object required")?;
    for key in ["key","authorizingKey","authorityEpoch","nextPublicFile"] { object.remove(key); }
    Ok(value)
}
fn stable_origin(record:&Value,setup:&Value)->Value {
    json!({"identityKey":record["miniKey"],"subject":setup["subject"],
        "configSha256":setup["configSha256"],"hostSha256":setup["hostSha256"]})
}
fn optional(path:&Path)->Result<Value> {
    match fs::symlink_metadata(path) {
        Ok(_)=>workspace::bounded_json(path),
        Err(e) if e.kind()==std::io::ErrorKind::NotFound=>Ok(Value::Null),
        Err(e)=>Err(e.to_string()),
    }
}
fn publish(path:&Path,value:&Value)->Result<()> {
    workspace::replace_private_file(path,&serde_json::to_vec_pretty(value).map_err(|e|e.to_string())?)
}
fn changes(path:&str,before:Value,after:Value)->Value {
    json!({"name":path,"before":before,"after":after})
}

// An admitted transition is replayed using exact retained before/after values.
// No authority read or new signed operation occurs during this bookkeeping.
fn apply(directory:&Path,journal:&Value,mut step:impl FnMut(usize)->Result<()>)->Result<()> {
    if journal["type"]!=TYPE { return Err("unknown paid custody transition".into()); }
    let files=journal["files"].as_array().ok_or("paid transition files missing")?;
    if files.len()<2 || files.len()>3 { return Err("paid transition file count invalid".into()); }
    let selection=journal["selectionName"].as_str().ok_or("paid transition selection missing")?;
    if !selection.starts_with("onboarding-") || !selection.ends_with(".json")
        || selection.len()!=80 || !selection.as_bytes()[11..75].iter().all(|b|b.is_ascii_hexdigit() && !b.is_ascii_uppercase()) {
        return Err("paid transition selection name invalid".into());
    }
    let mut seen=std::collections::BTreeSet::new();
    for (index,file) in files.iter().enumerate() {
        let name=file["name"].as_str().ok_or("paid transition filename missing")?;
        if !matches!(name,"workspace/workspace.json"|"workspace-setup.json") && name!=selection {
            return Err("paid transition attempts unrelated file publication".into());
        }
        if !seen.insert(name) || !file["after"].is_object() { return Err("paid transition file shape invalid".into()); }
        let path=directory.join(name);
        let current=optional(&path)?;
        if current!=file["after"] {
            if current!=file["before"] { return Err("paid custody changed since admitted transition; retain evidence".into()); }
            publish(&path,&file["after"])?;
        }
        // Replay may discover a rename completed before its directory fsync.
        File::open(path.parent().ok_or("paid publication parent missing")?).map_err(|e|e.to_string())?
            .sync_all().map_err(|e|e.to_string())?;
        step(index)?;
    }
    Ok(())
}
fn replay(directory:&Path,origin:&Value)->Result<()> {
    let active=optional(&directory.join(ACTIVE))?;
    if active.is_null() { return Ok(()); }
    if active["type"]!=TYPE || !active["complete"].is_boolean() { return Err("paid transition pointer invalid".into()); }
    if active["complete"]==true { return Ok(()); }
    let name=active["journal"].as_str().ok_or("paid transition journal missing")?;
    if !name.starts_with("paid-custody-") || !name.ends_with(".json") || name.contains('/') || name.contains('\\') {
        return Err("paid transition journal name invalid".into());
    }
    let path=directory.join(name);
    if host_image_sha256(&path)?!=active["journalSha256"].as_str().ok_or("paid journal hash missing")? {
        return Err("paid transition journal changed".into());
    }
    let journal=workspace::bounded_json(&path)?;
    if journal["origin"]!=*origin { return Err("paid transition stable identity or deployment changed".into()); }
    apply(directory,&journal,|_|Ok(()))?;
    let mut completed=active;
    completed["complete"]=json!(true);
    publish(&directory.join(ACTIVE),&completed)
}

/// Finish admitted bookkeeping before any fresh owner selection. A later key
/// rotation may refuse a new operation but cannot trap the earlier publication.
pub(crate) fn resume(directory:&Path,identity:&Value,subject:&Value,
    host_sha:&str,config_sha:&str)->Result<()> {
    if !directory.join(ACTIVE).exists() { return Ok(()); }
    let _setup=transport::service_lock(&directory.join("workspace-setup.lock"))?;
    let root=directory.join("workspace");
    let _key_lock=if root.exists() { Some(transport::service_lock(&root.join("key-transition.lock"))?) } else { None };
    replay(directory,&json!({"identityKey":identity,"subject":subject,
        "hostSha256":host_sha,"configSha256":config_sha}))
}

/// Caller holds workspace-setup.lock. Fresh setup remains ordinary init; an
/// existing custody selection changes only after current possession/continuity.
pub(crate) fn reconcile(directory:&Path,record:&Value,setup:&Value,account:&Value,
    prepare:impl FnOnce(&Path)->Result<()>) -> Result<()> {
    let origin=stable_origin(record,setup);
    let root=directory.join("workspace");
    let _key_lock=if root.exists() { Some(transport::service_lock(&root.join("key-transition.lock"))?) } else { None };
    replay(directory,&origin)?;
    let pin=directory.join("workspace-setup.json");
    let before_setup=optional(&pin)?;
    let name=selection_name(record)?;
    let held=optional(&directory.join(&name))?;
    let wanted=selection(record);
    if before_setup.is_null() && root.exists() {
        return Err("workspace exists without retained paid setup; refusing adoption".into());
    }
    if !before_setup.is_null() && stable_setup(&before_setup)?!=stable_setup(setup)? {
        return Err("paid recovery changes deployment, identity, account or birth context".into());
    }
    let changing=(!before_setup.is_null() && before_setup!=*setup) || (!held.is_null() && held!=wanted);
    if !changing {
        if held.is_null() { publish(&directory.join(&name),&wanted)?; }
        return Ok(());
    }
    let key=PathBuf::from(record["miniKeyFile"].as_str().ok_or("paid current key missing")?);
    let next=record["nextPublicFile"].as_str().map(Path::new);
    let mut files=Vec::new();
    let evidence=if root.exists() {
        let old=workspace::load_for_key_transition(&root)?;
        for field in ["subject","config","host","socket"] {
            if old[field]!=before_setup[field] { return Err(format!("paid workspace {field} differs from retained setup")); }
        }
        if old["key"]!=before_setup["key"] { return Err("paid workspace key differs from retained setup".into()); }
        let (before,after,evidence)=workspace::paid_owner_transition(&root,&key,next,&record["authorityEpoch"],account)?;
        files.push(changes("workspace/workspace.json",before,after));
        evidence
    } else {
        // No published first trust exists. Admit possession in a retained fresh
        // staging workspace before changing the earlier setup/selection pins.
        let staged=directory.join(format!("custody-proof-{}",workspace::random_nonce()?));
        prepare(&staged)?;
        workspace::import(&staged,workspace::ImportInput {name:"account",kind:"account",
            target:account["target"].as_str().ok_or("paid account missing")?,
            observe:account["observeCapability"].as_str().ok_or("paid account capability missing")?,
            operation:None,control:None,provenance:None,room:None})?;
        json!({"stagedWorkspace":staged,"firstTrust":workspace::complete_fresh_onboarding(&staged)?})
    };
    files.push(changes("workspace-setup.json",before_setup,setup.clone()));
    files.push(changes(&name,held,wanted));
    let journal=json!({"type":TYPE,"origin":origin,"paymentMemo":record["memo"],
        "selectionName":name,"evidence":evidence,"files":files});
    let journal_name=format!("paid-custody-{}.json",workspace::random_nonce()?);
    let journal_path=directory.join(&journal_name);
    workspace::private_file(&journal_path,&serde_json::to_vec_pretty(&journal).map_err(|e|e.to_string())?)?;
    publish(&directory.join(ACTIVE),&json!({"type":TYPE,"journal":journal_name,
        "journalSha256":host_image_sha256(&journal_path)?,"complete":false}))?;
    replay(directory,&origin)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn only_custody_fields_may_change() {
        let old=json!({"key":"A","authorizingKey":"a","authorityEpoch":"1","nextPublicFile":"B.pub","subject":"7","account":"9"});
        let mut new=old.clone(); new["key"]=json!("C");new["authorityEpoch"]=json!("3");
        assert_eq!(stable_setup(&old).unwrap(),stable_setup(&new).unwrap());
        new["account"]=json!("10");
        assert_ne!(stable_setup(&old).unwrap(),stable_setup(&new).unwrap());
    }
    #[test]
    fn interrupted_publication_replays_exactly_and_refuses_unrelated_changes() {
        let directory=std::env::temp_dir().join(format!("paid-custody-{}",workspace::random_nonce().unwrap()));
        workspace::make_private_dir(&directory).unwrap();
        let name=format!("onboarding-{}.json","a".repeat(64));
        let old=json!({"key":"B"});let new=json!({"key":"C"});
        publish(&directory.join("workspace-setup.json"),&old).unwrap();
        publish(&directory.join(&name),&old).unwrap();
        let journal=json!({"type":TYPE,"selectionName":name,"files":[
            changes("workspace-setup.json",old.clone(),new.clone()),changes(&name,old.clone(),new.clone())]});
        assert!(apply(&directory,&journal,|_|Err("injected interruption".into())).is_err());
        assert_eq!(optional(&directory.join("workspace-setup.json")).unwrap(),new);
        assert_eq!(optional(&directory.join(&name)).unwrap(),old);
        apply(&directory,&journal,|_|Ok(())).unwrap();
        apply(&directory,&journal,|_|Ok(())).unwrap();
        publish(&directory.join(&name),&json!({"key":"unrelated"})).unwrap();
        assert!(apply(&directory,&journal,|_|Ok(())).is_err());
        fs::remove_dir_all(directory).unwrap();
    }
    #[test]
    fn admitted_recovery_resumes_before_later_authority_refusal_without_old_secret() {
        let directory=std::env::temp_dir().join(format!("paid-replay-{}",workspace::random_nonce().unwrap()));
        workspace::make_private_dir(&directory).unwrap();
        let name=format!("onboarding-{}.json","b".repeat(64));
        let origin=json!({"identityKey":"old-payment","subject":"7","hostSha256":"h","configSha256":"c"});
        let old=json!({"key":"B"});let accepted=json!({"key":"C","authorityEpoch":"3"});
        publish(&directory.join("workspace-setup.json"),&accepted).unwrap(); // interrupted after first publication
        publish(&directory.join(&name),&old).unwrap();
        let journal=json!({"type":TYPE,"origin":origin,"selectionName":name,"files":[
            changes("workspace-setup.json",old.clone(),accepted.clone()),changes(&name,old,accepted.clone())]});
        let journal_path=directory.join("paid-custody-123.json");
        publish(&journal_path,&journal).unwrap();
        publish(&directory.join(ACTIVE),&json!({"type":TYPE,"journal":"paid-custody-123.json",
            "journalSha256":host_image_sha256(&journal_path).unwrap(),"complete":false})).unwrap();
        // The same consumer boundary used before wait's owner checks needs no
        // C secret/source authority after C→D; only later fresh work refuses C.
        resume(&directory,&json!("old-payment"),&json!("7"),"h","c").unwrap();
        assert_eq!(optional(&directory.join(&name)).unwrap(),accepted);
        assert_eq!(optional(&directory.join(ACTIVE)).unwrap()["complete"],true);
        resume(&directory,&json!("old-payment"),&json!("7"),"h","c").unwrap();
        fs::remove_dir_all(directory).unwrap();
    }
}
