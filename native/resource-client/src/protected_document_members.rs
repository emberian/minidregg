//! Recoverable current-text membership changes. Every source/ciphertext mutation
//! goes through the existing signed workspace path; package publication follows
//! the final all-holder post gate. Historical keys are never exported here.
use super::*;
use super::super as ws;
use std::{path::{Path, PathBuf}, fs};

fn id(change: &str, step: &str) -> String {
    crate::hex(&Sha256::digest([b"MINI/DOCUMENT-MEMBERSHIP-STEP/v1".as_slice(), change.as_bytes(), b"/", step.as_bytes()].concat()))
}
fn read(path: &Path) -> Result<Value> { ws::bounded_json(path) }
fn rows(value: &Value) -> Result<Vec<Value>> {
    value.as_array().cloned().ok_or("retained member list is not an array".into())
}
fn increment(value: &str) -> Result<String> {
    nat32(value)?;
    let next=mini_sdk::decimal::successor(value)?;
    if nat32(&next).is_err() {return Err("document epoch exceeds supported natural range".into());}
    Ok(next)
}
fn replace_json(path:&Path,value:&Value)->Result<()> {
    crate::fsio::replace_private(path,&serde_json::to_vec_pretty(value).map_err(|e|e.to_string())?)
}
pub(super) fn active_home(home:&Path)->Result<PathBuf> {
    let pointer=home.join("current-epoch.json");
    if !pointer.exists(){return Ok(home.to_owned());}
    let selected=read(&pointer)?;
    let change=text(&selected,"change")?;ws::validate_name(change)?;
    Ok(home.join("membership").join(change))
}
fn roster_entries(members:&[Value])->Result<Vec<Value>> {
    members.iter().map(|m|Ok(json!({"subject":m["subject"],"capability":m["capability"],
        "deviceSource":m["deviceSource"],"deviceGeneration":decimal(&crate::decode_hex(text(m,"generation")?)?),
        "keyCommitment":m["keyCommitment"]}))).collect()
}
fn current_members(home:&Path)->Result<Vec<Value>> {
    let active=active_home(home)?;
    if active==home {rows(&read(&home.join("enrollment-request.json"))?["recipients"])}
    else {rows(&read(&active.join("members.json"))?)}
}
fn source(root:&Path,workspace:&Value,name:&str)->Result<(Value,Value,Value,PathBuf)> {
    let reference=ws::reference(root,name)?;
    let (view,_,signed)=ws::signed_view(root,workspace,&reference,"resource")?;
    Ok((reference,view,audience_source(workspace,&signed)?,signed))
}
fn home_of(root:&Path,reference:&Value)->Result<PathBuf>{Ok(root.join("protected-documents").join(text(reference,"target")?))}
fn check_identity(stage:&Value,workspace:&Value,reference:&Value,name:&str)->Result<()> {
    if stage["type"]!="mini-document-membership-v1" || stage["name"]!=name
        || stage["object"]!=reference["target"] || stage["owner"]!=workspace["subject"] {
        return Err("membership recovery names another document or participant".into());
    }
    Ok(())
}
fn validate_device(device:&Value)->Result<()> {
    for field in ["deviceGeneration","keyCommitment"] {nat32(text(device,field)?)?;}
    for field in ["generation","dhPublic"] {
        let bytes=crate::decode_hex(text(device,field)?)?;
        if bytes.len()!=32 {return Err(format!("device {field} must contain 32 bytes"));}
    }
    if decimal(&crate::decode_hex(text(device,"generation")?)?)!=device["deviceGeneration"] {
        return Err("device generation decimal and bytes disagree".into());
    }
    let public=crate::object_keys_hybrid::DevicePublic {
        kem:crate::decode_hex(text(device,"kemPublic")?)?,
        dh:crate::decode_hex(text(device,"dhPublic")?)?.try_into().map_err(|_|"invalid device DH key")?,
    };
    if decimal(&crate::object_keys_hybrid::key_commitment(&public)?)!=device["keyCommitment"] {
        return Err("device key commitment differs from the actual public keys".into());
    }
    // Validate KEM modulus and contributory DH before freezing or granting.
    let context=Context{object:[0;32],epoch:0,transition:[0;32],operation:[0;32],law:[0;32]};
    crate::object_keys_hybrid::wrap(&context,&[0;32],&public,&[0;32])?;
    Ok(())
}
pub(crate) fn change(root:&Path,workspace:&Value,name:&str,change:&str,subject:&str,
    device_path:Option<&Path>)->Result<()> {
    ws::validate_name(change)?;nat32(subject)?;
    if workspace["subject"]==subject {return Err("the retaining owner cannot remove or replace itself with this command".into());}
    let (reference,_,observed,signed)=source(root,workspace,name)?;
    let home=home_of(root,&reference)?;
    let _lock=crate::transport::service_lock(&home.join("membership.lock"))?;
    let changes=home.join("membership");if !changes.exists(){ws::make_private_dir(&changes)?;}
    let dir=changes.join(change);if !dir.exists(){ws::make_private_dir(&dir)?;}
    let stage_path=dir.join("change.json");
    if stage_path.exists(){
        let prior=read(&stage_path)?;
        if prior["subject"]!=subject || prior["action"]!=if device_path.is_some(){"share"}else{"revoke"}{
            return Err("membership change id already names a different action".into());
        }
        if let Some(path)=device_path {if prior["device"]!=read(path)?{return Err("membership id already names another device".into());}}
        return recover_locked(root,workspace,name,change);
    }
    text(&reference,"controlCapability")?;
    let catalog=text(&reference["protectedDocument"],"catalog")?;
    let publication=active_home(&home)?;
    if publication==home && !home.join("epoch-manifest.bin").exists() {
        return Err("complete protected enrollment before a membership change".into());
    }
    if publication!=home && !publication.join("published.json").exists() {
        if device_path.is_some() {
            return Err("recover the current epoch before sharing; revoke can remove an ineligible holder from an unpublished epoch".into());
        }
        // A resumed but unpublished epoch can lose a holder's authority. Resolve
        // emitted exact posts before using revoke to repair its current roster.
        let prior=read(&publication.join("change.json"))?;
        drain_posts(root,workspace,&publication,text(&prior,"namespace")?,"rekey")?;
        drain_posts(root,workspace,&publication,text(&prior,"namespace")?,"format")?;
        drain_posts(root,workspace,&publication,text(&prior,"namespace")?,"publish")?;
    }
    let previous=current_members(&home)?;
    if device_path.is_some() && previous.len()>=4096 {
        return Err("protected audience already has the maximum 4096 device entries".into());
    }
    let actual=super::observe(root,workspace,&reference,&signed)?;
    let retained=roster_entries(&previous)?;
    if json!(retained)!=actual.roster["entries"] {return Err("local member custody is not the current admitted roster; synchronize before freezing".into());}
    let found=previous.iter().any(|row| row["subject"]==subject);
    if device_path.is_some()==found {return Err(if found{"member already included; revoke before replacing its device"}else{"member is absent from the retained audience"}.into());}
    if observed["active"]!=true {return Err("document has an unfinished audience phase; recover its named membership change".into());}
    let device=device_path.map(read).transpose()?.unwrap_or(Value::Null);
    if device_path.is_some(){validate_device(&device)?;}
    let stage=json!({"type":"mini-document-membership-v1","change":change,"name":name,
        "object":reference["target"],"owner":workspace["subject"],"subject":subject,
        "namespace":id(&format!("{}:{}:{}",text(&observed["sourceRecord"],"domain")?,text(&reference,"target")?,text(workspace,"subject")?),change),
        "action":if device_path.is_some(){"share"}else{"revoke"},"device":device,"catalog":catalog,
        "before":observed["audienceState"],"membersBefore":previous,"transition":ws::random_nonce()?,
        "predecessor":if publication==home{Value::Null}else{json!(text(&read(&publication.join("change.json"))?,"change")?)},
        "history":"current-text-only"});
    retain_json(&stage_path,&stage)?;
    recover_locked(root,workspace,name,change)
}

/// Retain each generation before preparing it. An emitted exact call is always
/// resolved first. Only an unequivocal non-admission permits another generation.
pub(super) fn action(root:&Path,workspace:&Value,dir:&Path,change:&str,label:&str,request:Value)->Result<Value> {
    let done=dir.join(format!("{label}-accepted.json"));
    if done.exists(){return read(&done);}
    for generation in 0..1024 {
        let proposal=id(change,&format!("{label}-{generation}"));
        let attempt=root.join("attempts").join(&proposal);
        let retained=dir.join(format!("{label}-{generation}.json"));
        let proposal_dir=root.join("proposals").join(&proposal);
        if retained.exists() && ((attempt.exists() && ws::attempt_definitely_unadmitted(&attempt)?)
            || (proposal_dir.exists() && !proposal_dir.join("intent.json").exists() && !attempt.join("call.bin").exists())) {continue;}
        if !retained.exists(){retain_json(&retained,&request)?;}
        if attempt.join("call.bin").exists(){crate::retry(&attempt,"submit",true)?;} else {
            let intent=root.join("proposals").join(&proposal).join("intent.json");
            if !intent.exists(){ws::propose(root,workspace,&retained,&proposal,None)?;}
            ws::submit_intent(root,workspace,&intent,"intent",false,Some(&attempt))?;
        }
        let confirmation=ws::accepted_outcome(&attempt)?.ok_or("membership step lacks exact accepted receipt")?;
        let result=json!({"proposal":proposal,"attempt":attempt,"receipt":confirmation});
        retain_json(&done,&result)?;
        return Ok(result);
    }
    Err("membership step exhausted retained attempts".into())
}
fn delegate(root:&Path,workspace:&Value,dir:&Path,stage:&Value,label:&str,name:&str,edit:bool)->Result<Value> {
    let saved=dir.join(format!("{label}-reference.json"));if saved.exists(){return read(&saved);}
    let mut reference=ws::reference(root,name)?;
    reference["observeCapability"]=reference["operationCapability"].clone();
    let (cap,_,_)=ws::signed_view(root,workspace,&reference,"capability")?;
    let maximum=text(&cap["head"],"maxCost")?;
    let step=action(root,workspace,dir,text(stage,"namespace")?,label,json!({
        "type":"minidregg-workspace-proposal-v1","action":"delegate","name":name,
        "recipient":stage["subject"],"verbs":if edit{json!(["observe","mutate"])}else{json!(["observe"])},"maxCost":maximum}))?;
    let proposal=text(&step,"proposal")?;
    ws::publish_delegation(root,proposal,Path::new(text(&step,"attempt")?))?;
    let mut hint=read(&root.join("proposals").join(proposal).join("recipient-reference.json"))?;
    // This admission conveys the current protected epoch, not legacy room keys.
    hint.as_object_mut().ok_or("invalid delegated hint")?.remove("sealedRoom");
    retain_json(&saved,&hint)?;Ok(hint)
}

/// Reconcile every retained generation, then grant this invocation a bounded
/// fresh budget. A busy authority history never permanently exhausts an epoch.
fn phase_generations(dir:&Path,phase:&str)->Result<Vec<u64>> {
    let mut existing=Vec::new();
    for entry in fs::read_dir(dir).map_err(|e|e.to_string())? {
        let entry=entry.map_err(|e|e.to_string())?;
        let name=entry.file_name();let Some(name)=name.to_str() else{continue};
        if let Some(number)=name.strip_prefix(&format!("{phase}-")).and_then(|s|s.parse::<u64>().ok()) {
            existing.push(number);
        }
    }
    existing.sort_unstable();existing.dedup();
    let next=match existing.last(){Some(n)=>n.checked_add(1).ok_or("phase generation counter exhausted")?,None=>0};
    for offset in 0..128 {existing.push(next.checked_add(offset).ok_or("phase generation counter exhausted")?);}
    Ok(existing)
}

fn phase(root:&Path,workspace:&Value,name:&str,dir:&Path,stage:&Value,phase:&str,
    mut request:Value)->Result<Value> {
    let done=dir.join(format!("{phase}-accepted.json"));if done.exists(){return read(&done);}
    let expected_before=if phase=="freeze"{stage["before"].clone()}else{read(&dir.join("freeze-accepted.json"))?["audience"].clone()};
    let (state,key)=custody_paths(root);
    for generation in phase_generations(dir,phase)? {
        let label=format!("{phase}-{generation}");let wrapper=dir.join(&label);let directory=wrapper.join("epoch");
        let operation=id(text(stage,"namespace")?,&label);
        let op=crate::decode_hex(&operation)?.try_into().map_err(|_|"invalid phase operation")?;
        let mut store=custody(root)?;
        let known=store.operation_known(&op)?;
        // A rejected earlier generation must not obstruct a later accepted one
        // whose outward acceptance marker was interrupted.
        if known && store.operation_settlement(&op)?==Some(false){continue;}
        let attempt=if known {store.pending_attempt(&op)?.unwrap_or_else(||directory.join("submission"))}
            else {directory.join("submission")};
        if !known && attempt.exists(){return Err("phase submission exists without durable custody; restore the complete backup".into());}
        let (_,_,current,signed)=source(root,workspace,name)?;
        if known && attempt.join("call.bin").is_file() && ws::attempt_definitely_unadmitted(&attempt)? {
            if current["audienceState"]!=expected_before {
                return Err("refused phase no longer has its exact predecessor audience; restore or inspect the retained transition".into());
            }
            store.settle(&op,false)?;continue;
        }
        if known && store.operation_settlement(&op)?.is_none() && !attempt.join("call.bin").exists() {
            let (_,_,intent)=store.phase_artifacts(&op)?;
            let intent:Value=serde_json::from_slice(&intent.ok_or("staged phase lacks its exact intent JSON")?).map_err(|e|e.to_string())?;
            let expected=text(&intent["purpose"]["draft"]["declaration"],"expectedPreRoot")?;
            let actual=text(&current,"currentAuthorityRoot")?;
            if expected!=actual {
                if current["audienceState"]!=expected_before {
                    return Err("unemitted phase has been superseded by another audience transition".into());
                }
                // The retained command can no longer pass its authority CAS.
                // submit persists call.bin before emitting, and this is the
                // custody-pinned attempt: no unknown call is abandoned here.
                let retirement=wrapper.join(format!("retirement-{}",ws::random_nonce()?));
                ws::make_private_dir(&retirement)?;
                retain_json(&retirement.join("source.json"),&current)?;
                retain_record(&retirement.join("signed.bin"),&fs::read(&signed).map_err(|e|e.to_string())?)?;
                retain_json(&retirement.join("reason.json"),&json!({"reason":"unemitted-authority-cas-moved", "expected":expected,"actual":actual}))?;
                store.settle(&op,false)?;continue;
            }
        }
        // An ordinary no-call interruption keeps the same command and key.
        drop(store);
        if directory.exists(){
            let known=crate::object_epoch_cli::restore_phase(&directory,&state,&key,&operation)?;
            if !known {
                if current["audienceState"]!=expected_before{return Err("audience moved before phase material was retained".into());}
                let request_path=dir.join(format!("{label}-request.json"));
                let original=read(&wrapper.join("source.json"))?;
                crate::object_epoch_cli::run(&original,&request_path,&ws::workspace_host(workspace)?,
                    &ws::member_path(workspace,"config")?,&ws::member_path(workspace,"key")?,&state,&key,&directory)?;
            }
            let intent=read(&directory.join("phase-intent.json"))?;
            let expected=&intent["purpose"]["draft"]["declaration"]["source"]["audience"];
            if current["audienceState"]!=expected_before && current["audienceState"]!=*expected {
                return Err("another audience transition superseded this retained membership phase".into());
            }
            let settlement=custody(root)?.operation_settlement(&op)?;
            match settlement {
                None=>crate::object_epoch_cli::retry(&directory,&state,&key,&operation,Some(&ws::member_path(workspace,"key")?))?,
                Some(true)=>if current["audienceState"]!=*expected && known {
                    return Err("settled phase does not match the current audience".into());
                },
                Some(false)=>return Err("phase was rejected while this recovery was running".into()),
            }
        }else{
            if current["audienceState"]!=expected_before{return Err("audience differs from retained membership phase".into());}
            if !wrapper.exists(){ws::make_private_dir(&wrapper)?;}
            let source_path=wrapper.join("source.json");
            if source_path.exists() && read(&source_path)?["worldRoot"]!=current["worldRoot"] {
                // No phase directory means no staged or emitted operation. Keep
                // the interrupted wrapper and retain a fresh generation.
                continue;
            }
            if !source_path.exists(){retain_json(&source_path,&current)?;}
            let observation=wrapper.join("signed-observation.bin");
            if !observation.exists(){retain_record(&observation,&fs::read(&signed).map_err(|e|e.to_string())?)?;}
            request["operation"]=json!(operation);request["phase"]=json!(phase);
            let request_path=dir.join(format!("{label}-request.json"));retain_json(&request_path,&request)?;
            crate::object_epoch_cli::run(&current,&request_path,&ws::workspace_host(workspace)?,
                &ws::member_path(workspace,"config")?,&ws::member_path(workspace,"key")?,&state,&key,&directory)?;
        }
        let expected=read(&directory.join("phase-intent.json"))?["purpose"]["draft"]["declaration"]["source"]["audience"].clone();
        let (_,_,current,_)=source(root,workspace,name)?;
        if current["audienceState"]!=expected{return Err("source does not confirm retained phase".into());}
        let result=json!({"audience":expected,"operation":operation,"directory":format!("{label}/epoch")});
        retain_json(&done,&result)?;return Ok(result);
    }
    Err("membership phase exhausted retained generations".into())
}

pub(crate) fn recover(root:&Path,workspace:&Value,name:&str,change:&str)->Result<()> {
    let home=home_of(root,&ws::reference(root,name)?)?;
    let _lock=crate::transport::service_lock(&home.join("membership.lock"))?;
    recover_locked(root,workspace,name,change)
}
fn recover_locked(root:&Path,workspace:&Value,name:&str,change:&str)->Result<()> {
    ws::validate_name(change)?;
    let reference=ws::reference(root,name)?;let home=home_of(root,&reference)?;
    let dir=home.join("membership").join(change);let stage=read(&dir.join("change.json"))?;
    check_identity(&stage,workspace,&reference,name)?;
    if dir.join("published.json").exists(){println!("{name}: membership change {change} is complete");return Ok(());}
    if dir.join("next-membership.json").exists() {
        return Err(format!("this epoch has a successor; recover membership {}",text(&read(&dir.join("next-membership.json"))?,"change")?));
    }
    let predecessor=match stage["predecessor"].as_str() {
        Some(previous)=>{ws::validate_name(previous)?;home.join("membership").join(previous)},
        None=>home.clone(),
    };
    let selected=active_home(&home)?;
    if selected!=predecessor && selected!=dir {
        return Err("another membership epoch superseded this recovery; current custody remains selected".into());
    }
    let claim=predecessor.join("next-membership.json");
    if claim.exists() && read(&claim)?["change"]!=change {
        return Err(format!("another membership change owns this epoch; recover {}",text(&read(&claim)?,"change")?));
    }
    let namespace=text(&stage,"namespace")?;
    let catalog=text(&stage,"catalog")?;
    let catalog_ref=ws::reference(root,catalog)?;
    let grants=json!([{"kind":"object","target":reference["target"],"capability":reference["observeCapability"]}]);
    let control=text(&reference,"controlCapability")?;
    let members_path=dir.join("members.json");
    let members=if members_path.exists(){rows(&read(&members_path)?)?}else{
        let mut members=rows(&stage["membersBefore"])?;
        if stage["action"]=="share" {
            let doc=delegate(root,workspace,&dir,&stage,"document-grant",name,true)?;
            let catalog_hint=delegate(root,workspace,&dir,&stage,"catalog-grant",catalog,false)?;
            let device=&stage["device"];
            members.push(json!({"subject":stage["subject"],"capability":doc["capability"],
                "catalogCapability":catalog_hint["capability"],"deviceSource":catalog_ref["target"],
                "generation":device["generation"],"keyCommitment":device["keyCommitment"],
                "kemPublic":device["kemPublic"],"dhPublic":device["dhPublic"]}));
        }else{
            // Revoke every currently standing grant governed by these two
            // local resources, including grants from interrupted invitations.
            // Ambient room grants govern other resources and are not removed
            // by a document-only membership change.
            for (resource,role,target) in [(name,"document",text(&reference,"target")?),
                (catalog,"catalog",text(&catalog_ref,"target")?)] {
                let standing=ws::standing_grants(root,workspace,resource,text(&stage,"subject")?)?;
                for (cap,_) in standing.into_iter().filter(|(_,policy)|policy==target) {
                    action(root,workspace,&dir,namespace,&format!("revoke-{role}-{cap}"),json!({
                        "type":"minidregg-workspace-proposal-v1","action":"revoke","name":resource,
                        "recipient":stage["subject"],"capability":cap}))?;
                }
            }
            members.retain(|m|m["subject"]!=stage["subject"]);
        }
        retain_json(&members_path,&json!(members))?;members
    };
    // Finish fallible grant construction before freezing. A new observer has
    // ciphertext but no epoch package; no historical key is disclosed here.
    // Failed preflight leaves the current editor usable and no epoch claim.
    retain_json(&claim,&json!({"change":change}))?;
    phase(root,workspace,name,&dir,&stage,"freeze",json!({"control":control,"transition":stage["transition"],"grants":grants}))?;
    let frozen=read(&dir.join("freeze-accepted.json"))?;
    let epoch=increment(text(&frozen["audience"],"epoch")?)?;
    let entries=roster_entries(&members)?;
    let roster=json!({"object":reference["target"],"epoch":epoch,"transition":stage["transition"],"entries":entries});
    let roster_json=dir.join("roster.json");retain_json(&roster_json,&roster)?;
    let host=ws::workspace_host(workspace)?;let config=ws::member_path(workspace,"config")?;
    let roster_bin=dir.join("roster.bin");retain_authored(&host,&config,"object-audience-roster",&roster_json,&roster_bin)?;
    let catalog_bin=dir.join("catalog.bin");retain_authored(&host,&config,"object-device-catalog",&roster_json,&catalog_bin)?;
    if !dir.join("catalog-edit-accepted.json").exists(){
        let (view,_,_)=ws::signed_view(root,workspace,&catalog_ref,"resource")?;
        let atom=ws::entries(&view)?.into_iter().find(|e|e["type"]=="atom"&&e["id"]=="0").ok_or("catalog atom zero missing")?;
        action(root,workspace,&dir,namespace,"catalog-edit",json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
            "targets":[{"name":catalog,"payload":{"type":"content","actions":[{"type":"editAtom","atom":"0",
                "before":ws::atom_record(&atom)?,"kind":{"type":"text"},"payload":crate::hex(&fs::read(&catalog_bin).map_err(|e|e.to_string())?),"tombstone":false}]}}]}))?;
    }
    let catalog_intent=dir.join("catalog-intent.json");
    if !catalog_intent.exists(){retain_json(&catalog_intent,&json!({"subject":workspace["subject"],"nonce":ws::random_nonce()?,
        "purpose":{"type":"query","kind":"object","target":catalog_ref["target"],"view":"resource"},
        "grants":[{"kind":"object","target":catalog_ref["target"],"capability":catalog_ref["observeCapability"]}]}))?;}
    let public=device(root)?;
    let resumed=phase(root,workspace,name,&dir,&stage,"resume",json!({"control":control,"audience":"0","devices":"0",
        "history":frozen["audience"]["history"],"dealerGeneration":public["generation"],"grants":grants,
        "recipients":members,"rosterBytes":crate::hex(&fs::read(&roster_bin).map_err(|e|e.to_string())?),"catalogIntent":catalog_intent}))?;
    retain_json(&dir.join("epoch.json"),&json!({"operation":resumed["operation"],"epoch":epoch,"audience":resumed["audience"]}))?;
    let relative=Path::new(text(&resumed,"directory")?);
    if relative.is_absolute() || relative.components().any(|c|!matches!(c,std::path::Component::Normal(_))) {
        return Err("retained phase directory escapes custody".into());
    }
    let phase_dir=dir.join(relative);
    retain_record(&dir.join("epoch-manifest.bin"),&fs::read(phase_dir.join("epoch-manifest.bin")).map_err(|e|e.to_string())?)?;
    replace_json(&home.join("current-epoch.json"),&json!({"change":change}))?;
    publish_current(root,workspace,name,&dir,&stage,&resumed)?;
    println!("{name}: {} complete for {}; current text uses the new epoch. Historical keys remain with their previous holders.",text(&stage,"action")?,text(&stage,"subject")?);
    Ok(())
}

/// Resolve every emitted exact post before scanning or superseding its epoch.
/// Unemitted drafts and final refusals remain retained but have no admission.
pub(super) fn drain_posts(root:&Path,workspace:&Value,dir:&Path,namespace:&str,prefix:&str)->Result<()> {
    for (label,generations) in post_generations(dir,prefix)? {
        if dir.join(format!("{label}-accepted.json")).exists(){continue;}
        for generation in generations {
            let proposal=id(namespace,&format!("{label}-{generation}"));
            let attempt=root.join("attempts").join(&proposal);
            if !attempt.join("call.bin").is_file() || ws::attempt_definitely_unadmitted(&attempt)? {continue;}
            if ws::accepted_outcome(&attempt)?.is_none(){crate::retry(&attempt,"submit",true)?;}
            let receipt=ws::accepted_outcome(&attempt)?.ok_or("retained membership post has an unresolved exact call")?;
            retain_json(&dir.join(format!("{label}-accepted.json")),&json!({"proposal":proposal,"attempt":attempt,"receipt":receipt}))?;
        }
    }
    let _=workspace;
    Ok(())
}
fn post_generations(dir:&Path,prefix:&str)->Result<std::collections::BTreeMap<String,Vec<u64>>> {
    let mut result=std::collections::BTreeMap::<String,Vec<u64>>::new();
    for file in fs::read_dir(dir).map_err(|e|e.to_string())? {
        let file=file.map_err(|e|e.to_string())?;let name=file.file_name();let Some(name)=name.to_str() else{continue};
        let Some(stem)=name.strip_suffix(".json") else{continue};
        let Some((label,generation))=stem.rsplit_once('-') else{continue};
        if !label.strip_prefix(&format!("{prefix}-")).is_some_and(|number|number.parse::<u64>().is_ok()){continue;}
        let Ok(generation)=generation.parse::<u64>() else{continue};
        result.entry(label.to_owned()).or_default().push(generation);
    }
    for generations in result.values_mut(){generations.sort_unstable();}
    Ok(result)
}
pub(super) fn next_post(dir:&Path,prefix:&str)->Result<u64> {
    let highest=post_generations(dir,prefix)?.keys().filter_map(|label|label.rsplit_once('-')?.1.parse::<u64>().ok()).max();
    highest.map_or(Ok(0),|n|n.checked_add(1).ok_or("membership post counter exhausted".into()))
}
pub(super) fn post_unadmitted(root:&Path,dir:&Path,namespace:&str,label:&str)->Result<bool> {
    let prefix=label.split('-').next().ok_or("invalid post label")?;
    for generation in post_generations(dir,prefix)?.get(label).into_iter().flatten() {
        let attempt=root.join("attempts").join(id(namespace,&format!("{label}-{generation}")));
        if attempt.join("call.bin").is_file() && !ws::attempt_definitely_unadmitted(&attempt)? {return Ok(false);}
    }
    Ok(true)
}
pub(super) fn publish_current(root:&Path,workspace:&Value,name:&str,dir:&Path,stage:&Value,resumed:&Value)->Result<()> {
    let namespace=text(stage,"namespace")?;
    drain_posts(root,workspace,dir,namespace,"rekey")?;
    drain_posts(root,workspace,dir,namespace,"publish")?;
    for _ in 0..128 {
        let checked_root=rekey_current(root,workspace,name,dir,stage)?;
        let label=format!("publish-{}",next_post(dir,"publish")?);
        let receipt=match action(root,workspace,dir,namespace,&label,json!({
            "type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{
            "name":name,"expectedTargetRoot":checked_root,"payload":{"type":"content","actions":[{
            "type":"createContainer","element":decimal(&crate::decode_hex(&id(namespace,&label))?) }]}}]})) {
            Ok(receipt)=>receipt,
            Err(error)=>{
                if !post_unadmitted(root,dir,namespace,&label)? {return Err(error);}
                let (_,view,_,_)=source(root,workspace,name)?;
                if view["cell"]["root"]!=checked_root {continue;}
                return Err(error);
            }
        };
        retain_json(&dir.join("published.json"),&json!({"type":"mini-document-membership-published-v1",
            "currentTextOnly":true,"audience":resumed["audience"],"receipt":receipt}))?;
        return Ok(());
    }
    Err("document kept changing during publication; recover this membership change to continue".into())
}

pub(super) fn atom_epoch(payload:&str)->Result<u64>{
    let bytes=crate::decode_hex(payload)?;
    let offset=FRAME.len()+64+MESSAGE_FRAME.len()+32;
    let epoch=bytes.get(offset..offset+8).ok_or("protected atom has no epoch")?;
    Ok(u64::from_be_bytes(epoch.try_into().map_err(|_|"invalid epoch bytes")?))
}
fn visible_atoms(document:&Value)->Result<std::collections::BTreeSet<String>> {
    ws::live_lines(document)?.into_iter().filter(|line|line["kind"]=="atom")
        .map(|line|text(line,"atom").map(str::to_owned)).collect()
}
fn rekey_current(root:&Path,workspace:&Value,name:&str,dir:&Path,stage:&Value)->Result<String> {
    let epoch=text(&read(&dir.join("epoch.json"))?,"epoch")?.parse::<u64>().map_err(|_|"epoch exceeds u64")?;
    rewriting::current(root,workspace,name,dir,text(stage,"namespace")?,epoch)
}

pub(crate) fn export_share(root:&Path,workspace:&Value,name:&str,change:&str,output:&Path)->Result<()> {
    ws::validate_name(change)?;
    let reference=ws::reference(root,name)?;let home=home_of(root,&reference)?;
    let dir=home.join("membership").join(change);let stage=read(&dir.join("change.json"))?;
    check_identity(&stage,workspace,&reference,name)?;
    if stage["action"]!="share" || !dir.join("published.json").exists(){return Err("sharing has not completed its current-text admission".into());}
    if active_home(&home)?!=dir{return Err("another membership epoch superseded this invitation; export its current recipient package instead".into());}
    let epoch_output=dir.join(format!(".export-{}.json",ws::random_nonce()?));
    super::export_epoch(root,workspace,name,&epoch_output)?;
    let bundle=json!({"type":"mini-protected-document-invitation-v1","currentTextOnly":true,
        "recipient":stage["subject"],"document":read(&dir.join("document-grant-reference.json"))?,
        "catalog":read(&dir.join("catalog-grant-reference.json"))?,"epoch":read(&epoch_output)?});
    retain_json(output,&bundle)
}
pub(crate) fn accept(root:&Path,workspace:&Value,name:&str,catalog:&str,input:&Path)->Result<()> {
    let bundle=read(input)?;
    if bundle["type"]!="mini-protected-document-invitation-v1" || bundle["currentTextOnly"]!=true
        || bundle["recipient"]!=workspace["subject"] {return Err("invitation is not addressed to this participant".into());}
    for (label,hint) in [(name,&bundle["document"]),(catalog,&bundle["catalog"])] {
        ws::validate_ref_name(label)?;
        if hint["recipient"]!=workspace["subject"] || hint["kind"]!="object"{return Err("invitation reference subject/kind mismatch".into());}
        match ws::local_reference(root,label){
            Ok(existing)=>if existing["target"]!=hint["target"] || existing["observeCapability"]!=hint["capability"] {
                return Err(format!("{label} already names another reference; choose a new local name"));
            },
            Err(_)=>{
                let path=root.join("sources").join(format!("invitation-{}.json",ws::random_nonce()?));
                retain_json(&path,hint)?;ws::import_delegated(root,workspace,label,&path)?;
            }
        }
    }
    let epoch=root.join("sources").join(format!("epoch-bundle-{}.json",ws::random_nonce()?));
    retain_json(&epoch,&bundle["epoch"])?;super::import_epoch(root,workspace,name,catalog,&epoch)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn caller_root_pin_cannot_be_refreshed_away(){
        assert!(ws::check_requested_root(&json!({"expectedTargetRoot":"17"}),"17").is_ok());
        assert!(ws::check_requested_root(&json!({"expectedTargetRoot":"17"}),"18").is_err());
        assert!(ws::check_requested_root(&json!({"expectedTargetRoot":17}),"17").is_err());
        assert!(ws::check_requested_root(&json!({}),"18").is_ok());
    }
    #[test] fn recovery_counter_advances_past_completed_and_interrupted_batches(){
        let dir=std::env::temp_dir().join(format!("mini-members-counter-{}",ws::random_nonce().unwrap()));
        ws::make_private_dir(&dir).unwrap();
        retain_json(&dir.join("rekey-4097-0.json"),&json!({"retained":"interrupted"})).unwrap();
        retain_json(&dir.join("rekey-8-0.json"),&json!({"retained":"complete"})).unwrap();
        retain_json(&dir.join("rekey-8-accepted.json"),&json!({})).unwrap();
        retain_json(&dir.join("publish-12-0.json"),&json!({})).unwrap();
        assert_eq!(next_post(&dir,"rekey").unwrap(),4098);
        assert_eq!(next_post(&dir,"publish").unwrap(),13);
        assert_eq!(post_generations(&dir,"rekey").unwrap().len(),2);
        ws::make_private_dir(&dir.join("resume-0")).unwrap();
        ws::make_private_dir(&dir.join("resume-128")).unwrap();
        let phases=phase_generations(&dir,"resume").unwrap();
        assert_eq!(&phases[..3],&[0,128,129]);
        assert_eq!(phases.last(),Some(&256));
        fs::remove_dir_all(dir).unwrap();
    }
    #[test] fn durable_step_ids_fit_and_separate_operation_phases(){
        let share=id("work-1","document-grant-0");let resume=id("work-1","resume-0");
        assert_eq!(share.len(),64);ws::validate_name(&share).unwrap();
        assert_ne!(share,resume);assert_ne!(share,id("work-2","document-grant-0"));
        assert_ne!(id(&id("domain:object1:owner","add-member"),"freeze-0"),
            id(&id("domain:object2:owner","add-member"),"freeze-0"));
    }
    #[test] fn atom_epoch_is_big_endian_and_requires_complete_header(){
        let context=Context{object:[2;32],epoch:257,transition:[3;32],operation:[4;32],law:[5;32]};
        let bytes=[FRAME,&[6;32],&[7;32],&context.bytes()].concat();
        assert_eq!(atom_epoch(&crate::hex(&bytes)).unwrap(),257);
        assert!(atom_epoch(&crate::hex(FRAME)).is_err());
    }
    #[test] fn publication_directory_cannot_escape_custody(){
        let home=std::env::temp_dir().join(format!("mini-members-publication-{}",ws::random_nonce().unwrap()));
        ws::make_private_dir(&home).unwrap();
        retain_json(&home.join("current-epoch.json"),&json!({"change":"../../outside"})).unwrap();
        assert!(active_home(&home).is_err());fs::remove_dir_all(home).unwrap();
    }
    #[test] fn device_preflight_rejects_a_forged_commitment_before_any_phase(){
        let (_,public)=crate::object_keys_hybrid::generate().unwrap();
        let generation=[9u8;32];
        let device=json!({"generation":crate::hex(&generation),"deviceGeneration":decimal(&generation),
            "kemPublic":crate::hex(&public.kem),"dhPublic":crate::hex(&public.dh),
            "keyCommitment":decimal(&crate::object_keys_hybrid::key_commitment(&public).unwrap())});
        validate_device(&device).unwrap();
        let mut wrong=device.clone();wrong["keyCommitment"]=json!("1");
        assert!(validate_device(&wrong).unwrap_err().contains("commitment"));
        let mut wrong=device;wrong["dhPublic"]=json!(crate::hex(&[0;32]));
        let zero=crate::object_keys_hybrid::DevicePublic{kem:public.kem,dh:[0;32]};
        wrong["keyCommitment"]=json!(decimal(&crate::object_keys_hybrid::key_commitment(&zero).unwrap()));
        assert!(validate_device(&wrong).unwrap_err().contains("noncontributory"));
    }

    #[test] fn sharing_selects_current_placed_text_not_struck_or_detached_history(){
        let document=json!({"order":[{"kind":"atom","atom":"1","struck":false},
            {"kind":"atom","atom":"2","struck":true},{"kind":"embed","element":"3"},
            {"kind":"section","element":"4"}]});
        assert_eq!(visible_atoms(&document).unwrap(),["1".to_owned()].into_iter().collect());
    }

}
