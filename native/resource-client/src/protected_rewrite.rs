//! One durable current-text rewrite for conversion and membership rotation.
//! Ciphertext and carried formatting have separate source receipts. Original
//! marks and links remain historical records with their authors. Annotation
//! ciphertext/authorship stays immutable while its fragment-key custody rotates.
use super::*;
use super::super as ws;
use std::{fs,path::Path,collections::BTreeSet};

fn id(namespace:&str,label:&str)->String {
    decimal(&Sha256::digest([b"MINI/PROTECTED-REWRITE/v1".as_slice(),namespace.as_bytes(),b"/",label.as_bytes()].concat()))
}
fn plaintext(entry:&Value)->Result<String> {
    if let Some(text)=entry["private"]["text"].as_str(){Ok(crate::hex(text.as_bytes()))}
    else if let Some(bytes)=entry["private"]["hex"].as_str(){Ok(bytes.to_owned())}
    else if entry["kind"]==json!({"type":"text"}){Ok(text(entry,"payload")?.to_owned())}
    else{Err("current-text protection requires openable text atoms; original data remains retained".into())}
}
fn visible(document:&Value)->Result<BTreeSet<String>> {
    ws::live_lines(document)?.into_iter().filter(|r|r["kind"]=="atom")
        .map(|r|text(r,"atom").map(str::to_owned)).collect()
}
fn atom<'a>(entries:&'a [Value],id:&str)->Result<&'a Value> {
    entries.iter().find(|r|r["type"]=="atom"&&r["id"]==id).ok_or("rewrite atom disappeared".into())
}
/// A current epoch header never substitutes for successfully authenticated
/// opening. Validate every live comment before selecting bounded maintenance.
pub(super) fn pending_annotations(raw:&[Value],opened:&[Value],epoch:u64,limit:usize)->Result<Vec<Value>> {
    let mut selected=Vec::new();
    for annotation in raw.iter().filter(|r|r["type"]=="annotation"&&r["tombstonedAt"].is_null()) {
        if annotation["body"]["type"]!="sealed" {
            return Err("live annotation has no immutable authored-fragment custody contract".into());
        }
        let display=opened.iter().find(|r|r["type"]=="annotation"&&r["id"]==annotation["id"])
            .ok_or("annotation disappeared from opened projection")?;
        if display["private"]["text"].as_str().is_none()&&display["private"]["hex"].as_str().is_none(){
            return Err("live annotation is locked; membership completion is withheld".into());
        }
        if super::annotations::epoch(&annotation["body"])?!=epoch&&selected.len()<limit {
            selected.push(annotation.clone());
        }
    }
    Ok(selected)
}
pub(super) fn validate_current(read:&ws::DocumentRead)->Result<()> {
    let visible=visible(&read.document)?;
    for id in visible {plaintext(atom(&read.entries,&id)?)?;}
    for annotation in read.entries.iter().filter(|r|r["type"]=="annotation"&&r["tombstonedAt"].is_null()) {
        if annotation["body"]["type"]!="sealed" {
            return Err("membership requires sealed authored annotations; original public annotation history is retained".into());
        }
        if !annotation["private"].is_object() {
            return Err("membership requires every live annotation key to be openable".into());
        }
    }
    Ok(())
}
fn planned_marks(entries:&[Value],atoms:&BTreeSet<String>)->Result<Vec<Value>> {
    entries.iter().filter(|r|r["type"]=="mark"&&r["fresh"]==true&&r["tombstonedAt"].is_null()
        && r["anchor"]["type"]=="atom"&&r["anchor"]["atom"].as_str().is_some_and(|a|atoms.contains(a)))
        .map(|r|{let mut retained=r.clone();if r["kind"]=="link"&&r["linkLive"]!=true{return Err("cannot carry a retired link mark".into());}
            retained.as_object_mut().ok_or("invalid mark")?.remove("fresh");Ok(retained)}).collect()
}
fn plans(dir:&Path)->Result<Vec<(u64,std::path::PathBuf)>> {
    let mut found=Vec::new();
    for file in fs::read_dir(dir).map_err(|e|e.to_string())? {
        let file=file.map_err(|e|e.to_string())?;let name=file.file_name();let Some(name)=name.to_str() else{continue};
        if let Some(n)=name.strip_prefix("rewrite-plan-").and_then(|s|s.strip_suffix(".json")).and_then(|s|s.parse::<u64>().ok()) {
            found.push((n,file.path()));
        }
    }
    found.sort_by_key(|r|r.0);Ok(found)
}
fn rekey_request(name:&str,plan:&Value)->Result<Value> {
    let mut edits=plan["atoms"].as_array().ok_or("rewrite plan lacks atoms")?.iter().map(|a|
        Ok(json!({"type":"editAtom","atom":a["atom"],"before":ws::atom_record(&a["rawBefore"])?,
            "kind":{"type":"text"},"payload":a["plaintext"],"tombstone":false})))
        .collect::<Result<Vec<Value>>>()?;
    for annotation in plan["annotations"].as_array().into_iter().flatten() {
        edits.push(json!({"type":"rewrapAnnotation","annotation":annotation["id"],
            "before":annotation["canonical"],"wrapping":annotation["body"]}));
    }
    Ok(json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{
        "name":name,"expectedTargetRoot":plan["root"],"payload":{"type":"content","actions":edits}}]}))
}
fn conflict(dir:&Path,plan:&Value,view:&Value,reason:&str)->Result<String> {
    let path=dir.join(format!("format-conflict-{}.json",ws::random_nonce()?));
    retain_json(&path,&json!({"reason":reason,"plan":plan,"currentSignedView":view}))?;
    Ok(format!("{reason}; original conversion and current evidence retained at {}; editor remains usable; no completion or package publication claimed",path.display()))
}
fn formatting_complete_at(dir:&Path,number:u64,path:&Path,root:&str)->Result<bool> {
    let checkpoint=dir.join(format!("format-plan-{number}-complete-{root}.json"));
    if !checkpoint.exists(){return Ok(false);}
    let proof=ws::bounded_json(&checkpoint)?;
    if proof["root"]!=root || proof["sourcePlan"]!=json!(path) || proof["formattingReceived"]!=true {
        return Err("formatting checkpoint does not match its exact source plan and root".into());
    }
    Ok(true)
}
fn all_formatting_at(dir:&Path,root:&str)->Result<bool> {
    for (number,path) in plans(dir)? {
        if dir.join(format!("rekey-{number}-accepted.json")).exists()
            && !formatting_complete_at(dir,number,&path,root)? {return Ok(false);}
    }
    Ok(true)
}
// Evidence can survive a crash before action() creates its first request.
// Reserve its label permanently; no emitted call exists at that boundary.
fn next_format(dir:&Path)->Result<u64> {
    let mut next=members::next_post(dir,"format")?;
    for entry in fs::read_dir(dir).map_err(|e|e.to_string())? {
        let entry=entry.map_err(|e|e.to_string())?;
        let name=entry.file_name();let Some(name)=name.to_str() else{continue};
        if let Some(n)=name.strip_prefix("format-").and_then(|s|s.strip_suffix("-source.json"))
            .and_then(|s|s.parse::<u64>().ok()) {
            next=next.max(n.checked_add(1).ok_or("format evidence counter exhausted")?);
        }
    }
    Ok(next)
}
/// Resolve old exact calls before scanning. Each accepted atom rewrite's mark
/// plan is repaired from fresh authenticated metadata; a new plan never replaces
/// an outstanding call or guesses whether a mark landed.
fn restore(root:&Path,workspace:&Value,name:&str,dir:&Path,namespace:&str)->Result<()> {
    members::drain_posts(root,workspace,dir,namespace,"format")?;
    for (number,path) in plans(dir)? {
        let plan=ws::bounded_json(&path)?;
        if !dir.join(format!("rekey-{number}-accepted.json")).exists(){continue;}
        let mut verified=false;
        for _ in 0..128 {
            let read=ws::rendered_document(root,workspace,name,None,None)?;
            let read_root=text(&read.view["cell"],"root")?;
            if formatting_complete_at(dir,number,&path,read_root)? {verified=true;break;}
            let raw=ws::entries(&read.view)?;
            let mut carry=Vec::new();
            for prior in plan["marks"].as_array().ok_or("rewrite plan lacks marks")? {
                let atom_id=text(&prior["anchor"],"atom")?;
                let current=atom(raw,atom_id)?;
                let staged=plan["atoms"].as_array().ok_or("rewrite plan lacks atoms")?.iter()
                    .find(|a|a["atom"]==atom_id).ok_or("format plan names unplanned atom")?;
                let display=atom(&read.entries,atom_id)?;
                if !current["tombstonedAt"].is_null() || plaintext(display)?!=staged["plaintext"] {
                    return Err(conflict(dir,&plan,&read.view,"a competing text edit invalidated the retained formatting plan")?);
                }
                let source_id=text(prior,"id")?;
                let source=raw.iter().find(|r|r["type"]=="mark"&&r["id"]==source_id)
                    .ok_or("retained formatting source disappeared")?;
                if source["canonical"]!=prior["canonical"] || (source["kind"]=="link"&&source["linkLive"]!=true) {
                    return Err(conflict(dir,&plan,&read.view,"a competing mark/link edit invalidated the retained formatting plan")?);
                }
                let revision=text(current,"revision")?;
                let mark=id(namespace,&format!("mark/{number}/{source_id}/{revision}"));
                let mut request=json!({"sourceMark":source_id,"mark":mark,"atom":atom_id,"revision":revision});
                if source["kind"]=="link" {request["link"]=json!(id(namespace,&format!("link/{number}/{source_id}/{revision}")));}
                if let Some(existing)=raw.iter().find(|r|r["type"]=="mark"&&r["id"]==mark) {
                    if existing["anchor"]!=json!({"type":"atom","atom":atom_id,"revision":revision})
                        || existing["kind"]!=source["kind"] || existing["fresh"]!=true || !existing["tombstonedAt"].is_null()
                        || (source["kind"]=="link"&&(existing["target"]!=source["target"]||existing["link"]!=request["link"]||existing["linkLive"]!=true)) {
                        return Err(conflict(dir,&plan,&read.view,"a carried formatting record differs from the exact retained plan")?);
                    }
                } else {carry.push(request);}
                if carry.len()==64{break;}
            }
            if carry.is_empty(){
                let complete=dir.join(format!("format-plan-{number}-complete-{read_root}.json"));
                retain_json(&complete,&json!({"root":read_root,"sourcePlan":path,"formattingReceived":true}))?;
                verified=true;break;
            }
            let label=format!("format-{}",next_format(dir)?);
            let proposal=json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{
                "name":name,"expectedTargetRoot":read.view["cell"]["root"],"payload":{"type":"carryFormatting","actions":carry}}]});
            let proof=dir.join(format!("{label}-source.json"));retain_json(&proof,&read.view)?;
            if let Err(error)=members::action(root,workspace,dir,namespace,&label,proposal) {
                if !members::post_unadmitted(root,dir,namespace,&label)? {return Err(error);}
                let now=ws::rendered_document(root,workspace,name,None,None)?;
                if now.view["cell"]["root"]!=read.view["cell"]["root"] {continue;}
                return Err(error);
            }
        }
        if !verified{return Err("formatting repair needs another recovery pass; no completion published".into());}
    }
    Ok(())
}

pub(super) fn current(root:&Path,workspace:&Value,name:&str,dir:&Path,namespace:&str,epoch:u64)->Result<String> {
    members::drain_posts(root,workspace,dir,namespace,"rekey")?;
    // A crash may leave the immutable plan before its first request artifact.
    // Recover that exact plan; never overwrite it with a fresh observation.
    for (number,path) in plans(dir)? {
        if dir.join(format!("rekey-{number}-accepted.json")).exists(){continue;}
        let plan=ws::bounded_json(&path)?;
        let label=format!("rekey-{number}");
        let request=rekey_request(name,&plan)?;
        if let Err(error)=members::action(root,workspace,dir,namespace,&label,request) {
            if !members::post_unadmitted(root,dir,namespace,&label)?{return Err(error);}
            let now=ws::rendered_document(root,workspace,name,None,None)?;
            if now.view["cell"]["root"]==plan["root"]{return Err(error);}
        }
    }
    restore(root,workspace,name,dir,namespace)?;
    for _ in 0..4096 {
        let read=ws::rendered_document(root,workspace,name,None,None)?;
        let visible=visible(&read.document)?;
        let raw=ws::entries(&read.view)?;
        let mut edits=Vec::new();let mut atoms=Vec::new();let mut selected=BTreeSet::new();
        for current in raw.iter().filter(|r|r["type"]=="atom"&&r["tombstonedAt"].is_null()&&r["id"].as_str().is_some_and(|id|visible.contains(id))) {
            let atom_id=text(current,"id")?;
            let plain=plaintext(atom(&read.entries,atom_id)?)?;
            if is_kind(&current["kind"])&&members::atom_epoch(text(current,"payload")?)?==epoch {continue;}
            selected.insert(atom_id.to_owned());atoms.push(json!({"atom":atom_id,"plaintext":plain,"rawBefore":current}));
            edits.push(json!({"type":"editAtom","atom":atom_id,"before":ws::atom_record(current)?,
                "kind":{"type":"text"},"payload":plain,"tombstone":false}));
            if edits.len()==64{break;}
        }
        let annotations=pending_annotations(raw,&read.entries,epoch,64-edits.len())?;
        if edits.is_empty()&&annotations.is_empty(){
            let current_root=text(&read.view["cell"],"root")?;
            if all_formatting_at(dir,current_root)? {return Ok(current_root.to_owned());}
            restore(root,workspace,name,dir,namespace)?;
            continue;
        }
        let number=members::next_post(dir,"rekey")?;
        let label=format!("rekey-{number}");
        let plan=json!({"type":"mini-protected-current-rewrite-plan-v1","root":read.view["cell"]["root"],
            "atoms":atoms,"annotations":annotations,"marks":planned_marks(raw,&selected)?,"epoch":epoch.to_string(),"signedView":read.view});
        retain_json(&dir.join(format!("rewrite-plan-{number}.json")),&plan)?;
        let request=rekey_request(name,&plan)?;
        if let Err(error)=members::action(root,workspace,dir,namespace,&label,request) {
            if !members::post_unadmitted(root,dir,namespace,&label)?{return Err(error);}
            let now=ws::rendered_document(root,workspace,name,None,None)?;
            if now.view["cell"]["root"]!=plan["root"]{continue;}
            return Err(error);
        }
        restore(root,workspace,name,dir,namespace)?;
    }
    Err("current-text rewrite needs another recovery pass".into())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn recovered_plan_retains_exact_raw_guard_and_semantic_root() {
        let before=json!({"type":"atom","id":"8","document":"9","kind":{"type":"inlineObject","schema":"77"},
            "payload":"deadbeef","createdBy":"7","createdAt":"2","revision":"3","tombstonedAt":null,
            "private":{"text":"display is not a stale guard"}});
        let plan=json!({"root":"123","atoms":[{"atom":"8","plaintext":"6869","rawBefore":before}]});
        let request=rekey_request("paper",&plan).unwrap();
        assert_eq!(request["targets"][0]["expectedTargetRoot"],"123");
        let action=&request["targets"][0]["payload"]["actions"][0];
        assert_eq!(action["before"]["payload"],"deadbeef");
        assert_eq!(action["before"]["kind"],plan["atoms"][0]["rawBefore"]["kind"]);
        assert!(action["before"].get("private").is_none());
        assert_eq!(action["payload"],"6869");
        let encoded=serde_json::to_vec(&plan).unwrap();
        assert_eq!(rekey_request("paper",&serde_json::from_slice(&encoded).unwrap()).unwrap(),request);
    }
    #[test]
    fn formatting_plan_selects_only_current_live_marks_on_rewritten_atoms() {
        let mark=json!({"type":"mark","id":"4","fresh":true,"tombstonedAt":null,
            "anchor":{"type":"atom","atom":"8","revision":"3"},"kind":"bold","canonical":"01"});
        let mut stale=mark.clone();stale["id"]=json!("5");stale["fresh"]=json!(false);
        let mut retired=mark.clone();retired["id"]=json!("6");retired["tombstonedAt"]=json!("7");
        let annotation=json!({"type":"annotation","id":"7","fresh":true,"anchor":mark["anchor"],"body":"6162"});
        let chosen=planned_marks(&[mark.clone(),stale,retired,annotation],&BTreeSet::from(["8".to_owned()])).unwrap();
        assert_eq!(chosen.len(),1);assert_eq!(chosen[0]["id"],"4");assert_eq!(chosen[0]["canonical"],"01");
        assert!(planned_marks(&[mark],&BTreeSet::from(["9".to_owned()])).unwrap().is_empty());
    }
    #[test]
    fn format_evidence_without_request_keeps_its_reserved_label() {
        let dir=std::env::temp_dir().join(format!("mini-format-reserve-{}",ws::random_nonce().unwrap()));
        fs::create_dir(&dir).unwrap();
        retain_json(&dir.join("format-0-source.json"),&json!({"root":"1"})).unwrap();
        assert_eq!(next_format(&dir).unwrap(),1);
        retain_json(&dir.join("format-3-0.json"),&json!({"request":"retained"})).unwrap();
        assert_eq!(next_format(&dir).unwrap(),4);
        assert_eq!(ws::bounded_json(&dir.join("format-0-source.json")).unwrap()["root"],"1");
        fs::remove_dir_all(&dir).unwrap();
    }
    #[test]
    fn completion_checkpoint_is_valid_only_at_exact_verified_resource_root() {
        let dir=std::env::temp_dir().join(format!("mini-format-root-{}",ws::random_nonce().unwrap()));
        fs::create_dir(&dir).unwrap();
        let path=dir.join("rewrite-plan-0.json");
        retain_json(&path,&json!({"retained":"plan"})).unwrap();
        retain_json(&dir.join("rekey-0-accepted.json"),&json!({"receipt":"accepted"})).unwrap();
        retain_json(&dir.join("format-plan-0-complete-11.json"),&json!({"root":"11","sourcePlan":path,"formattingReceived":true})).unwrap();
        assert!(all_formatting_at(&dir,"11").unwrap());
        assert!(!all_formatting_at(&dir,"12").unwrap());
        retain_json(&dir.join("format-plan-0-complete-12.json"),&json!({"root":"11","sourcePlan":path,"formattingReceived":true})).unwrap();
        assert!(all_formatting_at(&dir,"12").is_err());
        fs::remove_dir_all(&dir).unwrap();
    }

}
