//! Current context consumes participant signed reads and the Lean projection.
//! No resident/history database, provider invocation or grant inference.
use super::*;
const MAX_ROWS:usize=256;
const MAX_BYTES:usize=65_536;

/// Kept separate from rendered prose and discovery/roster state. The Host
/// derives pins from the canonical current resource-view bytes; the signed
/// participant observation supplies identity/authority before this inspector.
pub(crate) fn document(root:&Path, workspace:&Value, name:&str, max_rows:usize, max_bytes:usize)->Result<Value> {
    if !(1..=MAX_ROWS).contains(&max_rows)||!(1..=MAX_BYTES).contains(&max_bytes) {
        return Err("context bounds require rows1..256 and bytes1..65536".into());
    }
    let reference=reference(root,name)?;
    let (view,challenge,signed)=signed_view(root,workspace,&reference,"resource")?;
    let bin=fs::read(signed.with_file_name("view.bin")).map_err(|e|e.to_string())?;
    let (attempt,_)=new_attempt(root)?;
    make_private_dir(&attempt)?;
    let input=attempt.join("context-in.json");
    private_file(&input,&serde_json::to_vec(&json!({
        "target":member(&reference,"target")?,"view":hex(&bin),
        "maxRows":max_rows.to_string(),"maxBytes":max_bytes.to_string()
    })).map_err(|e|e.to_string())?)?;
    let mut projection=inspect(&workspace_host(workspace)?,&member_path(workspace,"config")?,
        "context-document",&input,&attempt.join("context.json"))?;
    if projection["type"]!="mini-context-document-v1"
        || projection["source"]!=reference["target"]
        || projection["sourceRoot"]!=view["cell"]["root"] {
        return Err("context projection differs from participant signed current source".into());
    }
    let raw=entries(&view)?;
    let opened=opened_entries(root,workspace,&reference,&view)?;
    let selected=projection["rows"].as_array().ok_or("context Host omitted rows")?;
    let mut rows=Vec::new();
    let mut opened_bytes=0usize;
    let mut unavailable=0usize;
    for row in selected {
        let id=member(row,"element")?;
        let revision=member(row,"revision")?;
        let matches:Vec<_>=raw.iter().filter(|a|a["type"]=="atom"&&a["id"].as_str()==Some(id)
            && a["revision"].as_str()==Some(revision)&&a["tombstonedAt"].is_null()).collect();
        if matches.len()!=1 {return Err("context pin has no unique current signed atom".into());}
        let atom=matches[0];
        let display=opened.iter().find(|a| {
            let mut original=(*a).clone();
            if let Some(fields)=original.as_object_mut(){fields.remove("private");}
            original==*atom
        }).ok_or("context current atom opening changed its signed source")?;
        let body=if atom["kind"]==json!({"type":"text"}) {
            Some(crate::decode_hex(member(atom,"payload")?)?)
        } else if private::is_private_kind(&atom["kind"]) {
            private::opened_text(display).ok().flatten()
        } else {None};
        let mut selected=row.clone();
        // Sealed/binary source bytes are support data, not inference text.
        selected.as_object_mut().ok_or("context row malformed")?.remove("payload");
        match body.and_then(|bytes|String::from_utf8(bytes).ok()) {
            Some(text) if opened_bytes.checked_add(text.len()).is_some_and(|n|n<=max_bytes)=>{
                let summary=serde_json::from_str::<Value>(&text).ok()
                    .filter(|value|value["type"]=="mini-context-summary-v1");
                if let Some(summary)=summary {
                    let (body,status)=summary_text(root,workspace,&summary)?;
                    selected["summary"]=status;
                    match body {
                        Some(text) if opened_bytes.checked_add(text.len()).is_some_and(|n|n<=max_bytes)=>{
                            opened_bytes+=text.len();selected["text"]=json!(text);selected["state"]=json!("current");
                        }
                        _=>{unavailable+=1;selected["state"]=json!("derived-context-invalidated");}
                    }
                } else {
                    opened_bytes+=text.len();selected["text"]=json!(text);selected["state"]=json!("current");
                }
            }
            _=>{unavailable+=1;selected["state"]=json!("unavailable");}
        }
        rows.push(selected);
    }
    projection["rows"]=json!(rows);
    projection["openedBytes"]=json!(opened_bytes);
    projection["unavailableRows"]=json!(unavailable);
    projection["name"]=json!(name);
    // Height is observation provenance only; sourceRoot carries currentness.
    projection["observedHeight"]=challenge["height"].clone();
    projection["readAuthorityRoot"]=challenge["worldRoot"].clone();
    projection["authority"]=json!("participant-current-signed-read");
    Ok(projection)
}

/// A model's request remains authored data. Every cited source becomes an
/// observe-only target with its exact expected base in the SAME ordinary native
/// command as the requested edit. A race after this read is refused by native
/// current-base/authority admission. This function authors a proposal; it does
/// not claim submit, installation, approval or autonomous model correctness.
pub(crate) fn review(root:&Path,workspace:&Value,id:&str,base:&Value,request:&Value)->Result<Value> {
    let native_request=review_request(base,request,|name|reference(root,name))?;
    propose_request(root,workspace,&native_request,id,None,false)
}
fn review_request(base:&Value,request:&Value,lookup:impl Fn(&str)->Result<Value>)->Result<Value> {
    if base["type"]!="mini-context-bundle-v1" {
        return Err("review requires a canonical context bundle".into());
    }
    if request["type"]!="minidregg-workspace-proposal-v1"||request["action"]!="invoke"
        || request.as_object().is_none_or(|m|m.len()!=3) {
        return Err("review takes an ordinary invoke proposal without a computation claim".into());
    }
    let sources=base["sources"].as_array().ok_or("review context sources absent")?;
    if sources.is_empty()||sources.len()>16 {return Err("review support requires1..16 sources".into());}
    let requested=request["targets"].as_array().ok_or("review targets absent")?;
    let mut pins=std::collections::BTreeMap::<String,(String,String)>::new();
    for source in sources {
        if source["type"]!="mini-context-document-v1" {return Err("review source projection differs".into());}
        let name=member(source,"name")?.to_owned();
        let target=member(source,"source")?.to_owned();
        let root_pin=member(source,"sourceRoot")?.to_owned();
        field_decimal(&root_pin,"context source root")?;
        if pins.insert(name,(target,root_pin)).is_some(){return Err("review duplicates source name".into());}
    }
    // A current derived summary's own input closure joins landing guards.
    // A proposal cannot use its source document root to hide stale citations.
    for source in sources {
        for row in source["rows"].as_array().into_iter().flatten() {
            let Some(summary)=row.get("summary") else {continue;};
            if summary["status"]!="current" {return Err("review context contains invalidated derived memory; reselect current source".into());}
            for dependency in summary["references"].as_array().ok_or("summary source reference closure absent")? {
                let name=member(dependency,"name")?.to_owned();
                let identity=member(dependency,"source")?.to_owned();
                let pin=member(dependency,"root")?.to_owned();
                field_decimal(&pin,"summary review source root")?;
                match pins.get(&name) {
                    Some(prior) if prior!=&(identity.clone(),pin.clone())=>return Err("summary review dependency differs from selected source".into()),
                    Some(_)=>{},
                    None=>{pins.insert(name,(identity,pin));}
                }
            }
        }
    }
    let mut lowered=Vec::new();
    let mut used=std::collections::BTreeSet::new();
    for target in requested {
        let name=member(target,"name")?;
        let (identity,root_pin)=pins.get(name).ok_or("review write target has no selected current-base source")?;
        let current_ref=lookup(name)?;
        if current_ref["target"].as_str()!=Some(identity){return Err("review source reference was rebound".into());}
        if !used.insert(name.to_owned()){return Err("review duplicates target".into());}
        let mut pinned=target.clone();
        if target.get("expectedTargetRoot").is_some_and(|r|r.as_str()!=Some(root_pin)) {
            return Err("review request target differs from selected base".into());
        }
        pinned["expectedTargetRoot"]=json!(root_pin);
        lowered.push(pinned);
    }
    for (name,(identity,root_pin)) in pins {
        if used.contains(&name){continue;}
        let current_ref=lookup(&name)?;
        if current_ref["target"].as_str()!=Some(identity.as_str()){return Err("review support reference was rebound".into());}
        lowered.push(json!({"name":name,"expectedTargetRoot":root_pin,"payload":{"type":"read"}}));
    }
    if lowered.is_empty()||lowered.len()>16{return Err("review command exceeds native16-target bound".into());}
    let native_request=json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":lowered});
    Ok(native_request)
}

fn summary_text(root:&Path,workspace:&Value,value:&Value)->Result<(Option<String>,Value)> {
    let obj=value.as_object().ok_or("summary source malformed")?;
    if obj.len()!=3||value["type"]!="mini-context-summary-v1" {
        return Err("summary source requires type,text,support".into());
    }
    let text=member(value,"text")?;
    let support=value["support"].as_array().ok_or("summary dependencies absent")?;
    if support.is_empty()||support.len()>16{return Err("summary support requires1..16 source pins".into());}
    let mut dependencies=Vec::new();
    let mut current=Vec::new();
    let mut unavailable=false;
    for dependency in support {
        if dependency.as_object().is_none_or(|o|o.len()!=3){return Err("summary pin requires name,source,root".into());}
        let name=member(dependency,"name")?;
        let source=member(dependency,"source")?;
        let expected=member(dependency,"root")?;
        decimal(source,"summary source")?;field_decimal(expected,"summary source root")?;
        dependencies.push(json!({"source":source,"root":expected}));
        // A citation is never a read grant. An unavailable reference/source
        // invalidates the summary's inference text without erasing its history.
        match reference(root,name).and_then(|reference|{
            if reference["target"].as_str()!=Some(source){return Err("summary reference rebound".into());}
            signed_view(root,workspace,&reference,"resource")
        }) {
            Ok((view,_,_))=>current.push(json!({"source":source,"root":member(&view["cell"],"root")?})),
            Err(_)=>unavailable=true,
        }
    }
    let (attempt,_)=new_attempt(root)?;make_private_dir(&attempt)?;
    let input=attempt.join("context-support-in.json");
    private_file(&input,&serde_json::to_vec(&json!({"dependencies":dependencies,"current":current})).map_err(|e|e.to_string())?)?;
    let verdict=inspect(&workspace_host(workspace)?,&member_path(workspace,"config")?,
        "context-support",&input,&attempt.join("context-support.json"))?;
    if verdict["type"]!="mini-context-support-v1"{return Err("summary support receiver differs".into());}
    let status=if unavailable{"unavailable"}else{member(&verdict,"status")?};
    Ok((if verdict["current"]==true&&!unavailable{Some(text.to_owned())}else{None},
        json!({"status":status,"dependencies":dependencies,"current":current,"references":support})))
}


#[cfg(test)]
mod tests {
    use super::*;
    fn base()->Value {
        json!({"type":"mini-context-bundle-v1","sources":[
            {"type":"mini-context-document-v1","name":"reviewed","source":"7","sourceRoot":"70"},
            {"type":"mini-context-document-v1","name":"evidence","source":"8","sourceRoot":"80"}
        ]})
    }
    fn request()->Value {
        json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
            "targets":[{"name":"reviewed","payload":{"type":"document","actions":[{"type":"append","text":"proposal"}]}}]})
    }
    fn lookup(name:&str)->Result<Value>{
        Ok(json!({"target":if name=="reviewed"{"7"}else{"8"}}))
    }
    #[test]
    fn cited_support_and_write_share_one_native_guarded_command() {
        let native=review_request(&base(),&request(),lookup).unwrap();
        assert_eq!(native["targets"].as_array().unwrap().len(),2);
        assert_eq!(native["targets"][0]["expectedTargetRoot"],"70");
        assert_eq!(native["targets"][1],json!({"name":"evidence","expectedTargetRoot":"80","payload":{"type":"read"}}));
        assert_eq!(native["targets"][0]["payload"],request()["targets"][0]["payload"]);
        assert!(native.get("run").is_none(),"external proposal prose isn't an execution claim");
    }
    #[test]
    fn proposal_cannot_rebind_source_or_replace_selected_base() {
        assert!(review_request(&base(),&request(),|_|Ok(json!({"target":"99"}))).is_err());
        let mut other=request();other["targets"][0]["expectedTargetRoot"]=json!("71");
        assert!(review_request(&base(),&other,lookup).is_err());
        let mut unknown=request();unknown["targets"][0]["name"]=json!("uncited");
        assert!(review_request(&base(),&unknown,lookup).is_err());
    }
    #[test]
    fn bounded_support_refuses_duplicate_target_aliases() {
        let mut selected=base();
        let source=selected["sources"][0].clone();selected["sources"].as_array_mut().unwrap().push(source);
        assert!(review_request(&selected,&request(),lookup).is_err());
        let mut duplicate=request();
        let target=duplicate["targets"][0].clone();
        duplicate["targets"].as_array_mut().unwrap().push(target);
        assert!(review_request(&base(),&duplicate,lookup).is_err());
    }
}
