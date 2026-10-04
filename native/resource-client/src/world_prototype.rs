//! Member-authored constructors consume signed native kind observations and
//! produce one canonical definition through the existing evaluator. The client
//! never decides source authority, kind validity or program result equality.
use super::*;

fn source_slots(view: &Value, whole_definition: bool) -> Result<Vec<Value>> {
    let source=view.pointer("/cell/worldKind").ok_or("source is not a readable world kind")?;
    let mut slots=source["sampleSlots"].as_array().cloned()
        .ok_or("Host lacks authenticated constructor sample slots")?;
    // The destination uses the management projection; only full authorized
    // kindRead parents expose the complete definition noun.
    if !whole_definition {
        slots.retain(|pair|pair.get(0).and_then(Value::as_str)!=Some("kind/definition/noun"));
    }
    Ok(slots)
}

fn selected_values(program: &Value, sources: &[Vec<Value>]) -> Result<Vec<Value>> {
    let mut result=Vec::new();
    for slot in program.pointer("/abi/sample").and_then(Value::as_array).ok_or("constructor lacks ABI sample")? {
        let index: usize=member(slot,"target")?.parse().map_err(|_|"constructor participant index out of range")?;
        let source=sources.get(index).ok_or("constructor sample names an absent participant")?;
        let name=member(slot,"slot")?;
        let value=source.iter().find(|pair|pair.get(0).and_then(Value::as_str)==Some(name))
            .and_then(|pair|pair.get(1)).ok_or_else(||format!("authenticated sample slot {name} absent"))?;
        result.push(json!([index.to_string(),name,value]));
    }
    Ok(result)
}

pub(super) fn construct(root: &Path, workspace: &Value, id: &str, target_name: &str,
    program: &str, parents_path: &Path) -> Result<()> {
    validate_name(id)?;
    validate_ref_name(target_name)?;
    field_decimal(program,"constructor program ID")?;
    let parents=bounded_json(parents_path)?;
    let parents=parents.as_array().ok_or("parents must be an ordered array of kind reference names")?;
    if parents.is_empty() || parents.len()>15 {return Err("constructor needs 1 through 15 authenticated parent participants".into());}
    let mut names=vec![target_name.to_owned()];
    for parent in parents {
        let parent=parent.as_str().ok_or("parent reference must be a string")?;
        validate_ref_name(parent)?;
        if names.iter().any(|name|name==parent) {return Err("duplicate target or parent reference".into());}
        names.push(parent.to_owned());
    }
    let selector=json!({"target":target_name,"program":program,"parents":parents});
    let selector_path=root.join("sources").join(format!("constructor-{}.json",ref_file(id)));
    let result_path=root.join("sources").join(format!("construction-{}.json",ref_file(id)));
    let directory=root.join("proposals").join(id);
    if directory.exists() {
        if bounded_json(&selector_path)? != selector {
            return Err("proposal ID already names a different construction".into());
        }
        let request=bounded_json(&directory.join("request.json"))?;
        let mut summary=law_export::retained(root,id,&request)?.ok_or("retained constructor disappeared")?;
        summary["construction"]=bounded_json(&result_path)?;
        return print_json(&summary);
    }
    let mut image=None;
    let mut targets=Vec::new();
    let mut slots=Vec::new();
    let mut origins=Vec::new();
    for (index,name) in names.iter().enumerate() {
        let reference=reference(root,name)?;
        let (view,challenge,_)=signed_view(root,workspace,&reference,"resource")?;
        let current=member(&challenge,"worldRoot")?;
        if image.as_ref().is_some_and(|previous:&String|previous!=current) {
            return Err("constructor observations moved; retry the same proposal before preparing".into());
        }
        image=Some(current.to_owned());
        slots.push(source_slots(&view,index!=0)?);
        targets.push(reference["target"].clone());
        origins.push(json!({"name":name,"target":reference["target"],
            "root":view["cell"]["root"],"revision":view["cell"]["worldKind"]["descriptor"]["revision"]}));
    }
    let shown=world_kind::method_operation(workspace,132,program.as_bytes())?;
    let outputs=shown.pointer("/abi/outputs").and_then(Value::as_array).ok_or("constructor lacks ABI outputs")?;
    if outputs.len()!=1 || outputs[0]["key"]!="definition" || outputs[0]["target"]!="0"
        || outputs[0]["field"]!="0" || outputs[0]["type"]!="noun" {
        return Err("constructor must declare sole noun output definition at target0 coordinate0".into());
    }
    let values=selected_values(&shown,&slots)?;
    let dry=world_kind::method_operation(workspace,134,
        json!({"programId":program,"caller":member(workspace,"subject")?,"room":"0",
            "targets":targets,"values":values}).to_string().as_bytes())?;
    if dry["verdict"]!="ok" {return Err(format!("constructor did not complete: {dry}"));}
    let kind=b"world-prototype-output";
    let mut payload=(kind.len() as u16).to_le_bytes().to_vec();
    payload.extend_from_slice(kind);
    payload.extend(unhex(member(&dry,"output")?)?);
    let result=world_kind::method_operation(workspace,8,&payload)?;
    let mut proposal_targets=vec![json!({"name":target_name,"expectedTargetRoot":origins[0]["root"],
        "payload":{"type":"kindDefinition","definition":result["definition"]}})];
    for origin in &origins[1..] {
        proposal_targets.push(json!({"name":origin["name"],"expectedTargetRoot":origin["root"],"payload":{"type":"kindRead"}}));
    }
    let proposal=json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":proposal_targets,
        "run":{"programId":program,"sample":dry["sample"],"output":dry["output"],"steps":dry["steps"]}});
    let construction=json!({"program":program,"origins":origins,"steps":dry["steps"],
        "definition":result["definition"],"definitionBytes":result["definitionBytes"]});
    create_private(&selector_path,&serde_json::to_vec(&selector).map_err(|e|e.to_string())?)?;
    create_private(&result_path,&serde_json::to_vec(&construction).map_err(|e|e.to_string())?)?;
    let mut summary=propose_request(root,workspace,&proposal,id,None,true)?;
    summary["construction"]=construction;
    print_json(&summary)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn destination_projection_does_not_advertise_parent_only_definition_slot() {
        let view=json!({"cell":{"worldKind":{"sampleSlots":[
            ["kind/definition/noun","400"],["kind/revision","2"]]}}});
        assert_eq!(source_slots(&view,false).unwrap(),vec![json!(["kind/revision","2"])]);
        assert_eq!(source_slots(&view,true).unwrap().len(),2);
    }
    #[test]
    fn constructor_values_preserve_source_index_and_refuse_missing_dependency() {
        let program=json!({"abi":{"sample":[{"target":"1","slot":"kind/definition/noun","key":"parent","type":"noun"}]}});
        let sources=vec![vec![],vec![json!(["kind/definition/noun","400"])]];
        assert_eq!(selected_values(&program,&sources).unwrap(),vec![json!(["1","kind/definition/noun","400"])]);
        assert!(selected_values(&program,&sources[..1]).is_err());
        assert!(selected_values(&program,&[vec![],vec![]]).is_err());
    }
}
