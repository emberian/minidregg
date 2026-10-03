//! Named world-kind operations. Signed views supply descriptors; Lean owns all
//! primitive wire encodings, typed lowering, current law and admission.
use super::*;

fn exact(value: &Value, keys: &[&str]) -> Result<()> {
    let object = value
        .as_object()
        .ok_or("world-kind record must be an object")?;
    if object.len() != keys.len() || keys.iter().any(|key| !object.contains_key(*key)) {
        return Err(format!(
            "world-kind record requires exactly {}",
            keys.join(", ")
        ));
    }
    Ok(())
}

fn fields(descriptor: &Value) -> Result<&Vec<Value>> {
    descriptor
        .get("fields")
        .and_then(Value::as_array)
        .ok_or("descriptor fields must be an array".into())
}

fn primitive(codec: &str, value: &str) -> Result<()> {
    match codec {
        "nat" => field_decimal(value, "natural value"),
        "int" => signed_decimal(value, "integer value"),
        "bytes"
            if value.len() <= 32768
                && value.len().is_multiple_of(2)
                && value
                    .bytes()
                    .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase()) =>
        {
            Ok(())
        }
        "bytes" => Err("bytes value must be lowercase hex, at most 16384 bytes".into()),
        _ => Err("field codec must be nat, int or bytes".into()),
    }
}

/// User source uses primitive values, never pre-encoded Store bytes. Host
/// builds the descriptor-dependent StoreCodec frame from this exact source.
pub(super) fn definition(source: &Value, target: Option<&str>) -> Result<Value> {
    exact(source, &["descriptor", "defaults"])?;
    let mut value = source.clone();
    let descriptor = &mut value["descriptor"];
    let object = descriptor
        .as_object_mut()
        .ok_or("descriptor must be an object")?;
    if let Some(target) = target {
        if object
            .get("kind")
            .is_some_and(|kind| kind.as_str() != Some(target))
        {
            return Err("definition kind differs from the resource target".into());
        }
        object.insert("kind".into(), json!(target));
    }
    let keys = if object.contains_key("kind") {
        vec!["kind", "revision", "fields"]
    } else {
        vec!["revision", "fields"]
    };
    exact(descriptor, &keys)?;
    if let Some(kind) = descriptor.get("kind") {
        field_decimal(kind.as_str().ok_or("kind must be decimal")?, "kind")?;
    }
    field_decimal(member(descriptor, "revision")?, "descriptor revision")?;
    let mut ids = std::collections::BTreeSet::new();
    let mut names = std::collections::BTreeSet::new();
    for field in fields(descriptor)? {
        exact(field, &["id", "name", "meaning", "codec", "discipline"])?;
        let id = member(field, "id")?;
        field_decimal(id, "field id")?;
        let name = member(field, "name")?;
        if !ids.insert(id)
            || !names.insert(name)
            || name.is_empty()
            || member(field, "meaning")?.is_empty()
        {
            return Err("fields need unique ids/names and nonempty names/meanings".into());
        }
        if !matches!(member(field, "codec")?, "nat" | "int" | "bytes") {
            return Err("unknown primitive codec".into());
        }
        if !matches!(member(field, "discipline")?, "rom" | "ram" | "append") {
            return Err("discipline must be rom, ram or append".into());
        }
    }
    let mut addresses = std::collections::BTreeSet::new();
    for entry in value["defaults"]
        .as_array()
        .ok_or("defaults must be an array")?
    {
        exact(entry, &["field", "key", "value"])?;
        let id = member(entry, "field")?;
        let key = member(entry, "key")?;
        field_decimal(key, "entry key")?;
        if !addresses.insert((id, key)) {
            return Err("duplicate default field/key".into());
        }
        let field = fields(&value["descriptor"])?
            .iter()
            .find(|field| field["id"].as_str() == Some(id))
            .ok_or("default names unknown field")?;
        if field["meaning"] == "dregg/world/method-table/v1" && entry["value"].is_array() {
            if field["codec"] != "bytes" || field["discipline"] != "rom" || key != "0" {
                return Err("method table must be ROM bytes at key zero".into());
            }
            method_table(&value["descriptor"], &entry["value"])?;
        } else {
            primitive(member(field, "codec")?, member(entry, "value")?)?;
        }
    }
    Ok(value)
}

/// Signed readback includes derived methods for inspection. Birth receives only
/// the source descriptor and defaults; inspection fields are never constructor input.
fn selected_definition(data: &Value, target: &str) -> Result<Value> {
    definition(&json!({"descriptor":data["descriptor"],"defaults":data["defaults"]}), Some(target))
}

fn cell<'a>(view: &'a Value, role: &str) -> Result<&'a Value> {
    view.get("cell")
        .and_then(|cell| cell.get(role))
        .ok_or_else(|| format!("signed resource is not {role}"))
}

fn seen_file(root: &Path, name: &str) -> Result<PathBuf> {
    validate_ref_name(name)?;
    Ok(root
        .join("seen")
        .join(format!("world-{}.json", ref_file(name))))
}

pub(super) fn show(root: &Path, workspace: &Value, name: &str, role: &str) -> Result<()> {
    let reference = reference(root, name)?;
    let (view, challenge, _) = signed_view(root, workspace, &reference, "resource")?;
    let data = cell(&view, role)?;
    let directory = root.join("seen");
    if !directory.exists() {
        make_private_dir(&directory)?;
    }
    private_dir(&directory)?;
    let staged = directory.join(format!(".world-{}-{}", ref_file(name), random_nonce()?));
    private_file(
        &staged,
        &serde_json::to_vec(&view).map_err(|e| e.to_string())?,
    )?;
    fs::rename(staged, seen_file(root, name)?).map_err(|e| e.to_string())?;
    print_json(&json!({"name":name,"target":reference["target"],"judgedAt":challenge,"value":data}))
}

/// Named edits retain the value the member last saw. The fresh signed read
/// supplies the current root guard, and Lean checks the old value again.
pub(super) fn named_actions(
    root: &Path,
    name: &str,
    current: &Value,
    actions: &Value,
    fresh: bool,
) -> Result<Value> {
    let retained = if fresh {
        current.clone()
    } else {
        bounded_json(&seen_file(root, name)?)
            .map_err(|_| "read this instance with `instance show` before editing".to_owned())?
    };
    lower_named(
        cell(&retained, "worldInstance")?,
        cell(current, "worldInstance")?,
        actions,
    )
}

fn lower_named(seen: &Value, current: &Value, actions: &Value) -> Result<Value> {
    if seen["descriptor"] != current["descriptor"] {
        return Err("instance descriptor changed since your last read".into());
    }
    let descriptor = &seen["descriptor"];
    let entries = seen["entries"]
        .as_array()
        .ok_or("instance view lacks entries")?;
    let mut lowered = Vec::new();
    for action in actions.as_array().ok_or("named actions must be an array")? {
        let verb = member(action, "type")?;
        match verb {
            "set" => exact(action, &["type", "field", "key", "value"])?,
            "erase" => exact(action, &["type", "field", "key"])?,
            _ => return Err("named action must be set or erase".into()),
        }
        let name = member(action, "field")?;
        let field = fields(descriptor)?
            .iter()
            .find(|field| field["name"].as_str() == Some(name))
            .ok_or_else(|| format!("unknown named field {name}"))?;
        let id = member(field, "id")?;
        let key = member(action, "key")?;
        field_decimal(key, "entry key")?;
        let previous = entries.iter().find(|entry| {
            entry["field"].as_str() == Some(id) && entry["key"].as_str() == Some(key)
        });
        if verb == "erase" {
            let before = previous.ok_or("cannot erase an absent entry")?;
            lowered.push(
                json!({"type":"erase","field":id,"key":key,"before":member(before,"value")?}),
            );
        } else {
            let text = member(action, "value")?;
            let value = if member(field, "codec")? == "bytes" {
                hex(text.as_bytes())
            } else {
                text.to_owned()
            };
            primitive(member(field, "codec")?, &value)?;
            lowered.push(match previous {
                Some(before) => json!({"type":"write","field":id,"key":key,"before":member(before,"value")?,"after":value}),
                None => json!({"type":"create","field":id,"key":key,"value":value}),
            });
        }
    }
    if lowered.is_empty() {
        return Err("world mutation needs an action".into());
    }
    Ok(json!({"type":"world","descriptor":descriptor,"actions":lowered}))
}

pub(super) fn revise(payload: &Value, view: &Value, target: &str) -> Result<Value> {
    exact(payload, &["type", "definition"])?;
    let old = cell(view, "worldKind")?;
    let updated = definition(&payload["definition"], Some(target))?;
    let prior = member(&old["descriptor"], "revision")?;
    let revision = member(&updated["descriptor"], "revision")?;
    if !decimal_leq(prior, revision) || prior == revision {
        return Err("kind revision must increase".into());
    }
    Ok(json!({"type":"kindDefinition","definition":updated}))
}

pub(super) fn create(
    root: &Path,
    workspace: &Value,
    name: &str,
    predicate_path: &Path,
    room: Option<&str>,
    definition_path: Option<&Path>,
    from: Option<&str>,
) -> Result<()> {
    validate_ref_name(name)?;
    let predicate = bounded_json(predicate_path)?;
    let data = match (definition_path, from) {
        (Some(path), None) => json!({"definition":definition(&bounded_json(path)?, None)?}),
        (None, Some(kind_name)) => {
            let reference = reference(root, kind_name)?;
            let target = member(&reference, "target")?;
            let retained = root
                .join("sources")
                .join(format!("create-{}.request.json", ref_file(name)));
            if retained.exists() {
                // Exact retry retains the originally selected definition, even
                // if its current head has changed or is no longer readable.
                let request = bounded_json(&retained)?;
                let selected = request
                    .get("world")
                    .ok_or("retained birth lacks kind selection")?;
                if member(selected, "fromKind")? != target {
                    return Err("retained birth names a different kind".into());
                }
                selected.clone()
            } else {
                let (view, _, _) = signed_view(root, workspace, &reference, "resource")?;
                let data = cell(&view, "worldKind")?;
                if member(&data["descriptor"], "kind")? != target {
                    return Err("signed kind descriptor identity differs from target".into());
                }
                json!({"fromKind":target,"expectedKindRoot":member(&view["cell"],"root")?,
                    "expectedKindRevision":member(&data["descriptor"],"revision")?,
                    "definition":selected_definition(data, target)?})
            }
        }
        _ => return Err("choose exactly one definition or --from kind reference".into()),
    };
    let storage = if from.is_some() {
        "world-instance"
    } else {
        "world-kind"
    };
    let room_reference = room.map(|room| reference(root, room)).transpose()?;
    if room_reference.as_ref().is_some_and(|resolved| resolved.get("private").is_some()) {
        return Err("world kinds do not yet support private room payload sealing".into());
    }
    let (source, receipt, reservation) = birth(
        root,
        workspace,
        name,
        &BirthShape {
            kind: "object",
            storage,
            owner: member(workspace, "subject")?,
            predicate: &predicate,
            funding: None,
            room: room_reference.as_ref(),
            program: None,
            fields: None,
            world: Some(data),
        },
    )?;
    complete_birth(root, name, &source, &receipt, &reservation, None, None)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn sample() -> Value {
        json!({"descriptor":{"revision":"1","fields":[
        {"id":"8","name":"votes","meaning":"poll vote","codec":"nat","discipline":"ram"},
        {"id":"2","name":"question","meaning":"poll question","codec":"bytes","discipline":"rom"}]},
        "defaults":[{"field":"2","key":"0","value":"4869"}]})
    }
    #[test]
    fn definition_rejects_ambiguous_and_noncanonical_sources() {
        assert!(definition(&sample(), Some("99")).is_ok());
        let mut value = sample();
        value["descriptor"]["fields"][1]["id"] = json!("8");
        assert!(definition(&value, None).is_err());
        let mut value = sample();
        value["defaults"][0]["value"] = json!("4A");
        assert!(definition(&value, None).is_err());
        let mut value = sample();
        value["descriptor"]["kind"] = json!("88");
        assert!(definition(&value, Some("99")).is_err());
        let mut value = sample();
        value["defaults"][0]["field"] = json!("55");
        assert!(definition(&value, None).is_err());
    }
    #[test]
    fn signed_kind_readback_supplies_only_canonical_constructor_source() {
        let mut source = sample();
        source["descriptor"]["kind"] = json!("99");
        let mut readback = source.clone();
        readback["methods"] = json!([{ "name":"inspection-only", "program":"7", "outputs":[] }]);
        assert!(definition(&readback, Some("99")).is_err());
        assert_eq!(selected_definition(&readback, "99").unwrap(), source);
        assert!(selected_definition(&readback, "88").is_err());
        readback["defaults"][0]["value"] = json!("4A");
        assert!(selected_definition(&readback, "99").is_err());
    }

    #[test]
    fn named_edit_uses_read_descriptor_and_exact_old_value() {
        let mut seen = json!({"descriptor":sample()["descriptor"],"entries":[{"field":"8","key":"7","value":"1"}]});
        let mut current = seen.clone();
        current["entries"][0]["value"] = json!("2");
        let action = json!([{"type":"set","field":"votes","key":"7","value":"3"}]);
        let lowered = lower_named(&seen, &current, &action).unwrap();
        assert_eq!(
            lowered["actions"][0],
            json!({"type":"write","field":"8","key":"7","before":"1","after":"3"})
        );
        seen["descriptor"]["revision"] = json!("2");
        assert!(lower_named(&seen, &current, &action).is_err());
    }
    #[test]
    fn fields_come_from_world_definition_not_a_host_named_kind() {
        let seen = json!({"descriptor":sample()["descriptor"],"entries":[]});
        let lowered = lower_named(
            &seen,
            &seen,
            &json!([{"type":"set","field":"question","key":"0","value":"hé"}]),
        )
        .unwrap();
        assert_eq!(lowered["actions"][0]["value"], json!("68c3a9"));
        assert!(lower_named(
            &seen,
            &seen,
            &json!([{"type":"set","field":"membership","key":"0","value":"1"}])
        )
        .is_err());
    }
}


fn method_table(descriptor: &Value, table: &Value) -> Result<()> {
    let mut names = std::collections::BTreeSet::new();
    let mut programs = std::collections::BTreeSet::new();
    for method in table.as_array().ok_or("methods must be an array")? {
        exact(method, &["name", "program", "outputs"])?;
        let name = member(method, "name")?;
        let program = member(method, "program")?;
        field_decimal(program, "method program")?;
        if name.is_empty() || !names.insert(name) || !programs.insert(program) {
            return Err("methods need unique names and program identities".into());
        }
        let mut coordinates = std::collections::BTreeSet::new();
        let mut addresses = std::collections::BTreeSet::new();
        for output in method["outputs"].as_array().ok_or("method outputs must be an array")? {
            exact(output, &["output", "field", "key"])?;
            let coordinate = member(output, "output")?;
            let id = member(output, "field")?;
            let key = member(output, "key")?;
            for value in [coordinate, id, key] { field_decimal(value, "method output coordinate")?; }
            if !coordinates.insert(coordinate) || !addresses.insert((id,key)) {
                return Err("method output coordinates and addresses must be unique".into());
            }
            let field = fields(descriptor)?.iter().find(|field| field["id"].as_str() == Some(id))
                .ok_or("method output names unknown field")?;
            if !matches!(member(field,"codec")?, "nat" | "int") || field["discipline"] == "rom" {
                return Err("method output requires a writable numeric field".into());
            }
        }
    }
    Ok(())
}

pub(super) fn method_operation(workspace: &Value, operation: u8, payload: &[u8]) -> Result<Value> {
    let frame = crate::session_invoke(&workspace_host(workspace)?,
        &member_path(workspace,"socket")?, &member_path(workspace,"config")?, operation, payload)?;
    match frame.split_first() {
        Some((actual, body)) if *actual == operation =>
            serde_json::from_slice(body).map_err(|e| format!("method op{operation}: {e}")),
        _ => Err(format!("method op{operation} refused: {}",String::from_utf8_lossy(&frame))),
    }
}

/// Translate evaluator output through the table read from the instance, never
/// through method-specific client code. The receiving source repeats this match.
fn method_actions(instance: &Value, method: &Value, dry: &Value) -> Result<Vec<Value>> {
    let bindings = method["outputs"].as_array().ok_or("method lacks output bindings")?;
    let mut seen = std::collections::BTreeSet::new();
    let mut actions = Vec::new();
    for write in dry["writes"].as_array().ok_or("method output has no field writes")? {
        let parts = write.as_array().ok_or("method write must be a triple")?;
        if parts.len() != 3 || parts[0].as_str() != Some("0") {
            return Err("single-instance method emitted another participant's write".into());
        }
        let output = parts[1].as_str().ok_or("method output field is not decimal")?;
        if !seen.insert(output) { return Err("method emitted duplicate output address".into()); }
        let binding = bindings.iter().find(|binding| binding["output"].as_str() == Some(output))
            .ok_or("method emitted undeclared output coordinate")?;
        let field = fields(&instance["descriptor"] )?.iter()
            .find(|field| field["id"] == binding["field"]).ok_or("method names missing field")?;
        let value = parts[2].as_str().ok_or("method output value is not numeric")?;
        primitive(member(field,"codec")?,value)?;
        actions.push(json!({"type":"set","field":member(field,"name")?,"key":binding["key"],"value":value}));
    }
    Ok(actions)
}

pub(super) fn validate_funding_payload(payload: &Value) -> Result<()> {
    exact(payload,&["type","asset","credits","expectedPayerBalance","expectedBookRoot"])?;
    if member(payload,"type")? != "computeFunding" {return Err("wrong compute funding payload".into());}
    decimal(member(payload,"asset")?,"credit asset")?;
    decimal(member(payload,"credits")?,"compute credits")?;
    signed_decimal(member(payload,"expectedPayerBalance")?,"payer balance")?;
    field_decimal(member(payload,"expectedBookRoot")?,"Book root")
}

/// Pricing uses the signed reader quota. Large cumulative usage is compared as
/// canonical decimal text; only bounded evaluator steps need a machine integer.
fn compute_consent(view: &Value, subject: &str, steps: &str, maximum: &str) -> Result<(Option<Value>,Value)> {
    decimal(steps,"admitted steps")?; decimal(maximum,"maximum compute credits")?;
    let quote=view.get("computeQuote").filter(|value|value.is_object())
        .ok_or("compute accounting is not active in this signed account view")?;
    if member(quote,"subject")? != subject {return Err("compute quote belongs to another member".into());}
    if member(quote,"freeSteps")? != "1000000" || member(quote,"creditsPerStep")? != "1" {
        return Err("unsupported source compute pricing".into());
    }
    let used=member(quote,"usedSteps")?; decimal(used,"used compute steps")?;
    let remaining=if decimal_leq(used,"1000000") {1_000_000-used.parse::<u64>().map_err(|e|e.to_string())?} else {0};
    let admitted=steps.parse::<u64>().map_err(|_|"method steps exceed this client's bounded evaluator range")?;
    let credits=admitted.saturating_sub(remaining).to_string();
    if !decimal_leq(&credits,maximum) {return Err(format!("method needs {credits} compute credits, above consent ceiling {maximum}"));}
    let summary=json!({"day":quote["day"],"usedSteps":used,"admittedSteps":steps,
        "credits":credits,"maxComputeCredits":maximum});
    if credits=="0" {return Ok((None,summary));}
    let asset=member(quote,"creditAsset")?;
    let balance=view["balances"].as_array().ok_or("signed account view lacks balances")?.iter()
        .find(|row|row.get(0).and_then(Value::as_str)==Some(asset))
        .and_then(|row|row.get(1)).and_then(Value::as_str)
        .ok_or("credit asset balance is outside the account's signed readable scope")?;
    signed_decimal(balance,"payer balance")?;
    if balance.starts_with('-') || !decimal_leq(&credits,balance) {return Err("funding account has insufficient compute credits".into());}
    let payload=json!({"type":"computeFunding","asset":asset,"credits":credits,
        "expectedPayerBalance":balance,"expectedBookRoot":quote["bookRoot"]});
    validate_funding_payload(&payload)?;
    Ok((Some(payload),summary))
}

/// A call prepares an ordinary signed transaction. Reusing the proposal ID
/// returns its retained exact intent, without rerunning or repricing the method.
pub(super) fn call(root: &Path, workspace: &Value, id: &str, name: &str, method_name: &str, funding: Option<&str>, maximum: Option<&str>) -> Result<()> {
    validate_name(id)?;
    validate_ref_name(name)?;
    if funding.is_some() != maximum.is_some() {return Err("--fund and --max-compute-credits must be supplied together".into());}
    if let Some(account)=funding {validate_ref_name(account)?;}
    if let Some(limit)=maximum {decimal(limit,"maximum compute credits")?;}
    let selector = json!({"instance":name,"method":method_name,"funding":funding,"maxComputeCredits":maximum});
    let directory = root.join("proposals").join(id);
    if directory.exists() {
        if bounded_json(&directory.join("method-request.json"))? != selector {
            return Err("proposal ID already names a different method call".into());
        }
        let request = bounded_json(&directory.join("request.json"))?;
        let mut summary = law_export::retained(root,id,&request)?.ok_or("retained method proposal disappeared")?;
        summary["compute"]=bounded_json(&directory.join("compute-consent.json"))?;
        return print_json(&summary);
    }
    let instance_reference = reference(root,name)?;
    let (view,_,_) = signed_view(root,workspace,&instance_reference,"resource")?;
    let instance = cell(&view,"worldInstance")?;
    let table = instance["methods"].as_array().ok_or("instance has no canonical method table")?;
    method_table(&instance["descriptor"],&instance["methods"])?;
    let method = table.iter().find(|method| method["name"].as_str() == Some(method_name))
        .ok_or("instance has no method with that name")?;
    let program = member(method,"program")?;
    let show = method_operation(workspace,132,program.as_bytes())?;
    let slots = instance["sampleSlots"].as_array().ok_or("signed view lacks source sample slots")?;
    let mut values = Vec::new();
    for slot in show.pointer("/abi/sample").and_then(Value::as_array).ok_or("program lacks ABI sample")? {
        if slot["target"].as_str() != Some("0") {
            return Err("single-instance method reads another participant; use a composed invocation".into());
        }
        let name = member(slot,"slot")?;
        let value = slots.iter().find(|pair| pair.get(0).and_then(Value::as_str) == Some(name))
            .and_then(|pair| pair.get(1)).ok_or_else(|| format!("method sample slot {name} absent in signed view"))?;
        values.push(json!(["0",name,value]));
    }
    let request = json!({"programId":program,"caller":member(workspace,"subject")?,"room":"0",
        "targets":[instance_reference["target"]],"values":values});
    let dry = method_operation(workspace,134,request.to_string().as_bytes())?;
    if dry["verdict"].as_str() != Some("ok") { return Err(format!("method did not finish: {dry}")); }
    let actions = method_actions(instance,method,&dry)?;
    let mut targets=vec![json!({"name":name,"payload":{"type":"worldNamed","actions":actions}})];
    let consent=if let (Some(account),Some(limit))=(funding,maximum) {
        let payer=reference(root,account)?;
        if member(&payer,"kind")? != "account" {return Err("--fund requires an account reference".into());}
        let (payer_view,_,_)=signed_view(root,workspace,&payer,"resource")?;
        let (payload,mut consent)=compute_consent(&payer_view,member(workspace,"subject")?,member(&dry,"steps")?,limit)?;
        consent["account"]=json!(account);
        if let Some(payload)=payload {targets.push(json!({"name":account,"payload":payload}));}
        consent
    } else {json!({"admittedSteps":dry["steps"],"maxComputeCredits":"0"})};
    let proposal = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":targets,
        "run":{"programId":program,"sample":dry["sample"],"output":dry["output"],"steps":dry["steps"]}});
    let mut summary = propose_request(root,workspace,&proposal,id,None,true)?;
    summary["compute"]=consent.clone();
    private_file(&directory.join("compute-consent.json"),&serde_json::to_vec(&consent).map_err(|e|e.to_string())?)?;
    private_file(&directory.join("method-request.json"),&serde_json::to_vec(&selector).map_err(|e|e.to_string())?)?;
    print_json(&summary)
}

#[cfg(test)]
mod method_tests {
    use super::*;
    fn instance() -> Value {
        json!({"descriptor":{"kind":"77","revision":"1","fields":[
          {"id":"3","name":"open","meaning":"poll/open","codec":"nat","discipline":"ram"},
          {"id":"4","name":"title","meaning":"poll/title","codec":"bytes","discipline":"rom"}
        ]},"entries":[]})
    }
    fn method() -> Value {
        json!({"name":"close","program":"42","outputs":[{"output":"90","field":"3","key":"0"}]})
    }
    #[test]
    fn compute_consent_binds_reader_threshold_and_explicit_limit() {
        let mut view=json!({"computeQuote":{"subject":"7","bookRoot":"4","day":"8","usedSteps":"999995",
            "freeSteps":"1000000","creditsPerStep":"1","creditAsset":"9"},"balances":[["9","30"]]});
        let (payload,summary)=compute_consent(&view,"7","8","3").unwrap();
        assert_eq!(payload.unwrap()["credits"],"3"); assert_eq!(summary["admittedSteps"],"8");
        assert!(compute_consent(&view,"7","8","2").is_err());
        assert!(compute_consent(&view,"8","8","3").is_err());
        assert!(compute_consent(&view,"7","5","0").unwrap().0.is_none());
        view["computeQuote"]["usedSteps"]=json!("99999999999999999999999999999999999");
        assert_eq!(compute_consent(&view,"7","8","8").unwrap().0.unwrap()["credits"],"8");
        view["balances"]=json!([]); assert!(compute_consent(&view,"7","8","8").is_err());
        view["computeQuote"]=Value::Null; assert!(compute_consent(&view,"7","0","0").is_err());
    }
    #[test]
    fn output_coordinate_maps_to_declared_semantic_address() {
        let actions = method_actions(&instance(),&method(),&json!({"writes":[["0","90","0"]]})).unwrap();
        assert_eq!(actions,json!([{"type":"set","field":"open","key":"0","value":"0"}]).as_array().unwrap().clone());
        assert!(method_actions(&instance(),&method(),&json!({"writes":[["0","3","0"]]})).is_err());
        assert!(method_actions(&instance(),&method(),&json!({"writes":[["1","90","0"]]})).is_err());
    }
    #[test]
    fn ambiguous_and_non_numeric_bindings_refuse() {
        let mut m=method();
        assert!(method_table(&instance()["descriptor"],&json!([m])).is_ok());
        assert!(method_table(&instance()["descriptor"],&json!([m,m])).is_err());
        m["outputs"][0]["field"]=json!("4");
        assert!(method_table(&instance()["descriptor"],&json!([m])).is_err());
    }
    #[test]
    fn duplicate_or_negative_natural_effect_refuses() {
        assert!(method_actions(&instance(),&method(),&json!({"writes":[["0","90","0"],["0","90","0"]]})).is_err());
        assert!(method_actions(&instance(),&method(),&json!({"writes":[["0","90","-1"]]})).is_err());
    }
}

/// Source program registration uses the existing canonical evaluator admission
/// and ordinary content-addressed birth. The client never interprets the code.
pub(super) fn program_create(root: &Path, workspace: &Value, name: &str,
    source_path: &Path, predicate: &Path, room: Option<&str>) -> Result<()> {
    validate_ref_name(name)?;
    let source=bounded_json(source_path)?;
    exact(&source,&["jam","abi"])?;
    let code=unhex(member(&source,"jam")?)?;
    let length=u32::try_from(code.len()).map_err(|_|"program code too large")?;
    let mut payload=length.to_le_bytes().to_vec();
    payload.extend_from_slice(&code);
    payload.extend_from_slice(&serde_json::to_vec(&source["abi"]).map_err(|e|e.to_string())?);
    let verdict=method_operation(workspace,131,&payload)?;
    if verdict["verdict"].as_str()!=Some("admissible") {
        return Err(format!("program admission refused: {verdict}"));
    }
    let directory=root.join("programs");
    if !directory.exists() { make_private_dir(&directory)?; }
    private_dir(&directory)?;
    let path=directory.join(format!("{}.json",ref_file(name)));
    if path.exists() {
        let held=bounded_json(&path)?;
        if held["program"]!=verdict["program"] {
            return Err("program name already pins different immutable code/ABI".into());
        }
    } else {
        private_file(&path,&serde_json::to_vec(&verdict).map_err(|e|e.to_string())?)?;
    }
    super::create(root,workspace,name,"nock",predicate,room,"object",None,Some(&path),None)
}
