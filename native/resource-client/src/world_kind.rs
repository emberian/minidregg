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
        primitive(member(field, "codec")?, member(entry, "value")?)?;
    }
    Ok(value)
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
                    "expectedKindRevision":member(&data["descriptor"],"revision")?, "definition":data})
            }
        }
        _ => return Err("choose exactly one definition or --from kind reference".into()),
    };
    let storage = if from.is_some() {
        "world-instance"
    } else {
        "world-kind"
    };
    if let Some(room) = room {
        if reference(root, room)?.get("private").is_some() {
            return Err("world kinds do not yet support private room payload sealing".into());
        }
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
            room,
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
