//! Strict content grammar boundary shared by ordinary and sealed authoring.
//! This classifies wire actions; the Host still decides all authority and laws.

use crate::Result;
use serde_json::{json, Value};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Exposure {
    Structure,
    CreateText,
    EditText,
    Annotation,
    RewrapAnnotation,
    RewrapAtom,
    Unsupported,
}

fn exact(value: &Value, fields: &[&str]) -> Result<()> {
    let obj = value.as_object().ok_or("content action must be an object")?;
    if obj.len() != fields.len() || fields.iter().any(|key| !obj.contains_key(*key)) {
        return Err("content action has unexpected fields".into());
    }
    Ok(())
}

fn decimal(value: &Value) -> Result<()> {
    let n = value.as_str().ok_or("content identifier must be a decimal string")?;
    if !mini_sdk::decimal::is_digits(n) {
        return Err("content identifier must be a decimal string".into());
    }
    Ok(())
}

// The kernel derives the canonical opening descriptor. Authoring supplies
// only source/range/mode/pins; there is no caller-controlled byte carrier.
fn transclusion_reference(request: &Value) -> Result<()> {
    exact(request, &["source", "range", "mode", "pins"])?;
    decimal(&request["source"])?;
    if !matches!(request["mode"].as_str(), Some("snapshot" | "live")) {
        return Err("transclusion mode must be snapshot or live".into());
    }
    exact(&request["range"], &["start", "finish"])?;
    for key in ["start", "finish"] {
        let point = &request["range"][key];
        exact(point, &["run", "neighbor", "bias", "death"])?;
        decimal(&point["run"])?;
        if !point["neighbor"].is_null() { decimal(&point["neighbor"])?; }
        if !matches!(point["bias"].as_str(), Some("before" | "after")) {
            return Err("transclusion bias must be before or after".into());
        }
        if !matches!(point["death"].as_str(), Some("invalidate" | "keepTombstone"
            | "preferPrevious" | "preferNext" | "preferPreviousThenNext" | "preferNextThenPrevious")) {
            return Err("unknown transclusion endpoint death policy".into());
        }
    }
    for pin in request["pins"].as_array().ok_or("transclusion pins must be an array")? {
        exact(pin, &["atom", "revision"])?;
        decimal(&pin["atom"])?;
        decimal(&pin["revision"])?;
    }
    Ok(())
}

/// Structure-only actions are checked recursively: no unexamined payload can
/// hide in an element edit, schema, run member or extra field.
pub(crate) fn classify(action: &Value) -> Result<Exposure> {
    let tag = action.get("type").and_then(Value::as_str).ok_or("content action lacks type")?;
    let (fields, exposure): (&[&str], _) = match tag {
        "createAtom" => (&["type", "atom", "kind", "payload"], Exposure::CreateText),
        "editAtom" => (&["type", "atom", "before", "kind", "payload", "tombstone"], Exposure::EditText),
        "createDocument" => (&["type", "rootElement", "schema"], Exposure::Structure),
        "createContainer" => (&["type", "element"], Exposure::Structure),
        "createRun" => (&["type", "run", "atoms"], Exposure::Structure),
        "editElement" => (&["type", "element", "revision", "op"], Exposure::Structure),
        "link" => (&["type", "link", "source", "target", "relation"], Exposure::Unsupported),
        "annotate" => (&["type", "annotation", "atom", "revision", "body"], Exposure::Annotation),
        "rewrapAtom" => (&["type", "atom", "before", "wrapping"], Exposure::RewrapAtom),
        "rewrapAnnotation" => (&["type", "annotation", "before", "wrapping"], Exposure::RewrapAnnotation),
        "transclude" => (&["type", "transclusion", "link", "request"], Exposure::Structure),
        "unlink" => (&["type", "link"], Exposure::Unsupported),
        "mark" => (&["type", "mark", "target", "revision", "kind"], Exposure::Unsupported),
        "unmark" => (&["type", "mark"], Exposure::Unsupported),
        _ => return Err("unknown workspace content action".into()),
    };
    exact(action, fields)?;
    match tag {
        "createDocument" => { decimal(&action["rootElement"])?; decimal(&action["schema"])?; }
        "createContainer" => decimal(&action["element"])? ,
        "createRun" => {
            decimal(&action["run"])?;
            for atom in action["atoms"].as_array().ok_or("run atoms must be an array")? {
                decimal(atom)?;
            }
        }
        "editElement" => {
            decimal(&action["element"])?;
            decimal(&action["revision"])?;
            let op = &action["op"];
            match op["type"].as_str() {
                Some("splice" | "move") => {
                    exact(op, &["type", "index", "child"])?;
                    decimal(&op["index"])?;
                }
                Some("remove") => exact(op, &["type", "child"])? ,
                _ => return Err("element edit must be splice, move or remove".into()),
            }
            decimal(&op["child"])?;
        }
        "createAtom" | "editAtom" | "rewrapAtom" => decimal(&action["atom"])? ,
        "annotate" => {decimal(&action["annotation"])?;decimal(&action["atom"])?;decimal(&action["revision"])?;}
        "rewrapAnnotation" => decimal(&action["annotation"])? ,
        "transclude" => {
            decimal(&action["transclusion"])?;
            decimal(&action["link"])?;
            transclusion_reference(&action["request"])?;
        }
        _ => {}
    }
    Ok(exposure)
}

pub(crate) fn actions(actions: &Value, sealed: bool) -> Result<Value> {
    let all = actions.as_array().ok_or("content actions must be an array")?;
    if all.is_empty() || all.len() > 64 {
        return Err("content proposal requires 1..64 actions".into());
    }
    for action in all {
        if classify(action)? == Exposure::Unsupported && sealed {
            return Err(format!("private document action {} has no sealing contract", action["type"]));
        }
    }
    Ok(json!({"type":"content", "actions":actions}))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structural_edits_cannot_smuggle_payloads() {
        let edit = json!({"type":"editElement","element":"1","revision":"2",
            "op":{"type":"move","child":"3","index":"0"}});
        assert_eq!(classify(&edit).unwrap(), Exposure::Structure);
        let mut extra = edit.clone();
        extra["op"]["payload"] = json!("secret");
        assert!(classify(&extra).is_err());
        let mut text_id = edit;
        text_id["op"]["child"] = json!("secret");
        assert!(classify(&text_id).is_err());
        assert!(classify(&json!({"type":"createDocument","rootElement":"1","schema":"2",
            "body":{"type":"opaque","bytes":"secret"}})).is_err());
    }

    #[test]
    fn comments_have_a_sealing_contract_and_unknown_private_actions_refuse() {
        let annotate = json!([{"type":"annotate","annotation":"1","atom":"2","revision":"3","body":"736563726574"}]);
        assert!(actions(&annotate, true).is_ok());
        assert!(actions(&annotate, false).is_ok());
        assert!(actions(&json!([{"type":"futureAction","payload":"secret"}]), true).is_err());
    }
    #[test]
    fn protected_references_are_metadata_only_at_every_level() {
        let point = json!({"run":"1","neighbor":null,"bias":"before","death":"invalidate"});
        let reference = json!({"type":"transclude","transclusion":"2","link":"3",
            "request":{"source":"4","mode":"snapshot","range":{"start":point,"finish":point},
                "pins":[{"atom":"5","revision":"6"}]}});
        assert_eq!(classify(&reference).unwrap(), Exposure::Structure);
        assert!(actions(&json!([reference.clone()]), true).is_ok());
        for pointer in ["/payload", "/request/payload", "/request/range/payload",
            "/request/range/start/payload", "/request/pins/0/payload"] {
            let mut bad=reference.clone();
            let (parent,key)=pointer.rsplit_once('/').unwrap();
            bad.pointer_mut(parent).unwrap().as_object_mut().unwrap().insert(key.into(),json!("secret"));
            assert!(classify(&bad).is_err(), "{pointer}");
        }
        for (pointer,value) in [("/request/mode","copy"),("/request/range/start/bias","secret"),
            ("/request/range/finish/death","secret"),("/request/pins/0/revision","secret")] {
            let mut bad=reference.clone(); *bad.pointer_mut(pointer).unwrap()=json!(value);
            assert!(classify(&bad).is_err());
        }
    }

}
