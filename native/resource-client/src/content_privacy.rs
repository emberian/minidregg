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
    if n.is_empty() || !n.bytes().all(|c| c.is_ascii_digit()) {
        return Err("content identifier must be a decimal string".into());
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
        "rewrapAnnotation" => (&["type", "annotation", "before", "wrapping"], Exposure::RewrapAnnotation),
        "transclude" => (&["type", "transclusion", "link", "request"], Exposure::Unsupported),
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
        "createAtom" | "editAtom" => decimal(&action["atom"])? ,
        "annotate" => {decimal(&action["annotation"])?;decimal(&action["atom"])?;decimal(&action["revision"])?;}
        "rewrapAnnotation" => decimal(&action["annotation"])? ,
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
}
