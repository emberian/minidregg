//! Existing formatting metadata carried across protected text conversion.
//!
//! Caller obligations: verified current resource view, protected-document
//! enrollment, exact caller root pin, ordinary all-holder admission and CAS.
//! This module establishes no authority and encrypts no text. Commit conversion
//! first, then observe its revision: source markStep forbids anchoring to a
//! revision created by the same command.
//!
//! Rows: {sourceMark, mark, atom, revision, link?}, canonical decimal strings.
//! A link requires a fresh link ID; finite styles forbid it. No caller kind,
//! target, annotation or bytes are accepted. Source marks may now be stale but
//! must remain live and on the same atom. Planners retain fresh marks selected
//! before conversion. Original marks, links, authors and annotations remain;
//! the source attributes newly allocated marks to the current converter.
use crate::Result;
use serde_json::{json, Map, Value};
use std::collections::BTreeSet;

const MAX_ACTIONS: usize = 64;
const MAX_DECIMAL_DIGITS: usize = 80;
const MAX_EXTERNAL_BYTES: usize = 64 * 1024;

fn object<'a>(value: &'a Value, label: &str) -> Result<&'a Map<String, Value>> {
    value.as_object().ok_or_else(|| format!("{label} must be an object"))
}
fn exact(value: &Value, fields: &[&str], label: &str) -> Result<()> {
    let obj = object(value, label)?;
    if obj.len() != fields.len() || fields.iter().any(|field| !obj.contains_key(*field)) {
        return Err(format!("{label} has unexpected or missing fields"));
    }
    Ok(())
}
fn text<'a>(value: &'a Value, field: &str) -> Result<&'a str> {
    value.get(field).and_then(Value::as_str).ok_or_else(|| format!("{field} must be a string"))
}
fn decimal(value: &str) -> Result<()> {
    if !mini_sdk::decimal::is_canonical_max(value, MAX_DECIMAL_DIGITS)
    {
        return Err("formatting identifiers must be canonical bounded decimal strings".into());
    }
    Ok(())
}
fn identifier<'a>(value: &'a Value, field: &str) -> Result<&'a str> {
    let id = text(value, field)?; decimal(id)?; Ok(id)
}
fn live(value: &Value) -> Result<()> {
    if value.get("tombstonedAt") != Some(&Value::Null) {
        return Err("formatting source or target is retired or lacks lifecycle metadata".into());
    }
    Ok(())
}
fn entry<'a>(entries: &'a [Value], kind: &str, id: &str) -> Result<&'a Value> {
    let mut matching = entries.iter().filter(|v| v["type"] == kind && v["id"] == id);
    let found = matching.next().ok_or_else(|| format!("unknown {kind} {id}"))?;
    if matching.next().is_some() {
        return Err(format!("ambiguous {kind} {id} in resource view"));
    }
    Ok(found)
}
fn fresh_id(entries: &[Value], kind: &str, id: &str, allocated: &mut BTreeSet<String>) -> Result<()> {
    if entries.iter().any(|v| v["type"] == kind && v["id"] == id) {
        return Err(format!("new {kind} identifier is already occupied"));
    }
    if !allocated.insert(id.to_owned()) {
        return Err("duplicate new formatting identifier".into());
    }
    Ok(())
}
fn point(value: &Value) -> Result<()> {
    exact(value, &["run", "neighbor", "bias", "death"], "link range endpoint")?;
    identifier(value, "run")?;
    match &value["neighbor"] {
        Value::Null => {},
        Value::String(id) => decimal(id)?,
        _ => return Err("link range neighbor must be an identifier or null".into()),
    }
    if !matches!(text(value, "bias")?, "before" | "after")
        || !matches!(text(value, "death")?, "invalidate" | "keepTombstone"
            | "preferPrevious" | "preferNext" | "preferPreviousThenNext" | "preferNextThenPrevious")
    {
        return Err("unknown link range endpoint policy".into());
    }
    Ok(())
}
fn link_target(value: &Value) -> Result<()> {
    match text(value, "type")? {
        "document" | "element" => {
            exact(value, &["type", "id"], "existing link target")?;
            identifier(value, "id")?;
        },
        "range" => {
            exact(value, &["type", "document", "range"], "existing link target")?;
            identifier(value, "document")?;
            exact(&value["range"], &["start", "finish"], "existing link range")?;
            point(&value["range"]["start"])?;
            point(&value["range"]["finish"])?;
        },
        "external" => {
            exact(value, &["type", "scheme", "authority", "path"], "existing external link")?;
            let mut total = 0usize;
            for field in ["scheme", "authority", "path"] {
                let bytes = text(value, field)?;
                if bytes.len() % 2 != 0 || !mini_sdk::hex::is_lower(bytes) {
                    return Err("existing external link metadata is not canonical hexadecimal".into());
                }
                total = total.checked_add(bytes.len() / 2).ok_or("existing link metadata is too large")?;
                if total > MAX_EXTERNAL_BYTES {
                    return Err("existing link metadata exceeds carry limit".into());
                }
            }
        },
        _ => return Err("formatting carry does not support this link target".into()),
    }
    Ok(())
}

/// The input view is the signed resource presentation with cell.entries, never
/// an opened/editor projection. Return only source-derived metadata actions.
pub(crate) fn lower(view: &Value, target: &str, actions: &Value) -> Result<Value> {
    decimal(target)?;
    let entries = view.get("cell").and_then(|v| v.get("entries")).and_then(Value::as_array)
        .ok_or("formatting carry requires a signed content resource view")?;
    let requested = actions.as_array().ok_or("formatting carry actions must be an array")?;
    if requested.is_empty() || requested.len() > MAX_ACTIONS {
        return Err("formatting carry requires 1..64 actions".into());
    }
    let mut allocated = BTreeSet::new();
    let mut sources = BTreeSet::new();
    let mut lowered = Vec::with_capacity(requested.len());
    for request in requested {
        let obj = object(request, "formatting carry request")?;
        let fields: &[&str] = if obj.contains_key("link") {
            &["sourceMark", "mark", "atom", "revision", "link"]
        } else { &["sourceMark", "mark", "atom", "revision"] };
        exact(request, fields, "formatting carry request")?;
        let source_id = identifier(request, "sourceMark")?;
        let mark_id = identifier(request, "mark")?;
        let atom_id = identifier(request, "atom")?;
        let revision = identifier(request, "revision")?;
        if !sources.insert(source_id.to_owned()) {
            return Err("source mark selected more than once in one carry".into());
        }
        let atom = entry(entries, "atom", atom_id)?;
        live(atom)?;
        if identifier(atom, "document")? != target || identifier(atom, "revision")? != revision {
            return Err("formatting target atom has another document or revision".into());
        }
        let source = entry(entries, "mark", source_id)?;
        live(source)?;
        if identifier(source, "document")? != target || identifier(source, "mark")? != source_id {
            return Err("source mark identity or document differs".into());
        }
        let anchor = &source["anchor"];
        exact(anchor, &["type", "atom", "revision"], "source mark anchor")?;
        if text(anchor, "type")? != "atom" || identifier(anchor, "atom")? != atom_id {
            return Err("source mark is not anchored to the requested atom".into());
        }
        let old_revision = identifier(anchor, "revision")?;
        if source.get("fresh").and_then(Value::as_bool) != Some(old_revision == revision) {
            return Err("source mark freshness disagrees with the current atom".into());
        }
        let copied_kind = match text(source, "kind")? {
            kind @ ("bold" | "italic" | "code" | "heading") => {
                if obj.contains_key("link")
                    || ["link", "target", "linkLive"].iter().any(|field| source.get(*field).is_some())
                {
                    return Err("finite style carries unexpected link metadata".into());
                }
                json!({"type":kind})
            },
            "link" => {
                let new_link = identifier(request, "link")?;
                let old_link = identifier(source, "link")?;
                if source.get("linkLive") != Some(&Value::Bool(true)) {
                    return Err("source mark link is retired or unavailable".into());
                }
                let record = entry(entries, "link", old_link)?;
                live(record)?;
                // Some Host presentations retain only this link row's ID,
                // lifecycle and canonical bytes. Its exact target and liveness
                // are projected by markJson from that same signed resource.
                let canonical = text(record, "canonical")?;
                if canonical.is_empty() || canonical.len() % 2 != 0
                    || !mini_sdk::hex::is_lower(canonical)
                {
                    return Err("linked record lacks its canonical hexadecimal witness".into());
                }
                let destination = source.get("target").ok_or("source mark lacks its link target")?;
                link_target(destination)?;
                fresh_id(entries, "link", new_link, &mut allocated)?;
                json!({"type":"link","link":new_link,"target":destination})
            },
            _ => return Err("unknown or unsupported source formatting kind".into()),
        };
        fresh_id(entries, "mark", mark_id, &mut allocated)?;
        lowered.push(json!({"type":"mark","mark":mark_id,
            "target":{"type":"atom","atom":atom_id},"revision":revision,"kind":copied_kind}));
    }
    Ok(json!({"type":"content","actions":lowered}))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn view() -> Value {
        json!({"cell":{"root":"100","entries":[
            {"type":"atom","id":"2","document":"1","revision":"20","tombstonedAt":null},
            {"type":"mark","id":"3","mark":"3","document":"1","kind":"bold",
             "anchor":{"type":"atom","atom":"2","revision":"10"},
             "author":{"subject":"7","capabilityKind":"object","capability":"8"},
             "fresh":false,"tombstonedAt":null,"canonical":"00"},
            {"type":"annotation","id":"4","anchor":{"type":"atom","atom":"2","revision":"10"},
             "body":{"type":"inline","bytes":"736563726574"}}
        ]}})
    }
    fn request() -> Value {
        json!([{"sourceMark":"3","mark":"30","atom":"2","revision":"20"}])
    }
    fn link_view(target: Value) -> Value {
        let mut view = view();
        let mark = &mut view["cell"]["entries"][1];
        mark["kind"] = json!("link"); mark["link"] = json!("5");
        mark["linkLive"] = json!(true); mark["target"] = target.clone();
        view["cell"]["entries"].as_array_mut().unwrap().push(json!({
            "type":"link","id":"5","tombstonedAt":null,"canonical":"0001"}));
        view
    }
    fn link_request() -> Value {
        let mut request = request(); request[0]["link"] = json!("50"); request
    }
    #[test]
    fn carries_finite_styles_after_text_revision_without_rewriting_history() {
        for style in ["bold", "italic", "code", "heading"] {
            let mut view = view(); view["cell"]["entries"][1]["kind"] = json!(style);
            let original = view.clone();
            assert_eq!(lower(&view, "1", &request()).unwrap(), json!({"type":"content","actions":[
                {"type":"mark","mark":"30","target":{"type":"atom","atom":"2"},
                 "revision":"20","kind":{"type":style}}]}));
            assert_eq!(view, original);
        }
    }
    #[test]
    fn copies_existing_link_target_exactly_and_allocates_distinct_link() {
        let target = json!({"type":"external","scheme":"6874747073","authority":"6578616d706c652e6f7267","path":"2f7075626c6963"});
        let view = link_view(target.clone()); let original = view.clone();
        let out = lower(&view, "1", &link_request()).unwrap();
        assert_eq!(out["actions"][0]["kind"], json!({"type":"link","link":"50","target":target}));
        assert_eq!(view, original);
        assert_eq!(out["actions"].as_array().unwrap().len(), 1);
        let mut missing = view;
        missing["cell"]["entries"][1].as_object_mut().unwrap().remove("target");
        assert!(lower(&missing, "1", &link_request()).is_err());
    }
    #[test]
    fn admits_only_exact_existing_supported_link_metadata() {
        let point = json!({"run":"6","neighbor":null,"bias":"before","death":"invalidate"});
        for target in [json!({"type":"document","id":"9"}),json!({"type":"element","id":"9"}),
            json!({"type":"range","document":"9","range":{"start":point,"finish":point}})] {
            let view = link_view(target.clone());
            assert_eq!(lower(&view, "1", &link_request()).unwrap()["actions"][0]["kind"]["target"], target);
        }
        for target in [json!({"type":"transclusion","id":"9"}),
            json!({"type":"external","scheme":"0","authority":"","path":""}),
            json!({"type":"external","scheme":"AA","authority":"","path":""}),
            json!({"type":"document","id":"9","body":"smuggled"}),
            json!({"type":"document","id":"09"}),
            json!({"type":"range","document":"9","range":{"start":point,"finish":{}}})] {
            assert!(lower(&link_view(target), "1", &link_request()).is_err());
        }
    }
    #[test]
    fn rejects_unknown_retired_wrong_atom_and_wrong_revision() {
        for (field,value) in [("sourceMark",json!("99")),("atom",json!("99")),
            ("revision",json!("19")),("revision",json!(20)),("mark",json!("030"))] {
            let mut request = request(); request[0][field] = value;
            assert!(lower(&view(), "1", &request).is_err());
        }
        for (row,field,value) in [(0,"tombstonedAt",json!("21")),(1,"tombstonedAt",json!("21")),
            (0,"document",json!("9")),(1,"document",json!("9")),(1,"fresh",json!(true)),
            (1,"mark",json!("99")),(1,"kind",json!("annotation"))] {
            let mut view = view(); view["cell"]["entries"][row][field] = value;
            assert!(lower(&view, "1", &request()).is_err());
        }
        let mut wrong_atom = view(); wrong_atom["cell"]["entries"][1]["anchor"]["atom"] = json!("9");
        assert!(lower(&wrong_atom, "1", &request()).is_err());
        assert!(lower(&view(), "9", &request()).is_err());
    }
    #[test]
    fn refuses_caller_bytes_targets_or_noncarry_actions() {
        for (field,value) in [("target",json!({"type":"document","id":"9"})),
            ("kind",json!({"type":"link"})),("payload",json!("736563726574")),
            ("body",json!({"bytes":"00"})),("type",json!("transclude")),("link",json!("50"))] {
            let mut request = request(); request[0][field] = value;
            assert!(lower(&view(), "1", &request).is_err());
        }
        let mut request = link_request(); request[0].as_object_mut().unwrap().remove("link");
        assert!(lower(&link_view(json!({"type":"document","id":"9"})), "1", &request).is_err());
    }
    #[test]
    fn refuses_retired_links_missing_metadata_and_occupied_ids() {
        let base = link_view(json!({"type":"document","id":"9"}));
        for (row,field,value) in [(1,"linkLive",json!(false)),(3,"tombstonedAt",json!("21")),
            (3,"canonical",json!("")),(3,"canonical",json!("0z")),(3,"id",json!("9"))] {
            let mut view = base.clone(); view["cell"]["entries"][row][field] = value;
            assert!(lower(&view, "1", &link_request()).is_err());
        }
        let mut missing = base.clone();
        missing["cell"]["entries"][0].as_object_mut().unwrap().remove("tombstonedAt");
        assert!(lower(&missing, "1", &link_request()).is_err());
        let mut missing_witness = base.clone();
        missing_witness["cell"]["entries"][3].as_object_mut().unwrap().remove("canonical");
        assert!(lower(&missing_witness, "1", &link_request()).is_err());
        for (field,id) in [("mark","3"),("link","5"),("link","30")] {
            let mut request = link_request(); request[0][field] = json!(id);
            assert!(lower(&base, "1", &request).is_err());
        }
    }
    #[test]
    fn enforces_batch_bounds_and_unique_allocations() {
        assert!(lower(&view(), "1", &json!([])).is_err());
        assert!(lower(&view(), "1", &json!(vec![request()[0].clone();65])).is_err());
        let mut view = view();
        let mut second = view["cell"]["entries"][1].clone();
        second["id"] = json!("6"); second["mark"] = json!("6");
        view["cell"]["entries"].as_array_mut().unwrap().push(second);
        let first = request()[0].clone();
        let mut second = first.clone(); second["sourceMark"] = json!("6");
        assert!(lower(&view, "1", &json!([first,second])).is_err());
        let duplicated = view["cell"]["entries"][1].clone();
        view["cell"]["entries"].as_array_mut().unwrap().push(duplicated);
        assert!(lower(&view, "1", &request()).is_err());
    }
}
