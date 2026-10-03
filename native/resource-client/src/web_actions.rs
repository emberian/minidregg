//! Authored connections over one retained signed document base.
//! The Host owns range openings, authority, placement, freshness and sealing.
use super::*;

fn positive(value: &Value, key: &str) -> Result<usize> {
    let n = member(value, key)?;
    decimal(n, key)?;
    n.parse::<usize>()
        .ok()
        .filter(|n| *n > 0)
        .ok_or_else(|| format!("{key} must be one or more"))
}

pub(crate) fn validate(action: &Value) -> Result<()> {
    let keys: &[&str] = match member(action, "type")? {
        "annotate" => &["type", "line", "text"],
        "range" => &["type", "from", "to"],
        "link" => &["type", "to", "relation"],
        "transclude" => &["type", "source", "from", "to", "mode", "death"],
        _ => return Err("unknown document connection action".into()),
    };
    let fields = action.as_object().ok_or("action must be an object")?;
    if fields.len() != keys.len() || keys.iter().any(|key| !fields.contains_key(*key)) {
        return Err("document connection has unexpected fields".into());
    }
    match member(action, "type")? {
        "annotate" => {
            positive(action, "line")?;
            text_argument(action)?;
        }
        "range" | "transclude" => {
            let from = positive(action, "from")?;
            if from > positive(action, "to")? {
                return Err("first line follows last line".into());
            }
            if action["type"] == "transclude" {
                validate_ref_name(member(action, "source")?)?;
                if !matches!(action["mode"].as_str(), Some("live" | "snapshot")) {
                    return Err("quote mode must be live or snapshot".into());
                }
                if !matches!(
                    action["death"].as_str(),
                    Some(
                        "invalidate"
                            | "keepTombstone"
                            | "preferPrevious"
                            | "preferNext"
                            | "preferPreviousThenNext"
                            | "preferNextThenPrevious"
                    )
                ) {
                    return Err("unknown endpoint death policy".into());
                }
            }
        }
        "link" => {
            validate_ref_name(member(action, "to")?)?;
            decimal(member(action, "relation")?, "relation")?;
        }
        _ => unreachable!(),
    }
    Ok(())
}

fn content_target(name: &str, actions: Vec<Value>) -> Value {
    json!({"name":name,"payload":{"type":"content","actions":actions}})
}

fn annotated(seen: &Value, action: &Value) -> Result<Value> {
    let line = positive(action, "line")?;
    let lines = live_lines(&seen["document"])?;
    let row = lines
        .get(line - 1)
        .ok_or("the retained document has no such line")?;
    if row["kind"] != "atom" {
        return Err("annotate the source of a transclusion".into());
    }
    let atom = member(row, "atom")?;
    let raw = entries(&seen["view"])?
        .iter()
        .find(|entry| entry["type"] == "atom" && entry["id"].as_str() == Some(atom))
        .ok_or("the retained view does not cover this atom")?;
    Ok(
        json!({"type":"annotate","annotation":random_nonce()?,"atom":atom,
        "revision":member(raw,"revision")?,"body":text_argument(action)?}),
    )
}

fn transclusion(source: &str, view: &Value, atoms: &[String], action: &Value) -> Result<Value> {
    let cell = entries(view)?;
    let from = atoms.first().ok_or("empty source range")?;
    let to = atoms.last().ok_or("empty source range")?;
    let run = cell.iter().find(|entry| entry["type"] == "run"
        && entry["atoms"].as_array().is_some_and(|members| {
            let first = members.iter().position(|a| a.as_str() == Some(from.as_str()));
            let last = members.iter().position(|a| a.as_str() == Some(to.as_str()));
            matches!((first,last),(Some(a),Some(b)) if a <= b)
        })).ok_or("publish a range in the source first; the selected endpoints must belong to one published range")?;
    let members = run["atoms"].as_array().ok_or("source run lacks atoms")?;
    let first = members
        .iter()
        .position(|a| a.as_str() == Some(from.as_str()))
        .unwrap();
    let last = members
        .iter()
        .position(|a| a.as_str() == Some(to.as_str()))
        .unwrap();
    // Pins describe the entire run slice, including live atoms omitted by a narrowed
    // projection. Missing coverage never fabricates an opening; the Host refuses it.
    let pins: Vec<Value> = members[first..=last]
        .iter()
        .filter_map(|id| {
            cell.iter()
                .find(|entry| {
                    entry["type"] == "atom"
                        && entry["id"] == *id
                        && entry["document"].as_str() == Some(source)
                        && entry["tombstonedAt"].is_null()
                })
                .map(|atom| json!({"atom":id,"revision":atom["revision"]}))
        })
        .collect();
    let point = |neighbor: &str, bias: &str| json!({"run":run["id"],"neighbor":neighbor,"bias":bias,"death":action["death"]});
    Ok(
        json!({"type":"transclude","transclusion":random_nonce()?,"link":random_nonce()?,
        "request":{"source":source,"range":{"start":point(from,"before"),"finish":point(to,"after")},
            "mode":action["mode"],"pins":pins}}),
    )
}

pub(crate) fn plan(
    root: &Path,
    workspace: &Value,
    name: &str,
    seen: &Value,
    action: &Value,
) -> Result<Value> {
    validate(action)?;
    content_page(&seen["view"], name)?;
    let mut targets = Vec::new();
    match member(action, "type")? {
        "annotate" => targets.push(content_target(name, vec![annotated(seen, action)?])),
        "range" => {
            let atoms = line_atoms(
                &seen["document"],
                name,
                positive(action, "from")?,
                positive(action, "to")?,
            )?;
            targets.push(content_target(
                name,
                vec![json!({"type":"createRun","run":random_nonce()?,"atoms":atoms})],
            ));
        }
        "link" => {
            let to = member(action, "to")?;
            let source_ref = reference(root, to)?;
            let (view, _, _) = signed_view(root, workspace, &source_ref, "resource")?;
            let cell = view.get("cell").ok_or("signed source lacks cell")?;
            let id = member(&source_ref, "target")?;
            let target = match cell_storage(cell)? {
                "content" => json!({"type":"document","id":id}),
                _ => resource_link_target(member(&source_ref, "kind")?, id),
            };
            if source_ref != reference(root, to)? {
                return Err("source reference changed while preparing the link".into());
            }
            targets.push(content_target(
                name,
                vec![json!({"type":"link","link":random_nonce()?,"source":null,
                "target":target,"relation":action["relation"]})],
            ));
            // Content source admission shares the final turn with the host write.
            // Other link targets use their signed observation above; a link carries
            // identity only, and following it requires fresh recipient authority.
            if to != name && cell_storage(cell)? == "content" {
                targets.push(json!({"name":to,"payload":{"type":"read"}}));
            }
        }
        "transclude" => {
            let source = member(action, "source")?;
            if source == name {
                return Err("use a separate source document reference for this quote".into());
            }
            let source_ref = reference(root, source)?;
            let read = rendered_document(root, workspace, source, None, None)?;
            let atoms = line_atoms(
                &read.document,
                source,
                positive(action, "from")?,
                positive(action, "to")?,
            )?;
            let quote = transclusion(member(&source_ref, "target")?, &read.view, &atoms, action)?;
            if read.host != member(&source_ref, "target")? || source_ref != reference(root, source)?
            {
                return Err("source reference changed while preparing the quote".into());
            }
            targets.push(content_target(name, vec![quote]));
            targets.push(json!({"name":source,"payload":{"type":"read"}}));
        }
        _ => unreachable!(),
    }
    Ok(json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":targets}))
}

/// IDs and revisions are from the exact base, not a reread or plaintext cache.
pub(crate) fn structure(seen: &Value) -> String {
    let escape = crate::web::escape;
    let mut html = String::from("<details data-document-structure><summary>Lines and published ranges in this base</summary><table><tr><th>Line</th><th>Kind</th><th>Identity</th><th>Revision</th></tr>");
    if let Ok(lines) = live_lines(&seen["document"]) {
        for (i, row) in lines.iter().enumerate() {
            html.push_str(&format!(
                "<tr><td>{}</td><td>{}</td><td><code>{}</code></td><td><code>{}</code></td></tr>",
                i + 1,
                escape(row["kind"].as_str().unwrap_or("?")),
                escape(
                    row["atom"]
                        .as_str()
                        .or_else(|| row["element"].as_str())
                        .unwrap_or("?")
                ),
                escape(row["revision"].as_str().unwrap_or("?"))
            ));
        }
    }
    html.push_str("</table><ul>");
    if let Ok(cell) = entries(&seen["view"]) {
        for run in cell.iter().filter(|entry| entry["type"] == "run") {
            html.push_str(&format!(
                "<li>Range <code>{}</code> · atoms <code>{}</code></li>",
                escape(run["id"].as_str().unwrap_or("?")),
                escape(&run["atoms"].to_string())
            ));
        }
    }
    html.push_str("</ul><p>Comments pin a line's revision. A pinned quote preserves the source opening; a live quote follows its stable range. Source access is checked again when opened.</p></details>");
    html
}

#[cfg(test)]
mod tests {
    use super::*;
    fn seen() -> Value {
        json!({"document":{"order":[{"kind":"atom","atom":"2","element":"2","revision":"99","struck":false}]},
        "view":{"cell":{"entries":[{"type":"atom","id":"2","document":"7","revision":"101","payload":"ciphertext","tombstonedAt":null}]}}})
    }
    #[test]
    fn annotations_use_exact_raw_revision_and_preserve_plaintext_for_sealer() {
        let a = annotated(
            &seen(),
            &json!({"type":"annotate","line":"1","text":"a <private> comment"}),
        )
        .unwrap();
        assert_eq!(a["revision"], "101");
        assert_eq!(a["body"], hex(b"a <private> comment"));
        assert!(annotated(
            &seen(),
            &json!({"type":"annotate","line":"2","text":"comment"})
        )
        .is_err());
    }
    #[test]
    fn ranges_refuse_zero_reversed_and_injected_fields_before_reads() {
        for action in [
            json!({"type":"range","from":"0","to":"1"}),
            json!({"type":"range","from":"2","to":"1"}),
            json!({"type":"range","from":"1","to":"1","payload":"hidden"}),
            json!({"type":"transclude","source":"s","from":"1","to":"1","mode":"snapshot","death":"anything"}),
        ] {
            assert!(validate(&action).is_err());
        }
    }
    #[test]
    fn quotes_pin_the_published_run_slice_and_never_copy_text() {
        let mut view = seen()["view"].clone();
        view["cell"]["entries"]
            .as_array_mut()
            .unwrap()
            .push(json!({"type":"run","id":"8","atoms":["2"]}));
        let quote = transclusion(
            "7",
            &view,
            &["2".into()],
            &json!({"mode":"snapshot","death":"invalidate"}),
        )
        .unwrap();
        assert_eq!(
            quote["request"]["pins"],
            json!([{"atom":"2","revision":"101"}])
        );
        assert_eq!(quote["request"]["range"]["start"]["run"], "8");
        assert!(!quote.to_string().contains("ciphertext"));
        view["cell"]["entries"].as_array_mut().unwrap().pop();
        assert!(transclusion(
            "7",
            &view,
            &["2".into()],
            &json!({"mode":"snapshot","death":"invalidate"})
        )
        .is_err());
    }
}
