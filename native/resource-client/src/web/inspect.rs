//! Structural and authored context from this member's own document projection.
//! Source bodies are opened by read_rendered, never borrowed from host custody.
use super::*;
use crate::render::{Annotation, Body};

pub(super) fn page(site: &Site, name: &str) -> Page {
    let title = format!("Source and authored context: {name}");
    let (read, rendered) = match workspace::read_rendered(&site.root, &site.workspace, name, None) {
        Ok(v) => v,
        Err(e) => return failure_page(&title, &e),
    };
    let challenge =
        workspace::bounded_json(&read.attempt.join("challenge.json")).unwrap_or(Value::Null);
    let base = site.base();
    let targets = site.targets();
    let source_link = |id: &str| -> String {
        match targets.iter().find(|(t, _)| t == id) {
            Some((_, n)) => format!("<a href=\"{base}/doc/{0}/inspect\">{0}</a>", escape(n)),
            None => format!("{} (no held source reference)", short(id)),
        }
    };
    let mut body=format!("<p><a href=\"{base}/doc/{0}\">Read document</a> | <a href=\"{base}/doc/{0}/edit\">Edit and inspect law</a> | <a href=\"{base}/doc/{0}/history\">History and diffs</a></p><p>Document <code>{1}</code>; root <code>{2}</code>; root revision <code>{3}</code>.</p>",escape(name),escape(name),escape(rendered.root.as_str().unwrap_or("?")),escape(rendered.root_revision.as_str().unwrap_or("?")));
    body.push_str("<h2>Lines and exact source revisions</h2><table data-source-lines><tr><th>Line</th><th>Authored object</th><th>Current revision</th><th>Context</th></tr>");
    for line in &rendered.lines {
        let atom = line.row["atom"]
            .as_str()
            .or_else(|| line.row["transclusion"].as_str())
            .or_else(|| line.row["element"].as_str())
            .or_else(|| line.row["id"].as_str())
            .unwrap_or("");
        let entry = read
            .entries
            .iter()
            .find(|e| e["type"] == "atom" && e["id"].as_str() == Some(atom));
        let revision = entry.and_then(|e| e["revision"].as_str()).unwrap_or("—");
        let kind = match &line.body {
            Body::Text { struck, .. } => {
                if *struck {
                    "removed text"
                } else {
                    "text"
                }
            }
            Body::Object { .. } => "object",
            Body::Transclusion(_) => "quotation",
            Body::Section => "section",
        };
        body.push_str(&format!(
            "<tr><td>{}</td><td>{kind} <code>{}</code></td><td><code>{}</code></td><td>",
            line.line
                .map(|n| n.to_string())
                .unwrap_or_else(|| "—".into()),
            escape(atom),
            escape(revision)
        ));
        if let Body::Transclusion(t) = &line.body {
            body.push_str(&format!(
                "{}; {} quote; source state <strong>{}</strong>. {}",
                source_link(&t.source),
                escape(&t.mode),
                escape(&t.view),
                escape(&t.header)
            ));
        }
        for annotation in &line.annotations {
            body.push_str(&annotation_html(annotation));
        }
        body.push_str("</td></tr>");
    }
    body.push_str("</table><p class=note>Exact revisions come from signed raw entries. Historical alternatives stay in history; a stale comment keeps its authored anchor and is not silently moved onto replacement text.</p>");
    if !rendered.document_annotations.is_empty() {
        body.push_str("<h2>Document comments</h2>");
        for a in &rendered.document_annotations {
            body.push_str(&annotation_html(a));
        }
    }
    body.push_str("<h2>Published ranges and quote bindings</h2>");
    for (key, title) in [
        ("runs", "Published ranges"),
        ("transclusions", "Quote bindings"),
    ] {
        let rows = read.document[key].as_array().cloned().unwrap_or_default();
        body.push_str(&format!(
            "<details><summary>{title} ({})</summary>",
            rows.len()
        ));
        for row in rows {
            // Include immutable identity, endpoint policy and revision pins,
            // never the source render's payload bytes or opening key material.
            let mut metadata = serde_json::Map::new();
            for field in [
                "id", "source", "run", "from", "to", "mode", "at", "death", "start", "end",
                "policy", "opening",
            ] {
                if let Some(v) = row.get(field) {
                    if field == "opening" {
                        let mut opening = serde_json::Map::new();
                        for f in ["source", "run", "from", "to", "pins", "root", "height"] {
                            if let Some(v) = v.get(f) {
                                opening.insert(f.into(), v.clone());
                            }
                        }
                        metadata.insert(field.into(), Value::Object(opening));
                    } else {
                        metadata.insert(field.into(), v.clone());
                    }
                }
            }
            body.push_str(&format!(
                "<pre>{}</pre>",
                escape(&serde_json::to_string_pretty(&metadata).unwrap_or_default())
            ));
        }
        body.push_str("</details>");
    }
    body.push_str("<details><summary>Current rendered document</summary>");
    body.push_str(&rendered.html(name));
    body.push_str("</details>");
    Page {
        status: 200,
        title,
        stamp: Stamp::Read(ReadContext::of(&challenge, &read.view)),
        body,
    }
}
fn annotation_html(a: &Annotation) -> String {
    format!(
        "<p class=ann data-anchor-fresh=\"{}\"><strong>{}</strong> by {} <code>{}</code>: {}</p>",
        a.fresh,
        if a.fresh {
            "Comment on this revision"
        } else {
            "Comment on an earlier revision"
        },
        escape(&a.author),
        escape(&a.id),
        escape(&a.body)
    )
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn authored_alternative_keeps_stale_anchor_and_escapes() {
        let a = Annotation {
            id: "17".into(),
            author: "<member>".into(),
            fresh: false,
            body: "<replacement>".into(),
            key_wrapping: None,
        };
        let h = annotation_html(&a);
        assert!(h.contains("earlier revision"));
        assert!(h.contains("data-anchor-fresh=\"false\""));
        assert!(h.contains("&lt;replacement&gt;"));
        assert!(!h.contains("<member>"));
    }
}
