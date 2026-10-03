//! One renderer vocabulary for all authored Objective Bend surfaces. Input is
//! the canonical-decoder/native-projection result, never raw source JSON.
use super::*;
use std::collections::BTreeMap;

const MAX_EXPANSIONS: usize = 4096;
const MAX_DEPTH: usize = 64;
const MAX_HTML: usize = 2 * 1024 * 1024;

/// Operation links are built by the server's native custody adapter. Source
/// labels cannot supply URLs. An absent binding yields a disabled action.
pub(super) fn body(projected: &Value, operation_links: &BTreeMap<String, String>, mount: &str) -> Result<String> {
    if mount.is_empty() || mount.len() > 64 || !mount.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_')) {
        return Err("surface mount identifier is invalid".into());
    }
    let nodes = projected["nodes"].as_array().ok_or("surface projection has no nodes")?;
    let root = projected["root"].as_str().and_then(|v| v.parse::<usize>().ok())
        .filter(|i| *i < nodes.len()).ok_or("surface projection has no root")?;
    let mut renderer = Renderer { nodes, operation_links, mount, visited: BTreeSet::new(), expansions: 0, html: String::new() };
    renderer.html.push_str("<section data-authored-surface>");
    renderer.push(&format!("<p data-surface-origin>Source artifact <code>{}</code>, export <code>{}</code>.</p>",
        escape(projected["artifact"].as_str().unwrap_or("unavailable")),
        escape(projected["exportName"].as_str().unwrap_or("unavailable"))))?;
    renderer.node(root, 0)?;
    renderer.html.push_str("</section>");
    Ok(renderer.html)
}

struct Renderer<'a> {
    nodes: &'a [Value],
    operation_links: &'a BTreeMap<String, String>,
    mount: &'a str,
    visited: BTreeSet<usize>,
    expansions: usize,
    html: String,
}

impl Renderer<'_> {
    fn push(&mut self, value: &str) -> Result<()> {
        if self.html.len().checked_add(value.len()).is_none_or(|size| size > MAX_HTML) {
            return Err("authored surface exceeds rendered size bound".into());
        }
        self.html.push_str(value);
        Ok(())
    }

    fn node(&mut self, index: usize, depth: usize) -> Result<()> {
        self.expansions += 1;
        if depth > MAX_DEPTH || self.expansions > MAX_EXPANSIONS {
            return Err("authored surface exceeds traversal bound".into());
        }
        let node = self.nodes.get(index).ok_or("surface node is absent")?.clone();
        let label = node["label"].as_str().ok_or("surface node has no label")?;
        if !self.visited.insert(index) {
            return self.push(&format!("<a href=\"#surface-{}-node-{index}\">{}</a>", self.mount, escape(label)));
        }
        let tag = node["tag"].as_str().ok_or("surface node has no tag")?;
        self.push(&format!("<section id=\"surface-{}-node-{index}\" data-surface-node=\"{}\">", self.mount, escape(tag)))?;
        match tag {
            "0" => self.push(&format!("<p>{}</p>", escape(label)))?,
            "1" | "2" => {
                // Source revisions, unavailable states and any content-origin
                // evidence are retained as admitted data. No read is initiated.
                let observation = node.get("observation").ok_or("surface observation was not admitted")?;
                self.push(&format!("<details open data-surface-observation><summary>{}</summary><pre>{}</pre></details>",
                    escape(label), escape(&serde_json::to_string_pretty(observation).map_err(|e| e.to_string())?)))?;
            }
            "3" => {
                let operation = &node["operation"];
                let id = operation["id"].as_str().filter(|id| id.len() == 32 && id.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)));
                let route = id.and_then(|id| self.operation_links.get(id))
                    .filter(|route| route.starts_with('/') && !route.starts_with("//") && !route.chars().any(|c| matches!(c, '\r' | '\n' | '\0')));
                if node["state"] == "prepared" {
                    if let Some(route) = route {
                        self.push(&format!("<a data-native-intent href=\"{}\">Review {}</a>", escape(route), escape(label)))?;
                    } else {
                        self.push(&format!("<button disabled>{}</button><p class=note>Native preparation has no review route in this session.</p>", escape(label)))?;
                    }
                } else {
                    self.push(&format!("<button disabled>{}</button><p class=note>This action has not been prepared under your current authority.</p>", escape(label)))?;
                }
            }
            "4" => self.push(&format!("<h2>{}</h2>", escape(label)))?,
            _ => return Err("surface node tag is unknown".into()),
        }
        let children = node["children"].as_array().ok_or("surface children are absent")?
            .iter().map(|child| child.as_str().and_then(|v| v.parse::<usize>().ok())
                .filter(|child| *child < index).ok_or_else(|| "surface child does not precede parent".to_owned()))
            .collect::<Result<Vec<_>>>()?;
        for child in children { self.node(child, depth + 1)?; }
        self.push("</section>")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    #[test]
    fn source_cannot_inject_markup_or_enable_missing_native_intent() {
        let source = json!({"root":"2","nodes":[
            {"tag":"0","label":"<script>alert(1)</script>","children":[]},
            {"tag":"3","label":"Publish","state":"unprepared","operation":{"id":"a".repeat(32)},"children":[]},
            {"tag":"4","label":"Workshop","children":["0","1"]}]});
        let routes = BTreeMap::from([("a".repeat(32), "/launch/review/native-id".into())]);
        let page = body(&source, &routes, "first").unwrap();
        assert!(page.contains("&lt;script&gt;"));
        assert!(!page.contains("<script>"));
        assert!(!page.contains("data-native-intent"));
        assert!(page.contains("<button disabled>Publish"));
        assert!(body(&source, &routes, "invalid/mount").is_err());
    }
    #[test]
    fn shared_children_do_not_expand_exponentially() {
        let mut nodes = vec![json!({"tag":"0","label":"shared","children":[]})];
        for n in 1..100 { nodes.push(json!({"tag":"4","label":"group","children":[(n-1).to_string(),(n-1).to_string()]})); }
        // Deep graphs refuse predictably; shallow shared graphs render once.
        assert!(body(&json!({"root":"99","nodes":nodes}), &BTreeMap::new(), "first").is_err());
        let source = json!({"root":"2","nodes":[
            {"tag":"0","label":"shared","children":[]},
            {"tag":"4","label":"group1","children":["0","0"]},
            {"tag":"4","label":"group2","children":["1","1"]}]});
        let page = body(&source, &BTreeMap::new(), "first").unwrap();
        assert_eq!(page.matches("<p>shared</p>").count(), 1);
        assert!(page.contains("href=\"#surface-first-node-1\""));
        let second = body(&source, &BTreeMap::new(), "second").unwrap();
        assert!(second.contains("href=\"#surface-second-node-1\""));
        assert!(!second.contains("surface-first-node"));
    }
}
