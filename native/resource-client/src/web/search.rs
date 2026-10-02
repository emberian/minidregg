//! Search is an explicit submitted form, never an automatic keystroke scan.
use super::*;
use crate::workspace::doc_search;
use std::collections::BTreeMap;

fn decode(value: &str) -> Result<String> {
    let mut bytes = Vec::new();
    let mut input = value.bytes();
    while let Some(c) = input.next() {
        match c {
            b'+' => bytes.push(b' '),
            b'%' => {
                let a = input.next().ok_or("bad percent escape")?;
                let b = input.next().ok_or("bad percent escape")?;
                let hex = std::str::from_utf8(&[a, b])
                    .map_err(|_| "bad percent escape")?
                    .to_owned();
                bytes.push(u8::from_str_radix(&hex, 16).map_err(|_| "bad percent escape")?);
            }
            _ => bytes.push(c),
        }
    }
    String::from_utf8(bytes).map_err(|_| "form is not UTF-8".into())
}
fn fields(target: &str) -> Result<BTreeMap<String, String>> {
    let mut out = BTreeMap::new();
    if let Some((_, query)) = target.split_once('?') {
        if query.len() > 8192 {
            return Err("search request is too large".into());
        }
        for pair in query.split('&').filter(|s| !s.is_empty()) {
            let (key, value) = pair.split_once('=').ok_or("invalid search form")?;
            let key = decode(key)?;
            if !matches!(key.as_str(), "query" | "scope" | "offset" | "cursor")
                || out.insert(key, decode(value)?).is_some()
            {
                return Err("unknown or repeated search field".into());
            }
        }
    }
    Ok(out)
}
fn form(base: &str, query: &str, scope: &str) -> String {
    format!("<form method=get action=\"{base}/search\"><label>Text <input name=query value=\"{}\" maxlength=256 required></label> <label>Documents <input name=scope value=\"{}\" required></label> <button>Search</button></form><p class=note>Enter document names separated by commas, or @held for your collection. Up to four per page.</p><p class=note>Searches visible document text. Annotations, objects, history and embedded quotations are not included.</p>",escape(query),escape(scope))
}
fn text(value: &Value) -> String {
    value
        .as_str()
        .map(str::to_owned)
        .unwrap_or_else(|| value.to_string())
}
fn details(value: &Value) -> String {
    let mut rows = String::new();
    for (label, field) in [
        ("Document", "target"),
        ("Atom", "atom"),
        ("Revision", "revision"),
        ("Read height", "height"),
        ("World root", "worldRoot"),
    ] {
        rows.push_str(&format!(
            "<dt>{label}</dt><dd class=id style=\"overflow-wrap:anywhere\">{}</dd>",
            escape(&text(&value[field]))
        ));
    }
    format!(
        "<details class=search-details><summary>Read details</summary><dl>{rows}</dl></details>"
    )
}
pub(super) fn page(site: &Site, target: &str) -> Page {
    let base = site.base();
    let fields = match fields(target) {
        Ok(v) => v,
        Err(e) => return simple(400, "Search", &e),
    };
    let query = fields.get("query").map(String::as_str).unwrap_or("");
    let scope = fields.get("scope").map(String::as_str).unwrap_or("@held");
    let mut body = form(&base, query, scope);
    if query.is_empty() {
        return Page {
            status: 200,
            title: "Search documents".into(),
            stamp: Stamp::None,
            body,
        };
    }
    let offset = match fields.get("offset").map(|s| s.parse::<usize>()).transpose() {
        Ok(v) => v.unwrap_or(0),
        Err(_) => return simple(400, "Search", "invalid offset"),
    };
    let result = match doc_search::search(
        &site.root,
        &site.workspace,
        query,
        scope,
        offset,
        fields.get("cursor").map(String::as_str),
    ) {
        Ok(v) => v,
        Err(e) => return simple(400, "Search", &e),
    };
    let documents = result["documents"]
        .as_array()
        .map(Vec::as_slice)
        .unwrap_or(&[]);
    let readable = documents
        .iter()
        .filter(|doc| doc["status"] == "read")
        .count();
    let hits = result["hits"].as_array().map(Vec::as_slice).unwrap_or(&[]);
    body.push_str(&format!(
        "<p>{} matching {} · {} of {} selected documents searched.</p>",
        hits.len(),
        if hits.len() == 1 { "line" } else { "lines" },
        readable,
        documents.len()
    ));
    if readable < documents.len() {
        body.push_str(
            "<p>Some documents could not be read. Results cover the readable documents only.</p>",
        );
    }
    if result["hitsTruncated"] == true {
        body.push_str("<p>Showing the first 100 matching lines from each document.</p>");
    }
    body.push_str("<ul class=search-hits>");
    for hit in hits {
        let name = hit["name"].as_str().unwrap_or("");
        let link = format!(
            "{base}/search-hit/{}/{}/{}/{}",
            crate::hex(name.as_bytes()),
            hit["target"].as_str().unwrap_or(""),
            hit["atom"].as_str().unwrap_or(""),
            hit["revision"].as_str().unwrap_or("")
        );
        body.push_str(&format!(
            "<li><a href=\"{}\">{} · line {}</a><blockquote>{}</blockquote>{}</li>",
            escape(&link),
            escape(name),
            escape(&text(&hit["line"])),
            escape(hit["snippet"].as_str().unwrap_or("")),
            details(hit)
        ));
    }
    body.push_str("</ul><details><summary>Search coverage</summary><ul>");
    for doc in documents {
        if doc["status"] == "read" {
            body.push_str(&format!(
                "<li>{}: {} matching lines; {} shown. Read height {}.</li>",
                escape(doc["name"].as_str().unwrap_or("")),
                doc["matchingLines"],
                doc["returned"],
                escape(&text(&doc["height"]))
            ));
        } else {
            body.push_str(&format!(
                "<li>{}: unavailable.<details><summary>Why?</summary><p>{}</p></details></li>",
                escape(doc["name"].as_str().unwrap_or("")),
                escape(doc["error"].as_str().unwrap_or("read failed"))
            ));
        }
    }
    body.push_str(&format!("</ul><p>References {}–{} of {}. Search took {} ms. Documents were read independently with your current access.</p></details>",
        if documents.is_empty() { offset } else { offset+1 }, result["through"], result["heldReferences"], result["elapsedMs"]));
    if let Some(next) = result["nextOffset"].as_u64() {
        body.push_str(&format!("<form method=get action=\"{base}/search\"><input type=hidden name=query value=\"{}\"><input type=hidden name=scope value=\"{}\"><input type=hidden name=offset value=\"{next}\"><input type=hidden name=cursor value=\"{}\"><button>Next four references</button></form>",escape(query),escape(scope),escape(result["collectionFingerprint"].as_str().unwrap_or(""))));
    }
    Page {
        status: 200,
        title: "Search documents".into(),
        stamp: Stamp::CurrentReads(readable),
        body,
    }
}
pub(super) fn hit(site: &Site, name: &str, target: &str, atom: &str, revision: &str) -> Page {
    let name = match crate::decode_hex(name)
        .and_then(|v| String::from_utf8(v).map_err(|_| "invalid name".into()))
    {
        Ok(v) => v,
        Err(e) => return simple(400, "Search hit", &e),
    };
    let value = match doc_search::follow(&site.root, &site.workspace, &name, target, atom, revision)
    {
        Ok(v) => v,
        Err(e) => return simple(403, "Search hit unavailable", &e),
    };
    let line = text(&value["line"]);
    let mut body = format!(
        "<article class=search-hit><p style=\"white-space:pre-wrap\">{}</p></article>",
        escape(value["text"].as_str().unwrap_or(""))
    );
    if value["changed"] == true {
        body.push_str("<p class=note>This line changed since your search. You are reading its current text.</p>");
    }
    if workspace::validate_name(&name).is_ok() {
        body.push_str(&format!(
            "<p><a href=\"{}/doc/{}\">Open surrounding document</a></p>",
            site.base(),
            escape(&name)
        ));
    }
    body.push_str(&details(&value));
    body.push_str(&format!(
        "<p><a href=\"{}/search\">Search again</a></p>",
        site.base()
    ));
    Page {
        status: 200,
        title: format!("{} · line {}", name, line),
        stamp: Stamp::CurrentReads(1),
        body,
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn submitted_form_preserves_unicode_and_rejects_ambiguity() {
        let parsed =
            fields("/secret/search?query=caf%C3%A9+notes&scope=paper%2Clab%2Findex").unwrap();
        assert_eq!(parsed["query"], "café notes");
        assert_eq!(parsed["scope"], "paper,lab/index");
        for bad in [
            "/?query=a&query=b",
            "/?scope=%GG",
            "/?unknown=x",
            "/?query=%FF",
        ] {
            assert!(fields(bad).is_err());
        }
    }
}
