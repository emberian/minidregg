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
    format!("<form method=get action=\"{base}/search\"><label>Text <input name=query value=\"{}\" maxlength=256 required></label> <label>Documents <input name=scope value=\"{}\" required></label> <button>Search</button></form><p class=note>Use comma-separated document names, or @held for your held references. Four references per page. Searches current visible direct text; annotations, objects, history and transcluded text are outside this scope.</p>",escape(query),escape(scope))
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
    body.push_str(&format!("<p>Checked references {}–{} of {} in {} ms. Each document has its own signed current read; this is not a simultaneous world snapshot.</p><ul class=search-hits>",offset,result["through"],result["heldReferences"],result["elapsedMs"]));
    for hit in result["hits"].as_array().into_iter().flatten() {
        let name = hit["name"].as_str().unwrap_or("");
        let link = format!(
            "{base}/search-hit/{}/{}/{}/{}",
            crate::hex(name.as_bytes()),
            hit["target"].as_str().unwrap_or(""),
            hit["atom"].as_str().unwrap_or(""),
            hit["revision"].as_str().unwrap_or("")
        );
        body.push_str(&format!("<li><a href=\"{}\">{} · line {} · atom {} revision {}</a><blockquote>{}</blockquote></li>",escape(&link),escape(name),hit["line"],hit["atom"],hit["revision"],escape(hit["snippet"].as_str().unwrap_or(""))));
    }
    body.push_str("</ul><details open><summary>Coverage and unreadable references</summary><ul>");
    for doc in result["documents"].as_array().into_iter().flatten() {
        if doc["status"] == "read" {
            body.push_str(&format!("<li>{}: {} matching lines ({} shown); {} non-text or transcluded rows omitted; height {}.</li>",escape(doc["name"].as_str().unwrap_or("")),doc["matchingLines"],doc["returned"],doc["omittedNonTextOrTranscluded"],doc["height"]));
        } else {
            body.push_str(&format!(
                "<li>{}: unavailable — {}. This is not a no-match result.</li>",
                escape(doc["name"].as_str().unwrap_or("")),
                escape(doc["error"].as_str().unwrap_or("read failed"))
            ));
        }
    }
    body.push_str("</ul></details>");
    if let Some(next) = result["nextOffset"].as_u64() {
        body.push_str(&format!("<form method=get action=\"{base}/search\"><input type=hidden name=query value=\"{}\"><input type=hidden name=scope value=\"{}\"><input type=hidden name=offset value=\"{next}\"><input type=hidden name=cursor value=\"{}\"><button>Next four references</button></form>",escape(query),escape(scope),escape(result["collectionFingerprint"].as_str().unwrap_or(""))));
    }
    Page {
        status: 200,
        title: "Search documents".into(),
        stamp: Stamp::None,
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
    Page{status:200,title:format!("{} · atom {}",name,atom),stamp:Stamp::None,
        body:format!("<p>Fresh authorized read at height {}. Atom revision {}{}. Line {}.</p><pre>{}</pre><p><a href=\"{}/search\">Search again</a></p>",value["height"],value["revision"],if value["changed"]==true {" — changed since search"}else{""},value["line"],escape(value["text"].as_str().unwrap_or("")),site.base())}
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
