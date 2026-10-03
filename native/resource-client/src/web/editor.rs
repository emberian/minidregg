//! Server-rendered editing and inspection, under the web launch secret.
//! Forms use the native client's pinned document diff and durable attempt.

use super::*;
use crate::workspace::web_author::{self, Edit};
use std::collections::BTreeMap;

pub(super) const MAX_FORM: usize = 3 * 64 * 1024 + 64;

/// POST has a stricter boundary than browsing: an exact same-origin Origin,
/// one bounded Content-Length, one form content type, no transfer coding.
pub(super) fn body_length(request: &Request) -> Result<usize> {
    let one = |key: &str| -> Result<&str> {
        let values: Vec<_> = request.headers.iter().filter(|(k, _)| k == key).collect();
        if values.len() != 1 {
            return Err(format!("expected exactly one {key} header"));
        }
        Ok(values[0].1.as_str())
    };
    if request
        .headers
        .iter()
        .any(|(k, _)| k == "transfer-encoding")
    {
        return Err("transfer encoding is not supported".into());
    }
    let host = one("host")?;
    if one("origin")? != format!("http://{host}") {
        return Err("saving requires this page's exact origin".into());
    }
    if one("content-type")? != "application/x-www-form-urlencoded" {
        return Err("expected a document form".into());
    }
    let length = one("content-length")?;
    if length.is_empty() || !length.bytes().all(|b| b.is_ascii_digit()) {
        return Err("invalid content length".into());
    }
    let length = length
        .parse::<usize>()
        .map_err(|_| "invalid content length")?;
    if length > MAX_FORM {
        return Err("document form is too large".into());
    }
    Ok(length)
}

pub(super) fn form(bytes: &[u8]) -> Result<BTreeMap<String, String>> {
    fn decode(bytes: &[u8]) -> Result<String> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < bytes.len() {
            match bytes[i] {
                b'+' => out.push(b' '),
                b'%' => {
                    let pair = bytes.get(i + 1..i + 3).ok_or("incomplete form escape")?;
                    let pair = std::str::from_utf8(pair).map_err(|_| "invalid form escape")?;
                    out.push(u8::from_str_radix(pair, 16).map_err(|_| "invalid form escape")?);
                    i += 2;
                }
                b => out.push(b),
            }
            i += 1;
        }
        String::from_utf8(out).map_err(|_| "form text is not UTF-8".into())
    }
    if bytes.len() > MAX_FORM {
        return Err("document form is too large".into());
    }
    let mut result = BTreeMap::new();
    if bytes.is_empty() {
        return Ok(result);
    }
    for pair in bytes.split(|b| *b == b'&') {
        let split = pair
            .iter()
            .position(|b| *b == b'=')
            .ok_or("invalid form field")?;
        let name = decode(&pair[..split])?;
        if result.insert(name, decode(&pair[split + 1..])?).is_some() {
            return Err("duplicate form field".into());
        }
    }
    Ok(result)
}

pub(super) fn open(site: &Site, name: &str, id: Option<&str>) -> Page {
    let edit = match id {
        Some(id) => web_author::load(&site.root, &site.workspace, name, id),
        None => web_author::open(&site.root, &site.workspace, name),
    };
    match edit {
        Ok(edit) => render(site, &edit),
        Err(error) => failure_page(&format!("Edit {name}"), &error),
    }
}

pub(super) fn post(site: &Site, name: &str, id: &str, body: &[u8], lookup: bool) -> Page {
    let mut fields = match form(body) {
        Ok(fields) => fields,
        Err(error) => return simple(400, "Cannot save", &error),
    };
    if lookup {
        if !fields.is_empty() {
            return simple(400, "Cannot check save", "unexpected form fields");
        }
        return match web_author::lookup(&site.root, &site.workspace, name, id) {
            Ok(edit) => render(site, &edit),
            Err(error) => failure_page("Check save", &error),
        };
    }
    if fields.len() != 1 || !fields.contains_key("text") {
        return simple(400, "Cannot save", "expected only document text");
    }
    // Browser textarea submission canonicalizes line breaks to CRLF. Mini's
    // document editor uses LF; do this conversion only at the form boundary.
    let text = fields.remove("text").unwrap().replace("\r\n", "\n");
    match web_author::submit(&site.root, &site.workspace, name, id, &text) {
        Ok(edit) => render(site, &edit),
        Err(error) => match web_author::load(&site.root, &site.workspace, name, id) {
            Ok(mut edit) => {
                edit.text = text;
                edit.message = format!("This draft was not saved: {error}");
                let mut page = render(site, &edit);
                page.status = 400;
                page
            }
            Err(_) => Page {
                status: 400,
                title: "Draft not saved".into(),
                stamp: Stamp::None,
                body: format!(
                    "<p class=refusal>{}</p><label>Your draft<textarea>\n{}</textarea></label>",
                    escape(&error),
                    escape(&text)
                ),
            },
        },
    }
}

fn display(value: &Value) -> String {
    value
        .as_str()
        .map(str::to_owned)
        .unwrap_or_else(|| value.to_string())
}

fn predicate_html(predicate: &Value, depth: usize) -> String {
    if depth > 32 {
        return "<p>Nested law: inspect the full definition below.</p>".into();
    }
    let kind = predicate["type"].as_str().unwrap_or("");
    if matches!(kind, "all" | "any") {
        if let Some(children) = predicate["predicates"].as_array() {
            return format!(
                "<p>{}</p><ul>{}</ul>",
                if kind == "all" {
                    "All of these conditions"
                } else {
                    "Any of these conditions"
                },
                children
                    .iter()
                    .map(|p| format!("<li>{}</li>", predicate_html(p, depth + 1)))
                    .collect::<String>()
            );
        }
    }
    let slot = predicate["slot"].as_str().unwrap_or("");
    let label = match slot {
        "request/verb" => "Operation",
        "content/payload-bytes/after" => "Document payload bytes after this turn",
        other => other,
    };
    let value = |v: &Value| -> String {
        if slot == "request/verb" {
            match v.as_str() {
                Some("1") => "read".into(),
                Some("2") => "edit".into(),
                Some("3") => "delegate".into(),
                Some("4") => "change law".into(),
                Some("5") => "revoke grant".into(),
                _ => display(v),
            }
        } else {
            display(v)
        }
    };
    match kind {
        "eq" | "le" | "lt" | "ge" | "gt" => format!(
            "<p>{} {} <code>{}</code></p>",
            escape(label),
            match kind {
                "eq" => "=",
                "le" => "≤",
                "lt" => "&lt;",
                "ge" => "≥",
                _ => "&gt;",
            },
            escape(&value(&predicate["value"]))
        ),
        "memberOf" if predicate["values"].is_array() => format!(
            "<p>{} is one of: {}</p>",
            escape(label),
            predicate["values"]
                .as_array()
                .unwrap()
                .iter()
                .map(|v| escape(&value(v)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        _ => format!(
            "<pre>{}</pre>",
            escape(&serde_json::to_string_pretty(predicate).unwrap_or_default())
        ),
    }
}

/// An action shares the editor's one durable operation identity.
pub(super) fn action(site: &Site, name: &str, id: &str, body: &[u8]) -> Page {
    let fields = match form(body) {
        Ok(fields) => fields,
        Err(error) => return simple(400, "Cannot connect", &error),
    };
    let value = Value::Object(
        fields
            .into_iter()
            .map(|(k, v)| (k, Value::String(v.replace("\r\n", "\n"))))
            .collect(),
    );
    match web_author::submit_action(&site.root, &site.workspace, name, id, &value) {
        Ok(edit) => render(site, &edit),
        Err(error) => match web_author::load(&site.root, &site.workspace, name, id) {
            Ok(mut edit) => {
                edit.message = format!("This action was not submitted: {error}");
                edit.action = Some(value);
                let mut page = render(site, &edit);
                page.status = 400;
                page
            }
            Err(_) => failure_page("Cannot connect", &error),
        },
    }
}

fn connections(url: &str) -> String {
    let target = format!("{url}/action");
    format!("<section data-document-connections><h2>Connect knowledge</h2>\
        <details><summary>Comment on a line</summary><form method=post action=\"{target}\">\
        <input type=hidden name=type value=annotate><label>Line <input name=line type=number min=1 required></label>\
        <label>Comment <textarea name=text maxlength=4096 required></textarea></label><button>Add comment</button></form></details>\
        <details><summary>Publish a source range</summary><form method=post action=\"{target}\">\
        <input type=hidden name=type value=range><label>First line <input name=from type=number min=1 required></label>\
        <label>Last line <input name=to type=number min=1 required></label><button>Publish range</button></form></details>\
        <details><summary>Quote a published range</summary><form method=post action=\"{target}\">\
        <input type=hidden name=type value=transclude><label>Source reference <input name=source required></label>\
        <label>First source line <input name=from type=number min=1 required></label>\
        <label>Last source line <input name=to type=number min=1 required></label>\
        <label>Meaning <select name=mode><option value=snapshot>Pinned quote</option><option value=live>Live transclusion</option></select></label>\
        <label>If an endpoint disappears <select name=death><option value=invalidate>Show unavailable</option>\
        <option value=keepTombstone>Keep its place</option><option value=preferPrevious>Follow previous</option>\
        <option value=preferNext>Follow next</option></select></label><button>Insert quote</button></form>\
        <p>Publish the range in the source first. Opening this quote always asks for the reader's own source access.</p></details>\
        <details><summary>Link another resource</summary><form method=post action=\"{target}\">\
        <input type=hidden name=type value=link><label>Target reference <input name=to required></label>\
        <input type=hidden name=relation value=0><button>Add link</button></form></details></section>")
}

fn inspector(site: &Site, name: &str) -> String {
    let mut out = String::from("<aside class=inspector><h2>Inspect this document</h2>");
    let reference = match workspace::reference(&site.root, name) {
        Ok(reference) => reference,
        Err(error) => return format!("{out}<p>{}</p></aside>", escape(&error)),
    };
    out.push_str(&format!(
        "<p>Cell <code>{}</code></p>",
        escape(reference["target"].as_str().unwrap_or("?"))
    ));
    out.push_str("<h3>Current law</h3>");
    match site.read(&reference, "policy") {
        Ok((policy, challenge, _)) => {
            out.push_str(&format!(
                "<p class=note>Read at height {}</p>",
                escape(challenge["height"].as_str().unwrap_or("?"))
            ));
            out.push_str(&predicate_html(&policy["predicate"], 0));
            out.push_str(&format!(
                "<details><summary>Full signed law record</summary><pre>{}</pre></details>",
                escape(&serde_json::to_string_pretty(&policy).unwrap_or_default())
            ));
        }
        Err(error) => out.push_str(&format!(
            "<p>{}</p>",
            escape(&refusal_text(&error).unwrap_or(error))
        )),
    }
    out.push_str("<h3>Your grants</h3><ul>");
    for (slot, label) in [
        ("observeCapability", "Read"),
        ("operationCapability", "Edit and delegate"),
        ("controlCapability", "Manage law and grants"),
    ] {
        let Some(id) = reference[slot].as_str() else {
            continue;
        };
        let mut selected = reference.clone();
        selected["observeCapability"] = Value::String(id.into());
        out.push_str(&format!(
            "<li><strong>{label}</strong> <code>{}</code>",
            escape(id)
        ));
        match site.read(&selected, "capability") {
            Ok((cap, challenge, _)) => {
                let head = &cap["head"];
                let verbs = head["verbs"]
                    .as_array()
                    .map(|xs| xs.iter().map(display).collect::<Vec<_>>().join(", "))
                    .unwrap_or_default();
                out.push_str(&format!("<p>{}</p><p class=note>Read at height {}</p><details><summary>Scope and limits</summary><pre>{}</pre></details>",
                    escape(&verbs),escape(challenge["height"].as_str().unwrap_or("?")),escape(&serde_json::to_string_pretty(head).unwrap_or_default())));
            }
            Err(error) => out.push_str(&format!(
                "<p class=note>Grant details unavailable: {}. Saving asks the current law.</p>",
                escape(&refusal_text(&error).unwrap_or(error))
            )),
        }
        out.push_str("</li>");
    }
    out.push_str(&format!("</ul><h3>History</h3><p><a href=\"{}/doc/{}/history\">Browse changes and earlier versions</a></p>",site.base(),escape(name)));
    match web_author::recent_turns(&site.root, &site.workspace, name) {
        Ok(rows) => {
            out.push_str("<ol data-recent-turns>");
            for row in rows {
                let h = row["height"].as_str().unwrap_or("?");
                out.push_str(&format!(
                    "<li>Height <a href=\"{}/at/{}/doc/{}\">{}</a> · subject <code>{}</code>",
                    site.base(),
                    escape(h),
                    escape(name),
                    escape(h),
                    escape(row["subject"].as_str().unwrap_or("?"))
                ));
                if let Some(before) = h.parse::<u64>().ok().and_then(|h| h.checked_sub(1)) {
                    out.push_str(&format!(
                        " · <a href=\"{}/doc/{}/diff/{}/{}\">changes</a>",
                        site.base(),
                        escape(name),
                        before,
                        escape(h)
                    ));
                }
                out.push_str("</li>");
            }
            out.push_str("</ol><p class=note>Recent turns visible to your current grant. Open a turn to read its historical content.</p>");
        }
        Err(error) => out.push_str(&format!(
            "<p>{}</p>",
            escape(&refusal_text(&error).unwrap_or(error))
        )),
    }
    out.push_str("</aside>");
    out
}

fn render(site: &Site, edit: &Edit) -> Page {
    let base = site.base();
    let name = escape(&edit.name);
    let url = format!("{base}/doc/{name}/edit/{}", edit.id);
    let terminal = matches!(
        edit.status.as_str(),
        "saved" | "unchanged" | "refused" | "failed"
    );
    let mut body = format!("<style>.editing{{display:grid;grid-template-columns:minmax(0,2fr) minmax(16rem,1fr);gap:2rem}}body{{max-width:90rem}}textarea{{display:block;box-sizing:border-box;width:100%;min-height:22rem;font:15px/1.6 ui-monospace,monospace;padding:1rem}}button{{padding:.6rem 1rem;margin:.5rem 0;font:inherit}}.inspector{{border-left:1px solid #ddd;padding-left:1rem}}pre{{white-space:pre-wrap;overflow-wrap:anywhere}}code{{overflow-wrap:anywhere}}details{{margin:.5rem 0}}@media(max-width:800px){{.editing{{display:block}}.inspector{{border:0;padding:0}}}}</style>\
        <p><a href=\"{base}/doc/{name}\">Read current document</a> · <a href=\"{url}\">Permalink to this draft and save</a></p>\
        <div class=editing><section><p class=note>Editing the document as read at height {}. Unchanged transclusion markers preserve their source links.</p>",escape(&edit.height));
    if !edit.message.is_empty() {
        body.push_str(&format!(
            "<p role=status data-save-status=\"{}\" class=\"{}\">{}</p>",
            escape(&edit.status),
            if edit.status == "saved" {
                "saved"
            } else {
                "note"
            },
            escape(&edit.message)
        ));
    }
    if let Some(action) = &edit.action {
        body.push_str(&format!("<details open data-authored-action><summary>Retained authored action</summary><pre>{}</pre></details>",
            escape(&serde_json::to_string_pretty(action).unwrap_or_default())));
    }
    if let Some(outcome) = &edit.outcome {
        body.push_str("<dl data-write-receipt>");
        for (key, label) in [
            ("confirmation", "Result"),
            ("transactionId", "Transaction"),
            ("eventId", "Event"),
            ("height", "Height"),
            ("acceptedCount", "Accepted count"),
        ] {
            if let Some(value) = outcome.get(key) {
                body.push_str(&format!(
                    "<dt>{label}</dt><dd><code>{}</code></dd>",
                    escape(&display(value))
                ));
            }
        }
        body.push_str("</dl>");
    }
    body.push_str(&format!("<form method=post action=\"{url}\"><label>Document text<textarea name=text spellcheck=true {}>\n{}</textarea></label>",
        if matches!(edit.status.as_str(),"saved"|"unchanged"|"uncertain") {"readonly"} else {""},escape(&edit.text)));
    if edit.status == "editing" {
        body.push_str("<button type=submit>Save document</button>");
    }
    body.push_str("</form>");
    if edit.status == "uncertain" {
        body.push_str(&format!("<form method=post action=\"{url}/lookup\"><button>Check this save's exact outcome</button></form>"));
    }
    if terminal {
        body.push_str(&format!("<p><a href=\"{base}/doc/{name}/edit\">Open the current version for another edit</a>. This draft remains here for copying and comparison.</p>"));
    }
    if edit.status == "editing" {
        body.push_str(&connections(&url));
    }
    body.push_str(&edit.structure);
    body.push_str(&format!("<details><summary>Rendered version at the start of this edit</summary>{}</details></section>",edit.preview));
    body.push_str(&inspector(site, &edit.name));
    body.push_str("</div>");
    Page {
        status: 200,
        title: format!("Edit {}", edit.name),
        stamp: Stamp::EditBase(ReadContext {
            height: edit.height.clone(),
            authority_root: edit.authority_root.clone(),
            cell_root: edit.cell_root.clone(),
        }),
        body,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn post(headers: &[(&str, &str)]) -> Request {
        Request {
            method: "POST".into(),
            target: "/s/doc/a/edit/e".into(),
            headers: headers
                .iter()
                .map(|(a, b)| (a.to_string(), b.to_string()))
                .collect(),
        }
    }
    #[test]
    fn save_requires_exact_origin_and_unambiguous_bounded_body() {
        let good = [
            ("host", "127.0.0.1:3"),
            ("origin", "http://127.0.0.1:3"),
            ("content-type", "application/x-www-form-urlencoded"),
            ("content-length", "9"),
        ];
        assert_eq!(body_length(&post(&good)).unwrap(), 9);
        for key in ["origin", "host", "content-length", "content-type"] {
            let missing: Vec<_> = good.iter().copied().filter(|(k, _)| *k != key).collect();
            assert!(body_length(&post(&missing)).is_err());
            let mut duplicate = good.to_vec();
            duplicate.push(*good.iter().find(|(k, _)| *k == key).unwrap());
            assert!(body_length(&post(&duplicate)).is_err());
        }
        let mut evil = good;
        evil[1].1 = "http://localhost:3";
        assert!(body_length(&post(&evil)).is_err());
        let mut encoded = good.to_vec();
        encoded.push(("transfer-encoding", "chunked"));
        assert!(body_length(&post(&encoded)).is_err());
        let mut huge = good;
        huge[3].1 = "196673";
        assert!(body_length(&post(&huge)).is_err());
    }
    #[test]
    fn connection_forms_use_the_same_durable_editor_action_route() {
        let html = connections("/secret/doc/paper/edit/0123");
        assert_eq!(
            html.matches("action=\"/secret/doc/paper/edit/0123/action\"")
                .count(),
            4
        );
        assert!(html.contains("value=snapshot"));
        assert!(html.contains("value=live"));
        assert!(html.contains("value=annotate"));
        assert!(!html.contains("script"));
    }
    #[test]
    fn forms_preserve_text_and_refuse_duplicate_or_invalid_fields() {
        assert_eq!(
            form(b"text=a%26b%3Dc+%F0%9F%90%88%0D%0A").unwrap()["text"],
            "a&b=c 🐈\r\n"
        );
        for bad in [
            b"text=a&text=b".as_slice(),
            b"text=%",
            b"text=%ff",
            b"text=%xz",
            b"text",
        ] {
            assert!(form(bad).is_err());
        }
    }
}
