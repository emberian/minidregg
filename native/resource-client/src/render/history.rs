//! History and diff, rendered once: `doc history`, `doc diff` (text, json,
//! html) and the web's `/doc/NAME/history` and `/doc/NAME/diff/H1/H2` share
//! these.  Input is the Host's `view-history` / `view-diff` (K-DOC-HISTORY:
//! `DocumentHistory.diff` over two `view-document` line lists, keyed by element,
//! moves named).  A page at a past height is `doc show --at H`: `render` itself.

use super::html::escape;
use serde_json::Value;

/// A line's payload as text (lossy); a payload that is not hex says so.
fn payload_text(hex: &str) -> String {
    let bytes: Option<Vec<u8>> = (hex.len() % 2 == 0)
        .then(|| (0..hex.len()).step_by(2).map(|i| u8::from_str_radix(&hex[i..i + 2], 16).ok()).collect())
        .flatten();
    match bytes {
        Some(bytes) => String::from_utf8_lossy(&bytes).into_owned(),
        None => format!("<payload {hex}>"),
    }
}

/// One side of a change: an atom's text, a transclusion, a section.
fn side(value: &Value) -> String {
    match value["kind"].as_str() {
        Some("atom") => format!(
            "\"{}\"{}",
            payload_text(value["payload"].as_str().unwrap_or("")),
            if value["struck"] == true { " (struck)" } else { "" }
        ),
        Some("embed") => format!("transclusion {}", value["transclusion"].as_str().unwrap_or("?")),
        Some("container") => "section".to_owned(),
        Some(other) => other.to_owned(),
        None => "?".to_owned(),
    }
}

/// One change as a line: `+ E …`, `- E …`, `~ E … -> …`, `moved E: after X -> after Y`.
pub fn change_line(change: &Value) -> String {
    let element = change["element"].as_str().unwrap_or("?");
    match change["type"].as_str() {
        Some("added") => format!("+ {element} {}", side(&change["after"])),
        Some("removed") => format!("- {element} {}", side(&change["before"])),
        Some("changed") => format!("~ {element} {} -> {}", side(&change["before"]), side(&change["after"])),
        Some("moved") => {
            let after = |value: &Value| value.as_str().unwrap_or("the start").to_owned();
            format!("moved {element}: after {} -> after {}", after(&change["before"]), after(&change["after"]))
        }
        _ => change.to_string(),
    }
}

const NOT_COVERED: &str = "content not shown: your grant did not cover this document at that height";

/// `doc diff`: the heights, then one line per change.
pub fn diff_text(diff: &Value) -> String {
    let mut out = format!(
        "# changes from height {} to height {}\n",
        diff["from"]["height"].as_str().unwrap_or("?"),
        diff["to"]["height"].as_str().unwrap_or("?")
    );
    match diff["changes"].as_array() {
        Some(changes) if changes.is_empty() => out.push_str("(no change)\n"),
        Some(changes) => changes.iter().for_each(|change| {
            out.push_str(&change_line(change));
            out.push('\n');
        }),
        None => out.push_str(&format!("({NOT_COVERED})\n")),
    }
    out
}

/// `doc history`: one row per signed write of the document (height, subject,
/// transaction), its changes indented under it where the grant stood.
pub fn history_text(history: &Value) -> String {
    let rows = history["rows"].as_array().cloned().unwrap_or_default();
    let mut out = format!("# history: {} write(s)\n", rows.len());
    for row in &rows {
        out.push_str(&format!(
            "{}  subject {}  transaction {}\n",
            row["height"].as_str().unwrap_or("?"),
            row["subject"].as_str().unwrap_or("-"),
            row["transaction"].as_str().unwrap_or("?")
        ));
        match row["changes"].as_array() {
            Some(changes) if changes.is_empty() => out.push_str("    (no change)\n"),
            Some(changes) => changes.iter().for_each(|change| {
                out.push_str("    ");
                out.push_str(&change_line(change));
                out.push('\n');
            }),
            None => out.push_str(&format!("    ({NOT_COVERED})\n")),
        }
    }
    out
}

/// The changes of one row or one diff as HTML: `data-change` / `data-element`
/// on each item; `null` changes (the grant did not stand) say so.
pub fn changes_html(changes: &Value) -> String {
    match changes.as_array() {
        Some(changes) if changes.is_empty() => "<p class=note>no change</p>".to_owned(),
        Some(changes) => {
            let mut out = format!("<ul data-changes=\"{}\">", changes.len());
            for change in changes {
                out.push_str(&format!(
                    "<li data-change=\"{}\" data-element=\"{}\">{}</li>",
                    escape(change["type"].as_str().unwrap_or("?")),
                    escape(change["element"].as_str().unwrap_or("?")),
                    escape(&change_line(change))
                ));
            }
            out.push_str("</ul>");
            out
        }
        None => format!("<p class=note data-no-content>{NOT_COVERED}</p>"),
    }
}

/// The history as an HTML table.  `links(height)` is what the caller puts
/// after a row's height (the web face's `show` / `diff` routes; nothing for
/// `doc history --format html`): routes are the web face's, not the renderer's.
pub fn history_html(history: &Value, links: &dyn Fn(&str) -> String) -> String {
    let rows = history["rows"].as_array().cloned().unwrap_or_default();
    let mut out = format!(
        "<section class=\"history\"><table data-history=\"{}\"><tr><th>height</th><th>subject</th>\
         <th>transaction</th><th>changes</th></tr>\n",
        rows.len()
    );
    for row in &rows {
        let height = row["height"].as_str().unwrap_or("?");
        out.push_str(&format!(
            "<tr data-row=\"{h}\" data-subject=\"{s}\" data-content=\"{c}\"><td>{h}{links}</td><td>{s}</td>\
             <td class=id>{t}</td><td>{changes}</td></tr>\n",
            h = escape(height),
            links = links(height),
            s = escape(row["subject"].as_str().unwrap_or("-")),
            t = escape(row["transaction"].as_str().unwrap_or("?")),
            c = !row["changes"].is_null(),
            changes = changes_html(&row["changes"]),
        ));
    }
    out.push_str("</table></section>\n");
    out
}

/// A diff as HTML: the two heights and the changes.
pub fn diff_html(diff: &Value) -> String {
    format!(
        "<section class=\"diff\" data-from=\"{f}\" data-to=\"{t}\"><h2>Changes from height {f} to height {t}</h2>\n{}</section>\n",
        changes_html(&diff["changes"]),
        f = escape(diff["from"]["height"].as_str().unwrap_or("?")),
        t = escape(diff["to"]["height"].as_str().unwrap_or("?")),
    )
}
