//! `/bend`: the member's Objective Bend programs. The list is the workspace's own registry
//! (`bend/objects/REF.json`, written by an admitted `bend run`: the bend, the object cell, the
//! birth transaction, the activity record); what an activity awaits is the shell's read
//! `bend await OBJECT TRANSACTION`, drawn as its phase, slot, decider, deadline and the object's
//! declared state; a slot the member decides carries the derived `bend answer` form with the slot
//! filled in, and its answer is that leaf's one outcome partial. Everything else a bend does
//! (publish, run, show, lookup, retry) is the derived `/verb/bend` page.

use super::body::{answer_html, verb};
use super::*;

/// A canonical decimal the shell's `bend await` accepts (a cell number, a transaction id).
fn decimal(text: &str) -> bool {
    !text.is_empty() && text.len() <= 80 && text.bytes().all(|b| b.is_ascii_digit()) && (text == "0" || !text.starts_with('0'))
}

use crate::bend::registry;

pub(super) fn index(site: &Site) -> Page {
    let mut rows = String::new();
    for (name, bend, object, transaction) in registry(&site.root) {
        let link = if decimal(&object) && decimal(&transaction) {
            format!("<a href=\"/bend/await/{object}/{transaction}\">what it awaits</a>")
        } else {
            String::new()
        };
        rows.push_str(&format!(
            "<tr data-object=\"{}\"><td><code>{}</code></td><td>{}</td><td><code>{}</code></td><td><code>{}</code></td><td>{link}</td></tr>\n",
            escape(&object), escape(&name), escape(&bend), escape(&object), escape(&transaction)
        ));
    }
    let list = if rows.is_empty() {
        "<p class=\"empty\">You have run no bend program from this workspace yet (<code>bend publish</code>, then <code>bend run</code>, on <a href=\"/verb/bend\">the bend page</a>).</p>".to_owned()
    } else {
        format!("<table><thead><tr><th>reference</th><th>bend</th><th>object</th><th>birth transaction</th><th></th></tr></thead><tbody>{rows}</tbody></table>")
    };
    let body = format!(
        "<p class=\"eyebrow\">Work that can wait for you</p><p>Follow the programs you have started and answer the decisions that are yours. Each activity names who can reply and its deadline; only that subject's answer is admitted, once.</p>\n\
         <section><h2>Your programs</h2>{list}</section>\n\
         <section><h2>Any activity</h2><p class=note>An await someone announced (<code>await OBJECT TRANSACTION</code> in a room) is read the same way.</p>\
         <form method=\"get\" action=\"/bend/await\" class=\"row\"><div><label for=\"aw-o\">Object cell</label><input id=\"aw-o\" name=\"object\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"aw-t\">Birth transaction</label><input id=\"aw-t\" name=\"transaction\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div><button>Read</button></form></section>\n\
         <p><a href=\"/verb/bend\">publish, run, show, look up or retry a bend</a></p>"
    );
    Page { status: 200, title: "Programs".into(), stamp: Stamp::None, body }
}

/// `/bend/await/OBJECT/TRANSACTION`: the shell's `bend await`, drawn.
pub(super) fn awaits(site: &Site, object: &str, transaction: &str) -> Page {
    let title = format!("Activity on object {object}");
    if !decimal(object) || !decimal(transaction) {
        return simple(400, &title, "the object cell and the birth transaction are decimals");
    }
    let Some(ending) = verb(site, &[format!("bend await {object} {transaction}")]) else {
        return simple(500, &title, "this body has no shell paths");
    };
    let parsed = (ending.code == 0).then(|| serde_json::from_str::<Value>(ending.stdout.trim()).ok()).flatten().filter(|v| v["type"] == "mini-bend-await-v1");
    let body = match parsed {
        Some(v) => format!("{}<details><summary>the shell's answer</summary>{}</details>", card(&v, &site.subject), answer_html(&ending, &[])),
        None => answer_html(&ending, &[("programs", "/bend")]),
    };
    Page { status: if ending.code == 0 { 200 } else { 403 }, title, stamp: Stamp::None, body }
}

/// One `mini-bend-await-v1` answer as a card: phase, state, and the reply slot with its decider and
/// deadline; the answer form when the slot is `me`'s to decide.
pub(super) fn card(v: &Value, me: &str) -> String {
    let s = |k: &str| v[k].as_str().map(str::to_owned).unwrap_or_else(|| if v[k].is_null() { String::new() } else { v[k].to_string() });
    let (phase, slot, decider) = (s("phase"), s("slot"), s("decider"));
    let mut rows = format!(
        "<tr><th>phase</th><td><strong>{}</strong></td></tr><tr><th>object</th><td><code>{}</code></td></tr><tr><th>birth transaction</th><td><code>{}</code></td></tr>",
        escape(&phase), escape(&s("object")), escape(&s("transaction"))
    );
    for (label, key) in [("activity record", "record"), ("read at height", "height"), ("declared state", "stateText")] {
        let value = s(key);
        if !value.is_empty() {
            rows.push_str(&format!("<tr><th>{label}</th><td><code>{}</code></td></tr>", escape(&value)));
        }
    }
    let mine = !decider.is_empty() && decider == me;
    if !slot.is_empty() {
        rows.push_str(&format!(
            "<tr><th>reply slot</th><td><code>{}</code></td></tr><tr><th>decider</th><td><code>{}</code>{}</td></tr><tr><th>deadline</th><td>height <code>{}</code></td></tr>",
            escape(&slot), escape(&decider), if mine { " (you)" } else { "" }, escape(&s("deadline"))
        ));
    }
    let mut out = format!(
        "<section class=\"await\" data-phase=\"{}\" data-slot=\"{}\" data-decider=\"{}\" data-mine=\"{mine}\"><h2>What it awaits</h2><table><tbody>{rows}</tbody></table>",
        escape(&phase), escape(&slot), escape(&decider)
    );
    match (phase.as_str(), slot.is_empty()) {
        ("none", _) => out.push_str("<p>No activity record: this transaction made none on this object, or has not yet.</p>"),
        (_, false) if mine => {
            out.push_str("<p>This slot is yours to decide. Your answer is one resolve turn signed by you, admitted once: <code>{\"reply\": DATA}</code> resumes the program with DATA (tagged data, as the program's reply type reads it, e.g. Tally's <code>{\"tag\":\"record\",\"fields\":[{\"name\":\"amount\",\"value\":{\"tag\":\"natural\",\"value\":\"7\"}}]}</code>), <code>{\"refused\": REASON}</code> declines.</p>");
            out.push_str(&super::verbs::form_for_filled("bend", "bend answer", "/verb/bend", "", &[("slot", &slot)]).unwrap_or_default());
        }
        (_, false) => out.push_str(&format!(
            "<p class=note>Only subject <code>{}</code> decides this slot: an answer signed by anyone else is refused <code>notDecider</code>.</p>",
            escape(&decider)
        )),
        _ => out.push_str("<p class=note>No reply slot is open: the program is not waiting on an answer now.</p>"),
    }
    out.push_str("</section>");
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn an_await_card_offers_the_answer_only_to_the_slots_decider() {
        let v = json!({"type":"mini-bend-await-v1","object":"12","transaction":"34","record":"77","height":"90","phase":"awaiting",
            "state":null,"stateText":"{total=0}","slot":"5551","decider":"42","deadline":"120"});
        let mine = card(&v, "42");
        assert!(mine.contains("data-mine=\"true\"") && mine.contains("data-slot=\"5551\""), "{mine}");
        assert!(mine.contains("action=\"/verb/bend\"") && mine.contains("value=\"5551\""), "the derived answer form, slot filled: {mine}");
        assert!(mine.contains("{total=0}") && mine.contains("height <code>120</code>"));
        let theirs = card(&v, "43");
        assert!(theirs.contains("data-mine=\"false\"") && !theirs.contains("action=\"/verb/bend\"") && theirs.contains("notDecider"), "{theirs}");
        let none = card(&json!({"type":"mini-bend-await-v1","object":"1","transaction":"1","record":"","phase":"none"}), "42");
        assert!(none.contains("data-phase=\"none\"") && none.contains("No activity record") && !none.contains("<form"), "{none}");
        assert!(card(&json!({"phase":"<b>"}), "1").contains("&lt;b&gt;"));
    }

    #[test]
    fn the_registry_lists_runs_and_only_decimals_are_linked() {
        assert!(decimal("12") && decimal("0") && !decimal("012") && !decimal("1a") && !decimal(""));
        let dir = std::env::temp_dir().join(format!("programs-{}", std::process::id()));
        fs::create_dir_all(dir.join("bend/objects")).unwrap();
        fs::write(dir.join("bend/objects/ask-alice.json"), r#"{"bend":"tally","object":"12","transaction":"34","record":"77"}"#).unwrap();
        fs::write(dir.join("bend/objects/broken.json"), "not json").unwrap();
        assert_eq!(registry(&dir), vec![("ask-alice".into(), "tally".into(), "12".into(), "34".into())]);
        fs::remove_dir_all(&dir).unwrap();
    }
}
