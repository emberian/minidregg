//! `/bend`: the member's Objective Bend programs and native object surfaces (`ObjectiveActivity`
//! `spawn` and `reply`, `ObjectiveCall` `invoke`, `ObjectiveSend` `send` and `deliver`, and a bridge
//! to `SeatStore` on `/object/...`).
//!
//! Instead of requiring raw nested tagged JSON (`{"tag":"record","fields":[...]}`), `/bend` accepts
//! structured human-friendly `key=value` fields (with optional variant tags) and compiles them to
//! canonical tagged `Data` JSON. Everything else a bend does (`publish`, `run`, `show`, `lookup`,
//! `retry`) stays available on the derived `/verb/bend` page.

use super::body::{answer_html, verb};
use super::*;
use crate::bend::registry;
use serde_json::{json, Value};

/// A canonical decimal the shell's `bend await` accepts (a cell number, a transaction id).
fn decimal(text: &str) -> bool {
    !text.is_empty() && text.len() <= 80 && text.bytes().all(|b| b.is_ascii_digit()) && (text == "0" || !text.starts_with('0'))
}

/// Split `text` on commas or newlines at top level (outside `(...)`, `{...}`, and `"..."`).
pub(crate) fn split_top_level(text: &str) -> Vec<String> {
    let mut items = Vec::new();
    let mut current = String::new();
    let mut paren = 0usize;
    let mut brace = 0usize;
    let mut quoted = false;
    for ch in text.chars() {
        match ch {
            '"' => {
                quoted = !quoted;
                current.push(ch);
            }
            '(' if !quoted => {
                paren += 1;
                current.push(ch);
            }
            ')' if !quoted => {
                paren = paren.saturating_sub(1);
                current.push(ch);
            }
            '{' if !quoted => {
                brace += 1;
                current.push(ch);
            }
            '}' if !quoted => {
                brace = brace.saturating_sub(1);
                current.push(ch);
            }
            ',' | '\n' | ';' if !quoted && paren == 0 && brace == 0 => {
                let trimmed = current.trim();
                if !trimmed.is_empty() {
                    items.push(trimmed.to_owned());
                }
                current.clear();
            }
            _ => current.push(ch),
        }
    }
    let trimmed = current.trim();
    if !trimmed.is_empty() {
        items.push(trimmed.to_owned());
    }
    items
}

/// Parse one human-friendly scalar, record (`{k=v, ...}`), or variant (`tag(payload)`) into tagged `Data` JSON.
pub(crate) fn parse_human_value(raw: &str) -> std::result::Result<Value, String> {
    let text = raw.trim();
    if text.is_empty() {
        return Ok(json!({"tag": "record", "fields": []}));
    }
    if text.starts_with('{') && text.contains("\"tag\"") {
        if let Ok(parsed) = serde_json::from_str::<Value>(text) {
            return Ok(parsed);
        }
    }
    if text == "true" || text == "false" {
        return Ok(json!({"tag": "boolean", "value": text == "true"}));
    }
    let nat_candidate = text.strip_suffix('n').unwrap_or(text);
    if decimal(nat_candidate) {
        return Ok(json!({"tag": "natural", "value": nat_candidate}));
    }
    if let Some(inner) = text.strip_prefix('"').and_then(|s| s.strip_suffix('"')) {
        return Ok(json!({"tag": "label", "value": inner}));
    }
    if let Some(inner) = text.strip_prefix('{').and_then(|s| s.strip_suffix('}')) {
        return parse_human_fields(inner);
    }
    if let Some((label, rest)) = text.split_once('(') {
        if let Some(inner) = rest.strip_suffix(')') {
            let label = label.trim();
            if !label.is_empty() && label.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-') {
                let payload = if inner.trim().contains('=') && !inner.trim().starts_with('{') {
                    parse_human_fields(inner)?
                } else {
                    parse_human_value(inner)?
                };
                return Ok(json!({"tag": "variant", "label": label, "payload": payload}));
            }
        }
    }
    if text.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-' || b == b'/' || b == b'.') {
        return Ok(json!({"tag": "label", "value": text}));
    }
    Err(format!("cannot parse `{text}` as human-friendly Data (use e.g. `7`, `true`, `alice`, `set(0)`, or `k=v`)"))
}

/// Parse `key=value` pairs into a tagged `Data::record` JSON object.
pub(crate) fn parse_human_fields(fields_text: &str) -> std::result::Result<Value, String> {
    let trimmed = fields_text.trim();
    if trimmed.is_empty() {
        return Ok(json!({"tag": "record", "fields": []}));
    }
    if trimmed.starts_with('{') && trimmed.contains("\"tag\"") {
        return serde_json::from_str::<Value>(trimmed).map_err(|e| format!("invalid tagged Data JSON: {e}"));
    }
    let body = trimmed.strip_prefix('{').and_then(|s| s.strip_suffix('}')).unwrap_or(trimmed);
    let mut fields = Vec::new();
    for entry in split_top_level(body) {
        let Some((name, value)) = entry.split_once('=') else {
            return Err(format!("field `{entry}` must be `name=value` (e.g. `amount=7`)"));
        };
        let name = name.trim();
        if name.is_empty() || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
            return Err(format!("invalid field name `{name}`"));
        }
        fields.push(json!({"name": name, "value": parse_human_value(value)?}));
    }
    Ok(json!({"tag": "record", "fields": fields}))
}

/// Build tagged `Data` JSON from an optional `variant` tag and structured `key=value` fields.
pub(crate) fn parse_human_data(variant: &str, fields_text: &str) -> std::result::Result<Value, String> {
    let variant = variant.trim();
    let payload = if fields_text.trim().contains('=') || fields_text.trim().is_empty() || fields_text.trim().starts_with('{') {
        parse_human_fields(fields_text)?
    } else {
        parse_human_value(fields_text)?
    };
    if variant.is_empty() {
        Ok(payload)
    } else if variant.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-') {
        Ok(json!({"tag": "variant", "label": variant, "payload": payload}))
    } else {
        Err(format!("invalid variant tag `{variant}`"))
    }
}

/// Format tagged `Data` JSON as a concise human-readable `key=value` / `tag(...)` string.
pub(crate) fn format_human_data(v: &Value) -> String {
    match v.get("tag").and_then(Value::as_str) {
        Some("natural") => v.get("value").and_then(Value::as_str).unwrap_or("?").to_owned(),
        Some("boolean") => v.get("value").and_then(Value::as_bool).map(|b| b.to_string()).unwrap_or_else(|| "?".into()),
        Some("label") => v.get("value").and_then(Value::as_str).unwrap_or("?").to_owned(),
        Some("record") => {
            let fields = v
                .get("fields")
                .and_then(Value::as_array)
                .map(|fs| {
                    fs.iter()
                        .map(|f| {
                            format!(
                                "{}={}",
                                f.get("name").and_then(Value::as_str).unwrap_or("?"),
                                format_human_data(f.get("value").unwrap_or(&Value::Null))
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(", ")
                })
                .unwrap_or_default();
            format!("{{{fields}}}")
        }
        Some("variant") => {
            let label = v.get("label").and_then(Value::as_str).unwrap_or("?");
            let payload = v.get("payload").unwrap_or(&Value::Null);
            let inner = format_human_data(payload);
            if inner == "{}" {
                label.to_owned()
            } else {
                format!("{label}({inner})")
            }
        }
        _ if v.is_null() => String::new(),
        _ => v.to_string(),
    }
}

/// Render a structured HTML table for a tagged `Data` value when it is a record or variant-of-record.
pub(crate) fn inspect_data_table(v: &Value) -> String {
    let (variant_badge, fields) = match v.get("tag").and_then(Value::as_str) {
        Some("record") => (None, v.get("fields").and_then(Value::as_array)),
        Some("variant") => (
            v.get("label").and_then(Value::as_str),
            v.pointer("/payload/fields").and_then(Value::as_array),
        ),
        _ => return String::new(),
    };
    let Some(fields) = fields.filter(|fs| !fs.is_empty()) else {
        return String::new();
    };
    let mut html = String::from("<table class=\"data-fields\" data-structured-state><thead><tr><th>field</th><th>value</th></tr></thead><tbody>");
    if let Some(tag) = variant_badge {
        html.push_str(&format!(
            "<tr data-variant><th>variant</th><td><code>{}</code></td></tr>",
            escape(tag)
        ));
    }
    for f in fields {
        let name = f.get("name").and_then(Value::as_str).unwrap_or("?");
        let val = format_human_data(f.get("value").unwrap_or(&Value::Null));
        html.push_str(&format!(
            "<tr><td><code>{}</code></td><td><code>{}</code></td></tr>",
            escape(name),
            escape(&val)
        ));
    }
    html.push_str("</tbody></table>");
    html
}

/// Build an `ObjectiveActivity` `spawn` (`birth`) turn specification from human-friendly inputs.
pub(crate) fn spawn_turn(
    bend: &str,
    object: &str,
    variant: &str,
    fields: &str,
    seed_fields: &str,
    deposit: Option<&str>,
) -> std::result::Result<Value, String> {
    let bend = bend.trim();
    let object = object.trim();
    if bend.is_empty() || object.is_empty() {
        return Err("bend name and object reference are required".into());
    }
    let input = parse_human_data(variant, fields)?;
    let mut spec = json!({
        "surface": "ObjectiveActivity",
        "kind": "spawn",
        "bend": bend,
        "object": object,
        "input": input,
    });
    if !seed_fields.trim().is_empty() {
        spec["seed"] = parse_human_data("", seed_fields)?;
    }
    if let Some(dep) = deposit.map(str::trim).filter(|d| !d.is_empty()) {
        if !decimal(dep) {
            return Err("deposit must be a canonical decimal".into());
        }
        spec["deposit"] = json!(dep);
    }
    Ok(spec)
}

/// Build an `ObjectiveActivity` `reply` (`resolve`) turn from human-friendly `key=value` fields or refusal reason.
pub(crate) fn reply_turn(
    slot: &str,
    mode: &str,
    variant: &str,
    fields: &str,
    refused: &str,
) -> std::result::Result<Value, String> {
    let slot = slot.trim();
    if !decimal(slot) {
        return Err("reply slot must be a canonical decimal".into());
    }
    let answer = match mode.trim() {
        "refused" => {
            let reason = refused.trim();
            if reason.is_empty() {
                return Err("refusal reason is required when declining a slot".into());
            }
            json!({"refused": reason})
        }
        _ => json!({"reply": parse_human_data(variant, fields)?}),
    };
    Ok(json!({
        "surface": "ObjectiveActivity",
        "kind": "resolve",
        "slot": slot,
        "answer": answer,
    }))
}

/// Build a synchronous `ObjectiveCall` `invoke` turn from human-friendly `variant` + `key=value` fields.
pub(crate) fn invoke_turn(
    object: &str,
    pin: &str,
    method: &str,
    variant: &str,
    fields: &str,
) -> std::result::Result<Value, String> {
    let object = object.trim();
    let method = method.trim();
    if object.is_empty() || method.is_empty() {
        return Err("object reference and method name are required".into());
    }
    let chosen_variant = if variant.trim().is_empty() { method } else { variant.trim() };
    let input = parse_human_data(chosen_variant, fields)?;
    Ok(json!({
        "surface": "ObjectiveCall",
        "kind": "invoke",
        "object": object,
        "pin": pin.trim(),
        "method": method,
        "input": input,
    }))
}

/// Build an `ObjectiveSend` `send` turn from human-friendly `variant` + `key=value` payload fields.
pub(crate) fn send_turn(
    source: &str,
    target: &str,
    variant: &str,
    fields: &str,
) -> std::result::Result<Value, String> {
    let source = source.trim();
    let target = target.trim();
    if source.is_empty() || target.is_empty() {
        return Err("source object and target object are required".into());
    }
    let message = parse_human_data(variant, fields)?;
    Ok(json!({
        "surface": "ObjectiveSend",
        "kind": "send",
        "source": source,
        "target": target,
        "message": message,
    }))
}

/// Build an `ObjectiveSend` / activity `deliver` turn.
pub(crate) fn deliver_turn_spec(
    object: &str,
    transaction: &str,
    account: Option<&str>,
) -> std::result::Result<Value, String> {
    let object = object.trim();
    let transaction = transaction.trim();
    if !decimal(object) || !decimal(transaction) {
        return Err("object cell and birth/message transaction must be canonical decimals".into());
    }
    let mut spec = json!({
        "surface": "ObjectiveSend",
        "kind": "deliver",
        "object": object,
        "transaction": transaction,
    });
    if let Some(acc) = account.map(str::trim).filter(|a| !a.is_empty()) {
        spec["account"] = json!(acc);
    }
    Ok(spec)
}

/// Render the structured human-friendly native surface forms on `/bend`.
fn surface_forms() -> String {
    String::from(
        "<section data-surface=\"objective-activity\"><h2>ObjectiveActivity · <code>spawn</code> &amp; <code>reply</code></h2>\
         <p class=note>Start an activity or answer a reply slot using human-friendly <code>key=value</code> fields (e.g. <code>amount=7</code> or <code>init=set(0), decider=42</code>) instead of nested tagged JSON.</p>\
         <form method=\"post\" action=\"/verb/bend\" class=\"row\" data-turn=\"spawn\">\
         <div><label for=\"oa-bend\">Program (bend)</label><input id=\"oa-bend\" name=\"bend\" type=\"text\" pattern=\"[A-Za-z0-9-]+\" required></div>\
         <div><label for=\"oa-obj\">Object reference</label><input id=\"oa-obj\" name=\"object\" type=\"text\" pattern=\"[A-Za-z0-9/-]+\" required></div>\
         <div><label for=\"oa-var\">Input variant (optional)</label><input id=\"oa-var\" name=\"variant\" type=\"text\" placeholder=\"e.g. start\"></div>\
         <div><label for=\"oa-fields\">Input fields (<code>key=value</code>)</label><input id=\"oa-fields\" name=\"fields\" type=\"text\" placeholder=\"init=set(0), decider=42\"></div>\
         <div><label for=\"oa-seed\">Seed fields (optional)</label><input id=\"oa-seed\" name=\"seed_fields\" type=\"text\" placeholder=\"total=0\"></div>\
         <div><label for=\"oa-dep\">Deposit (optional)</label><input id=\"oa-dep\" name=\"deposit\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]*\"></div>\
         <button>Spawn activity</button></form></section>\n\
         <section data-surface=\"objective-call\"><h2>ObjectiveCall · <code>invoke</code></h2>\
         <p class=note>Invoke a synchronous method on a pinned object with structured field inputs.</p>\
         <form method=\"post\" action=\"/paste\" class=\"row\" data-turn=\"invoke\">\
         <div><label for=\"oc-obj\">Object reference</label><input id=\"oc-obj\" name=\"object\" type=\"text\" pattern=\"[A-Za-z0-9/-]+\" required></div>\
         <div><label for=\"oc-method\">Method / action</label><input id=\"oc-method\" name=\"method\" type=\"text\" placeholder=\"e.g. claim, approve, vote\" required></div>\
         <div><label for=\"oc-var\">Variant tag (optional)</label><input id=\"oc-var\" name=\"variant\" type=\"text\" placeholder=\"defaults to method\"></div>\
         <div><label for=\"oc-fields\">Call fields (<code>key=value</code>)</label><input id=\"oc-fields\" name=\"fields\" type=\"text\" placeholder=\"milestone=1, payout=500\"></div>\
         <button>Invoke call</button></form></section>\n\
         <section data-surface=\"objective-send\"><h2>ObjectiveSend · <code>send</code> &amp; <code>deliver</code></h2>\
         <p class=note>Queue an asynchronous message between objects or deliver a settled message / await.</p>\
         <form method=\"post\" action=\"/paste\" class=\"row\" data-turn=\"send\">\
         <div><label for=\"os-src\">Source object</label><input id=\"os-src\" name=\"source\" type=\"text\" required></div>\
         <div><label for=\"os-dst\">Target object</label><input id=\"os-dst\" name=\"target\" type=\"text\" required></div>\
         <div><label for=\"os-var\">Message tag</label><input id=\"os-var\" name=\"variant\" type=\"text\" placeholder=\"e.g. credit, lease\" required></div>\
         <div><label for=\"os-fields\">Payload fields (<code>key=value</code>)</label><input id=\"os-fields\" name=\"fields\" type=\"text\" placeholder=\"amount=25, epoch=3\"></div>\
         <button>Send message</button></form>\
         <form method=\"post\" action=\"/verb/bend\" class=\"row\" data-turn=\"deliver\">\
         <div><label for=\"od-obj\">Object cell</label><input id=\"od-obj\" name=\"object\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"od-tx\">Birth / message transaction</label><input id=\"od-tx\" name=\"transaction\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"od-acc\">Account (optional)</label><input id=\"od-acc\" name=\"account\" type=\"text\"></div>\
         <button>Deliver</button></form></section>\n\
         <section data-surface=\"seat-store\"><h2>SeatStore · <code>create</code>, <code>fund</code>, <code>act</code>, <code>exit</code></h2>\
         <p class=note>Open any object under <code>/object/REF/behavior</code> to inspect open seats, invitations, and certified batch clearings or drive <code>create</code>, <code>fund</code>, <code>act</code>, and <code>exit</code> turns with human-friendly inputs.</p></section>\n",
    )
}

pub(super) fn index(site: &Site) -> Page {
    let mut rows = String::new();
    for (name, bend, object, transaction) in registry(&site.root) {
        let link = if decimal(&object) && decimal(&transaction) {
            format!("<a href=\"/bend/await/{object}/{transaction}\">inspect activity</a>")
        } else {
            String::new()
        };
        rows.push_str(&format!(
            "<tr data-object=\"{}\"><td><code>{}</code></td><td>{}</td><td><code>{}</code></td><td><code>{}</code></td><td>{link} · <a href=\"/object/{}/behavior\">world</a></td></tr>\n",
            escape(&object), escape(&name), escape(&bend), escape(&object), escape(&transaction), escape(&name)
        ));
    }
    let list = if rows.is_empty() {
        "<p class=\"empty\">No bend instances started from this workspace yet (<code>bend publish</code>, then <code>bend run</code> on <a href=\"/verb/bend\">/verb/bend</a>).</p>".to_owned()
    } else {
        format!("<table><thead><tr><th>reference</th><th>bend</th><th>object</th><th>birth transaction</th><th></th></tr></thead><tbody>{rows}</tbody></table>")
    };
    let forms = if site.front.read_only { String::new() } else { surface_forms() };
    let body = format!(
        "<p class=\"eyebrow\">Objective Bend programs</p><p>Follow the programs you have started and answer the decisions that are yours. Each activity names the reply slot decider and deadline height; only that subject's signed answer is admitted, once.</p>\n\
         <section><h2>Your programs</h2>{list}</section>\n\
         <section><h2>Inspect any activity</h2><p class=note>Look up an activity by object cell and birth transaction (<code>await OBJECT TRANSACTION</code>).</p>\
         <form method=\"get\" action=\"/bend/await\" class=\"row\"><div><label for=\"aw-o\">Object cell</label><input id=\"aw-o\" name=\"object\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"aw-t\">Birth transaction</label><input id=\"aw-t\" name=\"transaction\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div><button>Read</button></form></section>\n\
         {forms}\
         <p><a href=\"/verb/bend\">All bend commands (publish, run, show, lookup, answer, retry)</a></p>"
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
        Some(v) => format!("{}<details><summary>Shell output</summary>{}</details>", card(&v, &site.subject), answer_html(&ending, &[])),
        None => answer_html(&ending, &[("programs", "/bend")]),
    };
    Page { status: if ending.code == 0 { 200 } else { 403 }, title, stamp: Stamp::None, body }
}

/// One `mini-bend-await-v1` answer as a card: phase, structured state fields, and the reply slot with
/// its decider and deadline; the structured human-friendly reply form + derived verb form when the
/// slot is `me`'s to decide and the deadline has not passed.
pub(super) fn card(v: &Value, me: &str) -> String {
    let s = |k: &str| v[k].as_str().map(str::to_owned).unwrap_or_else(|| if v[k].is_null() { String::new() } else { v[k].to_string() });
    let (phase, slot, decider, height_s, deadline_s) = (s("phase"), s("slot"), s("decider"), s("height"), s("deadline"));
    let expired = match (height_s.parse::<u64>().ok(), deadline_s.parse::<u64>().ok()) {
        (Some(h), Some(d)) => h > d,
        _ => false,
    };
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
            "<tr><th>reply slot</th><td><code>{}</code></td></tr><tr><th>decider</th><td><code>{}</code>{}</td></tr><tr><th>deadline</th><td>height <code>{}</code>{}</td></tr>",
            escape(&slot), escape(&decider), if mine { " (you)" } else { "" }, escape(&deadline_s), if expired { " (expired)" } else { "" }
        ));
    }
    let mut out = format!(
        "<section class=\"await\" data-phase=\"{}\" data-slot=\"{}\" data-decider=\"{}\" data-mine=\"{mine}\"><h2>Activity status</h2><table><tbody>{rows}</tbody></table>",
        escape(&phase), escape(&slot), escape(&decider)
    );
    if let Some(state) = v.get("state").filter(|st| st.is_object()) {
        out.push_str(&inspect_data_table(state));
    }
    match (phase.as_str(), slot.is_empty(), expired) {
        ("none", _, _) => out.push_str("<p>No activity record: this transaction made none on this object, or has not yet.</p>"),
        ("awaiting", false, true) => out.push_str(&format!(
            "<p class=note>Reply slot <code>{}</code> expired at height <code>{}</code> (read at height <code>{}</code>): answers are refused <code>pastDeadline</code>.</p>",
            escape(&slot), escape(&deadline_s), escape(&height_s)
        )),
        ("awaiting", false, false) if mine => {
            let esc_slot = escape(&slot);
            out.push_str(&format!(
                "<p>This slot is yours to decide. Enter human-friendly <code>key=value</code> fields (e.g. <code>amount=7</code> or <code>choice=1, salt=42</code>) to build your signed <code>reply</code> turn, or use the command form below.</p>\
                 <form method=\"post\" action=\"/verb/bend\" class=\"row\" data-surface=\"objective-activity\" data-turn=\"reply\">\
                 <input type=\"hidden\" name=\"slot\" value=\"{esc_slot}\">\
                 <div><label for=\"reply-mode-{esc_slot}\">Decision</label><select id=\"reply-mode-{esc_slot}\" name=\"mode\"><option value=\"reply\">reply</option><option value=\"refused\">refused</option></select></div>\
                 <div><label for=\"reply-var-{esc_slot}\">Variant (optional)</label><input id=\"reply-var-{esc_slot}\" name=\"variant\" type=\"text\" placeholder=\"e.g. approve\"></div>\
                 <div><label for=\"reply-fields-{esc_slot}\">Reply fields (<code>key=value</code>)</label><input id=\"reply-fields-{esc_slot}\" name=\"fields\" type=\"text\" placeholder=\"amount=7\"></div>\
                 <div><label for=\"reply-refused-{esc_slot}\">Refusal reason (if refused)</label><input id=\"reply-refused-{esc_slot}\" name=\"refused\" type=\"text\" placeholder=\"declined\"></div>\
                 <button>Answer slot</button></form>"
            ));
            out.push_str(&super::verbs::form_for_filled("bend", "bend answer", "/verb/bend", "", &[("slot", &slot)]).unwrap_or_default());
        }
        ("awaiting", false, false) => out.push_str(&format!(
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
            "state":{"tag":"record","fields":[{"name":"total","value":{"tag":"natural","value":"0"}}]},
            "stateText":"{total=0}","slot":"5551","decider":"42","deadline":"120"});
        let mine = card(&v, "42");
        assert!(mine.contains("data-mine=\"true\"") && mine.contains("data-slot=\"5551\""), "{mine}");
        assert!(mine.contains("action=\"/verb/bend\"") && mine.contains("value=\"5551\""), "the derived answer form, slot filled: {mine}");
        assert!(mine.contains("data-surface=\"objective-activity\"") && mine.contains("data-turn=\"reply\""), "structured reply form: {mine}");
        assert!(mine.contains("data-structured-state"), "structured state table: {mine}");
        assert!(mine.contains("{total=0}") && mine.contains("height <code>120</code>"));
        let theirs = card(&v, "43");
        assert!(theirs.contains("data-mine=\"false\"") && !theirs.contains("action=\"/verb/bend\"") && theirs.contains("notDecider"), "{theirs}");
        let past = json!({"type":"mini-bend-await-v1","object":"12","transaction":"34","record":"77","height":"121","phase":"awaiting",
            "state":null,"stateText":"{total=0}","slot":"5551","decider":"42","deadline":"120"});
        let expired = card(&past, "42");
        assert!(!expired.contains("action=\"/verb/bend\"") && expired.contains("pastDeadline"), "expired await must not offer answer form: {expired}");
        let none = card(&json!({"type":"mini-bend-await-v1","object":"1","transaction":"1","record":"","phase":"none"}), "42");
        assert!(none.contains("data-phase=\"none\"") && none.contains("No activity record") && !none.contains("<form"), "{none}");
        assert!(card(&json!({"phase":"<b>"}), "1").contains("&lt;b&gt;"));
    }

    #[test]
    fn human_friendly_inputs_compile_to_tagged_data_and_turns() {
        let tally_reply = reply_turn("5551", "reply", "", "amount=7", "").unwrap();
        assert_eq!(
            tally_reply["answer"]["reply"],
            json!({"tag": "record", "fields": [{"name": "amount", "value": {"tag": "natural", "value": "7"}}]})
        );
        let declined = reply_turn("5551", "refused", "", "", "busy").unwrap();
        assert_eq!(declined["answer"], json!({"refused": "busy"}));

        let spawn = spawn_turn("tally", "lobby-tally", "", "init=set(0), decider=42", "total=0", Some("1200")).unwrap();
        assert_eq!(spawn["kind"], "spawn");
        assert_eq!(format_human_data(&spawn["input"]), "{init=set(0), decider=42}");
        assert_eq!(format_human_data(&spawn["seed"]), "{total=0}");

        let call = invoke_turn("bounty-1", "901", "approve", "approve", "milestone=1, payout=500, ok=true").unwrap();
        assert_eq!(call["surface"], "ObjectiveCall");
        assert_eq!(call["input"]["tag"], "variant");
        assert_eq!(call["input"]["label"], "approve");
        assert_eq!(format_human_data(&call["input"]), "approve({milestone=1, payout=500, ok=true})");

        let msg = send_turn("station-1", "desk-2", "lease", "holder=alice, epoch=3").unwrap();
        assert_eq!(msg["surface"], "ObjectiveSend");
        assert_eq!(format_human_data(&msg["message"]), "lease({holder=alice, epoch=3})");

        let deliv = deliver_turn_spec("12", "34", Some("my-acct")).unwrap();
        assert_eq!(deliv["kind"], "deliver");
        assert_eq!(deliv["account"], "my-acct");
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
