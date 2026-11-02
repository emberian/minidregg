//! Two useful faces of a member-defined kind, instance, or native object/seat world (`ObjectiveCall`,
//! `ObjectiveSend`, `ObjectiveActivity`, and `SeatStore`), over current signed reads.
//!
//! In addition to rendering `worldInstance` and `worldKind` records, `/object/NAME` and
//! `/object/NAME/behavior` inspect native object state, open seats, invitations, and certified
//! batch clearings, and render structured human-friendly form inputs (`key=value`, `asset:amount`,
//! `role:holder`) for `ObjectiveCall` (`invoke`), `ObjectiveSend` (`send`, `deliver`),
//! `ObjectiveActivity` (`spawn`, `reply`), and `SeatStore` (`create`, `fund`, `act`, `exit`) turns.

use super::programs::{
    deliver_turn_spec, format_human_data, inspect_data_table, invoke_turn, parse_human_data,
    reply_turn, send_turn, spawn_turn, split_top_level,
};
use super::*;
use serde_json::{json, Value};

fn decimal(text: &str) -> bool {
    !text.is_empty()
        && text.len() <= 80
        && text.bytes().all(|b| b.is_ascii_digit())
        && (text == "0" || !text.starts_with('0'))
}

/// Parse human-friendly `asset:amount` pairs (e.g. `1:500, 2:10`) for a `SeatStore` `fund` (`offer`) turn.
pub(crate) fn parse_asset_amounts(text: &str) -> std::result::Result<Vec<Value>, String> {
    let mut out = Vec::new();
    for item in split_top_level(text) {
        let Some((asset, amount)) = item.split_once(':').or_else(|| item.split_once('=')) else {
            return Err(format!("entry `{item}` must be `asset:amount` (e.g. `1:500`)"));
        };
        let (asset, amount) = (asset.trim(), amount.trim());
        if !decimal(asset) || !decimal(amount) {
            return Err(format!("asset `{asset}` and amount `{amount}` must be canonical decimals"));
        }
        out.push(json!([asset, amount]));
    }
    Ok(out)
}

/// Parse human-friendly `role:holder` pairs (e.g. `bidder:42, seller:43`) for a `SeatStore` `create` turn.
pub(crate) fn parse_invitation_roles(text: &str) -> std::result::Result<Vec<Value>, String> {
    let mut out = Vec::new();
    for item in split_top_level(text) {
        let Some((role, holder)) = item.split_once(':').or_else(|| item.split_once('=')) else {
            return Err(format!("invitation `{item}` must be `role:holder` (e.g. `bidder:42`)"));
        };
        let (role, holder) = (role.trim(), holder.trim());
        if role.is_empty() || !decimal(holder) {
            return Err(format!("role `{role}` must be non-empty and holder `{holder}` a decimal subject id"));
        }
        out.push(json!({"role": role, "holder": holder, "terms": []}));
    }
    Ok(out)
}

/// Build a `SeatStore` `create` turn from human-friendly inputs.
pub(crate) fn seat_create_turn(
    object: &str,
    package: &str,
    payer: &str,
    invitations_text: &str,
) -> std::result::Result<Value, String> {
    let (object, package, payer) = (object.trim(), package.trim(), payer.trim());
    if !decimal(object) || !decimal(package) || !decimal(payer) {
        return Err("object cell, package id, and payer account must be canonical decimals".into());
    }
    let invitations = parse_invitation_roles(invitations_text)?;
    Ok(json!({
        "surface": "SeatStore",
        "turn": {
            "kind": "create",
            "object": object,
            "package": package,
            "payer": payer,
            "clause": {"type": "all", "predicates": []},
            "invitations": invitations,
        }
    }))
}

/// Build a `SeatStore` `fund` (`offer`) turn from human-friendly `give` / `want` `asset:amount` pairs.
pub(crate) fn seat_fund_turn(
    invitation: &str,
    funding: &str,
    payee: &str,
    give_text: &str,
    want_text: &str,
    exit_rule: &str,
    confirm_donation: bool,
) -> std::result::Result<Value, String> {
    let (invitation, funding, payee) = (invitation.trim(), funding.trim(), payee.trim());
    if !decimal(invitation) || !decimal(funding) || !decimal(payee) {
        return Err("invitation id, funding account, and payee account must be canonical decimals".into());
    }
    let give = parse_asset_amounts(give_text)?;
    let want = parse_asset_amounts(want_text)?;
    let donate = want.is_empty();
    if donate && !confirm_donation {
        return Err("an offer with empty `want` is a donation; confirm_donation must be true".into());
    }
    let exit = if let Some(due) = exit_rule.trim().strip_prefix("afterDeadline:") {
        let due = due.trim();
        if !decimal(due) {
            return Err("afterDeadline height must be a canonical decimal".into());
        }
        json!({"afterDeadline": due})
    } else {
        json!("onDemand")
    };
    Ok(json!({
        "surface": "SeatStore",
        "confirmDonation": confirm_donation,
        "turn": {
            "kind": "offer",
            "invitation": invitation,
            "funding": funding,
            "payee": payee,
            "proposal": {
                "give": give,
                "want": want,
                "exit": exit,
                "donate": donate,
                "disclosure": {"offerer": true, "payee": true, "holder": true},
            }
        }
    }))
}

/// Build a `SeatStore` `act` (`invoke`) turn from human-friendly method/variant and `key=value` fields.
pub(crate) fn seat_act_turn(
    instance: &str,
    payer: &str,
    variant: &str,
    fields: &str,
) -> std::result::Result<Value, String> {
    let (instance, payer) = (instance.trim(), payer.trim());
    if !decimal(instance) || !decimal(payer) {
        return Err("instance id and payer account must be canonical decimals".into());
    }
    let argument = parse_human_data(variant, fields)?;
    Ok(json!({
        "surface": "SeatStore",
        "turn": {
            "kind": "invoke",
            "instance": instance,
            "payer": payer,
            "argument": argument,
        }
    }))
}

/// Build a `SeatStore` `exit` turn from a seat account id.
pub(crate) fn seat_exit_turn(seat: &str) -> std::result::Result<Value, String> {
    let seat = seat.trim();
    if !decimal(seat) {
        return Err("seat account coordinate must be a canonical decimal".into());
    }
    Ok(json!({
        "surface": "SeatStore",
        "turn": {
            "kind": "exit",
            "seat": seat,
        }
    }))
}

pub(super) fn page(site: &Site, name: &str, behavior: bool) -> Page {
    let reference = match site.reference(name) {
        Ok(reference) => reference,
        Err(page) => return page,
    };
    match site.read(&reference, "resource") {
        Ok((view, challenge, _)) => match body(site, name, &view, behavior) {
            Some(mut body) => {
                if behavior {
                    body.push_str("<h2>Current law</h2>");
                    match site.read(&reference, "policy") {
                        Ok((law, head, _)) => body.push_str(&format!(
                            "<p>Law read at height {}.</p><details><summary>Disclosed law</summary><pre>{}</pre></details>",
                            escape(head["height"].as_str().unwrap_or("?")),
                            escape(&serde_json::to_string_pretty(&law).unwrap_or_default())
                        )),
                        Err(error) => body.push_str(&format!(
                            "<p class=refusal>Law unavailable: {}</p>",
                            escape(&refusal_text(&error).unwrap_or(error))
                        )),
                    }
                }
                Page {
                    status: 200,
                    title: format!(
                        "{} · {}",
                        name,
                        if behavior { "behavior" } else { "fields" }
                    ),
                    stamp: Stamp::Read(ReadContext::of(&challenge, &view)),
                    body,
                }
            }
            None => simple(
                400,
                "No object view",
                "This resource has no member-defined kind or instance projection.",
            ),
        },
        Err(error) => failure_page(name, &error),
    }
}

pub(super) fn body(site: &Site, name: &str, view: &Value, behavior: bool) -> Option<String> {
    render(&site.base(), name, view, behavior)
}

/// Render structured human-friendly controls for `ObjectiveCall` (`invoke`), `ObjectiveSend`
/// (`send`, `deliver`), `ObjectiveActivity` (`spawn`, `reply`), and `SeatStore` (`create`, `fund`,
/// `act`, `exit`) on the behavior face of an object.
fn native_surface_controls(name: &str, object: &Value) -> String {
    let n = escape(name);
    let mut method_options = String::new();
    if let Some(methods) = object["methods"].as_array() {
        for m in methods {
            if let Some(mname) = m["name"].as_str() {
                method_options.push_str(&format!("<option value=\"{0}\">{0}</option>", escape(mname)));
            }
        }
    }
    let method_control = if method_options.is_empty() {
        format!("<input id=\"wc-method-{n}\" name=\"method\" type=\"text\" placeholder=\"e.g. claim, approve, vote\" required>")
    } else {
        format!("<select id=\"wc-method-{n}\" name=\"method\">{method_options}</select>")
    };
    format!(
        "<section data-world-surfaces>\
         <h2>Drive turns (structured inputs)</h2>\
         <p class=note>Enter human-friendly <code>key=value</code> fields, <code>asset:amount</code> pairs, or <code>role:holder</code> invitations instead of raw nested tagged JSON.</p>\
         <article data-surface=\"objective-call\"><h3>ObjectiveCall · <code>invoke</code></h3>\
         <form method=\"post\" action=\"/act/surface\" class=\"row\" data-turn=\"invoke\">\
         <input type=\"hidden\" name=\"surface\" value=\"objective-call\"><input type=\"hidden\" name=\"turn\" value=\"invoke\">\
         <input type=\"hidden\" name=\"object\" value=\"{n}\">\
         <div><label for=\"wc-method-{n}\">Method</label>{method_control}</div>\
         <div><label for=\"wc-var-{n}\">Variant tag (optional)</label><input id=\"wc-var-{n}\" name=\"variant\" type=\"text\" placeholder=\"defaults to method\"></div>\
         <div><label for=\"wc-fields-{n}\">Fields (<code>key=value</code>)</label><input id=\"wc-fields-{n}\" name=\"fields\" type=\"text\" placeholder=\"amount=10, milestone=1\"></div>\
         <button>Invoke</button></form></article>\
         <article data-surface=\"objective-send\"><h3>ObjectiveSend · <code>send</code> &amp; <code>deliver</code></h3>\
         <form method=\"post\" action=\"/act/surface\" class=\"row\" data-turn=\"send\">\
         <input type=\"hidden\" name=\"surface\" value=\"objective-send\"><input type=\"hidden\" name=\"turn\" value=\"send\">\
         <input type=\"hidden\" name=\"source\" value=\"{n}\">\
         <div><label for=\"ws-target-{n}\">Target object</label><input id=\"ws-target-{n}\" name=\"target\" type=\"text\" required></div>\
         <div><label for=\"ws-var-{n}\">Message tag</label><input id=\"ws-var-{n}\" name=\"variant\" type=\"text\" placeholder=\"e.g. credit, lease\" required></div>\
         <div><label for=\"ws-fields-{n}\">Payload fields (<code>key=value</code>)</label><input id=\"ws-fields-{n}\" name=\"fields\" type=\"text\" placeholder=\"amount=25, epoch=3\"></div>\
         <button>Send</button></form>\
         <form method=\"post\" action=\"/act/surface\" class=\"row\" data-turn=\"deliver\">\
         <input type=\"hidden\" name=\"surface\" value=\"objective-send\"><input type=\"hidden\" name=\"turn\" value=\"deliver\">\
         <div><label for=\"wd-obj-{n}\">Object cell</label><input id=\"wd-obj-{n}\" name=\"object\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"wd-tx-{n}\">Transaction</label><input id=\"wd-tx-{n}\" name=\"transaction\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <button>Deliver</button></form></article>\
         <article data-surface=\"objective-activity\"><h3>ObjectiveActivity · <code>spawn</code> &amp; <code>reply</code></h3>\
         <form method=\"post\" action=\"/act/surface\" class=\"row\" data-turn=\"spawn\">\
         <input type=\"hidden\" name=\"surface\" value=\"objective-activity\"><input type=\"hidden\" name=\"turn\" value=\"spawn\">\
         <input type=\"hidden\" name=\"object\" value=\"{n}\">\
         <div><label for=\"wa-bend-{n}\">Program (bend)</label><input id=\"wa-bend-{n}\" name=\"bend\" type=\"text\" required></div>\
         <div><label for=\"wa-fields-{n}\">Input fields (<code>key=value</code>)</label><input id=\"wa-fields-{n}\" name=\"fields\" type=\"text\" placeholder=\"init=set(0), decider=42\"></div>\
         <div><label for=\"wa-seed-{n}\">Seed fields (optional)</label><input id=\"wa-seed-{n}\" name=\"seed_fields\" type=\"text\" placeholder=\"total=0\"></div>\
         <button>Spawn</button></form>\
         <form method=\"post\" action=\"/act/surface\" class=\"row\" data-turn=\"reply\">\
         <input type=\"hidden\" name=\"surface\" value=\"objective-activity\"><input type=\"hidden\" name=\"turn\" value=\"reply\">\
         <div><label for=\"war-slot-{n}\">Reply slot</label><input id=\"war-slot-{n}\" name=\"slot\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"war-fields-{n}\">Reply fields (<code>key=value</code>)</label><input id=\"war-fields-{n}\" name=\"fields\" type=\"text\" placeholder=\"amount=7\"></div>\
         <button>Reply</button></form></article>\
         <article data-surface=\"seat-store\"><h3>SeatStore · <code>create</code>, <code>fund</code>, <code>act</code>, <code>exit</code></h3>\
         <form method=\"post\" action=\"/act/surface\" class=\"row\" data-turn=\"create\">\
         <input type=\"hidden\" name=\"surface\" value=\"seat-store\"><input type=\"hidden\" name=\"turn\" value=\"create\">\
         <div><label for=\"sc-obj-{n}\">Object cell</label><input id=\"sc-obj-{n}\" name=\"object\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"sc-pkg-{n}\">Package id</label><input id=\"sc-pkg-{n}\" name=\"package\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"sc-pay-{n}\">Payer account</label><input id=\"sc-pay-{n}\" name=\"payer\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"sc-inv-{n}\">Invitations (<code>role:holder</code>)</label><input id=\"sc-inv-{n}\" name=\"invitations\" type=\"text\" placeholder=\"bidder:42, seller:43\"></div>\
         <button>Create instance</button></form>\
         <form method=\"post\" action=\"/act/surface\" class=\"row\" data-turn=\"fund\">\
         <input type=\"hidden\" name=\"surface\" value=\"seat-store\"><input type=\"hidden\" name=\"turn\" value=\"fund\">\
         <div><label for=\"sf-inv-{n}\">Invitation / seat id</label><input id=\"sf-inv-{n}\" name=\"invitation\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"sf-fund-{n}\">Funding / holder account</label><input id=\"sf-fund-{n}\" name=\"funding\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"sf-pay-{n}\">Payee account</label><input id=\"sf-pay-{n}\" name=\"payee\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"sf-give-{n}\">Give (<code>asset:amount</code>)</label><input id=\"sf-give-{n}\" name=\"give\" type=\"text\" placeholder=\"1:500\" required></div>\
         <div><label for=\"sf-want-{n}\">Want (<code>asset:amount</code>)</label><input id=\"sf-want-{n}\" name=\"want\" type=\"text\" placeholder=\"2:10\"></div>\
         <div><label for=\"sf-exit-{n}\">Exit rule</label><input id=\"sf-exit-{n}\" name=\"exit_rule\" type=\"text\" value=\"onDemand\"></div>\
         <button>Fund seat</button></form>\
         <form method=\"post\" action=\"/act/surface\" class=\"row\" data-turn=\"act\">\
         <input type=\"hidden\" name=\"surface\" value=\"seat-store\"><input type=\"hidden\" name=\"turn\" value=\"act\">\
         <div><label for=\"sa-inst-{n}\">Instance id</label><input id=\"sa-inst-{n}\" name=\"instance\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"sa-pay-{n}\">Payer account</label><input id=\"sa-pay-{n}\" name=\"payer\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <div><label for=\"sa-var-{n}\">Action / variant</label><input id=\"sa-var-{n}\" name=\"variant\" type=\"text\" placeholder=\"clear, reallocate, settle\"></div>\
         <div><label for=\"sa-fields-{n}\">Action fields (<code>key=value</code>)</label><input id=\"sa-fields-{n}\" name=\"fields\" type=\"text\" placeholder=\"price=50, currency=1, goods=2, epsilon=0\"></div>\
         <button>Act / settle</button></form>\
         <form method=\"post\" action=\"/act/surface\" class=\"row\" data-turn=\"exit\">\
         <input type=\"hidden\" name=\"surface\" value=\"seat-store\"><input type=\"hidden\" name=\"turn\" value=\"exit\">\
         <div><label for=\"se-seat-{n}\">Seat account</label><input id=\"se-seat-{n}\" name=\"seat\" type=\"text\" inputmode=\"numeric\" pattern=\"[0-9]+\" required></div>\
         <button>Exit seat</button></form></article></section>"
    )
}

/// Render open seats and invitations if the object view includes a `seatStore` or `seats` projection.
fn render_seat_store_summary(object: &Value) -> String {
    let mut out = String::new();
    if let Some(state) = object.get("declaredState").or_else(|| object.get("state")).filter(|s| s.is_object()) {
        let table = inspect_data_table(state);
        if !table.is_empty() {
            out.push_str(&format!("<section data-declared-state><h2>Declared state</h2><p><code>{}</code></p>{table}</section>", escape(&format_human_data(state))));
        }
    }
    if let Some(seats) = object.get("seats").and_then(Value::as_array) {
        out.push_str("<section data-seat-table><h2>Open seats</h2><table><tr><th>Seat account</th><th>Offerer</th><th>Payee</th><th>Give</th><th>Want</th></tr>");
        for seat in seats {
            out.push_str(&format!(
                "<tr><td><code>{}</code></td><td><code>{}</code></td><td><code>{}</code></td><td><code>{}</code></td><td><code>{}</code></td></tr>",
                escape(seat["account"].as_str().unwrap_or("?")),
                escape(seat["offerer"].as_str().unwrap_or("?")),
                escape(seat["payee"].as_str().unwrap_or("?")),
                escape(&seat["give"].to_string()),
                escape(&seat["want"].to_string()),
            ));
        }
        out.push_str("</table></section>");
    }
    out
}

fn render(base: &str, name: &str, view: &Value, behavior: bool) -> Option<String> {
    let cell = &view["cell"];
    let (object, is_kind) = if cell["worldInstance"].is_object() {
        (&cell["worldInstance"], false)
    } else if cell["worldKind"].is_object() {
        (&cell["worldKind"], true)
    } else {
        return None;
    };
    let n = escape(name);
    let descriptor = &object["descriptor"];
    let mut html = format!(
        "<nav data-object-views><a href=\"{base}/object/{n}\">Fields</a> · \
        <a href=\"{base}/object/{n}/behavior\">Behavior and meaning</a></nav><p>{} · kind <code>{}</code> · revision <code>{}</code></p>",
        if is_kind { "Kind definition" } else { "Instance" },
        escape(descriptor["kind"].as_str().unwrap_or("?")),
        escape(descriptor["revision"].as_str().unwrap_or("?"))
    );
    if let Some(root) = object["kindRoot"].as_str() {
        html.push_str(&format!(
            "<p data-pinned-kind>Instance meaning pinned to kind root <code>{}</code>.</p>",
            escape(root)
        ));
    }
    if !behavior {
        html.push_str(&fields(object));
        html.push_str(&render_seat_store_summary(object));
    } else {
        html.push_str("<section data-object-behavior><h2>Methods</h2>");
        match object["methods"].as_array() {
            Some(methods) => {
                if methods.is_empty() {
                    html.push_str("<p>This definition has no named methods.</p>");
                }
                for method in methods {
                    html.push_str(&format!(
                        "<article><h3>{}</h3><p>Program <code>{}</code></p><table><tr><th>Output</th><th>Field</th><th>Key</th></tr>",
                        escape(method["name"].as_str().unwrap_or("?")),
                        escape(method["program"].as_str().unwrap_or("?"))
                    ));
                    if let Some(outputs) = method["outputs"].as_array() {
                        for output in outputs {
                            html.push_str(&format!(
                                "<tr><td>{}</td><td>{}</td><td>{}</td></tr>",
                                escape(output["output"].as_str().unwrap_or("?")),
                                escape(output["field"].as_str().unwrap_or("?")),
                                escape(output["key"].as_str().unwrap_or("?"))
                            ));
                        }
                    }
                    html.push_str("</table></article>");
                }
            }
            None => html.push_str("<p>No method table was disclosed by this read.</p>"),
        }
        html.push_str("</section><h2>Field meanings</h2><table><tr><th>Name</th><th>Meaning</th><th>Codec</th><th>Updates</th></tr>");
        if let Some(fields) = descriptor["fields"].as_array() {
            for field in fields {
                html.push_str(&format!(
                    "<tr><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>",
                    escape(field["name"].as_str().unwrap_or("?")),
                    escape(field["meaning"].as_str().unwrap_or("?")),
                    escape(field["codec"].as_str().unwrap_or("?")),
                    escape(field["discipline"].as_str().unwrap_or("?"))
                ));
            }
        }
        html.push_str("</table>");
        html.push_str(&render_seat_store_summary(object));
        html.push_str(&native_surface_controls(name, object));
        for (key, label) in [
            ("sampleSlots", "Source sample slots"),
            ("definitionBytes", "Canonical definition"),
            ("construction", "Construction and parents"),
            ("trace", "Definition trace"),
        ] {
            if let Some(value) = object.get(key) {
                html.push_str(&format!(
                    "<details data-object-{key}><summary>{label}</summary><pre>{}</pre></details>",
                    escape(&serde_json::to_string_pretty(value).unwrap_or_default())
                ));
            }
        }
        html.push_str(&format!(
            "<details><summary>Full disclosed object record</summary><pre>{}</pre></details>",
            escape(&serde_json::to_string_pretty(object).unwrap_or_default())
        ));
    }
    Some(html)
}

fn fields(object: &Value) -> String {
    let mut html =
        String::from("<table data-object-fields><tr><th>Field</th><th>Key</th><th>Value</th></tr>");
    let entries = object["entries"]
        .as_array()
        .or_else(|| object["defaults"].as_array());
    if let Some(entries) = entries {
        for entry in entries {
            let id = entry["field"].as_str().unwrap_or("?");
            let field = object["descriptor"]["fields"]
                .as_array()
                .and_then(|fields| fields.iter().find(|f| f["id"].as_str() == Some(id)));
            let label = field.and_then(|f| f["name"].as_str()).unwrap_or(id);
            let value = entry["value"].as_str().unwrap_or("?");
            let shown = if field.is_some_and(|f| f["codec"] == "bytes") {
                mini_sdk::hex::decode(value)
                    .ok()
                    .and_then(|bytes| String::from_utf8(bytes).ok())
                    .filter(|text| {
                        !text
                            .chars()
                            .any(|c| c.is_control() && !matches!(c, '\n' | '\t'))
                    })
                    .unwrap_or_else(|| format!("hex: {value}"))
            } else {
                value.to_owned()
            };
            html.push_str(&format!(
                "<tr><td>{} <small><code>{}</code></small></td><td>{}</td><td><pre>{}</pre></td></tr>",
                escape(label),
                escape(id),
                escape(entry["key"].as_str().unwrap_or("?")),
                escape(&shown)
            ));
        }
    }
    html.push_str("</table>");
    html
}

/// Dispatch a structured form submission for any of the four native surfaces (`ObjectiveCall`,
/// `ObjectiveSend`, `ObjectiveActivity`, `SeatStore`) into its canonical turn JSON.
pub(crate) fn compile_surface_turn(
    surface: &str,
    turn: &str,
    form: &std::collections::BTreeMap<String, String>,
) -> std::result::Result<Value, String> {
    let f = |k: &str| form.get(k).map(String::as_str).unwrap_or("").trim();
    let f_or = |k1: &str, k2: &str| {
        let v = f(k1);
        if v.is_empty() { f(k2) } else { v }
    };
    let dec_or = |val: &str, default: &str| -> String {
        if decimal(val) {
            val.to_owned()
        } else {
            default.to_owned()
        }
    };
    match (surface, turn) {
        ("objective-call", "invoke") => {
            let mut spec = invoke_turn(
                f("object"),
                f_or("pin", "bend"),
                f_or("method", "variant"),
                f("variant"),
                f("fields"),
            )?;
            spec["hasFields"] = json!(!f("fields").is_empty());
            Ok(spec)
        }
        ("objective-send", "send") => send_turn(
            f_or("source", "bend"),
            f_or("target", "object"),
            f("variant"),
            f("fields"),
        ),
        ("objective-send", "deliver") => deliver_turn_spec(f("object"), f("transaction"), (!f("account").is_empty()).then(|| f("account"))),
        ("objective-activity", "spawn") => spawn_turn(
            f("bend"),
            f("object"),
            f("variant"),
            f("fields"),
            f("seed_fields"),
            (!f("deposit").is_empty()).then(|| f("deposit")),
        ),
        ("objective-activity", "reply") => reply_turn(f("slot"), f("mode"), f("variant"), f("fields"), f("refused")),
        ("seat-store", "create") => seat_create_turn(f("object"), f("package"), f("payer"), f("invitations")),
        ("seat-store", "fund") => {
            let invitation = f_or("invitation", "seat");
            let funding = f_or("funding", "holder");
            let payee = {
                let p = f_or("payee", "holder");
                if p.is_empty() { funding } else { p }
            };
            let mut spec = seat_fund_turn(
                invitation,
                funding,
                payee,
                f("give"),
                f("want"),
                f("exit_rule"),
                f("donate") == "on" || f("confirmDonation") == "true",
            )?;
            let give_objs: Vec<Value> = spec["turn"]["proposal"]["give"]
                .as_array()
                .map(|arr| {
                    arr.iter()
                        .filter_map(|pair| {
                            let p = pair.as_array()?;
                            Some(json!({
                                "asset": p.first()?.as_str()?,
                                "amount": p.get(1)?.as_str()?,
                            }))
                        })
                        .collect()
                })
                .unwrap_or_default();
            let want_objs: Vec<Value> = spec["turn"]["proposal"]["want"]
                .as_array()
                .map(|arr| {
                    arr.iter()
                        .filter_map(|pair| {
                            let p = pair.as_array()?;
                            Some(json!({
                                "asset": p.first()?.as_str()?,
                                "amount": p.get(1)?.as_str()?,
                            }))
                        })
                        .collect()
                })
                .unwrap_or_default();
            spec["turn"]["object"] = json!(dec_or(f_or("object", "instance"), "0"));
            spec["turn"]["package"] = json!(dec_or(f("package"), "0"));
            spec["turn"]["seat"] = json!(if !f("seat").is_empty() { f("seat") } else { invitation });
            spec["turn"]["role"] = json!(if f("role").is_empty() { "bid" } else { f("role") });
            spec["turn"]["holder"] = json!(if !f("holder").is_empty() { f("holder") } else { funding });
            spec["turn"]["giveJson"] = json!(give_objs);
            spec["turn"]["wantJson"] = json!(want_objs);
            Ok(spec)
        }
        ("seat-store", "act") => {
            let instance = f_or("instance", "object");
            let payer = f("payer");
            let mut spec = if !f("action_json").is_empty() {
                if !decimal(instance) || !decimal(payer) {
                    return Err("instance id and payer account must be canonical decimals".into());
                }
                let raw_action: Value = serde_json::from_str(f("action_json"))
                    .map_err(|e| format!("invalid action_json: {e}"))?;
                let argument = crate::seat::to_data_json(&raw_action);
                json!({
                    "surface": "SeatStore",
                    "turn": {
                        "kind": "invoke",
                        "instance": instance,
                        "payer": payer,
                        "argument": argument,
                        "actionJson": raw_action,
                    }
                })
            } else {
                seat_act_turn(instance, payer, f("variant"), f("fields"))?
            };
            spec["turn"]["package"] = json!(dec_or(f("package"), "0"));
            Ok(spec)
        }
        ("seat-store", "exit") => {
            let mut spec = seat_exit_turn(f_or("seat", "object"))?;
            spec["turn"]["object"] = json!(dec_or(f_or("object", "instance"), "0"));
            spec["turn"]["package"] = json!(dec_or(f("package"), "0"));
            Ok(spec)
        }
        _ => Err(format!("unknown surface `{surface}` / turn `{turn}`")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn object() -> Value {
        serde_json::json!({"cell":{"worldInstance":{"kindRoot":"901","descriptor":{"kind":"7","revision":"2",
        "fields":[{"id":"4","name":"Votes <yes>","meaning":"number of approvals","codec":"nat","discipline":"ram"}]},
        "entries":[{"field":"4","key":"0","value":"12"}],"methods":[{"name":"vote","program":"42","outputs":[{"output":"0","field":"4","key":"0"}]}],
        "sampleSlots":[["world/before/Votes","12"]]}}})
    }
    #[test]
    fn two_views_share_one_pinned_instance_and_escape_member_data() {
        let fields = render("/secret", "poll", &object(), false).unwrap();
        let behavior = render("/secret", "poll", &object(), true).unwrap();
        assert!(fields.contains("Votes &lt;yes&gt;"));
        assert!(fields.contains("12"));
        assert!(behavior.contains("number of approvals"));
        assert!(behavior.contains("vote"));
        assert!(behavior.contains("world/before/Votes"));
        assert!(behavior.contains("data-surface=\"objective-call\""));
        assert!(behavior.contains("data-surface=\"objective-send\""));
        assert!(behavior.contains("data-surface=\"objective-activity\""));
        assert!(behavior.contains("data-surface=\"seat-store\""));
        assert!(behavior.contains("name=\"surface\" value=\"objective-call\""));
        assert!(behavior.contains("name=\"surface\" value=\"seat-store\""));
        for view in [fields, behavior] {
            assert!(view.contains("901"));
            assert!(view.contains("/object/poll/behavior"));
        }
        assert!(render(
            "/secret",
            "other",
            &serde_json::json!({"cell":{"entries":[]}}),
            false
        )
        .is_none());
    }

    #[test]
    fn seat_store_and_native_surfaces_compile_from_structured_form_inputs() {
        let created = seat_create_turn("90", "777", "130", "bidder:42, seller:43").unwrap();
        assert_eq!(created["turn"]["kind"], "create");
        assert_eq!(created["turn"]["invitations"].as_array().unwrap().len(), 2);

        let funded = seat_fund_turn("501", "130", "130", "1:500", "2:10", "afterDeadline:200", false).unwrap();
        assert_eq!(funded["turn"]["kind"], "offer");
        assert_eq!(funded["turn"]["proposal"]["give"], json!([["1", "500"]]));
        assert_eq!(funded["turn"]["proposal"]["want"], json!([["2", "10"]]));
        assert_eq!(funded["turn"]["proposal"]["exit"], json!({"afterDeadline": "200"}));

        // Donation guard requires explicit confirmation when `want` is empty.
        assert!(seat_fund_turn("501", "130", "130", "1:500", "", "onDemand", false).is_err());
        let donated = seat_fund_turn("501", "130", "130", "1:500", "", "onDemand", true).unwrap();
        assert_eq!(donated["turn"]["proposal"]["donate"], true);

        let acted = seat_act_turn("90", "130", "clear", "price=50, currency=1, goods=2, epsilon=0, slacks=[0, 1]").unwrap();
        assert_eq!(acted["turn"]["kind"], "invoke");
        assert_eq!(acted["turn"]["argument"]["label"], "clear");
        let slacks_field = acted["turn"]["argument"]["payload"]["fields"]
            .as_array()
            .unwrap()
            .iter()
            .find(|f| f["name"] == "slacks")
            .unwrap();
        assert_eq!(slacks_field["value"]["tag"], "variant");
        assert_eq!(slacks_field["value"]["label"], "cons");

        let exited = seat_exit_turn("808").unwrap();
        assert_eq!(exited["turn"], json!({"kind": "exit", "seat": "808"}));

        let mut form = std::collections::BTreeMap::new();
        form.insert("object".into(), "poll".into());
        form.insert("method".into(), "vote".into());
        form.insert("fields".into(), "choice=1".into());
        let invoked = compile_surface_turn("objective-call", "invoke", &form).unwrap();
        assert_eq!(invoked["surface"], "ObjectiveCall");
        assert_eq!(invoked["method"], "vote");

        let mut send_form = std::collections::BTreeMap::new();
        send_form.insert("source".into(), "station-1".into());
        send_form.insert("target".into(), "desk-2".into());
        send_form.insert("variant".into(), "issue".into());
        send_form.insert("fields".into(), "slot=3, holder=42".into());
        let sent = compile_surface_turn("objective-send", "send", &send_form).unwrap();
        assert_eq!(sent["surface"], "ObjectiveSend");
        assert_eq!(sent["source"], "station-1");
        assert_eq!(sent["target"], "desk-2");

        let mut seat_form = std::collections::BTreeMap::new();
        seat_form.insert("instance".into(), "90".into());
        seat_form.insert("payer".into(), "130".into());
        seat_form.insert("variant".into(), "clear".into());
        seat_form.insert("fields".into(), "price=50, slacks=[0, 1]".into());
        let seat_acted = compile_surface_turn("seat-store", "act", &seat_form).unwrap();
        assert_eq!(seat_acted["turn"]["kind"], "invoke");
        assert_eq!(seat_acted["turn"]["instance"], "90");
    }
}
