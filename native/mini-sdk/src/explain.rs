//! `explain()`: the faithful human reading of what a key is about to sign.
//!
//! Input is only what the member's OWN local Host presented: the retained authoring JSON the
//! Host turned into `intent.bin` (op 7), and the Host's `inspect plan` decoding of the exact
//! `plan.bin` (op 8). This crate never decodes Lean canonical bytes itself. The function is
//! total: anything it has no reading for is a line beginning `UNKNOWN` that says not to sign
//! blind; nothing is elided. The reading closes with the byte digests it is bound to, and the
//! [`crate::confirm::Confirmation`] covers the SHA-256 of this exact text.
//!
//! The TS SDK (`native/mini-sdk-ts/src/explain.ts`) renders byte-identical text; the
//! differential runs it against this function compiled to wasm.
use serde_json::{Map, Value};

use crate::contracts::canonical_json;
use crate::hex;

/// Payload types the native author reads (`Host/SourceAgreementJson.lean` `targetPayload`).
pub const PAYLOAD_TYPES: &[&str] = &["scalar", "content", "append", "world", "kindDefinition", "computeFunding", "read"];
/// Content actions the native author reads (`contentAction`).
pub const CONTENT_ACTIONS: &[&str] = &[
    "createDocument", "createContainer", "editElement", "createAtom", "createRun", "editAtom", "link",
    "annotate", "rewrapAtom", "rewrapAnnotation", "unlink", "mark", "unmark", "transclude",
];
const HEX_FIELDS: &[&str] = &["payload", "wrapping", "topic", "contextBytes"];
const UNKNOWN: &str = "UNKNOWN";
const BLIND: &str = "do not sign blind";

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Explanation {
    pub lines: Vec<String>,
    /// The exact text the confirmation binds: lines joined by `\n`, with a trailing `\n`.
    pub text: String,
    /// True iff some line is `UNKNOWN …`. A host UI must show it; the SDK still lets a member
    /// confirm a reading they have seen, but never one they have not.
    pub has_unknown: bool,
}

/// Digests the reading is bound to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Bound {
    pub intent_sha256: [u8; 32],
    pub plan_sha256: [u8; 32],
    pub headers_sha256: [u8; 32],
}

/// A string as JSON spells it (TS: `JSON.stringify`).
fn quote(s: &str) -> String {
    serde_json::to_string(s).unwrap_or_default()
}

fn str_of(v: &Value) -> String {
    match v {
        Value::String(s) => s.clone(),
        other => canonical_json(other).unwrap_or_else(|_| "<non-canonical JSON>".into()),
    }
}

fn hex_field(text: &str) -> String {
    match hex::decode(text) {
        Ok(bytes) => {
            let readable = std::str::from_utf8(&bytes).ok().filter(|s| !s.chars().any(char::is_control));
            match readable {
                Some(s) if !bytes.is_empty() => format!("0x{text} ({} bytes, text {})", bytes.len(), quote(s)),
                _ => format!("0x{text} ({} bytes)", bytes.len()),
            }
        }
        Err(_) => format!("{UNKNOWN} non-hex {} — {BLIND}", quote(text)),
    }
}

fn fields(obj: &Map<String, Value>, skip: &[&str]) -> String {
    let mut out = Vec::new();
    for (k, v) in obj {
        if skip.contains(&k.as_str()) {
            continue;
        }
        let shown = match (HEX_FIELDS.contains(&k.as_str()), v) {
            (true, Value::String(s)) => hex_field(s),
            _ => str_of(v),
        };
        out.push(format!("{k}={shown}"));
    }
    out.join(" ")
}

fn payload_lines(payload: &Value, lines: &mut Vec<String>) {
    let Some(obj) = payload.as_object() else {
        lines.push(format!("    {UNKNOWN} payload {} — {BLIND}", str_of(payload)));
        return;
    };
    let ty = obj.get("type").and_then(Value::as_str).unwrap_or("");
    if !PAYLOAD_TYPES.contains(&ty) {
        lines.push(format!("    {UNKNOWN} payload type {}: {} — {BLIND}", quote(ty), str_of(payload)));
        return;
    }
    match (ty, obj.get("actions").and_then(Value::as_array)) {
        ("content", Some(actions)) => {
            lines.push(format!("    content: {} action(s)", actions.len()));
            for action in actions {
                let Some(a) = action.as_object() else {
                    lines.push(format!("      {UNKNOWN} action {} — {BLIND}", str_of(action)));
                    continue;
                };
                let verb = a.get("type").and_then(Value::as_str).unwrap_or("");
                if CONTENT_ACTIONS.contains(&verb) {
                    lines.push(format!("      {verb} {}", fields(a, &["type"])));
                } else {
                    lines.push(format!("      {UNKNOWN} content action {}: {} — {BLIND}", quote(verb), str_of(action)));
                }
            }
        }
        ("scalar", Some(actions)) => {
            lines.push(format!("    scalar: {} action(s)", actions.len()));
            for action in actions {
                lines.push(format!("      {}", str_of(action)));
            }
        }
        _ => lines.push(format!("    {ty}: {}", fields(obj, &["type"]))),
    }
}

fn intent_lines(intent: &Value, lines: &mut Vec<String>) {
    let expect = ["grants", "nonce", "purpose", "subject"];
    let Some(obj) = intent.as_object() else {
        lines.push(format!("{UNKNOWN} intent {} — {BLIND}", str_of(intent)));
        return;
    };
    for k in obj.keys().filter(|k| !expect.contains(&k.as_str())) {
        lines.push(format!("{UNKNOWN} intent field {}={} — {BLIND}", quote(k), str_of(&obj[k])));
    }
    let purpose = &intent["purpose"];
    let draft = &purpose["draft"];
    let command = &draft["command"];
    if purpose["type"] != "prepare" || draft["type"] != "invoke" || !command.is_object() {
        lines.push(format!("{UNKNOWN} purpose {} — {BLIND}", str_of(purpose)));
        return;
    }
    lines.push(format!("invoke by subject {} (intent nonce {}, command nonce {})",
        str_of(&intent["subject"]), str_of(&intent["nonce"]), str_of(&command["nonce"])));
    if command["subject"] != intent["subject"] {
        lines.push(format!("{UNKNOWN} command subject {} differs from intent subject — {BLIND}", str_of(&command["subject"])));
    }
    for (k, v) in command.as_object().into_iter().flatten() {
        if !["nonce", "subject", "targets", "family"].contains(&k.as_str()) {
            lines.push(format!("{UNKNOWN} command field {}={} — {BLIND}", quote(k), str_of(v)));
        }
    }
    if let Some(grants) = intent["grants"].as_array() {
        for g in grants {
            lines.push(format!("  observes {} {} with capability {}", str_of(&g["kind"]), str_of(&g["target"]), str_of(&g["capability"])));
        }
    }
    for t in command["targets"].as_array().into_iter().flatten() {
        lines.push(format!("  writes {} {} at expected root {} with capability {} (observe {}), schema {}",
            str_of(&t["kind"]), str_of(&t["target"]), str_of(&t["expectedTargetRoot"]),
            str_of(&t["capability"]), str_of(&t["observeCapability"]), str_of(&t["schemaVersion"])));
        payload_lines(&t["payload"], lines);
    }
    if let Some(f) = command.get("family") {
        lines.push(format!("  family route {} context {}", str_of(&f["route"]), hex_field(f["contextBytes"].as_str().unwrap_or("?"))));
    }
}

fn plan_lines(plan: &Value, lines: &mut Vec<String>) {
    let draft = &plan["finalizedDraft"];
    lines.push(format!("plan at height {} world root {} domain {}: draft {}",
        str_of(&plan["height"]), str_of(&plan["worldRoot"]), str_of(&plan["domain"]), str_of(&draft["type"])));
    if draft["type"] != "invoke" {
        lines.push(format!("{UNKNOWN} plan draft type {} for an invoke intent — {BLIND}", str_of(&draft["type"])));
    }
    let slots = plan["slots"].as_array().cloned().unwrap_or_default();
    lines.push(format!("  {} signature slot(s)", slots.len()));
    for s in &slots {
        let g = &s["signing"];
        let decoded = g["decoded"] == Value::Bool(true);
        lines.push(format!("  role {} slot {}: key {} epoch {} valid until height {}, {} footprint cell(s)",
            str_of(&s["role"]), str_of(&s["index"]), str_of(&g["keyId"]), str_of(&g["keyEpoch"]),
            str_of(&g["validUntil"]), g["footprint"].as_array().map_or(0, Vec::len)));
        if !decoded {
            lines.push(format!("  {UNKNOWN} role {} slot {} is not decoded by the local Host — {BLIND}", str_of(&s["role"]), str_of(&s["index"])));
        }
    }
}

/// Render the reading of `intent` (the retained authoring JSON) and `plan` (the local Host's
/// `inspect plan` of the exact plan bytes), bound to `bound`.
pub fn explain(intent: &Value, plan: &Value, bound: &Bound) -> Explanation {
    let mut lines = Vec::new();
    intent_lines(intent, &mut lines);
    plan_lines(plan, &mut lines);
    lines.push(format!("bound to [intent {}] [plan {}] [headers {}]",
        hex::encode(&bound.intent_sha256), hex::encode(&bound.plan_sha256), hex::encode(&bound.headers_sha256)));
    let has_unknown = lines.iter().any(|l| l.trim_start().starts_with(UNKNOWN));
    let mut text = lines.join("\n");
    text.push('\n');
    Explanation { lines, text, has_unknown }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    const BOUND: Bound = Bound { intent_sha256: [1; 32], plan_sha256: [2; 32], headers_sha256: [3; 32] };

    #[test]
    fn unknown_actions_payloads_and_fields_are_surfaced_never_elided() {
        let intent = json!({"grants":[],"nonce":"1","subject":"5","extra":true,"purpose":{"type":"prepare","draft":{"type":"invoke",
            "command":{"nonce":"2","subject":"5","targets":[
                {"kind":"object","target":"9","expectedTargetRoot":"1","capability":"3","observeCapability":"3","schemaVersion":"9",
                 "payload":{"type":"content","actions":[{"type":"launchMissiles","n":"1"}]}},
                {"kind":"object","target":"9","expectedTargetRoot":"1","capability":"3","observeCapability":"3","schemaVersion":"9",
                 "payload":{"type":"teleport"}}]}}}});
        let plan = json!({"height":"1","worldRoot":"2","domain":"3","finalizedDraft":{"type":"invoke"},
            "slots":[{"index":"0","role":"4","signing":{"decoded":false,"keyId":"1","keyEpoch":"1","validUntil":"9","footprint":[]}}]});
        let e = explain(&intent, &plan, &BOUND);
        assert!(e.has_unknown);
        for needle in ["UNKNOWN intent field \"extra\"", "UNKNOWN content action \"launchMissiles\"",
            "UNKNOWN payload type \"teleport\"", "UNKNOWN role 4 slot 0 is not decoded"] {
            assert!(e.text.contains(needle), "missing {needle}:\n{}", e.text);
        }
        assert!(e.text.ends_with(&format!("[headers {}]\n", "03".repeat(32))));
    }

    #[test]
    fn a_changed_byte_in_any_rendered_field_changes_the_text() {
        let intent: Value = serde_json::from_str(include_str!("../tests/fixtures/intent.json")).unwrap();
        let plan: Value = serde_json::from_str(include_str!("../tests/fixtures/plan.json")).unwrap();
        let base = explain(&intent, &plan, &BOUND);
        assert!(!base.has_unknown, "{}", base.text);
        let mut moved = intent.clone();
        moved["purpose"]["draft"]["command"]["targets"][0]["payload"]["actions"][0]["payload"] = json!("62");
        assert_ne!(explain(&moved, &plan, &BOUND).text, base.text);
        let mut rerooted = plan.clone();
        rerooted["slots"][0]["signing"]["validUntil"] = json!("356");
        assert_ne!(explain(&intent, &rerooted, &BOUND).text, base.text);
    }
}
