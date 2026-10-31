//! Typed, package-pinned application tools (docs/APP-INTERFACE-2026-10-28.md).
//!
//! An operator-installed attachment pairs a declaration with an existing lifetime route. The
//! confined Hermes MCP worker runs the SDK's one executor (`Declaration::execute`), so the
//! model sees semantic tools while every HTTP request the executor prepares crosses the
//! ordinary Mini application API, one fresh admission and settlement each, through the
//! controller's `__mini_typed_http_raw` broker operation (the pattern of the GitWeb worker).
//! A declaration or attachment confers no grant: the route's native authority, the room's
//! `hermes/tools` apps bit and the app's own member permissions are each checked at dispatch.
use crate::Result;
use mini_sdk::app_interface::{Declaration, NativeReply, PreparedCall, Refusal, SessionBinding};
use serde::{Deserialize, Serialize};
use serde_json::{json, Map, Value};
use std::path::PathBuf;

/// The broker operation the MCP worker uses; internal (`__`), never offered to the model.
pub(crate) const RAW_TOOL: &str = "__mini_typed_http_raw";
const MAX_ATTACHMENTS: usize = 8;
const MAX_DECLARATION_BYTES: usize = 1024 * 1024;
const MAX_REPLY_BYTES: usize = 1024 * 1024;

pub(crate) fn is_raw_tool(name: &str) -> bool {
    name == RAW_TOOL
}

/// Controller configuration (`toolTask.typedApplications`). Paths select controller-owned
/// regular files; the route must already be one of `allowedApplicationLifetimeRoutes`.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct TypedApplicationAttachment {
    pub alias: String,
    pub declaration_path: PathBuf,
    /// The declaration's own digest (`Declaration::sha256`), not a file hash.
    pub declaration_sha256: String,
    pub package_id: String,
    pub route_name: String,
}

/// What the confined MCP worker learns about one attachment: the declaration it executes and
/// the route identities the SDK compares across callbacks. No socket, key or grant path.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CatalogEntry {
    pub alias: String,
    pub declaration: String,
    pub declaration_sha256: String,
    pub package_id: String,
    pub subject: String,
    pub app: String,
    pub generation: String,
    pub session: String,
    pub session_generation: String,
}

pub(crate) fn load(attachment: &TypedApplicationAttachment) -> Result<(Declaration, String)> {
    let bytes = crate::bounded_regular_file(&attachment.declaration_path, MAX_DECLARATION_BYTES)?;
    let declaration = Declaration::load(&bytes).map_err(|r| format!("typed declaration {}: {r}", attachment.alias))?;
    if declaration.sha256 != attachment.declaration_sha256 || declaration.package_id != attachment.package_id {
        return Err(format!("typed declaration {} differs from its attachment pin", attachment.alias));
    }
    let text = String::from_utf8(bytes).map_err(|_| "typed declaration is not UTF-8".to_owned())?;
    Ok((declaration, text))
}

/// Operator configuration check: unique aliases and tool names, every route an existing
/// lifetime route, every declaration loadable and equal to its pin.
pub(crate) fn validate(attachments: &[TypedApplicationAttachment], lifetime_routes: &[String]) -> Result<()> {
    if attachments.len() > MAX_ATTACHMENTS {
        return Err(format!("typedApplications exceeds {MAX_ATTACHMENTS} entries"));
    }
    let mut aliases = std::collections::HashSet::new();
    let mut names = std::collections::HashSet::new();
    for attachment in attachments {
        if !aliases.insert(attachment.alias.as_str()) {
            return Err("typedApplications has a duplicate alias".into());
        }
        if !lifetime_routes.contains(&attachment.route_name) {
            return Err("typedApplications requires a configured lifetime API route".into());
        }
        let (declaration, _) = load(attachment)?;
        for tool in declaration.bound_tools(&attachment.alias).map_err(|r| r.to_string())? {
            let name = tool["name"].as_str().ok_or("typed tool name absent")?.to_owned();
            if !names.insert(name) {
                return Err("typedApplications has a duplicate tool name".into());
            }
        }
    }
    Ok(())
}

/// Every bound tool name the attachments project, for the exact-catalogue check of a
/// restricted resident's ACP session.
pub(crate) fn tool_names(attachments: &[TypedApplicationAttachment]) -> Vec<String> {
    attachments.iter().filter_map(|a| {
        let (declaration, _) = load(a).ok()?;
        declaration.bound_tools(&a.alias).ok()
    }).flatten().filter_map(|tool| tool["name"].as_str().map(|n| format!("mcp__mini_grain__{n}"))).collect()
}

pub(crate) fn catalog(
    attachments: &[TypedApplicationAttachment],
    routes: &[crate::application_api_tools::LifetimeRoutePin],
) -> Result<Vec<CatalogEntry>> {
    attachments.iter().map(|a| {
        let route = routes.iter().find(|r| r.name == a.route_name)
            .ok_or("typed attachment route is absent")?;
        let (_, declaration) = load(a)?;
        Ok(CatalogEntry {
            alias: a.alias.clone(), declaration, declaration_sha256: a.declaration_sha256.clone(),
            package_id: a.package_id.clone(), subject: route.participant_subject.clone(),
            app: route.app_resource.clone(), generation: route.original_descriptor_sha256.clone(),
            session: route.session_resource.clone(), session_generation: route.grant_digest.clone(),
        })
    }).collect()
}

/// The controller's translation of one MCP worker request into the ordinary application API
/// arguments for the attachment's route. Alias, package and declaration must equal the
/// controller's own pins; the worker never chooses the route.
pub(crate) fn raw_arguments(attachments: &[TypedApplicationAttachment], request: &Value) -> Result<Value> {
    let object = request.as_object().ok_or("typed request must be an object")?;
    const KEYS: [&str; 10] = ["alias", "declarationSha256", "packageId", "operation", "write",
        "method", "path", "query", "headers", "bodyHex"];
    if object.keys().any(|k| !KEYS.contains(&k.as_str())) {
        return Err("typed request has unknown fields".into());
    }
    let text = |key: &str| object.get(key).and_then(Value::as_str).ok_or_else(|| format!("typed request {key} must be a string"));
    let alias = text("alias")?;
    let attachment = attachments.iter().find(|a| a.alias == alias)
        .ok_or_else(|| format!("refused: typed-app-not-attached: no attachment {alias:?} on this controller"))?;
    if text("declarationSha256")? != attachment.declaration_sha256 || text("packageId")? != attachment.package_id {
        return Err("refused: typed-declaration-mismatch: the request names a declaration or package other than the attachment's pin".into());
    }
    let mut mapped = Map::new();
    mapped.insert("application".into(), json!(attachment.route_name));
    for key in ["method", "path", "query", "headers", "bodyHex"] {
        mapped.insert(key.into(), object.get(key).cloned().ok_or_else(|| format!("typed request {key} absent"))?);
    }
    Ok(Value::Object(mapped))
}

/// `refused: NAME: detail` is the controller's no-send refusal spelling.
fn named_refusal(text: &str) -> Option<Refusal> {
    let rest = text.strip_prefix("refused: ")?;
    let name = rest.split(':').next()?.trim();
    (!name.is_empty() && name.len() <= 64 && name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-'))
        .then(|| Refusal { name: name.to_owned(), uncertain: false })
}

/// One controller reply to one prepared call, as the SDK callback result.
fn native_reply(reply: &Value) -> std::result::Result<NativeReply, Refusal> {
    let uncertain = |name: &str| Refusal { name: name.into(), uncertain: true };
    let text = reply.get("text").and_then(Value::as_str).unwrap_or("");
    if reply.get("isError").and_then(Value::as_bool) != Some(false) {
        if let Some(refusal) = named_refusal(text) {
            return Err(refusal);
        }
        return Err(match serde_json::from_str::<Value>(text) {
            Ok(v) if v["type"] == "refused-v3" => Refusal {
                name: format!("native-refused-{}", v["code"].as_str().unwrap_or("unnamed")),
                uncertain: false,
            },
            Ok(v) if v["type"] == "uncertain-v3" => uncertain(&format!("native-uncertain-{}", v["phase"].as_str().unwrap_or("unnamed"))),
            _ => uncertain("native-outcome-unknown"),
        });
    }
    let frame: Value = serde_json::from_str(text).map_err(|_| uncertain("native-reply-malformed"))?;
    if frame["type"] != "http-v3" {
        return Err(uncertain("native-reply-not-definite"));
    }
    let status = frame["status"].as_u64().filter(|s| (100..=599).contains(s)).ok_or_else(|| uncertain("native-reply-malformed"))? as u16;
    let hex = frame["bodyHex"].as_str().filter(|h| h.len() <= MAX_REPLY_BYTES * 2).ok_or_else(|| uncertain("native-reply-malformed"))?;
    let body = mini_sdk::hex::decode(hex).map_err(|_| uncertain("native-reply-malformed"))?;
    let headers = frame["headers"].as_array().into_iter().flatten().filter_map(|h| {
        Some((h["name"].as_str()?.to_owned(), h["value"].as_str()?.to_owned()))
    }).collect();
    let mut receipt = frame.clone();
    if let Some(object) = receipt.as_object_mut() {
        object.remove("bodyHex");
        object.insert("bodyBytes".into(), json!(body.len()));
    }
    Ok(NativeReply { status, headers, body, receipt })
}

fn prepared_request(entry: &CatalogEntry, call: &PreparedCall) -> Value {
    json!({
        "alias": entry.alias, "declarationSha256": call.declaration_sha256, "packageId": call.package_id,
        "operation": call.operation, "write": call.write,
        "method": call.method, "path": call.path, "query": call.query,
        "headers": call.ordered_headers.iter().map(|(n, v)| json!({"name":n,"value":v})).collect::<Vec<_>>(),
        "bodyHex": mini_sdk::hex::encode(&call.body),
    })
}

/// The bound tools an attachment projects, in MCP shape: the SDK's tool plus only standard
/// keys, so a client never meets the executor's own bookkeeping fields.
pub fn listed_tools(entry: &CatalogEntry) -> Result<Vec<Value>> {
    let declaration = Declaration::load(entry.declaration.as_bytes()).map_err(|r| r.to_string())?;
    if declaration.sha256 != entry.declaration_sha256 || declaration.package_id != entry.package_id {
        return Err("typed declaration differs from its catalog digest".into());
    }
    Ok(declaration.bound_tools(&entry.alias).map_err(|r| r.to_string())?.into_iter().map(|tool| {
        let mut shown = Map::new();
        for key in ["name", "description", "inputSchema", "outputSchema", "annotations", "_meta"] {
            if let Some(v) = tool.get(key) {
                shown.insert(key.into(), v.clone());
            }
        }
        Value::Object(shown)
    }).collect())
}

/// Does `name` belong to this entry's projection?
pub fn owns_tool(entry: &CatalogEntry, name: &str) -> bool {
    listed_tools(entry).is_ok_and(|tools| tools.iter().any(|t| t["name"] == name))
}

fn receipt_reference(receipt: &Value) -> Value {
    let mut reference = Map::new();
    for key in ["type", "operationId", "operationFingerprint", "bindingSha256", "status"] {
        if let Some(v) = receipt.get(key) {
            reference.insert(key.into(), v.clone());
        }
    }
    Value::Object(reference)
}

fn entropy<const N: usize>() -> std::io::Result<[u8; N]> {
    use std::io::Read;
    let mut bytes = [0u8; N];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut bytes)?;
    Ok(bytes)
}

/// Trusted per-invocation inputs for the executor: a fresh operation id, time and rendezvous seed
/// (never from the model's arguments) and the session binding the SDK compares across callbacks.
fn trusted_inputs(entry: &CatalogEntry) -> std::result::Result<(Value, SessionBinding), &'static str> {
    let (Ok(seed), Ok(operation_id)) = (entropy::<32>(), entropy::<8>()) else {
        return Err("entropy-unavailable");
    };
    let now_ms = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_millis() as u64);
    let context = json!({
        "operationId": mini_sdk::hex::encode(&operation_id),
        "nowMs": now_ms,
        "rendezvousSeed": mini_sdk::hex::encode(&seed),
    });
    let binding = SessionBinding {
        package_id: entry.package_id.clone(), subject: entry.subject.clone(), app: entry.app.clone(),
        generation: entry.generation.clone(), session: entry.session.clone(),
        session_generation: entry.session_generation.clone(),
    };
    Ok((context, binding))
}

fn finish(execution: mini_sdk::app_interface::Execution) -> Value {
    let references: Vec<Value> = execution.receipts.iter().map(receipt_reference).collect();
    match execution.outcome {
        Ok(value) => json!({
            "isError": false,
            "text": json!({"value": value, "nativeReceipts": references}).to_string(),
            "structured": {"value": value},
        }),
        Err(refusal) => refusal_result(&refusal.name, refusal.uncertain, &references),
    }
}

fn refusal_result(name: &str, uncertain: bool, references: &[Value]) -> Value {
    json!({
        "isError": true,
        "text": json!({"refusal": name, "uncertain": uncertain, "nativeReceipts": references}).to_string(),
    })
}

fn checked_declaration(entry: &CatalogEntry) -> std::result::Result<Declaration, Value> {
    let Ok(declaration) = Declaration::load(entry.declaration.as_bytes()) else {
        return Err(refusal_result("declaration-invalid", false, &[]));
    };
    if declaration.sha256 != entry.declaration_sha256 || declaration.package_id != entry.package_id {
        return Err(refusal_result("declaration-binding-mismatch", false, &[]));
    }
    Ok(declaration)
}

/// Run one typed tool call in the MCP worker. `forward` sends one prepared request to the
/// controller and returns its `{isError, text}` reply. The result is the MCP tool result:
/// `isError`, `text`, and for a success `structured` (`{value}`, the declared output).
pub fn call_tool(entry: &CatalogEntry, tool_name: &str, arguments: &Value, forward: &mut dyn FnMut(Value) -> Value) -> Value {
    let declaration = match checked_declaration(entry) { Ok(d) => d, Err(refusal) => return refusal };
    let operation = declaration.bound_tools(&entry.alias).ok().and_then(|tools| {
        tools.into_iter().find(|t| t["name"] == tool_name).and_then(|t| t["operation"].as_str().map(str::to_owned))
    });
    let Some(operation) = operation else {
        return refusal_result("typed-tool-unknown", false, &[]);
    };
    let (context, binding) = match trusted_inputs(entry) { Ok(v) => v, Err(name) => return refusal_result(name, false, &[]) };
    let execution = declaration.execute(&operation, arguments, &context, &binding, |same, call| {
        if same != &binding {
            return Err(Refusal { name: "session-binding-changed".into(), uncertain: false });
        }
        native_reply(&forward(prepared_request(entry, call)))
    });
    finish(execution)
}

/// The operator-foreground tools: the attachment's bound tools and its hidden qualification tool
/// (`mini_app_<alias>_qualify`, mini_sdk::app_interface::qualification_tool_name).
pub(crate) fn is_foreground_name(name: &str) -> bool {
    name.starts_with("mini_app_") && name.len() <= 64 && name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

/// The catalog entry a foreground tool name belongs to, and whether it is the qualification tool.
pub(crate) fn foreground_entry<'a>(entries: &'a [CatalogEntry], name: &str) -> Option<(&'a CatalogEntry, bool)> {
    entries.iter().find_map(|entry| {
        if mini_sdk::app_interface::qualification_tool_name(&entry.alias).is_ok_and(|q| q == name) {
            Some((entry, true))
        } else if owns_tool(entry, name) {
            Some((entry, false))
        } else {
            None
        }
    })
}

/// Foreground arguments carry the operator shell's `_miniInterfaceDigest`, which must equal the
/// attachment's pinned declaration digest and is stripped before the executor validates the rest.
/// Qualification arrives as `{context: ARGS}`.
pub(crate) fn foreground_arguments(entry: &CatalogEntry, arguments: &Value, qualify: bool) -> std::result::Result<Value, String> {
    let mut object = arguments.as_object().cloned().ok_or("refused: typed-arguments-invalid: arguments must be an object")?;
    match object.remove("_miniInterfaceDigest").as_ref().and_then(Value::as_str) {
        Some(digest) if digest == entry.declaration_sha256 => {}
        _ => return Err("refused: typed-declaration-mismatch: the call names a declaration digest other than the attachment's pin".into()),
    }
    if !qualify {
        return Ok(Value::Object(object));
    }
    if object.len() != 1 {
        return Err("refused: typed-arguments-invalid: qualification takes only {context}".into());
    }
    object.remove("context").filter(Value::is_object).ok_or_else(|| "refused: typed-arguments-invalid: qualification context must be an object".into())
}

/// Run the declaration's qualification scenario through the same executor and the same per-request
/// callback as a bound call (one fresh admission and settlement each). `context` is the operator's
/// scenario context (`runId`); the trusted operation id, time and seed are the controller's own.
pub fn qualify_tool(entry: &CatalogEntry, operator_context: &Value, forward: &mut dyn FnMut(Value) -> Value) -> Value {
    let declaration = match checked_declaration(entry) { Ok(d) => d, Err(refusal) => return refusal };
    let (mut context, binding) = match trusted_inputs(entry) { Ok(v) => v, Err(name) => return refusal_result(name, false, &[]) };
    if let (Some(trusted), Some(given)) = (context.as_object_mut(), operator_context.as_object()) {
        for (key, value) in given {
            if trusted.contains_key(key) {
                return refusal_result("context-key-reserved", false, &[]);
            }
            trusted.insert(key.clone(), value.clone());
        }
    }
    let execution = declaration.qualify(&context, &binding, |same, call| {
        if same != &binding {
            return Err(Refusal { name: "session-binding-changed".into(), uncertain: false });
        }
        native_reply(&forward(prepared_request(entry, call)))
    });
    finish(execution)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn attachment(alias: &str, route: &str) -> TypedApplicationAttachment {
        TypedApplicationAttachment {
            alias: alias.into(), declaration_path: "/nonexistent".into(),
            declaration_sha256: "ab".repeat(32), package_id: "pkg".into(), route_name: route.into(),
        }
    }


    const GOGS: &str = include_str!("../../../apps/interfaces/gogs.json");
    const DAVROS: &str = include_str!("../../../apps/interfaces/davros.json");

    fn entry(alias: &str, text: &str) -> CatalogEntry {
        let declaration = Declaration::load(text.as_bytes()).unwrap();
        CatalogEntry {
            alias: alias.into(), declaration: text.into(), declaration_sha256: declaration.sha256.clone(),
            package_id: declaration.package_id.clone(), subject: "7".into(), app: "6100".into(),
            generation: "ab".repeat(32), session: "6209".into(), session_generation: "456".into(),
        }
    }

    fn pins(entries: &[&CatalogEntry]) -> Vec<TypedApplicationAttachment> {
        entries.iter().map(|e| TypedApplicationAttachment {
            alias: e.alias.clone(), declaration_path: "/nonexistent".into(), declaration_sha256: e.declaration_sha256.clone(),
            package_id: e.package_id.clone(), route_name: format!("{}-app", e.alias),
        }).collect()
    }

    fn http(status: u64, body: &[u8], id: &str) -> Value {
        json!({"isError":false,"text":json!({"type":"http-v3","protocol":"mini-spk-agent-api-v3","status":status,
            "headers":[{"name":"content-type","value":"application/json"}],
            "bodyHex":mini_sdk::hex::encode(body),"operationId":id,"operationFingerprint":"cd".repeat(32)}).to_string()})
    }

    /// The controller's half, as the real mapping sees it: every request must pass `raw_arguments`
    /// against the operator pins, and each yields one canned definite reply.
    fn controller<'a>(pins: &'a [TypedApplicationAttachment], log: &'a mut Vec<Value>, replies: &'a mut Vec<Value>) -> impl FnMut(Value) -> Value + 'a {
        move |request| {
            let mapped = raw_arguments(pins, &request).expect("the controller accepts what the executor prepared");
            let routes = pins.iter().map(|pin| pin.route_name.clone()).collect::<Vec<_>>();
            crate::application_api_tools::parse_input(&mapped, &routes)
                .expect("typed requests satisfy the receiving native HTTP profile");
            log.push(mapped);
            replies.remove(0)
        }
    }

    const WBO: &str = include_str!("../../../apps/interfaces/wbo.json");

    /// Davros qualification args are objects keyed `path`; the executor must resolve them as
    /// arguments (not as path-part bindings) and prepare the first request.
    #[test]
    fn qualification_resolves_arguments_that_are_named_path() {
        let dav = entry("dav", DAVROS);
        let mut first: Option<Value> = None;
        let mut forward = |request: Value| -> Value {
            first.get_or_insert(request);
            http(500, b"{}", "1")
        };
        let result = qualify_tool(&dav, &json!({"runId":"qb44d7585667c47f0"}), &mut forward);
        assert!(!result["text"].as_str().unwrap().contains("declaration-invalid"), "{result}");
        let request = first.expect("the first qualification step reaches the controller");
        assert_eq!(request["operation"], "directory.create", "{request}");
    }

    #[test]
    fn foreground_names_digest_and_qualification_context_are_checked() {
        let wbo = entry("wbo", WBO);
        let catalog = vec![wbo.clone()];
        assert!(is_foreground_name("mini_app_wbo_qualify") && !is_foreground_name("mini_app_wbo-qualify"));
        let (found, qualify) = foreground_entry(&catalog, "mini_app_wbo_qualify").expect("hidden qualification tool");
        assert!(qualify && found.alias == "wbo");
        let (_, qualify) = foreground_entry(&catalog, "mini_app_wbo_board_read").expect("bound tool");
        assert!(!qualify);
        assert!(foreground_entry(&catalog, "mini_app_other_board_read").is_none());
        let digest = json!(wbo.declaration_sha256);
        assert_eq!(foreground_arguments(&wbo, &json!({"board":"b","_miniInterfaceDigest":digest}), false).unwrap(), json!({"board":"b"}));
        assert!(foreground_arguments(&wbo, &json!({"board":"b","_miniInterfaceDigest":"00"}), false).unwrap_err().contains("typed-declaration-mismatch"));
        assert!(foreground_arguments(&wbo, &json!({"board":"b"}), false).unwrap_err().contains("typed-declaration-mismatch"));
        assert_eq!(foreground_arguments(&wbo, &json!({"context":{"runId":"r1"},"_miniInterfaceDigest":digest}), true).unwrap(), json!({"runId":"r1"}));
        assert!(foreground_arguments(&wbo, &json!({"context":{},"extra":1,"_miniInterfaceDigest":digest}), true).is_err());
        let mut never = |_: Value| -> Value { panic!("a reserved context key refuses before any dispatch") };
        let refused = qualify_tool(&wbo, &json!({"operationId":"x"}), &mut never);
        assert!(refused["text"].as_str().unwrap().contains("context-key-reserved"));
    }

    /// The WBO declaration's conversation qualification through the controller's real request mapping:
    /// every prepared CONVERSATION request passes `raw_arguments` and the native HTTP profile.
    #[test]
    fn qualification_runs_a_conversation_declaration_through_the_controller_mapping() {
        let wbo = entry("wbo", WBO);
        let pins = pins(&[&wbo]);
        let routes = vec![pins[0].route_name.clone()];
        let mut item = Value::Null;
        let mut sent = 0;
        let mut forward = |request: Value| -> Value {
            let mapped = raw_arguments(&pins, &request).expect("the controller accepts what the executor prepared");
            crate::application_api_tools::parse_input(&mapped, &routes).expect("CONVERSATION satisfies the native HTTP profile");
            if mapped["method"] == "GET" {
                assert_eq!(mapped["path"], "download/abc123", "the saved-export read");
                return http(200, br#"<svg><rect id="abc123"/></svg>"#, "12");
            }
            assert_eq!(mapped["method"], "CONVERSATION", "{mapped}");
            let q: Value = serde_json::from_slice(&mini_sdk::hex::decode(mapped["bodyHex"].as_str().unwrap()).unwrap()).unwrap();
            let mut frames: Vec<String> = vec![];
            if q["op"] == "open" { frames.push(r#"0{"sid":"s","pingInterval":25000}"#.into()); }
            if q["op"] == "send" {
                let text = q["text"].as_str().unwrap();
                if text == "40" {
                    frames.push("40".into());
                    frames.push(r#"42["broadcast",{"type":0,"fromSeq":0,"seq":0,"_children":[]}]"#.into());
                } else {
                    let v: Value = serde_json::from_str(text.strip_prefix("42").unwrap()).unwrap();
                    item = v[1].clone();
                    sent += 1;
                    frames.push(format!("42{}", json!(["broadcast", {"seq":1,"mutation":item}])));
                }
            }
            // Later connections (the read-back) replay the stored item.
            if q["op"] == "send" && q["text"] == "40" && !item.is_null() {
                frames.pop();
                frames.push(format!("42{}", json!(["broadcast", {"type":0,"fromSeq":0,"seq":1,"_children":[item]}])));
            }
            http(200, &serde_json::to_vec(&json!({"version":1,"channel":q["channel"],"op":q["op"],"frames":frames})).unwrap(), "11")
        };
        let result = qualify_tool(&wbo, &json!({"runId":"abc123"}), &mut forward);
        assert_eq!(result["isError"], false, "{result}");
        assert_eq!(sent, 1, "the write is sent exactly once");
    }

    #[test]
    fn two_apps_one_task_write_and_read_back_through_the_real_declarations() {
        let (gogs, dav) = (entry("gogs", GOGS), entry("dav", DAVROS));
        let pins = pins(&[&gogs, &dav]);
        let mut log = Vec::new();
        let repo = br#"{"id":1,"name":"notes","owner":{"id":2,"login":"alice"}}"#;
        let issue = br#"{"id":5,"number":1,"title":"first","body":"hi","state":"open"}"#;
        let mut replies = vec![http(201, repo, "1"), http(201, issue, "2"), http(201, b"", "3"), http(200, b"issue 1", "4")];
        let mut forward = controller(&pins, &mut log, &mut replies);
        let made = call_tool(&gogs, "mini_app_gogs_repo_create", &json!({"name":"notes","description":"d"}), &mut forward);
        assert_eq!(made["isError"], false, "{made}");
        assert_eq!(made["structured"]["value"]["name"], "notes");
        assert_eq!(made["structured"]["value"]["owner"]["id"], 2);
        let opened = call_tool(&gogs, "mini_app_gogs_issue_create", &json!({"owner":"alice","repo":"notes","title":"first","body":"hi"}), &mut forward);
        assert_eq!(opened["structured"]["value"]["number"], 1, "{opened}");
        let b64 = "aXNzdWUgMQ==";
        let put = call_tool(&dav, "mini_app_dav_file_put", &json!({"path":"issue.txt","contentBase64":b64}), &mut forward);
        assert_eq!(put["structured"]["value"]["status"], 201, "{put}");
        let got = call_tool(&dav, "mini_app_dav_file_get", &json!({"path":"issue.txt"}), &mut forward);
        assert_eq!(got["structured"]["value"]["contentBase64"], b64, "{got}");
        assert!(got["text"].as_str().unwrap().contains("operationFingerprint"), "the model-visible result names its native receipt");
        assert!(!got["text"].as_str().unwrap().contains("bodyHex"));
        drop(forward);
        let routes: Vec<_> = log.iter().map(|m| (m["application"].as_str().unwrap(), m["method"].as_str().unwrap(), m["path"].as_str().unwrap())).collect();
        assert_eq!(routes, [("gogs-app", "POST", "api/v1/user/repos"), ("gogs-app", "POST", "api/v1/repos/alice/notes/issues"),
            ("dav-app", "PUT", "dav/issue.txt"), ("dav-app", "GET", "dav/issue.txt")]);
    }

    #[test]
    fn a_refused_dispatch_is_named_stops_the_executor_and_carries_no_receipt() {
        let dav = entry("dav", DAVROS);
        let pins = pins(&[&dav]);
        let (mut log, mut replies) = (Vec::new(), vec![json!({"isError":true,"text":"refused: typed-apps-not-granted: this room has not granted apps"}), http(201, b"", "9")]);
        let mut forward = controller(&pins, &mut log, &mut replies);
        let result = call_tool(&dav, "mini_app_dav_file_put", &json!({"path":"a.txt","contentBase64":"AA=="}), &mut forward);
        drop(forward);
        let text: Value = serde_json::from_str(result["text"].as_str().unwrap()).unwrap();
        assert_eq!((result["isError"].clone(), text["refusal"].clone(), text["uncertain"].clone()), (json!(true), json!("typed-apps-not-granted"), json!(false)));
        assert_eq!((log.len(), replies.len()), (1, 1), "exactly one attempt, no retry");
        assert_eq!(text["nativeReceipts"], json!([]));
    }

    #[test]
    fn a_verified_http_frame_parses_and_the_model_presentation_is_native_reply_malformed() {
        let frame = json!({"type":"http-v3","status":200,"headers":[{"name":"content-type","value":"text/plain"}],"bodyHex":"6869"});
        let ok = native_reply(&json!({"isError":false,"text":frame.to_string()})).unwrap_or_else(|e| panic!("{}", e.name));
        assert_eq!(ok.status, 200);
        // present_lifetime_http's text for a model is not a frame: the failure mode of a non-raw call.
        let presented = native_reply(&json!({"isError":false,"text":"HTTP 200 text/plain\n\nhi"}));
        let refusal = presented.err().expect("presentation is not a frame");
        assert_eq!((refusal.name.as_str(), refusal.uncertain), ("native-reply-malformed", true));
    }

    #[test]
    fn a_write_whose_reply_is_lost_is_uncertain_and_never_replayed() {
        let dav = entry("dav", DAVROS);
        let pins = pins(&[&dav]);
        let lost = json!({"isError":true,"text":"Mini tool delivery timed out or reply unavailable; outcome unknown"});
        let (mut log, mut replies) = (Vec::new(), vec![lost, http(201, b"", "9")]);
        let mut forward = controller(&pins, &mut log, &mut replies);
        let result = call_tool(&dav, "mini_app_dav_file_put", &json!({"path":"a.txt","contentBase64":"AA=="}), &mut forward);
        drop(forward);
        let text: Value = serde_json::from_str(result["text"].as_str().unwrap()).unwrap();
        assert_eq!((text["refusal"].clone(), text["uncertain"].clone()), (json!("native-outcome-unknown"), json!(true)));
        assert_eq!(log.len(), 1);
    }

    #[test]
    fn model_arguments_cannot_name_a_route_a_host_or_extra_fields() {
        let dav = entry("dav", DAVROS);
        let pins = pins(&[&dav]);
        let mut log = Vec::new();
        let mut replies = vec![http(201, b"", "9")];
        let mut forward = controller(&pins, &mut log, &mut replies);
        for bad in [json!({"path":"a.txt","contentBase64":"AA==","application":"gogs-app"}), json!({"path":"../x","contentBase64":"AA=="}), json!({"path":"a"})] {
            let result = call_tool(&dav, "mini_app_dav_file_put", &bad, &mut forward);
            assert_eq!(result["isError"], true, "{bad}");
        }
        assert!(call_tool(&dav, "mini_app_dav_no_such_tool", &json!({}), &mut forward)["text"].as_str().unwrap().contains("typed-tool-unknown"));
        drop(forward);
        assert!(log.is_empty(), "schema-invalid input is refused before any dispatch");
    }

    #[test]
    fn the_listing_is_standard_mcp_and_owned_by_one_entry() {
        let (gogs, dav) = (entry("gogs", GOGS), entry("dav", DAVROS));
        let tools = listed_tools(&gogs).unwrap();
        assert!(tools.iter().any(|t| t["name"] == "mini_app_gogs_issue_create"));
        for tool in &tools {
            assert!(tool.as_object().unwrap().keys().all(|k| ["name", "description", "inputSchema", "outputSchema", "annotations", "_meta"].contains(&k.as_str())), "{tool}");
        }
        assert!(owns_tool(&gogs, "mini_app_gogs_repo_create") && !owns_tool(&dav, "mini_app_gogs_repo_create"));
        let mut tampered = gogs.clone();
        tampered.declaration_sha256 = "00".repeat(32);
        assert!(listed_tools(&tampered).is_err() && !owns_tool(&tampered, "mini_app_gogs_repo_create"));
    }

    #[test]
    fn a_request_naming_another_declaration_or_alias_is_refused_by_name() {
        let attachments = [attachment("gogs", "gogs-app")];
        let base = json!({"alias":"gogs","declarationSha256":"ab".repeat(32),"packageId":"pkg","operation":"repo.create",
            "write":true,"method":"POST","path":"api/v1/user/repos","query":"","headers":[],"bodyHex":""});
        let mapped = raw_arguments(&attachments, &base).unwrap();
        assert_eq!(mapped["application"], "gogs-app", "the route is the controller's, not the worker's");
        for (key, value, expect) in [("alias", json!("other"), "typed-app-not-attached"),
            ("declarationSha256", json!("cd".repeat(32)), "typed-declaration-mismatch"),
            ("packageId", json!("other"), "typed-declaration-mismatch")] {
            let mut bad = base.clone();
            bad[key] = value;
            let error = raw_arguments(&attachments, &bad).unwrap_err();
            assert!(error.starts_with(&format!("refused: {expect}:")), "{key}: {error}");
        }
        let mut extra = base.clone();
        extra["application"] = json!("oracle-app");
        assert!(raw_arguments(&attachments, &extra).unwrap_err().contains("unknown fields"), "a worker cannot pick the route");
    }

    #[test]
    fn controller_text_maps_to_named_refusals_and_uncertainty() {
        let refused = native_reply(&json!({"isError":true,"text":"refused: typed-apps-not-granted: no apps bit"})).unwrap_err();
        assert_eq!((refused.name.as_str(), refused.uncertain), ("typed-apps-not-granted", false));
        let native = json!({"type":"refused-v3","code":"held"}).to_string();
        let refused = native_reply(&json!({"isError":true,"text":native})).unwrap_err();
        assert_eq!((refused.name.as_str(), refused.uncertain), ("native-refused-held", false));
        let lost = json!({"type":"uncertain-v3","phase":"sent"}).to_string();
        assert!(native_reply(&json!({"isError":true,"text":lost})).unwrap_err().uncertain);
        assert!(native_reply(&json!({"isError":true,"text":"timed out; outcome unknown"})).unwrap_err().uncertain, "unclassified loss is never a clean refusal");
        let ok = json!({"type":"http-v3","status":201,"headers":[{"name":"content-type","value":"application/json"}],
            "bodyHex":mini_sdk::hex::encode(b"{}"),"operationId":"7"}).to_string();
        let reply = native_reply(&json!({"isError":false,"text":ok})).unwrap();
        assert_eq!((reply.status, reply.body.as_slice()), (201, &b"{}"[..]));
        assert!(reply.receipt.get("bodyHex").is_none() && reply.receipt["bodyBytes"] == 2);
        let truncated = json!({"type":"http-v3","status":200,"headers":[],"bodyHex":"0"}).to_string();
        assert!(native_reply(&json!({"isError":false,"text":truncated})).unwrap_err().uncertain);
    }

    #[test]
    fn named_refusal_spelling_is_strict() {
        assert!(named_refusal("refused: a-b: x").is_some());
        assert!(named_refusal("refused: : x").is_none() && named_refusal("a refused: x").is_none());
        assert!(named_refusal("refused: bad name: x").is_none());
    }
}

#[cfg(test)]
mod controller_tests {
    use super::*;
    use crate::{application_api_tools::LifetimeRoutePin, Runtime};
    use std::fs;

    fn route(root: &std::path::Path, name: &str, app: &str) -> LifetimeRoutePin {
        let receipt = json!({"transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"});
        serde_json::from_value(json!({
            "name":name,"socketPath":root.join("agent.sock"),"hostUid":1001,"hostUnit":"spk-host@test.service",
            "appResource":app,"sessionResource":"6209","ticketResource":"6408","participantSubject":"7",
            "parentTask":"7101","originalParentGeneration":"1","originalDescriptorSha256":"ab".repeat(32),
            "purseResource":"7500","signedApiPath":"/",
            "dispatchSelectors":{"issueIndex":"9","packageManifest":"6101","snapshotManifest":"6102",
                "sessionObserve":"81","manifestObserve":"82","enrollmentObserve":"83"},
            "grantIssueIndex":"13","grantResource":"6600","grantObserveCapability":"84",
            "grantAttemptDir":root.join("grant"),"grantDigest":"456","grantInitializedRoot":"567",
            "originalIssueReceipt":receipt,"grantIssueReceipt":receipt
        })).unwrap()
    }

    /// A restricted room resident with a gogs and a davros attachment over two lifetime routes.
    fn resident(tag: &str) -> (std::path::PathBuf, Runtime) {
        let (root, mut rt) = crate::room_task::tests::fixture(tag);
        let mut attachments = Vec::new();
        for (alias, text) in [("gogs", include_str!("../../../apps/interfaces/gogs.json")), ("dav", include_str!("../../../apps/interfaces/davros.json"))] {
            let path = root.join(format!("{alias}.json"));
            fs::write(&path, text).unwrap();
            let declaration = Declaration::load(text.as_bytes()).unwrap();
            attachments.push(TypedApplicationAttachment { alias: alias.into(), declaration_path: path,
                declaration_sha256: declaration.sha256, package_id: declaration.package_id, route_name: format!("{alias}-app") });
        }
        let tool = rt.config.tool_task.as_mut().unwrap();
        tool.allowed_application_lifetime_routes = vec![route(&root, "gogs-app", "6100"), route(&root, "dav-app", "6101")];
        tool.typed_applications = attachments;
        tool.room.as_mut().unwrap().restrict_tools = true;
        (root, rt)
    }

    fn lifetime_names(rt: &Runtime) -> Vec<String> {
        rt.config.tool_task.as_ref().unwrap().allowed_application_lifetime_routes.iter().map(|r| r.name.clone()).collect()
    }

    #[test]
    fn the_restricted_catalogue_carries_each_attachment_without_its_route() {
        let (root, rt) = resident("typed-catalogue");
        let catalogue = rt.tool_catalog().unwrap();
        assert!(catalogue.room_tools && catalogue.api_applications.is_empty(), "typed tools open no raw application API");
        let ids: Vec<_> = catalogue.typed_applications.iter().map(|e| (e.alias.as_str(), e.app.as_str(), e.subject.as_str())).collect();
        assert_eq!(ids, [("gogs", "6100", "7"), ("dav", "6101", "7")]);
        let wire = serde_json::to_string(&catalogue.typed_applications).unwrap();
        assert!(!wire.contains("gogs-app") && !wire.contains("agent.sock") && !wire.contains("grant"), "no route, socket or grant path reaches the worker: {}", &wire[..200]);
        let names = rt.resident_extra_tool_names();
        for expected in ["mcp__mini_grain__mini_app_gogs_repo_create", "mcp__mini_grain__mini_app_gogs_issue_create", "mcp__mini_grain__mini_app_dav_file_put"] {
            assert!(names.iter().any(|n| n == expected), "{expected} in the exact catalogue the session must report");
        }
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn the_apps_bit_gates_dispatch_and_the_oracle_bit_does_not() {
        let (root, mut rt) = resident("typed-gate");
        for oracle_only in [true, false] {
            rt.prompt_oracle = oracle_only;
            rt.prompt_apps = false;
            let error = rt.restricted_application_call(RAW_TOOL).unwrap_err();
            assert!(error.starts_with("refused: typed-apps-not-granted:"), "{error}");
        }
        rt.prompt_apps = true;
        rt.restricted_application_call(RAW_TOOL).unwrap();
        rt.config.tool_task.as_mut().unwrap().typed_applications.clear();
        assert!(rt.restricted_application_call(RAW_TOOL).unwrap_err().starts_with("refused: typed-apps-not-configured:"));
        assert!(rt.restricted_application_call("mini_application_api").unwrap_err().contains("only room tools"), "typed apps do not reopen the raw API");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn the_controller_maps_a_prepared_request_to_its_own_route_only() {
        let (root, rt) = resident("typed-map");
        let dav = rt.tool_catalog().unwrap().typed_applications.remove(1);
        let request = json!({"alias":"dav","declarationSha256":dav.declaration_sha256,"packageId":dav.package_id,"operation":"file.put","write":true,
            "method":"PUT","path":"dav/a.txt","query":"","headers":[],"bodyHex":"00"});
        let mapped = rt.application_tool_arguments(RAW_TOOL, &request).unwrap();
        assert_eq!(mapped["application"], "dav-app");
        let tool = rt.config.tool_task.as_ref().unwrap();
        let parsed = crate::application_api_tools::parse_input(&mapped, &lifetime_names(&rt)).unwrap();
        assert_eq!((parsed.method.as_str(), parsed.path.as_str(), parsed.body.as_slice()), ("PUT", "dav/a.txt", &[0u8][..]));
        let mut foreign = request.clone();
        foreign["alias"] = json!("someone-elses-gogs");
        assert!(rt.application_tool_arguments(RAW_TOOL, &foreign).unwrap_err().starts_with("refused: typed-app-not-attached:"));
        assert!(tool.typed_applications.len() == 2);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn configuration_refuses_duplicates_unknown_routes_and_a_changed_declaration() {
        let (root, rt) = resident("typed-validate");
        let tool = rt.config.tool_task.as_ref().unwrap();
        let routes = lifetime_names(&rt);
        validate(&tool.typed_applications, &routes).unwrap();
        let mut dup = tool.typed_applications.clone();
        dup[1].alias = "gogs".into();
        assert!(validate(&dup, &routes).unwrap_err().contains("duplicate alias"));
        let mut unrouted = tool.typed_applications.clone();
        unrouted[0].route_name = "nowhere-app".into();
        assert!(validate(&unrouted, &routes).unwrap_err().contains("lifetime API route"));
        let mut wrong_pin = tool.typed_applications.clone();
        wrong_pin[0].declaration_sha256 = "00".repeat(32);
        assert!(validate(&wrong_pin, &routes).unwrap_err().contains("differs from its attachment pin"));
        let mut wrong_package = tool.typed_applications.clone();
        wrong_package[0].package_id = "other".into();
        assert!(validate(&wrong_package, &routes).is_err());
        // The same declaration attached twice under distinct aliases is fine; one alias cannot collide.
        let mut twice = tool.typed_applications.clone();
        twice.push(TypedApplicationAttachment { alias: "gogs2".into(), route_name: "gogs-app".into(), ..tool.typed_applications[0].clone() });
        validate(&twice, &routes).unwrap();
        // Tampering with the controller-owned file after the pin refuses the catalogue.
        fs::write(&tool.typed_applications[0].declaration_path, b"{}").unwrap();
        assert!(rt.tool_catalog().is_err());
        fs::remove_dir_all(root).unwrap();
    }
}

#[cfg(test)]
mod text_tests {
    use super::*;

    #[test]
    fn davros_text_helpers_need_no_base64_and_round_trip() {
        let text = include_str!("../../../apps/interfaces/davros.json");
        let declaration = Declaration::load(text.as_bytes()).unwrap();
        let entry = CatalogEntry {
            alias: "dav".into(), declaration: text.into(), declaration_sha256: declaration.sha256.clone(),
            package_id: declaration.package_id.clone(), subject: "7".into(), app: "6101".into(),
            generation: "ab".repeat(32), session: "6209".into(), session_generation: "456".into(),
        };
        let mut seen = Vec::new();
        let mut forward = |request: Value| {
            seen.push(request.clone());
            let body = if request["method"] == "PUT" { String::new() } else { mini_sdk::hex::encode("Issue: http://x/alice/notes/issues/1\n".as_bytes()) };
            let status = if request["method"] == "PUT" { 201 } else { 200 };
            json!({"isError":false,"text":json!({"type":"http-v3","status":status,"headers":[],"bodyHex":body,"operationId":"1"}).to_string()})
        };
        let put = call_tool(&entry, "mini_app_dav_file_put_text", &json!({"path":"issue.txt","content":"Issue: http://x/alice/notes/issues/1\n"}), &mut forward);
        assert_eq!(put["structured"]["value"]["status"], 201, "{put}");
        let got = call_tool(&entry, "mini_app_dav_file_get_text", &json!({"path":"issue.txt"}), &mut forward);
        assert_eq!(got["structured"]["value"], "Issue: http://x/alice/notes/issues/1\n", "{got}");
        assert_eq!(seen[0]["bodyHex"], mini_sdk::hex::encode(b"Issue: http://x/alice/notes/issues/1\n"));
    }
}
