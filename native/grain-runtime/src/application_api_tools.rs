//! Bounded model-facing input for one operator-bound application API session.
//!
//! The selected name is a controller catalog entry, not an application ID or
//! authority grant. The controller supplies the fixed app, agent ticket,
//! session, purse and operation ID when it invokes the resident host. Mini's
//! event21 receiver remains the authority for any eventual physical call.
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs;
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Receiver, TryRecvError};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

const MAX_TOOL_INPUT_BYTES: usize = 65_536;
const MAX_BODY_BYTES: usize = 24 * 1024;
const MAX_PATH_QUERY_BYTES: usize = 8192;
const MAX_HEADERS: usize = 128;
const MAX_FORWARD_FRAME: usize = 262_144;
const MAX_INSPECT_REPLY_FRAME: usize = 1_048_576;
const MAX_MODEL_TEXT_BODY: usize = 32 * 1024;
const PROTOCOL: &str = "mini-spk-agent-api-v1";
const LIFETIME_PROTOCOL: &str = "mini-spk-agent-api-v3";

const ORDINARY_HEADERS: &[&str] = &[
    "cookie",
    "accept",
    "accept-encoding",
    "content-type",
    "user-agent",
    "if-match",
    "if-none-match",
    "x-requested-with",
    "x-csrftoken",
    "x-csrf-token",
    "oc-total-length",
    "oc-chunk-size",
    "x-oc-mtime",
    "oc-fileid",
    "oc-chunked",
    "oc-checksum",
    "oc-chunk-offset",
    "oc-lazyops",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct HttpInput {
    pub application: String,
    pub method: String,
    pub path: String,
    pub query: String,
    pub ordered_headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(DIGITS[(byte >> 4) as usize] as char);
        encoded.push(DIGITS[(byte & 15) as usize] as char);
    }
    encoded
}

pub(crate) fn hello_request() -> Value {
    json!({"type":"hello","protocol":PROTOCOL})
}

pub(crate) fn lifetime_hello_request() -> Value {
    json!({"type":"hello-v3","protocol":LIFETIME_PROTOCOL})
}

/// Render only a bounded, derived view of an already verified resident reply
/// for the model. The exact `http-v3` frame remains in controller custody;
/// this projection never supplies a dispatch or settlement authority.
pub(crate) fn present_lifetime_http(reply: &Value) -> Result<Value, String> {
    if reply.get("type").and_then(Value::as_str) != Some("http-v3") {
        return Err("lifetime HTTP presentation requires a definite reply".into());
    }
    let body_hex = reply
        .get("bodyHex")
        .and_then(Value::as_str)
        .ok_or("lifetime HTTP response body absent")?;
    if body_hex.len() > MAX_INSPECT_REPLY_FRAME || !body_hex.len().is_multiple_of(2) {
        return Err("lifetime HTTP response body exceeds presentation bound".into());
    }
    let mut body = Vec::with_capacity(body_hex.len() / 2);
    for pair in body_hex.as_bytes().chunks_exact(2) {
        let nibble = |byte| match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            _ => None,
        };
        body.push(
            (nibble(pair[0]).ok_or("lifetime response body hex is not canonical")? << 4)
                | nibble(pair[1]).ok_or("lifetime response body hex is not canonical")?,
        );
    }
    let mut view = reply.clone();
    let object = view
        .as_object_mut()
        .ok_or("lifetime HTTP reply is not an object")?;
    object.remove("bodyHex");
    object.insert("bodyBytes".into(), json!(body.len()));
    if body.len() <= MAX_MODEL_TEXT_BODY {
        if let Ok(text) = String::from_utf8(body) {
            object.insert("bodyText".into(), json!(text));
            object.insert("bodyPresentation".into(), json!("utf-8"));
            return Ok(view);
        }
    }
    object.insert(
        "bodyPresentation".into(),
        json!("binary-or-oversize-omitted"),
    );
    Ok(view)
}

pub(crate) fn lifetime_dispatch_request(
    operation_id: u64,
    binding_sha256: &str,
    input: &HttpInput,
) -> Result<Value, String> {
    if !lowercase_hex64(binding_sha256) {
        return Err("lifetime binding digest is invalid".into());
    }
    Ok(json!({"type":"dispatch-v3","protocol":LIFETIME_PROTOCOL,
        "operationId":operation_id.to_string(),"bindingSha256":binding_sha256,
        "method":input.method,"path":input.path,"query":input.query,
        "headers":input.ordered_headers.iter().map(|(name,value)|
            json!({"name":name,"value":value})).collect::<Vec<_>>(),
        "bodyHex":hex(&input.body)}))
}

pub(crate) fn inspect_request(operation_id: u64) -> Value {
    json!({"type":"inspect","protocol":PROTOCOL,"operation_id":operation_id.to_string()})
}

pub(crate) fn inspect_historical_request(
    operation_id: u64,
    binding_sha256: &str,
) -> Result<Value, String> {
    if !lowercase_hex64(binding_sha256) {
        return Err("application API historical binding digest is invalid".into());
    }
    let mut request = inspect_request(operation_id);
    request["binding_sha256"] = json!(binding_sha256);
    Ok(request)
}

pub(crate) fn dispatch_request(operation_id: u64, input: &HttpInput) -> Value {
    json!({"type":"dispatch","protocol":PROTOCOL,"operation_id":operation_id.to_string(),
        "method":input.method,"path":input.path,"query":input.query,
        "headers":input.ordered_headers.iter().map(|(name,value)|
            json!({"name":name,"value":value})).collect::<Vec<_>>(),
        "body_hex":hex(&input.body)})
}

/// Compare the Host's source-decoded reserve request with the exact forward
/// call retained before socket I/O. The only routing transform permitted by
/// the first SPK API bridge is its operator-pinned signed `/repo.git/` prefix.
/// The model may choose a path relative to that prefix and ordinary headers, but may not substitute any
/// different bytes when asking the controller to spend its purse.
pub(crate) fn routed_reserve_http(
    retained_forward: &Value,
    signed_api_path: &str,
) -> Result<Value, String> {
    // The first application profile has one native GitWeb API bridge. Future
    // prefixes need a separately qualified source/host mapping, not a generic
    // string concatenation rule chosen by the model.
    if signed_api_path != "/repo.git/" {
        return Err("signed API prefix differs from the first native bridge".into());
    }
    let lifetime = retained_forward.get("type").and_then(Value::as_str) == Some("dispatch-v3")
        && retained_forward.get("protocol").and_then(Value::as_str) == Some(LIFETIME_PROTOCOL);
    let operation_id = retained_forward
        .get(if lifetime {
            "operationId"
        } else {
            "operation_id"
        })
        .and_then(Value::as_str)
        .ok_or("retained forward operation ID absent")?;
    if !canonical_decimal(operation_id) {
        return Err("retained forward operation ID is not canonical".into());
    }
    let field = |key: &str| -> Result<&str, String> {
        retained_forward
            .get(key)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("retained forward {key} absent"))
    };
    let method = field("method")?;
    let path = field("path")?;
    let query = field("query")?;
    let body_hex = field(if lifetime { "bodyHex" } else { "body_hex" })?;
    if path.starts_with('/') || path.contains(['?', '#']) || query.contains('#') {
        return Err("retained forward path or query differs from API profile".into());
    }
    let headers = retained_forward
        .get("headers")
        .and_then(Value::as_array)
        .ok_or("retained forward ordered headers absent")?
        .iter()
        .map(|header| {
            let name = header
                .get("name")
                .and_then(Value::as_str)
                .ok_or("retained forward header name absent")?;
            let value = header
                .get("value")
                .and_then(Value::as_str)
                .ok_or("retained forward header value absent")?;
            Ok(
                json!({"nameHex":hex(name.as_bytes()),"valueHex":hex(value.as_bytes()),
                "generated":false}),
            )
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(json!({
        "operationId": operation_id,
        "methodHex": hex(method.as_bytes()),
        "pathHex": hex(format!("{}{path}", &signed_api_path[1..]).as_bytes()),
        "queryHex": hex(query.as_bytes()),
        "headers": headers,
        "bodyHex": body_hex,
    }))
}

pub(crate) fn verify_routed_reserve_http(
    retained_forward: &Value,
    signed_api_path: &str,
    source_inspection: &Value,
) -> Result<(), String> {
    let expected = routed_reserve_http(retained_forward, signed_api_path)?;
    if source_inspection.pointer("/base/http") != Some(&expected) {
        return Err("source reserve HTTP differs from retained forward call".into());
    }
    Ok(())
}

/// An operator-selected forward route to one fixed resident API session.
/// Resource IDs select what Mini must check; none is authority by itself.
/// Current generations, grants and the host invocation are checked at use.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct RoutePin {
    pub name: String,
    pub socket_path: PathBuf,
    pub host_uid: u32,
    pub host_unit: String,
    pub app_resource: String,
    pub app_generation: String,
    pub session_resource: String,
    pub session_generation: String,
    pub ticket_resource: String,
    pub participant_subject: String,
    pub parent_task: String,
    pub parent_generation: String,
    pub purse_resource: String,
    pub dispatch_generation: String,
    pub signed_api_path: String,
    pub dispatch_selectors: DispatchSelectorPin,
}

/// Immutable native receipt identity. A lifetime route never accepts a
/// caller-supplied current generation in place of either historical receipt.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct SourceReceiptPin {
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub image_boundary: String,
}

impl SourceReceiptPin {
    fn valid(&self) -> bool {
        [
            &self.transaction_id,
            &self.event_id,
            &self.accepted_count,
            &self.image_boundary,
        ]
        .iter()
        .all(|value| canonical_native_nat(value))
    }
}

/// An explicitly issued event27 route. These are stable selector and
/// transport pins, never mutable app/session/parent/purse generation pins.
/// A fresh source-inspected event26 plan and signed current task observations
/// supply the latter at every use. V2 RoutePin keeps its old fixed semantics.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct LifetimeRoutePin {
    pub name: String,
    pub socket_path: PathBuf,
    pub host_uid: u32,
    pub host_unit: String,
    pub app_resource: String,
    pub session_resource: String,
    pub ticket_resource: String,
    pub participant_subject: String,
    pub parent_task: String,
    /// Event22 origin is historical provenance, not this prompt's generation.
    pub original_parent_generation: String,
    pub original_descriptor_sha256: String,
    pub purse_resource: String,
    pub signed_api_path: String,
    pub dispatch_selectors: DispatchSelectorPin,
    pub grant_issue_index: String,
    pub grant_resource: String,
    pub grant_observe_capability: String,
    /// Controller-owned sealed event27 attempt, required for detached paid
    /// planning; it is not an authority grant by pathname alone.
    pub grant_attempt_dir: PathBuf,
    pub grant_digest: String,
    pub grant_initialized_root: String,
    pub original_issue_receipt: SourceReceiptPin,
    pub grant_issue_receipt: SourceReceiptPin,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct LifetimeLineage {
    app_resource: String,
    session_resource: String,
    participant_subject: String,
    ticket_resource: String,
    original_parent_task: String,
    original_parent_generation: String,
    original_issue_index: String,
    original_issue_receipt: SourceReceiptPin,
    original_descriptor_sha256: String,
    grant_resource: String,
    grant_issue_index: String,
    grant_digest: String,
    grant_initialized_root: String,
    grant_issue_receipt: SourceReceiptPin,
    parent_task: String,
    purse_task: String,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct LifetimeBinding {
    protocol: String,
    lineage: LifetimeLineage,
    signed_api_path: String,
    host_unit: String,
    host_invocation: String,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct LifetimeBindingReply {
    #[serde(rename = "type")]
    kind: String,
    protocol: String,
    binding: LifetimeBinding,
    binding_sha256: String,
}

/// Exact order mirrors the resident v3 fingerprint preimage. These values
/// come from the source-owned reserve plan and signed task observations, not
/// from the forward dispatch frame or a static route generation.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct LifetimeCurrentClaims {
    pub app_generation: String,
    pub session_generation: String,
    pub parent_generation: String,
    pub purse_generation: String,
    pub app_physical_root: String,
    pub session_physical_root: String,
    pub parent_physical_root: String,
    pub purse_physical_root: String,
}

pub(crate) fn lifetime_operation_fingerprint(
    binding_sha256: &str,
    current: &LifetimeCurrentClaims,
    operation_id: &str,
    request_sha256: &str,
) -> Result<String, String> {
    if !lowercase_hex64(binding_sha256)
        || !lowercase_hex64(request_sha256)
        || !canonical_decimal(operation_id)
        || ![
            &current.app_generation,
            &current.session_generation,
            &current.parent_generation,
            &current.purse_generation,
            &current.app_physical_root,
            &current.session_physical_root,
            &current.parent_physical_root,
            &current.purse_physical_root,
        ]
        .iter()
        .all(|field| canonical_native_nat(field))
    {
        return Err("lifetime operation fingerprint coordinates are invalid".into());
    }
    let mut digest = Sha256::new();
    digest.update(b"DREGG/SPK-AGENT-LIFETIME-OPERATION/v3\0");
    digest.update(binding_sha256.as_bytes());
    digest.update(
        serde_json::to_vec(current)
            .map_err(|error| format!("lifetime current claims canonical JSON: {error}"))?,
    );
    digest.update(operation_id.as_bytes());
    digest.update(request_sha256.as_bytes());
    Ok(hex(&digest.finalize()))
}

pub(crate) fn verify_lifetime_binding_reply(
    reply: Value,
    route: &LifetimeRoutePin,
) -> Result<(String, String), String> {
    let reply: LifetimeBindingReply = serde_json::from_value(reply)
        .map_err(|error| format!("lifetime binding reply: {error}"))?;
    let lineage = &reply.binding.lineage;
    let invocation = &reply.binding.host_invocation;
    if reply.kind != "binding-v3"
        || reply.protocol != LIFETIME_PROTOCOL
        || reply.binding.protocol != "mini-spk-agent-lifetime-binding-v3"
        || lineage.app_resource != route.app_resource
        || lineage.session_resource != route.session_resource
        || lineage.participant_subject != route.participant_subject
        || lineage.ticket_resource != route.ticket_resource
        || lineage.original_parent_task != route.parent_task
        || lineage.original_parent_generation != route.original_parent_generation
        || lineage.original_issue_index != route.dispatch_selectors.issue_index
        || lineage.original_issue_receipt != route.original_issue_receipt
        || lineage.original_descriptor_sha256 != route.original_descriptor_sha256
        || lineage.grant_resource != route.grant_resource
        || lineage.grant_issue_index != route.grant_issue_index
        || lineage.grant_digest != route.grant_digest
        || lineage.grant_initialized_root != route.grant_initialized_root
        || lineage.grant_issue_receipt != route.grant_issue_receipt
        || lineage.parent_task != route.parent_task
        || lineage.purse_task != route.purse_resource
        || reply.binding.signed_api_path != route.signed_api_path
        || reply.binding.host_unit != route.host_unit
        || invocation.len() != 32
        || !invocation
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        || !lowercase_hex64(&reply.binding_sha256)
    {
        return Err("lifetime host binding differs from operator lineage".into());
    }
    let mut digest = Sha256::new();
    digest.update(b"DREGG/SPK-AGENT-LIFETIME-BINDING/v3\0");
    digest.update(
        serde_json::to_vec(&reply.binding)
            .map_err(|error| format!("lifetime binding canonical JSON: {error}"))?,
    );
    if hex(&digest.finalize()) != reply.binding_sha256 {
        return Err("lifetime host binding digest differs".into());
    }
    Ok((reply.binding_sha256, invocation.clone()))
}

/// Operator pins for every selection field the source reserve plan exposes.
/// These are compared byte-for-byte with the source inspection before the
/// controller approves purse signing; native op46 remains the authority.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct DispatchSelectorPin {
    pub issue_index: String,
    pub package_manifest: String,
    pub snapshot_manifest: String,
    pub session_observe: String,
    pub manifest_observe: String,
    pub enrollment_observe: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedBinding {
    pub protocol: String,
    pub app: String,
    pub app_generation: String,
    pub session: String,
    pub session_generation: String,
    pub subject: String,
    pub ticket: String,
    pub parent_task: String,
    pub parent_generation: String,
    pub purse_task: String,
    pub purse_generation: String,
    pub signed_api_path: String,
    pub host_unit: String,
    pub host_invocation: String,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "kebab-case", deny_unknown_fields)]
pub(crate) enum HostReply {
    Binding {
        protocol: String,
        binding: Box<FixedBinding>,
        binding_sha256: String,
    },
    Http {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        status: u16,
        headers: Vec<HostHeader>,
        body_hex: String,
    },
    Refused {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        code: String,
    },
    Uncertain {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        phase: String,
    },
    Inspection {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        state: String,
        #[serde(default)]
        definite_reply_json_hex: Option<String>,
        #[serde(default)]
        definite_reply_sha256: Option<String>,
        #[serde(default)]
        retention_error: Option<String>,
    },
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(crate) struct HostHeader {
    pub name: String,
    pub value: String,
}

fn lowercase_hex64(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

impl FixedBinding {
    fn fingerprint(&self) -> Result<String, String> {
        if self.protocol != "mini-spk-agent-binding-v1"
            || ![
                &self.app,
                &self.app_generation,
                &self.session,
                &self.session_generation,
                &self.subject,
                &self.ticket,
                &self.parent_task,
                &self.parent_generation,
                &self.purse_task,
                &self.purse_generation,
            ]
            .iter()
            .all(|value| canonical_decimal(value))
            || self.parent_task == self.purse_task
            || self.signed_api_path != "/repo.git/"
            || self.host_unit.is_empty()
            || self.host_unit.len() > 256
            || !clean_text(&self.host_unit)
            || self.host_invocation.len() != 32
            || !self
                .host_invocation
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err("application API host fixed binding is invalid".into());
        }
        let mut hash = Sha256::new();
        hash.update(b"DREGG/SPK-AGENT-API-BINDING/v1\0");
        hash.update(serde_json::to_vec(self).map_err(|error| error.to_string())?);
        Ok(format!("{:x}", hash.finalize()))
    }
}

/// The operator route pins the expected transport coordinates. A host-provided
/// binding is a transport identity check and never substitutes for event21's
/// fresh native admission of the current generations and request.
pub(crate) fn verify_binding(
    reply: HostReply,
    route: &RoutePin,
) -> Result<(String, String), String> {
    let HostReply::Binding {
        protocol,
        binding,
        binding_sha256,
    } = reply
    else {
        return Err("application API host did not return a binding".into());
    };
    if protocol != PROTOCOL
        || binding.app != route.app_resource
        || binding.app_generation != route.app_generation
        || binding.session != route.session_resource
        || binding.session_generation != route.session_generation
        || binding.subject != route.participant_subject
        || binding.ticket != route.ticket_resource
        || binding.parent_task != route.parent_task
        || binding.parent_generation != route.parent_generation
        || binding.purse_task != route.purse_resource
        || binding.purse_generation != route.dispatch_generation
        || binding.signed_api_path != route.signed_api_path
        || binding.host_unit != route.host_unit
        || !lowercase_hex64(&binding_sha256)
        || binding.fingerprint()? != binding_sha256
    {
        return Err("application API host binding differs from current operator pins".into());
    }
    Ok((binding_sha256, binding.host_invocation))
}

pub(crate) fn parse_host_reply(value: Value) -> Result<HostReply, String> {
    serde_json::from_value(value).map_err(|error| format!("application API host reply: {error}"))
}

pub(crate) fn verify_operation_reply(
    reply: &HostReply,
    operation_id: u64,
    binding_sha256: &str,
) -> Result<(), String> {
    let (protocol, id, binding) = match reply {
        HostReply::Binding { .. } => {
            return Err("application API operation returned a binding instead of a result".into())
        }
        HostReply::Http {
            protocol,
            operation_id,
            binding_sha256,
            status,
            headers,
            body_hex,
        } => {
            if !(100..=599).contains(status)
                || headers.len() > 128
                || headers.iter().any(|header| {
                    header.name.is_empty()
                        || header.name.len() > 128
                        || !clean_text(&header.name)
                        || header.value.len() > 8192
                        || !clean_text(&header.value)
                })
                || body_hex.len() > MAX_FORWARD_FRAME * 2
                || body_hex.len() % 2 != 0
                || !body_hex
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            {
                return Err("application API HTTP result exceeds protocol bounds".into());
            }
            (protocol, operation_id, binding_sha256)
        }
        HostReply::Refused {
            protocol,
            operation_id,
            binding_sha256,
            code,
        } => {
            if code.is_empty() || code.len() > 128 || !clean_text(code) {
                return Err("application API refusal code is invalid".into());
            }
            (protocol, operation_id, binding_sha256)
        }
        HostReply::Uncertain {
            protocol,
            operation_id,
            binding_sha256,
            phase,
        } => {
            if phase.is_empty() || phase.len() > 128 || !clean_text(phase) {
                return Err("application API uncertainty phase is invalid".into());
            }
            (protocol, operation_id, binding_sha256)
        }
        HostReply::Inspection {
            protocol,
            operation_id,
            binding_sha256,
            state,
            definite_reply_json_hex,
            definite_reply_sha256,
            retention_error,
        } => {
            if !matches!(
                state.as_str(),
                "not-seen" | "received" | "delivery-requested" | "definite" | "uncertain"
            ) {
                return Err("application API inspection state is invalid".into());
            }
            if definite_reply_json_hex.is_some() != definite_reply_sha256.is_some()
                || (state != "definite" && definite_reply_json_hex.is_some())
                || retention_error.as_deref().is_some_and(|error| {
                    state != "uncertain" || error != "definite-reply-unverified"
                })
            {
                return Err("application API recovered reply fields are inconsistent".into());
            }
            (protocol, operation_id, binding_sha256)
        }
    };
    let expected_id = operation_id.to_string();
    if protocol != PROTOCOL || id != &expected_id || binding != binding_sha256 {
        return Err("application API operation reply identity differs".into());
    }
    Ok(())
}

/// Recover only exact retained HTTP bytes from read-only inspection. A host
/// which cannot verify its retained definite reply reports an explicit
/// uncertain retention error; that remains terminal without a result.
pub(crate) fn recovered_definite_http(
    inspection: &HostReply,
    operation_id: u64,
    binding_sha256: &str,
) -> Result<Option<HostReply>, String> {
    verify_operation_reply(inspection, operation_id, binding_sha256)?;
    let HostReply::Inspection {
        state,
        definite_reply_json_hex,
        definite_reply_sha256,
        ..
    } = inspection
    else {
        return Err("application API recovery requires an inspection".into());
    };
    let (Some(encoded), Some(expected)) = (definite_reply_json_hex, definite_reply_sha256) else {
        return Ok(None);
    };
    if state != "definite"
        || !lowercase_hex64(expected)
        || encoded.len() > MAX_FORWARD_FRAME * 2
        || !encoded.len().is_multiple_of(2)
    {
        return Err("application API recovered definite bytes exceed bound".into());
    }
    let bytes = decode_hex_bounded(encoded, MAX_FORWARD_FRAME)?;
    let digest = hex(&Sha256::digest(&bytes));
    if &digest != expected {
        return Err("application API recovered definite reply digest differs".into());
    }
    let reply: HostReply = serde_json::from_slice(&bytes)
        .map_err(|error| format!("application API exact definite reply JSON: {error}"))?;
    if !matches!(reply, HostReply::Http { .. }) {
        return Err("application API retained definite reply is not HTTP".into());
    }
    verify_operation_reply(&reply, operation_id, binding_sha256)?;
    Ok(Some(reply))
}

fn decode_hex_bounded(value: &str, max_bytes: usize) -> Result<Vec<u8>, String> {
    if !value.len().is_multiple_of(2) || value.len() > 2 * max_bytes {
        return Err("application API recovered hex exceeds byte bound".into());
    }
    let mut decoded = Vec::with_capacity(value.len() / 2);
    for pair in value.as_bytes().chunks_exact(2) {
        let digit = |byte| match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            _ => None,
        };
        let value = digit(pair[0])
            .zip(digit(pair[1]))
            .map(|(high, low)| high * 16 + low)
            .ok_or("application API recovered hex is not lowercase")?;
        decoded.push(value);
    }
    Ok(decoded)
}

fn canonical_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 20
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
        && value.parse::<u64>().is_ok()
}

fn canonical_native_nat(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 78
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

pub(crate) fn validate_lifetime_routes(
    routes: &[LifetimeRoutePin],
    old_routes: &[RoutePin],
    parent_task: &str,
    purse_resource: &str,
    participant_subject: &str,
    host_uid: u32,
) -> Result<(), String> {
    if routes.len() > 16
        || routes.len() + old_routes.len() > 16
        || !canonical_decimal(parent_task)
        || !canonical_decimal(purse_resource)
        || !canonical_decimal(participant_subject)
    {
        return Err("lifetime API route count or dispatch authority is invalid".into());
    }
    for (index, route) in routes.iter().enumerate() {
        if route.name.is_empty()
            || route.name.len() > 64
            || !route.name.ends_with("-app")
            || !route
                .name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
            || routes[..index].iter().any(|prior| prior.name == route.name)
            || old_routes.iter().any(|old| old.name == route.name)
            || !route.socket_path.is_absolute()
            || route.host_uid != host_uid
            || route.host_uid == 0
            || route.host_unit.is_empty()
            || route.host_unit.len() > 256
            || !clean_text(&route.host_unit)
            || !route.grant_attempt_dir.is_absolute()
            || route.purse_resource != purse_resource
            || route.parent_task != parent_task
            || route.parent_task == route.purse_resource
            || !canonical_decimal(&route.original_parent_generation)
            || !lowercase_hex64(&route.original_descriptor_sha256)
            || [
                &route.app_resource,
                &route.session_resource,
                &route.ticket_resource,
                &route.parent_task,
                &route.purse_resource,
            ]
            .contains(&&route.grant_resource)
            || route.participant_subject != participant_subject
            || route.signed_api_path != "/repo.git/"
        {
            return Err("lifetime API route differs from operator dispatch binding".into());
        }
        for value in [
            &route.app_resource,
            &route.session_resource,
            &route.ticket_resource,
            &route.participant_subject,
            &route.purse_resource,
            &route.parent_task,
            &route.grant_resource,
            &route.grant_observe_capability,
            &route.dispatch_selectors.package_manifest,
            &route.dispatch_selectors.snapshot_manifest,
            &route.dispatch_selectors.session_observe,
            &route.dispatch_selectors.manifest_observe,
            &route.dispatch_selectors.enrollment_observe,
        ] {
            if !canonical_decimal(value) || value == "0" {
                return Err("lifetime API resource or capability is not canonical".into());
            }
        }
        if !canonical_decimal(&route.dispatch_selectors.issue_index)
            || !canonical_decimal(&route.grant_issue_index)
            || route
                .grant_issue_index
                .parse::<u64>()
                .ok()
                .zip(route.dispatch_selectors.issue_index.parse::<u64>().ok())
                .is_none_or(|(grant, issue)| grant <= issue)
            || !canonical_native_nat(&route.grant_digest)
            || !canonical_native_nat(&route.grant_initialized_root)
            || !route.original_issue_receipt.valid()
            || !route.grant_issue_receipt.valid()
            || route.original_issue_receipt == route.grant_issue_receipt
            || route
                .dispatch_selectors
                .issue_index
                .parse::<u64>()
                .ok()
                .and_then(|index| index.checked_add(1))
                .is_none_or(|count| {
                    route.original_issue_receipt.accepted_count != count.to_string()
                })
            || route
                .grant_issue_index
                .parse::<u64>()
                .ok()
                .and_then(|index| index.checked_add(1))
                .is_none_or(|count| route.grant_issue_receipt.accepted_count != count.to_string())
        {
            return Err("lifetime API historical grant identity is invalid".into());
        }
    }
    Ok(())
}

/// The source author inspects its own canonical request and reserve plan.
/// This check compares those decoded bytes with the controller's retained
/// forward call and immutable route, before the private purse key is used.
/// Current generations are *not* taken from the route: the caller supplies
/// signed task observations and retains this exact plan for later native
/// admission. This function itself does not confer a send permit.
pub(crate) struct LifetimeReserveInspection<'a> {
    pub route: &'a LifetimeRoutePin,
    pub retained_forward: &'a Value,
    pub expected_selectors: &'a Value,
    pub reserve_operation_id: &'a str,
    pub signed_parent_generation: &'a str,
    pub signed_purse_generation: &'a str,
    pub signed_app_physical_root: &'a str,
    pub signed_session_physical_root: &'a str,
    pub signed_parent_physical_root: &'a str,
    pub signed_purse_physical_root: &'a str,
    pub request: &'a Value,
    pub plan: &'a Value,
}

pub(crate) fn verify_lifetime_reserve_inspection(
    inspection: LifetimeReserveInspection<'_>,
) -> Result<(), String> {
    let LifetimeReserveInspection {
        route,
        retained_forward,
        expected_selectors,
        reserve_operation_id,
        signed_parent_generation,
        signed_purse_generation,
        signed_app_physical_root,
        signed_session_physical_root,
        signed_parent_physical_root,
        signed_purse_physical_root,
        request,
        plan,
    } = inspection;
    let expected_http = routed_reserve_http(retained_forward, &route.signed_api_path)?;
    if request.get("type").and_then(Value::as_str)
        != Some("application-agent-lifetime-author-request-v3")
        || plan.get("type").and_then(Value::as_str)
            != Some("application-agent-lifetime-reserve-plan-v3")
        || request.get("fixedSelectors") != Some(expected_selectors)
        || plan.get("fixedSelectors") != Some(expected_selectors)
        || request.get("http") != Some(&expected_http)
        || plan.get("http") != Some(&expected_http)
        || request.get("canonicalRequestHex") != plan.get("canonicalRequestHex")
        || request.get("canonicalHttpHex") != plan.get("canonicalHttpHex")
    {
        return Err("lifetime reserve source request differs from retained forward call".into());
    }
    let context = plan
        .get("context")
        .ok_or("lifetime source reserve context absent")?;
    let bindings = plan
        .get("bindings")
        .ok_or("lifetime source reserve bindings absent")?;
    let same = |object: &Value, field: &str, expected: &str| -> Result<(), String> {
        if object.get(field).and_then(Value::as_str) != Some(expected) {
            return Err(format!(
                "lifetime source {field} differs from current/route pin"
            ));
        }
        Ok(())
    };
    same(context, "appResource", &route.app_resource)?;
    same(context, "sessionResource", &route.session_resource)?;
    same(context, "participantSubject", &route.participant_subject)?;
    same(context, "ticketResource", &route.ticket_resource)?;
    same(context, "parentTask", &route.parent_task)?;
    same(context, "parentGeneration", signed_parent_generation)?;
    same(context, "purseTask", &route.purse_resource)?;
    same(context, "purseGeneration", signed_purse_generation)?;
    same(context, "grantResource", &route.grant_resource)?;
    same(context, "grantIssueIndex", &route.grant_issue_index)?;
    same(context, "grantDigest", &route.grant_digest)?;
    same(context, "reserveOperationId", reserve_operation_id)?;
    same(
        context,
        "httpOperationId",
        retained_forward
            .get("operation_id")
            .and_then(Value::as_str)
            .ok_or("retained lifetime forward operation ID absent")?,
    )?;
    if context.get("requestDigest") != request.get("requestDigest") {
        return Err("lifetime reserve HTTP digest differs from source request".into());
    }
    let original = serde_json::to_value(&route.original_issue_receipt)
        .map_err(|error| format!("original issue receipt pin: {error}"))?;
    let grant = serde_json::to_value(&route.grant_issue_receipt)
        .map_err(|error| format!("grant issue receipt pin: {error}"))?;
    if bindings.get("originalIssueReceipt") != Some(&original)
        || bindings.get("grantIssueReceipt") != Some(&grant)
    {
        return Err("lifetime reserve historical receipt differs from route".into());
    }
    same(
        bindings,
        "grantInitializedRoot",
        &route.grant_initialized_root,
    )?;
    same(bindings, "grantPhysicalRoot", &route.grant_initialized_root)?;
    for (field, expected) in [
        ("appPhysicalRoot", signed_app_physical_root),
        ("sessionPhysicalRoot", signed_session_physical_root),
        ("parentPhysicalRoot", signed_parent_physical_root),
        ("pursePhysicalRoot", signed_purse_physical_root),
    ] {
        if !canonical_native_nat(expected) {
            return Err(format!("lifetime signed {field} is not canonical"));
        }
        same(bindings, field, expected)?;
    }
    Ok(())
}

/// The post-reserve purse is a different physical cell state. Compare the
/// immutable ticket/grant, parent and exact HTTP bindings, but check the
/// post-reserve purse root as its own current fence. The native event26
/// receiver still proves the exact reserve chronology and current hold.
pub(crate) struct LifetimePaidInspection<'a> {
    pub reserve: &'a Value,
    pub paid: &'a Value,
    pub reserve_index: &'a str,
    pub reserve_receipt: &'a Value,
    pub signed_post_purse_physical_root: &'a str,
}

pub(crate) fn verify_lifetime_paid_inspection(
    inspection: LifetimePaidInspection<'_>,
) -> Result<(), String> {
    let LifetimePaidInspection {
        reserve,
        paid,
        reserve_index,
        reserve_receipt,
        signed_post_purse_physical_root,
    } = inspection;
    if reserve.get("type").and_then(Value::as_str)
        != Some("application-agent-lifetime-reserve-plan-v3")
        || paid.get("type").and_then(Value::as_str)
            != Some("application-agent-lifetime-paid-plan-v3")
        || paid.get("fixedSelectors") != reserve.get("fixedSelectors")
        || paid.get("context") != reserve.get("context")
        || paid.get("canonicalHttpHex") != reserve.get("canonicalHttpHex")
        || paid.get("http") != reserve.get("http")
        || paid.get("reserveIndex").and_then(Value::as_str) != Some(reserve_index)
        || paid.get("reserveReceipt") != Some(reserve_receipt)
    {
        return Err("lifetime paid plan differs from exact confirmed reserve".into());
    }
    let pre = reserve
        .get("bindings")
        .ok_or("lifetime reserve source bindings absent")?;
    let post = paid
        .get("bindings")
        .ok_or("lifetime paid source bindings absent")?;
    for field in [
        "originalIssueReceipt",
        "grantIssueReceipt",
        "grantInitializedRoot",
        "grantPhysicalRoot",
        "appPhysicalRoot",
        "sessionPhysicalRoot",
        "parentPhysicalRoot",
    ] {
        if post.get(field) != pre.get(field) {
            return Err(format!("lifetime paid {field} differs from source reserve"));
        }
    }
    if !canonical_native_nat(signed_post_purse_physical_root)
        || post.get("pursePhysicalRoot").and_then(Value::as_str)
            != Some(signed_post_purse_physical_root)
    {
        return Err("lifetime paid purse root differs from signed current view".into());
    }
    Ok(())
}

pub(crate) fn validate_routes(
    routes: &[RoutePin],
    parent_task: &str,
    purse_resource: &str,
    participant_subject: &str,
    host_uid: u32,
) -> Result<(), String> {
    if routes.len() > 16
        || !canonical_decimal(parent_task)
        || !canonical_decimal(purse_resource)
        || !canonical_decimal(participant_subject)
    {
        return Err("application API route count or dispatch authority is invalid".into());
    }
    for (index, route) in routes.iter().enumerate() {
        if route.name.is_empty()
            || route.name.len() > 64
            || !route.name.ends_with("-app")
            || !route
                .name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
            || routes[..index].iter().any(|prior| prior.name == route.name)
            || !route.socket_path.is_absolute()
            || route.host_uid != host_uid
            || route.host_uid == 0
            || route.host_unit.is_empty()
            || route.host_unit.len() > 256
            || !clean_text(&route.host_unit)
            || route.purse_resource != purse_resource
            || route.parent_task != parent_task
            || route.parent_task == route.purse_resource
            || route.participant_subject != participant_subject
            || route.signed_api_path != "/repo.git/"
        {
            return Err("application API route differs from operator dispatch binding".into());
        }
        for value in [
            &route.app_resource,
            &route.session_resource,
            &route.ticket_resource,
            &route.participant_subject,
            &route.purse_resource,
            &route.parent_task,
            &route.dispatch_selectors.package_manifest,
            &route.dispatch_selectors.snapshot_manifest,
            &route.dispatch_selectors.session_observe,
            &route.dispatch_selectors.manifest_observe,
            &route.dispatch_selectors.enrollment_observe,
        ] {
            if !canonical_decimal(value) || value == "0" {
                return Err("application API route resource identity is not canonical".into());
            }
        }
        if !canonical_decimal(&route.dispatch_selectors.issue_index) {
            return Err("application API issue history index is not canonical".into());
        }
        if [
            &route.app_generation,
            &route.session_generation,
            &route.dispatch_generation,
            &route.parent_generation,
        ]
        .iter()
        .any(|generation| !canonical_decimal(generation))
        {
            return Err("application API route generation is not canonical".into());
        }
    }
    Ok(())
}

/// `BeforeSend` is the only transport result that proves this invocation did
/// not send any request byte. Once a byte crosses the socket, an absent reply
/// is uncertain and must be inspected by the same durable operation ID.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum TransportError {
    BeforeSend(String),
    Uncertain(String),
}

/// A brief first-byte barrier shared with the hard-interrupt callback. If a
/// send has crossed before cancellation, the retained attempt is uncertain;
/// no later invocation gets a second dispatch under that operation ID.
pub(crate) struct ForwardSendGate {
    stopped: Mutex<bool>,
}

impl ForwardSendGate {
    pub(crate) fn new() -> Self {
        Self {
            stopped: Mutex::new(false),
        }
    }

    pub(crate) fn cancel(&self) {
        if let Ok(mut stopped) = self.stopped.lock() {
            *stopped = true;
        }
    }

    pub(crate) fn reset(&self) -> Result<(), String> {
        let mut stopped = self
            .stopped
            .lock()
            .map_err(|_| "application API send gate poisoned")?;
        *stopped = false;
        Ok(())
    }
}

fn first_write(
    stream: &mut UnixStream,
    frame: &[u8],
    gate: &ForwardSendGate,
    cancelled: &AtomicBool,
    deadline: Instant,
) -> Result<usize, TransportError> {
    loop {
        if Instant::now() >= deadline {
            return Err(TransportError::BeforeSend(
                "application API send deadline".into(),
            ));
        }
        let stopped = gate
            .stopped
            .lock()
            .map_err(|_| TransportError::BeforeSend("application API send gate poisoned".into()))?;
        if *stopped || cancelled.load(Ordering::SeqCst) {
            return Err(TransportError::BeforeSend(
                "application API send was cancelled".into(),
            ));
        }
        let result = stream.write(frame);
        drop(stopped);
        match result {
            Ok(0) => {
                return Err(TransportError::BeforeSend(
                    "application API socket closed".into(),
                ))
            }
            Ok(count) => return Ok(count),
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                thread::sleep(Duration::from_millis(2));
            }
            Err(error) => {
                return Err(TransportError::BeforeSend(format!(
                    "application API first write: {error}"
                )))
            }
        }
    }
}

fn transfer(
    stream: &mut UnixStream,
    bytes: &mut [u8],
    write: bool,
    deadline: Instant,
    cancelled: Option<&AtomicBool>,
) -> (usize, io::Result<()>) {
    let mut offset = 0;
    while offset < bytes.len() {
        if cancelled.is_some_and(|flag| flag.load(Ordering::SeqCst)) {
            return (
                offset,
                Err(io::Error::new(
                    io::ErrorKind::Interrupted,
                    "application API dispatch cancelled after first byte",
                )),
            );
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return (
                offset,
                Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "application API deadline",
                )),
            );
        }
        let result = if write {
            stream.write(&bytes[offset..])
        } else {
            stream.read(&mut bytes[offset..])
        };
        match result {
            Ok(0) => {
                return (
                    offset,
                    Err(io::Error::new(
                        io::ErrorKind::UnexpectedEof,
                        "application API socket closed",
                    )),
                )
            }
            Ok(count) => offset += count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(2));
            }
            Err(error) => {
                return (
                    offset,
                    Err(io::Error::new(
                        error.kind(),
                        format!("socket transfer: {error}"),
                    )),
                )
            }
        }
    }
    (offset, Ok(()))
}

fn connect_nonblocking(
    socket: &Path,
    deadline: Instant,
    cancelled: Option<&AtomicBool>,
) -> Result<UnixStream, TransportError> {
    if cancelled.is_some_and(|flag| flag.load(Ordering::SeqCst)) {
        return Err(TransportError::BeforeSend(
            "application API host connect cancelled".into(),
        ));
    }
    if Instant::now() >= deadline {
        return Err(TransportError::BeforeSend(
            "application API host connect deadline".into(),
        ));
    }
    let path = socket.as_os_str().as_bytes();
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if path.is_empty() || path.len() >= address.sun_path.len() || path.contains(&0) {
        return Err(TransportError::BeforeSend(
            "application API Unix socket path exceeds native sockaddr".into(),
        ));
    }
    address.sun_family = libc::AF_UNIX as libc::sa_family_t;
    for (slot, byte) in address.sun_path.iter_mut().zip(path) {
        *slot = *byte as libc::c_char;
    }
    let length = std::mem::offset_of!(libc::sockaddr_un, sun_path) + path.len() + 1;
    #[cfg(target_os = "macos")]
    {
        address.sun_len = u8::try_from(length).map_err(|_| {
            TransportError::BeforeSend("application API Darwin socket address too long".into())
        })?;
    }
    // Linux creates the fd close-on-exec atomically. Darwin has no libc
    // SOCK_CLOEXEC; set FD_CLOEXEC immediately below before connect. Its
    // socket/fcntl gap requires no concurrent child spawn for strict custody.
    #[cfg(target_os = "linux")]
    let socket_type = libc::SOCK_STREAM | libc::SOCK_CLOEXEC;
    #[cfg(target_os = "macos")]
    let socket_type = libc::SOCK_STREAM;
    let raw = unsafe { libc::socket(libc::AF_UNIX, socket_type, 0) };
    if raw < 0 {
        return Err(TransportError::BeforeSend(format!(
            "application API socket create: {}",
            io::Error::last_os_error()
        )));
    }
    let owned = unsafe { OwnedFd::from_raw_fd(raw) };
    #[cfg(target_os = "macos")]
    {
        let descriptor_flags = unsafe { libc::fcntl(owned.as_raw_fd(), libc::F_GETFD) };
        if descriptor_flags < 0
            || unsafe {
                libc::fcntl(
                    owned.as_raw_fd(),
                    libc::F_SETFD,
                    descriptor_flags | libc::FD_CLOEXEC,
                )
            } != 0
        {
            return Err(TransportError::BeforeSend(format!(
                "application API socket close-on-exec: {}",
                io::Error::last_os_error()
            )));
        }
    }
    let flags = unsafe { libc::fcntl(owned.as_raw_fd(), libc::F_GETFL) };
    if flags < 0
        || unsafe { libc::fcntl(owned.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) } != 0
    {
        return Err(TransportError::BeforeSend(format!(
            "application API socket nonblocking mode: {}",
            io::Error::last_os_error()
        )));
    }
    let status = unsafe {
        libc::connect(
            owned.as_raw_fd(),
            (&raw const address).cast(),
            length as libc::socklen_t,
        )
    };
    if status == 0 {
        return Ok(UnixStream::from(owned));
    }
    let error = io::Error::last_os_error();
    if error.raw_os_error() == Some(libc::EAGAIN) {
        return Err(TransportError::BeforeSend(
            "application API host connect backlog is full".into(),
        ));
    }
    if !matches!(error.raw_os_error(), Some(libc::EINPROGRESS | libc::EINTR)) {
        return Err(TransportError::BeforeSend(format!(
            "application API host connect: {error}"
        )));
    }
    loop {
        if cancelled.is_some_and(|flag| flag.load(Ordering::SeqCst)) {
            return Err(TransportError::BeforeSend(
                "application API host connect cancelled".into(),
            ));
        }
        if Instant::now() >= deadline {
            return Err(TransportError::BeforeSend(
                "application API host connect deadline".into(),
            ));
        }
        let mut ready = libc::pollfd {
            fd: owned.as_raw_fd(),
            events: libc::POLLOUT,
            revents: 0,
        };
        let polled = unsafe { libc::poll(&mut ready, 1, 20) };
        if polled == 0
            || (polled < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted)
        {
            continue;
        }
        if polled < 0 {
            return Err(TransportError::BeforeSend(format!(
                "application API host connect poll: {}",
                io::Error::last_os_error()
            )));
        }
        let mut socket_error: libc::c_int = 0;
        let mut size = std::mem::size_of::<libc::c_int>() as libc::socklen_t;
        if unsafe {
            libc::getsockopt(
                owned.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_ERROR,
                (&raw mut socket_error).cast(),
                &mut size,
            )
        } != 0
            || size as usize != std::mem::size_of::<libc::c_int>()
        {
            return Err(TransportError::BeforeSend(format!(
                "application API host connect result: {}",
                io::Error::last_os_error()
            )));
        }
        if socket_error != 0 {
            return Err(TransportError::BeforeSend(format!(
                "application API host connect: {}",
                io::Error::from_raw_os_error(socket_error)
            )));
        }
        // A saturated Unix listener can report POLLOUT with SO_ERROR=0 while
        // connect is still pending. Only a named peer proves completion.
        let mut peer: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
        let mut peer_len = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
        if unsafe { libc::getpeername(owned.as_raw_fd(), (&raw mut peer).cast(), &mut peer_len) }
            == 0
        {
            return Ok(UnixStream::from(owned));
        }
        let error = io::Error::last_os_error();
        if error.raw_os_error() != Some(libc::ENOTCONN) {
            return Err(TransportError::BeforeSend(format!(
                "application API host connect peer: {error}"
            )));
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

#[cfg(target_os = "linux")]
fn peer_uid(stream: &UnixStream) -> io::Result<u32> {
    use std::mem::{size_of, MaybeUninit};
    use std::os::fd::AsRawFd;
    let mut credential = MaybeUninit::<libc::ucred>::uninit();
    let mut len = size_of::<libc::ucred>() as libc::socklen_t;
    if unsafe {
        libc::getsockopt(
            stream.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            credential.as_mut_ptr().cast(),
            &mut len,
        )
    } != 0
        || len as usize != size_of::<libc::ucred>()
    {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { credential.assume_init() }.uid)
}

#[cfg(target_os = "macos")]
fn peer_uid(stream: &UnixStream) -> io::Result<u32> {
    use std::os::fd::AsRawFd;
    let mut uid = 0;
    let mut gid = 0;
    if unsafe { libc::getpeereid(stream.as_raw_fd(), &mut uid, &mut gid) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(uid)
}

/// Exactly one request frame and at most one response frame. The caller must
/// durably retain its operation ID and request bytes before entering here.
/// This function performs no retry, including after a lost response.
pub(crate) fn exchange_once(
    socket: &Path,
    expected_host_uid: u32,
    request: &Value,
    deadline: Instant,
) -> Result<Value, TransportError> {
    exchange_once_guarded(socket, expected_host_uid, request, deadline, None, None)
}

fn check_socket_ancestors(socket: &Path, expected_host_uid: u32) -> Result<(), TransportError> {
    let parent = socket
        .parent()
        .ok_or_else(|| TransportError::BeforeSend("application API socket has no parent".into()))?;
    for (depth, ancestor) in parent.ancestors().enumerate() {
        let metadata = fs::symlink_metadata(ancestor).map_err(|error| {
            TransportError::BeforeSend(format!("application API socket ancestor: {error}"))
        })?;
        let safe_sticky = depth > 0 && metadata.uid() == 0 && metadata.mode() & 0o1000 != 0;
        if !metadata.file_type().is_dir()
            || metadata.file_type().is_symlink()
            || (metadata.mode() & 0o022 != 0 && !safe_sticky)
            || !matches!(metadata.uid(), 0)
                && metadata.uid() != expected_host_uid
                && metadata.uid() != unsafe { libc::geteuid() }
        {
            return Err(TransportError::BeforeSend(format!(
                "application API socket ancestor {} is not a protected directory",
                ancestor.display()
            )));
        }
    }
    Ok(())
}

fn exchange_once_guarded(
    socket: &Path,
    expected_host_uid: u32,
    request: &Value,
    deadline: Instant,
    send_gate: Option<(&ForwardSendGate, &AtomicBool)>,
    cancelled: Option<&AtomicBool>,
) -> Result<Value, TransportError> {
    let encoded = serde_json::to_vec(request)
        .map_err(|error| TransportError::BeforeSend(error.to_string()))?;
    if encoded.is_empty() || encoded.len() > MAX_FORWARD_FRAME {
        return Err(TransportError::BeforeSend(
            "application API forward request exceeds frame bound".into(),
        ));
    }
    check_socket_ancestors(socket, expected_host_uid)?;
    let before = fs::symlink_metadata(socket)
        .map_err(|error| TransportError::BeforeSend(format!("host socket: {error}")))?;
    if !before.file_type().is_socket() {
        return Err(TransportError::BeforeSend(
            "application API forward path is not a socket".into(),
        ));
    }
    let mut stream = connect_nonblocking(socket, deadline, cancelled)?;
    if peer_uid(&stream)
        .map_err(|error| TransportError::BeforeSend(format!("host peer UID: {error}")))?
        != expected_host_uid
    {
        return Err(TransportError::BeforeSend(
            "application API host peer UID differs".into(),
        ));
    }
    let after = fs::symlink_metadata(socket)
        .map_err(|error| TransportError::BeforeSend(format!("host socket recheck: {error}")))?;
    if !after.file_type().is_socket() || (before.dev(), before.ino()) != (after.dev(), after.ino())
    {
        return Err(TransportError::BeforeSend(
            "application API host socket identity changed".into(),
        ));
    }
    stream
        .set_nonblocking(true)
        .map_err(|error| TransportError::BeforeSend(format!("host socket mode: {error}")))?;
    let mut frame = Vec::with_capacity(encoded.len() + 4);
    frame.extend_from_slice(&(encoded.len() as u32).to_be_bytes());
    frame.extend_from_slice(&encoded);
    let initially_written = if let Some((gate, cancelled)) = send_gate {
        first_write(&mut stream, &frame, gate, cancelled, deadline)?
    } else {
        0
    };
    let (remaining, sent) = if initially_written == frame.len() {
        (0, Ok(()))
    } else {
        if let Some((_, cancelled)) = send_gate {
            if cancelled.load(Ordering::SeqCst) {
                return Err(TransportError::Uncertain(
                    "application API send cancelled after first byte".into(),
                ));
            }
        }
        transfer(
            &mut stream,
            &mut frame[initially_written..],
            true,
            deadline,
            cancelled,
        )
    };
    let written = initially_written + remaining;
    if let Err(error) = sent {
        return Err(if written == 0 {
            TransportError::BeforeSend(format!("host request was not sent: {error}"))
        } else {
            TransportError::Uncertain(format!("host request delivery uncertain: {error}"))
        });
    }
    let mut size = [0_u8; 4];
    transfer(&mut stream, &mut size, false, deadline, cancelled)
        .1
        .map_err(|error| TransportError::Uncertain(format!("host reply header: {error}")))?;
    let size = u32::from_be_bytes(size) as usize;
    let max_reply = if request.get("type").and_then(Value::as_str) == Some("inspect") {
        MAX_INSPECT_REPLY_FRAME
    } else {
        MAX_FORWARD_FRAME
    };
    if size == 0 || size > max_reply {
        return Err(TransportError::Uncertain(
            "host reply exceeds frame bound".into(),
        ));
    }
    let mut payload = vec![0_u8; size];
    transfer(&mut stream, &mut payload, false, deadline, cancelled)
        .1
        .map_err(|error| {
            TransportError::Uncertain(format!("host reply payload ({size} bytes): {error}"))
        })?;
    // Decode against the strict tagged wire before admitting a Value. Direct
    // typed decoding rejects duplicate fields that Value would collapse.
    serde_json::from_slice::<HostReply>(&payload)
        .map_err(|error| TransportError::Uncertain(format!("host reply wire: {error}")))?;
    serde_json::from_slice(&payload)
        .map_err(|error| TransportError::Uncertain(format!("host reply JSON: {error}")))
}

/// A forward call runs on an I/O-only thread. It owns no Mini key or Runtime
/// journal, so the controller thread remains free to service the host's
/// reverse dispatch-custody requests while this one-shot call is pending.
pub(crate) struct PendingExchange {
    result: Receiver<Result<Value, TransportError>>,
}

impl PendingExchange {
    pub(crate) fn poll(&self) -> Option<Result<Value, TransportError>> {
        match self.result.try_recv() {
            Ok(result) => Some(result),
            Err(TryRecvError::Empty) => None,
            Err(TryRecvError::Disconnected) => Some(Err(TransportError::Uncertain(
                "application API I/O worker exited without a result".into(),
            ))),
        }
    }
}

pub(crate) fn start_exchange_once(
    socket: &Path,
    expected_host_uid: u32,
    request: Value,
    deadline: Instant,
    cancelled: Arc<AtomicBool>,
) -> Result<PendingExchange, TransportError> {
    let (reply, result) = mpsc::channel();
    let socket = socket.to_owned();
    thread::Builder::new()
        .name("mini-application-api".into())
        .spawn(move || {
            let _ = reply.send(exchange_once_guarded(
                &socket,
                expected_host_uid,
                &request,
                deadline,
                None,
                Some(&cancelled),
            ));
        })
        .map_err(|error| {
            TransportError::BeforeSend(format!("application API worker spawn: {error}"))
        })?;
    Ok(PendingExchange { result })
}

pub(crate) fn start_dispatch_once(
    socket: &Path,
    expected_host_uid: u32,
    request: Value,
    deadline: Instant,
    send_gate: Arc<ForwardSendGate>,
    cancelled: Arc<AtomicBool>,
) -> Result<PendingExchange, TransportError> {
    let (reply, result) = mpsc::channel();
    let socket = socket.to_owned();
    thread::Builder::new()
        .name("mini-application-api-dispatch".into())
        .spawn(move || {
            let outcome = exchange_once_guarded(
                &socket,
                expected_host_uid,
                &request,
                deadline,
                Some((&send_gate, &cancelled)),
                Some(&cancelled),
            );
            let _ = reply.send(outcome);
        })
        .map_err(|error| {
            TransportError::BeforeSend(format!("application API dispatch worker spawn: {error}"))
        })?;
    Ok(PendingExchange { result })
}

fn clean_text(value: &str) -> bool {
    !value
        .bytes()
        .any(|byte| matches!(byte, 0 | 10 | 13 | 127) || (byte < 0x20 && byte != b'\t'))
}

fn decode_hex(value: &str) -> Result<Vec<u8>, String> {
    if !value.len().is_multiple_of(2) || value.len() > 2 * MAX_BODY_BYTES {
        return Err("application API bodyHex exceeds bound or has odd length".into());
    }
    let mut body = Vec::with_capacity(value.len() / 2);
    for pair in value.as_bytes().chunks_exact(2) {
        let digit = |byte: u8| -> Option<u8> {
            match byte {
                b'0'..=b'9' => Some(byte - b'0'),
                b'a'..=b'f' => Some(byte - b'a' + 10),
                _ => None,
            }
        };
        body.push(
            digit(pair[0])
                .zip(digit(pair[1]))
                .map(|(high, low)| high * 16 + low)
                .ok_or("application API bodyHex is not lowercase hex")?,
        );
    }
    Ok(body)
}

/// Parse a single MCP tool call against operator-selected names. This is a
/// preflight bound only; it never authorizes a session, dispatch or charge.
pub(crate) fn parse_input(
    arguments: &Value,
    allowed_applications: &[String],
) -> Result<HttpInput, String> {
    let encoded = serde_json::to_vec(arguments).map_err(|error| error.to_string())?;
    if encoded.len() > MAX_TOOL_INPUT_BYTES {
        return Err("application API tool input exceeds MCP frame bound".into());
    }
    let object = arguments
        .as_object()
        .ok_or("application API arguments must be an object")?;
    if object.len() != 6
        || object.keys().any(|key| {
            !matches!(
                key.as_str(),
                "application" | "method" | "path" | "query" | "headers" | "bodyHex"
            )
        })
    {
        return Err("application API arguments have noncanonical fields".into());
    }
    let string = |key: &str| -> Result<&str, String> {
        object
            .get(key)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("application API {key} must be a string"))
    };
    let application = string("application")?;
    if !allowed_applications.iter().any(|name| name == application) {
        return Err("application API name is not operator-selected".into());
    }
    let method = string("method")?;
    if !matches!(method, "GET" | "HEAD" | "POST" | "PUT" | "PATCH" | "DELETE") {
        return Err("application API method is unavailable".into());
    }
    let path = string("path")?;
    let query = string("query")?;
    if path.starts_with('/')
        || path.contains(['?', '#'])
        || query.contains('#')
        || !clean_text(path)
        || !clean_text(query)
        || path.len() + query.len() > MAX_PATH_QUERY_BYTES
    {
        return Err("application API path or query is outside native profile".into());
    }
    let headers = object
        .get("headers")
        .and_then(Value::as_array)
        .ok_or("application API headers must be an array")?;
    if headers.len() > MAX_HEADERS {
        return Err("application API header count exceeds native profile".into());
    }
    let mut ordered_headers = Vec::with_capacity(headers.len());
    for header in headers {
        let fields = header
            .as_object()
            .ok_or("application API header must be an object")?;
        if fields.len() != 2 || !fields.contains_key("name") || !fields.contains_key("value") {
            return Err("application API header fields are noncanonical".into());
        }
        let name = fields
            .get("name")
            .and_then(Value::as_str)
            .ok_or("application API header name must be a string")?;
        let value = fields
            .get("value")
            .and_then(Value::as_str)
            .ok_or("application API header value must be a string")?;
        if !ORDINARY_HEADERS.contains(&name)
            || name.len() > 128
            || value.len() > 8192
            || !clean_text(value)
        {
            return Err("application API header is outside native ordinary-header profile".into());
        }
        ordered_headers.push((name.to_owned(), value.to_owned()));
    }
    let body = decode_hex(string("bodyHex")?)?;
    if matches!(method, "GET" | "HEAD" | "DELETE") && !body.is_empty() {
        return Err("application API body is unavailable for this method".into());
    }
    Ok(HttpInput {
        application: application.to_owned(),
        method: method.to_owned(),
        path: path.to_owned(),
        query: query.to_owned(),
        ordered_headers,
        body,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn definite_gitweb_http_projects_bounded_readable_body_without_changing_receipt() {
        let raw = json!({"type":"http-v3","status":200,
            "bodyHex":"3c68313e4769745765623c2f68313e",
            "responseSha256":"aa".repeat(32),
            "committedReceipt":{"transactionId":"1","eventId":"2",
                "acceptedCount":"3","imageBoundary":"4"}});
        let shown = present_lifetime_http(&raw).unwrap();
        assert_eq!(shown["bodyText"], "<h1>GitWeb</h1>");
        assert_eq!(shown["bodyBytes"], 15);
        assert_eq!(shown["bodyPresentation"], "utf-8");
        assert!(shown.get("bodyHex").is_none());
        assert_eq!(shown["committedReceipt"], raw["committedReceipt"]);
        assert_eq!(raw["bodyHex"], "3c68313e4769745765623c2f68313e");
        let binary = json!({"type":"http-v3","bodyHex":"00ff"});
        let omitted = present_lifetime_http(&binary).unwrap();
        assert_eq!(omitted["bodyPresentation"], "binary-or-oversize-omitted");
        assert!(omitted.get("bodyText").is_none());
        let oversized = json!({"type":"http-v3","bodyHex":"61".repeat(32_769)});
        assert_eq!(
            present_lifetime_http(&oversized).unwrap()["bodyBytes"],
            32_769
        );
        assert!(present_lifetime_http(&json!({"type":"http-v3","bodyHex":"0G"})).is_err());
        assert!(present_lifetime_http(&json!({"type":"uncertain-v3","bodyHex":""})).is_err());
    }
    use serde_json::json;
    use std::os::unix::fs::PermissionsExt;
    use std::os::unix::net::UnixListener;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::thread;

    static NEXT_SOCKET: AtomicUsize = AtomicUsize::new(1);

    fn socket_path() -> std::path::PathBuf {
        let directory = std::env::temp_dir().join(format!(
            "mini-application-api-{}-{}",
            std::process::id(),
            NEXT_SOCKET.fetch_add(1, Ordering::SeqCst)
        ));
        fs::create_dir(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        fs::canonicalize(directory).unwrap().join("agent.sock")
    }

    fn remove_socket(path: &Path) {
        if path.exists() {
            fs::remove_file(path).unwrap();
        }
        fs::remove_dir(path.parent().unwrap()).unwrap();
    }

    fn request() -> Value {
        json!({"application":"workroom", "method":"POST", "path":"git-receive-pack",
            "query":"service=git-receive-pack", "headers":[{"name":"content-type","value":"application/x-git-receive-pack-request"}],
            "bodyHex":"000102ff"})
    }

    #[test]
    fn preserves_exact_bounded_http_input_without_model_authority_fields() {
        let parsed = parse_input(&request(), &["workroom".into()]).unwrap();
        assert_eq!(parsed.body, [0, 1, 2, 255]);
        assert_eq!(parsed.ordered_headers[0].0, "content-type");
        assert_eq!(parsed.path, "git-receive-pack");
        assert!(parse_input(&request(), &["other".into()]).is_err());
        let mut extra = request();
        extra["ticketResource"] = json!("17");
        assert!(parse_input(&extra, &["workroom".into()]).is_err());
        let wire = dispatch_request(7, &parsed);
        assert_eq!(wire["protocol"], PROTOCOL);
        assert_eq!(wire["operation_id"], "7");
        assert_eq!(wire["body_hex"], "000102ff");
        assert_eq!(wire["headers"][0]["name"], "content-type");
        assert!(wire.get("ticket").is_none());
        assert_eq!(hello_request()["type"], "hello");
        assert_eq!(inspect_request(7)["operation_id"], "7");
        assert_eq!(
            inspect_historical_request(7, &"a".repeat(64)).unwrap()["binding_sha256"],
            "a".repeat(64)
        );
        assert!(inspect_historical_request(7, "A").is_err());
    }

    #[test]
    fn reserve_http_requires_exact_forward_bytes_under_fixed_app_prefix() {
        let parsed = parse_input(&request(), &["workroom".into()]).unwrap();
        let retained = dispatch_request(37, &parsed);
        let expected = json!({"base":{"http":{
            "operationId":"37",
            "methodHex":"504f5354",
            "pathHex":hex(b"repo.git/git-receive-pack"),
            "queryHex":hex(b"service=git-receive-pack"),
            "headers":[{"nameHex":hex(b"content-type"),
                "valueHex":hex(b"application/x-git-receive-pack-request"),
                "generated":false}],
            "bodyHex":"000102ff"}}});
        verify_routed_reserve_http(&retained, "/repo.git/", &expected).unwrap();
        for key in ["methodHex", "pathHex", "queryHex", "bodyHex", "operationId"] {
            let mut changed = expected.clone();
            changed["base"]["http"][key] = json!("00");
            assert!(
                verify_routed_reserve_http(&retained, "/repo.git/", &changed).is_err(),
                "{key}"
            );
        }
        let mut changed = expected.clone();
        changed["base"]["http"]["headers"][0]["generated"] = json!(true);
        assert!(verify_routed_reserve_http(&retained, "/repo.git/", &changed).is_err());
        let mut changed = expected.clone();
        changed["base"]["http"]["headers"][0]["valueHex"] = json!("00");
        assert!(verify_routed_reserve_http(&retained, "/repo.git/", &changed).is_err());
        let mut changed = expected.clone();
        changed["base"]["http"]["headers"] = json!([]);
        assert!(verify_routed_reserve_http(&retained, "/repo.git/", &changed).is_err());
        assert!(verify_routed_reserve_http(&retained, "/other/", &expected).is_err());
    }

    #[test]
    fn read_only_inspection_recovers_only_exact_hashed_http_reply() {
        let binding = "a".repeat(64);
        let original = HostReply::Http {
            protocol: PROTOCOL.into(),
            operation_id: "37".into(),
            binding_sha256: binding.clone(),
            status: 200,
            headers: vec![HostHeader {
                name: "content-type".into(),
                value: "text/plain".into(),
            }],
            body_hex: "00ff".into(),
        };
        let bytes = serde_json::to_vec(&original).unwrap();
        let exact_hex = hex(&bytes);
        let digest = hex(&Sha256::digest(&bytes));
        let inspection = HostReply::Inspection {
            protocol: PROTOCOL.into(),
            operation_id: "37".into(),
            binding_sha256: binding.clone(),
            state: "definite".into(),
            definite_reply_json_hex: Some(exact_hex.clone()),
            definite_reply_sha256: Some(digest.clone()),
            retention_error: None,
        };
        assert_eq!(
            recovered_definite_http(&inspection, 37, &binding).unwrap(),
            Some(original)
        );
        let corrupt = HostReply::Inspection {
            protocol: PROTOCOL.into(),
            operation_id: "37".into(),
            binding_sha256: binding.clone(),
            state: "definite".into(),
            definite_reply_json_hex: Some(exact_hex.clone()),
            definite_reply_sha256: Some("0".repeat(64)),
            retention_error: None,
        };
        assert!(recovered_definite_http(&corrupt, 37, &binding).is_err());
        let missing = HostReply::Inspection {
            protocol: PROTOCOL.into(),
            operation_id: "37".into(),
            binding_sha256: binding.clone(),
            state: "definite".into(),
            definite_reply_json_hex: None,
            definite_reply_sha256: None,
            retention_error: None,
        };
        assert_eq!(
            recovered_definite_http(&missing, 37, &binding).unwrap(),
            None
        );
        let mismatched = HostReply::Inspection {
            protocol: PROTOCOL.into(),
            operation_id: "38".into(),
            binding_sha256: binding.clone(),
            state: "definite".into(),
            definite_reply_json_hex: Some(exact_hex),
            definite_reply_sha256: Some(digest),
            retention_error: None,
        };
        assert!(recovered_definite_http(&mismatched, 37, &binding).is_err());
        let unverified = HostReply::Inspection {
            protocol: PROTOCOL.into(),
            operation_id: "37".into(),
            binding_sha256: binding.clone(),
            state: "uncertain".into(),
            definite_reply_json_hex: None,
            definite_reply_sha256: None,
            retention_error: Some("definite-reply-unverified".into()),
        };
        assert_eq!(
            recovered_definite_http(&unverified, 37, &binding).unwrap(),
            None
        );
        let mut invalid = serde_json::to_value(&unverified).unwrap();
        invalid["state"] = json!("definite");
        let invalid = parse_host_reply(invalid).unwrap();
        assert!(verify_operation_reply(&invalid, 37, &binding).is_err());
    }

    #[test]
    fn refuses_generated_headers_ambiguous_paths_and_body_mismatch() {
        let mut input = request();
        input["headers"] = json!([{"name":"x-sandstorm-permissions","value":"read,write"}]);
        assert!(parse_input(&input, &["workroom".into()]).is_err());
        input = request();
        input["path"] = json!("/repo.git");
        assert!(parse_input(&input, &["workroom".into()]).is_err());
        input = request();
        input["method"] = json!("GET");
        assert!(parse_input(&input, &["workroom".into()]).is_err());
        input = request();
        input["bodyHex"] = json!("00FF");
        assert!(parse_input(&input, &["workroom".into()]).is_err());
    }

    #[test]
    fn route_requires_fixed_purse_subject_and_unique_named_app() {
        let route = RoutePin {
            name: "workroom-app".into(),
            socket_path: "/tmp/host-agent.sock".into(),
            host_uid: 1001,
            host_unit: "spk-host@example.service".into(),
            app_resource: "6100".into(),
            app_generation: "2".into(),
            session_resource: "6209".into(),
            session_generation: "3".into(),
            ticket_resource: "6408".into(),
            participant_subject: "8".into(),
            parent_task: "6000".into(),
            parent_generation: "5".into(),
            purse_resource: "6500".into(),
            dispatch_generation: "4".into(),
            signed_api_path: "/repo.git/".into(),
            dispatch_selectors: DispatchSelectorPin {
                issue_index: "9".into(),
                package_manifest: "6101".into(),
                snapshot_manifest: "6102".into(),
                session_observe: "81".into(),
                manifest_observe: "82".into(),
                enrollment_observe: "83".into(),
            },
        };
        assert!(validate_routes(std::slice::from_ref(&route), "6000", "6500", "8", 1001).is_ok());
        assert!(
            validate_routes(&[route.clone(), route.clone()], "6000", "6500", "8", 1001).is_err()
        );
        assert!(validate_routes(std::slice::from_ref(&route), "6000", "6501", "8", 1001).is_err());
        let mut changed = route;
        changed.ticket_resource = "06408".into();
        assert!(validate_routes(&[changed.clone()], "6000", "6500", "8", 1001).is_err());
        let mut changed = RoutePin {
            dispatch_selectors: DispatchSelectorPin {
                issue_index: "00".into(),
                package_manifest: "6101".into(),
                snapshot_manifest: "6102".into(),
                session_observe: "81".into(),
                manifest_observe: "82".into(),
                enrollment_observe: "83".into(),
            },
            ..changed
        };
        changed.ticket_resource = "6408".into();
        assert!(validate_routes(&[changed], "6000", "6500", "8", 1001).is_err());
    }

    fn lifetime_route() -> LifetimeRoutePin {
        let receipt = |count: &str| SourceReceiptPin {
            transaction_id: "123456789012345678901234567890".into(),
            event_id: "234567890123456789012345678901".into(),
            accepted_count: count.into(),
            image_boundary: "345678901234567890123456789012".into(),
        };
        LifetimeRoutePin {
            name: "shared-app".into(),
            socket_path: "/tmp/lifetime-host-agent.sock".into(),
            host_uid: 1001,
            host_unit: "spk-host@example.service".into(),
            app_resource: "6100".into(),
            session_resource: "6209".into(),
            ticket_resource: "6408".into(),
            participant_subject: "8".into(),
            parent_task: "6000".into(),
            original_parent_generation: "1".into(),
            original_descriptor_sha256: "ab".repeat(32),
            purse_resource: "6500".into(),
            signed_api_path: "/repo.git/".into(),
            dispatch_selectors: DispatchSelectorPin {
                issue_index: "9".into(),
                package_manifest: "6101".into(),
                snapshot_manifest: "6102".into(),
                session_observe: "81".into(),
                manifest_observe: "82".into(),
                enrollment_observe: "83".into(),
            },
            grant_issue_index: "13".into(),
            grant_resource: "6600".into(),
            grant_observe_capability: "84".into(),
            grant_attempt_dir: "/tmp/grant-attempt".into(),
            grant_digest: "456789012345678901234567890123".into(),
            grant_initialized_root: "567890123456789012345678901234".into(),
            original_issue_receipt: receipt("10"),
            grant_issue_receipt: receipt("14"),
        }
    }

    #[test]
    fn lifetime_hello_pins_historical_lineage_and_forward_has_no_current_claim() {
        let route = lifetime_route();
        let binding = LifetimeBinding {
            protocol: "mini-spk-agent-lifetime-binding-v3".into(),
            lineage: LifetimeLineage {
                app_resource: route.app_resource.clone(),
                session_resource: route.session_resource.clone(),
                participant_subject: route.participant_subject.clone(),
                ticket_resource: route.ticket_resource.clone(),
                original_parent_task: route.parent_task.clone(),
                original_parent_generation: route.original_parent_generation.clone(),
                original_issue_index: route.dispatch_selectors.issue_index.clone(),
                original_issue_receipt: route.original_issue_receipt.clone(),
                original_descriptor_sha256: route.original_descriptor_sha256.clone(),
                grant_resource: route.grant_resource.clone(),
                grant_issue_index: route.grant_issue_index.clone(),
                grant_digest: route.grant_digest.clone(),
                grant_initialized_root: route.grant_initialized_root.clone(),
                grant_issue_receipt: route.grant_issue_receipt.clone(),
                parent_task: route.parent_task.clone(),
                purse_task: route.purse_resource.clone(),
            },
            signed_api_path: route.signed_api_path.clone(),
            host_unit: route.host_unit.clone(),
            host_invocation: "ab".repeat(16),
        };
        let mut digest = Sha256::new();
        digest.update(b"DREGG/SPK-AGENT-LIFETIME-BINDING/v3\0");
        digest.update(serde_json::to_vec(&binding).unwrap());
        let sha = hex(&digest.finalize());
        let reply = json!({"type":"binding-v3","protocol":LIFETIME_PROTOCOL,
            "binding":binding,"bindingSha256":sha});
        let (checked, invocation) = verify_lifetime_binding_reply(reply.clone(), &route).unwrap();
        assert_eq!(checked, sha);
        assert_eq!(invocation, "ab".repeat(16));
        let mut changed = route.clone();
        changed.original_parent_generation = "2".into();
        assert!(verify_lifetime_binding_reply(reply.clone(), &changed).is_err());
        changed = route.clone();
        changed.original_descriptor_sha256 = "cd".repeat(32);
        assert!(verify_lifetime_binding_reply(reply, &changed).is_err());
        let forward = lifetime_dispatch_request(
            9,
            &sha,
            &HttpInput {
                application: route.name,
                method: "GET".into(),
                path: "info/refs".into(),
                query: "service=git-upload-pack".into(),
                ordered_headers: vec![],
                body: vec![],
            },
        )
        .unwrap();
        assert_eq!(forward["type"], "dispatch-v3");
        assert_eq!(forward["bindingSha256"], sha);
        assert!(forward.get("current").is_none());
        assert_eq!(
            routed_reserve_http(&forward, &route.signed_api_path).unwrap()["operationId"],
            "9"
        );
    }

    #[test]
    fn lifetime_fingerprint_matches_resident_golden_vector() {
        let current = LifetimeCurrentClaims {
            app_generation: "4".into(),
            session_generation: "5".into(),
            parent_generation: "6".into(),
            purse_generation: "7".into(),
            app_physical_root: "200".into(),
            session_physical_root: "201".into(),
            parent_physical_root: "202".into(),
            purse_physical_root: "203".into(),
        };
        assert_eq!(
            lifetime_operation_fingerprint(
                "35065312baf0eb84168bf6b6037d776907411e0ae571d0b16de64046ad081d46",
                &current,
                "9",
                &"cd".repeat(32),
            )
            .unwrap(),
            "2824c93080445e7846b388355db9bd0fab208b2fa311d4f2125b1650759f00f1"
        );
    }

    #[test]
    fn lifetime_route_pins_historical_receipts_without_current_generations() {
        let route = lifetime_route();
        assert!(validate_lifetime_routes(
            std::slice::from_ref(&route),
            &[],
            "6000",
            "6500",
            "8",
            1001
        )
        .is_ok());
        let mut changed = route.clone();
        changed.grant_issue_receipt.accepted_count = "13".into();
        assert!(validate_lifetime_routes(&[changed], &[], "6000", "6500", "8", 1001).is_err());
        let mut changed = route.clone();
        changed.grant_digest = "0456789".into();
        assert!(validate_lifetime_routes(&[changed], &[], "6000", "6500", "8", 1001).is_err());
        assert!(
            validate_lifetime_routes(&[route.clone(), route], &[], "6000", "6500", "8", 1001)
                .is_err()
        );
    }

    #[test]
    fn lifetime_reserve_inspection_binds_exact_http_and_historical_grant() {
        let route = lifetime_route();
        let retained =
            dispatch_request(37, &parse_input(&request(), &["workroom".into()]).unwrap());
        let http = routed_reserve_http(&retained, &route.signed_api_path).unwrap();
        let selectors = json!({"sourceBuiltExactSelectors":"test"});
        let source = json!({
            "type":"application-agent-lifetime-author-request-v3",
            "fixedSelectors":selectors,
            "http":http,
            "canonicalRequestHex":"0102",
            "canonicalHttpHex":"0304",
            "requestDigest":"901"
        });
        let plan = json!({
            "type":"application-agent-lifetime-reserve-plan-v3",
            "fixedSelectors":selectors,
            "http":http,
            "canonicalRequestHex":"0102",
            "canonicalHttpHex":"0304",
            "context":{
                "appResource":"6100","sessionResource":"6209",
                "participantSubject":"8","ticketResource":"6408",
                "parentTask":"6000","parentGeneration":"7",
                "purseTask":"6500","purseGeneration":"6",
                "grantResource":"6600","grantIssueIndex":"13",
                "grantDigest":route.grant_digest,
                "reserveOperationId":"88","httpOperationId":"37",
                "requestDigest":"901"
            },
            "bindings":{
                "originalIssueReceipt":route.original_issue_receipt,
                "grantIssueReceipt":route.grant_issue_receipt,
                "grantInitializedRoot":route.grant_initialized_root,
                "grantPhysicalRoot":route.grant_initialized_root,
                "appPhysicalRoot":"800",
                "sessionPhysicalRoot":"801",
                "parentPhysicalRoot":"802",
                "pursePhysicalRoot":"803"
            }
        });
        let verify = |request: &Value, plan: &Value| {
            verify_lifetime_reserve_inspection(LifetimeReserveInspection {
                route: &route,
                retained_forward: &retained,
                expected_selectors: &selectors,
                reserve_operation_id: "88",
                signed_parent_generation: "7",
                signed_purse_generation: "6",
                signed_app_physical_root: "800",
                signed_session_physical_root: "801",
                signed_parent_physical_root: "802",
                signed_purse_physical_root: "803",
                request,
                plan,
            })
        };
        verify(&source, &plan).unwrap();
        let mut changed = source.clone();
        changed["http"]["headers"][0]["generated"] = json!(true);
        assert!(verify(&changed, &plan).is_err());
        let mut changed = plan.clone();
        changed["bindings"]["grantIssueReceipt"]["imageBoundary"] = json!("1");
        assert!(verify(&source, &changed).is_err());
        let mut changed = plan.clone();
        changed["context"]["parentGeneration"] = json!("8");
        assert!(verify(&source, &changed).is_err());
        let mut changed = plan.clone();
        changed["bindings"]["grantPhysicalRoot"] = json!("9");
        assert!(verify(&source, &changed).is_err());
        let mut changed = plan.clone();
        changed["bindings"]["sessionPhysicalRoot"] = json!("9");
        assert!(verify(&source, &changed).is_err());
    }

    #[test]
    fn lifetime_paid_inspection_keeps_history_but_accepts_new_purse_root() {
        let reserve = json!({
            "type":"application-agent-lifetime-reserve-plan-v3",
            "fixedSelectors":{"grantIssueIndex":"13"},
            "context":{"canonicalHex":"abcd","parentGeneration":"7"},
            "canonicalHttpHex":"0102",
            "http":{"operationId":"37","bodyHex":"ff"},
            "bindings":{
                "originalIssueReceipt":{"acceptedCount":"10"},
                "grantIssueReceipt":{"acceptedCount":"14"},
                "grantInitializedRoot":"41",
                "grantPhysicalRoot":"41",
                "appPhysicalRoot":"50",
                "sessionPhysicalRoot":"51",
                "parentPhysicalRoot":"52",
                "pursePhysicalRoot":"63"
            }
        });
        let receipt = json!({"transactionId":"71","eventId":"72",
            "acceptedCount":"15","imageBoundary":"73"});
        let mut paid = reserve.clone();
        paid["type"] = json!("application-agent-lifetime-paid-plan-v3");
        paid["reserveIndex"] = json!("14");
        paid["reserveReceipt"] = receipt.clone();
        paid["bindings"]["pursePhysicalRoot"] = json!("64");
        let verify = |paid: &Value| {
            verify_lifetime_paid_inspection(LifetimePaidInspection {
                reserve: &reserve,
                paid,
                reserve_index: "14",
                reserve_receipt: &receipt,
                signed_post_purse_physical_root: "64",
            })
        };
        verify(&paid).unwrap();
        let mut changed = paid.clone();
        changed["bindings"]["grantPhysicalRoot"] = json!("42");
        assert!(verify(&changed).is_err());
        let mut changed = paid.clone();
        changed["bindings"]["appPhysicalRoot"] = json!("55");
        assert!(verify(&changed).is_err());
        let mut changed = paid.clone();
        changed["http"]["bodyHex"] = json!("ee");
        assert!(verify(&changed).is_err());
        let mut changed = paid.clone();
        changed["reserveReceipt"]["eventId"] = json!("74");
        assert!(verify(&changed).is_err());
    }

    #[test]
    fn forward_exchange_sends_one_exact_frame_and_requires_one_reply() {
        let path = socket_path();
        let listener = UnixListener::bind(&path).unwrap();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut size = [0_u8; 4];
            stream.read_exact(&mut size).unwrap();
            let mut payload = vec![0_u8; u32::from_be_bytes(size) as usize];
            stream.read_exact(&mut payload).unwrap();
            assert_eq!(
                serde_json::from_slice::<Value>(&payload).unwrap(),
                json!({"type":"dispatch","operation_id":"7"})
            );
            let reply = serde_json::to_vec(&json!({"type":"refused","protocol":PROTOCOL,
                "operation_id":"7","binding_sha256":"0".repeat(64),"code":"disabled"}))
            .unwrap();
            stream
                .write_all(&(reply.len() as u32).to_be_bytes())
                .unwrap();
            stream.write_all(&reply).unwrap();
        });
        let pending = start_exchange_once(
            &path,
            unsafe { libc::geteuid() },
            json!({"type":"dispatch","operation_id":"7"}),
            Instant::now() + Duration::from_secs(2),
            Arc::new(AtomicBool::new(false)),
        )
        .unwrap();
        let reply = loop {
            if let Some(result) = pending.poll() {
                break result.unwrap();
            }
            thread::sleep(Duration::from_millis(2));
        };
        assert_eq!(reply["operation_id"], "7");
        server.join().unwrap();
        remove_socket(&path);
    }

    #[test]
    fn lost_reply_is_uncertain_and_no_connect_is_definite_no_send() {
        let absent = socket_path();
        assert!(matches!(
            exchange_once(
                &absent,
                unsafe { libc::geteuid() },
                &json!({"type":"inspect","operation_id":"8"}),
                Instant::now() + Duration::from_secs(2),
            ),
            Err(TransportError::BeforeSend(_))
        ));
        remove_socket(&absent);
        let path = socket_path();
        let listener = UnixListener::bind(&path).unwrap();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut size = [0_u8; 4];
            stream.read_exact(&mut size).unwrap();
            let mut payload = vec![0_u8; u32::from_be_bytes(size) as usize];
            stream.read_exact(&mut payload).unwrap();
        });
        assert!(matches!(
            exchange_once(
                &path,
                unsafe { libc::geteuid() },
                &json!({"type":"dispatch","operation_id":"8"}),
                Instant::now() + Duration::from_secs(2),
            ),
            Err(TransportError::Uncertain(_))
        ));
        server.join().unwrap();
        remove_socket(&path);
    }

    #[test]
    fn fixed_binding_hash_and_operation_reply_match_exact_operator_coordinates() {
        let route = RoutePin {
            name: "workroom-app".into(),
            socket_path: "/tmp/host-agent.sock".into(),
            host_uid: 1001,
            host_unit: "spk-host@example.service".into(),
            app_resource: "6100".into(),
            app_generation: "2".into(),
            session_resource: "6209".into(),
            session_generation: "3".into(),
            ticket_resource: "6408".into(),
            participant_subject: "8".into(),
            parent_task: "6000".into(),
            parent_generation: "5".into(),
            purse_resource: "6500".into(),
            dispatch_generation: "4".into(),
            signed_api_path: "/repo.git/".into(),
            dispatch_selectors: DispatchSelectorPin {
                issue_index: "9".into(),
                package_manifest: "6101".into(),
                snapshot_manifest: "6102".into(),
                session_observe: "81".into(),
                manifest_observe: "82".into(),
                enrollment_observe: "83".into(),
            },
        };
        let binding = FixedBinding {
            protocol: "mini-spk-agent-binding-v1".into(),
            app: "6100".into(),
            app_generation: "2".into(),
            session: "6209".into(),
            session_generation: "3".into(),
            subject: "8".into(),
            ticket: "6408".into(),
            parent_task: "6000".into(),
            parent_generation: "5".into(),
            purse_task: "6500".into(),
            purse_generation: "4".into(),
            signed_api_path: "/repo.git/".into(),
            host_unit: "spk-host@example.service".into(),
            host_invocation: "0123456789abcdef0123456789abcdef".into(),
        };
        let digest = binding.fingerprint().unwrap();
        assert_eq!(digest.len(), 64);
        let reply = HostReply::Binding {
            protocol: PROTOCOL.into(),
            binding: Box::new(binding.clone()),
            binding_sha256: digest.clone(),
        };
        assert_eq!(
            verify_binding(reply, &route).unwrap(),
            (digest.clone(), binding.host_invocation.clone())
        );
        assert_ne!(binding.parent_task, binding.purse_task);
        let wrong_prefix = HostReply::Binding {
            protocol: PROTOCOL.into(),
            binding: Box::new(FixedBinding {
                signed_api_path: "/other/".into(),
                ..binding.clone()
            }),
            binding_sha256: digest.clone(),
        };
        assert!(verify_binding(wrong_prefix, &route).is_err());
        let conflated = FixedBinding {
            purse_task: binding.parent_task.clone(),
            ..binding.clone()
        };
        assert!(conflated.fingerprint().is_err());
        let reply = parse_host_reply(json!({"type":"inspection","protocol":PROTOCOL,
            "operation_id":"7","binding_sha256":digest,"state":"delivery-requested"}))
        .unwrap();
        verify_operation_reply(&reply, 7, &binding.fingerprint().unwrap()).unwrap();
        assert!(verify_operation_reply(&reply, 8, &binding.fingerprint().unwrap()).is_err());
        let wrong = HostReply::Binding {
            protocol: PROTOCOL.into(),
            binding: Box::new(FixedBinding {
                session_generation: "4".into(),
                ..binding
            }),
            binding_sha256: digest,
        };
        assert!(verify_binding(wrong, &route).is_err());
    }

    #[test]
    fn cancelled_forward_gate_prevents_first_request_byte() {
        let (mut sender, mut receiver) = UnixStream::pair().unwrap();
        receiver.set_nonblocking(true).unwrap();
        let gate = ForwardSendGate::new();
        let cancelled = AtomicBool::new(false);
        gate.cancel();
        assert!(matches!(
            first_write(
                &mut sender,
                b"request",
                &gate,
                &cancelled,
                Instant::now() + Duration::from_secs(1)
            ),
            Err(TransportError::BeforeSend(_))
        ));
        let mut one = [0_u8; 1];
        assert_eq!(
            receiver.read(&mut one).unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        gate.reset().unwrap();
        cancelled.store(true, Ordering::SeqCst);
        assert!(matches!(
            first_write(
                &mut sender,
                b"request",
                &gate,
                &cancelled,
                Instant::now() + Duration::from_secs(1)
            ),
            Err(TransportError::BeforeSend(_))
        ));
        assert_eq!(
            receiver.read(&mut one).unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
    }

    #[test]
    fn duplicate_reply_fields_remain_uncertain_instead_of_value_collapsing() {
        let path = socket_path();
        let listener = UnixListener::bind(&path).unwrap();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut size = [0_u8; 4];
            stream.read_exact(&mut size).unwrap();
            let mut request = vec![0_u8; u32::from_be_bytes(size) as usize];
            stream.read_exact(&mut request).unwrap();
            let reply = br#"{"type":"refused","protocol":"mini-spk-agent-api-v1","operation_id":"7","operation_id":"8","binding_sha256":"0000000000000000000000000000000000000000000000000000000000000000","code":"disabled"}"#;
            stream
                .write_all(&(reply.len() as u32).to_be_bytes())
                .unwrap();
            stream.write_all(reply).unwrap();
        });
        assert!(matches!(
            exchange_once(
                &path,
                unsafe { libc::geteuid() },
                &inspect_request(7),
                Instant::now() + Duration::from_secs(2)
            ),
            Err(TransportError::Uncertain(_))
        ));
        server.join().unwrap();
        remove_socket(&path);
    }

    #[test]
    fn hard_eof_before_dispatch_first_byte_leaves_no_host_request() {
        let path = socket_path();
        let listener = UnixListener::bind(&path).unwrap();
        let gate = Arc::new(ForwardSendGate::new());
        let cancelled = Arc::new(AtomicBool::new(false));
        let barrier = gate.stopped.lock().unwrap();
        let pending = start_dispatch_once(
            &path,
            unsafe { libc::geteuid() },
            dispatch_request(9, &parse_input(&request(), &["workroom".into()]).unwrap()),
            Instant::now() + Duration::from_secs(2),
            gate.clone(),
            cancelled.clone(),
        )
        .unwrap();
        // The worker may connect, but the controller's hard interrupt sets
        // cancellation before it can pass the first-byte gate.
        cancelled.store(true, Ordering::SeqCst);
        drop(barrier);
        gate.cancel();
        let outcome = loop {
            if let Some(outcome) = pending.poll() {
                break outcome;
            }
            thread::sleep(Duration::from_millis(2));
        };
        assert!(matches!(outcome, Err(TransportError::BeforeSend(_))));
        listener.set_nonblocking(true).unwrap();
        match listener.accept() {
            Ok((mut stream, _)) => {
                let mut first = [0_u8; 1];
                assert_eq!(stream.read(&mut first).unwrap(), 0);
            }
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {}
            Err(error) => panic!("host accept: {error}"),
        }
        drop(listener);
        remove_socket(&path);
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn nonaccepting_listener_backlog_cannot_block_connect_past_deadline() {
        let path = socket_path();
        let listener = UnixListener::bind(&path).unwrap();
        assert_eq!(unsafe { libc::listen(listener.as_raw_fd(), 0) }, 0);
        let mut occupied = Vec::new();
        let mut saturated = false;
        for _ in 0..64 {
            let start = Instant::now();
            match connect_nonblocking(&path, start + Duration::from_secs(2), None) {
                Ok(stream) => occupied.push(stream),
                Err(TransportError::BeforeSend(_)) => {
                    saturated = true;
                    assert!(start.elapsed() < Duration::from_millis(300));
                    break;
                }
                Err(TransportError::Uncertain(_)) => panic!("connect has no sent bytes"),
            }
        }
        assert!(
            saturated,
            "fixture did not fill the nonaccepting Unix backlog"
        );
        let cancelled = AtomicBool::new(true);
        let start = Instant::now();
        assert!(matches!(
            connect_nonblocking(&path, start + Duration::from_secs(1), Some(&cancelled)),
            Err(TransportError::BeforeSend(_))
        ));
        assert!(start.elapsed() < Duration::from_millis(300));
        drop(occupied);
        drop(listener);
        remove_socket(&path);
    }
}
