//! Versioned lifetime agent route comparisons. These are transport custody
//! checks, not Mini admission or an fd3 send permit. In particular, an op77
//! historical lookup can corroborate a receipt but cannot authorize delivery.
#![allow(dead_code)] // No resident v3 caller until op76/80 native routes are qualified.

use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::io;

fn refused(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn hex64(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn hex32(value: &str) -> bool {
    value.len() == 32
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn decode_hex(value: &str) -> io::Result<Vec<u8>> {
    if !value.len().is_multiple_of(2)
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(refused("lifetime source hex noncanonical"));
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16)
                .map_err(|_| refused("lifetime source hex byte"))
        })
        .collect()
}

fn encode_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn field<'a>(value: &'a Value, name: &str) -> io::Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| refused("lifetime source inspection field absent"))
}

fn same(value: &Value, name: &str, expected: &str) -> io::Result<()> {
    if field(value, name)? != expected {
        return Err(refused("lifetime source inspection differs from route"));
    }
    Ok(())
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct ReceiptPin {
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub image_boundary: String,
}

impl ReceiptPin {
    fn validate(&self) -> io::Result<()> {
        if [
            &self.transaction_id,
            &self.event_id,
            &self.accepted_count,
            &self.image_boundary,
        ]
        .into_iter()
        .all(|value| decimal(value))
        {
            Ok(())
        } else {
            Err(refused("lifetime original receipt pin refused"))
        }
    }
}

/// An event27 grant and its event22 provenance. The historical ticket's
/// origin generation remains here even when the parent executes at a newer
/// generation. Its lifetime and ceiling are checked by Mini, not by this type.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct LifetimeLineage {
    pub app_resource: String,
    pub session_resource: String,
    pub participant_subject: String,
    pub ticket_resource: String,
    pub original_parent_task: String,
    pub original_parent_generation: String,
    pub original_issue_index: String,
    pub original_issue_receipt: ReceiptPin,
    pub original_descriptor_sha256: String,
    pub grant_resource: String,
    pub grant_issue_index: String,
    pub grant_digest: String,
    pub grant_initialized_root: String,
    pub grant_issue_receipt: ReceiptPin,
    pub parent_task: String,
    pub purse_task: String,
}

impl LifetimeLineage {
    pub(crate) fn validate(&self) -> io::Result<()> {
        if ![
            &self.app_resource,
            &self.session_resource,
            &self.participant_subject,
            &self.ticket_resource,
            &self.original_parent_task,
            &self.original_parent_generation,
            &self.original_issue_index,
            &self.grant_resource,
            &self.grant_issue_index,
            &self.grant_digest,
            &self.grant_initialized_root,
            &self.parent_task,
            &self.purse_task,
        ]
        .into_iter()
        .all(|value| decimal(value))
            || !hex64(&self.original_descriptor_sha256)
            || self.parent_task != self.original_parent_task
            || self.parent_task == self.purse_task
        {
            return Err(refused("lifetime route lineage refused"));
        }
        self.original_issue_receipt.validate()?;
        self.grant_issue_receipt.validate()
    }
}

/// Claims from this *operation's* transport and signed current observations. They
/// are never promoted to authority without a matching native source plan and
/// a fresh installed committed permit. The purse physical root here is the
/// pre-reserve root; a later committed comparison requires a separately signed
/// post-reserve purse root without changing this operation's binding.
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct CurrentClaims {
    pub app_generation: String,
    pub session_generation: String,
    pub parent_generation: String,
    pub purse_generation: String,
    pub app_root: String,
    pub session_root: String,
    pub app_physical_root: String,
    pub session_physical_root: String,
    pub parent_physical_root: String,
    pub purse_physical_root: String,
}

impl CurrentClaims {
    pub(crate) fn validate(&self) -> io::Result<()> {
        if [
            &self.app_generation,
            &self.session_generation,
            &self.parent_generation,
            &self.purse_generation,
            &self.app_root,
            &self.session_root,
            &self.app_physical_root,
            &self.session_physical_root,
            &self.parent_physical_root,
            &self.purse_physical_root,
        ]
        .into_iter()
        .all(|value| decimal(value))
        {
            Ok(())
        } else {
            Err(refused("lifetime current claim refused"))
        }
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
/// Stable Hello identity for one resident app incarnation. A hard reconnect
/// does not rewrite event22's original origin or turn a prior task generation
/// into a fresh one; the per-dispatch `CurrentClaims` supply that witness.
pub(crate) struct LifetimeBinding {
    pub protocol: String,
    pub lineage: LifetimeLineage,
    pub signed_api_path: String,
    pub host_unit: String,
    pub host_invocation: String,
}

impl LifetimeBinding {
    pub(crate) fn validate(&self) -> io::Result<()> {
        self.lineage.validate()?;
        if self.protocol != "mini-spk-agent-lifetime-binding-v3"
            || !self.signed_api_path.starts_with('/')
            || !self.signed_api_path.ends_with('/')
            || self.signed_api_path.len() > 256
            || self
                .signed_api_path
                .bytes()
                .any(|byte| byte < 0x20 || byte == 0x7f)
            || self.host_unit.is_empty()
            || self.host_unit.len() > 256
            || self
                .host_unit
                .bytes()
                .any(|byte| byte < 0x20 || byte == 0x7f)
            || !hex32(&self.host_invocation)
        {
            return Err(refused("lifetime transport binding refused"));
        }
        Ok(())
    }

    pub(crate) fn fingerprint(&self) -> io::Result<String> {
        self.validate()?;
        let mut digest = Sha256::new();
        digest.update(b"DREGG/SPK-AGENT-LIFETIME-BINDING/v3\0");
        digest.update(serde_json::to_vec(self)?);
        Ok(digest
            .finalize()
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect())
    }
}

/// A journal coordinate for one exact request under one stable Hello. Fresh
/// task generations/roots cannot be substituted into a retained attempt even
/// if the caller reconnects through the same lifetime route.
pub(crate) fn operation_fingerprint(
    binding: &LifetimeBinding,
    current: &CurrentClaims,
    operation_id: &str,
    request_sha256: &str,
) -> io::Result<String> {
    current.validate()?;
    if !decimal(operation_id) || !hex64(request_sha256) {
        return Err(refused("lifetime operation coordinate refused"));
    }
    let mut digest = Sha256::new();
    digest.update(b"DREGG/SPK-AGENT-LIFETIME-OPERATION/v3\0");
    digest.update(binding.fingerprint()?.as_bytes());
    digest.update(serde_json::to_vec(current)?);
    digest.update(operation_id.as_bytes());
    digest.update(request_sha256.as_bytes());
    Ok(encode_hex(&digest.finalize()))
}

/// Compare source-owned op80 inspection with the exact received HTTP and
/// current transport. Op80 projects the full app/session physical roots from
/// its verified image; the ordinary purse reserve signature itself does not
/// commit those roots and cannot authorize delivery without event26.
pub(crate) fn match_reserve_plan(
    binding: &LifetimeBinding,
    current: &CurrentClaims,
    inspected_request: &Value,
    inspected_plan: &Value,
    decoded_http: &Value,
) -> io::Result<()> {
    binding.validate()?;
    current.validate()?;
    if field(inspected_request, "type")? != "application-agent-lifetime-author-request-v3"
        || field(inspected_plan, "type")? != "application-agent-lifetime-reserve-plan-v3"
        || inspected_request.get("http") != Some(decoded_http)
        || inspected_plan.get("http") != Some(decoded_http)
        || inspected_plan.get("fixedSelectors") != inspected_request.get("fixedSelectors")
        || inspected_plan.get("canonicalRequestHex") != inspected_request.get("canonicalRequestHex")
        || inspected_plan.get("canonicalHttpHex") != inspected_request.get("canonicalHttpHex")
    {
        return Err(refused("lifetime reserve request or HTTP changed"));
    }
    let context = inspected_plan
        .get("context")
        .ok_or_else(|| refused("lifetime context absent"))?;
    let lineage = &binding.lineage;
    let fixed = inspected_plan
        .get("fixedSelectors")
        .ok_or_else(|| refused("lifetime fixed selectors absent"))?;
    for (name, expected) in [
        ("issueIndex", &lineage.original_issue_index),
        ("ticketResource", &lineage.ticket_resource),
        ("grantIssueIndex", &lineage.grant_issue_index),
        ("grantResource", &lineage.grant_resource),
        ("parentTask", &lineage.parent_task),
        ("purseTask", &lineage.purse_task),
    ] {
        same(fixed, name, expected)?;
    }
    for (name, expected) in [
        ("appResource", &lineage.app_resource),
        ("sessionResource", &lineage.session_resource),
        ("participantSubject", &lineage.participant_subject),
        ("ticketResource", &lineage.ticket_resource),
        ("grantResource", &lineage.grant_resource),
        ("grantIssueIndex", &lineage.grant_issue_index),
        ("grantDigest", &lineage.grant_digest),
        ("parentTask", &lineage.parent_task),
        ("purseTask", &lineage.purse_task),
        ("appGeneration", &current.app_generation),
        ("sessionGeneration", &current.session_generation),
        ("parentGeneration", &current.parent_generation),
        ("purseGeneration", &current.purse_generation),
    ] {
        same(context, name, expected)?;
    }
    let origin = context
        .get("sessionOrigin")
        .ok_or_else(|| refused("lifetime original origin absent"))?;
    same(origin, "type", "agent")?;
    same(origin, "task", &lineage.original_parent_task)?;
    same(origin, "generation", &lineage.original_parent_generation)?;
    let bindings = inspected_plan
        .get("bindings")
        .ok_or_else(|| refused("lifetime source bindings absent"))?;
    for (name, expected) in [
        ("grantInitializedRoot", &lineage.grant_initialized_root),
        ("grantPhysicalRoot", &lineage.grant_initialized_root),
        ("appPhysicalRoot", &current.app_physical_root),
        ("sessionPhysicalRoot", &current.session_physical_root),
        ("parentPhysicalRoot", &current.parent_physical_root),
        ("pursePhysicalRoot", &current.purse_physical_root),
    ] {
        same(bindings, name, expected)?;
    }
    if bindings.get("originalIssueReceipt")
        != Some(&serde_json::to_value(&lineage.original_issue_receipt)?)
        || bindings.get("grantIssueReceipt")
            != Some(&serde_json::to_value(&lineage.grant_issue_receipt)?)
    {
        return Err(refused("lifetime historical receipt differs from binding"));
    }
    Ok(())
}

/// Retain the exact reserve chronology while independently fencing the
/// changed purse cell after its confirmed reserve. The source plan is still
/// only a signing candidate, never the native committed dispatch permit.
pub(crate) fn match_paid_plan(
    binding: &LifetimeBinding,
    current: &CurrentClaims,
    reserve_plan: &Value,
    paid_plan: &Value,
    reserve_index: &str,
    reserve_receipt: &ReceiptPin,
    signed_post_reserve_purse_physical_root: &str,
) -> io::Result<()> {
    binding.validate()?;
    current.validate()?;
    reserve_receipt.validate()?;
    if !decimal(reserve_index) || !decimal(signed_post_reserve_purse_physical_root) {
        return Err(refused("lifetime paid reserve coordinate noncanonical"));
    }
    if field(reserve_plan, "type")? != "application-agent-lifetime-reserve-plan-v3"
        || field(paid_plan, "type")? != "application-agent-lifetime-paid-plan-v3"
        || paid_plan.get("fixedSelectors") != reserve_plan.get("fixedSelectors")
        || paid_plan.get("context") != reserve_plan.get("context")
        || paid_plan.get("canonicalHttpHex") != reserve_plan.get("canonicalHttpHex")
        || paid_plan.get("http") != reserve_plan.get("http")
        || field(paid_plan, "reserveIndex")? != reserve_index
        || paid_plan.get("reserveReceipt") != Some(&serde_json::to_value(reserve_receipt)?)
    {
        return Err(refused("lifetime paid plan differs from confirmed reserve"));
    }
    let before = reserve_plan
        .get("bindings")
        .ok_or_else(|| refused("lifetime reserve bindings absent"))?;
    for (name, expected) in [
        ("appPhysicalRoot", &current.app_physical_root),
        ("sessionPhysicalRoot", &current.session_physical_root),
        ("parentPhysicalRoot", &current.parent_physical_root),
        ("pursePhysicalRoot", &current.purse_physical_root),
    ] {
        same(before, name, expected)?;
    }
    let after = paid_plan
        .get("bindings")
        .ok_or_else(|| refused("lifetime paid bindings absent"))?;
    for name in [
        "originalIssueReceipt",
        "grantIssueReceipt",
        "grantInitializedRoot",
        "grantPhysicalRoot",
        "appPhysicalRoot",
        "sessionPhysicalRoot",
        "parentPhysicalRoot",
    ] {
        if before.get(name) != after.get(name) {
            return Err(refused(
                "lifetime paid immutable physical/history binding changed",
            ));
        }
    }
    same(
        after,
        "pursePhysicalRoot",
        signed_post_reserve_purse_physical_root,
    )
}

/// A committed-frame *comparison* for an already obtained native op76 result.
/// A caller must still prove that the exact frame came from a fresh installed
/// CAS, and verify current process/lease and signed task state before fd3.
/// The post-reserve purse physical root is intentionally distinct from the
/// binding's pre-reserve root.
pub(crate) struct CommittedMatch<'a> {
    pub binding: &'a LifetimeBinding,
    pub current: &'a CurrentClaims,
    pub inspected: &'a Value,
    pub decoded_http: &'a Value,
    pub canonical_http_hex: &'a str,
    pub expected_receipt: &'a ReceiptPin,
    pub exact_frame: &'a [u8],
    pub signed_post_reserve_purse_physical_root: &'a str,
}

pub(crate) fn match_committed_inspection(input: CommittedMatch<'_>) -> io::Result<()> {
    let CommittedMatch {
        binding,
        current,
        inspected,
        decoded_http,
        canonical_http_hex,
        expected_receipt,
        exact_frame,
        signed_post_reserve_purse_physical_root,
    } = input;
    binding.validate()?;
    current.validate()?;
    expected_receipt.validate()?;
    if !decimal(signed_post_reserve_purse_physical_root) {
        return Err(refused("lifetime post-reserve purse root noncanonical"));
    }
    if field(inspected, "type")? != "application-agent-lifetime-dispatch-committed-inspection-v3" {
        return Err(refused("lifetime committed frame type refused"));
    }
    let lineage = &binding.lineage;
    let issue = inspected
        .get("originalIssue")
        .ok_or_else(|| refused("original issue absent"))?;
    same(issue, "index", &lineage.original_issue_index)?;
    if issue.get("receipt") != Some(&serde_json::to_value(&lineage.original_issue_receipt)?) {
        return Err(refused("original issue receipt changed"));
    }
    let descriptor = field(issue, "descriptorHex")?;
    let descriptor_bytes = decode_hex(descriptor)?;
    let descriptor_sha = Sha256::digest(descriptor_bytes);
    if encode_hex(&descriptor_sha) != lineage.original_descriptor_sha256 {
        return Err(refused("original descriptor changed"));
    }
    let grant = inspected
        .get("grant")
        .ok_or_else(|| refused("grant absent"))?;
    for (name, expected) in [
        ("resource", &lineage.grant_resource),
        ("issueIndex", &lineage.grant_issue_index),
        ("digest", &lineage.grant_digest),
        ("initializedRoot", &lineage.grant_initialized_root),
        ("currentPhysicalRoot", &lineage.grant_initialized_root),
    ] {
        same(grant, name, expected)?;
    }
    if grant.get("issueReceipt") != Some(&serde_json::to_value(&lineage.grant_issue_receipt)?) {
        return Err(refused("grant issue receipt changed"));
    }
    let app = inspected.get("app").ok_or_else(|| refused("app absent"))?;
    same(app, "resource", &lineage.app_resource)?;
    same(app, "generation", &current.app_generation)?;
    let session = inspected
        .get("session")
        .ok_or_else(|| refused("session absent"))?;
    same(session, "resource", &lineage.session_resource)?;
    same(session, "generation", &current.session_generation)?;
    same(session, "subject", &lineage.participant_subject)?;
    let origin = session
        .get("originalOrigin")
        .ok_or_else(|| refused("origin absent"))?;
    same(origin, "type", "agent")?;
    same(origin, "task", &lineage.original_parent_task)?;
    same(origin, "generation", &lineage.original_parent_generation)?;
    let image = inspected
        .get("currentImage")
        .ok_or_else(|| refused("current image absent"))?;
    same(image, "appRoot", &current.app_root)?;
    same(image, "sessionRoot", &current.session_root)?;
    let parent = inspected
        .get("parent")
        .ok_or_else(|| refused("parent absent"))?;
    same(parent, "task", &lineage.parent_task)?;
    same(parent, "generation", &current.parent_generation)?;
    same(parent, "physicalRoot", &current.parent_physical_root)?;
    let purse = inspected
        .get("purse")
        .ok_or_else(|| refused("purse absent"))?;
    same(purse, "task", &lineage.purse_task)?;
    same(purse, "generation", &current.purse_generation)?;
    same(
        purse,
        "physicalRoot",
        signed_post_reserve_purse_physical_root,
    )?;
    let request = inspected
        .get("request")
        .ok_or_else(|| refused("request absent"))?;
    if field(request, "canonicalHex")? != canonical_http_hex
        || decode_hex(canonical_http_hex)?.is_empty()
    {
        return Err(refused("lifetime exact HTTP stream changed"));
    }
    for (name, http_name) in [
        ("operationId", "operationId"),
        ("methodHex", "methodHex"),
        ("pathHex", "pathHex"),
        ("queryHex", "queryHex"),
        ("bodyHex", "bodyHex"),
    ] {
        same(request, name, field(decoded_http, http_name)?)?;
    }
    if field(inspected, "frameByteCount")? != exact_frame.len().to_string()
        || field(inspected, "frameHex")? != encode_hex(exact_frame)
        || inspected.get("dispatchReceipt") != Some(&serde_json::to_value(expected_receipt)?)
    {
        return Err(refused("lifetime committed frame or receipt changed"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn receipt(count: &str) -> ReceiptPin {
        ReceiptPin {
            transaction_id: "11".into(),
            event_id: "12".into(),
            accepted_count: count.into(),
            image_boundary: "13".into(),
        }
    }

    fn binding() -> LifetimeBinding {
        LifetimeBinding {
            protocol: "mini-spk-agent-lifetime-binding-v3".into(),
            lineage: LifetimeLineage {
                app_resource: "800".into(),
                session_resource: "801".into(),
                participant_subject: "8".into(),
                ticket_resource: "802".into(),
                original_parent_task: "700".into(),
                original_parent_generation: "1".into(),
                original_issue_index: "2".into(),
                original_issue_receipt: receipt("3"),
                original_descriptor_sha256: encode_hex(&Sha256::digest(b"descriptor")),
                grant_resource: "803".into(),
                grant_issue_index: "3".into(),
                grant_digest: "123".into(),
                grant_initialized_root: "456".into(),
                grant_issue_receipt: receipt("4"),
                parent_task: "700".into(),
                purse_task: "701".into(),
            },
            signed_api_path: "/api/".into(),
            host_unit: "mini-app.service".into(),
            host_invocation: "ab".repeat(16),
        }
    }

    fn current() -> CurrentClaims {
        CurrentClaims {
            app_generation: "4".into(),
            session_generation: "5".into(),
            parent_generation: "6".into(),
            purse_generation: "7".into(),
            app_root: "100".into(),
            session_root: "101".into(),
            app_physical_root: "200".into(),
            session_physical_root: "201".into(),
            parent_physical_root: "202".into(),
            purse_physical_root: "203".into(),
        }
    }

    fn http() -> Value {
        json!({"operationId":"9","methodHex":"474554","pathHex":"6170692f",
            "queryHex":"","headers":[],"bodyHex":""})
    }

    fn reserve_plan(binding: &LifetimeBinding, current: &CurrentClaims) -> (Value, Value) {
        let lineage = &binding.lineage;
        let source_http = http();
        let fixed = json!({"issueIndex":lineage.original_issue_index,
            "ticketResource":lineage.ticket_resource,
            "grantIssueIndex":lineage.grant_issue_index,
            "grantResource":lineage.grant_resource,
            "parentTask":lineage.parent_task,
            "purseTask":lineage.purse_task});
        let request = json!({"type":"application-agent-lifetime-author-request-v3",
            "canonicalRequestHex":"ab","canonicalHttpHex":"cd",
            "fixedSelectors":fixed,"http":source_http});
        let plan = json!({"type":"application-agent-lifetime-reserve-plan-v3",
            "canonicalRequestHex":"ab","canonicalHttpHex":"cd",
            "fixedSelectors":fixed,"http":source_http,
            "context":{"appResource":lineage.app_resource,
                "sessionResource":lineage.session_resource,
                "participantSubject":lineage.participant_subject,
                "ticketResource":lineage.ticket_resource,
                "grantResource":lineage.grant_resource,
                "grantIssueIndex":lineage.grant_issue_index,
                "grantDigest":lineage.grant_digest,
                "parentTask":lineage.parent_task,
                "purseTask":lineage.purse_task,
                "appGeneration":current.app_generation,
                "sessionGeneration":current.session_generation,
                "parentGeneration":current.parent_generation,
                "purseGeneration":current.purse_generation,
                "sessionOrigin":{"type":"agent",
                    "task":lineage.original_parent_task,
                    "generation":lineage.original_parent_generation}},
            "bindings":{"originalIssueReceipt":lineage.original_issue_receipt,
                "grantIssueReceipt":lineage.grant_issue_receipt,
                "grantInitializedRoot":lineage.grant_initialized_root,
                "grantPhysicalRoot":lineage.grant_initialized_root,
                "appPhysicalRoot":current.app_physical_root,
                "sessionPhysicalRoot":current.session_physical_root,
                "parentPhysicalRoot":current.parent_physical_root,
                "pursePhysicalRoot":current.purse_physical_root}});
        (request, plan)
    }

    #[test]
    fn lineage_fingerprint_keeps_origin_and_current_generation_separate() {
        let binding = binding();
        let first = binding.fingerprint().unwrap();
        let current = current();
        let request_sha = "cd".repeat(32);
        let op = operation_fingerprint(&binding, &current, "9", &request_sha).unwrap();
        let mut next_current = current.clone();
        next_current.parent_generation = "7".into();
        assert_eq!(first, binding.fingerprint().unwrap());
        assert_ne!(
            op,
            operation_fingerprint(&binding, &next_current, "9", &request_sha).unwrap()
        );
        let mut next = binding.clone();
        assert_eq!(next.lineage.original_parent_generation, "1");
        next.lineage.original_issue_receipt.accepted_count = "04".into();
        assert!(next.validate().is_err());
        let mut invalid = binding;
        invalid.host_invocation = "ab".repeat(32);
        assert!(invalid.validate().is_err());
    }

    #[test]
    fn reserve_comparison_rejects_changed_http_and_physical_root() {
        let binding = binding();
        let current = current();
        let (request, mut plan) = reserve_plan(&binding, &current);
        match_reserve_plan(&binding, &current, &request, &plan, &http()).unwrap();
        plan["bindings"]["sessionPhysicalRoot"] = json!("999");
        assert!(match_reserve_plan(&binding, &current, &request, &plan, &http()).is_err());
        let (_, plan) = reserve_plan(&binding, &current);
        let mut changed = http();
        changed["headers"] = json!([{"nameHex":"61","valueHex":"62","generated":false}]);
        assert!(match_reserve_plan(&binding, &current, &request, &plan, &changed).is_err());
    }

    #[test]
    fn paid_comparison_keeps_history_and_checks_new_purse_root() {
        let binding = binding();
        let current = current();
        let (_, reserve) = reserve_plan(&binding, &current);
        let receipt = receipt("5");
        let mut paid = reserve.clone();
        paid["type"] = json!("application-agent-lifetime-paid-plan-v3");
        paid["reserveIndex"] = json!("4");
        paid["reserveReceipt"] = serde_json::to_value(&receipt).unwrap();
        paid["bindings"]["pursePhysicalRoot"] = json!("204");
        match_paid_plan(&binding, &current, &reserve, &paid, "4", &receipt, "204").unwrap();
        let mut changed = paid.clone();
        changed["bindings"]["appPhysicalRoot"] = json!("999");
        assert!(
            match_paid_plan(&binding, &current, &reserve, &changed, "4", &receipt, "204").is_err()
        );
        assert!(
            match_paid_plan(&binding, &current, &reserve, &paid, "4", &receipt, "203").is_err()
        );
    }

    #[test]
    fn committed_comparison_checks_exact_frame_receipt_and_original_descriptor() {
        let binding = binding();
        let lineage = &binding.lineage;
        let current = current();
        let receipt = receipt("5");
        let frame = b"native-frame";
        let mut inspected = json!({
            "type":"application-agent-lifetime-dispatch-committed-inspection-v3",
            "frameByteCount":frame.len().to_string(),"frameHex":encode_hex(frame),
            "dispatchReceipt":receipt,
            "originalIssue":{"index":lineage.original_issue_index,
                "receipt":lineage.original_issue_receipt,
                "descriptorHex":encode_hex(b"descriptor")},
            "grant":{"resource":lineage.grant_resource,
                "issueIndex":lineage.grant_issue_index,
                "digest":lineage.grant_digest,
                "initializedRoot":lineage.grant_initialized_root,
                "currentPhysicalRoot":lineage.grant_initialized_root,
                "issueReceipt":lineage.grant_issue_receipt},
            "app":{"resource":lineage.app_resource,"generation":current.app_generation},
            "session":{"resource":lineage.session_resource,
                "generation":current.session_generation,
                "subject":lineage.participant_subject,
                "originalOrigin":{"type":"agent","task":lineage.original_parent_task,
                    "generation":lineage.original_parent_generation}},
            "currentImage":{"appRoot":current.app_root,"sessionRoot":current.session_root},
            "parent":{"task":lineage.parent_task,
                "generation":current.parent_generation,
                "physicalRoot":current.parent_physical_root},
            "purse":{"task":lineage.purse_task,
                "generation":current.purse_generation,
                "physicalRoot":"204"},
            "request":{"operationId":"9","canonicalHex":"cd",
                "methodHex":"474554","pathHex":"6170692f",
                "queryHex":"","bodyHex":""}
        });
        let received_http = http();
        let check = |inspected: &Value, post_root: &str| {
            match_committed_inspection(CommittedMatch {
                binding: &binding,
                current: &current,
                inspected,
                decoded_http: &received_http,
                canonical_http_hex: "cd",
                expected_receipt: &receipt,
                exact_frame: frame,
                signed_post_reserve_purse_physical_root: post_root,
            })
        };
        check(&inspected, "204").unwrap();
        inspected["dispatchReceipt"]["acceptedCount"] = json!("6");
        assert!(check(&inspected, "204").is_err());
        inspected["dispatchReceipt"]["acceptedCount"] = json!("5");
        inspected["originalIssue"]["descriptorHex"] = json!("00");
        assert!(check(&inspected, "204").is_err());
        inspected["originalIssue"]["descriptorHex"] = json!(encode_hex(b"descriptor"));
        assert!(check(&inspected, "203").is_err());
    }
}
