//! Operator-pinned names for applications born by another controller.
//!
//! A reference is a discovery hint and an exact historical evidence pointer.
//! It is never inserted into `born_resources`, never supplies an owner grant,
//! and cannot authorize session birth or dispatch. Resolution replays the
//! retained native receipts by lookup and reads the current resources with
//! this controller's separately delegated observe capabilities. The Lean
//! author/receiver must still decide every proposed transition.

use crate::resource_tools::AllowedResourceRead;
use crate::{bounded_regular_file, decimal, Config, Result, ToolTask};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

const MAX_REFERENCES: usize = 64;
const MAX_READ_BYTES: usize = 256 * 1024;
const MAX_HOST_IMAGE_BYTES: u64 = 512 * 1024 * 1024;
const MAX_CALL_BYTES: u64 = 4 * 1024 * 1024;
const MAX_ISSUE_BYTES: u64 = 12_102_759;

fn hash_bounded_file(path: &Path, maximum: u64) -> Result<String> {
    let before = fs::symlink_metadata(path)
        .map_err(|error| format!("shared app digest input {}: {error}", path.display()))?;
    if !before.file_type().is_file() || before.len() == 0 || before.len() > maximum {
        return Err("shared app digest input has wrong type or length".into());
    }
    let mut file = File::open(path)
        .map_err(|error| format!("shared app digest open {}: {error}", path.display()))?;
    let opened = file
        .metadata()
        .map_err(|error| format!("shared app digest metadata: {error}"))?;
    if !opened.is_file()
        || opened.len() != before.len()
        || opened.dev() != before.dev()
        || opened.ino() != before.ino()
    {
        return Err("shared app digest input changed before read".into());
    }
    let mut hash = Sha256::new();
    let mut total = 0u64;
    let mut buffer = [0u8; 65_536];
    loop {
        let count = file
            .read(&mut buffer)
            .map_err(|error| format!("shared app digest read: {error}"))?;
        if count == 0 {
            break;
        }
        total = total
            .checked_add(count as u64)
            .ok_or("shared app digest length overflow")?;
        if total > maximum {
            return Err("shared app digest input exceeded bound".into());
        }
        hash.update(&buffer[..count]);
    }
    if total != before.len() {
        return Err("shared app digest input changed during read".into());
    }
    Ok(hash
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct ExactReceiptPin {
    /// A private copy of the original native client attempt, including its
    /// exact signed call. `mini retry --mode lookup` never resubmits it.
    pub attempt: PathBuf,
    pub call_sha256: String,
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub image_boundary: String,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct ShareIssuePin {
    /// Private copy of the native client's prepared and submitted issue
    /// attempt. Its op29 lookup replays the source event and nullifier at the
    /// original accepted prefix; `ingressSha256` pins `ingress.bin` inside it.
    pub attempt: PathBuf,
    pub ingress_sha256: String,
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub image_boundary: String,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct SharedApplicationRef {
    pub name: String,
    pub application_family: String,
    pub app_target: String,
    pub manifest_target: String,
    pub snapshot_target: String,
    pub ticket_target: String,
    /// These three observe grants belong to this controller's tool subject.
    /// They are never copied from the app creator's owner bundle.
    pub app_observe_capability: String,
    pub manifest_observe_capability: String,
    pub snapshot_observe_capability: String,
    pub ticket_observe_capability: String,
    pub birth: ExactReceiptPin,
    pub issue: ShareIssuePin,
}

/// Discovery provenance only. The six separate native results below do not
/// prove a single-image app/ticket/manifest relationship; the current Lean
/// receiver must source and check that join when admitting use.
#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct CurrentSharedApplication {
    pub name: String,
    pub app_target: String,
    pub birth_receipt: Value,
    pub issue_receipt: Value,
    pub app_read: Value,
    pub manifest_read: Value,
    pub snapshot_read: Value,
    pub ticket_read: Value,
}

fn valid_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= 64
        && name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
}

fn sha256_hex(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn validate_pin(pin: &ExactReceiptPin) -> Result<()> {
    if !pin.attempt.is_absolute() || !sha256_hex(&pin.call_sha256) {
        return Err("shared application receipt needs an absolute attempt and SHA-256".into());
    }
    for (value, label) in [
        (&pin.transaction_id, "transactionId"),
        (&pin.event_id, "eventId"),
        (&pin.accepted_count, "acceptedCount"),
        (&pin.image_boundary, "imageBoundary"),
    ] {
        decimal(value, label)?;
    }
    if pin.accepted_count == "0" {
        return Err("shared application receipt has no accepted transition".into());
    }
    Ok(())
}

fn validate_issue_pin(pin: &ShareIssuePin) -> Result<()> {
    if !pin.attempt.is_absolute() || !sha256_hex(&pin.ingress_sha256) {
        return Err("shared app issue needs an absolute retained attempt and SHA-256".into());
    }
    for (value, label) in [
        (&pin.transaction_id, "transactionId"),
        (&pin.event_id, "eventId"),
        (&pin.accepted_count, "acceptedCount"),
        (&pin.image_boundary, "imageBoundary"),
    ] {
        decimal(value, label)?;
    }
    if pin.accepted_count == "0" {
        return Err("shared app issue has no accepted transition".into());
    }
    Ok(())
}

pub(super) fn validate_refs(refs: &[SharedApplicationRef], tool: &ToolTask) -> Result<()> {
    if refs.len() > MAX_REFERENCES {
        return Err("shared application reference catalog exceeds 64 names".into());
    }
    for (index, reference) in refs.iter().enumerate() {
        if !valid_name(&reference.name)
            || !reference.name.ends_with("-app")
            || !valid_name(&reference.application_family)
            || !tool
                .allowed_session_families
                .iter()
                .any(|family| family.application_family == reference.application_family)
            || refs[..index]
                .iter()
                .any(|prior| prior.name == reference.name)
        {
            return Err("shared application name or family is not uniquely allowlisted".into());
        }
        for (value, label) in [
            (&reference.app_target, "shared app target"),
            (&reference.manifest_target, "shared manifest target"),
            (&reference.snapshot_target, "shared snapshot target"),
            (&reference.ticket_target, "shared ticket target"),
            (
                &reference.app_observe_capability,
                "shared app observe capability",
            ),
            (
                &reference.manifest_observe_capability,
                "shared manifest observe capability",
            ),
            (
                &reference.snapshot_observe_capability,
                "shared snapshot observe capability",
            ),
            (
                &reference.ticket_observe_capability,
                "shared ticket observe capability",
            ),
        ] {
            decimal(value, label)?;
        }
        let targets = [
            &reference.app_target,
            &reference.manifest_target,
            &reference.snapshot_target,
            &reference.ticket_target,
        ];
        let capabilities = [
            &reference.app_observe_capability,
            &reference.manifest_observe_capability,
            &reference.snapshot_observe_capability,
            &reference.ticket_observe_capability,
        ];
        if targets
            .iter()
            .enumerate()
            .any(|(index, value)| targets[..index].contains(value))
            || capabilities
                .iter()
                .enumerate()
                .any(|(index, value)| capabilities[..index].contains(value))
        {
            return Err("shared application targets and observe grants must be distinct".into());
        }
        for capability in capabilities {
            if capability == &tool.capability
                || capability == &tool.parent_capability
                || tool
                    .allowed_publications
                    .iter()
                    .any(|grant| capability == &grant.capability)
            {
                return Err("shared application observe grant overlaps mutation authority".into());
            }
        }
        validate_pin(&reference.birth)?;
        validate_issue_pin(&reference.issue)?;
    }
    Ok(())
}

fn same_pinned_deployment(config: &Config, attempt: &Path) -> Result<()> {
    let manifest = bounded_regular_file(&attempt.join("attempt.json"), 65_536)?;
    let value: Value = serde_json::from_slice(&manifest)
        .map_err(|error| format!("shared application attempt manifest: {error}"))?;
    if value.get("format").and_then(Value::as_str) != Some("minidregg-resource-client-attempt-v1") {
        return Err("shared application attempt manifest format differs".into());
    }
    let host = value
        .get("host")
        .and_then(Value::as_str)
        .ok_or("shared application attempt has no Host pin")?;
    let native_config = value
        .get("config")
        .and_then(Value::as_str)
        .ok_or("shared application attempt has no config pin")?;
    if hash_bounded_file(Path::new(host), MAX_HOST_IMAGE_BYTES)?
        != hash_bounded_file(&config.host, MAX_HOST_IMAGE_BYTES)?
        || bounded_regular_file(Path::new(native_config), 65_536)?
            != bounded_regular_file(&config.host_config, 65_536)?
    {
        return Err("shared application receipt uses a different native deployment".into());
    }
    if let Some(socket) = value.get("socket").and_then(Value::as_str) {
        if config.host_socket.as_deref() != Some(Path::new(socket)) {
            return Err("shared application receipt uses a different native socket".into());
        }
    }
    Ok(())
}

/// The runtime owns process lifetime and cancellation for every operation.
/// A callback must use a supervised native client/Host route, retain the exact
/// input and binary reply, and return only the Host-inspected JSON. In
/// particular, `IssueLookup` is native op29 or its source CLI equivalent, not
/// a generic transaction lookup that would lose the event-15 check.
pub(super) enum NativeOperation {
    BirthLookup {
        attempt: PathBuf,
    },
    IssueLookup {
        attempt: PathBuf,
    },
    SignedRead {
        read: AllowedResourceRead,
        nonce: u64,
    },
}

fn exact_birth_input(config: &Config, pin: &ExactReceiptPin) -> Result<PathBuf> {
    validate_pin(pin)?;
    let root = fs::canonicalize(&config.state_dir)
        .map_err(|error| format!("private shared application root: {error}"))?;
    let attempt = fs::canonicalize(&pin.attempt)
        .map_err(|error| format!("private shared application attempt: {error}"))?;
    if !attempt.starts_with(root.join("shared-app-refs")) {
        return Err("shared application attempt must be staged in private stateDir".into());
    }
    same_pinned_deployment(config, &attempt)?;
    if hash_bounded_file(&attempt.join("call.bin"), MAX_CALL_BYTES)? != pin.call_sha256 {
        return Err("shared application exact call digest changed".into());
    }
    Ok(attempt)
}

fn exact_issue_input(config: &Config, pin: &ShareIssuePin) -> Result<PathBuf> {
    validate_issue_pin(pin)?;
    let root = fs::canonicalize(&config.state_dir)
        .map_err(|error| format!("private shared application root: {error}"))?;
    let attempt = fs::canonicalize(&pin.attempt)
        .map_err(|error| format!("private shared app issue attempt: {error}"))?;
    if !attempt.starts_with(root.join("shared-app-refs"))
        || hash_bounded_file(&attempt.join("ingress.bin"), MAX_ISSUE_BYTES)? != pin.ingress_sha256
    {
        return Err("shared app issue ingress differs from private exact pin".into());
    }
    let metadata = bounded_regular_file(&attempt.join("pin.json"), 65_536)?;
    let value: Value = serde_json::from_slice(&metadata)
        .map_err(|error| format!("shared app issue custody pin: {error}"))?;
    let host = value
        .get("host")
        .and_then(Value::as_str)
        .ok_or("shared app issue has no Host pin")?;
    let native_config = value
        .get("config")
        .and_then(Value::as_str)
        .ok_or("shared app issue has no config pin")?;
    // The original source author used a private operator socket. Historical
    // op29 is also available through this controller's fixed public Host
    // socket, and the native client deliberately supports that override.
    // Keep the original pin intact; it is not this runtime's read socket.
    value
        .get("operatorSocket")
        .and_then(Value::as_str)
        .ok_or("shared app issue has no original operator socket pin")?;
    if hash_bounded_file(Path::new(host), MAX_HOST_IMAGE_BYTES)?
        != hash_bounded_file(&config.host, MAX_HOST_IMAGE_BYTES)?
        || bounded_regular_file(Path::new(native_config), 65_536)?
            != bounded_regular_file(&config.host_config, 65_536)?
    {
        return Err("shared app issue belongs to a different native deployment".into());
    }
    Ok(attempt)
}

fn receipt_matches(
    result: &Value,
    transaction_id: &str,
    event_id: &str,
    accepted_count: &str,
    image_boundary: &str,
) -> Result<()> {
    if result.get("type").and_then(Value::as_str) != Some("confirmed")
        || !matches!(
            result.get("confirmation").and_then(Value::as_str),
            Some("installed" | "replayed")
        )
    {
        return Err("shared application call has no historical accepted receipt".into());
    }
    for (field, expected) in [
        ("transactionId", transaction_id),
        ("eventId", event_id),
        ("acceptedCount", accepted_count),
        ("imageBoundary", image_boundary),
    ] {
        if result.get(field).and_then(Value::as_str) != Some(expected) {
            return Err(format!(
                "shared application {field} differs from exact receipt"
            ));
        }
    }
    Ok(())
}

fn read_selector(name: &str, target: &str, observe_capability: &str) -> AllowedResourceRead {
    AllowedResourceRead {
        name: name.to_owned(),
        kind: "object".into(),
        target: target.to_owned(),
        observe_capability: observe_capability.to_owned(),
        max_result_bytes: MAX_READ_BYTES,
        fn_inbox_summary: false,
    }
}

fn read_result(result: Value, target: &str) -> Result<Value> {
    // The supervised runner must bind this selector to its exact retained
    // signed query. Host's resource presentation carries the decoded page,
    // not a duplicate authority-bearing target selector.
    if result.get("target").and_then(Value::as_str) != Some(target) {
        return Err("shared application signed read selected a different target".into());
    }
    if result.pointer("/view/type").and_then(Value::as_str) != Some("resource")
        || !result.pointer("/view/page").is_some_and(Value::is_object)
    {
        return Err("shared application native read has no complete resource view".into());
    }
    Ok(result)
}

/// Resolve one operator name. Every receipt is a historical fact; each read
/// is a current signed observation. Neither implies current permission to
/// birth a session or dispatch an application request.
pub(super) fn resolve_with(
    config: &Config,
    tool: &ToolTask,
    reference: &SharedApplicationRef,
    nonces: [u64; 4],
    mut run: impl FnMut(NativeOperation) -> Result<Value>,
) -> Result<CurrentSharedApplication> {
    validate_refs(std::slice::from_ref(reference), tool)?;
    if nonces
        .iter()
        .enumerate()
        .any(|(index, nonce)| nonces[..index].contains(nonce))
    {
        return Err("shared application signed reads need distinct durable nonces".into());
    }
    let birth_attempt = exact_birth_input(config, &reference.birth)?;
    let issue_attempt = exact_issue_input(config, &reference.issue)?;
    let birth_receipt = run(NativeOperation::BirthLookup {
        attempt: birth_attempt.clone(),
    })?;
    receipt_matches(
        &birth_receipt,
        &reference.birth.transaction_id,
        &reference.birth.event_id,
        &reference.birth.accepted_count,
        &reference.birth.image_boundary,
    )?;
    if hash_bounded_file(&birth_attempt.join("call.bin"), MAX_CALL_BYTES)?
        != reference.birth.call_sha256
    {
        return Err("shared application exact birth call changed during lookup".into());
    }
    let issue_receipt = run(NativeOperation::IssueLookup {
        attempt: issue_attempt.clone(),
    })?;
    receipt_matches(
        &issue_receipt,
        &reference.issue.transaction_id,
        &reference.issue.event_id,
        &reference.issue.accepted_count,
        &reference.issue.image_boundary,
    )?;
    if hash_bounded_file(&issue_attempt.join("ingress.bin"), MAX_ISSUE_BYTES)?
        != reference.issue.ingress_sha256
    {
        return Err("shared application exact issue ingress changed during lookup".into());
    }
    let selections = [
        (
            format!("{}-current", reference.name),
            &reference.app_target,
            &reference.app_observe_capability,
        ),
        (
            format!("{}-manifest", reference.name),
            &reference.manifest_target,
            &reference.manifest_observe_capability,
        ),
        (
            format!("{}-snapshot", reference.name),
            &reference.snapshot_target,
            &reference.snapshot_observe_capability,
        ),
        (
            format!("{}-ticket", reference.name),
            &reference.ticket_target,
            &reference.ticket_observe_capability,
        ),
    ];
    let mut views = Vec::with_capacity(4);
    for ((name, target, observe), nonce) in selections.into_iter().zip(nonces) {
        let read = read_selector(&name, target, observe);
        let result = run(NativeOperation::SignedRead { read, nonce })?;
        views.push(read_result(result, target)?);
    }
    let [app_read, manifest_read, snapshot_read, ticket_read]: [Value; 4] = views
        .try_into()
        .map_err(|_| "shared application read count differs from full bundle")?;
    // These are four independently signed current observations. The public
    // resource presentation does not carry one shared image boundary; source
    // admission must re-read and join them at its own loaded image.
    Ok(CurrentSharedApplication {
        name: reference.name.clone(),
        app_target: reference.app_target.clone(),
        birth_receipt,
        issue_receipt,
        app_read,
        manifest_read,
        snapshot_read,
        ticket_read,
    })
}

pub(super) fn discovery_names(refs: &[SharedApplicationRef]) -> Vec<String> {
    refs.iter()
        .map(|reference| reference.name.clone())
        .collect()
}

pub(super) fn validate_selected(
    reference: &SharedApplicationRef,
    selected: &CurrentSharedApplication,
) -> Result<()> {
    if selected.name != reference.name || selected.app_target != reference.app_target {
        return Err("retained shared application selector differs from operator reference".into());
    }
    receipt_matches(
        &selected.birth_receipt,
        &reference.birth.transaction_id,
        &reference.birth.event_id,
        &reference.birth.accepted_count,
        &reference.birth.image_boundary,
    )?;
    receipt_matches(
        &selected.issue_receipt,
        &reference.issue.transaction_id,
        &reference.issue.event_id,
        &reference.issue.accepted_count,
        &reference.issue.image_boundary,
    )?;
    for (view, target) in [
        (&selected.app_read, &reference.app_target),
        (&selected.manifest_read, &reference.manifest_target),
        (&selected.snapshot_read, &reference.snapshot_target),
        (&selected.ticket_read, &reference.ticket_target),
    ] {
        read_result(view.clone(), target)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::application_tools::{BirthProfile, SessionFamily, SessionNamespace};
    use serde_json::json;

    fn pin(attempt: &str, call: &str) -> ExactReceiptPin {
        ExactReceiptPin {
            attempt: PathBuf::from(attempt),
            call_sha256: call.into(),
            transaction_id: "1".into(),
            event_id: "2".into(),
            accepted_count: "3".into(),
            image_boundary: "4".into(),
        }
    }

    fn reference() -> SharedApplicationRef {
        SharedApplicationRef {
            name: "shared-app".into(),
            application_family: "office".into(),
            app_target: "100".into(),
            manifest_target: "101".into(),
            snapshot_target: "102".into(),
            ticket_target: "103".into(),
            app_observe_capability: "200".into(),
            manifest_observe_capability: "201".into(),
            snapshot_observe_capability: "202".into(),
            ticket_observe_capability: "203".into(),
            birth: pin("/private/birth", &"a".repeat(64)),
            issue: ShareIssuePin {
                attempt: PathBuf::from("/private/issue"),
                ingress_sha256: "b".repeat(64),
                transaction_id: "5".into(),
                event_id: "6".into(),
                accepted_count: "7".into(),
                image_boundary: "8".into(),
            },
        }
    }

    fn tool() -> ToolTask {
        ToolTask {
            task: "10".into(),
            subject: "11".into(),
            capability: "12".into(),
            query_capability: "13".into(),
            custody_key: "/private/tool.key".into(),
            parent_capability: "14".into(),
            parent_observe_capability: "15".into(),
            reserve: "10".into(),
            charge: "1".into(),
            allowed_publications: vec![],
            allowed_reads: vec![],
            allowed_birth_families: vec![],
            allowed_application_families: vec![],
            allowed_session_families: vec![SessionFamily {
                name: "office-web".into(),
                application_family: "office".into(),
                kind: "web".into(),
                profile: BirthProfile {
                    genesis: json!({}),
                    template: json!({}),
                    factory_target: "20".into(),
                    factory_observe_capability: "21".into(),
                    payer_account: "22".into(),
                    payer_capability: "23".into(),
                    payer_observe_capability: "24".into(),
                    tariff_base: "1".into(),
                    tariff_per_birth: "0".into(),
                },
                namespace: SessionNamespace {
                    session: "300".into(),
                    descriptor: "301".into(),
                    session_owner_capability: "302".into(),
                    session_control_capability: "303".into(),
                    descriptor_owner_capability: "304".into(),
                    descriptor_control_capability: "305".into(),
                },
                max_births: 1,
                max_result_bytes: 1024,
            }],
            registered_shared_applications: vec![],
            current_birth_host_sha256: None,
        }
    }

    #[test]
    fn references_are_not_local_birth_records_or_owner_grants() {
        let registered = reference();
        validate_refs(&[registered], &tool()).unwrap();
        // The selected read grant is distinct from the tool's mutation and
        // parent authority, and no BornResource or owner cap is produced.
        let mut invalid = reference();
        invalid.app_observe_capability = tool().capability;
        assert!(validate_refs(&[invalid], &tool()).is_err());
    }

    #[test]
    fn tampered_receipt_or_cross_controller_grant_is_refused() {
        let mut invalid = reference();
        invalid.birth.call_sha256 = "A".repeat(64);
        assert!(validate_refs(&[invalid], &tool()).is_err());
        let mut invalid = reference();
        invalid.birth.accepted_count = "0".into();
        assert!(validate_refs(&[invalid], &tool()).is_err());
        let mut invalid = reference();
        invalid.issue.ingress_sha256 = "B".repeat(64);
        assert!(validate_refs(&[invalid], &tool()).is_err());
        let mut invalid = reference();
        invalid.ticket_observe_capability = invalid.app_observe_capability.clone();
        assert!(validate_refs(&[invalid], &tool()).is_err());
        let mut invalid = reference();
        invalid.application_family = "other".into();
        assert!(validate_refs(&[invalid], &tool()).is_err());
    }

    #[test]
    fn only_bounded_unique_names_are_discovered() {
        let reference = reference();
        assert_eq!(discovery_names(&[reference.clone()]), vec!["shared-app"]);
        assert!(validate_refs(&[reference.clone(), reference], &tool()).is_err());
    }

    #[test]
    fn historical_receipt_requires_every_exact_native_field() {
        let accepted = json!({"type":"confirmed","confirmation":"replayed",
            "transactionId":"1","eventId":"2","acceptedCount":"3",
            "imageBoundary":"4"});
        receipt_matches(&accepted, "1", "2", "3", "4").unwrap();
        for field in ["transactionId", "eventId", "acceptedCount", "imageBoundary"] {
            let mut changed = accepted.clone();
            changed[field] = json!("999");
            assert!(receipt_matches(&changed, "1", "2", "3", "4").is_err());
        }
        let mut refused = accepted;
        refused["type"] = json!("absent");
        assert!(receipt_matches(&refused, "1", "2", "3", "4").is_err());
    }

    #[test]
    fn read_projection_cannot_replace_signed_target_or_complete_page() {
        let valid = json!({"target":"100","view":{"type":"resource","page":{}}});
        read_result(valid.clone(), "100").unwrap();
        assert!(read_result(valid.clone(), "101").is_err());
        let mut without_page = valid;
        without_page["view"]["page"] = Value::Null;
        assert!(read_result(without_page, "100").is_err());
    }

    #[test]
    fn retained_shared_selection_cannot_swap_names_targets_or_receipts() {
        let reference = reference();
        let confirmed = |tx: &str, event: &str, count: &str, boundary: &str| {
            json!({"type":"confirmed","confirmation":"replayed",
                "transactionId":tx,"eventId":event,
                "acceptedCount":count,"imageBoundary":boundary})
        };
        let view = |target: &str| {
            json!({"target":target,
            "view":{"type":"resource","page":{}}})
        };
        let selected = CurrentSharedApplication {
            name: reference.name.clone(),
            app_target: reference.app_target.clone(),
            birth_receipt: confirmed("1", "2", "3", "4"),
            issue_receipt: confirmed("5", "6", "7", "8"),
            app_read: view("100"),
            manifest_read: view("101"),
            snapshot_read: view("102"),
            ticket_read: view("103"),
        };
        validate_selected(&reference, &selected).unwrap();
        let mut swapped = selected.clone();
        swapped.name = "other-app".into();
        assert!(validate_selected(&reference, &swapped).is_err());
        let mut swapped = selected.clone();
        swapped.issue_receipt["imageBoundary"] = json!("999");
        assert!(validate_selected(&reference, &swapped).is_err());
        let mut swapped = selected;
        swapped.ticket_read["target"] = json!("104");
        assert!(validate_selected(&reference, &swapped).is_err());
    }

    #[test]
    fn issue_lookup_can_use_current_public_socket_distinct_from_original_operator_socket() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root =
            std::env::temp_dir().join(format!("mini-shared-issue-{}-{unique}", std::process::id()));
        let attempt = root.join("state/shared-app-refs/issue");
        fs::create_dir_all(&attempt).unwrap();
        let host = root.join("host");
        let host_config = root.join("host.json");
        fs::write(&host, b"pinned native host").unwrap();
        fs::write(&host_config, b"pinned deployment config").unwrap();
        let ingress = b"canonical issue ingress";
        fs::write(attempt.join("ingress.bin"), ingress).unwrap();
        fs::write(
            attempt.join("pin.json"),
            serde_json::to_vec(&json!({
                "host":host,"config":host_config,
                "operatorSocket":root.join("old-operator.sock")
            }))
            .unwrap(),
        )
        .unwrap();
        let config: Config = serde_json::from_value(json!({
            "mini":root.join("mini"),"host":host,"hostConfig":host_config,
            "hostSocket":root.join("current-public.sock"),
            "controlSocket":root.join("control.sock"),"custodyKey":root.join("parent.key"),
            "stateDir":root.join("state"),"cwd":root,"task":"1","subject":"2",
            "capability":"3","queryCapability":"4","commands":[]
        }))
        .unwrap();
        let pin = ShareIssuePin {
            attempt: attempt.clone(),
            ingress_sha256: format!("{:x}", Sha256::digest(ingress)),
            transaction_id: "1".into(),
            event_id: "2".into(),
            accepted_count: "3".into(),
            image_boundary: "4".into(),
        };
        assert_eq!(
            exact_issue_input(&config, &pin).unwrap(),
            fs::canonicalize(&attempt).unwrap()
        );
        fs::remove_dir_all(root).unwrap();
    }
}
