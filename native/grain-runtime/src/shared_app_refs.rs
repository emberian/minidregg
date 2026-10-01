//! Operator-pinned names for applications born by another controller.
//!
//! A reference is a discovery hint and an exact historical evidence pointer.
//! It is never inserted into `born_resources`, never supplies an owner grant,
//! and cannot authorize session birth or dispatch. Resolution replays the
//! retained native receipts by lookup and reads the current resources with
//! this controller's separately delegated observe capabilities. The Lean
//! author/receiver must still decide every proposed transition.

use crate::resource_tools::AllowedResourceRead;
use crate::{decimal, Config, Result, ToolTask};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

const MAX_REFERENCES: usize = 64;
const MAX_READ_BYTES: usize = 256 * 1024;
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
    /// Only the exact original signed call is staged in this controller's
    /// private state. Native op3 replays its historical receipt.
    pub call: PathBuf,
    pub call_sha256: String,
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub world_root: String,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct ShareIssuePin {
    /// The carrier determines which distinct native historical lookup may
    /// interpret these exact bytes. No default maps event 22 to event 15.
    pub kind: ShareIssueKind,
    /// Only the source-authored exact ingress is staged here. Native op29 or
    /// op55 replays its own event/nullifier; no issuer attempt is imported.
    pub ingress: PathBuf,
    pub ingress_sha256: String,
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub world_root: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub(super) enum ShareIssueKind {
    BareEvent15,
    GrainBackedEvent22,
}

impl ShareIssueKind {
    /// Public historical receipt routes only. Issuer prepare/submit commands
    /// are deliberately absent from this recipient selection.
    pub(super) fn recipient_lookup_command(self) -> &'static str {
        match self {
            Self::BareEvent15 => "share-issue-receipt-lookup",
            Self::GrainBackedEvent22 => "grain-share-issue-receipt-lookup",
        }
    }
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
    if !pin.call.is_absolute() || !sha256_hex(&pin.call_sha256) {
        return Err("shared application receipt needs an absolute call and SHA-256".into());
    }
    for (value, label) in [
        (&pin.transaction_id, "transactionId"),
        (&pin.event_id, "eventId"),
        (&pin.accepted_count, "acceptedCount"),
        (&pin.world_root, "worldRoot"),
    ] {
        decimal(value, label)?;
    }
    if pin.accepted_count == "0" {
        return Err("shared application receipt has no accepted transition".into());
    }
    Ok(())
}

fn validate_issue_pin(pin: &ShareIssuePin) -> Result<()> {
    if !pin.ingress.is_absolute() || !sha256_hex(&pin.ingress_sha256) {
        return Err("shared app issue needs an absolute ingress and SHA-256".into());
    }
    for (value, label) in [
        (&pin.transaction_id, "transactionId"),
        (&pin.event_id, "eventId"),
        (&pin.accepted_count, "acceptedCount"),
        (&pin.world_root, "worldRoot"),
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

/// The runtime owns process lifetime and cancellation for every operation.
/// A callback must use a supervised native client/Host route, retain the exact
/// input and binary reply, and return only the Host-inspected JSON. In
/// particular, `BirthLookup` is native op3 over the exact signed call and
/// `IssueLookup` selects op29 or op55 by an explicit pinned carrier kind over
/// exact ingress. Neither may resubmit a transition.
pub(super) enum NativeOperation {
    BirthLookup {
        call: PathBuf,
    },
    IssueLookup {
        kind: ShareIssueKind,
        ingress: PathBuf,
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
    let call = fs::canonicalize(&pin.call)
        .map_err(|error| format!("private shared application call: {error}"))?;
    if !call.starts_with(root.join("shared-app-refs")) || !call.is_file() {
        return Err("shared application call must be staged in private stateDir".into());
    }
    if hash_bounded_file(&call, MAX_CALL_BYTES)? != pin.call_sha256 {
        return Err("shared application exact call digest changed".into());
    }
    Ok(call)
}

fn exact_issue_input(config: &Config, pin: &ShareIssuePin) -> Result<PathBuf> {
    validate_issue_pin(pin)?;
    let root = fs::canonicalize(&config.state_dir)
        .map_err(|error| format!("private shared application root: {error}"))?;
    let ingress = fs::canonicalize(&pin.ingress)
        .map_err(|error| format!("private shared app issue ingress: {error}"))?;
    if !ingress.starts_with(root.join("shared-app-refs"))
        || !ingress.is_file()
        || hash_bounded_file(&ingress, MAX_ISSUE_BYTES)? != pin.ingress_sha256
    {
        return Err("shared app issue ingress differs from private exact pin".into());
    }
    Ok(ingress)
}

fn receipt_matches(
    result: &Value,
    transaction_id: &str,
    event_id: &str,
    accepted_count: &str,
    world_root: &str,
) -> Result<()> {
    if result.get("type").and_then(Value::as_str) != Some("confirmed")
        || result.get("confirmation").and_then(Value::as_str) != Some("replayed")
    {
        return Err("shared application call has no historical accepted receipt".into());
    }
    for (field, expected) in [
        ("transactionId", transaction_id),
        ("eventId", event_id),
        ("acceptedCount", accepted_count),
        ("worldRoot", world_root),
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
        || !result.pointer("/view/cell").is_some_and(Value::is_object)
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
    let birth_call = exact_birth_input(config, &reference.birth)?;
    let issue_ingress = exact_issue_input(config, &reference.issue)?;
    let birth_receipt = run(NativeOperation::BirthLookup {
        call: birth_call.clone(),
    })?;
    receipt_matches(
        &birth_receipt,
        &reference.birth.transaction_id,
        &reference.birth.event_id,
        &reference.birth.accepted_count,
        &reference.birth.world_root,
    )?;
    if hash_bounded_file(&birth_call, MAX_CALL_BYTES)? != reference.birth.call_sha256 {
        return Err("shared application exact birth call changed during lookup".into());
    }
    let issue_receipt = run(NativeOperation::IssueLookup {
        kind: reference.issue.kind,
        ingress: issue_ingress.clone(),
    })?;
    receipt_matches(
        &issue_receipt,
        &reference.issue.transaction_id,
        &reference.issue.event_id,
        &reference.issue.accepted_count,
        &reference.issue.world_root,
    )?;
    if hash_bounded_file(&issue_ingress, MAX_ISSUE_BYTES)? != reference.issue.ingress_sha256 {
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
    // resource presentation does not carry one shared world root; source
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
        &reference.birth.world_root,
    )?;
    receipt_matches(
        &selected.issue_receipt,
        &reference.issue.transaction_id,
        &reference.issue.event_id,
        &reference.issue.accepted_count,
        &reference.issue.world_root,
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

    fn pin(call: &str, digest: &str) -> ExactReceiptPin {
        ExactReceiptPin {
            call: PathBuf::from(call),
            call_sha256: digest.into(),
            transaction_id: "1".into(),
            event_id: "2".into(),
            accepted_count: "3".into(),
            world_root: "4".into(),
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
            birth: pin("/private/birth-call.bin", &"a".repeat(64)),
            issue: ShareIssuePin {
                kind: ShareIssueKind::BareEvent15,
                ingress: PathBuf::from("/private/issue-ingress.bin"),
                ingress_sha256: "b".repeat(64),
                transaction_id: "5".into(),
                event_id: "6".into(),
                accepted_count: "7".into(),
                world_root: "8".into(),
            },
        }
    }

    fn tool() -> ToolTask {
        ToolTask {
            room: None,
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
            resource_workspace: None,
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
            allowed_application_api_routes: vec![],
            allowed_application_lifetime_routes: vec![],
            agent_api_host_sha256: None,
            lifetime_api_host_sha256: None,
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
    fn issue_carrier_kind_is_required_and_cannot_fall_back_to_event15() {
        let mut encoded = serde_json::to_value(reference().issue).unwrap();
        assert_eq!(encoded["kind"], json!("bareEvent15"));
        encoded.as_object_mut().unwrap().remove("kind");
        assert!(serde_json::from_value::<ShareIssuePin>(encoded.clone()).is_err());
        encoded["kind"] = json!("unknownEvent");
        assert!(serde_json::from_value::<ShareIssuePin>(encoded.clone()).is_err());
        encoded["kind"] = json!("grainBackedEvent22");
        let grain: ShareIssuePin = serde_json::from_value(encoded).unwrap();
        assert_eq!(grain.kind, ShareIssueKind::GrainBackedEvent22);
        assert_eq!(
            ShareIssueKind::BareEvent15.recipient_lookup_command(),
            "share-issue-receipt-lookup"
        );
        assert_eq!(
            grain.kind.recipient_lookup_command(),
            "grain-share-issue-receipt-lookup"
        );
        for kind in [ShareIssueKind::BareEvent15, grain.kind] {
            let command = kind.recipient_lookup_command();
            assert!(command.ends_with("-receipt-lookup"));
            assert!(!command.contains("submit"));
        }
    }

    #[test]
    fn only_bounded_unique_names_are_discovered() {
        let reference = reference();
        assert_eq!(
            discovery_names(std::slice::from_ref(&reference)),
            vec!["shared-app"]
        );
        assert!(validate_refs(&[reference.clone(), reference], &tool()).is_err());
    }

    #[test]
    fn historical_receipt_requires_every_exact_native_field() {
        let accepted = json!({"type":"confirmed","confirmation":"replayed",
            "transactionId":"1","eventId":"2","acceptedCount":"3",
            "worldRoot":"4"});
        receipt_matches(&accepted, "1", "2", "3", "4").unwrap();
        for field in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
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
        let valid = json!({"target":"100","view":{"type":"resource","cell":{}}});
        read_result(valid.clone(), "100").unwrap();
        assert!(read_result(valid.clone(), "101").is_err());
        let mut without_page = valid;
        without_page["view"]["cell"] = Value::Null;
        assert!(read_result(without_page, "100").is_err());
    }

    #[test]
    fn retained_shared_selection_cannot_swap_names_targets_or_receipts() {
        let reference = reference();
        let confirmed = |tx: &str, event: &str, count: &str, boundary: &str| {
            json!({"type":"confirmed","confirmation":"replayed",
                "transactionId":tx,"eventId":event,
                "acceptedCount":count,"worldRoot":boundary})
        };
        let view = |target: &str| {
            json!({"target":target,
            "view":{"type":"resource","cell":{}}})
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
        swapped.issue_receipt["worldRoot"] = json!("999");
        assert!(validate_selected(&reference, &swapped).is_err());
        let mut swapped = selected;
        swapped.ticket_read["target"] = json!("104");
        assert!(validate_selected(&reference, &swapped).is_err());
    }

    #[test]
    fn issue_lookup_needs_only_recipient_ingress_with_public_deployment() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root =
            std::env::temp_dir().join(format!("mini-shared-issue-{}-{unique}", std::process::id()));
        let staging = root.join("state/shared-app-refs/issue");
        fs::create_dir_all(&staging).unwrap();
        let host = root.join("host");
        let host_config = root.join("host.json");
        fs::write(&host, b"pinned native host").unwrap();
        fs::write(&host_config, b"pinned deployment config").unwrap();
        let ingress = b"canonical issue ingress";
        let ingress_path = staging.join("ingress.bin");
        fs::write(&ingress_path, ingress).unwrap();
        let call = b"exact signed application birth call";
        let call_path = staging.join("call.bin");
        fs::write(&call_path, call).unwrap();
        let config: Config = serde_json::from_value(json!({
            "mini":root.join("mini"),"host":host,"hostConfig":host_config,
            "hostSocket":root.join("current-public.sock"),
            "controlSocket":root.join("control.sock"),"custodyKey":root.join("parent.key"),
            "stateDir":root.join("state"),"cwd":root,"task":"1","subject":"2",
            "capability":"3","queryCapability":"4","commands":[]
        }))
        .unwrap();
        let pin = ShareIssuePin {
            kind: ShareIssueKind::BareEvent15,
            ingress: ingress_path.clone(),
            ingress_sha256: format!("{:x}", Sha256::digest(ingress)),
            transaction_id: "1".into(),
            event_id: "2".into(),
            accepted_count: "3".into(),
            world_root: "4".into(),
        };
        assert_eq!(
            exact_issue_input(&config, &pin).unwrap(),
            fs::canonicalize(&ingress_path).unwrap()
        );
        let birth = ExactReceiptPin {
            call: call_path.clone(),
            call_sha256: format!("{:x}", Sha256::digest(call)),
            transaction_id: "5".into(),
            event_id: "6".into(),
            accepted_count: "7".into(),
            world_root: "8".into(),
        };
        assert_eq!(
            exact_birth_input(&config, &birth).unwrap(),
            fs::canonicalize(&call_path).unwrap()
        );
        let outside = root.join("owner-private-call.bin");
        fs::write(&outside, call).unwrap();
        let mut other_controller = birth;
        other_controller.call = outside;
        assert!(exact_birth_input(&config, &other_controller).is_err());
        let mut changed_issue = pin;
        changed_issue.ingress_sha256 = "0".repeat(64);
        assert!(exact_issue_input(&config, &changed_issue).is_err());
        assert!(!staging.join("pin.json").exists());
        assert!(!staging.join("attempt.json").exists());
        fs::remove_dir_all(root).unwrap();
    }
}
