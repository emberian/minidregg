//! Source-owned v3 launch claim plan, detached assembly, and fresh op26
//! committed callback inspection. Physical INSTALL/START remains gated until
//! the linked source receiver, completion, and volume joins qualify.
#![allow(dead_code)] // Awaiting the physical v3 lifecycle caller.

use crate::dispatch_author::SignerPin;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::hostd::VerifiedBegin;
use crate::lifecycle_v3_native::{
    decimal, framed_payload, hex, lowercase_hex, sign_pinned_slots, text, AcceptedLaunchBegin,
    LaunchBeginAction,
};
use crate::resident_begin_native::allocate_operation_id;
use crate::resident_launch::SourceBoundLaunch;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder};
use std::io;
use std::os::unix::fs::DirBuilderExt;
use std::path::{Path, PathBuf};

const PLAN_TAG: &[u8] = b"DREGG/APPLICATION/LAUNCH-CLAIM-OPERATOR-PLAN/v1";
const INGRESS_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-CLAIM-INGRESS/v3";
const COMMITTED_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-CLAIM-COMMITTED/v3";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn previous_index(count: &str) -> io::Result<String> {
    if !decimal(count) || count == "0" {
        return Err(invalid("v3 claim original BEGIN count refused"));
    }
    let mut bytes = count.as_bytes().to_vec();
    for byte in bytes.iter_mut().rev() {
        if *byte != b'0' {
            *byte -= 1;
            break;
        }
        *byte = b'9';
    }
    let first = bytes
        .iter()
        .position(|byte| *byte != b'0')
        .unwrap_or(bytes.len() - 1);
    String::from_utf8(bytes[first..].to_vec())
        .map_err(|_| invalid("v3 claim original BEGIN index malformed"))
}

pub(crate) fn later_decimal(value: &str, earlier: &str) -> bool {
    decimal(value)
        && decimal(earlier)
        && (value.len() > earlier.len()
            || (value.len() == earlier.len() && value.as_bytes() > earlier.as_bytes()))
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedLaunchClaimSigners {
    protocol: String,
    app: String,
    package_manifest: String,
    management_subject: String,
    signers: Vec<SignerPin>,
}

struct ClaimPlanEvidence<'a> {
    plan: &'a [u8],
    request: &'a [u8],
    begin: &'a AcceptedLaunchBegin,
    launch: &'a SourceBoundLaunch<'a>,
    original_index: &'a str,
    query_nonce: &'a str,
}

impl FixedLaunchClaimSigners {
    pub(crate) fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-resident-claim-management-v1"
            || self.signers.is_empty()
            || self.signers.len() > 64
            || ![&self.app, &self.package_manifest, &self.management_subject]
                .iter()
                .all(|value| decimal(value))
        {
            return Err(invalid("v3 claim fixed management custody refused"));
        }
        let config: Value = serde_json::from_slice(&operator.pinned_config()?)?;
        let manager = config
            .get("residentClaimManagement")
            .ok_or_else(|| invalid("Mini claim management pin absent"))?;
        for (field, expected) in [
            ("app", &self.app),
            ("packageManifest", &self.package_manifest),
            ("managementSubject", &self.management_subject),
        ] {
            let value = manager
                .get(field)
                .ok_or_else(|| invalid("Mini claim management coordinate absent"))?;
            let value = value
                .as_str()
                .map(str::to_owned)
                .or_else(|| value.as_u64().map(|number| number.to_string()))
                .ok_or_else(|| invalid("Mini claim management coordinate malformed"))?;
            if value != *expected {
                return Err(invalid("v3 claim fixed management differs from Mini pin"));
            }
        }
        let key_id = manager
            .get("managementKeyId")
            .and_then(|value| {
                value
                    .as_str()
                    .map(str::to_owned)
                    .or_else(|| value.as_u64().map(|number| number.to_string()))
            })
            .ok_or_else(|| invalid("Mini claim management key absent"))?;
        for signer in &self.signers {
            if signer.key_id != key_id {
                return Err(invalid("v3 claim signer key differs from Mini pin"));
            }
            crate::sandbox::open_protected_directory(
                signer
                    .seed_path
                    .parent()
                    .ok_or_else(|| invalid("v3 claim signer parent absent"))?,
                app_uid,
                false,
            )?;
        }
        Ok(())
    }

    fn checked_plan_slots<'a>(
        &self,
        view: &'a Value,
        evidence: &ClaimPlanEvidence<'_>,
    ) -> io::Result<&'a [Value]> {
        let ClaimPlanEvidence {
            plan,
            request,
            begin,
            launch,
            original_index,
            query_nonce,
        } = evidence;
        let descriptor = launch.descriptor();
        if text(view, "type")? != "application-lifecycle-launch-claim-plan-v1"
            || text(view, "canonicalPlanHex")? != hex(plan)
            || text(view, "canonicalRequestHex")? != hex(request)
            || text(view, "originalBeginHex")? != hex(&begin.ingress)
            || text(view, "descriptorHex")? != hex(&descriptor.canonical)
            || text(view, "descriptorRoot")? != descriptor.root
            || text(view, "volumeIdHex")? != begin.volume_id_hex
            || text(view, "clientOperationId")? != begin.client_operation_id
            || text(view, "authorizationOperationId")? != begin.authorization_operation_id
            || text(view, "originalIndex")? != *original_index
            || text(view, "queryNonce")? != *query_nonce
            || text(view, "app")? != self.app
            || text(view, "managementSubject")? != self.management_subject
            || text(view, "originalBeginTransactionId")? != begin.transaction_id
            || text(view, "originalBeginEventId")? != begin.event_id
            || text(view, "originalBeginAcceptedCount")? != begin.accepted_count
            || text(view, "originalBeginWorldRoot")? != begin.world_root
            || !lowercase_hex(text(view, "originalBeginReceiptHex")?)
            || text(view, "originalBeginReceiptHex")?.is_empty()
            || !lowercase_hex(text(view, "sourceHex")?)
            || text(view, "sourceHex")?.is_empty()
            || !decimal(text(view, "currentAppRoot")?)
            || !decimal(text(view, "currentPackageRoot")?)
            || !decimal(text(view, "currentWorldRoot")?)
            || !decimal(text(view, "worldRoot")?)
            || !decimal(text(view, "height")?)
        {
            return Err(invalid("v3 claim plan differs from retained fresh BEGIN"));
        }
        let binding = view
            .get("binding")
            .ok_or_else(|| invalid("v3 claim binding field absent"))?;
        match &begin.action {
            LaunchBeginAction::Install if !binding.is_null() => {
                return Err(invalid("INSTALL claim unexpectedly selects a launch"));
            }
            LaunchBeginAction::Create(index) => {
                let selected = descriptor
                    .create_digests
                    .get(*index)
                    .ok_or_else(|| invalid("v3 claim create index absent"))?;
                if text(binding, "choice")? != "create"
                    || text(binding, "createIndex")? != index.to_string()
                    || text(binding, "commandDigest")? != selected
                    || binding.get("priorCreate") != Some(&Value::Null)
                {
                    return Err(invalid("v3 claim create choice differs from signed SPK"));
                }
            }
            LaunchBeginAction::Continue { .. } => {
                let prior = begin
                    .prior_create
                    .as_ref()
                    .ok_or_else(|| invalid("v3 claim retained create witness absent"))?;
                let selected = &descriptor.continue_digest;
                let binding_prior = binding
                    .get("priorCreate")
                    .ok_or_else(|| invalid("v3 claim prior create binding absent"))?;
                if text(binding, "choice")? != "continue"
                    || binding.get("createIndex") != Some(&Value::Null)
                    || text(binding, "commandDigest")? != selected
                    || text(binding_prior, "receiptHex")? != prior.receipt_hex
                    || text(binding_prior, "custodyHex")? != prior.custody_hex
                {
                    return Err(invalid("v3 claim continue witness differs from BEGIN"));
                }
            }
            LaunchBeginAction::Install => {}
        }
        let slots = view
            .get("slots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("v3 claim signing slots absent"))?;
        if slots.len() != self.signers.len() {
            return Err(invalid("v3 claim signer count differs"));
        }
        Ok(slots)
    }
}

pub(crate) struct AssembledLaunchClaim {
    attempt_dir: PathBuf,
    active_marker: Vec<u8>,
    begin_sha256: String,
    descriptor_sha256: String,
    ingress: Vec<u8>,
    original_index: String,
    query_nonce: String,
}

pub(crate) struct CommittedLaunchClaim {
    pub committed: Vec<u8>,
    pub inspection: Vec<u8>,
    pub claim_ingress: Vec<u8>,
    pub physical_begin: VerifiedBegin,
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub world_root: String,
}

/// Current-image op68 plan plus detached op69 ingress. This does not submit
/// op26 or authorize a physical action; the absent committed-v3 inspector must
/// later bind a fresh op26 receipt to these exact bytes and the original BEGIN.
pub(crate) fn assemble_once(
    operator: &PrivateOperator,
    fixed: &FixedLaunchClaimSigners,
    app_uid: u32,
    begin: &AcceptedLaunchBegin,
    launch: &SourceBoundLaunch<'_>,
    nonce_ledger: &Path,
    attempt_dir: &Path,
) -> io::Result<AssembledLaunchClaim> {
    fixed.validate(operator, app_uid)?;
    let original_index = previous_index(&begin.accepted_count)?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v3 claim attempt parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let query_nonce = allocate_operation_id(nonce_ledger)?;
    let source = json!({"originalIndex":original_index,"queryNonce":query_nonce});
    let source_path = write_new(attempt_dir, "request.json", &serde_json::to_vec(&source)?)?;
    let request = operator.tool(
        "author",
        "application-lifecycle-launch-claim-request",
        &source_path,
        &attempt_dir.join("request.bin"),
    )?;
    let active = serde_json::to_vec(&json!({
        "protocol":"mini-spk-launch-claim-prepare-requested-v1",
        "originalIndex":original_index,
        "queryNonce":query_nonce,
        "requestSha256":hex(&Sha256::digest(&request)),
        "originalBeginSha256":hex(&Sha256::digest(&begin.ingress)),
    }))?;
    write_new(attempt_dir, "op68-requested.json", &active)?;
    write_new(parent, "lifecycle-claim-v3-active.json", &active)?;
    let reply = operator.invoke(68, &request)?;
    write_new(attempt_dir, "op68-frame.bin", &reply)?;
    let plan = framed_payload(&reply, 68, PLAN_TAG)?;
    let plan_path = write_new(attempt_dir, "plan.bin", plan)?;
    let inspected = operator.tool(
        "inspect",
        "application-lifecycle-launch-claim-plan",
        &plan_path,
        &attempt_dir.join("plan.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let slots = fixed.checked_plan_slots(
        &view,
        &ClaimPlanEvidence {
            plan,
            request: &request,
            begin,
            launch,
            original_index: &original_index,
            query_nonce: &query_nonce,
        },
    )?;
    let signatures = sign_pinned_slots(slots, &fixed.signers)?;
    let signatures_path = write_new(
        attempt_dir,
        "signatures.json",
        &serde_json::to_vec(&signatures)?,
    )?;
    let encoded = operator.tool(
        "signatures",
        "",
        &signatures_path,
        &attempt_dir.join("signatures.bin"),
    )?;
    let mut pair = Vec::with_capacity(4 + plan.len() + encoded.len());
    pair.extend_from_slice(&(plan.len() as u32).to_le_bytes());
    pair.extend_from_slice(plan);
    pair.extend_from_slice(&encoded);
    write_new(attempt_dir, "op69-requested.bin", &pair)?;
    let reply = operator.invoke(69, &pair)?;
    write_new(attempt_dir, "op69-frame.bin", &reply)?;
    let ingress = framed_payload(&reply, 69, INGRESS_TAG)?.to_vec();
    write_new(attempt_dir, "claim-v3.bin", &ingress)?;
    Ok(AssembledLaunchClaim {
        attempt_dir: attempt_dir.to_path_buf(),
        active_marker: active,
        begin_sha256: hex(&Sha256::digest(&begin.ingress)),
        descriptor_sha256: hex(&Sha256::digest(&launch.descriptor().canonical)),
        ingress,
        original_index,
        query_nonce,
    })
}

fn checked_committed(
    view: &Value,
    committed: &[u8],
    assembled: &AssembledLaunchClaim,
    begin: &AcceptedLaunchBegin,
    launch: &SourceBoundLaunch<'_>,
    fixed: &FixedLaunchClaimSigners,
) -> io::Result<(String, String, String, String)> {
    let descriptor = launch.descriptor();
    let kind = match &begin.action {
        LaunchBeginAction::Install => "install",
        LaunchBeginAction::Create(_) | LaunchBeginAction::Continue { .. } => "start",
    };
    if text(view, "type")? != "application-lifecycle-claim-committed-v3"
        || text(view, "frameHex")? != hex(committed)
        || text(view, "frameByteCount")? != committed.len().to_string()
        || text(view, "originalClaimHex")? != hex(&assembled.ingress)
        || text(view, "originalBeginHex")? != hex(&begin.ingress)
        || text(view, "app")? != fixed.app
        || text(view, "kind")? != kind
        || text(view, "clientOperationId")? != begin.client_operation_id
        || text(view, "authorizationOperationId")? != begin.authorization_operation_id
        || text(view, "packageManifest")? != fixed.package_manifest
        || text(view, "snapshotManifest")? != begin.snapshot_manifest
        || text(view, "processGeneration")? != begin.process_generation
        || text(view, "processIdentityHex")? != begin.process_identity_hex
        || text(view, "descriptorHex")? != hex(&descriptor.canonical)
        || text(view, "descriptorRoot")? != descriptor.root
        || text(view, "volumeIdHex")? != begin.volume_id_hex
        || text(view, "originalTransaction")? != begin.transaction_id
        || text(view, "originalEvent")? != begin.event_id
        || text(view, "imageIdentityHex")? != hex(&descriptor.package.image_identity)
        || !decimal(text(view, "originalNullifier")?)
        || !decimal(text(view, "claimNullifier")?)
        || !decimal(text(view, "appPhysicalRoot")?)
        || !decimal(text(view, "packagePhysicalRoot")?)
        || !decimal(text(view, "authorityPhysicalRoot")?)
        || !decimal(text(view, "postWorldRoot")?)
    {
        return Err(invalid(
            "v3 committed claim differs from fresh ingress or signed SPK",
        ));
    }
    let binding = view
        .get("binding")
        .ok_or_else(|| invalid("v3 committed claim binding absent"))?;
    match &begin.action {
        LaunchBeginAction::Install if !binding.is_null() => {
            return Err(invalid(
                "INSTALL committed claim unexpectedly selected launch",
            ));
        }
        LaunchBeginAction::Create(index) => {
            let digest = descriptor
                .create_digests
                .get(*index)
                .ok_or_else(|| invalid("v3 committed create index absent"))?;
            if text(binding, "choice")? != "create"
                || text(binding, "createIndex")? != index.to_string()
                || text(binding, "commandDigest")? != digest
                || binding.get("priorCreate") != Some(&Value::Null)
            {
                return Err(invalid("v3 committed create binding differs"));
            }
        }
        LaunchBeginAction::Continue { .. } => {
            let prior = begin
                .prior_create
                .as_ref()
                .ok_or_else(|| invalid("v3 committed continue witness absent"))?;
            let committed_prior = binding
                .get("priorCreate")
                .ok_or_else(|| invalid("v3 committed prior create absent"))?;
            if text(binding, "choice")? != "continue"
                || binding.get("createIndex") != Some(&Value::Null)
                || text(binding, "commandDigest")? != descriptor.continue_digest
                || text(committed_prior, "receiptHex")? != prior.receipt_hex
                || text(committed_prior, "custodyHex")? != prior.custody_hex
            {
                return Err(invalid("v3 committed continue witness differs"));
            }
        }
        LaunchBeginAction::Install => {}
    }
    let receipt = view
        .get("receipt")
        .ok_or_else(|| invalid("v3 committed receipt absent"))?;
    let receipt_field = |name| -> io::Result<String> {
        let value = text(receipt, name)?;
        if !decimal(value) {
            return Err(invalid("v3 committed receipt noncanonical"));
        }
        Ok(value.to_owned())
    };
    let transaction_id = receipt_field("transactionId")?;
    let event_id = receipt_field("eventId")?;
    let accepted_count = receipt_field("acceptedCount")?;
    let world_root = receipt_field("worldRoot")?;
    if !later_decimal(&accepted_count, &begin.accepted_count)
        || world_root != text(view, "postWorldRoot")?
    {
        return Err(invalid(
            "v3 committed receipt differs from claimed post-image",
        ));
    }
    Ok((transaction_id, event_id, accepted_count, world_root))
}

/// Submit once to op26. Only its fresh-tip committed-v3 callback can arm a
/// physical caller; an op27 receipt-only lookup never enters this path.
pub(crate) fn submit_fresh_once(
    operator: &PrivateOperator,
    assembled: AssembledLaunchClaim,
    begin: &AcceptedLaunchBegin,
    launch: &SourceBoundLaunch<'_>,
    fixed: &FixedLaunchClaimSigners,
) -> io::Result<CommittedLaunchClaim> {
    checked_assembled(&assembled, begin, launch)?;
    let attempt_dir = &assembled.attempt_dir;
    let marker = json!({
        "protocol":"mini-spk-launch-claim-submit-requested-v1",
        "originalIndex":assembled.original_index,
        "queryNonce":assembled.query_nonce,
        "ingressSha256":hex(&Sha256::digest(&assembled.ingress)),
        "originalBeginSha256":hex(&Sha256::digest(&begin.ingress)),
    });
    write_new(
        attempt_dir,
        "op26-requested.json",
        &serde_json::to_vec(&marker)?,
    )?;
    let reply = operator.invoke(26, &assembled.ingress)?;
    write_new(attempt_dir, "op26-frame.bin", &reply)?;
    let committed = framed_payload(&reply, 26, COMMITTED_TAG)?.to_vec();
    let committed_path = write_new(attempt_dir, "committed-v3.bin", &committed)?;
    let inspection = operator.tool(
        "inspect",
        "application-lifecycle-claim-committed-v3",
        &committed_path,
        &attempt_dir.join("committed-v3.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspection)?;
    let (transaction_id, event_id, accepted_count, world_root) =
        checked_committed(&view, &committed, &assembled, begin, launch, fixed)?;
    let physical_begin = verified_physical_begin(fixed, begin, launch, &transaction_id, &event_id)?;
    Ok(CommittedLaunchClaim {
        committed,
        inspection,
        claim_ingress: assembled.ingress,
        physical_begin,
        transaction_id,
        event_id,
        accepted_count,
        world_root,
    })
}

fn verified_physical_begin(
    fixed: &FixedLaunchClaimSigners,
    begin: &AcceptedLaunchBegin,
    launch: &SourceBoundLaunch<'_>,
    transaction_id: &str,
    event_id: &str,
) -> io::Result<VerifiedBegin> {
    let app: u64 = fixed
        .app
        .parse()
        .map_err(|_| invalid("v3 claimed app exceeds host unit range"))?;
    let generation: u64 = begin
        .process_generation
        .parse()
        .map_err(|_| invalid("v3 claimed generation exceeds host unit range"))?;
    if app == 0
        || generation == 0
        || !decimal(&begin.authorization_operation_id)
        || !decimal(transaction_id)
        || !decimal(event_id)
    {
        return Err(invalid("v3 claimed physical identity malformed"));
    }
    let unit = format!("mini-spk-a{app}-g{generation}.service");
    if begin.process_identity_hex != hex(unit.as_bytes()) {
        return Err(invalid("v3 claimed unit differs from inspected BEGIN"));
    }
    Ok(VerifiedBegin {
        app,
        generation,
        operation_id: begin.authorization_operation_id.clone(),
        transaction_id: transaction_id.to_owned(),
        event_id: event_id.to_owned(),
        package_sha256: launch.signed_package_sha256().to_owned(),
        image_identity: hex(&launch.descriptor().package.image_identity),
        process_identity: unit.clone(),
        unit,
    })
}

fn checked_assembled(
    assembled: &AssembledLaunchClaim,
    begin: &AcceptedLaunchBegin,
    launch: &SourceBoundLaunch<'_>,
) -> io::Result<()> {
    let attempt_dir = &assembled.attempt_dir;
    private_dir(attempt_dir)?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v3 claim attempt parent absent"))?;
    private_dir(parent)?;
    if fs::read(parent.join("lifecycle-claim-v3-active.json"))? != assembled.active_marker
        || fs::read(attempt_dir.join("claim-v3.bin"))? != assembled.ingress
        || assembled.begin_sha256 != hex(&Sha256::digest(&begin.ingress))
        || assembled.descriptor_sha256 != hex(&Sha256::digest(&launch.descriptor().canonical))
    {
        return Err(invalid("v3 claim attempt artifacts differ before submit"));
    }
    if !decimal(&assembled.original_index) || !decimal(&assembled.query_nonce) {
        return Err(invalid("v3 assembled claim identity malformed"));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_native::SourceDescriptor;
    use crate::launch_descriptor_native::SourceLaunchDescriptor;
    use crate::materialize::InstalledPackage;
    use sandstorm_package::{manifest::Action, manifest::Command as SpkCommand, SpkManifest};
    use std::os::unix::fs::DirBuilderExt;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn launch() -> SourceBoundLaunch<'static> {
        let manifest: SpkManifest = serde_json::from_value(json!({
            "app_id":"signed", "app_title":"test", "app_version":1,
            "actions":[],
            "continue_command":{"argv":["/continue"],"environ":[]}
        }))
        .unwrap();
        let mut package = InstalledPackage {
            directory: "/protected/image".into(),
            raw_sha256: "a".repeat(64),
            raw_sha256_bytes: [0xaa; 32],
            raw_length: 1,
            signed_manifest_sha256: [0xbb; 32],
            signed_bridge_config_sha256: None,
            signed_bridge_config: None,
            manifest,
        };
        package.manifest.actions.push(Action {
            noun_phrase: "create".into(),
            command: SpkCommand {
                argv: vec!["/create".into()],
                environ: vec![],
            },
        });
        SourceBoundLaunch::test_pair(
            Box::leak(Box::new(package)),
            SourceLaunchDescriptor {
                package: SourceDescriptor {
                    canonical: b"package".to_vec(),
                    root: "11".into(),
                    image_identity: b"image".to_vec(),
                    api_path: None,
                },
                canonical: b"launch".to_vec(),
                root: "22".into(),
                create_digests: vec!["33".into()],
                continue_digest: "44".into(),
            },
        )
    }

    #[test]
    fn original_index_carries_full_nat_without_u64_truncation() {
        assert_eq!(previous_index("1").unwrap(), "0");
        assert_eq!(
            previous_index("100000000000000000000").unwrap(),
            "99999999999999999999"
        );
        assert!(later_decimal(
            "100000000000000000000",
            "99999999999999999999"
        ));
        assert!(!later_decimal(
            "99999999999999999999",
            "100000000000000000000"
        ));
        for bad in ["0", "01", "", "-1"] {
            assert!(previous_index(bad).is_err());
        }
    }

    #[test]
    fn claim_frame_cannot_be_v2_or_wrong_opcode() {
        let mut frame = ((INGRESS_TAG.len() + 2) as u32).to_le_bytes().to_vec();
        frame.push(69);
        frame.extend_from_slice(INGRESS_TAG);
        frame.push(1);
        assert!(framed_payload(&frame, 69, INGRESS_TAG).is_ok());
        assert!(
            framed_payload(&frame, 69, b"DREGG/APPLICATION/LIFECYCLE-CLAIM-INGRESS/v2").is_err()
        );
        assert!(framed_payload(&frame, 53, INGRESS_TAG).is_err());
    }

    #[test]
    fn claim_plan_joins_original_receipt_volume_and_selected_command() {
        let launch = launch();
        let begin = AcceptedLaunchBegin {
            ingress: b"original begin".to_vec(),
            action: LaunchBeginAction::Create(0),
            prior_create: None,
            client_operation_id: "7".into(),
            authorization_operation_id: "8".into(),
            volume_id_hex: "aa".repeat(32),
            snapshot_manifest: "16".into(),
            process_generation: "2".into(),
            process_identity_hex: hex(b"mini-spk-a5-g2.service"),
            transaction_id: "9".into(),
            event_id: "10".into(),
            accepted_count: "12".into(),
            world_root: "13".into(),
        };
        let fixed = FixedLaunchClaimSigners {
            protocol: "mini-spk-resident-claim-management-v1".into(),
            app: "5".into(),
            package_manifest: "6".into(),
            management_subject: "4".into(),
            signers: vec![],
        };
        let mut plan = json!({
            "type":"application-lifecycle-launch-claim-plan-v1",
            "canonicalPlanHex":"706c616e",
            "canonicalRequestHex":"72657175657374",
            "originalBeginHex":hex(&begin.ingress),
            "descriptorHex":hex(&launch.descriptor().canonical),
            "descriptorRoot":"22",
            "volumeIdHex":begin.volume_id_hex,
            "clientOperationId":"7",
            "authorizationOperationId":"8",
            "originalIndex":"11",
            "queryNonce":"14",
            "app":"5",
            "managementSubject":"4",
            "originalBeginTransactionId":"9",
            "originalBeginEventId":"10",
            "originalBeginAcceptedCount":"12",
            "originalBeginWorldRoot":"13",
            "originalBeginReceiptHex":"ab",
            "sourceHex":"cd",
            "currentAppRoot":"2",
            "currentPackageRoot":"3",
            "currentWorldRoot":"4",
            "worldRoot":"5",
            "height":"6",
            "binding":{"choice":"create","createIndex":"0","commandDigest":"33","priorCreate":null},
            "slots":[],
        });
        let evidence = ClaimPlanEvidence {
            plan: b"plan",
            request: b"request",
            begin: &begin,
            launch: &launch,
            original_index: "11",
            query_nonce: "14",
        };
        assert!(fixed.checked_plan_slots(&plan, &evidence).is_ok());
        for (field, replacement) in [
            ("originalBeginEventId", "99"),
            ("volumeIdHex", "bb"),
            ("descriptorRoot", "99"),
        ] {
            let old = plan[field].clone();
            plan[field] = Value::String(replacement.into());
            assert!(fixed.checked_plan_slots(&plan, &evidence).is_err());
            plan[field] = old;
        }
        plan["binding"]["commandDigest"] = Value::String("44".into());
        assert!(fixed.checked_plan_slots(&plan, &evidence).is_err());
    }

    #[test]
    fn continue_claim_requires_same_created_receipt_and_custody_as_begin() {
        let launch = launch();
        let begin = AcceptedLaunchBegin {
            ingress: b"continued begin".to_vec(),
            action: LaunchBeginAction::Continue {
                created_index: "7".into(),
            },
            prior_create: Some(crate::lifecycle_v3_native::CreatedWitness {
                receipt_hex: "abcd".into(),
                custody_hex: "ef01".into(),
            }),
            client_operation_id: "8".into(),
            authorization_operation_id: "9".into(),
            volume_id_hex: "aa".repeat(32),
            snapshot_manifest: "16".into(),
            process_generation: "2".into(),
            process_identity_hex: hex(b"mini-spk-a5-g2.service"),
            transaction_id: "10".into(),
            event_id: "11".into(),
            accepted_count: "12".into(),
            world_root: "13".into(),
        };
        let fixed = FixedLaunchClaimSigners {
            protocol: "mini-spk-resident-claim-management-v1".into(),
            app: "5".into(),
            package_manifest: "6".into(),
            management_subject: "4".into(),
            signers: vec![],
        };
        let mut plan = json!({
            "type":"application-lifecycle-launch-claim-plan-v1",
            "canonicalPlanHex":"706c616e", "canonicalRequestHex":"72657175657374",
            "originalBeginHex":hex(&begin.ingress),
            "descriptorHex":hex(&launch.descriptor().canonical), "descriptorRoot":"22",
            "volumeIdHex":begin.volume_id_hex, "clientOperationId":"8",
            "authorizationOperationId":"9", "originalIndex":"11", "queryNonce":"14",
            "app":"5", "managementSubject":"4",
            "originalBeginTransactionId":"10", "originalBeginEventId":"11",
            "originalBeginAcceptedCount":"12", "originalBeginWorldRoot":"13",
            "originalBeginReceiptHex":"ab", "sourceHex":"cd",
            "currentAppRoot":"2",
            "currentPackageRoot":"3", "currentWorldRoot":"4",
            "worldRoot":"5", "height":"6",
            "binding":{"choice":"continue","createIndex":null,"commandDigest":"44",
                       "priorCreate":{"receiptHex":"abcd","custodyHex":"ef01"}},
            "slots":[],
        });
        let evidence = ClaimPlanEvidence {
            plan: b"plan",
            request: b"request",
            begin: &begin,
            launch: &launch,
            original_index: "11",
            query_nonce: "14",
        };
        assert!(fixed.checked_plan_slots(&plan, &evidence).is_ok());
        plan["binding"]["priorCreate"]["custodyHex"] = json!("ef02");
        assert!(fixed.checked_plan_slots(&plan, &evidence).is_err());
    }

    #[test]
    fn committed_claim_must_echo_fresh_frame_and_original_authority() {
        let launch = launch();
        let mut begin = AcceptedLaunchBegin {
            ingress: b"begin".to_vec(),
            action: LaunchBeginAction::Create(0),
            prior_create: None,
            client_operation_id: "7".into(),
            authorization_operation_id: "8".into(),
            volume_id_hex: "aa".repeat(32),
            snapshot_manifest: "16".into(),
            process_generation: "2".into(),
            process_identity_hex: hex(b"mini-spk-a5-g2.service"),
            transaction_id: "9".into(),
            event_id: "10".into(),
            accepted_count: "11".into(),
            world_root: "12".into(),
        };
        let assembled = AssembledLaunchClaim {
            attempt_dir: "/protected/claim-attempt".into(),
            active_marker: b"active".to_vec(),
            begin_sha256: hex(&Sha256::digest(b"begin")),
            descriptor_sha256: hex(&Sha256::digest(&launch.descriptor().canonical)),
            ingress: b"claim".to_vec(),
            original_index: "10".into(),
            query_nonce: "14".into(),
        };
        let fixed = FixedLaunchClaimSigners {
            protocol: "mini-spk-resident-claim-management-v1".into(),
            app: "5".into(),
            package_manifest: "6".into(),
            management_subject: "4".into(),
            signers: vec![],
        };
        let committed = b"committed";
        let mut view = json!({
            "type":"application-lifecycle-claim-committed-v3",
            "frameHex":hex(committed), "frameByteCount":committed.len().to_string(),
            "originalClaimHex":hex(&assembled.ingress),
            "originalBeginHex":hex(&begin.ingress),
            "app":"5", "kind":"start", "clientOperationId":"7",
            "authorizationOperationId":"8", "packageManifest":"6",
            "snapshotManifest":"16", "processGeneration":"2",
            "processIdentityHex":begin.process_identity_hex,
            "imageIdentityHex":hex(&launch.descriptor().package.image_identity),
            "descriptorHex":hex(&launch.descriptor().canonical),
            "descriptorRoot":"22", "volumeIdHex":begin.volume_id_hex,
            "originalTransaction":"9", "originalEvent":"10",
            "originalNullifier":"15", "claimNullifier":"16",
            "appPhysicalRoot":"17", "packagePhysicalRoot":"18",
            "authorityPhysicalRoot":"19", "postWorldRoot":"24",
            "binding":{"choice":"create","createIndex":"0",
                       "commandDigest":"33","priorCreate":null},
            "receipt":{"transactionId":"21","eventId":"22",
                       "acceptedCount":"23","worldRoot":"24"}
        });
        assert_eq!(
            checked_committed(&view, committed, &assembled, &begin, &launch, &fixed).unwrap(),
            ("21".into(), "22".into(), "23".into(), "24".into())
        );
        let identity = verified_physical_begin(&fixed, &begin, &launch, "21", "22").unwrap();
        assert_eq!(identity.unit, "mini-spk-a5-g2.service");
        assert_eq!(identity.package_sha256, "a".repeat(64));
        assert_eq!(identity.transaction_id, "21");
        for (field, changed) in [
            ("frameHex", "00"),
            ("originalClaimHex", "00"),
            ("originalBeginHex", "00"),
            ("volumeIdHex", "00"),
            ("originalTransaction", "99"),
            ("postWorldRoot", "20"),
        ] {
            let saved = view[field].clone();
            view[field] = json!(changed);
            assert!(
                checked_committed(&view, committed, &assembled, &begin, &launch, &fixed).is_err()
            );
            view[field] = saved;
        }
        view["receipt"]["acceptedCount"] = json!("023");
        assert!(checked_committed(&view, committed, &assembled, &begin, &launch, &fixed).is_err());
        view["receipt"]["acceptedCount"] = json!("11");
        assert!(checked_committed(&view, committed, &assembled, &begin, &launch, &fixed).is_err());
        begin.authorization_operation_id =
            "115792089237316195423570985008687907853269984665640564039457584007913129639935".into();
        assert_eq!(
            verified_physical_begin(&fixed, &begin, &launch, "21", "22")
                .unwrap()
                .operation_id,
            begin.authorization_operation_id
        );
    }

    #[test]
    fn assembled_claim_preflight_binds_one_parent_marker_begin_and_descriptor() {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let parent = std::env::temp_dir().join(format!(
            "spk-v3-claim-active-{}-{stamp}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&parent).unwrap();
        let attempt_dir = parent.join("attempt");
        DirBuilder::new().mode(0o700).create(&attempt_dir).unwrap();
        let launch = launch();
        let mut begin = AcceptedLaunchBegin {
            ingress: b"begin".to_vec(),
            action: LaunchBeginAction::Install,
            prior_create: None,
            client_operation_id: "7".into(),
            authorization_operation_id: "8".into(),
            volume_id_hex: "aa".repeat(32),
            snapshot_manifest: "16".into(),
            process_generation: "2".into(),
            process_identity_hex: hex(b"mini-spk-a5-g2.service"),
            transaction_id: "9".into(),
            event_id: "10".into(),
            accepted_count: "11".into(),
            world_root: "12".into(),
        };
        let assembled = AssembledLaunchClaim {
            attempt_dir: attempt_dir.clone(),
            active_marker: b"active".to_vec(),
            begin_sha256: hex(&Sha256::digest(&begin.ingress)),
            descriptor_sha256: hex(&Sha256::digest(&launch.descriptor().canonical)),
            ingress: b"claim".to_vec(),
            original_index: "10".into(),
            query_nonce: "13".into(),
        };
        write_new(&parent, "lifecycle-claim-v3-active.json", b"active").unwrap();
        write_new(&attempt_dir, "claim-v3.bin", b"claim").unwrap();
        assert!(checked_assembled(&assembled, &begin, &launch).is_ok());
        begin.ingress = b"different begin".to_vec();
        assert!(checked_assembled(&assembled, &begin, &launch).is_err());
        begin.ingress = b"begin".to_vec();
        fs::write(attempt_dir.join("claim-v3.bin"), b"different claim").unwrap();
        assert!(checked_assembled(&assembled, &begin, &launch).is_err());
        fs::remove_dir_all(&parent).unwrap();
    }
}
