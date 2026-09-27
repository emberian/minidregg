//! Source-owned v3 launch claim plan and detached assembly. Fresh op26
//! committed-v3 inspection is still unavailable, so no physical caller may
//! promote these signed ingress bytes into an INSTALL or START permit.
#![allow(dead_code)] // Awaiting native event24 receiver and committed inspector.

use crate::dispatch_author::SignerPin;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::lifecycle_v3_native::{
    decimal, framed_payload, hex, lowercase_hex, sign_pinned_slots, text, AcceptedLaunchBegin,
    LaunchBeginAction,
};
use crate::resident_begin_native::allocate_operation_id;
use crate::resident_launch::SourceBoundLaunch;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::DirBuilder;
use std::io;
use std::os::unix::fs::DirBuilderExt;
use std::path::Path;

const PLAN_TAG: &[u8] = b"DREGG/APPLICATION/LAUNCH-CLAIM-OPERATOR-PLAN/v1";
const INGRESS_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-CLAIM-INGRESS/v3";

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
            || text(view, "originalBeginImageBoundary")? != begin.image_boundary
            || !lowercase_hex(text(view, "originalBeginReceiptHex")?)
            || text(view, "originalBeginReceiptHex")?.is_empty()
            || !lowercase_hex(text(view, "sourceHex")?)
            || text(view, "sourceHex")?.is_empty()
            || !decimal(text(view, "currentAuthorityRoot")?)
            || !decimal(text(view, "currentAppRoot")?)
            || !decimal(text(view, "currentPackageRoot")?)
            || !decimal(text(view, "currentImageBoundary")?)
            || !decimal(text(view, "imageBoundary")?)
            || !decimal(text(view, "height")?)
        {
            return Err(invalid("v3 claim plan differs from retained fresh BEGIN"));
        }
        let binding = view
            .get("binding")
            .ok_or_else(|| invalid("v3 claim binding field absent"))?;
        match begin.action {
            LaunchBeginAction::Install if !binding.is_null() => {
                return Err(invalid("INSTALL claim unexpectedly selects a launch"));
            }
            LaunchBeginAction::Create(index) => {
                let selected = descriptor
                    .create_digests
                    .get(index)
                    .ok_or_else(|| invalid("v3 claim create index absent"))?;
                if text(binding, "choice")? != "create"
                    || text(binding, "createIndex")? != index.to_string()
                    || text(binding, "commandDigest")? != selected
                    || binding.get("priorCreate") != Some(&Value::Null)
                {
                    return Err(invalid("v3 claim create choice differs from signed SPK"));
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
    pub ingress: Vec<u8>,
    pub original_index: String,
    pub query_nonce: String,
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
        ingress,
        original_index,
        query_nonce,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_native::SourceDescriptor;
    use crate::launch_descriptor_native::SourceLaunchDescriptor;
    use crate::materialize::InstalledPackage;
    use sandstorm_package::{manifest::Action, manifest::Command as SpkCommand, SpkManifest};

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
            client_operation_id: "7".into(),
            authorization_operation_id: "8".into(),
            volume_id_hex: "aa".repeat(32),
            transaction_id: "9".into(),
            event_id: "10".into(),
            accepted_count: "12".into(),
            image_boundary: "13".into(),
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
            "originalBeginImageBoundary":"13",
            "originalBeginReceiptHex":"ab",
            "sourceHex":"cd",
            "currentAuthorityRoot":"1",
            "currentAppRoot":"2",
            "currentPackageRoot":"3",
            "currentImageBoundary":"4",
            "imageBoundary":"5",
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
}
