//! Source-authored launch-bound BEGIN request, signing and one-shot admission.
//! The callable INSTALL/START routes remain gated until event23–25 Host
//! authoring, fresh callbacks and physical claim inspection are qualified.
#![allow(dead_code)] // The v3 lifecycle caller is still source-gated.

use crate::dispatch_author::{private_signing_key, SignerPin};
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::resident_begin_native::allocate_operation_id;
use crate::resident_launch::SourceBoundLaunch;
use ed25519_dalek::Signer;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::DirBuilder;
use std::io;
use std::os::unix::fs::DirBuilderExt;
use std::path::Path;

const MAX_FRAME: usize = 12_102_760;
const PLAN_TAG: &[u8] = b"DREGG/APPLICATION/LAUNCH-BEGIN-OPERATOR-PLAN/v1";
const BEGIN_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-BEGIN-INGRESS/v3";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

pub(crate) fn hex(bytes: &[u8]) -> String {
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(result, "{byte:02x}").expect("writing to String");
    }
    result
}

pub(crate) fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

pub(crate) fn lowercase_hex(value: &str) -> bool {
    value.len().is_multiple_of(2)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

pub(crate) fn unhex(value: &str) -> io::Result<Vec<u8>> {
    if !lowercase_hex(value) {
        return Err(invalid("v3 BEGIN noncanonical hexadecimal"));
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let pair = std::str::from_utf8(pair).map_err(|_| invalid("v3 BEGIN hex pair"))?;
            u8::from_str_radix(pair, 16).map_err(|_| invalid("v3 BEGIN hex pair"))
        })
        .collect()
}

pub(crate) fn text<'a>(value: &'a Value, field: &str) -> io::Result<&'a str> {
    value
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("v3 BEGIN source inspection field absent"))
}

fn checked_physical_identity(view: &Value, launch: &SourceBoundLaunch<'_>) -> io::Result<()> {
    let app = text(view, "app")?
        .parse::<u64>()
        .map_err(|_| invalid("v3 BEGIN app exceeds physical unit range"))?;
    let before = text(view, "beforeGeneration")?
        .parse::<u64>()
        .map_err(|_| invalid("v3 BEGIN prior generation exceeds physical unit range"))?;
    let generation = text(view, "processGeneration")?
        .parse::<u64>()
        .map_err(|_| invalid("v3 BEGIN generation exceeds physical unit range"))?;
    let expected = before
        .checked_add(1)
        .ok_or_else(|| invalid("v3 BEGIN generation overflow"))?;
    if app == 0
        || generation != expected
        || text(view, "processIdentityHex")?
            != hex(format!("mini-spk-a{app}-g{generation}.service").as_bytes())
        || text(view, "imageIdentityHex")? != hex(&launch.descriptor().package.image_identity)
    {
        return Err(invalid("v3 BEGIN physical unit or image identity differs"));
    }
    Ok(())
}

pub(crate) fn framed_payload<'a>(reply: &'a [u8], opcode: u8, tag: &[u8]) -> io::Result<&'a [u8]> {
    if reply.len() < 6 {
        return Err(invalid("v3 BEGIN native reply truncated"));
    }
    let length = u32::from_le_bytes(reply[..4].try_into().unwrap()) as usize;
    if !(2..=MAX_FRAME).contains(&length)
        || length + 4 != reply.len()
        || reply[4] != opcode
        || !reply[5..].starts_with(tag)
        || reply[5..].len() <= tag.len()
    {
        return Err(invalid("v3 BEGIN native reply version or framing refused"));
    }
    Ok(&reply[5..])
}

fn hold_begin_attempt(parent: &Path, active: &[u8]) -> io::Result<()> {
    write_new(parent, "lifecycle-begin-v3-active.json", active)?;
    Ok(())
}

/// Sign only source-inspected, ordered Ed25519 headers pinned to exact
/// operator custody. Both v3 BEGIN and v3 claim plans use this slot grammar.
pub(crate) fn sign_pinned_slots(slots: &[Value], pins: &[SignerPin]) -> io::Result<Value> {
    if slots.len() != pins.len() {
        return Err(invalid("v3 lifecycle signing slot count differs"));
    }
    let mut signatures = Vec::with_capacity(slots.len());
    for (slot, pin) in slots.iter().zip(pins) {
        let signing = slot
            .get("signing")
            .ok_or_else(|| invalid("v3 lifecycle signing decode absent"))?;
        let header = text(slot, "headerHex")?;
        if text(slot, "role")? != pin.role
            || text(slot, "index")? != pin.index
            || signing.get("decoded").and_then(Value::as_bool) != Some(true)
            || text(signing, "keyId")? != pin.key_id
            || text(signing, "keyEpoch")? != pin.key_epoch
            || text(signing, "algorithm")? != "1"
            || !decimal(text(signing, "authorityRoot")?)
            || !decimal(text(signing, "nullifier")?)
            || !lowercase_hex(text(signing, "domainHex")?)
            || !lowercase_hex(text(signing, "messageHex")?)
        {
            return Err(invalid("v3 lifecycle slot differs from pinned signer"));
        }
        let bytes = unhex(header)?;
        if bytes.is_empty() || bytes.len() > 65_536 {
            return Err(invalid("v3 lifecycle signing header bound refused"));
        }
        let key = private_signing_key(&pin.seed_path)?;
        if hex(&key.verifying_key().to_bytes()) != pin.public_key_hex {
            return Err(invalid("v3 lifecycle signer private/public pin differs"));
        }
        signatures.push(Value::String(hex(&key.sign(&bytes).to_bytes())));
    }
    Ok(Value::Array(signatures))
}

#[derive(Clone)]
pub(crate) enum LaunchBeginAction {
    Install,
    Create(usize),
    /// A retained successful create is selected by its verified native index.
    /// The receipt and custody are supplied only by Mini's inspected plan.
    Continue {
        created_index: String,
    },
}

impl LaunchBeginAction {
    fn kind(&self) -> &'static str {
        match self {
            Self::Install => "install",
            Self::Create(_) => "start",
            Self::Continue { .. } => "continue",
        }
    }

    fn author_kind(&self) -> &'static str {
        match self {
            Self::Continue { .. } => "application-lifecycle-launch-continue-request",
            _ => "application-lifecycle-launch-begin-request",
        }
    }

    fn create_index(&self) -> Value {
        match self {
            Self::Install => Value::Null,
            Self::Create(index) => Value::String(index.to_string()),
            Self::Continue { .. } => Value::Null,
        }
    }

    fn selected_digest<'a>(
        &self,
        launch: &'a SourceBoundLaunch<'_>,
    ) -> io::Result<Option<&'a str>> {
        match self {
            Self::Install => Ok(None),
            Self::Create(index) => launch
                .descriptor()
                .create_digests
                .get(*index)
                .map(String::as_str)
                .map(Some)
                .ok_or_else(|| invalid("v3 BEGIN create index absent from signed descriptor")),
            Self::Continue { created_index } => {
                if !decimal(created_index) {
                    return Err(invalid("v3 BEGIN created index noncanonical"));
                }
                Ok(Some(&launch.descriptor().continue_digest))
            }
        }
    }
}

fn request_json(
    action: &LaunchBeginAction,
    client_operation_id: &str,
    launch: &SourceBoundLaunch<'_>,
) -> io::Result<Value> {
    if !decimal(client_operation_id)
        || launch.descriptor().canonical.is_empty()
        || launch.descriptor().canonical.len() >= MAX_FRAME
    {
        return Err(invalid("v3 BEGIN client operation or descriptor refused"));
    }
    action.selected_digest(launch)?;
    Ok(match action {
        LaunchBeginAction::Continue { created_index } => json!({
            "clientOperationId":client_operation_id,
            "descriptor":hex(&launch.descriptor().canonical),
            "createdIndex":created_index,
        }),
        _ => json!({
            "kind":action.kind(),
            "clientOperationId":client_operation_id,
            "descriptor":hex(&launch.descriptor().canonical),
            "createIndex":action.create_index(),
        }),
    })
}

#[derive(Clone)]
pub(crate) struct CreatedWitness {
    pub receipt_hex: String,
    pub custody_hex: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedLaunchBeginSigners {
    protocol: String,
    app: String,
    package_manifest: String,
    snapshot_manifest: String,
    management_subject: String,
    signers: Vec<SignerPin>,
}

impl FixedLaunchBeginSigners {
    pub(crate) fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-resident-begin-management-v1"
            || self.signers.is_empty()
            || self.signers.len() > 64
            || ![
                &self.app,
                &self.package_manifest,
                &self.snapshot_manifest,
                &self.management_subject,
            ]
            .iter()
            .all(|value| decimal(value))
        {
            return Err(invalid("v3 BEGIN fixed management custody refused"));
        }
        let config: Value = serde_json::from_slice(&operator.pinned_config()?)?;
        let manager = config
            .get("residentBeginManagement")
            .ok_or_else(|| invalid("Mini BEGIN management pin absent"))?;
        for (field, expected) in [
            ("app", &self.app),
            ("packageManifest", &self.package_manifest),
            ("snapshotManifest", &self.snapshot_manifest),
            ("managementSubject", &self.management_subject),
        ] {
            let value = manager
                .get(field)
                .ok_or_else(|| invalid("Mini BEGIN management coordinate absent"))?;
            let value = value
                .as_str()
                .map(str::to_owned)
                .or_else(|| value.as_u64().map(|number| number.to_string()))
                .ok_or_else(|| invalid("Mini BEGIN management coordinate malformed"))?;
            if value != *expected {
                return Err(invalid("v3 BEGIN fixed management differs from Mini pin"));
            }
        }
        let key_id = manager
            .get("managementKeyId")
            .and_then(|value| {
                value
                    .as_str()
                    .map(str::to_owned)
                    .or_else(|| value.as_u64().map(|n| n.to_string()))
            })
            .ok_or_else(|| invalid("Mini BEGIN management key absent"))?;
        for signer in &self.signers {
            if signer.key_id != key_id {
                return Err(invalid("v3 BEGIN signer key differs from Mini pin"));
            }
            crate::sandbox::open_protected_directory(
                signer
                    .seed_path
                    .parent()
                    .ok_or_else(|| invalid("v3 BEGIN signer parent absent"))?,
                app_uid,
                false,
            )?;
        }
        Ok(())
    }

    fn checked_plan_slots<'a>(
        &self,
        view: &'a Value,
        plan: &[u8],
        request: &[u8],
        action: &LaunchBeginAction,
        client_operation_id: &str,
        launch: &SourceBoundLaunch<'_>,
    ) -> io::Result<(&'a [Value], Option<CreatedWitness>)> {
        let descriptor = launch.descriptor();
        let selected = action.selected_digest(launch)?;
        let nested = view
            .get("request")
            .ok_or_else(|| invalid("v3 BEGIN inspected request absent"))?;
        if text(view, "type")? != "application-lifecycle-launch-begin-plan-v1"
            || text(view, "canonicalPlanHex")? != hex(plan)
            || text(view, "canonicalRequestHex")? != hex(request)
            || text(nested, "canonicalRequestHex")? != hex(request)
            || text(nested, "type")?
                != if matches!(action, LaunchBeginAction::Continue { .. }) {
                    "application-lifecycle-launch-continue-request-v1"
                } else {
                    "application-lifecycle-launch-begin-request-v1"
                }
            || text(nested, "kind")? != action.kind()
            || text(nested, "clientOperationId")? != client_operation_id
            || text(nested, "descriptorHex")? != hex(&descriptor.canonical)
            || text(view, "app")? != self.app
            || text(view, "packageManifest")? != self.package_manifest
            || text(view, "snapshotManifest")? != self.snapshot_manifest
            || text(view, "managementSubject")? != self.management_subject
            || text(view, "descriptorRoot")? != descriptor.root
            || text(view, "packageRoot")? != descriptor.root
            || view.get("selectedCommandDigest")
                != Some(&selected.map_or(Value::Null, |digest| Value::String(digest.into())))
            || !decimal(text(view, "authorizationOperationId")?)
            || !decimal(text(view, "imageBoundary")?)
            || !decimal(text(view, "height")?)
            || !lowercase_hex(text(view, "unsignedIngressHex")?)
            || text(view, "unsignedIngressHex")?.is_empty()
            || text(view, "volumeIdHex")?.len() != 64
            || !lowercase_hex(text(view, "volumeIdHex")?)
        {
            return Err(invalid("v3 BEGIN plan differs from fixed signed launch"));
        }
        let prior_create = match action {
            LaunchBeginAction::Continue { created_index } => {
                if text(nested, "createdIndex")? != created_index {
                    return Err(invalid("v3 BEGIN created index differs from request"));
                }
                let prior = view
                    .get("priorCreate")
                    .ok_or_else(|| invalid("v3 BEGIN prior create witness absent"))?;
                let receipt_hex = text(prior, "receiptHex")?;
                let custody_hex = text(prior, "custodyHex")?;
                if receipt_hex.is_empty()
                    || custody_hex.is_empty()
                    || !lowercase_hex(receipt_hex)
                    || !lowercase_hex(custody_hex)
                {
                    return Err(invalid("v3 BEGIN prior create witness malformed"));
                }
                Some(CreatedWitness {
                    receipt_hex: receipt_hex.to_owned(),
                    custody_hex: custody_hex.to_owned(),
                })
            }
            _ => {
                if nested.get("createIndex") != Some(&action.create_index())
                    || view.get("priorCreate") != Some(&Value::Null)
                {
                    return Err(invalid("v3 BEGIN unexpected prior create witness"));
                }
                None
            }
        };
        checked_physical_identity(view, launch)?;
        let slots = view
            .get("slots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("v3 BEGIN signing slots absent"))?;
        if slots.len() != self.signers.len() {
            return Err(invalid("v3 BEGIN signing slot count differs"));
        }
        Ok((slots, prior_create))
    }

    fn signatures(
        &self,
        view: &Value,
        plan: &[u8],
        request: &[u8],
        action: &LaunchBeginAction,
        client_operation_id: &str,
        launch: &SourceBoundLaunch<'_>,
    ) -> io::Result<(Value, Option<CreatedWitness>)> {
        let (slots, prior_create) =
            self.checked_plan_slots(view, plan, request, action, client_operation_id, launch)?;
        Ok((sign_pinned_slots(slots, &self.signers)?, prior_create))
    }
}

pub(crate) struct AcceptedLaunchBegin {
    pub ingress: Vec<u8>,
    pub action: LaunchBeginAction,
    pub prior_create: Option<CreatedWitness>,
    pub client_operation_id: String,
    pub authorization_operation_id: String,
    pub volume_id_hex: String,
    pub snapshot_manifest: String,
    pub process_generation: String,
    pub process_identity_hex: String,
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub image_boundary: String,
}

/// Single v3 author/assemble/submit attempt. The request marker is durable
/// before the first current-image call; uncertain results are never retried.
pub(crate) fn submit_once(
    operator: &PrivateOperator,
    fixed: &FixedLaunchBeginSigners,
    app_uid: u32,
    launch: &SourceBoundLaunch<'_>,
    action: LaunchBeginAction,
    ledger: &Path,
    attempt_dir: &Path,
) -> io::Result<AcceptedLaunchBegin> {
    fixed.validate(operator, app_uid)?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v3 BEGIN attempt parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let client_operation_id = allocate_operation_id(ledger)?;
    let source = request_json(&action, &client_operation_id, launch)?;
    let source_path = write_new(attempt_dir, "request.json", &serde_json::to_vec(&source)?)?;
    let request = operator.tool(
        "author",
        action.author_kind(),
        &source_path,
        &attempt_dir.join("request.bin"),
    )?;
    let active = serde_json::to_vec(&json!({
        "protocol":"mini-spk-launch-begin-prepare-requested-v1",
        "clientOperationId":client_operation_id,
        "requestSha256":hex(&Sha256::digest(&request)),
    }))?;
    write_new(attempt_dir, "op66-requested.json", &active)?;
    // A different attempt directory in this journal cannot invoke op66/67/22
    // after an uncertain current-image or submit response. A local ID has
    // already been allocated; recovery must inspect the original attempt and
    // never call submit_once again.
    hold_begin_attempt(parent, &active)?;
    let reply = operator.invoke(66, &request)?;
    write_new(attempt_dir, "op66-frame.bin", &reply)?;
    let plan = framed_payload(&reply, 66, PLAN_TAG)?;
    let plan_path = write_new(attempt_dir, "plan.bin", plan)?;
    let inspection = operator.tool(
        "inspect",
        "application-lifecycle-launch-begin-plan",
        &plan_path,
        &attempt_dir.join("plan.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspection)?;
    let (signatures, prior_create) =
        fixed.signatures(&view, plan, &request, &action, &client_operation_id, launch)?;
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
    write_new(attempt_dir, "op67-requested.bin", &pair)?;
    let reply = operator.invoke(67, &pair)?;
    write_new(attempt_dir, "op67-frame.bin", &reply)?;
    let ingress = framed_payload(&reply, 67, BEGIN_TAG)?.to_vec();
    write_new(attempt_dir, "begin-v3.bin", &ingress)?;
    let marker = json!({
        "protocol":"mini-spk-launch-begin-submit-requested-v1",
        "clientOperationId":client_operation_id,
        "authorizationOperationId":text(&view,"authorizationOperationId")?,
        "volumeIdHex":text(&view,"volumeIdHex")?,
        "ingressSha256":hex(&Sha256::digest(&ingress)),
    });
    write_new(
        attempt_dir,
        "op22-requested.json",
        &serde_json::to_vec(&marker)?,
    )?;
    let reply = operator.invoke(22, &ingress)?;
    write_new(attempt_dir, "op22-frame.bin", &reply)?;
    let outcome = framed_payload(&reply, 22, b"DREGG/NATIVE-HOST/OUTCOME/v3")?;
    let outcome_path = write_new(attempt_dir, "op22-outcome.bin", outcome)?;
    let inspection = operator.tool(
        "inspect",
        "outcome",
        &outcome_path,
        &attempt_dir.join("op22-outcome.json"),
    )?;
    let outcome: Value = serde_json::from_slice(&inspection)?;
    if text(&outcome, "type")? != "confirmed" || text(&outcome, "confirmation")? != "installed" {
        return Err(invalid("v3 BEGIN not freshly accepted"));
    }
    let receipt = |name| -> io::Result<String> {
        let value = text(&outcome, name)?;
        if !decimal(value) {
            return Err(invalid("v3 BEGIN receipt noncanonical"));
        }
        Ok(value.to_owned())
    };
    Ok(AcceptedLaunchBegin {
        ingress,
        action,
        prior_create,
        client_operation_id,
        authorization_operation_id: text(&view, "authorizationOperationId")?.to_owned(),
        volume_id_hex: text(&view, "volumeIdHex")?.to_owned(),
        snapshot_manifest: text(&view, "snapshotManifest")?.to_owned(),
        process_generation: text(&view, "processGeneration")?.to_owned(),
        process_identity_hex: text(&view, "processIdentityHex")?.to_owned(),
        transaction_id: receipt("transactionId")?,
        event_id: receipt("eventId")?,
        accepted_count: receipt("acceptedCount")?,
        image_boundary: receipt("imageBoundary")?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_native::SourceDescriptor;
    use crate::launch_descriptor_native::SourceLaunchDescriptor;
    use crate::materialize::InstalledPackage;
    use sandstorm_package::manifest::Action;
    use sandstorm_package::{manifest::Command as SpkCommand, SpkManifest};
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
        let package = Box::leak(Box::new(package));
        SourceBoundLaunch::test_pair(
            package,
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
    fn request_requires_source_owned_launch_and_exact_create_selection() {
        let launch = launch();
        let install = request_json(&LaunchBeginAction::Install, "7", &launch).unwrap();
        assert_eq!(install["createIndex"], Value::Null);
        assert_eq!(install["descriptor"], "6c61756e6368");
        let create = request_json(&LaunchBeginAction::Create(0), "7", &launch).unwrap();
        assert_eq!(create["createIndex"], "0");
        assert!(request_json(&LaunchBeginAction::Create(1), "7", &launch).is_err());
        assert!(request_json(&LaunchBeginAction::Install, "07", &launch).is_err());
        let continued = request_json(
            &LaunchBeginAction::Continue {
                created_index: "12345678901234567890".into(),
            },
            "7",
            &launch,
        )
        .unwrap();
        assert_eq!(continued["createdIndex"], "12345678901234567890");
        assert!(continued.get("createIndex").is_none());
        assert!(request_json(
            &LaunchBeginAction::Continue {
                created_index: "01".into(),
            },
            "7",
            &launch
        )
        .is_err());
    }

    #[test]
    fn v3_plan_and_ingress_reply_tags_cannot_accept_historical_payload() {
        let mut reply = ((PLAN_TAG.len() + 2) as u32).to_le_bytes().to_vec();
        reply.push(66);
        reply.extend_from_slice(PLAN_TAG);
        reply.push(1);
        assert!(framed_payload(&reply, 66, PLAN_TAG).is_ok());
        assert!(framed_payload(&reply, 67, PLAN_TAG).is_err());
        assert!(framed_payload(&reply, 66, BEGIN_TAG).is_err());
        reply.push(0);
        assert!(framed_payload(&reply, 66, PLAN_TAG).is_err());
    }

    #[test]
    fn inspected_unit_and_image_are_joined_to_signed_spk() {
        let launch = launch();
        let mut view = json!({
            "app":"8401",
            "beforeGeneration":"1",
            "processGeneration":"2",
            "processIdentityHex":hex(b"mini-spk-a8401-g2.service"),
            "imageIdentityHex":hex(&launch.descriptor().package.image_identity),
        });
        checked_physical_identity(&view, &launch).unwrap();
        view["processGeneration"] = json!("3");
        assert!(checked_physical_identity(&view, &launch).is_err());
        view["processGeneration"] = json!("2");
        view["imageIdentityHex"] = json!(hex(b"other-image"));
        assert!(checked_physical_identity(&view, &launch).is_err());
    }

    #[test]
    fn plan_pin_uses_launch_root_for_installed_package_and_exact_request() {
        let launch = launch();
        let fixed = FixedLaunchBeginSigners {
            protocol: "mini-spk-resident-begin-management-v1".into(),
            app: "8401".into(),
            package_manifest: "17".into(),
            snapshot_manifest: "18".into(),
            management_subject: "19".into(),
            signers: vec![],
        };
        let plan = b"source-plan";
        let request = b"source-request";
        let mut view = json!({
            "type":"application-lifecycle-launch-begin-plan-v1",
            "canonicalPlanHex":hex(plan),
            "canonicalRequestHex":hex(request),
            "request":{
                "type":"application-lifecycle-launch-begin-request-v1",
                "canonicalRequestHex":hex(request), "kind":"install",
                "clientOperationId":"7", "descriptorHex":hex(&launch.descriptor().canonical),
                "createIndex":null
            },
            "unsignedIngressHex":"01", "app":"8401",
            "packageManifest":"17", "snapshotManifest":"18",
            "managementSubject":"19", "authorizationOperationId":"123",
            "volumeIdHex":"a".repeat(64),
            "descriptorRoot":"22", "packageRoot":"22",
            "beforeGeneration":"1", "processGeneration":"2",
            "processIdentityHex":hex(b"mini-spk-a8401-g2.service"),
            "imageIdentityHex":hex(&launch.descriptor().package.image_identity),
            "imageBoundary":"10", "height":"11",
            "selectedCommandDigest":null, "priorCreate":null, "slots":[]
        });
        fixed
            .checked_plan_slots(
                &view,
                plan,
                request,
                &LaunchBeginAction::Install,
                "7",
                &launch,
            )
            .unwrap();
        view["packageRoot"] = json!("11");
        assert!(fixed
            .checked_plan_slots(
                &view,
                plan,
                request,
                &LaunchBeginAction::Install,
                "7",
                &launch
            )
            .is_err());
        view["packageRoot"] = json!("22");
        view["request"]["clientOperationId"] = json!("8");
        assert!(fixed
            .checked_plan_slots(
                &view,
                plan,
                request,
                &LaunchBeginAction::Install,
                "7",
                &launch
            )
            .is_err());
    }

    #[test]
    fn continue_plan_requires_retained_created_witness_and_exact_digest() {
        let launch = launch();
        let fixed = FixedLaunchBeginSigners {
            protocol: "mini-spk-resident-begin-management-v1".into(),
            app: "8401".into(),
            package_manifest: "17".into(),
            snapshot_manifest: "18".into(),
            management_subject: "19".into(),
            signers: vec![],
        };
        let action = LaunchBeginAction::Continue {
            created_index: "77".into(),
        };
        let plan = b"source-plan";
        let request = b"source-request";
        let mut view = json!({
            "type":"application-lifecycle-launch-begin-plan-v1",
            "canonicalPlanHex":hex(plan), "canonicalRequestHex":hex(request),
            "request":{
                "type":"application-lifecycle-launch-continue-request-v1",
                "canonicalRequestHex":hex(request), "kind":"continue",
                "clientOperationId":"7", "descriptorHex":hex(&launch.descriptor().canonical),
                "createdIndex":"77"
            },
            "unsignedIngressHex":"01", "app":"8401",
            "packageManifest":"17", "snapshotManifest":"18",
            "managementSubject":"19", "authorizationOperationId":"123",
            "volumeIdHex":"a".repeat(64), "descriptorRoot":"22", "packageRoot":"22",
            "beforeGeneration":"1", "processGeneration":"2",
            "processIdentityHex":hex(b"mini-spk-a8401-g2.service"),
            "imageIdentityHex":hex(&launch.descriptor().package.image_identity),
            "imageBoundary":"10", "height":"11",
            "selectedCommandDigest":"44",
            "priorCreate":{"receiptHex":"abcd","custodyHex":"ef01"}, "slots":[]
        });
        let (_, witness) = fixed
            .checked_plan_slots(&view, plan, request, &action, "7", &launch)
            .unwrap();
        let witness = witness.unwrap();
        assert_eq!(witness.receipt_hex, "abcd");
        assert_eq!(witness.custody_hex, "ef01");
        view["priorCreate"]["custodyHex"] = json!("XX");
        assert!(fixed
            .checked_plan_slots(&view, plan, request, &action, "7", &launch)
            .is_err());
        view["priorCreate"]["custodyHex"] = json!("ef01");
        view["selectedCommandDigest"] = json!("33");
        assert!(fixed
            .checked_plan_slots(&view, plan, request, &action, "7", &launch)
            .is_err());
    }

    #[test]
    fn uncertain_begin_attempt_blocks_new_client_id_in_same_journal() {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let parent = std::env::temp_dir().join(format!(
            "spk-v3-begin-active-{}-{stamp}",
            std::process::id()
        ));
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(&parent)
            .unwrap();
        hold_begin_attempt(&parent, b"first-request").unwrap();
        assert!(hold_begin_attempt(&parent, b"second-request").is_err());
        assert_eq!(
            std::fs::read(parent.join("lifecycle-begin-v3-active.json")).unwrap(),
            b"first-request"
        );
        std::fs::remove_dir_all(parent).unwrap();
    }
}
