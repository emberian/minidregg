//! Physical START/INSTALL observation and pinned completion-custodian signature.
//!
//! Rust observes the running unit or a materialized protected image, signs
//! only source-authored frames and headers, and retains one-shot op38 evidence.
//! It does not mint a completion or bind HTTP; START requires a fresh installed
//! receipt and physical recheck before opening its private entrance.
#![allow(dead_code)] // Resident lifecycle route is still staged.

use crate::dispatch_author::{private_signing_key, SignerPin};
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::hostd::Journal;
use crate::sandbox::open_protected_directory;
use ed25519_dalek::Signer;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{DirBuilder, File};
use std::io::{self, Read};
use std::os::unix::fs::DirBuilderExt;
use std::path::{Path, PathBuf};

const MAX_BEGIN: usize = 12_102_759;
const MAX_REPORT: usize = 12_102_759;
const MAX_FRAME: usize = 12_102_760;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn hex(bytes: &[u8]) -> String {
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(result, "{byte:02x}").expect("writing to String");
    }
    result
}

fn unhex(value: &str) -> io::Result<Vec<u8>> {
    if !value.len().is_multiple_of(2)
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(invalid("noncanonical completion hex"));
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let text = std::str::from_utf8(pair).map_err(|_| invalid("completion hex pair"))?;
            u8::from_str_radix(text, 16).map_err(|_| invalid("completion hex pair"))
        })
        .collect()
}

fn canonical_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn pinned_context(
    operator: &PrivateOperator,
    seed: &Path,
    semantics: &str,
) -> io::Result<(String, String)> {
    // The Host's own config is the genesis-bound source of domain, semantics,
    // and completion custodian public key. A request cannot supply them.
    let config: Value = serde_json::from_slice(&operator.pinned_config()?)?;
    let object = config
        .as_object()
        .ok_or_else(|| invalid("Mini Host config is not an object"))?;
    let decimal = |name: &str| -> io::Result<String> {
        let value = object
            .get(name)
            .ok_or_else(|| invalid("Mini Host completion context absent"))?;
        let value = value
            .as_str()
            .map(str::to_owned)
            .or_else(|| value.as_u64().map(|number| number.to_string()))
            .ok_or_else(|| invalid("Mini Host completion context malformed"))?;
        if !canonical_decimal(&value) {
            return Err(invalid("Mini Host completion context noncanonical"));
        }
        Ok(value)
    };
    let key = object
        .get("completionCustodianKey")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("Mini Host completion custodian key absent"))?;
    let signer = private_signing_key(seed)?;
    if hex(&signer.verifying_key().to_bytes()) != key {
        return Err(invalid(
            "completion signer differs from genesis-bound Mini key",
        ));
    }
    if !canonical_decimal(semantics) {
        return Err(invalid("completion semantics noncanonical"));
    }
    // The source author validates this physical profile against BEGIN-v2.
    Ok((decimal("domain")?, semantics.to_owned()))
}

pub(crate) fn preflight_custodian(
    operator: &PrivateOperator,
    seed: &Path,
    semantics: &str,
) -> io::Result<()> {
    pinned_context(operator, seed, semantics).map(|_| ())
}

fn fresh_nonce() -> io::Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")?.read_exact(&mut bytes)?;
    let nonce = u128::from_le_bytes(bytes);
    if nonce == 0 {
        return Err(invalid("zero physical report nonce"));
    }
    Ok(nonce.to_string())
}

pub(crate) struct PreparedRunningReport {
    pub signed_report: Vec<u8>,
    pub attempt_dir: PathBuf,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedCompletionSigners {
    protocol: String,
    app: String,
    package_manifest: String,
    management_subject: String,
    signers: Vec<SignerPin>,
}

fn decimal(value: &Value) -> io::Result<String> {
    let value = value
        .as_str()
        .map(str::to_owned)
        .or_else(|| value.as_u64().map(|number| number.to_string()))
        .ok_or_else(|| invalid("completion management number malformed"))?;
    if !canonical_decimal(&value) {
        return Err(invalid("completion management number noncanonical"));
    }
    Ok(value)
}

fn text_field<'a>(value: &'a Value, name: &str) -> io::Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("completion signer field absent"))
}

impl FixedCompletionSigners {
    pub(crate) fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-completion-management-v1"
            || self.signers.is_empty()
            || self.signers.len() > 64
            || ![&self.app, &self.package_manifest, &self.management_subject]
                .iter()
                .all(|value| canonical_decimal(value))
        {
            return Err(invalid("fixed completion signer profile refused"));
        }
        let config: Value = serde_json::from_slice(&operator.pinned_config()?)?;
        let manager = config
            .get("completionManagement")
            .ok_or_else(|| invalid("Mini completion management pin absent"))?;
        for (field, expected) in [
            ("app", &self.app),
            ("packageManifest", &self.package_manifest),
            ("managementSubject", &self.management_subject),
        ] {
            if decimal(
                manager
                    .get(field)
                    .ok_or_else(|| invalid("Mini management pin field absent"))?,
            )? != *expected
            {
                return Err(invalid("fixed signer differs from Mini management pin"));
            }
        }
        let management_key = decimal(
            manager
                .get("managementKeyId")
                .ok_or_else(|| invalid("Mini management key pin absent"))?,
        )?;
        for pin in &self.signers {
            if pin.key_id != management_key {
                return Err(invalid(
                    "completion signer differs from Mini management key",
                ));
            }
            open_protected_directory(
                pin.seed_path
                    .parent()
                    .ok_or_else(|| invalid("management signer parent absent"))?,
                app_uid,
                false,
            )?;
        }
        Ok(())
    }

    fn sign_plan(&self, inspection: &Value, plan: &[u8]) -> io::Result<Value> {
        let field = |name: &str| -> io::Result<&str> {
            inspection
                .get(name)
                .and_then(Value::as_str)
                .ok_or_else(|| invalid("completion plan inspection field absent"))
        };
        if field("type")? != "application-lifecycle-completion-operator-plan-v1"
            || field("canonicalPlan")? != hex(plan)
            || field("app")? != self.app
            || field("packageManifest")? != self.package_manifest
            || field("managementSubject")? != self.management_subject
        {
            return Err(invalid(
                "completion plan differs from fixed management custody",
            ));
        }
        let slots = inspection
            .get("slots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("completion plan slots absent"))?;
        if slots.len() != self.signers.len() {
            return Err(invalid("completion signer slot count differs"));
        }
        let mut signed = Vec::with_capacity(slots.len());
        for (slot, pin) in slots.iter().zip(&self.signers) {
            let signing = slot
                .get("signing")
                .ok_or_else(|| invalid("completion signing inspection absent"))?;
            let header = text_field(slot, "header")?;
            if text_field(slot, "role")? != pin.role
                || text_field(slot, "index")? != pin.index
                || signing.get("decoded").and_then(Value::as_bool) != Some(true)
                || text_field(signing, "canonical")? != header
                || text_field(signing, "keyId")? != pin.key_id
                || text_field(signing, "keyEpoch")? != pin.key_epoch
                || text_field(signing, "algorithm")? != "1"
            {
                return Err(invalid("completion slot differs from fixed signer"));
            }
            let header = unhex(header)?;
            if header.is_empty() || header.len() > 65_536 {
                return Err(invalid("completion signing header bound refused"));
            }
            let key = private_signing_key(&pin.seed_path)?;
            if hex(&key.verifying_key().to_bytes()) != pin.public_key_hex {
                return Err(invalid("completion management seed/public pin differs"));
            }
            signed.push(Value::String(hex(&key.sign(&header).to_bytes())));
        }
        Ok(Value::Array(signed))
    }
}

fn reply_payload(reply: &[u8], opcode: u8) -> io::Result<&[u8]> {
    if reply.len() < 6 {
        return Err(invalid("truncated Mini completion reply"));
    }
    let length = u32::from_le_bytes(reply[..4].try_into().unwrap()) as usize;
    if !(2..=MAX_FRAME).contains(&length) || length + 4 != reply.len() || reply[4] != opcode {
        return Err(invalid("Mini completion reply refused"));
    }
    Ok(&reply[5..])
}

/// Assemble a signed completion ingress from the fresh source-owned current
/// plan. This still does not submit op38 or authorize opening HTTP. Op44 and
/// op45 refusal/uncertainty retain the attempt directory; there is no retry.
pub(crate) fn assemble_current_completion(
    operator: &PrivateOperator,
    begin: &[u8],
    claim_ingress: &[u8],
    signed_report: &[u8],
    fixed: &FixedCompletionSigners,
    app_uid: u32,
    attempt_dir: &Path,
) -> io::Result<Vec<u8>> {
    fixed.validate(operator, app_uid)?;
    private_dir(
        attempt_dir
            .parent()
            .ok_or_else(|| invalid("completion attempt parent absent"))?,
    )?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let source = json!({"begin":hex(begin), "claimIngress":hex(claim_ingress),
        "signedReport":hex(signed_report)});
    let input = write_new(
        attempt_dir,
        "operator-request.json",
        &serde_json::to_vec(&source)?,
    )?;
    let request = operator.tool(
        "author",
        "application-lifecycle-completion-operator-request",
        &input,
        &attempt_dir.join("operator-request.bin"),
    )?;
    write_new(attempt_dir, "op44-requested.bin", &request)?;
    let reply = operator.invoke(44, &request)?;
    write_new(attempt_dir, "op44-frame.bin", &reply)?;
    let plan = reply_payload(&reply, 44)?;
    let plan_path = write_new(attempt_dir, "operator-plan.bin", plan)?;
    let inspected = operator.tool(
        "inspect",
        "application-lifecycle-completion-operator-plan",
        &plan_path,
        &attempt_dir.join("operator-plan.json"),
    )?;
    let inspection: Value = serde_json::from_slice(&inspected)?;
    let signatures = fixed.sign_plan(&inspection, plan)?;
    let signatures_input = write_new(
        attempt_dir,
        "signatures.json",
        &serde_json::to_vec(&signatures)?,
    )?;
    let signatures_bytes = operator.tool(
        "signatures",
        "",
        &signatures_input,
        &attempt_dir.join("signatures.bin"),
    )?;
    let mut pair = Vec::with_capacity(4 + plan.len() + signatures_bytes.len());
    pair.extend_from_slice(&(plan.len() as u32).to_le_bytes());
    pair.extend_from_slice(plan);
    pair.extend_from_slice(&signatures_bytes);
    write_new(attempt_dir, "op45-requested.bin", &pair)?;
    let reply = operator.invoke(45, &pair)?;
    write_new(attempt_dir, "op45-frame.bin", &reply)?;
    let ingress = reply_payload(&reply, 45)?.to_vec();
    write_new(attempt_dir, "completion-ingress.bin", &ingress)?;
    Ok(ingress)
}

pub(crate) struct ConfirmedCompletion {
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub image_boundary: String,
}

/// A durable submit marker precedes the one op38 send. A lost reply remains
/// uncertain and cannot be converted from op39 lookup into permission to
/// expose HTTP. Only a fresh source-inspected `installed` response qualifies.
pub(crate) fn submit_completion_once(
    operator: &PrivateOperator,
    journal: &Journal,
    ingress: &[u8],
    attempt_dir: &Path,
) -> io::Result<ConfirmedCompletion> {
    submit_completion_inner(operator, Some(journal), ingress, attempt_dir)
}

/// INSTALL has no app process or Running journal. Its only physical action is
/// the separately bounded, root-owned image publication; the caller verifies
/// that exact image before invoking this one-shot native completion.
pub(crate) fn submit_materialized_completion_once(
    operator: &PrivateOperator,
    ingress: &[u8],
    attempt_dir: &Path,
) -> io::Result<ConfirmedCompletion> {
    submit_completion_inner(operator, None, ingress, attempt_dir)
}

fn submit_completion_inner(
    operator: &PrivateOperator,
    journal: Option<&Journal>,
    ingress: &[u8],
    attempt_dir: &Path,
) -> io::Result<ConfirmedCompletion> {
    if ingress.is_empty() || ingress.len() >= MAX_FRAME {
        return Err(invalid("completion ingress bound refused"));
    }
    private_dir(
        attempt_dir
            .parent()
            .ok_or_else(|| invalid("completion submit parent absent"))?,
    )?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    write_new(attempt_dir, "ingress.bin", ingress)?;
    let marker = json!({"protocol":"mini-spk-completion-submit-requested-v1",
        "ingressSha256":hex(&Sha256::digest(ingress))});
    write_new(
        attempt_dir,
        "op38-requested.json",
        &serde_json::to_vec(&marker)?,
    )?;
    if let Some(journal) = journal {
        journal
            .read()?
            .ok_or_else(|| invalid("resident journal absent"))?
            .verify_running_instance()?;
    }
    let reply = operator.invoke(38, ingress)?;
    write_new(attempt_dir, "op38-frame.bin", &reply)?;
    let payload = reply_payload(&reply, 38)?;
    let payload_path = write_new(attempt_dir, "op38-outcome.bin", payload)?;
    let inspected = operator.tool(
        "inspect",
        "outcome",
        &payload_path,
        &attempt_dir.join("op38-outcome.json"),
    )?;
    let outcome: Value = serde_json::from_slice(&inspected)?;
    if outcome.get("type").and_then(Value::as_str) != Some("confirmed")
        || outcome.get("confirmation").and_then(Value::as_str) != Some("installed")
    {
        return Err(invalid(
            "native lifecycle completion was not freshly confirmed",
        ));
    }
    let field = |name: &str| -> io::Result<String> {
        let value = outcome
            .get(name)
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("completion receipt field absent"))?;
        if !canonical_decimal(value) {
            return Err(invalid("completion receipt noncanonical"));
        }
        Ok(value.to_owned())
    };
    let confirmed = ConfirmedCompletion {
        transaction_id: field("transactionId")?,
        event_id: field("eventId")?,
        accepted_count: field("acceptedCount")?,
        image_boundary: field("imageBoundary")?,
    };
    if let Some(journal) = journal {
        journal
            .read()?
            .ok_or_else(|| invalid("resident journal absent"))?
            .verify_running_instance()?;
    }
    Ok(confirmed)
}

/// The source author derives the prospective Manifest from the original
/// signed BEGIN and exact committed-v2 claim. The operator signs only the
/// source-produced frame after verifying the live manager/cgroup observation.
/// A fresh private directory is durable before any helper invocation; errors
/// leave it intact for review and never imply physical completion.
pub(crate) fn prepare_running_report(
    operator: &PrivateOperator,
    journal: &Journal,
    begin: &[u8],
    claim: &[u8],
    custodian_seed: &Path,
    semantics: &str,
    attempt_dir: &Path,
) -> io::Result<PreparedRunningReport> {
    if begin.is_empty() || begin.len() > MAX_BEGIN || claim.is_empty() || claim.len() > MAX_REPORT {
        return Err(invalid("physical completion source frame size refused"));
    }
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("physical report attempt parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let (domain, semantics) = pinned_context(operator, custodian_seed, semantics)?;
    let record = journal
        .read()?
        .ok_or_else(|| invalid("resident Running record absent"))?;
    record.verify_running_instance()?;
    let invocation = record
        .invocation_id()
        .ok_or_else(|| invalid("manager InvocationID absent"))?;
    let cgroup = record
        .control_group()
        .ok_or_else(|| invalid("manager ControlGroup absent"))?;
    let child = record
        .child_pid
        .ok_or_else(|| invalid("resident app child PID absent"))?;
    let unit = record.unit().as_bytes();
    let image = record.image_identity();
    let report_source = json!({
        "begin":hex(begin), "claim":hex(claim), "nonce":fresh_nonce()?,
        "unit":hex(unit), "materializedImage":image, "outcome":"running",
        "invocationId":hex(invocation.as_bytes()), "controlGroup":hex(cgroup.as_bytes()),
        "pid":child.to_string(), "stopAudit":""
    });
    let source = write_new(
        attempt_dir,
        "report-source.json",
        &serde_json::to_vec(&report_source)?,
    )?;
    let report = operator.tool(
        "author",
        "application-lifecycle-completion-report",
        &source,
        &attempt_dir.join("report.bin"),
    )?;
    let frame_source = json!({"domain":domain,"semantics":semantics,
        "begin":hex(begin),"report":hex(&report)});
    let frame_input = write_new(
        attempt_dir,
        "signing-frame-source.json",
        &serde_json::to_vec(&frame_source)?,
    )?;
    let frame = operator.tool(
        "author",
        "application-lifecycle-completion-signing-frame",
        &frame_input,
        &attempt_dir.join("signing-frame.bin"),
    )?;
    record.verify_running_instance()?;
    let signature = private_signing_key(custodian_seed)?.sign(&frame).to_bytes();
    let signed_source = json!({"begin":hex(begin),"report":hex(&report),
        "signature":hex(&signature)});
    let signed_input = write_new(
        attempt_dir,
        "signed-report-source.json",
        &serde_json::to_vec(&signed_source)?,
    )?;
    let signed_report = operator.tool(
        "author",
        "application-lifecycle-completion-signed-report",
        &signed_input,
        &attempt_dir.join("signed-report.bin"),
    )?;
    Ok(PreparedRunningReport {
        signed_report,
        attempt_dir: attempt_dir.to_path_buf(),
    })
}

/// Record an installed, signature-verified image without claiming an app
/// process exists. The caller must compare the published image to the exact
/// pre-ingest SPK and the retained op26 INSTALL frame before invoking this.
/// Mini derives the installed Manifest from that original BEGIN/claim; Rust
/// cannot supply or alter Manifest bytes in this report.
pub(crate) struct MaterializedObservation<'a> {
    pub unit: &'a str,
    pub image_identity: &'a [u8],
}

pub(crate) fn prepare_materialized_report(
    operator: &PrivateOperator,
    begin: &[u8],
    claim: &[u8],
    observed: MaterializedObservation<'_>,
    custodian_seed: &Path,
    semantics: &str,
    attempt_dir: &Path,
) -> io::Result<PreparedRunningReport> {
    if begin.is_empty()
        || begin.len() > MAX_BEGIN
        || claim.is_empty()
        || claim.len() > MAX_REPORT
        || observed.unit.is_empty()
        || observed.unit.len() > 256
        || observed.image_identity.len() != b"DREGG/SPK-IMAGE/v1".len() + 32
        || !observed.image_identity.starts_with(b"DREGG/SPK-IMAGE/v1")
    {
        return Err(invalid(
            "materialized report identity or source bound refused",
        ));
    }
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("materialized report attempt parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let (domain, semantics) = pinned_context(operator, custodian_seed, semantics)?;
    let report_source = json!({
        "begin":hex(begin), "claim":hex(claim), "nonce":fresh_nonce()?,
        "unit":hex(observed.unit.as_bytes()),
        "materializedImage":hex(observed.image_identity),
        "outcome":"materialized", "invocationId":"", "controlGroup":"",
        "pid":"0", "stopAudit":""
    });
    let source = write_new(
        attempt_dir,
        "report-source.json",
        &serde_json::to_vec(&report_source)?,
    )?;
    let report = operator.tool(
        "author",
        "application-lifecycle-completion-report",
        &source,
        &attempt_dir.join("report.bin"),
    )?;
    let frame_input = write_new(
        attempt_dir,
        "signing-frame-source.json",
        &serde_json::to_vec(&json!({"domain":domain,"semantics":semantics,
            "begin":hex(begin),"report":hex(&report)}))?,
    )?;
    let frame = operator.tool(
        "author",
        "application-lifecycle-completion-signing-frame",
        &frame_input,
        &attempt_dir.join("signing-frame.bin"),
    )?;
    let signature = private_signing_key(custodian_seed)?.sign(&frame).to_bytes();
    let signed_input = write_new(
        attempt_dir,
        "signed-report-source.json",
        &serde_json::to_vec(&json!({"begin":hex(begin),"report":hex(&report),
            "signature":hex(&signature)}))?,
    )?;
    let signed_report = operator.tool(
        "author",
        "application-lifecycle-completion-signed-report",
        &signed_input,
        &attempt_dir.join("signed-report.bin"),
    )?;
    Ok(PreparedRunningReport {
        signed_report,
        attempt_dir: attempt_dir.to_path_buf(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frame(opcode: u8, payload: &[u8]) -> Vec<u8> {
        let mut out = ((payload.len() + 1) as u32).to_le_bytes().to_vec();
        out.push(opcode);
        out.extend_from_slice(payload);
        out
    }

    #[test]
    fn completion_plan_and_outcome_are_exact_private_opcodes() {
        let plan = frame(
            44,
            b"DREGG/APPLICATION/LIFECYCLE-COMPLETION-OPERATOR-PLAN/v1",
        );
        assert_eq!(reply_payload(&plan, 44).unwrap(), &plan[5..]);
        assert!(reply_payload(&plan, 45).is_err());
        let mut trailing = plan.clone();
        trailing.push(0);
        assert!(reply_payload(&trailing, 44).is_err());
        let outcome = frame(38, b"DREGG/NATIVE-HOST/OUTCOME/v2");
        assert!(reply_payload(&outcome, 44).is_err());
        assert_eq!(reply_payload(&outcome, 38).unwrap(), &outcome[5..]);
    }

    #[test]
    fn canonical_completion_ids_refuse_aliases() {
        assert!(canonical_decimal("0"));
        assert!(canonical_decimal("18446744073709551616"));
        for alias in ["", "00", "01", "+1", "-1", "1.0", " 1"] {
            assert!(!canonical_decimal(alias));
        }
        assert!(unhex("aa00ff").is_ok());
        assert!(unhex("AA00ff").is_err());
    }
}
