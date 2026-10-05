//! Governed repeat-CREATE BEGIN (event69) after a failed first-create START
//! that a failed-START recovery (event66) reconciled to a stopped app.
//!
//! Modeled line by line on `lifecycle_v3_native`. The v3 BEGIN for this
//! create refuses forever (its first-attempt nullifier is consumed); the only
//! lawful repeat names the exact accepted recovery by its native index and
//! canonical ingress. Selection is decided from protected local evidence
//! before any Mini call, and v3 attempt evidence is never touched: every v4
//! artifact lives in its own per-generation directory and marker.
//!
//! Wire (CONTRACT-V4-WIRE): op66 plan / op67 assemble / op22 submit /
//! op23 receipt-only lookup. Uncertainty is never resubmitted.
#![allow(dead_code)] // The retry lookup arm is reached only by operator recovery.

use crate::dispatch_author::SignerPin;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::lifecycle_v3_native::{
    decimal, framed_payload, hex, lowercase_hex, sign_pinned_slots, text, AcceptedLaunchBegin,
    LaunchBeginAction,
};
use crate::operation_ledger::allocate_operation_id;
use crate::resident_launch::SourceBoundLaunch;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::Path;

const MAX_FRAME: usize = 12_102_760;
const MAX_RECOVERY_INGRESS: u64 = 12_102_759;
const MAX_RECOVERY_RECORD: u64 = 16 * 1024;

/// Host/ApplicationLifecycleLaunchBeginAuthoring.lean:46-48 (requestCodec frame).
#[cfg(test)]
pub(crate) const V3_LAUNCH_REQUEST_TAG: &[u8] = b"DREGG/APPLICATION/LAUNCH-BEGIN-OPERATOR-REQUEST/v1";
/// Host/ApplicationLifecycleRetryBeginV4Authoring.lean:36-37 (requestCodec frame).
pub(crate) const REQUEST_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-BEGIN-OPERATOR-REQUEST/v4";
/// Host/ApplicationLifecycleRetryBeginV4Authoring.lean:53-55 (planCodec frame).
const PLAN_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-BEGIN-OPERATOR-PLAN/v4";
/// Kernel/ApplicationLifecycleRetryBeginV4Ingress.lean:28-29 (codec frame).
pub(crate) const BEGIN_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-BEGIN-INGRESS/v4";
/// Kernel/ApplicationFailedStartRecoveryIngress.lean:36-39 (codec frame).
pub(crate) const RECOVERY_INGRESS_TAG: &[u8] =
    b"DREGG/APPLICATION/FAILED-START-RECOVERY-INGRESS/v1";
/// Kernel/ApplicationFailedCreateRetryEvidence.lean:33-35 (selectorCodec frame).
pub(crate) const SELECTOR_TAG: &[u8] = b"DREGG/APPLICATION/FAILED-CREATE-RETRY-SELECTOR/v1";
pub(crate) const OUTCOME_TAG: &[u8] = b"DREGG/NATIVE-HOST/OUTCOME/v4";

/// Host inspect kinds (CONTRACT-V4-WIRE) and the `type` values
/// Host/ApplicationLifecycleRetryBeginV4Inspection.lean returns.
const REQUEST_INSPECT_KIND: &str = "application-lifecycle-retry-begin-request";
const PLAN_INSPECT_KIND: &str = "application-lifecycle-retry-begin-plan";
pub(crate) const REQUEST_VIEW_TYPE: &str = "application-lifecycle-retry-begin-request-v4";
pub(crate) const PLAN_VIEW_TYPE: &str = "application-lifecycle-retry-begin-plan-v4";

/// Retained by the failed-START recovery writer in the failed generation.
pub(crate) const RECOVERED_RECORD: &str = "failed-start-recovered-v1.json";
pub(crate) const RECOVERY_DIR: &str = "failed-start-recovery-v1";
const RECOVERED_PROTOCOL: &str = "mini-spk-failed-start-recovered-v1";

/// Per-generation v4 artifacts. All are siblings of the v3 attempt
/// directories under the resident journal and never share a name with them.
pub(crate) const ACTIVE_MARKER: &str = "lifecycle-begin-retry-v4-active.json";
pub(crate) const BEGIN_ATTEMPT_DIR: &str = "begin-attempt-retry-v4";
pub(crate) const BEGIN_INGRESS_FILE: &str = "begin-retry-v4.bin";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

// ---------------------------------------------------------------------------
// StreamCodec encoders (Compiler/Tower256ConcreteBackend.lean)

/// `StreamCodec.nat` (Tower256ConcreteBackend.lean:151-206): base-255
/// little-endian digits of a canonical decimal, then terminator byte 255.
/// Zero is the single byte 255 (`Nat.digits 255 0 = []`).
pub(crate) fn encode_nat_decimal(value: &str) -> io::Result<Vec<u8>> {
    if !decimal(value) {
        return Err(invalid("v4 retry natural is not canonical decimal"));
    }
    let mut digits: Vec<u32> = value.bytes().map(|byte| u32::from(byte - b'0')).collect();
    let mut encoded = Vec::new();
    while digits.iter().any(|digit| *digit != 0) {
        let mut remainder = 0u32;
        let mut quotient = Vec::with_capacity(digits.len());
        for digit in &digits {
            let current = remainder * 10 + digit;
            let next = current / 255;
            remainder = current % 255;
            if !(quotient.is_empty() && next == 0) {
                quotient.push(next);
            }
        }
        encoded.push(remainder as u8);
        digits = quotient;
    }
    encoded.push(255);
    Ok(encoded)
}

pub(crate) fn encode_nat_usize(mut value: usize) -> Vec<u8> {
    let mut encoded = Vec::new();
    while value != 0 {
        encoded.push((value % 255) as u8);
        value /= 255;
    }
    encoded.push(255);
    encoded
}

/// `bytesStream` (Tower256ConcreteBackend.lean:291-293): nat length, then bytes.
pub(crate) fn encode_bytes(bytes: &[u8]) -> Vec<u8> {
    let mut encoded = encode_nat_usize(bytes.len());
    encoded.extend_from_slice(bytes);
    encoded
}

/// Canonical decimal `count - 1`; refuses zero and noncanonical input.
pub(crate) fn decimal_predecessor(count: &str) -> io::Result<String> {
    if !decimal(count) || count == "0" {
        return Err(invalid("v4 retry accepted count refused"));
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
    String::from_utf8(bytes[first..].to_vec()).map_err(|_| invalid("v4 retry index malformed"))
}

// ---------------------------------------------------------------------------
// Selection: v3 create, v3 continue, or v4 repeat create

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RecoveredOutcome {
    #[serde(rename = "type")]
    kind: String,
    confirmation: String,
    accepted_count: String,
    event_id: String,
    transaction_id: String,
    world_root: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RecoveredRecord {
    protocol: String,
    app: String,
    generation: String,
    ingress_sha256: String,
    outcome: RecoveredOutcome,
    reconciled_generation: String,
}

/// The exact admitted failed-START recovery a v4 retry names
/// (Kernel/ApplicationFailedCreateRetryEvidence.lean:20-23 `Selector`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RetrySelection {
    pub failed_generation: u64,
    pub before_generation: u64,
    /// Native accepted index of the recovery record (`acceptedCount - 1`).
    pub recovery_index: String,
    /// `ApplicationFailedStartRecoveryIngress.codec` bytes (framed), exactly
    /// as retained and admitted.
    pub recovery_ingress: Vec<u8>,
    pub recovery_ingress_sha256: String,
    pub record_sha256: String,
}

impl RetrySelection {
    /// Pure check of the retained recovery record and ingress for app
    /// `app`, failed generation `failed` and current before-generation
    /// `before`. Refuses rather than falls back once a record is present.
    pub(crate) fn from_retained(
        record: &[u8],
        ingress: &[u8],
        app: u64,
        failed: u64,
        before: u64,
    ) -> io::Result<Self> {
        let parsed: RecoveredRecord = serde_json::from_slice(record)?;
        let outcome = &parsed.outcome;
        if parsed.protocol != RECOVERED_PROTOCOL
            || parsed.app != app.to_string()
            || parsed.generation != failed.to_string()
            || outcome.kind != "confirmed"
            || !matches!(outcome.confirmation.as_str(), "installed" | "replayed")
            || !decimal(&outcome.accepted_count)
            || !decimal(&outcome.event_id)
            || !decimal(&outcome.transaction_id)
            || !decimal(&outcome.world_root)
            || parsed.ingress_sha256.len() != 64
            || !lowercase_hex(&parsed.ingress_sha256)
        {
            return Err(invalid("failed-START recovery record refused"));
        }
        if parsed.reconciled_generation != before.to_string() {
            return Err(invalid(
                "failed-START recovery reconciled a different generation",
            ));
        }
        if hex(&Sha256::digest(ingress)) != parsed.ingress_sha256 {
            return Err(invalid(
                "failed-START recovery ingress differs from recorded SHA-256",
            ));
        }
        if !ingress.starts_with(RECOVERY_INGRESS_TAG)
            || ingress.len() <= RECOVERY_INGRESS_TAG.len()
            || ingress.len() as u64 > MAX_RECOVERY_INGRESS
        {
            return Err(invalid("failed-START recovery ingress frame refused"));
        }
        Ok(Self {
            failed_generation: failed,
            before_generation: before,
            recovery_index: decimal_predecessor(&outcome.accepted_count)?,
            recovery_ingress: ingress.to_vec(),
            recovery_ingress_sha256: parsed.ingress_sha256.clone(),
            record_sha256: hex(&Sha256::digest(record)),
        })
    }

    /// `selectorStream` (ApplicationFailedCreateRetryEvidence.lean:25-31):
    /// `nat recoveryIndex ++ ingressStream recovery`. The ingress stream is
    /// the retained `codec` bytes without their frame
    /// (`NativeHostCodec.framedRaw`: `frame ++ stream.encode`).
    pub(crate) fn selector_stream(&self) -> io::Result<Vec<u8>> {
        let stream = self
            .recovery_ingress
            .strip_prefix(RECOVERY_INGRESS_TAG)
            .filter(|stream| !stream.is_empty())
            .ok_or_else(|| invalid("failed-START recovery ingress frame refused"))?;
        let mut selector = encode_nat_decimal(&self.recovery_index)?;
        selector.extend_from_slice(stream);
        Ok(selector)
    }

    /// `Selector.canonicalBytes` = `selectorCodec.encode`
    /// (ApplicationFailedCreateRetryEvidence.lean:33-38): frame ++ stream.
    pub(crate) fn selector_canonical(&self) -> io::Result<Vec<u8>> {
        let mut canonical = SELECTOR_TAG.to_vec();
        canonical.extend_from_slice(&self.selector_stream()?);
        Ok(canonical)
    }
}

/// `mini-spk-s{store}-a{app}-g{generation}.service`, the only unit grammar a
/// resident config accepts for the generation it is about to claim.
pub(crate) fn unit_generation(unit: &str, app: u64) -> io::Result<u64> {
    let (_, _, generation) = crate::broker::parse_resident_unit(unit)
        .filter(|(_, unit_app, _)| *unit_app == app.to_string())
        .ok_or_else(|| invalid("resident unit is not this app's generation unit"))?;
    generation
        .parse::<u64>()
        .map_err(|_| invalid("resident unit generation exceeds range"))
}

fn retained(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || metadata.nlink() != 1
        || metadata.uid() != unsafe { libc::geteuid() }
        || metadata.permissions().mode() & 0o777 != 0o600
        || metadata.len() == 0
        || metadata.len() > max
    {
        return Err(invalid("failed-START recovery artifact identity refused"));
    }
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let opened = file.metadata()?;
    if opened.dev() != metadata.dev() || opened.ino() != metadata.ino() {
        return Err(invalid("failed-START recovery artifact changed"));
    }
    let mut bytes = Vec::with_capacity(metadata.len() as usize);
    file.by_ref().take(max + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != metadata.len() {
        return Err(invalid("failed-START recovery artifact length changed"));
    }
    Ok(bytes)
}

/// Pure choice. Continue never retries; a create retries only when the
/// generation it would claim is `before + 1` and the failed generation
/// `before - 1` retained a recovery that reconciled to exactly `before`
/// (ApplicationFailedCreateRetryEvidence.lean:157-163,
/// `bindingMatches_stopped_generation`).
pub(crate) fn retry_generations(create: bool, generation: u64) -> Option<(u64, u64)> {
    if !create {
        return None;
    }
    let before = generation.checked_sub(1)?;
    let failed = before.checked_sub(1)?;
    if failed == 0 {
        return None;
    }
    Some((failed, before))
}

/// Selects the lawful BEGIN for a resident START. `Ok(None)` keeps the v3
/// path unchanged. A present recovery record that does not match exactly is
/// refused: v3 would refuse the same create forever, and a malformed record
/// is not evidence of absence.
pub(crate) fn select_retry(
    journal_dir: &Path,
    unit: &str,
    app: u64,
    create: bool,
) -> io::Result<Option<RetrySelection>> {
    let generation = unit_generation(unit, app)?;
    let Some((failed, before)) = retry_generations(create, generation) else {
        return Ok(None);
    };
    let apps = journal_dir
        .parent()
        .ok_or_else(|| invalid("resident journal parent absent"))?;
    let failed_dir = apps.join(format!("g{failed}"));
    let record_path = failed_dir.join(RECOVERED_RECORD);
    let record = match fs::symlink_metadata(&record_path) {
        Ok(_) => retained(&record_path, MAX_RECOVERY_RECORD)?,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error),
    };
    private_dir(&failed_dir)?;
    let recovery_dir = failed_dir.join(RECOVERY_DIR);
    private_dir(&recovery_dir)?;
    let ingress = retained(&recovery_dir.join("ingress.bin"), MAX_RECOVERY_INGRESS)?;
    RetrySelection::from_retained(&record, &ingress, app, failed, before).map(Some)
}

/// `requestStream` (Host/ApplicationLifecycleRetryBeginV4Authoring.lean:29-37):
/// `REQUEST_TAG ++ LaunchBeginAuthoring.requestStream launch ++ selectorStream`.
/// Test-only hand-checked expectation of what the Host author kind emits.
#[cfg(test)]
pub(crate) fn retry_request_bytes(
    launch_request: &[u8],
    selection: &RetrySelection,
) -> io::Result<Vec<u8>> {
    let launch = launch_request
        .strip_prefix(V3_LAUNCH_REQUEST_TAG)
        .filter(|stream| !stream.is_empty())
        .ok_or_else(|| invalid("v4 retry launch request frame refused"))?;
    let selector = selection.selector_stream()?;
    let mut request = Vec::with_capacity(REQUEST_TAG.len() + launch.len() + selector.len());
    request.extend_from_slice(REQUEST_TAG);
    request.extend_from_slice(launch);
    request.extend_from_slice(&selector);
    if request.len() >= MAX_FRAME {
        return Err(invalid("v4 retry BEGIN request exceeds frame"));
    }
    Ok(request)
}

/// Every Host view that carries a Selector names it by index, by the full
/// canonical recovery ingress and by the canonical selector bytes
/// (Host/ApplicationLifecycleRetryBeginV4Inspection.lean:37-41
/// `selectorFields`). The SHA-256 was already checked against the retained
/// record in `RetrySelection::from_retained`; these must equal the very bytes
/// that check admitted.
pub(crate) fn checked_retry_fields(view: &Value, selection: &RetrySelection) -> io::Result<()> {
    if text(view, "retryRecoveryIndex")? != selection.recovery_index
        || text(view, "retryRecoveryIngressHex")? != hex(&selection.recovery_ingress)
        || text(view, "retrySelectorHex")? != hex(&selection.selector_canonical()?)
    {
        return Err(invalid("v4 retry view names a different recovery"));
    }
    Ok(())
}

/// Host/Json.lean `retryBeginOperatorRequest`: kind is fixed START; the
/// selector is the recovery index and the full canonical recovery ingress.
fn create_request_json(
    create_index: usize,
    client_operation_id: &str,
    launch: &SourceBoundLaunch<'_>,
    selection: &RetrySelection,
) -> io::Result<Value> {
    if !decimal(client_operation_id)
        || launch.descriptor().canonical.is_empty()
        || launch.descriptor().canonical.len() >= MAX_FRAME
        || launch.descriptor().create_digests.get(create_index).is_none()
    {
        return Err(invalid("v4 retry client operation or descriptor refused"));
    }
    Ok(json!({
        "clientOperationId":client_operation_id,
        "descriptor":hex(&launch.descriptor().canonical),
        "createIndex":create_index.to_string(),
        "retry":{
            "recoveryIndex":selection.recovery_index,
            "recoveryIngress":hex(&selection.recovery_ingress),
        },
    }))
}

/// The Host-authored request is `REQUEST_TAG ++ launch ++ selectorStream`
/// (Host/ApplicationLifecycleRetryBeginV4Authoring.lean:29-37), so its frame
/// and its selector suffix are fixed by bytes this resident already checked
/// against the retained recovery record.
fn checked_request_frame(request: &[u8], selection: &RetrySelection) -> io::Result<()> {
    if request.is_empty()
        || request.len() >= MAX_FRAME
        || !request.starts_with(REQUEST_TAG)
        || !request.ends_with(&selection.selector_stream()?)
    {
        return Err(invalid("v4 retry BEGIN request frame or selector differs"));
    }
    Ok(())
}

fn checked_physical_identity(
    view: &Value,
    launch: &SourceBoundLaunch<'_>,
    selection: &RetrySelection,
) -> io::Result<()> {
    let app = text(view, "app")?
        .parse::<u64>()
        .map_err(|_| invalid("v4 retry app exceeds physical unit range"))?;
    let before = text(view, "beforeGeneration")?
        .parse::<u64>()
        .map_err(|_| invalid("v4 retry prior generation exceeds physical unit range"))?;
    let generation = text(view, "processGeneration")?
        .parse::<u64>()
        .map_err(|_| invalid("v4 retry generation exceeds physical unit range"))?;
    let expected = before
        .checked_add(1)
        .ok_or_else(|| invalid("v4 retry generation overflow"))?;
    // Mini names the unit with its own Store key; the resident checks the app
    // and generation here and the Store against its pinned unit when it runs.
    let unit = String::from_utf8(crate::lifecycle_v3_native::unhex(text(view, "processIdentityHex")?)?)
        .map_err(|_| invalid("v4 retry unit is not UTF-8"))?;
    if app == 0
        || before != selection.before_generation
        || generation != expected
        || !crate::broker::parse_resident_unit(&unit).is_some_and(|(_, unit_app, unit_generation)| {
            unit_app == app.to_string() && unit_generation == generation.to_string()
        })
        || text(view, "imageIdentityHex")? != hex(&launch.descriptor().package.image_identity)
    {
        return Err(invalid("v4 retry physical unit, generation or image differs"));
    }
    Ok(())
}

/// Same custody file and protocol as the v3 BEGIN signers: one management
/// custody signs every lifecycle plan for this app.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedRetryBeginSigners {
    protocol: String,
    selector: crate::lifecycle_selector::LifecycleSelector,
    management_subject: String,
    signers: Vec<SignerPin>,
}

struct BeginPlanEvidence<'a> {
    plan: &'a [u8],
    request: &'a [u8],
    create_index: usize,
    client_operation_id: &'a str,
    launch: &'a SourceBoundLaunch<'a>,
    selection: &'a RetrySelection,
}

impl FixedRetryBeginSigners {
    pub(crate) fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-resident-begin-management-v1" {
            return Err(invalid("v4 retry BEGIN fixed management custody refused"));
        }
        crate::lifecycle_selector::validate_custody(
            operator,
            &self.selector,
            &self.management_subject,
            &self.signers,
            app_uid,
        )
    }

    fn checked_request(
        &self,
        view: &Value,
        request: &[u8],
        create_index: usize,
        client_operation_id: &str,
        launch: &SourceBoundLaunch<'_>,
        selection: &RetrySelection,
    ) -> io::Result<()> {
        if text(view, "type")? != REQUEST_VIEW_TYPE
            || text(view, "canonicalRequestHex")? != hex(request)
            || text(view, "kind")? != "start"
            || text(view, "clientOperationId")? != client_operation_id
            || text(view, "descriptorHex")? != hex(&launch.descriptor().canonical)
            || text(view, "createIndex")? != create_index.to_string()
        {
            return Err(invalid("v4 retry BEGIN request differs from signed launch"));
        }
        checked_retry_fields(view, selection)
    }

    fn checked_plan_slots<'a>(
        &self,
        view: &'a Value,
        evidence: &BeginPlanEvidence<'_>,
    ) -> io::Result<&'a [Value]> {
        let BeginPlanEvidence {
            plan,
            request,
            create_index,
            client_operation_id,
            launch,
            selection,
        } = evidence;
        let descriptor = launch.descriptor();
        let selected = descriptor
            .create_digests
            .get(*create_index)
            .ok_or_else(|| invalid("v4 retry create index absent from signed descriptor"))?;
        let nested = view
            .get("request")
            .ok_or_else(|| invalid("v4 retry inspected request absent"))?;
        self.checked_request(
            nested,
            request,
            *create_index,
            client_operation_id,
            launch,
            selection,
        )?;
        if text(view, "type")? != PLAN_VIEW_TYPE
            || text(view, "canonicalPlanHex")? != hex(plan)
            || text(view, "canonicalRequestHex")? != hex(request)
            || text(view, "app")? != self.selector.app
            || text(view, "packageManifest")? != self.selector.package_manifest
            || text(view, "snapshotManifest")? != self.selector.snapshot_manifest
            || text(view, "managementSubject")? != self.management_subject
            || text(view, "descriptorRoot")? != descriptor.root
            || text(view, "packageRoot")? != descriptor.root
            || view.get("selectedCommandDigest") != Some(&Value::String(selected.clone()))
            || view.get("priorCreate") != Some(&Value::Null)
            || !decimal(text(view, "authorizationOperationId")?)
            || !decimal(text(view, "worldRoot")?)
            || !decimal(text(view, "height")?)
            || !lowercase_hex(text(view, "unsignedIngressHex")?)
            || text(view, "unsignedIngressHex")?.is_empty()
            || text(view, "volumeIdHex")?.len() != 64
            || !lowercase_hex(text(view, "volumeIdHex")?)
        {
            return Err(invalid("v4 retry BEGIN plan differs from fixed signed launch"));
        }
        checked_retry_fields(view, selection)?;
        checked_physical_identity(view, launch, selection)?;
        let slots = view
            .get("slots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("v4 retry BEGIN signing slots absent"))?;
        if slots.len() > self.signers.len() {
            return Err(invalid("v4 retry BEGIN signing slot count exceeds custody pins"));
        }
        Ok(slots)
    }
}

fn outcome_receipt(outcome: &Value, confirmation: &str) -> io::Result<[String; 4]> {
    if text(outcome, "type")? != "confirmed" || text(outcome, "confirmation")? != confirmation {
        return Err(invalid("v4 retry outcome confirmation refused"));
    }
    let receipt = |name| -> io::Result<String> {
        let value = text(outcome, name)?;
        if !decimal(value) {
            return Err(invalid("v4 retry receipt noncanonical"));
        }
        Ok(value.to_owned())
    };
    Ok([
        receipt("transactionId")?,
        receipt("eventId")?,
        receipt("acceptedCount")?,
        receipt("worldRoot")?,
    ])
}

/// Single v4 author/assemble/submit attempt. The request marker is durable
/// before the first current-image call; uncertain results are never retried.
#[allow(clippy::too_many_arguments)]
pub(crate) fn submit_once(
    operator: &PrivateOperator,
    fixed: &FixedRetryBeginSigners,
    app_uid: u32,
    launch: &SourceBoundLaunch<'_>,
    create_index: usize,
    selection: &RetrySelection,
    ledger: &Path,
    attempt_dir: &Path,
) -> io::Result<AcceptedLaunchBegin> {
    fixed.validate(operator, app_uid)?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v4 retry BEGIN attempt parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let client_operation_id = allocate_operation_id(ledger)?;
    let source = create_request_json(create_index, &client_operation_id, launch, selection)?;
    let source_path = write_new(attempt_dir, "request.json", &serde_json::to_vec(&source)?)?;
    let request = operator.tool(
        "author",
        REQUEST_INSPECT_KIND,
        &source_path,
        &attempt_dir.join("request.bin"),
    )?;
    checked_request_frame(&request, selection)?;
    let request_path = attempt_dir.join("request.bin");
    let inspected = operator.tool(
        "inspect",
        REQUEST_INSPECT_KIND,
        &request_path,
        &attempt_dir.join("request-inspection.json"),
    )?;
    // Host/ApplicationLifecycleRetryBeginV4Inspection.lean `inspectRequest`:
    // the request view, beside the descriptor it decoded and checked.
    let request_view: Value = serde_json::from_slice(&inspected)?;
    if text(&request_view, "descriptorCanonicalHex")? != hex(&launch.descriptor().canonical)
        || text(&request_view, "descriptorRoot")? != launch.descriptor().root
    {
        return Err(invalid("v4 retry BEGIN request descriptor differs from signed launch"));
    }
    fixed.checked_request(
        request_view
            .get("request")
            .ok_or_else(|| invalid("v4 retry inspected request absent"))?,
        &request,
        create_index,
        &client_operation_id,
        launch,
        selection,
    )?;
    let active = serde_json::to_vec(&json!({
        "protocol":"mini-spk-launch-retry-begin-prepare-requested-v4",
        "clientOperationId":client_operation_id,
        "requestSha256":hex(&Sha256::digest(&request)),
        "retryRecoveryIndex":selection.recovery_index,
        "retryRecoveryIngressSha256":selection.recovery_ingress_sha256,
        "failedGeneration":selection.failed_generation.to_string(),
        "beforeGeneration":selection.before_generation.to_string(),
    }))?;
    write_new(attempt_dir, "op66-requested.json", &active)?;
    // As in v3: no second attempt in this journal can invoke op66/67/22 after
    // an uncertain response. Recovery inspects this attempt and may only look up.
    write_new(parent, ACTIVE_MARKER, &active)?;
    let reply = operator.invoke(66, &fixed.selector.framed(&request)?)?;
    write_new(attempt_dir, "op66-frame.bin", &reply)?;
    let plan = framed_payload(&reply, 66, PLAN_TAG)?;
    let plan_path = write_new(attempt_dir, "plan.bin", plan)?;
    let inspection = operator.tool(
        "inspect",
        PLAN_INSPECT_KIND,
        &plan_path,
        &attempt_dir.join("plan.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspection)?;
    let slots = fixed.checked_plan_slots(
        &view,
        &BeginPlanEvidence {
            plan,
            request: &request,
            create_index,
            client_operation_id: &client_operation_id,
            launch,
            selection,
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
    write_new(attempt_dir, "op67-requested.bin", &pair)?;
    let reply = operator.invoke(67, &pair)?;
    write_new(attempt_dir, "op67-frame.bin", &reply)?;
    let ingress = framed_payload(&reply, 67, BEGIN_TAG)?.to_vec();
    write_new(attempt_dir, BEGIN_INGRESS_FILE, &ingress)?;
    let marker = json!({
        "protocol":"mini-spk-launch-retry-begin-submit-requested-v4",
        "clientOperationId":client_operation_id,
        "authorizationOperationId":text(&view,"authorizationOperationId")?,
        "volumeIdHex":text(&view,"volumeIdHex")?,
        "ingressSha256":hex(&Sha256::digest(&ingress)),
        "retryRecoveryIndex":selection.recovery_index,
        "retryRecoveryIngressSha256":selection.recovery_ingress_sha256,
    });
    write_new(
        attempt_dir,
        "op22-requested.json",
        &serde_json::to_vec(&marker)?,
    )?;
    let reply = operator.invoke(22, &ingress)?;
    write_new(attempt_dir, "op22-frame.bin", &reply)?;
    let outcome = framed_payload(&reply, 22, OUTCOME_TAG)?;
    let outcome_path = write_new(attempt_dir, "op22-outcome.bin", outcome)?;
    let inspection = operator.tool(
        "inspect",
        "outcome",
        &outcome_path,
        &attempt_dir.join("op22-outcome.json"),
    )?;
    let outcome: Value = serde_json::from_slice(&inspection)?;
    let [transaction_id, event_id, accepted_count, world_root] =
        outcome_receipt(&outcome, "installed")?;
    Ok(AcceptedLaunchBegin {
        ingress,
        action: LaunchBeginAction::Create(create_index),
        prior_create: None,
        client_operation_id,
        authorization_operation_id: text(&view, "authorizationOperationId")?.to_owned(),
        volume_id_hex: text(&view, "volumeIdHex")?.to_owned(),
        snapshot_manifest: text(&view, "snapshotManifest")?.to_owned(),
        process_generation: text(&view, "processGeneration")?.to_owned(),
        process_identity_hex: text(&view, "processIdentityHex")?.to_owned(),
        transaction_id,
        event_id,
        accepted_count,
        world_root,
    })
}

/// Historical receipt only. It cannot arm a CLAIM or a physical launch.
pub(crate) struct RecoveredRetryReceipt {
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub world_root: String,
    pub inspection_name: String,
    pub inspection_sha256: String,
}

/// Reads the retained one-shot attempt and returns its exact submitted
/// ingress after checking the active marker, the op66 marker and the submit
/// marker. Never assembles, signs or chooses a new ingress.
pub(crate) fn retained_submitted_ingress(
    attempt_dir: &Path,
    active_marker: &str,
    prepare_marker: &str,
    submit_marker: &str,
    submit_protocol: &str,
    ingress_file: &str,
) -> io::Result<Vec<u8>> {
    private_dir(attempt_dir)?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v4 retry retained parent absent"))?;
    private_dir(parent)?;
    if retained(&parent.join(active_marker), 4096)?
        != retained(&attempt_dir.join(prepare_marker), 4096)?
    {
        return Err(invalid("v4 retry active marker differs from attempt"));
    }
    let marker: Value = serde_json::from_slice(&retained(&attempt_dir.join(submit_marker), 4096)?)?;
    let ingress = retained(&attempt_dir.join(ingress_file), MAX_FRAME as u64)?;
    if text(&marker, "protocol")? != submit_protocol
        || text(&marker, "ingressSha256")? != hex(&Sha256::digest(&ingress))
    {
        return Err(invalid("v4 retry original submit marker differs"));
    }
    Ok(ingress)
}

/// Read-only lookup of one retained exact ingress: opcode `lookup` with the
/// same bytes the one submit carried. Each probe owns fresh output paths.
pub(crate) fn lookup_retained(
    operator: &PrivateOperator,
    attempt_dir: &Path,
    lookup: u8,
    ingress: &[u8],
) -> io::Result<RecoveredRetryReceipt> {
    let mut nonce = [0u8; 16];
    File::open("/dev/urandom")?.read_exact(&mut nonce)?;
    let lookup_dir = attempt_dir.join(format!("op{lookup}-lookup-{}", hex(&nonce)));
    DirBuilder::new().mode(0o700).create(&lookup_dir)?;
    let reply = operator.invoke(lookup, ingress)?;
    write_new(&lookup_dir, "frame.bin", &reply)?;
    let payload = framed_payload(&reply, lookup, OUTCOME_TAG)?;
    let payload_path = write_new(&lookup_dir, "outcome.bin", payload)?;
    let inspected = operator.tool(
        "inspect",
        "outcome",
        &payload_path,
        &lookup_dir.join("outcome.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let [transaction_id, event_id, accepted_count, world_root] =
        outcome_receipt(&view, "replayed")?;
    let lookup_name = lookup_dir
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| invalid("v4 retry lookup name absent"))?;
    Ok(RecoveredRetryReceipt {
        transaction_id,
        event_id,
        accepted_count,
        world_root,
        inspection_name: format!("{lookup_name}/outcome.json"),
        inspection_sha256: hex(&Sha256::digest(&inspected)),
    })
}

/// Op23 after an uncertain op22: the exact retained v4 BEGIN only.
pub(crate) fn recover_begin_receipt_only(
    operator: &PrivateOperator,
    attempt_dir: &Path,
) -> io::Result<RecoveredRetryReceipt> {
    let ingress = retained_submitted_ingress(
        attempt_dir,
        ACTIVE_MARKER,
        "op66-requested.json",
        "op22-requested.json",
        "mini-spk-launch-retry-begin-submit-requested-v4",
        BEGIN_INGRESS_FILE,
    )?;
    if !ingress.starts_with(BEGIN_TAG) {
        return Err(invalid("v4 retry retained BEGIN frame refused"));
    }
    lookup_retained(operator, attempt_dir, 23, &ingress)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn record(accepted: &str, generation: &str, reconciled: &str, sha: &str) -> Vec<u8> {
        serde_json::to_vec(&json!({
            "app":"8502","generation":generation,"ingressSha256":sha,
            "outcome":{"acceptedCount":accepted,"confirmation":"installed",
                "eventId":"21","transactionId":"24","type":"confirmed","worldRoot":"77"},
            "protocol":"mini-spk-failed-start-recovered-v1",
            "reconciledGeneration":reconciled,
        }))
        .unwrap()
    }

    fn ingress() -> Vec<u8> {
        let mut bytes = RECOVERY_INGRESS_TAG.to_vec();
        bytes.extend_from_slice(b"recovery-stream");
        bytes
    }

    #[test]
    fn retry_v4_nat_matches_lean_base255_terminated_digits() {
        assert_eq!(encode_nat_decimal("0").unwrap(), vec![255]);
        assert_eq!(encode_nat_decimal("77").unwrap(), vec![77, 255]);
        assert_eq!(encode_nat_decimal("254").unwrap(), vec![254, 255]);
        assert_eq!(encode_nat_decimal("255").unwrap(), vec![0, 1, 255]);
        assert_eq!(encode_nat_decimal("65025").unwrap(), vec![0, 0, 1, 255]);
        assert_eq!(encode_nat_decimal("65026").unwrap(), vec![1, 0, 1, 255]);
        assert_eq!(encode_nat_usize(255), vec![0, 1, 255]);
        assert_eq!(
            encode_nat_decimal("18446744073709551615").unwrap(),
            encode_nat_usize(usize::MAX)
        );
        assert!(encode_nat_decimal("077").is_err());
        assert_eq!(encode_bytes(b"ab"), vec![2, 255, b'a', b'b']);
    }

    #[test]
    fn retry_v4_selector_bytes_strip_recovery_frame_and_prefix_index() {
        let ingress = ingress();
        let sha = hex(&Sha256::digest(&ingress));
        let selection =
            RetrySelection::from_retained(&record("78", "2", "3", &sha), &ingress, 8502, 2, 3)
                .unwrap();
        assert_eq!(selection.recovery_index, "77");
        let mut expected = vec![0x4d, 0xff];
        expected.extend_from_slice(b"recovery-stream");
        assert_eq!(selection.selector_stream().unwrap(), expected);
        let mut canonical = b"DREGG/APPLICATION/FAILED-CREATE-RETRY-SELECTOR/v1".to_vec();
        canonical.extend_from_slice(&expected);
        assert_eq!(selection.selector_canonical().unwrap(), canonical);
        let view = json!({
            "retryRecoveryIndex":"77",
            "retryRecoveryIngressHex":hex(&ingress),
            "retrySelectorHex":hex(&canonical),
        });
        checked_retry_fields(&view, &selection).unwrap();
        let mut wrong = view.clone();
        wrong["retryRecoveryIndex"] = json!("78");
        assert!(checked_retry_fields(&wrong, &selection).is_err());
        let mut wrong = view.clone();
        wrong["retrySelectorHex"] = json!(hex(&expected));
        assert!(checked_retry_fields(&wrong, &selection).is_err());
        let mut launch = V3_LAUNCH_REQUEST_TAG.to_vec();
        launch.extend_from_slice(b"launch-stream");
        let request = retry_request_bytes(&launch, &selection).unwrap();
        let mut wanted = b"DREGG/APPLICATION/RETRY-CREATE-BEGIN-OPERATOR-REQUEST/v4".to_vec();
        wanted.extend_from_slice(b"launch-stream");
        wanted.extend_from_slice(&[0x4d, 0xff]);
        wanted.extend_from_slice(b"recovery-stream");
        assert_eq!(request, wanted);
        checked_request_frame(&request, &selection).unwrap();
        let mut other = request.clone();
        *other.last_mut().unwrap() ^= 1;
        assert!(checked_request_frame(&other, &selection).is_err());
        assert!(retry_request_bytes(b"launch-stream", &selection).is_err());
        assert!(retry_request_bytes(V3_LAUNCH_REQUEST_TAG, &selection).is_err());
    }

    #[test]
    fn retry_v4_refuses_ingress_sha_mismatch() {
        let ingress = ingress();
        let other = hex(&Sha256::digest(b"other"));
        assert!(
            RetrySelection::from_retained(&record("78", "2", "3", &other), &ingress, 8502, 2, 3)
                .is_err()
        );
        let unframed = b"recovery-stream".to_vec();
        let sha = hex(&Sha256::digest(&unframed));
        assert!(RetrySelection::from_retained(
            &record("78", "2", "3", &sha),
            &unframed,
            8502,
            2,
            3
        )
        .is_err());
    }

    #[test]
    fn retry_v4_refuses_different_reconciled_generation() {
        let ingress = ingress();
        let sha = hex(&Sha256::digest(&ingress));
        assert!(
            RetrySelection::from_retained(&record("78", "2", "4", &sha), &ingress, 8502, 2, 3)
                .is_err()
        );
        assert!(
            RetrySelection::from_retained(&record("78", "1", "3", &sha), &ingress, 8502, 2, 3)
                .is_err()
        );
        assert!(
            RetrySelection::from_retained(&record("78", "2", "3", &sha), &ingress, 8503, 2, 3)
                .is_err()
        );
        assert!(
            RetrySelection::from_retained(&record("0", "2", "3", &sha), &ingress, 8502, 2, 3)
                .is_err()
        );
        assert!(
            RetrySelection::from_retained(&record("078", "2", "3", &sha), &ingress, 8502, 2, 3)
                .is_err()
        );
    }

    #[test]
    fn retry_v4_choice_only_for_create_after_recovered_generation() {
        assert_eq!(retry_generations(true, 4), Some((2, 3)));
        assert_eq!(retry_generations(false, 4), None);
        assert_eq!(retry_generations(true, 2), None);
        assert_eq!(retry_generations(true, 1), None);
        assert_eq!(unit_generation("mini-spk-s0123456789abcdef-a8502-g4.service", 8502).unwrap(), 4);
        assert!(unit_generation("mini-spk-s0123456789abcdef-a8502-g4.service", 8503).is_err());
        assert!(unit_generation("mini-spk-s0123456789abcdef-a8502-g04.service", 8502).is_err());
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let apps = std::env::temp_dir().join(format!(
            "spk-retry-v4-select-{}-{stamp}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&apps).unwrap();
        let journal = apps.join("g4");
        DirBuilder::new().mode(0o700).create(&journal).unwrap();
        // No failed generation record: unchanged v3 create.
        assert_eq!(
            select_retry(&journal, "mini-spk-s0123456789abcdef-a8502-g4.service", 8502, true).unwrap(),
            None
        );
        let failed = apps.join("g2");
        DirBuilder::new().mode(0o700).create(&failed).unwrap();
        DirBuilder::new()
            .mode(0o700)
            .create(failed.join(RECOVERY_DIR))
            .unwrap();
        let ingress = ingress();
        let sha = hex(&Sha256::digest(&ingress));
        let write = |path: std::path::PathBuf, bytes: &[u8]| {
            use std::io::Write;
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(path)
                .unwrap();
            file.write_all(bytes).unwrap();
        };
        write(failed.join(RECOVERED_RECORD), &record("78", "2", "3", &sha));
        write(failed.join(RECOVERY_DIR).join("ingress.bin"), &ingress);
        let selected = select_retry(&journal, "mini-spk-s0123456789abcdef-a8502-g4.service", 8502, true)
            .unwrap()
            .unwrap();
        assert_eq!(selected.recovery_index, "77");
        assert_eq!((selected.failed_generation, selected.before_generation), (2, 3));
        // Continue never retries, even with the record present.
        assert_eq!(
            select_retry(&journal, "mini-spk-s0123456789abcdef-a8502-g4.service", 8502, false).unwrap(),
            None
        );
        // A later generation does not reuse an older recovery.
        assert_eq!(
            select_retry(&journal, "mini-spk-s0123456789abcdef-a8502-g5.service", 8502, true).unwrap(),
            None
        );
        fs::remove_dir_all(apps).unwrap();
    }

    #[test]
    fn retry_v4_reply_tags_cannot_accept_v3_payloads() {
        let mut reply = ((PLAN_TAG.len() + 2) as u32).to_le_bytes().to_vec();
        reply.push(66);
        reply.extend_from_slice(PLAN_TAG);
        reply.push(1);
        assert!(framed_payload(&reply, 66, PLAN_TAG).is_ok());
        assert!(framed_payload(&reply, 66, b"DREGG/APPLICATION/LAUNCH-BEGIN-OPERATOR-PLAN/v1").is_err());
        assert!(framed_payload(&reply, 67, PLAN_TAG).is_err());
    }
}
