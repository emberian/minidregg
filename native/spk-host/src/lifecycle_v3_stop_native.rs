//! Exact physical STOP target selected by Mini's current verified history.
//! A sealed fresh op26 claim may fence the running incarnation. Recovery can
//! only resume its exact retained attempt from an already-Fenced journal row.
#![allow(dead_code)]

use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::hostd::{Journal, Phase, Record, StopIdentity, UnitStopAudit};
use crate::lifecycle_v3_native::{decimal, framed_payload, hex, lowercase_hex, unhex};
use crate::lifecycle_v3_stop_claim_native::{ExactReceipt, FreshStopClaim};
use crate::volume_custody::VolumeWitness;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{DirBuilder, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const MAX_INSPECTION: usize = 2 * 1024 * 1024;
const MAX_FRAME: usize = 12_102_760;
const MARKER_NAME: &str = "stop-fence-requested.json";
const MAX_MARKER: u64 = 8192;
const COMMITTED_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-CLAIM-COMMITTED/v3";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn field<'a>(value: &'a Value, name: &str) -> io::Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("STOP verified inspection field absent"))
}

fn number(value: &str) -> io::Result<u64> {
    if !decimal(value) {
        return Err(invalid("STOP verified inspection number noncanonical"));
    }
    value
        .parse()
        .map_err(|_| invalid("STOP verified inspection number exceeds host range"))
}

fn bounded_hex(value: &str, max_bytes: usize) -> io::Result<Vec<u8>> {
    if value.len() > max_bytes.saturating_mul(2) || !lowercase_hex(value) {
        return Err(invalid("STOP verified inspection hex refused"));
    }
    unhex(value)
}

fn utf8_hex(value: &str, max_bytes: usize) -> io::Result<String> {
    String::from_utf8(bounded_hex(value, max_bytes)?)
        .map_err(|_| invalid("STOP verified inspection identity is not UTF-8"))
}

/// Constructed only from the read-only `inspect-stop-claim` output for the
/// retained op66 STOP plan and exact fresh op26 committed frame. The Lean
/// inspector has already reselected the original event23/24 records and the
/// original event25 running completion from one Verified prefix.
pub(crate) struct StopTarget {
    app: u64,
    operation_generation: u64,
    running_generation: u64,
    running_index: u64,
    running_receipt_hex: String,
    unit: String,
    image_hex: String,
    invocation_id: String,
    control_group: String,
    volume_id_hex: String,
    custody: Vec<u8>,
    physical_witness: Vec<u8>,
    plan_sha256: String,
    claim_sha256: String,
    begin_sha256: String,
}

#[derive(Clone, Copy)]
struct RunningState<'a> {
    app: u64,
    generation: u64,
    unit: &'a str,
    image_hex: &'a str,
    invocation_id: Option<&'a str>,
    control_group: Option<&'a str>,
    volume_resource: u64,
    volume_id_hex: &'a str,
    physical_witness: &'a [u8],
}

pub(crate) struct ReceiptFields<'a> {
    pub transaction_id: &'a str,
    pub event_id: &'a str,
    pub accepted_count: &'a str,
    pub image_boundary: &'a str,
}

fn same_receipt(source: &Value, retained: ReceiptFields<'_>) -> io::Result<()> {
    for (name, expected) in [
        ("transactionId", retained.transaction_id),
        ("eventId", retained.event_id),
        ("acceptedCount", retained.accepted_count),
        ("imageBoundary", retained.image_boundary),
    ] {
        let value = field(source, name)?;
        if !decimal(value) || value != expected {
            return Err(invalid(
                "STOP verified receipt differs from retained receipt",
            ));
        }
    }
    Ok(())
}

impl StopTarget {
    pub(crate) fn from_verified_inspection(
        retained_plan: &[u8],
        fresh_committed_frame: &[u8],
        original_begin: &[u8],
        inspection: &[u8],
        begin_receipt: ReceiptFields<'_>,
        claim_receipt: ReceiptFields<'_>,
    ) -> io::Result<Self> {
        if inspection.is_empty() || inspection.len() > MAX_INSPECTION {
            return Err(invalid("STOP verified inspection size refused"));
        }
        let view: Value = serde_json::from_slice(inspection)?;
        if field(&view, "type")? != "application-lifecycle-stop-claim-verified-v1"
            || field(&view, "retainedPlanHex")? != hex(retained_plan)
            || field(&view, "freshCommittedFrameHex")? != hex(fresh_committed_frame)
        {
            return Err(invalid(
                "STOP verified inspection differs from retained frames",
            ));
        }
        let plan = view
            .get("plan")
            .ok_or_else(|| invalid("STOP verified plan absent"))?;
        let claim = view
            .get("claim")
            .ok_or_else(|| invalid("STOP verified claim absent"))?;
        if field(plan, "type")? != "application-lifecycle-launch-stop-plan-v2"
            || field(plan, "canonicalPlanHex")? != hex(retained_plan)
            || field(
                plan.get("basePlan")
                    .and_then(|base| base.get("request"))
                    .ok_or_else(|| invalid("STOP base request absent"))?,
                "kind",
            )? != "stop"
            || field(claim, "frameHex")? != hex(fresh_committed_frame)
            || field(claim, "originalBeginHex")? != hex(original_begin)
            || field(claim, "kind")? != "stop"
        {
            return Err(invalid(
                "STOP nested source inspection differs from retained frames",
            ));
        }
        let running = plan
            .get("running")
            .ok_or_else(|| invalid("STOP running witness absent"))?;
        let index = field(running, "index")?;
        let receipt_hex = field(running, "receiptHex")?;
        let begin_receipt_hex = field(&view, "beginReceiptHex")?;
        let claim_receipt_hex = field(&view, "claimReceiptHex")?;
        if field(&view, "runningIndex")? != index
            || field(&view, "runningReceiptHex")? != receipt_hex
            || [receipt_hex, begin_receipt_hex, claim_receipt_hex]
                .iter()
                .any(|value| value.is_empty() || value.len() > 1024 || !lowercase_hex(value))
        {
            return Err(invalid("STOP running receipt echo differs"));
        }
        same_receipt(
            view.get("beginReceipt")
                .ok_or_else(|| invalid("STOP verified BEGIN receipt absent"))?,
            begin_receipt,
        )?;
        same_receipt(
            view.get("claimReceipt")
                .ok_or_else(|| invalid("STOP verified claim receipt absent"))?,
            claim_receipt,
        )?;
        let running_index = number(index)?;
        let receipt = running
            .get("receipt")
            .ok_or_else(|| invalid("STOP running receipt fields absent"))?;
        if number(field(receipt, "acceptedCount")?)?
            != running_index
                .checked_add(1)
                .ok_or_else(|| invalid("STOP running index overflow"))?
        {
            return Err(invalid("STOP running receipt count differs from index"));
        }
        for name in ["transactionId", "eventId", "imageBoundary"] {
            if !decimal(field(receipt, name)?) {
                return Err(invalid("STOP running receipt digest noncanonical"));
            }
        }
        let app = number(field(plan, "app")?)?;
        let operation_generation = number(field(plan, "operationGeneration")?)?;
        let running_generation = number(field(running, "generation")?)?;
        if app == 0
            || running_generation == 0
            || running_generation.checked_add(1) != Some(operation_generation)
        {
            return Err(invalid("STOP running and operation generations differ"));
        }
        let unit = utf8_hex(field(running, "unitHex")?, 512)?;
        let image_hex = field(running, "imageHex")?.to_owned();
        if unit.is_empty() || image_hex.is_empty() || !lowercase_hex(&image_hex) {
            return Err(invalid("STOP running unit or image refused"));
        }
        let invocation_id = utf8_hex(field(running, "invocationIdHex")?, 128)?;
        let control_group = utf8_hex(field(running, "controlGroupHex")?, 2048)?;
        if invocation_id.is_empty() || control_group.is_empty() {
            return Err(invalid("STOP running invocation or cgroup absent"));
        }
        let volume_id_hex = field(running, "volumeIdHex")?.to_owned();
        if volume_id_hex.len() != 64 || !lowercase_hex(&volume_id_hex) {
            return Err(invalid("STOP source volume ID refused"));
        }
        Ok(Self {
            app,
            operation_generation,
            running_generation,
            running_index,
            running_receipt_hex: receipt_hex.to_owned(),
            unit,
            image_hex,
            invocation_id,
            control_group,
            volume_id_hex,
            custody: bounded_hex(field(running, "custodyHex")?, 8192)?,
            physical_witness: bounded_hex(field(running, "physicalWitnessHex")?, 4096)?,
            plan_sha256: hex(&Sha256::digest(retained_plan)),
            claim_sha256: hex(&Sha256::digest(fresh_committed_frame)),
            begin_sha256: hex(&Sha256::digest(original_begin)),
        })
    }

    fn marker_bytes(&self) -> io::Result<Vec<u8>> {
        let bytes = serde_json::to_vec(&json!({
            "protocol":"mini-spk-lifecycle-stop-fence-requested-v1",
            "planSha256":self.plan_sha256,
            "freshCommittedSha256":self.claim_sha256,
            "originalBeginSha256":self.begin_sha256,
            "runningIndex":self.running_index.to_string(),
            "runningReceiptHex":self.running_receipt_hex,
            "app":self.app.to_string(),
            "operationGeneration":self.operation_generation.to_string(),
            "runningGeneration":self.running_generation.to_string(),
            "unitHex":hex(self.unit.as_bytes()),
            "imageHex":self.image_hex,
            "invocationIdHex":hex(self.invocation_id.as_bytes()),
            "controlGroupHex":hex(self.control_group.as_bytes()),
            "volumeIdHex":self.volume_id_hex,
            "custodySha256":hex(&Sha256::digest(&self.custody)),
            "physicalWitnessSha256":hex(&Sha256::digest(&self.physical_witness)),
        }))?;
        if bytes.is_empty() || bytes.len() as u64 > MAX_MARKER {
            return Err(invalid("STOP marker exceeds recoverable bound"));
        }
        Ok(bytes)
    }

    /// This private marker is fsynced before any future manager fence. The
    /// caller has to retain the exact source plan/claim/BEGIN artifacts too;
    /// their SHA-256 values are pinned here for crash recovery.
    fn persist_marker(&self, attempt_dir: &Path) -> io::Result<PathBuf> {
        private_dir(attempt_dir)?;
        write_new(attempt_dir, MARKER_NAME, &self.marker_bytes()?)
    }

    /// A recovered STOP may audit the same Fenced unit, never submit op26
    /// again. The marker must match freshly re-inspected original bytes and
    /// the same selected event25 receipt/incarnation.
    fn check_marker(&self, attempt_dir: &Path) -> io::Result<()> {
        private_dir(attempt_dir)?;
        let expected = self.marker_bytes()?;
        let path = attempt_dir.join(MARKER_NAME);
        let mut file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(path)?;
        let before = file.metadata()?;
        if !before.is_file()
            || before.uid() != unsafe { libc::geteuid() }
            || before.nlink() != 1
            || before.permissions().mode() & 0o777 != 0o600
            || before.len() == 0
            || before.len() > MAX_MARKER
        {
            return Err(invalid("STOP marker file custody refused"));
        }
        let mut actual = Vec::with_capacity(before.len() as usize);
        file.by_ref()
            .take(MAX_MARKER + 1)
            .read_to_end(&mut actual)?;
        let after = file.metadata()?;
        if actual != expected
            || actual.len() as u64 != before.len()
            || after.dev() != before.dev()
            || after.ino() != before.ino()
            || after.len() != before.len()
            || after.mtime() != before.mtime()
            || after.mtime_nsec() != before.mtime_nsec()
            || after.ctime() != before.ctime()
            || after.ctime_nsec() != before.ctime_nsec()
        {
            return Err(invalid("STOP retained marker differs from source attempt"));
        }
        Ok(())
    }

    fn compare_identity(&self, actual: RunningState<'_>) -> io::Result<()> {
        if actual.app != self.app
            || actual.generation != self.running_generation
            || actual.unit != self.unit
            || actual.image_hex != self.image_hex
            || actual.invocation_id != Some(self.invocation_id.as_str())
            || actual.control_group != Some(self.control_group.as_str())
            || actual.volume_resource != self.app
            || actual.volume_id_hex != self.volume_id_hex
            || actual.physical_witness != self.physical_witness
        {
            return Err(invalid(
                "STOP source running witness differs from retained physical state",
            ));
        }
        Ok(())
    }

    pub(crate) fn compare_retained(
        &self,
        record: &Record,
        volume: &VolumeWitness,
    ) -> io::Result<()> {
        if record.phase != Phase::Running {
            return Err(invalid("STOP journal is not Running"));
        }
        self.compare_identity(RunningState {
            app: record.app(),
            generation: record.generation(),
            unit: record.unit(),
            image_hex: record.image_identity(),
            invocation_id: record.invocation_id(),
            control_group: record.control_group(),
            volume_resource: volume.resource,
            volume_id_hex: &volume.volume_id,
            physical_witness: &volume.bytes,
        })
    }

    /// Read-only final preflight. The caller must still use a hostd audited
    /// fence that rechecks this same identity under its journal lock.
    pub(crate) fn recheck_volume(&self, volume: &VolumeWitness) -> io::Result<()> {
        if volume.bytes != self.physical_witness || volume.volume_id != self.volume_id_hex {
            return Err(invalid(
                "STOP root volume witness differs from admitted custody",
            ));
        }
        volume.recheck_handoff()
    }

    fn stop_identity(&self) -> StopIdentity {
        StopIdentity {
            app: self.app,
            generation: self.running_generation,
            unit: self.unit.clone(),
            image_identity: self.image_hex.clone(),
            invocation_id: self.invocation_id.clone(),
            control_group: self.control_group.clone(),
        }
    }
}

/// Consume only the sealed fresh op26 STOP callback. The read-only historical
/// inspector and a matching journal record cannot call this entry on their
/// own. A private exact-attempt marker is durable before the manager fence;
/// the journal hook then rechecks the same incarnation and volume under lock.
pub(crate) fn fence_exact(
    fresh: &FreshStopClaim,
    journal: &Journal,
    volume: &VolumeWitness,
    attempt_dir: &Path,
) -> io::Result<UnitStopAudit> {
    let target = fresh.target();
    let record = journal
        .read()?
        .ok_or_else(|| invalid("STOP running journal absent"))?;
    target.compare_retained(&record, volume)?;
    target.recheck_volume(volume)?;
    target.persist_marker(attempt_dir)?;
    target.check_marker(attempt_dir)?;
    journal
        .fence_and_stop_manager_checked(&target.stop_identity(), || target.recheck_volume(volume))
}

fn read_private_artifact(path: &Path, max: usize) -> io::Result<Vec<u8>> {
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)?;
    let before = file.metadata()?;
    if !before.is_file()
        || before.uid() != unsafe { libc::geteuid() }
        || before.nlink() != 1
        || before.permissions().mode() & 0o777 != 0o600
        || before.len() == 0
        || before.len() > max as u64
    {
        return Err(invalid("STOP recovery inspection file custody refused"));
    }
    let mut bytes = Vec::with_capacity(before.len() as usize);
    file.by_ref().take(max as u64 + 1).read_to_end(&mut bytes)?;
    let after = file.metadata()?;
    if bytes.len() as u64 != before.len()
        || after.dev() != before.dev()
        || after.ino() != before.ino()
        || after.len() != before.len()
        || after.mtime() != before.mtime()
        || after.mtime_nsec() != before.mtime_nsec()
        || after.ctime() != before.ctime()
        || after.ctime_nsec() != before.ctime_nsec()
    {
        return Err(invalid("STOP recovery inspection changed during read"));
    }
    Ok(bytes)
}

fn retained_receipt(value: &Value) -> io::Result<ExactReceipt> {
    ExactReceipt::new(
        field(value, "transactionId")?,
        field(value, "eventId")?,
        field(value, "acceptedCount")?,
        field(value, "imageBoundary")?,
    )
}

fn receipt_fields(receipt: &ExactReceipt) -> ReceiptFields<'_> {
    ReceiptFields {
        transaction_id: receipt.transaction_id(),
        event_id: receipt.event_id(),
        accepted_count: receipt.accepted_count(),
        image_boundary: receipt.image_boundary(),
    }
}

/// Resume only a STOP that already crossed the fresh fence's durable Fenced
/// boundary. Historical ingress or an op27 receipt cannot call `fence_exact`.
/// The current pinned Host reselects the exact retained plan, committed op26
/// frame and prior running event25; the private marker must match those bytes.
/// The hostd recovery method independently requires Fenced under its lock.
pub(crate) fn resume_fenced_exact(
    operator: &PrivateOperator,
    attempt_dir: &Path,
    fresh_probe_dir: &Path,
    journal: &Journal,
    volume: &VolumeWitness,
) -> io::Result<UnitStopAudit> {
    private_dir(attempt_dir)?;
    let retained_plan = read_private_artifact(&attempt_dir.join("stop-plan-v2.bin"), MAX_FRAME)?;
    let original_begin =
        read_private_artifact(&attempt_dir.join("original-begin-v3.bin"), MAX_FRAME)?;
    let claim_ingress =
        read_private_artifact(&attempt_dir.join("claim-ingress-v3.bin"), MAX_FRAME)?;
    let retained_committed =
        read_private_artifact(&attempt_dir.join("committed-v3.bin"), MAX_FRAME)?;
    let original_frame = read_private_artifact(&attempt_dir.join("op26-frame.bin"), MAX_FRAME)?;
    if framed_payload(&original_frame, 26, COMMITTED_TAG)? != retained_committed {
        return Err(invalid("STOP recovery original op26 frame differs"));
    }
    let requested: Value = serde_json::from_slice(&read_private_artifact(
        &attempt_dir.join("op26-requested.json"),
        MAX_MARKER as usize,
    )?)?;
    if field(&requested, "protocol")? != "mini-spk-stop-claim-op26-requested-v1"
        || field(&requested, "stopPlanSha256")? != hex(&Sha256::digest(&retained_plan))
        || field(&requested, "originalBeginSha256")? != hex(&Sha256::digest(&original_begin))
        || field(&requested, "claimIngressSha256")? != hex(&Sha256::digest(&claim_ingress))
    {
        return Err(invalid("STOP recovery original op26 attempt differs"));
    }
    let begin_receipt = retained_receipt(
        requested
            .get("beginReceipt")
            .ok_or_else(|| invalid("STOP recovery original BEGIN receipt absent"))?,
    )?;
    let committed_view: Value = serde_json::from_slice(&read_private_artifact(
        &attempt_dir.join("committed-v3.json"),
        MAX_INSPECTION,
    )?)?;
    if field(&committed_view, "type")? != "application-lifecycle-claim-committed-v3"
        || field(&committed_view, "kind")? != "stop"
        || field(&committed_view, "frameHex")? != hex(&retained_committed)
        || field(&committed_view, "originalClaimHex")? != hex(&claim_ingress)
        || field(&committed_view, "originalBeginHex")? != hex(&original_begin)
    {
        return Err(invalid("STOP recovery original claim inspection differs"));
    }
    let claim_receipt = retained_receipt(
        committed_view
            .get("receipt")
            .ok_or_else(|| invalid("STOP recovery original claim receipt absent"))?,
    )?;
    let probe_parent = fresh_probe_dir
        .parent()
        .ok_or_else(|| invalid("STOP recovery probe parent absent"))?;
    private_dir(probe_parent)?;
    DirBuilder::new().mode(0o700).create(fresh_probe_dir)?;
    let plan_path = write_new(fresh_probe_dir, "stop-plan-v2.bin", &retained_plan)?;
    let committed_path = write_new(fresh_probe_dir, "committed-v3.bin", &retained_committed)?;
    let output = fresh_probe_dir.join("stop-claim-current.json");
    let _ = operator.pinned_config()?;
    let status = Command::new(&operator.host)
        .arg(&operator.config)
        .arg("inspect-stop-claim")
        .arg(&plan_path)
        .arg(&committed_path)
        .arg(&output)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()?;
    if !status.success() {
        return Err(invalid("pinned Mini Host STOP recovery inspection refused"));
    }
    let inspection = read_private_artifact(&output, MAX_INSPECTION)?;
    let _ = operator.pinned_config()?;
    let target = StopTarget::from_verified_inspection(
        &retained_plan,
        &retained_committed,
        &original_begin,
        &inspection,
        receipt_fields(&begin_receipt),
        receipt_fields(&claim_receipt),
    )?;
    target.check_marker(attempt_dir)?;
    let record = journal
        .read()?
        .ok_or_else(|| invalid("STOP fenced recovery journal absent"))?;
    if record.phase != Phase::Fenced {
        return Err(invalid("STOP recovery requires Fenced journal"));
    }
    target.compare_identity(RunningState {
        app: record.app(),
        generation: record.generation(),
        unit: record.unit(),
        image_hex: record.image_identity(),
        invocation_id: record.invocation_id(),
        control_group: record.control_group(),
        volume_resource: volume.resource,
        volume_id_hex: &volume.volume_id,
        physical_witness: &volume.bytes,
    })?;
    target.recheck_volume(volume)?;
    journal.resume_fenced_stop_manager_checked(&target.stop_identity(), || {
        target.recheck_volume(volume)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::fs::{self, DirBuilder};
    use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
    use std::time::{SystemTime, UNIX_EPOCH};

    const LARGE_DIGEST: &str = "340282366920938463463374607431768211456";

    fn inspected(plan: &[u8], committed: &[u8], begin: &[u8]) -> Value {
        json!({
            "type":"application-lifecycle-stop-claim-verified-v1",
            "retainedPlanHex":hex(plan),
            "freshCommittedFrameHex":hex(committed),
            "beginReceiptHex":"01",
            "beginReceipt":{"transactionId":LARGE_DIGEST,"eventId":"11","acceptedCount":"12","imageBoundary":"13"},
            "claimReceiptHex":"02",
            "claimReceipt":{"transactionId":"20","eventId":"21","acceptedCount":"22","imageBoundary":LARGE_DIGEST},
            "runningIndex":"4",
            "runningReceiptHex":"03",
            "plan":{
                "type":"application-lifecycle-launch-stop-plan-v2",
                "canonicalPlanHex":hex(plan),
                "basePlan":{"request":{"kind":"stop"}},
                "app":"8401",
                "operationGeneration":"7",
                "running":{
                    "index":"4",
                    "receiptHex":"03",
                    "receipt":{
                        "transactionId":LARGE_DIGEST,
                        "eventId":"21",
                        "acceptedCount":"5",
                        "imageBoundary":LARGE_DIGEST
                    },
                    "generation":"6",
                    "unitHex":hex(b"mini-spk-a8401-g6.service"),
                    "imageHex":"abcd",
                    "invocationIdHex":hex(b"0123456789abcdef0123456789abcdef"),
                    "controlGroupHex":hex(b"/system.slice/mini-spk-a8401-g6.service"),
                    "volumeIdHex":"a".repeat(64),
                    "custodyHex":"04",
                    "physicalWitnessHex":"05"
                }
            },
            "claim":{
                "kind":"stop",
                "frameHex":hex(committed),
                "originalBeginHex":hex(begin)
            }
        })
    }

    fn checked(
        plan: &[u8],
        committed: &[u8],
        begin: &[u8],
        view: &Value,
    ) -> io::Result<StopTarget> {
        StopTarget::from_verified_inspection(
            plan,
            committed,
            begin,
            &serde_json::to_vec(view).unwrap(),
            ReceiptFields {
                transaction_id: LARGE_DIGEST,
                event_id: "11",
                accepted_count: "12",
                image_boundary: "13",
            },
            ReceiptFields {
                transaction_id: "20",
                event_id: "21",
                accepted_count: "22",
                image_boundary: LARGE_DIGEST,
            },
        )
    }

    fn private_attempt() -> PathBuf {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "mini-spk-stop-marker-{}-{stamp}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&path).unwrap();
        path
    }

    #[test]
    fn stop_target_requires_exact_source_echoes_and_running_incarnation() {
        let plan = b"plan";
        let committed = b"fresh-claim";
        let begin = b"original-begin";
        let mut view = inspected(plan, committed, begin);
        let target = checked(plan, committed, begin, &view).unwrap();
        assert_eq!(target.running_index, 4);
        assert_eq!(target.operation_generation, 7);
        assert_eq!(target.running_receipt_hex, "03");
        assert_eq!(target.custody, [4]);
        let stop_identity = target.stop_identity();
        assert_eq!(stop_identity.generation, 6);
        assert_eq!(stop_identity.unit, "mini-spk-a8401-g6.service");
        assert_eq!(
            stop_identity.invocation_id,
            "0123456789abcdef0123456789abcdef"
        );
        assert!(checked(plan, b"other", begin, &view).is_err());
        assert!(checked(plan, committed, b"other", &view).is_err());
        view["claimReceipt"]["imageBoundary"] = json!("24");
        assert!(checked(plan, committed, begin, &view).is_err());

        let volume_id = "a".repeat(64);
        let current = RunningState {
            app: 8401,
            generation: 6,
            unit: "mini-spk-a8401-g6.service",
            image_hex: "abcd",
            invocation_id: Some("0123456789abcdef0123456789abcdef"),
            control_group: Some("/system.slice/mini-spk-a8401-g6.service"),
            volume_resource: 8401,
            volume_id_hex: &volume_id,
            physical_witness: &[5],
        };
        assert!(target.compare_identity(current).is_ok());
        assert!(target
            .compare_identity(RunningState {
                invocation_id: Some("different-invocation"),
                ..current
            })
            .is_err());
        assert!(target
            .compare_identity(RunningState {
                control_group: Some("/system.slice/other.service"),
                ..current
            })
            .is_err());
        assert!(target
            .compare_identity(RunningState {
                physical_witness: &[6],
                ..current
            })
            .is_err());
    }

    #[test]
    fn stop_target_rejects_inconsistent_receipt_or_generation() {
        let plan = b"plan";
        let committed = b"fresh-claim";
        let begin = b"original-begin";
        let mut view = inspected(plan, committed, begin);
        view["plan"]["running"]["receipt"]["acceptedCount"] = json!("6");
        assert!(checked(plan, committed, begin, &view).is_err());
        view["plan"]["running"]["receipt"]["acceptedCount"] = json!("5");
        view["plan"]["operationGeneration"] = json!("8");
        assert!(checked(plan, committed, begin, &view).is_err());
        view["plan"]["operationGeneration"] = json!("7");
        view["plan"]["running"]["receipt"]["transactionId"] = json!("01");
        assert!(checked(plan, committed, begin, &view).is_err());
    }

    #[test]
    fn stop_target_marker_reopens_exactly_and_refuses_interrupted_write() {
        let plan = b"plan";
        let committed = b"fresh-claim";
        let begin = b"original-begin";
        let view = inspected(plan, committed, begin);
        let target = checked(plan, committed, begin, &view).unwrap();
        let directory = private_attempt();
        let marker = target.persist_marker(&directory).unwrap();
        target.check_marker(&directory).unwrap();
        assert!(target.persist_marker(&directory).is_err());
        let other = checked(
            b"other-plan",
            committed,
            begin,
            &inspected(b"other-plan", committed, begin),
        )
        .unwrap();
        assert!(other.check_marker(&directory).is_err());
        fs::remove_file(marker).unwrap();
        fs::remove_dir(directory).unwrap();

        let interrupted = private_attempt();
        let partial = interrupted.join(MARKER_NAME);
        fs::write(&partial, b"partial").unwrap();
        fs::set_permissions(&partial, fs::Permissions::from_mode(0o600)).unwrap();
        assert!(target.check_marker(&interrupted).is_err());
        assert!(target.persist_marker(&interrupted).is_err());
        fs::remove_file(partial).unwrap();
        fs::remove_dir(interrupted).unwrap();
    }

    #[test]
    fn stop_recovery_artifacts_require_private_exact_files_and_large_receipts() {
        let dir = private_attempt();
        let original = dir.join("original.bin");
        fs::write(&original, b"retained").unwrap();
        fs::set_permissions(&original, fs::Permissions::from_mode(0o600)).unwrap();
        assert_eq!(read_private_artifact(&original, 8).unwrap(), b"retained");
        assert!(read_private_artifact(&original, 7).is_err());
        let link = dir.join("alias.bin");
        std::os::unix::fs::symlink(&original, &link).unwrap();
        assert!(read_private_artifact(&link, 8).is_err());
        fs::set_permissions(&original, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(read_private_artifact(&original, 8).is_err());
        let receipt = retained_receipt(&json!({
            "transactionId":LARGE_DIGEST,
            "eventId":"1",
            "acceptedCount":"2",
            "imageBoundary":LARGE_DIGEST,
        }))
        .unwrap();
        assert_eq!(receipt.transaction_id(), LARGE_DIGEST);
        assert!(retained_receipt(&json!({
            "transactionId":"01", "eventId":"1", "acceptedCount":"2",
            "imageBoundary":"3"
        }))
        .is_err());
        fs::remove_dir_all(dir).unwrap();
    }
}
