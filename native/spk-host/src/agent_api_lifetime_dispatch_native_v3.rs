//! Fresh event26 lifetime permit. A retained op77 receipt cannot construct
//! this type and can never authorize fd3 delivery.
#![allow(dead_code)] // The resident v3 entrance is wired separately.

use crate::agent_api_lifetime_paid_native_v3::AssembledLifetimePaidV3;
use crate::agent_api_lifetime_reverse_v3::RetainedReserveV3;
use crate::agent_api_lifetime_v3::{
    match_committed_inspection, CommittedMatch, LifetimeBinding, ReceiptPin,
};
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};

const COMMITTED: &[u8] = b"DREGG/APPLICATION/AGENT-LIFETIME-DISPATCH-COMMITTED-PERMIT/v3";

fn refused(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn later_count(later: &str, earlier: &str) -> bool {
    later.len() > earlier.len()
        || later.len() == earlier.len() && later.as_bytes() > earlier.as_bytes()
}

fn source_payload(frame: &[u8], opcode: u8) -> io::Result<&[u8]> {
    if frame.len() < 6
        || u32::from_le_bytes(frame[..4].try_into().unwrap()) as usize + 4 != frame.len()
        || frame[4] != opcode
    {
        return Err(refused("lifetime submit reply opcode/frame drift"));
    }
    Ok(&frame[5..])
}

pub(crate) struct FreshLifetimePermitV3 {
    frame: Vec<u8>,
    inspection: Value,
    receipt: ReceiptPin,
    active_marker: PathBuf,
    active_bytes: Vec<u8>,
    active_identity: (u64, u64),
}

impl FreshLifetimePermitV3 {
    pub(crate) fn frame(&self) -> &[u8] {
        &self.frame
    }

    pub(crate) fn inspection(&self) -> &Value {
        &self.inspection
    }

    pub(crate) fn receipt(&self) -> &ReceiptPin {
        &self.receipt
    }

    /// Clear only after a retained definite reply and confirmed controller
    /// settlement. The one-shot per-operation submit marker is never erased.
    pub(crate) fn clear_active_after_settlement(&self) -> io::Result<()> {
        let metadata = fs::symlink_metadata(&self.active_marker)?;
        if !metadata.is_file()
            || (metadata.dev(), metadata.ino()) != self.active_identity
            || fs::read(&self.active_marker)? != self.active_bytes
        {
            return Err(refused("lifetime active marker changed before settlement"));
        }
        fs::remove_file(&self.active_marker)?;
        File::open(
            self.active_marker
                .parent()
                .ok_or_else(|| refused("lifetime marker parent absent"))?,
        )?
        .sync_all()
    }
}

/// Historical cleanup after exact controller settlement inspection and
/// hostd's recovered Delivered transition. This only clears the same
/// per-route op76 marker; it cannot create a fresh permit.
pub(crate) fn clear_retained_active_after_settlement(attempt_dir: &Path) -> io::Result<()> {
    private_dir(attempt_dir)?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| refused("lifetime attempt parent absent"))?;
    private_dir(parent)?;
    let expected = crate::agent_api_server::read_private_recovery(
        &attempt_dir.join("op76-submit-requested-v3.json"),
        4096,
    )?;
    let path = parent.join("native-agent-lifetime-active.json");
    let mut file = match OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&path)
    {
        Ok(file) => file,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    };
    let metadata = file.metadata()?;
    if !metadata.is_file()
        || metadata.nlink() != 1
        || metadata.uid() != unsafe { libc::geteuid() }
        || metadata.permissions().mode() & 0o777 != 0o600
        || metadata.len() != expected.len() as u64
    {
        return Err(refused("retained lifetime active marker identity drift"));
    }
    let mut actual = Vec::new();
    file.read_to_end(&mut actual)?;
    if actual != expected || fs::symlink_metadata(&path)?.ino() != metadata.ino() {
        return Err(refused("retained lifetime active marker bytes drift"));
    }
    fs::remove_file(path)?;
    File::open(parent)?.sync_all()
}

pub(crate) fn submit_fresh_once(
    operator: &PrivateOperator,
    binding: &LifetimeBinding,
    reserve: &RetainedReserveV3,
    paid: &AssembledLifetimePaidV3,
    decoded_http: &Value,
    attempt_dir: &Path,
    cancelled: &AtomicBool,
) -> io::Result<FreshLifetimePermitV3> {
    if cancelled.load(Ordering::Acquire) || paid.ingress.is_empty() {
        return Err(refused("lifetime submit cancelled or ingress absent"));
    }
    private_dir(attempt_dir)?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| refused("lifetime attempt parent absent"))?;
    private_dir(parent)?;
    let marker_bytes = serde_json::to_vec(&json!({
        "protocol":"mini-spk-lifetime-op76-submit-requested-v3",
        "httpOperationId":reserve.http_operation_id,
        "bindingSha256":reserve.binding_sha256,
        "operationFingerprint":reserve.operation_fingerprint,
        "ingressSha256":hex(&Sha256::digest(&paid.ingress)),
    }))?;
    write_new(attempt_dir, "op76-submit-requested-v3.json", &marker_bytes)?;
    let active_marker = parent.join("native-agent-lifetime-active.json");
    let mut active = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&active_marker)?;
    active.write_all(&marker_bytes)?;
    active.sync_all()?;
    let metadata = active.metadata()?;
    let active_identity = (metadata.dev(), metadata.ino());
    File::open(parent)?.sync_all()?;
    if cancelled.load(Ordering::Acquire) {
        // No op76 call has begun. Keep the attempt as terminal for this ID.
        return Err(refused("lifetime caller cancelled before op76"));
    }
    let outer = operator.invoke(76, &paid.ingress)?;
    write_new(attempt_dir, "op76-frame-v3.bin", &outer)?;
    let frame = source_payload(&outer, 76)?;
    if !frame.starts_with(COMMITTED) || frame.len() <= COMMITTED.len() {
        return Err(refused(
            "op76 did not return fresh lifetime committed permit",
        ));
    }
    let frame = frame.to_vec();
    let input = write_new(attempt_dir, "committed-v3.bin", &frame)?;
    let view_bytes = operator.tool(
        "inspect",
        "application-agent-lifetime-dispatch-committed",
        &input,
        &attempt_dir.join("committed-v3.json"),
    )?;
    let inspection: Value = serde_json::from_slice(&view_bytes)?;
    let purse = inspection
        .get("purse")
        .ok_or_else(|| refused("lifetime committed purse absent"))?;
    if purse.get("reserveOperationId").and_then(Value::as_str)
        != Some(reserve.reserve_operation_id.as_str())
        || purse.get("reserveIndex").and_then(Value::as_str) != Some(reserve.reserve_index.as_str())
        || purse.get("reserveReceipt") != Some(&serde_json::to_value(&reserve.reserve_receipt)?)
        || inspection.get("reserveContextHex").and_then(Value::as_str)
            != Some(hex(&reserve.context_bytes).as_str())
        || inspection
            .pointer("/request/canonicalHex")
            .and_then(Value::as_str)
            != paid
                .inspection
                .get("canonicalHttpHex")
                .and_then(Value::as_str)
    {
        return Err(refused(
            "lifetime fresh permit differs from retained reserve",
        ));
    }
    let receipt: ReceiptPin = serde_json::from_value(
        inspection
            .get("dispatchReceipt")
            .cloned()
            .ok_or_else(|| refused("lifetime committed receipt absent"))?,
    )?;
    receipt.validate()?;
    if !later_count(
        &receipt.accepted_count,
        &reserve.reserve_receipt.accepted_count,
    ) {
        return Err(refused("lifetime fresh dispatch receipt not after reserve"));
    }
    match_committed_inspection(CommittedMatch {
        binding,
        current: &reserve.current_claims,
        inspected: &inspection,
        decoded_http,
        canonical_http_hex: paid
            .inspection
            .get("canonicalHttpHex")
            .and_then(Value::as_str)
            .ok_or_else(|| refused("lifetime canonical HTTP absent"))?,
        expected_receipt: &receipt,
        exact_frame: &frame,
        signed_post_reserve_purse_physical_root: &paid.signed_post_reserve_purse_physical_root,
    })?;
    Ok(FreshLifetimePermitV3 {
        frame,
        inspection,
        receipt,
        active_marker,
        active_bytes: marker_bytes,
        active_identity,
    })
}

#[cfg(test)]
mod tests {
    use super::{later_count, source_payload, COMMITTED};

    #[test]
    fn only_fresh_op76_payload_with_distinct_permit_tag_can_advance() {
        let mut outer = Vec::new();
        outer.extend_from_slice(&((COMMITTED.len() + 2) as u32).to_le_bytes());
        outer.push(76);
        outer.extend_from_slice(COMMITTED);
        outer.push(1);
        assert!(source_payload(&outer, 76).unwrap().starts_with(COMMITTED));
        assert!(source_payload(&outer, 77).is_err());
        outer[4] = 77;
        assert!(source_payload(&outer, 76).is_err());
    }

    #[test]
    fn committed_receipt_order_uses_full_decimal_nat() {
        assert!(later_count(
            "340282366920938463463374607431768211456",
            "340282366920938463463374607431768211455"
        ));
        assert!(!later_count("13", "13"));
        assert!(!later_count("12", "13"));
    }
}
