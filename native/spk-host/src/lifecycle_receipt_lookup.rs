//! The receipt-only lookups of an uncertain BEGIN (op22 -> op23), CLAIM
//! (op26 -> op27) and COMPLETION (op38 -> op39) submit, for both the v3 and
//! the governed repeat (v4) lifecycle lanes.
//!
//! The Host answers op23/op27/op39 for either lane with one frame
//! (`DREGG/NATIVE-HOST/OUTCOME/v4`, `confirmed replayed`): it selects the
//! lane by the ingress tag. So the lookup is one function, and a lane differs
//! only in which retained attempt directory, markers and ingress file it
//! names. A lookup reads the exact ingress the one original submit carried;
//! it never submits, assembles or signs anything.

use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::lifecycle_v3_native::{decimal, framed_payload, hex, text};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::Path;

pub(crate) const OUTCOME_TAG: &[u8] = b"DREGG/NATIVE-HOST/OUTCOME/v4";
const MAX_FRAME: u64 = 12_102_760;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

/// Read one retained private file: regular, single-link, operator-owned,
/// mode 0600, non-empty, at most `max` bytes, and unchanged while read.
pub(crate) fn retained(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || metadata.nlink() != 1
        || metadata.uid() != unsafe { libc::geteuid() }
        || metadata.permissions().mode() & 0o777 != 0o600
        || metadata.len() == 0
        || metadata.len() > max
    {
        return Err(invalid("retained lifecycle artifact identity refused"));
    }
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let opened = file.metadata()?;
    if opened.dev() != metadata.dev() || opened.ino() != metadata.ino() {
        return Err(invalid("retained lifecycle artifact changed"));
    }
    let mut bytes = Vec::with_capacity(metadata.len() as usize);
    file.by_ref().take(max + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != metadata.len() {
        return Err(invalid("retained lifecycle artifact length changed"));
    }
    Ok(bytes)
}

/// `[transactionId, eventId, acceptedCount, worldRoot]` of a confirmed outcome
/// whose confirmation is exactly `confirmation` (`installed` for a fresh
/// admission, `replayed` for a lookup).
pub(crate) fn outcome_receipt(outcome: &Value, confirmation: &str) -> io::Result<[String; 4]> {
    if text(outcome, "type")? != "confirmed" || text(outcome, "confirmation")? != confirmation {
        return Err(invalid("lifecycle outcome confirmation refused"));
    }
    let receipt = |name| -> io::Result<String> {
        let value = text(outcome, name)?;
        if !decimal(value) {
            return Err(invalid("lifecycle receipt noncanonical"));
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

/// Historical receipt only. It cannot arm a CLAIM or a physical launch.
pub(crate) struct RecoveredReceipt {
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub world_root: String,
    pub inspection_name: String,
    pub inspection_sha256: String,
}

/// Reads the retained one-shot attempt and returns its exact submitted
/// ingress after checking the active marker, the prepare marker and the
/// submit marker. Never assembles, signs or chooses a new ingress.
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
        .ok_or_else(|| invalid("retained lifecycle attempt parent absent"))?;
    private_dir(parent)?;
    if retained(&parent.join(active_marker), 4096)?
        != retained(&attempt_dir.join(prepare_marker), 4096)?
    {
        return Err(invalid("retained lifecycle active marker differs from attempt"));
    }
    let marker: Value = serde_json::from_slice(&retained(&attempt_dir.join(submit_marker), 4096)?)?;
    let ingress = retained(&attempt_dir.join(ingress_file), MAX_FRAME)?;
    if text(&marker, "protocol")? != submit_protocol
        || text(&marker, "ingressSha256")? != hex(&Sha256::digest(&ingress))
    {
        return Err(invalid("retained lifecycle original submit marker differs"));
    }
    Ok(ingress)
}

/// Read-only lookup of one retained exact ingress: opcode `lookup` with the
/// same bytes the one submit carried. Each probe owns fresh output paths, so a
/// lookup may be repeated after another lost reply.
pub(crate) fn lookup_retained(
    operator: &PrivateOperator,
    attempt_dir: &Path,
    lookup: u8,
    ingress: &[u8],
) -> io::Result<RecoveredReceipt> {
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
        .ok_or_else(|| invalid("lifecycle lookup name absent"))?;
    Ok(RecoveredReceipt {
        transaction_id,
        event_id,
        accepted_count,
        world_root,
        inspection_name: format!("{lookup_name}/outcome.json"),
        inspection_sha256: hex(&Sha256::digest(&inspected)),
    })
}
