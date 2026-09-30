//! One private, no-retry lifecycle-v2 claim submit and source inspection.
//!
//! Only the operator broker's fresh op26 callback can supply the retained
//! committed frame. A historical op27 receipt, a caller-supplied JSON view,
//! and a structurally decodable frame cannot arm the physical journal.
#![allow(dead_code)] // Resident CLI is staged separately from the native link.

use crate::claim_descriptor::{compare_claim, compare_install_claim, MatchedPackage};
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::materialize::{signed_schema_source, InstalledPackage};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::fs::{DirBuilder, File, OpenOptions};
use std::io::{self, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::Path;

const MAX_FRAME: usize = 12_102_760;
const COMMITTED_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-CLAIM-COMMITTED/v2";
const OUTCOME_TAG: &[u8] = b"DREGG/NATIVE-HOST/OUTCOME/v3";

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

fn parse_op26(frame: &[u8]) -> io::Result<&[u8]> {
    let header = frame
        .get(..5)
        .ok_or_else(|| invalid("truncated Mini claim reply"))?;
    let length = u32::from_le_bytes(header[..4].try_into().unwrap()) as usize;
    if !(2..=MAX_FRAME).contains(&length) || length + 4 != frame.len() || header[4] != 26 {
        return Err(invalid("Mini claim reply framing refused"));
    }
    let payload = &frame[5..];
    if payload.starts_with(COMMITTED_TAG) && payload.len() > COMMITTED_TAG.len() {
        Ok(payload)
    } else if payload.starts_with(OUTCOME_TAG) {
        Err(invalid("Mini claim did not reserve a physical launch"))
    } else {
        Err(invalid("Mini claim reply lacks committed-v2 frame"))
    }
}

pub(crate) struct CapturedClaim {
    pub payload: Vec<u8>,
    pub inspection: Vec<u8>,
}

/// The marker is durable before op26. Any timeout, refusal or process death
/// leaves it in place; there is deliberately no automatic retry or op27
/// conversion to launch authority.
pub(crate) fn submit_once(
    operator: &PrivateOperator,
    canonical_ingress: &[u8],
    attempt_dir: &Path,
) -> io::Result<CapturedClaim> {
    if canonical_ingress.is_empty() || canonical_ingress.len() >= MAX_FRAME {
        return Err(invalid("Mini claim ingress size refused"));
    }
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("claim attempt parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    write_new(attempt_dir, "ingress.bin", canonical_ingress)?;
    let marker = json!({
        "protocol":"mini-spk-lifecycle-claim-submit-requested-v1",
        "ingressSha256":hex(&Sha256::digest(canonical_ingress))
    });
    write_new(
        attempt_dir,
        "submit-requested.json",
        &serde_json::to_vec(&marker)?,
    )?;
    let active = parent.join("lifecycle-claim-active.json");
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&active)?;
    file.write_all(&serde_json::to_vec(&marker)?)?;
    file.sync_all()?;
    File::open(parent)?.sync_all()?;

    let reply = operator.invoke(26, canonical_ingress)?;
    write_new(attempt_dir, "op26-frame.bin", &reply)?;
    let payload = parse_op26(&reply)?.to_vec();
    let payload_path = write_new(attempt_dir, "committed-v2.bin", &payload)?;
    let inspection_path = attempt_dir.join("claim-inspection.json");
    let inspection = operator.tool(
        "inspect",
        "application-lifecycle-claim-committed-v2",
        &payload_path,
        &inspection_path,
    )?;
    Ok(CapturedClaim {
        payload,
        inspection,
    })
}

/// Author the permission schema from the exact retained signed bridge bytes,
/// inspect Mini's canonical source result, then compare all v2 claim fields.
/// This is a physical package equality check, not a new authority source.
pub(crate) fn match_signed_package(
    operator: &PrivateOperator,
    package: &InstalledPackage,
    captured: &CapturedClaim,
    attempt_dir: &Path,
) -> io::Result<MatchedPackage> {
    match_signed_package_kind(operator, package, captured, attempt_dir, false)
}

pub(crate) fn match_signed_install_package(
    operator: &PrivateOperator,
    package: &InstalledPackage,
    captured: &CapturedClaim,
    attempt_dir: &Path,
) -> io::Result<MatchedPackage> {
    match_signed_package_kind(operator, package, captured, attempt_dir, true)
}

fn match_signed_package_kind(
    operator: &PrivateOperator,
    package: &InstalledPackage,
    captured: &CapturedClaim,
    attempt_dir: &Path,
    install: bool,
) -> io::Result<MatchedPackage> {
    private_dir(attempt_dir)?;
    let signed = package
        .signed_bridge_config
        .as_deref()
        .ok_or_else(|| invalid("bridge-only SPK lacks signed config"))?;
    let bridge = minidregg_spk_rpc::decode_bridge_config(signed).map_err(io::Error::other)?;
    let source = signed_schema_source(&bridge, package.manifest.app_version);
    let source_path = write_new(
        attempt_dir,
        "schema-source.json",
        &serde_json::to_vec(&source)?,
    )?;
    let schema_path = attempt_dir.join("schema.bin");
    let schema = operator.tool(
        "author",
        "application-permission-schema",
        &source_path,
        &schema_path,
    )?;
    let inspection_path = attempt_dir.join("schema-inspection.json");
    let inspected = operator.tool(
        "inspect",
        "application-permission-schema",
        &schema_path,
        &inspection_path,
    )?;
    let compare = if install {
        compare_install_claim
    } else {
        compare_claim
    };
    compare(
        package,
        &captured.payload,
        &captured.inspection,
        &schema,
        &inspected,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frame(op: u8, payload: &[u8]) -> Vec<u8> {
        let mut bytes = ((payload.len() + 1) as u32).to_le_bytes().to_vec();
        bytes.push(op);
        bytes.extend_from_slice(payload);
        bytes
    }

    #[test]
    fn only_exact_op26_committed_v2_frame_classifies_as_launch_candidate() {
        let mut committed = COMMITTED_TAG.to_vec();
        committed.push(7);
        assert_eq!(parse_op26(&frame(26, &committed)).unwrap(), committed);
        assert!(parse_op26(&frame(27, &committed)).is_err());
        assert!(parse_op26(&frame(26, OUTCOME_TAG)).is_err());
        assert!(parse_op26(&frame(26, COMMITTED_TAG)).is_err());
        let mut trailing = frame(26, &committed);
        trailing.push(0);
        assert!(parse_op26(&trailing).is_err());
    }
}
