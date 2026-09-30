//! Current-image source authoring for resident INSTALL/START BEGIN-v2.
//!
//! No Rust code constructs DRC headers, state roots, generation or manifest.
//! Op50 derives them from one Verified Mini tip and fixed Host management pin;
//! this module signs only inspected exact headers and retains a one-shot op22
//! result. Historical op23 lookup cannot authorize a physical action.
#![allow(dead_code)] // Physical INSTALL/START caller is being integrated.

use crate::dispatch_author::{private_signing_key, SignerPin};
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use ed25519_dalek::Signer;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{DirBuilder, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

const MAX_FRAME: usize = 12_102_760;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(out, "{byte:02x}").expect("writing to String");
    }
    out
}

fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn text<'a>(value: &'a Value, name: &str) -> io::Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("resident BEGIN inspection field absent"))
}

fn number(value: &Value) -> io::Result<String> {
    let number = value
        .as_str()
        .map(str::to_owned)
        .or_else(|| value.as_u64().map(|value| value.to_string()))
        .ok_or_else(|| invalid("resident BEGIN management number malformed"))?;
    if !decimal(&number) {
        return Err(invalid("resident BEGIN number noncanonical"));
    }
    Ok(number)
}

fn unhex(value: &str) -> io::Result<Vec<u8>> {
    if !value.len().is_multiple_of(2)
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(invalid("resident BEGIN header hex refused"));
    }
    value
        .as_bytes()
        .as_chunks::<2>()
        .0
        .iter()
        .map(|pair| {
            let pair = std::str::from_utf8(pair).map_err(|_| invalid("header hex pair"))?;
            u8::from_str_radix(pair, 16).map_err(|_| invalid("header hex pair"))
        })
        .collect()
}

/// The operator-owned ledger allocates one monotonic identity before source
/// planning. A crash consumes an ID; it never reuses or silently retries it.
pub(crate) fn allocate_operation_id(ledger: &Path) -> io::Result<String> {
    let parent = ledger
        .parent()
        .ok_or_else(|| invalid("operation ledger parent absent"))?;
    private_dir(parent)?;
    let mut lock_name = ledger.as_os_str().to_os_string();
    lock_name.push(".lock");
    let lock_path = PathBuf::from(lock_name);
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&lock_path)?;
    let lock_named = std::fs::symlink_metadata(&lock_path)?;
    let lock_meta = lock.metadata()?;
    if !lock_meta.is_file()
        || lock_meta.nlink() != 1
        || lock_meta.uid() != unsafe { libc::geteuid() }
        || lock_meta.permissions().mode() & 0o777 != 0o600
        || (lock_named.dev(), lock_named.ino()) != (lock_meta.dev(), lock_meta.ino())
    {
        return Err(invalid("operation ledger lock identity refused"));
    }
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let mut file = match OpenOptions::new()
        .read(true)
        .append(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(ledger)
    {
        Ok(mut file) => {
            // The first allocation is ID 1. Persist the next ID before
            // returning it; an interrupted empty creation stays refused.
            file.write_all(b"2\n")?;
            file.sync_all()?;
            File::open(parent)?.sync_all()?;
            return Ok("1".to_owned());
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => OpenOptions::new()
            .read(true)
            .append(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(ledger)?,
        Err(error) => return Err(error),
    };
    let named = std::fs::symlink_metadata(ledger)?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o777 != 0o600
        || meta.len() == 0
        || meta.len() > 1_048_576
        || (named.dev(), named.ino()) != (meta.dev(), meta.ino())
    {
        return Err(invalid(
            "operation ledger identity or incomplete write refused",
        ));
    }
    let mut history = String::new();
    file.read_to_string(&mut history)?;
    if history.len() as u64 != meta.len() || !history.ends_with('\n') {
        return Err(invalid("operation ledger incomplete tail refused"));
    }
    let mut expected = 2u64;
    for record in history.lines() {
        if !decimal(record) || record.parse::<u64>().ok() != Some(expected) {
            return Err(invalid("operation ledger sequence refused"));
        }
        expected = expected
            .checked_add(1)
            .ok_or_else(|| invalid("operation ledger exhausted"))?;
    }
    let current = expected - 1;
    writeln!(file, "{expected}")?;
    file.sync_all()?;
    File::open(parent)?.sync_all()?;
    Ok(current.to_string())
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedBeginSigners {
    protocol: String,
    selector: crate::lifecycle_selector::LifecycleSelector,
    management_subject: String,
    signers: Vec<SignerPin>,
}

impl FixedBeginSigners {
    pub(crate) fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-resident-begin-management-v1" {
            return Err(invalid("fixed resident BEGIN management refused"));
        }
        crate::lifecycle_selector::validate_custody(
            operator,
            &self.selector,
            &self.management_subject,
            &self.signers,
            app_uid,
        )
    }

    fn sign_plan(
        &self,
        inspection: &Value,
        plan: &[u8],
        descriptor: &[u8],
        kind: &str,
        operation_id: &str,
    ) -> io::Result<Value> {
        if text(inspection, "type")? != "application-lifecycle-resident-begin-operator-plan-v1"
            || text(inspection, "canonicalPlan")? != hex(plan)
            || text(inspection, "descriptor")? != hex(descriptor)
            || text(inspection, "kind")? != kind
            || text(inspection, "operationId")? != operation_id
            || text(inspection, "app")? != self.selector.app
            || text(inspection, "packageManifest")? != self.selector.package_manifest
            || text(inspection, "snapshotManifest")? != self.selector.snapshot_manifest
            || text(inspection, "managementSubject")? != self.management_subject
        {
            return Err(invalid("resident BEGIN plan differs from fixed request"));
        }
        let slots = inspection
            .get("slots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("resident BEGIN slots absent"))?;
        if slots.len() != self.signers.len() {
            return Err(invalid("BEGIN slot count differs"));
        }
        let mut signatures = Vec::with_capacity(slots.len());
        for (slot, pin) in slots.iter().zip(&self.signers) {
            let signing = slot
                .get("signing")
                .ok_or_else(|| invalid("BEGIN signing slot inspection absent"))?;
            let header = text(slot, "header")?;
            if text(slot, "role")? != pin.role
                || text(slot, "index")? != pin.index
                || signing.get("decoded").and_then(Value::as_bool) != Some(true)
                || text(signing, "canonical")? != header
                || text(signing, "keyId")? != pin.key_id
                || text(signing, "keyEpoch")? != pin.key_epoch
                || text(signing, "algorithm")? != "1"
            {
                return Err(invalid("BEGIN slot differs from fixed signer"));
            }
            let bytes = unhex(header)?;
            if bytes.is_empty() || bytes.len() > 65_536 {
                return Err(invalid("BEGIN header bound refused"));
            }
            let key = private_signing_key(&pin.seed_path)?;
            if hex(&key.verifying_key().to_bytes()) != pin.public_key_hex {
                return Err(invalid("BEGIN signer private/public pin differs"));
            }
            signatures.push(Value::String(hex(&key.sign(&bytes).to_bytes())));
        }
        Ok(Value::Array(signatures))
    }
}

fn reply_payload(reply: &[u8], opcode: u8) -> io::Result<&[u8]> {
    if reply.len() < 6 {
        return Err(invalid("truncated resident BEGIN reply"));
    }
    let len = u32::from_le_bytes(reply[..4].try_into().unwrap()) as usize;
    if !(2..=MAX_FRAME).contains(&len) || len + 4 != reply.len() || reply[4] != opcode {
        return Err(invalid("resident BEGIN reply frame refused"));
    }
    Ok(&reply[5..])
}

pub(crate) struct AcceptedBegin {
    pub ingress: Vec<u8>,
    pub operation_id: String,
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub world_root: String,
}

fn prior_index(accepted_count: &str) -> io::Result<String> {
    if !decimal(accepted_count) || accepted_count == "0" {
        return Err(invalid(
            "BEGIN accepted count cannot select an original record",
        ));
    }
    let mut bytes = accepted_count.as_bytes().to_vec();
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
        .map_err(|_| invalid("BEGIN accepted count index malformed"))
}

/// One source-authored BEGIN install/start. The attempt directory and
/// operation ledger refuse re-entry after any uncertain broker response.
pub(crate) fn submit_once(
    operator: &PrivateOperator,
    fixed: &FixedBeginSigners,
    app_uid: u32,
    descriptor: &[u8],
    kind: &str,
    ledger: &Path,
    attempt_dir: &Path,
) -> io::Result<AcceptedBegin> {
    fixed.validate(operator, app_uid)?;
    if !matches!(kind, "install" | "start")
        || descriptor.is_empty()
        || descriptor.len() >= MAX_FRAME
    {
        return Err(invalid("BEGIN descriptor/kind refused"));
    }
    private_dir(
        attempt_dir
            .parent()
            .ok_or_else(|| invalid("BEGIN attempt parent absent"))?,
    )?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let operation_id = allocate_operation_id(ledger)?;
    let source = json!({"kind":kind,"operationId":operation_id,
        "descriptor":hex(descriptor)});
    let input = write_new(attempt_dir, "request.json", &serde_json::to_vec(&source)?)?;
    let request = operator.tool(
        "author",
        "application-lifecycle-resident-begin-operator-request",
        &input,
        &attempt_dir.join("request.bin"),
    )?;
    write_new(attempt_dir, "op50-requested.bin", &request)?;
    let reply = operator.invoke(50, &fixed.selector.framed(&request)?)?;
    write_new(attempt_dir, "op50-frame.bin", &reply)?;
    let plan = reply_payload(&reply, 50)?;
    let plan_path = write_new(attempt_dir, "plan.bin", plan)?;
    let inspected = operator.tool(
        "inspect",
        "application-lifecycle-resident-begin-operator-plan",
        &plan_path,
        &attempt_dir.join("plan.json"),
    )?;
    let inspection: Value = serde_json::from_slice(&inspected)?;
    let signatures = fixed.sign_plan(&inspection, plan, descriptor, kind, &operation_id)?;
    let signatures_input = write_new(
        attempt_dir,
        "signatures.json",
        &serde_json::to_vec(&signatures)?,
    )?;
    let encoded = operator.tool(
        "signatures",
        "",
        &signatures_input,
        &attempt_dir.join("signatures.bin"),
    )?;
    let mut pair = Vec::with_capacity(4 + plan.len() + encoded.len());
    pair.extend_from_slice(&(plan.len() as u32).to_le_bytes());
    pair.extend_from_slice(plan);
    pair.extend_from_slice(&encoded);
    write_new(attempt_dir, "op51-requested.bin", &pair)?;
    let reply = operator.invoke(51, &pair)?;
    write_new(attempt_dir, "op51-frame.bin", &reply)?;
    let ingress = reply_payload(&reply, 51)?.to_vec();
    let ingress_path = write_new(attempt_dir, "begin-v2.bin", &ingress)?;
    let echo_source = write_new(
        attempt_dir,
        "resident-echo.json",
        &serde_json::to_vec(&json!({"begin":hex(&ingress)}))?,
    )?;
    if operator.tool(
        "author",
        "application-lifecycle-resident-begin",
        &echo_source,
        &attempt_dir.join("resident-echo.bin"),
    )? != ingress
    {
        return Err(invalid("source resident BEGIN echo differs"));
    }
    let marker = json!({"protocol":"mini-spk-begin-submit-requested-v1",
        "operationId":operation_id,"ingressSha256":hex(&Sha256::digest(&ingress))});
    write_new(
        attempt_dir,
        "op22-requested.json",
        &serde_json::to_vec(&marker)?,
    )?;
    let reply = operator.invoke(22, &ingress)?;
    write_new(attempt_dir, "op22-frame.bin", &reply)?;
    let payload = reply_payload(&reply, 22)?;
    let outcome_path = write_new(attempt_dir, "op22-outcome.bin", payload)?;
    let inspected = operator.tool(
        "inspect",
        "outcome",
        &outcome_path,
        &attempt_dir.join("op22-outcome.json"),
    )?;
    let outcome: Value = serde_json::from_slice(&inspected)?;
    if text(&outcome, "type")? != "confirmed" || text(&outcome, "confirmation")? != "installed" {
        return Err(invalid("resident BEGIN not freshly accepted"));
    }
    let receipt = |name| -> io::Result<String> {
        let value = text(&outcome, name)?;
        if !decimal(value) {
            return Err(invalid("BEGIN receipt noncanonical"));
        }
        Ok(value.to_owned())
    };
    // Keep the exact original ingress even though an op23 lookup could later
    // identify its receipt; historical lookup never becomes a physical permit.
    let _ = ingress_path;
    Ok(AcceptedBegin {
        ingress,
        operation_id,
        transaction_id: receipt("transactionId")?,
        event_id: receipt("eventId")?,
        accepted_count: receipt("acceptedCount")?,
        world_root: receipt("worldRoot")?,
    })
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedClaimSigners {
    protocol: String,
    selector: crate::lifecycle_selector::LifecycleSelector,
    management_subject: String,
    signers: Vec<SignerPin>,
}

impl FixedClaimSigners {
    pub(crate) fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-resident-claim-management-v1" {
            return Err(invalid("fixed resident CLAIM management refused"));
        }
        crate::lifecycle_selector::validate_custody(
            operator,
            &self.selector,
            &self.management_subject,
            &self.signers,
            app_uid,
        )
    }

    fn sign_plan(
        &self,
        inspection: &Value,
        plan: &[u8],
        begin: &AcceptedBegin,
        original_index: &str,
        query_nonce: &str,
    ) -> io::Result<Value> {
        if text(inspection, "type")? != "application-lifecycle-claim-operator-plan-v1"
            || text(inspection, "canonicalPlan")? != hex(plan)
            || text(inspection, "originalBegin")? != hex(&begin.ingress)
            || text(inspection, "app")? != self.selector.app
            || text(inspection, "originalIndex")? != original_index
            || text(inspection, "queryNonce")? != query_nonce
            || text(inspection, "managementSubject")? != self.management_subject
        {
            return Err(invalid("resident CLAIM plan differs from fixed request"));
        }
        let slots = inspection
            .get("slots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("resident CLAIM slots absent"))?;
        if slots.len() != self.signers.len() {
            return Err(invalid("CLAIM slot count differs"));
        }
        let mut signatures = Vec::with_capacity(slots.len());
        for (slot, pin) in slots.iter().zip(&self.signers) {
            let signing = slot
                .get("signing")
                .ok_or_else(|| invalid("CLAIM signing slot inspection absent"))?;
            let header = text(slot, "header")?;
            if text(slot, "role")? != pin.role
                || text(slot, "index")? != pin.index
                || signing.get("decoded").and_then(Value::as_bool) != Some(true)
                || text(signing, "canonical")? != header
                || text(signing, "keyId")? != pin.key_id
                || text(signing, "keyEpoch")? != pin.key_epoch
                || text(signing, "algorithm")? != "1"
            {
                return Err(invalid("CLAIM slot differs from fixed signer"));
            }
            let bytes = unhex(header)?;
            if bytes.is_empty() || bytes.len() > 65_536 {
                return Err(invalid("CLAIM header bound refused"));
            }
            let key = private_signing_key(&pin.seed_path)?;
            if hex(&key.verifying_key().to_bytes()) != pin.public_key_hex {
                return Err(invalid("CLAIM signer private/public pin differs"));
            }
            signatures.push(Value::String(hex(&key.sign(&bytes).to_bytes())));
        }
        Ok(Value::Array(signatures))
    }
}

/// Source-authors one op26 ingress from the exact confirmed op22 BEGIN. The
/// caller then passes these bytes to `claim_native::submit_once`, which owns
/// the durable one-shot submit marker and exact committed-v2 readback.
pub(crate) fn assemble_current_claim(
    operator: &PrivateOperator,
    fixed: &FixedClaimSigners,
    app_uid: u32,
    begin: &AcceptedBegin,
    nonce_ledger: &Path,
    attempt_dir: &Path,
) -> io::Result<Vec<u8>> {
    fixed.validate(operator, app_uid)?;
    let original_index = prior_index(&begin.accepted_count)?;
    private_dir(
        attempt_dir
            .parent()
            .ok_or_else(|| invalid("CLAIM attempt parent absent"))?,
    )?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let query_nonce = allocate_operation_id(nonce_ledger)?;
    let request = json!({"originalIndex":original_index,"queryNonce":query_nonce});
    let input = write_new(attempt_dir, "request.json", &serde_json::to_vec(&request)?)?;
    let canonical = operator.tool(
        "author",
        "application-lifecycle-claim-operator-request",
        &input,
        &attempt_dir.join("request.bin"),
    )?;
    write_new(attempt_dir, "op52-requested.bin", &canonical)?;
    let reply = operator.invoke(52, &fixed.selector.framed(&canonical)?)?;
    write_new(attempt_dir, "op52-frame.bin", &reply)?;
    let plan = reply_payload(&reply, 52)?;
    let plan_path = write_new(attempt_dir, "plan.bin", plan)?;
    let inspected = operator.tool(
        "inspect",
        "application-lifecycle-claim-operator-plan",
        &plan_path,
        &attempt_dir.join("plan.json"),
    )?;
    let inspection: Value = serde_json::from_slice(&inspected)?;
    let signatures = fixed.sign_plan(&inspection, plan, begin, &original_index, &query_nonce)?;
    let signatures_input = write_new(
        attempt_dir,
        "signatures.json",
        &serde_json::to_vec(&signatures)?,
    )?;
    let encoded = operator.tool(
        "signatures",
        "",
        &signatures_input,
        &attempt_dir.join("signatures.bin"),
    )?;
    let mut pair = Vec::with_capacity(4 + plan.len() + encoded.len());
    pair.extend_from_slice(&(plan.len() as u32).to_le_bytes());
    pair.extend_from_slice(plan);
    pair.extend_from_slice(&encoded);
    write_new(attempt_dir, "op53-requested.bin", &pair)?;
    let reply = operator.invoke(53, &pair)?;
    write_new(attempt_dir, "op53-frame.bin", &reply)?;
    let ingress = reply_payload(&reply, 53)?.to_vec();
    write_new(attempt_dir, "claim-v2.bin", &ingress)?;
    Ok(ingress)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::DirBuilderExt;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn scratch() -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "spk-operation-ledger-{}-{nonce}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&path).unwrap();
        path
    }

    #[test]
    fn only_exact_begin_opcode_and_canonical_numbers_pass() {
        let payload = b"DREGG/APPLICATION/RESIDENT-BEGIN-OPERATOR-PLAN/v1X";
        let mut reply = ((payload.len() + 1) as u32).to_le_bytes().to_vec();
        reply.push(50);
        reply.extend_from_slice(payload);
        assert_eq!(reply_payload(&reply, 50).unwrap(), payload);
        assert!(reply_payload(&reply, 51).is_err());
        reply.push(0);
        assert!(reply_payload(&reply, 50).is_err());
        assert!(decimal("18446744073709551616"));
        for value in ["", "00", "01", "-1", "+1"] {
            assert!(!decimal(value));
        }
    }

    #[test]
    fn original_history_index_is_confirmed_begin_count_minus_one() {
        assert_eq!(prior_index("1").unwrap(), "0");
        assert_eq!(
            prior_index("100000000000000000000").unwrap(),
            "99999999999999999999"
        );
        for invalid in ["0", "01", "", "-1"] {
            assert!(prior_index(invalid).is_err());
        }
    }

    #[test]
    fn interrupted_ledger_creation_or_append_refuses_reuse() {
        let directory = scratch();
        let ledger = directory.join("begin.log");
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&ledger)
            .unwrap();
        assert!(allocate_operation_id(&ledger).is_err());
        std::fs::write(&ledger, b"2").unwrap();
        assert!(allocate_operation_id(&ledger).is_err());
        std::fs::write(&ledger, b"2\n").unwrap();
        assert_eq!(allocate_operation_id(&ledger).unwrap(), "2");
        assert_eq!(std::fs::read(&ledger).unwrap(), b"2\n3\n");
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn concurrent_allocations_keep_distinct_durable_ids() {
        let directory = scratch();
        let ledger = directory.join("begin.log");
        let joins: Vec<_> = (0..16)
            .map(|_| {
                let ledger = ledger.clone();
                std::thread::spawn(move || {
                    allocate_operation_id(&ledger)
                        .unwrap()
                        .parse::<u64>()
                        .unwrap()
                })
            })
            .collect();
        let mut ids: Vec<_> = joins.into_iter().map(|join| join.join().unwrap()).collect();
        ids.sort_unstable();
        assert_eq!(ids, (1..=16).collect::<Vec<_>>());
        assert_eq!(allocate_operation_id(&ledger).unwrap(), "17");
        std::fs::remove_dir_all(directory).unwrap();
    }
}
