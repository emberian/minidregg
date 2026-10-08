//! Grain export and import: a stopped volume's exact bytes bound to the STOP
//! receipt that fenced them, signed by the exporting Store's completion
//! custodian. Import checks the signature, the image bytes, the package and
//! the class before any Mini effect, and the restored grain is always a new
//! application resource (Mini: recreating a grain needs a new resource ID).
//! It also holds the host side of a failed START's reconciliation
//! (`reconcile_failed_start`), which retains its artifacts beside the
//! generation's journal the same way.
//!
//! Kernel-side, `import_binds_stop_receipt` (K-SPK, `ApplicationGrainExport`)
//! makes the STOP receipt a checked fact on the importing Store; until then
//! the binding is the exporter's signature over the receipt bytes.

use ed25519_dalek::{Signature, Signer, VerifyingKey};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::Path;

const MAX_MANIFEST: u64 = 64 * 1024;

fn invalid(reason: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason.into())
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn unhex<const N: usize>(text: &str) -> io::Result<[u8; N]> {
    let text = text.trim();
    if text.len() != N * 2 {
        return Err(invalid("hex length refused"));
    }
    let mut out = [0u8; N];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&text[index * 2..index * 2 + 2], 16)
            .map_err(|_| invalid("hex refused"))?;
    }
    Ok(out)
}

fn sha256_file(path: &Path) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut digest = Sha256::new();
    let mut chunk = vec![0u8; 1 << 20];
    loop {
        let count = file.read(&mut chunk)?;
        if count == 0 {
            break;
        }
        digest.update(&chunk[..count]);
    }
    Ok(format!("{:x}", digest.finalize()))
}

fn bounded(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(path)?.take(max + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > max {
        return Err(invalid(format!("{} exceeds its bound", path.display())));
    }
    Ok(bytes)
}

fn write_new(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)?;
    file.write_all(bytes)?;
    file.sync_all()
}

/// Lay out `OUT/{var.ext4, manifest.json, manifest.sig}` from the broker's
/// copy of a stopped volume.
pub(crate) fn write_export(
    out: &Path,
    copied: &Value,
    base: &Value,
    stop_receipt: &[u8],
    custodian_seed: &Path,
) -> io::Result<Value> {
    let source = copied
        .get("image")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("broker export reply lacks image"))?;
    let sha = copied
        .get("sha256")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("broker export reply lacks sha256"))?;
    let receipt: Value =
        serde_json::from_slice(stop_receipt).map_err(|_| invalid("STOP receipt is not JSON"))?;
    DirBuilder::new().mode(0o700).create(out)?;
    let image = out.join("var.ext4");
    if fs::rename(source, &image).is_err() {
        fs::copy(source, &image)?;
        fs::remove_file(source)?;
    }
    if sha256_file(&image)? != sha {
        return Err(invalid("exported image differs from the broker's digest"));
    }
    let mut manifest = base.clone();
    manifest["protocol"] = json!("mini-spk-grain-export-v1");
    manifest["image"] = json!({"file":"var.ext4","sha256":sha,
        "bytes":fs::metadata(&image)?.len().to_string()});
    manifest["stopReceipt"] = receipt;
    manifest["stopReceiptSha256"] = json!(format!("{:x}", Sha256::digest(stop_receipt)));
    let bytes = serde_json::to_vec_pretty(&manifest)?;
    let key = crate::dispatch_author::private_signing_key(custodian_seed)?;
    let signature = key.sign(&bytes);
    write_new(&out.join("manifest.json"), &bytes)?;
    write_new(
        &out.join("manifest.sig"),
        hex(&signature.to_bytes()).as_bytes(),
    )?;
    write_new(
        &out.join("exporter.pub"),
        hex(key.verifying_key().as_bytes()).as_bytes(),
    )?;
    Ok(
        json!({"protocol":"mini-spk-grain-export-result-v1","dir":out,
        "manifestSha256":format!("{:x}", Sha256::digest(&bytes)),
        "imageSha256":sha,"stopReceiptSha256":manifest["stopReceiptSha256"],
        "exporterKey":hex(key.verifying_key().as_bytes())}),
    )
}

pub(crate) struct Imported {
    pub(crate) record: Value,
    pub(crate) image_sha256: String,
}

/// Every refusal names what failed; nothing reaches Mini or the broker first.
pub(crate) fn verify_import(
    dir: &Path,
    exporter_key: &str,
    raw_sha256: &str,
    class: &str,
    imports: &Path,
) -> io::Result<Imported> {
    let bytes = bounded(&dir.join("manifest.json"), MAX_MANIFEST)?;
    let signature = Signature::from_bytes(&unhex::<64>(&String::from_utf8_lossy(&bounded(
        &dir.join("manifest.sig"),
        256,
    )?))?);
    let key = VerifyingKey::from_bytes(&unhex::<32>(exporter_key)?)
        .map_err(|_| invalid("exporter key refused"))?;
    key.verify_strict(&bytes, &signature)
        .map_err(|_| invalid("import refused: exporter signature does not verify"))?;
    let manifest: Value = serde_json::from_slice(&bytes)?;
    let text = |pointer: &str| -> io::Result<String> {
        manifest
            .pointer(pointer)
            .and_then(Value::as_str)
            .map(str::to_owned)
            .ok_or_else(|| invalid(format!("import manifest lacks {pointer}")))
    };
    if text("/protocol")? != "mini-spk-grain-export-v1" {
        return Err(invalid("import manifest protocol refused"));
    }
    if text("/packageRawSha256")? != raw_sha256 {
        return Err(invalid("import refused: archive is of a different package"));
    }
    if text("/class")? != class {
        return Err(invalid("import refused: archive size class differs"));
    }
    let receipt = serde_json::to_vec(
        manifest
            .get("stopReceipt")
            .ok_or_else(|| invalid("import manifest lacks the STOP receipt"))?,
    )?;
    if receipt.is_empty() || text("/stopReceiptSha256")?.len() != 64 {
        return Err(invalid("import manifest STOP binding refused"));
    }
    let image_sha = text("/image/sha256")?;
    if sha256_file(&dir.join("var.ext4"))? != image_sha {
        return Err(invalid(
            "import refused: image bytes differ from the signed manifest",
        ));
    }
    match DirBuilder::new().mode(0o700).create(imports) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error),
    }
    let staged = imports.join(format!("{image_sha}.ext4"));
    if !staged.exists() {
        let temp = imports.join(format!(".{image_sha}.tmp"));
        let _ = fs::remove_file(&temp);
        fs::copy(dir.join("var.ext4"), &temp)?;
        File::open(&temp)?.sync_all()?;
        fs::rename(&temp, &staged)?;
    }
    if sha256_file(&staged)? != image_sha {
        return Err(invalid("staged import differs from the signed manifest"));
    }
    Ok(Imported {
        record: json!({"protocol":"mini-spk-grain-import-v1","exporterKey":exporter_key,
            "manifestSha256":format!("{:x}", Sha256::digest(&bytes)),"manifest":manifest,
            "signature":"verified"}),
        image_sha256: image_sha,
    })
}

/// Fixed source-owned operator routes. These are supplied by the shared Host
/// dispatch, never selected by an app or a recovery JSON document.
pub(crate) struct FailedStartRecoveryRoutes {
    pub prepare: u8,
    pub assemble: u8,
    pub submit: u8,
    pub lookup: u8,
}

pub(crate) const FAILED_START_RECOVERY_ROUTES: FailedStartRecoveryRoutes =
    FailedStartRecoveryRoutes {
        prepare: 206,
        assemble: 207,
        submit: 208,
        lookup: 209,
    };

fn recovery_read(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
    if !path.is_absolute() {
        return Err(invalid("recovery path is not absolute"));
    }
    crate::dispatch_native::private_dir(
        path.parent()
            .ok_or_else(|| invalid("recovery parent absent"))?,
    )?;
    let named = fs::symlink_metadata(path)?;
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let before = file.metadata()?;
    if !before.is_file()
        || before.uid() != unsafe { libc::geteuid() }
        || before.nlink() != 1
        || before.permissions().mode() & 0o777 != 0o600
        || named.dev() != before.dev()
        || named.ino() != before.ino()
        || before.len() == 0
        || before.len() > max
    {
        return Err(invalid("recovery retained file identity refused"));
    }
    let mut bytes = Vec::new();
    Read::by_ref(&mut file)
        .take(max + 1)
        .read_to_end(&mut bytes)?;
    let after = file.metadata()?;
    if bytes.len() as u64 != before.len()
        || after.len() != before.len()
        || after.mtime() != before.mtime()
        || after.mtime_nsec() != before.mtime_nsec()
        || after.ctime() != before.ctime()
        || after.ctime_nsec() != before.ctime_nsec()
    {
        return Err(invalid("recovery retained file changed during read"));
    }
    Ok(bytes)
}

fn retain_exact(dir: &Path, name: &str, bytes: &[u8]) -> io::Result<std::path::PathBuf> {
    let path = dir.join(name);
    match fs::symlink_metadata(&path) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => write_new(&path, bytes)?,
        Ok(_) => {
            if recovery_read(&path, 32 * 1024 * 1024)? != bytes {
                return Err(invalid(
                    "recovery retained artifact differs from exact rederivation",
                ));
            }
        }
        Err(e) => return Err(e),
    }
    File::open(dir)?.sync_all()?;
    Ok(path)
}

fn recovery_tool(
    operator: &crate::dispatch_native::PrivateOperator,
    command: &str,
    kind: &str,
    input: &Path,
    output: &Path,
) -> io::Result<Vec<u8>> {
    operator.pinned_config()?;
    match fs::symlink_metadata(output) {
        Ok(_) => recovery_read(output, 32 * 1024 * 1024),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            operator.tool(command, kind, input, output)
        }
        Err(e) => Err(e),
    }
}

#[derive(serde::Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RecoveryCustody {
    protocol: String,
    selector: crate::lifecycle_selector::LifecycleSelector,
    management_subject: String,
    signers: Vec<crate::dispatch_author::SignerPin>,
}

/// Recover only the exact entered/no-child START. No local state is rewritten.
/// Once submit is durably marked, all further calls are exact ingress lookups;
/// even a missing response cannot authorize a new request or physical launch.
pub(crate) fn reconcile_failed_start(
    operator: &crate::dispatch_native::PrivateOperator,
    resident_config: &Path,
    app: &str,
    generation: u64,
    routes: FailedStartRecoveryRoutes,
) -> io::Result<Value> {
    use crate::lifecycle_v3_native::{framed_payload, sign_pinned_slots, text, unhex};
    use std::os::fd::AsRawFd;
    use std::os::unix::fs::MetadataExt;
    const MAX: u64 = 32 * 1024 * 1024;
    const PLAN: &[u8] = b"DREGG/APPLICATION/FAILED-START-RECOVERY-PLAN/v1";
    const INGRESS: &[u8] = b"DREGG/APPLICATION/FAILED-START-RECOVERY-INGRESS/v1";
    const OUTCOME: &[u8] = b"DREGG/NATIVE-HOST/OUTCOME/v5";
    let config: Value = serde_json::from_slice(&recovery_read(resident_config, MAX_MANIFEST)?)?;
    if text(&config, "protocol")? != "mini-spk-resident-start-v3" {
        return Err(invalid("recovery resident protocol refused"));
    }
    let journal = std::path::PathBuf::from(text(&config, "journalDir")?);
    if resident_config.parent() != Some(journal.as_path()) {
        return Err(invalid("recovery config/journal mismatch"));
    }
    let directory = journal.join("failed-start-recovery-v1");
    match DirBuilder::new().mode(0o700).create(&directory) {
        Ok(()) => File::open(&journal)?.sync_all()?,
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
            crate::dispatch_native::private_dir(&directory)?
        }
        Err(e) => return Err(e),
    }
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(directory.join(".recovery.lock"))?;
    if lock.metadata()?.uid() != unsafe { libc::geteuid() } || lock.metadata()?.nlink() != 1 {
        return Err(invalid("recovery lock identity refused"));
    }
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let ingress_path = directory.join("ingress.bin");
    // Every Host reply is retained under its own observation name and read
    // back through the pinned Host's own outcome inspector.
    let observe = |reply: &[u8], opcode: u8| -> io::Result<Value> {
        let outcome = framed_payload(reply, opcode, OUTCOME)?;
        let observation = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|_| invalid("recovery clock before epoch"))?
            .as_nanos();
        let path = retain_exact(
            &directory,
            &format!("outcome-{opcode}-{observation}.bin"),
            outcome,
        )?;
        let out = directory.join(format!("outcome-inspection-{opcode}-{observation}.json"));
        Ok(serde_json::from_slice(&operator.tool("inspect", "outcome", &path, &out)?)?)
    };
    let finish = |view: Value, opcode: u8| -> io::Result<Value> {
        let confirmation = text(&view, "confirmation").unwrap_or("");
        let expected = if opcode == routes.lookup {
            confirmation == "replayed"
        } else {
            matches!(
                confirmation,
                "installed" | "recoveredAfterUncertainResponse"
            )
        };
        if text(&view, "type")? != "confirmed" || !expected {
            return Err(invalid(format!(
                "failed START recovery not confirmed (op {opcode}: {}); the retained ingress \
                 is resolved by exact lookup on the next call",
                text(&view, "type").unwrap_or("unreadable")
            )));
        }
        for field in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
            if !crate::lifecycle_v3_native::decimal(text(&view, field)?) {
                return Err(invalid("recovery receipt number noncanonical"));
            }
        }
        // Kernel `ApplicationGrain.Operation.after .reconcileFailedStart`
        // advances the claimed generation by one and returns phase 2
        // (`ApplicationFailedStartRecoverySource.recovery_stopped_generation`);
        // the Plan inspected above names the claimed generation.
        let result = json!({"protocol":"mini-spk-failed-start-recovered-v1","app":app,
            "generation":generation.to_string(),"reconciledGeneration":generation.checked_add(1)
                .ok_or_else(||invalid("recovery generation overflow"))?.to_string(),
            "ingressSha256":sha256_file(&ingress_path)?,"outcome":view});
        // The original receipt stays immutable; a lookup must name the same
        // transaction, event, position and world root.
        let confirmed = directory.join("confirmed.json");
        if !confirmed.exists() {
            retain_exact(&directory, "confirmed.json", &serde_json::to_vec(&result)?)?;
        } else {
            let original: Value = serde_json::from_slice(&recovery_read(&confirmed, MAX)?)?;
            for field in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
                if original.pointer(&format!("/outcome/{field}"))
                    != result.pointer(&format!("/outcome/{field}"))
                {
                    return Err(invalid(
                        "recovery lookup receipt differs from original confirmation",
                    ));
                }
            }
        }
        let receipt_bytes = recovery_read(&confirmed, MAX)?;
        retain_exact(&journal, "failed-start-recovered-v1.json", &receipt_bytes)?;
        serde_json::from_slice(&receipt_bytes).map_err(io::Error::from)
    };
    if directory.join("submit-requested.json").exists() {
        let ingress = recovery_read(&ingress_path, MAX)?;
        let marker: Value = serde_json::from_slice(&recovery_read(
            &directory.join("submit-requested.json"),
            MAX_MANIFEST,
        )?)?;
        if text(&marker, "app")? != app
            || text(&marker, "generation")? != generation.to_string()
            || text(&marker, "ingressSha256")? != hex(&Sha256::digest(&ingress))
        {
            return Err(invalid(
                "recovery lookup differs from exact submitted ingress",
            ));
        }
        // A submission was sent and its answer is not on disk: ask Mini for
        // the receipt of exactly these bytes before anything else.
        let view = observe(&operator.invoke(routes.lookup, &ingress)?, routes.lookup)?;
        if text(&view, "type")? != "absent" {
            return finish(view, routes.lookup);
        }
        // Mini holds no receipt for these bytes, so they were never admitted.
        // The SAME bytes go again: their stable nullifier
        // (`ApplicationFailedStartRecoveryIngress.stableNullifier`, derived
        // from the original claim) admits at most one recovery of this START
        // however often it is sent, and a racing earlier copy that lands
        // first makes this one a refusal that the next lookup resolves.
        let view = observe(&operator.invoke(routes.submit, &ingress)?, routes.submit)?;
        return finish(view, routes.submit);
    }
    let stage: Value = serde_json::from_slice(&recovery_read(
        &journal.join("start-admitted-v3.json"),
        MAX_MANIFEST,
    )?)?;
    if text(&stage, "protocol")? != "mini-spk-resident-start-admitted-v3" {
        return Err(invalid("original START admission absent"));
    }
    let physical: crate::hostd::VerifiedBegin = serde_json::from_value(
        stage
            .pointer("/claim/physicalBegin")
            .ok_or_else(|| invalid("original START physical claim absent"))?
            .clone(),
    )?;
    if physical.app.to_string() != app || physical.generation != generation {
        return Err(invalid("recovery target differs from original START"));
    }
    let begin_dir = std::path::PathBuf::from(text(&config, "beginAttemptDir")?);
    let claim_dir = std::path::PathBuf::from(text(&config, "claimAuthorAttemptDir")?);
    if begin_dir.parent() != Some(journal.as_path())
        || claim_dir.parent() != Some(journal.as_path())
    {
        return Err(invalid("recovery original attempt outside journal"));
    }
    let begin = recovery_read(&begin_dir.join("begin-v3.bin"), MAX)?;
    let claim = recovery_read(&claim_dir.join("claim-v3.bin"), MAX)?;
    let committed = recovery_read(&claim_dir.join("committed-v3.bin"), MAX)?;
    for (name, bytes) in [
        ("beginSha256", &begin),
        ("claimIngressSha256", &claim),
        ("committedClaimSha256", &committed),
    ] {
        if text(&stage, name)? != hex(&Sha256::digest(bytes)) {
            return Err(invalid("recovery retained original digest mismatch"));
        }
    }
    let audit = crate::hostd::Journal::open(&journal)?.audit_failed_start(&physical)?;
    let report_source = json!({"originalBeginHex":hex(&begin),"originalClaimHex":hex(&claim),
        "committedClaimHex":hex(&committed),"audit":audit,"semantics":text(&config,"completionSemantics")?});
    let source_path = retain_exact(
        &directory,
        "report-source.json",
        &serde_json::to_vec(&report_source)?,
    )?;
    let report_path = directory.join("report.bin");
    let report = recovery_tool(
        operator,
        "author",
        "application-failed-start-report",
        &source_path,
        &report_path,
    )?;
    let inspected = recovery_tool(
        operator,
        "inspect",
        "application-failed-start-report",
        &report_path,
        &directory.join("report-inspection.json"),
    )?;
    let report_view: Value = serde_json::from_slice(&inspected)?;
    if text(&report_view, "type")? != "application-failed-start-report-v1"
        || text(&report_view, "canonicalReportHex")? != hex(&report)
        || report_view.get("source") != Some(&report_source)
    {
        return Err(invalid(
            "recovery physical report differs from observed source",
        ));
    }
    let key = crate::dispatch_author::private_signing_key(Path::new(text(
        &config,
        "completionCustodianSeed",
    )?))?;
    let signed_source = json!({"reportHex":hex(&report),"publicKeyHex":hex(key.verifying_key().as_bytes()),
        "signatureHex":hex(&key.sign(&unhex(text(&report_view,"signingHeaderHex")?)?).to_bytes())});
    let signed_source_path = retain_exact(
        &directory,
        "signed-report.json",
        &serde_json::to_vec(&signed_source)?,
    )?;
    let signed_report = recovery_tool(
        operator,
        "author",
        "application-failed-start-signed-report",
        &signed_source_path,
        &directory.join("signed-report.bin"),
    )?;
    let custody: RecoveryCustody = serde_json::from_slice(&recovery_read(
        Path::new(text(&config, "completionManagementCustody")?),
        MAX_MANIFEST,
    )?)?;
    if custody.protocol != "mini-spk-completion-management-v1" || custody.selector.app != app {
        return Err(invalid("recovery management custody differs from target"));
    }
    crate::lifecycle_selector::validate_custody(
        operator,
        &custody.selector,
        &custody.management_subject,
        &custody.signers,
        config
            .get("appUid")
            .and_then(Value::as_u64)
            .and_then(|n| u32::try_from(n).ok())
            .ok_or_else(|| invalid("recovery app UID malformed"))?,
    )?;
    let request = recovery_tool(
        operator,
        "author",
        "application-failed-start-recovery-request",
        &retain_exact(
            &directory,
            "request-source.json",
            &serde_json::to_vec(&json!({
            "originalBeginHex":hex(&begin),"originalClaimHex":hex(&claim),"signedReportHex":hex(&signed_report)}))?,
        )?,
        &directory.join("request.bin"),
    )?;
    let reply = operator.invoke(routes.prepare, &custody.selector.framed(&request)?)?;
    let plan = framed_payload(&reply, routes.prepare, PLAN)?;
    let plan_path = retain_exact(&directory, "plan.bin", plan)?;
    let view: Value = serde_json::from_slice(&recovery_tool(
        operator,
        "inspect",
        "application-failed-start-recovery-plan",
        &plan_path,
        &directory.join("plan.json"),
    )?)?;
    if text(&view, "type")? != "application-failed-start-recovery-plan-v1"
        || text(&view, "canonicalPlanHex")? != hex(plan)
        || text(&view, "canonicalRequestHex")? != hex(&request)
        || text(&view, "originalBeginHex")? != hex(&begin)
        || text(&view, "originalClaimHex")? != hex(&claim)
        || text(&view, "signedReportHex")? != hex(&signed_report)
        || text(&view, "app")? != app
        || text(&view, "generation")? != generation.to_string()
    {
        return Err(invalid(
            "recovery source Plan differs from original failed START",
        ));
    }
    let signatures = sign_pinned_slots(
        view.get("slots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("recovery signing slots absent"))?,
        &custody.signers,
    )?;
    let sig_path = retain_exact(
        &directory,
        "signatures.json",
        &serde_json::to_vec(&signatures)?,
    )?;
    let sigs = recovery_tool(
        operator,
        "signatures",
        "",
        &sig_path,
        &directory.join("signatures.bin"),
    )?;
    let mut pair = Vec::new();
    pair.extend_from_slice(
        &u32::try_from(plan.len())
            .map_err(|_| invalid("recovery plan too large"))?
            .to_le_bytes(),
    );
    pair.extend_from_slice(plan);
    pair.extend_from_slice(&sigs);
    retain_exact(&directory, "assemble-request.bin", &pair)?;
    let reply = operator.invoke(routes.assemble, &pair)?;
    let ingress = framed_payload(&reply, routes.assemble, INGRESS)?;
    retain_exact(&directory, "ingress.bin", ingress)?;
    retain_exact(
        &directory,
        "submit-requested.json",
        &serde_json::to_vec(&json!({"ingressSha256":hex(&Sha256::digest(ingress)),
        "app":app,"generation":generation.to_string()}))?,
    )?;
    let view = observe(&operator.invoke(routes.submit, ingress)?, routes.submit)?;
    finish(view, routes.submit)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::SigningKey;

    fn scratch(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "grain-export-{name}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        DirBuilder::new().mode(0o700).create(&dir).unwrap();
        dir
    }

    fn export_fixture(key: &SigningKey) -> std::path::PathBuf {
        let dir = scratch("export");
        let image = vec![7u8; 4096];
        fs::write(dir.join("var.ext4"), &image).unwrap();
        let receipt = br#"{"receipt":{"acceptedCount":"31"}}"#;
        let manifest = json!({"protocol":"mini-spk-grain-export-v1","app":"7701",
            "packageRawSha256":"a".repeat(64),"class":"S",
            "image":{"file":"var.ext4","sha256":format!("{:x}", Sha256::digest(&image)),"bytes":"4096"},
            "stopReceipt":serde_json::from_slice::<Value>(receipt).unwrap(),
            "stopReceiptSha256":format!("{:x}", Sha256::digest(receipt))});
        let bytes = serde_json::to_vec_pretty(&manifest).unwrap();
        fs::write(dir.join("manifest.json"), &bytes).unwrap();
        fs::write(dir.join("manifest.sig"), hex(&key.sign(&bytes).to_bytes())).unwrap();
        dir
    }

    /// A pinned "Host" that is /bin/sh running the config file as its
    /// outcome inspector, and an operator socket that answers each request
    /// with a scripted outcome. The served opcodes and payloads are returned.
    struct FakeHost {
        root: std::path::PathBuf,
        operator: crate::dispatch_native::PrivateOperator,
    }

    const INSPECTOR: &str = "#!/bin/sh\n\
        # sh runs this as: CONFIG inspect outcome INPUT OUTPUT\n\
        [ \"$1 $2\" = 'inspect outcome' ] || exit 9\n\
        for c in replayed installed recoveredAfterUncertainResponse; do\n\
          if grep -q \"$c\" \"$3\"; then\n\
            printf '{\"type\":\"confirmed\",\"confirmation\":\"%s\",\"transactionId\":\"71\",\"eventId\":\"72\",\"acceptedCount\":\"73\",\"worldRoot\":\"74\"}' \"$c\" >\"$4\"; exit 0\n\
          fi\n\
        done\n\
        if grep -q absent \"$3\"; then printf '{\"type\":\"absent\"}' >\"$4\"; exit 0; fi\n\
        printf '{\"type\":\"refused\",\"reason\":\"operationRejected\"}' >\"$4\"\n";

    impl FakeHost {
        fn new(name: &str) -> Self {
            let root = scratch(name);
            let host = root.join("host");
            fs::copy("/bin/sh", &host).unwrap();
            fs::set_permissions(&host, std::os::unix::fs::PermissionsExt::from_mode(0o755)).unwrap();
            let config = root.join("inspector.sh");
            fs::write(&config, INSPECTOR).unwrap();
            fs::set_permissions(&config, std::os::unix::fs::PermissionsExt::from_mode(0o700)).unwrap();
            let sockets = root.join("sock");
            DirBuilder::new().mode(0o700).create(&sockets).unwrap();
            let operator = crate::dispatch_native::PrivateOperator {
                host: host.clone(),
                config: config.clone(),
                socket: sockets.join("operator.sock"),
                host_sha256: hex(&Sha256::digest(fs::read(&host).unwrap())),
                config_sha256: hex(&Sha256::digest(INSPECTOR.as_bytes())),
            };
            Self { root, operator }
        }

        /// Serve one connection per scripted reply; each reply is OUTCOME/v4
        /// followed by the word the inspector maps to a JSON view.
        fn serve(&self, replies: Vec<&'static str>) -> std::thread::JoinHandle<Vec<(u8, Vec<u8>)>> {
            let listener = std::os::unix::net::UnixListener::bind(&self.operator.socket).unwrap();
            fs::set_permissions(&self.operator.socket, std::os::unix::fs::PermissionsExt::from_mode(0o600)).unwrap();
            std::thread::spawn(move || {
                let mut seen = Vec::new();
                for word in replies {
                    let (mut stream, _) = listener.accept().unwrap();
                    let mut prefix = [0u8; 4];
                    stream.read_exact(&mut prefix).unwrap();
                    let mut request = vec![0u8; u32::from_le_bytes(prefix) as usize];
                    stream.read_exact(&mut request).unwrap();
                    let config_len = u32::from_le_bytes(request[1..5].try_into().unwrap()) as usize;
                    let at = 5 + config_len + 32;
                    let opcode = request[at];
                    seen.push((opcode, request[at + 1..].to_vec()));
                    let mut body = vec![opcode];
                    body.extend_from_slice(b"DREGG/NATIVE-HOST/OUTCOME/v5");
                    body.extend_from_slice(word.as_bytes());
                    let mut frame = (body.len() as u32).to_le_bytes().to_vec();
                    frame.extend_from_slice(&body);
                    stream.write_all(&frame).unwrap();
                }
                seen
            })
        }

        /// A generation journal whose recovery submission was sent and whose
        /// answer was lost: the exact ingress and its marker are retained.
        fn submitted_journal(&self, app: &str, generation: u64, ingress: &[u8]) -> std::path::PathBuf {
            let journal = self.root.join(format!("g{generation}"));
            DirBuilder::new().mode(0o700).create(&journal).unwrap();
            let config = json!({"protocol":"mini-spk-resident-start-v3","journalDir":journal});
            write_new(&journal.join("resident.json"), &serde_json::to_vec(&config).unwrap()).unwrap();
            let directory = journal.join("failed-start-recovery-v1");
            DirBuilder::new().mode(0o700).create(&directory).unwrap();
            write_new(&directory.join("ingress.bin"), ingress).unwrap();
            let marker = json!({"ingressSha256":hex(&Sha256::digest(ingress)),"app":app,
                "generation":generation.to_string()});
            write_new(&directory.join("submit-requested.json"), &serde_json::to_vec(&marker).unwrap()).unwrap();
            journal
        }
    }

    fn reconcile(fake: &FakeHost, journal: &Path, app: &str, generation: u64) -> io::Result<Value> {
        reconcile_failed_start(&fake.operator, &journal.join("resident.json"), app, generation,
            FAILED_START_RECOVERY_ROUTES)
    }

    #[test]
    fn failed_start_recovery_after_lost_answer_looks_up_exact_bytes_first() {
        let fake = FakeHost::new("recovery-lookup");
        let ingress = b"DREGG/APPLICATION/FAILED-START-RECOVERY-INGRESS/v1 exact".to_vec();
        let journal = fake.submitted_journal("7101", 3, &ingress);
        let server = fake.serve(vec!["replayed"]);
        let result = reconcile(&fake, &journal, "7101", 3).unwrap();
        // One request, the lookup, carrying exactly the retained bytes.
        assert_eq!(server.join().unwrap(), vec![(209, ingress.clone())]);
        assert_eq!(result["protocol"], "mini-spk-failed-start-recovered-v1");
        assert_eq!(result["generation"], "3");
        assert_eq!(result["reconciledGeneration"], "4");
        assert_eq!(result["outcome"]["confirmation"], "replayed");
        assert_eq!(result["ingressSha256"], hex(&Sha256::digest(&ingress)));
        // The journal receipt `scan_runs` reads is the confirmed record.
        let receipt: Value = serde_json::from_slice(
            &fs::read(journal.join("failed-start-recovered-v1.json")).unwrap()).unwrap();
        assert_eq!(receipt, result);
    }

    #[test]
    fn failed_start_recovery_resubmits_the_same_bytes_only_when_mini_has_no_receipt() {
        let fake = FakeHost::new("recovery-absent");
        let ingress = b"DREGG/APPLICATION/FAILED-START-RECOVERY-INGRESS/v1 never-admitted".to_vec();
        let journal = fake.submitted_journal("7101", 3, &ingress);
        let server = fake.serve(vec!["absent", "installed"]);
        let result = reconcile(&fake, &journal, "7101", 3).unwrap();
        assert_eq!(server.join().unwrap(), vec![(209, ingress.clone()), (208, ingress.clone())]);
        assert_eq!(result["outcome"]["confirmation"], "installed");
        // A later lookup must name the same receipt as the original confirmation.
        fs::remove_file(&fake.operator.socket).unwrap();
        let server = fake.serve(vec!["replayed"]);
        let again = reconcile(&fake, &journal, "7101", 3).unwrap();
        assert_eq!(server.join().unwrap(), vec![(209, ingress)]);
        assert_eq!(again["outcome"]["confirmation"], "installed");
    }

    #[test]
    fn failed_start_recovery_refusal_leaves_no_receipt_and_foreign_marker_sends_nothing() {
        let fake = FakeHost::new("recovery-refused");
        let ingress = b"DREGG/APPLICATION/FAILED-START-RECOVERY-INGRESS/v1 refused".to_vec();
        let journal = fake.submitted_journal("7101", 3, &ingress);
        let server = fake.serve(vec!["refused"]);
        let error = reconcile(&fake, &journal, "7101", 3).unwrap_err().to_string();
        assert_eq!(server.join().unwrap(), vec![(209, ingress.clone())]);
        assert!(error.contains("not confirmed"), "{error}");
        assert!(!journal.join("failed-start-recovered-v1.json").exists());
        assert!(!journal.join("failed-start-recovery-v1/confirmed.json").exists());
        // The marker names another app / generation: refused before any request
        // (the socket has no listener, so any request would fail differently).
        fs::remove_file(&fake.operator.socket).unwrap();
        for (app, generation) in [("7102", 3), ("7101", 4)] {
            let error = reconcile(&fake, &journal, app, generation).unwrap_err().to_string();
            assert!(error.contains("differs from exact submitted ingress"), "{error}");
        }
        // One flipped byte of the retained ingress is refused the same way.
        let path = journal.join("failed-start-recovery-v1/ingress.bin");
        let mut bytes = fs::read(&path).unwrap();
        bytes[0] ^= 1;
        fs::remove_file(&path).unwrap();
        write_new(&path, &bytes).unwrap();
        let error = reconcile(&fake, &journal, "7101", 3).unwrap_err().to_string();
        assert!(error.contains("differs from exact submitted ingress"), "{error}");
    }

    #[test]
    fn import_binds_signature_bytes_package_and_class() {
        let key = SigningKey::from_bytes(&[5u8; 32]);
        let public = hex(key.verifying_key().as_bytes());
        let dir = export_fixture(&key);
        let imports = scratch("imports").join("imports");
        let ok = verify_import(&dir, &public, &"a".repeat(64), "S", &imports).unwrap();
        assert_eq!(ok.record["signature"], "verified");
        // a different package, a different class, another exporter
        assert!(verify_import(&dir, &public, &"b".repeat(64), "S", &imports).is_err());
        assert!(verify_import(&dir, &public, &"a".repeat(64), "M", &imports).is_err());
        let other = hex(SigningKey::from_bytes(&[6u8; 32])
            .verifying_key()
            .as_bytes());
        assert!(verify_import(&dir, &other, &"a".repeat(64), "S", &imports).is_err());
        // one flipped image byte
        let mut image = fs::read(dir.join("var.ext4")).unwrap();
        image[100] ^= 1;
        fs::write(dir.join("var.ext4"), &image).unwrap();
        let error = verify_import(&dir, &public, &"a".repeat(64), "S", &imports)
            .err()
            .unwrap()
            .to_string();
        assert!(error.contains("image bytes differ"), "{error}");
        // one flipped manifest byte
        let dir = export_fixture(&key);
        let mut manifest = fs::read(dir.join("manifest.json")).unwrap();
        let at = manifest.iter().position(|b| *b == b'7').unwrap();
        manifest[at] = b'8';
        fs::write(dir.join("manifest.json"), &manifest).unwrap();
        let error = verify_import(&dir, &public, &"a".repeat(64), "S", &imports)
            .err()
            .unwrap()
            .to_string();
        assert!(error.contains("signature"), "{error}");
    }
}
