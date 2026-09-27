//! Two-phase private INSTALL: reserve Mini authority before root materializes
//! the verified SPK, then report the exact published image without app launch.
//! Every native submit has a fresh durable attempt directory and no retry.
#![allow(dead_code)] // Enabled only with the matching native descriptor route.

use crate::claim_native::{
    match_signed_install_package, submit_once as submit_claim_once, CapturedClaim,
};
use crate::completion_native::{
    assemble_current_completion, preflight_custodian, prepare_materialized_report,
    submit_materialized_completion_once, FixedCompletionSigners, MaterializedObservation,
};
use crate::descriptor_native::author_signed_package;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::materialize::{qualify_bridge_spk, verify_installed_spk};
use crate::resident_begin_native::{
    assemble_current_claim, submit_once as submit_begin_once, FixedBeginSigners, FixedClaimSigners,
};
use crate::sandbox::open_protected_directory;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

const MAX_CONFIG: u64 = 16 * 1024;
const MAX_SPK: u64 = 256 * 1024 * 1024;
const MAX_CLAIM: u64 = 12_102_759;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn hex(bytes: &[u8]) -> String {
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(text, "{byte:02x}").expect("writing to String");
    }
    text
}

fn hex64(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn hidden_by_private_tmp(path: &Path) -> bool {
    path.starts_with("/tmp") || path.starts_with("/var/tmp")
}

fn private_file(path: &Path, maximum: u64) -> io::Result<Vec<u8>> {
    let parent = path
        .parent()
        .ok_or_else(|| invalid("private parent absent"))?;
    let owner = unsafe { libc::geteuid() };
    for ancestor in parent.ancestors() {
        let meta = fs::symlink_metadata(ancestor)?;
        if !meta.is_dir()
            || meta.file_type().is_symlink()
            || (meta.uid() != 0 && meta.uid() != owner)
            || meta.permissions().mode() & 0o022 != 0
        {
            return Err(invalid("private file ancestor custody refused"));
        }
    }
    private_dir(parent)?;
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let meta = file.metadata()?;
    let named = fs::symlink_metadata(path)?;
    if !path.is_absolute()
        || !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o777 != 0o600
        || (meta.dev(), meta.ino()) != (named.dev(), named.ino())
        || meta.len() == 0
        || meta.len() > maximum
    {
        return Err(invalid("private file identity or bound refused"));
    }
    let mut bytes = Vec::new();
    file.by_ref().take(maximum + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != meta.len() {
        return Err(invalid("private file changed during read"));
    }
    Ok(bytes)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct InstallConfig {
    protocol: String,
    journal_dir: PathBuf,
    source_spk: PathBuf,
    image_dir: PathBuf,
    expected_raw_sha256: String,
    app_uid: u32,
    mini_host: PathBuf,
    mini_host_sha256: String,
    mini_config: PathBuf,
    mini_config_sha256: String,
    mini_operator_socket: PathBuf,
    begin_management_custody: PathBuf,
    claim_management_custody: PathBuf,
    completion_management_custody: PathBuf,
    completion_custodian_seed: PathBuf,
    completion_semantics: String,
}

impl InstallConfig {
    fn load(path: &Path) -> io::Result<Self> {
        let config: Self = serde_json::from_slice(&private_file(path, MAX_CONFIG)?)?;
        if config.protocol != "mini-spk-resident-install-v1"
            || path.parent() != Some(config.journal_dir.as_path())
            || !hex64(&config.expected_raw_sha256)
            || !hex64(&config.mini_host_sha256)
            || !hex64(&config.mini_config_sha256)
            || config.app_uid == 0
            || config.app_uid == unsafe { libc::geteuid() }
            || config.completion_semantics.is_empty()
            || !config
                .completion_semantics
                .bytes()
                .all(|byte| byte.is_ascii_digit())
            || ![
                &config.source_spk,
                &config.image_dir,
                &config.mini_host,
                &config.mini_config,
                &config.mini_operator_socket,
                &config.begin_management_custody,
                &config.claim_management_custody,
                &config.completion_management_custody,
                &config.completion_custodian_seed,
            ]
            .iter()
            .all(|item| item.is_absolute())
            || [
                &config.source_spk,
                &config.image_dir,
                &config.mini_host,
                &config.mini_config,
                &config.mini_operator_socket,
                &config.begin_management_custody,
                &config.claim_management_custody,
                &config.completion_management_custody,
                &config.completion_custodian_seed,
            ]
            .iter()
            .any(|item| hidden_by_private_tmp(item))
            || config.image_dir.file_name().and_then(|name| name.to_str())
                != Some(format!("sha256-{}", config.expected_raw_sha256).as_str())
        {
            return Err(invalid("resident INSTALL config refused"));
        }
        Ok(config)
    }

    fn operator(&self) -> PrivateOperator {
        PrivateOperator {
            host: self.mini_host.clone(),
            config: self.mini_config.clone(),
            socket: self.mini_operator_socket.clone(),
            host_sha256: self.mini_host_sha256.clone(),
            config_sha256: self.mini_config_sha256.clone(),
        }
    }

    fn artifact(&self, name: &str) -> PathBuf {
        self.journal_dir.join(name)
    }

    fn preflight_artifacts(&self) -> io::Result<()> {
        private_dir(&self.journal_dir)?;
        for name in [
            "descriptor",
            "begin",
            "claim-author",
            "claim",
            "lifecycle-claim-active.json",
            "install-prepared.json",
            "install-completed.json",
            "materialized-verify",
            "materialized-report",
            "completion-author",
            "completion-submit",
        ] {
            match fs::symlink_metadata(self.artifact(name)) {
                Ok(_) => return Err(invalid("INSTALL attempt already exists")),
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(error),
            }
        }
        Ok(())
    }

    fn preflight_operator_paths(&self) -> io::Result<()> {
        private_dir(&self.journal_dir)?;
        open_protected_directory(&self.journal_dir, self.app_uid, false)?;
        for path in [
            &self.mini_host,
            &self.mini_config,
            &self.mini_operator_socket,
            &self.begin_management_custody,
            &self.claim_management_custody,
            &self.completion_management_custody,
            &self.completion_custodian_seed,
        ] {
            open_protected_directory(
                path.parent()
                    .ok_or_else(|| invalid("operator artifact parent absent"))?,
                self.app_uid,
                false,
            )?;
        }
        Ok(())
    }
}

/// Run inside a bounded offline operator unit: Bread's XZ decoder has a
/// whole-block peak not constrained by its archive output limit.
pub fn prepare(config_path: &Path) -> io::Result<()> {
    let config = InstallConfig::load(config_path)?;
    config.preflight_artifacts()?;
    config.preflight_operator_paths()?;
    open_protected_directory(
        config
            .source_spk
            .parent()
            .ok_or_else(|| invalid("SPK parent absent"))?,
        config.app_uid,
        false,
    )?;
    // The operator receives a private exact-byte copy of the root inbox SPK.
    // The root-only ingest later checks that inbox file's raw SHA separately.
    let source = private_file(&config.source_spk, MAX_SPK)?;
    if hex(&Sha256::digest(&source)) != config.expected_raw_sha256 {
        return Err(invalid("operator SPK copy differs from pinned raw SHA"));
    }
    drop(source);
    let (package, _) = qualify_bridge_spk(&config.source_spk)?;
    if package.raw_sha256 != config.expected_raw_sha256 {
        return Err(invalid("signed source SPK changed during qualification"));
    }
    let operator = config.operator();
    preflight_custodian(
        &operator,
        &config.completion_custodian_seed,
        &config.completion_semantics,
    )?;
    let descriptor = author_signed_package(&operator, &package, &config.artifact("descriptor"))?;
    let begin_signers: FixedBeginSigners =
        serde_json::from_slice(&private_file(&config.begin_management_custody, MAX_CONFIG)?)?;
    let claim_signers: FixedClaimSigners =
        serde_json::from_slice(&private_file(&config.claim_management_custody, MAX_CONFIG)?)?;
    let begin = submit_begin_once(
        &operator,
        &begin_signers,
        config.app_uid,
        &descriptor.canonical,
        "install",
        &config.artifact("begin-operation-ledger"),
        &config.artifact("begin"),
    )?;
    let ingress = assemble_current_claim(
        &operator,
        &claim_signers,
        config.app_uid,
        &begin,
        &config.artifact("claim-nonce-ledger"),
        &config.artifact("claim-author"),
    )?;
    let captured = submit_claim_once(&operator, &ingress, &config.artifact("claim"))?;
    let matched =
        match_signed_install_package(&operator, &package, &captured, &config.artifact("claim"))?;
    if matched.descriptor_root != descriptor.root
        || matched.begin.image_identity != hex(&descriptor.image_identity)
    {
        return Err(invalid("INSTALL claim differs from signed SPK descriptor"));
    }
    let stage = json!({
        "protocol":"mini-spk-install-prepared-v1",
        "rawSha256":package.raw_sha256,
        "descriptorRoot":descriptor.root,
        "imageIdentityHex":hex(&descriptor.image_identity),
        "unit":matched.begin.unit,
        "beginSha256":hex(&Sha256::digest(&begin.ingress)),
        "claimSha256":hex(&Sha256::digest(&captured.payload)),
        "claimReceipt":{"transactionId":matched.begin.transaction_id,
            "eventId":matched.begin.event_id},
    });
    write_new(
        &config.journal_dir,
        "install-prepared.json",
        &serde_json::to_vec(&stage)?,
    )?;
    Ok(())
}

/// After the separately bounded root `spk-ingest` reports exact image SHA,
/// independently reparse that protected image and join it to the retained
/// INSTALL claim. Neither this phase nor Mini completion starts an app child.
pub fn complete(config_path: &Path) -> io::Result<()> {
    let config = InstallConfig::load(config_path)?;
    config.preflight_operator_paths()?;
    private_dir(&config.journal_dir)?;
    for name in [
        "materialized-verify",
        "materialized-report",
        "completion-author",
        "completion-submit",
        "install-completed.json",
    ] {
        match fs::symlink_metadata(config.artifact(name)) {
            Ok(_) => return Err(invalid("INSTALL completion attempt already exists")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    let stage: Value = serde_json::from_slice(&private_file(
        &config.artifact("install-prepared.json"),
        MAX_CONFIG,
    )?)?;
    if stage.get("protocol").and_then(Value::as_str) != Some("mini-spk-install-prepared-v1")
        || stage.get("rawSha256").and_then(Value::as_str)
            != Some(config.expected_raw_sha256.as_str())
    {
        return Err(invalid("retained INSTALL preparation differs"));
    }
    let package = verify_installed_spk(&config.image_dir, config.app_uid)?;
    if package.raw_sha256 != config.expected_raw_sha256 {
        return Err(invalid("root-published image differs from prepared SPK"));
    }
    let begin = private_file(&config.artifact("begin/begin-v2.bin"), MAX_CLAIM)?;
    let claim_ingress = private_file(&config.artifact("claim-author/claim-v2.bin"), MAX_CLAIM)?;
    let claim = private_file(&config.artifact("claim/committed-v2.bin"), MAX_CLAIM)?;
    if stage.get("beginSha256").and_then(Value::as_str)
        != Some(hex(&Sha256::digest(&begin)).as_str())
        || stage.get("claimSha256").and_then(Value::as_str)
            != Some(hex(&Sha256::digest(&claim)).as_str())
    {
        return Err(invalid("retained INSTALL ingress or claim changed"));
    }
    let operator = config.operator();
    let verify_dir = config.artifact("materialized-verify");
    DirBuilder::new().mode(0o700).create(&verify_dir)?;
    let inspection = operator.tool(
        "inspect",
        "application-lifecycle-claim-committed-v2",
        &config.artifact("claim/committed-v2.bin"),
        &verify_dir.join("claim-inspection.json"),
    )?;
    let captured = CapturedClaim {
        payload: claim.clone(),
        inspection,
    };
    let matched = match_signed_install_package(&operator, &package, &captured, &verify_dir)?;
    if stage.get("descriptorRoot").and_then(Value::as_str) != Some(matched.descriptor_root.as_str())
        || stage.get("unit").and_then(Value::as_str) != Some(matched.begin.unit.as_str())
        || stage.get("imageIdentityHex").and_then(Value::as_str)
            != Some(matched.begin.image_identity.as_str())
    {
        return Err(invalid(
            "published image differs from prepared INSTALL claim",
        ));
    }
    let mut image_identity = b"DREGG/SPK-IMAGE/v1".to_vec();
    image_identity.extend_from_slice(&package.raw_sha256_bytes);
    preflight_custodian(
        &operator,
        &config.completion_custodian_seed,
        &config.completion_semantics,
    )?;
    let signers: FixedCompletionSigners = serde_json::from_slice(&private_file(
        &config.completion_management_custody,
        MAX_CONFIG,
    )?)?;
    signers.validate(&operator, config.app_uid)?;
    let report = prepare_materialized_report(
        &operator,
        &begin,
        &claim,
        MaterializedObservation {
            unit: &matched.begin.unit,
            image_identity: &image_identity,
        },
        &config.completion_custodian_seed,
        &config.completion_semantics,
        &config.artifact("materialized-report"),
    )?;
    let ingress = assemble_current_completion(
        &operator,
        &begin,
        &claim_ingress,
        &report.signed_report,
        &signers,
        config.app_uid,
        &config.artifact("completion-author"),
    )?;
    let receipt = submit_materialized_completion_once(
        &operator,
        &ingress,
        &config.artifact("completion-submit"),
    )?;
    write_new(
        &config.journal_dir,
        "install-completed.json",
        &serde_json::to_vec(&json!({
            "protocol":"mini-spk-install-completed-v1",
            "transactionId":receipt.transaction_id,
            "eventId":receipt.event_id,
            "acceptedCount":receipt.accepted_count,
            "imageBoundary":receipt.image_boundary,
            "rawSha256":package.raw_sha256,
        }))?,
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::DirBuilderExt;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn private_tmp_sources_cannot_enter_bounded_install_unit() {
        assert!(hidden_by_private_tmp(Path::new("/tmp/mini/operator.sock")));
        assert!(hidden_by_private_tmp(Path::new("/var/tmp/mini/source.spk")));
        assert!(!hidden_by_private_tmp(Path::new(
            "/run/user/1000/mini/operator.sock"
        )));
        assert!(!hidden_by_private_tmp(Path::new(
            "/var/lib/minidregg/spk/source.spk"
        )));
    }

    #[test]
    fn stale_install_artifact_refuses_before_any_native_or_image_work() {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "spk-install-attempt-{}-{stamp}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&directory).unwrap();
        let config = InstallConfig {
            protocol: "mini-spk-resident-install-v1".into(),
            journal_dir: directory.clone(),
            source_spk: PathBuf::from("/nonexistent/source.spk"),
            image_dir: PathBuf::from("/nonexistent/image"),
            expected_raw_sha256: "a".repeat(64),
            app_uid: 12345,
            mini_host: PathBuf::from("/nonexistent/host"),
            mini_host_sha256: "b".repeat(64),
            mini_config: PathBuf::from("/nonexistent/config"),
            mini_config_sha256: "c".repeat(64),
            mini_operator_socket: PathBuf::from("/nonexistent/socket"),
            begin_management_custody: PathBuf::from("/nonexistent/begin"),
            claim_management_custody: PathBuf::from("/nonexistent/claim"),
            completion_management_custody: PathBuf::from("/nonexistent/completion"),
            completion_custodian_seed: PathBuf::from("/nonexistent/seed"),
            completion_semantics: "1".into(),
        };
        config.preflight_artifacts().unwrap();
        let stale = write_new(&directory, "lifecycle-claim-active.json", b"uncertain").unwrap();
        assert!(config.preflight_artifacts().is_err());
        fs::remove_file(stale).unwrap();
        let stale = write_new(&directory, "materialized-verify", b"incomplete").unwrap();
        assert!(config.preflight_artifacts().is_err());
        fs::remove_file(stale).unwrap();
        fs::remove_dir(directory).unwrap();
    }
}
