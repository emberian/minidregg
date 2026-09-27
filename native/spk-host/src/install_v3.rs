//! Versioned preflight for launch-bound INSTALL. The event23–25 author and
//! admission routes are not source-qualified yet, so this path cannot submit
//! or mark an INSTALL prepared. Historical v1 attempts stay in their own
//! journal format and never supply a v2 launch root.

use super::{invalid, InstallConfig};
use crate::dispatch_native::PrivateOperator;
use crate::launch_descriptor_native::SourceLaunchDescriptor;
use crate::materialize::InstalledPackage;
use crate::resident_launch::SourceBoundLaunch;
use crate::sandbox::open_protected_directory;
use serde::Deserialize;
use sha2::{Digest, Sha256};
use std::fs;
use std::io;
use std::path::Path;

const MAX_QUALIFICATION: u64 = 16 * 1024;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct QualifiedLaunch {
    protocol: String,
    raw_sha256: String,
    package_root: String,
    launch_root: String,
    launch_canonical_sha256: String,
    create_count: String,
    create_digests: Vec<String>,
    continue_digest: String,
}

impl QualifiedLaunch {
    fn read(config: &InstallConfig) -> io::Result<Self> {
        let path = config
            .launch_qualification
            .as_ref()
            .ok_or_else(|| invalid("v2 launch qualification absent"))?;
        let qualification: Self =
            serde_json::from_slice(&super::private_file(path, MAX_QUALIFICATION)?)?;
        if qualification.protocol != "mini-spk-launch-qualified-v2"
            || qualification.raw_sha256 != config.expected_raw_sha256
            || !super::hex64(&qualification.launch_canonical_sha256)
            || qualification.create_digests.is_empty()
            || qualification.create_digests.len() > 64
            || qualification.create_count != qualification.create_digests.len().to_string()
        {
            return Err(invalid("v2 launch qualification differs from INSTALL pins"));
        }
        Ok(qualification)
    }

    fn matches(&self, launch: &SourceLaunchDescriptor, raw_sha256: &str) -> io::Result<()> {
        if self.raw_sha256 != raw_sha256
            || self.package_root != launch.package.root
            || self.launch_root != launch.root
            || self.launch_canonical_sha256 != super::hex(&Sha256::digest(&launch.canonical))
            || self.create_digests != launch.create_digests
            || self.continue_digest != launch.continue_digest
            || self.create_count != launch.create_digests.len().to_string()
        {
            return Err(invalid(
                "verified SPK differs from retained v2 launch qualification",
            ));
        }
        Ok(())
    }
}

/// The only v3 INSTALL descriptor entrance. One signature-verified SPK parse
/// supplies v1 identity and all ordered commands; Mini authors both canonical
/// descriptors, and the protected qualifier must match the complete result.
/// A future v3 BEGIN may use `launch.canonical` only after this returns.
fn author_qualified_launch<'a>(
    config: &InstallConfig,
    operator: &PrivateOperator,
    package: &'a InstalledPackage,
    qualification: &QualifiedLaunch,
    attempt_dir: &Path,
) -> io::Result<SourceBoundLaunch<'a>> {
    let launch = SourceBoundLaunch::author(operator, package, attempt_dir)?;
    qualification.matches(launch.descriptor(), &package.raw_sha256)?;
    // Reopen the private qualifier after source authoring so an in-place
    // replacement cannot silently change the retained authority comparison.
    QualifiedLaunch::read(config)?.matches(launch.descriptor(), &package.raw_sha256)?;
    Ok(launch)
}

const V3_ARTIFACTS: &[&str] = &[
    "launch-descriptor",
    "lifecycle-begin-v3-active.json",
    "begin-v3",
    "claim-v3-author",
    "claim-v3",
    "lifecycle-claim-v3-active.json",
    "install-prepared-v2.json",
    "materialized-verify-v2",
    "materialized-report-v2",
    "completion-v2-author",
    "completion-v2-submit",
    "install-completed-v2.json",
];

fn preflight_prepare_artifacts(config: &InstallConfig) -> io::Result<()> {
    // A journal is one attempt. Reject both namespaces so an old v1 attempt
    // cannot accidentally be presented as a fresh v3 operation, or vice versa.
    config.preflight_artifacts()?;
    for name in V3_ARTIFACTS {
        match fs::symlink_metadata(config.artifact(name)) {
            Ok(_) => return Err(invalid("launch-bound INSTALL attempt already exists")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    Ok(())
}

pub(super) fn preflight_prepare(config: &InstallConfig) -> io::Result<()> {
    config.preflight_operator_paths()?;
    preflight_prepare_artifacts(config)?;
    QualifiedLaunch::read(config)?;
    open_protected_directory(
        config
            .source_spk
            .parent()
            .ok_or_else(|| invalid("SPK parent absent"))?,
        config.app_uid,
        false,
    )?;
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "launch-bound INSTALL requires source-qualified event23–25 author and admission routes",
    ))
}

pub(super) fn preflight_complete(config: &InstallConfig) -> io::Result<()> {
    config.preflight_operator_paths()?;
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "launch-bound INSTALL completion requires a source-qualified prepared-v2 claim",
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_native::SourceDescriptor;
    use crate::dispatch_native::write_new;
    use std::os::unix::fs::DirBuilderExt;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn config(journal_dir: PathBuf) -> InstallConfig {
        InstallConfig {
            protocol: "mini-spk-resident-install-v2".into(),
            journal_dir,
            source_spk: PathBuf::from("/nonexistent/source.spk"),
            image_dir: PathBuf::from("/nonexistent/image"),
            expected_raw_sha256: "a".repeat(64),
            app_uid: 12345,
            deployment_id: Some("d".repeat(64)),
            host_id: Some("e".repeat(64)),
            launch_qualification: Some(PathBuf::from("/private/qualification.json")),
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
        }
    }

    #[test]
    fn v3_artifact_namespace_refuses_v1_or_v3_attempt() {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = std::env::temp_dir().join(format!(
            "spk-install-v3-artifacts-{}-{stamp}",
            std::process::id()
        ));
        std::fs::DirBuilder::new().mode(0o700).create(&dir).unwrap();
        let config = config(dir.clone());
        preflight_prepare_artifacts(&config).unwrap();
        for artifact in ["descriptor", "begin-v3", "install-prepared-v2.json"] {
            let path = write_new(&dir, artifact, b"held").unwrap();
            assert!(preflight_prepare_artifacts(&config).is_err());
            assert!(std::fs::symlink_metadata(&path).is_ok());
            std::fs::remove_file(path).unwrap();
        }
        std::fs::remove_dir(dir).unwrap();
    }

    #[test]
    fn deployment_and_host_pins_are_required_only_for_v2_install() {
        let mut config = config(PathBuf::from("/private/install"));
        assert!(config.valid_host_identity());
        config.host_id = None;
        assert!(!config.valid_host_identity());
        config.host_id = Some("F".repeat(64));
        assert!(!config.valid_host_identity());
        config.host_id = Some("e".repeat(64));
        config.launch_qualification = None;
        assert!(!config.valid_host_identity());
        config.launch_qualification = Some(PathBuf::from("/private/qualification.json"));
        config.protocol = "mini-spk-resident-install-v1".into();
        assert!(!config.valid_host_identity());
        config.deployment_id = None;
        config.host_id = None;
        config.launch_qualification = None;
        assert!(config.valid_host_identity());
    }

    #[test]
    fn retained_qualifier_must_equal_entire_source_authored_launch() {
        let launch = SourceLaunchDescriptor {
            package: SourceDescriptor {
                canonical: b"package".to_vec(),
                root: "11".into(),
                image_identity: b"image".to_vec(),
                api_path: None,
            },
            canonical: b"launch".to_vec(),
            root: "22".into(),
            create_digests: vec!["33".into(), "44".into()],
            continue_digest: "55".into(),
        };
        let qualification = QualifiedLaunch {
            protocol: "mini-spk-launch-qualified-v2".into(),
            raw_sha256: "a".repeat(64),
            package_root: "11".into(),
            launch_root: "22".into(),
            launch_canonical_sha256: super::super::hex(&Sha256::digest(&launch.canonical)),
            create_count: "2".into(),
            create_digests: vec!["33".into(), "44".into()],
            continue_digest: "55".into(),
        };
        qualification.matches(&launch, &"a".repeat(64)).unwrap();
        let mut wrong = qualification;
        wrong.create_digests.swap(0, 1);
        assert!(wrong.matches(&launch, &"a".repeat(64)).is_err());
        wrong.create_digests.swap(0, 1);
        wrong.launch_canonical_sha256 = "b".repeat(64);
        assert!(wrong.matches(&launch, &"a".repeat(64)).is_err());
        wrong.launch_canonical_sha256 = super::super::hex(&Sha256::digest(&launch.canonical));
        wrong.package_root = "12".into();
        assert!(wrong.matches(&launch, &"a".repeat(64)).is_err());
    }
}
