//! Two-phase private INSTALL: reserve Mini authority before root materializes
//! the verified SPK, then report the exact published image without app launch.
//! Every native submit has a fresh durable attempt directory and no retry.
#![allow(dead_code)] // Enabled only with the matching native descriptor route.

#[path = "install_v3.rs"]
mod install_v3;

use crate::dispatch_native::{private_dir, PrivateOperator};
#[cfg(test)]
use crate::dispatch_native::write_new;
use crate::sandbox::open_protected_directory;
use serde::Deserialize;
use std::fs::{self, DirBuilder, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
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
    deployment_id: Option<String>,
    host_id: Option<String>,
    launch_qualification: Option<PathBuf>,
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
    fn valid_host_identity(&self) -> bool {
        match self.protocol.as_str() {
            "mini-spk-resident-install-v2" => {
                self.deployment_id.as_deref().is_some_and(hex64)
                    && self.host_id.as_deref().is_some_and(hex64)
                    && self
                        .launch_qualification
                        .as_ref()
                        .is_some_and(|path| path.is_absolute() && !hidden_by_private_tmp(path))
            }
            _ => false,
        }
    }

    fn load(path: &Path) -> io::Result<Self> {
        let config: Self = serde_json::from_slice(&private_file(path, MAX_CONFIG)?)?;
        if config.protocol != "mini-spk-resident-install-v2"
            || path.parent() != Some(config.journal_dir.as_path())
            || !config.valid_host_identity()
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
        if let Some(path) = &self.launch_qualification {
            open_protected_directory(
                path.parent()
                    .ok_or_else(|| invalid("launch qualification parent absent"))?,
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
    install_v3::preflight_prepare(&InstallConfig::load(config_path)?)
}

/// After the separately bounded root `spk-ingest` reports exact image SHA,
/// independently reparse that protected image and join it to the retained
/// INSTALL claim. Neither this phase nor Mini completion starts an app child.
pub fn complete(config_path: &Path) -> io::Result<()> {
    install_v3::preflight_complete(&InstallConfig::load(config_path)?)
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
            protocol: "mini-spk-resident-install-v2".into(),
            journal_dir: directory.clone(),
            source_spk: PathBuf::from("/nonexistent/source.spk"),
            image_dir: PathBuf::from("/nonexistent/image"),
            expected_raw_sha256: "a".repeat(64),
            app_uid: 12345,
            deployment_id: None,
            host_id: None,
            launch_qualification: None,
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
