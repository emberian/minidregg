//! Signed SPK launch commands supplied to Mini's v2 descriptor author.
//!
//! The physical source is one `InstalledPackage` from a signature-verified
//! Bread parse. This module preserves create-action order, argument order and
//! every environment pair, including duplicate names. Mini alone owns the
//! canonical descriptor codec and root.
#![allow(dead_code)] // Resident v3 START caller follows the source-qualified route.

use sandstorm_package::manifest::Command as SpkCommand;
use sandstorm_package::SpkManifest;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use crate::descriptor_native::{author_signed_package, SourceDescriptor, SourceStep, SourceTool};
use crate::dispatch_native::{private_dir, write_new};
use crate::materialize::qualify_bridge_spk;
use crate::materialize::InstalledPackage;
use serde::Deserialize;

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

const MAX_SOURCE_CONFIG: u64 = 65_536;
const MAX_SOURCE_INSPECTION: u64 = 8 * 12_102_760;
const MAX_SOURCE_CANONICAL: u64 = 12_102_759;
// Cold Lean source authoring can be slow, but never indefinitely hold the
// pre-Store qualifier or leave an unobserved child behind.
const SOURCE_CHILD_DEADLINE: Duration = Duration::from_secs(600);

/// Pure offline Host author/inspect. `Host.Main` loads Settings but these two
/// branches do not open or mutate the Store. This is distinct from the live
/// socket-bound PrivateOperator used for lifecycle admission.
pub(crate) struct OfflineSourceHost {
    pub host: PathBuf,
    pub host_sha256: String,
    pub config: PathBuf,
    pub config_sha256: String,
}

fn read_private(path: &Path, bound: u64) -> io::Result<Vec<u8>> {
    let parent = path
        .parent()
        .ok_or_else(|| invalid("source artifact parent absent"))?;
    private_dir(parent)?;
    let named = fs::symlink_metadata(path)?;
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let opened = file.metadata()?;
    if !path.is_absolute()
        || !opened.is_file()
        || opened.len() == 0
        || opened.len() > bound
        || opened.uid() != unsafe { libc::geteuid() }
        || opened.nlink() != 1
        || opened.permissions().mode() & 0o777 != 0o600
        || (named.dev(), named.ino()) != (opened.dev(), opened.ino())
    {
        return Err(invalid("offline source artifact identity or bound refused"));
    }
    let mut bytes = Vec::new();
    file.by_ref().take(bound + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != opened.len() {
        return Err(invalid("offline source artifact changed during read"));
    }
    Ok(bytes)
}

impl OfflineSourceHost {
    fn check_pin(&self) -> io::Result<()> {
        let named = fs::symlink_metadata(&self.host)?;
        if !self.host.is_absolute()
            || !named.is_file()
            || named.permissions().mode() & 0o022 != 0
            || named.len() == 0
        {
            return Err(invalid("offline Mini Host image identity refused"));
        }
        let mut host = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&self.host)?;
        let opened = host.metadata()?;
        if !opened.is_file() || (named.dev(), named.ino()) != (opened.dev(), opened.ino()) {
            return Err(invalid("offline Mini Host image changed before hash"));
        }
        let mut digest = Sha256::new();
        let mut chunk = [0u8; 64 * 1024];
        loop {
            let count = host.read(&mut chunk)?;
            if count == 0 {
                break;
            }
            digest.update(&chunk[..count]);
        }
        if self.host_sha256 != hex(&digest.finalize())
            || self.config_sha256
                != hex(&Sha256::digest(read_private(
                    &self.config,
                    MAX_SOURCE_CONFIG,
                )?))
        {
            return Err(invalid("offline Mini Host/config SHA-256 pin drift"));
        }
        Ok(())
    }

    fn run_step(
        &self,
        step: SourceStep,
        input: &Path,
        output: &Path,
        timeout: Duration,
    ) -> io::Result<Vec<u8>> {
        self.check_pin()?;
        let (command, kind) = step.command_kind();
        let limit = if command == "author" {
            22 * 1024 * 1024
        } else {
            MAX_SOURCE_CANONICAL
        };
        let input_bytes = read_private(input, limit)?;
        if output.parent() != input.parent() {
            return Err(invalid("offline source output parent differs"));
        }
        match fs::symlink_metadata(output) {
            Ok(_) => return Err(invalid("offline source output already exists")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
        let mut child = Command::new(&self.host)
            .arg(&self.config)
            .arg(command)
            .arg(kind)
            .arg(input)
            .arg(output)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()?;
        let deadline = Instant::now() + timeout;
        let status = loop {
            match child.try_wait() {
                Ok(Some(status)) => break status,
                Ok(None) if Instant::now() < deadline => thread::sleep(Duration::from_millis(25)),
                Ok(None) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(io::Error::new(
                        io::ErrorKind::TimedOut,
                        "pinned offline Mini Host source deadline",
                    ));
                }
                Err(error) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(error);
                }
            }
        };
        if !status.success() {
            return Err(invalid("pinned offline Mini Host author/inspect refused"));
        }
        let mut file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(output)?;
        let named = fs::symlink_metadata(output)?;
        let opened = file.metadata()?;
        let output_bound = if command == "inspect" {
            MAX_SOURCE_INSPECTION
        } else {
            MAX_SOURCE_CANONICAL
        };
        if !opened.is_file()
            || opened.len() == 0
            || opened.len() > output_bound
            || opened.uid() != unsafe { libc::geteuid() }
            || opened.nlink() != 1
            || (named.dev(), named.ino()) != (opened.dev(), opened.ino())
        {
            return Err(invalid("offline source output identity or bound refused"));
        }
        file.set_permissions(fs::Permissions::from_mode(0o600))?;
        file.sync_all()?;
        File::open(
            output
                .parent()
                .ok_or_else(|| invalid("source output parent absent"))?,
        )?
        .sync_all()?;
        let mut bytes = Vec::new();
        file.by_ref()
            .take(output_bound + 1)
            .read_to_end(&mut bytes)?;
        self.check_pin()?;
        if read_private(input, limit)? != input_bytes || bytes.len() as u64 != opened.len() {
            return Err(invalid(
                "offline source input/output changed during authoring",
            ));
        }
        Ok(bytes)
    }
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct QualificationConfig {
    protocol: String,
    source_spk: PathBuf,
    mini_host: PathBuf,
    mini_host_sha256: String,
    mini_config: PathBuf,
    mini_config_sha256: String,
    attempt_dir: PathBuf,
}

fn lowercase_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

/// Pure pre-Store qualification entry point. The signed SPK is parsed once;
/// direct Host author/inspect uses only the pinned Settings file, never a
/// service socket or an opened Store. This does not install or launch an app.
pub fn qualify_launch(config_path: &Path) -> io::Result<Value> {
    let config_bytes = read_private(config_path, MAX_SOURCE_CONFIG)?;
    let config: QualificationConfig = serde_json::from_slice(&config_bytes)?;
    if config.protocol != "mini-spk-launch-qualification-v1"
        || ![
            &config.source_spk,
            &config.mini_host,
            &config.mini_config,
            &config.attempt_dir,
        ]
        .iter()
        .all(|path| path.is_absolute())
        || !lowercase_sha256(&config.mini_host_sha256)
        || !lowercase_sha256(&config.mini_config_sha256)
    {
        return Err(invalid("offline launch qualification config refused"));
    }
    let source_host = OfflineSourceHost {
        host: config.mini_host,
        host_sha256: config.mini_host_sha256,
        config: config.mini_config,
        config_sha256: config.mini_config_sha256,
    };
    source_host.check_pin()?;
    let (package, _) = qualify_bridge_spk(&config.source_spk)?;
    let launch = author_signed_launch(&source_host, &package, &config.attempt_dir)?;
    if read_private(config_path, MAX_SOURCE_CONFIG)? != config_bytes {
        return Err(invalid("offline launch qualification input changed"));
    }
    source_host.check_pin()?;
    let result = json!({
        "protocol":"mini-spk-launch-qualified-v2",
        "rawSha256":package.raw_sha256,
        "packageRoot":launch.package.root,
        "launchRoot":launch.root,
        "launchCanonicalSha256":hex(&Sha256::digest(&launch.canonical)),
        "createCount":launch.create_digests.len().to_string(),
        "createDigests":launch.create_digests,
        "continueDigest":launch.continue_digest,
    });
    write_new(
        &config.attempt_dir,
        "qualification.json",
        &serde_json::to_vec_pretty(&result)?,
    )?;
    Ok(result)
}

impl SourceTool for OfflineSourceHost {
    fn source_step(&self, step: SourceStep, input: &Path, output: &Path) -> io::Result<Vec<u8>> {
        self.run_step(step, input, output, SOURCE_CHILD_DEADLINE)
    }
}

fn valid_command(command: &SpkCommand) -> io::Result<()> {
    let Some(executable) = command.argv.first() else {
        return Err(invalid("signed SPK launch command has no executable"));
    };
    if executable.is_empty()
        || command.argv.len() > 64
        || command.environ.len() > 128
        || command
            .argv
            .iter()
            .any(|arg| arg.len() > 4096 || arg.as_bytes().contains(&0))
        || command.environ.iter().any(|(key, value)| {
            key.is_empty()
                || key.len() > 256
                || value.len() > 4096
                || key.as_bytes().contains(&0)
                || value.as_bytes().contains(&0)
        })
    {
        return Err(invalid("signed SPK launch command exceeds v2 bound"));
    }
    Ok(())
}

fn command_source(command: &SpkCommand) -> io::Result<Value> {
    valid_command(command)?;
    Ok(json!({
        "argvHex":command.argv.iter().map(|arg| hex(arg.as_bytes())).collect::<Vec<_>>(),
        "environHex":command.environ.iter().map(|(key,value)|
            json!({"keyHex":hex(key.as_bytes()),"valueHex":hex(value.as_bytes())}))
            .collect::<Vec<_>>(),
    }))
}

/// Exact input projection for `application-spk-launch-descriptor`. The caller
/// must obtain `manifest` and the v1 canonical descriptor from the same
/// `InstalledPackage`, never from a caller-provided digest or extracted image.
pub(crate) fn signed_launch_source(
    manifest: &SpkManifest,
    package_canonical: &[u8],
) -> io::Result<Value> {
    if manifest.actions.is_empty() || manifest.actions.len() > 64 {
        return Err(invalid("signed SPK create-action count outside v2 profile"));
    }
    let creates = manifest
        .actions
        .iter()
        .map(|action| command_source(&action.command))
        .collect::<io::Result<Vec<_>>>()?;
    let continuation = command_source(&manifest.continue_command)?;
    Ok(json!({
        "packageCanonicalHex":hex(package_canonical),
        "createCommands":creates,
        "continueCommand":continuation,
    }))
}

pub(crate) struct SourceLaunchDescriptor {
    pub package: SourceDescriptor,
    pub canonical: Vec<u8>,
    pub root: String,
    /// Source-owned command roots in signed create-action order.
    pub create_digests: Vec<String>,
    pub continue_digest: String,
}

fn field<'a>(value: &'a Value, name: &str) -> io::Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("Mini launch descriptor inspection field absent"))
}

fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn checked_command_echo(view: &Value, physical: &Value) -> io::Result<String> {
    if view.get("argvHex") != physical.get("argvHex")
        || view.get("environHex") != physical.get("environHex")
        || field(view, "canonical")?.is_empty()
        || !decimal(field(view, "digest")?)
    {
        return Err(invalid(
            "Mini launch command differs from signed manifest order/bytes",
        ));
    }
    Ok(field(view, "digest")?.to_owned())
}

/// Author and verify both descriptors from one `InstalledPackage` that was
/// produced by a signature-verified Bread parse. No extracted-image reparse,
/// caller SHA claim, or Rust implementation of Mini's canonical codec occurs.
pub(crate) fn author_signed_launch<T: SourceTool>(
    operator: &T,
    package: &InstalledPackage,
    attempt_dir: &Path,
) -> io::Result<SourceLaunchDescriptor> {
    private_dir(
        attempt_dir
            .parent()
            .ok_or_else(|| invalid("launch descriptor attempt parent absent"))?,
    )?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let v1 = author_signed_package(operator, package, &attempt_dir.join("package-v1"))?;
    let source = signed_launch_source(&package.manifest, &v1.canonical)?;
    let input = write_new(
        attempt_dir,
        "launch-source.json",
        &serde_json::to_vec(&source)?,
    )?;
    let canonical = operator.source_step(
        SourceStep::AuthorLaunch,
        &input,
        &attempt_dir.join("launch-descriptor.bin"),
    )?;
    let inspected = operator.source_step(
        SourceStep::InspectLaunch,
        &attempt_dir.join("launch-descriptor.bin"),
        &attempt_dir.join("launch-inspection.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspected)?;
    if field(&view, "type")? != "application-spk-launch-descriptor-v2"
        || field(&view, "canonical")? != hex(&canonical)
        || field(&view, "packageCanonicalHex")? != hex(&v1.canonical)
        || field(&view, "packageRoot")? != v1.root
        || !decimal(field(&view, "root")?)
    {
        return Err(invalid(
            "Mini v2 descriptor differs from verified v1 package",
        ));
    }
    let expected_creates = source["createCommands"]
        .as_array()
        .ok_or_else(|| invalid("signed create actions absent"))?;
    let creates = view["createCommands"]
        .as_array()
        .ok_or_else(|| invalid("Mini launch create actions absent"))?;
    if creates.len() != expected_creates.len() {
        return Err(invalid("Mini launch create-action count differs"));
    }
    let create_digests = creates
        .iter()
        .zip(expected_creates)
        .map(|(command, physical)| checked_command_echo(command, physical))
        .collect::<io::Result<Vec<_>>>()?;
    let continue_digest =
        checked_command_echo(&view["continueCommand"], &source["continueCommand"])?;
    Ok(SourceLaunchDescriptor {
        package: v1,
        canonical,
        root: field(&view, "root")?.to_owned(),
        create_digests,
        continue_digest,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use sandstorm_package::manifest::Action;
    use std::io::Write;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn offline_fixture(script: &str) -> (PathBuf, OfflineSourceHost, PathBuf, PathBuf) {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root =
            std::env::temp_dir().join(format!("spk-offline-source-{}-{nonce}", std::process::id()));
        DirBuilder::new().mode(0o700).create(&root).unwrap();
        let host = root.join("mock-host");
        let config = root.join("config.json");
        let input = root.join("input.bin");
        let output = root.join("output.bin");
        for (path, bytes) in [
            (&host, script.as_bytes()),
            (&config, b"{}"),
            (&input, b"original"),
        ] {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(path)
                .unwrap();
            file.write_all(bytes).unwrap();
            file.sync_all().unwrap();
        }
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let source = OfflineSourceHost {
            host_sha256: hex(&Sha256::digest(fs::read(&host).unwrap())),
            config_sha256: hex(&Sha256::digest(fs::read(&config).unwrap())),
            host,
            config,
        };
        (root, source, input, output)
    }

    #[test]
    fn offline_source_runs_without_socket_and_rejects_pin_drift() {
        let (root, source, input, output) = offline_fixture("#!/bin/sh\ncat \"$4\" > \"$5\"\n");
        assert_eq!(
            source
                .run_step(
                    SourceStep::AuthorSchema,
                    &input,
                    &output,
                    Duration::from_secs(2)
                )
                .unwrap(),
            b"original"
        );
        let second = root.join("second.bin");
        fs::write(&source.config, b"{\"changed\":true}").unwrap();
        assert!(source
            .run_step(
                SourceStep::AuthorSchema,
                &input,
                &second,
                Duration::from_secs(2)
            )
            .is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn offline_source_rechecks_input_after_child_and_reaps_timeout() {
        let (root, source, input, output) =
            offline_fixture("#!/bin/sh\nprintf tampered > \"$4\"\ncat \"$4\" > \"$5\"\n");
        assert!(source
            .run_step(
                SourceStep::AuthorSchema,
                &input,
                &output,
                Duration::from_secs(2)
            )
            .is_err());
        fs::remove_dir_all(root).unwrap();

        let (root, source, input, output) =
            offline_fixture("#!/bin/sh\ncat \"$4\" > \"$5\"\nprintf changed > \"$1\"\n");
        assert!(source
            .run_step(
                SourceStep::AuthorSchema,
                &input,
                &output,
                Duration::from_secs(2)
            )
            .is_err());
        fs::remove_dir_all(root).unwrap();

        let (root, source, input, output) = offline_fixture("#!/bin/sh\nwhile :; do :; done\n");
        let started = Instant::now();
        let error = source
            .run_step(
                SourceStep::AuthorSchema,
                &input,
                &output,
                Duration::from_millis(100),
            )
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
        assert!(started.elapsed() < Duration::from_secs(2));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn source_preserves_create_order_and_duplicate_environment_names() {
        let first = SpkCommand {
            argv: vec!["/first".into(), "".into(), "a".into()],
            environ: vec![("A".into(), "one".into()), ("A".into(), "two".into())],
        };
        let second = SpkCommand {
            argv: vec!["/second".into()],
            environ: vec![],
        };
        let mut manifest: SpkManifest = serde_json::from_value(json!({
            "app_id":"ignored-by-this-projection", "app_title":"test", "app_version":1,
            "actions":[],"continue_command":{"argv":["/continue"],"environ":[]}
        }))
        .unwrap();
        manifest.actions = vec![
            Action {
                noun_phrase: "first".into(),
                command: first,
            },
            Action {
                noun_phrase: "second".into(),
                command: second,
            },
        ];
        let source = signed_launch_source(&manifest, b"v1").unwrap();
        assert_eq!(source["packageCanonicalHex"], "7631");
        assert_eq!(
            source["createCommands"][0]["argvHex"],
            json!(["2f6669727374", "", "61"])
        );
        assert_eq!(
            source["createCommands"][0]["environHex"],
            json!([
                {"keyHex":"41","valueHex":"6f6e65"},
                {"keyHex":"41","valueHex":"74776f"}
            ])
        );
        assert_eq!(
            source["createCommands"][1]["argvHex"],
            json!(["2f7365636f6e64"])
        );
        assert_eq!(
            source["continueCommand"]["argvHex"],
            json!(["2f636f6e74696e7565"])
        );
    }

    #[test]
    fn command_bounds_refuse_nul_and_empty_executable() {
        let mut command = SpkCommand {
            argv: vec!["".into()],
            environ: vec![],
        };
        assert!(valid_command(&command).is_err());
        command.argv[0] = "/app".into();
        command.environ.push(("A".into(), "\0".into()));
        assert!(valid_command(&command).is_err());
    }
}
