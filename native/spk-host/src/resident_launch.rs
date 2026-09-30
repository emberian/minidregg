//! One resident operator supervisor starts the app child and retains fd3.
//! The source-owned lifecycle-v2 claim/descriptor adapter must construct the
//! exact `VerifiedBegin` and package command before calling this module.
#![allow(dead_code)] // Native lifecycle-v2 Host route is not linked yet.

use crate::dispatch_native::{private_dir, PrivateOperator};
use crate::hostd::{Journal, VerifiedBegin};
use crate::launch_descriptor_native::{
    author_signed_launch, signed_launch_source, SourceLaunchDescriptor,
};
use crate::materialize::{signed_schema_source, InstalledPackage};
use crate::rpc_adapter::RpcDriver;
use crate::sandbox::{
    app_output, bwrap_args, directory_entry, inherited_fd, open_protected_directory,
    verify_executable, verify_var_volume, AppOutput, AppOutputSummary, SandboxSpec,
};
use crate::spawn_gate::{AppFds, BoundedChild, SpawnSpec};
use crate::volume_custody::VolumeWitness;
use minidregg_spk_rpc::decode_bridge_config;
use sandstorm_package::manifest::Command as SpkCommand;
use serde_json::Value;
use std::fs::{DirBuilder, OpenOptions};
use std::io;
use std::io::Read;
use std::os::fd::{AsRawFd, OwnedFd};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::path::Path;

const MAX_RETAINED_DESCRIPTOR: u64 = 12_102_759;

fn retained_descriptor_file(path: &Path) -> io::Result<Vec<u8>> {
    let parent = path
        .parent()
        .ok_or_else(|| invalid("descriptor parent absent"))?;
    private_dir(parent)?;
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.nlink() != 1
        || meta.permissions().mode() & 0o777 != 0o600
        || meta.len() == 0
        || meta.len() > MAX_RETAINED_DESCRIPTOR
    {
        return Err(invalid("retained signed descriptor file custody refused"));
    }
    let mut bytes = Vec::with_capacity(meta.len() as usize);
    file.by_ref()
        .take(MAX_RETAINED_DESCRIPTOR + 1)
        .read_to_end(&mut bytes)?;
    let after = file.metadata()?;
    if bytes.len() as u64 != meta.len()
        || after.dev() != meta.dev()
        || after.ino() != meta.ino()
        || after.len() != meta.len()
        || after.mtime() != meta.mtime()
        || after.mtime_nsec() != meta.mtime_nsec()
    {
        return Err(invalid("retained signed descriptor changed during read"));
    }
    Ok(bytes)
}

fn source_text<'a>(view: &'a Value, name: &str) -> io::Result<&'a str> {
    view.get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("retained signed descriptor source field absent"))
}

fn hex_bytes(bytes: &[u8]) -> String {
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(result, "{byte:02x}").expect("hex String");
    }
    result
}

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, reason)
}

/// A source descriptor and commands from one signature-verified SPK parse.
/// Callers cannot pair an arbitrary package with a different descriptor.
pub(crate) struct SourceBoundLaunch<'a> {
    package: &'a InstalledPackage,
    descriptor: SourceLaunchDescriptor,
}

impl<'a> SourceBoundLaunch<'a> {
    #[cfg(test)]
    pub(crate) fn test_pair(
        package: &'a InstalledPackage,
        descriptor: SourceLaunchDescriptor,
    ) -> Self {
        Self {
            package,
            descriptor,
        }
    }

    pub(crate) fn author(
        operator: &PrivateOperator,
        package: &'a InstalledPackage,
        attempt_dir: &Path,
    ) -> io::Result<Self> {
        let descriptor = author_signed_launch(operator, package, attempt_dir)?;
        Ok(Self {
            package,
            descriptor,
        })
    }

    /// Reopen a retained descriptor after process restart without issuing a
    /// second author request. A fresh private read-only inspector rechecks all
    /// canonical bytes against this one verified signed-SPK parse.
    pub(crate) fn load_retained(
        operator: &PrivateOperator,
        package: &'a InstalledPackage,
        attempt_dir: &Path,
        probe_dir: &Path,
    ) -> io::Result<Self> {
        private_dir(attempt_dir)?;
        private_dir(
            probe_dir
                .parent()
                .ok_or_else(|| invalid("descriptor probe parent absent"))?,
        )?;
        DirBuilder::new().mode(0o700).create(probe_dir)?;
        let package_dir = attempt_dir.join("package-v1");
        let member = package
            .signed_bridge_config
            .as_deref()
            .ok_or_else(|| invalid("retained signed bridge absent"))?;
        let bridge = decode_bridge_config(member).map_err(io::Error::other)?;
        if bridge.save_identity_caps
            || bridge.expect_app_hooks
            || bridge
                .api_path
                .as_deref()
                .is_some_and(|path| minidregg_signed_api_path::checked_prefix(path).is_err())
        {
            return Err(invalid("retained signed bridge outside resident mapping"));
        }
        let schema_source = signed_schema_source(&bridge, package.manifest.app_version);
        let schema = retained_descriptor_file(&package_dir.join("schema.bin"))?;
        let schema_view: Value = serde_json::from_slice(&operator.tool(
            "inspect",
            "application-permission-schema",
            &package_dir.join("schema.bin"),
            &probe_dir.join("schema.json"),
        )?)?;
        if source_text(&schema_view, "type")? != "minidregg-application-permission-schema-v1"
            || source_text(&schema_view, "canonical")? != hex_bytes(&schema)
            || schema_view.get("version") != schema_source.get("version")
            || schema_view.get("permissions") != schema_source.get("permissions")
            || schema_view.get("roles") != schema_source.get("roles")
            || schema_view.get("denied") != schema_source.get("denied")
        {
            return Err(invalid("retained schema differs from signed bridge"));
        }
        let package_canonical = retained_descriptor_file(&package_dir.join("descriptor.bin"))?;
        let package_view: Value = serde_json::from_slice(&operator.tool(
            "inspect",
            "application-spk-package-identity",
            &package_dir.join("descriptor.bin"),
            &probe_dir.join("package.json"),
        )?)?;
        let bridge_sha = package
            .signed_bridge_config_sha256
            .ok_or_else(|| invalid("retained signed bridge digest absent"))?;
        let mut image_identity = b"DREGG/SPK-IMAGE/v1".to_vec();
        image_identity.extend_from_slice(&package.raw_sha256_bytes);
        if source_text(&package_view, "type")?
            != minidregg_signed_api_path::descriptor_inspection_type(bridge.api_path.as_deref())
                .map_err(invalid)?
            || source_text(&package_view, "canonical")? != hex_bytes(&package_canonical)
            || source_text(&package_view, "rawSha256")? != hex_bytes(&package.raw_sha256_bytes)
            || source_text(&package_view, "rawLength")? != package.raw_length.to_string()
            || source_text(&package_view, "signedAppId")?
                != hex_bytes(package.manifest.app_id.0.as_bytes())
            || source_text(&package_view, "signedAppVersion")?
                != package.manifest.app_version.to_string()
            || source_text(&package_view, "manifestSha256")?
                != hex_bytes(&package.signed_manifest_sha256)
            || source_text(&package_view, "bridgeConfigSha256")? != hex_bytes(&bridge_sha)
            || source_text(&package_view, "imageIdentity")? != hex_bytes(&image_identity)
            || source_text(&package_view, "bridgeApiPath")?
                != hex_bytes(bridge.api_path.as_deref().unwrap_or("").as_bytes())
        {
            return Err(invalid(
                "retained package descriptor differs from signed SPK",
            ));
        }
        let interfaces = package_view
            .get("interfaces")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("retained package interfaces absent"))?;
        let expected: &[(&str, &str)] = if bridge.api_path.is_some() {
            &[("1", "web"), ("2", "api")]
        } else {
            &[("1", "web")]
        };
        if interfaces.len() != expected.len() {
            return Err(invalid("retained package interface count differs"));
        }
        for (interface, (id, kind)) in interfaces.iter().zip(expected) {
            if source_text(interface, "id")? != *id
                || source_text(interface, "version")? != "1"
                || source_text(interface, "kind")? != *kind
                || source_text(interface, "schema")? != hex_bytes(&schema)
                || source_text(interface, "schemaRoot")? != source_text(&schema_view, "root")?
            {
                return Err(invalid(
                    "retained package interface differs from signed bridge",
                ));
            }
        }
        let package_root = source_text(&package_view, "root")?.to_owned();
        if !crate::lifecycle_v3_native::decimal(&package_root) {
            return Err(invalid("retained package root malformed"));
        }
        let launch_source = signed_launch_source(&package.manifest, &package_canonical)?;
        let retained_source: Value = serde_json::from_slice(&retained_descriptor_file(
            &attempt_dir.join("launch-source.json"),
        )?)?;
        if retained_source != launch_source {
            return Err(invalid(
                "retained launch source differs from signed command order",
            ));
        }
        let canonical = retained_descriptor_file(&attempt_dir.join("launch-descriptor.bin"))?;
        let view: Value = serde_json::from_slice(&operator.tool(
            "inspect",
            "application-spk-launch-descriptor",
            &attempt_dir.join("launch-descriptor.bin"),
            &probe_dir.join("launch.json"),
        )?)?;
        if source_text(&view, "type")?
            != minidregg_signed_api_path::launch_inspection_type(bridge.api_path.as_deref())
                .map_err(invalid)?
            || source_text(&view, "canonical")? != hex_bytes(&canonical)
            || source_text(&view, "packageCanonicalHex")? != hex_bytes(&package_canonical)
            || source_text(&view, "packageRoot")? != package_root
            || !crate::lifecycle_v3_native::decimal(source_text(&view, "root")?)
        {
            return Err(invalid("retained launch descriptor differs from package"));
        }
        let creates = view
            .get("createCommands")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("retained create command projection absent"))?;
        let expected = launch_source["createCommands"]
            .as_array()
            .ok_or_else(|| invalid("signed create commands absent"))?;
        if creates.len() != expected.len() {
            return Err(invalid("retained create count differs"));
        }
        let mut create_digests = Vec::with_capacity(creates.len());
        for (actual, expected) in creates.iter().zip(expected) {
            if actual.get("argvHex") != expected.get("argvHex")
                || actual.get("environHex") != expected.get("environHex")
            {
                return Err(invalid("retained create command differs from signed SPK"));
            }
            let digest = source_text(actual, "digest")?;
            if !crate::lifecycle_v3_native::decimal(digest)
                || source_text(actual, "canonical")?.is_empty()
            {
                return Err(invalid("retained create command commitment malformed"));
            }
            create_digests.push(digest.to_owned());
        }
        let continuation = &view["continueCommand"];
        if continuation.get("argvHex") != launch_source["continueCommand"].get("argvHex")
            || continuation.get("environHex") != launch_source["continueCommand"].get("environHex")
        {
            return Err(invalid("retained continue command differs from signed SPK"));
        }
        if !crate::lifecycle_v3_native::decimal(source_text(continuation, "digest")?)
            || source_text(continuation, "canonical")?.is_empty()
        {
            return Err(invalid("retained continue command commitment malformed"));
        }
        let descriptor = SourceLaunchDescriptor {
            package: crate::descriptor_native::SourceDescriptor {
                canonical: package_canonical,
                root: package_root,
                image_identity,
                api_path: bridge.api_path,
            },
            canonical,
            root: source_text(&view, "root")?.to_owned(),
            create_digests,
            continue_digest: source_text(continuation, "digest")?.to_owned(),
        };
        Ok(Self {
            package,
            descriptor,
        })
    }

    pub(crate) fn descriptor(&self) -> &SourceLaunchDescriptor {
        &self.descriptor
    }

    pub(crate) fn signed_package_sha256(&self) -> &str {
        &self.package.raw_sha256
    }

    /// Select only the signed create command named by Mini's inspected v3
    /// BEGIN/claim. No default action or `continueCommand` may substitute.
    pub(crate) fn source_selected_create(
        &self,
        index: usize,
        source_digest: &str,
    ) -> io::Result<&SpkCommand> {
        if self
            .descriptor
            .create_digests
            .get(index)
            .map(String::as_str)
            != Some(source_digest)
        {
            return Err(invalid(
                "source create selection differs from signed launch descriptor",
            ));
        }
        self.package
            .manifest
            .actions
            .get(index)
            .map(|action| &action.command)
            .ok_or_else(|| invalid("source create selection absent from signed SPK"))
    }

    /// Continue is selected only by the source-inspected v3 BEGIN with a
    /// retained successful create witness. The caller must compare that
    /// witness to the committed claim before opening the physical volume.
    pub(crate) fn source_selected_continue(&self, source_digest: &str) -> io::Result<&SpkCommand> {
        if self.descriptor.continue_digest != source_digest {
            return Err(invalid(
                "source continue selection differs from signed launch descriptor",
            ));
        }
        Ok(&self.package.manifest.continue_command)
    }
}

/// Preopened file descriptors never appear in HTTP or Mini JSON. The app end
/// is duplicated to fd3 only inside the bounded, privilege-dropping gate.
pub(crate) struct PreparedResident {
    host_rpc: UnixStream,
    _child_rpc: OwnedFd,
    _image: OwnedFd,
    _persistent_var: OwnedFd,
    _seccomp: OwnedFd,
    /// Write end of the app's stdout/stderr pipe; dropped once the gate has
    /// spawned so the pump sees EOF when the app's last writer exits.
    _output_writer: OwnedFd,
    output: AppOutput,
    launch: SpawnSpec,
}

pub(crate) struct ResidentProcess {
    pub rpc: RpcDriver,
    child: BoundedChild,
    output: AppOutput,
}

impl ResidentProcess {
    pub(crate) fn child_pid(&self) -> u32 {
        self.child.pid()
    }

    /// A normal service shutdown drops the gate child, while systemd's exact
    /// unit cgroup closes any descendants. No HTTP request owns this process.
    pub(crate) fn wait(mut self) -> io::Result<(i32, AppOutputSummary)> {
        let status = self.child.wait()?;
        Ok((status, self.output.finish()?))
    }
}

impl PreparedResident {
    pub(crate) fn prepare(
        spec: &SandboxSpec,
        app_uid: u32,
        app_gid: u32,
        bwrap_sha256: &str,
    ) -> io::Result<Self> {
        if app_uid == 0 || app_gid == 0 || unsafe { libc::geteuid() } == app_uid {
            return Err(invalid("resident supervisor must be separate from app UID"));
        }
        let args = bwrap_args(spec)?;
        let image = open_protected_directory(&spec.image_root, app_uid, false)?;
        let persistent_var = open_protected_directory(&spec.persistent_var, app_uid, true)?;
        if spec.persistent_var.starts_with(&spec.image_root)
            || spec.image_root.starts_with(&spec.persistent_var)
        {
            return Err(invalid("image and persistent /var overlap"));
        }
        for mountpoint in ["var", "tmp", "proc", "dev"] {
            directory_entry(image.as_raw_fd(), mountpoint)?;
        }
        verify_var_volume(
            &spec.persistent_var,
            persistent_var.as_raw_fd(),
            spec.persistent_var_max_bytes,
            app_uid,
        )?;
        verify_executable(&spec.bwrap, app_uid)?;

        let (host_rpc, child_rpc) = UnixStream::pair()?;
        let child_rpc = inherited_fd(child_rpc.as_raw_fd())?;
        let image = inherited_fd(image.as_raw_fd())?;
        let persistent_var = inherited_fd(persistent_var.as_raw_fd())?;
        let seccomp = inherited_fd(crate::seccomp::resident_filter_fd()?.as_raw_fd())?;
        let (output_writer, output) = app_output(&spec.app_output)?;
        let output_writer = inherited_fd(output_writer.as_raw_fd())?;
        let launch = SpawnSpec {
            program: spec.bwrap.clone(),
            sha256: bwrap_sha256.to_owned(),
            args,
            app_uid,
            app_gid,
            fds: Some(AppFds {
                rpc: child_rpc.as_raw_fd(),
                image: image.as_raw_fd(),
                persistent_var: persistent_var.as_raw_fd(),
                seccomp: seccomp.as_raw_fd(),
                output: output_writer.as_raw_fd(),
            }),
        };
        Ok(Self {
            host_rpc,
            _child_rpc: child_rpc,
            _image: image,
            _persistent_var: persistent_var,
            _seccomp: seccomp,
            _output_writer: output_writer,
            output,
            launch,
        })
    }

    /// Compare the root-owned custody handoff with the exact directory held
    /// open for fd5. This is a physical observation; the caller must also
    /// compare the witness bytes and volume ID to the source-owned v3 claim.
    pub(crate) fn compare_attested_volume(&self, witness: &VolumeWitness) -> io::Result<()> {
        witness.compare_open_mount(self._persistent_var.as_raw_fd())?;
        witness.recheck_handoff()
    }

    /// Repeat the fixed handoff/FD5 check at the last physical boundary before
    /// consuming the journal's one-shot spawn. This does not mint Mini launch
    /// authority or promise cancellation of a later operator mount change.
    pub(crate) fn start_attested(
        self,
        journal: &Journal,
        begin: &VerifiedBegin,
        witness: &VolumeWitness,
    ) -> io::Result<ResidentProcess> {
        self.compare_attested_volume(witness)?;
        self.start(journal, begin)
    }

    /// Must execute as the exact unit MainPID after native COMMITTED/v2 claim
    /// and signed package identity were independently matched. A source
    /// refusal or RPC setup failure never starts a second app generation.
    pub(crate) fn start(
        self,
        journal: &Journal,
        begin: &VerifiedBegin,
    ) -> io::Result<ResidentProcess> {
        let child = journal.enter_and_spawn(begin, &self.launch)?;
        let rpc = RpcDriver::from_connected_stream(begin.app, begin.generation, self.host_rpc)?;
        Ok(ResidentProcess { rpc, child, output: self.output })
    }

    /// `start` without the journal: the identical gate call and descriptor
    /// lifetimes, for the root-only sandbox audit.
    #[cfg(test)]
    fn spawn_for_audit(self) -> io::Result<(BoundedChild, UnixStream, AppOutput)> {
        let child = crate::spawn_gate::spawn_bounded(&self.launch)?;
        Ok((child, self.host_rpc, self.output))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_native::SourceDescriptor;
    use sandstorm_package::manifest::Action;
    use sandstorm_package::SpkManifest;
    use serde_json::json;

    #[test]
    fn resident_refuses_app_uid_equal_to_operator_before_opening_paths() {
        let spec = SandboxSpec {
            bwrap: "/missing/bwrap".into(),
            image_root: "/missing/image".into(),
            persistent_var: "/missing/var".into(),
            persistent_var_max_bytes: 1024,
            argv: vec!["/bin/true".into()],
            environ: vec![],
            app_output: "/missing/app-output.log".into(),
        };
        assert!(PreparedResident::prepare(
            &spec,
            unsafe { libc::geteuid() },
            unsafe { libc::getegid() },
            &"0".repeat(64),
        )
        .is_err());
    }

    /// Root-only audit inputs, set by `scripts/spk-platform/sandbox-floor-audit.sh`.
    struct Audit {
        spec: SandboxSpec,
        uid: u32,
        gid: u32,
        bwrap_sha256: String,
    }

    fn audit_inputs(output_name: &str) -> Audit {
        assert_eq!(unsafe { libc::geteuid() }, 0, "the resident sandbox audit runs as root");
        let var = |key: &str| std::env::var(key).unwrap_or_else(|_| panic!("{key} unset"));
        let dir = std::path::PathBuf::from(var("SPK_AUDIT_DIR"));
        Audit {
            spec: SandboxSpec {
                bwrap: var("SPK_AUDIT_BWRAP").into(),
                image_root: dir.join("image"),
                persistent_var: dir.join("var"),
                persistent_var_max_bytes: 64 * 1024 * 1024,
                argv: vec!["/spk-sandbox-probe".into()],
                environ: vec![("SPK_PROBE".into(), "resident".into())],
                app_output: dir.join(output_name),
            },
            uid: var("SPK_AUDIT_UID").parse().unwrap(),
            gid: var("SPK_AUDIT_GID").parse().unwrap(),
            bwrap_sha256: var("SPK_AUDIT_BWRAP_SHA256"),
        }
    }

    /// Launch the probe as the app; return its wait status and parsed report lines.
    fn run_probe(prepared: PreparedResident, log: &Path) -> (i32, Vec<Value>) {
        let (mut child, _host_rpc, output) = prepared.spawn_for_audit().unwrap();
        let status = child.wait().unwrap();
        let summary = output.finish().unwrap();
        let text = std::fs::read_to_string(log).unwrap();
        println!("{text}");
        println!(
            "bwrap-wait-status={status:#x} exited={} code={} signaled={} signal={}",
            libc::WIFEXITED(status),
            libc::WEXITSTATUS(status),
            libc::WIFSIGNALED(status),
            libc::WTERMSIG(status)
        );
        println!("output-summary kept={} discarded={}", summary.kept, summary.discarded);
        let lines = text.lines().filter_map(|line| serde_json::from_str(line).ok()).collect();
        (status, lines)
    }

    fn verdict(lines: &[Value]) -> Option<&str> {
        lines.iter().find_map(|line| line["verdict"].as_str())
    }

    fn held(lines: &[Value], check: &str) -> Option<bool> {
        lines.iter().find(|line| line["check"] == check).and_then(|line| line["held"].as_bool())
    }

    /// The exit gate of the sandbox floor: the probe, run as the app through the
    /// production preparation and spawn gate, reports every check held.
    #[test]
    #[ignore = "root only; run by scripts/spk-platform/sandbox-floor-audit.sh"]
    fn root_probe_holds_inside_resident_sandbox() {
        let audit = audit_inputs("app-output-floor.log");
        let prepared =
            PreparedResident::prepare(&audit.spec, audit.uid, audit.gid, &audit.bwrap_sha256).unwrap();
        let (status, lines) = run_probe(prepared, &audit.spec.app_output);
        assert_eq!(verdict(&lines), Some("floor-held"));
        for check in [
            "fd-census-self", "dotdot-from-inherited-fd", "network-public-connect",
            "userns-unshare-refused", "userns-clone-refused", "seccomp-filter-active",
            "capabilities-all-zero", "web-app-positive-control",
        ] {
            assert_eq!(held(&lines, check), Some(true), "{check}");
        }
        assert!(libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0, "status {status}");
    }

    /// Negative control: the same gate and probe with the pre-floor argument
    /// list (abe988d). The probe must report a breach, so the audit can go red.
    #[test]
    #[ignore = "root only; run by scripts/spk-platform/sandbox-floor-audit.sh"]
    fn root_probe_breaches_under_pre_floor_arguments() {
        let audit = audit_inputs("app-output-pre-floor.log");
        let mut prepared =
            PreparedResident::prepare(&audit.spec, audit.uid, audit.gid, &audit.bwrap_sha256).unwrap();
        let mut legacy: Vec<String> = [
            "--die-with-parent", "--new-session", "--unshare-user", "--unshare-pid",
            "--unshare-ipc", "--unshare-uts", "--unshare-cgroup", "--unshare-net",
            "--clearenv", "--ro-bind-fd", "4", "/", "--bind-fd", "5", "/var",
            "--size", "134217728", "--tmpfs", "/tmp", "--proc", "/proc",
            "--dev", "/dev", "--chdir", "/", "--setenv", "HOME", "/var",
            "--setenv", "TMPDIR", "/tmp", "--setenv", "PATH", "/usr/bin:/bin",
        ]
        .map(str::to_owned)
        .to_vec();
        legacy.extend(["--setenv", "SPK_PROBE", "pre-floor", "--", "/spk-sandbox-probe"].map(str::to_owned));
        prepared.launch.args = legacy;
        let (status, lines) = run_probe(prepared, &audit.spec.app_output);
        assert_eq!(verdict(&lines), Some("floor-breached"));
        for check in [
            "seccomp-filter-active", "fd-census-self", "socket-netlink-refused",
            "userns-unshare-refused",
        ] {
            assert_eq!(held(&lines, check), Some(false), "{check} did not fail");
        }
        assert!(libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 1, "status {status}");
    }

    #[test]
    fn inspected_create_index_and_digest_select_exact_signed_action() {
        let mut manifest: SpkManifest = serde_json::from_value(json!({
            "app_id":"signed", "app_title":"test", "app_version":1,
            "actions":[],
            "continue_command":{"argv":["/continue"],"environ":[]}
        }))
        .unwrap();
        manifest.actions = ["/first", "/second"]
            .into_iter()
            .map(|executable| Action {
                noun_phrase: executable.into(),
                command: SpkCommand {
                    argv: vec![executable.into()],
                    environ: vec![],
                },
            })
            .collect();
        let package = InstalledPackage {
            directory: "/protected/image".into(),
            raw_sha256: "a".repeat(64),
            raw_sha256_bytes: [0xaa; 32],
            raw_length: 1,
            signed_manifest_sha256: [0xbb; 32],
            signed_bridge_config_sha256: None,
            signed_bridge_config: None,
            manifest,
        };
        let launch = SourceLaunchDescriptor {
            package: SourceDescriptor {
                canonical: b"package".to_vec(),
                root: "1".into(),
                image_identity: b"image".to_vec(),
                api_path: None,
            },
            canonical: b"launch".to_vec(),
            root: "2".into(),
            create_digests: vec!["3".into(), "4".into()],
            continue_digest: "5".into(),
        };
        let bound = SourceBoundLaunch {
            package: &package,
            descriptor: launch,
        };
        assert_eq!(
            bound.source_selected_create(1, "4").unwrap().argv,
            ["/second"]
        );
        assert!(bound.source_selected_create(1, "3").is_err());
        assert!(bound.source_selected_create(2, "4").is_err());
        assert_eq!(
            bound.source_selected_continue("5").unwrap().argv,
            ["/continue"]
        );
        assert!(bound.source_selected_continue("4").is_err());
    }
}
