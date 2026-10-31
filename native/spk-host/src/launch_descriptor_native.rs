//! Signed SPK launch commands supplied to Mini's v2 descriptor author.
//!
//! The physical source is one `InstalledPackage` from a signature-verified
//! Bread parse. This module preserves create-action order, argument order and
//! every environment pair, including duplicate names. Mini alone owns the
//! canonical descriptor codec and root.
#![allow(dead_code)] // Resident v3 START caller follows the source-qualified route.

use crate::io_context::IoContext;
use sandstorm_package::manifest::Command as SpkCommand;
use sandstorm_package::SpkManifest;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use crate::descriptor_native::{author_signed_package, SourceDescriptor, SourceStep, SourceTool};
use crate::dispatch_native::{private_dir, write_new};
use crate::materialize::InstalledPackage;
use crate::materialize::{qualify_bridge_spk_with_profile, ImportProfile};
use serde::Deserialize;
use crate::canonical::{decimal, hex};

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
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
///
/// The steps of one qualification go to ONE storeless codec child (`HOST CONFIG codec`,
/// `Host.Main.serveCodec`: frames 7 and 8 are the detached `author` and `inspect` verbs, it never
/// opens a Store), started at the first step and ended with this value. A child that cannot be
/// started or ends without answering leaves the step to the detached verb, as before; a step whose
/// frame exceeds the codec bound is a detached verb too.
pub(crate) struct OfflineSourceHost {
    pub host: PathBuf,
    pub host_sha256: String,
    pub config: PathBuf,
    pub config_sha256: String,
    pub codec: std::sync::Mutex<CodecSlot>,
}

/// The qualification's codec child: not yet started, running, or unavailable (the detached verb
/// answers every later step).
#[derive(Default)]
pub(crate) enum CodecSlot {
    #[default]
    Unstarted,
    Running(CodecChild),
    Unavailable,
}

/// The codec frame bound (`HOST_MAX_FRAME`): a length prefix counts the operation byte.
const CODEC_FRAME_BOUND: usize = 12_102_760;

pub(crate) struct CodecChild {
    child: std::process::Child,
    input: std::process::ChildStdin,
    output: std::process::ChildStdout,
}

/// Why a codec exchange did not answer: the child is gone or misbehaved (the step falls back to
/// the detached verb), or the deadline passed (the step fails, as a detached verb past it does).
enum CodecFailure {
    Lost,
    Deadline,
}

impl CodecChild {
    fn spawn(host: &Path, config: &Path) -> io::Result<Self> {
        use std::os::fd::AsRawFd;
        let mut child = Command::new(host)
            .arg(config)
            .arg("codec")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        let (Some(input), Some(output)) = (child.stdin.take(), child.stdout.take()) else {
            let _ = child.kill();
            let _ = child.wait();
            return Err(invalid("offline codec pipes absent"));
        };
        for fd in [input.as_raw_fd(), output.as_raw_fd()] {
            // Non-blocking, so every write and read is bounded by the step's deadline.
            let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
            if flags < 0 || unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
                let _ = child.kill();
                let _ = child.wait();
                return Err(io::Error::last_os_error());
            }
        }
        Ok(CodecChild { child, input, output })
    }

    fn wait_ready(fd: i32, events: i16, deadline: Instant) -> Result<(), CodecFailure> {
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return Err(CodecFailure::Deadline);
            }
            let mut poll = libc::pollfd { fd, events, revents: 0 };
            let millis = remaining.as_millis().clamp(1, i32::MAX as u128) as i32;
            match unsafe { libc::poll(&mut poll, 1, millis) } {
                0 => continue,
                n if n > 0 => return Ok(()),
                _ if io::Error::last_os_error().kind() == io::ErrorKind::Interrupted => continue,
                _ => return Err(CodecFailure::Lost),
            }
        }
    }

    fn write_all(&mut self, mut bytes: &[u8], deadline: Instant) -> Result<(), CodecFailure> {
        use std::io::Write;
        use std::os::fd::AsRawFd;
        while !bytes.is_empty() {
            Self::wait_ready(self.input.as_raw_fd(), libc::POLLOUT, deadline)?;
            match self.input.write(bytes) {
                Ok(0) => return Err(CodecFailure::Lost),
                Ok(count) => bytes = &bytes[count..],
                Err(error) if matches!(error.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted) => {}
                Err(_) => return Err(CodecFailure::Lost),
            }
        }
        Ok(())
    }

    fn read_exact(&mut self, bytes: &mut [u8], deadline: Instant) -> Result<(), CodecFailure> {
        use std::os::fd::AsRawFd;
        let mut received = 0;
        while received < bytes.len() {
            Self::wait_ready(self.output.as_raw_fd(), libc::POLLIN, deadline)?;
            match self.output.read(&mut bytes[received..]) {
                Ok(0) => return Err(CodecFailure::Lost),
                Ok(count) => received += count,
                Err(error) if matches!(error.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted) => {}
                Err(_) => return Err(CodecFailure::Lost),
            }
        }
        Ok(())
    }

    /// One frame out (`u32 LE length, operation, payload`), one frame in: the answering operation
    /// and its body.
    fn exchange(&mut self, operation: u8, payload: &[u8], deadline: Instant) -> Result<(u8, Vec<u8>), CodecFailure> {
        let size = u32::try_from(payload.len() + 1).map_err(|_| CodecFailure::Lost)?;
        let mut frame = Vec::with_capacity(payload.len() + 5);
        frame.extend_from_slice(&size.to_le_bytes());
        frame.push(operation);
        frame.extend_from_slice(payload);
        self.write_all(&frame, deadline)?;
        let mut width = [0u8; 4];
        self.read_exact(&mut width, deadline)?;
        let size = u32::from_le_bytes(width) as usize;
        if size == 0 || size > CODEC_FRAME_BOUND {
            return Err(CodecFailure::Lost);
        }
        let mut answer = vec![0u8; size];
        self.read_exact(&mut answer, deadline)?;
        let body = answer.split_off(1);
        Ok((answer[0], body))
    }
}

impl Drop for CodecChild {
    fn drop(&mut self) {
        // A pure child holds nothing worth a goodbye: end it and reap it.
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

/// A codec step's answer, written where the detached verb would have written it: a new private
/// file, never through a link.
fn write_new_output(output: &Path, bytes: &[u8]) -> io::Result<()> {
    use std::io::Write;
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(output)
        .ctx("open", output)?;
    file.write_all(bytes)
}

fn read_private(path: &Path, bound: u64) -> io::Result<Vec<u8>> {
    private_dir(path.parent().ok_or_else(|| invalid("source artifact parent absent"))?)?;
    crate::private_file::read(path, bound, "offline source artifact identity or bound refused")
}

impl OfflineSourceHost {
    /// The pinned Host image is verified once per inode in this process (`verified_image`: the
    /// path must still name the hashed inode with the same size, mode, owner and both times, or it
    /// is hashed again); the small config is read and hashed every time. A qualification checks
    /// the pin before and after each of its steps: hashing the 180 MB image each time cost about
    /// 0.15 s per check, a dozen per qualification.
    fn check_pin(&self) -> io::Result<()> {
        let named = fs::symlink_metadata(&self.host).ctx("inspect", &self.host)?;
        if !self.host.is_absolute()
            || !named.is_file()
            || named.permissions().mode() & 0o022 != 0
            || named.len() == 0
        {
            return Err(invalid("offline Mini Host image identity refused"));
        }
        crate::dispatch_native::verified_image(&self.host, &self.host_sha256)
            .map_err(|_| invalid("offline Mini Host/config SHA-256 pin drift"))?;
        if self.config_sha256
            != hex(&Sha256::digest(crate::dispatch_native::read_pinned_input(
                &self.config,
                MAX_SOURCE_CONFIG as usize,
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
        let deadline = Instant::now() + timeout;
        if !self.codec_step(command, kind, &input_bytes, output, deadline)? {
            self.detached_step(command, kind, input, output, deadline)?;
        }
        self.checked_output(command, input, limit, &input_bytes, output)
    }

    /// The step on this qualification's codec child. `false`: no child can answer it (none could
    /// be started, the child ended without answering, or the frame exceeds the codec bound), and
    /// the detached verb runs it. A refusal is the step's refusal; the deadline is the step's.
    fn codec_step(
        &self,
        command: &str,
        kind: &str,
        input_bytes: &[u8],
        output: &Path,
        deadline: Instant,
    ) -> io::Result<bool> {
        use crate::host_operations::{AUTHOR, INSPECT, RESPONSE_HOST_OUTCOME, RESPONSE_NO_RECORD};
        let operation = match command {
            "author" => AUTHOR,
            "inspect" => INSPECT,
            _ => return Ok(false),
        };
        if kind.is_empty() || kind.len() > u16::MAX as usize
            || 1 + 2 + kind.len() + input_bytes.len() > CODEC_FRAME_BOUND
        {
            return Ok(false);
        }
        let mut payload = Vec::with_capacity(2 + kind.len() + input_bytes.len());
        payload.extend_from_slice(&(kind.len() as u16).to_le_bytes());
        payload.extend_from_slice(kind.as_bytes());
        payload.extend_from_slice(input_bytes);
        let mut slot = self.codec.lock().map_err(|_| invalid("offline codec lock poisoned"))?;
        if matches!(*slot, CodecSlot::Unstarted) {
            *slot = match CodecChild::spawn(&self.host, &self.config) {
                Ok(child) => CodecSlot::Running(child),
                Err(_) => CodecSlot::Unavailable,
            };
        }
        let CodecSlot::Running(child) = &mut *slot else {
            return Ok(false);
        };
        match child.exchange(operation, &payload, deadline) {
            Ok((answer, body)) if answer == operation => {
                if body.is_empty() {
                    *slot = CodecSlot::Unavailable;
                    return Err(invalid("pinned offline Mini Host author/inspect refused"));
                }
                write_new_output(output, &body)?;
                Ok(true)
            }
            Ok((answer, _)) if answer == RESPONSE_NO_RECORD || answer == RESPONSE_HOST_OUTCOME => {
                Err(invalid("pinned offline Mini Host author/inspect refused"))
            }
            Ok(_) => {
                // Answered out of turn: this child is not trusted with another frame.
                *slot = CodecSlot::Unavailable;
                Err(invalid("pinned offline Mini Host codec answered out of turn"))
            }
            Err(CodecFailure::Lost) => {
                *slot = CodecSlot::Unavailable;
                Ok(false)
            }
            Err(CodecFailure::Deadline) => {
                *slot = CodecSlot::Unavailable;
                Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "pinned offline Mini Host source deadline",
                ))
            }
        }
    }

    /// The step as the detached `HOST CONFIG VERB KIND INPUT OUTPUT`, one process.
    fn detached_step(
        &self,
        command: &str,
        kind: &str,
        input: &Path,
        output: &Path,
        deadline: Instant,
    ) -> io::Result<()> {
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
        Ok(())
    }

    /// The step's output as the next step reads it: one private regular file of this uid within
    /// the bound, with the pin and the input unchanged since the step began.
    fn checked_output(
        &self,
        command: &str,
        input: &Path,
        limit: u64,
        input_bytes: &[u8],
        output: &Path,
    ) -> io::Result<Vec<u8>> {
        let mut file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&output).ctx("open", &output)?;
        let named = fs::symlink_metadata(&output).ctx("inspect", &output)?;
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
    #[serde(default)]
    import_profile: Option<String>,
    mini_host: PathBuf,
    mini_host_sha256: String,
    mini_config: PathBuf,
    mini_config_sha256: String,
    attempt_dir: PathBuf,
}

fn lowercase_sha256(value: &str) -> bool {
    crate::canonical::hex64(&value)
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
    let import_profile: ImportProfile = config
        .import_profile
        .as_deref()
        .unwrap_or("standard-v1")
        .parse()?;
    let source_host = OfflineSourceHost {
        host: config.mini_host,
        host_sha256: config.mini_host_sha256,
        config: config.mini_config,
        config_sha256: config.mini_config_sha256,
        codec: Default::default(),
    };
    source_host.check_pin()?;
    let (package, _) = qualify_bridge_spk_with_profile(&config.source_spk, import_profile)?;
    let launch = author_signed_launch(&source_host, &package, &config.attempt_dir)?;
    if read_private(config_path, MAX_SOURCE_CONFIG)? != config_bytes {
        return Err(invalid("offline launch qualification input changed"));
    }
    source_host.check_pin()?;
    let result = qualification_json(&package.raw_sha256, &launch.package.root, &launch.root,
        &hex(&Sha256::digest(&launch.canonical)), &launch.create_digests, &launch.continue_digest);
    // Beside the qualification, never in it: the consumers of qualification.json read it with
    // deny_unknown_fields. `grain install` reports these two values to the apps worker.
    write_new(
        &config.attempt_dir,
        "signed-identity.json",
        &serde_json::to_vec_pretty(&json!({
            "signedAppId":package.manifest.app_id.0,
            "signedAppVersion":package.manifest.app_version.to_string(),
        }))?,
    )?;
    write_new(
        &config.attempt_dir,
        "qualification.json",
        &serde_json::to_vec_pretty(&result)?,
    )?;
    Ok(result)
}

/// The one qualification document (`qualification.json`). Its readers (install_v3, resident_service,
/// the stop service) parse it with deny_unknown_fields, so a field added here breaks resident START:
/// anything else the install wants to report goes in a separate file beside it.
pub(crate) fn qualification_json(raw_sha256: &str, package_root: &str, launch_root: &str, canonical_sha256: &str,
    create_digests: &[String], continue_digest: &str) -> serde_json::Value {
    json!({
        "protocol":"mini-spk-launch-qualified-v2",
        "rawSha256":raw_sha256,
        "packageRoot":package_root,
        "launchRoot":launch_root,
        "launchCanonicalSha256":canonical_sha256,
        "createCount":create_digests.len().to_string(),
        "createDigests":create_digests,
        "continueDigest":continue_digest,
    })
}

impl SourceTool for OfflineSourceHost {
    fn source_step(&self, step: SourceStep, input: &Path, output: &Path) -> io::Result<Vec<u8>> {
        self.run_step(step, input, output, SOURCE_CHILD_DEADLINE)
    }
}

/// The one launch-command profile (`sandbox::validate_command`), applied at
/// qualification so a package the sandbox or spawn gate would refuse never
/// reaches a BEGIN.
fn valid_command(command: &SpkCommand) -> io::Result<()> {
    crate::sandbox::validate_command(&command.argv, &command.environ)
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
    if field(&view, "type")?
        != minidregg_signed_api_path::launch_inspection_type(v1.api_path.as_deref())
            .map_err(invalid)?
        || field(&view, "canonical")? != hex(&canonical)
        || field(&view, "packageCanonicalHex")? != hex(&v1.canonical)
        || field(&view, "packageRoot")? != v1.root
        || !decimal(field(&view, "root")?)
    {
        return Err(invalid(
            "Mini launch descriptor differs from verified signed package",
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
        }
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let source = OfflineSourceHost {
            host_sha256: hex(&Sha256::digest(fs::read(&host).unwrap())),
            config_sha256: hex(&Sha256::digest(fs::read(&config).unwrap())),
            host,
            config,
            codec: Default::default(),
        };
        (root, source, input, output)
    }

    #[test]
    fn offline_check_pin_reads_a_config_under_a_group_readable_parent_but_not_a_writable_one() {
        let (root, source, _input, _output) = offline_fixture("#!/bin/sh\nexit 0\n");
        // The hosted frame: the Host's deployment directory is 0710 for the mini-sessions group.
        fs::set_permissions(&root, fs::Permissions::from_mode(0o710)).unwrap();
        source.check_pin().unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o770)).unwrap();
        let error = source.check_pin().unwrap_err().to_string();
        assert!(error.contains("pinned input directory") && error.contains("writable by group or others"), "{error}");
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        fs::remove_dir_all(&root).unwrap();
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
        // The image is verified once per inode; a rewrite of it is hashed again and refused.
        let image = fs::read(&source.host).unwrap();
        let mode = fs::metadata(&source.host).unwrap().permissions();
        fs::write(&source.host, [image.as_slice(), b"# drift\n"].concat()).unwrap();
        fs::set_permissions(&source.host, mode).unwrap();
        assert!(source.check_pin().is_err());
        fs::write(&source.host, &image).unwrap();
        fs::set_permissions(&source.host, fs::metadata(&source.host).unwrap().permissions()).unwrap();
        assert!(source.check_pin().is_ok());
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

    /// A mock Host that speaks the codec loop: each frame `7|8, u16 kind length, kind, input`
    /// is answered with the same operation and `kind:input`, except the kind `refuse`, answered
    /// with the outcome marker 255. Every start appends its mode to `starts`.
    fn codec_mock(root: &Path) -> String {
        const MOCK: &str = r#"#!/usr/bin/env python3
import sys, struct
open(STARTS, 'a').write(sys.argv[2] + '\n')
if sys.argv[2] != 'codec':
    d = open(sys.argv[4], 'rb').read()
    open(sys.argv[5], 'wb').write(sys.argv[3].encode() + b':' + d)
    sys.exit(0)
i, o = sys.stdin.buffer, sys.stdout.buffer
while True:
    h = i.read(4)
    if len(h) < 4:
        break
    f = i.read(struct.unpack('<I', h)[0])
    op = f[0]
    n = struct.unpack('<H', f[1:3])[0]
    k, d = f[3:3 + n], f[3 + n:]
    a = bytes([255]) + b'refused' if k == b'refuse' else bytes([op]) + k + b':' + d
    o.write(struct.pack('<I', len(a)) + a)
    o.flush()
"#;
        MOCK.replace("STARTS", &format!("{:?}", root.join("starts").display().to_string()))
    }

    #[test]
    fn offline_steps_share_one_codec_child_and_answer_as_the_detached_verb() {
        let (root, source, input, _output) = offline_fixture("#!/bin/sh\nexit 1\n");
        fs::write(&source.host, codec_mock(&root)).unwrap();
        let source = OfflineSourceHost {
            host_sha256: hex(&Sha256::digest(fs::read(&source.host).unwrap())),
            ..source
        };
        let mut answers = Vec::new();
        for (index, step) in [SourceStep::AuthorSchema, SourceStep::InspectSchema, SourceStep::AuthorLaunch]
            .into_iter()
            .enumerate()
        {
            let output = root.join(format!("out-{index}.bin"));
            let (_, kind) = step.command_kind();
            let bytes = source.run_step(step, &input, &output, Duration::from_secs(5)).unwrap();
            assert_eq!(bytes, [kind.as_bytes(), b":original"].concat());
            assert_eq!(fs::read(&output).unwrap(), bytes);
            assert_eq!(fs::metadata(&output).unwrap().permissions().mode() & 0o777, 0o600);
            answers.push(bytes);
        }
        // One codec child answered all three; no detached verb ran.
        assert_eq!(fs::read_to_string(root.join("starts")).unwrap(), "codec\n");
        // The detached verb's answer for the same step is the same bytes.
        *source.codec.lock().unwrap() = CodecSlot::Unavailable;
        let detached = source
            .run_step(SourceStep::AuthorSchema, &input, &root.join("detached.bin"), Duration::from_secs(5))
            .unwrap();
        assert_eq!(detached, answers[0]);
        assert_eq!(fs::read_to_string(root.join("starts")).unwrap(), "codec\nauthor\n");
        drop(source);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn offline_codec_refusal_is_the_steps_refusal_and_a_lost_child_falls_back() {
        let (root, source, input, _output) = offline_fixture("#!/bin/sh\nexit 1\n");
        fs::write(&source.host, codec_mock(&root)).unwrap();
        let source = OfflineSourceHost {
            host_sha256: hex(&Sha256::digest(fs::read(&source.host).unwrap())),
            ..source
        };
        let refused = root.join("refused.bin");
        let error = source.codec_step("author", "refuse", b"x", &refused, Instant::now() + Duration::from_secs(5))
            .unwrap_err();
        assert!(error.to_string().contains("refused"), "{error}");
        assert!(fs::symlink_metadata(&refused).is_err());
        // The child that refused still serves the next step.
        let output = root.join("after.bin");
        source.run_step(SourceStep::InspectPackage, &input, &output, Duration::from_secs(5)).unwrap();
        assert_eq!(fs::read_to_string(root.join("starts")).unwrap(), "codec\n");
        // A child that ends without answering leaves the step to the detached verb.
        if let CodecSlot::Running(child) = &mut *source.codec.lock().unwrap() {
            let _ = child.child.kill();
            let _ = child.child.wait();
        }
        let output = root.join("fallback.bin");
        let bytes = source.run_step(SourceStep::AuthorPackage, &input, &output, Duration::from_secs(5)).unwrap();
        assert_eq!(bytes, b"application-spk-package-identity:original");
        assert_eq!(fs::read_to_string(root.join("starts")).unwrap(), "codec\nauthor\n");
        assert!(matches!(*source.codec.lock().unwrap(), CodecSlot::Unavailable));
        drop(source);
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
        command.argv[0] = "app".into();
        assert!(valid_command(&command).is_err());
        command.argv[0] = "/app".into();
        command.environ.push(("A".into(), "\0".into()));
        assert!(valid_command(&command).is_err());
        command.environ[0] = ("A=B".into(), "v".into());
        assert!(valid_command(&command).is_err());
        command.environ[0] = ("A".into(), "v".into());
        assert!(valid_command(&command).is_ok());
    }
}
