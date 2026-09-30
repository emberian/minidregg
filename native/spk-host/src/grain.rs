//! `spk-host grain`: install one signed SPK as one admitted Mini application
//! resource, then START, STOP and restart it, with every per-instance
//! placement derived from that resource's admitted identity and one host
//! profile. No per-instance configuration is written by hand.
//!
//! This module is a planner and dispatcher only. It keeps no operation
//! journal of its own: each lifecycle effect is performed by the existing
//! INSTALL (`install_service`), resident START (`resident_service`) and STOP
//! (`lifecycle_v3_stop_service`) custody, which own their one-shot markers and
//! exact recovery. Before dispatching, this module reads those retained
//! artifacts; an attempt they leave uncertain is reported and never retried.
//!
//! The only record written here that is not derivable from Mini is the
//! physical placement of the instance (its app UID), `placement.json`. The
//! root volume registration later records the same UID and is rechecked.

use crate::dispatch_native::{private_dir, PrivateOperator};
use crate::lifecycle_selector::{self, LifecycleSelector};
use crate::materialize::verify_installed_spk;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const MAX_JSON: u64 = 64 * 1024;
const MAX_SPK: u64 = 256 * 1024 * 1024;
const PACKAGE_STORE: &str = "/var/lib/minidregg/spk/packages";
const INBOX: &str = "/var/lib/minidregg/spk/inbox";
const VOLUME_REGISTRY: &str = "/etc/minidregg/spk/volumes";
const VOLUME_MOUNTS: &str = "/var/lib/minidregg/spk/vars";
const HOST_IDENTITY: &str = "/etc/minidregg/spk/host-identity";
const START_WAIT: Duration = Duration::from_secs(900);

/// Mini plan signing-slot order per lifecycle kind (role, index). Mini's plan
/// inspection remains decisive: a differing slot list refuses before signing.
const BEGIN_SLOTS: &[(&str, &str)] = &[("4", "0"), ("1", "0"), ("9", "0")];
const CLAIM_SLOTS: &[(&str, &str)] = &[("4", "0"), ("1", "0"), ("9", "0"), ("10", "0")];
const COMPLETION_SLOTS: &[(&str, &str)] = &[
    ("4", "0"),
    ("4", "1"),
    ("8", "0"),
    ("8", "1"),
    ("1", "0"),
    ("9", "0"),
];

fn invalid(reason: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason.into())
}

fn unresolved(reason: impl Into<String>) -> io::Error {
    io::Error::other(format!("UNRESOLVED: {}", reason.into()))
}

fn hex64(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn exists(path: &Path) -> io::Result<bool> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(true),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(error),
    }
}

/// Owner-private regular file, single link, bounded.
fn read_private(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let meta = file.metadata()?;
    if !path.is_absolute()
        || !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o777 != 0o600
        || meta.len() == 0
        || meta.len() > max
    {
        return Err(invalid(format!(
            "private file identity refused: {}",
            path.display()
        )));
    }
    let mut bytes = Vec::with_capacity(meta.len() as usize);
    Read::by_ref(&mut file).take(max + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != meta.len() {
        return Err(invalid("private file changed while reading"));
    }
    Ok(bytes)
}

fn read_json(path: &Path) -> io::Result<Value> {
    Ok(serde_json::from_slice(&read_private(path, MAX_JSON)?)?)
}

/// A derived file is written once; a later derivation must be byte-equal.
/// A difference means the admitted identity or host profile changed under an
/// existing instance, which is refused rather than silently rewritten.
fn derived_file(path: &Path, bytes: &[u8]) -> io::Result<()> {
    if exists(path)? {
        if read_private(path, MAX_JSON)? != bytes {
            return Err(invalid(format!(
                "derived file differs from retained instance record: {}",
                path.display()
            )));
        }
        return Ok(());
    }
    let parent = path.parent().ok_or_else(|| invalid("derived parent"))?;
    let temp = parent.join(format!(
        ".{}.tmp",
        path.file_name().and_then(|n| n.to_str()).unwrap_or("derived")
    ));
    let _ = fs::remove_file(&temp);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&temp)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    fs::rename(&temp, path)?;
    File::open(parent)?.sync_all()
}

fn private_directory(path: &Path) -> io::Result<()> {
    match DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => {
            if let Some(parent) = path.parent() {
                File::open(parent)?.sync_all()?;
            }
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(error),
    }
    private_dir(path)
}

fn file_sha256(path: &Path) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut digest = Sha256::new();
    let mut chunk = [0u8; 64 * 1024];
    loop {
        let count = file.read(&mut chunk)?;
        if count == 0 {
            break;
        }
        digest.update(&chunk[..count]);
    }
    Ok(format!("{:x}", digest.finalize()))
}

fn pinned_executable(path: &Path, sha: &str) -> io::Result<()> {
    let meta = fs::symlink_metadata(path)?;
    if !path.is_absolute()
        || !meta.is_file()
        || meta.uid() != 0
        || meta.permissions().mode() & 0o022 != 0
        || !hex64(sha)
        || file_sha256(path)? != sha
    {
        return Err(invalid(format!(
            "pinned executable refused: {}",
            path.display()
        )));
    }
    Ok(())
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct HostProfile {
    protocol: String,
    state_root: PathBuf,
    mini_host: PathBuf,
    mini_host_sha256: String,
    mini_config: PathBuf,
    mini_config_sha256: String,
    mini_operator_socket: PathBuf,
    management_subject: String,
    management_key_epoch: String,
    management_public_key_hex: String,
    management_seed: PathBuf,
    completion_custodian_seed: PathBuf,
    completion_semantics: String,
    bwrap: PathBuf,
    bwrap_sha256: String,
    spk_host: PathBuf,
    spk_host_sha256: String,
    ingest_helper: PathBuf,
    volume_helper: PathBuf,
    app_uids: Vec<u32>,
    volume_mib: u64,
}

struct HostIdentity {
    deployment_id: String,
    host_id: String,
}

struct Host {
    profile: HostProfile,
    identity: HostIdentity,
    management_key_id: String,
}

impl Host {
    fn load(path: &Path) -> io::Result<Self> {
        let profile: HostProfile = serde_json::from_slice(&read_private(path, MAX_JSON)?)?;
        if profile.protocol != "mini-spk-grain-host-v1"
            || path.parent() != Some(profile.state_root.as_path())
            || !lifecycle_selector::decimal(&profile.management_subject)
            || !lifecycle_selector::decimal(&profile.management_key_epoch)
            || !hex64(&profile.management_public_key_hex)
            || !lifecycle_selector::decimal(&profile.completion_semantics)
            || profile.app_uids.is_empty()
            || profile.app_uids.contains(&0)
            || !(64..=16384).contains(&profile.volume_mib)
            || ![
                &profile.state_root,
                &profile.mini_host,
                &profile.mini_config,
                &profile.mini_operator_socket,
                &profile.management_seed,
                &profile.completion_custodian_seed,
                &profile.bwrap,
                &profile.spk_host,
                &profile.ingest_helper,
                &profile.volume_helper,
            ]
            .iter()
            .all(|path| path.is_absolute())
        {
            return Err(invalid("grain host profile refused"));
        }
        private_dir(&profile.state_root)?;
        pinned_executable(&profile.bwrap, &profile.bwrap_sha256)?;
        pinned_executable(&profile.spk_host, &profile.spk_host_sha256)?;
        let identity = read_host_identity()?;
        let operator = operator_of(&profile);
        let (subject, key) = lifecycle_selector::pinned_management(&operator)?;
        if subject != profile.management_subject {
            return Err(invalid(
                "host profile management subject differs from Mini lifecycle pin",
            ));
        }
        Ok(Self {
            profile,
            identity,
            management_key_id: key,
        })
    }

    fn operator(&self) -> PrivateOperator {
        operator_of(&self.profile)
    }

    fn app_dir(&self, app: &str) -> PathBuf {
        self.profile.state_root.join("apps").join(app)
    }

    fn package_dir(&self, raw_sha256: &str) -> PathBuf {
        self.profile
            .state_root
            .join("packages")
            .join(format!("sha256-{raw_sha256}"))
    }
}

fn operator_of(profile: &HostProfile) -> PrivateOperator {
    PrivateOperator {
        host: profile.mini_host.clone(),
        config: profile.mini_config.clone(),
        socket: profile.mini_operator_socket.clone(),
        host_sha256: profile.mini_host_sha256.clone(),
        config_sha256: profile.mini_config_sha256.clone(),
    }
}

/// Root-published two-line host identity (see deploy/spk-host/README.md).
fn read_host_identity() -> io::Result<HostIdentity> {
    let meta = fs::symlink_metadata(HOST_IDENTITY)?;
    if !meta.is_file() || meta.uid() != 0 || meta.permissions().mode() & 0o777 != 0o600 {
        return Err(invalid("root host identity custody refused"));
    }
    let text = fs::read_to_string(HOST_IDENTITY)?;
    let lines: Vec<_> = text.lines().collect();
    match lines.as_slice() {
        [deployment, host] => {
            let deployment_id = deployment
                .strip_prefix("deployment_id=")
                .filter(|v| hex64(v))
                .ok_or_else(|| invalid("deployment identity malformed"))?;
            let host_id = host
                .strip_prefix("host_id=")
                .filter(|v| hex64(v))
                .ok_or_else(|| invalid("host identity malformed"))?;
            Ok(HostIdentity {
                deployment_id: deployment_id.into(),
                host_id: host_id.into(),
            })
        }
        _ => Err(invalid("root host identity shape refused")),
    }
}

/// The admitted application resource: an accepted current-application birth.
/// The selector confers nothing; Mini's lifecycle receivers check the app's
/// current law (naming these manifests and the management subject) and the
/// capabilities against current authority on every BEGIN, claim and completion.
fn admitted_application(source: &Path, receipt: &Path) -> io::Result<(LifecycleSelector, String)> {
    let source = read_json(source)?;
    let application = source
        .pointer("/applicationGrainBirth/applicationBirth/application")
        .ok_or_else(|| invalid("source is not a current-application birth"))?;
    let field = |name: &str| -> io::Result<String> {
        application
            .get(name)
            .and_then(Value::as_str)
            .filter(|v| lifecycle_selector::decimal(v))
            .map(str::to_owned)
            .ok_or_else(|| invalid(format!("application birth field {name} refused")))
    };
    let receipt = read_json(receipt)?;
    if receipt.get("type").and_then(Value::as_str) != Some("confirmed")
        || !matches!(
            receipt.get("confirmation").and_then(Value::as_str),
            Some("installed" | "replayed")
        )
    {
        return Err(invalid("application birth receipt is not confirmed"));
    }
    let selector = LifecycleSelector {
        app: field("app")?,
        package_manifest: field("packageManifest")?,
        snapshot_manifest: field("snapshotManifest")?,
        app_capability: field("appOwnerCapability")?,
        app_observe_capability: field("appOwnerCapability")?,
        package_capability: field("packageOwnerCapability")?,
        package_observe_capability: field("packageOwnerCapability")?,
    };
    selector.validate()?;
    Ok((selector, field("owner")?))
}

#[derive(Serialize, Deserialize, PartialEq, Eq, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Placement {
    protocol: String,
    pub(crate) selector: LifecycleSelector,
    pub(crate) raw_sha256: String,
    pub(crate) app_uid: u32,
    app_gid: u32,
    volume_resource: String,
    volume_mib: u64,
}

pub(crate) fn load_placement(path: &Path) -> io::Result<Placement> {
    let placement: Placement = serde_json::from_slice(&read_private(path, MAX_JSON)?)?;
    if placement.protocol != "mini-spk-grain-placement-v1" {
        return Err(invalid("grain placement protocol refused"));
    }
    placement.selector.validate()?;
    Ok(placement)
}

fn account_gid(uid: u32) -> io::Result<u32> {
    let entry = unsafe { libc::getpwuid(uid) };
    if entry.is_null() {
        return Err(invalid(format!("app UID {uid} has no account")));
    }
    let gid = unsafe { (*entry).pw_gid };
    if gid == 0 {
        return Err(invalid("app account primary group is root"));
    }
    Ok(gid)
}

/// UIDs already bound: other instances' placements and every root volume
/// registration. A root registration is a durable physical fact; it wins.
fn bound_uids(host: &Host, except_app: &str) -> io::Result<Vec<(u32, String)>> {
    let mut bound = Vec::new();
    let apps = host.profile.state_root.join("apps");
    if exists(&apps)? {
        for entry in fs::read_dir(&apps)? {
            let entry = entry?;
            let name = entry.file_name().to_string_lossy().into_owned();
            if name == except_app {
                continue;
            }
            let path = entry.path().join("placement.json");
            if exists(&path)? {
                bound.push((load_placement(&path)?.app_uid, name));
            }
        }
    }
    if exists(Path::new(VOLUME_REGISTRY))? {
        for entry in fs::read_dir(VOLUME_REGISTRY)? {
            let entry = entry?;
            let name = entry.file_name().to_string_lossy().into_owned();
            let Some(resource) = name.strip_suffix(".conf") else {
                continue;
            };
            if resource == except_app {
                continue;
            }
            let text = fs::read_to_string(entry.path())?;
            if let Some(uid) = text
                .lines()
                .find_map(|line| line.strip_prefix("app_uid="))
                .and_then(|v| v.parse::<u32>().ok())
            {
                bound.push((uid, resource.to_owned()));
            }
        }
    }
    Ok(bound)
}

fn place(host: &Host, selector: &LifecycleSelector, raw_sha256: &str) -> io::Result<Placement> {
    let app_dir = host.app_dir(&selector.app);
    private_directory(&host.profile.state_root.join("apps"))?;
    private_directory(&app_dir)?;
    let path = app_dir.join("placement.json");
    let bound = bound_uids(host, &selector.app)?;
    if exists(&path)? {
        let placement = load_placement(&path)?;
        if placement.selector != *selector || placement.raw_sha256 != raw_sha256 {
            return Err(invalid(
                "application already placed with a different package or selector",
            ));
        }
        if let Some((_, other)) = bound.iter().find(|(uid, _)| *uid == placement.app_uid) {
            return Err(invalid(format!(
                "placed app UID is also bound to resource {other}"
            )));
        }
        return Ok(placement);
    }
    let uid = host
        .profile
        .app_uids
        .iter()
        .copied()
        .find(|uid| !bound.iter().any(|(bound, _)| bound == uid))
        .ok_or_else(|| invalid("host app UID pool exhausted"))?;
    let placement = Placement {
        protocol: "mini-spk-grain-placement-v1".into(),
        selector: selector.clone(),
        raw_sha256: raw_sha256.into(),
        app_uid: uid,
        app_gid: account_gid(uid)?,
        volume_resource: selector.app.clone(),
        volume_mib: host.profile.volume_mib,
    };
    derived_file(&path, &serde_json::to_vec_pretty(&placement)?)?;
    Ok(placement)
}

/// Stage the signed SPK once per content hash and qualify its launch
/// descriptor through the pinned Host. Qualification is pure (no Store
/// effect), so an interrupted attempt is set aside and repeated.
fn stage_package(host: &Host, spk: &Path) -> io::Result<(String, PathBuf, PathBuf)> {
    let meta = fs::metadata(spk)?;
    if !meta.is_file() || meta.len() == 0 || meta.len() > MAX_SPK {
        return Err(invalid("signed SPK input refused"));
    }
    let raw_sha256 = file_sha256(spk)?;
    private_directory(&host.profile.state_root.join("packages"))?;
    let dir = host.package_dir(&raw_sha256);
    private_directory(&dir)?;
    let copy = dir.join("package.spk");
    if !exists(&copy)? {
        let temp = dir.join(".package.spk.tmp");
        let _ = fs::remove_file(&temp);
        fs::copy(spk, &temp)?;
        fs::set_permissions(&temp, fs::Permissions::from_mode(0o600))?;
        File::open(&temp)?.sync_all()?;
        fs::rename(&temp, &copy)?;
        File::open(&dir)?.sync_all()?;
    }
    if file_sha256(&copy)? != raw_sha256 {
        return Err(invalid("staged SPK copy differs from input hash"));
    }
    let attempt = dir.join("qualification");
    let result = attempt.join("qualification.json");
    if !exists(&result)? {
        if exists(&attempt)? {
            let mut random = [0u8; 8];
            File::open("/dev/urandom")?.read_exact(&mut random)?;
            let aside = dir.join(format!(
                "qualification-interrupted-{}",
                random.iter().map(|b| format!("{b:02x}")).collect::<String>()
            ));
            fs::rename(&attempt, aside)?;
        }
        let config = dir.join("qualify.json");
        let bytes = serde_json::to_vec(&json!({
            "protocol":"mini-spk-launch-qualification-v1",
            "sourceSpk":copy,
            "miniHost":host.profile.mini_host,
            "miniHostSha256":host.profile.mini_host_sha256,
            "miniConfig":host.profile.mini_config,
            "miniConfigSha256":host.profile.mini_config_sha256,
            "attemptDir":attempt,
        }))?;
        if exists(&config)? {
            fs::remove_file(&config)?;
        }
        derived_file(&config, &bytes)?;
        crate::launch_descriptor_native::qualify_launch(&config)?;
    }
    let qualified = read_json(&result)?;
    if qualified.get("protocol").and_then(Value::as_str) != Some("mini-spk-launch-qualified-v2")
        || qualified.get("rawSha256").and_then(Value::as_str) != Some(raw_sha256.as_str())
    {
        return Err(invalid("retained launch qualification differs"));
    }
    Ok((raw_sha256, copy, result))
}

fn custody(
    host: &Host,
    protocol: &str,
    selector: &LifecycleSelector,
    slots: &[(&str, &str)],
) -> io::Result<Vec<u8>> {
    let signers: Vec<Value> = slots
        .iter()
        .map(|(role, index)| {
            json!({"role":role,"index":index,"keyId":host.management_key_id,
                "keyEpoch":host.profile.management_key_epoch,
                "publicKeyHex":host.profile.management_public_key_hex,
                "seedPath":host.profile.management_seed})
        })
        .collect();
    Ok(serde_json::to_vec_pretty(&json!({
        "protocol":protocol,
        "selector":selector,
        "managementSubject":host.profile.management_subject,
        "signers":signers,
    }))?)
}

struct CustodyPaths {
    begin: PathBuf,
    claim: PathBuf,
    completion: PathBuf,
}

fn write_custody(host: &Host, selector: &LifecycleSelector) -> io::Result<CustodyPaths> {
    let dir = host.app_dir(&selector.app).join("custody");
    private_directory(&dir)?;
    let paths = CustodyPaths {
        begin: dir.join("begin.json"),
        claim: dir.join("claim.json"),
        completion: dir.join("completion.json"),
    };
    derived_file(
        &paths.begin,
        &custody(
            host,
            "mini-spk-resident-begin-management-v1",
            selector,
            BEGIN_SLOTS,
        )?,
    )?;
    derived_file(
        &paths.claim,
        &custody(
            host,
            "mini-spk-resident-claim-management-v1",
            selector,
            CLAIM_SLOTS,
        )?,
    )?;
    derived_file(
        &paths.completion,
        &custody(
            host,
            "mini-spk-completion-management-v1",
            selector,
            COMPLETION_SLOTS,
        )?,
    )?;
    Ok(paths)
}

fn image_dir(raw_sha256: &str) -> PathBuf {
    Path::new(PACKAGE_STORE).join(format!("sha256-{raw_sha256}"))
}

fn run_helper(program: &Path, args: &[&str]) -> io::Result<String> {
    let output = Command::new(program)
        .args(args)
        .stdin(Stdio::null())
        .output()?;
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    if !output.status.success() {
        return Err(io::Error::other(format!(
            "{} {} failed: {}{}",
            program.display(),
            args.join(" "),
            stdout,
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    Ok(stdout)
}

/// Root publishes one immutable image per signed-SPK hash, shared by every
/// instance of that package. The bounded ingest unit is the only writer.
fn ensure_image(host: &Host, placement: &Placement, staged: &Path) -> io::Result<()> {
    let image = image_dir(&placement.raw_sha256);
    if !exists(&image)? {
        let inbox = Path::new(INBOX).join(format!("grain-{}.spk", placement.raw_sha256));
        if !exists(&inbox)? {
            let temp = Path::new(INBOX).join(format!(".grain-{}.tmp", placement.raw_sha256));
            let _ = fs::remove_file(&temp);
            fs::copy(staged, &temp)?;
            fs::set_permissions(&temp, fs::Permissions::from_mode(0o600))?;
            File::open(&temp)?.sync_all()?;
            fs::rename(&temp, &inbox)?;
        }
        let uid = placement.app_uid.to_string();
        run_helper(
            &host.profile.ingest_helper,
            &[
                host.profile.spk_host.to_str().ok_or_else(|| invalid("path"))?,
                &host.profile.spk_host_sha256,
                inbox.to_str().ok_or_else(|| invalid("path"))?,
                &uid,
            ],
        )?;
    }
    let installed = verify_installed_spk(&image, placement.app_uid)?;
    if installed.raw_sha256 != placement.raw_sha256 {
        return Err(invalid("published image differs from placed package"));
    }
    Ok(())
}

fn registration(resource: &str) -> io::Result<Option<String>> {
    let path = Path::new(VOLUME_REGISTRY).join(format!("{resource}.conf"));
    if !exists(&path)? {
        return Ok(None);
    }
    Ok(Some(fs::read_to_string(path)?))
}

fn ensure_volume(host: &Host, placement: &Placement, volume_id: &str) -> io::Result<()> {
    if !hex64(volume_id) {
        return Err(invalid("source volume ID malformed"));
    }
    let uid = placement.app_uid.to_string();
    let mib = placement.volume_mib.to_string();
    let resource = &placement.volume_resource;
    match registration(resource)? {
        None => {
            run_helper(
                &host.profile.volume_helper,
                &["create", resource, &uid, &mib, volume_id],
            )?;
        }
        Some(text) => {
            let expected = [
                format!("app_uid={uid}"),
                format!("size_mib={mib}"),
                format!("volume_id={volume_id}"),
                format!("deployment_id={}", host.identity.deployment_id),
                format!("host_id={}", host.identity.host_id),
            ];
            if !expected.iter().all(|line| text.lines().any(|l| l == line)) {
                return Err(invalid(
                    "root volume registration differs from placement or Mini volume ID",
                ));
            }
            run_helper(&host.profile.volume_helper, &["verify", resource, &uid, &mib])?;
        }
    }
    Ok(())
}

const INSTALL_ATTEMPT_ARTIFACTS: &[&str] = &[
    "launch-descriptor",
    "lifecycle-begin-v3-active.json",
    "begin-v3",
    "claim-v3-author",
    "claim-v3",
    "lifecycle-claim-v3-active.json",
];

/// `spk-host grain install PROFILE APP_SOURCE.json APP_RECEIPT.json SIGNED.spk`
fn install(host: &Host, source: &Path, receipt: &Path, spk: &Path) -> io::Result<Value> {
    let (selector, owner) = admitted_application(source, receipt)?;
    if owner != host.profile.management_subject {
        return Err(invalid(
            "application owner is not this host's lifecycle management subject",
        ));
    }
    let (raw_sha256, staged, qualification) = stage_package(host, spk)?;
    let placement = place(host, &selector, &raw_sha256)?;
    let custody = write_custody(host, &selector)?;
    let journal = host.app_dir(&selector.app).join("install");
    private_directory(&journal)?;
    let config_path = journal.join("install.json");
    let config = json!({
        "protocol":"mini-spk-resident-install-v2",
        "journalDir":journal,
        "sourceSpk":staged,
        "imageDir":image_dir(&raw_sha256),
        "expectedRawSha256":raw_sha256,
        "appUid":placement.app_uid,
        "deploymentId":host.identity.deployment_id,
        "hostId":host.identity.host_id,
        "launchQualification":qualification,
        "miniHost":host.profile.mini_host,
        "miniHostSha256":host.profile.mini_host_sha256,
        "miniConfig":host.profile.mini_config,
        "miniConfigSha256":host.profile.mini_config_sha256,
        "miniOperatorSocket":host.profile.mini_operator_socket,
        "beginManagementCustody":custody.begin,
        "claimManagementCustody":custody.claim,
        "completionManagementCustody":custody.completion,
        "completionCustodianSeed":host.profile.completion_custodian_seed,
        "completionSemantics":host.profile.completion_semantics,
    });
    derived_file(&config_path, &serde_json::to_vec_pretty(&config)?)?;
    let prepared = journal.join("install-prepared-v2.json");
    if !exists(&prepared)? {
        for name in INSTALL_ATTEMPT_ARTIFACTS {
            if exists(&journal.join(name))? {
                return Err(unresolved(format!(
                    "INSTALL preparation attempt {name} exists without a prepared record in {}; \
                     its BEGIN/claim may be accepted, so it is not repeated",
                    journal.display()
                )));
            }
        }
        crate::install_service::prepare(&config_path)?;
    }
    ensure_image(host, &placement, &staged)?;
    if !exists(&journal.join("install-completed-v2.json"))? {
        crate::install_service::complete(&config_path)?;
    }
    let prepared = read_json(&prepared)?;
    let volume_id = prepared
        .pointer("/begin/volumeIdHex")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("prepared INSTALL lacks source volume ID"))?
        .to_owned();
    ensure_volume(host, &placement, &volume_id)?;
    let completed = read_json(&journal.join("install-completed-v2.json"))?;
    Ok(json!({
        "protocol":"mini-spk-grain-install-v1",
        "app":selector.app,
        "rawSha256":raw_sha256,
        "appUid":placement.app_uid,
        "volumeIdHex":volume_id,
        "installGeneration":prepared.pointer("/begin/processGeneration"),
        "completion":completed,
    }))
}

/// One resident generation directory `g<N>` holds START (and, later, its STOP).
#[derive(Debug, PartialEq, Eq)]
enum RunState {
    Running,
    Stopped,
    Uncertain(String),
}

struct Run {
    generation: u64,
    dir: PathBuf,
    state: RunState,
    create: bool,
    stop_generation: Option<u64>,
}

fn stop_completed(dir: &Path) -> io::Result<bool> {
    let mut current = dir.join("stop-completion");
    for _ in 0..8 {
        if !exists(&current)? {
            return Ok(false);
        }
        if exists(&current.join("receipt-anchor.json"))? {
            return Ok(true);
        }
        current = current.join("replan");
    }
    Ok(false)
}

fn decimal_u64(value: Option<&Value>) -> Option<u64> {
    value
        .and_then(Value::as_str)
        .filter(|v| lifecycle_selector::decimal(v))
        .and_then(|v| v.parse().ok())
}

fn scan_runs(app_dir: &Path) -> io::Result<Vec<Run>> {
    let mut runs = Vec::new();
    for entry in fs::read_dir(app_dir)? {
        let entry = entry?;
        let name = entry.file_name().to_string_lossy().into_owned();
        let Some(generation) = name
            .strip_prefix('g')
            .filter(|v| lifecycle_selector::decimal(v))
            .and_then(|v| v.parse::<u64>().ok())
        else {
            continue;
        };
        let dir = entry.path();
        let config = read_json(&dir.join("resident.json"))?;
        let create = config.pointer("/startAction/kind").and_then(Value::as_str) == Some("create");
        let admitted = dir.join("start-admitted-v3.json");
        let completed = dir.join("start-completed-v3.json");
        let stop_plan = dir.join("stop-begin").join("plan.json");
        let stop_generation = if exists(&stop_plan)? {
            decimal_u64(read_json(&stop_plan)?.get("processGeneration"))
        } else {
            None
        };
        let state = if exists(&completed)? {
            if stop_completed(&dir)? {
                RunState::Stopped
            } else if exists(&dir.join("stop.json"))? {
                RunState::Uncertain("STOP attempted without a completion receipt".into())
            } else {
                RunState::Running
            }
        } else if exists(&admitted)? || exists(&dir.join("begin-attempt"))? {
            RunState::Uncertain("START attempted without a completion record".into())
        } else {
            RunState::Uncertain("START configured but never admitted".into())
        };
        if let Some(admitted_generation) = if exists(&admitted)? {
            decimal_u64(read_json(&admitted)?.pointer("/begin/processGeneration"))
        } else {
            None
        } {
            if admitted_generation != generation {
                return Err(invalid(format!(
                    "resident journal g{generation} admitted generation {admitted_generation}"
                )));
            }
        }
        runs.push(Run {
            generation,
            dir,
            state,
            create,
            stop_generation,
        });
    }
    runs.sort_by_key(|run| run.generation);
    Ok(runs)
}

fn unit_active(unit: &str) -> io::Result<String> {
    let output = Command::new("/usr/bin/systemctl")
        .args(["--system", "show", unit, "--property=ActiveState", "--value"])
        .stdin(Stdio::null())
        .output()?;
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RouteRecord {
    protocol: String,
    display_name: String,
    preferred_handle: String,
}

/// Routes are entrance directories under `apps/<app>/routes/<name>/`, each a
/// custodian (`custodian.json`, owner-private tokens) plus the participant's
/// `dispatch-custody.json`. Every HTTP request is still admitted by Mini.
fn routes(app_dir: &Path, app: &str) -> io::Result<Vec<Value>> {
    let root = app_dir.join("routes");
    let mut routes = Vec::new();
    if !exists(&root)? {
        return Ok(routes);
    }
    let mut names: Vec<_> = fs::read_dir(&root)?
        .map(|entry| entry.map(|e| e.path()))
        .collect::<io::Result<_>>()?;
    names.sort();
    for dir in names {
        let record_path = dir.join("route.json");
        if !exists(&record_path)? || !exists(&dir.join("custodian.json"))? {
            continue;
        }
        let record: RouteRecord = serde_json::from_slice(&read_private(&record_path, MAX_JSON)?)?;
        if record.protocol != "mini-spk-grain-route-v1" {
            return Err(invalid("grain route protocol refused"));
        }
        let custody = dir.join("dispatch-custody.json");
        let fixed = read_json(&custody)?;
        if fixed.get("app").and_then(Value::as_str) != Some(app) {
            return Err(invalid("route dispatch custody names another application"));
        }
        routes.push(json!({"directory":dir,"dispatchCustody":custody,
            "displayName":record.display_name,"preferredHandle":record.preferred_handle}));
    }
    Ok(routes)
}

/// `spk-host grain start PROFILE APP`
fn start(host: &Host, app: &str) -> io::Result<Value> {
    let app_dir = host.app_dir(app);
    private_dir(&app_dir)?;
    let placement = load_placement(&app_dir.join("placement.json"))?;
    let install_dir = app_dir.join("install");
    let install_config = read_json(&install_dir.join("install.json"))?;
    let prepared = read_json(&install_dir.join("install-prepared-v2.json"))?;
    let _completed = read_json(&install_dir.join("install-completed-v2.json"))
        .map_err(|_| invalid("INSTALL is not complete for this application"))?;
    let volume_id = prepared
        .pointer("/begin/volumeIdHex")
        .and_then(Value::as_str)
        .filter(|v| hex64(v))
        .ok_or_else(|| invalid("prepared INSTALL lacks volume ID"))?
        .to_owned();
    let install_generation = decimal_u64(prepared.pointer("/begin/processGeneration"))
        .ok_or_else(|| invalid("prepared INSTALL lacks generation"))?;
    let runs = scan_runs(&app_dir)?;
    for run in &runs {
        match &run.state {
            RunState::Running => {
                let unit = format!("mini-spk-a{app}-g{}.service", run.generation);
                return Ok(json!({"protocol":"mini-spk-grain-start-v1","app":app,
                    "generation":run.generation.to_string(),"unit":unit,
                    "already":"running","activeState":unit_active(&unit)?}));
            }
            RunState::Uncertain(reason) => {
                return Err(unresolved(format!(
                    "{} is uncertain ({reason}); reconcile it before another START",
                    run.dir.display()
                )));
            }
            RunState::Stopped => {}
        }
    }
    let latest = runs
        .iter()
        .flat_map(|run| [Some(run.generation), run.stop_generation])
        .flatten()
        .chain([install_generation])
        .max()
        .unwrap_or(install_generation);
    if runs
        .iter()
        .any(|run| run.state == RunState::Stopped && run.stop_generation.is_none())
    {
        return Err(unresolved(
            "a stopped generation lacks its retained STOP BEGIN generation",
        ));
    }
    let generation = latest + 1;
    let start_action = match runs.iter().find(|run| run.create) {
        None => json!({"kind":"create","index":0}),
        Some(created) => {
            let completed = read_json(&created.dir.join("start-completed-v3.json"))?;
            let count = decimal_u64(completed.pointer("/completionReceipt/acceptedCount"))
                .filter(|count| *count > 0)
                .ok_or_else(|| invalid("prior create completion receipt malformed"))?;
            json!({"kind":"continue","createdIndex":(count - 1).to_string()})
        }
    };
    let entrances = routes(&app_dir, app)?;
    if entrances.is_empty() {
        return Err(invalid(
            "application has no route; `grain route` must bind at least one entrance",
        ));
    }
    run_helper(
        &host.profile.volume_helper,
        &["attest", &placement.volume_resource],
    )?;
    let unit = format!("mini-spk-a{app}-g{generation}.service");
    let journal = app_dir.join(format!("g{generation}"));
    private_directory(&journal)?;
    let config_path = journal.join("resident.json");
    let resident = json!({
        "protocol":"mini-spk-resident-start-v3",
        "journalDir":journal,
        "imageDir":install_config["imageDir"],
        "expectedRawSha256":placement.raw_sha256,
        "launchQualification":install_config["launchQualification"],
        "startAction":start_action,
        "volumeResource":placement.volume_resource.parse::<u64>()
            .map_err(|_| invalid("volume resource exceeds host range"))?,
        "expectedVolumeId":volume_id,
        "persistentVar":Path::new(VOLUME_MOUNTS).join(&placement.volume_resource),
        "persistentVarMaxBytes":placement.volume_mib * 1024 * 1024,
        "deploymentId":host.identity.deployment_id,
        "hostId":host.identity.host_id,
        "bwrap":host.profile.bwrap,
        "bwrapSha256":host.profile.bwrap_sha256,
        "appUid":placement.app_uid,
        "appGid":placement.app_gid,
        "unit":unit,
        "miniHost":host.profile.mini_host,
        "miniHostSha256":host.profile.mini_host_sha256,
        "miniConfig":host.profile.mini_config,
        "miniConfigSha256":host.profile.mini_config_sha256,
        "miniOperatorSocket":host.profile.mini_operator_socket,
        "beginManagementCustody":install_config["beginManagementCustody"],
        "claimManagementCustody":install_config["claimManagementCustody"],
        "beginOperationLedger":journal.join("begin-operation-ledger"),
        "claimNonceLedger":journal.join("claim-nonce-ledger"),
        "descriptorAttemptDir":journal.join("descriptor-attempt"),
        "beginAttemptDir":journal.join("begin-attempt"),
        "claimAuthorAttemptDir":journal.join("claim-author-attempt"),
        "claimAttemptDir":journal.join("claim-attempt"),
        "completionAttemptDir":journal.join("completion-attempt"),
        "completionSignAttemptDir":journal.join("completion-sign-attempt"),
        "completionSubmitAttemptDir":journal.join("completion-submit-attempt"),
        "completionCustodianSeed":host.profile.completion_custodian_seed,
        "completionManagementCustody":install_config["completionManagementCustody"],
        "completionSemantics":host.profile.completion_semantics,
        "entrances":entrances,
        "agents":[],
    });
    derived_file(&config_path, &serde_json::to_vec_pretty(&resident)?)?;
    // A failed earlier incarnation of this exact unit name may still be loaded.
    let _ = Command::new("/usr/bin/systemctl")
        .args(["--system", "reset-failed", &unit])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
    let started = Instant::now();
    let status = Command::new("/usr/bin/systemd-run")
        .args([
            "--system",
            &format!("--unit={unit}"),
            "--property=Type=exec",
            "--property=KillMode=control-group",
            "--property=MemoryMax=2G",
            "--property=TasksMax=512",
            "--property=NoNewPrivileges=yes",
            "--",
        ])
        .arg(&host.profile.spk_host)
        .arg("resident-run")
        .arg(&config_path)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()?;
    if !status.success() {
        return Err(io::Error::other(format!("systemd-run {unit} failed")));
    }
    let completed = journal.join("start-completed-v3.json");
    loop {
        let sockets_ready = entrances.iter().all(|route| {
            route
                .get("directory")
                .and_then(Value::as_str)
                .is_some_and(|dir| Path::new(dir).join("http.sock").exists())
        });
        if exists(&completed)? && sockets_ready {
            break;
        }
        let state = unit_active(&unit)?;
        if !matches!(state.as_str(), "active" | "activating") {
            return Err(io::Error::other(format!(
                "resident unit {unit} is {state} before START completion; see journalctl -u {unit}"
            )));
        }
        if started.elapsed() > START_WAIT {
            return Err(unresolved(format!(
                "resident unit {unit} still running without START completion after {}s",
                START_WAIT.as_secs()
            )));
        }
        std::thread::sleep(Duration::from_millis(500));
    }
    Ok(json!({
        "protocol":"mini-spk-grain-start-v1",
        "app":app,
        "generation":generation.to_string(),
        "unit":unit,
        "startAction":start_action,
        "elapsedMs":started.elapsed().as_millis().to_string(),
        "completion":read_json(&completed)?,
        "routes":entrances.iter().map(|route| route["directory"].clone()).collect::<Vec<_>>(),
    }))
}

/// `spk-host grain stop PROFILE APP` — dispatch the existing source-authorized
/// STOP for the one running generation. A rerun resumes STOP's own journal.
fn stop(host: &Host, app: &str) -> io::Result<Value> {
    let app_dir = host.app_dir(app);
    private_dir(&app_dir)?;
    let runs = scan_runs(&app_dir)?;
    let target = runs
        .iter()
        .rev()
        .find(|run| {
            matches!(run.state, RunState::Running)
                || matches!(&run.state, RunState::Uncertain(reason) if reason.starts_with("STOP"))
        })
        .ok_or_else(|| invalid("no running or stopping generation for this application"))?;
    let journal = &target.dir;
    let config_path = journal.join("stop.json");
    let config = json!({
        "protocol":"mini-spk-resident-stop-v3",
        "residentStartConfig":journal.join("resident.json"),
        "beginAttemptDir":journal.join("stop-begin"),
        "claimAuthorAttemptDir":journal.join("stop-claim-author"),
        "claimAttemptDir":journal.join("stop-claim"),
        "reportAttemptDir":journal.join("stop-report"),
        "completionAttemptDir":journal.join("stop-completion"),
    });
    derived_file(&config_path, &serde_json::to_vec_pretty(&config)?)?;
    let started = Instant::now();
    crate::lifecycle_v3_stop_service::run(&config_path)?;
    let unit = format!("mini-spk-a{app}-g{}.service", target.generation);
    Ok(json!({
        "protocol":"mini-spk-grain-stop-v1",
        "app":app,
        "generation":target.generation.to_string(),
        "unit":unit,
        "activeState":unit_active(&unit)?,
        "elapsedMs":started.elapsed().as_millis().to_string(),
    }))
}

fn status(host: &Host, app: &str) -> io::Result<Value> {
    let app_dir = host.app_dir(app);
    private_dir(&app_dir)?;
    let placement = load_placement(&app_dir.join("placement.json"))?;
    let install = app_dir.join("install");
    let runs = scan_runs(&app_dir)?;
    Ok(json!({
        "protocol":"mini-spk-grain-status-v1",
        "app":app,
        "rawSha256":placement.raw_sha256,
        "appUid":placement.app_uid,
        "installPrepared":exists(&install.join("install-prepared-v2.json"))?,
        "installCompleted":exists(&install.join("install-completed-v2.json"))?,
        "runs":runs.iter().map(|run| json!({
            "generation":run.generation.to_string(),
            "state":match &run.state {
                RunState::Running => "running".to_owned(),
                RunState::Stopped => "stopped".to_owned(),
                RunState::Uncertain(reason) => format!("uncertain: {reason}"),
            },
            "unitActiveState":unit_active(&format!("mini-spk-a{app}-g{}.service", run.generation))
                .unwrap_or_default(),
        })).collect::<Vec<_>>(),
    }))
}

pub fn usage() -> &'static str {
    "spk-host grain install PROFILE APP_SOURCE.json APP_RECEIPT.json SIGNED.spk | \
     grain route PROFILE APP ROUTE_REQUEST.json | grain start PROFILE APP | \
     grain stop PROFILE APP | grain status PROFILE APP"
}

pub fn run(args: &[String]) -> io::Result<Value> {
    match args {
        [verb, profile, rest @ ..] => {
            let host = Host::load(Path::new(profile))?;
            match (verb.as_str(), rest) {
                ("install", [source, receipt, spk]) => {
                    install(&host, Path::new(source), Path::new(receipt), Path::new(spk))
                }
                ("route", [app, request]) => {
                    crate::grain_route::route(&host_view(&host), app, Path::new(request))
                }
                ("start", [app]) => start(&host, app),
                ("stop", [app]) => stop(&host, app),
                ("status", [app]) => status(&host, app),
                _ => Err(invalid(usage())),
            }
        }
        _ => Err(invalid(usage())),
    }
}

/// The subset of the host a route derivation may read.
pub(crate) struct HostView<'a> {
    pub state_root: &'a Path,
    pub operator: PrivateOperator,
}

fn host_view(host: &Host) -> HostView<'_> {
    HostView {
        state_root: &host.profile.state_root,
        operator: host.operator(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn slot_tables_are_unique_role_index_pairs() {
        for table in [BEGIN_SLOTS, CLAIM_SLOTS, COMPLETION_SLOTS] {
            let mut seen = std::collections::BTreeSet::new();
            for pair in table {
                assert!(seen.insert(pair));
            }
        }
    }

    #[test]
    fn stop_completion_follows_bounded_replans() {
        let root = std::env::temp_dir().join(format!(
            "grain-stop-{}-{}",
            std::process::id(),
            Instant::now().elapsed().as_nanos()
        ));
        fs::create_dir_all(root.join("stop-completion/replan")).unwrap();
        assert!(!stop_completed(&root).unwrap());
        fs::write(root.join("stop-completion/replan/receipt-anchor.json"), b"{}").unwrap();
        assert!(stop_completed(&root).unwrap());
        fs::remove_dir_all(root).unwrap();
    }
}
