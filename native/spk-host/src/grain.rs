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
//! physical placement of the instance (its app UID and size class),
//! `placement.json`, a copy of what the root broker allocated.
//!
//! `grain` runs as the Store operator, never as root. Every root-only step
//! (app UID allocation, the per-app slice, image publication, the /var
//! volume, the resident unit, starting and stopping it) is one typed request
//! to `mini-spk-broker` (`crate::broker`).

use crate::broker::{self, Request};
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

#[path = "grain_profile_upgrade.rs"]
mod profile_upgrade;
#[path = "grain_management.rs"]
mod management;

const MAX_JSON: u64 = 64 * 1024;
const MAX_SPK: u64 = 256 * 1024 * 1024;
const PACKAGE_STORE: &str = "/var/lib/minidregg/spk/packages";
/// How long `grain start` waits for the resident's START completion before
/// reporting UNRESOLVED (the resident keeps going either way). Measured on
/// final (SPK-APPS 2026-10-01): a START is BEGIN, claim, launch, report,
/// sign, op70 and op38, several of which replay the Store's history in the
/// Host; 245-626 s at load 20-45, and op38 alone 6.5 min at load 45. At
/// 900 s the operator gave up on STARTs that then completed, and a harness
/// that stopped the Store services on that verdict wedged them. 30 minutes
/// until the Host's replay is fixed (task HOST-KECCAK).
const START_WAIT: Duration = Duration::from_secs(1800);

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

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct HostProfile {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    genesis_config_sha256: Option<String>,
    #[serde(default)]
    ws_authority_lease_seconds: Option<u64>,
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
    grains_root: PathBuf,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    broker_socket: Option<PathBuf>,
    bwrap: PathBuf,
    bwrap_sha256: String,
    spk_host: PathBuf,
    spk_host_sha256: String,
}

struct HostIdentity {
    deployment_id: String,
    host_id: String,
}

struct Host {
    profile: HostProfile,
    identity: HostIdentity,
    management_key_id: String,
    /// The Store key: Mini's `storeTag` of the deployment's genesis seed
    /// identity, read from the pinned Host's profile at every load. Resident
    /// unit, volume, mount, witness and slice names and the state root carry it.
    store: String,
    // Serializes profile selection with grain lifecycle operations.
    _profile_lock: File,
}

impl Host {
    fn load(path: &Path) -> io::Result<Self> {
        if unsafe { libc::geteuid() } == 0 {
            return Err(invalid(
                "grain runs as the Store operator; root steps go through mini-spk-broker",
            ));
        }
        let profile: HostProfile = serde_json::from_slice(&read_private(path, MAX_JSON)?)?;
        if let Some(seconds) = profile.ws_authority_lease_seconds {
            crate::web_socket::StreamLease::begin(Duration::from_secs(seconds))?;
        }
        let profile_lock = profile_upgrade::lock(&profile.state_root, false)?;
        profile_upgrade::validate_selected(path, &profile)?;
        let genesis = profile
            .genesis_config_sha256
            .as_ref()
            .unwrap_or(&profile.mini_config_sha256);
        if profile.protocol != "mini-spk-grain-host-v2"
            || !hex64(genesis)
            || !lifecycle_selector::decimal(&profile.management_subject)
            || !lifecycle_selector::decimal(&profile.management_key_epoch)
            || !hex64(&profile.management_public_key_hex)
            || !lifecycle_selector::decimal(&profile.completion_semantics)
            || ![
                &profile.state_root,
                &profile.mini_host,
                &profile.mini_config,
                &profile.mini_operator_socket,
                &profile.management_seed,
                &profile.completion_custodian_seed,
                &profile.bwrap,
                &profile.spk_host,
                &profile.grains_root,
            ]
            .iter()
            .all(|path| path.is_absolute())
        {
            return Err(invalid("grain host profile refused"));
        }
        private_dir(&profile.state_root)?;
        pinned_executable(&profile.bwrap, &profile.bwrap_sha256)?;
        pinned_executable(&profile.spk_host, &profile.spk_host_sha256)?;
        let identity = read_host_identity(&profile.state_root)?;
        let operator = operator_of(&profile);
        let store = operator.store_tag(&profile.state_root)?;
        if profile.state_root != profile.grains_root.join(&store).join("host") {
            return Err(invalid(
                "grain host profile state root is not this Mini Store's (storeTag)",
            ));
        }
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
            store,
            _profile_lock: profile_lock,
        })
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

/// The root host identity (`/etc/minidregg/spk/host-identity`, root 0600) as
/// the broker reported it at `init-store`. The operator keeps a copy only to
/// pin what the root volume witness must carry; a wrong copy refuses START.
fn read_host_identity(state_root: &Path) -> io::Result<HostIdentity> {
    let value = read_json(&state_root.join("host-identity.json"))?;
    let field = |name: &str| -> io::Result<String> {
        value
            .get(name)
            .and_then(Value::as_str)
            .filter(|v| hex64(v))
            .map(str::to_owned)
            .ok_or_else(|| invalid(format!("host identity {name} malformed")))
    };
    Ok(HostIdentity {
        deployment_id: field("deploymentId")?,
        host_id: field("hostId")?,
    })
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
    /// Retained physical package namespace selected by the root broker.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) image_dir: Option<PathBuf>,
    pub(crate) app_uid: u32,
    app_gid: u32,
    volume_resource: String,
    volume_mib: u64,
    class: String,
}

pub(crate) fn load_placement(path: &Path) -> io::Result<Placement> {
    let placement: Placement = serde_json::from_slice(&read_private(path, MAX_JSON)?)?;
    if placement.protocol != "mini-spk-grain-placement-v2" {
        return Err(invalid("grain placement protocol refused"));
    }
    placement.selector.validate()?;
    Ok(placement)
}

fn reply_u32(reply: &Value, name: &str) -> io::Result<u32> {
    reply
        .get(name)
        .and_then(Value::as_u64)
        .and_then(|v| u32::try_from(v).ok())
        .filter(|v| *v != 0)
        .ok_or_else(|| invalid(format!("broker reply lacks {name}")))
}

/// The broker allocates the app UID from its own pool (the operator never
/// chooses a UID) and renders the app's slice for its size class.
fn place(
    host: &Host,
    selector: &LifecycleSelector,
    raw_sha256: &str,
    class: &str,
) -> io::Result<Placement> {
    let app_dir = host.app_dir(&selector.app);
    private_directory(&host.profile.state_root.join("apps"))?;
    private_directory(&app_dir)?;
    let path = app_dir.join("placement.json");
    if exists(&path)? {
        let placement = load_placement(&path)?;
        if placement.selector != *selector
            || placement.raw_sha256 != raw_sha256
            || placement.class != class
        {
            return Err(invalid(
                "application already placed with a different package, selector or class",
            ));
        }
        return Ok(placement);
    }
    let placed = broker::call_at(&host.profile.grains_root, host.profile.broker_socket.as_deref(), &Request::Place {
        store: host.store.clone(),
        app: selector.app.clone(),
    })?;
    let cgroup = broker::call_at(&host.profile.grains_root, host.profile.broker_socket.as_deref(), &Request::SetCgroup {
        store: host.store.clone(),
        app: selector.app.clone(),
        class: class.to_owned(),
    })?;
    let placement = Placement {
        protocol: "mini-spk-grain-placement-v2".into(),
        selector: selector.clone(),
        raw_sha256: raw_sha256.into(),
        image_dir: Some(broker::package_image_at(&host.profile.grains_root,host.profile.broker_socket.as_deref(),raw_sha256)?),
        app_uid: reply_u32(&placed, "appUid")?,
        app_gid: reply_u32(&placed, "appGid")?,
        volume_resource: selector.app.clone(),
        volume_mib: cgroup
            .get("volumeMib")
            .and_then(Value::as_u64)
            .ok_or_else(|| invalid("broker reply lacks volumeMib"))?,
        class: class.to_owned(),
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

pub(crate) fn placement_image_dir(placement: &Placement) -> io::Result<PathBuf> {
    let image=placement.image_dir.clone().unwrap_or_else(||Path::new(PACKAGE_STORE).join(format!("sha256-{}",placement.raw_sha256)));
    let parent=image.parent().and_then(Path::to_str).ok_or_else(||invalid("placement image namespace malformed"))?;
    let identity=json!({"protocol":"mini-spk-broker-identity-v1","packageStore":parent});
    if image!=broker::image_path_from_identity(&identity,&placement.raw_sha256)? {
        return Err(invalid("placement image path differs from its exact package hash"));
    }
    Ok(image)
}

/// Root publishes one immutable image per signed-SPK hash, shared by every
/// instance of that package; the broker runs the bounded ingest unit.
fn ensure_image(host: &Host, placement: &Placement) -> io::Result<()> {
    let image = placement_image_dir(placement)?;
    if !exists(&image)? {
        let reply=broker::call_at(&host.profile.grains_root, host.profile.broker_socket.as_deref(), &Request::Ingest {
            store: host.store.clone(),
            app: placement.selector.app.clone(),
            sha256: placement.raw_sha256.clone(),
        })?;
        if reply.get("imageDir").and_then(Value::as_str)!=image.to_str() {
            return Err(invalid("broker ingest image differs from retained placement namespace"));
        }
    }
    let installed = verify_installed_spk(&image, placement.app_uid)?;
    if installed.raw_sha256 != placement.raw_sha256 {
        return Err(invalid("published image differs from placed package"));
    }
    Ok(())
}

/// Create (once) and attest the Store-keyed /var volume. A fresh witness is
/// published on every call; START and STOP each consume one.
fn mount_volume(
    host: &Host,
    placement: &Placement,
    volume_id: &str,
    import_sha256: Option<String>,
) -> io::Result<Value> {
    if !hex64(volume_id) {
        return Err(invalid("source volume ID malformed"));
    }
    let reply = broker::call_at(&host.profile.grains_root, host.profile.broker_socket.as_deref(), &Request::MountVolume {
        store: host.store.clone(),
        app: placement.selector.app.clone(),
        volume_id: volume_id.to_owned(),
        import_sha256,
    })?;
    if reply_u32(&reply, "appUid")? != placement.app_uid
        || reply.get("sizeMib").and_then(Value::as_u64) != Some(placement.volume_mib)
    {
        return Err(invalid("broker volume differs from placement"));
    }
    Ok(reply)
}

fn persistent_var(host: &Host, placement: &Placement) -> PathBuf {
    host.profile
        .grains_root
        .join("vars")
        .join(broker::volume_name(&host.store, &placement.volume_resource))
}

const INSTALL_ATTEMPT_ARTIFACTS: &[&str] = &[
    "launch-descriptor",
    "lifecycle-begin-v3-active.json",
    "begin-v3",
    "claim-v3-author",
    "claim-v3",
    "lifecycle-claim-v3-active.json",
];

/// `spk-host grain install PROFILE APP_SOURCE.json APP_RECEIPT.json SIGNED.spk
/// [--class S|M|L] [--import EXPORT_DIR --exporter-key HEX]`
fn install(
    host: &Host,
    source: &Path,
    receipt: &Path,
    spk: &Path,
    class: &str,
    import: Option<(&Path, &str)>,
    management_selector: Option<&Path>,
) -> io::Result<Value> {
    let (admitted, owner) = admitted_application(source, receipt)?;
    let delegation = management_selector
        .map(|path| read_private(path, MAX_JSON))
        .transpose()?;
    let selector = match &delegation {
        Some(bytes) => management::select(bytes, &admitted, &owner, &host.profile.management_subject)?,
        None if owner == host.profile.management_subject => admitted,
        None => return Err(invalid("member-owned app requires an explicit lifecycle delegation selector")),
    };
    broker::class(class)?;
    let (raw_sha256, staged, qualification) = stage_package(host, spk)?;
    // An import is checked completely before any Mini effect: the exporter's
    // signature, the image bytes, the package and the class all bind.
    let imported = match import {
        None => None,
        Some((dir, key)) => Some(crate::grain_export::verify_import(
            dir,
            key,
            &raw_sha256,
            class,
            &host.profile.grains_root.join(&host.store).join("imports"),
        )?),
    };
    let placement = place(host, &selector, &raw_sha256, class)?;
    if let Some(bytes) = &delegation {
        derived_file(&host.app_dir(&selector.app).join("lifecycle-delegation.json"), bytes)?;
    }
    if let Some(imported) = &imported {
        derived_file(
            &host.app_dir(&selector.app).join("import.json"),
            &serde_json::to_vec_pretty(&imported.record)?,
        )?;
    }
    let custody = write_custody(host, &selector)?;
    let journal = host.app_dir(&selector.app).join("install");
    private_directory(&journal)?;
    let config_path = journal.join("install.json");
    let config = json!({
        "protocol":"mini-spk-resident-install-v2",
        "journalDir":journal,
        "sourceSpk":staged,
        "imageDir":placement_image_dir(&placement)?,
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
    let _ = &staged;
    ensure_image(host, &placement)?;
    if !exists(&journal.join("install-completed-v2.json"))? {
        crate::install_service::complete(&config_path)?;
    }
    let prepared = read_json(&prepared)?;
    let volume_id = prepared
        .pointer("/begin/volumeIdHex")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("prepared INSTALL lacks source volume ID"))?
        .to_owned();
    mount_volume(
        host,
        &placement,
        &volume_id,
        imported.as_ref().map(|i| i.image_sha256.clone()),
    )?;
    let completed = read_json(&journal.join("install-completed-v2.json"))?;
    Ok(json!({
        "protocol":"mini-spk-grain-install-v2",
        "app":selector.app,
        "store":host.store,
        "class":placement.class,
        "imported":imported.as_ref().map(|i| i.record.clone()),
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
    /// Configured, but no BEGIN was ever requested: nothing reached Mini, so
    /// the same generation may be started again.
    NeverBegun,
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
    Ok(stop_receipt(dir)?.is_some())
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
        let stop_plan = dir.join("stop-begin").join("stop-plan-v2.json");
        let recovered_path=dir.join("failed-start-recovered-v1.json");
        let recovered_generation=if exists(&recovered_path)? {
            let recovered:Value=serde_json::from_slice(&read_private(&recovered_path,MAX_JSON)?)?;
            let expected=generation.checked_add(1).ok_or_else(||invalid("recovered generation overflow"))?;
            if recovered.get("protocol").and_then(Value::as_str)!=Some("mini-spk-failed-start-recovered-v1")
                || decimal_u64(recovered.get("generation"))!=Some(generation)
                || decimal_u64(recovered.get("reconciledGeneration"))!=Some(expected)
                || recovered.get("app").and_then(Value::as_str)!=app_dir.file_name().and_then(|n|n.to_str())
                || recovered.pointer("/outcome/type").and_then(Value::as_str)!=Some("confirmed") {
                return Err(invalid("failed START recovery receipt identity refused"));
            }
            Some(expected)
        } else {None};
        let stop_generation = if recovered_generation.is_some() { recovered_generation }
        else if exists(&stop_plan)? {
            decimal_u64(read_json(&stop_plan)?.pointer("/basePlan/processGeneration"))
        } else {
            None
        };
        let state = if recovered_generation.is_some() { RunState::Stopped }
        else if exists(&completed)? {
            if stop_completed(&dir)? {
                RunState::Stopped
            } else if exists(&dir.join("stop.json"))? {
                RunState::Uncertain("STOP attempted without a completion receipt".into())
            } else {
                RunState::Running
            }
        } else if exists(&admitted)?
            || exists(&dir.join("begin-attempt"))?
            || exists(&dir.join("lifecycle-begin-v3-active.json"))?
        {
            RunState::Uncertain("START attempted without a completion record".into())
        } else {
            RunState::NeverBegun
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
            create: create && recovered_generation.is_none(),
            stop_generation,
        });
    }
    runs.sort_by_key(|run| run.generation);
    Ok(runs)
}

fn unit_property(unit: &str, property: &str) -> io::Result<String> {
    let output = Command::new("/usr/bin/systemctl")
        .args(["--system", "show", unit, &format!("--property={property}"), "--value"])
        .stdin(Stdio::null())
        .output()?;
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn unit_active(unit: &str) -> io::Result<String> {
    unit_property(unit, "ActiveState")
}

/// The resident unit is rendered by the broker from its own template (the
/// operator passes only store, app and generation) as a loaded runtime unit:
/// STOP audits a loaded, inactive unit with no invocation and an empty exact
/// cgroup. It runs as the operator under the app's class slice, and its
/// failure starts the app's supervisor. Re-installing the same generation is
/// idempotent.
fn install_unit(host: &Host, app: &str, generation: u64) -> io::Result<String> {
    let reply = broker::call_at(&host.profile.grains_root, host.profile.broker_socket.as_deref(), &Request::InstallUnit {
        store: host.store.clone(),
        app: app.to_owned(),
        generation: generation.to_string(),
        runtime_sha256: Some(host.profile.spk_host_sha256.clone()),
    })?;
    let unit = broker::resident_unit(&host.store, app, &generation.to_string());
    if reply.get("unit").and_then(Value::as_str) != Some(unit.as_str()) {
        return Err(invalid("broker installed a different unit"));
    }
    Ok(unit)
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
    profile_upgrade::require_ready_runtime(&host.profile)?;
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
                let unit = broker::resident_unit(&host.store, app, &run.generation.to_string());
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
            RunState::Stopped | RunState::NeverBegun => {}
        }
    }
    if runs
        .iter()
        .any(|run| run.state == RunState::Stopped && run.stop_generation.is_none())
    {
        return Err(unresolved(
            "a stopped generation lacks its retained STOP BEGIN generation",
        ));
    }
    // A never-begun generation is reused; its descriptor authoring was pure
    // (no Store effect) and is set aside so the resident starts fresh.
    let reuse = runs
        .iter()
        .find(|run| run.state == RunState::NeverBegun)
        .map(|run| run.generation);
    if let Some(generation) = reuse {
        let dir = app_dir.join(format!("g{generation}"));
        let descriptor = dir.join("descriptor-attempt");
        if exists(&descriptor)? {
            let mut random = [0u8; 8];
            File::open("/dev/urandom")?.read_exact(&mut random)?;
            fs::rename(
                &descriptor,
                dir.join(format!(
                    "descriptor-attempt-never-begun-{}",
                    random.iter().map(|b| format!("{b:02x}")).collect::<String>()
                )),
            )?;
            File::open(&dir)?.sync_all()?;
        }
    }
    let latest = runs
        .iter()
        .filter(|run| run.state != RunState::NeverBegun)
        .flat_map(|run| [Some(run.generation), run.stop_generation])
        .flatten()
        .chain([install_generation])
        .max()
        .unwrap_or(install_generation);
    let generation = reuse.unwrap_or(latest + 1);
    let start_action = match runs
        .iter()
        .find(|run| run.create && run.state != RunState::NeverBegun)
    {
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
    mount_volume(host, &placement, &volume_id, None)?;
    let unit = broker::resident_unit(&host.store, app, &generation.to_string());
    let journal = app_dir.join(format!("g{generation}"));
    private_directory(&journal)?;
    let config_path = journal.join("resident.json");
    let mut resident = json!({
        "protocol":"mini-spk-resident-start-v3",
        "journalDir":journal,
        "imageDir":install_config["imageDir"],
        "expectedRawSha256":placement.raw_sha256,
        "launchQualification":install_config["launchQualification"],
        "startAction":start_action,
        "volumeResource":placement.volume_resource.parse::<u64>()
            .map_err(|_| invalid("volume resource exceeds host range"))?,
        "expectedVolumeId":volume_id,
        "persistentVar":persistent_var(host, &placement),
        "persistentVarMaxBytes":placement.volume_mib * 1024 * 1024,
        "sizeClass":placement.class,
        "grainsRoot":host.profile.grains_root,
        "store":host.store,
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
    resident["brokerSocket"] = json!(broker::socket_path(&host.profile.grains_root, host.profile.broker_socket.as_deref())?);
    if let Some(seconds) = host.profile.ws_authority_lease_seconds {
        resident["wsAuthorityLeaseSeconds"] = json!(seconds);
    }

    derived_file(&config_path, &serde_json::to_vec_pretty(&resident)?)?;
    install_unit(host, app, generation)?;
    let started = Instant::now();
    if let Err(error) = broker::call_at(&host.profile.grains_root, host.profile.broker_socket.as_deref(), &Request::Start { unit: unit.clone() }) {
        if !matches!(unit_active(&unit)?.as_str(), "failed" | "inactive") {
            return Err(error);
        }
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
    let unit = install_unit(host, app, target.generation)?;
    // STOP consumes a fresh root volume witness, like START.
    let placement = load_placement(&app_dir.join("placement.json"))?;
    let prepared = read_json(&app_dir.join("install").join("install-prepared-v2.json"))?;
    let volume_id = prepared
        .pointer("/begin/volumeIdHex")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("prepared INSTALL lacks volume ID"))?
        .to_owned();
    mount_volume(host, &placement, &volume_id, None)?;
    let started = Instant::now();
    crate::lifecycle_v3_stop_service::run(&config_path)?;
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
        "protocol":"mini-spk-grain-status-v2",
        "app":app,
        "store":host.store,
        "class":placement.class,
        "rawSha256":placement.raw_sha256,
        "appUid":placement.app_uid,
        "installPrepared":exists(&install.join("install-prepared-v2.json"))?,
        "installCompleted":exists(&install.join("install-completed-v2.json"))?,
        "runs":runs.iter().map(|run| json!({
            "generation":run.generation.to_string(),
            "state":match &run.state {
                RunState::NeverBegun => "never-begun".to_owned(),
                RunState::Running => "running".to_owned(),
                RunState::Stopped => "stopped".to_owned(),
                RunState::Uncertain(reason) => format!("uncertain: {reason}"),
            },
            "unit":broker::resident_unit(&host.store, app, &run.generation.to_string()),
            "unitActiveState":unit_active(&broker::resident_unit(&host.store, app, &run.generation.to_string()))
                .unwrap_or_default(),
            "slice":unit_property(&broker::resident_unit(&host.store, app, &run.generation.to_string()), "Slice")
                .unwrap_or_default(),
        })).collect::<Vec<_>>(),
    }))
}

/// `spk-host grain supervise PROFILE APP`, started by the failed resident
/// unit's `OnFailure=` (as the operator, via the broker-rendered supervisor
/// template). A generation is never relaunched in place: the crashed one is
/// STOPped through Mini (the exact-unit audit proves the dead incarnation) and
/// a continue-START of the next generation follows. An uncertain record is
/// reported and never retried (exit 3; the template does not restart on it).
fn supervise(host: &Host, app: &str) -> io::Result<Value> {
    let app_dir = host.app_dir(app);
    private_dir(&app_dir)?;
    let runs = scan_runs(&app_dir)?;
    let Some(latest) = runs.iter().rev().find(|run| run.state != RunState::NeverBegun) else {
        return Ok(json!({"protocol":"mini-spk-grain-supervise-v1","app":app,"action":"none",
            "reason":"never started"}));
    };
    let unit = broker::resident_unit(&host.store, app, &latest.generation.to_string());
    match &latest.state {
        RunState::Stopped => Ok(json!({"protocol":"mini-spk-grain-supervise-v1","app":app,
            "action":"none","reason":"stopped by a completed STOP"})),
        RunState::Uncertain(reason) if reason.starts_with("START") => {
            // A START that failed after its claim (phase 9) leaves the app
            // wedged until Mini's `reconcileFailedStart` (9 -> 2) is admitted.
            crate::grain_export::reconcile_failed_start(
                &operator_of(&host.profile), &latest.dir.join("resident.json"),
                app, latest.generation, crate::grain_export::FAILED_START_RECOVERY_ROUTES,
            )
        }
        // A STOP this supervisor (or the operator) began resumes from STOP's
        // own journal: exact recovery, never a second claim.
        RunState::Uncertain(reason) if reason.starts_with("STOP") => {
            let stopped = stop(host, app)?;
            let started = start(host, app)?;
            Ok(json!({"protocol":"mini-spk-grain-supervise-v1","app":app,
                "action":"resume-stop-and-continue","stop":stopped,"start":started}))
        }
        RunState::Uncertain(reason) => Err(unresolved(format!(
            "{} is uncertain ({reason}); the supervisor does not retry it",
            latest.dir.display()
        ))),
        RunState::NeverBegun => unreachable!("filtered above"),
        RunState::Running => {
            let state = unit_active(&unit)?;
            if matches!(state.as_str(), "active" | "activating" | "reloading") {
                return Ok(json!({"protocol":"mini-spk-grain-supervise-v1","app":app,
                    "action":"none","reason":format!("{unit} is {state}")}));
            }
            let crashed_at = Instant::now();
            let stopped = stop(host, app)?;
            let started = start(host, app)?;
            Ok(json!({"protocol":"mini-spk-grain-supervise-v1","app":app,
                "action":"stop-and-continue","crashed":{"unit":unit,"activeState":state,
                    "generation":latest.generation.to_string()},
                "stop":stopped,"start":started,
                "elapsedMs":crashed_at.elapsed().as_millis().to_string()}))
        }
    }
}

/// `spk-host grain export PROFILE APP OUT_DIR`: the stopped volume's bytes
/// bound to the STOP receipt that fenced them, signed by this Store's
/// completion custodian.
fn export(host: &Host, app: &str, out: &Path) -> io::Result<Value> {
    let app_dir = host.app_dir(app);
    private_dir(&app_dir)?;
    let placement = load_placement(&app_dir.join("placement.json"))?;
    let runs = scan_runs(&app_dir)?;
    let latest = runs
        .iter()
        .rev()
        .find(|run| run.state != RunState::NeverBegun)
        .ok_or_else(|| invalid("export refused: never started"))?;
    if latest.state != RunState::Stopped {
        return Err(invalid(format!(
            "export refused: generation {} is not stopped by a completed STOP",
            latest.generation
        )));
    }
    let receipt = stop_receipt(&latest.dir)?
        .ok_or_else(|| invalid("export refused: STOP receipt absent"))?;
    let prepared = read_json(&app_dir.join("install").join("install-prepared-v2.json"))?;
    let volume_id = prepared
        .pointer("/begin/volumeIdHex")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("prepared INSTALL lacks volume ID"))?
        .to_owned();
    let copied = broker::call_at(&host.profile.grains_root, host.profile.broker_socket.as_deref(), &Request::ExportVolume {
        store: host.store.clone(),
        app: app.to_owned(),
    })?;
    crate::grain_export::write_export(
        out,
        &copied,
        &json!({
            "store":host.store,
            "app":app,
            "volumeIdHex":volume_id,
            "packageRawSha256":placement.raw_sha256,
            "class":placement.class,
            "volumeMib":placement.volume_mib,
            "stopGeneration":latest.generation.to_string(),
        }),
        &fs::read(&receipt)?,
        &host.profile.completion_custodian_seed,
    )
}

/// The STOP completion's retained receipt (following bounded replans).
fn stop_receipt(dir: &Path) -> io::Result<Option<PathBuf>> {
    let mut current = dir.join("stop-completion");
    for _ in 0..8 {
        if !exists(&current)? {
            return Ok(None);
        }
        let receipt = current.join("receipt-anchor.json");
        if exists(&receipt)? {
            return Ok(Some(receipt));
        }
        current = current.join("replan");
    }
    Ok(None)
}

pub fn usage() -> &'static str {
    "spk-host grain install PROFILE APP_SOURCE.json APP_RECEIPT.json SIGNED.spk \
     [--class S|M|L] [--import EXPORT_DIR --exporter-key HEX] [--management-selector PATH] | \
     grain route PROFILE APP ROUTE_REQUEST.json | grain start PROFILE APP | \
     grain stop PROFILE APP | grain status PROFILE APP | grain supervise PROFILE APP | \
     grain supervise-instance GRAINS_ROOT STORE-APP | grain export PROFILE APP OUT_DIR | \
     grain init-store GRAINS_ROOT MINI_HOST MINI_CONFIG [--broker-socket PATH] | grain backup PROFILE | \
     grain rebind-profile OLD_PROFILE ADMISSION | grain session-intents PROFILE APP | \
     grain register-route --socket PATH --request PATH | \
     grain current-profile BASELINE | grain runtime-status PROFILE | grain adopt-runtime PROFILE ADMISSION"
}

struct InstallOptions {
    class: String,
    import: Option<(PathBuf, String)>,
    management_selector: Option<PathBuf>,
}
fn install_options(rest: &[String]) -> io::Result<InstallOptions> {
    let mut class = "S".to_owned();
    let mut import = None;
    let mut key = None;
    let mut management_selector = None;
    let mut index = 0;
    while index < rest.len() {
        match (rest[index].as_str(), rest.get(index + 1)) {
            ("--class", Some(value)) => class = value.clone(),
            ("--import", Some(value)) => import = Some(PathBuf::from(value)),
            ("--exporter-key", Some(value)) => key = Some(value.clone()),
            ("--management-selector", Some(value)) if management_selector.is_none() => {
                let path = PathBuf::from(value);
                if !path.is_absolute() { return Err(invalid("management selector path must be absolute")); }
                management_selector = Some(path);
            }
            _ => return Err(invalid(usage())),
        }
        index += 2;
    }
    let import = match (import, key) {
        (None, None) => None,
        (Some(dir), Some(key)) => Some((dir, key)),
        _ => return Err(invalid("--import and --exporter-key go together")),
    };
    Ok(InstallOptions { class, import, management_selector })
}

/// `spk-host grain init-store GRAINS_ROOT MINI_HOST MINI_CONFIG`: the broker
/// creates this Store's operator-owned state directory under the grains root,
/// named by the Store key MINI_HOST reports for MINI_CONFIG (`storeTag`). The
/// profile later pins that Host; every load re-reads the key from it.
fn init_store(root: &Path, host: &Path, config: &Path, socket: Option<&Path>) -> io::Result<Value> {
    let output = Command::new(host)
        .arg(config)
        .arg("profile")
        .stdin(Stdio::null())
        .stderr(Stdio::null())
        .output()?;
    if !output.status.success() || output.stdout.len() > 64 * 1024 {
        return Err(invalid("Mini Host refused to describe the Store's profile"));
    }
    let profile: Value = serde_json::from_slice(&output.stdout)?;
    let store = profile
        .get("storeTag")
        .and_then(Value::as_str)
        .filter(|tag| broker::store_key(tag))
        .ok_or_else(|| invalid("Mini Host profile lacks a canonical Store tag"))?
        .to_owned();
    let reply = broker::call_at(root, socket, &Request::InitStore { store: store.clone() })?;
    let expected = root.join(&store).join("host");
    if reply.get("stateRoot").and_then(Value::as_str) != expected.to_str() {
        return Err(invalid("broker grains root differs from the requested one"));
    }
    private_directory(&expected)?;
    let identity = json!({"deploymentId":reply.get("deploymentId"),"hostId":reply.get("hostId")});
    let path = expected.join("host-identity.json");
    if !exists(&path)? {
        derived_file(&path, &serde_json::to_vec_pretty(&identity)?)?;
    }
    let held = read_host_identity(&expected)?;
    if Some(held.deployment_id.as_str()) != reply.get("deploymentId").and_then(Value::as_str)
        || Some(held.host_id.as_str()) != reply.get("hostId").and_then(Value::as_str)
    {
        return Err(invalid("retained host identity differs from the broker's"));
    }
    Ok(json!({"protocol":"mini-spk-grain-init-store-v1","store":store,"stateRoot":expected,
        "brokerSocket":broker::socket_path(root, socket)?}))
}

pub fn run(args: &[String]) -> io::Result<Value> {
    if let [verb, root, host, config, flag, socket] = args {
        if verb == "init-store" && flag == "--broker-socket" {
            return init_store(
                Path::new(root),
                Path::new(host),
                Path::new(config),
                Some(Path::new(socket)),
            );
        }
    }
    if let [verb, profile] = args {
        if verb == "current-profile" {
            return profile_upgrade::current_profile(Path::new(profile));
        }
        if verb == "runtime-status" {
            return profile_upgrade::runtime_status(Path::new(profile));
        }
    }
    if let [verb, profile, admission] = args {
        if verb == "adopt-runtime" {
            return profile_upgrade::adopt_runtime(Path::new(profile), Path::new(admission));
        }
    }
    if let [verb, socket_flag, socket, request_flag, request] = args {
        if verb == "register-route" && socket_flag == "--socket" && request_flag == "--request" {
            return Ok(serde_json::to_value(
                crate::resident_route_control::register_file(
                    Path::new(socket),
                    Path::new(request),
                )?,
            )?);
        }
    }
    if let [verb, profile, admission] = args {
        if verb == "rebind-profile" {
            return profile_upgrade::rebind(Path::new(profile), Path::new(admission));
        }
    }
    if let [verb, root, host, config] = args {
        if verb == "init-store" {
            return init_store(Path::new(root), Path::new(host), Path::new(config), None);
        }
    }
    if let [verb, root, instance] = args {
        if verb == "supervise-instance" {
            let (store, app) = instance
                .split_once('-')
                .filter(|(store, app)| broker::store_key(store) && broker::decimal(app))
                .ok_or_else(|| invalid("supervisor instance must be STORE-APP"))?;
            let state_root = Path::new(root).join(store).join("host");
            let profile = profile_upgrade::selected_path(&state_root)?;
            let host = Host::load(&profile)?;
            return supervise(&host, app);
        }
    }
    match args {
        [verb, profile, rest @ ..] => {
            let host = Host::load(Path::new(profile))?;
            match (verb.as_str(), rest) {
                ("install", [source, receipt, spk, options @ ..]) => {
                    let options = install_options(options)?;
                    install(
                        &host,
                        Path::new(source),
                        Path::new(receipt),
                        Path::new(spk),
                        &options.class,
                        options.import.as_ref().map(|(dir, key)| (dir.as_path(), key.as_str())),
                        options.management_selector.as_deref(),
                    )
                }
                ("route", [app, request]) => {
                    crate::grain_route::route(&host_view(&host), app, Path::new(request))
                }
                ("start", [app]) => start(&host, app),
                ("stop", [app]) => stop(&host, app),
                ("status", [app]) => status(&host, app),
                ("session-intents", [app]) => profile_upgrade::session_intents(&host, app),
                ("supervise", [app]) => supervise(&host, app),
                ("export", [app, out]) => export(&host, app, Path::new(out)),
                ("backup", []) => broker::call_at(&host.profile.grains_root, host.profile.broker_socket.as_deref(), &Request::Backup {}),
                _ => Err(invalid(usage())),
            }
        }
        _ => Err(invalid(usage())),
    }
}

/// The subset of the host a route derivation may read.
pub(crate) struct HostView<'a> {
    pub state_root: &'a Path,
}

fn host_view(host: &Host) -> HostView<'_> {
    HostView {
        state_root: &host.profile.state_root,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn package_placement() -> Placement {
        Placement { protocol:"mini-spk-grain-placement-v2".into(),
            selector:LifecycleSelector {app:"8502".into(),package_manifest:"8503".into(),snapshot_manifest:"8504".into(),
                app_capability:"9502".into(),app_observe_capability:"9503".into(),package_capability:"9504".into(),package_observe_capability:"9505".into()},
            raw_sha256:"a".repeat(64),image_dir:None,app_uid:64010,app_gid:64010,
            volume_resource:"8502".into(),volume_mib:512,class:"S".into() }
    }

    #[test]
    fn spk_namespace_placement_old_bytes_preserve_global_image() {
        let old=package_placement();
        let value=serde_json::to_value(&old).unwrap();
        assert!(value.get("imageDir").is_none());
        let decoded:Placement=serde_json::from_value(value).unwrap();
        assert_eq!(placement_image_dir(&decoded).unwrap(),Path::new(PACKAGE_STORE).join(format!("sha256-{}",old.raw_sha256)));
    }

    #[test]
    fn spk_namespace_placement_retains_exact_configured_image_for_route_and_restart() {
        let mut placement=package_placement();
        let image=Path::new("/var/lib/mini-r2/spk/packages").join(format!("sha256-{}",placement.raw_sha256));
        placement.image_dir=Some(image.clone());
        let decoded:Placement=serde_json::from_slice(&serde_json::to_vec(&placement).unwrap()).unwrap();
        assert_eq!(placement_image_dir(&decoded).unwrap(),image);
        placement.image_dir=Some(Path::new("/var/lib/mini-r2/spk/packages").join("sha256-other"));
        assert!(placement_image_dir(&placement).is_err());
        placement.image_dir=Some(PathBuf::from("/var/lib/../mini-r2/spk/packages/sha256-other"));
        assert!(placement_image_dir(&placement).is_err());
    }

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
    fn failed_start_receipt_makes_the_claimed_generation_stopped_at_the_next_generation() {
        let root = std::env::temp_dir().join(format!(
            "grain-failed-start-{}-{:?}", std::process::id(), std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let app_dir = root.join("7101");
        let g3 = app_dir.join("g3");
        fs::create_dir_all(&g3).unwrap();
        let private = |path: &Path, value: &Value| {
            let _ = fs::remove_file(path);
            let mut file = OpenOptions::new().write(true).create_new(true).mode(0o600)
                .open(path).unwrap();
            file.write_all(&serde_json::to_vec(value).unwrap()).unwrap();
        };
        private(&g3.join("resident.json"),
            &json!({"startAction":{"kind":"create","index":0}}));
        private(&g3.join("start-admitted-v3.json"), &json!({"begin":{"processGeneration":"3"}}));
        // Claimed, never completed, no receipt: the supervisor's uncertain START.
        let runs = scan_runs(&app_dir).unwrap();
        assert!(matches!(&runs[0].state, RunState::Uncertain(r) if r.starts_with("START")));
        // Mini's reconciliation receipt: STOPPED, the generation it consumed is
        // the next START's floor, and the failed create created nothing.
        let receipt = json!({"protocol":"mini-spk-failed-start-recovered-v1","app":"7101",
            "generation":"3","reconciledGeneration":"4","outcome":{"type":"confirmed"}});
        private(&g3.join("failed-start-recovered-v1.json"), &receipt);
        let runs = scan_runs(&app_dir).unwrap();
        assert_eq!(runs[0].state, RunState::Stopped);
        assert_eq!(runs[0].stop_generation, Some(4));
        assert!(!runs[0].create);
        // Any other app, generation, advance or outcome is refused, not read as stopped.
        for (pointer, wrong) in [("/app", json!("7102")), ("/generation", json!("2")),
            ("/reconciledGeneration", json!("5")), ("/outcome/type", json!("absent")),
            ("/protocol", json!("mini-spk-failed-start-recovered-v0"))] {
            let mut bad = receipt.clone();
            *bad.pointer_mut(pointer).unwrap() = wrong;
            private(&g3.join("failed-start-recovered-v1.json"), &bad);
            assert!(scan_runs(&app_dir).is_err(), "{pointer}");
        }
        fs::remove_dir_all(root).unwrap();
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
