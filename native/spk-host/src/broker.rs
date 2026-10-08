//! Operator-owned typed SPK broker. User units and mapped subordinate app uids
//! provide grain isolation. Only the registered one-shot helper holds volume
//! mount/freeze privilege; the broker never runs with host uid zero.

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::ffi::CString;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, BufReader, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

#[path = "broker_endpoint.rs"]
mod endpoint;

#[path = "broker_runtime_adoption.rs"]
mod runtime_adoption;

#[path = "broker_home.rs"]
mod home_visibility;

#[path = "broker_volume_custody.rs"]
mod volume_custody;

const MAX_REQUEST: u64 = 16 * 1024;
const MAX_CONFIG: u64 = 64 * 1024;

fn invalid(reason: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, reason.into())
}

/// One size class: the per-app slice limits and the volume size. The kernel
/// will pin the class in the app birth descriptor (K-SPK); until then it is a
/// broker-side record set by `set-cgroup`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SizeClass {
    pub name: &'static str,
    pub memory_max: &'static str,
    pub cpu_weight: u32,
    pub tasks_max: u32,
    pub io_weight: u32,
    pub volume_mib: u64,
    /// Concurrent WebSockets one grain generation may hold open. The open is
    /// a Mini dispatch; frames are unmetered by design (SPK-HOSTING §348), so
    /// this and `ws_bytes_per_minute` are their physical bound. The open past
    /// the cap is refused `wsConcurrencyCap` before any Mini write.
    pub ws_max_open: usize,
    /// Bytes per minute one socket may carry, both directions summed, as a
    /// token bucket holding at most one minute. A socket past it is cut
    /// (`wsByteCap`) and the others on the grain are untouched.
    pub ws_bytes_per_minute: u64,
}

pub const CLASSES: &[SizeClass] = &[
    SizeClass {
        name: "S",
        memory_max: "512M",
        cpu_weight: 50,
        tasks_max: 256,
        io_weight: 50,
        volume_mib: 512,
        ws_max_open: 32,
        ws_bytes_per_minute: 4 * 1024 * 1024,
    },
    SizeClass {
        name: "M",
        memory_max: "1G",
        cpu_weight: 100,
        tasks_max: 512,
        io_weight: 100,
        volume_mib: 1024,
        ws_max_open: 64,
        ws_bytes_per_minute: 8 * 1024 * 1024,
    },
    SizeClass {
        name: "L",
        memory_max: "2G",
        cpu_weight: 200,
        tasks_max: 1024,
        io_weight: 200,
        volume_mib: 2048,
        ws_max_open: 128,
        ws_bytes_per_minute: 16 * 1024 * 1024,
    },
];

pub fn class(name: &str) -> io::Result<SizeClass> {
    CLASSES
        .iter()
        .copied()
        .find(|class| class.name == name)
        .ok_or_else(|| invalid(format!("size class {name:?} refused (S, M or L)")))
}

pub fn store_key(text: &str) -> bool {
    text.len() == 16
        && text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

pub fn decimal(text: &str) -> bool {
    !text.is_empty()
        && text.len() <= 18
        && !(text.len() > 1 && text.starts_with('0'))
        && text.bytes().all(|b| b.is_ascii_digit())
        && text != "0"
}

fn hex64(text: &str) -> bool {
    text.len() == 64
        && text
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// Mini's lifecycle receivers pin the resident unit name (Kernel
/// `ApplicationLifecycleResidentProfile.processIdentity`): the Store key (Mini's
/// `storeTag` of the genesis seed identity), the app and the generation. Two
/// Stores on one host never name the same unit.
/// Canonical Store coordinate; an absent or malformed id cannot name a unit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoreId(String);
impl StoreId {
    pub fn parse(value: &str) -> io::Result<Self> {
        if !store_key(value) { return Err(invalid("resident unit requires a canonical store id")); }
        Ok(Self(value.to_owned()))
    }
    pub fn as_str(&self) -> &str { &self.0 }
}
/// The only resident name constructor. Fields remain private.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidentUnit(String);
impl ResidentUnit {
    pub fn new(store: &StoreId, app: &str, generation: &str) -> io::Result<Self> {
        if !decimal(app) || !decimal(generation) { return Err(invalid("resident unit coordinates refused")); }
        let store = store.as_str();
        let name = format!("mini-spk-s{store}-a{app}-g{generation}.service");
        // Independent inverse guards constructor faults before systemd sees a name.
        if parse_resident_unit(&name) != Some((store.to_owned(), app.to_owned(), generation.to_owned())) {
            return Err(invalid("unit-name-collision: rendered resident name lost store identity"));
        }
        Ok(Self(name))
    }
    pub fn into_string(self) -> String { self.0 }
}
pub fn resident_unit(store: &str, app: &str, generation: &str) -> io::Result<String> {
    ResidentUnit::new(&StoreId::parse(store)?, app, generation).map(ResidentUnit::into_string)
}
/// Independent exact inverse; old names refuse rather than load a legacy world.
pub fn parse_resident_unit(unit: &str) -> Option<(String, String, String)> {
    let rest = unit.strip_prefix("mini-spk-s")?.strip_suffix(".service")?;
    let (store, rest) = rest.split_once("-a")?;
    let (app, generation) = rest.split_once("-g")?;
    (store_key(store) && decimal(app) && decimal(generation))
        .then(|| (store.to_owned(), app.to_owned(), generation.to_owned()))
}

/// Volume, mount and witness names carry the Store key: two Stores on one
/// host never adopt each other's /var.
pub fn volume_name(store: &str, app: &str) -> String {
    format!("{store}-{app}")
}

pub fn app_slice(prefix: &str, store: &str, app: &str) -> String {
    format!("s{store}-{prefix}-grains-a{app}.slice")
}

pub fn supervisor_unit(prefix: &str, store: &str, app: &str) -> String {
    format!("{prefix}-spk-supervisor@{store}-{app}.service")
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct BrokerConfig {
    pub protocol: String,
    pub store: String,
    pub grains_root: PathBuf,
    /// Explicit physical package namespace; absence refuses to load.
    #[serde(default)]
    pub spk_root: Option<PathBuf>,
    #[serde(default)]
    pub broker_socket: Option<PathBuf>,
    pub operator_user: String,
    pub unit_prefix: String,
    pub spk_host: PathBuf,
    pub spk_host_sha256: String,
    pub ingest_helper: PathBuf,
    pub volume_helper: PathBuf,
    pub app_uids: Vec<u32>,
    #[serde(default)]
    pub resident_home_read_only_paths: Vec<PathBuf>,
}

fn spk_namespace_paths(root: Option<&Path>) -> io::Result<(PathBuf, PathBuf)> {
    let root=root.ok_or_else(||invalid("SPK namespace requires an explicit store-scoped root"))?;
    let text = root.to_str().ok_or_else(|| invalid("SPK root must be UTF-8"))?;
    if !root.is_absolute() || text == "/" || text.ends_with('/')
        || text.contains("//") || text.contains("/../") || text.contains("/./")
        || text.ends_with("/..") || text.ends_with("/.")
        || !text.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b,b'/'|b'_'|b'-'|b'.')) {
        return Err(invalid("SPK root must be a simple canonical absolute namespace"));
    }
    Ok((root.join("packages"),root.join("inbox")))
}

fn validate_spk_namespace(root: Option<&Path>) -> io::Result<()> {
    let root=root.ok_or_else(||invalid("SPK namespace requires an explicit store-scoped root"))?;
    let (packages,inbox)=spk_namespace_paths(Some(root))?;
    if fs::canonicalize(root)? != root {
        return Err(invalid("SPK root traverses a symlink"));
    }
    for entry in root.ancestors() {
        let metadata=fs::symlink_metadata(entry)?;
        if !metadata.is_dir() || !(crate::os::root_owner(metadata.uid()) || metadata.uid()==unsafe{libc::geteuid()}) || metadata.mode()&0o022!=0 {
            return Err(invalid(format!("SPK root custody differs: {}",entry.display())));
        }
    }
    for (path,mode) in [(root,0o755),(packages.as_path(),0o755),(inbox.as_path(),0o700)] {
        let metadata=fs::symlink_metadata(path)?;
        if !metadata.is_dir() || !(crate::os::root_owner(metadata.uid()) || metadata.uid()==unsafe{libc::geteuid()}) || metadata.mode()&0o777!=mode {
            return Err(invalid(format!("SPK namespace directory custody differs: {}",path.display())));
        }
    }
    Ok(())
}

fn validate_world_package_namespace(store: &str, world: &Path, packages: Option<&Path>) -> io::Result<()> {
    let store = StoreId::parse(store)?;
    if world != Path::new("/var/lib/mini-spk-worlds").join(store.as_str())
        || packages != Some(world.join("spk").as_path())
    {
        return Err(invalid("broker package namespace belongs to another world"));
    }
    Ok(())
}

fn ingest_arguments(root: Option<&Path>, host: &Path, host_sha: &str, inbox: &Path, uid: u32) -> io::Result<Vec<String>> {
    let (_,expected_inbox)=spk_namespace_paths(root)?;
    if inbox.parent()!=Some(expected_inbox.as_path()) {
        return Err(invalid("ingest package is outside selected SPK inbox"));
    }
    let mut args=Vec::new();
    if let Some(root)=root {
        args.extend(["--root".to_owned(),root.to_str().ok_or_else(||invalid("SPK root path"))?.to_owned()]);
    }
    args.extend([host.to_str().ok_or_else(||invalid("Host path"))?.to_owned(),host_sha.to_owned(),
        inbox.to_str().ok_or_else(||invalid("inbox path"))?.to_owned(),uid.to_string()]);
    Ok(args)
}

pub(crate) fn image_path_from_identity(identity: &Value, raw_sha256: &str) -> io::Result<PathBuf> {
    if !hex64(raw_sha256) || identity.get("protocol").and_then(Value::as_str)!=Some("mini-spk-broker-identity-v1") {
        return Err(invalid("package image requires typed broker identity and exact SHA-256"));
    }
    let package_store=match identity.get("packageStore") {
        None=>return Err(invalid("broker identity requires explicit package namespace")),
        Some(Value::String(path))=>{
            let path=PathBuf::from(path);
            let root=path.parent().ok_or_else(||invalid("package store parent"))?;
            let (expected,_)=spk_namespace_paths(Some(root))?;
            if path!=expected { return Err(invalid("broker package store is outside selected SPK namespace")); }
            path
        },
        _=>return Err(invalid("broker package store has wrong type")),
    };
    Ok(package_store.join(format!("sha256-{raw_sha256}")))
}

pub(crate) fn package_image_at(grains_root: &Path, socket: Option<&Path>, raw_sha256: &str) -> io::Result<PathBuf> {
    let identity=call_at(grains_root,socket,&Request::Identify {})?;
    if identity.get("grainsRoot").and_then(Value::as_str)!=grains_root.to_str()
        || identity.get("brokerSocket").and_then(Value::as_str)!=socket_path(grains_root,socket)?.to_str() {
        return Err(invalid("package namespace broker identity differs from selected installation"));
    }
    image_path_from_identity(&identity,raw_sha256)
}

struct Broker {
    config: BrokerConfig,
    operator_uid: u32,
    operator_gid: u32,
    log: File,
}

/// The typed protocol. Unknown verbs and fields refuse at decode.
#[derive(Debug, Deserialize, Serialize)]
#[serde(tag = "verb", rename_all = "kebab-case", deny_unknown_fields)]
pub enum Request {
    Identify {},
    /// Create `GRAINS/<store>` (operator-owned 0700), the grain host state.
    InitStore {
        store: String,
    },
    /// Allocate (or return) the app UID for `<store>-<app>` from the pool.
    Place {
        store: String,
        app: String,
    },
    /// Record the app's size class and render its slice.
    SetCgroup {
        store: String,
        app: String,
        class: String,
    },
    /// Publish the root image for a staged package of this Store.
    Ingest {
        store: String,
        app: String,
        sha256: String,
    },
    /// Create (once) and attest the app's /var volume; `importSha256`
    /// creates it from `GRAINS/<store>/imports/<sha>.ext4`.
    MountVolume {
        store: String,
        app: String,
        #[serde(rename = "volumeId")]
        volume_id: String,
        #[serde(rename = "importSha256", default)]
        import_sha256: Option<String>,
    },
    /// Unmount a volume whose app has no active unit.
    Unmount {
        store: String,
        app: String,
    },
    /// Adopt a root-admitted runtime for one stopped Store.
    AdoptRuntime {
        store: String,
        admission: PathBuf,
    },
    RuntimeStatus {
        store: String,
    },
    /// Render the resident unit for one generation.
    InstallUnit {
        store: String,
        app: String,
        generation: String,
        #[serde(rename = "runtimeSha256", default)]
        runtime_sha256: Option<String>,
    },
    Start {
        unit: String,
    },
    /// Stop an installed resident unit; a failed unit is reset to inactive so
    /// STOP's exact audit can prove it.
    Stop {
        unit: String,
    },
    /// Copy a stopped app's volume image to `GRAINS/<store>/exports/`.
    ExportVolume {
        store: String,
        app: String,
    },
    /// Snapshot registered volumes through fixed-verb helper custody.
    Backup {},
}

pub fn socket_path(root: &Path, socket: Option<&Path>) -> io::Result<PathBuf> {
    endpoint::resolve(root, socket)
}
pub fn call_at(root: &Path, socket: Option<&Path>, request: &Request) -> io::Result<Value> {
    endpoint::call_at(root, socket, request)
}

fn read_private_operator(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() || meta.uid()!=unsafe{libc::geteuid()} || meta.mode() & 0o077 != 0 || meta.len() > max {
        return Err(invalid(format!("{} must be operator 0600", path.display())));
    }
    let mut bytes = Vec::new();
    file.take(max + 1).read_to_end(&mut bytes)?;
    Ok(bytes)
}

fn file_sha256(file: &mut File) -> io::Result<String> {
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

fn pinned_root_executable(path: &Path, sha: Option<&str>) -> io::Result<()> {
    let meta = fs::symlink_metadata(path)?;
    if !path.is_absolute() || !meta.is_file() || !(crate::os::root_owner(meta.uid()) || meta.uid()==unsafe{libc::geteuid()}) || meta.mode() & 0o022 != 0 {
        return Err(invalid(format!(
            "{} must be a root-owned executable",
            path.display()
        )));
    }
    if let Some(sha) = sha {
        if !hex64(sha) || file_sha256(&mut File::open(path)?)? != sha {
            return Err(invalid(format!(
                "{} SHA-256 differs from its pin",
                path.display()
            )));
        }
    }
    Ok(())
}

/// A root directory under the grains root: created on first use, then
/// required to be exactly root-owned with the given mode.
fn operator_dir(path: &Path, mode: u32) -> io::Result<()> {
    match fs::symlink_metadata(path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            fs::create_dir(path)?;
            fs::set_permissions(path, fs::Permissions::from_mode(mode))?;
        }
        Err(error) => return Err(error),
        Ok(_) => {}
    }
    let meta = fs::symlink_metadata(path)?;
    if !meta.is_dir()
        || meta.uid()!=unsafe{libc::geteuid()}
        || meta.gid()!=unsafe{libc::getegid()}
        || meta.mode() & 0o7777 != mode
    {
        return Err(invalid(format!("{} must be operator {mode:o}", path.display())));
    }
    Ok(())
}

/// Open `root/rel...` without following any symlink, requiring every
/// component below `root` to be owned by the operator and the leaf to be a
/// regular file. Root reads operator files only through this walk.
fn open_operator_file(root: &Path, rel: &[&str], operator_uid: u32) -> io::Result<File> {
    let root_c = CString::new(root.as_os_str().as_encoded_bytes()).map_err(|_| invalid("NUL"))?;
    let fd = unsafe {
        libc::open(
            root_c.as_ptr(),
            libc::O_PATH | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
        )
    };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    let mut current = unsafe { OwnedFd::from_raw_fd(fd) };
    for (index, part) in rel.iter().enumerate() {
        if part.is_empty() || *part == "." || *part == ".." || part.contains('/') {
            return Err(invalid("operator path component refused"));
        }
        let leaf = index + 1 == rel.len();
        let name = CString::new(*part).map_err(|_| invalid("NUL"))?;
        let flags = if leaf {
            libc::O_RDONLY | libc::O_NONBLOCK | libc::O_NOFOLLOW | libc::O_CLOEXEC
        } else {
            libc::O_PATH | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC
        };
        let fd = unsafe { libc::openat(current.as_raw_fd(), name.as_ptr(), flags) };
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }
        current = unsafe { OwnedFd::from_raw_fd(fd) };
        let mut stat = unsafe { std::mem::zeroed::<libc::stat>() };
        if unsafe { libc::fstat(current.as_raw_fd(), &mut stat) } != 0 {
            return Err(io::Error::last_os_error());
        }
        let kind = stat.st_mode & libc::S_IFMT;
        if stat.st_uid != operator_uid
            || (leaf && kind != libc::S_IFREG)
            || (!leaf && kind != libc::S_IFDIR)
            || stat.st_mode & 0o022 != 0
        {
            return Err(invalid(format!(
                "{} is not an operator-owned private path",
                rel.join("/")
            )));
        }
    }
    Ok(File::from(current))
}

/// `/etc/minidregg/spk/host-identity`: root 0600, two lines; the same file
/// `spk-var-volume` writes into every witness.

fn systemctl(args: &[&str]) -> io::Result<String> {
    let output = crate::os::systemctl()
        .arg("--user")
        .args(args)
        .stdin(Stdio::null())
        .output()?;
    if !output.status.success() {
        return Err(invalid(format!(
            "systemctl {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn active_state(unit: &str) -> io::Result<String> {
    systemctl(&["show", unit, "--property=ActiveState", "--value"])
}

fn helper(program: &Path, args: &[&str]) -> io::Result<String> {
    let output = Command::new(program)
        .args(args)
        .stdin(Stdio::null())
        .env_clear()
        .env("PATH", "/usr/sbin:/usr/bin:/sbin:/bin")
        .env("XDG_RUNTIME_DIR", format!("/run/user/{}", unsafe { libc::geteuid() }))
        .output()?;
    if !output.status.success() {
        return Err(invalid(format!(
            "{} {} failed: {}{}",
            program.display(),
            args.join(" "),
            String::from_utf8_lossy(&output.stdout).trim(),
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

/// Write a root file atomically with the given mode; refuse to replace a
/// different existing text unless `replace`.
fn write_operator_text(path: &Path, text: &str, mode: u32, replace: bool) -> io::Result<bool> {
    if let Ok(current) = fs::read(path) {
        if current == text.as_bytes() {
            fs::set_permissions(path, fs::Permissions::from_mode(mode))?;
            return Ok(false);
        }
        if !replace {
            return Err(invalid(format!(
                "{} exists with different text",
                path.display()
            )));
        }
    }
    let parent = path.parent().ok_or_else(|| invalid("path has no parent"))?;
    let temp = parent.join(format!(
        ".{}.tmp",
        path.file_name()
            .and_then(|n| n.to_str())
            .unwrap_or("broker")
    ));
    let _ = fs::remove_file(&temp);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(mode)
        .open(&temp)?;
    // The broker's umask is 077; unit files are meant to be world-readable.
    file.set_permissions(fs::Permissions::from_mode(mode))?;
    file.write_all(text.as_bytes())?;
    file.sync_all()?;
    fs::rename(&temp, path)?;
    File::open(parent)?.sync_all()?;
    Ok(true)
}

#[derive(Debug, Deserialize, Serialize, Clone, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Placement {
    protocol: String,
    store: String,
    app: String,
    app_uid: u32,
    app_gid: u32,
    class: Option<String>,
}

impl Broker {
    fn root(&self) -> &Path {
        &self.config.grains_root
    }
    fn broker_dir(&self) -> PathBuf {
        self.root().join("broker")
    }
    fn placement_path(&self, store: &str, app: &str) -> PathBuf {
        self.broker_dir()
            .join("placements")
            .join(format!("{}.json", volume_name(store, app)))
    }
    fn unit_tag_path(&self, unit: &str) -> PathBuf {
        self.broker_dir().join("units").join(unit)
    }

    fn load(config_path: &Path) -> io::Result<Self> {
        let config: BrokerConfig =
            serde_json::from_slice(&read_private_operator(config_path, MAX_CONFIG)?)?;
        if config.protocol != "mini-spk-broker-config-v2"
            || !store_key(&config.store)
            || config.grains_root.file_name().and_then(|n|n.to_str())!=Some(config.store.as_str())
            || config.spk_root.is_none()
            || !config.grains_root.is_absolute()
            || config.app_uids.is_empty()
            || config.app_uids.iter().any(|uid| *uid < 100)
            || config.unit_prefix.is_empty()
            || !config
                .unit_prefix
                .bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
            || config.unit_prefix.starts_with('-')
            || config.unit_prefix.ends_with('-')
        {
            return Err(invalid("broker config refused"));
        }
        validate_world_package_namespace(&config.store, &config.grains_root, config.spk_root.as_deref())?;
        validate_spk_namespace(config.spk_root.as_deref())?;
        pinned_root_executable(&config.spk_host, Some(&config.spk_host_sha256))?;
        pinned_root_executable(&config.ingest_helper, None)?;
        let registry=crate::volume_helper::Registry::load(&config.store)?;
        if registry.grains_root!=config.grains_root || registry.app_uids!=config.app_uids || registry.helper!=config.volume_helper {
            return Err(invalid("broker config differs from root-registered volume and subuid custody"));
        }
        let user = CString::new(config.operator_user.as_str()).map_err(|_| invalid("NUL"))?;
        let entry = unsafe { libc::getpwnam(user.as_ptr()) };
        if entry.is_null() {
            return Err(invalid("operator user absent"));
        }
        let (operator_uid, operator_gid) = unsafe { ((*entry).pw_uid, (*entry).pw_gid) };
        if operator_uid == 0 || operator_gid == 0 || operator_uid!=unsafe{libc::geteuid()} || operator_gid!=unsafe{libc::getegid()} || operator_uid!=registry.operator_uid || operator_gid!=registry.operator_gid || config.app_uids.contains(&operator_uid) {
            return Err(invalid(
                "operator must be an unprivileged user outside the app pool",
            ));
        }
        home_visibility::validate(&config.resident_home_read_only_paths,operator_uid)?;
        validate_subids(&config.operator_user,&config.app_uids)?;
        // Every ancestor of the grains root is root-owned and not group or
        // world writable: nothing below it can be swapped by a rename.
        let mut prefix = PathBuf::from("/");
        for part in config.grains_root.components().skip(1) {
            prefix.push(part);
            if prefix == config.grains_root {
                break;
            }
            let meta = fs::symlink_metadata(&prefix)?;
            if !meta.is_dir() || !(crate::os::root_owner(meta.uid()) || meta.uid()==unsafe{libc::geteuid()}) || meta.mode() & 0o022 != 0 {
                return Err(invalid(format!(
                    "grains root ancestor {} is not root-owned",
                    prefix.display()
                )));
            }
        }
        let root=fs::symlink_metadata(&config.grains_root)?;
        if !root.is_dir() || root.uid()!=0 || root.mode()&0o7777!=0o755 { return Err(invalid("protected world root custody refused")); }
        let broker = config.grains_root.join("broker");
        operator_dir(&broker, 0o700)?;
        operator_dir(&broker.join("placements"), 0o700)?;
        operator_dir(&broker.join("units"), 0o700)?;
        operator_dir(&broker.join("runtimes"), 0o700)?;
        operator_dir(&broker.join("unit-runtimes"), 0o700)?;

        let log = OpenOptions::new()
            .append(true)
            .create(true)
            .mode(0o600)
            .open(broker.join("broker.log"))?;
        Ok(Self {
            config,
            operator_uid,
            operator_gid,
            log,
        })
    }

    fn log(&mut self, line: &Value) {
        let mut bytes = line.to_string().into_bytes();
        bytes.push(b'\n');
        let _ = self.log.write_all(&bytes);
        let _ = self.log.sync_data();
        eprintln!("{line}");
    }

    /// The supervisor template and the grains slice, rendered at startup.
    /// The supervisor is `Type=exec`, not oneshot: while an `OnFailure=`
    /// target's start job is pending, systemd keeps the failed resident unit
    /// loaded with its old InvocationID, and STOP's exact post-stop audit
    /// requires that InvocationID cleared (Mini's `managerInvocationCleared`).
    fn render_static(&self) -> io::Result<()> {
        let prefix = &self.config.unit_prefix;
        let store = &self.config.store;
        let slice = "# rendered by mini-spk-broker\n[Unit]\nDescription=Mini SPK grains\n\n\
             [Slice]\nCPUWeight=50\nIOWeight=50\n";
        write_operator_text(
            &crate::os::runtime_units().join(format!("s{store}-{prefix}-grains.slice")),
            slice,
            0o644,
            true,
        )?;
        let supervisor = format!(
            "# rendered by mini-spk-broker\n[Unit]\nDescription=Mini SPK grain supervisor %i\n\
             StartLimitIntervalSec=1800\nStartLimitBurst=3\n\n[Service]\nType=exec\n\
             Slice=s{store}-{prefix}-grains.slice\n\
             ExecStart={spk} grain supervise-instance {root} %i\n\
             Restart=on-failure\nRestartSec=30\nRestartPreventExitStatus=3\n\
             NoNewPrivileges=yes\nUMask=0077\n",
            spk = self.config.spk_host.display(),
            root = self.root().display(),
        );
        write_operator_text(
            &crate::os::runtime_units().join(format!("{prefix}-spk-supervisor-s{store}@.service")),
            &supervisor,
            0o644,
            true,
        )?;
        self.render_adopted_supervisors()?;
        systemctl(&["daemon-reload"])?;
        Ok(())
    }

    fn placement(&self, store: &str, app: &str) -> io::Result<Placement> {
        let bytes = read_private_operator(&self.placement_path(store, app), MAX_CONFIG)
            .map_err(|_| invalid(format!("app {app} of store {store} is not placed")))?;
        let placement: Placement = serde_json::from_slice(&bytes)?;
        if placement.protocol != "mini-spk-broker-placement-v1"
            || placement.store != store
            || placement.app != app
            || placement.store != self.config.store
            || !self.config.app_uids.contains(&placement.app_uid)
            || placement.app_gid != placement.app_uid
        {
            return Err(invalid("placement record differs from its name"));
        }
        Ok(placement)
    }

    fn save_placement(&self, placement: &Placement) -> io::Result<()> {
        write_operator_text(
            &self.placement_path(&placement.store, &placement.app),
            &serde_json::to_string_pretty(placement)?,
            0o600,
            true,
        )
        .map(|_| ())
    }

    fn check_coordinates(store: &str, app: &str) -> io::Result<()> {
        if !store_key(store) || !decimal(app) {
            return Err(invalid("store key or app id refused"));
        }
        Ok(())
    }

    /// The broker installed this unit for exactly one Store.
    fn unit_store(&self, unit: &str) -> io::Result<Option<String>> {
        match fs::read_to_string(self.unit_tag_path(unit)) {
            Ok(text) => Ok(Some(text.trim().to_owned())),
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(error) => Err(error),
        }
    }

    /// `(store, app, generation)` of a resident unit name, or a refusal.
    fn check_resident_unit_name(unit: &str) -> io::Result<(String, String, String)> {
        parse_resident_unit(unit).ok_or_else(|| invalid("resident unit name refused"))
    }

    fn app_units_active(&self, store: &str, app: &str) -> io::Result<Vec<String>> {
        let mut active = Vec::new();
        for entry in fs::read_dir(self.broker_dir().join("units"))? {
            let name = entry?.file_name().to_string_lossy().into_owned();
            let Ok((unit_store, unit_app, _)) = Self::check_resident_unit_name(&name) else {
                continue;
            };
            if unit_app == app
                && unit_store == store
                && self.unit_store(&name)?.as_deref() == Some(store)
            {
                let state = active_state(&name)?;
                if matches!(
                    state.as_str(),
                    "active" | "activating" | "deactivating" | "reloading"
                ) {
                    active.push(name);
                }
            }
        }
        Ok(active)
    }

    fn handle(&mut self, request: Request) -> io::Result<Value> {
        let named=match &request {
            Request::Identify{}|Request::Backup{} => &self.config.store,
            Request::Start{unit}|Request::Stop{unit} => {
                let (store,_,_)=Self::check_resident_unit_name(unit)?;
                if store!=self.config.store { return Err(invalid("unit-name-collision: unit belongs to another store")); }
                &self.config.store
            }
            Request::InitStore{store}|Request::Place{store,..}|Request::SetCgroup{store,..}|Request::Ingest{store,..}|Request::MountVolume{store,..}|Request::Unmount{store,..}|Request::AdoptRuntime{store,..}|Request::RuntimeStatus{store}|Request::InstallUnit{store,..}|Request::ExportVolume{store,..}=>store,
        };
        if named!=&self.config.store { return Err(invalid("broker refuses a different store")); }
        match request {
            Request::Identify {} => Ok(json!({"protocol":"mini-spk-broker-identity-v1",
                "grainsRoot":self.root(),"brokerSocket":socket_path(self.root(), self.config.broker_socket.as_deref())?,
                "store":self.config.store,"packageStore":spk_namespace_paths(self.config.spk_root.as_deref())?.0})),
            Request::InitStore { store } => {
                if !store_key(&store) {
                    return Err(invalid("store key refused"));
                }
                let dir = self.root().join(&store);
                match fs::symlink_metadata(&dir) {
                    Err(error) if error.kind() == io::ErrorKind::NotFound => {
                        fs::create_dir(&dir)?;
                        std::os::unix::fs::chown(
                            &dir,
                            Some(self.operator_uid),
                            Some(self.operator_gid),
                        )?;
                        fs::set_permissions(&dir, fs::Permissions::from_mode(0o700))?;
                    }
                    Err(error) => return Err(error),
                    Ok(_) => {}
                }
                let meta = fs::symlink_metadata(&dir)?;
                if !meta.is_dir()
                    || meta.uid() != self.operator_uid
                    || meta.mode() & 0o7777 != 0o700
                {
                    return Err(invalid("store directory identity drift"));
                }
                let registry=crate::volume_helper::Registry::load(&store)?;
                let (deployment_id, host_id)=(registry.deployment_id,registry.host_id);
                Ok(
                    json!({"stateRoot":dir.join("host"),"deploymentId":deployment_id,
                    "hostId":host_id}),
                )
            }
            Request::Place { store, app } => {
                Self::check_coordinates(&store, &app)?;
                self.require_not_pending(&store)?;
                if let Ok(placement) = self.placement(&store, &app) {
                    return Ok(
                        json!({"appUid":placement.app_uid,"appGid":placement.app_gid,
                        "class":placement.class}),
                    );
                }
                let mut bound = Vec::new();
                for entry in fs::read_dir(self.broker_dir().join("placements"))? {
                    let path = entry?.path();
                    if path.extension().and_then(|e| e.to_str()) != Some("json") {
                        continue;
                    }
                    let placement: Placement =
                        serde_json::from_slice(&read_private_operator(&path, MAX_CONFIG)?)?;
                    bound.push(placement.app_uid);
                }
                let uid = self
                    .config
                    .app_uids
                    .iter()
                    .copied()
                    .find(|uid| !bound.contains(uid))
                    .ok_or_else(|| invalid("app UID pool exhausted"))?;
                let gid = uid;
                if gid == 0 || gid == self.operator_gid {
                    return Err(invalid("app account group refused"));
                }
                let placement = Placement {
                    protocol: "mini-spk-broker-placement-v1".into(),
                    store,
                    app,
                    app_uid: uid,
                    app_gid: gid,
                    class: None,
                };
                self.save_placement(&placement)?;
                Ok(json!({"appUid":uid,"appGid":gid,"class":null}))
            }
            Request::SetCgroup {
                store,
                app,
                class: name,
            } => {
                Self::check_coordinates(&store, &app)?;
                self.require_not_pending(&store)?;
                let class = class(&name)?;
                let mut placement = self.placement(&store, &app)?;
                if let Some(existing) = &placement.class {
                    if existing != class.name && !self.app_units_active(&store, &app)?.is_empty() {
                        return Err(invalid("class change refused while the app is running"));
                    }
                }
                let slice = app_slice(&self.config.unit_prefix, &store, &app);
                let text = format!(
                    "# rendered by mini-spk-broker store={store} app={app} class={c}\n\
                     [Unit]\nDescription=Mini SPK grain {app} store {store} class {c}\n\n\
                     [Slice]\nMemoryAccounting=yes\nMemoryMax={mem}\nMemorySwapMax=0\n\
                     CPUWeight={cpu}\nTasksMax={tasks}\nIOWeight={io}\n",
                    c = class.name,
                    mem = class.memory_max,
                    cpu = class.cpu_weight,
                    tasks = class.tasks_max,
                    io = class.io_weight,
                );
                write_operator_text(&crate::os::runtime_units().join(&slice), &text, 0o644, true)?;
                systemctl(&["daemon-reload"])?;
                placement.class = Some(class.name.into());
                self.save_placement(&placement)?;
                Ok(
                    json!({"slice":slice,"class":class.name,"memoryMax":class.memory_max,
                    "cpuWeight":class.cpu_weight,"tasksMax":class.tasks_max,
                    "volumeMib":class.volume_mib}),
                )
            }
            Request::Ingest { store, app, sha256 } => {
                Self::check_coordinates(&store, &app)?;
                let runtime = self.runtime_for(&store)?;
                if !hex64(&sha256) {
                    return Err(invalid("package SHA-256 refused"));
                }
                let placement = self.placement(&store, &app)?;
                let (package_store,private_inbox)=spk_namespace_paths(self.config.spk_root.as_deref())?;
                let image = package_store.join(format!("sha256-{sha256}"));
                if fs::symlink_metadata(&image).is_err() {
                    let package = format!("sha256-{sha256}");
                    let mut source = open_operator_file(
                        self.root(),
                        &[&store, "host", "packages", &package, "package.spk"],
                        self.operator_uid,
                    )?;
                    if source.metadata()?.len() > 256 * 1024 * 1024 {
                        return Err(invalid("staged package exceeds bound"));
                    }
                    let inbox = private_inbox.join(format!("grain-{sha256}.spk"));
                    let temp = private_inbox.join(format!(".grain-{sha256}.broker"));
                    let _ = fs::remove_file(&temp);
                    let mut out = OpenOptions::new()
                        .write(true)
                        .create_new(true)
                        .mode(0o600)
                        .open(&temp)?;
                    io::copy(&mut source, &mut out)?;
                    out.sync_all()?;
                    if file_sha256(&mut File::open(&temp)?)? != sha256 {
                        let _ = fs::remove_file(&temp);
                        return Err(invalid("staged package differs from its SHA-256"));
                    }
                    fs::rename(&temp, &inbox)?;
                    let arguments=ingest_arguments(self.config.spk_root.as_deref(),&runtime.spk_host,
                        &runtime.spk_host_sha256,&inbox,placement.app_uid)?;
                    let borrowed=arguments.iter().map(String::as_str).collect::<Vec<_>>();
                    helper(&self.config.ingest_helper,&borrowed)?;
                }
                Ok(json!({"imageDir":image}))
            }
            Request::MountVolume { store, app, volume_id, import_sha256 } => {
                Self::check_coordinates(&store,&app)?;
                let placement=self.placement(&store,&app)?;
                let class=class(placement.class.as_deref().ok_or_else(||invalid("set-cgroup must precede mount-volume"))?)?;
                let request=self.volume_request(&store,&app,&placement,&volume_id,class.volume_mib,crate::volume_helper::Verb::Create,import_sha256)?;
                crate::volume_helper::call(&self.config.volume_helper,&request)?;
                write_operator_text(&self.broker_dir().join(format!("volume-{app}.json")),&serde_json::to_string(&request)?,0o600,false)?;
                Ok(json!({"name":volume_name(&store,&app),"mount":request.volume_path,
                    "witness":self.root().join("attest").join(format!("{}-{}.witness",store,app)),"appUid":placement.app_uid,"sizeMib":class.volume_mib}))
            }
            Request::Unmount { store, app } => {
                Self::check_coordinates(&store,&app)?;
                if !self.app_units_active(&store,&app)?.is_empty() { return Err(invalid("unmount refused: active app")); }
                self.volume_action(&app,crate::volume_helper::Verb::Unmount)
            }
            Request::AdoptRuntime { store, admission } => self.adopt_runtime(&store, &admission),
            Request::RuntimeStatus { store } => self.runtime_status(&store),
            Request::InstallUnit {
                store,
                app,
                generation,
                runtime_sha256,
            } => {
                Self::check_coordinates(&store, &app)?;
                if !decimal(&generation) {
                    return Err(invalid("generation refused"));
                }
                let runtime = self.runtime_for(&store)?;
                runtime_adoption::check_install_pin(
                    runtime_sha256.as_deref(),
                    &runtime.spk_host_sha256,
                    self.adoption_exists(&store)?,
                )?;
                let placement = self.placement(&store, &app)?;
                if placement.class.is_none() {
                    return Err(invalid("set-cgroup must precede install-unit"));
                }
                let unit = resident_unit(&store, &app, &generation)?;
                if let Some(owner) = self.unit_store(&unit)? {
                    if owner != store {
                        return Err(invalid(format!(
                            "unit {unit} is recorded for store {owner}, not the store its name carries"
                        )));
                    }
                } else if fs::symlink_metadata(crate::os::runtime_units().join(&unit)).is_ok()
                    || !active_state(&unit)
                        .map(|s| s == "inactive")
                        .unwrap_or(false)
                {
                    return Err(invalid(format!(
                        "unit {unit} exists outside this broker's records; refusing to adopt it"
                    )));
                }
                let gen_dir = format!("g{generation}");
                // The config must exist and be operator-owned; its contents are
                // the resident's to check (it runs as the operator).
                let mut resident_file=open_operator_file(
                    self.root(),
                    &[&store, "host", "apps", &app, &gen_dir, "resident.json"],
                    self.operator_uid,
                )?;
                let mut resident_bytes=Vec::new();
                Read::by_ref(&mut resident_file).take(MAX_CONFIG+1).read_to_end(&mut resident_bytes)?;
                if resident_bytes.len() as u64>MAX_CONFIG { return Err(invalid("resident visibility config exceeds bound")); }
                let resident:Value=serde_json::from_slice(&resident_bytes)?;
                let visibility=home_visibility::render(self,&store,&app,&resident)?;
                let config = self
                    .root()
                    .join(&store)
                    .join("host/apps")
                    .join(&app)
                    .join(&gen_dir)
                    .join("resident.json");
                let prefix = &self.config.unit_prefix;
                let text = format!(
                    "# rendered by mini-spk-broker store={store} app={app} generation={generation}\n\
                     [Unit]\nDescription=Mini SPK resident app {app} generation {generation} store {store}\n\
                     OnFailure={supervisor}\n\n[Service]\nType=exec\n\
                     Slice={slice}\n\
                     Environment=MINI_SPK_APP_UID={uid} MINI_SPK_APP_GID={gid} MINI_SPK_OPERATOR_UID={operator_uid} MINI_SPK_OPERATOR_GID={operator_gid} \
                     MINI_SPK_GRAINS_ROOT={root} MINI_SPK_STORE={store} MINI_SPK_UNIT={unit} MINI_SPK_BROKER_SOCKET={broker_socket}\n\
                     ExecStart={spk} resident-bootstrap {config}\n\
                     AmbientCapabilities=\n\
                     NoNewPrivileges=no\n\
                     KillMode=control-group\nUMask=0077\n",
                    supervisor = supervisor_unit(prefix, &store, &app),
                    operator_uid = self.operator_uid,
                    operator_gid = self.operator_gid,
                    slice = app_slice(prefix, &store, &app),
                    uid = placement.app_uid,
                    gid = placement.app_gid,
                    root = self.root().display(),
                    broker_socket = socket_path(self.root(), self.config.broker_socket.as_deref())?.display(),
                    spk = runtime.spk_host.display(),
                    config = config.display(),
                );
                self.render_store_supervisor(&store, &app, &runtime)?;
                write_operator_text(
                    &self.unit_tag_path(&unit),
                    &format!("{store}\n"),
                    0o600,
                    false,
                )?;
                write_operator_text(&crate::os::runtime_units().join(&unit), &text, 0o644, false)?;
                // No reset-failed here: a crashed generation's failed state and
                // InvocationID are what STOP's pre-stop check identifies the
                // dead incarnation by. `start` and `stop` reset it.
                if !visibility.is_empty() {
                    let drop_dir=crate::os::runtime_units().join(format!("{unit}.d"));
                    fs::create_dir_all(&drop_dir)?;
                    fs::set_permissions(&drop_dir,fs::Permissions::from_mode(0o755))?;
                    write_operator_text(&drop_dir.join("10-native-visibility.conf"),&visibility,0o644,false)?;
                }
                systemctl(&["daemon-reload"])?;
                self.save_unit_runtime(&unit, &runtime)?;
                Ok(
                    json!({"unit":unit,"slice":app_slice(prefix, &store, &app),"spkHostSha256":runtime.spk_host_sha256}),
                )
            }
            Request::Start { unit } => {
                let (named, _, _) = Self::check_resident_unit_name(&unit)?;
                let store = self
                    .unit_store(&unit)?
                    .filter(|store| *store == named)
                    .ok_or_else(|| invalid("start refused: unit not installed by this broker for its store"))?;
                self.require_unit_runtime(&store, &unit)?;
                // A never-begun generation's earlier failed attempt.
                if active_state(&unit)? == "failed" {
                    systemctl(&["reset-failed", &unit])?;
                }
                systemctl(&["start", &unit])?;
                Ok(json!({"unit":unit,"activeState":active_state(&unit)?}))
            }
            Request::Stop { unit } => {
                let (named, _, _) = Self::check_resident_unit_name(&unit)?;
                if self.unit_store(&unit)?.as_deref() != Some(named.as_str()) {
                    return Err(invalid("stop refused: unit not installed by this broker for its store"));
                }
                systemctl(&["stop", &unit])?;
                if active_state(&unit)? == "failed" {
                    systemctl(&["reset-failed", &unit])?;
                }
                Ok(json!({"unit":unit,"activeState":active_state(&unit)?}))
            }
            Request::Backup {} => {

                let stamp = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map_err(|_| invalid("clock"))?
                    .as_secs();
                self.backup_into(&self.broker_dir().join("backups").join(stamp.to_string()))
            }
            Request::ExportVolume { store, app } => {
                Self::check_coordinates(&store, &app)?;
                let active = self.app_units_active(&store, &app)?;
                if !active.is_empty() {
                    return Err(invalid(format!(
                        "export refused: {} active; STOP first",
                        active.join(",")
                    )));
                }
                self.volume_action(&app,crate::volume_helper::Verb::Freeze)

            }
        }
    }
}

/// `mini-spk-broker backup CONFIG OUT_DIR` as the operator.
/// Every registered volume is copied with its filesystem frozen for the
/// duration of the copy, so a running app's image (a live SQLite file inside
/// it is the hazard) is captured at one crash-consistent instant: what a
/// power cut would leave, which SQLite's journal is built to recover. A
/// stopped app's copy is exact. Each copy is checked (`e2fsck -fn`) and its
/// root directory listed (`debugfs`) without mounting it.
pub fn backup(config_path: &Path, out: &Path) -> io::Result<Value> {
    Broker::load(config_path)?.backup_into(out)
}

impl Broker {
    fn backup_into(&self, out: &Path) -> io::Result<Value> {
        let parent=out.parent().ok_or_else(||invalid("backup parent"))?;
        operator_dir(parent,0o700)?;
        operator_dir(out,0o700)?;
        let mut grains=Vec::new();
        for volume in crate::volume_helper::volumes_status(&self.config.volume_helper,&self.config.store)? {
            let request=volume.request;
            let active=self.app_units_active(&request.store,&request.grain)?;
            let mut freeze=request.clone();freeze.verb=crate::volume_helper::Verb::Freeze;
            let mut copied=crate::volume_helper::call(&self.config.volume_helper,&freeze)?;
            copied["state"]=json!(if active.is_empty(){"stopped-exact"}else{"running-frozen-crash-consistent"});
            copied["activeUnits"]=json!(active);
            copied["store"]=json!(request.store);
            copied["app"]=json!(request.grain);
            copied["name"]=json!(volume_name(&request.store,&request.grain));
            grains.push(copied);
        }
        let manifest=json!({"protocol":"mini-spk-grain-backup-v1","grainsRoot":self.root(),"grains":grains});
        write_operator_text(&out.join("grains-backup.json"),&serde_json::to_string_pretty(&manifest)?,0o600,false)?;
        Ok(manifest)
    }
}

fn peer_credentials(stream: &UnixStream) -> io::Result<libc::ucred> {
    let mut cred = libc::ucred {
        pid: 0,
        uid: u32::MAX,
        gid: u32::MAX,
    };
    let mut len = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
    if unsafe {
        libc::getsockopt(
            stream.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            (&mut cred as *mut libc::ucred).cast(),
            &mut len,
        )
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    Ok(cred)
}

/// `mini-spk-broker CONFIG`: serve until killed, one request per connection,
/// strictly sequentially (two requests never race on one grain).
pub fn serve(config_path: &Path) -> io::Result<()> {
    if unsafe{libc::geteuid()}==0 { return Err(invalid("mini-spk-broker requires unprivileged operator")); }
    unsafe {
        libc::umask(0o077);
    }
    let mut broker = Broker::load(config_path)?;
    let socket = socket_path(broker.root(), broker.config.broker_socket.as_deref())?;
    operator_dir(socket.parent().ok_or_else(||invalid("runtime dir"))?,0o700)?;
    let (listener, _socket_lock) = endpoint::bind(&socket, broker.operator_gid)?;
    broker.render_static()?;
    broker.log(&json!({"event":"listening","socket":socket,
        "grainsRoot":broker.config.grains_root,"operator":broker.config.operator_user,
        "unitPrefix":broker.config.unit_prefix}));
    for stream in listener.incoming() {
        let mut stream = match stream {
            Ok(stream) => stream,
            Err(_) => continue,
        };
        let _ = stream.set_read_timeout(Some(Duration::from_secs(10)));
        let cred = match peer_credentials(&stream) {
            Ok(cred) => cred,
            Err(_) => continue,
        };
        let mut line = Vec::new();
        let read = BufReader::new((&stream).take(MAX_REQUEST + 1)).read_until(b'\n', &mut line);
        let outcome: io::Result<(Value, io::Result<Value>)> = (|| {
            read?;
            if cred.uid != broker.operator_uid {
                return Err(invalid(format!(
                    "peer uid {} is not the operator",
                    cred.uid
                )));
            }
            if line.len() as u64 > MAX_REQUEST || line.last() != Some(&b'\n') {
                return Err(invalid("request framing refused"));
            }
            let request: Request = serde_json::from_slice(&line)
                .map_err(|error| invalid(format!("request refused: {error}")))?;
            let echo = serde_json::to_value(&request)?;
            let result = broker.handle(request);
            Ok((echo, result))
        })();
        let (echo, result) = match outcome {
            Ok((echo, result)) => (echo, result),
            Err(error) => (Value::Null, Err(error)),
        };
        let reply = match &result {
            Ok(value) => json!({"ok":true,"result":value}),
            Err(error) => json!({"ok":false,"error":error.to_string()}),
        };
        broker.log(&json!({
            "at":SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0),
            "peer":{"pid":cred.pid,"uid":cred.uid,"gid":cred.gid},
            "request":echo,
            "ok":result.is_ok(),
            "error":result.as_ref().err().map(|e| e.to_string()),
        }));
        let _ = stream.write_all(reply.to_string().as_bytes());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tenancy_package_namespace_cannot_alias_another_world() {
        let a = Path::new("/var/lib/mini-spk-worlds/0123456789abcdef");
        let b = Path::new("/var/lib/mini-spk-worlds/fedcba9876543210");
        assert!(validate_world_package_namespace("0123456789abcdef", a, Some(&a.join("spk"))).is_ok());
        assert!(validate_world_package_namespace("0123456789abcdef", a, Some(&b.join("spk"))).is_err());
        assert!(validate_world_package_namespace("0123456789abcdef", b, Some(&b.join("spk"))).is_err());
        assert!(validate_world_package_namespace("0123456789abcdef", a, None).is_err());
    }

    #[test]
    fn spk_namespace_refuses_missing_world_namespace() {
        assert!(spk_namespace_paths(None).is_err());
        assert!(ingest_arguments(None,Path::new("/operator/spk-host"),"hash",Path::new("/var/lib/minidregg/spk/inbox/grain-package.spk"),165536).is_err());
    }

    #[test]
    fn spk_namespace_explicit_root_binds_helper_and_both_paths() {
        let root=Path::new("/var/lib/mini-bigstep-hbox-r2/spk");
        let (packages,inbox)=spk_namespace_paths(Some(root)).unwrap();
        assert_eq!(packages,root.join("packages"));
        assert_eq!(inbox,root.join("inbox"));
        let args=ingest_arguments(Some(root),Path::new("/root/candidate/spk-host"),"hash",
            &inbox.join("grain-package.spk"),64010).unwrap();
        assert_eq!(&args[..2],["--root","/var/lib/mini-bigstep-hbox-r2/spk"]);
        assert_eq!(args[4],"/var/lib/mini-bigstep-hbox-r2/spk/inbox/grain-package.spk");
        assert!(ingest_arguments(Some(root),Path::new("/root/spk-host"),"hash",
            Path::new("/var/lib/minidregg/spk/inbox/package.spk"),64010).is_err());
    }

    #[test]
    fn spk_namespace_refuses_ambiguous_root_paths() {
        for bad in ["/","relative","/var/lib/../spk","/var/lib/./spk","/var//lib/spk","/var/lib/spk/","/var/lib/spk/..","/var/lib/spk x"] {
            assert!(spk_namespace_paths(Some(Path::new(bad))).is_err(),"{bad}");
        }
        assert!(validate_spk_namespace(Some(Path::new("/tmp"))).is_err());
    }

    #[test]
    fn spk_namespace_identity_refuses_legacy_and_malformed_routes() {
        let sha="a".repeat(64);
        let old=json!({"protocol":"mini-spk-broker-identity-v1"});
        assert!(image_path_from_identity(&old,&sha).is_err());
        let current=json!({"protocol":"mini-spk-broker-identity-v1","packageStore":"/var/lib/mini-r2/spk/packages"});
        assert_eq!(image_path_from_identity(&current,&sha).unwrap(),Path::new("/var/lib/mini-r2/spk/packages").join(format!("sha256-{sha}")));
        for bad in [json!(null),json!("relative/packages"),json!("/var/lib/spk/not-packages"),json!("/var/lib/../spk/packages")] {
            let mut value=old.clone();value["packageStore"]=bad;
            assert!(image_path_from_identity(&value,&sha).is_err());
        }
        assert!(image_path_from_identity(&current,"../escape").is_err());
    }

    #[test]
    fn protocol_refuses_unknown_verbs_and_fields() {
        assert!(serde_json::from_str::<Request>(
            r#"{"verb":"start","unit":"mini-spk-s0123456789abcdef-a1-g2.service"}"#
        )
        .is_ok());
        assert!(serde_json::from_str::<Request>(r#"{"verb":"exec","command":"sh"}"#).is_err());
        assert!(serde_json::from_str::<Request>(
            r#"{"verb":"start","unit":"mini-spk-s0123456789abcdef-a1-g2.service","text":"[Service]"}"#
        )
        .is_err());
        assert!(serde_json::from_str::<Request>(
            r#"{"verb":"install-unit","store":"0123456789abcdef","app":"7","generation":"2","unitText":"x"}"#
        )
        .is_err());
    }

    #[test]
    fn tenancy_resident_unit_names_are_exact_and_carry_the_store() {
        let store = "0123456789abcdef";
        assert!(resident_unit("", "7701", "2").is_err());
        assert!(resident_unit(store, "7701", "").is_err());
        let unit = resident_unit(store, "7701", "2").unwrap();
        assert_eq!(unit, "mini-spk-s0123456789abcdef-a7701-g2.service");
        assert_eq!(
            Broker::check_resident_unit_name(&unit).unwrap(),
            (store.to_owned(), "7701".to_owned(), "2".to_owned())
        );
        // The same app and generation in another Store is another unit.
        assert_ne!(resident_unit("fedcba9876543210", "7701", "2").unwrap(), unit);
        for bad in [
            "mini-spk-a7701-g2.service",
            "mini-spk-s0123456789abcdef-a07701-g2.service",
            "mini-spk-s0123456789abcdef-a7701-g2.service.d",
            "mini-spk-s0123456789abcdef-a7701-g0.service",
            "mini-spk-s0123456789ABCDEF-a7701-g2.service",
            "mini-spk-s0123456789abcde-a7701-g2.service",
            "mini-spk-s0123456789abcdef0-a7701-g2.service",
            "mini-spk-s0123456789abcdef-a1-g2-g3.service",
            "mini-spk-s0123456789abcdef-a1-g2.service/../x",
            "sshd.service",
        ] {
            assert!(Broker::check_resident_unit_name(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn coordinates_and_classes() {
        assert!(Broker::check_coordinates("0123456789abcdef", "7701").is_ok());
        assert!(Broker::check_coordinates("0123456789ABCDEF", "7701").is_err());
        assert!(Broker::check_coordinates("0123456789abcdef", "../1").is_err());
        assert!(Broker::check_coordinates("0123456789abcde", "1").is_err());
        assert_eq!(class("S").unwrap().memory_max, "512M");
        assert_eq!(class("M").unwrap().memory_max, "1G");
        assert_eq!(class("L").unwrap().memory_max, "2G");
        assert!(class("XL").is_err());
        assert_eq!(class("S").unwrap().ws_max_open, 32);
        assert!(CLASSES
            .windows(2)
            .all(|pair| pair[0].ws_max_open < pair[1].ws_max_open
                && pair[0].ws_bytes_per_minute < pair[1].ws_bytes_per_minute));
        assert_eq!(
            volume_name("0123456789abcdef", "7701"),
            "0123456789abcdef-7701"
        );
        assert_eq!(
            app_slice("mini", "0123456789abcdef", "7701"),
            "s0123456789abcdef-mini-grains-a7701.slice"
        );
    }
}

#[path = "broker_checkpoint.rs"]
mod checkpoint;
pub fn checkpoint_pause_check(config: &Path, input: &Path) -> io::Result<Value> {
    checkpoint::check(config, input)
}
pub fn checkpoint_backup(config: &Path, out: &Path, input: &Path) -> io::Result<Value> {
    checkpoint::backup(config, out, input)
}

// Only the installed one-shot volume helper calls these root receiving paths.
pub(crate) fn volume_import(root: &Path, store: &str, sha: &str, uid: u32) -> io::Result<File> {
    open_operator_file(root, &[store, "imports", &format!("{sha}.ext4")], uid)
}
pub(crate) fn volume_pause_bytes(root:&Path,store:&str,app:&str,parts:&[&str],uid:u32) -> io::Result<Vec<u8>> {
    let mut path=vec![store,"host","apps",app];path.extend_from_slice(parts);
    let file=open_operator_file(root,&path,uid)?;
    if file.metadata()?.len()>1024*1024 {return Err(invalid("checkpoint custody file exceeds bound"))}
    let mut bytes=Vec::new();file.take(1024*1024+1).read_to_end(&mut bytes)?;
    if bytes.len()>1024*1024 {return Err(invalid("checkpoint custody file grew"))}
    Ok(bytes)
}
pub(crate) fn volume_recover(root: &Path) -> io::Result<()> { volume_custody::recover(root) }
pub(crate) fn volume_export(root: &Path, store: &str, app: &str, uid: u32, gid: u32) -> io::Result<Value> {
    volume_custody::export(root, store, app, uid, gid)
}

fn validate_subids(user: &str, ids: &[u32]) -> io::Result<()> {
    for source in ["/etc/subuid", "/etc/subgid"] {
        let text=fs::read_to_string(source)?;
        let ranges:Vec<(u32,u32)>=text.lines().filter_map(|line| {
            let mut p=line.split(':');
            if p.next()?!=user { return None; }
            Some((p.next()?.parse().ok()?,p.next()?.parse().ok()?))
        }).collect();
        if ids.iter().any(|id| !ranges.iter().any(|(start,count)| *id>=*start && (*id as u64)<(*start as u64)+(*count as u64))) {
            return Err(invalid(format!("world app uid outside {source} allocation")));
        }
    }
    Ok(())
}
impl Broker {
    fn volume_request(&self,store:&str,app:&str,placement:&Placement,volume_id:&str,mib:u64,verb:crate::volume_helper::Verb,import:Option<String>)->io::Result<crate::volume_helper::Request> {
        let registry=crate::volume_helper::Registry::load(store)?;
        Ok(crate::volume_helper::Request { verb,store:store.to_owned(),deployment_id:registry.deployment_id,
            grain:app.to_owned(),volume_path:self.root().join("vars").join(volume_name(store,app)),
            app_uid:placement.app_uid,size_mib:mib,volume_id:volume_id.to_owned(),import_sha256:import })
    }
    fn volume_action(&self,app:&str,verb:crate::volume_helper::Verb)->io::Result<Value> {
        if !decimal(app) { return Err(invalid("volume app refused")); }
        let mut request:crate::volume_helper::Request=serde_json::from_slice(&read_private_operator(&self.broker_dir().join(format!("volume-{app}.json")),MAX_CONFIG)?)?;
        request.verb=verb;
        crate::volume_helper::call(&self.config.volume_helper,&request)
    }
}
