//! Operator-owned typed SPK broker. User units and mapped subordinate app uids
//! provide grain isolation. Only the registered one-shot helper holds volume
//! mount/freeze privilege; the broker never runs with host uid zero.

use crate::io_context::IoContext;
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
use crate::canonical::hex64;

#[path = "broker_endpoint.rs"]
mod endpoint;
#[cfg(test)]
pub(crate) fn connect_for_test(path: &Path) -> io::Result<std::os::unix::net::UnixStream> { endpoint::connect_for_test(path) }

#[path = "broker_runtime_adoption.rs"]
mod runtime_adoption;

#[path = "broker_home.rs"]
mod home_visibility;

#[path = "broker_volume_custody.rs"]
mod volume_custody;

#[path = "broker_volume_dir.rs"]
mod volume_dir;
pub(crate) use volume_dir::{export_image_bytes, Registration, Volume};

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
    /// a Mini dispatch; frames are not Mini writes and carry no fee, so
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
    crate::canonical::lower_hex_of(&text, 8)
}

/// A positive canonical decimal that fits an unsigned 64-bit integer (at most 20 digits): a member's
/// application is a participant-namespace id, which is at least 2^63.
pub fn decimal(text: &str) -> bool {
    crate::canonical::decimal_u64(text).is_some_and(|value| value != 0)
}

/// Mini's lifecycle receivers pin the resident unit name (Kernel
/// `ApplicationLifecycleResidentProfile.processIdentity`): the Store key (Mini's
/// `storeTag` of the Store identity, the genesis seed at the Store's root), the
/// app and the generation. Two Stores on one host never name the same unit, a
/// world restored or forked to another root included.
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

/// The slice tree is derived by systemd from dashes, and these three functions
/// are the only place its names are written:
///
/// ```text
/// s{store}-{prefix}-grains.slice                  everything (supervisors sit here)
///   s{store}-{prefix}-grains-{S|M|L}.slice        one class
///     s{store}-{prefix}-grains-{S|M|L}-a{app}.slice   one app: its resident grain
/// ```
///
/// A drop-in on the class slice bounds the class in aggregate; a prefix drop-in
/// `s{store}-{prefix}-grains-{S|M|L}-.slice.d/` bounds each app of that class
/// (a `CPUQuota` there is per app, i.e. per resident grain unit, not shared).
/// The class is the one `set-cgroup` recorded from the app's declared size
/// class; there is no class-less app slice.
pub fn grains_slice(prefix: &str, store: &str) -> String {
    format!("s{store}-{prefix}-grains.slice")
}

pub fn class_slice(prefix: &str, store: &str, class: &SizeClass) -> String {
    format!("s{store}-{prefix}-grains-{}.slice", class.name)
}

pub fn app_slice(prefix: &str, store: &str, class: &SizeClass, app: &str) -> String {
    format!("s{store}-{prefix}-grains-{}-a{app}.slice", class.name)
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
    /// The physical bubblewrap that creates each resident's user namespace (and
    /// sandboxes its app): one of `namespace_identity::PHYSICAL_BWRAPS`, pinned.
    pub bwrap: PathBuf,
    pub bwrap_sha256: String,
    pub ingest_helper: PathBuf,
    /// Operator-selected physical intake budget; never accepted in an Ingest request.
    #[serde(default)]
    pub import_profile: Option<String>,
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
    if fs::canonicalize(&root).ctx("resolve", &root)? != root {
        return Err(invalid("SPK root traverses a symlink"));
    }
    for entry in root.ancestors() {
        let metadata=fs::symlink_metadata(&entry).ctx("inspect", &entry)?;
        if !metadata.is_dir() || !(crate::os::root_owner(metadata.uid()) || metadata.uid()==unsafe{libc::geteuid()}) || metadata.mode()&0o022!=0 {
            return Err(invalid(format!("SPK root custody differs: {}",entry.display())));
        }
    }
    for (path,mode) in [(root,0o755),(packages.as_path(),0o755),(inbox.as_path(),0o700)] {
        let metadata=fs::symlink_metadata(&path).ctx("inspect", &path)?;
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

fn ingest_arguments(root: Option<&Path>, host: &Path, host_sha: &str, inbox: &Path, uid: u32, profile: crate::materialize::ImportProfile) -> io::Result<Vec<String>> {
    let (_,expected_inbox)=spk_namespace_paths(root)?;
    if inbox.parent()!=Some(expected_inbox.as_path()) {
        return Err(invalid("ingest package is outside selected SPK inbox"));
    }
    let mut args=Vec::new();
    if let Some(root)=root {
        args.extend(["--root".to_owned(),root.to_str().ok_or_else(||invalid("SPK root path"))?.to_owned()]);
    }
    if profile != crate::materialize::ImportProfile::Standard {
        args.extend(["--import-profile".to_owned(), profile.as_str().to_owned()]);
    }
    args.extend([host.to_str().ok_or_else(||invalid("Host path"))?.to_owned(),host_sha.to_owned(),
        inbox.to_str().ok_or_else(||invalid("inbox path"))?.to_owned(),uid.to_string()]);
    Ok(args)
}

fn import_profile(config: &BrokerConfig) -> io::Result<crate::materialize::ImportProfile> {
    config.import_profile.as_deref().unwrap_or("standard-v1").parse()
        .map_err(|_| invalid("unknown operator importProfile"))
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
        .open(&path).ctx("open", &path)?;
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

/// HOT-PATH 2g: the digest of a pinned executable, computed ONCE per file identity per process.
/// The 159 MB spk-host image was hashed on every broker config load, adoption pin and runtime
/// status (five times across one STOP). The key is the file's full identity (device, inode, size,
/// mtime, ctime): a replaced, rewritten or touched image is a new key and is hashed again; the
/// cached value is the DIGEST, never the verdict, so a different pin against the same bytes is still
/// compared. `PINNED_HASHES` counts the hashes taken (the test's witness).
static PINNED_DIGESTS: std::sync::Mutex<Option<std::collections::HashMap<(u64, u64, u64, i64, i64, i64, i64), String>>> =
    std::sync::Mutex::new(None);
static PINNED_HASHES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

fn pinned_digest(path: &Path, meta: &fs::Metadata) -> io::Result<String> {
    let key = (meta.dev(), meta.ino(), meta.size(), meta.mtime(), meta.mtime_nsec(), meta.ctime(), meta.ctime_nsec());
    if let Some(known) = PINNED_DIGESTS.lock().ok().and_then(|cache| cache.as_ref().and_then(|c| c.get(&key).cloned())) {
        return Ok(known);
    }
    let digest = file_sha256(&mut File::open(&path).ctx("open", &path)?)?;
    PINNED_HASHES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    // The identity must still be the one hashed: a file replaced mid-read is not remembered.
    let after = fs::symlink_metadata(&path).ctx("inspect", &path)?;
    if (after.dev(), after.ino(), after.size(), after.mtime(), after.mtime_nsec(), after.ctime(), after.ctime_nsec()) == key {
        if let Ok(mut cache) = PINNED_DIGESTS.lock() {
            cache.get_or_insert_with(Default::default).insert(key, digest.clone());
        }
    }
    Ok(digest)
}

fn pinned_root_executable(path: &Path, sha: Option<&str>) -> io::Result<()> {
    let meta = fs::symlink_metadata(&path).ctx("inspect", &path)?;
    if !path.is_absolute() || !meta.is_file() || !(crate::os::root_owner(meta.uid()) || meta.uid()==unsafe{libc::geteuid()}) || meta.mode() & 0o022 != 0 {
        return Err(invalid(format!(
            "{} must be a root-owned executable",
            path.display()
        )));
    }
    if let Some(sha) = sha {
        if !hex64(sha) || pinned_digest(path, &meta)? != sha {
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
            fs::create_dir(&path).ctx("create directory", &path)?;
            fs::set_permissions(path, fs::Permissions::from_mode(mode)).ctx("set permissions", &path)?;
        }
        Err(error) => return Err(error),
        Ok(_) => {}
    }
    let meta = fs::symlink_metadata(&path).ctx("inspect", &path)?;
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
/// the volume helper writes into every witness.

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
            fs::set_permissions(path, fs::Permissions::from_mode(mode)).ctx("set permissions", &path)?;
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
    let _ = fs::remove_file(&temp).ctx("remove", &temp);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(mode)
        .open(&temp).ctx("open", &temp)?;
    // The broker's umask is 077; unit files are meant to be world-readable.
    file.set_permissions(fs::Permissions::from_mode(mode))?;
    file.write_all(text.as_bytes())?;
    file.sync_all()?;
    fs::rename(&temp, path).ctx("rename", &temp)?;
    File::open(&parent).ctx("open", &parent)?.sync_all()?;
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
        import_profile(&config)?;
        if config.protocol != "mini-spk-broker-config-v3"
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
        crate::namespace_identity::pinned_bwrap(&config.bwrap, &config.bwrap_sha256)?;
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
            let meta = fs::symlink_metadata(&prefix).ctx("inspect", &prefix)?;
            if !meta.is_dir() || !(crate::os::root_owner(meta.uid()) || meta.uid()==unsafe{libc::geteuid()}) || meta.mode() & 0o022 != 0 {
                return Err(invalid(format!(
                    "grains root ancestor {} is not root-owned",
                    prefix.display()
                )));
            }
        }
        let root=fs::symlink_metadata(&config.grains_root).ctx("inspect", &config.grains_root)?;
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
            .open(broker.join("broker.log")).ctx("open", &(broker.join("broker.log")))?;
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

    /// The grains slice, rendered at startup; supervisor instances are
    /// rendered per app (`render_store_supervisor`), the names `OnFailure=` uses.
    fn render_static(&self) -> io::Result<()> {
        let prefix = &self.config.unit_prefix;
        let store = &self.config.store;
        let slice = "# rendered by mini-spk-broker\n[Unit]\nDescription=Mini SPK grains\n\n\
             [Slice]\nCPUWeight=50\nIOWeight=50\n";
        write_operator_text(
            &crate::os::runtime_units().join(grains_slice(prefix, store)),
            slice,
            0o644,
            true,
        )?;
        for class in CLASSES {
            write_operator_text(
                &crate::os::runtime_units().join(class_slice(prefix, store, class)),
                &format!(
                    "# rendered by mini-spk-broker class={c}\n[Unit]\nDescription=Mini SPK grains class {c}\n",
                    c = class.name
                ),
                0o644,
                true,
            )?;
        }
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

    /// Resident units installed for this app (any state).
    fn app_units_installed(&self, store: &str, app: &str) -> io::Result<Vec<String>> {
        let mut installed = Vec::new();
        for entry in fs::read_dir(self.broker_dir().join("units")).ctx("list", &(self.broker_dir().join("units")))? {
            let name = entry?.file_name().to_string_lossy().into_owned();
            let Ok((unit_store, unit_app, _)) = Self::check_resident_unit_name(&name) else {
                continue;
            };
            if unit_app == app
                && unit_store == store
                && self.unit_store(&name)?.as_deref() == Some(store)
            {
                installed.push(name);
            }
        }
        Ok(installed)
    }

    fn app_units_active(&self, store: &str, app: &str) -> io::Result<Vec<String>> {
        let mut active = Vec::new();
        for entry in fs::read_dir(self.broker_dir().join("units")).ctx("list", &(self.broker_dir().join("units")))? {
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
                        fs::create_dir(&dir).ctx("create directory", &dir)?;
                        std::os::unix::fs::chown(
                            &dir,
                            Some(self.operator_uid),
                            Some(self.operator_gid),
                        )?;
                        fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).ctx("set permissions", &dir)?;
                    }
                    Err(error) => return Err(error),
                    Ok(_) => {}
                }
                let meta = fs::symlink_metadata(&dir).ctx("inspect", &dir)?;
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
                for entry in fs::read_dir(self.broker_dir().join("placements")).ctx("list", &(self.broker_dir().join("placements")))? {
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
                    if existing != class.name && !self.app_units_installed(&store, &app)?.is_empty() {
                        return Err(invalid("class change refused once a unit is installed: the unit names its class slice"));
                    }
                }
                let slice = app_slice(&self.config.unit_prefix, &store, &class, &app);
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
                    let source = open_operator_file(
                        self.root(),
                        &[&store, "host", "packages", &package, "package.spk"],
                        self.operator_uid,
                    )?;
                    let profile = import_profile(&self.config)?;
                    let bound = profile.limits().raw_bytes;
                    let source_length = source.metadata()?.len();
                    if source_length > bound {
                        return Err(invalid("staged package exceeds bound"));
                    }
                    let inbox = private_inbox.join(format!("grain-{sha256}.spk"));
                    let temp = private_inbox.join(format!(".grain-{sha256}.broker"));
                    let _ = fs::remove_file(&temp).ctx("remove", &temp);
                    let mut out = OpenOptions::new()
                        .write(true)
                        .create_new(true)
                        .mode(0o600)
                        .open(&temp).ctx("open", &temp)?;
                    let copied = io::copy(&mut source.take(bound + 1), &mut out)?;
                    if copied > bound || copied != source_length {
                        let _ = fs::remove_file(&temp).ctx("remove", &temp);
                        return Err(invalid("staged package changed or exceeds import profile bound"));
                    }
                    out.sync_all()?;
                    if file_sha256(&mut File::open(&temp).ctx("open", &temp)?)? != sha256 {
                        let _ = fs::remove_file(&temp).ctx("remove", &temp);
                        return Err(invalid("staged package differs from its SHA-256"));
                    }
                    fs::rename(&temp, &inbox).ctx("rename", &temp)?;
                    let arguments=ingest_arguments(self.config.spk_root.as_deref(),&runtime.spk_host,
                        &runtime.spk_host_sha256,&inbox,placement.app_uid,profile)?;
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
                let unit_class = class(
                    placement.class.as_deref().ok_or_else(|| invalid("set-cgroup must precede install-unit"))?,
                )?;
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
                     MINI_SPK_GRAINS_ROOT={root} MINI_SPK_STORE={store} MINI_SPK_UNIT={unit} MINI_SPK_BROKER_SOCKET={broker_socket} \
                     MINI_SPK_BWRAP={bwrap} MINI_SPK_BWRAP_SHA256={bwrap_sha256}\n\
                     ExecStart={spk} resident-bootstrap {config}\n\
                     AmbientCapabilities=\n\
                     NoNewPrivileges=no\n\
                     KillMode=control-group\nUMask=0077\n",
                    supervisor = supervisor_unit(prefix, &store, &app),
                    operator_uid = self.operator_uid,
                    operator_gid = self.operator_gid,
                    slice = app_slice(prefix, &store, &unit_class, &app),
                    uid = placement.app_uid,
                    gid = placement.app_gid,
                    root = self.root().display(),
                    broker_socket = socket_path(self.root(), self.config.broker_socket.as_deref())?.display(),
                    spk = runtime.spk_host.display(),
                    bwrap = self.config.bwrap.display(),
                    bwrap_sha256 = self.config.bwrap_sha256,
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
                    fs::create_dir_all(&drop_dir).ctx("create directory", &drop_dir)?;
                    fs::set_permissions(&drop_dir,fs::Permissions::from_mode(0o755)).ctx("set permissions", &drop_dir)?;
                    write_operator_text(&drop_dir.join("10-native-visibility.conf"),&visibility,0o644,false)?;
                }
                systemctl(&["daemon-reload"])?;
                self.save_unit_runtime(&unit, &runtime)?;
                Ok(
                    json!({"unit":unit,"slice":app_slice(prefix, &store, &unit_class, &app),"spkHostSha256":runtime.spk_host_sha256}),
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
            Err(error) => {
                broker.log(&json!({
                    "at":SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0),
                    "ok":false,"error":format!("peer credentials unavailable: {error}"),
                }));
                continue;
            }
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
    /// HOT-PATH 2g: one hash per image identity; a rewritten image is a new identity and is hashed
    /// (and refused against the old pin); a wrong pin against cached bytes is refused.
    #[test]
    fn pinned_executable_is_hashed_once_per_identity() {
        use std::os::unix::fs::PermissionsExt;
        let dir = std::env::temp_dir().join(format!("spk-pinned-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir(&dir).unwrap();
        let image = dir.join("spk-host");
        std::fs::write(&image, b"candidate image bytes v1").unwrap();
        std::fs::set_permissions(&image, std::fs::Permissions::from_mode(0o700)).unwrap();
        let pin = format!("{:x}", super::Sha256::digest(b"candidate image bytes v1"));
        let before = super::PINNED_HASHES.load(std::sync::atomic::Ordering::Relaxed);
        super::pinned_root_executable(&image, Some(&pin)).unwrap();
        super::pinned_root_executable(&image, Some(&pin)).unwrap();
        super::pinned_root_executable(&image, Some(&pin)).unwrap();
        assert_eq!(super::PINNED_HASHES.load(std::sync::atomic::Ordering::Relaxed) - before, 1, "three checks, one hash");
        let wrong = format!("{:x}", super::Sha256::digest(b"another pin"));
        assert!(super::pinned_root_executable(&image, Some(&wrong)).is_err(), "the verdict is never cached");
        std::thread::sleep(std::time::Duration::from_millis(20));
        std::fs::write(&image, b"candidate image bytes v2 (longer)").unwrap();
        assert!(super::pinned_root_executable(&image, Some(&pin)).is_err(), "a rewritten image is hashed again and refused");
        assert_eq!(super::PINNED_HASHES.load(std::sync::atomic::Ordering::Relaxed) - before, 2);
        let _ = std::fs::remove_dir_all(&dir);
    }
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
        assert!(ingest_arguments(None,Path::new("/operator/spk-host"),"hash",Path::new("/var/lib/minidregg/spk/inbox/grain-package.spk"),165536,crate::materialize::ImportProfile::Standard).is_err());
    }

    #[test]
    fn spk_namespace_explicit_root_binds_helper_and_both_paths() {
        let root=Path::new("/var/lib/mini-bigstep-hbox-r2/spk");
        let (packages,inbox)=spk_namespace_paths(Some(root)).unwrap();
        assert_eq!(packages,root.join("packages"));
        assert_eq!(inbox,root.join("inbox"));
        let args=ingest_arguments(Some(root),Path::new("/root/candidate/spk-host"),"hash",
            &inbox.join("grain-package.spk"),64010,crate::materialize::ImportProfile::Standard).unwrap();
        assert_eq!(&args[..2],["--root","/var/lib/mini-bigstep-hbox-r2/spk"]);
        assert_eq!(args[4],"/var/lib/mini-bigstep-hbox-r2/spk/inbox/grain-package.spk");
        assert!(ingest_arguments(Some(root),Path::new("/root/spk-host"),"hash",
            Path::new("/var/lib/minidregg/spk/inbox/package.spk"),64010,crate::materialize::ImportProfile::Standard).is_err());
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
            r#"{"verb":"ingest","store":"0123456789abcdef","app":"7","sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa","importProfile":"operator-appliance-v1"}"#
        ).is_err());
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
    fn operator_import_profile_reaches_helper_without_changing_package_coordinates() {
        let root = Path::new("/var/lib/mini-spk-worlds/0123456789abcdef/spk");
        let package = root.join("inbox/package.spk");
        let args = ingest_arguments(Some(root), Path::new("/operator/spk-host"), "pin",
            &package, 64010, crate::materialize::ImportProfile::OperatorAppliance).unwrap();
        assert_eq!(&args[2..4], ["--import-profile", "operator-appliance-v1"]);
        assert_eq!(args[4], "/operator/spk-host");
        assert_eq!(args[6], package.to_str().unwrap());
        assert_eq!(args[7], "64010");
        assert!("unlimited".parse::<crate::materialize::ImportProfile>().is_err());
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
            app_slice("mini", "0123456789abcdef", &class("M").unwrap(), "7701"),
            "s0123456789abcdef-mini-grains-M-a7701.slice"
        );
    }

    /// systemd nests a slice under the slice named by dropping its last dash
    /// segment.
    fn systemd_parent(slice: &str) -> String {
        let stem = slice.strip_suffix(".slice").unwrap();
        format!("{}.slice", stem.rsplit_once('-').unwrap().0)
    }

    /// Mirrors Kernel `ApplicationLifecycleCompletionReport.controlGroupBound` (323): the longest
    /// control group a resident unit can have, built from the real naming functions at their
    /// maximum components (10-digit uid, 16-hex Store tag, u64 app and generation: 20 digits).
    #[test]
    fn resident_control_group_stays_within_the_lean_bound() {
        let (uid, st, big) = ("4294967295", "0123456789abcdef", "18446744073709551615");
        let longest = CLASSES.iter().map(|c| {
            let unit = format!("mini-spk-s{st}-a{big}-g{big}.service");
            assert!(parse_resident_unit(&unit).is_some(), "the unit is a resident unit");
            let path = format!("/user.slice/user-{uid}.slice/user@{uid}.service/s{st}.slice/s{st}-mini.slice/{}/{}/{}/{unit}",
                grains_slice("mini", st), class_slice("mini", st, c), app_slice("mini", st, c, big));
            assert!(path.split('/').all(|part| part.len() <= 255), "NAME_MAX");
            path.len()
        }).max().unwrap();
        assert_eq!(longest, 323);
        assert!(longest < 4096, "the control-group cap");
        // the 260-byte group observed on dregg-build (app 9101, generation 2, uid 1000)
        let seen = format!("/user.slice/user-1000.slice/user@1000.service/s{st}.slice/s{st}-mini.slice/{}/{}/{}/mini-spk-s{st}-a9101-g2.service",
            grains_slice("mini", st), class_slice("mini", st, &class("S").unwrap()), app_slice("mini", st, &class("S").unwrap(), "9101"));
        assert_eq!(seen.len(), 260);
    }
    /// The u64 poles of a coordinate: a namespace id (at least 2^63) and the largest u64 are admitted;
    /// 2^64, a 21-digit string, a leading zero and zero are refused.
    #[test]
    fn coordinates_admit_exactly_the_positive_u64() {
        for good in ["1", "999999999999999999", "13827490942341725565", "18446744073709551615"] { assert!(decimal(good), "{good}"); }
        for bad in ["0", "01", "18446744073709551616", "100000000000000000000", "123456789012345678901", "", "-1", "1a"] { assert!(!decimal(bad), "{bad}"); }
        assert!(parse_resident_unit("mini-spk-s0123456789abcdef-a13827490942341725565-g18446744073709551615.service").is_some());
        assert!(parse_resident_unit("mini-spk-s0123456789abcdef-a18446744073709551616-g1.service").is_none());
    }
    #[test]
    fn grain_class_slices_nest_by_class() {
        let (p, st) = ("mini", "0123456789abcdef");
        for (name, mem) in [("S", "512M"), ("M", "1G"), ("L", "2G")] {
            // a small grain lands in S, a large in L: the class is the one the
            // size class table names, read through `class`, never a default
            let c = class(name).unwrap();
            assert_eq!(c.memory_max, mem);
            let app = app_slice(p, st, &c, "7701");
            assert_eq!(app, format!("s{st}-mini-grains-{name}-a7701.slice"));
            assert_eq!(systemd_parent(&app), class_slice(p, st, &c));
            assert_eq!(class_slice(p, st, &c), format!("s{st}-mini-grains-{name}.slice"));
            assert_eq!(systemd_parent(&class_slice(p, st, &c)), grains_slice(p, st));
        }
        // every class has its own slice, so no two classes share a quota
        let mut names: Vec<_> = CLASSES.iter().map(|c| app_slice(p, st, c, "1")).collect();
        names.sort();
        names.dedup();
        assert_eq!(names.len(), CLASSES.len());
        // there is no class-less size: an unknown class is refused, not defaulted
        assert!(class("").is_err());
        assert!(class("l").is_err());
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
