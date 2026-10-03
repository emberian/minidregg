//! `mini-spk-broker`: the one root-owned surface a grain host needs.
//!
//! The Store operator (`mini`) runs `spk-host grain` and every resident; it
//! holds no root. The broker accepts a fixed set of typed requests on a
//! `0660 root:<operator>` Unix socket from exactly the operator UID and does
//! the root-only work: it allocates app UIDs from its own pool, renders unit
//! and slice text from its own templates (the client passes parameters, never
//! text), publishes package images, creates/attests loop-mounted volumes, and
//! starts/stops the units it installed. Every path it touches is below its
//! configured grains root; every request is logged with the peer's credentials.

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

pub const SOCKET: &str = "/run/mini-spk-broker.sock";
const MAX_REQUEST: u64 = 16 * 1024;
const MAX_CONFIG: u64 = 64 * 1024;
const RUNTIME_UNITS: &str = "/run/systemd/system";
const PACKAGE_STORE: &str = "/var/lib/minidregg/spk/packages";
const INBOX: &str = "/var/lib/minidregg/spk/inbox";

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
/// `ApplicationLifecycleResidentProfile.processIdentity`), so it carries no
/// Store identity; the broker refuses a second Store's claim on a name.
pub fn resident_unit(app: &str, generation: &str) -> String {
    format!("mini-spk-a{app}-g{generation}.service")
}

/// Volume, mount and witness names carry the Store key: two Stores on one
/// host never adopt each other's /var.
pub fn volume_name(store: &str, app: &str) -> String {
    format!("{store}-{app}")
}

pub fn app_slice(prefix: &str, store: &str, app: &str) -> String {
    format!("{prefix}-grains-s{store}a{app}.slice")
}

pub fn supervisor_unit(prefix: &str, store: &str, app: &str) -> String {
    format!("{prefix}-spk-supervisor@{store}-{app}.service")
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct BrokerConfig {
    pub protocol: String,
    pub grains_root: PathBuf,
    /// Explicit physical package namespace; absent preserves the installed host default.
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
    let Some(root) = root else {
        return Ok((PathBuf::from(PACKAGE_STORE), PathBuf::from(INBOX)));
    };
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
    let Some(root)=root else { return Ok(()); };
    let (packages,inbox)=spk_namespace_paths(Some(root))?;
    if fs::canonicalize(root)? != root {
        return Err(invalid("SPK root traverses a symlink"));
    }
    for entry in root.ancestors() {
        let metadata=fs::symlink_metadata(entry)?;
        if !metadata.is_dir() || metadata.uid()!=0 || metadata.mode()&0o022!=0 {
            return Err(invalid(format!("SPK root custody differs: {}",entry.display())));
        }
    }
    for (path,mode) in [(root,0o755),(packages.as_path(),0o755),(inbox.as_path(),0o700)] {
        let metadata=fs::symlink_metadata(path)?;
        if !metadata.is_dir() || metadata.uid()!=0 || metadata.mode()&0o777!=mode {
            return Err(invalid(format!("SPK namespace directory custody differs: {}",path.display())));
        }
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
        None=>PathBuf::from(PACKAGE_STORE), // Older brokers implement only this fixed physical namespace.
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
    /// Snapshot every volume into `GRAINS/backups/<time>/` (root-only); the
    /// reply is the backup manifest. `mini-backup` runs the same code as root.
    Backup {},
}

pub fn call(request: &Request) -> io::Result<Value> {
    endpoint::call_legacy(request)
}
pub fn socket_path(root: &Path, socket: Option<&Path>) -> io::Result<PathBuf> {
    endpoint::resolve(root, socket)
}
pub fn call_at(root: &Path, socket: Option<&Path>, request: &Request) -> io::Result<Value> {
    endpoint::call_at(root, socket, request)
}

fn read_private_root(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() || meta.uid() != 0 || meta.mode() & 0o077 != 0 || meta.len() > max {
        return Err(invalid(format!("{} must be root 0600", path.display())));
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
    if !path.is_absolute() || !meta.is_file() || meta.uid() != 0 || meta.mode() & 0o022 != 0 {
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
fn root_dir(path: &Path, mode: u32) -> io::Result<()> {
    match fs::symlink_metadata(path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            fs::create_dir(path)?;
            fs::set_permissions(path, fs::Permissions::from_mode(mode))?;
        }
        Err(error) => return Err(error),
        Ok(_) => {}
    }
    let meta = fs::symlink_metadata(path)?;
    if !meta.is_dir() || meta.uid() != 0 || meta.gid() != 0 || meta.mode() & 0o7777 != mode {
        return Err(invalid(format!("{} must be root {mode:o}", path.display())));
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
fn host_identity() -> io::Result<(String, String)> {
    let text = String::from_utf8(read_private_root(
        Path::new("/etc/minidregg/spk/host-identity"),
        4096,
    )?)
    .map_err(|_| invalid("host identity is not UTF-8"))?;
    let lines: Vec<_> = text.lines().collect();
    match lines.as_slice() {
        [deployment, host] => {
            let deployment = deployment
                .strip_prefix("deployment_id=")
                .filter(|v| hex64(v))
                .ok_or_else(|| invalid("deployment identity malformed"))?;
            let host = host
                .strip_prefix("host_id=")
                .filter(|v| hex64(v))
                .ok_or_else(|| invalid("host identity malformed"))?;
            Ok((deployment.to_owned(), host.to_owned()))
        }
        _ => Err(invalid("host identity shape refused")),
    }
}

fn systemctl(args: &[&str]) -> io::Result<String> {
    let output = Command::new("/usr/bin/systemctl")
        .arg("--system")
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
fn write_root_text(path: &Path, text: &str, mode: u32, replace: bool) -> io::Result<bool> {
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
            serde_json::from_slice(&read_private_root(config_path, MAX_CONFIG)?)?;
        if config.protocol != "mini-spk-broker-config-v1"
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
        validate_spk_namespace(config.spk_root.as_deref())?;
        pinned_root_executable(&config.spk_host, Some(&config.spk_host_sha256))?;
        pinned_root_executable(&config.ingest_helper, None)?;
        pinned_root_executable(&config.volume_helper, None)?;
        let user = CString::new(config.operator_user.as_str()).map_err(|_| invalid("NUL"))?;
        let entry = unsafe { libc::getpwnam(user.as_ptr()) };
        if entry.is_null() {
            return Err(invalid("operator user absent"));
        }
        let (operator_uid, operator_gid) = unsafe { ((*entry).pw_uid, (*entry).pw_gid) };
        if operator_uid == 0 || operator_gid == 0 || config.app_uids.contains(&operator_uid) {
            return Err(invalid(
                "operator must be an unprivileged user outside the app pool",
            ));
        }
        home_visibility::validate(&config.resident_home_read_only_paths,operator_uid)?;
        for uid in &config.app_uids {
            if unsafe { libc::getpwuid(*uid) }.is_null() {
                return Err(invalid(format!("app pool UID {uid} has no account")));
            }
        }
        // Every ancestor of the grains root is root-owned and not group or
        // world writable: nothing below it can be swapped by a rename.
        let mut prefix = PathBuf::from("/");
        for part in config.grains_root.components().skip(1) {
            prefix.push(part);
            if prefix == config.grains_root {
                break;
            }
            let meta = fs::symlink_metadata(&prefix)?;
            if !meta.is_dir() || meta.uid() != 0 || meta.mode() & 0o022 != 0 {
                return Err(invalid(format!(
                    "grains root ancestor {} is not root-owned",
                    prefix.display()
                )));
            }
        }
        root_dir(&config.grains_root, 0o755)?;
        let broker = config.grains_root.join("broker");
        root_dir(&broker, 0o700)?;
        root_dir(&broker.join("placements"), 0o700)?;
        root_dir(&broker.join("units"), 0o700)?;
        root_dir(&broker.join("runtimes"), 0o700)?;
        root_dir(&broker.join("unit-runtimes"), 0o700)?;
        volume_custody::recover(&config.grains_root)?;
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
        let slice = "# rendered by mini-spk-broker\n[Unit]\nDescription=Mini SPK grains\n\n\
             [Slice]\nCPUWeight=50\nIOWeight=50\n";
        write_root_text(
            &Path::new(RUNTIME_UNITS).join(format!("{prefix}-grains.slice")),
            slice,
            0o644,
            true,
        )?;
        let supervisor = format!(
            "# rendered by mini-spk-broker\n[Unit]\nDescription=Mini SPK grain supervisor %i\n\
             StartLimitIntervalSec=1800\nStartLimitBurst=3\n\n[Service]\nType=exec\n\
             User={user}\nGroup={group}\nSlice={prefix}-grains.slice\n\
             ExecStart={spk} grain supervise-instance {root} %i\n\
             Restart=on-failure\nRestartSec=30\nRestartPreventExitStatus=3\n\
             NoNewPrivileges=yes\nUMask=0077\nPrivateTmp=yes\n",
            user = self.config.operator_user,
            group = self.operator_gid,
            spk = self.config.spk_host.display(),
            root = self.root().display(),
        );
        write_root_text(
            &Path::new(RUNTIME_UNITS).join(format!("{prefix}-spk-supervisor@.service")),
            &supervisor,
            0o644,
            true,
        )?;
        self.render_adopted_supervisors()?;
        systemctl(&["daemon-reload"])?;
        Ok(())
    }

    fn placement(&self, store: &str, app: &str) -> io::Result<Placement> {
        let bytes = read_private_root(&self.placement_path(store, app), MAX_CONFIG)
            .map_err(|_| invalid(format!("app {app} of store {store} is not placed")))?;
        let placement: Placement = serde_json::from_slice(&bytes)?;
        if placement.protocol != "mini-spk-broker-placement-v1"
            || placement.store != store
            || placement.app != app
        {
            return Err(invalid("placement record differs from its name"));
        }
        Ok(placement)
    }

    fn save_placement(&self, placement: &Placement) -> io::Result<()> {
        write_root_text(
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

    fn check_resident_unit_name(unit: &str) -> io::Result<(String, String)> {
        let rest = unit
            .strip_prefix("mini-spk-a")
            .and_then(|rest| rest.strip_suffix(".service"))
            .ok_or_else(|| invalid("not a resident unit name"))?;
        let (app, generation) = rest
            .split_once("-g")
            .ok_or_else(|| invalid("not a resident unit name"))?;
        if !decimal(app) || !decimal(generation) || resident_unit(app, generation) != unit {
            return Err(invalid("resident unit name refused"));
        }
        Ok((app.to_owned(), generation.to_owned()))
    }

    fn app_units_active(&self, store: &str, app: &str) -> io::Result<Vec<String>> {
        let mut active = Vec::new();
        for entry in fs::read_dir(self.broker_dir().join("units"))? {
            let name = entry?.file_name().to_string_lossy().into_owned();
            let Ok((unit_app, _)) = Self::check_resident_unit_name(&name) else {
                continue;
            };
            if unit_app == app && self.unit_store(&name)?.as_deref() == Some(store) {
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
        // A prior copy may have returned after an uncertain thaw. Reconcile
        // retained freeze custody before admitting another physical action.
        volume_custody::recover(self.root())?;
        match request {
            Request::Identify {} => Ok(json!({"protocol":"mini-spk-broker-identity-v1",
                "grainsRoot":self.root(),"brokerSocket":socket_path(self.root(), self.config.broker_socket.as_deref())?,
                "packageStore":spk_namespace_paths(self.config.spk_root.as_deref())?.0})),
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
                let (deployment_id, host_id) = host_identity()?;
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
                        serde_json::from_slice(&read_private_root(&path, MAX_CONFIG)?)?;
                    bound.push(placement.app_uid);
                }
                let uid = self
                    .config
                    .app_uids
                    .iter()
                    .copied()
                    .find(|uid| !bound.contains(uid))
                    .ok_or_else(|| invalid("app UID pool exhausted"))?;
                let entry = unsafe { libc::getpwuid(uid) };
                if entry.is_null() {
                    return Err(invalid("app UID has no account"));
                }
                let gid = unsafe { (*entry).pw_gid };
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
                write_root_text(&Path::new(RUNTIME_UNITS).join(&slice), &text, 0o644, true)?;
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
            Request::MountVolume {
                store,
                app,
                volume_id,
                import_sha256,
            } => {
                Self::check_coordinates(&store, &app)?;
                if !hex64(&volume_id) {
                    return Err(invalid("volume id refused"));
                }
                let placement = self.placement(&store, &app)?;
                let class = class(
                    placement
                        .class
                        .as_deref()
                        .ok_or_else(|| invalid("set-cgroup must precede mount-volume"))?,
                )?;
                let root = self
                    .root()
                    .to_str()
                    .ok_or_else(|| invalid("path"))?
                    .to_owned();
                let uid = placement.app_uid.to_string();
                let mib = class.volume_mib.to_string();
                let name = volume_name(&store, &app);
                let registration = self.root().join("volumes").join(format!("{name}.conf"));
                if fs::symlink_metadata(&registration).is_err() {
                    match import_sha256 {
                        None => {
                            helper(
                                &self.config.volume_helper,
                                &[
                                    "--root", &root, "create", &store, &app, &uid, &mib, &volume_id,
                                ],
                            )?;
                        }
                        Some(sha) => {
                            if !hex64(&sha) {
                                return Err(invalid("import SHA-256 refused"));
                            }
                            let file = format!("{sha}.ext4");
                            let mut source = open_operator_file(
                                self.root(),
                                &[&store, "imports", &file],
                                self.operator_uid,
                            )?;
                            if source.metadata()?.len() != class.volume_mib * 1024 * 1024 {
                                return Err(invalid("imported image size differs from the class"));
                            }
                            let staging =
                                self.root().join("volumes").join(format!(".import-{name}"));
                            let _ = fs::remove_file(&staging);
                            let mut out = OpenOptions::new()
                                .write(true)
                                .create_new(true)
                                .mode(0o600)
                                .open(&staging)?;
                            io::copy(&mut source, &mut out)?;
                            out.sync_all()?;
                            if file_sha256(&mut File::open(&staging)?)? != sha {
                                let _ = fs::remove_file(&staging);
                                return Err(invalid("imported image differs from its SHA-256"));
                            }
                            let staging_text = staging.to_str().ok_or_else(|| invalid("path"))?;
                            helper(
                                &self.config.volume_helper,
                                &[
                                    "--root",
                                    &root,
                                    "create-from",
                                    &store,
                                    &app,
                                    &uid,
                                    &mib,
                                    &volume_id,
                                    staging_text,
                                ],
                            )?;
                        }
                    }
                } else {
                    let text = fs::read_to_string(&registration)?;
                    if !text.lines().any(|l| l == format!("volume_id={volume_id}"))
                        || !text.lines().any(|l| l == format!("app_uid={uid}"))
                    {
                        return Err(invalid(
                            "volume registration differs from placement or Mini volume ID",
                        ));
                    }
                }
                helper(
                    &self.config.volume_helper,
                    &["--root", &root, "attest", &store, &app],
                )?;
                Ok(
                    json!({"name":name,"mount":self.root().join("vars").join(&name),
                    "witness":self.root().join("attest").join(format!("{name}.witness")),
                    "appUid":placement.app_uid,"sizeMib":class.volume_mib}),
                )
            }
            Request::Unmount { store, app } => {
                Self::check_coordinates(&store, &app)?;
                let active = self.app_units_active(&store, &app)?;
                if !active.is_empty() {
                    return Err(invalid(format!(
                        "unmount refused: {} active",
                        active.join(",")
                    )));
                }
                let mount = self.root().join("vars").join(volume_name(&store, &app));
                helper(
                    Path::new("/usr/bin/umount"),
                    &[mount.to_str().ok_or_else(|| invalid("path"))?],
                )?;
                Ok(json!({"unmounted":mount}))
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
                let unit = resident_unit(&app, &generation);
                if let Some(owner) = self.unit_store(&unit)? {
                    if owner != store {
                        return Err(invalid(format!(
                            "unit {unit} belongs to store {owner}; Mini's resident unit name \
                             carries no Store identity (K-SPK)"
                        )));
                    }
                } else if fs::symlink_metadata(Path::new(RUNTIME_UNITS).join(&unit)).is_ok()
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
                let name = volume_name(&store, &app);
                let text = format!(
                    "# rendered by mini-spk-broker store={store} app={app} generation={generation}\n\
                     [Unit]\nDescription=Mini SPK resident app {app} generation {generation} store {store}\n\
                     OnFailure={supervisor}\n\n[Service]\nType=exec\nUser={user}\nGroup={group}\n\
                     Slice={slice}\n\
                     Environment=MINI_SPK_APP_UID={uid} MINI_SPK_APP_GID={gid} \
                     MINI_SPK_GRAINS_ROOT={root} MINI_SPK_STORE={store} MINI_SPK_BROKER_SOCKET={broker_socket}\n\
                     ExecStart={spk} resident-run {config}\n\
                     AmbientCapabilities=CAP_SETUID CAP_SETGID\n\
                     CapabilityBoundingSet=CAP_SETUID CAP_SETGID\nNoNewPrivileges=yes\n\
                     KillMode=control-group\nUMask=0077\nProtectSystem=strict\n\
                     ReadWritePaths={root}/{store} {root}/vars/{name}\nProtectHome=yes\nPrivateTmp=yes\n",
                    supervisor = supervisor_unit(prefix, &store, &app),
                    user = self.config.operator_user,
                    group = self.operator_gid,
                    slice = app_slice(prefix, &store, &app),
                    uid = placement.app_uid,
                    gid = placement.app_gid,
                    root = self.root().display(),
                    broker_socket = socket_path(self.root(), self.config.broker_socket.as_deref())?.display(),
                    spk = runtime.spk_host.display(),
                    config = config.display(),
                );
                self.render_store_supervisor(&store, &app, &runtime)?;
                write_root_text(
                    &self.unit_tag_path(&unit),
                    &format!("{store}\n"),
                    0o600,
                    false,
                )?;
                write_root_text(&Path::new(RUNTIME_UNITS).join(&unit), &text, 0o644, false)?;
                // No reset-failed here: a crashed generation's failed state and
                // InvocationID are what STOP's pre-stop check identifies the
                // dead incarnation by. `start` and `stop` reset it.
                if !visibility.is_empty() {
                    let drop_dir=Path::new(RUNTIME_UNITS).join(format!("{unit}.d"));
                    fs::create_dir_all(&drop_dir)?;
                    fs::set_permissions(&drop_dir,fs::Permissions::from_mode(0o755))?;
                    write_root_text(&drop_dir.join("10-native-visibility.conf"),&visibility,0o644,false)?;
                }
                systemctl(&["daemon-reload"])?;
                self.save_unit_runtime(&unit, &runtime)?;
                Ok(
                    json!({"unit":unit,"slice":app_slice(prefix, &store, &app),"spkHostSha256":runtime.spk_host_sha256}),
                )
            }
            Request::Start { unit } => {
                Self::check_resident_unit_name(&unit)?;
                let store = self
                    .unit_store(&unit)?
                    .ok_or_else(|| invalid("start refused: unit not installed by this broker"))?;
                self.require_unit_runtime(&store, &unit)?;
                // A never-begun generation's earlier failed attempt.
                if active_state(&unit)? == "failed" {
                    systemctl(&["reset-failed", &unit])?;
                }
                systemctl(&["start", &unit])?;
                Ok(json!({"unit":unit,"activeState":active_state(&unit)?}))
            }
            Request::Stop { unit } => {
                Self::check_resident_unit_name(&unit)?;
                if self.unit_store(&unit)?.is_none() {
                    return Err(invalid("stop refused: unit not installed by this broker"));
                }
                systemctl(&["stop", &unit])?;
                if active_state(&unit)? == "failed" {
                    systemctl(&["reset-failed", &unit])?;
                }
                Ok(json!({"unit":unit,"activeState":active_state(&unit)?}))
            }
            Request::Backup {} => {
                root_dir(&self.root().join("backups"), 0o700)?;
                let stamp = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map_err(|_| invalid("clock"))?
                    .as_secs();
                self.backup_into(&self.root().join("backups").join(stamp.to_string()))
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
                volume_custody::export(self.root(),&store,&app,self.operator_uid,self.operator_gid)

            }
        }
    }
}

/// `mini-spk-broker backup CONFIG OUT_DIR` (root; `mini-backup` calls it).
/// Every registered volume is copied with its filesystem frozen for the
/// duration of the copy, so a running app's image (a live SQLite file inside
/// it is the hazard) is captured at one crash-consistent instant: what a
/// power cut would leave, which SQLite's journal is built to recover. A
/// stopped app's copy is exact. Each copy is checked (`e2fsck -fn`) and its
/// root directory listed (`debugfs`) without mounting it.
pub fn backup(config_path: &Path, out: &Path) -> io::Result<Value> {
    if unsafe { libc::geteuid() } != 0 {
        return Err(invalid("backup runs as root"));
    }
    Broker::load(config_path)?.backup_into(out)
}

impl Broker {
    fn backup_into(&self, out: &Path) -> io::Result<Value> {
        let broker = self;
        let backup=volume_custody::BackupTarget::create(out,self.operator_uid)?;
        let volumes = broker.root().join("volumes");
        let mut names = Vec::new();
        for entry in fs::read_dir(&volumes)? {
            let name = entry?.file_name().to_string_lossy().into_owned();
            if let Some(stem) = name.strip_suffix(".conf") {
                if !stem.starts_with('.') {
                    names.push(stem.to_owned());
                }
            }
        }
        names.sort();
        let mut grains = Vec::new();
        for name in names {
            let (store, app) = name
                .split_once('-')
                .filter(|(store, app)| store_key(store) && decimal(app))
                .ok_or_else(|| invalid(format!("registration name {name} refused")))?;
            let active = broker.app_units_active(store, app)?;
            let copy=out.join(format!("{name}.ext4"));
            let captured=backup.copy_volume(broker.root(),&name,!active.is_empty())?;
            let fsck=volume_custody::inspect_copy("/usr/sbin/e2fsck",&["-fn"],&captured.file)?;
            let listing=volume_custody::inspect_copy("/usr/sbin/debugfs",&["-R","ls -l /"],&captured.file)?;
            grains.push(json!({
            "name":name,"store":store,"app":app,
            "state":if active.is_empty() { "stopped-exact" } else { "running-frozen-crash-consistent" },
             "activeUnits":active,"frozenMs":captured.frozen_ms.to_string(),
            "image":copy,"sha256":captured.hash,"bytes":captured.bytes.to_string(),
            "e2fsck":if fsck.status.success() { "clean" } else { "errors" },
            "rootListing":String::from_utf8_lossy(&listing.stdout).lines()
                .map(str::trim).filter(|l| !l.is_empty()).collect::<Vec<_>>(),
        }));
        }
        let manifest = json!({"protocol":"mini-spk-grain-backup-v1","grainsRoot":broker.root(),
        "grains":grains});
        backup.write_manifest(&manifest)?;
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
    if unsafe { libc::geteuid() } != 0 {
        return Err(invalid("mini-spk-broker runs as root"));
    }
    unsafe {
        libc::umask(0o077);
    }
    let mut broker = Broker::load(config_path)?;
    let socket = socket_path(broker.root(), broker.config.broker_socket.as_deref())?;
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
    fn spk_namespace_default_preserves_existing_helper_protocol() {
        let (packages,inbox)=spk_namespace_paths(None).unwrap();
        assert_eq!(packages,Path::new(PACKAGE_STORE));
        assert_eq!(inbox,Path::new(INBOX));
        let args=ingest_arguments(None,Path::new("/root/candidate/spk-host"),"hash",
            &inbox.join("grain-package.spk"),64010).unwrap();
        assert_eq!(args,vec!["/root/candidate/spk-host","hash","/var/lib/minidregg/spk/inbox/grain-package.spk","64010"]);
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
    fn spk_namespace_identity_preserves_legacy_and_rejects_malformed_routes() {
        let sha="a".repeat(64);
        let old=json!({"protocol":"mini-spk-broker-identity-v1"});
        assert_eq!(image_path_from_identity(&old,&sha).unwrap(),Path::new(PACKAGE_STORE).join(format!("sha256-{sha}")));
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
            r#"{"verb":"start","unit":"mini-spk-a1-g2.service"}"#
        )
        .is_ok());
        assert!(serde_json::from_str::<Request>(r#"{"verb":"exec","command":"sh"}"#).is_err());
        assert!(serde_json::from_str::<Request>(
            r#"{"verb":"start","unit":"mini-spk-a1-g2.service","text":"[Service]"}"#
        )
        .is_err());
        assert!(serde_json::from_str::<Request>(
            r#"{"verb":"install-unit","store":"0123456789abcdef","app":"7","generation":"2","unitText":"x"}"#
        )
        .is_err());
    }

    #[test]
    fn resident_unit_names_are_exact() {
        assert!(Broker::check_resident_unit_name("mini-spk-a7701-g2.service").is_ok());
        for bad in [
            "mini-spk-a07701-g2.service",
            "mini-spk-a7701-g2.service.d",
            "mini-spk-a7701-g0.service",
            "sshd.service",
            "mini-spk-a1-g2-g3.service",
            "mini-spk-a1-g2.service/../x",
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
            "mini-grains-s0123456789abcdefa7701.slice"
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
