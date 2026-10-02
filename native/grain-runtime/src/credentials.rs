//! Provider table and per-subject provider credential custody.
//!
//! One source, two consumers: the grain controller (`grain-runtime`) resolves
//! a route and a credential at provider-reserve time, and the `mini key`
//! verbs (`resource-client`, included with `#[path]`) write the records. The
//! two must never disagree about a file's shape, so neither owns a copy.
//!
//! Layout (every file 0600, every directory 0700, all owned by the one
//! service user that runs both the hosted shell and the controller):
//!
//!   TABLE  /etc/mini/providers.json           root-owned, not group/world writable
//!   KEY    /etc/mini/credentials.key          32 random bytes, the at-rest key
//!   ROOT   /var/lib/mini/credentials/
//!            SUBJECT/PUBLIC-KEY-HEX/PROVIDER.key          sealed secret
//!            SUBJECT/PUBLIC-KEY-HEX/PROVIDER.grants.json  runners allowed to use it
//!            SUBJECT/PUBLIC-KEY-HEX/PROVIDER.usage.json   per-runner day counters
//!            _pool/PROVIDER.key                           the operator's pool secret
//!
//! A friend's namespace is named by the subject AND the public key of the
//! workspace key that wrote it. `mini key` derives that key from the
//! workspace's own signing key, so a workspace that merely claims another
//! subject number writes into a different directory and can neither read,
//! replace, grant nor revoke the real owner's credential. The controller
//! looks only under the operator-pinned `onBehalfOf` subject and public key.
//!
//! Custody statement: this is hosted custody. The at-rest seal keeps the
//! secret out of anything that copies ROOT without KEY (backups of
//! /var/lib/mini, a stray tarball). It does not hide the secret from root or
//! from the service user, which must read KEY to use the credential.
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
#[path = "provider_choice.rs"]
pub mod choice;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::io::AsRawFd;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

pub const DEFAULT_TABLE: &str = "/etc/mini/providers.json";
pub const DEFAULT_ROOT: &str = "/var/lib/mini/credentials";
pub const DEFAULT_KEY: &str = "/etc/mini/credentials.key";
const POOL_NAMESPACE: &str = "_pool";
const TABLE_TYPE: &str = "mini-provider-table-v2";
const SEALED_TYPE: &str = "mini-provider-credential-v1";
const GRANTS_TYPE: &str = "mini-provider-grants-v1";
const SCOPED_GRANTS_TYPE: &str = "mini-provider-grants-v2";
const USAGE_TYPE: &str = "mini-provider-usage-v1";
const MAX_TABLE: u64 = 65_536;
const MAX_RECORD: u64 = 65_536;
const MAX_SECRET: usize = 4096;
const MAX_GRANTS: usize = 64;
/// Refusal prefix. The gateway turns `provider-refused:CODE` into a named
/// HTTP refusal; nothing else in the controller starts with it.
pub const REFUSED: &str = "provider-refused:";

extern "C" {
    fn geteuid() -> u32;
    fn flock(fd: i32, operation: i32) -> i32;
}
const LOCK_EX: i32 = 2;
const LOCK_NB: i32 = 4;

fn euid() -> u32 {
    unsafe { geteuid() }
}

pub fn refused(code: &str) -> String {
    format!("{REFUSED}{code}")
}

/// A provider bearer value. It has no `Display`, its `Debug` is redacted,
/// and it is zeroed on drop, so formatting an error or a struct that holds
/// one can never print it.
pub struct Secret(String);

impl Secret {
    pub fn new(value: String) -> Result<Self, String> {
        if value.is_empty()
            || value.len() > MAX_SECRET
            || value.bytes().any(|b| !(0x21..=0x7e).contains(&b))
        {
            return Err(
                "provider secret must be 1..4096 printable ASCII bytes without spaces".into(),
            );
        }
        Ok(Self(value))
    }
    /// The only way to read the value. Callers: the curl config line and the
    /// response echo check. Nothing else.
    pub fn expose(&self) -> &str {
        &self.0
    }
}

impl std::fmt::Debug for Secret {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Secret(<redacted>)")
    }
}

impl Drop for Secret {
    fn drop(&mut self) {
        // SAFETY: zero bytes are valid UTF-8.
        unsafe { self.0.as_bytes_mut().fill(0) };
    }
}

// ------------------------------------------------------------------ table

/// Who pays the provider for a call through this row. It is also the
/// route the provider purse records at reserve and charges by at settle
/// (`Kernel/ProviderRoute.lean`): the Host's per-route tariff, not the row,
/// prices it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CredentialSource {
    /// The calling friend's own key, used only under their grant. Mini
    /// charges the purse only the per-operation fee.
    User,
    /// The operator's key; the purse pays the metered tariff, and the row's
    /// caps bound each call's `max_tokens` and the calls per day.
    Pool,
    /// No bearer at all (a homelab endpoint on the operator's own network),
    /// priced by the tariff's homelab route.
    Homelab,
}

impl CredentialSource {
    /// The route name the Host's tariff and the purse use.
    pub fn route(self) -> &'static str {
        match self {
            CredentialSource::User => "user",
            CredentialSource::Pool => "pool",
            CredentialSource::Homelab => "homelab",
        }
    }
}

/// The operator's bound on its own key, per runner: the largest
/// `max_tokens` one call may ask for and the calls per UTC day.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Caps {
    pub per_call: u64,
    pub per_day: u64,
}

#[derive(Clone, Debug)]
pub struct ProviderRow {
    pub name: String,
    pub endpoint: String,
    pub models: Vec<String>,
    pub credential: CredentialSource,
    /// Required on a pool row, refused on any other.
    pub caps: Option<Caps>,
}

pub struct ProviderTable {
    pub sha256: String,
    pub rows: Vec<ProviderRow>,
}

fn decimal(value: &str, label: &str) -> Result<(), String> {
    if value.is_empty()
        || value.len() > 40
        || !value.bytes().all(|b| b.is_ascii_digit())
        || (value.len() > 1 && value.starts_with('0'))
    {
        return Err(format!("{label} must be a canonical decimal"));
    }
    Ok(())
}

pub fn provider_name(value: &str) -> Result<(), String> {
    let bytes = value.as_bytes();
    if bytes.is_empty()
        || bytes.len() > 32
        || !bytes[0].is_ascii_lowercase()
        || !bytes
            .iter()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || *b == b'-')
    {
        return Err("provider name must be [a-z][a-z0-9-]{0,31}".into());
    }
    Ok(())
}

fn object_keys(value: &Value, allowed: &[&str], label: &str) -> Result<(), String> {
    let object = value
        .as_object()
        .ok_or_else(|| format!("{label} must be an object"))?;
    if let Some(name) = object.keys().find(|k| !allowed.contains(&k.as_str())) {
        return Err(format!("{label} has unknown field {name}"));
    }
    Ok(())
}

fn string<'a>(value: &'a Value, name: &str, label: &str) -> Result<&'a str, String> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{label}.{name} must be a string"))
}

/// Exact Chat Completions endpoint. The same rule held when the endpoint was
/// one configured URL; now it holds for every row.
pub fn validate_endpoint(url: &str) -> Result<(), String> {
    let (scheme, remainder) = url.split_once("://").ok_or("upstream URL lacks scheme")?;
    let (authority, path) = remainder.split_once('/').ok_or("upstream URL lacks path")?;
    if !matches!(path, "v1/chat/completions" | "api/v1/chat/completions")
        || authority.is_empty()
        || authority
            .bytes()
            .any(|b| !(b.is_ascii_alphanumeric() || b".-:[]".contains(&b)))
        || authority.contains("..")
        || authority.contains('@')
    {
        return Err("upstream must pin one Chat Completions endpoint".into());
    }
    if scheme == "http" {
        if !is_loopback_http(url) {
            return Err("plain HTTP upstream is permitted only on loopback".into());
        }
    } else if scheme != "https" {
        return Err("provider upstream must use verified HTTPS".into());
    }
    Ok(())
}

pub fn is_loopback_http(url: &str) -> bool {
    let Some(rest) = url.strip_prefix("http://") else {
        return false;
    };
    let authority = rest.split('/').next().unwrap_or("");
    authority == "127.0.0.1"
        || authority.starts_with("127.0.0.1:")
        || authority == "[::1]"
        || authority.starts_with("[::1]:")
}

impl ProviderTable {
    pub fn parse(bytes: &[u8]) -> Result<Self, String> {
        let value: Value =
            serde_json::from_slice(bytes).map_err(|e| format!("provider table JSON: {e}"))?;
        object_keys(&value, &["type", "providers"], "provider table")?;
        if value.get("type").and_then(Value::as_str) != Some(TABLE_TYPE) {
            return Err(format!("provider table type must be {TABLE_TYPE}"));
        }
        let entries = value
            .get("providers")
            .and_then(Value::as_array)
            .filter(|rows| !rows.is_empty() && rows.len() <= 32)
            .ok_or("provider table needs 1..32 providers")?;
        let mut rows: Vec<ProviderRow> = Vec::with_capacity(entries.len());
        for entry in entries {
            let label = "provider row";
            object_keys(
                entry,
                &["name", "endpoint", "kind", "models", "credential", "caps"],
                label,
            )?;
            let name = string(entry, "name", label)?.to_owned();
            provider_name(&name)?;
            if rows.iter().any(|row| row.name == name) {
                return Err(format!("provider table repeats {name}"));
            }
            if string(entry, "kind", label)? != "openai-compatible" {
                return Err(format!("provider {name}: kind must be openai-compatible"));
            }
            let endpoint = string(entry, "endpoint", label)?.to_owned();
            validate_endpoint(&endpoint).map_err(|e| format!("provider {name}: {e}"))?;
            let models = entry
                .get("models")
                .and_then(Value::as_array)
                .filter(|models| !models.is_empty() && models.len() <= 64)
                .ok_or_else(|| format!("provider {name}: models must list 1..64 names"))?
                .iter()
                .map(|model| {
                    model
                        .as_str()
                        .filter(|m| {
                            !m.is_empty() && m.len() <= 256 && !m.chars().any(char::is_control)
                        })
                        .map(str::to_owned)
                        .ok_or_else(|| format!("provider {name}: invalid model name"))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let credential = match string(entry, "credential", label)? {
                "user" => CredentialSource::User,
                "pool" => CredentialSource::Pool,
                "homelab" => CredentialSource::Homelab,
                _ => {
                    return Err(format!(
                        "provider {name}: credential must be user|pool|homelab"
                    ))
                }
            };
            let caps = match (credential, entry.get("caps")) {
                (CredentialSource::Pool, Some(caps)) => {
                    let label = "provider caps";
                    object_keys(caps, &["perCall", "perDay"], label)?;
                    let field = |n: &str, max: u64| -> Result<u64, String> {
                        let v = string(caps, n, label)?;
                        decimal(v, n)?;
                        v.parse::<u64>()
                            .ok()
                            .filter(|v| (1..=max).contains(v))
                            .ok_or_else(|| format!("provider {name}: caps.{n} must be 1..{max}"))
                    };
                    Some(Caps {
                        per_call: field("perCall", 1_000_000)?,
                        per_day: field("perDay", 100_000)?,
                    })
                }
                (CredentialSource::Pool, None) => {
                    return Err(format!(
                        "provider {name}: a pool row needs caps {{perCall, perDay}}"
                    ))
                }
                (_, Some(_)) => return Err(format!("provider {name}: only a pool row has caps")),
                (_, None) => None,
            };
            rows.push(ProviderRow {
                name,
                endpoint,
                models,
                credential,
                caps,
            });
        }
        Ok(Self {
            rows,
            sha256: hex(&Sha256::digest(bytes)),
        })
    }

    /// Production callers pass owner 0: the table names where the operator's
    /// money and the friends' keys may be sent, so the service user that
    /// uses it must not be able to rewrite it.
    pub fn load(path: &Path, owner_uid: u32) -> Result<Self, String> {
        let meta = fs::symlink_metadata(path).map_err(|e| format!("provider table: {e}"))?;
        if !meta.file_type().is_file()
            || meta.uid() != owner_uid
            || meta.permissions().mode() & 0o022 != 0
            || meta.len() > MAX_TABLE
        {
            return Err(format!(
                "provider table must be a regular file owned by uid {owner_uid}, not group/world writable"
            ));
        }
        Self::parse(&fs::read(path).map_err(|e| format!("provider table: {e}"))?)
    }

    /// The task's row: the explicitly configured one, which must list the
    /// model, or else the first row that lists it. There is no fall-through
    /// from one payer to another: a caller whose row needs their own key and
    /// who has none is refused, never silently moved onto the pool.
    pub fn select(&self, model: &str, explicit: Option<&str>) -> Result<&ProviderRow, String> {
        let row = match explicit {
            Some(name) => self.rows.iter().find(|row| row.name == name),
            None => self
                .rows
                .iter()
                .find(|row| row.models.iter().any(|m| m == model)),
        };
        row.filter(|row| row.models.iter().any(|m| m == model))
            .ok_or_else(|| refused("no-route"))
    }
}

// ------------------------------------------------------------------ records

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Grant {
    /// The runner subject (a Hermes provider task's signing subject).
    pub runner: String,
    /// Ceiling on the exact forwarded request's `max_tokens`.
    pub per_call: u64,
    /// Calls per UTC day for this runner.
    pub per_day: u64,
    /// Last block height at which the grant is usable (inclusive).
    pub not_after: u64,
    /// Optional exact allowed model. None retains the legacy provider-wide grant.
    pub model: Option<String>,
    /// Native owner epoch when this grant was authenticated.
    pub owner_epoch: Option<String>,
}

impl Grant {
    pub fn validate(&self) -> Result<(), String> {
        decimal(&self.runner, "grant runner")?;
        if let Some(epoch) = &self.owner_epoch {
            decimal(epoch, "owner epoch")?;
        }
        if !(1..=1_000_000).contains(&self.per_call) {
            return Err("grant per-call must be 1..1000000 output tokens".into());
        }
        if !(1..=100_000).contains(&self.per_day) {
            return Err("grant per-day must be 1..100000 calls".into());
        }
        if self
            .model
            .as_ref()
            .is_some_and(|m| m.is_empty() || m.len() > 256 || m.chars().any(char::is_control))
        {
            return Err("grant model must be a nonempty model name of at most 256 bytes".into());
        }
        Ok(())
    }
    pub fn to_json(&self) -> Value {
        let mut value = json!({"runner":self.runner,"perCall":self.per_call.to_string(),
            "perDay":self.per_day.to_string(),"notAfter":self.not_after.to_string()});
        if let Some(model) = &self.model {
            value["model"] = json!(model);
        }
        if let Some(epoch) = &self.owner_epoch {
            value["ownerEpoch"] = json!(epoch);
        }
        value
    }
    pub fn from_json(value: &Value) -> Result<Self, String> {
        object_keys(
            value,
            &[
                "runner",
                "perCall",
                "perDay",
                "notAfter",
                "model",
                "ownerEpoch",
            ],
            "grant",
        )?;
        let number = |name: &str| -> Result<u64, String> {
            let v = string(value, name, "grant")?;
            decimal(v, name)?;
            v.parse().map_err(|_| format!("grant {name} exceeds u64"))
        };
        let grant = Self {
            runner: string(value, "runner", "grant")?.to_owned(),
            per_call: number("perCall")?,
            per_day: number("perDay")?,
            not_after: number("notAfter")?,
            owner_epoch: value
                .get("ownerEpoch")
                .map(|m| {
                    m.as_str()
                        .map(str::to_owned)
                        .ok_or("grant owner epoch must be a string")
                })
                .transpose()?,
            model: value
                .get("model")
                .map(|m| {
                    m.as_str()
                        .map(str::to_owned)
                        .ok_or("grant model must be a string")
                })
                .transpose()?,
        };
        grant.validate()?;
        Ok(grant)
    }
}

/// Whose credential. `public_key` is the 32-byte ed25519 key of the
/// workspace that wrote it, lower-case hex.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Owner {
    pub subject: String,
    pub public_key: String,
}

impl Owner {
    pub fn new(subject: &str, public_key: &str) -> Result<Self, String> {
        decimal(subject, "credential subject")?;
        if public_key.len() != 64
            || !public_key
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err("credential owner public key must be 64 lower-case hex digits".into());
        }
        Ok(Self {
            subject: subject.to_owned(),
            public_key: public_key.to_owned(),
        })
    }
}

/// Whose namespace: a friend, or the operator's pool.
#[derive(Clone, Copy, Debug)]
pub enum Namespace<'a> {
    Owner(&'a Owner),
    Pool,
}

/// Derive the exact namespace using the same identity parser as credential use.
/// This is pure: it neither reads the master key nor creates/locks a directory.
pub fn namespace_path(root: &Path, namespace: Namespace<'_>) -> Result<PathBuf, String> {
    if !root.is_absolute()
        || root.components().any(|p| {
            !matches!(
                p,
                std::path::Component::RootDir | std::path::Component::Normal(_)
            )
        })
    {
        return Err("credential root must be a canonical absolute path".into());
    }
    Ok(match namespace {
        Namespace::Pool => root.join(POOL_NAMESPACE),
        Namespace::Owner(owner) => {
            Owner::new(&owner.subject, &owner.public_key)?;
            root.join(&owner.subject).join(&owner.public_key)
        }
    })
}

pub struct CredentialStore {
    root: PathBuf,
    key: [u8; 32],
    rooted_namespaces: bool,
}

fn private_dir_check(path: &Path, label: &str) -> Result<(), String> {
    let meta = fs::symlink_metadata(path).map_err(|e| format!("{label}: {e}"))?;
    if !meta.file_type().is_dir() || meta.uid() != euid() || meta.permissions().mode() & 0o077 != 0
    {
        return Err(format!("{label} must be an owned 0700 directory"));
    }
    Ok(())
}

/// Every ancestor is immutable to the service UID. In particular the subject
/// parent cannot be swapped after source scope admission but before systemd mounts.
fn root_directory_chain(path: &Path, label: &str) -> Result<(), String> {
    namespace_path(path, Namespace::Pool)?; // shared canonical lexical validation
    for entry in path.ancestors() {
        let meta = fs::symlink_metadata(entry).map_err(|e| format!("{label}: {e}"))?;
        if !meta.file_type().is_dir() || meta.uid() != 0 || meta.permissions().mode() & 0o022 != 0 {
            return Err(format!(
                "{label} requires root-owned immutable directory ancestry"
            ));
        }
    }
    Ok(())
}

fn private_file_check(path: &Path, label: &str, bound: u64) -> Result<(), String> {
    let meta = fs::symlink_metadata(path).map_err(|e| format!("{label}: {e}"))?;
    if !meta.file_type().is_file()
        || meta.uid() != euid()
        || meta.permissions().mode() & 0o077 != 0
        || meta.len() > bound
    {
        return Err(format!("{label} must be an owned private regular file"));
    }
    Ok(())
}

fn ensure_private_dir(path: &Path, label: &str) -> Result<(), String> {
    match fs::symlink_metadata(path) {
        Ok(_) => private_dir_check(path, label),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            fs::DirBuilder::new()
                .mode(0o700)
                .create(path)
                .map_err(|e| format!("{label}: {e}"))?;
            private_dir_check(path, label)
        }
        Err(e) => Err(format!("{label}: {e}")),
    }
}

/// Replace `path` with `bytes` atomically: a fresh 0600 sibling, fsync,
/// rename, fsync the directory.
fn replace_private(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let parent = path.parent().ok_or("record path has no parent")?;
    let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .ok_or("record path has no name")?;
    let temporary = parent.join(format!(".{name}.{}.tmp", std::process::id()));
    let _ = fs::remove_file(&temporary);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&temporary)
        .map_err(|e| format!("credential record write: {e}"))?;
    file.write_all(bytes)
        .and_then(|_| file.sync_all())
        .map_err(|e| format!("credential record write: {e}"))?;
    fs::rename(&temporary, path).map_err(|e| format!("credential record rename: {e}"))?;
    File::open(parent)
        .and_then(|d| d.sync_all())
        .map_err(|e| format!("credential directory sync: {e}"))
}

// One provider-wide lock orders key replacement, grant changes, revocation
// and reserve-time authorization. Usage retains its separate counter lock.
fn lock_until(lock: &File, end: Instant) -> Result<(), String> {
    loop {
        if Instant::now() >= end {
            return Err("credential authority busy; retry the same action".into());
        }
        if unsafe { flock(lock.as_raw_fd(), LOCK_EX | LOCK_NB) } == 0 {
            return Ok(());
        }
        let error = std::io::Error::last_os_error();
        if !matches!(
            error.kind(),
            std::io::ErrorKind::WouldBlock | std::io::ErrorKind::Interrupted
        ) {
            return Err("credential authority lock unavailable".into());
        }
        std::thread::sleep(
            Duration::from_millis(5).min(end.saturating_duration_since(Instant::now())),
        );
    }
}

fn provider_lock(dir: &Path, provider: &str) -> Result<File, String> {
    provider_lock_until(dir, provider, Instant::now() + Duration::from_secs(2))
}

fn provider_lock_until(dir: &Path, provider: &str, end: Instant) -> Result<File, String> {
    let path = dir.join(format!("{provider}.authority.lock"));
    let lock = OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&path)
        .map_err(|_| "credential authority lock unavailable".to_owned())?;
    private_file_check(&path, "credential authority lock", 0)?;
    lock_until(&lock, end)?;
    Ok(lock)
}

fn read_record(path: &Path, label: &str) -> Result<Option<Value>, String> {
    match fs::symlink_metadata(path) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(format!("{label}: {e}")),
        Ok(_) => {
            private_file_check(path, label, MAX_RECORD)?;
            let bytes = fs::read(path).map_err(|e| format!("{label}: {e}"))?;
            serde_json::from_slice(&bytes)
                .map(Some)
                .map_err(|e| format!("{label} JSON: {e}"))
        }
    }
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        out.push(DIGITS[(b >> 4) as usize] as char);
        out.push(DIGITS[(b & 15) as usize] as char);
    }
    out
}

fn unhex(text: &str) -> Result<Vec<u8>, String> {
    if text.len() % 2 != 0 || !text.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("invalid hex encoding".into());
    }
    (0..text.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&text[i..i + 2], 16).map_err(|_| "invalid hex".to_string()))
        .collect()
}

/// UTC day number, the unit of `perDay`.
pub fn utc_day() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs() / 86_400)
        .unwrap_or(0)
}

impl CredentialStore {
    /// Serialize one member's actions; unrelated members never share its wait.
    pub fn member_service_lock_until(&self, owner: &Owner, end: Instant) -> Result<File, String> {
        Owner::new(&owner.subject, &owner.public_key)?;
        let dir = if self.rooted_namespaces {
            root_directory_chain(&self.root, "credential root")?;
            let dir = self.root.join("_service");
            private_dir_check(&dir, "credential service lock namespace")?;
            dir
        } else {
            self.root.clone()
        };
        provider_lock_until(
            &dir,
            &format!("member-{}-{}", owner.subject, owner.public_key),
            end,
        )
    }

    /// Local stores may use an owned 0700 root. Hosted stores use immutable
    /// root-owned ancestry and preallocated service-owned 0700 namespace leaves.
    /// KEY remains service-owned 0600, outside ROOT.
    pub fn open(root: &Path, key_path: &Path) -> Result<Self, String> {
        if !root.is_absolute() || !key_path.is_absolute() || key_path.starts_with(root) {
            return Err("credential root and key must be distinct absolute paths".into());
        }
        let root_meta = fs::symlink_metadata(root).map_err(|e| format!("credential root: {e}"))?;
        let rooted_namespaces = root_meta.uid() == 0 && euid() != 0;
        if rooted_namespaces {
            root_directory_chain(root, "credential root")?;
        } else {
            private_dir_check(root, "credential root")?;
        }
        private_file_check(key_path, "credential key", 32)?;
        let mut key = [0u8; 32];
        let mut file = File::open(key_path).map_err(|e| format!("credential key: {e}"))?;
        file.read_exact(&mut key)
            .map_err(|_| "credential key must be exactly 32 bytes".to_string())?;
        if file.metadata().map(|m| m.len()).unwrap_or(0) != 32 {
            return Err("credential key must be exactly 32 bytes".into());
        }
        Ok(Self {
            root: root.to_owned(),
            key,
            rooted_namespaces,
        })
    }

    fn directory(&self, namespace: Namespace<'_>, create: bool) -> Result<PathBuf, String> {
        if self.rooted_namespaces {
            root_directory_chain(&self.root, "credential root")?;
            let dir = namespace_path(&self.root, namespace)?;
            if let Namespace::Owner(owner) = namespace {
                let subject = self.root.join(&owner.subject);
                if create || subject.exists() {
                    root_directory_chain(&subject, "subject namespace")?;
                }
            }
            if create {
                private_dir_check(&dir, "root-provisioned credential namespace")?;
            }
            return Ok(dir);
        }
        match namespace {
            Namespace::Pool => {
                let dir = namespace_path(&self.root, namespace)?;
                if create {
                    ensure_private_dir(&dir, "pool namespace")?;
                }
                Ok(dir)
            }
            Namespace::Owner(owner) => {
                let subject = self.root.join(&owner.subject);
                let dir = namespace_path(&self.root, namespace)?;
                if create {
                    ensure_private_dir(&subject, "subject namespace")?;
                    ensure_private_dir(&dir, "credential namespace")?;
                }
                Ok(dir)
            }
        }
    }

    fn aad(namespace: Namespace<'_>, provider: &str) -> Vec<u8> {
        let who = match namespace {
            Namespace::Pool => format!("{POOL_NAMESPACE}\0-"),
            Namespace::Owner(owner) => format!("{}\0{}", owner.subject, owner.public_key),
        };
        format!("{SEALED_TYPE}\0{who}\0{provider}").into_bytes()
    }

    fn aead_key(&self) -> Result<ring::aead::LessSafeKey, String> {
        let unbound = ring::aead::UnboundKey::new(&ring::aead::CHACHA20_POLY1305, &self.key)
            .map_err(|_| "credential key rejected")?;
        Ok(ring::aead::LessSafeKey::new(unbound))
    }

    /// Store (or replace) the namespace's secret for `provider`. Grants on
    /// a replaced secret are kept: the grant names who may use "my
    /// OpenRouter key", not one particular value of it.
    pub fn set(
        &self,
        namespace: Namespace<'_>,
        provider: &str,
        secret: &Secret,
    ) -> Result<(), String> {
        provider_name(provider)?;
        let dir = self.directory(namespace, true)?;
        let _lock = provider_lock(&dir, provider)?;
        let mut nonce = [0u8; 12];
        ring::rand::SecureRandom::fill(&ring::rand::SystemRandom::new(), &mut nonce)
            .map_err(|_| "credential nonce entropy unavailable")?;
        let mut sealed = secret.expose().as_bytes().to_vec();
        self.aead_key()?
            .seal_in_place_append_tag(
                ring::aead::Nonce::assume_unique_for_key(nonce),
                ring::aead::Aad::from(Self::aad(namespace, provider)),
                &mut sealed,
            )
            .map_err(|_| "credential seal failed")?;
        let record = json!({"type":SEALED_TYPE,"provider":provider,
            "nonce":hex(&nonce),"sealed":hex(&sealed)});
        sealed.fill(0);
        let mut bytes = serde_json::to_vec_pretty(&record).map_err(|e| e.to_string())?;
        bytes.push(b'\n');
        replace_private(&dir.join(format!("{provider}.key")), &bytes)
    }

    fn secret(&self, namespace: Namespace<'_>, provider: &str) -> Result<Option<Secret>, String> {
        let dir = self.directory(namespace, false)?;
        let Some(record) = read_record(&dir.join(format!("{provider}.key")), "sealed credential")?
        else {
            return Ok(None);
        };
        object_keys(
            &record,
            &["type", "provider", "nonce", "sealed"],
            "sealed credential",
        )?;
        if record.get("type").and_then(Value::as_str) != Some(SEALED_TYPE)
            || record.get("provider").and_then(Value::as_str) != Some(provider)
        {
            return Err("sealed credential names another provider or version".into());
        }
        let nonce: [u8; 12] = unhex(string(&record, "nonce", "sealed credential")?)?
            .try_into()
            .map_err(|_| "sealed credential nonce must be 12 bytes")?;
        let mut sealed = unhex(string(&record, "sealed", "sealed credential")?)?;
        let opened = self
            .aead_key()?
            .open_in_place(
                ring::aead::Nonce::assume_unique_for_key(nonce),
                ring::aead::Aad::from(Self::aad(namespace, provider)),
                &mut sealed,
            )
            .map_err(|_| "sealed credential does not open under this key and namespace")?
            .to_vec();
        sealed.fill(0);
        let text = String::from_utf8(opened).map_err(|_| "sealed credential is not UTF-8")?;
        Secret::new(text).map(Some)
    }

    fn grants(&self, dir: &Path, provider: &str) -> Result<Vec<Grant>, String> {
        let Some(record) = read_record(&dir.join(format!("{provider}.grants.json")), "grants")?
        else {
            return Ok(Vec::new());
        };
        object_keys(&record, &["type", "provider", "grants"], "grants")?;
        if !matches!(
            record.get("type").and_then(Value::as_str),
            Some(GRANTS_TYPE | SCOPED_GRANTS_TYPE)
        ) || record.get("provider").and_then(Value::as_str) != Some(provider)
        {
            return Err("grant record names another provider or version".into());
        }
        let grants = record
            .get("grants")
            .and_then(Value::as_array)
            .filter(|g| g.len() <= MAX_GRANTS)
            .ok_or("grant list is not bounded")?
            .iter()
            .map(Grant::from_json)
            .collect::<Result<Vec<_>, _>>()?;
        if record["type"] == GRANTS_TYPE
            && grants
                .iter()
                .any(|g| g.model.is_some() || g.owner_epoch.is_some())
        {
            return Err("model-scoped grants require mini-provider-grants-v2".into());
        }
        Ok(grants)
    }

    fn write_grants(&self, dir: &Path, provider: &str, grants: &[Grant]) -> Result<(), String> {
        let version = if grants
            .iter()
            .any(|g| g.model.is_some() || g.owner_epoch.is_some())
        {
            SCOPED_GRANTS_TYPE
        } else {
            GRANTS_TYPE
        };
        let record = json!({"type":version,"provider":provider,
            "grants":grants.iter().map(Grant::to_json).collect::<Vec<_>>()});
        let mut bytes = serde_json::to_vec_pretty(&record).map_err(|e| e.to_string())?;
        bytes.push(b'\n');
        replace_private(&dir.join(format!("{provider}.grants.json")), &bytes)
    }

    /// Grant (or replace the grant for) one runner. Needs a stored secret.
    pub fn grant(&self, owner: &Owner, provider: &str, grant: Grant) -> Result<(), String> {
        provider_name(provider)?;
        grant.validate()?;
        let namespace = Namespace::Owner(owner);
        let dir = self.directory(namespace, false)?;
        private_dir_check(&dir, "credential namespace")?;
        let _lock = provider_lock(&dir, provider)?;
        if !dir.join(format!("{provider}.key")).exists() {
            return Err(format!(
                "no stored {provider} credential to grant; run key set first"
            ));
        }
        let mut grants = self.grants(&dir, provider)?;
        grants.retain(|g| g.runner != grant.runner);
        if grants.len() >= MAX_GRANTS {
            return Err("grant list is full".into());
        }
        grants.push(grant);
        self.write_grants(&dir, provider, &grants)
    }

    /// `runner = None` deletes the secret, every grant and the counters.
    /// Returns whether anything was removed.
    pub fn revoke(
        &self,
        namespace: Namespace<'_>,
        provider: &str,
        runner: Option<&str>,
    ) -> Result<bool, String> {
        provider_name(provider)?;
        let dir = self.directory(namespace, false)?;
        if fs::symlink_metadata(&dir).is_err() {
            return Ok(false);
        }
        private_dir_check(&dir, "credential namespace")?;
        let _lock = provider_lock(&dir, provider)?;
        match runner {
            Some(runner) => {
                let mut grants = self.grants(&dir, provider)?;
                let before = grants.len();
                grants.retain(|g| g.runner != runner);
                if grants.len() == before {
                    return Ok(false);
                }
                self.write_grants(&dir, provider, &grants)?;
                Ok(true)
            }
            None => {
                let mut removed = ["key", "grants.json", "usage.json"]
                    .iter()
                    .any(|suffix| dir.join(format!("{provider}.{suffix}")).exists());
                if !removed {
                    return Ok(false);
                }
                // Durable revocation first. A crash while removing custody must
                // not let a later key set revive an old runner grant.
                self.write_grants(&dir, provider, &[])?;
                for suffix in ["key", "grants.json", "usage.json"] {
                    match fs::remove_file(dir.join(format!("{provider}.{suffix}"))) {
                        Ok(()) => removed = true,
                        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
                        Err(e) => return Err(format!("credential revoke: {e}")),
                    }
                }
                File::open(&dir)
                    .and_then(|d| d.sync_all())
                    .map_err(|e| format!("credential directory sync: {e}"))?;
                Ok(removed)
            }
        }
    }

    /// Names and caps, never values.
    pub fn list(&self, namespace: Namespace<'_>) -> Result<Value, String> {
        let dir = self.directory(namespace, false)?;
        let mut providers = Vec::new();
        if fs::symlink_metadata(&dir).is_ok() {
            private_dir_check(&dir, "credential namespace")?;
            let mut names: Vec<String> = fs::read_dir(&dir)
                .map_err(|e| format!("credential namespace: {e}"))?
                .filter_map(|e| e.ok()?.file_name().into_string().ok())
                .filter_map(|n| n.strip_suffix(".key").map(str::to_owned))
                .filter(|n| provider_name(n).is_ok())
                .collect();
            names.sort();
            for name in names {
                let grants = self.grants(&dir, &name)?;
                providers.push(json!({"provider":name,
                    "grants":grants.iter().map(Grant::to_json).collect::<Vec<_>>()}));
            }
        }
        Ok(json!({"type":"mini-provider-credentials-list-v1","credentials":providers}))
    }

    /// The controller's one question at reserve time: may `runner` use this
    /// owner's `provider` credential for a call with this output ceiling at
    /// this signed height? A yes counts the call against today's cap before
    /// the secret is returned.
    pub fn authorize(
        &self,
        owner: &Owner,
        provider: &str,
        runner: &str,
        height: u64,
        max_tokens: Option<u64>,
        day: u64,
    ) -> Result<Secret, String> {
        self.authorize_model(owner, provider, runner, None, height, max_tokens, day)
    }

    /// Model-aware reserve-time authorization. Legacy callers cannot use a
    /// scoped grant because they supply no model. Refusal never consumes a call.
    pub fn authorize_model(
        &self,
        owner: &Owner,
        provider: &str,
        runner: &str,
        model: Option<&str>,
        height: u64,
        max_tokens: Option<u64>,
        day: u64,
    ) -> Result<Secret, String> {
        self.authorize_model_epoch(
            owner, provider, runner, model, None, height, max_tokens, day,
        )
    }

    /// Production use supplies a freshly verified native epoch. Legacy grants
    /// and old epochs cannot regain authority when a public key is reused.
    pub fn authorize_model_epoch(
        &self,
        owner: &Owner,
        provider: &str,
        runner: &str,
        model: Option<&str>,
        owner_epoch: Option<&str>,
        height: u64,
        max_tokens: Option<u64>,
        day: u64,
    ) -> Result<Secret, String> {
        provider_name(provider)?;
        let namespace = Namespace::Owner(owner);
        let dir = self.directory(namespace, false)?;
        if fs::symlink_metadata(&dir).is_err()
            || fs::symlink_metadata(dir.join(format!("{provider}.key"))).is_err()
        {
            return Err(refused("no-credential"));
        }
        private_dir_check(&dir, "credential namespace")?;
        let _lock = provider_lock(&dir, provider)?;
        let grant = self
            .grants(&dir, provider)?
            .into_iter()
            .find(|g| g.runner == runner)
            .ok_or_else(|| refused("no-credential"))?;
        if grant.owner_epoch.as_deref() != owner_epoch {
            return Err(refused("owner-epoch-not-granted"));
        }
        if grant
            .model
            .as_deref()
            .is_some_and(|allowed| Some(allowed) != model)
        {
            return Err(refused("model-not-granted"));
        }
        if height > grant.not_after {
            return Err(refused("grant-expired"));
        }
        if max_tokens.is_none_or(|tokens| tokens > grant.per_call) {
            return Err(refused("per-call-cap"));
        }
        let secret = self
            .secret(namespace, provider)?
            .ok_or_else(|| refused("no-credential"))?;
        self.count_call(&dir, provider, runner, grant.per_day, day)?;
        Ok(secret)
    }

    /// Validate the current member grant without charging daily usage. Used by
    /// typed owner migration, which must never manufacture replacement authority.
    pub fn verify_grant(
        &self,
        owner: &Owner,
        provider: &str,
        runner: &str,
        model: &str,
        epoch: &str,
        height: u64,
    ) -> Result<Grant, String> {
        provider_name(provider)?;
        let dir = self.directory(Namespace::Owner(owner), false)?;
        private_dir_check(&dir, "credential namespace")?;
        let _lock = provider_lock(&dir, provider)?;
        let grant = self
            .grants(&dir, provider)?
            .into_iter()
            .find(|g| g.runner == runner)
            .ok_or_else(|| refused("no-credential"))?;
        if grant.model.as_deref() != Some(model) || grant.owner_epoch.as_deref() != Some(epoch) {
            return Err(refused("owner-model-epoch-not-granted"));
        }
        if height > grant.not_after {
            return Err(refused("grant-expired"));
        }
        self.secret(Namespace::Owner(owner), provider)?
            .ok_or_else(|| refused("no-credential"))?;
        Ok(grant)
    }

    /// The pool secret, for one call of `runner` within the row's caps: a
    /// call without `max_tokens`, or above `caps.per_call`, is refused
    /// `per-call-cap`; the call is counted against `caps.per_day` (in the
    /// pool namespace, per runner) before the secret is returned.
    pub fn pool(
        &self,
        provider: &str,
        runner: &str,
        max_tokens: Option<u64>,
        caps: Caps,
        day: u64,
    ) -> Result<Secret, String> {
        provider_name(provider)?;
        let dir = self.directory(Namespace::Pool, false)?;
        if fs::symlink_metadata(&dir).is_err()
            || fs::symlink_metadata(dir.join(format!("{provider}.key"))).is_err()
        {
            return Err(refused("no-credential"));
        }
        private_dir_check(&dir, "pool credential namespace")?;
        let _lock = provider_lock(&dir, provider)?;
        if max_tokens.is_none_or(|tokens| tokens > caps.per_call) {
            return Err(refused("per-call-cap"));
        }
        let secret = self
            .secret(Namespace::Pool, provider)?
            .ok_or_else(|| refused("no-credential"))?;
        self.count_call(&dir, provider, runner, caps.per_day, day)?;
        Ok(secret)
    }

    fn count_call(
        &self,
        dir: &Path,
        provider: &str,
        runner: &str,
        per_day: u64,
        day: u64,
    ) -> Result<(), String> {
        let lock_path = dir.join(format!("{provider}.usage.lock"));
        let lock = OpenOptions::new()
            .create(true)
            .truncate(false)
            .write(true)
            .mode(0o600)
            .open(&lock_path)
            .map_err(|e| format!("usage lock: {e}"))?;
        lock_until(&lock, Instant::now() + Duration::from_secs(2))?;
        let path = dir.join(format!("{provider}.usage.json"));
        let mut usage = match read_record(&path, "usage")? {
            Some(record) => {
                object_keys(&record, &["type", "provider", "runners"], "usage")?;
                if record.get("type").and_then(Value::as_str) != Some(USAGE_TYPE)
                    || record.get("provider").and_then(Value::as_str) != Some(provider)
                {
                    return Err("usage record names another provider or version".into());
                }
                record
            }
            None => json!({"type":USAGE_TYPE,"provider":provider,"runners":{}}),
        };
        let runners = usage
            .get_mut("runners")
            .and_then(Value::as_object_mut)
            .ok_or("usage runners must be an object")?;
        let (last_day, calls) = runners
            .get(runner)
            .map(|entry| {
                (
                    entry.get("day").and_then(Value::as_u64).unwrap_or(0),
                    entry
                        .get("calls")
                        .and_then(Value::as_u64)
                        .unwrap_or(u64::MAX),
                )
            })
            .unwrap_or((day, 0));
        let calls = if last_day == day { calls } else { 0 };
        if calls >= per_day {
            return Err(refused("per-day-cap"));
        }
        runners.insert(runner.to_owned(), json!({"day":day,"calls":calls + 1}));
        let mut bytes = serde_json::to_vec_pretty(&usage).map_err(|e| e.to_string())?;
        bytes.push(b'\n');
        replace_private(&path, &bytes)
        // The lock is released when `lock` drops.
    }
}

/// Parse a bearer secret from `mini key set` input: one line, surrounding
/// whitespace removed.
pub fn secret_from_input(bytes: &[u8]) -> Result<Secret, String> {
    if bytes.len() > MAX_SECRET + 2 {
        return Err("provider secret input exceeds 4096 bytes".into());
    }
    let text = std::str::from_utf8(bytes).map_err(|_| "provider secret is not UTF-8")?;
    let trimmed = text.trim();
    if trimmed.lines().count() != 1 {
        return Err("provider secret input must be exactly one line".into());
    }
    Secret::new(trimmed.to_owned())
}

#[cfg(test)]
mod credential_tests {
    #[test]
    fn immutable_namespace_parents_refuse_traversal_and_symlink() {
        assert!(super::root_directory_chain(
            std::path::Path::new("/var/lib/mini/../other"),
            "test"
        )
        .is_err());
        let dir = std::env::temp_dir().join(format!(
            "mini-credential-parent-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let link = dir.join("subject");
        std::os::unix::fs::symlink("/", &link).unwrap();
        assert!(super::root_directory_chain(&link, "test").is_err());
        std::fs::remove_file(link).unwrap();
        std::fs::remove_dir(dir).unwrap();
    }
    #[test]
    fn held_member_is_bounded_and_other_member_advances() {
        let dir = std::env::temp_dir().join(format!("mini-member-lock-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
        let held = super::provider_lock(&dir, "member-a").unwrap();
        let start = Instant::now();
        assert!(
            super::provider_lock_until(&dir, "member-a", start + Duration::from_millis(40))
                .unwrap_err()
                .contains("busy")
        );
        assert!(start.elapsed() < Duration::from_secs(1));
        let independent = super::provider_lock_until(
            &dir,
            "member-b",
            Instant::now() + Duration::from_millis(40),
        )
        .unwrap();
        drop(independent);
        drop(held);
        super::provider_lock(&dir, "member-a").unwrap();
        std::fs::remove_dir_all(dir).unwrap();
    }
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    static ID: AtomicU64 = AtomicU64::new(1);

    fn store() -> (PathBuf, CredentialStore) {
        let base = std::env::temp_dir().join(format!(
            "mini-credentials-test-{}-{}",
            std::process::id(),
            ID.fetch_add(1, Ordering::SeqCst)
        ));
        fs::DirBuilder::new().mode(0o700).create(&base).unwrap();
        let root = base.join("credentials");
        fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        let key = base.join("credentials.key");
        let mut f = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&key)
            .unwrap();
        f.write_all(&[7u8; 32]).unwrap();
        let opened = CredentialStore::open(&root, &key).unwrap();
        (base, opened)
    }

    fn owner(subject: &str, fill: char) -> Owner {
        Owner::new(subject, &fill.to_string().repeat(64)).unwrap()
    }

    fn grant(runner: &str) -> Grant {
        Grant {
            runner: runner.into(),
            per_call: 64,
            per_day: 2,
            not_after: 100,
            model: None,
            owner_epoch: None,
        }
    }

    fn walk(dir: &Path, out: &mut Vec<Vec<u8>>) {
        for entry in fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                walk(&path, out);
            } else {
                out.push(fs::read(&path).unwrap());
            }
        }
    }

    #[test]
    fn owners_get_their_own_secret_and_nobody_elses() {
        let (base, store) = store();
        let a = owner("11", 'a');
        let b = owner("12", 'b');
        store
            .set(
                Namespace::Owner(&a),
                "openrouter",
                &Secret::new("sk-A-token".into()).unwrap(),
            )
            .unwrap();
        store
            .set(
                Namespace::Owner(&b),
                "openrouter",
                &Secret::new("sk-B-token".into()).unwrap(),
            )
            .unwrap();
        store.grant(&a, "openrouter", grant("9")).unwrap();
        store.grant(&b, "openrouter", grant("9")).unwrap();
        assert_eq!(
            store
                .authorize(&a, "openrouter", "9", 5, Some(64), 1)
                .unwrap()
                .expose(),
            "sk-A-token"
        );
        assert_eq!(
            store
                .authorize(&b, "openrouter", "9", 5, Some(64), 1)
                .unwrap()
                .expose(),
            "sk-B-token"
        );
        // A workspace that claims subject 11 with another key is a different namespace.
        let impostor = owner("11", 'c');
        assert_eq!(
            store
                .authorize(&impostor, "openrouter", "9", 5, Some(64), 1)
                .unwrap_err(),
            refused("no-credential")
        );
        // A runner without a grant gets nothing.
        assert_eq!(
            store
                .authorize(&a, "openrouter", "10", 5, Some(64), 1)
                .unwrap_err(),
            refused("no-credential")
        );
        // Nothing on disk holds a plaintext secret.
        let mut files = Vec::new();
        walk(&base, &mut files);
        for bytes in files {
            for needle in [&b"sk-A-token"[..], b"sk-B-token"] {
                assert!(!bytes.windows(needle.len()).any(|w| w == needle));
            }
        }
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn a_sealed_secret_moved_to_another_namespace_does_not_open() {
        let (base, store) = store();
        let a = owner("11", 'a');
        let b = owner("12", 'b');
        store
            .set(
                Namespace::Owner(&a),
                "openrouter",
                &Secret::new("sk-A-token".into()).unwrap(),
            )
            .unwrap();
        store
            .set(
                Namespace::Owner(&b),
                "openrouter",
                &Secret::new("sk-B-token".into()).unwrap(),
            )
            .unwrap();
        store.grant(&b, "openrouter", grant("9")).unwrap();
        let from = base
            .join("credentials/11")
            .join("a".repeat(64))
            .join("openrouter.key");
        let to = base
            .join("credentials/12")
            .join("b".repeat(64))
            .join("openrouter.key");
        fs::copy(&from, &to).unwrap();
        let error = store
            .authorize(&b, "openrouter", "9", 5, Some(64), 1)
            .unwrap_err();
        assert!(error.contains("does not open"), "{error}");
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn caps_expiry_and_revocation_refuse_by_name() {
        let (base, store) = store();
        let a = owner("11", 'a');
        store
            .set(
                Namespace::Owner(&a),
                "openrouter",
                &Secret::new("sk-A-token".into()).unwrap(),
            )
            .unwrap();
        store.grant(&a, "openrouter", grant("9")).unwrap();
        assert_eq!(
            store
                .authorize(&a, "openrouter", "9", 101, Some(64), 1)
                .unwrap_err(),
            refused("grant-expired")
        );
        assert_eq!(
            store
                .authorize(&a, "openrouter", "9", 100, Some(65), 1)
                .unwrap_err(),
            refused("per-call-cap")
        );
        assert_eq!(
            store
                .authorize(&a, "openrouter", "9", 100, None, 1)
                .unwrap_err(),
            refused("per-call-cap")
        );
        store
            .authorize(&a, "openrouter", "9", 100, Some(64), 1)
            .unwrap();
        store
            .authorize(&a, "openrouter", "9", 100, Some(64), 1)
            .unwrap();
        assert_eq!(
            store
                .authorize(&a, "openrouter", "9", 100, Some(64), 1)
                .unwrap_err(),
            refused("per-day-cap")
        );
        // A new day resets the counter.
        store
            .authorize(&a, "openrouter", "9", 100, Some(64), 2)
            .unwrap();
        // Revoking one runner leaves the secret; revoking all removes it.
        assert!(store
            .revoke(Namespace::Owner(&a), "openrouter", Some("9"))
            .unwrap());
        assert_eq!(
            store
                .authorize(&a, "openrouter", "9", 1, Some(1), 3)
                .unwrap_err(),
            refused("no-credential")
        );
        store.grant(&a, "openrouter", grant("9")).unwrap();
        assert!(store
            .revoke(Namespace::Owner(&a), "openrouter", None)
            .unwrap());
        assert_eq!(
            store
                .authorize(&a, "openrouter", "9", 1, Some(1), 3)
                .unwrap_err(),
            refused("no-credential")
        );
        assert!(store.grant(&a, "openrouter", grant("9")).is_err());
        let listed = store.list(Namespace::Owner(&a)).unwrap();
        assert_eq!(listed["credentials"], json!([]));
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn list_shows_names_and_caps_and_debug_never_shows_values() {
        let (base, store) = store();
        let a = owner("11", 'a');
        store
            .set(
                Namespace::Owner(&a),
                "openrouter",
                &Secret::new("sk-A-token".into()).unwrap(),
            )
            .unwrap();
        store.grant(&a, "openrouter", grant("9")).unwrap();
        let listed = store.list(Namespace::Owner(&a)).unwrap().to_string();
        assert!(listed.contains("openrouter") && listed.contains("\"perDay\":\"2\""));
        assert!(!listed.contains("sk-A-token"));
        let secret = store
            .authorize(&a, "openrouter", "9", 1, Some(1), 1)
            .unwrap();
        let rendered = format!("{secret:?} {:?}", Some(&secret));
        assert!(!rendered.contains("sk-A-token"), "{rendered}");
        store
            .set(
                Namespace::Pool,
                "pool",
                &Secret::new("sk-POOL".into()).unwrap(),
            )
            .unwrap();
        let caps = Caps {
            per_call: 64,
            per_day: 1,
        };
        assert_eq!(
            store.pool("pool", "9", Some(65), caps, 1).unwrap_err(),
            refused("per-call-cap")
        );
        assert_eq!(
            store.pool("pool", "9", None, caps, 1).unwrap_err(),
            refused("per-call-cap")
        );
        assert_eq!(
            store.pool("pool", "9", Some(64), caps, 1).unwrap().expose(),
            "sk-POOL"
        );
        assert_eq!(
            store.pool("pool", "9", Some(64), caps, 1).unwrap_err(),
            refused("per-day-cap")
        );
        assert_eq!(
            store.pool("pool", "9", Some(64), caps, 2).unwrap().expose(),
            "sk-POOL"
        );
        assert_eq!(
            store.pool("other", "9", Some(1), caps, 1).unwrap_err(),
            refused("no-credential")
        );
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn native_epoch_never_upgrades_legacy_or_reused_key_grants() {
        let (base, store) = store();
        let a = owner("20", char::from(97));
        store
            .set(
                Namespace::Owner(&a),
                "chutes",
                &Secret::new("synthetic-epoch".into()).unwrap(),
            )
            .unwrap();
        let mut g = grant("9");
        g.model = Some("m".into());
        store.grant(&a, "chutes", g.clone()).unwrap();
        assert!(store
            .authorize_model_epoch(&a, "chutes", "9", Some("m"), Some("1"), 1, Some(2), 1)
            .is_err());
        g.owner_epoch = Some("1".into());
        store.grant(&a, "chutes", g.clone()).unwrap();
        assert!(store.verify_grant(&a, "chutes", "9", "m", "2", 1).is_err());
        assert!(store
            .authorize_model(&a, "chutes", "9", Some("m"), 1, Some(2), 1)
            .is_err());
        assert!(store
            .authorize_model_epoch(&a, "chutes", "9", Some("m"), Some("2"), 1, Some(2), 1)
            .is_err());
        assert!(store.verify_grant(&a, "chutes", "9", "m", "1", 1).is_ok());
        assert!(store.verify_grant(&a, "chutes", "9", "m", "1", 1).is_ok());
        // Observations and refusals consumed neither of the two daily calls.
        for _ in 0..2 {
            store
                .authorize_model_epoch(&a, "chutes", "9", Some("m"), Some("1"), 1, Some(2), 1)
                .unwrap();
        }
        assert!(store
            .authorize_model_epoch(&a, "chutes", "9", Some("m"), Some("1"), 1, Some(2), 1)
            .is_err());
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn model_scope_refuses_before_counting_and_survives_replacement() {
        let (base, store) = store();
        let a = owner("11", 'a');
        store
            .set(
                Namespace::Owner(&a),
                "chutes",
                &Secret::new("synthetic-first".into()).unwrap(),
            )
            .unwrap();
        let mut g = grant("9");
        g.model = Some("chosen/model".into());
        g.per_day = 1;
        store.grant(&a, "chutes", g).unwrap();
        assert_eq!(
            store
                .authorize(&a, "chutes", "9", 1, Some(64), 1)
                .unwrap_err(),
            refused("model-not-granted")
        );
        assert_eq!(
            store
                .authorize_model(&a, "chutes", "9", Some("other/model"), 1, Some(64), 1)
                .unwrap_err(),
            refused("model-not-granted")
        );
        store
            .set(
                Namespace::Owner(&a),
                "chutes",
                &Secret::new("synthetic-replacement".into()).unwrap(),
            )
            .unwrap();
        assert_eq!(
            store
                .authorize_model(&a, "chutes", "9", Some("chosen/model"), 1, Some(64), 1)
                .unwrap()
                .expose(),
            "synthetic-replacement"
        );
        store
            .set(
                Namespace::Owner(&a),
                "chutes",
                &Secret::new("synthetic-third".into()).unwrap(),
            )
            .unwrap();
        assert_eq!(
            store
                .authorize_model(&a, "chutes", "9", Some("chosen/model"), 1, Some(64), 1)
                .unwrap_err(),
            refused("per-day-cap")
        );
        assert_eq!(
            store.list(Namespace::Owner(&a)).unwrap()["credentials"][0]["grants"][0]["model"],
            "chosen/model"
        );
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn interrupted_revoke_cannot_resurrect_authority_on_replacement() {
        let (base, store) = store();
        let a = owner("11", 'a');
        store
            .set(
                Namespace::Owner(&a),
                "openrouter",
                &Secret::new("synthetic-before".into()).unwrap(),
            )
            .unwrap();
        store.grant(&a, "openrouter", grant("9")).unwrap();
        let dir = store.directory(Namespace::Owner(&a), false).unwrap();
        // Durable first step of whole-provider revoke, then process loss.
        store.write_grants(&dir, "openrouter", &[]).unwrap();
        drop(store);
        let store = CredentialStore::open(&base.join("credentials"), &base.join("credentials.key"))
            .unwrap();
        store
            .set(
                Namespace::Owner(&a),
                "openrouter",
                &Secret::new("synthetic-after".into()).unwrap(),
            )
            .unwrap();
        assert_eq!(
            store
                .authorize(&a, "openrouter", "9", 1, Some(1), 1)
                .unwrap_err(),
            refused("no-credential")
        );
        assert!(store
            .revoke(Namespace::Owner(&a), "openrouter", None)
            .unwrap());
        assert!(!store
            .revoke(Namespace::Owner(&a), "openrouter", None)
            .unwrap());
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn scoped_grants_are_versioned_and_never_coerced_from_malformed_values() {
        let legacy = json!({"runner":"9","perCall":"64","perDay":"2","notAfter":"100"});
        assert_eq!(Grant::from_json(&legacy).unwrap().model, None);
        for model in [
            json!(null),
            json!(42),
            json!(""),
            json!("bad\nmodel"),
            json!("x".repeat(257)),
        ] {
            let mut bad = legacy.clone();
            bad["model"] = model;
            assert!(Grant::from_json(&bad).is_err());
        }
        let (base, store) = store();
        let a = owner("11", 'a');
        store
            .set(
                Namespace::Owner(&a),
                "chutes",
                &Secret::new("synthetic-key".into()).unwrap(),
            )
            .unwrap();
        let mut g = grant("9");
        g.model = Some("m".into());
        store.grant(&a, "chutes", g).unwrap();
        let path = store
            .directory(Namespace::Owner(&a), false)
            .unwrap()
            .join("chutes.grants.json");
        let mut record: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        assert_eq!(record["type"], SCOPED_GRANTS_TYPE);
        record["type"] = json!(GRANTS_TYPE);
        replace_private(&path, &serde_json::to_vec(&record).unwrap()).unwrap();
        assert!(store
            .authorize_model(&a, "chutes", "9", Some("m"), 1, Some(1), 1)
            .is_err());
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn concurrent_grants_retain_both_runners_and_lock_symlinks_refuse() {
        let (base, store) = store();
        let a = owner("11", 'a');
        store
            .set(
                Namespace::Owner(&a),
                "chutes",
                &Secret::new("synthetic-key".into()).unwrap(),
            )
            .unwrap();
        std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for runner in ["9", "10", "11", "12"] {
                let base = &base;
                let a = &a;
                handles.push(scope.spawn(move || {
                    CredentialStore::open(&base.join("credentials"), &base.join("credentials.key"))
                        .unwrap()
                        .grant(a, "chutes", grant(runner))
                        .unwrap();
                }));
            }
            for handle in handles {
                handle.join().unwrap();
            }
        });
        assert_eq!(
            store.list(Namespace::Owner(&a)).unwrap()["credentials"][0]["grants"]
                .as_array()
                .unwrap()
                .len(),
            4
        );
        let dir = store.directory(Namespace::Owner(&a), false).unwrap();
        std::os::unix::fs::symlink(
            base.join("credentials.key"),
            dir.join("evil.authority.lock"),
        )
        .unwrap();
        assert!(store
            .set(
                Namespace::Owner(&a),
                "evil",
                &Secret::new("synthetic-key".into()).unwrap()
            )
            .is_err());
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn signed_choice_is_task_owner_route_and_catalogue_bound() {
        use ring::signature::KeyPair;
        let (base, store) = store();
        let seed = [42u8; 32];
        let signing = ring::signature::Ed25519KeyPair::from_seed_unchecked(&seed).unwrap();
        let a = Owner::new("11", &hex(signing.public_key().as_ref())).unwrap();
        let table=ProviderTable::parse(br#"{"type":"mini-provider-table-v2","providers":[{"name":"chutes","endpoint":"https://example.test/v1/chat/completions","kind":"openai-compatible","models":["m","n"],"credential":"user"}]}"#).unwrap();
        store
            .set(
                Namespace::Owner(&a),
                "chutes",
                &Secret::new("synthetic-choice-key".into()).unwrap(),
            )
            .unwrap();
        let mut g = grant("9");
        g.model = Some("m".into());
        store.grant(&a, "chutes", g).unwrap();
        let selected =
            choice::Choice::signed(a.clone(), "9", "88", "chutes", "m", &table, &seed).unwrap();
        store.choose(&selected, &table).unwrap();
        assert_eq!(store.selected(&a, "9", "88", &table).unwrap(), selected);
        assert!(store.selected(&a, "10", "88", &table).is_err());
        assert!(store.selected(&a, "9", "89", &table).is_err());
        assert!(store
            .selected(&owner("11", 'c'), "9", "88", &table)
            .is_err());
        for field in ["task", "runner", "model", "provider", "tableSha256"] {
            let mut changed = selected.to_json();
            changed[field] = json!("tampered");
            assert!(choice::Choice::from_json(&changed).is_err(), "{field}");
        }
        let mut bad = selected.to_json();
        bad["signature"] = json!("é".repeat(64));
        assert!(choice::Choice::from_json(&bad).is_err());
        let mut changed_table = table;
        changed_table.sha256 = "b".repeat(64);
        assert!(store.selected(&a, "9", "88", &changed_table).is_err());
        store
            .revoke(Namespace::Owner(&a), "chutes", Some("9"))
            .unwrap();
        assert!(store.selected(&a, "9", "88", &changed_table).is_err());
        let mut disk = Vec::new();
        walk(&base, &mut disk);
        for bytes in disk {
            assert!(!bytes.windows(20).any(|w| w == b"synthetic-choice-key"));
        }
        fs::remove_dir_all(base).unwrap();
    }

    #[test]
    fn table_selects_one_row_without_payer_fallthrough() {
        let table = ProviderTable::parse(
            br#"{"type":"mini-provider-table-v2","providers":[
            {"name":"openrouter","endpoint":"https://openrouter.ai/api/v1/chat/completions",
             "kind":"openai-compatible","models":["m1","shared"],"credential":"user"},
            {"name":"pool","endpoint":"https://openrouter.ai/api/v1/chat/completions",
             "kind":"openai-compatible","models":["shared"],"credential":"pool",
             "caps":{"perCall":"1024","perDay":"50"}},
            {"name":"homelab","endpoint":"http://127.0.0.1:18081/v1/chat/completions",
             "kind":"openai-compatible","models":["bonsai"],"credential":"homelab"}]}"#,
        )
        .unwrap();
        assert_eq!(table.select("shared", None).unwrap().name, "openrouter");
        assert_eq!(table.select("shared", Some("pool")).unwrap().name, "pool");
        assert_eq!(
            table.select("bonsai", None).unwrap().credential,
            CredentialSource::Homelab
        );
        assert_eq!(
            table.select("shared", Some("pool")).unwrap().caps,
            Some(Caps {
                per_call: 1024,
                per_day: 50
            })
        );
        assert_eq!(
            table.select("m1", Some("pool")).unwrap_err(),
            refused("no-route")
        );
        assert_eq!(
            table.select("absent", None).unwrap_err(),
            refused("no-route")
        );
        for bad in [
            r#"{"type":"mini-provider-table-v2","providers":[{"name":"x","endpoint":"https://a.b/v1/chat/completions?x=1","kind":"openai-compatible","models":["m"],"credential":"user"}]}"#,
            r#"{"type":"mini-provider-table-v2","providers":[{"name":"x","endpoint":"http://10.0.0.1/v1/chat/completions","kind":"openai-compatible","models":["m"],"credential":"homelab"}]}"#,
            // the HERMES-KEYS v1 shapes: `none` and a row tariff refuse to load
            r#"{"type":"mini-provider-table-v1","providers":[{"name":"x","endpoint":"https://a.b/v1/chat/completions","kind":"openai-compatible","models":["m"],"credential":"user"}]}"#,
            r#"{"type":"mini-provider-table-v2","providers":[{"name":"x","endpoint":"http://127.0.0.1:9/v1/chat/completions","kind":"openai-compatible","models":["m"],"credential":"none"}]}"#,
            r#"{"type":"mini-provider-table-v2","providers":[{"name":"x","endpoint":"https://a.b/v1/chat/completions","kind":"openai-compatible","models":["m"],"credential":"user","tariff":{"version":"1","inputMicroPerMillion":"1","outputMicroPerMillion":"1"}}]}"#,
            // a pool row needs caps; only a pool row may carry them
            r#"{"type":"mini-provider-table-v2","providers":[{"name":"x","endpoint":"https://a.b/v1/chat/completions","kind":"openai-compatible","models":["m"],"credential":"pool"}]}"#,
            r#"{"type":"mini-provider-table-v2","providers":[{"name":"x","endpoint":"https://a.b/v1/chat/completions","kind":"openai-compatible","models":["m"],"credential":"user","caps":{"perCall":"1","perDay":"1"}}]}"#,
            r#"{"type":"mini-provider-table-v2","providers":[{"name":"x","endpoint":"https://a.b/v1/chat/completions","kind":"openai-compatible","models":["m"],"credential":"pool","caps":{"perCall":"0","perDay":"1"}}]}"#,
            r#"{"type":"mini-provider-table-v2","providers":[{"name":"x","endpoint":"https://a.b/v1/chat/completions","kind":"anthropic","models":["m"],"credential":"user"}]}"#,
            r#"{"type":"mini-provider-table-v2","providers":[{"name":"x","endpoint":"https://a.b/v1/chat/completions","kind":"openai-compatible","models":["m"],"credential":"user","key":"sk"}]}"#,
            r#"{"type":"mini-provider-table-v2","providers":[{"name":"x","endpoint":"https://a.b/v1/chat/completions","kind":"openai-compatible","models":["m"],"credential":"user"},{"name":"x","endpoint":"https://a.b/v1/chat/completions","kind":"openai-compatible","models":["m"],"credential":"pool"}]}"#,
        ] {
            assert!(ProviderTable::parse(bad.as_bytes()).is_err(), "{bad}");
        }
    }

    #[test]
    fn endpoint_is_exact_and_openrouter_path_is_supported() {
        assert!(validate_endpoint("https://openrouter.ai/api/v1/chat/completions").is_ok());
        assert!(
            validate_endpoint("https://openrouter.ai/api/v1/chat/completions?model=x").is_err()
        );
        assert!(validate_endpoint("http://openrouter.ai/api/v1/chat/completions").is_err());
        assert!(validate_endpoint("https://openrouter.ai/other").is_err());
        assert!(validate_endpoint("http://127.0.0.1:9/v1/chat/completions").is_ok());
        assert!(validate_endpoint("https://user@host/v1/chat/completions").is_err());
    }

    #[test]
    fn secret_input_is_one_trimmed_line() {
        assert_eq!(secret_from_input(b"  sk-x\n").unwrap().expose(), "sk-x");
        assert!(secret_from_input(b"sk-x\nsk-y\n").is_err());
        assert!(secret_from_input(b"sk x\n").is_err());
        assert!(secret_from_input(b"\n").is_err());
    }
}
