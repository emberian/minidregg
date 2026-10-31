//! The broker: config, custody checks at start, the accept loop, roles, the
//! audit log, and dispatch. The operations live in [`member`], [`provider`] and
//! [`discord`].
use crate::peer::{self, Peer};
use crate::wire;
use serde_json::{json, Map, Value};
use std::collections::HashMap;
use std::fs::{File, OpenOptions};
use std::io::Write;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

pub use crate::credentials;

pub mod discord;
pub mod member;
pub mod native;
pub mod provider;
pub mod ticket;

pub const CONFIG_TYPE: &str = "mini-keys-broker-v1";
const MAX_CONFIG: u64 = 16_384;
/// Connection slots, by the highest role a peer holds: one class cannot take
/// another's, so session accounts can never starve the Hermes controller.
const SLOTS: [(Class, usize); 4] = [(Class::Provider, 8), (Class::Operator, 2), (Class::Discord, 2), (Class::Member, 20)];
/// Within the member class, one uid holds at most this many.
const MEMBER_SLOTS_PER_UID: usize = 4;
/// Every exchange but a provider forward ends within this.
pub const EXCHANGE: Duration = Duration::from_secs(30);
pub const CURL: &str = "/usr/bin/curl";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Role {
    Member,
    Provider,
    Discord,
    Operator,
}

impl Role {
    pub fn name(self) -> &'static str {
        match self {
            Role::Member => "member",
            Role::Provider => "provider",
            Role::Discord => "discord",
            Role::Operator => "operator",
        }
    }
    fn parse(name: &str) -> Result<Self, String> {
        Ok(match name {
            "member" => Role::Member,
            "provider" => Role::Provider,
            "discord" => Role::Discord,
            "operator" => Role::Operator,
            _ => return Err(format!("unknown peer role {name:?}")),
        })
    }
}

/// The slot class of a peer: its highest role.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Class {
    Provider,
    Operator,
    Discord,
    Member,
}

impl Class {
    fn of(roles: &[Role]) -> Option<Class> {
        [(Role::Provider, Class::Provider), (Role::Operator, Class::Operator), (Role::Discord, Class::Discord), (Role::Member, Class::Member)]
            .into_iter()
            .find(|(r, _)| roles.contains(r))
            .map(|(_, c)| c)
    }
}

/// The largest first frame a peer holding `roles` can need. It is read before
/// the operation is known, so it is sized by role: a session account's first
/// frame is `{"op":"member-action"}`, never megabytes.
pub fn first_frame_bound(roles: &[Role]) -> usize {
    roles
        .iter()
        .map(|r| match r {
            Role::Member => 4096,
            Role::Operator => 16_384,
            Role::Discord => 65_536,
            Role::Provider => 2 * wire::MAX_PROVIDER_REQUEST + 4096,
        })
        .max()
        .unwrap_or(1024)
}

/// The role an operation needs. An operation not listed here does not exist.
pub fn role_for(op: &str) -> Option<Role> {
    Some(match op {
        "hello" => return None,
        "member-action" => Role::Member,
        "provider-authorize" | "provider-forward" | "provider-verify-grant" | "provider-selected-choice" => Role::Provider,
        "discord-post" | "discord-read" => Role::Discord,
        "pool" => Role::Operator,
        _ => return None,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PeerRule {
    pub role: Role,
    pub uids: Vec<u32>,
    /// Matched against the peer's effective gid at connect (SO_PEERCRED): the
    /// member rule names the session accounts' primary group.
    pub gids: Vec<u32>,
}

#[derive(Clone, Debug)]
pub struct Credentials {
    pub host: PathBuf,
    /// The Host image's SHA-256 from the candidate manifest.
    pub host_sha256: String,
    pub host_config: PathBuf,
    pub public_socket: PathBuf,
    /// The only uid whose operation-144 answer the broker accepts: the account
    /// serving the Host's public socket.
    pub public_socket_uid: u32,
    pub providers: PathBuf,
    pub root: PathBuf,
    pub key: PathBuf,
    pub namespace_helper: Option<(PathBuf, String)>,
}

#[derive(Clone, Debug)]
pub struct Discord {
    /// mini-keys 0600: `{"type":"mini-discord-mirror-secrets-v1","webhookUrl","channelUrl","botToken"}`.
    pub mirror: PathBuf,
}

#[derive(Clone, Debug)]
pub struct Config {
    pub socket: PathBuf,
    pub socket_group: Option<u32>,
    pub audit: PathBuf,
    pub spool: PathBuf,
    /// The TEST shape: the broker shares one account with its peers (a sandbox
    /// journey, the crate's tests). A root-owned config (every deployed box's)
    /// cannot select it, the broker still never runs as root, and `hello` and
    /// every audit line say so.
    pub single_account: bool,
    pub peers: Vec<PeerRule>,
    pub credentials: Option<Credentials>,
    pub discord: Option<Discord>,
    /// The uid that must own every root-custody input (the config, the provider
    /// table, the namespace helper): 0 on a box; a test names itself.
    pub trust_owner: u32,
    /// Bytes of the config file, for its digest in `hello`.
    pub sha256: String,
}

fn fields(value: &Value, allowed: &[&str], label: &str) -> Result<(), String> {
    match value.as_object() {
        Some(m) if m.keys().all(|k| allowed.contains(&k.as_str())) => Ok(()),
        Some(_) => Err(format!("{label} has a field outside {allowed:?}")),
        None => Err(format!("{label} must be an object")),
    }
}

fn abs(value: &Value, key: &str) -> Result<PathBuf, String> {
    value
        .get(key)
        .and_then(Value::as_str)
        .filter(|s| s.starts_with('/') && !s.contains("/../") && !s.ends_with("/.."))
        .map(PathBuf::from)
        .ok_or_else(|| format!("{key} must be an absolute path"))
}

fn ids(value: Option<&Value>, label: &str) -> Result<Vec<u32>, String> {
    match value {
        None => Ok(vec![]),
        Some(Value::Array(items)) => items
            .iter()
            .map(|v| v.as_u64().filter(|n| *n <= u32::MAX as u64).map(|n| n as u32).ok_or_else(|| format!("{label} must be numeric ids")))
            .collect(),
        Some(_) => Err(format!("{label} must be an array")),
    }
}

impl Config {
    /// Parse and custody-check a broker config. On a box `trust_owner` is 0
    /// (`mini-keys serve` passes nothing else).
    pub fn load(path: &Path, trust_owner: u32) -> Result<Self, String> {
        let bytes = crate::client::custody_file(path, trust_owner, MAX_CONFIG)?;
        Self::parse(&bytes, trust_owner)
    }

    pub fn parse(bytes: &[u8], trust_owner: u32) -> Result<Self, String> {
        use sha2::{Digest, Sha256};
        let v: Value = serde_json::from_slice(bytes).map_err(|_| "broker config is not JSON")?;
        fields(&v, &["type", "socket", "socketGroup", "audit", "spool", "singleAccount", "peers", "credentials", "discord"], "broker config")?;
        if v["type"] != CONFIG_TYPE {
            return Err(format!("broker config is not {CONFIG_TYPE}"));
        }
        let socket_group = match v.get("socketGroup") {
            None => None,
            Some(g) => Some(g.as_u64().filter(|n| *n <= u32::MAX as u64).ok_or("socketGroup must be a gid")? as u32),
        };
        let single_account = match v.get("singleAccount") {
            None => false,
            Some(Value::Bool(b)) => *b,
            Some(_) => return Err("singleAccount must be a boolean".into()),
        };
        if single_account && trust_owner == 0 {
            return Err("singleAccount is the test shape: a root-owned (deployed) broker config cannot select it".into());
        }
        let mut peers = Vec::new();
        for rule in v.get("peers").and_then(Value::as_array).ok_or("peers must be an array")? {
            fields(rule, &["role", "uids", "gids"], "peer rule")?;
            let role = Role::parse(rule.get("role").and_then(Value::as_str).ok_or("peer rule needs a role")?)?;
            let uids = ids(rule.get("uids"), "uids")?;
            let gids = ids(rule.get("gids"), "gids")?;
            if uids.is_empty() && gids.is_empty() {
                return Err(format!("peer rule {} names nobody", role.name()));
            }
            if role != Role::Member && !gids.is_empty() {
                return Err(format!("peer rule {} must name uids: only members are admitted by group", role.name()));
            }
            peers.push(PeerRule { role, uids, gids });
        }
        let credentials = match v.get("credentials") {
            None => None,
            Some(c) => {
                fields(c, &["host", "hostSha256", "hostConfig", "publicSocket", "publicSocketUid", "providers", "root", "key", "namespaceHelper", "namespaceHelperSha256"], "credentials")?;
                let root = abs(c, "root")?;
                let key = abs(c, "key")?;
                if key.starts_with(&root) {
                    return Err("the seal key must live outside the credential root".into());
                }
                let namespace_helper = match (c.get("namespaceHelper"), c.get("namespaceHelperSha256")) {
                    (None, None) => None,
                    (Some(_), Some(sha)) => {
                        let sha = sha.as_str().filter(|s| s.len() == 64 && wire::unhex(s).is_ok()).ok_or("namespaceHelperSha256 must be 64 lowercase hex")?;
                        Some((abs(c, "namespaceHelper")?, sha.to_owned()))
                    }
                    _ => return Err("namespaceHelper and namespaceHelperSha256 are pinned together".into()),
                };
                let host_sha256 = c
                    .get("hostSha256")
                    .and_then(Value::as_str)
                    .filter(|s| s.len() == 64 && wire::unhex(s).is_ok())
                    .ok_or("hostSha256 must be the candidate's 64-lowercase-hex Host image digest")?
                    .to_owned();
                let public_socket_uid = c
                    .get("publicSocketUid")
                    .and_then(Value::as_u64)
                    .filter(|n| *n <= u32::MAX as u64)
                    .ok_or("publicSocketUid must be the numeric uid serving the public socket")? as u32;
                Some(Credentials {
                    host: abs(c, "host")?,
                    host_sha256,
                    host_config: abs(c, "hostConfig")?,
                    public_socket: abs(c, "publicSocket")?,
                    public_socket_uid,
                    providers: abs(c, "providers")?,
                    root,
                    key,
                    namespace_helper,
                })
            }
        };
        let discord = match v.get("discord") {
            None => None,
            Some(d) => {
                fields(d, &["mirror"], "discord")?;
                Some(Discord { mirror: abs(d, "mirror")? })
            }
        };
        Ok(Config {
            socket: abs(&v, "socket")?,
            socket_group,
            audit: abs(&v, "audit")?,
            spool: abs(&v, "spool")?,
            single_account,
            peers,
            credentials,
            discord,
            trust_owner,
            sha256: wire::hex(&Sha256::digest(bytes)),
        })
    }

    /// The broker's own load (`mini-keys serve`): the config belongs to root or to
    /// the broker's own account, and that owner (with root) is the one trusted
    /// for every root-custody input. On a box it is root; in a sandbox journey
    /// that runs everything as one account, it is that account.
    pub fn load_for_broker(path: &Path) -> Result<Self, String> {
        let owner = std::fs::symlink_metadata(path).map_err(|_| format!("{} is unavailable", path.display()))?.uid();
        if owner != 0 && owner != peer::euid() {
            return Err(format!("{} must belong to root or to the broker's own account (uid {})", path.display(), peer::euid()));
        }
        Self::load(path, owner)
    }

    pub fn roles_of(&self, peer: &Peer) -> Vec<Role> {
        let mut roles = Vec::new();
        for rule in &self.peers {
            if (rule.uids.contains(&peer.uid) || rule.gids.contains(&peer.gid)) && !roles.contains(&rule.role) {
                roles.push(rule.role);
            }
        }
        roles
    }
}

/// The provider table names where money and members' keys may be sent: it
/// belongs to root or to the config's owner, and nobody else may write it.
pub fn provider_table(path: &Path, trust_owner: u32) -> Result<credentials::ProviderTable, String> {
    let owner = std::fs::symlink_metadata(path).map_err(|e| format!("provider table: {e}"))?.uid();
    if owner != 0 && owner != trust_owner {
        return Err("the provider table must belong to root (or the broker config's owner)".into());
    }
    credentials::ProviderTable::load(path, owner)
}

/// A directory nobody but `owner` (or root) may write: a file in it cannot be
/// swapped by another account.
pub fn steady_dir(path: &Path, owner: u32, label: &str) -> Result<(), String> {
    let meta = std::fs::symlink_metadata(path).map_err(|_| format!("{label} {} is unavailable", path.display()))?;
    if !meta.file_type().is_dir() || (meta.uid() != owner && meta.uid() != 0) || meta.mode() & 0o022 != 0 {
        return Err(format!("{label} {} must be a directory owned by uid {owner} or root, writable by no other account", path.display()));
    }
    Ok(())
}

/// A secret file: a regular file of this account's, readable by no other, in a
/// directory nobody else can write.
pub fn secret_file(path: &Path, label: &str, bound: u64) -> Result<(), String> {
    let me = peer::euid();
    let meta = std::fs::symlink_metadata(path).map_err(|_| format!("{label} {} is unavailable", path.display()))?;
    if !meta.file_type().is_file() || meta.uid() != me || meta.mode() & 0o077 != 0 || meta.len() > bound {
        return Err(format!("{label} {} must be a regular file of the broker account (uid {me}) with no group or other bits", path.display()));
    }
    steady_dir(path.parent().ok_or("secret file has no directory")?, me, label)
}

pub struct Broker {
    pub config: Config,
    pub tickets: ticket::Tickets,
    pub host: Option<native::HostPin>,
    audit: Mutex<File>,
    slots: Mutex<HashMap<(Class, Option<u32>), usize>>,
}

/// One held connection slot; released on drop, so a panicking handler cannot leak it.
struct Slot {
    broker: Arc<Broker>,
    keys: Vec<(Class, Option<u32>)>,
}

impl Drop for Slot {
    fn drop(&mut self) {
        let mut slots = self.broker.slots.lock().unwrap_or_else(|p| p.into_inner());
        for key in &self.keys {
            if let Some(n) = slots.get_mut(key) {
                *n = n.saturating_sub(1);
            }
        }
    }
}

/// What an audit line records about the request's progress.
pub enum Outcome<'a> {
    /// Written, and made durable, before any effect: an operation that cannot
    /// be audited does not run.
    Begin,
    Ok,
    Refused(&'a Refusal),
}

/// What one request leaves in the audit log, beside who and which operation.
#[derive(Default)]
pub struct Note(pub Map<String, Value>);

impl Note {
    pub fn with(mut self, key: &str, value: impl Into<Value>) -> Self {
        self.0.insert(key.into(), value.into());
        self
    }
    pub fn set(&mut self, key: &str, value: impl Into<Value>) {
        self.0.insert(key.into(), value.into());
    }
}

/// A named refusal and what the audit log says about it.
pub struct Refusal {
    pub code: String,
    pub detail: String,
}

pub fn refuse(code: &str, detail: impl Into<String>) -> Refusal {
    Refusal { code: code.into(), detail: detail.into() }
}

/// A credential-store error: a `provider-refused:CODE` keeps its name (the
/// gateway turns it into a named HTTP refusal); anything else is `credential-store`.
pub fn store_refusal(error: String) -> Refusal {
    if error.starts_with(credentials::REFUSED) {
        Refusal { code: error.clone(), detail: error }
    } else {
        Refusal { code: "credential-store".into(), detail: error }
    }
}

impl Broker {
    /// Check every custody premise, then bind the socket. Nothing is served yet.
    pub fn start(config: Config) -> Result<(Arc<Broker>, UnixListener), String> {
        let me = peer::euid();
        if me == 0 {
            return Err("the broker never runs as root: run it as its own account (mini-keys)".into());
        }
        if !config.single_account {
            if config.peers.iter().any(|r| r.uids.contains(&me)) {
                return Err(format!("a peer rule names the broker's own uid {me}: a client account must not be the account holding the secrets"));
            }
            if config.peers.iter().any(|r| r.gids.contains(&peer::egid())) {
                return Err("a member rule names the broker's own primary group".into());
            }
        }
        let mut host = None;
        if let Some(c) = &config.credentials {
            secret_file(&c.key, "the seal key", 32)?;
            credentials::CredentialStore::open(&c.root, &c.key)?;
            let table = provider_table(&c.providers, config.trust_owner)?;
            // Ember's ruling (2026-10-26): the provider-side hard cap on the pool
            // key is never the first line. A deployed broker holds every pool row
            // to its own spend ceiling.
            if !config.single_account {
                if let Some(row) = table.rows.iter().find(|r| r.caps.is_some_and(|c| c.spend.is_none())) {
                    return Err(format!("pool row {} has no caps.ceilingMicroUsd/callMicroUsd: a deployed broker never spends the operator's key without its own ceiling", row.name));
                }
            }
            let pin = native::HostPin::new(&c.host, &c.host_sha256);
            pin.current()?;
            host = Some(pin);
        }
        if let Some(d) = &config.discord {
            discord::Secrets::load(&d.mirror)?;
        }
        let spool_parent = config.spool.parent().ok_or("spool has no parent")?;
        steady_dir(spool_parent, me, "spool parent")?;
        match std::fs::DirBuilder::new().mode(0o700).create(&config.spool) {
            Ok(()) => {}
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(e) => return Err(format!("spool {}: {e}", config.spool.display())),
        }
        let meta = std::fs::symlink_metadata(&config.spool).map_err(|e| e.to_string())?;
        if !meta.is_dir() || meta.uid() != me || meta.mode() & 0o077 != 0 {
            return Err(format!("spool {} must be the broker's 0700 directory", config.spool.display()));
        }
        // A crash mid-forward leaves a member's prompt and the reply in the spool,
        // and a reused pid would then collide with it: nothing in flight survives
        // a start, so the residue goes.
        for entry in std::fs::read_dir(&config.spool).map_err(|e| format!("spool: {e}"))? {
            let path = entry.map_err(|e| e.to_string())?.path();
            if path.file_name().and_then(|n| n.to_str()).is_some_and(|n| n.starts_with("forward-") || n.starts_with("discord-")) {
                let _ = std::fs::remove_file(&path);
            }
        }
        let tickets = ticket::Tickets::open(&config.spool)?;
        steady_dir(config.audit.parent().ok_or("audit has no parent")?, me, "audit directory")?;
        let audit = OpenOptions::new()
            .create(true)
            .append(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&config.audit)
            .map_err(|e| format!("audit log {}: {e}", config.audit.display()))?;
        let am = audit.metadata().map_err(|e| e.to_string())?;
        if !am.is_file() || am.uid() != me || am.mode() & 0o077 != 0 {
            return Err(format!("audit log {} must be the broker's 0600 file", config.audit.display()));
        }
        let socket_dir = config.socket.parent().ok_or("socket has no directory")?;
        steady_dir(socket_dir, me, "socket directory")?;
        if let Ok(meta) = std::fs::symlink_metadata(&config.socket) {
            use std::os::unix::fs::FileTypeExt;
            if !meta.file_type().is_socket() || meta.uid() != me {
                return Err(format!("{} exists and is not this broker's socket", config.socket.display()));
            }
            std::fs::remove_file(&config.socket).map_err(|e| e.to_string())?;
        }
        let listener = UnixListener::bind(&config.socket).map_err(|e| format!("bind {}: {e}", config.socket.display()))?;
        let mode = if config.socket_group.is_some() { 0o660 } else { 0o600 };
        std::fs::set_permissions(&config.socket, std::fs::Permissions::from_mode(mode)).map_err(|e| e.to_string())?;
        if let Some(gid) = config.socket_group {
            use std::os::unix::ffi::OsStrExt;
            let c = std::ffi::CString::new(config.socket.as_os_str().as_bytes()).map_err(|_| "socket path")?;
            if unsafe { libc::chown(c.as_ptr(), u32::MAX, gid) } != 0 {
                return Err(format!("socket group {gid}: {}", std::io::Error::last_os_error()));
            }
        }
        let broker = Arc::new(Broker { config, tickets, host, audit: Mutex::new(audit), slots: Mutex::new(HashMap::new()) });
        broker.record(&Peer { uid: me, gid: peer::egid(), pid: std::process::id() as i32 }, &[], "start", Outcome::Ok, Note::default().with("configSha256", broker.config.sha256.clone()).with("singleAccount", broker.config.single_account)).map_err(|r| r.detail)?;
        Ok((broker, listener))
    }

    /// Serve until the listener fails. One thread per connection, within the
    /// peer's slot class ([`SLOTS`], [`MEMBER_SLOTS_PER_UID`]); a connection over
    /// its class's bound is refused `busy` without blocking the accept loop.
    pub fn serve(self: Arc<Self>, listener: UnixListener) -> Result<(), String> {
        for stream in listener.incoming() {
            let mut stream = match stream {
                Ok(s) => s,
                Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(e) => return Err(format!("accept: {e}")),
            };
            let Ok(peer) = peer::of(&stream) else { continue };
            let roles = self.config.roles_of(&peer);
            let Some(class) = Class::of(&roles) else {
                let r = refuse("peer-not-allowed", format!("uid {} gid {} holds no role at this broker", peer.uid, peer.gid));
                let _ = self.record(&peer, &roles, "connect", Outcome::Refused(&r), Note::default());
                refuse_now(&mut stream, &r);
                continue;
            };
            let Some(slot) = self.take_slot(class, peer.uid) else {
                refuse_now(&mut stream, &refuse("busy", "the broker is at this account's connection bound; retry"));
                continue;
            };
            let broker = self.clone();
            std::thread::spawn(move || {
                let _slot = slot;
                broker.connection(stream, peer, roles);
            });
        }
        Ok(())
    }

    fn take_slot(self: &Arc<Self>, class: Class, uid: u32) -> Option<Slot> {
        let bound = SLOTS.iter().find(|(c, _)| *c == class).map(|(_, n)| *n).unwrap_or(0);
        let mut keys = vec![(class, None)];
        if class == Class::Member {
            keys.push((class, Some(uid)));
        }
        let mut slots = self.slots.lock().unwrap_or_else(|p| p.into_inner());
        let held = |k: &(Class, Option<u32>)| slots.get(k).copied().unwrap_or(0);
        if held(&(class, None)) >= bound || (class == Class::Member && held(&(class, Some(uid))) >= MEMBER_SLOTS_PER_UID) {
            return None;
        }
        for key in &keys {
            *slots.entry(*key).or_insert(0) += 1;
        }
        drop(slots);
        Some(Slot { broker: self.clone(), keys })
    }

    /// One audit line, written through to the disk. Never a secret: callers put
    /// digests and names in `note`. An error is returned, never swallowed.
    pub fn record(&self, peer: &Peer, roles: &[Role], op: &str, outcome: Outcome<'_>, note: Note) -> Result<(), Refusal> {
        let mut line = note.0;
        line.insert("at".into(), json!(ticket::now()));
        line.insert("peer".into(), json!({"uid":peer.uid,"gid":peer.gid,"pid":peer.pid}));
        line.insert("roles".into(), json!(roles.iter().map(|r| r.name()).collect::<Vec<_>>()));
        line.insert("op".into(), json!(op));
        match outcome {
            Outcome::Begin => {
                line.insert("outcome".into(), json!("begin"));
            }
            Outcome::Ok => {
                line.insert("outcome".into(), json!("ok"));
            }
            Outcome::Refused(r) => {
                line.insert("outcome".into(), json!("refused"));
                line.insert("refused".into(), json!(r.code));
                line.insert("detail".into(), json!(r.detail.chars().take(300).collect::<String>()));
            }
        }
        if self.config.single_account {
            line.insert("singleAccount".into(), json!(true));
        }
        let written = serde_json::to_vec(&Value::Object(line)).map_err(|e| e.to_string()).and_then(|mut bytes| {
            bytes.push(b'\n');
            let mut f = self.audit.lock().map_err(|_| "audit lock poisoned".to_owned())?;
            f.write_all(&bytes).map_err(|e| e.to_string())
        });
        written.map_err(|e| {
            eprintln!("mini-keys: AUDIT WRITE FAILED ({op}): {e}");
            refuse("audit-unavailable", format!("the audit log {} cannot be written: {e}", self.config.audit.display()))
        })
    }

    /// Record a request's outcome after its effect: the effect already
    /// happened, so a failure here is reported loudly (stderr, the journal)
    /// rather than undone.
    fn settle(&self, peer: &Peer, roles: &[Role], op: &str, outcome: Outcome<'_>, note: Note) {
        let _ = self.record(peer, roles, op, outcome, note);
    }

    fn connection(&self, mut stream: UnixStream, peer: Peer, roles: Vec<Role>) {
        let end = Instant::now() + EXCHANGE;
        let request = match wire::recv(&mut stream, first_frame_bound(&roles), end) {
            Ok(v) => v,
            Err(e) => {
                let r = refuse("bad-request", e);
                self.settle(&peer, &roles, "read", Outcome::Refused(&r), Note::default());
                let _ = wire::send(&mut stream, &wire::refusal(&r.code, &r.detail), end);
                return;
            }
        };
        let op = request.get("op").and_then(Value::as_str).unwrap_or("").to_owned();
        let granted = match role_for(&op) {
            None if op == "hello" => true,
            None => {
                let r = refuse("op-unknown", format!("the broker has no operation {op:?}"));
                self.settle(&peer, &roles, "unknown", Outcome::Refused(&r), Note::default());
                let _ = wire::send(&mut stream, &wire::refusal(&r.code, &r.detail), end);
                return;
            }
            Some(role) => roles.contains(&role),
        };
        if !granted {
            let r = refuse("op-not-granted", format!("{op} needs role {}; uid {} holds {:?}", role_for(&op).map(Role::name).unwrap_or("?"), peer.uid, roles.iter().map(|r| r.name()).collect::<Vec<_>>()));
            self.settle(&peer, &roles, &op, Outcome::Refused(&r), Note::default());
            let _ = wire::send(&mut stream, &wire::refusal(&r.code, &r.detail), end);
            return;
        }
        // Law: refusal must be loud. Nothing with an effect runs unaudited.
        if op != "hello" {
            if let Err(r) = self.record(&peer, &roles, &op, Outcome::Begin, Note::default()) {
                if op == "member-action" {
                    let _ = wire::send(&mut stream, &json!({"type":member::REFUSED,"error":r.detail}), end);
                } else {
                    let _ = wire::send(&mut stream, &wire::refusal(&r.code, &r.detail), end);
                }
                return;
            }
        }
        let mut note = Note::default();
        // member-action owns its frames (the ssh key-service exchange, verbatim).
        if op == "member-action" {
            let outcome = member::exchange(self, &peer, &mut stream, &mut note);
            self.settle(&peer, &roles, &op, outcome.as_ref().map_or_else(Outcome::Refused, |_| Outcome::Ok), note);
            return;
        }
        let result = match op.as_str() {
            "hello" => {
                // The mirror's channel URL is not a secret (the webhook URL and the
                // token are); a discord peer binds its custody to it.
                let channel = match (&self.config.discord, roles.contains(&Role::Discord)) {
                    (Some(d), true) => discord::Secrets::load(&d.mirror).ok().map(|s| s.channel_url.clone()),
                    _ => None,
                };
                Ok(json!({"ok":true,"broker":CONFIG_TYPE,"peer":{"uid":peer.uid,"gid":peer.gid},
                    "roles":roles.iter().map(|r| r.name()).collect::<Vec<_>>(),"singleAccount":self.config.single_account,
                    "shape":if self.config.single_account { "test-single-account" } else { "split" },
                    "configSha256":self.config.sha256,"credentials":self.config.credentials.is_some(),"discord":self.config.discord.is_some(),
                    "discordChannel":channel}))
            }
            "provider-authorize" => provider::authorize(self, &peer, &request, &mut note),
            "provider-forward" => provider::forward(self, &peer, &request, &mut stream, &mut note),
            "provider-verify-grant" => provider::verify_grant(self, &request, &mut note),
            "provider-selected-choice" => provider::selected_choice(self, &request, &mut note),
            "pool" => provider::pool(self, &request, &mut note),
            "discord-post" => discord::post(self, &request, &mut note),
            "discord-read" => discord::read(self, &request, &mut note),
            _ => Err(refuse("op-unknown", op.clone())),
        };
        let response = match &result {
            Ok(v) => v.clone(),
            Err(r) => wire::refusal(&r.code, &r.detail),
        };
        self.settle(&peer, &roles, &op, result.as_ref().map_or_else(Outcome::Refused, |_| Outcome::Ok), note);
        // A forward whose caller hung up has nobody to answer; its answer is
        // journaled, so an exact retry replays it.
        let _ = wire::send(&mut stream, &response, Instant::now() + Duration::from_secs(10));
    }
}

/// A refusal written without waiting: one non-blocking write of a small frame.
/// A peer that does not read cannot stall the accept loop.
fn refuse_now(stream: &mut UnixStream, r: &Refusal) {
    use std::io::Write as _;
    if stream.set_nonblocking(true).is_err() {
        return;
    }
    if let Ok(body) = serde_json::to_vec(&wire::refusal(&r.code, &r.detail)) {
        let mut frame = (body.len() as u32).to_le_bytes().to_vec();
        frame.extend_from_slice(&body);
        let _ = stream.write(&frame);
    }
}

/// `mini-keys serve`: load a root-owned config and serve forever.
pub fn serve_box(config: &Path) -> Result<(), String> {
    let config = Config::load_for_broker(config)?;
    let (broker, listener) = Broker::start(config)?;
    broker.serve(listener)
}
