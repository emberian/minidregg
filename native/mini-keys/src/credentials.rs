//! Provider table, grants, owners, choices, and (under the `server` feature)
//! the sealed per-member credential store.
//!
//! One implementation, owned by the key broker. Clients (`grain-runtime`
//! resolving a route at reserve time, `mini key` in resource-client building
//! signed requests) depend on `mini-keys` with `default-features = false` and
//! get the parsers: [`ProviderTable`], [`Grant`], [`Owner`], [`Secret`],
//! [`choice::Choice`]. The sealed store, [`CredentialStore`], compiles only
//! with `server`, so it executes only inside the broker.
//!
//! Layout (every file 0600, every directory 0700; under split tenancy the
//! leaves belong to the broker account `mini-keys` and the root, subject
//! directories and `_service`/`_pool` leaves are pre-created by the installer):
//!
//!   TABLE  /etc/mini/providers.json           root-owned, not group/world writable
//!   KEY    /etc/mini/credentials.key          32 random bytes, the at-rest key (mini-keys 0600)
//!   ROOT   /var/lib/mini/credentials/
//!            SUBJECT/PUBLIC-KEY-HEX/PROVIDER.key          sealed secret
//!            SUBJECT/PUBLIC-KEY-HEX/PROVIDER.grants.json  runners allowed to use it
//!            SUBJECT/PUBLIC-KEY-HEX/PROVIDER.usage.json   per-runner day counters
//!            _pool/PROVIDER.key                           the operator's pool secret
//!            _service/                                    per-member exchange locks
//!
//! A friend's namespace is named by the subject AND the public key of the
//! workspace key that wrote it, so a workspace that merely claims another
//! subject number writes into a different directory and can neither read,
//! replace, grant nor revoke the real owner's credential.
//!
//! Custody statement: this is hosted custody. The at-rest seal keeps the
//! secret out of anything that copies ROOT without KEY (backups of
//! /var/lib/mini, a stray tarball). It does not hide the secret from root or
//! from the broker account, which must read KEY to use the credential.
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
pub mod choice;
#[cfg(feature = "server")]
mod store;
#[cfg(feature = "server")]
pub use store::{utc_day, CredentialStore};
pub(crate) use crate::wire::{hex, unhex};
use std::fs;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};

pub const DEFAULT_TABLE: &str = "/etc/mini/providers.json";
pub const DEFAULT_ROOT: &str = "/var/lib/mini/credentials";
pub const DEFAULT_KEY: &str = "/etc/mini/credentials.key";
const POOL_NAMESPACE: &str = "_pool";
const TABLE_TYPE: &str = "mini-provider-table-v2";
const MAX_TABLE: u64 = 65_536;
const MAX_SECRET: usize = 4096;
/// Refusal prefix. The gateway turns `provider-refused:CODE` into a named
/// HTTP refusal; nothing else in the controller starts with it.
pub const REFUSED: &str = "provider-refused:";


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
/// `max_tokens` one call may ask for and the calls per UTC day; and, across
/// all runners, the broker's own spend ceiling on the key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Caps {
    pub per_call: u64,
    pub per_day: u64,
    /// The broker's own ceiling, below the provider-side hard cap so that cap
    /// is never the first line: `(ceilingMicroUsd, callMicroUsd)`. Each
    /// authorized pool call is charged `callMicroUsd` (the operator's worst
    /// case for one call at `perCall` output tokens and the row's input bound)
    /// against a durable running total before the call is counted; a call that
    /// would pass the ceiling refuses `spend-ceiling`. A deployed (root-owned)
    /// broker refuses to start with a pool row that has none.
    pub spend: Option<(u64, u64)>,
    /// One member's share of that ceiling: `(memberDayMicroUsd,
    /// memberTotalMicroUsd)`, charged at the same `callMicroUsd` per call
    /// against the member the call serves (the resident's requester, else the
    /// runner). A call past either refuses `member-day-ceiling` or
    /// `member-total-ceiling`. A row with a spend ceiling and no member caps
    /// gets the defaults: a day at 1/40 and a total at 1/10 of the ceiling.
    pub member: Option<(u64, u64)>,
}

/// The default member share of a pool row's spend ceiling.
pub const MEMBER_DAY_DIVISOR: u64 = 40;
pub const MEMBER_TOTAL_DIVISOR: u64 = 10;

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

/// The most path segments a provider row may put before `chat/completions`
/// (`api/coding/paas/v4` is four).
const MAX_CHAT_PREFIX: usize = 4;

/// The path is an OpenAI-compatible Chat Completions endpoint: the row's own
/// prefix (`v1`, `api/v1`, Z.AI's `api/coding/paas/v4`), then exactly
/// `chat/completions`. Every prefix segment is plain (lowercase letters,
/// digits, `-`, `.`; never `.` or `..`), and nothing follows: no query, no
/// fragment, no escape, no trailing slash. So each row pins exactly the chat
/// endpoint its provider serves, and nothing else reachable on that host.
fn is_chat_path(path: &str) -> bool {
    let segments: Vec<&str> = path.split('/').collect();
    let Some(prefix) = segments.strip_suffix(&["chat", "completions"]) else { return false };
    prefix.len() <= MAX_CHAT_PREFIX
        && prefix.iter().all(|s| {
            !s.is_empty() && *s != "." && *s != ".."
                && s.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-' || b == b'.')
        })
}

/// Exact Chat Completions endpoint (`is_chat_path`). The same rule held when
/// the endpoint was one configured URL; now it holds for every row.
pub fn validate_endpoint(url: &str) -> Result<(), String> {
    let (scheme, remainder) = url.split_once("://").ok_or("upstream URL lacks scheme")?;
    let (authority, path) = remainder.split_once('/').ok_or("upstream URL lacks path")?;
    if !is_chat_path(path)
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
                    object_keys(caps, &["perCall", "perDay", "ceilingMicroUsd", "callMicroUsd",
                        "memberDayMicroUsd", "memberTotalMicroUsd"], label)?;
                    let field = |n: &str, max: u64| -> Result<u64, String> {
                        let v = string(caps, n, label)?;
                        decimal(v, n)?;
                        v.parse::<u64>()
                            .ok()
                            .filter(|v| (1..=max).contains(v))
                            .ok_or_else(|| format!("provider {name}: caps.{n} must be 1..{max}"))
                    };
                    let spend = match (caps.get("ceilingMicroUsd"), caps.get("callMicroUsd")) {
                        (None, None) => None,
                        (Some(_), Some(_)) => {
                            let ceiling = field("ceilingMicroUsd", 1_000_000_000_000)?;
                            let call = field("callMicroUsd", 1_000_000_000)?;
                            if call > ceiling {
                                return Err(format!("provider {name}: caps.callMicroUsd exceeds caps.ceilingMicroUsd"));
                            }
                            Some((ceiling, call))
                        }
                        _ => return Err(format!("provider {name}: caps.ceilingMicroUsd and caps.callMicroUsd go together")),
                    };
                    let member = match (spend, caps.get("memberDayMicroUsd"), caps.get("memberTotalMicroUsd")) {
                        (None, None, None) => None,
                        (None, _, _) => return Err(format!("provider {name}: member caps need caps.ceilingMicroUsd and caps.callMicroUsd")),
                        (Some((ceiling, call)), None, None) => {
                            Some(((ceiling / MEMBER_DAY_DIVISOR).max(call), (ceiling / MEMBER_TOTAL_DIVISOR).max(call)))
                        }
                        (Some((ceiling, call)), Some(_), Some(_)) => {
                            let day = field("memberDayMicroUsd", 1_000_000_000_000)?;
                            let total = field("memberTotalMicroUsd", 1_000_000_000_000)?;
                            if call > day || day > total || total > ceiling {
                                return Err(format!(
                                    "provider {name}: caps need callMicroUsd <= memberDayMicroUsd <= memberTotalMicroUsd <= ceilingMicroUsd"
                                ));
                            }
                            Some((day, total))
                        }
                        _ => return Err(format!("provider {name}: caps.memberDayMicroUsd and caps.memberTotalMicroUsd go together")),
                    };
                    Some(Caps {
                        per_call: field("perCall", 1_000_000)?,
                        per_day: field("perDay", 100_000)?,
                        spend,
                        member,
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
