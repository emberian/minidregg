//! The door's queue: the one schema the unprivileged writers put in a spool and the root
//! processor reads back (deploy/door/README.md).
//!
//! * the `/join` form (`mini-door`, uid `mini-door`) writes [`Request`]s;
//! * the Discord entrance (`mini-discord`) writes [`Link`]s for `/mini line:link CODE`;
//! * the processor (`mini-door-process`, root) reads both with [`spool_read`], which refuses a
//!   file that is not a regular file owned by the expected writer, or is over [`MAX_FILE`],
//!   and decodes it with [`Request::parse`] / [`Link::parse`], which refuse any key outside
//!   the schema. Nothing a writer puts in a spool is trusted beyond that.

use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::Path;

use serde_json::{json, Map, Value};

use crate::interaction::is_snowflake;

pub const REQUEST_TYPE: &str = "minidregg-door-request-v1";
pub const LINK_TYPE: &str = "minidregg-door-link-v1";
pub const STATUS_TYPE: &str = "minidregg-door-status-v1";
pub const STATE_TYPE: &str = "minidregg-door-state-v1";
/// The largest spool file the processor reads.
pub const MAX_FILE: u64 = 8192;
/// The largest detached SSH signature a stranger may paste.
pub const MAX_ARMOUR: usize = 2048;
/// Names a stranger may never take: the box's own accounts and roles.
pub const RESERVED: &[&str] = &[
    "ember", "mini", "core", "keys", "discord", "door", "root", "admin", "operator", "sponsor",
    "pubread", "public", "grain", "web", "mirror", "nobody", "caddy", "backup",
];
const B32: &[u8; 32] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZ234567";
const B58: &[u8; 58] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
/// `string "ssh-ed25519" || uint32 32`: the 19 bytes before an ssh-ed25519 key in its blob.
const SSH_BLOB_PREFIX: [u8; 19] = [
    0, 0, 0, 11, b's', b's', b'h', b'-', b'e', b'd', b'2', b'5', b'5', b'1', b'9', 0, 0, 0, 32,
];

/// A door account name: `^[a-z][a-z0-9-]{1,24}$` (split tenancy logs in as `mini-s-NAME`,
/// 32 characters at most), never reserved, never ending in `-`.
/// The member's research-consent fact (ember's policy ruling, 2026-10-27): the reference
/// `research-consent` in the member's own workspace, a declared cell under the open law holding
/// field 1 is 1 for CC0 (contributed for research) and 0 for none. The lines that write it at
/// enrolment, as the member, through the same tenant path as every other enrolment step.
pub const RESEARCH_CONSENT_REF: &str = "research-consent";
pub const RESEARCH_CONSENT_FIELD: u32 = 1;
pub const RESEARCH_CONSENT_ATTEMPT: &str = "research-consent-0";

pub fn research_consent_lines(cc0: bool) -> [String; 3] {
    [
        format!("create {RESEARCH_CONSENT_REF} declared open {RESEARCH_CONSENT_FIELD}"),
        format!("invoke {RESEARCH_CONSENT_ATTEMPT} {RESEARCH_CONSENT_REF} create {RESEARCH_CONSENT_FIELD} {}", u8::from(cc0)),
        format!("submit {RESEARCH_CONSENT_ATTEMPT}"),
    ]
}

/// The member's invite fact: present only for a member admitted with an operator-issued invite
/// code. The reference `invite`, a declared open cell, whose field 1 is the code's
/// SERIAL in the operator's codes file (never the code: the world is world-readable). Serials are
/// 1 or more, and `invoke ... create` writes one scalar, so field 1 IS the serial. An uncoded
/// member has no `invite` reference at all (absence = admitted on an open seat; a field-1 = 0 fact
/// would only add a write whose absence says the same).
pub const INVITE_REF: &str = "invite";
pub const INVITE_ATTEMPT: &str = "invite-0";

pub fn invite_lines(serial: u32) -> [String; 3] {
    [
        format!("create {INVITE_REF} declared open"),
        format!("invoke {INVITE_ATTEMPT} {INVITE_REF} create 1 {serial}"),
        format!("submit {INVITE_ATTEMPT}"),
    ]
}

/// An invite code as the operator issues it and the form carries it: 8 to 64 of A-Z a-z 0-9 -.
pub fn is_invite_code(code: &str) -> bool {
    (8..=64).contains(&code.len()) && code.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
}

/// The sentence the join page, /subscribe and /export carry (ember's ruling, verbatim; one file,
/// `deploy/policy/RETENTION.txt`, read by the door and the web body alike).
pub const RETENTION_POLICY: &str = include_str!("../../../deploy/policy/RETENTION.txt").trim_ascii_end();

pub fn is_door_name(s: &str) -> bool {
    let b = s.as_bytes();
    (2..=25).contains(&b.len())
        && b[0].is_ascii_lowercase()
        && b.iter().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || *c == b'-')
        && !s.ends_with('-')
        && !RESERVED.contains(&s)
}

/// A request id: 32 lowercase hex digits (128 bits from the kernel CSPRNG).
pub fn is_request_id(s: &str) -> bool {
    s.len() == 32 && s.bytes().all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}

/// A Discord link code: 16 characters of RFC 4648 base32 (80 bits).
pub fn is_link_code(s: &str) -> bool {
    s.len() == 16 && s.bytes().all(|c| B32.contains(&c))
}

fn b64_decode(text: &str) -> Option<Vec<u8>> {
    const T: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    if text.len() % 4 != 0 {
        return None;
    }
    let body = text.trim_end_matches('=');
    if text.len() - body.len() > 2 {
        return None;
    }
    let (mut out, mut acc, mut bits) = (Vec::new(), 0u32, 0u32);
    for c in body.bytes() {
        acc = (acc << 6) | T.iter().position(|t| *t == c)? as u32;
        bits += 6;
        if bits >= 8 {
            bits -= 8;
            out.push((acc >> bits) as u8);
        }
    }
    Some(out)
}

/// One `ssh-ed25519 BASE64 [comment]` line, normalized to `ssh-ed25519 BASE64` (the comment
/// is dropped: it is the stranger's text and would land in a root-owned file). Anything but
/// exactly one plain Ed25519 key refuses (RSA, ECDSA, FIDO, options, two keys).
pub fn ssh_ed25519(line: &str) -> Result<String, String> {
    let line = line.trim();
    if line.len() > 512 || line.chars().any(char::is_control) {
        return Err("the ssh key is one line of at most 512 characters".into());
    }
    let mut words = line.split(' ').filter(|w| !w.is_empty());
    let (Some(kind), Some(blob)) = (words.next(), words.next()) else {
        return Err("paste one public key line: ssh-ed25519 AAAA... (from ~/.ssh/id_ed25519.pub)".into());
    };
    if kind != "ssh-ed25519" {
        return Err(format!("only ssh-ed25519 keys are accepted, not {kind:?} (make one with ssh-keygen -t ed25519)"));
    }
    let bytes = b64_decode(blob).ok_or("the key's base64 does not decode")?;
    if bytes.len() != 51 || bytes[..19] != SSH_BLOB_PREFIX {
        return Err("the key is not one ssh-ed25519 public key".into());
    }
    Ok(format!("ssh-ed25519 {blob}"))
}

/// A detached SSH signature as `ssh-keygen -Y sign` writes it.
pub fn is_signature_armour(s: &str) -> bool {
    let s = s.trim();
    let Some(body) = s
        .strip_prefix("-----BEGIN SSH SIGNATURE-----")
        .and_then(|rest| rest.strip_suffix("-----END SSH SIGNATURE-----"))
    else {
        return false;
    };
    s.len() <= MAX_ARMOUR
        && !body.trim().is_empty()
        && body.lines().all(|l| l.trim().bytes().all(|c| c.is_ascii_alphanumeric() || matches!(c, b'+' | b'/' | b'=')))
}

/// A Solana transaction signature: base58 of 64 bytes.
pub fn is_tx_signature(s: &str) -> bool {
    if !(64..=88).contains(&s.len()) || !s.bytes().all(|c| B58.contains(&c)) {
        return false;
    }
    let mut bytes: Vec<u8> = Vec::new();
    for c in s.bytes() {
        let mut carry = B58.iter().position(|x| *x == c).unwrap() as u32;
        for b in bytes.iter_mut().rev() {
            carry += (*b as u32) * 58;
            *b = carry as u8;
            carry >>= 8;
        }
        while carry > 0 {
            bytes.insert(0, carry as u8);
            carry >>= 8;
        }
    }
    let zeros = s.bytes().take_while(|c| *c == b'1').count();
    zeros + bytes.len() == 64
}

/// Which way an account is funded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Route {
    /// The sponsor provisions the door's fixed funding (`mini-reenroll`).
    Free,
    /// The stranger pays on Solana; the enrolment lands on the hosted key (P1).
    Paid,
}

impl Route {
    pub fn word(self) -> &'static str {
        match self {
            Route::Free => "free",
            Route::Paid => "paid",
        }
    }
}

/// One spool file written by the form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Request {
    /// `research`: the stranger ticked "contribute my data for research (CC0; kept private until
    /// reviewed)"; the processor writes it as the member's research-consent fact at enrolment.
    Join { id: String, at: u64, name: String, ssh_key: String, discord: bool, route: Route, research: bool,
        /// An operator-issued one-use invite code (free route only), for seats past freeCap - inviteReserve.
        invite: Option<String> },
    /// The stranger's detached ssh signature over the paid-enrolment statement.
    Sign { id: String, at: u64, signature: String },
    /// The stranger's Solana transaction signature after paying.
    Paid { id: String, at: u64, transaction: String },
}

fn exact<'a>(value: &'a Value, keys: &[&str]) -> Result<&'a Map<String, Value>, String> {
    let object = value.as_object().ok_or("not a JSON object")?;
    if object.len() != keys.len() || keys.iter().any(|k| !object.contains_key(*k)) {
        return Err(format!("keys must be exactly {}", keys.join(", ")));
    }
    Ok(object)
}

fn text<'a>(object: &'a Map<String, Value>, key: &str) -> Result<&'a str, String> {
    object.get(key).and_then(Value::as_str).ok_or(format!("{key} is not a string"))
}

fn natural(object: &Map<String, Value>, key: &str) -> Result<u64, String> {
    object.get(key).and_then(Value::as_u64).ok_or(format!("{key} is not a natural"))
}

impl Request {
    pub fn id(&self) -> &str {
        match self {
            Request::Join { id, .. } | Request::Sign { id, .. } | Request::Paid { id, .. } => id,
        }
    }

    pub fn to_json(&self) -> Value {
        match self {
            Request::Join { id, at, name, ssh_key, discord, route, research, invite } => {
                let mut v = json!({"type":REQUEST_TYPE,"kind":"join",
                    "id":id,"at":at,"name":name,"sshKey":ssh_key,"discord":discord,"route":route.word(),"research":research});
                if let Some(code) = invite {
                    v["invite"] = json!(code);
                }
                v
            }
            Request::Sign { id, at, signature } => json!({"type":REQUEST_TYPE,"kind":"sign","id":id,"at":at,"signature":signature}),
            Request::Paid { id, at, transaction } => json!({"type":REQUEST_TYPE,"kind":"paid","id":id,"at":at,"transaction":transaction}),
        }
    }

    /// The exact schema, every field re-checked: the processor's only reading of a request.
    pub fn parse(bytes: &[u8]) -> Result<Request, String> {
        let value: Value = serde_json::from_slice(bytes).map_err(|e| format!("request JSON: {e}"))?;
        let kind = value.get("kind").and_then(Value::as_str).unwrap_or("");
        let request = match kind {
            "join" => {
                // `research` is required of every request the form writes now; a request queued
                // before it existed reads as not ticked.
                // `invite` is optional and present only when a code was given.
                let mut stripped = value.clone();
                let invite = match stripped.as_object_mut().and_then(|m| m.remove("invite")) {
                    None => None,
                    Some(Value::String(c)) if is_invite_code(&c) => Some(c),
                    Some(_) => return Err("invite is not an invite code".into()),
                };
                let o = match exact(&stripped, &["type", "kind", "id", "at", "name", "sshKey", "discord", "route", "research"]) {
                    Ok(o) => o,
                    Err(_) => exact(&stripped, &["type", "kind", "id", "at", "name", "sshKey", "discord", "route"])?,
                };
                let name = text(o, "name")?;
                if !is_door_name(name) {
                    return Err(format!("{name:?} is not a door name"));
                }
                // An empty sshKey is a browser-only join: the box makes the hosted key and the door
                // answers a one-time web login link; the roster's login key is then a throwaway the
                // processor generates and destroys (the paid route needs the stranger's own key).
                let ssh_key = if text(o, "sshKey")?.is_empty() { String::new() } else { ssh_ed25519(text(o, "sshKey")?)? };
                if ssh_key != text(o, "sshKey")? {
                    return Err("sshKey is not normalized".into());
                }
                let route = match text(o, "route")? {
                    "free" => Route::Free,
                    "paid" if ssh_key.is_empty() => return Err("the paid route needs an ssh key (its memo is signed with it)".into()),
                    "paid" => Route::Paid,
                    other => return Err(format!("route {other:?} is neither free nor paid")),
                };
                if invite.is_some() && route != Route::Free {
                    return Err("an invite code is for the free route only".into());
                }
                Request::Join {
                    id: text(o, "id")?.into(),
                    at: natural(o, "at")?,
                    name: name.into(),
                    ssh_key,
                    discord: o.get("discord").and_then(Value::as_bool).ok_or("discord is not a boolean")?,
                    route,
                    research: match o.get("research") { None => false, Some(v) => v.as_bool().ok_or("research is not a boolean")? },
                    invite,
                }
            }
            "sign" => {
                let o = exact(&value, &["type", "kind", "id", "at", "signature"])?;
                let signature = text(o, "signature")?;
                if !is_signature_armour(signature) {
                    return Err("signature is not one ssh-keygen -Y sign armour".into());
                }
                Request::Sign { id: text(o, "id")?.into(), at: natural(o, "at")?, signature: signature.into() }
            }
            "paid" => {
                let o = exact(&value, &["type", "kind", "id", "at", "transaction"])?;
                let transaction = text(o, "transaction")?;
                if !is_tx_signature(transaction) {
                    return Err("transaction is not a base58 Solana signature".into());
                }
                Request::Paid { id: text(o, "id")?.into(), at: natural(o, "at")?, transaction: transaction.into() }
            }
            other => return Err(format!("kind {other:?} is not join, sign or paid")),
        };
        if value["type"] != REQUEST_TYPE {
            return Err(format!("type is not {REQUEST_TYPE}"));
        }
        if !is_request_id(request.id()) {
            return Err("id is not 32 lowercase hex digits".into());
        }
        Ok(request)
    }

    /// The spool file name: the kind and the id, so a stranger's later submissions never
    /// overwrite an earlier one (`create_new`), and a resubmission of the same step is refused.
    pub fn file_name(&self) -> String {
        let kind = match self {
            Request::Join { .. } => "join",
            Request::Sign { .. } => "sign",
            Request::Paid { .. } => "paid",
        };
        format!("{kind}-{}.json", self.id())
    }
}

/// One `/mini line:link CODE` from a Discord user the roster does not know yet. The signed
/// interaction proves the Discord id; the code proves the door account.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Link {
    pub interaction: String,
    pub user: String,
    pub code: String,
    pub at: u64,
}

impl Link {
    pub fn to_json(&self) -> Value {
        json!({"type":LINK_TYPE,"interaction":self.interaction,"discordUser":self.user,"code":self.code,"at":self.at})
    }

    pub fn parse(bytes: &[u8]) -> Result<Link, String> {
        let value: Value = serde_json::from_slice(bytes).map_err(|e| format!("link JSON: {e}"))?;
        let o = exact(&value, &["type", "interaction", "discordUser", "code", "at"])?;
        if text(o, "type")? != LINK_TYPE {
            return Err(format!("type is not {LINK_TYPE}"));
        }
        let link = Link {
            interaction: text(o, "interaction")?.into(),
            user: text(o, "discordUser")?.into(),
            code: text(o, "code")?.into(),
            at: natural(o, "at")?,
        };
        if !is_snowflake(&link.interaction) || !is_snowflake(&link.user) {
            return Err("interaction and discordUser must be snowflakes".into());
        }
        if !is_link_code(&link.code) {
            return Err("code is not a door link code".into());
        }
        Ok(link)
    }

    pub fn file_name(&self) -> String {
        format!("link-{}.json", self.interaction)
    }
}

/// `link CODE` (any case, surrounding spaces), the one line the entrance answers for a
/// Discord user who is not on the roster.
pub fn link_line(line: &str) -> Option<String> {
    let mut words = line.split_whitespace();
    match (words.next(), words.next(), words.next()) {
        (Some("link"), Some(code), None) => {
            let code = code.to_ascii_uppercase();
            is_link_code(&code).then_some(code)
        }
        _ => None,
    }
}

/// `n` bytes from the kernel CSPRNG.
pub fn random(n: usize) -> Result<Vec<u8>, String> {
    let mut bytes = vec![0u8; n];
    std::fs::File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut bytes))
        .map_err(|e| format!("/dev/urandom: {e}"))?;
    Ok(bytes)
}

pub fn new_request_id() -> Result<String, String> {
    Ok(random(16)?.iter().map(|b| format!("{b:02x}")).collect())
}

pub fn new_link_code() -> Result<String, String> {
    let bytes = random(10)?;
    let (mut out, mut acc, mut bits) = (String::new(), 0u32, 0u32);
    for b in bytes {
        acc = (acc << 8) | b as u32;
        bits += 8;
        while bits >= 5 {
            bits -= 5;
            out.push(B32[((acc >> bits) & 31) as usize] as char);
        }
    }
    Ok(out)
}

/// Write one spool file: created new (never over another), 0600 with its directory.
pub fn spool_write(dir: &Path, name: &str, value: &Value) -> Result<(), String> {
    let bytes = serde_json::to_vec(value).map_err(|e| e.to_string())?;
    if bytes.len() as u64 > MAX_FILE {
        return Err("request exceeds the spool bound".into());
    }
    let path = dir.join(name);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&path)
        .map_err(|e| match e.kind() {
            std::io::ErrorKind::AlreadyExists => "this step was already submitted".to_string(),
            _ => format!("{}: {e}", path.display()),
        })?;
    file.write_all(&bytes).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(())
}

/// Read one spool file as the processor does: never through a symlink, a regular file owned
/// by `owner` (the writer's uid), at most [`MAX_FILE`] bytes.
pub fn spool_read(path: &Path, owner: u32) -> Result<Vec<u8>, String> {
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    let meta = file.metadata().map_err(|e| e.to_string())?;
    if !meta.is_file() {
        return Err("not a regular file".into());
    }
    if meta.uid() != owner {
        return Err(format!("owned by uid {}, not the spool's writer {owner}", meta.uid()));
    }
    if meta.len() > MAX_FILE {
        return Err(format!("{} bytes, over the {MAX_FILE}-byte bound", meta.len()));
    }
    let mut bytes = Vec::new();
    Read::by_ref(&mut file).take(MAX_FILE + 1).read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    if bytes.len() as u64 > MAX_FILE {
        return Err("grew past the bound while read".into());
    }
    Ok(bytes)
}

/// The `*.json` files in a spool, oldest name first (names carry no order; the processor
/// sorts by modification time, then name).
pub fn spool_list(dir: &Path) -> Result<Vec<std::path::PathBuf>, String> {
    let mut files = Vec::new();
    for entry in std::fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))? {
        let entry = entry.map_err(|e| e.to_string())?;
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        if name.ends_with(".json") && !name.starts_with('.') {
            let at = entry.metadata().and_then(|m| m.modified()).ok();
            files.push((at, entry.path()));
        }
    }
    files.sort();
    Ok(files.into_iter().map(|(_, p)| p).collect())
}

/// HTML-escape for the form's pages.
pub fn html(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            c => out.push(c),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    const KEY: &str = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIOMqqnkVzrm0SdG6UOoqKLsabgH5C9okWi0dh2l9GKJl";

    #[test]
    fn names_ids_and_codes() {
        assert!(is_door_name("alice"));
        assert!(is_door_name("k9-lab"));
        for bad in ["a", "ember", "mini", "1abc", "Alice", "a_b", "abc-", &"a".repeat(26)] {
            assert!(!is_door_name(bad), "{bad}");
        }
        assert!(is_request_id(&new_request_id().unwrap()));
        assert!(!is_request_id("ABCDEF00000000000000000000000000"));
        let code = new_link_code().unwrap();
        assert!(is_link_code(&code), "{code}");
        assert_eq!(link_line(&format!("  link {}  ", code.to_lowercase())), Some(code.clone()));
        assert_eq!(link_line("link"), None);
        assert_eq!(link_line(&format!("link {code} extra")), None);
        assert_eq!(link_line("read shared"), None);
    }

    #[test]
    fn only_one_plain_ed25519_key_is_accepted_and_its_comment_is_dropped() {
        assert_eq!(ssh_ed25519(&format!("{KEY} alice@laptop")).unwrap(), KEY);
        for bad in [
            "ssh-rsa AAAAB3NzaC1yc2EAAAADAQABAAABAQ",
            "sk-ssh-ed25519@openssh.com AAAA",
            "ssh-ed25519 AAAA",
            "ssh-ed25519",
            "",
            "command=\"x\" ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIOMqqnkVzrm0SdG6UOoqKLsabgH5C9okWi0dh2l9GKJl",
        ] {
            assert!(ssh_ed25519(bad).is_err(), "{bad}");
        }
        assert!(ssh_ed25519(&format!("{KEY}\nssh-ed25519 AAAA")).is_err());
    }

    #[test]
    fn requests_round_trip_and_anything_else_refuses() {
        let id = new_request_id().unwrap();
        let join = Request::Join { id: id.clone(), at: 7, name: "alice".into(), ssh_key: KEY.into(), discord: true, route: Route::Paid, research: true, invite: None };
        let bytes = serde_json::to_vec(&join.to_json()).unwrap();
        assert_eq!(Request::parse(&bytes).unwrap(), join);
        assert_eq!(join.file_name(), format!("join-{id}.json"));
        let mut extra = join.to_json();
        extra["sponsor"] = json!(true);
        assert!(Request::parse(&serde_json::to_vec(&extra).unwrap()).is_err());
        for (key, value) in [("name", json!("ember")), ("route", json!("comp")), ("id", json!("x")),
            ("sshKey", json!(format!("{KEY} comment"))), ("discord", json!("yes")), ("type", json!("other"))] {
            let mut bad = join.to_json();
            bad[key] = value;
            assert!(Request::parse(&serde_json::to_vec(&bad).unwrap()).is_err(), "{key}");
        }
        let armour = "-----BEGIN SSH SIGNATURE-----\nU1NIU0lHAAAAAQAAADMAAAALc3No\nLWVkMjU1MTk=\n-----END SSH SIGNATURE-----\n";
        let sign = Request::Sign { id: id.clone(), at: 8, signature: armour.into() };
        assert_eq!(Request::parse(&serde_json::to_vec(&sign.to_json()).unwrap()).unwrap(), sign);
        let bad = Request::Sign { id: id.clone(), at: 8, signature: "-----BEGIN SSH SIGNATURE-----\n$(rm)\n-----END SSH SIGNATURE-----".into() };
        assert!(Request::parse(&serde_json::to_vec(&bad.to_json()).unwrap()).is_err());
        let tx = "2Ana1pUpv2ZbMVkwF5FXapYeBEjdxDatLn7nvJkhgTSXbs59SyZSx866bXirPgj8QQVB57uxHJBG1YFvkRbFj4T";
        assert!(is_tx_signature(tx));
        assert!(!is_tx_signature("0OIl"));
        let paid = Request::Paid { id, at: 9, transaction: tx.into() };
        assert_eq!(Request::parse(&serde_json::to_vec(&paid.to_json()).unwrap()).unwrap(), paid);
    }

    #[test]
    fn links_round_trip_and_refuse_malformed_fields() {
        let link = Link { interaction: "1234567890".into(), user: "42".into(), code: new_link_code().unwrap(), at: 3 };
        assert_eq!(Link::parse(&serde_json::to_vec(&link.to_json()).unwrap()).unwrap(), link);
        let mut bad = link.to_json();
        bad["code"] = json!("short");
        assert!(Link::parse(&serde_json::to_vec(&bad).unwrap()).is_err());
        let mut bad = link.to_json();
        bad["name"] = json!("ember");
        assert!(Link::parse(&serde_json::to_vec(&bad).unwrap()).is_err());
    }

    #[test]
    fn the_spool_is_create_new_and_read_back_only_from_its_owner() {
        use std::os::unix::fs::PermissionsExt;
        let dir = std::env::temp_dir().join(format!("door-spool-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        spool_write(&dir, "a.json", &json!({"x":1})).unwrap();
        assert!(spool_write(&dir, "a.json", &json!({"x":2})).unwrap_err().contains("already submitted"));
        let me = std::fs::metadata(dir.join("a.json")).unwrap().uid();
        assert_eq!(std::fs::metadata(dir.join("a.json")).unwrap().permissions().mode() & 0o777, 0o600);
        assert_eq!(spool_read(&dir.join("a.json"), me).unwrap(), br#"{"x":1}"#);
        assert!(spool_read(&dir.join("a.json"), me + 1).is_err());
        std::os::unix::fs::symlink(dir.join("a.json"), dir.join("b.json")).unwrap();
        assert!(spool_read(&dir.join("b.json"), me).is_err(), "never through a symlink");
        std::fs::write(dir.join("c.json"), vec![b'x'; MAX_FILE as usize + 1]).unwrap();
        assert!(spool_read(&dir.join("c.json"), me).is_err());
        assert_eq!(spool_list(&dir).unwrap().len(), 3);
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
