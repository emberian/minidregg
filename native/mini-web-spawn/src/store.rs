//! The helper's state: one-time login records the door's root processor wrote, and the browser
//! sessions this helper minted from them. Tokens never touch the disk; a record is named by the
//! token's SHA-256. Everything here is root 0600 in a root 0700 directory.

use std::fs;
use std::io::Write;
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

use serde_json::{json, Value};

use crate::{new_token, now, sha256_hex};

/// A session ends after this long without a request, or this long after creation.
pub const IDLE_SECS: u64 = 24 * 3600;
pub const HARD_SECS: u64 = 7 * 24 * 3600;
/// The public body's pseudo-session (no cookie ever names it).
pub const PUBLIC: &str = "public";

#[derive(Debug, Clone, PartialEq)]
pub struct Session {
    /// SHA-256 of the session id (the file name), or `public`.
    pub hash: String,
    pub name: String,
    pub csrf: String,
    pub created: u64,
    pub last_seen: u64,
    pub expires: u64,
    pub body_pid: Option<u32>,
    pub shells: Vec<u32>,
}

impl Session {
    pub fn prefix(&self) -> String {
        self.hash.chars().take(12).collect()
    }

    fn to_json(&self) -> Value {
        json!({
            "version": 1,
            "name": self.name,
            "csrf": self.csrf,
            "created": self.created,
            "lastSeen": self.last_seen,
            "expires": self.expires,
            "bodyPid": self.body_pid,
            "shells": self.shells,
        })
    }

    fn from_json(hash: &str, v: &Value) -> Result<Session, String> {
        let text = |k: &str| v[k].as_str().map(str::to_owned).ok_or_else(|| format!("session {hash}: {k} missing"));
        let num = |k: &str| v[k].as_u64().ok_or_else(|| format!("session {hash}: {k} missing"));
        Ok(Session {
            hash: hash.to_owned(),
            name: text("name")?,
            csrf: text("csrf")?,
            created: num("created")?,
            last_seen: num("lastSeen")?,
            expires: num("expires")?,
            body_pid: v["bodyPid"].as_u64().map(|p| p as u32),
            shells: v["shells"].as_array().map(|a| a.iter().filter_map(|p| p.as_u64().map(|p| p as u32)).collect()).unwrap_or_default(),
        })
    }
}

pub struct Store {
    dir: PathBuf,
}

impl Store {
    pub fn open(dir: &Path) -> Result<Store, String> {
        for sub in ["logins", "sessions"] {
            let path = dir.join(sub);
            fs::create_dir_all(&path).map_err(|e| format!("{}: {e}", path.display()))?;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).map_err(|e| format!("{}: {e}", path.display()))?;
        }
        Ok(Store { dir: dir.to_path_buf() })
    }

    pub fn logins_dir(&self) -> PathBuf {
        self.dir.join("logins")
    }

    fn session_path(&self, hash: &str) -> PathBuf {
        self.dir.join("sessions").join(format!("{hash}.json"))
    }

    /// The door wrote `logins/<sha256(code)>.json` as `{"name": NAME, "expires": T}`. Consume it:
    /// read, check, delete, in that order, so a code is good exactly once.
    pub fn consume_login(&self, code: &str) -> Result<String, String> {
        let path = self.logins_dir().join(format!("{}.json", sha256_hex(code.as_bytes())));
        let bytes = fs::read(&path).map_err(|_| "unknown or already used login code".to_owned())?;
        let _ = fs::remove_file(&path);
        let v: Value = serde_json::from_slice(&bytes).map_err(|e| format!("login record: {e}"))?;
        let name = v["name"].as_str().ok_or("login record without a name")?.to_owned();
        if !is_account_name(&name) {
            return Err("login record names no account".into());
        }
        if v["expires"].as_u64().is_none_or(|t| t < now()) {
            return Err("login code expired".into());
        }
        Ok(name)
    }

    /// Mint a session for NAME: the id goes to the caller once, the hash to disk.
    pub fn create(&self, name: &str) -> Result<(String, Session), String> {
        let sid = new_token().map_err(|e| e.to_string())?;
        let csrf = new_token().map_err(|e| e.to_string())?;
        let t = now();
        let session = Session {
            hash: sha256_hex(sid.as_bytes()),
            name: name.to_owned(),
            csrf,
            created: t,
            last_seen: t,
            expires: t + HARD_SECS,
            body_pid: None,
            shells: Vec::new(),
        };
        self.save(&session)?;
        Ok((sid, session))
    }

    pub fn save(&self, session: &Session) -> Result<(), String> {
        let path = self.session_path(&session.hash);
        let tmp = path.with_extension("tmp");
        let bytes = serde_json::to_vec_pretty(&session.to_json()).map_err(|e| e.to_string())?;
        let mut file = fs::OpenOptions::new().write(true).create(true).truncate(true).mode(0o600).open(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?;
        file.write_all(&bytes).map_err(|e| format!("{}: {e}", tmp.display()))?;
        fs::rename(&tmp, &path).map_err(|e| format!("{}: {e}", path.display()))
    }

    /// The live session a cookie names, with its clock advanced. Expired sessions are reported
    /// as absent (the sweep removes them).
    pub fn touch(&self, sid: &str) -> Result<Session, String> {
        let mut session = self.load_hash(&sha256_hex(sid.as_bytes())).ok_or("no such session")?;
        let t = now();
        if t >= session.expires || t >= session.last_seen + IDLE_SECS {
            return Err("session expired".into());
        }
        session.last_seen = t;
        self.save(&session)?;
        Ok(session)
    }

    pub fn load_hash(&self, hash: &str) -> Option<Session> {
        let bytes = fs::read(self.session_path(hash)).ok()?;
        let v: Value = serde_json::from_slice(&bytes).ok()?;
        Session::from_json(hash, &v).ok()
    }

    /// The pseudo-session that holds the public body's pid.
    pub fn public(&self) -> Session {
        self.load_hash(PUBLIC).unwrap_or(Session {
            hash: PUBLIC.into(),
            name: PUBLIC.into(),
            csrf: String::new(),
            created: now(),
            last_seen: now(),
            expires: u64::MAX,
            body_pid: None,
            shells: Vec::new(),
        })
    }

    pub fn delete(&self, hash: &str) {
        let _ = fs::remove_file(self.session_path(hash));
    }

    pub fn all(&self) -> Vec<Session> {
        let Ok(entries) = fs::read_dir(self.dir.join("sessions")) else { return Vec::new() };
        let mut out: Vec<Session> = entries
            .filter_map(|e| e.ok())
            .filter_map(|e| {
                let name = e.file_name().into_string().ok()?;
                let hash = name.strip_suffix(".json")?;
                if hash == PUBLIC {
                    return None;
                }
                self.load_hash(hash)
            })
            .collect();
        out.sort_by_key(|s| s.created);
        out
    }

    pub fn for_name(&self, name: &str) -> Vec<Session> {
        self.all().into_iter().filter(|s| s.name == name).collect()
    }

    pub fn is_expired(session: &Session) -> bool {
        let t = now();
        t >= session.expires || t >= session.last_seen + IDLE_SECS
    }
}

/// A door account name: `^[a-z][a-z0-9-]{0,31}$`, the same rule `mini-session-run` applies.
pub fn is_account_name(s: &str) -> bool {
    let b = s.as_bytes();
    !b.is_empty()
        && b.len() <= 32
        && b[0].is_ascii_lowercase()
        && b.iter().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || *c == b'-')
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch() -> PathBuf {
        let dir = std::env::temp_dir().join(format!("mini-web-spawn-store-{}-{}", std::process::id(), new_token().unwrap()));
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn write_login(store: &Store, code: &str, name: &str, expires: u64) {
        let path = store.logins_dir().join(format!("{}.json", sha256_hex(code.as_bytes())));
        fs::write(path, json!({"name": name, "expires": expires}).to_string()).unwrap();
    }

    #[test]
    fn a_login_code_is_good_exactly_once_and_expires() {
        let store = Store::open(&scratch()).unwrap();
        let code = new_token().unwrap();
        write_login(&store, &code, "alice", now() + 3600);
        assert_eq!(store.consume_login(&code).unwrap(), "alice");
        assert!(store.consume_login(&code).is_err(), "second use refused");
        let stale = new_token().unwrap();
        write_login(&store, &stale, "bob", now() - 1);
        assert!(store.consume_login(&stale).unwrap_err().contains("expired"));
        let bad = new_token().unwrap();
        write_login(&store, &bad, "Not A Name", now() + 10);
        assert!(store.consume_login(&bad).is_err());
    }

    #[test]
    fn sessions_round_trip_touch_and_list_by_name() {
        let store = Store::open(&scratch()).unwrap();
        let (sid, s) = store.create("alice").unwrap();
        assert_eq!(s.hash, sha256_hex(sid.as_bytes()));
        let touched = store.touch(&sid).unwrap();
        assert_eq!(touched.name, "alice");
        assert!(store.touch(&new_token().unwrap()).is_err());
        let (_, _) = store.create("alice").unwrap();
        let (_, _) = store.create("bob").unwrap();
        assert_eq!(store.for_name("alice").len(), 2);
        assert_eq!(store.all().len(), 3);
        let mut old = store.load_hash(&s.hash).unwrap();
        old.last_seen = now() - IDLE_SECS - 1;
        store.save(&old).unwrap();
        assert!(store.touch(&sid).unwrap_err().contains("expired"));
        assert!(Store::is_expired(&old));
        store.delete(&s.hash);
        assert!(store.load_hash(&s.hash).is_none());
        let p = store.public();
        assert_eq!(p.hash, PUBLIC);
        assert!(store.all().iter().all(|s| s.hash != PUBLIC));
    }
}
