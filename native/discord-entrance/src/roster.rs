//! `discord_user_id -> session NAME`, read from a root-owned JSON file on every request.
//!
//! ```json
//! { "version": 1, "users": { "123456789012345678": "ember" } }
//! ```
//!
//! Fail-closed: the file must be owned by the configured uid (root in deployment) and not
//! writable by group or others, every key must be a snowflake and every NAME must match the
//! friends roster's own rule `^[a-z][a-z0-9-]{0,31}$` (`render-authorized-keys.sh`). A file
//! that fails any check answers no one; it does not answer the entries that parse.

use std::collections::BTreeMap;
use std::os::unix::fs::MetadataExt;
use std::path::Path;

use serde_json::Value;

use crate::interaction::is_snowflake;

#[derive(Debug)]
pub struct Roster {
    users: BTreeMap<String, String>,
}

/// The friends roster's name rule.
pub fn is_session_name(s: &str) -> bool {
    let b = s.as_bytes();
    !b.is_empty()
        && b.len() <= 32
        && b[0].is_ascii_lowercase()
        && b.iter().all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || *c == b'-')
}

impl Roster {
    pub fn load(path: &Path, owner_uid: u32) -> Result<Roster, String> {
        let meta = std::fs::metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
        if !meta.is_file() {
            return Err(format!("{} is not a file", path.display()));
        }
        if meta.uid() != owner_uid {
            return Err(format!("{} is owned by uid {}, not {owner_uid}", path.display(), meta.uid()));
        }
        if meta.mode() & 0o022 != 0 {
            return Err(format!("{} is writable by group or others", path.display()));
        }
        let text = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
        Self::parse(&text)
    }

    pub fn parse(text: &[u8]) -> Result<Roster, String> {
        let v: Value = serde_json::from_slice(text).map_err(|e| format!("roster JSON: {e}"))?;
        let obj = v.as_object().ok_or("roster must be an object")?;
        if obj.keys().any(|k| k != "version" && k != "users") {
            return Err("roster has a key other than version and users".into());
        }
        if obj.get("version").and_then(Value::as_u64) != Some(1) {
            return Err("roster version must be 1".into());
        }
        let users = obj.get("users").and_then(Value::as_object).ok_or("roster has no users object")?;
        let mut out = BTreeMap::new();
        for (id, name) in users {
            if !is_snowflake(id) {
                return Err(format!("roster key {id:?} is not a Discord user id"));
            }
            let name = name.as_str().ok_or(format!("roster entry {id} is not a string"))?;
            if !is_session_name(name) {
                return Err(format!("roster entry {id} names {name:?}, not a session name"));
            }
            out.insert(id.clone(), name.to_string());
        }
        Ok(Roster { users: out })
    }

    pub fn session_of(&self, discord_user_id: &str) -> Option<&str> {
        self.users.get(discord_user_id).map(String::as_str)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_looks_up() {
        let r = Roster::parse(br#"{"version":1,"users":{"123":"ember","456":"k1-friend"}}"#).unwrap();
        assert_eq!(r.session_of("123"), Some("ember"));
        assert_eq!(r.session_of("456"), Some("k1-friend"));
        assert_eq!(r.session_of("789"), None);
    }

    #[test]
    fn one_bad_entry_refuses_the_whole_file() {
        for bad in [
            &br#"{"version":1,"users":{"123":"ember","456":"../root"}}"#[..],
            br#"{"version":1,"users":{"12x":"ember"}}"#,
            br#"{"version":1,"users":{"123":"Ember"}}"#,
            br#"{"version":1,"users":{"123":7}}"#,
            br#"{"version":2,"users":{}}"#,
            br#"{"version":1,"users":{},"sponsor":"x"}"#,
            br#"[]"#,
        ] {
            assert!(Roster::parse(bad).is_err(), "{}", String::from_utf8_lossy(bad));
        }
    }

    #[test]
    fn refuses_a_file_with_the_wrong_owner_or_mode() {
        use std::os::unix::fs::PermissionsExt;
        let dir = std::env::temp_dir().join(format!("roster-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let p = dir.join("roster.json");
        std::fs::write(&p, br#"{"version":1,"users":{"1":"a"}}"#).unwrap();
        let me = std::fs::metadata(&p).unwrap().uid();
        std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o644)).unwrap();
        assert!(Roster::load(&p, me).is_ok());
        assert!(Roster::load(&p, me.wrapping_add(1)).is_err());
        std::fs::set_permissions(&p, std::fs::Permissions::from_mode(0o664)).unwrap();
        assert!(Roster::load(&p, me).is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn session_name_rule() {
        assert!(is_session_name("ember"));
        assert!(is_session_name("k1-friend2"));
        assert!(!is_session_name("1abc"));
        assert!(!is_session_name(""));
        assert!(!is_session_name(&"a".repeat(33)));
        assert!(!is_session_name("a/b"));
    }
}
