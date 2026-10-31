//! Saved identity capabilities, per application, across generations
//! (`BridgeConfig.saveIdentityCaps`; docs/APP-MARKET-2026-10-27.md §3).
//!
//! When a participant opens a grain whose bridge keeps identities, the bridge
//! asks `SandstormApi.save` for a token and keeps it in the grain's `/var`. The
//! record behind the token lives here, outside the sandbox, in the app's state
//! directory `apps/<app>/identities/<token-hex>.json` (0600, the operator's):
//! it is a grant the member made by opening the grain, listed in the member's
//! receipts, and revocable from outside the grain (`revoke`), after which the
//! token answers `identityRevoked` for every later generation. The grain never
//! sees the record, only the token; the record carries no permission bits.

use crate::io_context::IoContext;
use minidregg_spk_rpc::{CustodyRefusal, IdentityCustody, SavedIdentity};
use serde_json::{json, Value};
use std::fs::{self, DirBuilder, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use crate::canonical::hex;

const PROTOCOL: &str = "mini-spk-saved-identity-v1";
const MAX_RECORD: usize = 4096;

pub struct FileIdentityCustody {
    directory: PathBuf,
}

fn invalid(reason: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason.into())
}

fn token_name(token: &[u8]) -> Option<String> {
    (token.len() == 32).then(|| format!("{}.json", hex(token)))
}

fn now() -> String {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs().to_string())
        .unwrap_or_default()
}

/// A record file, bounded and owned by this uid, mode 0600.
fn read_record(path: &Path) -> io::Result<Value> {
    let mut file = OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(&path).ctx("open", &path)?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o077 != 0
        || meta.len() as usize > MAX_RECORD
    {
        return Err(invalid("saved identity record custody refused"));
    }
    let mut bytes = Vec::with_capacity(meta.len() as usize);
    file.take(MAX_RECORD as u64 + 1).read_to_end(&mut bytes)?;
    if bytes.len() > MAX_RECORD {
        return Err(invalid("saved identity record grew"));
    }
    let value: Value = serde_json::from_slice(&bytes)?;
    if value.get("protocol").and_then(Value::as_str) != Some(PROTOCOL) {
        return Err(invalid("saved identity record protocol differs"));
    }
    Ok(value)
}

fn write_record(path: &Path, value: &Value, replace: bool) -> io::Result<()> {
    let bytes = serde_json::to_vec_pretty(value)?;
    let temp = path.with_extension("json.new");
    let _ = fs::remove_file(&temp).ctx("remove", &temp);
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&temp).ctx("open", &temp)?;
    file.write_all(&bytes)?;
    drop(file);
    if replace {
        fs::rename(&temp, path).ctx("rename", &temp)?;
    } else {
        // A fresh token never replaces a record: the name is 256 random bits.
        fs::hard_link(&temp, path).inspect_err(|_| {
            let _ = fs::remove_file(&temp).ctx("remove", &temp);
        })?;
        fs::remove_file(&temp).ctx("remove", &temp)?;
    }
    Ok(())
}

fn decode(value: &Value) -> io::Result<(SavedIdentity, bool)> {
    let id_hex = value.get("identityId").and_then(Value::as_str).ok_or_else(|| invalid("record lacks identityId"))?;
    if id_hex.len() != 64 || !id_hex.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(invalid("record identityId is not 32 bytes of hex"));
    }
    let mut identity_id = [0_u8; 32];
    for (i, pair) in id_hex.as_bytes().chunks(2).enumerate() {
        identity_id[i] = u8::from_str_radix(std::str::from_utf8(pair).map_err(|_| invalid("hex"))?, 16)
            .map_err(|_| invalid("hex"))?;
    }
    let text = |key: &str, bound: usize| -> io::Result<String> {
        let t = value.get(key).and_then(Value::as_str).ok_or_else(|| invalid(format!("record lacks {key}")))?;
        if t.len() > bound {
            return Err(invalid(format!("record {key} over bound")));
        }
        Ok(t.to_owned())
    };
    Ok((
        SavedIdentity {
            identity_id,
            display_name: text("displayName", 1024)?,
            preferred_handle: text("preferredHandle", 256)?,
        },
        value.get("revoked").and_then(Value::as_bool).unwrap_or(false),
    ))
}

impl FileIdentityCustody {
    /// Open (creating once, 0700) the app's identities directory. Its parent
    /// must already be the operator's private app directory.
    pub fn open(directory: PathBuf) -> io::Result<Self> {
        if !directory.is_absolute() {
            return Err(invalid("identities directory must be absolute"));
        }
        match fs::symlink_metadata(&directory) {
            Ok(meta) => {
                if !meta.is_dir() || meta.file_type().is_symlink() || meta.uid() != unsafe { libc::geteuid() } || meta.permissions().mode() & 0o077 != 0 {
                    return Err(invalid("identities directory custody refused"));
                }
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                DirBuilder::new().mode(0o700).create(&directory)?;
            }
            Err(error) => return Err(error),
        }
        Ok(Self { directory })
    }

    fn record_path(&self, token: &[u8]) -> Option<PathBuf> {
        token_name(token).map(|name| self.directory.join(name))
    }

    /// Every record, for receipts and `mini apps list`: (token hex, identity, revoked, savedAt).
    pub fn list(directory: &Path) -> io::Result<Vec<(String, SavedIdentity, bool, String)>> {
        let mut out = Vec::new();
        let entries = match fs::read_dir(directory) {
            Ok(entries) => entries,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(out),
            Err(error) => return Err(error),
        };
        for entry in entries {
            let entry = entry?;
            let name = entry.file_name().to_string_lossy().into_owned();
            let Some(token_hex) = name.strip_suffix(".json") else { continue };
            if token_hex.len() != 64 {
                continue;
            }
            let value = read_record(&entry.path())?;
            let (identity, revoked) = decode(&value)?;
            let saved_at = value.get("savedAt").and_then(Value::as_str).unwrap_or("").to_owned();
            out.push((token_hex.to_owned(), identity, revoked, saved_at));
        }
        out.sort_by(|a, b| a.0.cmp(&b.0));
        Ok(out)
    }

    /// The member or the operator withdraws the grant: the record stays, marked.
    pub fn revoke(directory: &Path, token_hex: &str) -> io::Result<SavedIdentity> {
        if token_hex.len() != 64 || !token_hex.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')) {
            return Err(invalid("token is not 32 bytes of lowercase hex"));
        }
        let path = directory.join(format!("{token_hex}.json"));
        let mut value = read_record(&path)?;
        let (identity, _) = decode(&value)?;
        value["revoked"] = json!(true);
        value["revokedAt"] = json!(now());
        write_record(&path, &value, true)?;
        Ok(identity)
    }
}

impl IdentityCustody for FileIdentityCustody {
    fn save(&self, identity: &SavedIdentity) -> Result<Vec<u8>, CustodyRefusal> {
        let io = |e: io::Error| CustodyRefusal::Io(e.to_string());
        let mut token = [0_u8; 32];
        fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut token)).map_err(io)?;
        let path = self.record_path(&token).ok_or_else(|| CustodyRefusal::Io("token".into()))?;
        let record = json!({
            "protocol": PROTOCOL,
            "identityId": hex(&identity.identity_id),
            "displayName": identity.display_name,
            "preferredHandle": identity.preferred_handle,
            "savedAt": now(),
            "revoked": false,
        });
        write_record(&path, &record, false).map_err(io)?;
        Ok(token.to_vec())
    }

    fn restore(&self, token: &[u8]) -> Result<SavedIdentity, CustodyRefusal> {
        let path = self.record_path(token).ok_or(CustodyRefusal::UnknownToken)?;
        let value = match read_record(&path) {
            Ok(value) => value,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Err(CustodyRefusal::UnknownToken),
            Err(error) => return Err(CustodyRefusal::Io(error.to_string())),
        };
        let (identity, revoked) = decode(&value).map_err(|e| CustodyRefusal::Io(e.to_string()))?;
        if revoked {
            return Err(CustodyRefusal::IdentityRevoked);
        }
        Ok(identity)
    }

    fn release(&self, token: &[u8]) -> Result<(), CustodyRefusal> {
        let path = self.record_path(token).ok_or(CustodyRefusal::UnknownToken)?;
        let mut value = match read_record(&path) {
            Ok(value) => value,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Err(CustodyRefusal::UnknownToken),
            Err(error) => return Err(CustodyRefusal::Io(error.to_string())),
        };
        value["revoked"] = json!(true);
        value["releasedAt"] = json!(now());
        write_record(&path, &value, true).map_err(|e| CustodyRefusal::Io(e.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("mini-identity-custody-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        DirBuilder::new().mode(0o700).recursive(true).create(&dir).unwrap();
        dir
    }

    fn ada() -> SavedIdentity {
        SavedIdentity { identity_id: [7; 32], display_name: "Ada".into(), preferred_handle: "ada".into() }
    }

    #[test]
    fn identity_custody_saves_restores_releases_and_revokes_across_opens() {
        let dir = scratch("roundtrip").join("identities");
        let custody = FileIdentityCustody::open(dir.clone()).unwrap();
        let token = custody.save(&ada()).unwrap();
        assert_eq!(token.len(), 32);
        assert_eq!(custody.restore(&token).unwrap(), ada());
        assert_eq!(fs::symlink_metadata(&dir).unwrap().permissions().mode() & 0o777, 0o700);
        // A later generation opens the same directory and finds the record.
        let later = FileIdentityCustody::open(dir.clone()).unwrap();
        assert_eq!(later.restore(&token).unwrap(), ada());
        assert_eq!(later.restore(&[1; 32]), Err(CustodyRefusal::UnknownToken));
        assert_eq!(later.restore(b"short"), Err(CustodyRefusal::UnknownToken));
        let listed = FileIdentityCustody::list(&dir).unwrap();
        assert_eq!(listed.len(), 1);
        assert_eq!((listed[0].0.as_str(), &listed[0].1, listed[0].2), (hex(&token).as_str(), &ada(), false));
        // The member revokes from outside the grain: the token answers by name afterwards.
        assert_eq!(FileIdentityCustody::revoke(&dir, &hex(&token)).unwrap(), ada());
        assert_eq!(later.restore(&token), Err(CustodyRefusal::IdentityRevoked));
        assert!(FileIdentityCustody::list(&dir).unwrap()[0].2);
        // release() by the grain has the same effect on a second token.
        let second = custody.save(&ada()).unwrap();
        custody.release(&second).unwrap();
        assert_eq!(custody.restore(&second), Err(CustodyRefusal::IdentityRevoked));
        assert_eq!(custody.release(&[2; 32]), Err(CustodyRefusal::UnknownToken));
        assert!(FileIdentityCustody::revoke(&dir, "zz").is_err());
    }

    #[test]
    fn identity_custody_refuses_drifted_records_and_foreign_directories() {
        let root = scratch("custody");
        let dir = root.join("identities");
        let custody = FileIdentityCustody::open(dir.clone()).unwrap();
        let token = custody.save(&ada()).unwrap();
        let path = dir.join(format!("{}.json", hex(&token)));
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(matches!(custody.restore(&token), Err(CustodyRefusal::Io(_))));
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
        fs::write(&path, br#"{"protocol":"other"}"#).unwrap();
        assert!(matches!(custody.restore(&token), Err(CustodyRefusal::Io(_))));
        let loose = root.join("loose");
        DirBuilder::new().mode(0o755).create(&loose).unwrap();
        assert!(FileIdentityCustody::open(loose).is_err());
        assert!(FileIdentityCustody::open(PathBuf::from("relative")).is_err());
    }
}
