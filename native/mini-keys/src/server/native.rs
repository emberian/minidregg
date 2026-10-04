//! What the broker asks the Store: whether a member key is the subject's
//! current, unrevoked key, and at which key epoch. One public-socket query
//! (operation 144), pinned to the Host image and config the challenge named.
use super::credentials::Owner;
use crate::wire;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::io::Read;
use std::path::Path;
use std::time::Instant;

pub const MAX_HOST_CONFIG: usize = 65_536;
const MAX_HOST_IMAGE: u64 = 1 << 31;
const KEY_STATUS: u8 = 144;

pub fn sha256_hex(bytes: &[u8]) -> String {
    wire::hex(&Sha256::digest(bytes))
}

/// SHA-256 of the selected Host image (a regular file).
pub fn host_sha256(host: &Path) -> Result<String, String> {
    let mut file = std::fs::File::open(host).map_err(|_| "the selected Host image is unavailable")?;
    let meta = file.metadata().map_err(|_| "the selected Host image is unavailable")?;
    if !meta.is_file() || meta.len() > MAX_HOST_IMAGE {
        return Err("the selected Host image is not a regular file".into());
    }
    let mut hasher = Sha256::new();
    let mut buf = vec![0u8; 1 << 16];
    loop {
        let n = file.read(&mut buf).map_err(|_| "the selected Host image is unreadable")?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    Ok(wire::hex(&hasher.finalize()))
}

/// The pinned Host config bytes, exactly (their digest is what members compare).
pub fn host_config(path: &Path) -> Result<Vec<u8>, String> {
    let file = std::fs::File::open(path).map_err(|_| "the pinned Host config is unavailable")?;
    let mut bytes = Vec::new();
    file.take((MAX_HOST_CONFIG + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|_| "the pinned Host config is unreadable")?;
    if bytes.len() > MAX_HOST_CONFIG {
        return Err("the pinned Host config exceeds its bound".into());
    }
    Ok(bytes)
}

/// Ask the Store about `owner` through the public socket.
pub fn key_status(socket: &Path, config: &[u8], host_sha: &str, owner: &Owner, end: Instant) -> Result<Value, String> {
    let mut frame = vec![2];
    frame.extend_from_slice(&(config.len() as u32).to_le_bytes());
    frame.extend_from_slice(config);
    frame.extend_from_slice(&wire::unhex(host_sha)?);
    frame.push(KEY_STATUS);
    frame.extend_from_slice(&serde_json::to_vec(&json!({"subject":owner.subject,"publicKey":owner.public_key})).unwrap());
    let mut stream = crate::client::connect(socket, end).map_err(|_| "the native key-status query is unavailable")?;
    wire::write_frame(&mut stream, &frame, end)?;
    let reply = wire::read_frame(&mut stream, MAX_HOST_CONFIG, end)?;
    match reply.split_first() {
        Some((&KEY_STATUS, body)) => serde_json::from_slice(body).map_err(|_| "invalid native key status".into()),
        _ => Err("the native key-status query refused".into()),
    }
}

fn canonical_epoch(value: &str) -> bool {
    !value.is_empty() && value.len() <= 40 && value.bytes().all(|b| b.is_ascii_digit()) && (value == "0" || !value.starts_with('0'))
}

/// The view must say: this subject, this key, current, not revoked; it names the epoch.
pub fn current_epoch(view: &Value, owner: &Owner) -> Result<String, String> {
    let epoch = view["keyEpoch"].as_str().filter(|e| canonical_epoch(e));
    if view["type"] != "subject-key-status-v1"
        || view["subject"] != owner.subject
        || view.get("publicKey").is_some_and(|k| k != &json!(owner.public_key))
        || view["isCurrent"] != true
        || view["currentRevoked"] != false
        || epoch.is_none()
    {
        return Err("owner-not-current".into());
    }
    Ok(epoch.unwrap().to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_a_current_unrevoked_exact_view_names_an_epoch() {
        let owner = Owner::new("20", &"ab".repeat(32)).unwrap();
        let good = json!({"type":"subject-key-status-v1","subject":"20","keyEpoch":"1","isCurrent":true,"currentRevoked":false});
        assert_eq!(current_epoch(&good, &owner).unwrap(), "1");
        for field in ["isCurrent", "currentRevoked", "subject", "keyEpoch", "type"] {
            let mut bad = good.clone();
            bad.as_object_mut().unwrap().remove(field);
            assert!(current_epoch(&bad, &owner).is_err(), "{field}");
        }
        let mut revoked = good.clone();
        revoked["currentRevoked"] = json!(true);
        assert!(current_epoch(&revoked, &owner).is_err());
        let mut other_key = good.clone();
        other_key["publicKey"] = json!("cd".repeat(32));
        assert!(current_epoch(&other_key, &owner).is_err());
        let mut padded = good;
        padded["keyEpoch"] = json!("01");
        assert!(current_epoch(&padded, &owner).is_err());
    }
}
