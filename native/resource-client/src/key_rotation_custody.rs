//! Physical retained key rotation custody. These records are local recovery
//! responsibility, never native admission or signing authority.
use crate::*;
use serde_json::{json, Value};

pub(super) fn directory(path: &Path) -> Result<()> {
    match fs::symlink_metadata(path) {
        Ok(_) => workspace::private_dir(path)?,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => workspace::make_private_dir(path)?,
        Err(e) => return Err(e.to_string()),
    }
    sync_parent(path)
}
pub(super) fn publish(path: &Path, value: &Value, expected: Option<&Value>) -> Result<()> {
    workspace::publish_retained_json(path, value, expected)
}
pub(super) fn read(path: &Path) -> Result<Value> {
    participant_enrollment::json_private(path)
}
pub(super) fn bytes(path: &Path, limit: usize) -> Result<Vec<u8>> {
    agent_reserve::private_bytes(path, limit)
}
pub(super) use crate::fsio::sync_parent;
pub(super) fn immutable(path: &Path, value: &[u8]) -> Result<()> {
    crate::fsio::retain_exact(path, value, || "retained rotation bytes changed".to_owned()).map(|_| ())
}
pub(super) fn stable_id(id: &str) -> Result<()> {
    if id.is_empty()
        || id.len() > 64
        || !id
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
    {
        return Err("--new-attempt must be 1..64 ASCII letters, digits, '-' or '_'".into());
    }
    Ok(())
}
/// The caller holds the workspace transition lock. Accept only the retained
/// prior value or the exact installed value. Rename plus directory fsync makes
/// a crash after rename recoverable by exact readback, with no fresh keygen.
fn install_bytes(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.file_type().is_file() || meta.len() > limit as u64 {
        return Err("rotation install input is not bounded regular bytes".into());
    }
    fs::read(path).map_err(|e| e.to_string())
}
pub(super) fn install(path: &Path, prior: Option<&[u8]>, next: &[u8]) -> Result<()> {
    match fs::symlink_metadata(path) {
        Ok(meta) => {
            if !meta.file_type().is_file() {
                return Err("rotation destination is not a regular file".into());
            }
            let existing =
                install_bytes(path, next.len().max(prior.map_or(0, |p| p.len())).max(1))?;
            if existing == next {
                return sync_parent(path);
            }
            if prior != Some(existing.as_slice()) {
                return Err(
                    "rotation destination differs from retained prior and successor".into(),
                );
            }
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound && prior.is_none() => (),
        Err(e) => return Err(format!("rotation destination cannot be reconciled: {e}")),
    }
    workspace::replace_private_file(path, next)
}
pub(super) fn phase(path: &Path, prior: &Value, name: &str) -> Result<Value> {
    let mut next = prior.clone();
    next["phase"] = json!(name);
    publish(path, &next, Some(prior))?;
    Ok(next)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn temp() -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-rotation-custody-{}-{}",
            std::process::id(),
            crate::hex(&crate::fsio::random::<32>().unwrap())
        ));
        directory(&p).unwrap();
        p
    }
    #[test]
    fn retained_rotation_post_admission_install_retries_preserve_both_secrets() {
        let p = temp();
        let old = [1u8; 32];
        let successor = [2u8; 32];
        let after = [3u8; 32];
        immutable(&p.join("old"), &old).unwrap();
        immutable(&p.join("successor"), &successor).unwrap();
        immutable(&p.join("after"), &after).unwrap();
        let daily = p.join("daily");
        let next = p.join("next");
        immutable(&daily, &old).unwrap();
        immutable(&next, &successor).unwrap();
        let state = p.join("state.json");
        let admitted = json!({"phase":"confirmed","exactIngress":"0102","operation":"stable"});
        publish(&state, &admitted, None).unwrap();
        // Interrupt after only daily installation; restart never reads the
        // changed NEXT as the original signer and never regenerates after.
        install(&daily, Some(&old), &successor).unwrap();
        assert_eq!(read(&state).unwrap(), admitted);
        install(&daily, Some(&old), &successor).unwrap();
        install(&next, Some(&successor), &after).unwrap();
        install(&next, Some(&successor), &after).unwrap();
        assert_eq!(bytes(&p.join("successor"), 32).unwrap(), successor);
        assert_eq!(bytes(&p.join("after"), 32).unwrap(), after);
        immutable(&next, &[9; 32]).unwrap_err();
        workspace::replace_private_file(&next, &[9; 32]).unwrap();
        assert!(install(&next, Some(&successor), &after).is_err());
        fs::remove_dir_all(p).unwrap();
    }
    #[test]
    fn retained_rotation_operation_binding_and_uncertain_phase_are_sticky() {
        let p = temp();
        let state = p.join("state.json");
        let prepared =
            json!({"phase":"prepared","operation":"one","next":"/original","destination":"/next"});
        publish(&state, &prepared, None).unwrap();
        let submitted = phase(&state, &prepared, "submitted").unwrap();
        assert!(publish(&state, &prepared, None).is_err());
        let changed = json!({"phase":"submitted","operation":"one","next":"/different","destination":"/next"});
        assert!(publish(&state, &changed, None).is_err());
        assert_eq!(read(&state).unwrap(), submitted);
        assert!(stable_id("../other").is_err());
        stable_id("succession_2").unwrap();
        fs::remove_dir_all(p).unwrap();
    }
}
