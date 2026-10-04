//! Durable custody of a source Host refusal before a signed call exists.
//!
//! Only the submit path's socket op 1 may use this marker. The runtime still
//! rechecks the exact files and asks Lean to decode the retained Outcome.

use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self};
use std::io::{self};
use std::path::{Path, PathBuf};

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn require_absent(path: &Path) -> Result<(), String> {
    match fs::symlink_metadata(path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Ok(_) => Err(format!("{} already exists", path.display())),
        Err(error) => Err(format!("cannot inspect {}: {error}", path.display())),
    }
}

/// Retain the *whole* socket reply, including op 255, before returning the
/// refusal to submit. Failure to make the marker durable leaves the attempt
/// unresolved; it must never be inferred from stderr or a missing call.bin.
pub(crate) fn retain(
    destination: &Path,
    request: &[u8],
    config: &Path,
    frame: &[u8],
) -> Result<(), String> {
    if frame.len() < 2 || frame.len() > super::transport::HOST_MAX_FRAME + 1 || frame[0] != 255 {
        return Err("prepare refusal is not a bounded op 255 frame".into());
    }
    let attempt = destination
        .parent()
        .ok_or("prepare destination has no attempt directory")?;
    if destination
        .file_name()
        .is_none_or(|name| name != "plan.bin")
    {
        return Err("prepare refusal has no plan destination".into());
    }
    if config != attempt.join("config.json") {
        return Err("prepare refusal config is not retained attempt config".into());
    }
    require_absent(&attempt.join("call.bin"))?;
    require_absent(destination)?;
    let request_file = crate::fsio::read_bounded_or_empty(
        &attempt.join("signed-observation.bin"),
        super::transport::HOST_MAX_FRAME,
    )?;
    if request_file != request {
        return Err("prepare request differs from retained signed observation".into());
    }
    let config_bytes = crate::fsio::read_bounded_or_empty(config, 65_536)?;
    let manifest_bytes = crate::fsio::read_bounded_or_empty(&attempt.join("attempt.json"), 65_536)?;
    let manifest: Value = serde_json::from_slice(&manifest_bytes)
        .map_err(|error| format!("attempt manifest decode: {error}"))?;
    if manifest["format"] != "minidregg-resource-client-attempt-v1"
        || manifest["operation"] != "submit"
        || manifest["config"].as_str().map(PathBuf::from) != Some(super::absolute(config)?)
    {
        return Err("prepare refusal does not match a retained submit attempt".into());
    }
    let marker = json!({
        "type":"minidregg-pre-submit-refusal-v1",
        "stage":"prepare",
        "operation":1,
        "frameSha256":digest(frame),
        "requestSha256":digest(request),
        "hostConfigSha256":digest(&config_bytes),
        "attemptManifestSha256":digest(&manifest_bytes),
    });
    let mut marker_bytes = serde_json::to_vec_pretty(&marker)
        .map_err(|error| format!("prepare refusal marker render: {error}"))?;
    marker_bytes.push(b'\n');
    super::create_private(&attempt.join("pre-submit-refusal.frame"), frame)?;
    super::create_private(&attempt.join("pre-submit-refusal.json"), &marker_bytes)?;
    super::sync_directory_ancestors(attempt)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn fixture() -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "mini-pre-submit-refusal-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        root
    }

    #[test]
    fn retains_exact_pre_call_frame_and_all_four_file_bindings() {
        let root = fixture();
        let config = root.join("config.json");
        let request = b"signed-observation";
        let frame = [vec![255], b"canonical-host-outcome".to_vec()].concat();
        fs::write(&config, b"pinned-config").unwrap();
        fs::write(root.join("signed-observation.bin"), request).unwrap();
        let manifest = json!({"format":"minidregg-resource-client-attempt-v1",
            "operation":"submit","config":config.to_str().unwrap()});
        fs::write(
            root.join("attempt.json"),
            serde_json::to_vec(&manifest).unwrap(),
        )
        .unwrap();
        retain(&root.join("plan.bin"), request, &config, &frame).unwrap();
        assert_eq!(
            fs::read(root.join("pre-submit-refusal.frame")).unwrap(),
            frame
        );
        let marker: Value =
            serde_json::from_slice(&fs::read(root.join("pre-submit-refusal.json")).unwrap())
                .unwrap();
        assert_eq!(marker["type"], "minidregg-pre-submit-refusal-v1");
        assert_eq!(marker["stage"], "prepare");
        assert_eq!(marker["operation"], 1);
        assert_eq!(marker["frameSha256"], digest(&frame));
        assert_eq!(marker["requestSha256"], digest(request));
        assert_eq!(marker["hostConfigSha256"], digest(b"pinned-config"));
        assert_eq!(
            marker["attemptManifestSha256"],
            digest(&fs::read(root.join("attempt.json")).unwrap())
        );
        assert!(!root.join("call.bin").exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn never_marks_non_refusal_or_existing_call() {
        let root = fixture();
        let config = root.join("config.json");
        fs::write(&config, b"config").unwrap();
        fs::write(root.join("signed-observation.bin"), b"request").unwrap();
        fs::write(
            root.join("attempt.json"),
            serde_json::to_vec(&json!({
            "format":"minidregg-resource-client-attempt-v1","operation":"submit",
            "config":config.to_str().unwrap()}))
            .unwrap(),
        )
        .unwrap();
        assert!(retain(&root.join("plan.bin"), b"request", &config, b"\x00ok").is_err());
        fs::write(root.join("call.bin"), b"signed-call").unwrap();
        assert!(retain(&root.join("plan.bin"), b"request", &config, b"\xffrefusal").is_err());
        assert!(!root.join("pre-submit-refusal.frame").exists());
        assert!(!root.join("pre-submit-refusal.json").exists());
        fs::remove_dir_all(root).unwrap();
    }
}
