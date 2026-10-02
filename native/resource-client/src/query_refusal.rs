//! Keep a socket query refusal as typed, request-bound evidence. A caller may
//! make a fresh read after stale-root; this marker never authorizes a submit.
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{fs, io, path::Path};

fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn read(path: &Path, limit: usize) -> Result<Vec<u8>, String> {
    use std::io::Read;
    use std::os::unix::fs::MetadataExt;
    let named = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !named.file_type().is_file() || named.len() > limit as u64 {
        return Err("query refusal artifact is not a bounded regular file".into());
    }
    let file = fs::File::open(path).map_err(|e| e.to_string())?;
    let opened = file.metadata().map_err(|e| e.to_string())?;
    if !opened.is_file() || (opened.dev(), opened.ino()) != (named.dev(), named.ino()) {
        return Err("query refusal artifact changed while opening".into());
    }
    let mut bytes = Vec::new();
    file.take(limit as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > limit {
        return Err("query refusal artifact exceeds bound".into());
    }
    Ok(bytes)
}

/// Called only at socket op 5's actual op-255 response. Keep the whole frame
/// and hashes; the controller asks the pinned Host to decode it independently.
pub(crate) fn retain(
    destination: &Path,
    request: &[u8],
    config: &Path,
    frame: &[u8],
) -> Result<(), String> {
    if frame.len() < 2 || frame.len() > super::transport::HOST_MAX_FRAME + 1 || frame[0] != 255 {
        return Err("query refusal is not a bounded op 255 frame".into());
    }
    let attempt = destination
        .parent()
        .ok_or("query destination has no parent")?;
    if destination
        .file_name()
        .is_none_or(|name| name != "view.bin")
        || config != attempt.join("config.json")
    {
        return Err("query refusal lacks its retained query destination/config".into());
    }
    for name in [
        "view.bin",
        "view.json",
        "plan.bin",
        "call.bin",
        "outcome.bin",
        "outcome.json",
    ] {
        match fs::symlink_metadata(attempt.join(name)) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            _ => return Err("query refusal has a result or submit artifact".into()),
        }
    }
    let signed = read(
        &attempt.join("signed-observation.bin"),
        super::transport::HOST_MAX_FRAME,
    )?;
    if signed.is_empty() || signed != request {
        return Err("query refusal differs from retained signed observation".into());
    }
    let config_bytes = read(config, 65_536)?;
    let manifest_bytes = read(&attempt.join("attempt.json"), 65_536)?;
    let manifest: Value = serde_json::from_slice(&manifest_bytes).map_err(|e| e.to_string())?;
    if manifest["format"] != "minidregg-resource-client-attempt-v1"
        || manifest["operation"] != "query"
        || manifest["config"].as_str().map(Path::new) != Some(super::absolute(config)?.as_path())
    {
        return Err("query refusal manifest is not this query attempt".into());
    }
    let marker = json!({"type":"minidregg-query-refusal-v1", "stage":"query", "operation":5,
        "frameSha256":digest(frame), "requestSha256":digest(request),
        "hostConfigSha256":digest(&config_bytes), "attemptManifestSha256":digest(&manifest_bytes)});
    super::create_private(&attempt.join("query-refusal.frame"), frame)?;
    super::create_private(
        &attempt.join("query-refusal.json"),
        &serde_json::to_vec_pretty(&marker).map_err(|e| e.to_string())?,
    )?;
    super::sync_directory_ancestors(attempt)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> std::path::PathBuf {
        let root = std::env::temp_dir().join(format!(
            "mini-query-refusal-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        fs::write(root.join("config.json"), b"config").unwrap();
        fs::write(root.join("signed-observation.bin"), b"signed").unwrap();
        fs::write(
            root.join("attempt.json"),
            serde_json::to_vec(&json!({
            "format":"minidregg-resource-client-attempt-v1", "operation":"query",
            "config":root.join("config.json")}))
            .unwrap(),
        )
        .unwrap();
        root
    }
    #[test]
    fn keeps_exact_frame_and_bindings_without_interpreting_error_text() {
        let root = fixture();
        retain(
            &root.join("view.bin"),
            b"signed",
            &root.join("config.json"),
            b"\xffencoded",
        )
        .unwrap();
        let marker: Value =
            serde_json::from_slice(&fs::read(root.join("query-refusal.json")).unwrap()).unwrap();
        assert_eq!(marker["operation"], 5);
        assert_eq!(marker["frameSha256"], digest(b"\xffencoded"));
        assert_eq!(marker["requestSha256"], digest(b"signed"));
        assert_eq!(marker["hostConfigSha256"], digest(b"config"));
        assert_eq!(
            marker["attemptManifestSha256"],
            digest(&fs::read(root.join("attempt.json")).unwrap())
        );
        assert_eq!(
            fs::read(root.join("query-refusal.frame")).unwrap(),
            b"\xffencoded"
        );
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn refuses_mismatched_request_submit_and_dangling_result() {
        for variant in ["request", "submit", "symlink"] {
            let root = fixture();
            if variant == "submit" {
                let path = root.join("attempt.json");
                let mut value: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
                value["operation"] = json!("submit");
                fs::write(path, serde_json::to_vec(&value).unwrap()).unwrap();
            }
            if variant == "symlink" {
                std::os::unix::fs::symlink(root.join("absent"), root.join("view.bin")).unwrap();
            }
            assert!(retain(
                &root.join("view.bin"),
                if variant == "request" {
                    b"other"
                } else {
                    b"signed"
                },
                &root.join("config.json"),
                b"\xffencoded"
            )
            .is_err());
            assert!(!root.join("query-refusal.json").exists());
            fs::remove_dir_all(root).unwrap();
        }
    }
}
