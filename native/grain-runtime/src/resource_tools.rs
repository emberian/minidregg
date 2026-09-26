//! Operator-named, signed reads of shared Mini resources. This module only
//! selects a fixed observe grant and invokes the native client; the Lean host
//! checks the current grant and materializes the resource view.
use crate::{write_new, Config, PublicationGrant, Result, ToolTask};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};

// A complete content page can include the fn consumer's typed inbox atom and
// exact carrier. Refuse larger pages explicitly instead of returning a prefix.
// The native content page may carry several 36 KiB inbox atoms. Its JSON
// presentation repeats bytes in the whole-page canonical stream and per-entry
// fields, so the operator may provision a larger complete response.
const MAX_RESULT_BYTES: usize = 4 * 1024 * 1024;

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct AllowedResourceRead {
    pub name: String,
    pub kind: String,
    pub target: String,
    pub observe_capability: String,
    pub max_result_bytes: usize,
}

pub(super) fn validate_reads(
    reads: &[AllowedResourceRead],
    publications: &[PublicationGrant],
) -> Result<()> {
    for (index, read) in reads.iter().enumerate() {
        if read.name.is_empty()
            || !read
                .name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'-')
        {
            return Err("resource read name must be alphanumeric or '-'".into());
        }
        if reads[..index].iter().any(|prior| prior.name == read.name) {
            return Err(format!("duplicate resource read name {}", read.name));
        }
        if !matches!(read.kind.as_str(), "object" | "account" | "program") {
            return Err(format!("unknown resource read kind for {}", read.name));
        }
        crate::decimal(&read.target, "resource read target")?;
        crate::decimal(&read.observe_capability, "resource observe capability")?;
        if read.max_result_bytes == 0 || read.max_result_bytes > MAX_RESULT_BYTES {
            return Err(format!(
                "{} maxResultBytes must be between 1 and {MAX_RESULT_BYTES}",
                read.name
            ));
        }
        if publications
            .iter()
            .any(|publication| publication.capability == read.observe_capability)
        {
            return Err(format!(
                "{} needs a distinct observe capability outside publication authority",
                read.name
            ));
        }
    }
    Ok(())
}

pub(super) fn select_read<'a>(
    reads: &'a [AllowedResourceRead],
    arguments: &Value,
) -> Result<&'a AllowedResourceRead> {
    let object = arguments
        .as_object()
        .ok_or("mini_read_resource arguments must be an object")?;
    if object.len() != 1 {
        return Err("mini_read_resource requires exactly one name argument".into());
    }
    let name = object
        .get("name")
        .and_then(Value::as_str)
        .ok_or("mini_read_resource name must be a string")?;
    reads
        .iter()
        .find(|read| read.name == name)
        .ok_or_else(|| format!("resource read {name} is not allowlisted"))
}

pub(super) fn read_resource(
    config: &Config,
    tool: &ToolTask,
    read: &AllowedResourceRead,
    nonce: u64,
) -> Result<Value> {
    if read.observe_capability == tool.capability
        || read.observe_capability == tool.parent_capability
    {
        return Err("resource read needs an observe grant distinct from mutation authority".into());
    }
    // The caller selects `read` by its configured name and allocates `nonce`
    // from the durable journal before entering this function. No caller-supplied
    // target, grant, signer, or path is accepted here.
    let dir = config.state_dir.join(format!("resource-read-{nonce:016}"));
    fs::create_dir(&dir).map_err(|e| format!("resource read directory: {e}"))?;
    let intent = json!({
        "subject": tool.subject,
        "nonce": nonce.to_string(),
        "purpose": {
            "type": "query", "kind": read.kind, "target": read.target,
            "view": "resource"
        },
        "grants": [{
            "kind": read.kind, "target": read.target,
            "capability": read.observe_capability
        }]
    });
    let intent_path = dir.join("intent-source.json");
    let intent_bytes = serde_json::to_vec_pretty(&intent).map_err(|e| e.to_string())?;
    write_new(&intent_path, &intent_bytes)?;

    let attempt = dir.join("attempt");
    let mut command = Command::new(&config.mini);
    command
        .arg("query")
        .arg("--host")
        .arg(&config.host)
        .arg("--config")
        .arg(&config.host_config)
        .arg("--intent")
        .arg(&intent_path)
        .arg("--key")
        .arg(&tool.custody_key)
        .arg("--view")
        .arg("resource")
        .arg("--dir")
        .arg(&attempt)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    if let Some(socket) = &config.host_socket {
        command.arg("--socket").arg(socket);
    }
    let status = command
        .status()
        .map_err(|e| format!("native Mini resource query: {e}"))?;
    if !status.success() {
        return Err(format!(
            "native Mini refused resource read {} ({}); retained attempt at {}",
            read.name,
            status,
            attempt.display()
        ));
    }
    let path = attempt.join("view.json");
    let bytes = read_bounded(&path, read.max_result_bytes)?;
    let view: Value = serde_json::from_slice(&bytes)
        .map_err(|e| format!("native resource view is not JSON: {e}"))?;
    if view.get("type").and_then(Value::as_str) != Some("resource")
        || !view.get("page").is_some_and(Value::is_object)
    {
        return Err("native resource query returned the wrong view shape".into());
    }
    let result = json!({"kind":read.kind,"target":read.target,"view":view});
    let result_len = serde_json::to_vec(&result)
        .map_err(|e| e.to_string())?
        .len();
    if result_len > read.max_result_bytes {
        return Err(format!(
            "signed resource result is {result_len} bytes, above {} maxResultBytes; complete attempt retained at {}",
            read.max_result_bytes,
            attempt.display()
        ));
    }
    Ok(result)
}

fn read_bounded(path: &Path, max: usize) -> Result<Vec<u8>> {
    let size = fs::metadata(path)
        .map_err(|e| format!("native resource view unavailable: {e}"))?
        .len();
    if size > max as u64 {
        return Err(format!(
            "signed resource view is {size} bytes, above {max} maxResultBytes; complete view retained at {}",
            path.display()
        ));
    }
    let bytes = fs::read(path).map_err(|e| format!("native resource view read: {e}"))?;
    if bytes.len() > max {
        return Err(format!(
            "signed resource view grew beyond {max} maxResultBytes; complete view retained at {}",
            path.display()
        ));
    }
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read(name: &str, capability: &str) -> AllowedResourceRead {
        AllowedResourceRead {
            name: name.into(),
            kind: "object".into(),
            target: "8001".into(),
            observe_capability: capability.into(),
            max_result_bytes: 64 * 1024,
        }
    }

    #[test]
    fn rejects_publication_authority_and_ambiguous_names() {
        let publications = vec![PublicationGrant {
            kind: "object".into(),
            target: "8001".into(),
            capability: "88".into(),
            observe_capability: "89".into(),
        }];
        assert!(validate_reads(&[read("inbox", "90")], &publications).is_ok());
        assert!(validate_reads(&[read("inbox", "88")], &publications).is_err());
        assert!(validate_reads(&[read("inbox", "89")], &publications).is_ok());
        assert!(validate_reads(&[read("inbox", "90"), read("inbox", "91")], &[]).is_err());
    }

    #[test]
    fn refuses_unbounded_view() {
        let mut entry = read("inbox", "90");
        entry.max_result_bytes = MAX_RESULT_BYTES + 1;
        assert!(validate_reads(&[entry], &[]).is_err());
    }

    #[test]
    fn accepts_only_exact_allowlisted_name_argument() {
        let reads = [read("inbox", "90")];
        assert!(select_read(&reads, &json!({"name":"inbox"})).is_ok());
        assert!(select_read(&reads, &json!({"name":"other"})).is_err());
        assert!(select_read(&reads, &json!({"name":"inbox","target":"999"})).is_err());
        assert!(select_read(&reads, &json!({"name":90})).is_err());
    }
}
