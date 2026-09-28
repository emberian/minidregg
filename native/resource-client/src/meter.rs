//! Retain exact provider HTTP evidence before asking the pinned Lean Host for a
//! read-only usage quote. This module does not calculate a charge or submit a
//! settlement. The controller must independently bind the quote to its held
//! Mini reservation and durable gateway attempt.

use serde_json::Value;
use std::fs::File;
use std::io::Read;
use std::path::Path;

use super::{
    create_private, print_json, private_consumer_attempt, session_invoke, sync_directory_ancestors,
    transport, Result,
};

const MAX_METADATA: usize = 4096;
const MAX_REQUEST: usize = 1_048_576;
const MAX_RESPONSE: usize = 8_388_608;

fn bounded_file(path: &Path, maximum: usize, label: &str) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|error| format!("cannot open {label} {}: {error}", path.display()))?
        .take((maximum + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("cannot read {label} {}: {error}", path.display()))?;
    if bytes.is_empty() || bytes.len() > maximum {
        return Err(format!("{label} is empty or exceeds its byte bound"));
    }
    Ok(bytes)
}

fn canonical_decimal(value: &Value, name: &str) -> Result<()> {
    let text = value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("provider quote lacks {name}"))?;
    if text.is_empty()
        || text.len() > 80
        || !text.bytes().all(|byte| byte.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
    {
        return Err(format!("provider quote has noncanonical {name}"));
    }
    Ok(())
}

fn selected_provider(metadata: &[u8]) -> Result<Option<String>> {
    let value: Value = serde_json::from_slice(metadata)
        .map_err(|e| format!("invalid retained metering metadata: {e}"))?;
    match value.get("version") {
        None => Ok(None),
        Some(Value::String(version)) if version == "2" => {
            let id = value
                .get("providerResourceId")
                .and_then(Value::as_str)
                .ok_or("v2 metering metadata lacks providerResourceId")?;
            if id == "0"
                || id.is_empty()
                || id.len() > 80
                || !id.bytes().all(|byte| byte.is_ascii_digit())
                || (id.len() > 1 && id.starts_with('0'))
            {
                return Err("v2 metering metadata providerResourceId is not canonical".into());
            }
            Ok(Some(id.to_owned()))
        }
        _ => Err("unknown metering metadata version".into()),
    }
}

fn quoted_report(value: &Value, expected_provider: Option<&str>) -> Result<()> {
    if value.get("type").and_then(Value::as_str) != Some("minidregg-provider-metering-v1")
        || value.get("status").and_then(Value::as_str) != Some("quoted-reported-usage")
    {
        return Err("unexpected provider metering reply type/status".into());
    }
    let model = value
        .get("model")
        .and_then(Value::as_str)
        .ok_or("provider quote lacks model")?;
    if model.is_empty() || model.len() > 256 {
        return Err("provider quote has invalid model".into());
    }
    for field in [
        "providerResourceId",
        "tariffVersion",
        "tariffDigest",
        "requestDigest",
        "responseDigest",
        "requestBytes",
        "responseBytes",
        "promptTokens",
        "completionTokens",
        "totalTokens",
        "reserve",
        "charge",
    ] {
        canonical_decimal(value, field)?;
    }
    if expected_provider
        .is_some_and(|id| value.get("providerResourceId").and_then(Value::as_str) != Some(id))
    {
        return Err("provider quote selected another configured resource".into());
    }
    let operation = value
        .get("operation")
        .ok_or("provider quote lacks operation")?;
    if operation.get("type").and_then(Value::as_str) != Some("settle")
        || operation.get("charge") != value.get("charge")
    {
        return Err("provider quote has inconsistent settlement operation".into());
    }
    if value.get("claim").and_then(Value::as_str)
        != Some("provider-reported usage under operator tariff; not invoice-verified")
    {
        return Err("provider quote lacks provenance limitation".into());
    }
    Ok(())
}

pub(crate) fn meter(
    host: &Path,
    config: &Path,
    socket: &Path,
    metadata: &Path,
    request: &Path,
    response: &Path,
    directory: &Path,
) -> Result<()> {
    if !socket.is_absolute() {
        return Err("meter requires an absolute persistent Host socket path".into());
    }
    // Read each input once. The bytes submitted to Lean are precisely those
    // copied into the private attempt, even if an input pathname later changes.
    let metadata_bytes = bounded_file(metadata, MAX_METADATA, "provider metadata")?;
    let expected_provider = selected_provider(&metadata_bytes)?;
    let request_bytes = bounded_file(request, MAX_REQUEST, "provider request")?;
    let response_bytes = bounded_file(response, MAX_RESPONSE, "provider response")?;
    let total = 1usize
        .checked_add(8)
        .and_then(|value| value.checked_add(metadata_bytes.len()))
        .and_then(|value| value.checked_add(request_bytes.len()))
        .and_then(|value| value.checked_add(response_bytes.len()))
        .ok_or("provider metering frame length overflow")?;
    if total > transport::HOST_MAX_FRAME {
        return Err("provider metering inputs exceed Host frame budget".into());
    }
    let retained_config = private_consumer_attempt(host, config, directory, "meter")?;
    create_private(&directory.join("metadata.json"), &metadata_bytes)?;
    create_private(&directory.join("request.bin"), &request_bytes)?;
    create_private(&directory.join("response.bin"), &response_bytes)?;
    sync_directory_ancestors(directory)?;

    let mut payload = Vec::with_capacity(total - 1);
    payload.extend_from_slice(&(metadata_bytes.len() as u32).to_le_bytes());
    payload.extend_from_slice(&metadata_bytes);
    payload.extend_from_slice(&(request_bytes.len() as u32).to_le_bytes());
    payload.extend_from_slice(&request_bytes);
    payload.extend_from_slice(&response_bytes);
    let frame = session_invoke(host, socket, &retained_config, 19, &payload)?;
    create_private(&directory.join("reply.frame"), &frame)?;
    sync_directory_ancestors(directory)?;
    match frame.first() {
        Some(19) => {
            let value: Value = serde_json::from_slice(&frame[1..]).map_err(|error| {
                format!("invalid provider metering reply; complete frame retained: {error}")
            })?;
            quoted_report(&value, expected_provider.as_deref())?;
            create_private(&directory.join("meter.json"), &frame[1..])?;
            sync_directory_ancestors(directory)?;
            print_json(&value)
        }
        Some(255) => {
            create_private(&directory.join("refusal.bin"), &frame[1..])?;
            if let Ok(value) = serde_json::from_slice::<Value>(&frame[1..]) {
                create_private(&directory.join("refusal.json"), &frame[1..])?;
                print_json(&value)?;
            }
            sync_directory_ancestors(directory)?;
            Err("Host refused provider metering; complete reply retained".into())
        }
        _ => Err("unexpected provider metering reply operation; complete frame retained".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn quote_requires_source_operation_and_provenance() {
        let mut report = json!({
            "type":"minidregg-provider-metering-v1",
            "status":"quoted-reported-usage",
            "providerResourceId":"7004","model":"fixture","tariffVersion":"1",
            "tariffDigest":"1","requestDigest":"2","responseDigest":"3",
            "requestBytes":"10","responseBytes":"20","promptTokens":"1",
            "completionTokens":"2","totalTokens":"3","reserve":"5","charge":"5",
            "operation":{"type":"settle","charge":"5"},
            "claim":"provider-reported usage under operator tariff; not invoice-verified"
        });
        assert!(quoted_report(&report, None).is_ok());
        assert!(quoted_report(&report, Some("7004")).is_ok());
        assert!(quoted_report(&report, Some("7950")).is_err());
        report["operation"]["charge"] = json!("4");
        assert!(quoted_report(&report, None).is_err());
        report["operation"]["charge"] = json!("5");
        report["requestDigest"] = json!("02");
        assert!(quoted_report(&report, None).is_err());
    }

    #[test]
    fn selected_provider_is_explicit_in_v2_metadata() {
        let metadata = br#"{"version":"2","providerResourceId":"7950","status":"200","contentType":"application/json","reserve":"8"}"#;
        assert_eq!(
            selected_provider(metadata).unwrap().as_deref(),
            Some("7950")
        );
        assert!(selected_provider(br#"{"version":"2","providerResourceId":"07950"}"#).is_err());
        assert!(selected_provider(br#"{"version":"3","providerResourceId":"7950"}"#).is_err());
        assert_eq!(selected_provider(br#"{"status":"200"}"#).unwrap(), None);
    }
}
