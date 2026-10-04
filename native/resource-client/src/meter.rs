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
    if !mini_sdk::decimal::is_canonical_max(text, 80)
    {
        return Err(format!("provider quote has noncanonical {name}"));
    }
    Ok(())
}

/// The metering selection in the retained metadata (v3): the configured
/// provider resource and the route the purse recorded at reserve.
struct Selection {
    provider: String,
    route: String,
}

fn selected_provider(metadata: &[u8]) -> Result<Selection> {
    let value: Value = serde_json::from_slice(metadata)
        .map_err(|e| format!("invalid retained metering metadata: {e}"))?;
    if value.get("version").and_then(Value::as_str) != Some("3") {
        return Err("unknown metering metadata version (v3 names the route)".into());
    }
    let id = value
        .get("providerResourceId")
        .and_then(Value::as_str)
        .ok_or("metering metadata lacks providerResourceId")?;
    if id == "0" || !mini_sdk::decimal::is_canonical_max(id, 80) {
        return Err("metering metadata providerResourceId is not canonical".into());
    }
    let route = value
        .get("route")
        .and_then(Value::as_str)
        .filter(|route| matches!(*route, "user" | "pool" | "homelab"))
        .ok_or("metering metadata route must be user, pool or homelab")?;
    Ok(Selection {
        provider: id.to_owned(),
        route: route.to_owned(),
    })
}

fn quoted_report(value: &Value, expected: &Selection) -> Result<()> {
    let user = expected.route == "user";
    let (status, claim) = if user {
        (
            "quoted-per-operation",
            "per-operation fee under operator tariff; the provider bill is the key owner's",
        )
    } else {
        (
            "quoted-reported-usage",
            "provider-reported usage under operator tariff; not invoice-verified",
        )
    };
    if value.get("type").and_then(Value::as_str) != Some("minidregg-provider-metering-v2")
        || value.get("status").and_then(Value::as_str) != Some(status)
        || value.get("route").and_then(Value::as_str) != Some(expected.route.as_str())
    {
        return Err("unexpected provider metering reply type/status/route".into());
    }
    let model = value
        .get("model")
        .and_then(Value::as_str)
        .ok_or("provider quote lacks model")?;
    if model.is_empty() || model.len() > 256 {
        return Err("provider quote has invalid model".into());
    }
    let counts: &[&str] = if user {
        &[]
    } else {
        &["promptTokens", "completionTokens", "totalTokens"]
    };
    for field in [
        "providerResourceId",
        "tariffVersion",
        "tariffDigest",
        "requestDigest",
        "responseDigest",
        "requestBytes",
        "responseBytes",
        "perOp",
        "reserve",
        "charge",
    ]
    .iter()
    .chain(counts)
    {
        canonical_decimal(value, field)?;
    }
    if user && ["promptTokens", "completionTokens", "totalTokens"]
        .iter()
        .any(|field| value.get(*field).is_some())
    {
        return Err("a user-route quote carries no token counts".into());
    }
    if value.get("providerResourceId").and_then(Value::as_str) != Some(expected.provider.as_str()) {
        return Err("provider quote selected another configured resource".into());
    }
    let operation = value
        .get("operation")
        .ok_or("provider quote lacks operation")?;
    if operation.get("type").and_then(Value::as_str) != Some("settle")
        || operation.get("charge") != value.get("charge")
        || operation.get("route") != value.get("route")
    {
        return Err("provider quote has inconsistent settlement operation".into());
    }
    if value.get("claim").and_then(Value::as_str) != Some(claim) {
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
            quoted_report(&value, &expected_provider)?;
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
    fn quote_requires_source_operation_route_and_provenance() {
        let pool = Selection { provider: "7004".into(), route: "pool".into() };
        let mut report = json!({
            "type":"minidregg-provider-metering-v2",
            "status":"quoted-reported-usage","route":"pool",
            "providerResourceId":"7004","model":"fixture","tariffVersion":"1",
            "tariffDigest":"1","requestDigest":"2","responseDigest":"3",
            "requestBytes":"10","responseBytes":"20","promptTokens":"1",
            "completionTokens":"2","totalTokens":"3","perOp":"2","reserve":"5","charge":"5",
            "operation":{"type":"settle","charge":"5","route":"pool"},
            "claim":"provider-reported usage under operator tariff; not invoice-verified"
        });
        assert!(quoted_report(&report, &pool).is_ok());
        let other = Selection { provider: "7950".into(), route: "pool".into() };
        assert!(quoted_report(&report, &other).is_err());
        let user = Selection { provider: "7004".into(), route: "user".into() };
        assert!(quoted_report(&report, &user).is_err());
        report["operation"]["route"] = json!("user");
        assert!(quoted_report(&report, &pool).is_err());
        report["operation"]["route"] = json!("pool");
        report["operation"]["charge"] = json!("4");
        assert!(quoted_report(&report, &pool).is_err());
        report["operation"]["charge"] = json!("5");
        report["requestDigest"] = json!("02");
        assert!(quoted_report(&report, &pool).is_err());
        let fee = json!({
            "type":"minidregg-provider-metering-v2","status":"quoted-per-operation","route":"user",
            "providerResourceId":"7004","model":"fixture","tariffVersion":"1",
            "tariffDigest":"1","requestDigest":"2","responseDigest":"3",
            "requestBytes":"10","responseBytes":"20","perOp":"1","reserve":"1","charge":"1",
            "operation":{"type":"settle","charge":"1","route":"user"},
            "claim":"per-operation fee under operator tariff; the provider bill is the key owner's"
        });
        assert!(quoted_report(&fee, &user).is_ok());
        let mut counted = fee.clone();
        counted["promptTokens"] = json!("1");
        assert!(quoted_report(&counted, &user).is_err());
    }

    #[test]
    fn metadata_v3_names_the_provider_and_the_route() {
        let metadata = br#"{"version":"3","providerResourceId":"7950","route":"pool","status":"200","contentType":"application/json","reserve":"8"}"#;
        let selected = selected_provider(metadata).unwrap();
        assert_eq!((selected.provider.as_str(), selected.route.as_str()), ("7950", "pool"));
        assert!(selected_provider(br#"{"version":"3","providerResourceId":"07950","route":"pool"}"#).is_err());
        assert!(selected_provider(br#"{"version":"3","providerResourceId":"7950","route":"none"}"#).is_err());
        assert!(selected_provider(br#"{"version":"2","providerResourceId":"7950"}"#).is_err());
        assert!(selected_provider(br#"{"status":"200"}"#).is_err());
    }
}
