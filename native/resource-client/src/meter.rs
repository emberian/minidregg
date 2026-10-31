//! Retain exact provider HTTP evidence before asking the pinned Lean Host for a
//! read-only usage quote. This module does not calculate a charge or submit a
//! settlement. The controller must independently bind the quote to its held
//! Mini reservation and durable gateway attempt.

use serde_json::Value;
use std::path::Path;

use super::{
    create_private, print_json, private_consumer_attempt, session_invoke, transport, Result,
};

const MAX_METADATA: usize = 4096;
const MAX_REQUEST: usize = 1_048_576;
const MAX_RESPONSE: usize = 8_388_608;

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

/// The metering selection in the retained metadata (v4,
/// `Host/ProviderUsage.lean` `quotePayload`): the configured provider
/// resource, the route the purse recorded at reserve, and the leg.
struct Selection {
    provider: String,
    route: String,
}

fn selected_provider(metadata: &[u8]) -> Result<Selection> {
    let value: Value = serde_json::from_slice(metadata)
        .map_err(|e| format!("invalid retained metering metadata: {e}"))?;
    if value.get("version").and_then(Value::as_str) != Some("4") {
        return Err("unknown metering metadata version (v4 names the route and the leg)".into());
    }
    if !value
        .get("leg")
        .and_then(Value::as_str)
        .is_some_and(|leg| matches!(leg, "complete" | "timeout" | "truncated" | "lost"))
    {
        return Err("metering metadata leg must be complete, timeout, truncated or lost".into());
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
    // The four bases `Host/ProviderUsage.lean` `reportJson` answers: the user
    // route is always the per-operation fee; a metered route is reported
    // usage, a refused (non-200) reply at the route fee, or an undecided leg
    // at the hold. Only reported usage carries token counts.
    let status = value.get("status").and_then(Value::as_str).unwrap_or("");
    let claim = match (user, status) {
        (true, "quoted-per-operation") => {
            "per-operation fee under operator tariff; the provider bill is the key owner's"
        }
        (false, "quoted-reported-usage") => {
            "provider-reported usage under operator tariff; not invoice-verified"
        }
        (false, "quoted-refused-reply") => {
            "complete non-200 reply: the route's declared per-operation fee; the provider bills nothing for a refused call"
        }
        (false, "quoted-undecided-at-hold") => {
            "no usage record could be read for this leg: the whole hold, the maximum the provider may have billed"
        }
        _ => return Err("unexpected provider metering reply type/status/route".into()),
    };
    if value.get("type").and_then(Value::as_str) != Some("minidregg-provider-metering-v2")
        || value.get("route").and_then(Value::as_str) != Some(expected.route.as_str())
        || !value
            .get("leg")
            .and_then(Value::as_str)
            .is_some_and(|leg| matches!(leg, "complete" | "timeout" | "truncated" | "lost"))
    {
        return Err("unexpected provider metering reply type/status/route".into());
    }
    let counted = status == "quoted-reported-usage";
    let model = value
        .get("model")
        .and_then(Value::as_str)
        .ok_or("provider quote lacks model")?;
    if model.is_empty() || model.len() > 256 {
        return Err("provider quote has invalid model".into());
    }
    let counts: &[&str] = if !counted {
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
    if !counted && ["promptTokens", "completionTokens", "totalTokens"]
        .iter()
        .any(|field| value.get(*field).is_some())
    {
        return Err("only a reported-usage quote carries token counts".into());
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
    let metadata_bytes = crate::fsio::read_bounded(metadata, MAX_METADATA)?;
    let expected_provider = selected_provider(&metadata_bytes)?;
    let request_bytes = crate::fsio::read_bounded(request, MAX_REQUEST)?;
    let response_bytes = crate::fsio::read_bounded(response, MAX_RESPONSE)?;
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

    let mut payload = Vec::with_capacity(total - 1);
    payload.extend_from_slice(&(metadata_bytes.len() as u32).to_le_bytes());
    payload.extend_from_slice(&metadata_bytes);
    payload.extend_from_slice(&(request_bytes.len() as u32).to_le_bytes());
    payload.extend_from_slice(&request_bytes);
    payload.extend_from_slice(&response_bytes);
    let frame = session_invoke(host, socket, &retained_config, mini_sdk::host_operations::PROVIDER_USAGE_QUOTE, &payload)?;
    create_private(&directory.join("reply.frame"), &frame)?;
    match frame.first() {
        Some(19) => {
            let value: Value = serde_json::from_slice(&frame[1..]).map_err(|error| {
                format!("invalid provider metering reply; complete frame retained: {error}")
            })?;
            quoted_report(&value, &expected_provider)?;
            create_private(&directory.join("meter.json"), &frame[1..])?;
            print_json(&value)
        }
        Some(&(crate::RESPONSE_HOST_OUTCOME | crate::RESPONSE_NO_RECORD)) => {
            create_private(&directory.join("refusal.bin"), &frame[1..])?;
            if let Ok(value) = serde_json::from_slice::<Value>(&frame[1..]) {
                create_private(&directory.join("refusal.json"), &frame[1..])?;
                print_json(&value)?;
            }
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
            "type":"minidregg-provider-metering-v2","leg":"complete",
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
            "type":"minidregg-provider-metering-v2","leg":"complete","status":"quoted-per-operation","route":"user",
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
        let refused = json!({
            "type":"minidregg-provider-metering-v2","leg":"complete","status":"quoted-refused-reply","route":"pool",
            "providerResourceId":"7004","model":"fixture","tariffVersion":"1",
            "tariffDigest":"1","requestDigest":"2","responseDigest":"3",
            "requestBytes":"10","responseBytes":"20","perOp":"2","reserve":"5","charge":"2",
            "operation":{"type":"settle","charge":"2","route":"pool"},
            "claim":"complete non-200 reply: the route's declared per-operation fee; the provider bills nothing for a refused call"
        });
        assert!(quoted_report(&refused, &pool).is_ok());
        assert!(quoted_report(&refused, &user).is_err());
        let mut undecided = refused.clone();
        undecided["status"] = json!("quoted-undecided-at-hold");
        undecided["leg"] = json!("lost");
        undecided["claim"] = json!("no usage record could be read for this leg: the whole hold, the maximum the provider may have billed");
        assert!(quoted_report(&undecided, &pool).is_ok());
        undecided["promptTokens"] = json!("1");
        assert!(quoted_report(&undecided, &pool).is_err());
    }

    #[test]
    fn metadata_v4_names_the_provider_the_route_and_the_leg() {
        let metadata = br#"{"version":"4","providerResourceId":"7950","route":"pool","leg":"complete","status":"200","contentType":"application/json","reserve":"8"}"#;
        let selected = selected_provider(metadata).unwrap();
        assert_eq!((selected.provider.as_str(), selected.route.as_str()), ("7950", "pool"));
        assert!(selected_provider(br#"{"version":"4","providerResourceId":"07950","route":"pool","leg":"complete"}"#).is_err());
        assert!(selected_provider(br#"{"version":"4","providerResourceId":"7950","route":"none","leg":"complete"}"#).is_err());
        assert!(selected_provider(br#"{"version":"2","providerResourceId":"7950"}"#).is_err());
        let v3 = selected_provider(br#"{"version":"3","providerResourceId":"7950","route":"pool","status":"200","contentType":"application/json","reserve":"8"}"#);
        assert!(v3.as_ref().err().is_some_and(|e| e.contains("unknown metering metadata version") && e.contains("v4")),
            "a v3 frame is refused by name: {:?}", v3.err());
        assert!(selected_provider(br#"{"version":"4","providerResourceId":"7950","route":"pool","leg":"gone"}"#).is_err());
        assert!(selected_provider(br#"{"status":"200"}"#).is_err());
    }
}
