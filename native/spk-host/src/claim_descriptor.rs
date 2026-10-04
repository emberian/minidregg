//! Physical comparison of Mini's v2 claim inspection with one verified SPK.
//! Inspector JSON interprets retained op26 callback bytes; it does not mint a
//! claim. The caller must obtain those bytes from the private fresh-tip route.
#![allow(dead_code)] // Resident lifecycle-v2 route is not linked yet.

use crate::hostd::VerifiedBegin;
use crate::materialize::{signed_schema_source, InstalledPackage};
use minidregg_spk_rpc::{decode_bridge_config, BridgeConfig};
use serde_json::{json, Value};
use std::io;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn hex(bytes: &[u8]) -> String {
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(result, "{byte:02x}").expect("writing to String");
    }
    result
}

fn text<'a>(value: &'a Value, field: &str) -> io::Result<&'a str> {
    value
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("source descriptor inspection field absent"))
}

fn canonical_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

pub(crate) struct MatchedPackage {
    pub bridge: BridgeConfig,
    pub descriptor_root: String,
    pub begin: VerifiedBegin,
}

const IMAGE_ID_PREFIX: &[u8] = b"DREGG/SPK-IMAGE/v1";

fn verified_identity(
    inspected: &Value,
    raw_sha256: &[u8; 32],
    expected_kind: &str,
) -> io::Result<VerifiedBegin> {
    if text(inspected, "kind")? != expected_kind {
        return Err(invalid("resident claim kind differs from physical phase"));
    }
    let app = text(inspected, "app")?;
    let generation = text(inspected, "processGeneration")?;
    let operation_id = text(inspected, "operationId")?;
    if !canonical_decimal(app) || !canonical_decimal(generation) || !canonical_decimal(operation_id)
    {
        return Err(invalid("source lifecycle coordinate is noncanonical"));
    }
    let app: u64 = app
        .parse()
        .map_err(|_| invalid("app exceeds host unit range"))?;
    let generation: u64 = generation
        .parse()
        .map_err(|_| invalid("generation exceeds host unit range"))?;
    if generation == 0 {
        return Err(invalid("resident process generation is zero"));
    }
    let unit = String::from_utf8(crate::lifecycle_v3_native::unhex(text(inspected, "processIdentityHex")?)?)
        .map_err(|_| invalid("source process identity is not UTF-8"))?;
    if !crate::broker::parse_resident_unit(&unit).is_some_and(|(_, unit_app, unit_generation)| {
        unit_app == app.to_string() && unit_generation == generation.to_string()
    }) {
        return Err(invalid("source process identity differs from pinned unit"));
    }
    let mut image_id = Vec::with_capacity(IMAGE_ID_PREFIX.len() + 32);
    image_id.extend_from_slice(IMAGE_ID_PREFIX);
    image_id.extend_from_slice(raw_sha256);
    let image_id_hex = hex(&image_id);
    if text(inspected, "imageIdentityHex")? != image_id_hex {
        return Err(invalid("source image identity differs from signed SPK"));
    }
    let receipt = inspected
        .get("receipt")
        .ok_or_else(|| invalid("source claim receipt absent"))?;
    let transaction_id = text(receipt, "transactionId")?;
    let event_id = text(receipt, "eventId")?;
    if !canonical_decimal(transaction_id) || !canonical_decimal(event_id) {
        return Err(invalid("source claim receipt identity is noncanonical"));
    }
    Ok(VerifiedBegin {
        app,
        generation,
        operation_id: operation_id.to_owned(),
        transaction_id: transaction_id.to_owned(),
        event_id: event_id.to_owned(),
        package_sha256: hex(raw_sha256),
        image_identity: image_id_hex,
        process_identity: unit.clone(),
        unit,
    })
}

/// `schema_inspection` must come from the pinned Host's strict inspection of
/// bytes it just source-authored from `signed_schema_source`. Comparing its
/// canonical echo and role fields to the signed bridge closes the physical
/// schema join without reimplementing Mini's cSHAKE/codec in Rust.
fn compare_claim_kind(
    package: &InstalledPackage,
    committed_frame: &[u8],
    claim_inspection: &[u8],
    schema_bytes: &[u8],
    schema_inspection: &[u8],
    expected_kind: &str,
) -> io::Result<MatchedPackage> {
    if committed_frame.is_empty() || committed_frame.len() > 12_102_759 {
        return Err(invalid("retained lifecycle claim frame size refused"));
    }
    if claim_inspection.is_empty()
        || claim_inspection.len() > 96_822_080
        || schema_bytes.is_empty()
        || schema_bytes.len() > 65_536
        || schema_inspection.is_empty()
        || schema_inspection.len() > 65_536
    {
        return Err(invalid("source claim or schema inspection size refused"));
    }
    let signed_bridge = package
        .signed_bridge_config
        .as_deref()
        .ok_or_else(|| invalid("bridge-only SPK lacks signed config"))?;
    let bridge = decode_bridge_config(signed_bridge).map_err(io::Error::other)?;
    if bridge.save_identity_caps || bridge.expect_app_hooks {
        return Err(invalid(
            "SPK bridge requires unsupported identity or hook behavior",
        ));
    }
    if bridge
        .api_path
        .as_deref()
        .is_some_and(|path| minidregg_signed_api_path::checked_prefix(path).is_err())
    {
        return Err(invalid("signed API path has no Mini v1 interface mapping"));
    }
    let inspected: Value = serde_json::from_slice(claim_inspection)?;
    if text(&inspected, "type")? != "application-lifecycle-claim-committed-v2"
        || text(&inspected, "frameHex")? != hex(committed_frame)
        || text(&inspected, "frameByteCount")? != committed_frame.len().to_string()
    {
        return Err(invalid("source lifecycle-v2 frame echo differs"));
    }
    let begin = verified_identity(&inspected, &package.raw_sha256_bytes, expected_kind)?;
    let descriptor = inspected
        .get("descriptor")
        .ok_or_else(|| invalid("source descriptor inspection absent"))?;
    let root = text(descriptor, "root")?;
    if !canonical_decimal(root)
        || text(&inspected, "packageDigest")? != root
        || text(descriptor, "canonicalHex")?.is_empty()
        || text(descriptor, "rawSha256Hex")? != hex(&package.raw_sha256_bytes)
        || text(descriptor, "rawLength")? != package.raw_length.to_string()
        || text(descriptor, "signedAppIdHex")? != hex(package.manifest.app_id.0.as_bytes())
        || text(descriptor, "signedAppVersion")? != package.manifest.app_version.to_string()
        || text(descriptor, "manifestSha256Hex")? != hex(&package.signed_manifest_sha256)
        || text(descriptor, "bridgeConfigSha256Hex")?
            != hex(&package
                .signed_bridge_config_sha256
                .ok_or_else(|| invalid("signed bridge hash absent"))?)
        || text(descriptor, "bridgeApiPathHex")?
            != hex(bridge.api_path.as_deref().unwrap_or("").as_bytes())
    {
        return Err(invalid("source claim descriptor differs from signed SPK"));
    }

    let source_schema: Value = serde_json::from_slice(schema_inspection)?;
    let signed_schema = signed_schema_source(&bridge, package.manifest.app_version);
    if text(&source_schema, "type")? != "minidregg-application-permission-schema-v1"
        || text(&source_schema, "canonical")? != hex(schema_bytes)
        || source_schema.get("version") != Some(&json!(package.manifest.app_version.to_string()))
        || source_schema.get("permissions") != signed_schema.get("permissions")
        || source_schema.get("roles") != signed_schema.get("roles")
        || source_schema.get("denied") != signed_schema.get("denied")
    {
        return Err(invalid("source schema differs from signed bridge roles"));
    }
    let schema_root = text(&source_schema, "root")?;
    if !canonical_decimal(schema_root) {
        return Err(invalid("source schema root is noncanonical"));
    }
    let interfaces = descriptor
        .get("interfaces")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid("source descriptor interfaces absent"))?;
    let expected: &[(&str, &str)] = if bridge.api_path.is_some() {
        &[("1", "web"), ("2", "api")]
    } else {
        &[("1", "web")]
    };
    if interfaces.len() != expected.len() {
        return Err(invalid("source descriptor interface count differs"));
    }
    for (entry, (id, kind)) in interfaces.iter().zip(expected) {
        if text(entry, "id")? != *id
            || text(entry, "version")? != "1"
            || text(entry, "kind")? != *kind
            || text(entry, "schemaRoot")? != schema_root
        {
            return Err(invalid(
                "source descriptor interface differs from signed bridge",
            ));
        }
    }
    Ok(MatchedPackage {
        bridge,
        descriptor_root: root.to_owned(),
        begin,
    })
}

pub(crate) fn compare_claim(
    package: &InstalledPackage,
    committed_frame: &[u8],
    claim_inspection: &[u8],
    schema_bytes: &[u8],
    schema_inspection: &[u8],
) -> io::Result<MatchedPackage> {
    compare_claim_kind(
        package,
        committed_frame,
        claim_inspection,
        schema_bytes,
        schema_inspection,
        "start",
    )
}

/// INSTALL uses the same source-owned descriptor and signed bridge equality
/// check, but never arms the START process journal from this identity.
pub(crate) fn compare_install_claim(
    package: &InstalledPackage,
    committed_frame: &[u8],
    claim_inspection: &[u8],
    schema_bytes: &[u8],
    schema_inspection: &[u8],
) -> io::Result<MatchedPackage> {
    compare_claim_kind(
        package,
        committed_frame,
        claim_inspection,
        schema_bytes,
        schema_inspection,
        "install",
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    const GITWEB: &[u8] =
        include_bytes!("../../spk-rpc/tests/fixtures/gitweb-signed-bridge-config.capnp");

    #[test]
    fn signed_gitweb_bridge_projects_exact_ordered_schema_and_api_path() {
        let bridge = decode_bridge_config(GITWEB).unwrap();
        let projected = signed_schema_source(&bridge, 10);
        assert_eq!(projected["version"], "10");
        assert_eq!(
            projected["permissions"],
            json!([
                {"name":"read","obsolete":false},
                {"name":"write","obsolete":false}
            ])
        );
        assert_eq!(
            projected["roles"],
            json!([
                {"permissions":[true,false],"obsolete":false,"default":false},
                {"permissions":[true,true],"obsolete":false,"default":true}
            ])
        );
        assert_eq!(bridge.api_path.as_deref(), Some("/repo.git/"));
    }

    #[test]
    fn start_identity_binds_exact_unit_raw_spk_digest_and_native_decimal_receipt() {
        let sha = [0x5a; 32];
        let unit = "mini-spk-s0123456789abcdef-a8401-g2.service";
        let mut image = IMAGE_ID_PREFIX.to_vec();
        image.extend_from_slice(&sha);
        let source = json!({
            "kind":"start", "app":"8401", "processGeneration":"2", "operationId":"9",
            "processIdentityHex":hex(unit.as_bytes()), "imageIdentityHex":hex(&image),
            "receipt":{"transactionId":"123456", "eventId":"7890"}
        });
        let begin = verified_identity(&source, &sha, "start").unwrap();
        assert_eq!(begin.unit, unit);
        assert_eq!(begin.transaction_id, "123456");
        assert_eq!(begin.package_sha256, hex(&sha));
        let mut wrong_unit = source.clone();
        wrong_unit["processIdentityHex"] = json!(hex(b"mini-spk-s0123456789abcdef-a8401-g3.service"));
        assert!(verified_identity(&wrong_unit, &sha, "start").is_err());
        let mut wrong_digest = source.clone();
        wrong_digest["imageIdentityHex"] = json!(hex(b"sha256:5a"));
        assert!(verified_identity(&wrong_digest, &sha, "start").is_err());
        assert!(verified_identity(&source, &sha, "install").is_err());
    }
}
