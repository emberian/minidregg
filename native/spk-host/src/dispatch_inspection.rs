//! Compare Mini's read-only op34 inspection to the exact private Host payload
//! and the authenticated, canonical HTTP request. This is not admission:
//! source JSON from a caller cannot replace the captured Host response.
#![allow(dead_code)] // The private signer/op34 invocation is not linked yet.

use serde_json::Value;
use std::io;

const MAX_INSPECTION_BYTES: usize = 96_822_080;
const MAX_PERMIT_BYTES: usize = 12_102_759; // Host frame also has opcode 34.

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn member<'a>(object: &'a Value, field: &str) -> io::Result<&'a Value> {
    object
        .get(field)
        .ok_or_else(|| invalid("Mini inspection field absent"))
}

fn string<'a>(object: &'a Value, field: &str) -> io::Result<&'a str> {
    member(object, field)?
        .as_str()
        .ok_or_else(|| invalid("Mini inspection field is not text"))
}

fn canonical_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn decimal<'a>(object: &'a Value, field: &str) -> io::Result<&'a str> {
    let value = string(object, field)?;
    if !canonical_decimal(value) {
        return Err(invalid("Mini inspection integer is not canonical decimal"));
    }
    Ok(value)
}

fn hex(bytes: &[u8]) -> String {
    let mut result = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        result.push_str(&format!("{byte:02x}"));
    }
    result
}

fn lower_hex(value: &str) -> bool {
    value.len().is_multiple_of(2)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn hex32(value: &str) -> io::Result<[u8; 32]> {
    if value.len() != 64 || !lower_hex(value) {
        return Err(invalid(
            "Mini checked identity is not 32 lowercase-hex bytes",
        ));
    }
    let mut bytes = [0u8; 32];
    for (index, pair) in value.as_bytes().as_chunks::<2>().0.iter().enumerate() {
        let digit = |byte: u8| -> u8 {
            if byte.is_ascii_digit() {
                byte - b'0'
            } else {
                byte - b'a' + 10
            }
        };
        bytes[index] = (digit(pair[0]) << 4) | digit(pair[1]);
    }
    Ok(bytes)
}

/// Mini Digest Nat is projected as decimal; the physical RPC cache uses the
/// same 256-bit value as little-endian bytes. Refuse overflow rather than
/// truncating an arbitrary Nat into a shorter cache key.
fn digest_nat_bytes(value: &str) -> io::Result<[u8; 32]> {
    if !canonical_decimal(value) {
        return Err(invalid("Mini digest is not canonical decimal"));
    }
    let mut bytes = [0u8; 32];
    for digit in value.bytes() {
        let mut carry = (digit - b'0') as u16;
        for byte in &mut bytes {
            let next = u16::from(*byte) * 10 + carry;
            *byte = next as u8;
            carry = next >> 8;
        }
        if carry != 0 {
            return Err(invalid("Mini digest exceeds 256 bits"));
        }
    }
    Ok(bytes)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Route<'a> {
    Browser,
    /// Decoded from the signature-verified bridge config and compared with
    /// Mini's v1 fixed mapping. It is never supplied by HTTP input.
    Api {
        signed_path: &'a str,
    },
}

pub(crate) struct HttpProjection<'a> {
    pub method: &'a str,
    pub path_and_query: &'a str,
    pub ordered_headers: &'a [(String, String)],
    pub body: &'a [u8],
    pub route: Route<'a>,
}

/// Operator-pinned single-participant custody, loaded from the protected
/// custodian config. None of these selectors come from HTTP fields or tokens.
pub(crate) struct FixedCustody<'a> {
    pub app: &'a str,
    pub subject: &'a str,
    pub session: &'a str,
    pub ticket: &'a str,
}

/// Only the source inspector may interpret the committed payload. This
/// struct is an exact matched coordinate for the physical journal and RPC
/// adapter, not an independent authorization proof.
pub(crate) struct MatchedInspection {
    pub app: u64,
    pub app_generation: u64,
    pub session_resource: String,
    pub session_generation: String,
    pub subject: String,
    pub operation_id: String,
    pub physical_request_digest: String,
    pub dispatch_transaction: String,
    pub dispatch_event: String,
    pub session_fingerprint: [u8; 32],
    pub principal: [u8; 32],
    pub before_image_boundary: String,
    pub after_image_boundary: String,
    pub accepted_count: String,
    pub effective_bits: Vec<bool>,
    pub app_path_and_query: String,
    pub method: String,
}

/// Browser targets are already canonical relative paths. API targets are
/// external relative paths, prefixed only by the signature-verified bridge
/// configuration. Authoring and post-CAS comparison share this transformation.
pub(crate) fn app_route_path(http: &HttpProjection<'_>) -> io::Result<(String, String)> {
    if http.path_and_query.starts_with('/')
        || http.path_and_query.contains('#')
        || http
            .path_and_query
            .bytes()
            .filter(|byte| *byte == b'?')
            .count()
            > 1
        || http.path_and_query.len() > 8192
    {
        return Err(invalid(
            "authenticated HTTP path is not canonical relative form",
        ));
    }
    let (path, query) = http
        .path_and_query
        .split_once('?')
        .unwrap_or((http.path_and_query, ""));
    let app_path = match http.route {
        Route::Browser => path.to_owned(),
        Route::Api { signed_path } => {
            if signed_path != "/repo.git/" {
                return Err(invalid(
                    "signed API prefix differs from Mini bridge v1 mapping",
                ));
            }
            format!("repo.git/{path}")
        }
    };
    Ok((app_path, query.to_owned()))
}

/// `committed_payload` must be retained from this host's own fresh op34
/// response. The function checks the inspector's byte echo first, then exact
/// transport request coordinates and human-only v1 origin. It does not accept
/// an op35 historical receipt, a candidate frame, or caller-authored JSON as
/// a substitute for that private provenance.
pub(crate) fn match_inspection(
    committed_payload: &[u8],
    inspection_json: &[u8],
    http: &HttpProjection<'_>,
    custody: &FixedCustody<'_>,
) -> io::Result<MatchedInspection> {
    if committed_payload.is_empty()
        || committed_payload.len() > MAX_PERMIT_BYTES
        || inspection_json.is_empty()
        || inspection_json.len() > MAX_INSPECTION_BYTES
    {
        return Err(invalid("Mini committed inspection size refused"));
    }
    let parsed: Value = serde_json::from_slice(inspection_json)?;
    if string(&parsed, "type")? != "application-dispatch-committed-inspection-v1"
        || decimal(&parsed, "frameByteCount")? != committed_payload.len().to_string()
        || string(&parsed, "frameHex")? != hex(committed_payload)
    {
        return Err(invalid(
            "Mini inspection does not echo exact private op34 payload",
        ));
    }
    let app = member(&parsed, "app")?;
    let session = member(&parsed, "session")?;
    if ![
        custody.app,
        custody.subject,
        custody.session,
        custody.ticket,
    ]
    .iter()
    .all(|value| canonical_decimal(value))
        || decimal(app, "resource")? != custody.app
        || decimal(session, "subject")? != custody.subject
        || decimal(session, "resource")? != custody.session
        || decimal(&parsed, "ticketResource")? != custody.ticket
    {
        return Err(invalid(
            "Mini inspection differs from fixed participant custody",
        ));
    }
    let origin = member(session, "origin")?;
    if string(origin, "type")? != "human" {
        return Err(invalid(
            "agent-origin v1 dispatch lacks checked parent custody",
        ));
    }
    let expected_kind = match http.route {
        Route::Browser => "web",
        Route::Api { .. } => "api",
    };
    if string(session, "kind")? != expected_kind {
        return Err(invalid(
            "Mini session kind differs from authenticated entrance",
        ));
    }
    let request = member(&parsed, "request")?;
    let (app_path, query) = app_route_path(http)?;
    if string(request, "methodHex")? != hex(http.method.as_bytes())
        || string(request, "pathHex")? != hex(app_path.as_bytes())
        || string(request, "queryHex")? != hex(query.as_bytes())
        || string(request, "bodyHex")? != hex(http.body)
    {
        return Err(invalid(
            "Mini committed request differs from authenticated HTTP bytes",
        ));
    }
    let inspected_headers = member(request, "headers")?
        .as_array()
        .ok_or_else(|| invalid("Mini inspection headers are not ordered array"))?;
    if inspected_headers.len() != http.ordered_headers.len() {
        return Err(invalid("Mini committed header count differs from HTTP"));
    }
    for (inspected, (name, value)) in inspected_headers.iter().zip(http.ordered_headers) {
        if member(inspected, "generated")?.as_bool() != Some(false)
            || string(inspected, "nameHex")? != hex(name.as_bytes())
            || string(inspected, "valueHex")? != hex(value.as_bytes())
        {
            return Err(invalid("Mini committed ordered header differs from HTTP"));
        }
    }
    let identity = member(&parsed, "identity")?;
    let principal = hex32(string(identity, "principalHex")?)?;
    let bits = member(&parsed, "effectiveBits")?
        .as_array()
        .ok_or_else(|| invalid("Mini effective bits are not ordered array"))?;
    let effective_bits = bits
        .iter()
        .map(|bit| {
            bit.as_bool()
                .ok_or_else(|| invalid("Mini effective bit is not boolean"))
        })
        .collect::<io::Result<Vec<_>>>()?;
    if effective_bits.len() > 128 {
        return Err(invalid(
            "Mini effective permission bits exceed bridge bound",
        ));
    }
    let app_resource = decimal(app, "resource")?
        .parse::<u64>()
        .map_err(|_| invalid("Mini app ID exceeds physical host range"))?;
    let app_generation = string(app, "generation")?
        .parse::<u64>()
        .map_err(|_| invalid("Mini app generation exceeds physical host range"))?;
    if app_generation == 0 || string(app, "generation")? != app_generation.to_string() {
        return Err(invalid(
            "Mini app generation is not canonical Running generation",
        ));
    }
    let session_generation = string(session, "generation")?
        .parse::<u64>()
        .map_err(|_| invalid("Mini session generation exceeds physical host range"))?;
    if string(session, "generation")? != session_generation.to_string() {
        return Err(invalid("Mini session generation is not canonical"));
    }
    if decimal(session, "appResource")? != app_resource.to_string()
        || string(session, "appGeneration")? != app_generation.to_string()
    {
        return Err(invalid("Mini app/session generation relation differs"));
    }
    let receipt = member(&parsed, "receipt")?;
    if decimal(receipt, "transactionId")? != decimal(&parsed, "dispatchTransaction")?
        || decimal(receipt, "eventId")? != decimal(&parsed, "dispatchEvent")?
    {
        return Err(invalid("Mini committed projection and receipt disagree"));
    }
    Ok(MatchedInspection {
        app: app_resource,
        app_generation,
        session_resource: decimal(session, "resource")?.to_owned(),
        session_generation: session_generation.to_string(),
        subject: decimal(session, "subject")?.to_owned(),
        operation_id: decimal(request, "operationId")?.to_owned(),
        physical_request_digest: decimal(&parsed, "physicalRequestDigest")?.to_owned(),
        dispatch_transaction: decimal(&parsed, "dispatchTransaction")?.to_owned(),
        dispatch_event: decimal(&parsed, "dispatchEvent")?.to_owned(),
        session_fingerprint: digest_nat_bytes(decimal(&parsed, "sessionFingerprint")?)?,
        principal,
        before_image_boundary: decimal(&parsed, "currentImageBoundary")?.to_owned(),
        after_image_boundary: decimal(receipt, "imageBoundary")?.to_owned(),
        accepted_count: decimal(receipt, "acceptedCount")?.to_owned(),
        effective_bits,
        app_path_and_query: if query.is_empty() {
            app_path
        } else {
            format!("{app_path}?{query}")
        },
        method: http.method.to_owned(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn fixture(payload: &[u8]) -> Value {
        json!({
            "type":"application-dispatch-committed-inspection-v1",
            "frameByteCount":payload.len().to_string(),"frameHex":hex(payload),
            "app":{"resource":"6100","generation":"1"},
            "session":{"kind":"api","resource":"6209","appResource":"6100",
                "appGeneration":"1","generation":"0","subject":"9","origin":{"type":"human"}},
            "identity":{"principalHex":"a".repeat(64)},
            "request":{"operationId":"7","methodHex":hex(b"GET"),
                "pathHex":hex(b"repo.git/info/refs"),"queryHex":hex(b"service=git-upload-pack"),
                "bodyHex":"","headers":[{"nameHex":hex(b"accept"),
                    "valueHex":hex(b"application/x-git-upload-pack-advertisement"),"generated":false}]},
            "effectiveBits":[true,false],"ticketResource":"6309","physicalRequestDigest":"123",
            "dispatchTransaction":"456","dispatchEvent":"789","sessionFingerprint":"42",
            "currentImageBoundary":"111",
            "receipt":{"transactionId":"456","eventId":"789","acceptedCount":"12","imageBoundary":"222"}
        })
    }

    #[test]
    fn same_private_payload_and_signed_api_route_match_exact_http() {
        let payload = b"private op34 payload (transport fixture only)";
        let headers = vec![(
            "accept".into(),
            "application/x-git-upload-pack-advertisement".into(),
        )];
        let http = HttpProjection {
            method: "GET",
            path_and_query: "info/refs?service=git-upload-pack",
            ordered_headers: &headers,
            body: b"",
            route: Route::Api {
                signed_path: "/repo.git/",
            },
        };
        let custody = FixedCustody {
            app: "6100",
            subject: "9",
            session: "6209",
            ticket: "6309",
        };
        let inspected = match_inspection(
            payload,
            &serde_json::to_vec(&fixture(payload)).unwrap(),
            &http,
            &custody,
        )
        .unwrap();
        assert_eq!((inspected.app, inspected.app_generation), (6100, 1));
        assert_eq!(inspected.session_resource, "6209");
        assert_eq!(inspected.effective_bits, [true, false]);
        assert_eq!(inspected.session_fingerprint[0], 42);
        assert_eq!(inspected.principal, [0xaa; 32]);
        assert_eq!(inspected.before_image_boundary, "111");
        assert_eq!(inspected.after_image_boundary, "222");
    }

    #[test]
    fn caller_drift_agent_origin_and_wrong_signed_prefix_refuse() {
        let payload = b"private op34 payload (transport fixture only)";
        let headers = vec![(
            "accept".into(),
            "application/x-git-upload-pack-advertisement".into(),
        )];
        let http = HttpProjection {
            method: "GET",
            path_and_query: "info/refs?service=git-upload-pack",
            ordered_headers: &headers,
            body: b"",
            route: Route::Api {
                signed_path: "/repo.git/",
            },
        };
        let custody = FixedCustody {
            app: "6100",
            subject: "9",
            session: "6209",
            ticket: "6309",
        };
        let mut json = fixture(payload);
        json["frameHex"] = Value::String(hex(b"different"));
        assert!(match_inspection(
            payload,
            &serde_json::to_vec(&json).unwrap(),
            &http,
            &custody
        )
        .is_err());
        let mut json = fixture(payload);
        json["session"]["origin"]["type"] = Value::String("agent".into());
        assert!(match_inspection(
            payload,
            &serde_json::to_vec(&json).unwrap(),
            &http,
            &custody
        )
        .is_err());
        let other = HttpProjection {
            route: Route::Api {
                signed_path: "/other/",
            },
            ..http
        };
        assert!(match_inspection(
            payload,
            &serde_json::to_vec(&fixture(payload)).unwrap(),
            &other,
            &custody
        )
        .is_err());
        let mut mismatched_receipt = fixture(payload);
        mismatched_receipt["receipt"]["eventId"] = Value::String("790".into());
        assert!(match_inspection(
            payload,
            &serde_json::to_vec(&mismatched_receipt).unwrap(),
            &http,
            &custody
        )
        .is_err());
        let wrong_custody = FixedCustody {
            subject: "8",
            ..custody
        };
        assert!(match_inspection(
            payload,
            &serde_json::to_vec(&fixture(payload)).unwrap(),
            &http,
            &wrong_custody
        )
        .is_err());
        let wrong_path = HttpProjection {
            path_and_query: "/info/refs?service=git-upload-pack",
            ..http
        };
        assert!(match_inspection(
            payload,
            &serde_json::to_vec(&fixture(payload)).unwrap(),
            &wrong_path,
            &custody
        )
        .is_err());
    }

    #[test]
    fn decimal_digest_is_exact_little_endian_and_refuses_overflow() {
        assert_eq!(digest_nat_bytes("0").unwrap(), [0; 32]);
        assert_eq!(digest_nat_bytes("256").unwrap()[..2], [0, 1]);
        assert_eq!(digest_nat_bytes("42").unwrap()[0], 42);
        assert!(digest_nat_bytes("01").is_err());
        assert!(digest_nat_bytes(
            "115792089237316195423570985008687907853269984665640564039457584007913129639936"
        )
        .is_err());
    }
}
