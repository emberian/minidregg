//! Opt-in export custody from one admitted, delivered app request. This is
//! host/TLS provenance; the Mini kernel does not attest the app response bytes.
use crate::{
    dispatch_author::FixedAuthoring, dispatch_inspection::HttpProjection, hostd::DispatchIdentity,
    http_entrance::CustodianPolicy,
};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::io;

pub(crate) const CAPTURE_HEADER: &str = "x-mini-export-capture";
const RECEIPT_HEADER: &str = "X-Mini-Export-Receipt";
fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}
fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Reject an unsupported export request before any Mini or physical call.
pub(crate) fn requested(
    policy: &CustodianPolicy,
    http: &HttpProjection<'_>,
) -> io::Result<Option<String>> {
    let headers: Vec<_> = http
        .ordered_headers
        .iter()
        .filter(|(name, _)| name.eq_ignore_ascii_case(CAPTURE_HEADER))
        .collect();
    if headers.is_empty() && !policy.export_capture {
        return Ok(None);
    }
    if !policy.export_capture
        || (policy.fixed_session_kind == crate::http_entrance::EntranceKind::Api)
            != matches!(http.route, crate::dispatch_inspection::Route::Api { .. })
        || headers.len() != 1
        || http.method != "GET"
        || !http.body.is_empty()
        || http
            .ordered_headers
            .iter()
            .any(|(name, _)| name.eq_ignore_ascii_case("upgrade"))
    {
        return Err(invalid("export capture requires an enabled GET-only route"));
    }
    let (path, query) = crate::dispatch_inspection::app_route_path(http)?;
    if policy.export_capture_path.as_deref() != Some(path.as_str()) || !query.is_empty() {
        return Err(invalid(
            "export capture differs from its fixed sheet CSV route",
        ));
    }
    let id = &headers[0].1;
    if id.len() != 32
        || !id
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(invalid("invalid export capture identity"));
    }
    Ok(Some(id.to_string()))
}

/// Construct BEFORE completing delivery. An error leaves its exact physical
/// request uncertain. The caller emits these prepared bytes only AFTER finish.
pub(crate) fn prepare(
    response: Vec<u8>,
    capture: &str,
    custody: &FixedAuthoring,
    identity: &DispatchIdentity,
    http: &HttpProjection<'_>,
) -> io::Result<Vec<u8>> {
    if custody.app != identity.app.to_string() || custody.session != identity.session_resource {
        return Err(invalid("export custody differs from delivered identity"));
    }
    let end = response
        .windows(4)
        .position(|w| w == b"\r\n\r\n")
        .ok_or_else(|| invalid("export response lacks framing"))?;
    if end > 64 * 1024 || response.len() > 8 * 1024 * 1024 + 64 * 1024 {
        return Err(invalid("export response exceeds bound"));
    }
    let header = std::str::from_utf8(&response[..end])
        .map_err(|_| invalid("export response header is not text"))?;
    if !header.starts_with("HTTP/1.1 200 ") {
        return Err(invalid("export requires a successful representation"));
    }
    if header.lines().any(|line| {
        line.split_once(':')
            .is_some_and(|(name, _)| name.eq_ignore_ascii_case(RECEIPT_HEADER))
    }) {
        return Err(invalid("app response supplied a reserved export receipt"));
    }
    let (path, query) = crate::dispatch_inspection::app_route_path(http)?;
    let signed_api_path = match http.route {
        crate::dispatch_inspection::Route::Api { signed_path } => Some(signed_path),
        crate::dispatch_inspection::Route::Browser => None,
    };
    let body = &response[end + 4..];
    let receipt = json!({"type":"mini-spk-export-custody-v1","capture":capture,
        "app":identity.app.to_string(),"generation":identity.app_generation.to_string(),
        "subject":custody.subject,"session":identity.session_resource,"sessionKind":custody.session_kind,
        "credentialKind":if custody.session_kind == "api" {"bearer"} else {"cookie"},
        "packageManifest":custody.package_manifest,
        "sessionGeneration":identity.session_generation,"ticket":custody.ticket_resource,
        "operation":identity.operation_id,"transaction":identity.dispatch_transaction,
        "event":identity.dispatch_event,"requestDigest":identity.request_digest,
        "permitSha256":identity.permit_sha256,"method":"GET","path":path,"query":query,
        "signedApiPath":signed_api_path,
        "bodySha256":format!("{:x}",Sha256::digest(body)),"bodyBytes":body.len().to_string(),
        "evidence":"host/TLS custody; kernel admits request, not response body"});
    let line = format!(
        "\r\n{RECEIPT_HEADER}: {}",
        hex(&serde_json::to_vec(&receipt)?)
    );
    if end + line.len() > 64 * 1024 {
        return Err(invalid("export receipt exceeds response header bound"));
    }
    let mut out = Vec::with_capacity(response.len() + line.len());
    out.extend_from_slice(&response[..end]);
    out.extend_from_slice(line.as_bytes());
    out.extend_from_slice(&response[end..]);
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn capture_opt_in_confines_browser_and_api_to_exact_csv_get() {
        let mut p = CustodianPolicy {
            expected_host: "app.example".into(),
            fixed_app: "7".into(),
            fixed_subject: "8".into(),
            fixed_session: "9".into(),
            fixed_ticket: "10".into(),
            fixed_session_kind: crate::http_entrance::EntranceKind::Api,
            export_capture: false,
            export_capture_path: Some("_/survey/csv".into()),
            browser_token_sha256: [0; 32],
            bootstrap_token_sha256: [0; 32],
            api_token_sha256: [0; 32],
        };
        let headers = vec![(CAPTURE_HEADER.to_owned(), "a".repeat(32))];
        let mut h = HttpProjection {
            method: "GET",
            path_and_query: "survey/csv",
            ordered_headers: &headers,
            body: &[],
            route: crate::dispatch_inspection::Route::Api { signed_path: "/_/" },
        };
        assert!(requested(&p, &h).is_err());
        p.export_capture = true;
        let another = HttpProjection {
            path_and_query: "other/csv",
            ..h
        };
        assert!(requested(&p, &another).is_err());
        assert_eq!(requested(&p, &h).unwrap(), Some("a".repeat(32)));
        for method in ["HEAD", "POST", "WEBSOCKET"] {
            h.method = method;
            assert!(requested(&p, &h).is_err());
        }
        h.method = "GET";
        h.body = b"x";
        assert!(requested(&p, &h).is_err());
        h.body = &[];
        h.route = crate::dispatch_inspection::Route::Browser;
        assert!(requested(&p, &h).is_err());
        h.route = crate::dispatch_inspection::Route::Api { signed_path: "/_/" };
        let duplicate = vec![headers[0].clone(), headers[0].clone()];
        h.ordered_headers = &duplicate;
        assert!(requested(&p, &h).is_err());
        h.ordered_headers = &headers;
        h.route = crate::dispatch_inspection::Route::Browser;
        h.path_and_query = "_/survey/csv";
        p.fixed_session_kind = crate::http_entrance::EntranceKind::Browser;
        assert_eq!(requested(&p, &h).unwrap(), Some("a".repeat(32)));
        h.path_and_query = "_/survey/csv?format=other";
        assert!(requested(&p, &h).is_err());
        h.path_and_query = "_/survey/csv";
        h.ordered_headers = &[];
        assert!(requested(&p, &h).is_err());
        p.export_capture = false;
        assert_eq!(requested(&p, &h).unwrap(), None);
    }
    #[test]
    fn receipt_cannot_be_supplied_by_app_or_non_success_body() {
        let c = FixedAuthoring {
            protocol: "mini-spk-human-dispatch-custody-v1".into(),
            app: "7".into(),
            subject: "8".into(),
            session: "9".into(),
            session_kind: "api".into(),
            issue_index: "1".into(),
            ticket_resource: "10".into(),
            package_manifest: "11".into(),
            snapshot_manifest: "12".into(),
            session_observe_capability: "13".into(),
            manifest_observe_capability: "14".into(),
            enrollment_observe_capability: "15".into(),
            signers: vec![],
        };
        let i = DispatchIdentity {
            permit_sha256: "a".repeat(64),
            request_digest: "16".into(),
            app: 7,
            app_generation: 3,
            invocation_id: "b".repeat(32),
            operation_id: "17".into(),
            session_resource: "9".into(),
            session_generation: "2".into(),
            dispatch_transaction: "18".into(),
            dispatch_event: "19".into(),
        };
        let h = HttpProjection {
            method: "GET",
            path_and_query: "_/sheet/csv",
            ordered_headers: &[],
            body: &[],
            route: crate::dispatch_inspection::Route::Browser,
        };
        let body = b"HTTP/1.1 200 OK\r\nContent-Length: 3\r\n\r\nabc".to_vec();
        let stamped = prepare(body, "aabbccddeeff00112233445566778899", &c, &i, &h).unwrap();
        assert!(stamped.ends_with(b"\r\n\r\nabc"));
        assert!(prepare(stamped, "aabbccddeeff00112233445566778899", &c, &i, &h).is_err());
        assert!(prepare(
            b"HTTP/1.1 403 Refused\r\n\r\n".to_vec(),
            "aabbccddeeff00112233445566778899",
            &c,
            &i,
            &h
        )
        .is_err());
    }
}
