//! Exact receiving checks for a fresh private source route admission.
//! This type does not grant a dispatch or renew any existing stream lease.
use crate::dispatch_native::PrivateRouteAdmissionReply;
use crate::stream_continuity::{ContinuityBinding, ContinuityTip};
use serde::Deserialize;
use std::io;

fn invalid() -> io::Error {
    io::Error::new(
        io::ErrorKind::PermissionDenied,
        "source route admission refused",
    )
}

#[derive(Clone, Debug)]
pub(crate) struct RouteAdmissionExpectation {
    pub binding: ContinuityBinding,
    pub session_kind: String,
    pub registration_nonce_hex: String,
}
impl RouteAdmissionExpectation {
    pub(crate) fn validate(&self) -> io::Result<()> {
        self.binding.validate()?;
        if !matches!(self.session_kind.as_str(), "web" | "api")
            || self.registration_nonce_hex.len() != 64
            || !self
                .registration_nonce_hex
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(invalid());
        }
        Ok(())
    }
}

/// Only the pinned private native pipeline can construct this result.
#[derive(Clone)]
pub(crate) struct VerifiedRouteAdmission {
    binding: ContinuityBinding,
    tip: ContinuityTip,
    session_kind: String,
    registration_nonce_hex: String,
}
impl VerifiedRouteAdmission {
    pub(crate) fn binding(&self) -> &ContinuityBinding {
        &self.binding
    }
    pub(crate) fn tip(&self) -> &ContinuityTip {
        &self.tip
    }
    pub(crate) fn session_kind(&self) -> &str {
        &self.session_kind
    }
    pub(crate) fn registration_nonce_hex(&self) -> &str {
        &self.registration_nonce_hex
    }
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Inspection {
    #[serde(rename = "type")]
    kind: String,
    frame_hex: String,
    challenge_hex: String,
    domain: String,
    semantics: String,
    registration_nonce_hex: String,
    app: String,
    app_generation: String,
    session: String,
    session_generation: String,
    subject: String,
    ticket_resource: String,
    session_kind: String,
    session_fingerprint: String,
    tip: Tip,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Tip {
    height: String,
    chain: String,
    world_root: String,
}

pub(crate) fn verify_reply(
    expected: &RouteAdmissionExpectation,
    reply: &PrivateRouteAdmissionReply,
) -> io::Result<VerifiedRouteAdmission> {
    verify_bytes(
        expected,
        reply.payload(),
        reply.challenge(),
        reply.inspection(),
    )
}

fn verify_bytes(
    expected: &RouteAdmissionExpectation,
    payload: &[u8],
    challenge: &[u8],
    inspection: &[u8],
) -> io::Result<VerifiedRouteAdmission> {
    expected.validate()?;
    if payload.is_empty() || challenge.is_empty() || inspection.len() > 4 * 1024 * 1024 {
        return Err(invalid());
    }
    let parsed: Inspection = serde_json::from_slice(inspection).map_err(|_| invalid())?;
    if parsed.kind != "application-route-admission-inspection-v1"
        || !crate::stream_continuity::exact_hex(&parsed.frame_hex, payload)
        || !crate::stream_continuity::exact_hex(&parsed.challenge_hex, challenge)
        || parsed.registration_nonce_hex != expected.registration_nonce_hex
        || parsed.session_kind != expected.session_kind
    {
        return Err(invalid());
    }
    let binding = ContinuityBinding {
        domain: parsed.domain,
        semantics: parsed.semantics,
        app: parsed.app,
        app_generation: parsed.app_generation,
        session: parsed.session,
        session_generation: parsed.session_generation,
        subject: parsed.subject,
        ticket_resource: parsed.ticket_resource,
        session_fingerprint: crate::stream_continuity::digest(&parsed.session_fingerprint)?,
    };
    binding.validate()?;
    // The source resolves the fingerprint; all selected identities must match.
    let mut actual_selector = binding.clone();
    actual_selector.session_fingerprint = [0; 32];
    let mut expected_selector = expected.binding.clone();
    expected_selector.session_fingerprint = [0; 32];
    if actual_selector != expected_selector {
        return Err(invalid());
    }
    let tip = ContinuityTip {
        height: parsed.tip.height,
        chain: Some(parsed.tip.chain),
        world_root: parsed.tip.world_root,
    };
    tip.validate()?;
    Ok(VerifiedRouteAdmission {
        binding,
        tip,
        session_kind: parsed.session_kind,
        registration_nonce_hex: parsed.registration_nonce_hex,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{json, Value};
    fn expectation() -> RouteAdmissionExpectation {
        RouteAdmissionExpectation {
            binding: ContinuityBinding {
                domain: "1".into(),
                semantics: "2".into(),
                app: "91".into(),
                app_generation: "4".into(),
                session: "6208".into(),
                session_generation: "3".into(),
                subject: "9".into(),
                ticket_resource: "6000".into(),
                session_fingerprint: [0; 32],
            },
            session_kind: "web".into(),
            registration_nonce_hex: "11".repeat(32),
        }
    }
    fn document(e: &RouteAdmissionExpectation) -> Value {
        json!({"type":"application-route-admission-inspection-v1", "frameHex":"abcd","challengeHex":"1234",
        "domain":"1","semantics":"2","registrationNonceHex":e.registration_nonce_hex,
        "app":"91","appGeneration":"4","session":"6208","sessionGeneration":"3","subject":"9",
        "ticketResource":"6000","sessionKind":"web","sessionFingerprint":"99",
        "tip":{"height":"12","chain":"50","worldRoot":"100"}})
    }
    fn verify(e: &RouteAdmissionExpectation, value: &Value) -> io::Result<VerifiedRouteAdmission> {
        verify_bytes(
            e,
            &[0xab, 0xcd],
            &[0x12, 0x34],
            &serde_json::to_vec(value).unwrap(),
        )
    }
    #[test]
    fn route_response_binds_selector_nonce_and_exact_source_frames() {
        let e = expectation();
        let v = document(&e);
        let admitted = verify(&e, &v).unwrap();
        assert_eq!(admitted.binding().session_fingerprint[0], 99);
        assert_eq!(admitted.tip().height, "12");
        assert_eq!(admitted.session_kind(), "web");
        assert_eq!(admitted.registration_nonce_hex(), e.registration_nonce_hex);
        for (field, replacement) in [
            ("domain", "3"),
            ("semantics", "3"),
            ("app", "92"),
            ("appGeneration", "5"),
            ("session", "6209"),
            ("sessionGeneration", "4"),
            ("subject", "10"),
            ("ticketResource", "6001"),
            ("sessionKind", "api"),
            ("registrationNonceHex", "22"),
            ("frameHex", "ABCD"),
            ("challengeHex", "5678"),
        ] {
            let mut bad = v.clone();
            bad[field] = json!(replacement);
            assert!(verify(&e, &bad).is_err(), "{field}");
        }
    }
    #[test]
    fn malformed_or_ambiguous_route_inspection_is_refused() {
        let e = expectation();
        let v = document(&e);
        let mut bad = v.clone();
        bad["tip"]["height"] = json!("012");
        assert!(verify(&e, &bad).is_err());
        let mut bad = v.clone();
        bad["sessionFingerprint"] = json!(
            "99999999999999999999999999999999999999999999999999999999999999999999999999999999"
        );
        assert!(verify(&e, &bad).is_err());
        let text = serde_json::to_string(&v).unwrap();
        let duplicated = text.replacen("{", "{\"domain\":\"1\",", 1);
        assert!(verify_bytes(&e, &[0xab, 0xcd], &[0x12, 0x34], duplicated.as_bytes()).is_err());
        let mut bad = v.clone();
        bad["unknown"] = json!(1);
        assert!(verify(&e, &bad).is_err());
    }
}
