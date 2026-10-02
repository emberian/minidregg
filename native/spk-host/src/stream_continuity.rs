//! Physical continuity receiving boundary. Only the pinned private operator
//! pipeline can supply PrivateContinuityReply. Source inspection owns semantic
//! interpretation; this module checks exact local challenge and stream binding.
use crate::dispatch_native::PrivateContinuityReply;
use crate::web_socket::RenewalChallenge;
use serde::Deserialize;
use std::cmp::Ordering;
use std::io;

fn invalid() -> io::Error {
    io::Error::new(
        io::ErrorKind::PermissionDenied,
        "stream continuity response refused",
    )
}
fn decimal(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 4096
        && s.bytes().all(|b| b.is_ascii_digit())
        && (s.len() == 1 || !s.starts_with('0'))
}
pub(crate) fn digest(s: &str) -> io::Result<[u8; 32]> {
    if !decimal(s) {
        return Err(invalid());
    }
    let mut bytes = [0u8; 32];
    for digit in s.bytes() {
        let mut carry = u16::from(digit - b'0');
        for byte in &mut bytes {
            let next = u16::from(*byte) * 10 + carry;
            *byte = next as u8;
            carry = next >> 8;
        }
        if carry != 0 {
            return Err(invalid());
        }
    }
    Ok(bytes)
}
pub(crate) fn exact_hex(s: &str, bytes: &[u8]) -> bool {
    s.len() == bytes.len() * 2
        && s.as_bytes().chunks_exact(2).zip(bytes).all(|(pair, byte)| {
            let digit = |v: u8| if v < 10 { b'0' + v } else { b'a' + v - 10 };
            pair == [digit(byte >> 4), digit(byte & 15)]
        })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ContinuityBinding {
    pub domain: String,
    pub semantics: String,
    pub app: String,
    pub app_generation: String,
    pub session: String,
    pub session_generation: String,
    pub subject: String,
    pub ticket_resource: String,
    pub session_fingerprint: [u8; 32],
}
impl ContinuityBinding {
    pub(crate) fn validate(&self) -> io::Result<()> {
        if [
            &self.domain,
            &self.semantics,
            &self.app,
            &self.app_generation,
            &self.session,
            &self.session_generation,
            &self.subject,
            &self.ticket_resource,
        ]
        .iter()
        .all(|s| decimal(s))
        {
            Ok(())
        } else {
            Err(invalid())
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ContinuityTip {
    pub height: String,
    pub chain: Option<String>,
    pub world_root: String,
}
impl ContinuityTip {
    pub(crate) fn validate(&self) -> io::Result<()> {
        if decimal(&self.height)
            && decimal(&self.world_root)
            && self.chain.as_ref().is_none_or(|c| decimal(c))
        {
            Ok(())
        } else {
            Err(invalid())
        }
    }
    pub(crate) fn follows(&self, minimum: &Self) -> io::Result<()> {
        self.validate()?;
        minimum.validate()?;
        match self
            .height
            .len()
            .cmp(&minimum.height.len())
            .then_with(|| self.height.cmp(&minimum.height))
        {
            Ordering::Less => Err(invalid()),
            Ordering::Equal
                if self.world_root != minimum.world_root
                    || minimum
                        .chain
                        .as_ref()
                        .is_some_and(|c| self.chain.as_ref() != Some(c)) =>
            {
                Err(invalid())
            }
            _ => Ok(()),
        }
    }
}

/// Fields are private; caller JSON cannot construct this typed authority result.
pub(crate) struct VerifiedContinuity {
    challenge: RenewalChallenge,
    tip: ContinuityTip,
}
impl VerifiedContinuity {
    pub(crate) fn into_parts(self) -> (RenewalChallenge, ContinuityTip) {
        (self.challenge, self.tip)
    }
    #[cfg(test)]
    pub(crate) fn fixture(challenge: RenewalChallenge, tip: ContinuityTip) -> Self {
        Self { challenge, tip }
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
    stream_nonce_hex: String,
    attempt_nonce_hex: String,
    app: String,
    app_generation: String,
    session: String,
    session_generation: String,
    subject: String,
    ticket_resource: String,
    session_fingerprint: String,
    tip: TipInspection,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct TipInspection {
    height: String,
    chain: String,
    world_root: String,
}

/// Never call this with HTTP input or a standalone inspector document. The
/// private wrapper is minted only after pinned op152 IO and source inspection.
pub(crate) fn verify_reply(
    challenge: RenewalChallenge,
    reply: &PrivateContinuityReply,
) -> io::Result<VerifiedContinuity> {
    verify_bytes(
        challenge,
        reply.payload(),
        reply.challenge(),
        reply.inspection(),
    )
}
fn verify_bytes(
    challenge: RenewalChallenge,
    payload: &[u8],
    challenge_bytes: &[u8],
    inspection: &[u8],
) -> io::Result<VerifiedContinuity> {
    challenge.check()?;
    if payload.is_empty() || challenge_bytes.is_empty() || inspection.len() > 4 * 1024 * 1024 {
        return Err(invalid());
    }
    let parsed: Inspection = serde_json::from_slice(inspection).map_err(|_| invalid())?;
    if parsed.kind != "application-stream-continuity-inspection-v1"
        || !exact_hex(&parsed.frame_hex, payload)
        || !exact_hex(&parsed.challenge_hex, challenge_bytes)
        || parsed.stream_nonce_hex != challenge.stream_nonce_hex()
        || parsed.attempt_nonce_hex != challenge.attempt_nonce_hex()
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
        session_fingerprint: digest(&parsed.session_fingerprint)?,
    };
    binding.validate()?;
    if &binding != challenge.binding() {
        return Err(invalid());
    }
    let tip = ContinuityTip {
        height: parsed.tip.height,
        chain: Some(parsed.tip.chain),
        world_root: parsed.tip.world_root,
    };
    tip.follows(challenge.minimum_tip())?;
    challenge.check()?;
    Ok(VerifiedContinuity { challenge, tip })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::web_socket::StreamLease;
    use serde_json::{json, Value};
    use std::time::Duration;

    pub(crate) fn binding() -> ContinuityBinding {
        ContinuityBinding {
            domain: "1".into(),
            semantics: "2".into(),
            app: "91".into(),
            app_generation: "2".into(),
            session: "6208".into(),
            session_generation: "1".into(),
            subject: "8".into(),
            ticket_resource: "6000".into(),
            session_fingerprint: [0; 32],
        }
    }
    pub(crate) fn tip() -> ContinuityTip {
        ContinuityTip {
            height: "10".into(),
            chain: None,
            world_root: "42".into(),
        }
    }
    fn lease() -> StreamLease {
        let lease = StreamLease::begin(Duration::from_secs(10)).unwrap();
        lease.bind_continuity(binding(), tip()).unwrap();
        lease
    }
    fn document(c: &RenewalChallenge) -> Value {
        json!({"type":"application-stream-continuity-inspection-v1", "frameHex":"abcd", "challengeHex":"1234",
            "domain":"1", "semantics":"2", "streamNonceHex":c.stream_nonce_hex(), "attemptNonceHex":c.attempt_nonce_hex(),
            "app":"91", "appGeneration":"2", "session":"6208", "sessionGeneration":"1", "subject":"8",
            "ticketResource":"6000", "sessionFingerprint":"0", "tip":{"height":"10", "chain":"99", "worldRoot":"42"}})
    }
    fn verify(c: RenewalChallenge, v: Value) -> io::Result<VerifiedContinuity> {
        verify_bytes(
            c,
            &[0xab, 0xcd],
            &[0x12, 0x34],
            &serde_json::to_vec(&v).unwrap(),
        )
    }
    #[test]
    fn private_inspection_requires_every_exact_identity_and_nonce() {
        for field in [
            "type",
            "frameHex",
            "challengeHex",
            "domain",
            "semantics",
            "streamNonceHex",
            "attemptNonceHex",
            "app",
            "appGeneration",
            "session",
            "sessionGeneration",
            "subject",
            "ticketResource",
            "sessionFingerprint",
        ] {
            let l = lease();
            let c = l.begin_renewal().unwrap();
            let mut v = document(&c);
            v[field] = json!("wrong");
            assert!(verify(c, v).is_err(), "{field}");
        }
        let l = lease();
        let c = l.begin_renewal().unwrap();
        let mut v = document(&c);
        v["subject"] = json!("9");
        assert!(verify(c, v).is_err());
        let c = l.begin_renewal().unwrap();
        let mut v = document(&c);
        v["extra"] = json!(true);
        assert!(verify(c, v).is_err());
        let c = l.begin_renewal().unwrap();
        let v = document(&c);
        assert!(verify(c, v).is_ok());
    }
    #[test]
    fn continuity_tip_cannot_rollback_or_fork_known_height() {
        let min = ContinuityTip {
            height: "10".into(),
            chain: Some("99".into()),
            world_root: "42".into(),
        };
        for candidate in [
            ContinuityTip {
                height: "9".into(),
                ..min.clone()
            },
            ContinuityTip {
                world_root: "43".into(),
                ..min.clone()
            },
            ContinuityTip {
                chain: Some("98".into()),
                ..min.clone()
            },
            ContinuityTip {
                chain: None,
                ..min.clone()
            },
            ContinuityTip {
                height: "010".into(),
                ..min.clone()
            },
        ] {
            assert!(candidate.follows(&min).is_err());
        }
        assert!(min.follows(&tip()).is_ok());
        assert!(ContinuityTip {
            height: "11".into(),
            chain: Some("100".into()),
            world_root: "77".into()
        }
        .follows(&min)
        .is_ok());
    }
    #[test]
    fn old_response_and_different_stream_cannot_renew() {
        let a = lease();
        let b = lease();
        let old = a.begin_renewal().unwrap();
        let old_doc = document(&old);
        let current = a.begin_renewal().unwrap();
        assert!(verify(old, old_doc.clone()).is_err());
        assert!(verify(current, old_doc).is_err());
        let c = a.begin_renewal().unwrap();
        let v = document(&c);
        let grant = verify(c, v).unwrap();
        assert!(b.renew(grant).is_err());
        let c = a.begin_renewal().unwrap();
        let v = document(&c);
        let grant = verify(c, v).unwrap();
        a.revoke();
        assert!(a.renew(grant).is_err());
    }
    #[test]
    fn stale_duplicate_fields_and_noncanonical_digest_refuse() {
        let l = lease();
        let c = l.begin_renewal().unwrap();
        let mut s = serde_json::to_string(&document(&c)).unwrap();
        s.insert_str(1, "\"subject\":\"8\",");
        assert!(verify_bytes(c, &[0xab, 0xcd], &[0x12, 0x34], s.as_bytes()).is_err());
        assert!(digest("00").is_err());
        assert!(digest(&"9".repeat(79)).is_err());
    }
}
