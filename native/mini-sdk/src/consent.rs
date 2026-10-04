//! Client of the local consent process (`minidregg-client-consent`, `Host/ClientConsentCore`).
//!
//! The plan check is Lean (`NativeClientConsent`, `NativeSpecializedConsent`); this module only
//! frames requests to it, so there is exactly one check. Operations (READ
//! `Host/ClientConsentCore.lean` `serve`/`consent`/`specialized`):
//! 220 intent, 221 observation, 222 plan, 224 operator (specialized) plan, 226 possession,
//! 227 Objective (W1.2 owns its Objective half; not wrapped here until it lands).
use std::path::Path;

use ed25519_dalek::VerifyingKey;
use serde_json::Value;

use crate::frame::{pair, Process};
use crate::sign::ConsentedIntent;
use crate::{Error, Result};

pub struct Consent(Process);

/// The opcodes whose operator replies the transport checks against consent before any
/// signing consumer sees them (`client_consent.rs::plan_operation`, 29 opcodes).
pub const OPERATOR_PLAN_OPS: &[u8] = &[32, 36, 44, 48, 50, 52, 58, 66, 68, 70, 74, 78, 80, 82, 86, 92, 96, 103, 108,
    113, 117, 123, 126, 140, 160, 170, 183, 201, 206];

fn headers(bytes: &[u8]) -> Result<Vec<Vec<u8>>> {
    let v: Value = serde_json::from_slice(bytes).map_err(|e| format!("consent headers: {e}"))?;
    v.as_array()
        .ok_or("consent headers are not a list")?
        .iter()
        .map(|h| crate::hex::decode(h.as_str().ok_or("consent header is not hex")?))
        .collect()
}

impl Consent {
    /// Start the consent executable selected by LOCAL custody (never by the operator).
    pub fn start(executable: &Path, settings: &Path) -> Result<Self> {
        Process::start(executable, settings).map(Consent)
    }

    /// Op 220: this key is the intent subject's current signing key at the verified frontier.
    pub fn intent(&mut self, intent_bin: &[u8], key: &VerifyingKey) -> Result<ConsentedIntent> {
        let reply = self.0.call(220, &pair(intent_bin, &pair(key.as_bytes(), &[])?)?)?;
        ConsentedIntent::from_consent_reply(intent_bin, reply)
    }

    /// Op 221: the headers of the operator's challenge that this intent permits this key to sign.
    pub fn observation(&mut self, intent_bin: &[u8], key: &VerifyingKey, intent_signature: &[u8; 64],
        challenge_bin: &[u8]) -> Result<Vec<Vec<u8>>> {
        let payload = pair(intent_bin, &pair(key.as_bytes(), &pair(intent_signature, challenge_bin)?)?)?;
        headers(&self.0.call(221, &payload)?)
    }

    /// Op 222: the headers of the operator's plan that this intent permits this key to sign.
    pub fn plan(&mut self, intent_bin: &[u8], key: &VerifyingKey, plan_bin: &[u8]) -> Result<Vec<Vec<u8>>> {
        headers(&self.0.call(222, &pair(intent_bin, &pair(key.as_bytes(), plan_bin)?)?)?)
    }

    /// Op 224: the operator's reply to a specialized plan request equals the plan the Lean
    /// planner reconstructs; a refusal never falls back to the offered plan.
    pub fn operator_plan(&mut self, operation: u8, request: &[u8], candidate: &[u8]) -> Result<()> {
        if !OPERATOR_PLAN_OPS.contains(&operation) {
            return Err(Error(format!("operation {operation} is not a checked operator plan")));
        }
        let retained = [vec![operation], request.to_vec()].concat();
        let expected = self.0.call(224, &pair(&retained, candidate)?)?;
        if expected != candidate {
            return Err("local specialized consent returned a different plan".into());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frame::fake;

    #[test]
    fn headers_preserve_order_and_duplicates_and_reject_unframed() {
        assert_eq!(headers(br#"["aabb","ff","aabb"]"#).unwrap(), vec![vec![170, 187], vec![255], vec![170, 187]]);
        for bad in [br#"{"headers":["aabb"]}"#.as_slice(), br#"[true]"#, br#"["zz"]"#] {
            assert!(headers(bad).is_err());
        }
    }

    #[test]
    fn a_consent_that_echoes_other_intent_bytes_refuses() {
        // Answers op 220 with the 3 bytes "abd" whatever was asked.
        let (exe, settings) = fake::script("echo", "exec 3<&0; cat <&3 >/dev/null & printf '\\004\\000\\000\\000\\334abd'");
        let mut c = Consent::start(&exe, &settings).unwrap();
        let key = ed25519_dalek::SigningKey::from_bytes(&[1; 32]).verifying_key();
        let err = c.intent(b"abc", &key).unwrap_err();
        assert!(err.0.contains("different retained intent"), "{err}");
    }

    #[test]
    fn unchecked_operator_opcodes_refuse_before_any_frame() {
        let (exe, settings) = fake::script("noop", "exec 3<&0; cat <&3 >/dev/null");
        let mut c = Consent::start(&exe, &settings).unwrap();
        assert!(c.operator_plan(1, b"", b"").is_err());
        assert_eq!(OPERATOR_PLAN_OPS.len(), 29);
    }
}
