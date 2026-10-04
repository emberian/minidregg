//! Signing. A key signs exactly the bytes the consent process returned, and the transaction
//! headers only under a matching [`Confirmation`]. Signatures are over the raw bytes, as
//! `resource-client`'s `sign_headers` and intent signing do; domain separation lives in the
//! Lean header encoding (`DREGG/AUTH/SIGNED-REQUEST`, `DREGG/AUTH/PLAN`). The key is any
//! [`Signer`] (Ed25519 or the Ed25519 + ML-DSA-65 hybrid); a signature is that scheme's
//! fixed-width byte string.
use crate::confirm::{Confirmation, Presented};
use crate::signer::Signer;
use crate::{Error, Result};

/// Consent op 220 returned these intent bytes unchanged for this key: the subject's current
/// signing key is this key. Constructed only from a consent reply.
#[derive(Debug, Clone)]
pub struct ConsentedIntent(Vec<u8>);
impl ConsentedIntent {
    /// `retained` is what the client sent; `reply` is the consent process's answer.
    pub fn from_consent_reply(retained: &[u8], reply: Vec<u8>) -> Result<Self> {
        if reply != retained {
            return Err("local consent returned a different retained intent".into());
        }
        Ok(ConsentedIntent(reply))
    }
    pub fn bytes(&self) -> &[u8] {
        &self.0
    }
}

pub fn sign_intent(key: &dyn Signer, intent: &ConsentedIntent) -> Result<Vec<u8>> {
    key.sign(&intent.0)
}

/// Observation headers (consent op 221). An observation authorizes a read, never a mutation
/// (SHARED-CONTRACTS); it is consent-gated, not confirmation-gated.
pub fn sign_observation_headers(key: &dyn Signer, consented: &[Vec<u8>]) -> Result<Vec<Vec<u8>>> {
    consented.iter().map(|h| key.sign(h)).collect()
}

/// Transaction headers: only under the member's confirmation of this exact presentation.
pub fn sign_transaction(key: &dyn Signer, presented: &Presented, confirmation: &Confirmation) -> Result<Vec<Vec<u8>>> {
    confirmation.check(presented)?;
    if presented.headers.is_empty() {
        return Err(Error("no consented headers".into()));
    }
    presented.headers.iter().map(|h| key.sign(h)).collect()
}

/// The JSON list the Host's `signatures` codec (op 9) reads.
pub fn signatures_json(signatures: &[Vec<u8>]) -> String {
    let list: Vec<String> = signatures.iter().map(|s| crate::hex::encode(s)).collect();
    serde_json::to_string(&list).unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::contracts::InvocationId;
    use crate::signer::{verify, Ed25519Signer, HybridSigner, Scheme};
    use ed25519_dalek::SigningKey;
    use serde_json::json;

    fn presented() -> Presented {
        let intent: serde_json::Value = serde_json::from_str(include_str!("../tests/fixtures/intent.json")).unwrap();
        let plan: serde_json::Value = serde_json::from_str(include_str!("../tests/fixtures/plan.json")).unwrap();
        Presented::new(InvocationId([7; 32]), 1, &intent, b"intent".to_vec(), &plan, b"plan".to_vec(),
            vec![b"h1".to_vec(), b"h2".to_vec()]).unwrap()
    }

    #[test]
    fn signatures_need_the_confirmation_of_this_exact_presentation() {
        let key = Ed25519Signer(SigningKey::from_bytes(&[9; 32]));
        let p = presented();
        let c = p.confirm([5; 16]).unwrap();
        let sigs = sign_transaction(&key, &p, &c).unwrap();
        assert_eq!(sigs.len(), 2);
        // A different attempt, plan byte, header, reading or nonce refuses.
        let mut q = p.clone();
        q.attempt = 2;
        assert!(sign_transaction(&key, &q, &c).is_err());
        let mut q = p.clone();
        q.plan_bin[0] ^= 1;
        assert!(sign_transaction(&key, &q, &c).is_err());
        let mut q = p.clone();
        q.headers[1] = b"h3".to_vec();
        assert!(sign_transaction(&key, &q, &c).is_err());
        let mut q = p.clone();
        q.explanation.text.push('x');
        assert!(sign_transaction(&key, &q, &c).is_err());
        let forged = Confirmation { nonce: [6; 16], ..c };
        assert!(sign_transaction(&key, &p, &forged).is_err());
    }

    #[test]
    fn intent_signing_requires_the_unchanged_consent_reply() {
        assert!(ConsentedIntent::from_consent_reply(b"abc", b"abd".to_vec()).is_err());
        let ok = ConsentedIntent::from_consent_reply(b"abc", b"abc".to_vec()).unwrap();
        let key = Ed25519Signer(SigningKey::from_bytes(&[9; 32]));
        assert_eq!(sign_intent(&key, &ok).unwrap(), key.sign(b"abc").unwrap());
        assert_eq!(signatures_json(&[vec![0; 64]]), json!(["00".repeat(64)]).to_string());
    }

    #[test]
    fn hybrid_keys_sign_transactions_end_to_end_and_every_header_verifies_under_both_halves() {
        let key = HybridSigner::from_seeds(&[9; 32], &[3; 32]);
        let p = presented();
        let c = p.confirm([5; 16]).unwrap();
        let sigs = sign_transaction(&key, &p, &c).unwrap();
        assert_eq!(sigs.len(), p.headers.len());
        for (header, sig) in p.headers.iter().zip(&sigs) {
            assert_eq!(sig.len(), Scheme::HybridEd25519MlDsa65.signature_len());
            verify(Scheme::HybridEd25519MlDsa65, &key.public_key(), header, sig).unwrap();
        }
        // The confirmation gate is scheme-independent.
        let forged = Confirmation { nonce: [6; 16], ..c };
        assert!(sign_transaction(&key, &p, &forged).is_err());
        let body: Vec<String> = serde_json::from_str(&signatures_json(&sigs)).unwrap();
        assert!(body.iter().all(|h| h.len() == 2 * 3373));
    }
}
