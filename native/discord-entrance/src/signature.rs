//! Discord's request signature: Ed25519 by the application's key over
//! `X-Signature-Timestamp || raw body`, hex in `X-Signature-Ed25519`.
//!
//! `verify_strict` rejects non-canonical and small-order encodings. A timestamp further than
//! [`MAX_SKEW_S`] from now is refused, so a captured request cannot be replayed later; replay
//! inside the window is caught by the interaction-id memory in [`crate::server`].

use ed25519_dalek::{Signature, VerifyingKey};

pub const MAX_SKEW_S: u64 = 300;

#[derive(Debug, PartialEq, Eq)]
pub enum SigError {
    Missing,
    Malformed,
    Stale,
    Invalid,
}

impl SigError {
    pub fn as_str(&self) -> &'static str {
        match self {
            SigError::Missing => "missing signature headers",
            SigError::Malformed => "malformed signature headers",
            SigError::Stale => "signature timestamp outside the accepted window",
            SigError::Invalid => "invalid request signature",
        }
    }
}

pub struct Verifier {
    key: VerifyingKey,
}

impl Verifier {
    pub fn from_hex(public_key_hex: &str) -> Result<Self, String> {
        let bytes: [u8; 32] = hex_decode(public_key_hex.trim())
            .and_then(|b| b.try_into().ok())
            .ok_or("the public key must be 64 hex characters")?;
        let key = VerifyingKey::from_bytes(&bytes).map_err(|e| format!("public key: {e}"))?;
        Ok(Verifier { key })
    }

    pub fn verify(
        &self,
        signature_hex: Option<&str>,
        timestamp: Option<&str>,
        body: &[u8],
        now: u64,
    ) -> Result<(), SigError> {
        let (sig, ts) = match (signature_hex, timestamp) {
            (Some(s), Some(t)) => (s, t),
            _ => return Err(SigError::Missing),
        };
        let sig: [u8; 64] = hex_decode(sig)
            .and_then(|b| b.try_into().ok())
            .ok_or(SigError::Malformed)?;
        if ts.is_empty() || !ts.bytes().all(|b| b.is_ascii_digit()) || ts.len() > 12 {
            return Err(SigError::Malformed);
        }
        let mut message = Vec::with_capacity(ts.len() + body.len());
        message.extend_from_slice(ts.as_bytes());
        message.extend_from_slice(body);
        self.key
            .verify_strict(&message, &Signature::from_bytes(&sig))
            .map_err(|_| SigError::Invalid)?;
        // Checked after the signature, so an unsigned request is always "invalid".
        let t: u64 = ts.parse().map_err(|_| SigError::Malformed)?;
        if t.abs_diff(now) > MAX_SKEW_S {
            return Err(SigError::Stale);
        }
        Ok(())
    }
}

pub fn hex_decode(s: &str) -> Option<Vec<u8>> {
    if !s.len().is_multiple_of(2) {
        return None;
    }
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(s.get(i..i + 2)?, 16).ok())
        .collect()
}

pub fn hex_encode(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::{Signer, SigningKey};

    fn key() -> SigningKey {
        SigningKey::from_bytes(&[7u8; 32])
    }

    fn sign(k: &SigningKey, ts: &str, body: &[u8]) -> String {
        let mut m = ts.as_bytes().to_vec();
        m.extend_from_slice(body);
        hex_encode(&k.sign(&m).to_bytes())
    }

    #[test]
    fn accepts_a_valid_signature_and_refuses_every_variation() {
        let k = key();
        let v = Verifier::from_hex(&hex_encode(k.verifying_key().as_bytes())).unwrap();
        let body = br#"{"type":1}"#;
        let sig = sign(&k, "1000", body);
        assert_eq!(v.verify(Some(&sig), Some("1000"), body, 1000), Ok(()));
        // a different body, a different timestamp, another key
        assert_eq!(v.verify(Some(&sig), Some("1000"), br#"{"type":2}"#, 1000), Err(SigError::Invalid));
        assert_eq!(v.verify(Some(&sig), Some("1001"), body, 1000), Err(SigError::Invalid));
        let other = sign(&SigningKey::from_bytes(&[8u8; 32]), "1000", body);
        assert_eq!(v.verify(Some(&other), Some("1000"), body, 1000), Err(SigError::Invalid));
        // one flipped bit
        let mut flipped = hex_decode(&sig).unwrap();
        flipped[10] ^= 1;
        assert_eq!(v.verify(Some(&hex_encode(&flipped)), Some("1000"), body, 1000), Err(SigError::Invalid));
        // shape
        assert_eq!(v.verify(None, Some("1000"), body, 1000), Err(SigError::Missing));
        assert_eq!(v.verify(Some(&sig), None, body, 1000), Err(SigError::Missing));
        assert_eq!(v.verify(Some("zz"), Some("1000"), body, 1000), Err(SigError::Malformed));
        assert_eq!(v.verify(Some(&sig), Some("-1000"), body, 1000), Err(SigError::Malformed));
        // a valid signature outside the window
        assert_eq!(v.verify(Some(&sig), Some("1000"), body, 1000 + MAX_SKEW_S + 1), Err(SigError::Stale));
        assert_eq!(v.verify(Some(&sig), Some("1000"), body, 1000 + MAX_SKEW_S), Ok(()));
    }

    #[test]
    fn refuses_a_malformed_public_key() {
        assert!(Verifier::from_hex("00").is_err());
        assert!(Verifier::from_hex(&"g".repeat(64)).is_err());
    }
}
