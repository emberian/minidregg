//! Versioned hybrid key transport, not a ratchet. Static recipient keys do not
//! provide forward secrecy against later recipient compromise or PQ PCS.
//!
//! A device key is the shared `hybrid_kem` pair (X25519 + ML-KEM-768); the wrap's
//! key-encryption key comes from that module's one combiner, under the suite
//! below. This file keeps no combiner of its own.
use crate::hybrid_kem::{self, HybridPublic, HybridSecret, CIPHERTEXT_LEN};
use crate::{object_messages::Context, Result};
use chacha20poly1305::{
    aead::{Aead, KeyInit, Payload},
    XChaCha20Poly1305, XNonce,
};
use serde_json::Value;
use zeroize::Zeroizing;

const FRAME: &[u8] = b"MINI/OBJECT-KEYS.WRAP/v2";
const SUITE: &[u8] = b"DREGG.OBJECT-KEYS.KEK/x25519+ml-kem-768/v2";
const NONCE: usize = 24;
const BOX: usize = 32 + 16;
/// `hybrid ciphertext (1120) || nonce (24) || box (48)`.
pub(crate) const WRAP_LEN: usize = CIPHERTEXT_LEN + NONCE + BOX;
const COMMITMENT_LABEL: &[u8] = b"MINI/OBJECT-DEVICE/v2";

pub(crate) fn generate() -> Result<(HybridSecret, HybridPublic)> {
    let secret = HybridSecret::generate()?;
    let public = secret.public().clone();
    Ok((secret, public))
}

/// A device record or custody row in the pre-hybrid shape (separate ML-KEM and
/// X25519 halves) is refused by name, never reinterpreted.
pub(crate) fn refuse_pre_hybrid(row: &Value) -> Result<()> {
    for field in ["kemPublic", "dhPublic", "kemSecret", "dhSecret"] {
        if row.get(field).is_some() {
            return Err(format!("device record field {field} is the pre-hybrid kem/dh split and is refused: a device key is one hybridPublic / hybridSecret (X25519 + ML-KEM-768)"));
        }
    }
    Ok(())
}

/// The one public-key field of a device record, strict.
pub(crate) fn public_from_record(row: &Value) -> Result<HybridPublic> {
    refuse_pre_hybrid(row)?;
    let text = row["hybridPublic"].as_str().ok_or("missing hybridPublic")?;
    HybridPublic::from_bytes(&crate::decode_hex(text)?)
}

/// Retained device custody, strict.
pub(crate) fn secret_from_record(row: &Value) -> Result<HybridSecret> {
    refuse_pre_hybrid(row)?;
    let text = row["hybridSecret"].as_str().ok_or("missing hybridSecret")?;
    HybridSecret::from_bytes(&Zeroizing::new(crate::decode_hex(text)?))
}

fn parts<'a>(context: &'a [u8], device_generation: &'a [u8; 32]) -> [&'a [u8]; 2] {
    [context, device_generation]
}

/// Caller authenticates recipient device generation and signs the complete
/// manifest (including these bytes). AEAD alone does not authenticate sender.
pub(crate) fn wrap(
    context: &Context,
    device_generation: &[u8; 32],
    recipient: &HybridPublic,
    key: &[u8; 32],
) -> Result<Vec<u8>> {
    let context = context.bytes();
    let sent = hybrid_kem::encapsulate(SUITE, FRAME, &parts(&context, device_generation), recipient)?;
    let nonce = hybrid_kem::random::<NONCE>()?;
    let boxed = XChaCha20Poly1305::new((&*sent.kek).into())
        .encrypt(XNonce::from_slice(&nonce), Payload { msg: key, aad: &sent.transcript })
        .map_err(|_| "wrap encryption failed")?;
    // The recipient public key is bound in the transcript, not repeated on the wire.
    Ok([&sent.ciphertext[..], &nonce, &boxed].concat())
}

pub(crate) fn unwrap(
    context: &Context,
    device_generation: &[u8; 32],
    secret: &HybridSecret,
    recipient: &HybridPublic,
    wire: &[u8],
) -> Result<Zeroizing<[u8; 32]>> {
    if wire.len() != WRAP_LEN {
        return Err(format!("invalid hybrid wrap length {}: a v2 wrap is {WRAP_LEN} bytes", wire.len()));
    }
    if !secret.matches(recipient) {
        return Err("device secret does not belong to the recipient public key".into());
    }
    let context = context.bytes();
    let (kek, transcript) = hybrid_kem::decapsulate(
        SUITE,
        FRAME,
        &parts(&context, device_generation),
        secret,
        &wire[..CIPHERTEXT_LEN],
    )?;
    let nonce = &wire[CIPHERTEXT_LEN..CIPHERTEXT_LEN + NONCE];
    let plain = Zeroizing::new(
        XChaCha20Poly1305::new((&*kek).into())
            .decrypt(
                XNonce::from_slice(nonce),
                Payload { msg: &wire[CIPHERTEXT_LEN + NONCE..], aad: &transcript },
            )
            .map_err(|_| "hybrid wrap authentication failed")?,
    );
    Ok(Zeroizing::new(
        plain.as_slice().try_into().map_err(|_| "invalid epoch key length")?,
    ))
}

/// Canonical actual-device-key commitment used by the source roster/catalog:
/// SHA-256 over the label and the 1216-byte hybrid public key, whose length is
/// fixed, so no ambiguity or lossy reduction is introduced. This hashes the
/// ACTUAL wrap destination bytes, never a caller-supplied label.
pub(crate) fn key_commitment(public: &HybridPublic) -> [u8; 32] {
    use sha2::{Digest, Sha256};
    let mut h = Sha256::new();
    h.update(COMMITMENT_LABEL);
    h.update(public.to_bytes());
    h.finalize().into()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn context() -> Context {
        Context { object: [1; 32], epoch: 1, transition: [2; 32], operation: [3; 32], law: [4; 32] }
    }

    #[test]
    fn roundtrip_and_generation_binding() {
        let (s, p) = generate().unwrap();
        let c = context();
        let w = wrap(&c, &[5; 32], &p, &[6; 32]).unwrap();
        assert_eq!(w.len(), WRAP_LEN);
        assert_eq!(*unwrap(&c, &[5; 32], &s, &p, &w).unwrap(), [6; 32]);
        assert!(unwrap(&c, &[7; 32], &s, &p, &w).is_err());
        let mut other = c.clone();
        other.epoch = 2;
        assert!(unwrap(&other, &[5; 32], &s, &p, &w).is_err(), "context is bound");
        for at in [0, 31, 32, 1119, 1120, 1143, WRAP_LEN - 1] {
            let mut bad = w.clone();
            bad[at] ^= 1;
            assert!(unwrap(&c, &[5; 32], &s, &p, &bad).is_err(), "wrap byte {at}");
        }
        let (stranger, _) = generate().unwrap();
        assert!(unwrap(&c, &[5; 32], &stranger, &p, &w).is_err());
    }

    #[test]
    fn the_wrap_goes_through_the_shared_combiner() {
        // The KEK of a wrap is hybrid_kem's: decapsulating the wire's hybrid
        // ciphertext under the module's suite and transcript opens its box.
        let (s, p) = generate().unwrap();
        let c = context();
        let w = wrap(&c, &[5; 32], &p, &[6; 32]).unwrap();
        let bytes = c.bytes();
        let (kek, transcript) =
            hybrid_kem::decapsulate(SUITE, FRAME, &[&bytes, &[5; 32]], &s, &w[..CIPHERTEXT_LEN]).unwrap();
        let plain = XChaCha20Poly1305::new((&*kek).into())
            .decrypt(
                XNonce::from_slice(&w[CIPHERTEXT_LEN..CIPHERTEXT_LEN + NONCE]),
                Payload { msg: &w[CIPHERTEXT_LEN + NONCE..], aad: &transcript },
            )
            .unwrap();
        assert_eq!(plain, [6; 32]);
    }

    #[test]
    fn the_commitment_is_over_the_whole_hybrid_key_and_names_v2() {
        let (_, a) = generate().unwrap();
        let (_, b) = generate().unwrap();
        assert_ne!(key_commitment(&a), key_commitment(&b));
        let mut halved = a.to_bytes();
        halved[0] ^= 1;
        assert_ne!(key_commitment(&a), key_commitment(&HybridPublic::from_bytes(&halved).unwrap()));
        let mut tail = a.to_bytes();
        tail[1215] ^= 1;
        assert_ne!(key_commitment(&a), key_commitment(&HybridPublic::from_bytes(&tail).unwrap()));
    }

    #[test]
    fn pre_hybrid_device_shapes_are_refused_by_name() {
        let (s, p) = generate().unwrap();
        let public = crate::hex(&p.to_bytes());
        assert_eq!(public_from_record(&json!({"hybridPublic": public})).unwrap(), p);
        let old = json!({"kemPublic": crate::hex(&p.to_bytes()[32..]), "dhPublic": crate::hex(&p.to_bytes()[..32])});
        assert!(public_from_record(&old).unwrap_err().contains("pre-hybrid"));
        let mixed = json!({"hybridPublic": public, "dhPublic": crate::hex(&[0; 32])});
        assert!(public_from_record(&mixed).unwrap_err().contains("pre-hybrid"));
        assert!(public_from_record(&json!({"hybridPublic": crate::hex(&p.to_bytes()[32..])})).unwrap_err().contains("pre-hybrid"));
        let secret = crate::hex(&s.to_bytes());
        assert!(secret_from_record(&json!({"hybridSecret": secret})).unwrap().matches(&p));
        let old = json!({"kemSecret": crate::hex(&[7; 2400]), "dhSecret": crate::hex(&[8; 32])});
        assert!(secret_from_record(&old).err().unwrap().contains("pre-hybrid"));
        assert!(secret_from_record(&json!({"hybridSecret": crate::hex(&[7; 2400])})).err().unwrap().contains("pre-hybrid"));
    }
}
