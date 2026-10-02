//! Versioned hybrid key transport, not a ratchet. Static recipient keys do not
//! provide forward secrecy against later recipient compromise or PQ PCS.
use crate::{object_messages::Context, Result};
use aws_lc_rs::kem::{Ciphertext, DecapsulationKey, EncapsulationKey, ML_KEM_768};
use chacha20poly1305::{
    aead::{Aead, KeyInit, Payload},
    XChaCha20Poly1305, XNonce,
};
use ring::{
    hkdf,
    rand::{SecureRandom, SystemRandom},
};
use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::Zeroizing;
const FRAME: &[u8] = b"MINI/MLKEM768-X25519-XCHACHA/v1";
pub(crate) struct DeviceSecret {
    pub(crate) kem: Zeroizing<Vec<u8>>,
    pub(crate) dh: Zeroizing<[u8; 32]>,
}
pub(crate) struct DevicePublic {
    pub(crate) kem: Vec<u8>,
    pub(crate) dh: [u8; 32],
}
pub(crate) fn generate() -> Result<(DeviceSecret, DevicePublic)> {
    let dk = DecapsulationKey::generate(&ML_KEM_768).map_err(|_| "ML-KEM generation failed")?;
    let ek = dk
        .encapsulation_key()
        .map_err(|_| "ML-KEM public extraction failed")?;
    let retained_secret = Zeroizing::new(
        dk.key_bytes()
            .map_err(|_| "ML-KEM secret extraction failed")?
            .as_ref()
            .to_vec(),
    );
    let mut seed = Zeroizing::new([0; 32]);
    SystemRandom::new()
        .fill(&mut *seed)
        .map_err(|_| "randomness unavailable")?;
    let dh = StaticSecret::from(*seed);
    let public = PublicKey::from(&dh).to_bytes();
    Ok((
        DeviceSecret {
            kem: retained_secret,
            dh: seed,
        },
        DevicePublic {
            kem: ek
                .key_bytes()
                .map_err(|_| "ML-KEM public extraction failed")?
                .as_ref()
                .to_vec(),
            dh: public,
        },
    ))
}
struct Length;
impl hkdf::KeyType for Length {
    fn len(&self) -> usize {
        32
    }
}
fn combine(pq: &[u8], dh: &[u8; 32], header: &[u8]) -> Result<Zeroizing<[u8; 32]>> {
    let ikm = Zeroizing::new([pq, dh].concat());
    let prk = hkdf::Salt::new(hkdf::HKDF_SHA256, FRAME).extract(&ikm);
    let info = [header];
    let okm = prk.expand(&info, Length).map_err(|_| "hybrid KDF failed")?;
    let mut key = Zeroizing::new([0; 32]);
    okm.fill(&mut *key).map_err(|_| "hybrid KDF failed")?;
    Ok(key)
}
fn ek(bytes: &[u8]) -> Result<EncapsulationKey> {
    // Import validates length; AWS-LC performs FIPS203 modulus validation during
    // encapsulation. An imported object alone is not a key-validity certificate.
    EncapsulationKey::new(&ML_KEM_768, bytes).map_err(|_| "invalid ML-KEM public key".into())
}
/// Caller authenticates recipient device generation and signs the complete
/// manifest (including these bytes). AEAD alone does not authenticate sender.
pub(crate) fn wrap(
    context: &Context,
    device_generation: &[u8; 32],
    recipient: &DevicePublic,
    key: &[u8; 32],
) -> Result<Vec<u8>> {
    let (ct, pq) = ek(&recipient.kem)?
        .encapsulate()
        .map_err(|_| "ML-KEM encapsulation failed")?;
    let mut seed = Zeroizing::new([0; 32]);
    SystemRandom::new()
        .fill(&mut *seed)
        .map_err(|_| "randomness unavailable")?;
    let ephemeral = StaticSecret::from(*seed);
    let public = PublicKey::from(&ephemeral);
    let dh = ephemeral.diffie_hellman(&PublicKey::from(recipient.dh));
    if !dh.was_contributory() {
        return Err("noncontributory X25519 recipient".into());
    }
    let mut nonce = [0; 24];
    SystemRandom::new()
        .fill(&mut nonce)
        .map_err(|_| "randomness unavailable")?;
    let header = [
        FRAME,
        &context.bytes(),
        device_generation,
        recipient.kem.as_slice(),
        &recipient.dh,
        ct.as_ref(),
        public.as_bytes(),
        &nonce,
    ]
    .concat();
    let kek = combine(pq.as_ref(), dh.as_bytes(), &header)?;
    let encrypted = XChaCha20Poly1305::new((&*kek).into())
        .encrypt(
            XNonce::from_slice(&nonce),
            Payload {
                msg: key,
                aad: &header,
            },
        )
        .map_err(|_| "wrap encryption failed")?;
    // Recipient public key is implicit in canonical header, not repeated on wire.
    Ok([
        ct.as_ref().to_vec(),
        public.as_bytes().to_vec(),
        nonce.to_vec(),
        encrypted,
    ]
    .concat())
}
pub(crate) fn unwrap(
    context: &Context,
    device_generation: &[u8; 32],
    secret: &DeviceSecret,
    recipient: &DevicePublic,
    wire: &[u8],
) -> Result<Zeroizing<[u8; 32]>> {
    if wire.len() != 1088 + 32 + 24 + 48 {
        return Err("invalid hybrid wrap length".into());
    }
    // Import is for previously generated, authenticated encrypted custody;
    // size validation alone does not establish DK integrity. Decapsulation
    // checks the FIPS203 embedded-public-key hash and rejects invalid keys.
    let dk =
        DecapsulationKey::new(&ML_KEM_768, &secret.kem).map_err(|_| "invalid ML-KEM secret key")?;
    let pq = dk
        .decapsulate(Ciphertext::from(&wire[..1088]))
        .map_err(|_| "ML-KEM decapsulation failed")?;
    let ephemeral: [u8; 32] = wire[1088..1120].try_into().unwrap();
    let dh = StaticSecret::from(*secret.dh).diffie_hellman(&PublicKey::from(ephemeral));
    if !dh.was_contributory() {
        return Err("noncontributory X25519 ephemeral".into());
    }
    let nonce = &wire[1120..1144];
    let header = [
        FRAME,
        &context.bytes(),
        device_generation,
        recipient.kem.as_slice(),
        &recipient.dh,
        &wire[..1088],
        &ephemeral,
        nonce,
    ]
    .concat();
    let kek = combine(pq.as_ref(), dh.as_bytes(), &header)?;
    let plain = Zeroizing::new(
        XChaCha20Poly1305::new((&*kek).into())
            .decrypt(
                XNonce::from_slice(nonce),
                Payload {
                    msg: &wire[1144..],
                    aad: &header,
                },
            )
            .map_err(|_| "hybrid wrap authentication failed")?,
    );
    Ok(Zeroizing::new(
        plain
            .as_slice()
            .try_into()
            .map_err(|_| "invalid epoch key length")?,
    ))
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn roundtrip_and_generation_binding() {
        let (s, p) = generate().unwrap();
        let c = Context {
            object: [1; 32],
            epoch: 1,
            transition: [2; 32],
            operation: [3; 32],
            law: [4; 32],
        };
        let w = wrap(&c, &[5; 32], &p, &[6; 32]).unwrap();
        assert_eq!(*unwrap(&c, &[5; 32], &s, &p, &w).unwrap(), [6; 32]);
        assert!(unwrap(&c, &[7; 32], &s, &p, &w).is_err());
    }
}

/// Canonical actual-device-key commitment used by the source roster/catalog.
/// Both key lengths are fixed; no ambiguity or lossy reduction is introduced.
/// This hashes the ACTUAL wrap destination bytes, never a caller-supplied label.
pub(crate) fn key_commitment(public: &DevicePublic) -> Result<[u8; 32]> {
    use sha2::{Digest, Sha256};
    if public.kem.len() != 1184 {
        return Err("ML-KEM-768 public key must be exactly 1184 bytes".into());
    }
    let mut h = Sha256::new();
    h.update(b"MINI/OBJECT-DEVICE/v1");
    h.update(&public.kem);
    h.update(public.dh);
    Ok(h.finalize().into())
}
