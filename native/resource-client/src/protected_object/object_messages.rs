//! Confidential object records. AEAD protects confidentiality; the signature
//! separately authenticates the writer against other readers. Authority is
//! checked by the source receiving controller, never inferred from a key here.
use crate::Result;
use chacha20poly1305::{
    aead::{Aead, KeyInit, Payload},
    XChaCha20Poly1305, XNonce,
};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use ring::rand::{SecureRandom, SystemRandom};

pub(crate) const MAX_MESSAGE: usize = 1 << 20;
const FRAME: &[u8] = b"MINI/OBJECT-MESSAGE/v1";
/// These are opaque canonical source commitments, not recipient lists.
#[derive(Clone, PartialEq, Eq, Debug)]
pub(crate) struct Context {
    pub object: [u8; 32],
    pub epoch: u64,
    pub transition: [u8; 32],
    pub operation: [u8; 32],
    pub law: [u8; 32],
}
impl Context {
    pub(crate) fn bytes(&self) -> Vec<u8> {
        [
            FRAME,
            &self.object,
            &self.epoch.to_be_bytes(),
            &self.transition,
            &self.operation,
            &self.law,
        ]
        .concat()
    }
}
/// Entire emitted record is retained for exact retry. Never reseal an uncertain operation.
pub(crate) fn seal(
    context: &Context,
    key: &[u8; 32],
    writer: &SigningKey,
    plain: &[u8],
) -> Result<Vec<u8>> {
    if plain.len() > MAX_MESSAGE {
        return Err("object message exceeds limit".into());
    }
    let mut nonce = [0u8; 24];
    SystemRandom::new()
        .fill(&mut nonce)
        .map_err(|_| "randomness unavailable")?;
    let public = writer.verifying_key().to_bytes();
    let header = [context.bytes(), public.to_vec(), nonce.to_vec()].concat();
    let ciphertext = XChaCha20Poly1305::new(key.into())
        .encrypt(
            XNonce::from_slice(&nonce),
            Payload {
                msg: plain,
                aad: &header,
            },
        )
        .map_err(|_| "object encryption failed")?;
    let mut record = [header, ciphertext].concat();
    record.extend_from_slice(&writer.sign(&record).to_bytes());
    Ok(record)
}
pub(crate) fn open(
    context: &Context,
    key: &[u8; 32],
    expected_writer: &[u8; 32],
    record: &[u8],
) -> Result<Vec<u8>> {
    let binding = context.bytes();
    let h = binding.len();
    if record.len() < h + 32 + 24 + 16 + 64 || record.len() > h + 32 + 24 + 16 + 64 + MAX_MESSAGE {
        return Err("invalid object message length".into());
    }
    if record[..h] != binding || record[h..h + 32] != *expected_writer {
        return Err("object message context or writer mismatch".into());
    }
    let end = record.len() - 64;
    let signature =
        Signature::from_slice(&record[end..]).map_err(|_| "invalid writer signature")?;
    VerifyingKey::from_bytes(expected_writer)
        .map_err(|_| "invalid writer key")?
        .verify_strict(&record[..end], &signature)
        .map_err(|_| "writer authentication failed")?;
    XChaCha20Poly1305::new(key.into())
        .decrypt(
            XNonce::from_slice(&record[h + 32..h + 56]),
            Payload {
                msg: &record[h + 56..end],
                aad: &record[..h + 56],
            },
        )
        .map_err(|_| "object decryption failed".into())
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn context_and_reader_forgery_are_rejected() {
        let c = Context {
            object: [1; 32],
            epoch: 3,
            transition: [2; 32],
            operation: [3; 32],
            law: [4; 32],
        };
        let s = SigningKey::from_bytes(&[5; 32]);
        let k = [6; 32];
        let wire = seal(&c, &k, &s, b"hello").unwrap();
        assert_eq!(
            open(&c, &k, &s.verifying_key().to_bytes(), &wire).unwrap(),
            b"hello"
        );
        let mut wrong = c.clone();
        wrong.epoch += 1;
        assert!(open(&wrong, &k, &s.verifying_key().to_bytes(), &wire).is_err());
        let mut tampered = wire;
        let n = tampered.len() - 65;
        tampered[n] ^= 1;
        assert!(open(&c, &k, &s.verifying_key().to_bytes(), &tampered).is_err());
    }
}
