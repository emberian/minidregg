//! Concrete ML-KEM-768/XChaCha transit primitives shared by the PQ cascade and
//! independently keyed party capsules. This module supplies no sender authority,
//! key custody, durable receipt, public schedule, padding or anonymity proof.
use aws_lc_rs::kem::{Ciphertext, DecapsulationKey, EncapsulationKey, ML_KEM_768};
use chacha20poly1305::{
    aead::{Aead, Payload},
    KeyInit, XChaCha20Poly1305, XNonce,
};
use ring::hmac;
use sha2::{Digest, Sha256};
use std::{fs::File, io::Read};

pub const KEM_CIPHERTEXT_BYTES: usize = 1088;
pub const NONCE_BYTES: usize = 24;
pub const COMMITMENT_BYTES: usize = 32;
pub const TAG_BYTES: usize = 16;
pub const OVERHEAD_BYTES: usize = KEM_CIPHERTEXT_BYTES + NONCE_BYTES + COMMITMENT_BYTES + TAG_BYTES;
pub const MAX_PLAINTEXT: usize = 262144;
const MAX_LAYER_PLAINTEXT: usize = MAX_PLAINTEXT + 4 * OVERHEAD_BYTES;
const MAX_CONTEXT: usize = 73728;
const RECIPIENT_DOMAIN: &[u8] = b"Mini/independent-recipient-transit/v1";
pub type Result<T> = std::result::Result<T, String>;

pub struct KeyPair {
    pub secret: Vec<u8>,
    pub public: Vec<u8>,
}
pub struct SealedParts {
    pub kem_ciphertext: [u8; KEM_CIPHERTEXT_BYTES],
    pub nonce: [u8; NONCE_BYTES],
    pub commitment: [u8; COMMITMENT_BYTES],
    /// Includes the16-byte AEAD tag. Caller pads plaintext to its public bound.
    pub ciphertext: Vec<u8>,
}
#[derive(Clone, Copy)]
pub struct SealedRef<'a> {
    pub kem_ciphertext: &'a [u8],
    pub nonce: &'a [u8],
    pub commitment: &'a [u8],
    pub ciphertext: &'a [u8],
}
impl SealedParts {
    pub fn as_ref(&self) -> SealedRef<'_> {
        SealedRef {
            kem_ciphertext: &self.kem_ciphertext,
            nonce: &self.nonce,
            commitment: &self.commitment,
            ciphertext: &self.ciphertext,
        }
    }
}
pub fn generate_keypair() -> Result<KeyPair> {
    let key = DecapsulationKey::generate(&ML_KEM_768).map_err(|_| "ML-KEM key generation")?;
    let secret = key
        .key_bytes()
        .map_err(|_| "ML-KEM secret serialization")?
        .as_ref()
        .to_vec();
    let public = key
        .encapsulation_key()
        .map_err(|_| "ML-KEM public derivation")?
        .key_bytes()
        .map_err(|_| "ML-KEM public serialization")?
        .as_ref()
        .to_vec();
    Ok(KeyPair { secret, public })
}
/// AWS-LC1.18.1 explicitly does not reconstruct a public representation from
/// a raw restored private key (kem.rs new/encapsulation_key documentation).
/// Persist BOTH generated serializations in the original pinned custody record.
/// This checks their pairing using real KEM operations; it does not promise full
/// integrity validation of arbitrary untrusted private-key bytes. Provider keys
/// must originate from generate_keypair and honest immutable private custody.
pub fn validate_keypair(secret: &[u8], public: &[u8]) -> Result<()> {
    let secret =
        DecapsulationKey::new(&ML_KEM_768, secret).map_err(|_| "ML-KEM restored secret key")?;
    let public =
        EncapsulationKey::new(&ML_KEM_768, public).map_err(|_| "ML-KEM restored public key")?;
    let (cipher, sent) = public
        .encapsulate()
        .map_err(|_| "ML-KEM pairing encapsulation")?;
    let received = secret
        .decapsulate(Ciphertext::from(cipher.as_ref()))
        .map_err(|_| "ML-KEM pairing decapsulation")?;
    let domain = b"Mini/independent-recipient-keypair/v1";
    let tag = hmac::sign(
        &hmac::Key::new(hmac::HMAC_SHA256, received.as_ref()),
        domain,
    );
    hmac::verify(
        &hmac::Key::new(hmac::HMAC_SHA256, sent.as_ref()),
        domain,
        tag.as_ref(),
    )
    .map_err(|_| "ML-KEM retained public/private pairing refused".into())
}
fn derive(secret: &[u8], aad: &[u8]) -> [u8; 32] {
    hmac::sign(&hmac::Key::new(hmac::HMAC_SHA256, secret), aad)
        .as_ref()
        .try_into()
        .unwrap()
}
fn commitment(key: &[u8], aad: &[u8], cipher: &[u8]) -> [u8; 32] {
    let mut context = aad.to_vec();
    context.extend_from_slice(&Sha256::digest(cipher));
    derive(key, &context)
}
/// Exact existing layer suite. Raw-AAD entrypoints preserve the PQ wire format;
/// party callers should use seal/open with their expected key epoch and binding.
pub fn seal_raw_context(public: &[u8], aad: &[u8], plain: &[u8]) -> Result<SealedParts> {
    if aad.is_empty() || aad.len() > MAX_CONTEXT || plain.len() > MAX_LAYER_PLAINTEXT {
        return Err("transit plaintext/context bound".into());
    }
    let key = EncapsulationKey::new(&ML_KEM_768, public).map_err(|_| "ML-KEM public key")?;
    let (kem, shared) = key.encapsulate().map_err(|_| "ML-KEM encapsulation")?;
    let derived = derive(shared.as_ref(), aad);
    let mut nonce = [0; NONCE_BYTES];
    File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut nonce))
        .map_err(|e| e.to_string())?;
    let ciphertext = XChaCha20Poly1305::new((&derived).into())
        .encrypt(XNonce::from_slice(&nonce), Payload { msg: plain, aad })
        .map_err(|_| "transit AEAD seal")?;
    Ok(SealedParts {
        kem_ciphertext: kem
            .as_ref()
            .try_into()
            .map_err(|_| "ML-KEM ciphertext size")?,
        nonce,
        commitment: commitment(&derived, aad, &ciphertext),
        ciphertext,
    })
}
pub fn open_raw_context(
    key: &DecapsulationKey,
    aad: &[u8],
    part: SealedRef<'_>,
) -> Result<Vec<u8>> {
    if aad.is_empty()
        || aad.len() > MAX_CONTEXT
        || part.kem_ciphertext.len() != KEM_CIPHERTEXT_BYTES
        || part.nonce.len() != NONCE_BYTES
        || part.commitment.len() != COMMITMENT_BYTES
        || part.ciphertext.len() < TAG_BYTES
        || part.ciphertext.len() > MAX_LAYER_PLAINTEXT + TAG_BYTES
    {
        return Err("transit ciphertext/context bound".into());
    }
    let shared = key
        .decapsulate(Ciphertext::from(part.kem_ciphertext))
        .map_err(|_| "ML-KEM decapsulation")?;
    let derived = derive(shared.as_ref(), aad);
    let mut context = aad.to_vec();
    context.extend_from_slice(&Sha256::digest(part.ciphertext));
    hmac::verify(
        &hmac::Key::new(hmac::HMAC_SHA256, &derived),
        &context,
        part.commitment,
    )
    .map_err(|_| "transit key/cipher commitment refused")?;
    XChaCha20Poly1305::new((&derived).into())
        .decrypt(
            XNonce::from_slice(part.nonce),
            Payload {
                msg: part.ciphertext,
                aad,
            },
        )
        .map_err(|_| "transit AEAD authentication refused".into())
}
fn recipient_context(key_epoch: &[u8], binding: &[u8]) -> Result<Vec<u8>> {
    if key_epoch.is_empty() || key_epoch.len() > 4096 || binding.is_empty() || binding.len() > 65536
    {
        return Err("recipient epoch/binding bound".into());
    }
    let mut aad = RECIPIENT_DOMAIN.to_vec();
    for v in [key_epoch, binding] {
        aad.extend_from_slice(&(v.len() as u64).to_le_bytes());
        aad.extend_from_slice(v);
    }
    Ok(aad)
}
/// Caller supplies canonical expected source context, not network claims. Epoch
/// bytes remain exact (including arbitrary Nat encodings); no integer truncation.
pub fn seal(public: &[u8], key_epoch: &[u8], binding: &[u8], plain: &[u8]) -> Result<SealedParts> {
    if plain.len() > MAX_PLAINTEXT {
        return Err("recipient plaintext bound".into());
    }
    seal_raw_context(public, &recipient_context(key_epoch, binding)?, plain)
}
pub fn open(
    secret: &[u8],
    key_epoch: &[u8],
    binding: &[u8],
    part: SealedRef<'_>,
) -> Result<Vec<u8>> {
    if part.ciphertext.len() > MAX_PLAINTEXT + TAG_BYTES {
        return Err("recipient ciphertext bound".into());
    }
    let aad = recipient_context(key_epoch, binding)?;
    let key = DecapsulationKey::new(&ML_KEM_768, secret).map_err(|_| "ML-KEM recipient secret")?;
    open_raw_context(&key, &aad, part)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn independent_recipient_epoch_binding_and_tag_are_enforced() {
        let key = generate_keypair().unwrap();
        validate_keypair(&key.secret, &key.public).unwrap();
        let other = generate_keypair().unwrap();
        assert!(validate_keypair(&key.secret, &other.public).is_err());
        assert!(validate_keypair(&other.secret, &key.public).is_err());
        let mut sealed = seal(
            &key.public,
            b"exact-key-epoch",
            b"canonical-source-binding",
            b"test private share",
        )
        .unwrap();
        assert_eq!(
            open(
                &key.secret,
                b"exact-key-epoch",
                b"canonical-source-binding",
                sealed.as_ref()
            )
            .unwrap(),
            b"test private share"
        );
        assert!(open(
            &other.secret,
            b"exact-key-epoch",
            b"canonical-source-binding",
            sealed.as_ref()
        )
        .is_err());
        assert!(open(
            &key.secret,
            b"different-epoch",
            b"canonical-source-binding",
            sealed.as_ref()
        )
        .is_err());
        assert!(open(
            &key.secret,
            b"exact-key-epoch",
            b"changed-source-binding",
            sealed.as_ref()
        )
        .is_err());
        sealed.nonce[0] ^= 1;
        assert!(open(
            &key.secret,
            b"exact-key-epoch",
            b"canonical-source-binding",
            sealed.as_ref()
        )
        .is_err());
        sealed.nonce[0] ^= 1;
        *sealed.ciphertext.last_mut().unwrap() ^= 1;
        assert!(open(
            &key.secret,
            b"exact-key-epoch",
            b"canonical-source-binding",
            sealed.as_ref()
        )
        .is_err());
    }
    #[test]
    fn fresh_seals_are_distinct_and_public_bounds_fail_closed() {
        let key = generate_keypair().unwrap();
        let a = seal(&key.public, b"epoch", b"binding", &[0; 1024]).unwrap();
        let b = seal(&key.public, b"epoch", b"binding", &[0; 1024]).unwrap();
        assert!(a.kem_ciphertext != b.kem_ciphertext);
        assert!(a.nonce != b.nonce);
        assert_eq!(a.ciphertext.len(), 1024 + TAG_BYTES);
        assert!(seal(&key.public, b"", b"binding", &[0; 1024]).is_err());
        assert!(seal(
            &key.public,
            b"epoch",
            b"binding",
            &vec![0; MAX_PLAINTEXT + 1]
        )
        .is_err());
        let invalid = SealedRef {
            ciphertext: &a.ciphertext[..15],
            ..a.as_ref()
        };
        assert!(open(&key.secret, b"epoch", b"binding", invalid).is_err());
    }
}
