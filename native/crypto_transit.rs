//! Hybrid X25519 + ML-KEM-768 / XChaCha transit primitives (suite v2), shared by
//! the PQ cascade and independently keyed party capsules. The key exchange is
//! `hybrid_kem` (the same combiner private rooms use): a layer or capsule is
//! sealed to a recipient's PAIR of public keys and opens only for a holder of
//! both secrets. There is no pure-ML-KEM path: the v1 suite (a bare 1184-byte
//! encapsulation key, a 1088-byte KEM ciphertext, a 2400-byte secret) is refused
//! by name. This module supplies no sender authority, key custody, durable
//! receipt, public schedule, padding or anonymity proof.
use crate::hybrid_kem::{self, HybridPublic, HybridSecret, CIPHERTEXT_LEN, KEM_CT_LEN};
use chacha20poly1305::{
    aead::{Aead, Payload},
    KeyInit, XChaCha20Poly1305, XNonce,
};
use ring::hmac;
use sha2::{Digest, Sha256};
use std::{fs::File, io::Read};

/// The hybrid ciphertext: ephemeral X25519 key (32) || ML-KEM-768 ciphertext (1088).
pub const HYBRID_CIPHERTEXT_BYTES: usize = CIPHERTEXT_LEN;
pub const NONCE_BYTES: usize = 24;
pub const COMMITMENT_BYTES: usize = 32;
pub const TAG_BYTES: usize = 16;
pub const OVERHEAD_BYTES: usize =
    HYBRID_CIPHERTEXT_BYTES + NONCE_BYTES + COMMITMENT_BYTES + TAG_BYTES;
pub const MAX_PLAINTEXT: usize = 262144;
const MAX_LAYER_PLAINTEXT: usize = MAX_PLAINTEXT + 4 * OVERHEAD_BYTES;
const MAX_CONTEXT: usize = 73728;
const RECIPIENT_DOMAIN: &[u8] = b"Mini/independent-recipient-transit/v2";
/// The versioned frame every transit encapsulation is bound to (a transcript part).
pub const FRAME: &[u8] = b"DREGG/HYBRID-TRANSIT/v2";
/// The combiner's customization string: it names this consumer and the suite.
pub const SUITE: &[u8] = b"DREGG.TRANSIT.KEK/x25519+ml-kem-768/v2";
const AEAD_LABEL: &[u8] = b"DREGG.TRANSIT.AEAD-KEY/v2";
const COMMIT_LABEL: &[u8] = b"DREGG.TRANSIT.COMMIT-KEY/v2";
/// The pre-hybrid suite's sizes, kept only to refuse them by name.
const V1_KEM_CIPHERTEXT_BYTES: usize = KEM_CT_LEN;
pub type Result<T> = std::result::Result<T, String>;

pub struct KeyPair {
    /// `X25519 secret (32) || FIPS 203 seed (64)`.
    pub secret: Vec<u8>,
    /// `X25519 public key (32) || ML-KEM-768 encapsulation key (1184)`.
    pub public: Vec<u8>,
}
pub struct SealedParts {
    pub hybrid_ciphertext: [u8; HYBRID_CIPHERTEXT_BYTES],
    pub nonce: [u8; NONCE_BYTES],
    pub commitment: [u8; COMMITMENT_BYTES],
    /// Includes the16-byte AEAD tag. Caller pads plaintext to its public bound.
    pub ciphertext: Vec<u8>,
}
#[derive(Clone, Copy)]
pub struct SealedRef<'a> {
    pub hybrid_ciphertext: &'a [u8],
    pub nonce: &'a [u8],
    pub commitment: &'a [u8],
    pub ciphertext: &'a [u8],
}
impl SealedParts {
    pub fn as_ref(&self) -> SealedRef<'_> {
        SealedRef {
            hybrid_ciphertext: &self.hybrid_ciphertext,
            nonce: &self.nonce,
            commitment: &self.commitment,
            ciphertext: &self.ciphertext,
        }
    }
}
pub fn generate_keypair() -> Result<KeyPair> {
    let key = HybridSecret::generate()?;
    Ok(KeyPair {
        secret: key.to_bytes().to_vec(),
        public: key.public().to_bytes(),
    })
}
/// The secret is a seed, so the public key is recomputed from it and compared:
/// a retained pair is valid exactly when the secret regenerates that public key
/// (the pre-hybrid check had to run a real KEM round trip because a restored
/// ML-KEM `dk` cannot export its public key).
pub fn validate_keypair(secret: &[u8], public: &[u8]) -> Result<()> {
    let secret = HybridSecret::from_bytes(secret)?;
    let public = HybridPublic::from_bytes(public)?;
    if secret.matches(&public) {
        Ok(())
    } else {
        Err("hybrid retained public/private pairing refused".into())
    }
}
/// The AEAD key and the key-commitment key are separate subkeys of the KEK.
fn subkeys(kek: &[u8; 32]) -> ([u8; 32], [u8; 32]) {
    (
        hybrid_kem::cshake(AEAD_LABEL, &[kek]),
        hybrid_kem::cshake(COMMIT_LABEL, &[kek]),
    )
}
fn commitment(commit_key: &[u8; 32], transcript: &[u8], cipher: &[u8]) -> [u8; 32] {
    let mut context = transcript.to_vec();
    context.extend_from_slice(&Sha256::digest(cipher));
    hmac::sign(&hmac::Key::new(hmac::HMAC_SHA256, commit_key), &context)
        .as_ref()
        .try_into()
        .unwrap()
}
/// Exact existing layer suite. Raw-AAD entrypoints preserve the layer wire
/// shape; party callers should use seal/open with their expected key epoch and
/// binding. `aad` is a transcript part: the combiner binds it with both
/// ciphertext components and both recipient keys.
pub fn seal_raw_context(public: &[u8], aad: &[u8], plain: &[u8]) -> Result<SealedParts> {
    if aad.is_empty() || aad.len() > MAX_CONTEXT || plain.len() > MAX_LAYER_PLAINTEXT {
        return Err("transit plaintext/context bound".into());
    }
    let recipient = HybridPublic::from_bytes(public)?;
    let sealed = hybrid_kem::encapsulate(SUITE, FRAME, &[aad], &recipient)?;
    let (aead_key, commit_key) = subkeys(&sealed.kek);
    let mut nonce = [0; NONCE_BYTES];
    File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut nonce))
        .map_err(|e| e.to_string())?;
    let ciphertext = XChaCha20Poly1305::new((&aead_key).into())
        .encrypt(
            XNonce::from_slice(&nonce),
            Payload { msg: plain, aad: &sealed.transcript },
        )
        .map_err(|_| "transit AEAD seal")?;
    Ok(SealedParts {
        hybrid_ciphertext: sealed.ciphertext,
        nonce,
        commitment: commitment(&commit_key, &sealed.transcript, &ciphertext),
        ciphertext,
    })
}
pub fn open_raw_context(key: &HybridSecret, aad: &[u8], part: SealedRef<'_>) -> Result<Vec<u8>> {
    if part.hybrid_ciphertext.len() == V1_KEM_CIPHERTEXT_BYTES {
        return Err(format!(
            "transit ciphertext is a v1 pure ML-KEM-768 capsule ({V1_KEM_CIPHERTEXT_BYTES}-byte KEM ciphertext, no X25519 component): refused; the suite is hybrid X25519 + ML-KEM-768 v2 ({HYBRID_CIPHERTEXT_BYTES}-byte ciphertext)"
        ));
    }
    if aad.is_empty()
        || aad.len() > MAX_CONTEXT
        || part.hybrid_ciphertext.len() != HYBRID_CIPHERTEXT_BYTES
        || part.nonce.len() != NONCE_BYTES
        || part.commitment.len() != COMMITMENT_BYTES
        || part.ciphertext.len() < TAG_BYTES
        || part.ciphertext.len() > MAX_LAYER_PLAINTEXT + TAG_BYTES
    {
        return Err("transit ciphertext/context bound".into());
    }
    let (kek, transcript) =
        hybrid_kem::decapsulate(SUITE, FRAME, &[aad], key, part.hybrid_ciphertext)?;
    let (aead_key, commit_key) = subkeys(&kek);
    let mut context = transcript.clone();
    context.extend_from_slice(&Sha256::digest(part.ciphertext));
    hmac::verify(
        &hmac::Key::new(hmac::HMAC_SHA256, &commit_key),
        &context,
        part.commitment,
    )
    .map_err(|_| "transit key/cipher commitment refused")?;
    XChaCha20Poly1305::new((&aead_key).into())
        .decrypt(
            XNonce::from_slice(part.nonce),
            Payload {
                msg: part.ciphertext,
                aad: &transcript,
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
    let key = HybridSecret::from_bytes(secret)?;
    open_raw_context(&key, &aad, part)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hybrid_kem::{KEM_EK_LEN, KEM_SEED_LEN};

    fn open_with(key: &[u8], sealed: &SealedParts) -> Result<Vec<u8>> {
        open(key, b"exact-key-epoch", b"canonical-source-binding", sealed.as_ref())
    }
    fn seal_to(key: &KeyPair) -> SealedParts {
        seal(
            &key.public,
            b"exact-key-epoch",
            b"canonical-source-binding",
            b"test private share",
        )
        .unwrap()
    }

    #[test]
    fn independent_recipient_epoch_binding_and_tag_are_enforced() {
        let key = generate_keypair().unwrap();
        validate_keypair(&key.secret, &key.public).unwrap();
        let other = generate_keypair().unwrap();
        assert!(validate_keypair(&key.secret, &other.public).is_err());
        assert!(validate_keypair(&other.secret, &key.public).is_err());
        let mut sealed = seal_to(&key);
        assert_eq!(open_with(&key.secret, &sealed).unwrap(), b"test private share");
        assert!(open_with(&other.secret, &sealed).is_err());
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
        assert!(open_with(&key.secret, &sealed).is_err());
        sealed.nonce[0] ^= 1;
        *sealed.ciphertext.last_mut().unwrap() ^= 1;
        assert!(open_with(&key.secret, &sealed).is_err());
    }
    #[test]
    fn fresh_seals_are_distinct_and_public_bounds_fail_closed() {
        let key = generate_keypair().unwrap();
        let a = seal(&key.public, b"epoch", b"binding", &[0; 1024]).unwrap();
        let b = seal(&key.public, b"epoch", b"binding", &[0; 1024]).unwrap();
        assert!(a.hybrid_ciphertext != b.hybrid_ciphertext);
        assert!(a.hybrid_ciphertext[..32] != b.hybrid_ciphertext[..32], "fresh ephemeral X25519 key");
        assert!(a.hybrid_ciphertext[32..] != b.hybrid_ciphertext[32..], "fresh ML-KEM encapsulation");
        assert!(a.nonce != b.nonce);
        assert_eq!(a.ciphertext.len(), 1024 + TAG_BYTES);
        assert_eq!(OVERHEAD_BYTES, 1120 + 24 + 32 + 16);
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

    #[test]
    fn tampering_either_ciphertext_component_or_the_box_refuses() {
        let key = generate_keypair().unwrap();
        let sealed = seal_to(&key);
        assert!(open_with(&key.secret, &sealed).is_ok());
        let flips: [(&str, usize); 6] = [
            ("ephemeral X25519 first byte", 0),
            ("ephemeral X25519 last byte", 31),
            ("ML-KEM first byte", 32),
            ("ML-KEM middle byte", 32 + KEM_CT_LEN / 2),
            ("ML-KEM last byte", HYBRID_CIPHERTEXT_BYTES - 1),
            ("ML-KEM second byte", 33),
        ];
        for (what, at) in flips {
            let mut t = SealedParts {
                hybrid_ciphertext: sealed.hybrid_ciphertext,
                nonce: sealed.nonce,
                commitment: sealed.commitment,
                ciphertext: sealed.ciphertext.clone(),
            };
            t.hybrid_ciphertext[at] ^= 1;
            assert!(open_with(&key.secret, &t).is_err(), "{what} flipped must refuse");
        }
        let mut commitment = SealedParts {
            hybrid_ciphertext: sealed.hybrid_ciphertext,
            nonce: sealed.nonce,
            commitment: sealed.commitment,
            ciphertext: sealed.ciphertext.clone(),
        };
        commitment.commitment[0] ^= 1;
        assert!(open_with(&key.secret, &commitment).unwrap_err().contains("commitment"));
    }

    #[test]
    fn a_capsule_needs_both_halves_of_the_recipient_secret() {
        let key = generate_keypair().unwrap();
        let other = generate_keypair().unwrap();
        let sealed = seal_to(&key);
        let (kx, kseed) = (&key.secret[..32], &key.secret[32..]);
        let (ox, oseed) = (&other.secret[..32], &other.secret[32..]);
        assert_eq!(kseed.len(), KEM_SEED_LEN);
        // Right X25519 half, wrong ML-KEM half; and the reverse: neither opens it.
        assert!(open_with(&[kx, oseed].concat(), &sealed).is_err());
        assert!(open_with(&[ox, kseed].concat(), &sealed).is_err());
        assert!(open_with(&[kx, kseed].concat(), &sealed).is_ok());
    }

    #[test]
    fn a_capsule_sealed_to_a_spliced_public_key_opens_for_nobody_else() {
        // X25519 half of A with the ML-KEM half of B names a third identity.
        let a = generate_keypair().unwrap();
        let b = generate_keypair().unwrap();
        let spliced = [&a.public[..32], &b.public[32..]].concat();
        let sealed = seal(&spliced, b"exact-key-epoch", b"canonical-source-binding", b"x").unwrap();
        assert!(open_with(&a.secret, &sealed).is_err());
        assert!(open_with(&b.secret, &sealed).is_err());
        assert!(open_with(&[&a.secret[..32], &b.secret[32..]].concat(), &sealed).is_ok());
    }

    #[test]
    fn the_v1_pure_ml_kem_suite_refuses_by_name() {
        let key = generate_keypair().unwrap();
        // A bare 1184-byte ML-KEM encapsulation key is not a recipient.
        let bare = &key.public[32..];
        assert_eq!(bare.len(), KEM_EK_LEN);
        assert!(seal(bare, b"epoch", b"binding", b"x").err().unwrap().contains("pre-hybrid"));
        // A bare 2400-byte ML-KEM secret is not a key.
        assert!(HybridSecret::from_bytes(&[0u8; 2400]).err().unwrap().contains("pre-hybrid"));
        assert!(validate_keypair(&[0u8; 2400], bare).is_err());
        // A v1 capsule: 1088-byte KEM ciphertext, no X25519 component.
        let sealed = seal_to(&key);
        let v1 = SealedRef {
            hybrid_ciphertext: &sealed.hybrid_ciphertext[32..],
            ..sealed.as_ref()
        };
        let refusal = open(&key.secret, b"exact-key-epoch", b"canonical-source-binding", v1)
            .unwrap_err();
        assert!(refusal.contains("v1 pure ML-KEM-768"), "{refusal}");
    }

    /// The combiner's known answer for this consumer, reusing the rooms' input
    /// vector (shared secrets 0x11 x32 and 0x22 x32, ephemeral 0x33 x32, KEM
    /// ciphertext 0x44 x1088, X25519 key 0x55 x32, ML-KEM key 0x66 x1184) under
    /// this suite and frame, and context "kat-context". Expected values were
    /// computed by an independent cSHAKE256 (Python, pycryptodome, not the
    /// `sha3` crate): the transcript's SHA-256, then
    /// KEK = cSHAKE256(S = SUITE, X = u64be(len)||bytes of [ss_x25519, ss_mlkem, transcript]).
    #[test]
    fn the_transit_combiner_matches_an_independent_known_answer() {
        let recipient = HybridPublic::from_raw_unchecked([0x55; 32], [0x66; KEM_EK_LEN]);
        let transcript =
            hybrid_kem::transcript(FRAME, &[b"kat-context"], &[0x33; 32], &[0x44; KEM_CT_LEN], &recipient);
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        assert_eq!(
            hex(&Sha256::digest(&transcript)),
            "f331ca4fcb6b081c22080269429cb751abdb86a2ce3098270b58d61c3e8fd54d"
        );
        let kek = hybrid_kem::combine(SUITE, &[0x11; 32], &[0x22; 32], &transcript);
        assert_eq!(
            hex(&kek[..]),
            "3f7b6f0e0059e59da8fe534bf9d0ae684cba401477e80d139ffcad0639dde2da"
        );
    }
}
