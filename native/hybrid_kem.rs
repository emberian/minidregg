//! Hybrid X25519 + ML-KEM-768 key encapsulation: the ONE implementation.
//!
//! Every key exchange in `native/` goes through here: private-room wraps and
//! seed escrow (`private.rs`), the traffic-privacy mix's layers, its link
//! enrollment and the independent-recipient capsules (`crypto_transit.rs`),
//! and protected-object device wraps. A sender encapsulates to a recipient's
//! PAIR of public keys with one fresh ephemeral X25519 key and one ML-KEM-768
//! encapsulation, and the resulting key-encryption key is a single cSHAKE256 --
//! under a customization string that names the consumer and the suite -- of
//! BOTH shared secrets and the full transcript (frame, caller context, both
//! ciphertext components, both recipient public keys), each input
//! length-prefixed. The key is unknown to an adversary that breaks only one
//! primitive, and substituting a ciphertext, key or context in either half
//! changes it. There is no pure-X25519 and no pure-ML-KEM path: a recipient is
//! a `HybridPublic` or it is not a recipient.
//!
//! The ML-KEM-768 implementation is AWS-LC (`aws-lc-rs`). Secret keys are
//! SEEDS: `x25519 secret (32) || FIPS 203 seed d||z (64)`, and the 2400-byte
//! `dk` is regenerated from the seed (so the public key is always derivable
//! from the secret, which `aws-lc-rs` alone cannot do for a restored `dk`).
//!
//! This file is `#[path]`-included by every crate that needs it
//! (`mini` resource-client, `mini-private-backend`); it has no crate-local
//! dependencies.
use aws_lc_rs::kem::{Ciphertext, DecapsulationKey, EncapsulationKey, ML_KEM_768};
use sha3::digest::{core_api::CoreWrapper, ExtendableOutput, Update, XofReader};
use sha3::CShake256Core;
use std::{fs::File, io::Read};
use x25519_dalek::{PublicKey, StaticSecret};
use zeroize::{Zeroize, Zeroizing};

/// ML-KEM-768 (FIPS 203) sizes, bytes.
pub const KEM_EK_LEN: usize = 1184;
pub const KEM_CT_LEN: usize = 1088;
const KEM_DK_LEN: usize = 2400;
/// FIPS 203 key-generation seed `d || z`.
pub const KEM_SEED_LEN: usize = 64;
/// A hybrid public key: X25519 (32) then the ML-KEM-768 encapsulation key.
pub const PUBLIC_LEN: usize = 32 + KEM_EK_LEN;
/// A hybrid ciphertext: the ephemeral X25519 public key then the ML-KEM-768 ciphertext.
pub const CIPHERTEXT_LEN: usize = 32 + KEM_CT_LEN;
/// A hybrid secret: the X25519 secret then the FIPS 203 seed.
pub const SECRET_LEN: usize = 32 + KEM_SEED_LEN;
/// The key-encryption key every encapsulation yields.
pub const KEK_LEN: usize = 32;

pub type Result<T> = std::result::Result<T, String>;

pub fn cshake(label: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    cshake_xof::<32>(label, parts)
}

pub fn cshake_xof<const N: usize>(label: &[u8], parts: &[&[u8]]) -> [u8; N] {
    let mut hasher = CoreWrapper::from_core(CShake256Core::new(label));
    for part in parts {
        hasher.update(&(part.len() as u64).to_be_bytes());
        hasher.update(part);
    }
    let mut output = [0u8; N];
    XofReader::read(&mut hasher.finalize_xof(), &mut output);
    output
}

pub fn random<const N: usize>() -> Result<[u8; N]> {
    let mut bytes = [0u8; N];
    File::open("/dev/urandom")
        .and_then(|mut source| source.read_exact(&mut bytes))
        .map_err(|error| format!("cannot obtain operating-system randomness: {error}"))?;
    Ok(bytes)
}

fn fixed<const N: usize>(bytes: &[u8], label: &str) -> Result<[u8; N]> {
    bytes
        .try_into()
        .map_err(|_| format!("{label} must be {N} bytes"))
}

/// The customization string that names a key's identity digest.
const KEY_ID_LABEL: &[u8] = b"DREGG.CLIENT.ENC-KEY-ID/v1";

/// A recipient's PUBLIC key pair: an X25519 key and an ML-KEM-768
/// encapsulation key. Something encapsulated to it opens only for a holder of
/// BOTH secrets, and stays sealed if EITHER primitive survives.
#[derive(Clone, PartialEq, Eq)]
pub struct HybridPublic {
    x25519: [u8; 32],
    kem: [u8; KEM_EK_LEN],
}

impl std::fmt::Debug for HybridPublic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "HybridPublic(id")?;
        for byte in self.id() {
            write!(f, "{byte:02x}")?;
        }
        write!(f, ")")
    }
}

impl HybridPublic {
    pub fn x25519(&self) -> &[u8; 32] {
        &self.x25519
    }

    pub fn kem(&self) -> &[u8; KEM_EK_LEN] {
        &self.kem
    }

    /// `x25519 (32) || ML-KEM-768 encapsulation key (1184)`.
    pub fn to_bytes(&self) -> Vec<u8> {
        [&self.x25519[..], &self.kem[..]].concat()
    }

    /// Strict: exactly `PUBLIC_LEN` bytes, and an encapsulation key the ML-KEM
    /// implementation accepts. A bare 1184-byte ML-KEM key (the pre-hybrid
    /// shape) is refused by name.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() == KEM_EK_LEN {
            return Err(format!(
                "a bare {KEM_EK_LEN}-byte ML-KEM-768 key is the pre-hybrid shape and is refused: a hybrid public key is {PUBLIC_LEN} bytes (X25519 32 + ML-KEM-768 {KEM_EK_LEN})"
            ));
        }
        if bytes.len() != PUBLIC_LEN {
            return Err(format!(
                "a hybrid encryption key is {PUBLIC_LEN} bytes (X25519 32 + ML-KEM-768 {KEM_EK_LEN}), not {}",
                bytes.len()
            ));
        }
        let kem: [u8; KEM_EK_LEN] = fixed(&bytes[32..], "ML-KEM-768 encapsulation key")?;
        EncapsulationKey::new(&ML_KEM_768, &kem)
            .map_err(|_| "the ML-KEM-768 encapsulation key is malformed")?;
        Ok(Self { x25519: fixed(&bytes[..32], "X25519 key")?, kem })
    }

    /// Only the known-answer test builds a key from raw halves it has not
    /// validated: the values are fixed bytes, not a real ML-KEM key.
    #[cfg(test)]
    pub fn from_raw_unchecked(x25519: [u8; 32], kem: [u8; KEM_EK_LEN]) -> Self {
        Self { x25519, kem }
    }

    /// The 32-byte name of this key pair: a digest over both halves.
    pub fn id(&self) -> [u8; 32] {
        cshake(KEY_ID_LABEL, &[&self.x25519, &self.kem])
    }
}

/// A recipient's SECRET keys: the X25519 secret and the ML-KEM-768 key
/// expanded from a FIPS 203 seed.
pub struct HybridSecret {
    x25519: StaticSecret,
    kem_seed: Zeroizing<[u8; KEM_SEED_LEN]>,
    kem: DecapsulationKey,
    public: HybridPublic,
}

impl HybridSecret {
    /// From the two secret halves: how a derived key, a keyring entry and a
    /// key file all build one.
    pub fn from_parts(x25519: [u8; 32], kem_seed: [u8; KEM_SEED_LEN]) -> Result<Self> {
        let x25519 = StaticSecret::from(x25519);
        let (kem, ek) = ml_kem_768_from_seed(&kem_seed)?;
        let public = HybridPublic { x25519: *PublicKey::from(&x25519).as_bytes(), kem: ek };
        Ok(Self { x25519, kem_seed: Zeroizing::new(kem_seed), kem, public })
    }

    /// A fresh random key pair (operator, link and recipient keys; room members
    /// derive theirs from their signing seed instead).
    pub fn generate() -> Result<Self> {
        let mut x25519 = random::<32>()?;
        let mut seed = random::<KEM_SEED_LEN>()?;
        let secret = Self::from_parts(x25519, seed);
        x25519.zeroize();
        seed.zeroize();
        secret
    }

    /// `x25519 secret (32) || FIPS 203 seed (64)`: the key file / custody record.
    /// A 2400-byte ML-KEM `dk` alone (the pre-hybrid shape) is refused by name.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self> {
        if bytes.len() == KEM_DK_LEN {
            return Err(format!(
                "a bare {KEM_DK_LEN}-byte ML-KEM-768 secret is the pre-hybrid shape and is refused: a hybrid secret is {SECRET_LEN} bytes (X25519 secret 32 + FIPS 203 seed 64)"
            ));
        }
        if bytes.len() != SECRET_LEN {
            return Err(format!("a hybrid secret key is {SECRET_LEN} bytes, not {}", bytes.len()));
        }
        Self::from_parts(fixed(&bytes[..32], "X25519 secret")?, fixed(&bytes[32..], "ML-KEM-768 seed")?)
    }

    pub fn to_bytes(&self) -> Zeroizing<Vec<u8>> {
        let (x25519, seed) = self.parts();
        Zeroizing::new([&x25519[..], &seed[..]].concat())
    }

    pub fn public(&self) -> &HybridPublic {
        &self.public
    }

    /// The two secret halves, for a keyring entry.
    pub fn parts(&self) -> (Zeroizing<[u8; 32]>, Zeroizing<[u8; KEM_SEED_LEN]>) {
        (Zeroizing::new(self.x25519.to_bytes()), self.kem_seed.clone())
    }

    /// Does `public` belong to this secret? Possible because the secret is a
    /// seed: the public key is recomputed, never trusted.
    pub fn matches(&self, public: &HybridPublic) -> bool {
        self.public == *public
    }

    /// The same X25519 half with another's ML-KEM half: only a test builds a
    /// split identity, to show an encapsulation needs both halves.
    #[cfg(test)]
    pub fn with_kem_of(&self, other: &HybridSecret) -> Result<Self> {
        Self::from_parts(self.x25519.to_bytes(), *other.kem_seed)
    }

    #[cfg(test)]
    pub fn with_x25519_of(&self, other: &HybridSecret) -> Result<Self> {
        Self::from_parts(other.x25519.to_bytes(), *self.kem_seed)
    }
}

/// Deterministic ML-KEM-768 key generation from a FIPS 203 seed (`d || z`).
///
/// `aws-lc-rs` generates a random key and loads a serialized one but exposes no
/// seeded generation. AWS-LC itself has it: `EVP_PKEY_keygen_deterministic`, the
/// call its own FIPS 203 known-answer tests use. `aws-lc-sys`'s portable
/// ("universal") bindings omit it, so it is declared here against the library
/// the workspace already links, at the exact pinned version the symbol carries
/// in its name (`aws_lc_0_45_0_*`): a version bump fails to LINK, loudly, and
/// is a deliberate edit of this line. The raw 2400-byte secret key it returns is
/// the standard FIPS 203 `dk`, which `DecapsulationKey::new` loads. The known-
/// answer test checks the derived encapsulation key against an independent
/// pure-Python FIPS 203 implementation, so a wrong seed layout cannot pass.
pub fn ml_kem_768_from_seed(seed: &[u8; KEM_SEED_LEN]) -> Result<(DecapsulationKey, [u8; KEM_EK_LEN])> {
    extern "C" {
        #[link_name = "aws_lc_0_45_0_EVP_PKEY_keygen_deterministic"]
        fn EVP_PKEY_keygen_deterministic(
            ctx: *mut aws_lc_sys::EVP_PKEY_CTX,
            out_pkey: *mut *mut aws_lc_sys::EVP_PKEY,
            seed: *const u8,
            seed_len: *mut usize,
        ) -> std::os::raw::c_int;
    }
    use aws_lc_sys as sys;
    struct Context(*mut sys::EVP_PKEY_CTX);
    impl Drop for Context {
        fn drop(&mut self) {
            // SAFETY: the pointer came from EVP_PKEY_CTX_new_id and is freed once.
            unsafe { sys::EVP_PKEY_CTX_free(self.0) }
        }
    }
    struct Pkey(*mut sys::EVP_PKEY);
    impl Drop for Pkey {
        fn drop(&mut self) {
            // SAFETY: the pointer came from EVP_PKEY_keygen_deterministic and is freed once.
            unsafe { sys::EVP_PKEY_free(self.0) }
        }
    }
    const FAIL: &str = "ML-KEM-768 key generation from the seed failed";
    // SAFETY: every pointer passed is either null where the API takes null or a
    // live buffer of the stated length; contexts and keys are freed by the guards.
    unsafe {
        let ctx = Context(sys::EVP_PKEY_CTX_new_id(sys::EVP_PKEY_KEM, std::ptr::null_mut()));
        if ctx.0.is_null()
            || sys::EVP_PKEY_CTX_kem_set_params(ctx.0, sys::NID_MLKEM768) != 1
            || sys::EVP_PKEY_keygen_init(ctx.0) != 1
        {
            return Err(FAIL.into());
        }
        let mut raw: *mut sys::EVP_PKEY = std::ptr::null_mut();
        let mut seed_len = KEM_SEED_LEN;
        if EVP_PKEY_keygen_deterministic(ctx.0, &mut raw, seed.as_ptr(), &mut seed_len) != 1
            || raw.is_null()
        {
            return Err(FAIL.into());
        }
        let pkey = Pkey(raw);
        let mut dk = Zeroizing::new(vec![0u8; KEM_DK_LEN]);
        let mut dk_len = dk.len();
        let mut ek = [0u8; KEM_EK_LEN];
        let mut ek_len = ek.len();
        if sys::EVP_PKEY_get_raw_private_key(pkey.0, dk.as_mut_ptr(), &mut dk_len) != 1
            || dk_len != KEM_DK_LEN
            || sys::EVP_PKEY_get_raw_public_key(pkey.0, ek.as_mut_ptr(), &mut ek_len) != 1
            || ek_len != KEM_EK_LEN
        {
            return Err(FAIL.into());
        }
        let key = DecapsulationKey::new(&ML_KEM_768, &dk).map_err(|_| FAIL.to_owned())?;
        Ok((key, ek))
    }
}

/// The transcript every part of an encapsulation is bound to, each part
/// length-prefixed: the frame, the caller's context, BOTH ciphertext
/// components (the ephemeral X25519 key and the ML-KEM ciphertext) and BOTH
/// recipient public keys. Callers use it as the AEAD's associated data.
pub fn transcript(
    frame: &[u8],
    context: &[&[u8]],
    ephemeral: &[u8; 32],
    kem_ct: &[u8],
    recipient: &HybridPublic,
) -> Vec<u8> {
    let mut aad = Vec::new();
    for part in [frame]
        .into_iter()
        .chain(context.iter().copied())
        .chain([&ephemeral[..], kem_ct, &recipient.x25519[..], &recipient.kem[..]])
    {
        aad.extend_from_slice(&(part.len() as u64).to_be_bytes());
        aad.extend_from_slice(part);
    }
    aad
}

/// The combiner. The key-encryption key is cSHAKE256 under `suite` (a
/// customization string naming the consumer and `X25519 + ML-KEM-768`) of the
/// two shared secrets and the full transcript, each input length-prefixed.
pub fn combine(suite: &[u8], shared_x25519: &[u8], shared_kem: &[u8], transcript: &[u8]) -> Zeroizing<[u8; KEK_LEN]> {
    Zeroizing::new(cshake(suite, &[shared_x25519, shared_kem, transcript]))
}

/// What an encapsulation yields.
pub struct Encapsulated {
    /// `ephemeral X25519 public key (32) || ML-KEM-768 ciphertext (1088)`.
    pub ciphertext: [u8; CIPHERTEXT_LEN],
    pub kek: Zeroizing<[u8; KEK_LEN]>,
    /// The full transcript the KEK was derived over: the AEAD associated data.
    pub transcript: Vec<u8>,
}

/// Encapsulate to `recipient`. `suite` is the cSHAKE256 customization string,
/// `frame` the versioned frame name, `context` the caller's binding (room,
/// epoch, member, packet hop, ...).
pub fn encapsulate(
    suite: &[u8],
    frame: &[u8],
    context: &[&[u8]],
    recipient: &HybridPublic,
) -> Result<Encapsulated> {
    let ephemeral_secret = StaticSecret::from(random::<32>()?);
    let ephemeral = *PublicKey::from(&ephemeral_secret).as_bytes();
    let shared_x = ephemeral_secret.diffie_hellman(&PublicKey::from(recipient.x25519));
    if !shared_x.was_contributory() {
        return Err("recipient X25519 key is a low-order point".into());
    }
    let encapsulation = EncapsulationKey::new(&ML_KEM_768, &recipient.kem)
        .map_err(|_| "recipient ML-KEM-768 encapsulation key is malformed")?;
    let (kem_ct, shared_k) = encapsulation
        .encapsulate()
        .map_err(|_| "ML-KEM-768 encapsulation failed")?;
    let kem_ct: [u8; KEM_CT_LEN] = fixed(kem_ct.as_ref(), "ML-KEM-768 ciphertext")?;
    let transcript = transcript(frame, context, &ephemeral, &kem_ct, recipient);
    let kek = combine(suite, shared_x.as_bytes(), shared_k.as_ref(), &transcript);
    let mut ciphertext = [0u8; CIPHERTEXT_LEN];
    ciphertext[..32].copy_from_slice(&ephemeral);
    ciphertext[32..].copy_from_slice(&kem_ct);
    Ok(Encapsulated { ciphertext, kek, transcript })
}

/// Decapsulate. A forged ML-KEM ciphertext yields an unrelated shared secret
/// (implicit rejection), so the KEK differs and the caller's AEAD fails; a
/// low-order ephemeral key is refused here.
pub fn decapsulate(
    suite: &[u8],
    frame: &[u8],
    context: &[&[u8]],
    secret: &HybridSecret,
    ciphertext: &[u8],
) -> Result<(Zeroizing<[u8; KEK_LEN]>, Vec<u8>)> {
    if ciphertext.len() != CIPHERTEXT_LEN {
        return Err(format!(
            "a hybrid ciphertext is {CIPHERTEXT_LEN} bytes (ephemeral X25519 32 + ML-KEM-768 {KEM_CT_LEN}), not {}",
            ciphertext.len()
        ));
    }
    let ephemeral: [u8; 32] = fixed(&ciphertext[..32], "ephemeral key")?;
    let shared_x = secret.x25519.diffie_hellman(&PublicKey::from(ephemeral));
    if !shared_x.was_contributory() {
        return Err("ephemeral X25519 key is a low-order point".into());
    }
    let shared_k = secret
        .kem
        .decapsulate(Ciphertext::from(&ciphertext[32..]))
        .map_err(|_| "ML-KEM-768 decapsulation failed")?;
    let transcript = transcript(frame, context, &ephemeral, &ciphertext[32..], &secret.public);
    let kek = combine(suite, shared_x.as_bytes(), shared_k.as_ref(), &transcript);
    Ok((kek, transcript))
}

#[cfg(test)]
mod tests {
    use super::*;

    const SUITE: &[u8] = b"DREGG.TEST.KEK/x25519+ml-kem-768/v1";
    const FRAME: &[u8] = b"DREGG/TEST/v1";

    #[test]
    fn an_encapsulation_opens_for_its_recipient_and_only_with_the_same_context() {
        let a = HybridSecret::generate().unwrap();
        let b = HybridSecret::generate().unwrap();
        let sent = encapsulate(SUITE, FRAME, &[b"ctx"], a.public()).unwrap();
        assert_eq!(sent.ciphertext.len(), CIPHERTEXT_LEN);
        let (kek, transcript) = decapsulate(SUITE, FRAME, &[b"ctx"], &a, &sent.ciphertext).unwrap();
        assert_eq!(kek[..], sent.kek[..]);
        assert_eq!(transcript, sent.transcript);
        let key_of = |suite: &[u8], frame: &[u8], ctx: &[u8], who: &HybridSecret| {
            decapsulate(suite, frame, &[ctx], who, &sent.ciphertext).unwrap().0
        };
        assert_ne!(key_of(SUITE, FRAME, b"ctx", &b)[..], sent.kek[..], "wrong recipient");
        assert_ne!(key_of(SUITE, FRAME, b"other", &a)[..], sent.kek[..], "context is bound");
        assert_ne!(key_of(SUITE, b"DREGG/TEST/v2", b"ctx", &a)[..], sent.kek[..], "frame is bound");
        assert_ne!(key_of(b"DREGG.TEST.KEK/other", FRAME, b"ctx", &a)[..], sent.kek[..], "suite is bound");
        let again = encapsulate(SUITE, FRAME, &[b"ctx"], a.public()).unwrap();
        assert_ne!(again.ciphertext, sent.ciphertext, "fresh ephemeral key and encapsulation");
        assert_ne!(again.kek[..], sent.kek[..]);
    }

    #[test]
    fn both_halves_are_required_and_both_ciphertext_components_are_bound() {
        let a = HybridSecret::generate().unwrap();
        let b = HybridSecret::generate().unwrap();
        let sent = encapsulate(SUITE, FRAME, &[b"ctx"], a.public()).unwrap();
        let kek_of = |who: &HybridSecret, ct: &[u8]| decapsulate(SUITE, FRAME, &[b"ctx"], who, ct).map(|v| v.0);
        for split in [a.with_kem_of(&b).unwrap(), a.with_x25519_of(&b).unwrap()] {
            assert_ne!(kek_of(&split, &sent.ciphertext).unwrap()[..], sent.kek[..]);
        }
        for at in [0, 31, 32, 32 + 544, CIPHERTEXT_LEN - 1] {
            let mut bad = sent.ciphertext;
            bad[at] ^= 1;
            if let Ok(kek) = kek_of(&a, &bad) {
                assert_ne!(kek[..], sent.kek[..], "ciphertext byte {at}");
            }
        }
        assert!(kek_of(&a, &sent.ciphertext[..CIPHERTEXT_LEN - 1]).is_err());
        assert!(kek_of(&a, &sent.ciphertext[32..]).is_err(), "a bare KEM ciphertext is not a hybrid one");
    }

    #[test]
    fn low_order_x25519_halves_are_refused_on_both_sides() {
        let a = HybridSecret::generate().unwrap();
        let zero = HybridPublic::from_bytes(&[&[0u8; 32][..], &a.public().to_bytes()[32..]].concat()).unwrap();
        assert!(encapsulate(SUITE, FRAME, &[b"c"], &zero).err().unwrap().contains("low-order"));
        let mut forged = encapsulate(SUITE, FRAME, &[b"c"], a.public()).unwrap().ciphertext;
        forged[..32].copy_from_slice(&[0; 32]);
        assert!(decapsulate(SUITE, FRAME, &[b"c"], &a, &forged).err().unwrap().contains("low-order"));
    }

    #[test]
    fn keys_serialize_regenerate_and_refuse_the_pre_hybrid_shapes_by_name() {
        let a = HybridSecret::generate().unwrap();
        let bytes = a.to_bytes();
        assert_eq!((bytes.len(), a.public().to_bytes().len()), (SECRET_LEN, PUBLIC_LEN));
        let back = HybridSecret::from_bytes(&bytes).unwrap();
        assert!(back.matches(a.public()), "the seed regenerates the public key");
        assert!(!back.matches(HybridSecret::generate().unwrap().public()));
        assert_eq!(HybridPublic::from_bytes(&a.public().to_bytes()).unwrap(), *a.public());
        assert_ne!(a.public().id(), HybridSecret::generate().unwrap().public().id());
        // Pre-hybrid shapes: a bare ML-KEM key (1184) and secret (2400).
        assert!(HybridPublic::from_bytes(&a.public().to_bytes()[32..]).unwrap_err().contains("pre-hybrid"));
        assert!(HybridSecret::from_bytes(&[0; 2400]).err().unwrap().contains("pre-hybrid"));
        assert!(HybridSecret::from_bytes(&bytes[..SECRET_LEN - 1]).is_err());
        assert!(HybridPublic::from_bytes(&a.public().to_bytes()[..PUBLIC_LEN - 1]).is_err());
    }
}
