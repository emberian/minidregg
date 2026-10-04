//! The signer abstraction: one interface over the key schemes a Mini participant or fleet key
//! can have, so no caller is written against `ed25519_dalek` directly.
//!
//! * [`Scheme::Ed25519`] — the scheme the Host admits today: a raw Ed25519 signature over the
//!   Lean-canonical bytes (`Compiler.CredentialSignatureAdmission.ed25519Algorithm = 1`,
//!   verified by `native/credential-signature-verifier`).
//! * [`Scheme::HybridEd25519MlDsa65`] — Ed25519 AND ML-DSA-65 (FIPS 204, via `fips204`) over the
//!   SAME bytes, algorithm code 2. A hybrid key is both public keys; a hybrid signature is both
//!   signatures; it verifies only if BOTH halves verify, so stripping either half, swapping
//!   either half, or tampering with either half is a refusal that names the half. The Ed25519
//!   half is byte-identical to what the Ed25519 scheme would sign, so a Host that admits a
//!   hybrid key record can verify that half with the verifier it already has (see
//!   `docs/SDK-PQ.md` for exactly what the Host must change).
//!
//! Wire layouts (fixed width; nothing is length-prefixed because every width is a constant):
//! ```text
//! Ed25519 public key   := ed[32]                      signature := ed[64]
//! Hybrid  public key   := ed[32] ‖ ml[1952]           signature := ed[64] ‖ ml[3309]
//! ```
//! ML-DSA signs with the FIPS 204 context string [`ML_DSA_CONTEXT`] (domain separation from every
//! other ML-DSA use in the repo, e.g. the joint-agreement helper's `MiniJointAgreementV1`) and
//! the deterministic variant (`rnd = 0^32`, FIPS 204 §3.4): a fixed key and message always give
//! the same signature, as with Ed25519, and no RNG is needed (the crate builds for wasm32).
//!
//! `fips204` is a pure-Rust implementation of FIPS 204; it is NOT the Lean-verified ML-DSA core
//! Bread's `dregg_turn::pq` uses. That is a stated difference, not a hidden one.
use ed25519_dalek::{Signer as _, SigningKey, VerifyingKey};
use fips204::ml_dsa_65 as dsa;
use fips204::traits::{KeyGen, SerDes, Signer as _, Verifier as _};
use zeroize::Zeroizing;

use crate::{Error, Result};

/// FIPS 204 context string of the hybrid scheme's ML-DSA half.
pub const ML_DSA_CONTEXT: &[u8] = b"MINI/SDK/HYBRID/ML-DSA-65/v1";
pub const ED_PK_LEN: usize = 32;
pub const ED_SIG_LEN: usize = 64;
pub const ML_PK_LEN: usize = dsa::PK_LEN;
pub const ML_SIG_LEN: usize = dsa::SIG_LEN;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scheme {
    Ed25519,
    HybridEd25519MlDsa65,
}

impl Scheme {
    /// The key record's algorithm code: 1 is the Host's `ed25519Algorithm`; 2 is the code this
    /// SDK reserves for the hybrid (the Host must define it; see `docs/SDK-PQ.md`).
    pub const fn code(self) -> u8 {
        match self {
            Scheme::Ed25519 => 1,
            Scheme::HybridEd25519MlDsa65 => 2,
        }
    }
    pub fn from_code(code: u8) -> Result<Self> {
        match code {
            1 => Ok(Scheme::Ed25519),
            2 => Ok(Scheme::HybridEd25519MlDsa65),
            _ => Err(Error(format!("unknown signature scheme code {code}"))),
        }
    }
    pub const fn public_key_len(self) -> usize {
        match self {
            Scheme::Ed25519 => ED_PK_LEN,
            Scheme::HybridEd25519MlDsa65 => ED_PK_LEN + ML_PK_LEN,
        }
    }
    pub const fn signature_len(self) -> usize {
        match self {
            Scheme::Ed25519 => ED_SIG_LEN,
            Scheme::HybridEd25519MlDsa65 => ED_SIG_LEN + ML_SIG_LEN,
        }
    }
}

/// A signing key of some [`Scheme`]. Key material; never logged.
pub trait Signer {
    fn scheme(&self) -> Scheme;
    /// The public key in the scheme's wire layout.
    fn public_key(&self) -> Vec<u8>;
    /// A signature over exactly `message`, in the scheme's wire layout.
    fn sign(&self, message: &[u8]) -> Result<Vec<u8>>;
}

pub struct Ed25519Signer(pub SigningKey);

impl Signer for Ed25519Signer {
    fn scheme(&self) -> Scheme {
        Scheme::Ed25519
    }
    fn public_key(&self) -> Vec<u8> {
        self.0.verifying_key().as_bytes().to_vec()
    }
    fn sign(&self, message: &[u8]) -> Result<Vec<u8>> {
        Ok(self.0.sign(message).to_bytes().to_vec())
    }
}

/// Ed25519 + ML-DSA-65 over the same message.
pub struct HybridSigner {
    ed: SigningKey,
    ml: dsa::PrivateKey,
    ml_public: Vec<u8>,
}

impl HybridSigner {
    /// From the two 32-byte seeds: the Ed25519 secret seed and the ML-DSA-65 `xi`
    /// (FIPS 204 `ML-DSA.KeyGen_internal` seed).
    pub fn from_seeds(ed_seed: &[u8; 32], ml_xi: &[u8; 32]) -> Self {
        let (pk, sk) = dsa::KG::keygen_from_seed(ml_xi);
        HybridSigner { ed: SigningKey::from_bytes(ed_seed), ml: sk, ml_public: pk.into_bytes().to_vec() }
    }
}

impl Signer for HybridSigner {
    fn scheme(&self) -> Scheme {
        Scheme::HybridEd25519MlDsa65
    }
    fn public_key(&self) -> Vec<u8> {
        let mut out = self.ed.verifying_key().as_bytes().to_vec();
        out.extend_from_slice(&self.ml_public);
        out
    }
    fn sign(&self, message: &[u8]) -> Result<Vec<u8>> {
        let mut out = self.ed.sign(message).to_bytes().to_vec();
        let ml = self.ml.try_sign_with_seed(&Zeroizing::new([0u8; 32]), message, ML_DSA_CONTEXT)
            .map_err(|e| Error(format!("ML-DSA-65 signing: {e}")))?;
        out.extend_from_slice(&ml);
        Ok(out)
    }
}

/// Verify `signature` over `message` under `public_key`, both in `scheme`'s wire layout. A
/// hybrid signature verifies only if BOTH halves do; the refusal names the first that does not.
pub fn verify(scheme: Scheme, public_key: &[u8], message: &[u8], signature: &[u8]) -> Result<()> {
    if public_key.len() != scheme.public_key_len() {
        return Err(Error(format!("{scheme:?} public key must be {} bytes, got {}", scheme.public_key_len(), public_key.len())));
    }
    if signature.len() != scheme.signature_len() {
        return Err(Error(format!("{scheme:?} signature must be {} bytes, got {}", scheme.signature_len(), signature.len())));
    }
    let (ed_pk, ml_pk) = public_key.split_at(ED_PK_LEN);
    let (ed_sig, ml_sig) = signature.split_at(ED_SIG_LEN);
    let key = VerifyingKey::from_bytes(ed_pk.try_into().expect("width checked")).map_err(|_| Error("Ed25519 public key does not decode".into()))?;
    let sig = ed25519_dalek::Signature::from_bytes(ed_sig.try_into().expect("width checked"));
    key.verify_strict(message, &sig).map_err(|_| Error("Ed25519 half does not verify".into()))?;
    if scheme == Scheme::HybridEd25519MlDsa65 {
        let pk = dsa::PublicKey::try_from_bytes(ml_pk.try_into().expect("width checked"))
            .map_err(|e| Error(format!("ML-DSA-65 public key does not decode: {e}")))?;
        let sig: [u8; ML_SIG_LEN] = ml_sig.try_into().expect("width checked");
        if !pk.verify(message, &sig, ML_DSA_CONTEXT) {
            return Err(Error("ML-DSA-65 half does not verify".into()));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hybrid() -> HybridSigner {
        HybridSigner::from_seeds(&[7; 32], &[9; 32])
    }

    #[test]
    fn both_schemes_sign_and_verify_and_widths_are_fixed() {
        let ed = Ed25519Signer(SigningKey::from_bytes(&[7; 32]));
        let h = hybrid();
        for (s, scheme) in [(&ed as &dyn Signer, Scheme::Ed25519), (&h as &dyn Signer, Scheme::HybridEd25519MlDsa65)] {
            assert_eq!(s.scheme(), scheme);
            let (pk, sig) = (s.public_key(), s.sign(b"frame").unwrap());
            assert_eq!((pk.len(), sig.len()), (scheme.public_key_len(), scheme.signature_len()));
            verify(scheme, &pk, b"frame", &sig).unwrap();
            assert!(verify(scheme, &pk, b"other", &sig).is_err(), "wrong message");
        }
        assert_eq!((Scheme::HybridEd25519MlDsa65.public_key_len(), Scheme::HybridEd25519MlDsa65.signature_len()), (1984, 3373));
    }

    #[test]
    fn signing_is_deterministic_and_the_ed_half_is_the_plain_ed25519_signature() {
        let (h, ed) = (hybrid(), Ed25519Signer(SigningKey::from_bytes(&[7; 32])));
        assert_eq!(h.sign(b"m").unwrap(), h.sign(b"m").unwrap());
        assert_eq!(h.sign(b"m").unwrap()[..64], ed.sign(b"m").unwrap()[..]);
        assert_eq!(h.public_key()[..32], ed.public_key()[..]);
    }

    #[test]
    fn a_wrong_key_refuses_in_every_half() {
        let h = hybrid();
        let sig = h.sign(b"frame").unwrap();
        let other_ed = HybridSigner::from_seeds(&[8; 32], &[9; 32]).public_key();
        let other_ml = HybridSigner::from_seeds(&[7; 32], &[10; 32]).public_key();
        assert_eq!(verify(Scheme::HybridEd25519MlDsa65, &other_ed, b"frame", &sig).unwrap_err().0, "Ed25519 half does not verify");
        assert_eq!(verify(Scheme::HybridEd25519MlDsa65, &other_ml, b"frame", &sig).unwrap_err().0, "ML-DSA-65 half does not verify");
    }

    #[test]
    fn tampering_either_half_or_the_layout_refuses_and_names_the_half() {
        let h = hybrid();
        let pk = h.public_key();
        let sig = h.sign(b"frame").unwrap();
        let check = |mutate: &dyn Fn(&mut Vec<u8>)| {
            let mut s = sig.clone();
            mutate(&mut s);
            assert_ne!(s, sig, "the mutation changed nothing");
            verify(Scheme::HybridEd25519MlDsa65, &pk, b"frame", &s).unwrap_err().0
        };
        assert_eq!(check(&|s| s[0] ^= 1), "Ed25519 half does not verify");
        assert_eq!(check(&|s| s[63] ^= 0x80), "Ed25519 half does not verify");
        assert_eq!(check(&|s| s[64] ^= 1), "ML-DSA-65 half does not verify");
        assert_eq!(check(&|s| { let n = s.len(); s[n - 1] ^= 1 }), "ML-DSA-65 half does not verify");
        assert!(check(&|s| { s.pop(); }).contains("signature must be 3373 bytes"));
        // The Ed25519 half alone is a valid Ed25519 signature but never a hybrid one: stripping
        // the ML-DSA half is a refusal, not a downgrade.
        let ed_only = sig[..64].to_vec();
        assert!(verify(Scheme::HybridEd25519MlDsa65, &pk, b"frame", &ed_only).is_err());
        verify(Scheme::Ed25519, &pk[..32], b"frame", &ed_only).unwrap();
        // A hybrid signature is also not an Ed25519 one (width), so schemes cannot be confused.
        assert!(verify(Scheme::Ed25519, &pk[..32], b"frame", &sig).is_err());
        // The ML-DSA half of another message does not transplant.
        let other = h.sign(b"other frame").unwrap();
        let mut spliced = sig[..64].to_vec();
        spliced.extend_from_slice(&other[64..]);
        assert_eq!(verify(Scheme::HybridEd25519MlDsa65, &pk, b"frame", &spliced).unwrap_err().0, "ML-DSA-65 half does not verify");
    }

    #[test]
    fn scheme_codes_round_trip_and_unknown_codes_refuse() {
        for s in [Scheme::Ed25519, Scheme::HybridEd25519MlDsa65] {
            assert_eq!(Scheme::from_code(s.code()).unwrap(), s);
        }
        assert!(Scheme::from_code(0).is_err() && Scheme::from_code(3).is_err());
    }
}
