//! Owned fixed-width integers for commitment digests.
//!
//! `[PROVER-digest-width]` cannot be closed by calling a single BabyBear value a
//! hash.  [`Digest`] therefore carries nine canonical BabyBear limbs in
//! little-endian positional order.  Since `BABY_BEAR_P > 2^30`, its value space
//! has cardinality `BABY_BEAR_P^9 > 2^270`, comfortably beyond a 248-bit range.
//! No external bignum crate is needed: comparison and the fixed wire encoding
//! operate directly on the limbs.
//!
//! Width is not collision resistance.  [`hash_fields`] expands the existing
//! demo permutation into nine independently domain-separated lanes, but the
//! permutation still has demo parameters and no collision-resistance theorem.
//! This module closes the runtime *representation* wound, not `[COMMIT-CR]` or
//! `[PROVER-poseidon-params]`.

use core::cmp::Ordering;
use core::fmt;

use crate::descriptor::Fp;
use crate::poseidon::{perm, PermSpec, BABY_BEAR_P};

/// Number of base-`BABY_BEAR_P` limbs in a commitment digest.
pub const DIGEST_LIMBS: usize = 9;

/// Conservative bit range guaranteed just by `BABY_BEAR_P > 2^30`.
pub const DIGEST_RANGE_BITS: usize = 30 * DIGEST_LIMBS;

/// Fixed byte width: one little-endian `u32` per canonical field limb.
pub const DIGEST_BYTES: usize = 4 * DIGEST_LIMBS;

const _: () = {
    assert!(BABY_BEAR_P > (1 << 30));
    assert!(DIGEST_RANGE_BITS >= 248);
};

/// Prefix used when a digest is encoded into a Fiat--Shamir transcript.
pub const DIGEST_ENCODING_TAG: Fp = 0x5744_4731; // "WDG1"

/// Hash domains.  These tags are part of the runtime commitment format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u64)]
pub enum DigestDomain {
    /// A scalar trace leaf.
    TraceLeaf = 0x5452_4c46, // "TRLF"
    /// A four-limb FRI extension-field leaf.
    FriExtLeaf = 0x4652_4c46, // "FRLF"
    /// A binary Merkle internal node.
    MerkleNode = 0x4d52_4b4e, // "MRKN"
    /// A leaf inserted only to complete a non-power-of-two tree.
    MerklePadding = 0x4d52_5044, // "MRPD"
}

impl DigestDomain {
    /// Canonical BabyBear field element used as the domain tag.
    pub const fn tag(self) -> Fp {
        self as Fp
    }
}

/// A malformed wide digest or wire encoding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DigestError {
    /// A limb is not the canonical representative in `[0, BABY_BEAR_P)`.
    NonCanonicalLimb { index: usize, value: Fp },
    /// A fixed-width byte encoding has the wrong length.
    WrongByteLength { expected: usize, actual: usize },
    /// A caller-supplied transcript domain is not canonical.
    NonCanonicalDomain(Fp),
}

impl fmt::Display for DigestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            DigestError::NonCanonicalLimb { index, value } => {
                write!(f, "digest limb {index} is non-canonical: {value}")
            }
            DigestError::WrongByteLength { expected, actual } => {
                write!(f, "digest encoding has {actual} bytes, expected {expected}")
            }
            DigestError::NonCanonicalDomain(value) => {
                write!(f, "digest encoding domain is non-canonical: {value}")
            }
        }
    }
}

impl std::error::Error for DigestError {}

/// A base-`BABY_BEAR_P` fixed-width integer, least-significant limb first.
///
/// The field is public on purpose: proof objects are untrusted data, so a
/// verifier must be able to receive a malformed limb and reject it.  Trusted
/// construction should use [`Digest::try_from_limbs`].
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Digest {
    /// Base-`BABY_BEAR_P` digits, least significant first.
    pub limbs: [Fp; DIGEST_LIMBS],
}

impl Digest {
    /// The all-zero wide integer.
    pub const ZERO: Digest = Digest {
        limbs: [0; DIGEST_LIMBS],
    };

    /// Validate and construct a canonical BabyBear-limb digest.
    pub fn try_from_limbs(limbs: [Fp; DIGEST_LIMBS]) -> Result<Self, DigestError> {
        let digest = Digest { limbs };
        digest.validate()?;
        Ok(digest)
    }

    /// Whether every limb is a canonical BabyBear representative.
    pub fn is_canonical(&self) -> bool {
        self.limbs.iter().all(|&limb| limb < BABY_BEAR_P)
    }

    /// Reject the first non-canonical limb.
    pub fn validate(&self) -> Result<(), DigestError> {
        match self
            .limbs
            .iter()
            .enumerate()
            .find(|(_, limb)| **limb >= BABY_BEAR_P)
        {
            Some((index, &value)) => Err(DigestError::NonCanonicalLimb { index, value }),
            None => Ok(()),
        }
    }

    /// Canonical limbs in little-endian positional order.
    pub const fn as_limbs(&self) -> &[Fp; DIGEST_LIMBS] {
        &self.limbs
    }

    /// Fixed-width canonical wire encoding: nine little-endian `u32` limbs.
    ///
    /// This is deliberately not a raw-memory cast, so host endianness and
    /// `u64` padding cannot leak into the format.
    pub fn to_le_bytes(&self) -> Result<[u8; DIGEST_BYTES], DigestError> {
        self.validate()?;
        let mut out = [0u8; DIGEST_BYTES];
        for (i, &limb) in self.limbs.iter().enumerate() {
            let bytes = (limb as u32).to_le_bytes();
            out[4 * i..4 * i + 4].copy_from_slice(&bytes);
        }
        Ok(out)
    }

    /// Parse the fixed-width canonical wire encoding.
    pub fn from_le_bytes(bytes: &[u8]) -> Result<Self, DigestError> {
        if bytes.len() != DIGEST_BYTES {
            return Err(DigestError::WrongByteLength {
                expected: DIGEST_BYTES,
                actual: bytes.len(),
            });
        }
        let mut limbs = [0; DIGEST_LIMBS];
        for (i, limb) in limbs.iter_mut().enumerate() {
            let mut chunk = [0u8; 4];
            chunk.copy_from_slice(&bytes[4 * i..4 * i + 4]);
            *limb = u32::from_le_bytes(chunk) as Fp;
        }
        Digest::try_from_limbs(limbs)
    }

    /// Domain-separated field encoding for transcript absorption.
    ///
    /// The returned vector is `WDG1 || domain || limb[0..9]`.  Callers must use
    /// distinct `domain` values for semantically distinct protocol objects.
    pub fn encode_with_domain(&self, domain: Fp) -> Result<[Fp; DIGEST_LIMBS + 2], DigestError> {
        self.validate()?;
        if domain >= BABY_BEAR_P {
            return Err(DigestError::NonCanonicalDomain(domain));
        }
        let mut out = [0; DIGEST_LIMBS + 2];
        out[0] = DIGEST_ENCODING_TAG;
        out[1] = domain;
        out[2..].copy_from_slice(&self.limbs);
        Ok(out)
    }
}

impl fmt::Debug for Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Digest").field(&self.limbs).finish()
    }
}

impl Ord for Digest {
    fn cmp(&self, other: &Self) -> Ordering {
        for i in (0..DIGEST_LIMBS).rev() {
            match self.limbs[i].cmp(&other.limbs[i]) {
                Ordering::Equal => {}
                order => return order,
            }
        }
        Ordering::Equal
    }
}

impl PartialOrd for Digest {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn compress2(spec: &PermSpec, left: Fp, right: Fp, p: u64) -> Fp {
    assert_eq!(p, BABY_BEAR_P, "wide digests use canonical BabyBear limbs");
    assert!(spec.width >= 2, "wide digest hashing needs width >= 2");
    assert!(
        left < p && right < p,
        "wide digest hash input must be canonical"
    );
    let mut state = vec![0; spec.width];
    state[0] = left;
    state[1] = right;
    perm(spec, &state, p)[0]
}

/// Expand canonical field elements into a nine-limb digest.
///
/// Every output lane starts from a distinct `(domain, lane)` seed and absorbs
/// the complete input plus its length.  Thus there is no single-field choke
/// point shared by all output lanes.  This is still a demo hash construction,
/// not evidence of 248-bit collision resistance; deployment needs audited
/// parameters and a proof/analysis for the full construction.
pub fn hash_fields(spec: &PermSpec, domain: DigestDomain, fields: &[Fp], p: u64) -> Digest {
    assert_eq!(p, BABY_BEAR_P, "wide digests use canonical BabyBear limbs");
    assert!(
        (fields.len() as u64) < p,
        "wide digest input length must fit one field element"
    );
    assert!(
        fields.iter().all(|&field| field < p),
        "wide digest hash input must be canonical"
    );
    let mut limbs = [0; DIGEST_LIMBS];
    for (lane, output) in limbs.iter_mut().enumerate() {
        let mut state = compress2(spec, domain.tag(), lane as Fp, p);
        for &field in fields {
            state = compress2(spec, state, field, p);
        }
        *output = compress2(spec, state, fields.len() as Fp, p);
    }
    Digest { limbs }
}

/// Domain-separated binary compression of two wide digests.
pub fn hash_pair(spec: &PermSpec, left: Digest, right: Digest, p: u64) -> Digest {
    left.validate().expect("left digest must be canonical");
    right.validate().expect("right digest must be canonical");
    let mut fields = [0; 2 * DIGEST_LIMBS];
    fields[..DIGEST_LIMBS].copy_from_slice(&left.limbs);
    fields[DIGEST_LIMBS..].copy_from_slice(&right.limbs);
    hash_fields(spec, DigestDomain::MerkleNode, &fields, p)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon::demo_spec;

    #[test]
    fn width_exceeds_requested_range_without_external_bignum() {
        assert_eq!(DIGEST_RANGE_BITS, 270);
    }

    #[test]
    fn positional_comparison_uses_high_limb_first() {
        let low = Digest::try_from_limbs([BABY_BEAR_P - 1, 0, 0, 0, 0, 0, 0, 0, 0]).unwrap();
        let high = Digest::try_from_limbs([0, 1, 0, 0, 0, 0, 0, 0, 0]).unwrap();
        assert!(low < high, "base-p positional comparison, not array order");
    }

    #[test]
    fn fixed_serialization_round_trips_and_rejects_aliases() {
        let digest =
            Digest::try_from_limbs([0, 1, 255, 256, 65_537, BABY_BEAR_P - 1, 42, 99, 1_000_000])
                .unwrap();
        let bytes = digest.to_le_bytes().unwrap();
        assert_eq!(Digest::from_le_bytes(&bytes), Ok(digest));
        assert!(matches!(
            Digest::from_le_bytes(&bytes[..DIGEST_BYTES - 1]),
            Err(DigestError::WrongByteLength { .. })
        ));

        let mut noncanonical = bytes;
        noncanonical[..4].copy_from_slice(&(BABY_BEAR_P as u32).to_le_bytes());
        assert!(matches!(
            Digest::from_le_bytes(&noncanonical),
            Err(DigestError::NonCanonicalLimb { index: 0, .. })
        ));
    }

    #[test]
    fn domains_and_lanes_have_teeth() {
        let spec = demo_spec();
        let leaf = hash_fields(&spec, DigestDomain::TraceLeaf, &[7], BABY_BEAR_P);
        let changed = hash_fields(&spec, DigestDomain::TraceLeaf, &[8], BABY_BEAR_P);
        let other_domain = hash_fields(&spec, DigestDomain::FriExtLeaf, &[7], BABY_BEAR_P);
        assert_ne!(leaf, changed);
        assert_ne!(leaf, other_domain);
        assert!(leaf.limbs.windows(2).any(|pair| pair[0] != pair[1]));
    }

    #[test]
    fn transcript_encoding_is_explicit_and_checked() {
        let digest = Digest::try_from_limbs([1, 2, 3, 4, 5, 6, 7, 8, 9]).unwrap();
        let encoded = digest.encode_with_domain(17).unwrap();
        assert_eq!(encoded[0], DIGEST_ENCODING_TAG);
        assert_eq!(encoded[1], 17);
        assert_eq!(&encoded[2..], digest.as_limbs());
        assert!(matches!(
            digest.encode_with_domain(BABY_BEAR_P),
            Err(DigestError::NonCanonicalDomain(_))
        ));
    }
}
