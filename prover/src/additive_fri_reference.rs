//! One full-opening additive-FRI fold-consistency round over [`TowerElem`].
//!
//! This module deliberately stops at the smallest honest committed round:
//!
//! 1. fast-transform novel-basis coefficients on `alpha + span(beta)`;
//! 2. commit the complete evaluation word;
//! 3. fold every pair in the last basis direction with a caller-visible
//!    challenge;
//! 4. commit the complete folded word;
//! 5. verify by reopening both words in full, recomputing both roots, and
//!    checking every fold equation.
//!
//! The proof therefore contains `n + n/2` tower elements.  It is a one-round,
//! full-opening reference, not a succinct FRI proof and not a low-degree
//! soundness claim.  Its useful job is to pin the transform/domain ordering,
//! canonical commitment encoding, and additive fold equation end to end.
//!
//! Tower leaves own a fixed canonical format: `BTL1 || level || bits[0..4]`,
//! where `bits` is four little-endian 16-bit chunks.  These six canonical
//! BabyBear elements are hashed to the existing nine-limb wide [`Digest`].
//! The format is injective on `TowerElem`; it does not rely on host layout.
//!
//! Honest residuals:
//!
//! * `[ANTT-FRI-basis-coherence-runtime]`: prove the explicit tower bits,
//!   ordered basis, affine-coset order, and folded image-domain indexing agree
//!   with Lean's choice-selected binary tower and `Theory.AdditiveNTT` domain.
//! * `[ANTT-FRI-RUST-UNVERIFIED]`: the fast Rust transform is unverified compute,
//!   canonical leaf encoding, Merkle fold, and one-round pair equations.
//! * `[ANTT-FRI-COMMIT-CR]`: binding still rests on collision resistance of an
//!   audited commitment permutation; the current wide hash has demo parameters.
//! * `[ANTT-FRI-FS]`: derive the challenge after the input root with a formally
//!   matched transcript/RBR game; this reference takes the challenge explicitly.
//! * `[ANTT-FRI-succinct]`: replace complete words with sampled Merkle openings
//!   and compose many rounds with the additive proximity theorem.

use core::fmt;

use crate::additive_ntt::{forward, AdditiveNttError};
use crate::binary_tower::{TowerElem, TowerError};
use crate::commit::commit_digests;
use crate::descriptor::Fp;
use crate::poseidon::{PermSpec, BABY_BEAR_P};
use crate::wide::{hash_fields, Digest, DigestDomain};

/// `"BTL1"`, the versioned canonical tower-leaf format tag.
pub const TOWER_LEAF_V1_TAG: Fp = 0x4254_4c31;

/// Number of canonical BabyBear elements in one tower-leaf preimage.
pub const TOWER_LEAF_FIELDS: usize = 6;

const _: () = assert!(TOWER_LEAF_V1_TAG < BABY_BEAR_P);

/// Public statement for one full-opening fold-consistency round.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdditiveFriRoundClaim {
    pub input_root: Digest,
    pub folded_root: Digest,
    pub input_len: usize,
    pub basis: Vec<TowerElem>,
    pub offset: TowerElem,
    pub challenge: TowerElem,
}

/// Deliberately non-succinct witness: both committed words in full.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdditiveFriRoundProof {
    pub input_word: Vec<TowerElem>,
    pub folded_word: Vec<TowerElem>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AdditiveFriError {
    Tower(TowerError),
    Transform(AdditiveNttError),
    UnsupportedModulus(u64),
    InvalidPermutation(String),
    EmptyWord,
    NoFoldDirection,
    InvalidShape {
        input_len: usize,
        folded_len: usize,
        basis_len: usize,
    },
    FieldLevelMismatch {
        role: &'static str,
        index: usize,
        expected: u8,
        actual: u8,
    },
    DomainTooLarge {
        basis_len: usize,
        dimension: usize,
    },
    DependentBasis {
        index: usize,
    },
    NonCanonicalCommitment(&'static str),
    CommitmentMismatch(&'static str),
    FoldMismatch,
}

impl From<TowerError> for AdditiveFriError {
    fn from(value: TowerError) -> Self {
        Self::Tower(value)
    }
}

impl From<AdditiveNttError> for AdditiveFriError {
    fn from(value: AdditiveNttError) -> Self {
        Self::Transform(value)
    }
}

impl fmt::Display for AdditiveFriError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Tower(error) => error.fmt(f),
            Self::Transform(error) => error.fmt(f),
            Self::UnsupportedModulus(p) => {
                write!(f, "tower commitments require BabyBear modulus, got {p}")
            }
            Self::InvalidPermutation(error) => write!(f, "invalid commitment permutation: {error}"),
            Self::EmptyWord => write!(f, "cannot commit an empty tower word"),
            Self::NoFoldDirection => write!(f, "one additive FRI round needs a nonempty basis"),
            Self::InvalidShape {
                input_len,
                folded_len,
                basis_len,
            } => write!(
                f,
                "round shape input={input_len}, folded={folded_len}, basis={basis_len} is invalid"
            ),
            Self::FieldLevelMismatch {
                role,
                index,
                expected,
                actual,
            } => write!(
                f,
                "{role}[{index}] is at tower level {actual}, expected {expected}"
            ),
            Self::DomainTooLarge {
                basis_len,
                dimension,
            } => write!(
                f,
                "{basis_len} independent directions do not fit field dimension {dimension}"
            ),
            Self::DependentBasis { index } => write!(
                f,
                "basis[{index}] lies in the span of the preceding directions"
            ),
            Self::NonCanonicalCommitment(side) => {
                write!(f, "{side} commitment has a noncanonical wide limb")
            }
            Self::CommitmentMismatch(side) => write!(f, "{side} commitment does not open"),
            Self::FoldMismatch => write!(f, "the opened folded word violates a pair equation"),
        }
    }
}

impl std::error::Error for AdditiveFriError {}

/// Canonical, injective preimage for one tower element.
///
/// The four 16-bit chunks are least significant first.  Every field is below
/// `BABY_BEAR_P`, and the tower level prevents equal bit strings at different
/// field levels from aliasing.
pub const fn tower_element_encoding(value: TowerElem) -> [Fp; TOWER_LEAF_FIELDS] {
    let bits = value.bits();
    [
        TOWER_LEAF_V1_TAG,
        value.level() as Fp,
        bits & 0xffff,
        (bits >> 16) & 0xffff,
        (bits >> 32) & 0xffff,
        (bits >> 48) & 0xffff,
    ]
}

/// Domain-separated wide digest of one canonically encoded tower element.
pub fn tower_leaf_digest(
    value: TowerElem,
    spec: &PermSpec,
    p: u64,
) -> Result<Digest, AdditiveFriError> {
    validate_commitment_runtime(spec, p)?;
    Ok(hash_fields(
        spec,
        DigestDomain::FriExtLeaf,
        &tower_element_encoding(value),
        p,
    ))
}

/// Wide Merkle root of a complete tower word.
pub fn commit_tower_word(
    word: &[TowerElem],
    spec: &PermSpec,
    p: u64,
) -> Result<Digest, AdditiveFriError> {
    validate_commitment_runtime(spec, p)?;
    if word.is_empty() {
        return Err(AdditiveFriError::EmptyWord);
    }
    let leaves = word
        .iter()
        .copied()
        .map(|value| tower_leaf_digest_validated(value, spec, p))
        .collect::<Vec<_>>();
    Ok(commit_digests(spec, &leaves, p).0)
}

/// Fold pairs separated by the last domain bit.
///
/// Output index `i` represents the transversal point
/// `offset + sum_{j<k-1} bit(i,j)*basis[j]`.  The implementation computes the
/// inverse of the last direction once and then applies the exact
/// `Theory.AdditiveNTT.friFold` equation to every pair.
pub fn fold_last_direction(
    input_word: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    challenge: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveFriError> {
    validate_round_domain(input_word, basis, offset, challenge)?;
    let half = input_word.len() / 2;
    let beta_inverse = basis
        .last()
        .copied()
        .ok_or(AdditiveFriError::NoFoldDirection)?
        .inverse()?;
    let points = transversal_points(&basis[..basis.len() - 1], offset)?;
    debug_assert_eq!(points.len(), half);

    let mut folded = Vec::with_capacity(half);
    for i in 0..half {
        let low = input_word[i];
        let high = input_word[half + i];
        let odd = low.add(high)?.mul(beta_inverse)?;
        folded.push(low.add(points[i].add(challenge)?.mul(odd)?)?);
    }
    Ok(folded)
}

/// Produce one committed full-opening reference round from novel-basis
/// coefficients.  The transform and basis validation are supplied by the fast
/// additive-NTT layer.
pub fn prove_round(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    challenge: TowerElem,
    spec: &PermSpec,
    p: u64,
) -> Result<(AdditiveFriRoundClaim, AdditiveFriRoundProof), AdditiveFriError> {
    validate_commitment_runtime(spec, p)?;
    if basis.is_empty() {
        return Err(AdditiveFriError::NoFoldDirection);
    }
    let input_word = forward(coefficients, basis, offset)?;
    let folded_word = fold_last_direction(&input_word, basis, offset, challenge)?;
    let input_root = commit_tower_word(&input_word, spec, p)?;
    let folded_root = commit_tower_word(&folded_word, spec, p)?;
    Ok((
        AdditiveFriRoundClaim {
            input_root,
            folded_root,
            input_len: input_word.len(),
            basis: basis.to_vec(),
            offset,
            challenge,
        },
        AdditiveFriRoundProof {
            input_word,
            folded_word,
        },
    ))
}

/// Fail-closed full-opening verifier for [`prove_round`].
pub fn verify_round(
    claim: &AdditiveFriRoundClaim,
    proof: &AdditiveFriRoundProof,
    spec: &PermSpec,
    p: u64,
) -> bool {
    check_round(claim, proof, spec, p).is_ok()
}

fn check_round(
    claim: &AdditiveFriRoundClaim,
    proof: &AdditiveFriRoundProof,
    spec: &PermSpec,
    p: u64,
) -> Result<(), AdditiveFriError> {
    validate_commitment_runtime(spec, p)?;
    claim
        .input_root
        .validate()
        .map_err(|_| AdditiveFriError::NonCanonicalCommitment("input"))?;
    claim
        .folded_root
        .validate()
        .map_err(|_| AdditiveFriError::NonCanonicalCommitment("folded"))?;
    if proof.input_word.len() != claim.input_len
        || proof.folded_word.len().checked_mul(2) != Some(claim.input_len)
    {
        return Err(AdditiveFriError::InvalidShape {
            input_len: proof.input_word.len(),
            folded_len: proof.folded_word.len(),
            basis_len: claim.basis.len(),
        });
    }
    validate_output_levels(&proof.folded_word, claim.offset.level())?;
    if commit_tower_word(&proof.input_word, spec, p)? != claim.input_root {
        return Err(AdditiveFriError::CommitmentMismatch("input"));
    }
    if commit_tower_word(&proof.folded_word, spec, p)? != claim.folded_root {
        return Err(AdditiveFriError::CommitmentMismatch("folded"));
    }
    if fold_last_direction(
        &proof.input_word,
        &claim.basis,
        claim.offset,
        claim.challenge,
    )? != proof.folded_word
    {
        return Err(AdditiveFriError::FoldMismatch);
    }
    Ok(())
}

fn validate_commitment_runtime(spec: &PermSpec, p: u64) -> Result<(), AdditiveFriError> {
    if p != BABY_BEAR_P {
        return Err(AdditiveFriError::UnsupportedModulus(p));
    }
    spec.validate(p)
        .map_err(AdditiveFriError::InvalidPermutation)?;
    if spec.width < 2 {
        return Err(AdditiveFriError::InvalidPermutation(
            "wide Merkle compression needs width >= 2".into(),
        ));
    }
    Ok(())
}

fn tower_leaf_digest_validated(value: TowerElem, spec: &PermSpec, p: u64) -> Digest {
    hash_fields(
        spec,
        DigestDomain::FriExtLeaf,
        &tower_element_encoding(value),
        p,
    )
}

fn validate_round_domain(
    input_word: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    challenge: TowerElem,
) -> Result<(), AdditiveFriError> {
    if basis.is_empty() {
        return Err(AdditiveFriError::NoFoldDirection);
    }
    if input_word.is_empty()
        || !input_word.len().is_power_of_two()
        || basis.len() != input_word.len().ilog2() as usize
    {
        return Err(AdditiveFriError::InvalidShape {
            input_len: input_word.len(),
            folded_len: input_word.len() / 2,
            basis_len: basis.len(),
        });
    }

    let level = offset.level();
    let dimension = 1usize << level;
    if basis.len() > dimension {
        return Err(AdditiveFriError::DomainTooLarge {
            basis_len: basis.len(),
            dimension,
        });
    }
    check_level("challenge", 0, level, challenge)?;
    for (index, value) in input_word.iter().copied().enumerate() {
        check_level("input", index, level, value)?;
    }
    for (index, value) in basis.iter().copied().enumerate() {
        check_level("basis", index, level, value)?;
    }

    // W_i(beta_i) != 0 is equivalent to beta_i escaping the preceding span.
    let mut gamma: Vec<TowerElem> = Vec::with_capacity(basis.len());
    for (i, beta) in basis.iter().copied().enumerate() {
        let mut value = beta;
        for coefficient in gamma.iter().copied() {
            value = value.square().add(coefficient.mul(value)?)?;
        }
        if value.is_zero() {
            return Err(AdditiveFriError::DependentBasis { index: i });
        }
        gamma.push(value);
    }
    Ok(())
}

fn validate_output_levels(folded_word: &[TowerElem], expected: u8) -> Result<(), AdditiveFriError> {
    for (index, value) in folded_word.iter().copied().enumerate() {
        check_level("folded", index, expected, value)?;
    }
    Ok(())
}

fn check_level(
    role: &'static str,
    index: usize,
    expected: u8,
    value: TowerElem,
) -> Result<(), AdditiveFriError> {
    if value.level() == expected {
        Ok(())
    } else {
        Err(AdditiveFriError::FieldLevelMismatch {
            role,
            index,
            expected,
            actual: value.level(),
        })
    }
}

/// Materialise `offset + span(basis)` in little-endian coefficient order.
fn transversal_points(
    basis: &[TowerElem],
    offset: TowerElem,
) -> Result<Vec<TowerElem>, AdditiveFriError> {
    let mut points = vec![offset];
    for beta in basis.iter().copied() {
        let old_len = points.len();
        for i in 0..old_len {
            points.push(points[i].add(beta)?);
        }
    }
    Ok(points)
}
