//! `[PROVER-accumulator-commit]` — the smallest honest commitment layer around
//! the executable accumulator algebra.
//!
//! [`AccClaim`] intentionally treats its root as opaque.  This module supplies
//! one reference realization: the root is the wide Merkle commitment to the
//! witness word, every word position travels with an authentication path, and
//! verification reconstructs the entire word, checks every opening, recomputes
//! the root, checks the linear channel, and directly checks two-adic
//! Reed--Solomon membership by inverse DFT.  Cross-word folding verifies both
//! input objects, folds their words and targets with the same challenge, and
//! commits the resulting word.
//!
//! That resolution is deliberately expensive: proofs contain all `n` values
//! and all `n` Merkle paths, and verification is `O(n^2)` because code
//! membership is direct.  It closes the executable root/word link without
//! pretending to be a succinct accumulator.  Collision resistance remains
//! `[COMMIT-CR]`; replacing full openings and inverse DFT with queried openings
//! plus the FRI/folding-PCS argument is `[PROVER-acc-succinct-openings]`.
//! [`commit_fold_fs`] derives the reference fold challenge after absorbing
//! both complete claims and wide roots under an accumulator-specific domain;
//! proving that runtime schedule refines the formal FS/RBR game, moving the
//! challenge to the deployed extension field, and relaxed proximity extraction
//! across a chain remain `[PROVER-acc-fs-RUST-UNVERIFIED]`,
//! `[PROVER-challenge-field-unification]`, and `[PROVER-acc-rbr-extract]`.

use core::fmt;

use crate::accumulator::{fold_claims, fold_words, AccClaim, AccError};
use crate::commit::{commit_trace, open, verify_open};
use crate::descriptor::Fp;
use crate::field4::{badd, binv, bmul, bpow, two_adic_generator, P, TWO_ADIC_BITS};
use crate::poseidon::PermSpec;
use crate::transcript::Transcript;
use crate::wide::Digest;

const ACC_FOLD_V1_TAG: Fp = 0x4143_4631; // "ACF1"
const ACC_LEFT_TAG: Fp = 0x4143_4c46; // "ACLF"
const ACC_RIGHT_TAG: Fp = 0x4143_5254; // "ACRT"
const ACC_ROW_TAG: Fp = 0x4143_5257; // "ACRW"

/// The exact two-adic RS code checked by the reference verifier:
/// evaluations on the natural-order subgroup of size `2^log_domain`, with
/// interpolating polynomial degree strictly below `degree_bound`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReferenceRsCode {
    pub log_domain: u32,
    pub degree_bound: usize,
}

/// One scalar word opening.  A reference proof carries one of these for every
/// position, in exact index order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WordOpening {
    pub index: usize,
    pub value: Fp,
    pub path: Vec<Digest>,
}

/// Full-opening proof for an [`AccClaim<Digest>`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommittedAccProof {
    pub openings: Vec<WordOpening>,
}

/// Borrowed committed input to one fold step.  Pairing the claim with its proof
/// prevents call sites from accidentally interleaving the left/right objects.
#[derive(Debug, Clone, Copy)]
pub struct CommittedAccRef<'a> {
    pub claim: &'a AccClaim<Digest>,
    pub proof: &'a CommittedAccProof,
}

/// Prover-side failures.  Verifier-side malformed data is mapped to `false`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CommittedAccError {
    Algebra(AccError),
    UnsupportedModulus(u64),
    InvalidPermutation(String),
    EmptyWord,
    InvalidCodeShape {
        log_domain: u32,
        degree_bound: usize,
        word_len: usize,
    },
    UnsatisfiedChannel,
    NotCodeword,
    InvalidInputProof(&'static str),
    TranscriptShape {
        what: &'static str,
        value: usize,
    },
}

impl fmt::Display for CommittedAccError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Algebra(err) => write!(f, "accumulator algebra: {err}"),
            Self::UnsupportedModulus(p) => {
                write!(f, "reference committed accumulator requires BabyBear, got {p}")
            }
            Self::InvalidPermutation(err) => write!(f, "invalid permutation: {err}"),
            Self::EmptyWord => write!(f, "cannot commit an empty accumulator word"),
            Self::InvalidCodeShape {
                log_domain,
                degree_bound,
                word_len,
            } => write!(
                f,
                "RS shape log_domain={log_domain}, degree_bound={degree_bound} does not match word length {word_len}"
            ),
            Self::UnsatisfiedChannel => write!(f, "word does not satisfy the claim channel"),
            Self::NotCodeword => write!(f, "word is not in the claimed reference RS code"),
            Self::InvalidInputProof(side) => write!(f, "{side} committed input proof rejects"),
            Self::TranscriptShape { what, value } => {
                write!(f, "{what} value {value} does not fit one BabyBear transcript element")
            }
        }
    }
}

impl std::error::Error for CommittedAccError {}

impl From<AccError> for CommittedAccError {
    fn from(value: AccError) -> Self {
        Self::Algebra(value)
    }
}

fn validate_runtime(spec: &PermSpec, p: u64) -> Result<(), CommittedAccError> {
    if p != P {
        return Err(CommittedAccError::UnsupportedModulus(p));
    }
    spec.validate(p)
        .map_err(CommittedAccError::InvalidPermutation)?;
    if spec.width < 2 {
        return Err(CommittedAccError::InvalidPermutation(
            "Merkle compression needs width >= 2".into(),
        ));
    }
    Ok(())
}

fn transcript_len(what: &'static str, value: usize, p: u64) -> Result<Fp, CommittedAccError> {
    if (value as u128) < p as u128 {
        Ok(value as Fp)
    } else {
        Err(CommittedAccError::TranscriptShape { what, value })
    }
}

fn absorb_claim(
    transcript: &mut Transcript,
    side_tag: Fp,
    claim: &AccClaim<Digest>,
    p: u64,
) -> Result<(), CommittedAccError> {
    claim.validate(p)?;
    claim
        .root
        .validate()
        .map_err(|_| CommittedAccError::InvalidInputProof("noncanonical root"))?;
    transcript.absorb(&[
        side_tag,
        transcript_len("word length", claim.word_len, p)?,
        transcript_len("channel length", claim.channel.len(), p)?,
    ]);
    transcript.absorb_digest(side_tag, &claim.root);
    for (row, constraint) in claim.channel.iter().enumerate() {
        transcript.absorb(&[
            ACC_ROW_TAG,
            transcript_len("channel row", row, p)?,
            constraint.target,
        ]);
        transcript.absorb(&constraint.weights);
    }
    Ok(())
}

/// Derive one base-BabyBear fold challenge after binding both complete input
/// claims and roots under the accumulator-fold transcript domain.
///
/// This removes a caller-controlled challenge from the reference API.  It is
/// not a 137-bit security claim: the current duplex permutation is a demo and
/// the returned scalar is still one base-field element.
pub fn derive_fold_challenge(
    left: &AccClaim<Digest>,
    right: &AccClaim<Digest>,
    spec: &PermSpec,
    p: u64,
) -> Result<Fp, CommittedAccError> {
    validate_runtime(spec, p)?;
    let mut transcript = Transcript::new(spec.clone(), p);
    transcript.absorb(&[ACC_FOLD_V1_TAG]);
    absorb_claim(&mut transcript, ACC_LEFT_TAG, left, p)?;
    absorb_claim(&mut transcript, ACC_RIGHT_TAG, right, p)?;
    Ok(transcript.squeeze_challenge())
}

fn validate_code(code: ReferenceRsCode, word_len: usize) -> Result<(), CommittedAccError> {
    let expected_len =
        1usize
            .checked_shl(code.log_domain)
            .ok_or(CommittedAccError::InvalidCodeShape {
                log_domain: code.log_domain,
                degree_bound: code.degree_bound,
                word_len,
            })?;
    if code.log_domain > TWO_ADIC_BITS || expected_len != word_len || code.degree_bound > word_len {
        return Err(CommittedAccError::InvalidCodeShape {
            log_domain: code.log_domain,
            degree_bound: code.degree_bound,
            word_len,
        });
    }
    Ok(())
}

/// Direct reference RS-membership check by inverse DFT.
///
/// For `word[j] = polynomial(g^j)`, coefficient `k` is
/// `n^-1 * sum_j word[j] * g^(-j*k)`.  Membership is exactly the vanishing of
/// every coefficient at `k >= degree_bound`.  Full rate (`degree_bound = n`)
/// accepts every word; bound zero accepts only the zero word.
pub fn reference_rs_contains(
    word: &[Fp],
    code: ReferenceRsCode,
    p: u64,
) -> Result<bool, CommittedAccError> {
    if p != P {
        return Err(CommittedAccError::UnsupportedModulus(p));
    }
    if word.is_empty() || word.iter().any(|&value| value >= p) {
        return Err(CommittedAccError::InvalidCodeShape {
            log_domain: code.log_domain,
            degree_bound: code.degree_bound,
            word_len: word.len(),
        });
    }
    validate_code(code, word.len())?;
    if code.degree_bound == word.len() {
        return Ok(true);
    }

    let n_inv = binv(word.len() as Fp);
    let g_inv = binv(two_adic_generator(code.log_domain));
    for k in code.degree_bound..word.len() {
        let step = bpow(g_inv, k as u64);
        let mut power = 1;
        let mut sum = 0;
        for &value in word {
            sum = badd(sum, bmul(value, power));
            power = bmul(power, step);
        }
        if bmul(sum, n_inv) != 0 {
            return Ok(false);
        }
    }
    Ok(true)
}

fn proof_from_tree(word: &[Fp], tree: &crate::commit::MerkleTree) -> CommittedAccProof {
    CommittedAccProof {
        openings: word
            .iter()
            .enumerate()
            .map(|(index, &value)| WordOpening {
                index,
                value,
                path: open(tree, index),
            })
            .collect(),
    }
}

/// Bind an algebraic claim to one full word and produce the full-opening
/// reference proof.  The honest prover refuses an unsatisfied channel or a word
/// outside the supplied RS code.
pub fn commit_claim<Root>(
    claim: &AccClaim<Root>,
    word: &[Fp],
    code: ReferenceRsCode,
    spec: &PermSpec,
    p: u64,
) -> Result<(AccClaim<Digest>, CommittedAccProof), CommittedAccError> {
    validate_runtime(spec, p)?;
    if word.is_empty() {
        return Err(CommittedAccError::EmptyWord);
    }
    if !claim.channel_satisfied_by(word, p)? {
        return Err(CommittedAccError::UnsatisfiedChannel);
    }
    validate_code(code, word.len())?;
    if !reference_rs_contains(word, code, p)? {
        return Err(CommittedAccError::NotCodeword);
    }
    let (root, tree) = commit_trace(spec, word, p);
    let bound = AccClaim {
        root,
        word_len: claim.word_len,
        channel: claim.channel.clone(),
    };
    Ok((bound, proof_from_tree(word, &tree)))
}

fn checked_word(
    claim: &AccClaim<Digest>,
    proof: &CommittedAccProof,
    code: ReferenceRsCode,
    spec: &PermSpec,
    p: u64,
) -> Option<Vec<Fp>> {
    validate_runtime(spec, p).ok()?;
    claim.validate(p).ok()?;
    claim.root.validate().ok()?;
    if claim.word_len == 0 || validate_code(code, claim.word_len).is_err() {
        return None;
    }
    let height = claim.word_len.next_power_of_two().trailing_zeros() as usize;
    if proof.openings.len() != claim.word_len {
        return None;
    }

    let mut word = Vec::with_capacity(claim.word_len);
    for (expected_index, opening) in proof.openings.iter().enumerate() {
        if opening.index != expected_index
            || opening.value >= p
            || opening.path.len() != height
            || !verify_open(
                claim.root,
                opening.index,
                opening.value,
                &opening.path,
                spec,
                p,
            )
        {
            return None;
        }
        word.push(opening.value);
    }

    // At this non-succinct resolution, recomputation pins the exact tree shape
    // (including domain-separated padding), while the paths independently
    // exercise the opening verifier on every position.
    if commit_trace(spec, &word, p).0 != claim.root {
        return None;
    }
    if !claim.channel_satisfied_by(&word, p).ok()? {
        return None;
    }
    if !reference_rs_contains(&word, code, p).ok()? {
        return None;
    }
    Some(word)
}

/// Fail-closed verifier for the reference committed claim.
pub fn verify_committed_claim(
    claim: &AccClaim<Digest>,
    proof: &CommittedAccProof,
    code: ReferenceRsCode,
    spec: &PermSpec,
    p: u64,
) -> bool {
    checked_word(claim, proof, code, spec, p).is_some()
}

/// Verify two committed claims, perform Loom's shared-channel cross-word fold,
/// and commit the folded word. This low-level algebra entry point takes an
/// explicit challenge; protocol callers should use [`commit_fold_fs`], which
/// derives it after binding both complete claims.
pub fn commit_fold(
    left: CommittedAccRef<'_>,
    right: CommittedAccRef<'_>,
    gamma: Fp,
    code: ReferenceRsCode,
    spec: &PermSpec,
    p: u64,
) -> Result<(AccClaim<Digest>, CommittedAccProof), CommittedAccError> {
    let left_word = checked_word(left.claim, left.proof, code, spec, p)
        .ok_or(CommittedAccError::InvalidInputProof("left"))?;
    let right_word = checked_word(right.claim, right.proof, code, spec, p)
        .ok_or(CommittedAccError::InvalidInputProof("right"))?;
    let folded_word = fold_words(&left_word, &right_word, gamma, p)?;
    let (folded_root, tree) = commit_trace(spec, &folded_word, p);
    let folded_claim = fold_claims(folded_root, left.claim, right.claim, gamma, p)?;

    // This is redundant given linear closure and RS linearity, intentionally:
    // the reference prover refuses rather than relying on a Rust-level theorem.
    if !folded_claim.channel_satisfied_by(&folded_word, p)? {
        return Err(CommittedAccError::UnsatisfiedChannel);
    }
    if !reference_rs_contains(&folded_word, code, p)? {
        return Err(CommittedAccError::NotCodeword);
    }
    Ok((folded_claim, proof_from_tree(&folded_word, &tree)))
}

/// Fiat--Shamir reference wrapper for [`commit_fold`].
///
/// The challenge is derived only after the transcript has absorbed both full
/// claims, including their wide roots, word shape, weights, and targets.  The
/// returned challenge is exposed for conformance and verifier replay; callers
/// never supply it.
pub fn commit_fold_fs(
    left: CommittedAccRef<'_>,
    right: CommittedAccRef<'_>,
    code: ReferenceRsCode,
    spec: &PermSpec,
    p: u64,
) -> Result<(Fp, AccClaim<Digest>, CommittedAccProof), CommittedAccError> {
    let gamma = derive_fold_challenge(left.claim, right.claim, spec, p)?;
    let (claim, proof) = commit_fold(left, right, gamma, code, spec, p)?;
    Ok((gamma, claim, proof))
}
