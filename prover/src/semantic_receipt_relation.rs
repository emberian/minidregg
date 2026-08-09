//! Executable reference for the clean-sheet semantic receipt relation.
//!
//! This mirrors `Assurance/SemanticReceiptRelation.lean` at full-opening
//! resolution.  One word begins with sixteen u16 cells carrying a canonical
//! 32-byte typed-receipt binding, followed by key-major
//! `[pre, post, touched]`; touched values are Boolean and
//! `(1-touched) * (post-pre) = 0` at every key.  The word is lifted
//! canonically into BabyBear⁶, committed with the binary cSHAKE Merkle
//! suite, converted to the field-generic runtime `AccClaim` with one shared
//! coordinate-evaluation row per cell, and folded at one atomic Ext6 challenge
//! derived only after both roots are fixed.
//!
//! This is a real root-linked linear fold, but deliberately exhaustive: the
//! verifier receives both semantic words and recomputes their commitments.
//! It does not yet prove code membership, proximity, or WARP extraction.  The
//! succinct replacement remains `[PCH-OUTER-ACCUMULATOR]`. This module is
//! unverified compute/conformance code, not a refinement; authoritative codec
//! and verifier control must be emitted from Lean.

use core::fmt;

use crate::{
    accumulator_generic::{
        fold_claims, fold_words, FieldAccClaim, FieldAccError, FieldLinearConstraint,
    },
    binary_hash::{BinaryHashDomain, BinaryRoot, BinaryShake256V1},
    binary_merkle::{BinaryMerkleError, BinaryMerkleTree},
    field4::P,
    field6::{Ext6, Ext6Error},
    semantic_receipt::SemanticId,
    transcript_ext6::{BinaryShakeExt6Backend, Ext6Transcript, Ext6TranscriptError},
};

const LEAF_TAG: &[u8; 4] = b"SRX1";
const DATA_FRAME: u8 = 1;
const PADDING_FRAME: u8 = 2;
const FOLD_PROTOCOL: &[u8] = b"minidregg/semantic-receipt/ext6-fold/v1";
const FOLD_META_DOMAIN: u64 = 0x5352_4d54; // "SRMT"
const FOLD_LEFT_ROOT_DOMAIN: u64 = 0x5352_4c52; // "SRLR"
const FOLD_RIGHT_ROOT_DOMAIN: u64 = 0x5352_5252; // "SRRR"
const FOLD_GAMMA_DOMAIN: u64 = 0x5352_4741; // "SRGA"

/// Canonical key-major semantic word.  All vectors have the same positive
/// length; values are canonical BabyBear representatives.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticReceiptWord {
    /// Digest of the complete typed request/outcome/native-clause header.
    pub binding: SemanticId,
    pub pre: Vec<u64>,
    pub post: Vec<u64>,
    pub touched: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CommittedSemanticReceipt {
    pub word: SemanticReceiptWord,
    pub root: BinaryRoot,
    pub claim: FieldAccClaim<BinaryRoot, Ext6>,
}

/// A folded accumulator word is not itself required to decode as one receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldedSemanticAccumulator {
    pub word: Vec<Ext6>,
    pub root: BinaryRoot,
    pub claim: FieldAccClaim<BinaryRoot, Ext6>,
    pub gamma: Ext6,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticReceiptRelationError {
    Empty,
    EmptyBinding,
    Shape {
        pre: usize,
        post: usize,
        touched: usize,
    },
    NonCanonical {
        section: &'static str,
        index: usize,
        value: u64,
    },
    NonBooleanTouched {
        index: usize,
        value: u64,
    },
    FrameViolation {
        index: usize,
    },
    CommitmentMismatch,
    ClaimMismatch,
    FoldClosureFailed,
    LengthOverflow,
    Accumulator(FieldAccError),
    Merkle(BinaryMerkleError),
    Extension(Ext6Error),
    Transcript(Ext6TranscriptError),
}

impl From<FieldAccError> for SemanticReceiptRelationError {
    fn from(value: FieldAccError) -> Self {
        Self::Accumulator(value)
    }
}

impl From<BinaryMerkleError> for SemanticReceiptRelationError {
    fn from(value: BinaryMerkleError) -> Self {
        Self::Merkle(value)
    }
}

impl From<Ext6Error> for SemanticReceiptRelationError {
    fn from(value: Ext6Error) -> Self {
        Self::Extension(value)
    }
}

impl From<Ext6TranscriptError> for SemanticReceiptRelationError {
    fn from(value: Ext6TranscriptError) -> Self {
        Self::Transcript(value)
    }
}

impl fmt::Display for SemanticReceiptRelationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => write!(f, "semantic receipt has no keys"),
            Self::EmptyBinding => write!(f, "semantic receipt binding is all zero"),
            Self::Shape { pre, post, touched } => write!(
                f,
                "semantic receipt shape differs: pre={pre}, post={post}, touched={touched}"
            ),
            Self::NonCanonical {
                section,
                index,
                value,
            } => write!(f, "{section}[{index}]={value} is not canonical BabyBear"),
            Self::NonBooleanTouched { index, value } => {
                write!(f, "touched[{index}]={value} is not Boolean")
            }
            Self::FrameViolation { index } => {
                write!(f, "untouched semantic cell {index} changed")
            }
            Self::CommitmentMismatch => write!(f, "semantic receipt root does not commit its word"),
            Self::ClaimMismatch => write!(f, "semantic receipt accumulator claim is not canonical"),
            Self::FoldClosureFailed => write!(f, "folded claim does not accept the folded word"),
            Self::LengthOverflow => write!(f, "semantic receipt length arithmetic overflow"),
            Self::Accumulator(error) => error.fmt(f),
            Self::Merkle(error) => error.fmt(f),
            Self::Extension(error) => {
                write!(f, "non-canonical Ext6 lane {}: {}", error.lane, error.value)
            }
            Self::Transcript(error) => error.fmt(f),
        }
    }
}

impl std::error::Error for SemanticReceiptRelationError {}

impl SemanticReceiptWord {
    pub fn validate(&self) -> Result<(), SemanticReceiptRelationError> {
        if self.binding.iter().all(|byte| *byte == 0) {
            return Err(SemanticReceiptRelationError::EmptyBinding);
        }
        let n = self.pre.len();
        if n == 0 {
            return Err(SemanticReceiptRelationError::Empty);
        }
        if self.post.len() != n || self.touched.len() != n {
            return Err(SemanticReceiptRelationError::Shape {
                pre: n,
                post: self.post.len(),
                touched: self.touched.len(),
            });
        }
        validate_section("pre", &self.pre)?;
        validate_section("post", &self.post)?;
        validate_section("touched", &self.touched)?;
        for (index, ((&pre, &post), &touched)) in self
            .pre
            .iter()
            .zip(&self.post)
            .zip(&self.touched)
            .enumerate()
        {
            if touched > 1 {
                return Err(SemanticReceiptRelationError::NonBooleanTouched {
                    index,
                    value: touched,
                });
            }
            if touched == 0 && post != pre {
                return Err(SemanticReceiptRelationError::FrameViolation { index });
            }
        }
        Ok(())
    }

    /// Exact runtime order: sixteen little-endian u16 binding cells followed
    /// by `(Key × ReceiptSlot)` in key-major `pre, post, touched` order.
    pub fn encode_word(&self) -> Result<Vec<u64>, SemanticReceiptRelationError> {
        self.validate()?;
        let mut word = Vec::with_capacity(
            self.pre
                .len()
                .checked_mul(3)
                .and_then(|length| length.checked_add(16))
                .ok_or(SemanticReceiptRelationError::LengthOverflow)?,
        );
        word.extend(
            self.binding
                .chunks_exact(2)
                .map(|chunk| u16::from_le_bytes([chunk[0], chunk[1]]) as u64),
        );
        for ((&pre, &post), &touched) in self.pre.iter().zip(&self.post).zip(&self.touched) {
            word.extend([pre, post, touched]);
        }
        Ok(word)
    }

    /// The literal two residuals in `ReceiptWitness.residual`.
    pub fn quadratic_residuals(&self) -> Result<Vec<[u64; 2]>, SemanticReceiptRelationError> {
        self.validate()?;
        Ok(self
            .pre
            .iter()
            .zip(&self.post)
            .zip(&self.touched)
            .map(|((&pre, &post), &touched)| {
                let boolean = mul_mod(touched, sub_mod(touched, 1));
                let frame = mul_mod(sub_mod(1, touched), sub_mod(post, pre));
                [boolean, frame]
            })
            .collect())
    }
}

/// Commit and bind one valid semantic receipt at exhaustive reference
/// resolution.
pub fn commit_semantic_receipt(
    word: SemanticReceiptWord,
) -> Result<CommittedSemanticReceipt, SemanticReceiptRelationError> {
    let encoded = word.encode_word()?;
    let lifted = lift_word(&encoded)?;
    let root = commit_accumulator_word(&lifted)?;
    let claim = coordinate_claim(root, &lifted)?;
    Ok(CommittedSemanticReceipt { word, root, claim })
}

/// Fail-closed full-reference verification of one semantic relation object.
pub fn verify_committed_semantic_receipt(
    receipt: &CommittedSemanticReceipt,
) -> Result<bool, SemanticReceiptRelationError> {
    let encoded = receipt.word.encode_word()?;
    let lifted = lift_word(&encoded)?;
    if commit_accumulator_word(&lifted)? != receipt.root {
        return Ok(false);
    }
    let expected = coordinate_claim(receipt.root, &lifted)?;
    if receipt.claim != expected {
        return Ok(false);
    }
    receipt
        .claim
        .channel_satisfied_by(&lifted)
        .map_err(Into::into)
}

/// Atomic security-field challenge derived after both committed inputs and the
/// exact shared word shape have been absorbed.
pub fn derive_semantic_receipt_fold_challenge(
    left: &CommittedSemanticReceipt,
    right: &CommittedSemanticReceipt,
) -> Result<Ext6, SemanticReceiptRelationError> {
    if left.claim.word_len != right.claim.word_len {
        return Err(FieldAccError::WordWidth {
            expected: left.claim.word_len,
            actual: right.claim.word_len,
        }
        .into());
    }
    let backend = BinaryShakeExt6Backend::new(FOLD_PROTOCOL);
    let mut transcript = Ext6Transcript::new(backend)?;
    let word_len = u64::try_from(left.claim.word_len)
        .map_err(|_| SemanticReceiptRelationError::LengthOverflow)?;
    if word_len >= P {
        return Err(SemanticReceiptRelationError::LengthOverflow);
    }
    transcript.absorb_record(FOLD_META_DOMAIN, &[1, word_len])?;
    transcript.absorb_record(FOLD_LEFT_ROOT_DOMAIN, &root_as_u16_fields(&left.root))?;
    transcript.absorb_record(FOLD_RIGHT_ROOT_DOMAIN, &root_as_u16_fields(&right.root))?;
    Ok(transcript.squeeze_ext6(FOLD_GAMMA_DOMAIN)?)
}

/// One real root-linked execution of Loom's cross-word linear fold.  Both
/// semantic inputs are reverified; the folded word is recommitted and checked
/// against the folded channel.
pub fn fold_semantic_receipts(
    left: &CommittedSemanticReceipt,
    right: &CommittedSemanticReceipt,
) -> Result<FoldedSemanticAccumulator, SemanticReceiptRelationError> {
    if !verify_committed_semantic_receipt(left)? || !verify_committed_semantic_receipt(right)? {
        return Err(SemanticReceiptRelationError::CommitmentMismatch);
    }
    let left_word = lift_word(&left.word.encode_word()?)?;
    let right_word = lift_word(&right.word.encode_word()?)?;
    let gamma = derive_semantic_receipt_fold_challenge(left, right)?;
    let word = fold_words(&left_word, &right_word, gamma)?;
    let root = commit_accumulator_word(&word)?;
    let claim = fold_claims(root, &left.claim, &right.claim, gamma)?;
    if !claim.channel_satisfied_by(&word)? {
        return Err(SemanticReceiptRelationError::FoldClosureFailed);
    }
    Ok(FoldedSemanticAccumulator {
        word,
        root,
        claim,
        gamma,
    })
}

pub fn verify_folded_semantic_accumulator(
    left: &CommittedSemanticReceipt,
    right: &CommittedSemanticReceipt,
    accumulator: &FoldedSemanticAccumulator,
) -> Result<bool, SemanticReceiptRelationError> {
    if !verify_committed_semantic_receipt(left)? || !verify_committed_semantic_receipt(right)? {
        return Ok(false);
    }
    let expected_gamma = derive_semantic_receipt_fold_challenge(left, right)?;
    if accumulator.gamma != expected_gamma {
        return Ok(false);
    }
    if commit_accumulator_word(&accumulator.word)? != accumulator.root
        || accumulator.claim.root != accumulator.root
    {
        return Ok(false);
    }
    let expected_word = fold_words(
        &lift_word(&left.word.encode_word()?)?,
        &lift_word(&right.word.encode_word()?)?,
        expected_gamma,
    )?;
    let expected_claim = fold_claims(accumulator.root, &left.claim, &right.claim, expected_gamma)?;
    if accumulator.word != expected_word || accumulator.claim != expected_claim {
        return Ok(false);
    }
    accumulator
        .claim
        .channel_satisfied_by(&accumulator.word)
        .map_err(Into::into)
}

fn validate_section(
    section: &'static str,
    values: &[u64],
) -> Result<(), SemanticReceiptRelationError> {
    for (index, &value) in values.iter().enumerate() {
        if value >= P {
            return Err(SemanticReceiptRelationError::NonCanonical {
                section,
                index,
                value,
            });
        }
    }
    Ok(())
}

fn coordinate_claim(
    root: BinaryRoot,
    word: &[Ext6],
) -> Result<FieldAccClaim<BinaryRoot, Ext6>, SemanticReceiptRelationError> {
    let mut channel = Vec::with_capacity(word.len());
    for (index, &target) in word.iter().enumerate() {
        let mut weights = vec![Ext6::ZERO; word.len()];
        weights[index] = Ext6::ONE;
        channel.push(FieldLinearConstraint { weights, target });
    }
    let claim = FieldAccClaim {
        root,
        word_len: word.len(),
        channel,
    };
    claim.validate()?;
    Ok(claim)
}

fn commit_accumulator_word(word: &[Ext6]) -> Result<BinaryRoot, SemanticReceiptRelationError> {
    if word.is_empty() {
        return Err(SemanticReceiptRelationError::Empty);
    }
    let leaf_count = word
        .len()
        .checked_next_power_of_two()
        .ok_or(SemanticReceiptRelationError::LengthOverflow)?;
    let logical_len =
        u64::try_from(word.len()).map_err(|_| SemanticReceiptRelationError::LengthOverflow)?;
    let mut payloads = Vec::with_capacity(leaf_count);
    for (index, value) in word.iter().enumerate() {
        let mut payload = LEAF_TAG.to_vec();
        payload.push(DATA_FRAME);
        payload.extend_from_slice(&logical_len.to_le_bytes());
        payload.extend_from_slice(&(index as u64).to_le_bytes());
        for limb in value.limbs() {
            payload.extend_from_slice(&limb.to_le_bytes());
        }
        payloads.push(payload);
    }
    for index in word.len()..leaf_count {
        let mut payload = LEAF_TAG.to_vec();
        payload.push(PADDING_FRAME);
        payload.extend_from_slice(&logical_len.to_le_bytes());
        payload.extend_from_slice(&(index as u64).to_le_bytes());
        payloads.push(payload);
    }
    Ok(
        BinaryMerkleTree::build(&BinaryShake256V1, BinaryHashDomain::Accumulator, &payloads)?
            .root(),
    )
}

fn lift_word(word: &[u64]) -> Result<Vec<Ext6>, SemanticReceiptRelationError> {
    word.iter()
        .copied()
        .map(|value| Ext6::try_from_base(value).map_err(Into::into))
        .collect()
}

fn root_as_u16_fields(root: &BinaryRoot) -> Vec<u64> {
    root.as_bytes()
        .chunks_exact(2)
        .map(|chunk| u16::from_le_bytes([chunk[0], chunk[1]]) as u64)
        .collect()
}

#[inline]
fn sub_mod(left: u64, right: u64) -> u64 {
    if left >= right {
        left - right
    } else {
        P - (right - left)
    }
}

#[inline]
fn mul_mod(left: u64, right: u64) -> u64 {
    ((left as u128 * right as u128) % P as u128) as u64
}
