//! Evaluation-channel retirement for one binary history append.
//!
//! The two input claims are treated as previously authenticated.  This join
//! verifies the existing sampled append, then verifies a standalone sampled OOD
//! opening for the append's exact output root, target, degree bound, domain, and
//! evaluation point.  Thus the output again is an authenticated evaluation
//! claim and proof size does not grow with history depth.
//!
//! The append and OOD protocols retain their existing, separate transcripts.
//! Their composition seam is equality of all output-claim metadata; no shared
//! random-oracle execution is claimed here.  The append-owned challenge API
//! supplies gamma for the folded coefficient witness, so this join does not
//! duplicate the private root-before-gamma schedule.

use core::fmt;

use crate::{
    additive_pcs_ood::AdditivePcsOodError,
    binary_evaluation_claim::{
        evaluation_channel_id, prove_evaluation_claim, verify_evaluation_claim,
        BinaryEvaluationClaimProof, BinaryEvaluationClaimStatement,
    },
    binary_history_append::{
        derive_binary_history_append_challenge, prove_binary_history_append,
        verify_binary_history_append, BinaryAdditiveRsClaim, BinaryHistoryAppendError,
        BinaryHistoryAppendProof, BinaryHistoryAppendStatement,
    },
    binary_tower::{TowerElem, TowerError, MAX_LEVEL},
};

/// Two previously authenticated evaluation statements.  Keeping their full
/// metadata here lets this join enforce equality of point, channel, affine
/// domain, coefficient bound, and query profile before deriving the append.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryEvaluationHistoryAppendStatement {
    pub left: BinaryEvaluationClaimStatement,
    pub right: BinaryEvaluationClaimStatement,
}

/// One sampled append plus one sampled OOD opening for its output claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryEvaluationHistoryAppendProof {
    pub append: BinaryHistoryAppendProof,
    pub output_evaluation: BinaryEvaluationClaimProof,
}

impl BinaryEvaluationHistoryAppendProof {
    pub fn output_claim(&self) -> &BinaryAdditiveRsClaim {
        &self.append.output_claim
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryEvaluationHistoryAppendError {
    Append(BinaryHistoryAppendError),
    Ood(AdditivePcsOodError),
    Tower(TowerError),
    InvalidEvaluationMetadata,
    OutputEvaluationMismatch,
}

impl From<BinaryHistoryAppendError> for BinaryEvaluationHistoryAppendError {
    fn from(value: BinaryHistoryAppendError) -> Self {
        Self::Append(value)
    }
}

impl From<AdditivePcsOodError> for BinaryEvaluationHistoryAppendError {
    fn from(value: AdditivePcsOodError) -> Self {
        Self::Ood(value)
    }
}

impl From<TowerError> for BinaryEvaluationHistoryAppendError {
    fn from(value: TowerError) -> Self {
        Self::Tower(value)
    }
}

impl fmt::Display for BinaryEvaluationHistoryAppendError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Append(error) => error.fmt(f),
            Self::Ood(error) => error.fmt(f),
            Self::Tower(error) => error.fmt(f),
            Self::InvalidEvaluationMetadata => {
                write!(
                    f,
                    "binary append inputs are not one common evaluation channel"
                )
            }
            Self::OutputEvaluationMismatch => {
                write!(f, "output OOD claim does not equal the append output claim")
            }
        }
    }
}

impl std::error::Error for BinaryEvaluationHistoryAppendError {}

/// Prove an append and re-authenticate its output in the fixed OOD-evaluation
/// channel.  Input claim proofs are deliberately absent: callers authenticate
/// them before invoking this history step.
#[allow(clippy::too_many_arguments)]
pub fn prove_binary_evaluation_history_append(
    statement: &BinaryEvaluationHistoryAppendStatement,
    left_word: &[TowerElem],
    left_coefficients: &[TowerElem],
    right_word: &[TowerElem],
    right_coefficients: &[TowerElem],
) -> Result<BinaryEvaluationHistoryAppendProof, BinaryEvaluationHistoryAppendError> {
    validate_evaluation_metadata(statement)?;
    let append_statement = derive_append_statement(statement);
    let (gamma, _) = derive_binary_history_append_challenge(&append_statement)?;
    let append = prove_binary_history_append(
        &append_statement,
        left_word,
        left_coefficients,
        right_word,
        right_coefficients,
    )?;

    if left_coefficients.len() != right_coefficients.len() {
        return Err(BinaryEvaluationHistoryAppendError::InvalidEvaluationMetadata);
    }
    let folded_coefficients = left_coefficients
        .iter()
        .copied()
        .zip(right_coefficients.iter().copied())
        .map(|(left, right)| left.add(gamma.mul(right)?).map_err(Into::into))
        .collect::<Result<Vec<_>, BinaryEvaluationHistoryAppendError>>()?;
    let coefficient_bound = usize::try_from(append.output_claim.coefficient_bound)
        .map_err(|_| BinaryEvaluationHistoryAppendError::InvalidEvaluationMetadata)?;
    let (output_statement, output_evaluation) = prove_evaluation_claim(
        &folded_coefficients,
        &statement.left.basis,
        statement.left.offset,
        coefficient_bound,
        statement.left.evaluation_point,
        statement.left.num_queries,
    )?;
    if output_statement.claim != append.output_claim {
        return Err(BinaryEvaluationHistoryAppendError::OutputEvaluationMismatch);
    }
    Ok(BinaryEvaluationHistoryAppendProof {
        append,
        output_evaluation,
    })
}

/// Verify the append recurrence and an OOD opening built from the append's own
/// output claim.  The proof cannot substitute a self-consistent unrelated OOD
/// statement because no OOD statement is carried by the proof.
pub fn verify_binary_evaluation_history_append(
    statement: &BinaryEvaluationHistoryAppendStatement,
    proof: &BinaryEvaluationHistoryAppendProof,
) -> bool {
    if validate_evaluation_metadata(statement).is_err() {
        return false;
    }
    let append_statement = derive_append_statement(statement);
    if !verify_binary_history_append(&append_statement, &proof.append) {
        return false;
    }
    let output_statement =
        output_evaluation_statement(statement, proof.append.output_claim.clone());
    verify_evaluation_claim(&output_statement, &proof.output_evaluation)
}

fn output_evaluation_statement(
    statement: &BinaryEvaluationHistoryAppendStatement,
    claim: BinaryAdditiveRsClaim,
) -> BinaryEvaluationClaimStatement {
    BinaryEvaluationClaimStatement {
        claim,
        basis: statement.left.basis.clone(),
        offset: statement.left.offset,
        evaluation_point: statement.left.evaluation_point,
        num_queries: statement.left.num_queries,
    }
}

fn derive_append_statement(
    statement: &BinaryEvaluationHistoryAppendStatement,
) -> BinaryHistoryAppendStatement {
    BinaryHistoryAppendStatement {
        left: statement.left.claim.clone(),
        right: statement.right.claim.clone(),
        basis: statement.left.basis.clone(),
        offset: statement.left.offset,
        num_queries: statement.left.num_queries,
    }
}

fn validate_evaluation_metadata(
    statement: &BinaryEvaluationHistoryAppendStatement,
) -> Result<(), BinaryEvaluationHistoryAppendError> {
    let left = &statement.left;
    let right = &statement.right;
    let channel = evaluation_channel_id(left.evaluation_point);
    if left.evaluation_point.level() != MAX_LEVEL
        || left.offset.level() != MAX_LEVEL
        || left.basis.is_empty()
        || left.num_queries == 0
        || left
            .basis
            .iter()
            .any(|element| element.level() != MAX_LEVEL)
        || left.basis != right.basis
        || left.offset != right.offset
        || left.evaluation_point != right.evaluation_point
        || left.num_queries != right.num_queries
        || left.claim.channel_id != channel
        || right.claim.channel_id != channel
        || left.claim.coefficient_bound == 0
        || left.claim.coefficient_bound != right.claim.coefficient_bound
        || left.claim.target.level() != MAX_LEVEL
        || right.claim.target.level() != MAX_LEVEL
    {
        return Err(BinaryEvaluationHistoryAppendError::InvalidEvaluationMetadata);
    }
    let word_len = 1usize
        .checked_shl(left.basis.len() as u32)
        .ok_or(BinaryEvaluationHistoryAppendError::InvalidEvaluationMetadata)?;
    let bound = usize::try_from(left.claim.coefficient_bound)
        .map_err(|_| BinaryEvaluationHistoryAppendError::InvalidEvaluationMetadata)?;
    if bound > word_len {
        return Err(BinaryEvaluationHistoryAppendError::InvalidEvaluationMetadata);
    }
    Ok(())
}
