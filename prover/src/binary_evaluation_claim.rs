//! Evaluation-channel claims for the binary proof-carrying-history path.
//!
//! A claim says that a committed additive-RS word has bounded novel-basis
//! degree and evaluates to `target` at one out-of-domain point. The channel ID
//! is the full 48-byte binary-suite hash of that point. The sampled quotient
//! opening discharges the claim without carrying the word.
//!
//! This is the concrete evaluation-functional regime of the accumulator's
//! linear channel. Arbitrary weight vectors remain
//! `[BINARY-PCS-general-linear-retirement]`.

use crate::{
    additive_fri_sampled::tower_leaf_payload,
    additive_pcs_ood::{
        evaluate_novel_polynomial, prove_ood, verify_ood, AdditivePcsOodProof,
        AdditivePcsOodStatement,
    },
    binary_hash::{BinaryHashDomain, BinaryShake256V1, HashSuite},
    binary_history_append::{BinaryAdditiveRsClaim, BinaryChannelId},
    binary_tower::TowerElem,
};

const EVALUATION_CHANNEL_TAG: &[u8] = b"minidregg/evaluation-channel/v1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryEvaluationClaimStatement {
    pub claim: BinaryAdditiveRsClaim,
    pub basis: Vec<TowerElem>,
    pub offset: TowerElem,
    pub evaluation_point: TowerElem,
    pub num_queries: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryEvaluationClaimProof {
    pub opening: AdditivePcsOodProof,
}

/// Full-width semantic identifier for evaluation at `point`.
pub fn evaluation_channel_id(point: TowerElem) -> BinaryChannelId {
    let mut payload = Vec::with_capacity(EVALUATION_CHANNEL_TAG.len() + 13);
    payload.extend_from_slice(EVALUATION_CHANNEL_TAG);
    payload.extend_from_slice(&tower_leaf_payload(point));
    BinaryChannelId::from_bytes(
        BinaryShake256V1
            .hash_leaf(BinaryHashDomain::Accumulator, 0, &payload)
            .into_bytes(),
    )
}

/// Create and prove one evaluation-channel claim from novel-basis coefficients.
pub fn prove_evaluation_claim(
    coefficients: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    coefficient_bound: usize,
    evaluation_point: TowerElem,
    num_queries: usize,
) -> Result<
    (BinaryEvaluationClaimStatement, BinaryEvaluationClaimProof),
    crate::additive_pcs_ood::AdditivePcsOodError,
> {
    let target = evaluate_novel_polynomial(coefficients, basis, evaluation_point)?;
    let (opening_statement, opening) = prove_ood(
        coefficients,
        basis,
        offset,
        coefficient_bound,
        evaluation_point,
        target,
        num_queries,
    )?;
    Ok((
        BinaryEvaluationClaimStatement {
            claim: BinaryAdditiveRsClaim {
                root: opening_statement.evaluation_root,
                coefficient_bound: coefficient_bound as u64,
                channel_id: evaluation_channel_id(evaluation_point),
                target,
            },
            basis: basis.to_vec(),
            offset,
            evaluation_point,
            num_queries,
        },
        BinaryEvaluationClaimProof { opening },
    ))
}

/// Verify the degree bound and evaluation target represented by one claim.
pub fn verify_evaluation_claim(
    statement: &BinaryEvaluationClaimStatement,
    proof: &BinaryEvaluationClaimProof,
) -> bool {
    let Ok(coefficient_bound) = usize::try_from(statement.claim.coefficient_bound) else {
        return false;
    };
    if statement.claim.channel_id != evaluation_channel_id(statement.evaluation_point) {
        return false;
    }
    verify_ood(
        &AdditivePcsOodStatement {
            evaluation_root: statement.claim.root,
            basis: statement.basis.clone(),
            offset: statement.offset,
            coefficient_bound,
            z: statement.evaluation_point,
            y: statement.claim.target,
            num_queries: statement.num_queries,
        },
        &proof.opening,
    )
}
