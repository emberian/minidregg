//! One focused smoke for the evaluation-channel history append.

use minidregg_prover::{
    additive_ntt::forward,
    binary_evaluation_claim::{
        evaluation_channel_id, prove_evaluation_claim, verify_evaluation_claim,
    },
    binary_tower::TowerElem,
};

// Resolve the future crate-relative imports of the path-loaded new module.
mod additive_pcs_ood {
    pub use minidregg_prover::additive_pcs_ood::*;
}
mod binary_evaluation_claim {
    pub use minidregg_prover::binary_evaluation_claim::*;
}
mod binary_history_append {
    pub use minidregg_prover::binary_history_append::*;
}
mod binary_tower {
    pub use minidregg_prover::binary_tower::*;
}
#[path = "../src/binary_evaluation_history_append.rs"]
mod binary_evaluation_history_append;

use binary_evaluation_history_append::{
    prove_binary_evaluation_history_append, verify_binary_evaluation_history_append,
    BinaryEvaluationHistoryAppendStatement,
};

fn e(bits: u64) -> TowerElem {
    TowerElem::new(6, bits).unwrap()
}

#[test]
fn evaluation_history_append_reauthenticates_output_and_rejects_substitution() {
    let log_domain = 5;
    let word_len = 1usize << log_domain;
    let bound = 8;
    let queries = 3;
    let basis = (0..log_domain)
        .map(|index| e(1u64 << index))
        .collect::<Vec<_>>();
    let offset = e(0xd6e8_feb8_6659_fd93);
    let point = e(1 << 12);
    let mut left_coefficients = vec![e(0); word_len];
    let mut right_coefficients = vec![e(0); word_len];
    for index in 0..bound {
        left_coefficients[index] = e((index as u64 + 3).wrapping_mul(0x9e37_79b9_7f4a_7c15));
        right_coefficients[index] = e((index as u64 + 11).wrapping_mul(0xbf58_476d_1ce4_e5b9));
    }
    let left_word = forward(&left_coefficients, &basis, offset).unwrap();
    let right_word = forward(&right_coefficients, &basis, offset).unwrap();
    let (left_statement, left_authentication) =
        prove_evaluation_claim(&left_coefficients, &basis, offset, bound, point, queries).unwrap();
    let (right_statement, right_authentication) =
        prove_evaluation_claim(&right_coefficients, &basis, offset, bound, point, queries).unwrap();
    assert!(verify_evaluation_claim(
        &left_statement,
        &left_authentication
    ));
    assert!(verify_evaluation_claim(
        &right_statement,
        &right_authentication
    ));

    let statement = BinaryEvaluationHistoryAppendStatement {
        left: left_statement,
        right: right_statement,
    };
    let proof = prove_binary_evaluation_history_append(
        &statement,
        &left_word,
        &left_coefficients,
        &right_word,
        &right_coefficients,
    )
    .unwrap();
    assert_eq!(proof.output_claim(), &proof.append.output_claim);
    assert!(verify_binary_evaluation_history_append(&statement, &proof));

    let mut bad_target = proof.clone();
    bad_target.append.output_claim.target =
        bad_target.append.output_claim.target.add(e(1)).unwrap();
    assert!(!verify_binary_evaluation_history_append(
        &statement,
        &bad_target
    ));

    let mut bad_point = statement.clone();
    bad_point.left.evaluation_point = e(1 << 13);
    bad_point.right.evaluation_point = e(1 << 13);
    assert!(!verify_binary_evaluation_history_append(&bad_point, &proof));

    let mut bad_channel = statement.clone();
    let other_channel = evaluation_channel_id(e(1 << 13));
    bad_channel.left.claim.channel_id = other_channel;
    bad_channel.right.claim.channel_id = other_channel;
    assert!(!verify_binary_evaluation_history_append(
        &bad_channel,
        &proof
    ));

    let mut unrelated_coefficients = vec![e(0); word_len];
    for (index, coefficient) in unrelated_coefficients[..bound].iter_mut().enumerate() {
        *coefficient = e((index as u64 + 29).wrapping_mul(0x94d0_49bb_1331_11eb));
    }
    let (unrelated_statement, unrelated_proof) = prove_evaluation_claim(
        &unrelated_coefficients,
        &basis,
        offset,
        bound,
        point,
        queries,
    )
    .unwrap();
    assert!(verify_evaluation_claim(
        &unrelated_statement,
        &unrelated_proof
    ));
    assert_ne!(
        unrelated_statement.claim.root,
        proof.append.output_claim.root
    );
    let mut substituted = proof.clone();
    substituted.output_evaluation = unrelated_proof;
    assert!(!verify_binary_evaluation_history_append(
        &statement,
        &substituted
    ));
}
