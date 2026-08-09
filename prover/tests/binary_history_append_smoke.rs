use minidregg_prover::{
    additive_ntt::forward,
    binary_evaluation_claim::{prove_evaluation_claim, verify_evaluation_claim},
    binary_history_append::{
        prove_binary_history_append, verify_binary_history_append, BinaryHistoryAppendStatement,
    },
    binary_tower::TowerElem,
};

fn e(bits: u64) -> TowerElem {
    TowerElem::new(6, bits).unwrap()
}

#[test]
fn binary_history_append_roundtrip_and_tamper_teeth() {
    let log_domain = 5;
    let word_len = 1usize << log_domain;
    let coefficient_bound = 8;
    let basis = (0..log_domain)
        .map(|index| e(1u64 << index))
        .collect::<Vec<_>>();
    let offset = e(0xd6e8_feb8_6659_fd93);
    let mut left_coefficients = vec![e(0); word_len];
    let mut right_coefficients = vec![e(0); word_len];
    for i in 0..coefficient_bound {
        left_coefficients[i] = e((i as u64 + 3).wrapping_mul(0x9e37_79b9_7f4a_7c15));
        right_coefficients[i] = e((i as u64 + 11).wrapping_mul(0xbf58_476d_1ce4_e5b9));
    }
    let left_word = forward(&left_coefficients, &basis, offset).unwrap();
    let right_word = forward(&right_coefficients, &basis, offset).unwrap();
    let evaluation_point = e(1 << 12);
    let (left_claim, left_claim_proof) = prove_evaluation_claim(
        &left_coefficients,
        &basis,
        offset,
        coefficient_bound,
        evaluation_point,
        3,
    )
    .unwrap();
    let (right_claim, right_claim_proof) = prove_evaluation_claim(
        &right_coefficients,
        &basis,
        offset,
        coefficient_bound,
        evaluation_point,
        3,
    )
    .unwrap();
    assert!(verify_evaluation_claim(&left_claim, &left_claim_proof));
    assert!(verify_evaluation_claim(&right_claim, &right_claim_proof));
    let statement = BinaryHistoryAppendStatement {
        left: left_claim.claim,
        right: right_claim.claim,
        basis,
        offset,
        num_queries: 3,
    };
    let proof = prove_binary_history_append(
        &statement,
        &left_word,
        &left_coefficients,
        &right_word,
        &right_coefficients,
    )
    .unwrap();
    assert_eq!(proof.relation_openings.len(), statement.num_queries);
    assert_eq!(proof.fri_proof.queries.len(), statement.num_queries);
    assert!(verify_binary_history_append(&statement, &proof));

    let mut bad = proof.clone();
    bad.relation_openings[0].left_low = bad.relation_openings[0].left_low.add(e(1)).unwrap();
    assert!(!verify_binary_history_append(&statement, &bad));

    let mut bad = proof.clone();
    bad.fri_proof.queries[1].rounds[0].low =
        bad.fri_proof.queries[1].rounds[0].low.add(e(1)).unwrap();
    assert!(!verify_binary_history_append(&statement, &bad));

    let mut changed_statement = statement.clone();
    changed_statement.left.target = changed_statement.left.target.add(e(1)).unwrap();
    assert!(!verify_binary_history_append(&changed_statement, &proof));

    let mut bad = proof.clone();
    bad.output_claim.target = bad.output_claim.target.add(e(1)).unwrap();
    assert!(!verify_binary_history_append(&statement, &bad));
}
