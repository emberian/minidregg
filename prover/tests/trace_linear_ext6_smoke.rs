use minidregg_prover::{
    field4::badd,
    field6::Ext6,
    trace_linear_ext6::{linear_functional_value, prove_trace_linear, verify_trace_linear},
};

fn e(limbs: [u64; 6]) -> Ext6 {
    Ext6::try_from_limbs(limbs).unwrap()
}

fn bump(value: Ext6) -> Ext6 {
    let mut limbs = *value.limbs();
    limbs[0] = badd(limbs[0], 1);
    e(limbs)
}

#[test]
fn trace_linear_opening_roundtrip_has_quadratic_and_commitment_teeth() {
    let table = (0..8)
        .map(|i| e([(13 * i + 5) as u64, (i * i + 3) as u64, 0, 0, 0, 0]))
        .collect::<Vec<_>>();
    let weights = (0..8)
        .map(|i| e([(7 * i + 11) as u64, 0, (3 * i + 1) as u64, 0, 0, 0]))
        .collect::<Vec<_>>();
    let claimed = linear_functional_value(&table, &weights).unwrap();
    let (statement, proof) = prove_trace_linear(&table, &weights, claimed, 2, 4).unwrap();
    assert_eq!(proof.sumcheck.rounds.len(), 3);
    assert_eq!(proof.table_mle_proof.roots.len(), 4);
    assert!(verify_trace_linear(&statement, &weights, &proof).unwrap());

    let mut bad_statement = statement.clone();
    bad_statement.claimed_value = bump(bad_statement.claimed_value);
    assert!(!verify_trace_linear(&bad_statement, &weights, &proof).unwrap());
    let mut bad_weights = weights.clone();
    bad_weights[2] = bump(bad_weights[2]);
    assert!(!verify_trace_linear(&statement, &bad_weights, &proof).unwrap());
    let mut bad = proof.clone();
    bad.sumcheck.rounds[1][2] = bump(bad.sumcheck.rounds[1][2]);
    assert!(!verify_trace_linear(&statement, &weights, &bad).unwrap());
    let mut bad = proof.clone();
    bad.table_mle_proof.queries[0].rounds[0].high =
        bump(bad.table_mle_proof.queries[0].rounds[0].high);
    assert!(!verify_trace_linear(&statement, &weights, &bad).unwrap());
}
