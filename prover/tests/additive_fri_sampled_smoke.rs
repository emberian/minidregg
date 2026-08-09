use minidregg_prover::{
    additive_fri_sampled::{
        prove_sampled, verify_sampled, BinaryShakeFriSource, SampledFriStatement,
    },
    binary_hash::{BinaryRoot, BinaryShake256V1, HashSuite},
    binary_tower::TowerElem,
};

fn e(level: u8, bits: u64) -> TowerElem {
    TowerElem::new(level, bits).unwrap()
}

fn source(statement: &SampledFriStatement) -> BinaryShakeFriSource {
    BinaryShakeFriSource::new(
        <BinaryShake256V1 as HashSuite>::SUITE_ID,
        &statement.basis,
        statement.offset,
        statement.coefficient_bound,
        statement.num_queries,
    )
}

fn changed_root(root: BinaryRoot) -> BinaryRoot {
    let mut bytes = root.into_bytes();
    bytes[0] ^= 1;
    BinaryRoot::from_bytes(bytes)
}

#[test]
fn sampled_multi_round_binary_shake_smoke_and_tamper_rejection() {
    let level = 3;
    let k = 5;
    let n = 1usize << k;
    let basis = (0..k).map(|i| e(level, 1u64 << i)).collect::<Vec<_>>();
    let coefficients = (0..n)
        .map(|i| e(level, ((i * 73 + 19) & 0xff) as u64))
        .collect::<Vec<_>>();
    let hash = BinaryShake256V1;
    let offset = e(level, 0xa5);
    let coefficient_bound = 8;
    let mut prover_source = BinaryShakeFriSource::new(
        <BinaryShake256V1 as HashSuite>::SUITE_ID,
        &basis,
        offset,
        coefficient_bound,
        3,
    );
    let mut coefficients = coefficients;
    coefficients[coefficient_bound..].fill(e(level, 0));
    let (statement, proof) = prove_sampled(
        &coefficients,
        &basis,
        offset,
        coefficient_bound,
        3,
        &hash,
        &mut prover_source,
    )
    .unwrap();
    assert_eq!(proof.roots.len(), k + 1);
    assert_eq!(proof.queries.len(), 3);
    assert!(proof.queries.iter().all(|query| query.rounds.len() == k));
    assert!(verify_sampled(
        &statement,
        &proof,
        &hash,
        &mut source(&statement)
    ));

    let mut bad = proof.clone();
    bad.queries[0].rounds[0].low = bad.queries[0].rounds[0].low.add(e(level, 1)).unwrap();
    assert!(!verify_sampled(
        &statement,
        &bad,
        &hash,
        &mut source(&statement)
    ));
    let mut bad = proof.clone();
    bad.queries[1].rounds[1].low_path.siblings[0] =
        changed_root(bad.queries[1].rounds[1].low_path.siblings[0]);
    assert!(!verify_sampled(
        &statement,
        &bad,
        &hash,
        &mut source(&statement)
    ));
    let mut bad = proof.clone();
    bad.roots[2] = changed_root(bad.roots[2]);
    assert!(!verify_sampled(
        &statement,
        &bad,
        &hash,
        &mut source(&statement)
    ));
    let mut bad = proof.clone();
    bad.final_value = bad.final_value.add(e(level, 1)).unwrap();
    assert!(!verify_sampled(
        &statement,
        &bad,
        &hash,
        &mut source(&statement)
    ));
    let mut changed_statement = statement.clone();
    changed_statement.offset = changed_statement.offset.add(e(level, 1)).unwrap();
    assert!(!verify_sampled(
        &changed_statement,
        &proof,
        &hash,
        &mut source(&changed_statement)
    ));
}
