use minidregg_prover::{
    additive_pcs_ood::{evaluate_novel_polynomial, prove_ood, verify_ood},
    binary_hash::{BinaryRoot, BinaryShake256V1, HashSuite},
    binary_tower::TowerElem,
};

fn e(bits: u64) -> TowerElem {
    TowerElem::new(6, bits).unwrap()
}

fn changed_root(root: BinaryRoot) -> BinaryRoot {
    let mut bytes = root.into_bytes();
    bytes[0] ^= 1;
    BinaryRoot::from_bytes(bytes)
}

#[test]
fn additive_pcs_ood_sampled_join_smoke_and_tampers() {
    let k = 5;
    let n = 1usize << k;
    let bound = 8;
    let basis = (0..k).map(|i| e(1u64 << i)).collect::<Vec<_>>();
    let offset = e(1 << 8);
    let z = e(1 << 12); // Outside offset + span{bits 0..4}.
    let mut coefficients = vec![e(0); n];
    for (i, coefficient) in coefficients[..bound].iter_mut().enumerate() {
        *coefficient = e((0x9e37_79b9u64.wrapping_mul(i as u64 + 1)) ^ (i as u64 * 17));
    }
    let y = evaluate_novel_polynomial(&coefficients, &basis, z).unwrap();
    let (statement, proof) = prove_ood(&coefficients, &basis, offset, bound, z, y, 4).unwrap();
    assert!(verify_ood(&statement, &proof));
    assert_eq!(proof.evaluation_openings.len(), 4);

    let mut bad_statement = statement.clone();
    bad_statement.y = bad_statement.y.add(e(1)).unwrap();
    assert!(!verify_ood(&bad_statement, &proof));
    let mut bad = proof.clone();
    bad.evaluation_openings[0].low = bad.evaluation_openings[0].low.add(e(1)).unwrap();
    assert!(!verify_ood(&statement, &bad));
    let mut bad = proof.clone();
    bad.evaluation_openings[1].high_path.siblings[0] =
        changed_root(bad.evaluation_openings[1].high_path.siblings[0]);
    assert!(!verify_ood(&statement, &bad));
    let mut bad = proof.clone();
    bad.quotient_fri.queries[0].rounds[0].low =
        bad.quotient_fri.queries[0].rounds[0].low.add(e(1)).unwrap();
    assert!(!verify_ood(&statement, &bad));
    let mut bad = proof.clone();
    bad.quotient_fri.roots[0] = changed_root(bad.quotient_fri.roots[0]);
    assert!(!verify_ood(&statement, &bad));

    // The protocol is pinned to the selected binary suite, not a caller-picked
    // demo hash; keep the suite identifier in this single join smoke.
    assert_eq!(
        <BinaryShake256V1 as HashSuite>::SUITE_ID,
        b"BinaryShake256V1"
    );
}
