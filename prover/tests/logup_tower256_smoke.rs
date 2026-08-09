use minidregg_prover::{
    binary_tower_256::Tower256,
    logup_tower256::{
        prove_logup256_single, semantic_index_bundle_root, verify_logup256_single,
        verify_logup256_single_bound, Logup256Error,
    },
    semantic_lookup::{
        bind_semantic_lookup_clause, semantic_lookup_native_binding, verify_semantic_lookup_clause,
        verify_semantic_lookup_native_binding,
    },
};

#[test]
fn tower256_logup_single_looker_end_to_end_smoke() {
    let table = [
        Tower256::from_limbs([0x11, 0x22, 0x33, 0x44]),
        Tower256::from_limbs([0x55, 0x66, 0x77, 0x88]),
        Tower256::from_limbs([0x99, 0xaa, 0xbb, 0xcc]),
        Tower256::from_limbs([0xdd, 0xee, 0xff, 0x101]),
    ];
    // Repeated and permuted hits exercise the weighted scatter; characteristic
    // two parity is not used as a substitute for the per-row eq weights.
    let addresses = [2usize, 0, 2, 3];
    let (statement, proof) = prove_logup256_single(&table, &addresses, 1, 2).unwrap();

    assert!(verify_logup256_single(&statement, &proof).unwrap());
    let semantic_bundle = semantic_index_bundle_root(&statement).unwrap();
    assert_eq!(semantic_bundle, statement.index_bundle_root);
    assert!(verify_logup256_single_bound(&semantic_bundle, &statement, &proof).unwrap());

    let mut unrelated_bundle_bytes = semantic_bundle.into_bytes();
    unrelated_bundle_bytes[0] ^= 1;
    let unrelated_bundle =
        minidregg_prover::binary_hash::BinaryRoot::from_bytes(unrelated_bundle_bytes);
    assert!(!verify_logup256_single_bound(&unrelated_bundle, &statement, &proof).unwrap());

    let clause = bind_semantic_lookup_clause(statement.clone(), proof.clone()).unwrap();
    assert!(verify_semantic_lookup_clause(&semantic_bundle, &clause).unwrap());
    assert!(!verify_semantic_lookup_clause(&unrelated_bundle, &clause).unwrap());
    let receipt_binding = semantic_lookup_native_binding(&clause);
    assert_eq!(receipt_binding.commitment_root, semantic_bundle);
    assert!(verify_semantic_lookup_native_binding(&receipt_binding, &clause).unwrap());

    let mut root_splice = receipt_binding.clone();
    root_splice.commitment_root = unrelated_bundle;
    assert!(!verify_semantic_lookup_native_binding(&root_splice, &clause).unwrap());

    let mut statement_splice = clause.clone();
    statement_splice.statement_id[0] ^= 1;
    assert!(!verify_semantic_lookup_clause(&semantic_bundle, &statement_splice).unwrap());

    let mut tampered = proof.clone();
    tampered.evaluation_value = tampered.evaluation_value.add(Tower256::ONE);
    assert!(!verify_logup256_single(&statement, &tampered).unwrap());

    // Booleanity is now proved against the same pre-challenge index root; it
    // is not an upstream-AIR comment.  A self-contained proof mutation fails
    // before the lookup reduction can use the column.
    let mut nonboolean_certificate = proof.clone();
    nonboolean_certificate.index_booleanity[0].rounds[0].evaluations[2] =
        nonboolean_certificate.index_booleanity[0].rounds[0].evaluations[2].add(Tower256::ONE);
    assert!(!verify_logup256_single(&statement, &nonboolean_certificate).unwrap());

    assert!(matches!(
        prove_logup256_single(&table, &[2, 0, 4, 3], 1, 2),
        Err(Logup256Error::AddressOutOfRange { row: 2, address: 4 })
    ));
}
