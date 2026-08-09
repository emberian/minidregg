//! One focused executable ordering/protocol smoke for the additive MLE terminal.

use minidregg_prover::{
    binary_hash::{BinaryRoot, BinaryShake256V1},
    binary_tower::TowerElem,
    binary_transcript::{BinaryShake256Transcript, TranscriptSuite},
};

// Resolve crate-relative imports while the new module remains intentionally
// unexported from `lib.rs` in this new-files-only lane.
mod additive_fri_sampled {
    pub use minidregg_prover::additive_fri_sampled::*;
}
mod additive_ntt {
    pub use minidregg_prover::additive_ntt::*;
}
mod binary_hash {
    pub use minidregg_prover::binary_hash::*;
}
mod binary_merkle {
    pub use minidregg_prover::binary_merkle::*;
}
mod binary_tower {
    pub use minidregg_prover::binary_tower::*;
}
mod binary_transcript {
    pub use minidregg_prover::binary_transcript::*;
}
#[path = "../src/additive_mle_terminal.rs"]
mod additive_mle_terminal;

use additive_mle_terminal::{
    bind_mle_coefficients, boolean_mobius_coefficients, evaluate_table_mle,
    fold_reversed_lch_round, reversed_lch_encode, reversed_lch_evaluations,
    verify_additive_mle_terminal, AdditiveMleTerminalProverState,
    ADDITIVE_MLE_TERMINAL_PROTOCOL_LABEL,
};

fn e(bits: u64) -> TowerElem {
    TowerElem::new(6, bits).unwrap()
}

fn bump_root(root: BinaryRoot) -> BinaryRoot {
    let mut bytes = root.into_bytes();
    bytes[0] ^= 1;
    BinaryRoot::from_bytes(bytes)
}

#[test]
fn reversed_lch_folds_bind_lsb_mle_variables_and_reject_tampers() {
    let table = [
        e(0x0123_4567_89ab_cdef),
        e(0xfedc_ba98_7654_3210),
        e(0x9e37_79b9_7f4a_7c15),
        e(0xbf58_476d_1ce4_e5b9),
        e(0x94d0_49bb_1331_11eb),
        e(0xd6e8_feb8_6659_fd93),
        e(0xa5a5_5a5a_f0f0_0f0f),
        e(0x1357_9bdf_2468_ace0),
    ];
    // Domain indices remain ordinary little-endian. Only the LCH polynomial
    // chain is reversed, so the first runtime fold removes basis[2].
    let basis = [e(1), e(2), e(4)];
    let offset = e(0x6a09_e667_f3bc_c908);
    let point = [
        e(0x243f_6a88_85a3_08d3),
        e(0x1319_8a2e_0370_7344),
        e(0xa409_3822_299f_31d0),
    ];
    let terminal = evaluate_table_mle(&table, &point).unwrap();

    // Keystone: after every runtime fold, the word equals a fresh dense
    // reversed-LCH evaluation of the correspondingly bound Mobius polynomial.
    // Thus the corrected permutation is the identity, not bit reversal.
    let mut coefficients = boolean_mobius_coefficients(&table).unwrap();
    let mut round_basis = basis.to_vec();
    let mut round_offset = offset;
    let mut word = reversed_lch_evaluations(&coefficients, &round_basis, round_offset).unwrap();
    assert_eq!(
        reversed_lch_encode(&coefficients, &round_basis, round_offset).unwrap(),
        word
    );
    for &challenge in &point {
        let (folded, next_basis, next_offset) =
            fold_reversed_lch_round(&word, &round_basis, round_offset, challenge).unwrap();
        coefficients = bind_mle_coefficients(&coefficients, challenge).unwrap();
        let expected = reversed_lch_evaluations(&coefficients, &next_basis, next_offset).unwrap();
        assert_eq!(folded, expected);
        assert_eq!(
            reversed_lch_encode(&coefficients, &next_basis, next_offset).unwrap(),
            expected
        );
        word = folded;
        round_basis = next_basis;
        round_offset = next_offset;
    }
    assert_eq!(coefficients, [terminal]);
    assert_eq!(word, [terminal]);

    let mut prover_transcript = BinaryShake256Transcript::new(ADDITIVE_MLE_TERMINAL_PROTOCOL_LABEL);
    let mut state = AdditiveMleTerminalProverState::commit_initial(
        &table,
        &basis,
        offset,
        BinaryShake256V1,
        &mut prover_transcript,
    )
    .unwrap();
    let input_root = state.input_root();
    for &challenge in &point {
        state.bind(challenge, &mut prover_transcript).unwrap();
    }
    let (statement, proof) = state.finish(terminal, 4, &mut prover_transcript).unwrap();
    assert_eq!(statement.input_root, input_root);
    assert_eq!(proof.roots.len(), point.len() + 1);
    assert_eq!(proof.queries.len(), statement.num_queries);
    assert!(proof
        .queries
        .iter()
        .all(|query| query.rounds.len() == point.len()));

    let verify = |statement, point: &[TowerElem], proof| {
        let mut transcript = BinaryShake256Transcript::new(ADDITIVE_MLE_TERMINAL_PROTOCOL_LABEL);
        verify_additive_mle_terminal(statement, point, proof, &BinaryShake256V1, &mut transcript)
    };
    assert!(verify(&statement, &point, &proof));

    let mut bad = proof.clone();
    bad.queries[0].rounds[0].low = bad.queries[0].rounds[0].low.add(e(1)).unwrap();
    assert!(!verify(&statement, &point, &bad));
    let mut bad = proof.clone();
    bad.roots[1] = bump_root(bad.roots[1]);
    assert!(!verify(&statement, &point, &bad));
    let mut bad_statement = statement.clone();
    bad_statement.claimed_terminal = bad_statement.claimed_terminal.add(e(1)).unwrap();
    assert!(!verify(&bad_statement, &point, &proof));
    let mut bad_point = point;
    bad_point[1] = bad_point[1].add(e(1)).unwrap();
    assert!(!verify(&statement, &bad_point, &proof));
}
