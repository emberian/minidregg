//! One focused smoke for arbitrary-functional binary append.

use minidregg_prover::{
    binary_hash::{BinaryRoot, BinaryShake256V1},
    binary_tower::TowerElem,
};

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
#[path = "../src/binary_functional_append.rs"]
mod binary_functional_append;
#[path = "../src/trace_linear_gf2.rs"]
mod trace_linear_gf2;

use additive_mle_terminal::{additive_mle_initial_word_with_blowup, commit_additive_mle_word};
use binary_functional_append::{
    binary_functional_channel_id, prove_binary_functional_append, verify_binary_functional_append,
    BinaryFunctionalAppendStatement, BinaryFunctionalClaim,
};
use trace_linear_gf2::{
    linear_functional_value_gf2, prove_trace_linear_gf2_with_blowup, TraceLinearGf2Statement,
};

const CHANNEL_LABEL: &[u8] = b"receipt/arbitrary-trace-functional/v1";

fn e(bits: u64) -> TowerElem {
    TowerElem::new(6, bits).unwrap()
}

fn bump(value: TowerElem) -> TowerElem {
    value.add(e(1)).unwrap()
}

fn bump_root(root: BinaryRoot) -> BinaryRoot {
    let mut bytes = root.into_bytes();
    bytes[0] ^= 1;
    BinaryRoot::from_bytes(bytes)
}

fn authenticated_claim(
    table: &[TowerElem],
    weights: &[TowerElem],
    basis: &[TowerElem],
    offset: TowerElem,
    log_blowup: u32,
    queries: usize,
) -> BinaryFunctionalClaim {
    let word = additive_mle_initial_word_with_blowup(table, basis, offset, log_blowup).unwrap();
    let root = commit_additive_mle_word(&word, &BinaryShake256V1)
        .unwrap()
        .root();
    BinaryFunctionalClaim {
        channel_id: binary_functional_channel_id(CHANNEL_LABEL, weights, basis, offset).unwrap(),
        linear: TraceLinearGf2Statement {
            table_root: root,
            log_blowup,
            basis: basis.to_vec(),
            offset,
            claimed_value: linear_functional_value_gf2(table, weights).unwrap(),
            num_queries: queries,
        },
    }
}

#[test]
fn arbitrary_functional_append_authenticates_both_input_words_at_output_queries() {
    let left_table = [
        e(0x0123_4567_89ab_cdef),
        e(0xfedc_ba98_7654_3210),
        e(0x9e37_79b9_7f4a_7c15),
        e(0xbf58_476d_1ce4_e5b9),
        e(0x94d0_49bb_1331_11eb),
        e(0xd6e8_feb8_6659_fd93),
        e(0xa5a5_5a5a_f0f0_0f0f),
        e(0x1357_9bdf_2468_ace0),
    ];
    let right_table = [
        e(0x3c6e_f372_fe94_f82b),
        e(0xbb67_ae85_84ca_a73b),
        e(0xa54f_f53a_5f1d_36f1),
        e(0x510e_527f_ade6_82d1),
        e(0x9b05_688c_2b3e_6c1f),
        e(0x1f83_d9ab_fb41_bd6b),
        e(0x5be0_cd19_137e_2179),
        e(0xcbbb_9d5d_c105_9ed8),
    ];
    let weights = [
        e(0x243f_6a88_85a3_08d3),
        e(0x1319_8a2e_0370_7344),
        e(0xa409_3822_299f_31d0),
        e(0x082e_fa98_ec4e_6c89),
        e(0x4528_21e6_38d0_1377),
        e(0xbe54_66cf_34e9_0c6c),
        e(0xc0ac_29b7_c97c_50dd),
        e(0x3f84_d5b5_b547_0917),
    ];
    let basis = [e(1), e(2), e(4), e(8), e(16)];
    let offset = e(0x6a09_e667_f3bc_c908);
    let log_blowup = 2;
    let queries = 4;
    let statement = BinaryFunctionalAppendStatement {
        left: authenticated_claim(&left_table, &weights, &basis, offset, log_blowup, queries),
        right: authenticated_claim(&right_table, &weights, &basis, offset, log_blowup, queries),
    };
    let proof = prove_binary_functional_append(
        &statement,
        &left_table,
        &right_table,
        &weights,
        CHANNEL_LABEL,
    )
    .unwrap();
    assert_eq!(proof.input_queries.len(), queries);
    assert_eq!(
        proof.output_trace_proof.table_mle_proof.queries.len(),
        queries
    );
    assert!(verify_binary_functional_append(&statement, &weights, CHANNEL_LABEL, &proof).unwrap());

    let mut bad_statement = statement.clone();
    bad_statement.left.linear.claimed_value = bump(bad_statement.left.linear.claimed_value);
    assert!(
        !verify_binary_functional_append(&bad_statement, &weights, CHANNEL_LABEL, &proof,).unwrap()
    );
    let mut bad_statement = statement.clone();
    bad_statement.right.linear.table_root = bump_root(bad_statement.right.linear.table_root);
    assert!(
        !verify_binary_functional_append(&bad_statement, &weights, CHANNEL_LABEL, &proof,).unwrap()
    );
    let mut bad = proof.clone();
    bad.input_queries[0].left.low = bump(bad.input_queries[0].left.low);
    assert!(!verify_binary_functional_append(&statement, &weights, CHANNEL_LABEL, &bad).unwrap());
    let mut bad = proof.clone();
    bad.output.channel_id =
        binary_functional_channel_id(b"receipt/unrelated-channel/v1", &weights, &basis, offset)
            .unwrap();
    assert!(!verify_binary_functional_append(&statement, &weights, CHANNEL_LABEL, &bad).unwrap());

    let mut unrelated_weights = weights;
    unrelated_weights[3] = bump(unrelated_weights[3]);
    assert!(
        verify_binary_functional_append(&statement, &unrelated_weights, CHANNEL_LABEL, &proof,)
            .is_err()
    );

    // A valid standalone proof for another table/root cannot be substituted
    // into this append transcript.
    let unrelated_table = right_table.map(bump);
    let unrelated_target = linear_functional_value_gf2(&unrelated_table, &weights).unwrap();
    let (unrelated_linear, unrelated_trace_proof) = prove_trace_linear_gf2_with_blowup(
        &unrelated_table,
        &weights,
        unrelated_target,
        &basis,
        offset,
        log_blowup,
        queries,
    )
    .unwrap();
    let mut unrelated = proof.clone();
    unrelated.output.linear = unrelated_linear;
    unrelated.output_trace_proof = unrelated_trace_proof;
    assert!(
        !verify_binary_functional_append(&statement, &weights, CHANNEL_LABEL, &unrelated,).unwrap()
    );
}
