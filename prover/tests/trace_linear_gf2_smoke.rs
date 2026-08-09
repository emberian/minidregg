//! One focused smoke for arbitrary GF(2^64) linear-functional retirement.

use minidregg_prover::{
    binary_hash::BinaryRoot,
    binary_tower::TowerElem,
    binary_transcript::{BinaryShake256Transcript, TranscriptSuite},
};

// Path-load both new modules without editing `lib.rs` or shared protocol files.
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
#[path = "../src/trace_linear_gf2.rs"]
mod trace_linear_gf2;

use additive_mle_terminal::commit_additive_mle_word;
use minidregg_prover::binary_hash::BinaryShake256V1;
use trace_linear_gf2::{
    commit_trace_linear_gf2_table_with_blowup, linear_functional_value_gf2,
    observe_trace_linear_gf2_initial, prove_trace_linear_gf2_from_state_with_blowup,
    prove_trace_linear_gf2_with_blowup, verify_trace_linear_gf2,
    verify_trace_linear_gf2_after_initial,
};

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

#[test]
fn binary_linear_retirement_has_sumcheck_and_additive_opening_teeth() {
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
    let claimed = linear_functional_value_gf2(&table, &weights).unwrap();
    let (statement, proof) = prove_trace_linear_gf2_with_blowup(
        &table, &weights, claimed, &basis, offset, log_blowup, 4,
    )
    .unwrap();
    assert_eq!(statement.log_blowup, log_blowup);
    assert_eq!(proof.sumcheck.rounds.len(), 3);
    assert_eq!(proof.table_mle_proof.roots.len(), 4);
    let final_codeword = vec![proof.table_mle_statement.claimed_terminal; 1usize << log_blowup];
    assert_eq!(
        proof.table_mle_proof.roots.last().copied().unwrap(),
        commit_additive_mle_word(&final_codeword, &BinaryShake256V1)
            .unwrap()
            .root()
    );
    assert!(verify_trace_linear_gf2(&statement, &weights, &proof).unwrap());

    let mut bad_rate = statement.clone();
    bad_rate.log_blowup -= 1;
    assert!(verify_trace_linear_gf2(&bad_rate, &weights, &proof).is_err());

    let mut bad_statement = statement.clone();
    bad_statement.claimed_value = bump(bad_statement.claimed_value);
    assert!(!verify_trace_linear_gf2(&bad_statement, &weights, &proof).unwrap());
    let mut bad_statement = statement.clone();
    bad_statement.table_root = bump_root(bad_statement.table_root);
    assert!(!verify_trace_linear_gf2(&bad_statement, &weights, &proof).unwrap());
    let mut bad_weights = weights;
    bad_weights[2] = bump(bad_weights[2]);
    assert!(!verify_trace_linear_gf2(&statement, &bad_weights, &proof).unwrap());
    let mut bad = proof.clone();
    bad.sumcheck.rounds[1][2] = bump(bad.sumcheck.rounds[1][2]);
    assert!(!verify_trace_linear_gf2(&statement, &weights, &bad).unwrap());
    let mut bad = proof.clone();
    bad.table_mle_proof.queries[0].rounds[0].high =
        bump(bad.table_mle_proof.queries[0].rounds[0].high);
    assert!(!verify_trace_linear_gf2(&statement, &weights, &bad).unwrap());
    let mut bad = proof.clone();
    let terminal = bad.table_mle_statement.claimed_terminal;
    let mut nonconstant_final = vec![terminal; 1usize << log_blowup];
    nonconstant_final[2] = bump(nonconstant_final[2]);
    *bad.table_mle_proof.roots.last_mut().unwrap() =
        commit_additive_mle_word(&nonconstant_final, &BinaryShake256V1)
            .unwrap()
            .root();
    assert!(!verify_trace_linear_gf2(&statement, &weights, &bad).unwrap());

    // Caller-owned seam: the table root precedes an outer receipt challenge;
    // proving and verification then continue without restarting the transcript.
    let caller_label = b"binary-receipt/caller-owned-smoke";
    let mut prover_transcript = BinaryShake256Transcript::new(caller_label);
    let state = commit_trace_linear_gf2_table_with_blowup(
        &table,
        &basis,
        offset,
        log_blowup,
        &mut prover_transcript,
    )
    .unwrap();
    let retained_root = state.input_root();
    prover_transcript.observe_bytes(b"outer/receipt", b"bound-before-linear-retirement");
    let outer_challenge = prover_transcript.sample_gf2_64(b"outer/challenge");
    let (nested_statement, nested_proof) = prove_trace_linear_gf2_from_state_with_blowup(
        &table,
        &weights,
        claimed,
        &basis,
        offset,
        log_blowup,
        4,
        state,
        &mut prover_transcript,
    )
    .unwrap();
    assert_eq!(nested_statement.table_root, retained_root);

    let mut verifier_transcript = BinaryShake256Transcript::new(caller_label);
    observe_trace_linear_gf2_initial(&nested_statement, &mut verifier_transcript).unwrap();
    verifier_transcript.observe_bytes(b"outer/receipt", b"bound-before-linear-retirement");
    assert_eq!(
        verifier_transcript.sample_gf2_64(b"outer/challenge"),
        outer_challenge
    );
    assert!(verify_trace_linear_gf2_after_initial(
        &nested_statement,
        &weights,
        &nested_proof,
        &mut verifier_transcript,
    )
    .unwrap());
}
