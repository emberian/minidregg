//! One-call composition tests for `[PROVER-e2e-reference]`.
//!
//! These exercise the real Lean-emitted demo descriptor through trace generation,
//! trace commitment, one Fiat--Shamir gate sumcheck, and one Fiat--Shamir FRI
//! descent.  As everywhere in this crate they are running conformance/teeth tests,
//! not a proof of the Rust or of the cryptographic assumptions.

use std::path::Path;

use minidregg_prover::commit::commit_trace;
use minidregg_prover::descriptor::Descriptor;
use minidregg_prover::field4::P;
use minidregg_prover::poseidon::demo_spec;
use minidregg_prover::protocol::{
    reference_prove, reference_verify, ReferenceConfig, ReferenceProof,
};

const HONEST_VARS: [u64; 5] = [13, 1, 0, 1, 1];

fn demo() -> Descriptor {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/demo_descriptor.json");
    Descriptor::from_file(Path::new(path)).expect("parse the Lean-emitted demo descriptor")
}

fn config() -> ReferenceConfig {
    // 23 trace coefficients need 5 folds; blowup 2 gives a 128-element word.
    ReferenceConfig {
        fri_log_blowup: 2,
        fri_queries: 8,
    }
}

fn proof() -> (Descriptor, ReferenceProof) {
    let d = demo();
    let proof = reference_prove(&d, &HONEST_VARS, config(), &demo_spec())
        .expect("honest emitted instance proves");
    (d, proof)
}

#[test]
fn emitted_descriptor_one_call_round_trip() {
    let (d, proof) = proof();
    assert_eq!(proof.trace.len(), 23);
    assert_eq!(proof.gate_sumcheck.claim, 0);
    assert_eq!(proof.gate_sumcheck.rounds.len(), 5); // 23 constraints -> 32-corner cube
    assert_eq!(proof.fri.round_commitments.len(), 5); // 23 coefficients -> degree < 32
    assert_eq!(proof.fri.final_codeword.len(), 4); // 2^2 blowup survives the descent
    assert!(reference_verify(&d, &[13], &proof, config(), &demo_spec()));
}

#[test]
fn wrong_statement_and_unsatisfied_witness_are_refused() {
    let (d, proof) = proof();
    assert!(!reference_verify(&d, &[14], &proof, config(), &demo_spec()));
    assert!(
        reference_prove(&d, &[14, 1, 0, 1, 1], config(), &demo_spec()).is_err(),
        "the honest prover refuses a nonzero gate claim"
    );
}

#[test]
fn every_composed_pillar_has_teeth() {
    let (d, good) = proof();
    let spec = demo_spec();

    let mut bad = good.clone();
    bad.trace[7] = (bad.trace[7] + 1) % P;
    assert!(
        !reference_verify(&d, &[13], &bad, config(), &spec),
        "trace tamper"
    );

    let mut bad = good.clone();
    bad.trace_root.limbs[0] = (bad.trace_root.limbs[0] + 1) % P;
    assert!(
        !reference_verify(&d, &[13], &bad, config(), &spec),
        "trace root tamper"
    );

    let mut bad = good.clone();
    bad.gate_sumcheck.rounds[1][0] = (bad.gate_sumcheck.rounds[1][0] + 1) % P;
    assert!(
        !reference_verify(&d, &[13], &bad, config(), &spec),
        "sumcheck tamper"
    );

    let mut bad = good.clone();
    bad.fri.round_commitments[2].limbs[0] = (bad.fri.round_commitments[2].limbs[0] + 1) % P;
    assert!(
        !reference_verify(&d, &[13], &bad, config(), &spec),
        "FRI root tamper"
    );

    let mut bad = good;
    bad.fri.query_openings[0].rounds[0].lo.c[0] =
        (bad.fri.query_openings[0].rounds[0].lo.c[0] + 1) % P;
    assert!(
        !reference_verify(&d, &[13], &bad, config(), &spec),
        "FRI opening tamper"
    );
}

#[test]
fn verifier_rejects_mismatched_carried_sumcheck_challenges() {
    let (d, mut proof) = proof();
    proof.gate_sumcheck.challenges[2] = (proof.gate_sumcheck.challenges[2] + 1) % P;
    assert!(!reference_verify(&d, &[13], &proof, config(), &demo_spec()));
}

#[test]
fn clear_trace_exact_gate_check_rejects_even_after_recommit() {
    let (d, mut proof) = proof();
    proof.trace[7] = (proof.trace[7] + 1) % P;
    proof.trace_root = commit_trace(&demo_spec(), &proof.trace, P).0;
    assert!(
        !reference_verify(&d, &[13], &proof, config(), &demo_spec()),
        "the reference verifier checks descriptor_holds, not only root consistency and batching"
    );
}

#[test]
fn malformed_public_split_returns_error_instead_of_panicking() {
    let mut d = demo();
    d.n_public = d.n_vars + 1;
    assert!(reference_prove(&d, &HONEST_VARS, config(), &demo_spec()).is_err());
}
