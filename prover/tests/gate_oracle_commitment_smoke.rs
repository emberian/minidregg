//! One smoke/teeth test for the full-opening gate-to-oracle join.

use std::path::Path;

use minidregg_prover::commit::{commit_trace, open};
use minidregg_prover::descriptor::Descriptor;
use minidregg_prover::field4::P;
use minidregg_prover::gate_oracle_commitment::{
    prove_committed_gate_oracle, verify_committed_gate_oracle, CommittedGateOracleProof,
    GateOracleOpening,
};
use minidregg_prover::poseidon::demo_spec;
use minidregg_prover::sumcheck::prove_sumcheck;
use minidregg_prover::trace::generate_trace;

#[test]
fn committed_gate_oracle_roundtrip_and_wrong_terminal_or_root_reject() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/demo_descriptor.json");
    let descriptor = Descriptor::from_file(Path::new(path)).expect("parse Lean-emitted descriptor");
    let trace = generate_trace(&descriptor, &[13, 1, 0, 1, 1]);
    let gamma = 17;
    let challenges = [2, 3, 5, 7, 11];
    let spec = demo_spec();
    let proof =
        prove_committed_gate_oracle(&descriptor, &trace, gamma, &challenges, &spec, P).unwrap();
    assert!(verify_committed_gate_oracle(
        &descriptor,
        &trace,
        gamma,
        &proof,
        &spec,
        P
    ));

    let mut wrong_root = proof.clone();
    wrong_root.oracle_root.limbs[0] = (wrong_root.oracle_root.limbs[0] + 1) % P;
    assert!(!verify_committed_gate_oracle(
        &descriptor,
        &trace,
        gamma,
        &wrong_root,
        &spec,
        P
    ));

    // A fully self-consistent *wrong* oracle: sum remains zero, its own
    // sumcheck and Merkle root/openings agree, but it is not the descriptor's
    // materialized residual table.  The join's equality check must reject it.
    let mut wrong_oracle = vec![0; proof.oracle_openings.len()];
    wrong_oracle[0] = 1;
    wrong_oracle[1] = P - 1;
    let (root, tree) = commit_trace(&spec, &wrong_oracle, P);
    let forged = CommittedGateOracleProof {
        oracle_root: root,
        oracle_openings: wrong_oracle
            .iter()
            .enumerate()
            .map(|(index, &value)| GateOracleOpening {
                index,
                value,
                path: open(&tree, index),
            })
            .collect(),
        gate_sumcheck: prove_sumcheck(&wrong_oracle, &challenges, P),
    };
    assert_eq!(forged.gate_sumcheck.claim, 0);
    assert!(!verify_committed_gate_oracle(
        &descriptor,
        &trace,
        gamma,
        &forged,
        &spec,
        P
    ));

    let mut wrong_terminal = proof;
    wrong_terminal.gate_sumcheck.rounds[4][0] = (wrong_terminal.gate_sumcheck.rounds[4][0] + 1) % P;
    assert!(!verify_committed_gate_oracle(
        &descriptor,
        &trace,
        gamma,
        &wrong_terminal,
        &spec,
        P
    ));
}
