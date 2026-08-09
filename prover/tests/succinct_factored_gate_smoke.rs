use minidregg_prover::{
    descriptor::{Descriptor, Gate, GateOp, Wire},
    field4::P,
    field6::Ext6,
};

// The protocol is path-loaded until its one-line `lib.rs` integration lands.
mod binary_hash {
    pub use minidregg_prover::binary_hash::*;
}
mod descriptor {
    pub use minidregg_prover::descriptor::*;
}
mod field4 {
    pub use minidregg_prover::field4::*;
}
mod field6 {
    pub use minidregg_prover::field6::*;
}
mod multiplicative_mle_terminal {
    pub use minidregg_prover::multiplicative_mle_terminal::*;
}
mod outer_factored_gate {
    pub use minidregg_prover::outer_factored_gate::*;
}
mod trace_linear_ext6 {
    pub use minidregg_prover::trace_linear_ext6::*;
}
mod transcript_ext6 {
    pub use minidregg_prover::transcript_ext6::*;
}
#[path = "../src/succinct_factored_gate.rs"]
mod succinct_factored_gate;

use succinct_factored_gate::prove_with_extension_cell_for_test;
use succinct_factored_gate::{prove_succinct_factored_gate, verify_succinct_factored_gate};

#[test]
fn succinct_factored_gate_roundtrip_rejects_an_unrelated_trace_splice() {
    // Wire 4 is intentionally private and unconstrained: changing it gives a
    // second valid witness with the same public statement and a different trace
    // root.  Splicing that independently valid opening into the first outer
    // proof must fail because the root was bound before gamma.  Public wire 1 is
    // also unreferenced, so its substitution specifically tests that the full
    // public prefix is included in the aggregated trace opening.
    let descriptor = Descriptor {
        p: P,
        n_public: 2,
        n_vars: 5,
        n_wires: 7,
        gates: vec![
            Gate {
                op: GateOp::Add,
                a: Wire::Wire(0),
                b: Wire::Wire(2),
                out: 5,
            },
            Gate {
                op: GateOp::Mul,
                a: Wire::Wire(5),
                b: Wire::Wire(3),
                out: 6,
            },
        ],
        zeros: vec![],
    };
    let public = [7, 50];
    let trace_a = [7, 50, 2, 3, 11, 9, 27];
    let trace_b = [7, 50, 2, 3, 12, 9, 27];
    let substituted_public = [7, 51];
    let trace_public_substitution = [7, 51, 2, 3, 11, 9, 27];

    let proof_a = prove_succinct_factored_gate(&descriptor, &public, &trace_a, 2, 4).unwrap();
    let proof_b = prove_succinct_factored_gate(&descriptor, &public, &trace_b, 2, 4).unwrap();
    assert!(verify_succinct_factored_gate(&descriptor, &public, 2, 4, &proof_a).unwrap());
    assert!(verify_succinct_factored_gate(&descriptor, &public, 2, 4, &proof_b).unwrap());
    assert_ne!(proof_a.trace_root, proof_b.trace_root);

    let mut spliced = proof_a.clone();
    spliced.trace_root = proof_b.trace_root;
    spliced.trace_linear_statement = proof_b.trace_linear_statement;
    spliced.trace_linear_proof = proof_b.trace_linear_proof;
    assert!(!verify_succinct_factored_gate(&descriptor, &public, 2, 4, &spliced).unwrap());

    let public_substitution = prove_succinct_factored_gate(
        &descriptor,
        &substituted_public,
        &trace_public_substitution,
        2,
        4,
    )
    .unwrap();
    assert!(verify_succinct_factored_gate(
        &descriptor,
        &substituted_public,
        2,
        4,
        &public_substitution,
    )
    .unwrap());
    assert!(
        !verify_succinct_factored_gate(&descriptor, &public, 2, 4, &public_substitution,).unwrap()
    );

    let extension_value =
        Ext6::try_from_limbs([11, 1, 0, 0, 0, 0]).expect("canonical extension value");
    let extension_trace = prove_with_extension_cell_for_test(
        &descriptor,
        &public,
        &trace_a,
        4,
        extension_value,
        2,
        4,
    )
    .unwrap();
    assert!(extension_trace
        .trace_linear_proof
        .table_mle_proof
        .queries
        .iter()
        .flat_map(|query| query.rounds.first())
        .any(|opening| {
            opening.low.limbs()[1..].iter().any(|&limb| limb != 0)
                || opening.high.limbs()[1..].iter().any(|&limb| limb != 0)
        }));
    assert!(!verify_succinct_factored_gate(&descriptor, &public, 2, 4, &extension_trace).unwrap());
}
