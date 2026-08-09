//! One focused smoke for the isolated Ext6 factored-gate algebra.

use std::path::Path;

use minidregg_prover::{
    descriptor::Descriptor,
    field4::P,
    field6::Ext6,
    gate_kernels::{batch_lifted_residuals, descriptor_defect_table, table_sum},
    trace::generate_trace,
};

// Let the path-loaded, not-yet-exported runtime module resolve its future
// `crate::descriptor` / `crate::field*` imports in this integration-test crate.
mod descriptor {
    pub use minidregg_prover::descriptor::*;
}
mod field4 {
    pub use minidregg_prover::field4::*;
}
mod field6 {
    pub use minidregg_prover::field6::*;
}
#[path = "../src/outer_factored_gate.rs"]
mod outer_factored_gate;

use outer_factored_gate::{
    build_factored_gate_tables, evaluate_quadratic, terminal_operand_selectors,
    QuadraticGateSumcheckState,
};

fn ext(limbs: [u64; 6]) -> Ext6 {
    Ext6::try_from_limbs(limbs).expect("canonical Ext6 smoke value")
}

#[test]
fn factored_gate_claim_streams_to_public_trace_selectors() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/demo_descriptor.json");
    let descriptor = Descriptor::from_file(Path::new(path)).expect("Lean-emitted descriptor");
    let mut trace = generate_trace(&descriptor, &[13, 1, 0, 1, 1]);
    trace[6] = (trace[6] + 1) % P;

    let gamma = ext([17, 1, 0, 0, 0, 0]);
    let challenges = [
        ext([2, 1, 0, 0, 0, 0]),
        ext([3, 0, 1, 0, 0, 0]),
        ext([5, 0, 0, 1, 0, 0]),
        ext([7, 0, 0, 0, 1, 0]),
        ext([11, 0, 0, 0, 0, 1]),
    ];

    let residuals = descriptor_defect_table(&descriptor, &trace).unwrap();
    let existing = batch_lifted_residuals::<Ext6>(&residuals, gamma)
        .and_then(|table| table_sum(&table))
        .expect("existing gamma-batched claim");

    let tables = build_factored_gate_tables(&descriptor, &trace, gamma).unwrap();
    assert_eq!(tables.cube_dim().unwrap(), challenges.len());
    assert_eq!(tables.cube_sum().unwrap(), existing);
    assert!(
        !existing.is_zero(),
        "the fixed tamper must survive this gamma"
    );

    let mut state = QuadraticGateSumcheckState::new(tables).unwrap();
    let mut running_claim = existing;
    for &challenge in &challenges {
        let message = state.round_message().unwrap();
        assert_eq!(message[0].add(message[1]), running_claim);
        running_claim = evaluate_quadratic(message, challenge);
        state.bind(challenge).unwrap();
        assert_eq!(state.claim().unwrap(), running_claim);
    }

    assert_eq!(state.rounds_remaining(), 0);
    let terminal = state.terminal().unwrap();
    assert_eq!(terminal.polynomial_value(), running_claim);

    let selectors = terminal_operand_selectors(&descriptor, gamma, &challenges).unwrap();
    let selected = selectors.evaluate(&trace).unwrap();
    assert_eq!(selected, terminal);
    assert_eq!(selected.polynomial_value(), running_claim);
}
