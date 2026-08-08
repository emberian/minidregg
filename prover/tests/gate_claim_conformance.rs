//! `[PROVER-sumcheck-gates]` conformance on the REAL emitted demo descriptor
//! (`prover/testdata/demo_descriptor.json`, written by the Lean `#eval` in
//! `Compiler/EmitSerialize.lean`): the gate system's defect table is all-zero on
//! the honest trace exactly when `descriptor_holds` is (the mirror of the Lean
//! faithfulness iffs `addGateLin_iff`/`mulConstraint_iff`/`rootZero_iff`), the
//! batched gate sumcheck round-trips, and tampers are genuinely caught.
//!
//! Cross-checks, NOT verification: the soundness bound a tamper is caught at is
//! the Lean's `airGateSystem_sound`; these vectors only check the Rust encoding
//! computes the claim object that theorem prices.

use std::path::Path;

use minidregg_prover::descriptor::Descriptor;
use minidregg_prover::gate_claim::{
    batch_defect_table, gate_claim_len, gate_cube_dim, gate_defect_table, prove_gates,
    verify_gates,
};
use minidregg_prover::sumcheck::{mle_eval, verify_sumcheck};
use minidregg_prover::trace::{descriptor_holds, generate_trace};

/// The honest assignment the Lean side proved accepting: x = 13, bits (1,0,1,1).
const HONEST_VARS: [u64; 5] = [13, 1, 0, 1, 1];

/// Fixed batching + round challenges (caller-supplied until [PROVER-fs]).
const GAMMA: u64 = 0x0102_0304;
const CHAL: [u64; 5] = [17, 4242, 99_991, 123_456_789, 987_654_321];

fn demo() -> Descriptor {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/demo_descriptor.json");
    let d = Descriptor::from_file(Path::new(path)).expect("parse the Lean-written demo descriptor");
    d.validate().expect("demo descriptor well-formed");
    d
}

/// 18 gates + 5 zero-checks pad to the 2^5 hypercube: 5 sumcheck rounds.
#[test]
fn demo_claim_dimensions() {
    let d = demo();
    assert_eq!(gate_claim_len(&d), 32);
    assert_eq!(gate_cube_dim(&d), 5);
}

/// Honest vector: the defect table vanishes entirely — every gate's defect and
/// every zero-check's read is 0 — and the batched sumcheck round-trips at claim 0.
#[test]
fn honest_trace_zero_table_and_round_trip() {
    let d = demo();
    let w = generate_trace(&d, &HONEST_VARS);
    let table = gate_defect_table(&d, &w);
    assert!(table.iter().all(|&v| v == 0), "honest defect table must be all-zero");
    assert!(descriptor_holds(&d, &w));

    let proof = prove_gates(&d, &w, GAMMA, &CHAL);
    assert_eq!(proof.claim, 0, "honest batched gate claim is 0");
    let batched = batch_defect_table(&table, GAMMA, d.p);
    assert!(verify_gates(&proof, |pt| mle_eval(&batched, pt, d.p), d.p));
}

/// The mirror cross-check, on every single-wire tamper of the honest trace:
/// all-zero defect table ⟺ descriptor_holds. (Both false on each tamper — every
/// wire of this demo is genuinely constrained.)
#[test]
fn table_zero_iff_descriptor_holds_under_tampers() {
    let d = demo();
    let honest = generate_trace(&d, &HONEST_VARS);
    for wi in 0..honest.len() {
        let mut w = honest.clone();
        w[wi] = (w[wi] + 1) % d.p;
        let table = gate_defect_table(&d, &w);
        assert_eq!(
            table.iter().all(|&v| v == 0),
            descriptor_holds(&d, &w),
            "wire {wi}: table-zero must mirror descriptorHolds"
        );
        assert!(!descriptor_holds(&d, &w), "wire {wi} tamper must violate the descriptor");
    }
}

/// Teeth: every single-wire tamper makes the batched claim nonzero at the fixed
/// γ and `verify_gates` reject — while the sumcheck TRANSCRIPT itself stays
/// internally consistent (the prover is honest about the nonzero sum): the
/// zero-claim check is exactly where the gate system bites.
#[test]
fn every_single_wire_tamper_caught() {
    let d = demo();
    let honest = generate_trace(&d, &HONEST_VARS);
    for wi in 0..honest.len() {
        let mut w = honest.clone();
        w[wi] = (w[wi] + 1) % d.p;
        let proof = prove_gates(&d, &w, GAMMA, &CHAL);
        assert_ne!(proof.claim, 0, "wire {wi}: batched defect sum must be nonzero at fixed γ");
        let batched = batch_defect_table(&gate_defect_table(&d, &w), GAMMA, d.p);
        assert!(
            verify_sumcheck(&proof, |pt| mle_eval(&batched, pt, d.p), d.p),
            "wire {wi}: the transcript is honest about its (nonzero) sum"
        );
        assert!(
            !verify_gates(&proof, |pt| mle_eval(&batched, pt, d.p), d.p),
            "wire {wi}: verify_gates must reject a nonzero gate claim"
        );
    }
}

/// The zero-check fold-in is load-bearing: x = 14 with bits summing to 13,
/// honestly traced — every GATE defect is 0 (the generator forces the gates),
/// but the recomposition root's zero-check entry is hot: wire 22 reads
/// 13 − 14 = −1 = p − 1. Caught only because zero-checks are table entries.
#[test]
fn wrong_public_input_caught_by_zero_check_entries() {
    let d = demo();
    let w = generate_trace(&d, &[14, 1, 0, 1, 1]);
    let table = gate_defect_table(&d, &w);
    assert!(
        table[..d.gates.len()].iter().all(|&v| v == 0),
        "honestly traced gates leave zero gate defects"
    );
    assert!(
        table[d.gates.len()..].iter().any(|&v| v != 0),
        "a zero-check entry must be nonzero"
    );
    // The root zero-check is zeros[4] = wire 22: recomposition − x = 13 − 14.
    assert_eq!(table[d.gates.len() + 4], d.p - 1);

    let proof = prove_gates(&d, &w, GAMMA, &CHAL);
    let batched = batch_defect_table(&table, GAMMA, d.p);
    assert!(!verify_gates(&proof, |pt| mle_eval(&batched, pt, d.p), d.p));
}

/// A lying prover forging claim = 0 over a tampered trace's table is caught by
/// the sumcheck round checks themselves.
#[test]
fn forged_zero_claim_rejected() {
    let d = demo();
    let mut w = generate_trace(&d, &HONEST_VARS);
    w[6] = (w[6] + 1) % d.p; // tamper a zero-checked wire
    let mut proof = prove_gates(&d, &w, GAMMA, &CHAL);
    proof.claim = 0;
    let batched = batch_defect_table(&gate_defect_table(&d, &w), GAMMA, d.p);
    assert!(!verify_gates(&proof, |pt| mle_eval(&batched, pt, d.p), d.p));
}
