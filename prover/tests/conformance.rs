//! Conformance vectors against the Lean-emitted demo descriptor
//! (`prover/testdata/demo_descriptor.json`, written by the `#eval` in
//! `Compiler/EmitSerialize.lean` — the Lean writer is the only author of that file).
//!
//! Cross-checks, NOT verification: the Lean side DECIDED that `x = 13,
//! bits = (1,0,1,1)` satisfies the demo system and that `x = 14` admits no
//! satisfying wire vector at all; these tests check the Rust mirror agrees on the
//! same descriptor bytes. Agreement on vectors is all this establishes.

use std::path::Path;

use minidregg_prover::descriptor::Descriptor;
use minidregg_prover::trace::{descriptor_holds, gates_hold, generate_trace, zeros_hold};

const BABY_BEAR_P: u64 = 2_013_265_921; // 2^31 - 2^27 + 1, [PROVER-field]

/// The honest assignment the Lean side proved accepting: x = 13, bits (1,0,1,1).
const HONEST_VARS: [u64; 5] = [13, 1, 0, 1, 1];

fn demo() -> Descriptor {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/demo_descriptor.json");
    let d = Descriptor::from_file(Path::new(path)).expect("parse the Lean-written demo descriptor");
    d.validate().expect("demo descriptor well-formed (mirror of emit_wellFormed)");
    d
}

/// The reader sees exactly the object the Lean `#eval` measured: BabyBear, 1 public
/// of 5 variables, 18 gates each defining one of the 18 aux wires, 5 zero-checks.
#[test]
fn demo_header_matches_lean_emit() {
    let d = demo();
    assert_eq!(d.p, BABY_BEAR_P);
    assert_eq!(d.n_public, 1);
    assert_eq!(d.n_vars, 5);
    assert_eq!(d.n_wires, 23);
    assert_eq!(d.gates.len(), 18);
    assert_eq!(d.zeros.len(), 5);
}

/// Honest vector: the generated trace satisfies the same predicate the Lean side
/// proved satisfiable (`emit_accepts_iff` built the witness there; the trace
/// generator exhibits it concretely here).
#[test]
fn honest_trace_satisfies_descriptor() {
    let d = demo();
    let trace = generate_trace(&d, &HONEST_VARS);
    assert_eq!(trace.len(), d.n_wires as usize);
    assert!(descriptor_holds(&d, &trace), "honest trace must satisfy descriptorHolds");
}

/// Teeth, gate side: tampering ANY single wire of the honest trace is rejected.
/// (Every aux wire is exactly one gate's output — flatten_covers — so a +1 tamper
/// breaks that gate; every variable wire of this demo is read by some gate, so a
/// var tamper breaks a downstream gate or the recomposition root.)
#[test]
fn any_single_wire_tamper_fails() {
    let d = demo();
    let trace = generate_trace(&d, &HONEST_VARS);
    for w in 0..d.n_wires as usize {
        let mut t = trace.clone();
        t[w] = (t[w] + 1) % d.p;
        assert!(
            !descriptor_holds(&d, &t),
            "tampered wire {w} still satisfies the descriptor"
        );
    }
}

/// Teeth, zero-check side: a WRONG statement (x = 14 with bits summing to 13),
/// honestly traced. Every gate holds — the generator forces them by construction —
/// but the recomposition root is nonzero, so the zero-checks alone reject. The
/// Lean side decided the matching fact: no wire vector at all satisfies the
/// descriptor at x = 14.
#[test]
fn wrong_public_input_fails_zero_checks_only() {
    let d = demo();
    let trace = generate_trace(&d, &[14, 1, 0, 1, 1]);
    assert!(gates_hold(&d, &trace), "honestly traced gates hold by construction");
    assert!(!zeros_hold(&d, &trace), "the root zero-check must reject x = 14");
    assert!(!descriptor_holds(&d, &trace));
}

/// Teeth, booleanity: a non-boolean "bit" (b0 = 2, x = 2 so recomposition holds)
/// is rejected by the booleanity root's zero-check — 2·(2−1) = 2 ≠ 0.
#[test]
fn non_boolean_bit_fails() {
    let d = demo();
    let trace = generate_trace(&d, &[2, 2, 0, 0, 0]);
    assert!(gates_hold(&d, &trace));
    assert!(!zeros_hold(&d, &trace), "booleanity zero-check must reject bit = 2");
}
