//! `[PROVER-commit]` conformance vectors against the Lean-computed Poseidon
//! reference (`prover/testdata/poseidon_conformance.json`, written by the `#eval`
//! in `Compiler/EmitSerialize.lean` §6 — the Lean writer is the only author of
//! that file; the `permOutput` there is additionally KERNEL-DECIDED in that file).
//!
//! Cross-checks, NOT verification: the Lean `permExec` is the executor the
//! verified gadget was proved equal to (`permGadget_eval`); these tests establish
//! that the Rust `perm` agrees with it ON THESE VECTORS. There is no formal
//! semantics of Rust, so vector agreement is the whole claim.

use std::path::Path;

use serde::Deserialize;

use minidregg_prover::commit::{commit_trace, open, verify_open};
use minidregg_prover::descriptor::{Descriptor, Fp};
use minidregg_prover::poseidon::{demo_spec, hash, perm, PermSpec, BABY_BEAR_P};
use minidregg_prover::trace::generate_trace;

/// Mirror of the conformance file the Lean `#eval` writes: the spec, the input,
/// and the Lean-computed `permExec`/`hashExec` outputs.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ConformanceFile {
    p: u64,
    spec: PermSpec,
    input: Vec<Fp>,
    perm_output: Vec<Fp>,
    hash_output: Fp,
}

fn conformance() -> ConformanceFile {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/poseidon_conformance.json");
    let s = std::fs::read_to_string(Path::new(path))
        .expect("read the Lean-written poseidon conformance file");
    serde_json::from_str(&s).expect("parse the Lean-written poseidon conformance file")
}

/// The Rust-side fixed spec IS the spec the Lean side instantiated — sameness is
/// checked field by field, not asserted in prose.
#[test]
fn rust_demo_spec_is_the_lean_spec() {
    let c = conformance();
    assert_eq!(c.p, BABY_BEAR_P);
    c.spec.validate(c.p).expect("Lean-written spec well-shaped");
    assert_eq!(c.spec, demo_spec(), "Rust demo_spec must equal the Lean proverPermSpec");
}

/// **The conformance vector**: the Rust permutation reproduces the Lean
/// `permExec` output on the shared spec + input. The matrices are non-symmetric
/// and per-round distinct, so this pins the add-rc → S-box → linear-layer order,
/// the row/column orientation, and the schedule wiring — a transposed or
/// reordered mirror fails this test.
#[test]
fn perm_matches_lean_reference() {
    let c = conformance();
    assert_eq!(
        perm(&c.spec, &c.input, c.p),
        c.perm_output,
        "Rust perm must reproduce the Lean permExec output"
    );
    assert_eq!(hash(&c.spec, &c.input, c.p), c.hash_output);
    // And through the Rust-side fixed spec (already checked equal):
    assert_eq!(perm(&demo_spec(), &c.input, c.p), c.perm_output);
}

/// `[PROVER-commit]` end-to-end on the REAL rung-2 artifact: commit the trace
/// generated from the Lean-emitted demo descriptor, open every leaf, verify;
/// tamper every leaf, reject. The commitment hash in play is the conformance-
/// checked permutation above.
#[test]
fn demo_trace_commits_opens_verifies() {
    let d = Descriptor::from_file(Path::new(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/demo_descriptor.json"
    )))
    .expect("parse the Lean-written demo descriptor");
    d.validate().expect("demo descriptor well-formed");
    let trace = generate_trace(&d, &[13, 1, 0, 1, 1]);
    let spec = demo_spec();

    let (root, tree) = commit_trace(&spec, &trace, d.p);
    let (root2, _) = commit_trace(&spec, &trace, d.p);
    assert_eq!(root, root2, "commitment root deterministic");

    for (i, &leaf) in trace.iter().enumerate() {
        let path = open(&tree, i);
        assert!(verify_open(root, i, leaf, &path, &spec, d.p), "leaf {i} opening verifies");
        let tampered = (leaf + 1) % d.p;
        assert!(!verify_open(root, i, tampered, &path, &spec, d.p), "tampered leaf {i} rejected");
    }
}
