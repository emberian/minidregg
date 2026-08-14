//! The zkML matmul contraction against the Lean-computed reference
//! (`prover/testdata/zkml_matmul_conformance.json`, written by the `#eval` in
//! `Assurance/ZkmlMatmulConformance.lean` — the Lean writer is the only author of
//! that file, and every value in it is additionally KERNEL-DECIDED there as a
//! NAMED theorem).
//!
//! Cross-checks, NOT verification. The Lean objects these numbers come from are
//! the ones the soundness theorems are about — `mle₂`, `rowPartial`, `colPartial`,
//! `matmulTable`, `cubicForm` at the contraction instance, and
//! `matmul_sumcheck_soundness` at `(μ+ν)/|F| + κ·3/|F|`. There is no formal
//! semantics of Rust, so agreement ON THESE VECTORS is the whole claim.
//!
//! ⚠ The vector deliberately pins the thing the naming mistake would hide: the
//! output table is the CONTRACTION `Σ_p A(a,p)·B(p,b)`, not the pointwise product.
//! A reader that computed `A·B` elementwise fails `output_matches_lean` on the
//! first entry.

use std::path::Path;

use serde::Deserialize;

use minidregg_prover::babybear::P;
use minidregg_prover::sumcheck::{
    cubic_round_sum_literal, mle2_eval, mle_eval, prove_matmul, verify_matmul, Fp, MatmulClaim,
};

/// Mirror of the file the Lean `#eval` writes.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct MatmulConformanceFile {
    p: u64,
    mu: usize,
    kappa: usize,
    nu: usize,
    degree: usize,
    table_a: Vec<Vec<Fp>>,
    table_b: Vec<Vec<Fp>>,
    x: Vec<Fp>,
    y: Vec<Fp>,
    challenges: Vec<Fp>,
    output: Vec<Vec<Fp>>,
    row_partial: Vec<Fp>,
    col_partial: Vec<Fp>,
    claim: Fp,
    mle2_output: Fp,
    rounds: Vec<Vec<Fp>>,
    openings: Vec<Fp>,
}

fn conformance() -> (MatmulConformanceFile, MatmulClaim) {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/zkml_matmul_conformance.json"
    );
    let s = std::fs::read_to_string(Path::new(path))
        .expect("read the Lean-written matmul conformance file");
    let c: MatmulConformanceFile =
        serde_json::from_str(&s).expect("parse the Lean-written matmul conformance file");
    assert_eq!(c.p, P, "the vector is over the prover's field");
    assert_eq!(c.degree, 3, "driven over the degree-3 rung");
    assert_eq!(c.x.len(), c.mu);
    assert_eq!(c.y.len(), c.nu);
    assert_eq!(c.challenges.len(), c.kappa);
    assert_eq!(c.rounds.len(), c.kappa);
    assert_eq!(c.openings.len(), 5);
    let claim = MatmulClaim {
        mu: c.mu,
        kappa: c.kappa,
        nu: c.nu,
        a: c.table_a.clone(),
        b: c.table_b.clone(),
    };
    (c, claim)
}

/// The true output table — the Lean `matmulTable`, `mmOutput_value`.
#[test]
fn output_matches_lean() {
    let (c, claim) = conformance();
    assert_eq!(claim.output(P), c.output);
}

/// The two folded tables — `rowPartial` / `colPartial`, `mmG_value` / `mmH_value`.
#[test]
fn partials_match_lean() {
    let (c, claim) = conformance();
    assert_eq!(claim.row_partial(&c.x, P), c.row_partial);
    assert_eq!(claim.col_partial(&c.y, P), c.col_partial);
}

/// **The contraction identity, on the vector.** `mle₂` of the output table at the
/// outer point equals the claimed total, and both equal the Lean numbers — the
/// numeric shadow of `mle₂_contraction` / `matmulClaim_is_contraction`.
#[test]
fn contraction_identity_matches_lean() {
    let (c, claim) = conformance();
    let target = mle2_eval(&c.output, &c.x, &c.y, P);
    assert_eq!(target, c.mle2_output, "mle₂ of the output table");
    assert_eq!(target, c.claim, "which IS the sumcheck's claimed total");
    let g = claim.row_partial(&c.x, P);
    let h = claim.col_partial(&c.y, P);
    let inner = (0..g.len()).fold(0u64, |acc, q| {
        (acc as u128 + (g[q] as u128 * h[q] as u128) % P as u128) as u64 % P
    });
    assert_eq!(inner, c.claim);
}

/// Every round message at the FOUR wire nodes, against the Lean `roundSum` of the
/// REAL `cubicForm` at the contraction instance. `h(1)` is one of the four: a
/// reader that reconstructed it as `claim − h(0)` would have made its own round
/// check a tautology and would still pass this test only by luck.
#[test]
fn rounds_match_lean() {
    let (c, claim) = conformance();
    let tabs = claim.tables(&c.x, &c.y, P);
    for (i, expected) in c.rounds.iter().enumerate() {
        for (t, &want) in expected.iter().enumerate() {
            assert_eq!(
                cubic_round_sum_literal(&tabs, &c.challenges, i, t as u64, P),
                want,
                "round {i} at node {t}"
            );
        }
    }
}

/// The five FACTORED openings — three of them the constants the verifier supplies
/// itself (`1, 0, 1`), two of them the real oracle openings. That split is the
/// whole cost argument for the contraction face, so it is pinned.
#[test]
fn openings_match_lean() {
    let (c, claim) = conformance();
    let tabs = claim.tables(&c.x, &c.y, P);
    let got = [
        mle_eval(&tabs.e, &c.challenges, P),
        mle_eval(&tabs.a, &c.challenges, P),
        mle_eval(&tabs.b, &c.challenges, P),
        mle_eval(&tabs.c, &c.challenges, P),
        mle_eval(&tabs.d, &c.challenges, P),
    ];
    assert_eq!(got.to_vec(), c.openings);
    assert_eq!(got[0], 1, "head is the constant 1 — no eq factor");
    assert_eq!(got[3], 0, "second pair is dead");
    assert_eq!(got[4], 1);
}

/// End to end on the Lean instance: the prover run at the Lean challenges emits
/// the Lean round messages, and the verifier accepts against the Lean output
/// table.
#[test]
fn prover_reproduces_the_lean_transcript() {
    let (c, claim) = conformance();
    let proof = prove_matmul(&claim, &c.x, &c.y, &c.challenges, P);
    assert_eq!(proof.claim, c.claim);
    for (i, expected) in c.rounds.iter().enumerate() {
        assert_eq!(proof.rounds[i].to_vec(), *expected, "round {i}");
    }
    let tabs = claim.tables(&c.x, &c.y, P);
    assert!(verify_matmul(
        &c.output,
        &c.x,
        &c.y,
        &proof,
        |r| (mle_eval(&tabs.a, r, P), mle_eval(&tabs.b, r, P)),
        P
    ));
}

/// ⚑ The contraction instance carries a degree-2 message on a degree-3 wire: the
/// third finite difference of every round message is ZERO on the Lean numbers, and
/// the second is not. Both are theorems in `Assurance/ZkmlMatmulConformance.lean`
/// (`matmulRounds_are_not_cubic`, `matmulRounds_are_quadratic`) — checked here on
/// the serialized values so the wire, not just the engine, carries the fact.
#[test]
fn lean_rounds_are_quadratic_not_cubic() {
    let (c, _) = conformance();
    let m = |a: u64, b: u64| ((a as u128 * b as u128) % P as u128) as u64;
    let sub = |a: u64, b: u64| ((a as u128 + P as u128 - b as u128) % P as u128) as u64;
    let add = |a: u64, b: u64| ((a as u128 + b as u128) % P as u128) as u64;
    for (i, h) in c.rounds.iter().enumerate() {
        let third = sub(add(h[3], m(3, h[1])), add(m(3, h[2]), h[0]));
        assert_eq!(third, 0, "round {i} has no cubic term");
        let second = sub(add(h[2], h[0]), m(2, h[1]));
        assert_ne!(second, 0, "round {i} is genuinely quadratic");
    }
}

/// A forged output table is refused, and the mutation is checked to be real before
/// the refusal is read — the `[MATMUL-forge]` tooth on the Lean vector itself.
#[test]
fn forged_output_refused_on_the_lean_vector() {
    let (c, claim) = conformance();
    let mut forged = c.output.clone();
    forged[0][0] = (forged[0][0] + 1) % P;
    assert_ne!(forged[0][0], c.output[0][0], "the mutation must be real");
    let proof = prove_matmul(&claim, &c.x, &c.y, &c.challenges, P);
    let tabs = claim.tables(&c.x, &c.y, P);
    assert!(!verify_matmul(
        &forged,
        &c.x,
        &c.y,
        &proof,
        |r| (mle_eval(&tabs.a, r, P), mle_eval(&tabs.b, r, P)),
        P
    ));
}
