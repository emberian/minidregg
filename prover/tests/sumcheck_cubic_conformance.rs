//! The degree-3 rung's conformance vectors against the Lean-computed reference
//! (`prover/testdata/sumcheck_cubic_conformance.json`, written by the `#eval` in
//! `Assurance/AirSumcheckCubicConformance.lean` — the Lean writer is the only
//! author of that file, and every value in it is additionally KERNEL-DECIDED
//! there as a NAMED theorem).
//!
//! Cross-checks, NOT verification: the Lean `cubicForm`/`roundSum` are the objects
//! the degree-3 soundness theorems are about (`cubic_sumcheck_soundness` at
//! `m·3/|F|`, `cubicRoundPoly_eval`, `scChain_cubicHonest_final`); these tests
//! establish that the Rust engine agrees with them ON THESE VECTORS. There is no
//! formal semantics of Rust, so vector agreement is the whole claim.

use std::path::Path;

use serde::Deserialize;

use minidregg_prover::babybear::P;
use minidregg_prover::sumcheck::{
    cubic_combine, cubic_round_evals, cubic_round_sum_literal, eval_lagrange,
    prove_cubic_sumcheck, verify_cubic_sumcheck, CubicTables, Fp,
};

/// Mirror of the file the Lean `#eval` writes: five LSB-first tables, the fixed
/// challenges, the claim, the per-round messages at the FOUR wire nodes
/// `t ∈ {0,1,2,3}`, and the five FACTORED terminal openings.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CubicConformanceFile {
    p: u64,
    m: usize,
    degree: usize,
    table_e: Vec<Fp>,
    table_a: Vec<Fp>,
    table_b: Vec<Fp>,
    table_c: Vec<Fp>,
    table_d: Vec<Fp>,
    challenges: Vec<Fp>,
    claim: Fp,
    rounds: Vec<Vec<Fp>>,
    openings: Vec<Fp>,
}

fn conformance() -> (CubicConformanceFile, CubicTables) {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/sumcheck_cubic_conformance.json"
    );
    let s = std::fs::read_to_string(Path::new(path))
        .expect("read the Lean-written cubic conformance file");
    let c: CubicConformanceFile =
        serde_json::from_str(&s).expect("parse the Lean-written cubic conformance file");
    assert_eq!(c.p, P, "the vector is over the prover's field");
    assert_eq!(c.degree, 3, "this is the degree-3 rung's vector");
    for t in [&c.table_e, &c.table_a, &c.table_b, &c.table_c, &c.table_d] {
        assert_eq!(t.len(), 1 << c.m);
    }
    assert_eq!(c.challenges.len(), c.m);
    assert_eq!(c.rounds.len(), c.m);
    assert_eq!(c.openings.len(), 5);
    let tabs = CubicTables {
        e: c.table_e.clone(),
        a: c.table_a.clone(),
        b: c.table_b.clone(),
        c: c.table_c.clone(),
        d: c.table_d.clone(),
    };
    (c, tabs)
}

/// **The claim and the five FACTORED openings.** The Rust engine reproduces the
/// Lean `Σ_b E(b)·(A(b)·B(b) + C(b)·D(b))` and each of `Ê(r), Â(r), B̂(r), Ĉ(r),
/// D̂(r)` — the five values `scChain_cubicHonest_final` says the verifier combines
/// itself, not one pre-combined number handed over by the prover.
#[test]
fn claim_and_openings_match_lean_reference() {
    let (c, tabs) = conformance();
    assert_eq!(tabs.claim(c.p), c.claim, "the Lean claim");
    let got = tabs.openings(&c.challenges, c.p);
    assert_eq!(got.to_vec(), c.openings, "the five Lean openings");
}

/// **The round-message conformance vector.** For every round and every wire node
/// `t ∈ {0,1,2,3}` the Rust literal mirror reproduces the Lean `roundSum
/// (cubicForm …)`. Round 1 is INTERIOR (challenge prefix and boolean suffix at
/// once — the full `glue` wiring); `t = 2, 3` are off the boolean pair, so the
/// vector pins the CUBIC shape rather than the two points a degree-1 reader fits.
#[test]
fn round_messages_match_lean_reference() {
    let (c, tabs) = conformance();
    for (i, evals) in c.rounds.iter().enumerate() {
        assert_eq!(evals.len(), 4, "Lean serializes t in {{0,1,2,3}}");
        for (t, &want) in evals.iter().enumerate() {
            assert_eq!(
                cubic_round_sum_literal(&tabs, &c.challenges, i, t as u64, c.p),
                want,
                "round {i} at t={t} must reproduce the Lean roundSum"
            );
        }
    }
}

/// **The FOLDED prover reproduces the Lean numbers too.** This is the load-bearing
/// one: the O(2^m) fast path is what a deployed prover runs, so it — not only the
/// literal mirror — must be the thing bound to Lean.
#[test]
fn folded_prover_matches_lean_reference() {
    let (c, tabs) = conformance();
    let proof = prove_cubic_sumcheck(&tabs, &c.challenges, c.p);
    assert_eq!(proof.claim, c.claim);
    for (i, h) in proof.rounds.iter().enumerate() {
        assert_eq!(h.to_vec(), c.rounds[i], "folded round {i} vs Lean");
    }
    assert!(
        verify_cubic_sumcheck(&proof, |pt| tabs.openings(pt, c.p), c.p),
        "the Lean-matching transcript verifies"
    );
}

/// **The chain identities on the LEAN numbers.** Non-vacuous: checked against the
/// serialized reference values themselves, so the vector really walks the chain
/// the Lean theorems describe — `cubicChain0` (`roundSum_zero` +
/// `cubicForm_cube_sum`), `cubicChainSucc0/1` (`roundSum_succ`), and
/// `cubicChainLast` (the FACTORED terminal value).
#[test]
fn chain_identities_hold_on_lean_reference_values() {
    let (c, _) = conformance();
    let add = |a: Fp, b: Fp| (a + b) % c.p;
    assert_eq!(
        add(c.rounds[0][0], c.rounds[0][1]),
        c.claim,
        "cubicChain0 on the vector"
    );
    for k in 0..c.m - 1 {
        let h_k_at_r = eval_lagrange(&c.rounds[k], c.challenges[k], c.p)
            .expect("BabyBear supports the {0,1,2,3} node set");
        assert_eq!(
            add(c.rounds[k + 1][0], c.rounds[k + 1][1]),
            h_k_at_r,
            "cubicChainSucc on the vector at k={k}"
        );
    }
    let final_fold = eval_lagrange(&c.rounds[c.m - 1], c.challenges[c.m - 1], c.p).unwrap();
    let mut o = [0u64; 5];
    o.copy_from_slice(&c.openings);
    assert_eq!(
        final_fold,
        cubic_combine(&o, c.p),
        "cubicChainLast on the vector: the last fold is the FACTORED terminal value"
    );
}

/// **The Lean messages are genuinely CUBIC**, mirroring `cubRounds_are_cubic`:
/// the third finite difference `h(3) − 3h(2) + 3h(1) − h(0)` is `6·(leading
/// coefficient)` and is NONZERO in every round. A reader that fitted a
/// degree-≤2 polynomial to these four points would disagree — so the vector
/// distinguishes a real degree-3 engine from a degree-2 one wearing the type.
#[test]
fn lean_round_messages_are_not_quadratic() {
    let (c, _) = conformance();
    let sub = |a: Fp, b: Fp| (a + c.p - b % c.p) % c.p;
    let mul = |a: Fp, b: Fp| ((a as u128 * b as u128) % c.p as u128) as u64;
    for (i, h) in c.rounds.iter().enumerate() {
        let d3 = sub(
            (h[3] + mul(3, h[1])) % c.p,
            (mul(3, h[2]) + h[0]) % c.p,
        );
        assert_ne!(d3, 0, "round {i} must have a nonzero cubic coefficient");
    }
}

/// **Tampering the vector's own numbers is caught.** Every one of the four wire
/// evaluations in every round is load-bearing — including `h(1)`, which a
/// p3-style verifier would have derived and therefore could not have checked.
#[test]
fn tampering_the_lean_vector_is_rejected() {
    let (c, tabs) = conformance();
    let good = prove_cubic_sumcheck(&tabs, &c.challenges, c.p);
    for i in 0..c.m {
        for j in 0..4 {
            let mut bad = good.clone();
            let before = bad.rounds[i][j];
            bad.rounds[i][j] = (before + 1) % c.p;
            assert_ne!(bad.rounds[i][j], before, "round {i} eval {j} unmutated");
            assert!(
                !verify_cubic_sumcheck(&bad, |pt| tabs.openings(pt, c.p), c.p),
                "tampered h_{i}({j}) rejected"
            );
        }
    }
    let mut bad = good;
    bad.claim = (bad.claim + 1) % c.p;
    assert!(!verify_cubic_sumcheck(
        &bad,
        |pt| tabs.openings(pt, c.p),
        c.p
    ));
}

/// **The folded and literal paths agree on the vector's own instance**, so the
/// speedup accelerates the Lean-mirroring computation rather than replacing it.
#[test]
fn folded_and_literal_paths_agree_on_the_vector() {
    let (c, tabs) = conformance();
    let mut state = tabs.clone();
    for i in 0..c.m {
        let folded = cubic_round_evals(&state, c.p);
        for (t, &got) in folded.iter().enumerate() {
            assert_eq!(
                got,
                cubic_round_sum_literal(&tabs, &c.challenges, i, t as u64, c.p),
                "round {i} t {t}"
            );
        }
        state = CubicTables {
            e: minidregg_prover::sumcheck::fold_table(&state.e, c.challenges[i], c.p),
            a: minidregg_prover::sumcheck::fold_table(&state.a, c.challenges[i], c.p),
            b: minidregg_prover::sumcheck::fold_table(&state.b, c.challenges[i], c.p),
            c: minidregg_prover::sumcheck::fold_table(&state.c, c.challenges[i], c.p),
            d: minidregg_prover::sumcheck::fold_table(&state.d, c.challenges[i], c.p),
        };
    }
}
