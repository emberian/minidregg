//! `[PROVER-sumcheck]` conformance vectors against the Lean-computed MLE/roundSum
//! reference (`prover/testdata/sumcheck_conformance.json`, written by the `#eval`
//! in `Compiler/SumcheckConformance.lean` — the Lean writer is the only author of
//! that file; every value there is additionally KERNEL-DECIDED in that file).
//!
//! Cross-checks, NOT verification: the Lean `mle`/`roundSum` are the objects the
//! sumcheck soundness theorems are about (`mle_sumcheck_soundness`,
//! `roundSum_zero`/`_succ`/`_last`); these tests establish that the Rust engine
//! agrees with them ON THESE VECTORS. There is no formal semantics of Rust, so
//! vector agreement is the whole claim.

use std::path::Path;

use serde::Deserialize;

use minidregg_prover::babybear::P;
use minidregg_prover::sumcheck::{
    eval_affine, mle_eval, prove_sumcheck, round_poly, round_sum, verify_sumcheck, Fp,
};

/// Mirror of the conformance file the Lean `#eval` writes: the table (LSB-first,
/// index bit i = coordinate i), the fixed challenges, and the Lean-computed
/// claim / round messages (`t ∈ {0,1,2}`) / MLE probe values.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ConformanceFile {
    p: u64,
    m: usize,
    table: Vec<Fp>,
    challenges: Vec<Fp>,
    claim: Fp,
    rounds: Vec<Vec<Fp>>,
    mle_at_challenges: Fp,
    extra_point: Vec<Fp>,
    mle_at_extra_point: Fp,
}

fn conformance() -> ConformanceFile {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/sumcheck_conformance.json"
    );
    let s = std::fs::read_to_string(Path::new(path))
        .expect("read the Lean-written sumcheck conformance file");
    let c: ConformanceFile =
        serde_json::from_str(&s).expect("parse the Lean-written sumcheck conformance file");
    assert_eq!(c.p, P, "the vector is over the prover's field");
    assert_eq!(c.table.len(), 1 << c.m);
    assert_eq!(c.challenges.len(), c.m);
    assert_eq!(c.rounds.len(), c.m);
    c
}

/// **The MLE conformance vector**: the Rust `mle_eval` reproduces the Lean `mle`
/// at both probe points — the challenge point (the final oracle value) and an
/// unrelated off-cube point (pinning `mle_eval` with no round structure in play).
/// All 8 table values are distinct, so an index-convention flip fails here.
#[test]
fn mle_eval_matches_lean_reference() {
    let c = conformance();
    assert_eq!(
        mle_eval(&c.table, &c.challenges, c.p),
        c.mle_at_challenges,
        "Rust mle_eval must reproduce the Lean mle at the challenge point"
    );
    assert_eq!(
        mle_eval(&c.table, &c.extra_point, c.p),
        c.mle_at_extra_point,
        "Rust mle_eval must reproduce the Lean mle at the extra probe point"
    );
}

/// **The round-message conformance vector**: for every round i and t ∈ {0,1,2},
/// the Rust `round_sum` reproduces the Lean `roundSum`. Round 1 is an INTERIOR
/// round (challenge prefix + boolean suffix at once — the full glue wiring); the
/// t = 2 column checks agreement beyond the two points that define the affine
/// message.
#[test]
fn round_sum_matches_lean_reference() {
    let c = conformance();
    for (i, evals) in c.rounds.iter().enumerate() {
        assert_eq!(evals.len(), 3, "Lean serializes t in {{0,1,2}}");
        for (t, &want) in evals.iter().enumerate() {
            assert_eq!(
                round_sum(&c.table, &c.challenges, i, t as u64, c.p),
                want,
                "round {i} at t={t} must reproduce the Lean roundSum"
            );
        }
        // round_poly is the [g(0), g(1)] slice of the same values.
        assert_eq!(
            round_poly(&c.table, &c.challenges, i, c.p),
            evals[..2].to_vec()
        );
    }
}

/// **The chain identities on the LEAN numbers** (non-vacuous: checked on the
/// reference values themselves, so the vector actually walks the chain the Lean
/// theorems describe): `g₀(0)+g₀(1) = claim` (`roundSum_zero`),
/// `g_{k+1}(0)+g_{k+1}(1) = g_k(r_k)` (`roundSum_succ`), and the last fold
/// `g_{m−1}(r_{m−1}) = f̂(r)` (`roundSum_last`). The affine fold at `r_k` is also
/// cross-checked against the Lean t = 2 column.
#[test]
fn chain_identities_hold_on_lean_reference_values() {
    let c = conformance();
    let add = |a: Fp, b: Fp| (a + b) % c.p;
    assert_eq!(
        add(c.rounds[0][0], c.rounds[0][1]),
        c.claim,
        "roundSum_zero on the vector"
    );
    for k in 0..c.m - 1 {
        let g_k_at_r = eval_affine(&c.rounds[k][..2], c.challenges[k], c.p);
        assert_eq!(
            add(c.rounds[k + 1][0], c.rounds[k + 1][1]),
            g_k_at_r,
            "roundSum_succ on the vector at k={k}"
        );
        // The affine interpolation matches the Lean t = 2 evaluation.
        assert_eq!(
            eval_affine(&c.rounds[k][..2], 2, c.p),
            c.rounds[k][2],
            "affine message consistent with the Lean t=2 column at round {k}"
        );
    }
    assert_eq!(
        eval_affine(&c.rounds[c.m - 1][..2], c.challenges[c.m - 1], c.p),
        c.mle_at_challenges,
        "roundSum_last on the vector: the final fold is f̂(r)"
    );
}

/// **Prove → verify on the vector**: the honest transcript on the Lean table and
/// challenges reproduces the Lean claim and round messages, and verifies against
/// the MLE oracle; tampering any round message or the claim fails. This is the
/// card-1 gate: the roundtrip where the verifier semantics are Selvage's
/// (`SumcheckAccepts`), bound to Lean by this vector.
#[test]
fn prove_verify_on_the_vector() {
    let c = conformance();
    let proof = prove_sumcheck(&c.table, &c.challenges, c.p);
    assert_eq!(
        proof.claim, c.claim,
        "the transcript's claim is the Lean claim"
    );
    for (i, g) in proof.rounds.iter().enumerate() {
        assert_eq!(
            g[..],
            c.rounds[i][..2],
            "round {i} message matches the Lean reference"
        );
    }
    let oracle = |pt: &[Fp]| mle_eval(&c.table, pt, c.p);
    assert!(
        verify_sumcheck(&proof, oracle, c.p),
        "honest transcript verifies"
    );

    for i in 0..c.m {
        for j in 0..2 {
            let mut bad = proof.clone();
            bad.rounds[i][j] = (bad.rounds[i][j] + 1) % c.p;
            assert!(
                !verify_sumcheck(&bad, oracle, c.p),
                "tampered g_{i}({j}) rejected"
            );
        }
    }
    let mut bad = proof;
    bad.claim = (bad.claim + 1) % c.p;
    assert!(!verify_sumcheck(&bad, oracle, c.p), "false claim rejected");
}

/// **Challenge-tampering, both edges of the Selvage semantics.** A tampered
/// NON-final challenge is rejected: the verifier re-folds `g₀` at the tampered
/// `r₀'`, and round 1's boolean check `g₁(0)+g₁(1) = g₀(r₀')` fails because the
/// honest `g₁` targets `g₀(r₀)` and `g₀` is affine with nonzero slope on this
/// vector (injective). A tampered FINAL challenge is ACCEPTED, and that is the
/// Lean semantics, not a hole: by `roundSum_last`, `g_{m−1}(t) = f̂(r₀,…,r_{m−2},t)`
/// for EVERY `t`, so the transcript is an honest proof of the same (true) claim
/// at a different evaluation point. Binding the challenges to the transcript is
/// Fiat-Shamir's job — `[PROVER-fs]`/`[RECURSE-fs-*]`, not this rung.
#[test]
fn challenge_tampering_matches_selvage_semantics() {
    let c = conformance();
    let proof = prove_sumcheck(&c.table, &c.challenges, c.p);
    let oracle = |pt: &[Fp]| mle_eval(&c.table, pt, c.p);

    // The vector's g₀ has nonzero slope (g₀(0) ≠ g₀(1)), so the rejection below
    // is forced, not probabilistic luck — assert the premise too.
    assert_ne!(
        proof.rounds[0][0], proof.rounds[0][1],
        "vector premise: g₀ is affine with nonzero slope"
    );
    let mut bad = proof.clone();
    bad.challenges[0] = (bad.challenges[0] + 1) % c.p;
    assert!(
        !verify_sumcheck(&bad, oracle, c.p),
        "tampered non-final challenge rejected at round 1's boolean check"
    );

    let mut last = proof;
    let m = c.m;
    last.challenges[m - 1] = (last.challenges[m - 1] + 1) % c.p;
    assert!(
        verify_sumcheck(&last, oracle, c.p),
        "tampered final challenge accepted — roundSum_last: the last message \
         is the correct affine polynomial at every t; challenge binding is FS's"
    );
}
