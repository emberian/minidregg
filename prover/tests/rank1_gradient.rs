//! Conformance: the Rust rank-1 gradient check against the F₅ numbers the Lean
//! `Selvage/Rank1GradientCheck.lean` teeth `decide`.
//!
//! **What binds what.** Lean owns the constraint semantics: `rank1_complete`,
//! `rank1_sound` (`(mi+mj)/|F|`), `rank1_refuses_other_outer_products` and the F₅
//! teeth are theorems there. This file re-computes the SAME 2×2 layer in Rust and
//! asserts the SAME numerals — including the two accept COUNTS, which the Lean
//! side proves by `decide` over all 25 challenges. Agreement on these vectors is
//! the whole claim; it is not refinement and there is no formal semantics of Rust.
//!
//! ⚠ The counts alone cannot see a TRANSPOSED row/column convention (the wrong
//! gradient's accepting set is symmetric), so the asymmetric witness pair below —
//! accept at `(1,2)`, refuse at `(2,1)` — is the test that actually pins the
//! index order, and both sides carry it.
//!
//! The layer: `δ = (1,2)` so `δ̂(t) = 1 + t`; `x = (3,4)` so `x̂(t) = 3 + t`;
//! `∇W = δ⊗x` is `[3,1,4,3]` LSB-first (row = bit 0, column = bit 1).

use minidregg_prover::rank1::{
    mle_eval_folded, outer_table, rank1_accepts, rank1_openings, sgd_step_accepts, sgd_step_table,
    split_point,
};

const P: u64 = 5;

/// Lean `Rank1Example.dv`.
fn dv() -> Vec<u64> {
    vec![1, 2]
}

/// Lean `Rank1Example.xv`.
fn xv() -> Vec<u64> {
    vec![3, 4]
}

/// Lean `Rank1Example.dv'` — a different backpropagated error.
fn dv_other() -> Vec<u64> {
    vec![1, 3]
}

/// Lean `Rank1Example.gWrong` — the true gradient with the `(1,1)` entry off by
/// one.
fn g_wrong() -> Vec<u64> {
    let mut g = outer_table(&dv(), &xv(), P);
    g[3] = (g[3] + 1) % P;
    g
}

fn accepts(g: &[u64], r: &[u64]) -> bool {
    rank1_accepts(&rank1_openings(g, &dv(), &xv(), r, P), P)
}

/// The Lean table `gTrue = outerTable dv xv` is `[3,1,4,3]` — the index
/// convention itself, checked before anything is built on it.
#[test]
fn the_true_gradient_table_matches_lean() {
    assert_eq!(outer_table(&dv(), &xv(), P), vec![3, 1, 4, 3]);
    // Lean `Rank1Example.other_rank_one_is_different`.
    assert_eq!(outer_table(&dv_other(), &xv(), P), vec![3, 4, 4, 2]);
    assert_ne!(outer_table(&dv_other(), &xv(), P), outer_table(&dv(), &xv(), P));
    // The transpose is a different matrix: Lean `rank1_refuses_the_transpose`.
    assert_eq!(outer_table(&xv(), &dv(), P), vec![3, 4, 1, 3]);
}

/// Lean `Rank1Example.rank1_complete_fires`: the true gradient is accepted at ALL
/// 25 challenges, not merely at sampled ones.
#[test]
fn the_true_gradient_is_accepted_at_every_challenge() {
    let g = outer_table(&dv(), &xv(), P);
    for r0 in 0..P {
        for r1 in 0..P {
            assert!(accepts(&g, &[r0, r1]), "refused the true gradient at ({r0},{r1})");
        }
    }
}

/// Lean `rank1_refuses_a_wrong_gradient` (refused at `(2,3)`),
/// `rank1_wrong_accept_witness` (wrongly accepted at `(0,3)`),
/// `rank1_wrong_accept_count` (9 of 25) and `rank1_refusal_is_the_common_case`
/// (16 of 25).
#[test]
fn a_wrong_gradient_matches_the_lean_counts() {
    let g = g_wrong();
    assert!(!accepts(&g, &[2, 3]), "must refuse at (2,3)");
    assert!(accepts(&g, &[0, 3]), "the false-accept event is nonempty at (0,3)");

    let mut accepted = 0;
    for r0 in 0..P {
        for r1 in 0..P {
            if accepts(&g, &[r0, r1]) {
                accepted += 1;
            }
        }
    }
    assert_eq!(accepted, 9, "Lean rank1_wrong_accept_count");
    assert_eq!(25 - accepted, 16, "Lean rank1_refusal_is_the_common_case");
    // The theorem's bound is (mi+mj)/|F| = 2/5 = 10/25: nearly attained, so the
    // measured 9 is evidence the bound is not loose slack.
    assert!(accepted * 5 <= 2 * 25);
}

/// ⚑ The sharp one, and the transposition detector.
///
/// Lean `rank1_refuses_another_rank_one` (refused at `(2,3)`) and
/// `rank1_other_accept_witness` (accepted at `(1,2)`). The SWAPPED point `(2,1)`
/// must be REFUSED — under a transposed row/column convention the two verdicts
/// exchange, and the accept counts would not notice.
#[test]
fn another_rank_one_matrix_is_refused_and_the_index_order_is_pinned() {
    let g = outer_table(&dv_other(), &xv(), P);
    assert!(!accepts(&g, &[2, 3]), "must refuse the other rank-1 matrix at (2,3)");
    assert!(accepts(&g, &[1, 2]), "accepts at (1,2)");
    assert!(
        !accepts(&g, &[2, 1]),
        "must REFUSE at the swapped point — a transposed convention would accept"
    );

    let accepted = (0..P)
        .flat_map(|r0| (0..P).map(move |r1| [r0, r1]))
        .filter(|r| accepts(&g, r))
        .count();
    assert_eq!(accepted, 9, "a rank-1 lie is no easier to catch than a one-entry lie");
}

/// Lean `rank1_refuses_the_transpose`: `x⊗δ` is refused at `(2,3)`.
#[test]
fn the_transpose_is_refused() {
    let g = outer_table(&xv(), &dv(), P);
    assert!(!accepts(&g, &[2, 3]));
}

/// Lean `sgd_step_fires`, `sgd_step_refuses_wrong_eta`,
/// `sgd_step_refuses_tampered_weights`: the whole optimizer step at `η = 2`.
#[test]
fn the_sgd_step_matches_lean() {
    let w = vec![1, 1, 1, 1]; // Lean `wOnes`
    let (d, x) = (dv(), xv());
    let w_prime = sgd_step_table(&w, 2, &d, &x, P);

    let mut accepted_honest = 0;
    let mut accepted_tampered = 0;
    for r0 in 0..P {
        for r1 in 0..P {
            let point = [r0, r1];
            let (row, col) = split_point(&point, 1);
            let d_open = mle_eval_folded(&d, row, P);
            let x_open = mle_eval_folded(&x, col, P);
            let w_open = mle_eval_folded(&w, &point, P);
            let w_prime_open = mle_eval_folded(&w_prime, &point, P);
            if sgd_step_accepts(w_open, w_prime_open, 2, d_open, x_open, P) {
                accepted_honest += 1;
            }
            let tampered: Vec<u64> = w_prime.iter().map(|v| (v + 1) % P).collect();
            let tampered_open = mle_eval_folded(&tampered, &point, P);
            if sgd_step_accepts(w_open, tampered_open, 2, d_open, x_open, P) {
                accepted_tampered += 1;
            }
        }
    }
    assert_eq!(accepted_honest, 25, "Lean sgd_step_fires: every challenge");
    assert_eq!(
        accepted_tampered, 0,
        "Lean sgd_step_refuses_tampered_weights: no challenge"
    );

    // Lean `sgd_step_refuses_wrong_eta`: the update used η = 2 and the verifier
    // checks η = 3, at (2,3).
    let point = [2, 3];
    let (row, col) = split_point(&point, 1);
    let d_open = mle_eval_folded(&d, row, P);
    let x_open = mle_eval_folded(&x, col, P);
    let w_open = mle_eval_folded(&w, &point, P);
    let w_prime_open = mle_eval_folded(&w_prime, &point, P);
    assert!(sgd_step_accepts(w_open, w_prime_open, 2, d_open, x_open, P));
    assert!(
        !sgd_step_accepts(w_open, w_prime_open, 3, d_open, x_open, P),
        "a wrong learning rate must be caught"
    );
}
