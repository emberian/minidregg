//! `low_rank_commit_cost` — what a training step COMMITS, in the unit that bills.
//!
//! `Selvage/Rank1GradientCheck.lean` made the gradient PROOF for a linear layer
//! ~7·10⁴× cheaper and said its own honest half out loud: **the check removes the
//! `n²` proof, not the `n²` commitment.** `notes/field-op-counts.md` then measured
//! the prover hash-bound by 5.0–7.2× at every feasible blowup, so a committed felt
//! IS the expensive thing. `Assurance/ZkmlLowRankUpdate.lean` is the structural
//! answer — `W' = W + A·B` at rank `r`, base committed once — and this binary
//! prices it.
//!
//! **There is no clock in this file.** Every number is a COUNT derived from what
//! the code decides, so it is contention-immune by construction; this box runs at
//! load 30–95 and its wall-clock is not evidence. One measured constant enters, at
//! the very end and clearly labelled: the Poseidon2 rate from
//! `notes/phase-profile.md` §7, used only to convert counts into milliseconds.
//!
//! ## The model, and where each half comes from
//!
//! Committing a `w`-column × `h`-row matrix at `log_blowup = lb` costs
//!
//! ```text
//!   n     = h · 2^lb                  leaves (rows of the low-degree extension)
//!   leaf  = ⌈w/8⌉ · n                 PaddingFreeSponge over each row, rate 8
//!   tree  = n − 1                     binary Merkle compressions
//! ```
//!
//! * The `⌈w/8⌉`-per-row leaf cost is the MECHANISM stated in `phase-profile.md`
//!   §6 ("the Merkle leaf hash is a `PaddingFreeSponge` over the whole committed
//!   row, so it costs `⌈w/8⌉` permutations per row").
//! * The tree law is CALIBRATED: `phase-profile.md` §7's measured Merkle-commit
//!   column fits `2n − 3` exactly at every blowup rung, with `n = 1656·2^b`. For a
//!   narrow commit (`w ≤ 8`) this model gives `2n − 1`, so it reproduces the
//!   measured column to within a constant 2 permutations, independent of `n`.
//!   `calibration()` asserts exactly that and the binary refuses to print if it
//!   fails.
//!
//! Rearranged, for `w ≥ 8`:
//!
//! ```text
//!   perms ≈ (2^lb / 8) · N · (1 + 8/w),   N = w·h committed felts
//! ```
//!
//! — so **committed felts is the right currency**, at `2^lb/8` permutations each,
//! with one correction: the aspect-ratio penalty `(1 + 8/w)`. It is under 7% for a
//! wide matrix and it is exactly where the low-rank route can lose, because the
//! natural `d×r` layout of `A` has `w = r ∈ {8,16,64}`.
//!
//! Usage: `cargo run --release --bin low_rank_commit_cost`

/// The deployed blowup after `notes/blowup-drop.md` removed the invented
/// `log_blowup ≥ ⌈log₂(d−1)⌉` floor.
const LOG_BLOWUP: u32 = 2;

/// Poseidon2 rate, from `phase-profile.md` §7 (min of 4,000 windows × 512
/// permutations). The ONLY measured quantity in this file, used ONLY for the
/// final ms conversion.
const NS_PER_PERM_PACKED: f64 = 758.0 / 4.0;
const NS_PER_PERM_SCALAR: f64 = 938.0;

/// Permutations to Merkle-commit a `w × h` matrix at `log_blowup = lb`.
fn commit_perms(w: u64, h: u64, lb: u32) -> u64 {
    let n = h << lb;
    let leaf = w.div_ceil(8) * n;
    let tree = n.saturating_sub(1);
    leaf + tree
}

/// The measured Merkle-commit column of `phase-profile.md` §7, which fits
/// `2n − 3` exactly at `n = 1656·2^b`. A narrow commit under our model is
/// `2n − 1`, so the two must agree to within a constant 2 at every rung — a real
/// falsifiable check on the tree law, not a restatement of it.
fn calibration() -> Result<Vec<(u32, u64, u64)>, String> {
    let measured: [(u32, u64); 5] = [
        (3, 26_493),
        (4, 52_989),
        (5, 105_981),
        (6, 211_965),
        (7, 423_933),
    ];
    let mut rows = Vec::new();
    for (b, m) in measured {
        // The profiled batch: 1656 trace rows, committed narrow (w ≤ 8).
        let modelled = commit_perms(8, 1656, b);
        let delta = modelled as i64 - m as i64;
        if delta != 2 {
            return Err(format!(
                "tree law FALSIFIED at b={b}: model {modelled}, measured {m}, delta {delta} (expected exactly 2)"
            ));
        }
        rows.push((b, m, modelled));
    }
    Ok(rows)
}

/// One commitment plan: what a step hands the PCS.
struct Plan {
    label: &'static str,
    /// `(columns, rows)` of each committed matrix.
    mats: Vec<(u64, u64)>,
}

impl Plan {
    fn felts(&self) -> u64 {
        self.mats.iter().map(|(w, h)| w * h).sum()
    }
    fn perms(&self, lb: u32) -> u64 {
        self.mats.iter().map(|(w, h)| commit_perms(*w, *h, lb)).sum()
    }
}

fn main() {
    println!("== low-rank update: what a training step COMMITS ==");
    println!("log_blowup = {LOG_BLOWUP} (blowup {}), Poseidon2 rate 8\n", 1u64 << LOG_BLOWUP);

    match calibration() {
        Ok(rows) => {
            println!("-- calibration against phase-profile.md §7's measured Merkle-commit column --");
            println!("  {:>4}  {:>12}  {:>12}  {:>6}", "b", "measured", "model", "delta");
            for (b, m, model) in rows {
                println!("  {:>4}  {:>12}  {:>12}  {:>6}", b, m, model, model as i64 - m as i64);
            }
            println!("  tree law holds: constant offset 2 at every rung, independent of n\n");
        }
        Err(e) => {
            eprintln!("CALIBRATION FAILED: {e}");
            std::process::exit(1);
        }
    }

    for d in [1024u64, 4096, 16384] {
        println!("== d = {d}  (W is d x d = {} felts) ==", d * d);

        let full = Plan { label: "full W' recommit", mats: vec![(d, d)] };
        println!(
            "  {:<34} {:>14} felts  {:>14} perms",
            full.label,
            full.felts(),
            full.perms(LOG_BLOWUP)
        );

        println!(
            "  {:>5}  {:>14}  {:>16}  {:>16}  {:>9}  {:>9}",
            "r", "felts (2rd)", "perms (A as d x r)", "perms (A transposed)", "x felts", "x perms"
        );
        for r in [8u64, 16, 64, 256] {
            // Naive layout: A is d rows of r columns, B is r rows of d columns.
            let naive = Plan { label: "", mats: vec![(r, d), (d, r)] };
            // Both factors committed WIDE: A stored transposed, so every row is d felts.
            let wide = Plan { label: "", mats: vec![(d, r), (d, r)] };
            println!(
                "  {:>5}  {:>14}  {:>16}  {:>16}  {:>8.1}x  {:>8.1}x",
                r,
                naive.felts(),
                naive.perms(LOG_BLOWUP),
                wide.perms(LOG_BLOWUP),
                full.felts() as f64 / naive.felts() as f64,
                full.perms(LOG_BLOWUP) as f64 / wide.perms(LOG_BLOWUP) as f64,
            );
        }

        // Break-even in RANK: 2rd = d^2.
        println!("  break-even rank (felts, 2rd = d^2): r = {}", d / 2);

        // Break-even in CHAIN LENGTH: merging the deltas back into W costs one
        // full recommit, and is worth it once the accumulated deltas cost more.
        println!(
            "  break-even chain length before a MERGE pays (T·2rd > d^2): r=8 -> T={}, r=16 -> T={}, r=64 -> T={}",
            d / 16,
            d / 32,
            d / 128
        );
        println!();
    }

    // The conversion, isolated and labelled.
    let d = 4096u64;
    let full = commit_perms(d, d, LOG_BLOWUP);
    let lr16 = 2 * commit_perms(d, 16, LOG_BLOWUP);
    println!("== conversion (the ONE measured constant, phase-profile.md §7) ==");
    println!("  packed {NS_PER_PERM_PACKED:.1} ns/perm (prover), scalar {NS_PER_PERM_SCALAR:.0} ns/perm (verifier)");
    println!(
        "  d=4096 full W' recommit : {full:>12} perms = {:.2} s packed",
        full as f64 * NS_PER_PERM_PACKED / 1e9
    );
    println!(
        "  d=4096 low-rank r=16    : {lr16:>12} perms = {:.1} ms packed",
        lr16 as f64 * NS_PER_PERM_PACKED / 1e6
    );
    println!(
        "  ratio {:.1}x",
        full as f64 / lr16 as f64
    );

    println!("\n== the sumcheck the one-commitment design ADDS ==");
    println!("  Assurance/ZkmlLowRankUpdate.lean's lowRank_sumcheck_soundness adds kappa*3/|F|");
    println!("  with kappa = log2 r. Its WORK is a sumcheck over kappa variables on tables of");
    println!("  r entries:");
    for r in [8u64, 16, 64, 256] {
        println!(
            "    r = {r:>4}: kappa = {:>2} rounds, ~{:>5} field ops, error term {:>3}*3/|F|",
            r.trailing_zeros(),
            2 * r,
            r.trailing_zeros()
        );
    }
    println!("  So the correction is real in the ERROR BOUND and nothing at all in the COST.");
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The tree law is calibrated against measured data, not asserted.
    #[test]
    fn the_model_reproduces_the_measured_merkle_column() {
        calibration().expect("calibration must hold");
    }

    /// ⚠ The calibration must be able to FAIL — a check that cannot go red is not
    /// a check. Perturbing the rate from 8 to 16 breaks it.
    #[test]
    fn the_calibration_is_refutable() {
        let n = 1656u64 << 6;
        let right = commit_perms(8, 1656, 6);
        let wrong = commit_perms(16, 1656, 6);
        assert_ne!(right, wrong, "rate 8 and rate 16 must give different counts");
        assert_eq!(right, 2 * n - 1);
    }

    /// Committing wide, permutations track committed felts at `2^lb/8` each — the
    /// statement that makes "committed felts" the right currency.
    #[test]
    fn perms_track_felts_when_the_matrix_is_wide() {
        let d = 4096u64;
        let felts = d * d;
        let perms = commit_perms(d, d, LOG_BLOWUP);
        let ideal = (felts << LOG_BLOWUP) / 8;
        // Within the (1 + 8/w) aspect penalty, which is 0.2% at w = 4096.
        assert!(perms > ideal);
        assert!((perms - ideal) * 400 < ideal, "aspect penalty must be under 0.25% at w=d");
    }

    /// ⚑ The aspect-ratio penalty BITES exactly in the low-rank regime: the
    /// natural `d x r` layout of `A` has `w = r`, and at `r = 8` that doubles the
    /// permutation cost of the same felts.
    #[test]
    fn the_naive_layout_costs_more_than_the_transposed_one_for_the_same_felts() {
        let d = 4096u64;
        for r in [8u64, 16, 64] {
            let naive = commit_perms(r, d, LOG_BLOWUP);
            let transposed = commit_perms(d, r, LOG_BLOWUP);
            assert_eq!(r * d, d * r, "same felt count");
            assert!(
                naive > transposed,
                "r={r}: naive {naive} should exceed transposed {transposed}"
            );
        }
        // At r = 8 the penalty is exactly 2x on the leaf term.
        let naive8 = commit_perms(8, d, LOG_BLOWUP);
        let transposed8 = commit_perms(d, 8, LOG_BLOWUP);
        assert!(naive8 as f64 / transposed8 as f64 > 1.9);
    }

    /// The break-even rank is `d/2` in BOTH units, so no rank anyone would use is
    /// anywhere near it — the commitment is never the reason to stop.
    #[test]
    fn break_even_rank_is_half_the_dimension() {
        let d = 4096u64;
        let full = commit_perms(d, d, LOG_BLOWUP);
        let at_half = 2 * commit_perms(d, d / 2, LOG_BLOWUP);
        assert_eq!(2 * (d / 2) * d, d * d, "felts break even at r = d/2");
        // Permutations agree with the felt count when both are committed wide.
        let rel = (at_half as f64 - full as f64).abs() / full as f64;
        assert!(rel < 0.01, "perms break even within 1% at r = d/2, got {rel}");
    }
}
