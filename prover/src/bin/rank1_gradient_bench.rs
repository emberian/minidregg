//! `rank1_gradient_bench` — what the rank-1 gradient check costs, against what
//! proving the same gradient AS A CIRCUIT costs, at a real layer size.
//!
//! The statement on both sides is identical: `∇W = δ·xᵀ` for a `4096 × 4096`
//! linear layer (`mi = mj = 12`, so `m = 24` hypercube variables and `2^24 =
//! 16 777 216` matrix entries).
//!
//! * **CHECK** — `Selvage/Rank1GradientCheck.lean`'s `rank1_sound`: open `δ̂` at
//!   `r_row` and `x̂` at `r_col` and multiply. Prover work is two MLE evaluations
//!   on `2^12`-element tables; verifier work is one multiplication. **Zero rounds.**
//! * **CIRCUIT** — the same claim as a zerocheck
//!   `Σ_b eq(z,b)·(δ(b_row)·x(b_col) − G(b)) = 0`, run through the repo's LANDED
//!   degree-3 engine (`Assurance/AirSumcheckCubic.lean`,
//!   `prover::sumcheck::prove_cubic_sumcheck`). Five `2^24` tables, 24 rounds.
//!
//! The baseline is the repo's own engine rather than an invented gate count, and
//! `rank1::tests::the_zerocheck_baseline_states_the_same_thing` checks the two
//! sides state the same thing before either is timed.
//!
//! ⚠ What is NOT measured here: the commitment. Both sides need `W` and `W'`
//! committed and opened; the rank-1 check adds `δ` and `x` (`2·2^12` elements)
//! while the circuit path additionally commits the gradient itself (`2^24`). The
//! element COUNTS are printed; their hashing cost belongs to the PCS and is
//! priced in `notes/phase-profile.md`, not here.
//!
//! Usage: `cargo run --release --bin rank1_gradient_bench [--quick]`
//! (`--quick` stops the baseline at `m = 20` instead of running `m = 24`.)

use std::hint::black_box;
use std::time::{Duration, Instant};

use minidregg_prover::babybear::P;
use minidregg_prover::hash_kernels::cshake256_xof;
use minidregg_prover::rank1::{
    mle_eval_folded, outer_table, rank1_accepts, split_point, zerocheck_tables, Rank1Openings,
};
use minidregg_prover::sumcheck::{prove_cubic_sumcheck, verify_cubic_sumcheck, Fp};

/// A deterministic table — no rand dependency in the crate.
fn table(len: usize, seed: u64) -> Vec<Fp> {
    let mut s = seed | 1;
    (0..len)
        .map(|_| {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (s >> 17) % P
        })
        .collect()
}

/// Modular multiply — the bench keeps its own so the crate's internals stay
/// `pub(crate)`.
fn mulm(a: Fp, b: Fp, p: u64) -> Fp {
    ((a as u128 * b as u128) % p as u128) as u64
}

fn secs(d: Duration) -> f64 {
    d.as_secs_f64()
}

fn human(d: Duration) -> String {
    let s = secs(d);
    if s >= 1.0 {
        format!("{s:.3} s")
    } else if s >= 1e-3 {
        format!("{:.3} ms", s * 1e3)
    } else if s >= 1e-6 {
        format!("{:.3} µs", s * 1e6)
    } else {
        format!("{:.1} ns", s * 1e9)
    }
}

/// Run `f` enough times to accumulate at least `min` seconds, return per-call time.
fn timed<T>(min: f64, mut f: impl FnMut() -> T) -> Duration {
    let mut iters = 1u64;
    loop {
        let start = Instant::now();
        for _ in 0..iters {
            black_box(f());
        }
        let elapsed = start.elapsed();
        if elapsed.as_secs_f64() >= min || iters >= 1 << 30 {
            return elapsed / iters as u32;
        }
        iters *= 4;
    }
}

fn main() {
    let quick = std::env::args().any(|a| a == "--quick");
    let (mi, mj) = (12usize, 12usize);
    let m = mi + mj;
    let n_rows = 1usize << mi;
    let n_cols = 1usize << mj;

    println!("# rank-1 gradient check vs. proving the gradient as a circuit");
    println!("# field: BabyBear p = {P}");
    println!("# layer: {n_rows} x {n_cols} linear layer, m = {m} hypercube variables");
    println!("# gradient entries: {}", n_rows * n_cols);
    println!();

    let d = table(n_rows, 7);
    let x = table(n_cols, 13);
    let point = table(m, 4242);
    let (row, col) = split_point(&point, mi);

    // ---------------------------------------------------------------- CHECK --
    let t_delta = timed(0.5, || mle_eval_folded(&d, row, P));
    let t_x = timed(0.5, || mle_eval_folded(&x, col, P));
    let d_open = mle_eval_folded(&d, row, P);
    let x_open = mle_eval_folded(&x, col, P);
    let g_open = mulm(d_open, x_open, P);
    let openings = Rank1Openings {
        g: g_open,
        d: d_open,
        x: x_open,
    };
    let t_verify = timed(0.2, || rank1_accepts(&openings, P));
    assert!(rank1_accepts(&openings, P));

    let check_prover = t_delta + t_x;
    println!("## CHECK — the rank-1 identity (zero rounds)");
    println!("  prover: δ̂(r_row) over 2^{mi}       {}", human(t_delta));
    println!("  prover: x̂(r_col) over 2^{mj}       {}", human(t_x));
    println!("  prover TOTAL (incremental)        {}", human(check_prover));
    println!("  verifier: one multiply + compare  {}", human(t_verify));
    println!("  rounds: 0    prover felts touched: {}", n_rows + n_cols);
    println!();

    // ------------------------------------------------- WHAT IS NOT NEEDED ----
    let t_materialize = timed(0.5, || outer_table(&d, &x, P));
    let g = outer_table(&d, &x, P);
    let t_g_open = timed(0.5, || mle_eval_folded(&g, &point, P));
    println!("## The work the factorization SKIPS");
    println!("  materialize ∇W = δxᵀ (2^{m})       {}", human(t_materialize));
    println!("  evaluate Ĝ(r) over 2^{m}           {}", human(t_g_open));
    println!(
        "  ratio, materialize / check        {:.0}x",
        secs(t_materialize) / secs(check_prover)
    );
    println!();

    // ------------------------------------------- WHAT IT DOES *NOT* FIX ----
    // The step still commits the UPDATED WEIGHTS. The gradient check removes the
    // n^2 PROOF; it does not remove the n^2 COMMITMENT, and at these sizes that
    // is what dominates a step. Only a low-rank update (commit A and B, not W')
    // removes it — the DARK-TRAINING §3 claim, which this measurement is the
    // evidence for rather than against.
    //
    // cshake256 over the little-endian felts is a HASH-THROUGHPUT PROXY, not the
    // deployed commitment (a Merkle tree over Poseidon2, priced in
    // notes/phase-profile.md). It bounds the order of magnitude, nothing finer.
    let bytes_of = |t: &[Fp]| -> Vec<u8> { t.iter().flat_map(|v| v.to_le_bytes()).collect() };
    let w_bytes = bytes_of(&g);
    let dx_bytes = {
        let mut b = bytes_of(&d);
        b.extend(bytes_of(&x));
        b
    };
    let t_hash_w = timed(0.0, || cshake256_xof(b"rank1-bench", &w_bytes, 32));
    let t_hash_dx = timed(0.2, || cshake256_xof(b"rank1-bench", &dx_bytes, 32));
    println!("## What the check does NOT remove: committing W' (hash proxy)");
    println!(
        "  hash 2^{m} felts ({} MB)          {}",
        w_bytes.len() / (1 << 20),
        human(t_hash_w)
    );
    println!("  hash 2·2^{mi} felts (δ and x)      {}", human(t_hash_dx));
    println!("  ⚠ per-step cost is now dominated by this, not by the gradient.");
    println!();

    // ------------------------------------------------------------- CIRCUIT --
    println!("## CIRCUIT — the same claim as a degree-3 zerocheck (landed engine)");
    println!("  m   entries      build tables   prove         verify        prove/entry");
    let top = if quick { 20 } else { m };
    let mut last: Option<(usize, f64)> = None;
    for mm in [16usize, 18, 20, 22, 24] {
        if mm > top {
            continue;
        }
        let (bi, bj) = (mm / 2, mm - mm / 2);
        let dd = table(1 << bi, 7);
        let xx = table(1 << bj, 13);
        let gg = outer_table(&dd, &xx, P);
        let z = table(mm, 909);
        let chal = table(mm, 55);

        let t_build = timed(0.0, || zerocheck_tables(&gg, &dd, &xx, &z, P));
        let tabs = zerocheck_tables(&gg, &dd, &xx, &z, P);
        let t_prove = timed(0.0, || prove_cubic_sumcheck(&tabs, &chal, P));
        let proof = prove_cubic_sumcheck(&tabs, &chal, P);
        // The verifier's OWN work: 24 rounds of interpolation and one combine.
        // The five openings are what a PCS hands it, so they are precomputed
        // (folded, O(2^m)) rather than recomputed inside the timed region —
        // timing them here would price the PCS, not the protocol.
        let ov = [
            mle_eval_folded(&tabs.e, &proof.challenges, P),
            mle_eval_folded(&tabs.a, &proof.challenges, P),
            mle_eval_folded(&tabs.b, &proof.challenges, P),
            mle_eval_folded(&tabs.c, &proof.challenges, P),
            mle_eval_folded(&tabs.d, &proof.challenges, P),
        ];
        let t_verify_sc = timed(0.05, || verify_cubic_sumcheck(&proof, |_| ov, P));
        // The honest claim is zero and the honest proof VERIFIES — the baseline is
        // a real run, not an empty one.
        assert_eq!(proof.claim, 0);
        assert!(
            verify_cubic_sumcheck(&proof, |_| ov, P),
            "the baseline proof must actually verify"
        );

        let per = secs(t_prove) / (1u64 << mm) as f64;
        println!(
            "  {mm:2}  {:>10}   {:>12}   {:>11}   {:>11}   {:.2} ns",
            1u64 << mm,
            human(t_build),
            human(t_prove),
            human(t_verify_sc),
            per * 1e9
        );
        last = Some((mm, secs(t_prove)));
    }
    println!();

    if let Some((mm, t)) = last {
        let extrapolated = t * (1u64 << (m - mm)) as f64;
        let label = if mm == m { "measured" } else { "extrapolated" };
        println!("## The comparison at {n_rows} x {n_cols}");
        println!(
            "  circuit prover ({label} from m = {mm}):  {:.3} s",
            extrapolated
        );
        println!("  rank-1 check prover:                     {}", human(check_prover));
        println!(
            "  ratio:                                   {:.0}x",
            extrapolated / secs(check_prover)
        );
        println!("  rounds: 24 vs 0.   Committed felts: 2^24 + 2·2^12 vs 2·2^12.");
    }
}
