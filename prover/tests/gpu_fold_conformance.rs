//! `[PROVER-fri-wgsl]` conformance: the GPU fold must equal `fri::fold` — the
//! CPU reference, itself vector-conformant to `Loom/Proximity.lean`'s verified
//! `fold` — EXACTLY, on random codewords across sizes and arities.
//!
//! Cross-check, NOT verification (no formal semantics of Rust or WGSL). Where
//! the runner has no GPU adapter the tests SKIP with a loud message and a
//! `SKIPPED` marker — they never falsely pass: the equality assertions only
//! count when a real adapter ran the kernel.

use minidregg_prover::field4::{Ext4, P};
use minidregg_prover::fri;
use minidregg_prover::gpu::{GpuFold, NO_ADAPTER};

fn prng(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    (*seed >> 16) % P
}

fn prng_ext(seed: &mut u64) -> Ext4 {
    Ext4 { c: [prng(seed), prng(seed), prng(seed), prng(seed)] }
}

fn prng_word(seed: &mut u64, n: usize) -> Vec<Ext4> {
    (0..n).map(|_| prng_ext(seed)).collect()
}

/// Acquire the GPU context, or skip loudly. Returns `None` ONLY on the
/// no-adapter marker; any other GPU failure is a real failure.
fn gpu_or_skip(test: &str) -> Option<GpuFold> {
    match GpuFold::new() {
        Ok(g) => {
            eprintln!("[{test}] GPU adapter: {}", g.adapter_name());
            Some(g)
        }
        Err(e) if e.starts_with(NO_ADAPTER) => {
            eprintln!("[{test}] SKIPPED: no GPU adapter in this runner — GPU conformance NOT exercised ({e})");
            None
        }
        Err(e) => panic!("[{test}] GPU setup failed on a machine WITH an adapter path: {e}"),
    }
}

/// The main gate: `fold_gpu == fri::fold` on random codewords, every
/// `log_n` in 1..=12 and every in-window arity (`log_arity <= min(5, log_n)`,
/// including 0 = identity and full collapse to a single element).
#[test]
fn gpu_fold_equals_cpu_fold_on_random_cases() {
    let Some(gpu) = gpu_or_skip("gpu_fold_equals_cpu_fold_on_random_cases") else {
        return;
    };
    let mut seed = 0x5eed_f01d_u64;
    let mut cases = 0usize;
    for log_n in 1u32..=12 {
        let n = 1usize << log_n;
        let cw = prng_word(&mut seed, n);
        let beta = prng_ext(&mut seed);
        for log_arity in 0..=(log_n.min(5) as usize) {
            let cpu = fri::fold(&cw, beta, log_arity);
            let gpu_out = gpu
                .fold(&cw, beta, log_arity)
                .expect("GPU fold must run once an adapter exists");
            assert_eq!(
                gpu_out, cpu,
                "GPU fold diverges from the CPU reference at log_n={log_n} log_arity={log_arity}"
            );
            cases += 1;
        }
    }
    eprintln!("GPU==CPU on {cases} random (log_n, log_arity) cases");
    assert!(cases >= 60, "the sweep must actually cover the grid");
}

/// Arities past the kernel's 32-slot window chain multiple dispatches; the
/// chain must still equal the single CPU fold (same beta-squaring schedule).
#[test]
fn gpu_fold_chains_large_arities() {
    let Some(gpu) = gpu_or_skip("gpu_fold_chains_large_arities") else {
        return;
    };
    let mut seed = 0xcafe_c0de_u64;
    for (log_n, log_arity) in [(10u32, 7usize), (12, 8), (8, 8), (13, 11)] {
        let cw = prng_word(&mut seed, 1 << log_n);
        let beta = prng_ext(&mut seed);
        let cpu = fri::fold(&cw, beta, log_arity);
        let gpu_out = gpu.fold(&cw, beta, log_arity).expect("chained GPU fold must run");
        assert_eq!(
            gpu_out, cpu,
            "chained GPU fold diverges at log_n={log_n} log_arity={log_arity}"
        );
    }
    eprintln!("GPU==CPU on 4 chained-dispatch cases (log_arity > 5)");
}

/// Teeth for the equality gate itself: a perturbed input must change the GPU
/// fold (so the assertions above cannot pass vacuously on constant outputs).
#[test]
fn gpu_fold_sees_tampered_input() {
    let Some(gpu) = gpu_or_skip("gpu_fold_sees_tampered_input") else {
        return;
    };
    let mut seed = 0x7ee7_u64;
    let cw = prng_word(&mut seed, 64);
    let beta = prng_ext(&mut seed);
    let reference = gpu.fold(&cw, beta, 2).expect("GPU fold must run");
    let mut bad = cw.clone();
    bad[17].c[3] = (bad[17].c[3] + 1) % P;
    let tampered = gpu.fold(&bad, beta, 2).expect("GPU fold must run");
    assert_ne!(tampered, reference, "a tampered element must show in the GPU fold");
}
