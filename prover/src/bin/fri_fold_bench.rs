//! `[PROVER-fri-wgsl]` benchmark: `fold_gpu` vs `fri::fold` on a large
//! codeword. Run release: `cargo run --release --bin fri_fold_bench`
//! (`FRI_BENCH_LOG_N=21` to change the size).
//!
//! Numbers, not claims: this measures UNVERIFIED COMPUTE. GPU timings include
//! the full per-fold cost (bitrev permutes, twiddle build, upload, dispatch,
//! readback) against a prebuilt pipeline; the CPU fold likewise rebuilds its
//! twiddles per round. Every timed GPU result is equality-checked against the
//! CPU reference before its number is reported.

use std::time::Instant;

use minidregg_prover::field4::{Ext4, P};
use minidregg_prover::fri;
use minidregg_prover::gpu::{GpuFold, NO_ADAPTER};

fn prng(seed: &mut u64) -> u64 {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    (*seed >> 16) % P
}

fn prng_ext(seed: &mut u64) -> Ext4 {
    Ext4 {
        c: [prng(seed), prng(seed), prng(seed), prng(seed)],
    }
}

fn main() {
    let log_n: u32 = std::env::var("FRI_BENCH_LOG_N")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(20);
    let n = 1usize << log_n;

    let mut seed = 0xbe4c_4_f01d_u64;
    let codeword: Vec<Ext4> = (0..n).map(|_| prng_ext(&mut seed)).collect();
    let beta = prng_ext(&mut seed);

    println!("FRI fold benchmark: 2^{log_n} = {n} BabyBear^4 elements");

    let gpu = match GpuFold::new() {
        Ok(g) => {
            println!("adapter: {}", g.adapter_name());
            Some(g)
        }
        Err(e) if e.starts_with(NO_ADAPTER) => {
            println!("adapter: NONE (no GPU on this runner) — CPU numbers only");
            None
        }
        Err(e) => {
            println!("GPU setup failed: {e} — CPU numbers only");
            None
        }
    };

    for log_arity in [1usize, 2, 4] {
        println!("-- log_arity {log_arity} (arity {})", 1 << log_arity);

        // CPU reference (also the conformance oracle for the GPU timings)
        let cpu_iters = 3;
        let t = Instant::now();
        let mut cpu_out = Vec::new();
        for _ in 0..cpu_iters {
            cpu_out = fri::fold(&codeword, beta, log_arity);
        }
        let cpu_ms = t.elapsed().as_secs_f64() * 1e3 / cpu_iters as f64;
        println!("   CPU fri::fold      {cpu_ms:9.3} ms  (avg of {cpu_iters})");

        if let Some(gpu) = &gpu {
            // warmup (first dispatch pays shader specialization)
            let warm = gpu.fold(&codeword, beta, log_arity).expect("GPU fold");
            assert_eq!(
                warm, cpu_out,
                "GPU diverged from CPU at log_arity {log_arity}"
            );

            let gpu_iters = 5;
            let t = Instant::now();
            let mut gpu_out = Vec::new();
            for _ in 0..gpu_iters {
                gpu_out = gpu.fold(&codeword, beta, log_arity).expect("GPU fold");
            }
            let gpu_ms = t.elapsed().as_secs_f64() * 1e3 / gpu_iters as f64;
            assert_eq!(
                gpu_out, cpu_out,
                "GPU diverged from CPU at log_arity {log_arity}"
            );
            println!(
                "   GPU fold_gpu       {gpu_ms:9.3} ms  (avg of {gpu_iters}, incl. permutes+upload+readback)  speedup x{:.1}",
                cpu_ms / gpu_ms
            );
            println!("   conformance: GPU == CPU on this word");
        }
    }
}
