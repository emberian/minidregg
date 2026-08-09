//! Reproducible scaling baseline for the honest full-trace reference protocol.
//!
//! This is deliberately a diagnostic, not a performance claim. The current
//! `reference_prove` path evaluates a trace-coefficient polynomial densely over
//! its complete RS domain and the proof carries the trace. The benchmark makes
//! that cost visible before `[PROVER-e2e-succinct-openings]` and the additive NTT
//! exist, so later backends have a fixed workload and output schema to beat.

use std::env;
use std::time::{Duration, Instant};

use minidregg_prover::descriptor::{Descriptor, Gate, GateOp, Wire};
use minidregg_prover::field4::P;
use minidregg_prover::poseidon::demo_spec;
use minidregg_prover::protocol::{
    reference_prove, reference_verify, ReferenceConfig, ReferenceProof,
};
use minidregg_prover::wide::DIGEST_LIMBS;

fn parse_arg(args: &[String], index: usize, default: u32, name: &str) -> u32 {
    args.get(index)
        .map(|raw| {
            raw.parse::<u32>()
                .unwrap_or_else(|_| panic!("{name} must be an unsigned integer, got {raw}"))
        })
        .unwrap_or(default)
}

/// A scalable, deterministic emitted-descriptor-shaped workload.
///
/// One public input flows through alternating `+ constant` and `* 1` gates.
/// Every auxiliary wire is defined exactly once in topological order, matching
/// the invariants proved of `Compiler.Emit`. This is not claimed to be emitted
/// by Lean; it is a runtime scaling fixture for the descriptor consumer.
fn chain_descriptor(log_gates: u32) -> Descriptor {
    let gate_count = 1usize
        .checked_shl(log_gates)
        .expect("log_gates exceeds the host usize width");
    assert!(
        gate_count < u32::MAX as usize,
        "too many gates for the wire format"
    );
    let mut gates = Vec::with_capacity(gate_count);
    for i in 0..gate_count {
        let (op, b) = if i % 2 == 0 {
            (GateOp::Add, Wire::Const((i as u64 + 1) % P))
        } else {
            (GateOp::Mul, Wire::Const(1))
        };
        gates.push(Gate {
            op,
            a: Wire::Wire(i as u32),
            b,
            out: (i + 1) as u32,
        });
    }
    Descriptor {
        p: P,
        n_public: 1,
        n_vars: 1,
        n_wires: (gate_count + 1) as u32,
        gates,
        zeros: Vec::new(),
    }
}

/// Proof footprint in canonical BabyBear-word equivalents.
///
/// This counts logical field limbs rather than Rust allocation overhead or a
/// promised wire format. An `Ext4` contributes four words and a `Digest` nine.
fn proof_field_words(proof: &ReferenceProof) -> usize {
    let trace = proof.trace.len();
    let trace_root = DIGEST_LIMBS;
    let sumcheck = 1
        + proof.gate_sumcheck.challenges.len()
        + proof
            .gate_sumcheck
            .rounds
            .iter()
            .map(Vec::len)
            .sum::<usize>();
    let fri_roots = proof.fri.round_commitments.len() * DIGEST_LIMBS;
    let fri_final = proof.fri.final_codeword.len() * 4;
    let fri_openings = proof
        .fri
        .query_openings
        .iter()
        .flat_map(|query| &query.rounds)
        .map(|round| 8 + (round.lo_path.len() + round.hi_path.len()) * DIGEST_LIMBS)
        .sum::<usize>();
    trace + trace_root + sumcheck + fri_roots + fri_final + fri_openings
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1_000.0
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let min_log = parse_arg(&args, 1, 6, "min_log_gates");
    let max_log = parse_arg(&args, 2, 10, "max_log_gates");
    let queries = parse_arg(&args, 3, 8, "queries") as usize;
    assert!(
        min_log <= max_log,
        "min_log_gates must not exceed max_log_gates"
    );
    assert!(queries > 0, "queries must be positive");

    let config = ReferenceConfig {
        fri_log_blowup: 2,
        fri_queries: queries,
    };
    let spec = demo_spec();

    println!("log_gates,gates,wires,prove_ms,verify_ms,proof_field_words,verified");
    for log_gates in min_log..=max_log {
        let descriptor = chain_descriptor(log_gates);
        descriptor
            .validate()
            .expect("scaling descriptor is well formed");

        let prove_start = Instant::now();
        let proof = reference_prove(&descriptor, &[7], config, &spec)
            .expect("the deterministic scaling assignment satisfies its descriptor");
        let prove_elapsed = prove_start.elapsed();

        let verify_start = Instant::now();
        let verified = reference_verify(&descriptor, &[7], &proof, config, &spec);
        let verify_elapsed = verify_start.elapsed();
        assert!(
            verified,
            "reference round trip failed at log_gates={log_gates}"
        );

        println!(
            "{log_gates},{},{},{:.3},{:.3},{},{}",
            descriptor.gates.len(),
            descriptor.n_wires,
            millis(prove_elapsed),
            millis(verify_elapsed),
            proof_field_words(&proof),
            verified
        );
    }
}
