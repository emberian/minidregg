//! CPU timings of the fast work-9104 prover at the production shape (lb = 2, m = ell - 4,
//! q = 148, final degree 4), split into encode / Merkle / folds / openings / other, plus the
//! primitive rates. Optionally writes each request, its receipt and roots for the GPU harness.
//!
//!     tower256_fri_fast_bench [--ell 14,16,20] [--threads 1,8] [--reps 3] [--emit DIR]
//!                             [--reference-max-ell 0]
//!
//! Prints one JSON object per line.

use std::time::Instant;

use minidregg_prover::binary_tower_256::Tower256;
use minidregg_prover::tower256_fri_fast::{encode_request, prove_fast, splitmix, Hashers, P256, CLMUL_BACKEND};
use minidregg_prover::tower256_fri_prove::{prove, ProveRequest};

fn rnd(s: &mut u64) -> Tower256 {
    Tower256::from_limbs([splitmix(s), splitmix(s), splitmix(s), splitmix(s)])
}

/// The production-shape request at `ell`, deterministic in `ell` (seed `0x7043_0000 + ell`).
pub fn production_request(ell: usize) -> ProveRequest {
    let mut s = 0x7043_0000u64 + ell as u64;
    let lb = 2;
    let m = ell - lb - 2;
    ProveRequest {
        statement_bytes: (0..48).map(|_| splitmix(&mut s) as u8).collect(),
        ell,
        m,
        query_count: 148,
        beta: (0..ell).map(|_| rnd(&mut s)).collect(),
        offset: rnd(&mut s),
        degree: (0..=m).map(|j| 1usize << (ell - lb - j)).collect(),
        input_word: (0..1usize << (ell - lb)).map(|_| rnd(&mut s)).collect(),
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn sha256_hex(data: &[u8]) -> String {
    // sha3-256 is what this crate carries; the harness recomputes it with hashlib.
    use sha3::{Digest, Sha3_256};
    hex(&Sha3_256::digest(data))
}

fn list(arg: &str) -> Vec<usize> {
    arg.split(',').map(|x| x.parse().expect("number")).collect()
}

fn main() {
    let mut ells = vec![14, 16, 20];
    let mut threads = vec![1, std::thread::available_parallelism().map_or(1, |n| n.get())];
    let mut reps = 3usize;
    let mut emit: Option<std::path::PathBuf> = None;
    let mut reference_max_ell = 0usize;
    let args: Vec<String> = std::env::args().collect();
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--ell" => ells = list(&args[i + 1]),
            "--threads" => threads = list(&args[i + 1]),
            "--reps" => reps = args[i + 1].parse().unwrap(),
            "--emit" => emit = Some(args[i + 1].clone().into()),
            "--reference-max-ell" => reference_max_ell = args[i + 1].parse().unwrap(),
            other => panic!("unknown argument {other}"),
        }
        i += 2;
    }

    if let Some(dir) = &emit {
        // Reference products and inverses (binary_tower_256.rs) for the device check.
        let (n, ni) = (1024u64, 16u64);
        let mut s = 0x6d75_6cu64;
        let mut out = Vec::new();
        out.extend_from_slice(&n.to_le_bytes());
        out.extend_from_slice(&ni.to_le_bytes());
        for _ in 0..n {
            let (a, b) = (rnd(&mut s), rnd(&mut s));
            for x in [a, b, a.mul(b)] {
                out.extend_from_slice(&x.to_le_bytes());
            }
        }
        for _ in 0..ni {
            let a = rnd(&mut s);
            out.extend_from_slice(&a.to_le_bytes());
            out.extend_from_slice(&a.inverse().expect("nonzero").to_le_bytes());
        }
        std::fs::create_dir_all(dir).unwrap();
        std::fs::write(dir.join("mul_check.bin"), out).unwrap();
    }

    // Primitive rates, one thread.
    let hs = Hashers::new();
    let n = 200_000;
    let mut d = [7u8; 32];
    let t = Instant::now();
    for _ in 0..n {
        d = hs.node(&d, &d);
    }
    let node_ns = t.elapsed().as_nanos() as f64 / n as f64;
    let mut s = 1u64;
    let (mut a, b) = (P256::from_tower(rnd(&mut s)), P256::from_tower(rnd(&mut s)));
    let n = 2_000_000;
    let t = Instant::now();
    for _ in 0..n {
        a = a.mul(b).add(b);
    }
    let mul_ns = t.elapsed().as_nanos() as f64 / n as f64;
    let (mut ta, tb) = (rnd(&mut s), rnd(&mut s));
    let n = 20_000;
    let t = Instant::now();
    for _ in 0..n {
        ta = ta.mul(tb).add(tb);
    }
    let ref_mul_ns = t.elapsed().as_nanos() as f64 / n as f64;
    let t = Instant::now();
    let mut x = P256::ZERO;
    for _ in 0..1000 {
        x = x.add(P256::from_tower(ta)).add(P256::from_tower(x.to_tower()));
    }
    let conv_ns = t.elapsed().as_nanos() as f64 / 2000.0;
    println!(
        "{{\"kind\":\"primitives\",\"clmul\":\"{CLMUL_BACKEND}\",\"keccak_node_ns\":{node_ns:.1},\"p256_mul_ns\":{mul_ns:.2},\"fanpaar_ref_mul_ns\":{ref_mul_ns:.1},\"basis_conversion_ns\":{conv_ns:.1},\"sink\":\"{}\"}}",
        hex(&d[..2]).to_string() + &hex(&a.tower_bytes()[..1]) + &hex(&x.tower_bytes()[..1])
    );

    for &ell in &ells {
        let req = production_request(ell);
        let request = encode_request(&req);
        let mut receipt_hash = String::new();
        for &th in &threads {
            let mut best: Option<minidregg_prover::tower256_fri_fast::Timings> = None;
            for _ in 0..reps {
                let p = prove_fast(&req, th).expect("prove");
                let h = sha256_hex(&p.receipt);
                if receipt_hash.is_empty() {
                    receipt_hash = h;
                    if let Some(dir) = &emit {
                        std::fs::create_dir_all(dir).unwrap();
                        std::fs::write(dir.join(format!("request_ell{ell}.bin")), &request).unwrap();
                        std::fs::write(dir.join(format!("receipt_ell{ell}.bin")), &p.receipt).unwrap();
                        let roots: Vec<String> = p.roots.iter().map(|r| format!("\"{}\"", hex(r))).collect();
                        std::fs::write(
                            dir.join(format!("expect_ell{ell}.json")),
                            format!(
                                "{{\"ell\":{ell},\"request_sha3_256\":\"{}\",\"receipt_sha3_256\":\"{}\",\"receipt_len\":{},\"roots\":[{}]}}\n",
                                sha256_hex(&request),
                                receipt_hash,
                                p.receipt.len(),
                                roots.join(",")
                            ),
                        )
                        .unwrap();
                    }
                } else {
                    assert_eq!(h, receipt_hash, "receipt changed between runs/thread counts");
                }
                if best.map_or(true, |b| p.timings.total_ns < b.total_ns) {
                    best = Some(p.timings);
                }
            }
            let tm = best.unwrap();
            let ms = |x: u128| x as f64 / 1e6;
            println!(
                "{{\"kind\":\"prove\",\"ell\":{ell},\"m\":{},\"q\":148,\"threads\":{th},\"total_ms\":{:.3},\"encode_ms\":{:.3},\"merkle_ms\":{:.3},\"folds_ms\":{:.3},\"openings_ms\":{:.3},\"other_ms\":{:.3},\"merkle_keccak_f\":{},\"encode_mults\":{},\"fold_mults\":{},\"receipt_sha3_256\":\"{receipt_hash}\"}}",
                req.m, ms(tm.total_ns), ms(tm.encode_ns), ms(tm.merkle_ns), ms(tm.folds_ns),
                ms(tm.openings_ns), ms(tm.other_ns), tm.merkle_keccak_f, tm.encode_mults, tm.fold_mults
            );
        }
        if ell <= reference_max_ell {
            let t = Instant::now();
            let want = prove(&req).expect("reference");
            let ref_s = t.elapsed().as_secs_f64();
            let same = sha256_hex(&want) == receipt_hash;
            println!("{{\"kind\":\"reference\",\"ell\":{ell},\"reference_s\":{ref_s:.1},\"identical\":{same}}}");
            assert!(same, "fast receipt differs from the conformance kernel at ell {ell}");
        }
    }
}
