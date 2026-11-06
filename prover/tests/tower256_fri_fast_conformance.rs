//! The fast work-9104 prover (`tower256_fri_fast`) against the Lean vectors and against the
//! conformance kernel (`tower256_fri_prove`, pinned to Lean) on random requests: every
//! receipt, and every refusal, is the same.

use minidregg_prover::binary_tower_256::Tower256;
use minidregg_prover::tower256_fri_fast::{encode_request, eval_subspace, prove_fast, splitmix, P256};
use minidregg_prover::tower256_fri_prove::{decode_request, prove, ProveRequest};
use serde::Deserialize;

#[derive(Deserialize)]
struct Vector {
    name: String,
    request: String,
    response: String,
}

#[derive(Deserialize)]
struct Vectors {
    vectors: Vec<Vector>,
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex")).collect()
}

fn vectors() -> Vec<Vector> {
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/tower256_fri_vectors.json"))
        .expect("vectors file");
    let v: Vectors = serde_json::from_str(&text).expect("vectors json");
    assert!(v.vectors.len() >= 5, "expected the five Lean vectors");
    v.vectors
}

fn rnd(s: &mut u64) -> Tower256 {
    Tower256::from_limbs([splitmix(s), splitmix(s), splitmix(s), splitmix(s)])
}

#[test]
fn fast_prover_matches_lean_vectors() {
    for v in vectors() {
        let req = decode_request(&unhex(&v.request)).expect("request");
        assert_eq!(encode_request(&req), unhex(&v.request), "{}: request codec round trip", v.name);
        for threads in [1, 4] {
            let got = prove_fast(&req, threads).unwrap_or_else(|e| panic!("{}: {e}", v.name)).receipt;
            assert!(got == unhex(&v.response), "{}: receipt differs (threads {threads})", v.name);
        }
        eprintln!("{}: ell {} m {} q {} input {} degree {:?} offset0 {}", v.name, req.ell, req.m,
                  req.query_count, req.input_word.len(), req.degree, req.offset.is_zero());
    }
}

fn random_request(s: &mut u64, ell: usize, m: usize, q: usize, input_len: usize, unit_basis: bool) -> ProveRequest {
    let beta = (0..ell)
        .map(|i| {
            if unit_basis {
                let mut l = [0u64; 4];
                l[i / 64] = 1 << (i % 64);
                Tower256::from_limbs(l)
            } else {
                rnd(s)
            }
        })
        .collect();
    let last = 1usize << (ell - m);
    let final_degree = (splitmix(s) as usize) % (last.min(8) + 1);
    let mut degree: Vec<usize> = (0..m).map(|j| input_len >> j).collect();
    degree.push(final_degree);
    ProveRequest {
        statement_bytes: (0..(splitmix(s) % 40) as usize).map(|_| splitmix(s) as u8).collect(),
        ell,
        m,
        query_count: q,
        beta,
        offset: if splitmix(s) % 3 == 0 { Tower256::ZERO } else { rnd(s) },
        degree,
        input_word: (0..input_len).map(|_| rnd(s)).collect(),
    }
}

#[test]
fn fast_prover_matches_conformance_kernel_on_random_requests() {
    let mut s = 0x7077_u64;
    let mut cases = 0;
    for ell in 1..=9usize {
        for _ in 0..3 {
            let m = (splitmix(&mut s) as usize) % (ell + 1);
            let lb = 1 + (splitmix(&mut s) as usize) % 2;
            let input_len = match splitmix(&mut s) % 4 {
                0 => 0,
                1 => (1usize << ell) + 3, // longer than the domain
                _ => (1usize << ell.saturating_sub(lb)).max(1) - (splitmix(&mut s) % 2) as usize,
            };
            let q = (splitmix(&mut s) % 6) as usize;
            let unit = splitmix(&mut s) % 2 == 0;
            let req = random_request(&mut s, ell, m, q, input_len, unit);
            let want = prove(&req);
            for threads in [1, 3] {
                let got = prove_fast(&req, threads).map(|p| p.receipt);
                assert_eq!(got, want, "ell {ell} m {m} q {q} input {input_len} unit {unit} threads {threads}");
            }
            cases += 1;
        }
    }
    // A dependent basis: a zero pivot, and (m = 0) an encode through the Horner fallback.
    for (ell, m) in [(4usize, 2usize), (4, 0), (5, 1)] {
        let mut req = random_request(&mut s, ell, m, 3, 1 << (ell - 1), false);
        req.beta[ell - 1] = req.beta[0];
        req.degree[m] = req.degree[m].min(1);
        assert_eq!(prove_fast(&req, 1).map(|p| p.receipt), prove(&req), "dependent basis ell {ell} m {m}");
        cases += 1;
    }
    eprintln!("{cases} random requests agree");
}

/// The production shape (lb = 2, m = ell - 4, q = 148) at sizes the conformance kernel still
/// finishes in seconds.
#[test]
fn fast_prover_matches_conformance_kernel_at_production_shape() {
    let mut s = 0x5ca1e_u64;
    for ell in [8usize, 10] {
        let req = random_request(&mut s, ell, ell - 4, 148, 1 << (ell - 2), false);
        let t = std::time::Instant::now();
        let want = prove(&req).expect("reference");
        let t_ref = t.elapsed();
        let got = prove_fast(&req, 4).expect("fast");
        assert!(got.receipt == want, "ell {ell}: receipt differs");
        eprintln!("ell {ell}: {} receipt bytes, reference {:?}, fast {:?}", want.len(), t_ref,
                  std::time::Duration::from_nanos(got.timings.total_ns as u64));
    }
}

#[test]
fn additive_fft_matches_horner() {
    let mut s = 0xadd_u64;
    for k in 0..=10usize {
        for len in [0usize, 1, 2, 3, (1 << k) / 4 + 1, 1 << k, (1 << k) + 5] {
            let coeffs: Vec<P256> = (0..len).map(|_| P256::from_tower(rnd(&mut s))).collect();
            let offset = P256::from_tower(rnd(&mut s));
            let basis: Vec<P256> = (0..k).map(|_| P256::from_tower(rnd(&mut s))).collect();
            let got = eval_subspace(&coeffs, offset, &basis, 3);
            for (i, g) in got.iter().enumerate() {
                let mut x = offset;
                for (b, &v) in basis.iter().enumerate() {
                    if i >> b & 1 == 1 {
                        x = x.add(v);
                    }
                }
                let want = coeffs.iter().rev().fold(P256::ZERO, |acc, &c| c.add(x.mul(acc)));
                assert_eq!(*g, want, "k {k} len {len} index {i}");
            }
        }
    }
}
