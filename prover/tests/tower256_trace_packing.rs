#![deny(warnings)]

use minidregg_prover::tower256_algebraic_cert::{
    encode_algebraic_receipt, prove_algebraic_document, verify_algebraic_cert_bytes,
};
use minidregg_prover::tower256_private_cert::{ClaimData, DfaTable};
use std::time::Instant;

use minidregg_prover::binary_tower_256::Tower256 as F;
use minidregg_prover::tower256_private_cert::{fast_mul256 as mul, fast_square256 as sq};
use minidregg_prover::tower256_trace_pack::{
    artin_schreier, content_commitment, dual_basis, pack_32_bytes_bijective, pluck_bit_via_dual,
    prove, trace, transpose_bit_matrix_256, verify, ByteAndDfa,
};
use serde_json::Value;

fn payload(n: usize) -> Vec<u8> {
    (0..n)
        .map(|i| ((197 * i) ^ (i >> 7) ^ (i >> 13)) as u8)
        .collect()
}

// Two-state byte DFA: toggle the parity bit when both selected input bits are set.
fn parity_dfa() -> DfaTable {
    DfaTable {
        states: 2,
        initial: 0,
        accepting: vec![false, true],
        delta: (0..512)
            .map(|i| (i >> 8) ^ usize::from(i & 0x81 == 0x81))
            .collect(),
    }
}

#[test]
fn unpacked_baseline() {
    let dfa = parity_dfa();
    for n in [16 << 10, 64 << 10] {
        let bytes = payload(n);
        let expected = dfa.accepts(&bytes);
        let start = Instant::now();
        let (stmt, proof) = prove_algebraic_document(
            &dfa,
            &bytes,
            ClaimData::Accept(expected),
            &[71; 32],
            &[62; 32],
        )
        .unwrap();
        let wire = encode_algebraic_receipt(&stmt, &proof).unwrap();
        let prover = start.elapsed();
        assert_eq!(stmt.fri_queries, 148);
        assert_eq!(stmt.fri_ell, stmt.cube_dim + 3);
        let packed_symbols =
            minidregg_prover::tower256_trace_pack::witness_codeword_symbols(n).unwrap();
        let byte_symbols = 1usize << stmt.fri_ell;
        assert_eq!(byte_symbols, 32 * packed_symbols);
        assert_eq!(8 * byte_symbols, 256 * packed_symbols);
        let start = Instant::now();
        verify_algebraic_cert_bytes(&stmt, &wire).unwrap();
        println!(
            "BENCH unpacked n={n} witness_symbols={} prove_ms={:.3} verify_ms={:.3} proof_bytes={}",
            1 << stmt.fri_ell,
            prover.as_secs_f64() * 1000.,
            start.elapsed().as_secs_f64() * 1000.,
            wire.len()
        );
    }
}

fn basis(j: usize) -> F {
    let mut b = [0; 32];
    b[j / 8] = 1 << (j % 8);
    F::from_le_bytes(b)
}
fn coord(x: F, j: usize) -> bool {
    x.limbs()[j / 64] & (1 << (j % 64)) != 0
}
fn unhex(v: &Value) -> F {
    let s = v.as_str().unwrap();
    assert_eq!(s.len(), 64);
    F::from_le_bytes(std::array::from_fn(|i| {
        u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()
    }))
}

#[test]
fn lean_conformance_and_trace_duality() {
    let v: Value = serde_json::from_str(include_str!(
        "../testdata/tower256_trace_pack_conformance.json"
    ))
    .unwrap();
    assert_eq!(v["schema"], "minidregg.tower256_trace_pack_conformance.v1");
    let mask = unhex(&v["trace_mask_hex"]);
    let rho = unhex(&v["rho_hex"]);
    assert!(trace(rho));
    assert_eq!(rho, basis(128));
    assert_eq!(unhex(&v["top_monomial_hex"]), basis(255));
    assert_eq!(
        trace(basis(255)),
        v["top_monomial_trace"].as_bool().unwrap()
    );
    assert_eq!(v["dual_basis_hex"].as_array().unwrap().len(), 256);
    for j in 0..256 {
        assert_eq!(trace(basis(j)), coord(mask, j));
        assert_eq!(dual_basis()[j], unhex(&v["dual_basis_hex"][j]));
        for i in 0..256 {
            assert_eq!(pluck_bit_via_dual(basis(i), j as u8), i == j);
        }
    }
    for vector in v["artin_schreier_vectors"].as_array().unwrap() {
        let z = unhex(&vector["z_hex"]);
        assert_eq!(trace(z), vector["trace"].as_bool().unwrap());
        if trace(z) {
            assert!(vector["t_hex"].is_null());
        } else {
            assert_eq!(artin_schreier(unhex(&vector["t_hex"])), z);
        }
    }
    let t = &v["packed_tensor_claim"];
    let xs: Vec<_> = t["x_hex"].as_array().unwrap().iter().map(unhex).collect();
    let cs: Vec<_> = t["c_hex"].as_array().unwrap().iter().map(unhex).collect();
    let d = unhex(&t["d_seed_hex"]);
    let y = unhex(&t["y_hex"]);
    let w = transpose_bit_matrix_256(&cs, &xs).unwrap();
    for (l, &column) in w.iter().enumerate() {
        let direct = cs
            .iter()
            .zip(&xs)
            .filter(|(c, _)| coord(**c, l))
            .fold(F::ZERO, |v, (_, x)| v.add(*x));
        assert_eq!(column, direct);
    }
    let value = w
        .iter()
        .enumerate()
        .fold(F::ZERO, |v, (l, &x)| v.add(mul(mul(basis(l), d), x)));
    assert_eq!(value, y);
    for (j, key) in [(0, "z_bit0_hex"), (128, "z_bit128_hex")] {
        let z = mul(dual_basis()[j], value).add(if coord(y, j) { rho } else { F::ZERO });
        assert_eq!(unhex(&t[key]), z);
        assert!(!trace(z));
    }
    for x in xs {
        assert_eq!(pack_32_bytes_bijective(x.to_le_bytes()), x);
    }
    assert!(transpose_bit_matrix_256(&cs, &[]).is_err());
}

#[test]
fn full_width_artin_schreier_distribution() {
    // Rank of the binary linear operator on ALL 256 basis vectors. Equal-size
    // fibers then give its exact distribution without sampling 2^256 elements.
    let mut pivots = [F::ZERO; 256];
    let mut rank = 0;
    for j in 0..256 {
        let mut v = artin_schreier(basis(j));
        assert!(!trace(v));
        for i in (0..256).rev() {
            if !coord(v, i) {
                continue;
            }
            if pivots[i].is_zero() {
                pivots[i] = v;
                rank += 1;
                break;
            }
            v = v.add(pivots[i]);
        }
    }
    // fast_square256 XORs 32 byte-table contributions. Check every entry
    // against the basis expansion before using linear rank to count fibers.
    for pos in 0..32 {
        let columns: [F; 8] = std::array::from_fn(|b| artin_schreier(basis(8 * pos + b)));
        for byte in 0u8..=255 {
            let mut x = [0u8; 32];
            x[pos] = byte;
            let expected = columns
                .iter()
                .enumerate()
                .filter(|(j, _)| byte & (1 << j) != 0)
                .fold(F::ZERO, |s, (_, &v)| s.add(v));
            assert_eq!(expected, artin_schreier(F::from_le_bytes(x)));
        }
    }
    assert!(trace(basis(128)));
    assert_eq!(rank, 255);
    assert_eq!(artin_schreier(F::ONE), F::ZERO);
    let x = F::from_le_bytes([173; 32]);
    let y = F::from_le_bytes([92; 32]);
    assert_eq!(sq(x.add(y)), sq(x).add(sq(y)));
    println!("AS rank={rank}, fibers=2, trace-zero image dimension=255, exact TVD=0");
}

#[test]
fn packed_receipts_and_negatives() {
    let dfa = ByteAndDfa {
        left: 1,
        right: 128,
    };
    for n in [16384usize, 65536] {
        let mut bytes = payload(n);
        let claim = parity_dfa().accepts(&bytes);
        assert_eq!(dfa.accepts(&bytes), claim);
        let start = Instant::now();
        let (root, proof) = prove(&bytes, dfa, claim, &[71; 32], &[62; 32]).unwrap();
        let prover = start.elapsed();
        let start = Instant::now();
        verify(&root, n, dfa, claim, &proof).unwrap();
        let verifier = start.elapsed();
        assert_eq!(content_commitment(&bytes, &[71; 32]).unwrap(), root);
        println!(
            "BENCH packed n={n} witness_symbols={} prove_ms={:.3} verify_ms={:.3} proof_bytes={}",
            minidregg_prover::tower256_trace_pack::witness_codeword_symbols(n).unwrap(),
            prover.as_secs_f64() * 1000.,
            verifier.as_secs_f64() * 1000.,
            proof.len()
        );
        if n == 65536 {
            // Flip an input bit ignored by this DFA. The claim stays true, so
            // rejection must come from binding to the independent document root.
            bytes[n - 1] ^= 0x40;
            assert_eq!(dfa.accepts(&bytes), claim);
            let changed_root = content_commitment(&bytes, &[71; 32]).unwrap();
            assert_ne!(root, changed_root);
            assert!(verify(&changed_root, n, dfa, claim, &proof).is_err());
            assert!(verify(&root, n, dfa, !claim, &proof).is_err());
            let mut bad = proof.clone();
            let first_u = 32 * (1 + 6 + (n.ilog2() as usize - 1) * 4 + 2);
            bad[first_u + 16] ^= 1;
            assert_eq!(
                verify(&root, n, dfa, claim, &bad),
                Err("trace-one masked claim")
            );
            let last = bad.len() - 1;
            bad = proof.clone();
            bad[last] ^= 1;
            assert_eq!(
                verify(&root, n, dfa, claim, &bad),
                Err("Merkle authentication")
            );
        }
    }
}

#[test]
fn short_partial_block_and_empty_input() {
    let dfa = ByteAndDfa {
        left: 0x33,
        right: 0x55,
    };
    let bytes = &payload(37);
    let claim = dfa.accepts(bytes);
    let (root, proof) = prove(bytes, dfa, claim, &[22; 32], &[12; 32]).unwrap();
    verify(&root, 37, dfa, claim, &proof).unwrap();
    assert!(prove(bytes, dfa, !claim, &[22; 32], &[12; 32]).is_err());
    assert!(verify(&root, 36, dfa, claim, &proof).is_err());
    assert!(verify(&root, 37, dfa, claim, &proof[..proof.len() - 1]).is_err());
    assert!(prove(&[], dfa, false, &[0; 32], &[0; 32]).is_err());
}

#[test]
fn table_dfa_receipts() {
    use minidregg_prover::tower256_trace_pack::{prove_dfa, verify_dfa};
    let table = parity_dfa();
    for n in [16 << 10, 64 << 10] {
        let bytes = payload(n);
        let claim = table.accepts(&bytes);
        let start = Instant::now();
        let (root, proof) = prove_dfa(&bytes, &table, claim, &[71; 32], &[30; 32]).unwrap();
        let prover = start.elapsed();
        let start = Instant::now();
        verify_dfa(&root, n, &table, claim, &proof).unwrap();
        let verifier = start.elapsed();
        assert_eq!(root, content_commitment(&bytes, &[71; 32]).unwrap());
        println!("BENCH packed_table n={n} witness_symbols={} prove_ms={:.3} verify_ms={:.3} proof_bytes={}",
             minidregg_prover::tower256_trace_pack::witness_codeword_symbols(n).unwrap(),prover.as_secs_f64()*1000.,verifier.as_secs_f64()*1000.,proof.len());
    }
    let table = DfaTable::no_sk_dash();
    for bytes in [&b"a secret sk-test"[..], &b"sk"[..], &b"x"[..]] {
        let claim = table.accepts(bytes);
        let (root, proof) =
            prove_dfa(bytes, &table, claim, &[7; 32], &[bytes.len() as u8; 32]).unwrap();
        verify_dfa(&root, bytes.len(), &table, claim, &proof).unwrap();
        assert!(verify_dfa(&root, bytes.len(), &table, !claim, &proof).is_err());
        let mut changed = table.clone();
        changed.initial = (table.initial + 1) % table.states;
        assert!(verify_dfa(&root, bytes.len(), &changed, claim, &proof).is_err());
    }
}
