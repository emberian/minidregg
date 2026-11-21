//! Conformance, zero-decay (`alpha_t = 0`), falsifier-teeth (`UW` 1-cell mutation &
//! `L_{0,0} = -1` non-strict-lower collision witness), and `Qwen3.8-Flash-Next` full-layer
//! (`H_v = 48, d = 128, C = 64`) `--release` benchmark suite for `prover/src/deltanet_wy.rs`
//! against `prover/testdata/deltanet_wy_conformance.json` (`Compiler/DeltaNetWyConformance.lean`).

use std::hint::black_box;
use std::path::Path;
use std::time::Instant;

use serde::Deserialize;

use minidregg_prover::babybear::{badd, bmul, P};
use minidregg_prover::deltanet_wy::{
    gdn_chunkwise_wy_head_bb, gdn_chunkwise_wy_layer_bb, gdn_sequential_head_bb,
    is_strict_lower_tri_2d, neumann_inv_bb, prove_wy_chunk_gruen, verify_wy_bilinear_unchecked_l,
    verify_wy_chunk_gruen,
};

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct DeltaNetWyConformanceFile {
    p: u64,
    c: usize,
    dk: usize,
    dv: usize,
    alpha: Vec<u64>,
    beta: Vec<u64>,
    q: Vec<Vec<u64>>,
    k: Vec<Vec<u64>>,
    v: Vec<Vec<u64>>,
    s_init: Vec<Vec<u64>>,
    gamma: Vec<u64>,
    bar_gamma: Vec<u64>,
    cap_gamma: Vec<Vec<u64>>,
    matrix_l: Vec<Vec<u64>>,
    neumann_inv_l: Vec<Vec<u64>>,
    rhs: Vec<Vec<u64>>,
    uw: Vec<Vec<u64>>,
    y_out: Vec<Vec<u64>>,
    s_final: Vec<Vec<u64>>,
}

fn load_conformance() -> DeltaNetWyConformanceFile {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/deltanet_wy_conformance.json"
    );
    let raw = std::fs::read_to_string(Path::new(path))
        .expect("read Lean-authored deltanet_wy_conformance.json");
    let c: DeltaNetWyConformanceFile =
        serde_json::from_str(&raw).expect("parse Lean-authored deltanet_wy_conformance.json");
    assert_eq!(c.p, P);
    assert_eq!(c.c, 4);
    assert_eq!(c.dk, 2);
    assert_eq!(c.dv, 2);
    assert_eq!(c.alpha[1], 0, "vector must exercise alpha_1 == 0 zero-decay step");
    c
}

fn matmul_bb(a: &[Vec<u64>], b: &[Vec<u64>]) -> Vec<Vec<u64>> {
    let m = a.len();
    let k = a[0].len();
    let n = b[0].len();
    (0..m)
        .map(|i| {
            (0..n)
                .map(|j| (0..k).fold(0u64, |acc, q| badd(acc, bmul(a[i][q], b[q][j]))))
                .collect()
        })
        .collect()
}

fn flatten_2d(m: &[Vec<u64>]) -> Vec<u64> {
    m.iter().flat_map(|r| r.iter().copied()).collect()
}

#[test]
fn lean_conformance_vector_wy_and_sequential_agree() {
    let c = load_conformance();

    // 1. Sequential GDN recurrence matches Lean `yOut` and `sFinal`:
    let (y_seq, s_seq) =
        gdn_sequential_head_bb(&c.q, &c.k, &c.v, &c.alpha, &c.beta, &c.s_init);
    assert_eq!(y_seq, c.y_out, "sequential gdnStep/gdnReadout matches Lean yOut");
    assert_eq!(s_seq, c.s_final, "sequential gdnStep matches Lean sFinal");

    // 2. Division-free chunkwise WY matches Lean on every intermediate and final matrix:
    let wy = gdn_chunkwise_wy_head_bb(&c.q, &c.k, &c.v, &c.alpha, &c.beta, &c.s_init);
    assert_eq!(wy.gamma, c.gamma);
    assert_eq!(wy.bar_gamma, c.bar_gamma);
    assert_eq!(wy.cap_gamma, c.cap_gamma);
    assert_eq!(wy.matrix_l, c.matrix_l);
    assert!(is_strict_lower_tri_2d(&wy.matrix_l));
    assert_eq!(wy.rhs, c.rhs);
    assert_eq!(wy.uw, c.uw);
    assert_eq!(wy.y_out, c.y_out);
    assert_eq!(wy.s_final, c.s_final);

    // 3. `neumannInv(L)` matches Lean and satisfies `(I + L)*UW == RHS` & `neumannInv(L)*RHS == UW`:
    let n_inv = neumann_inv_bb(&c.matrix_l);
    assert_eq!(n_inv, c.neumann_inv_l, "neumannInv matches Lean");
    assert_eq!(matmul_bb(&n_inv, &c.rhs), c.uw, "neumannInv(L) * RHS == UW");

    let mut i_plus_l = c.matrix_l.clone();
    for idx in 0..c.c {
        i_plus_l[idx][idx] = badd(i_plus_l[idx][idx], 1);
    }
    assert_eq!(matmul_bb(&i_plus_l, &c.uw), c.rhs, "(I + L) * UW == RHS");

    // 4. Flat multi-head kernel at H_v = H_k = 1 agrees identically and Gruen Mode-2 verifies:
    let layer = gdn_chunkwise_wy_layer_bb(
        1,
        1,
        c.c,
        c.dk,
        c.dv,
        &flatten_2d(&c.q),
        &flatten_2d(&c.k),
        &flatten_2d(&c.v),
        &c.alpha,
        &c.beta,
        &flatten_2d(&c.s_init),
    );
    assert_eq!(layer.l_flat, flatten_2d(&c.matrix_l));
    assert_eq!(layer.rhs_flat, flatten_2d(&c.rhs));
    assert_eq!(layer.uw_flat, flatten_2d(&c.uw));
    assert_eq!(layer.y_flat, flatten_2d(&c.y_out));
    assert_eq!(layer.s_final_flat, flatten_2d(&c.s_final));

    let cols = c.dv + c.dk;
    let r_h: Vec<u64> = vec![]; // H_v = 1 -> 2^0 => 0 head bits
    let r_i = vec![123_456_789, 987_654_321];
    let r_k = vec![111_222_333, 444_555_666];
    let chals = vec![777_888_999, 314_159_265];

    let proof = prove_wy_chunk_gruen(
        1,
        c.c,
        cols,
        &layer.l_flat,
        &layer.uw_flat,
        &layer.rhs_flat,
        &r_h,
        &r_i,
        &r_k,
        &chals,
    );
    assert!(verify_wy_chunk_gruen(
        1,
        c.c,
        cols,
        &layer.l_flat,
        &layer.uw_flat,
        &layer.rhs_flat,
        &proof
    ));
}

#[test]
fn multi_chunk_c64_with_zero_alpha_matches_sequential() {
    let h_k = 2usize;
    let h_v = 6usize; // 3:1 GVA
    let rep = h_v / h_k;
    let c_len = 64usize;
    let d_k = 16usize;
    let d_v = 16usize;
    let n_chunks = 2usize;

    let mut s_seq_heads: Vec<Vec<Vec<u64>>> = (0..h_v)
        .map(|hv| {
            (0..d_k)
                .map(|d| (0..d_v).map(|v| ((hv * 37 + d * 13 + v + 1) as u64) % P).collect())
                .collect()
        })
        .collect();
    let mut s_wy_flat: Vec<u64> = s_seq_heads
        .iter()
        .flat_map(|m| m.iter().flat_map(|r| r.iter().copied()))
        .collect();

    for chunk in 0..n_chunks {
        let q_flat: Vec<u64> = (0..(h_k * c_len * d_k))
            .map(|i| ((chunk * 1009 + i * 73 + 11) as u64) % P)
            .collect();
        let k_flat: Vec<u64> = (0..(h_k * c_len * d_k))
            .map(|i| ((chunk * 2003 + i * 59 + 7) as u64) % P)
            .collect();
        let v_flat: Vec<u64> = (0..(h_v * c_len * d_v))
            .map(|i| ((chunk * 3001 + i * 97 + 19) as u64) % P)
            .collect();
        let mut alpha_flat: Vec<u64> = (0..(h_v * c_len))
            .map(|i| ((chunk * 503 + i * 41 + 3) as u64) % P)
            .collect();
        // Inject explicit zero-decay alpha_t == 0 steps inside both chunks!
        alpha_flat[17] = 0;
        alpha_flat[c_len * 3 + 42] = 0;
        let beta_flat: Vec<u64> = (0..(h_v * c_len))
            .map(|i| ((chunk * 701 + i * 31 + 5) as u64) % P)
            .collect();

        let wy = gdn_chunkwise_wy_layer_bb(
            h_k,
            h_v,
            c_len,
            d_k,
            d_v,
            &q_flat,
            &k_flat,
            &v_flat,
            &alpha_flat,
            &beta_flat,
            &s_wy_flat,
        );

        for hv in 0..h_v {
            let hk = hv / rep;
            let q_2d: Vec<Vec<u64>> = (0..c_len)
                .map(|t| q_flat[(hk * c_len + t) * d_k..(hk * c_len + t + 1) * d_k].to_vec())
                .collect();
            let k_2d: Vec<Vec<u64>> = (0..c_len)
                .map(|t| k_flat[(hk * c_len + t) * d_k..(hk * c_len + t + 1) * d_k].to_vec())
                .collect();
            let v_2d: Vec<Vec<u64>> = (0..c_len)
                .map(|t| v_flat[(hv * c_len + t) * d_v..(hv * c_len + t + 1) * d_v].to_vec())
                .collect();
            let a_1d = &alpha_flat[hv * c_len..(hv + 1) * c_len];
            let b_1d = &beta_flat[hv * c_len..(hv + 1) * c_len];
            let (y_seq, s_next) =
                gdn_sequential_head_bb(&q_2d, &k_2d, &v_2d, a_1d, b_1d, &s_seq_heads[hv]);
            assert_eq!(
                &wy.y_flat[hv * c_len * d_v..(hv + 1) * c_len * d_v],
                flatten_2d(&y_seq).as_slice(),
                "chunk {chunk} head {hv} Y matches sequential"
            );
            assert_eq!(
                &wy.s_final_flat[hv * d_k * d_v..(hv + 1) * d_k * d_v],
                flatten_2d(&s_next).as_slice(),
                "chunk {chunk} head {hv} S_final matches sequential"
            );
            s_seq_heads[hv] = s_next;
        }
        s_wy_flat = wy.s_final_flat.clone();

        // Prove and verify chunk WY solve via Gruen Mode-2 (including an interior r_h[1] == 0!):
        let r_h = vec![101_010, 0, 303_030]; // H_v = 6 -> H_pad = 8 (3 bits), r_h[1] == 0!
        let r_i: Vec<u64> = (0..6).map(|b| (b + 1) * 111_117).collect();
        let r_k: Vec<u64> = (0..5).map(|b| (b + 1) * 222_229).collect(); // d_v + d_k = 32 (5 bits)
        let chals: Vec<u64> = (0..9).map(|b| (b + 1) * 333_337).collect();
        let pf = prove_wy_chunk_gruen(
            h_v,
            c_len,
            d_v + d_k,
            &wy.l_flat,
            &wy.uw_flat,
            &wy.rhs_flat,
            &r_h,
            &r_i,
            &r_k,
            &chals,
        );
        assert!(verify_wy_chunk_gruen(
            h_v,
            c_len,
            d_v + d_k,
            &wy.l_flat,
            &wy.uw_flat,
            &wy.rhs_flat,
            &pf
        ));
    }
}

/// **Falsifier A1a:** Mutating a single cell of `UW` breaks `(I + L) · UW = RHS` and is rejected.
#[test]
fn falsifier_a1a_uw_single_cell_mutation_rejected() {
    let c = load_conformance();
    let cols = c.dv + c.dk;
    let l_flat = flatten_2d(&c.matrix_l);
    let rhs_flat = flatten_2d(&c.rhs);
    let uw_flat = flatten_2d(&c.uw);

    let r_i = vec![424_242_424, 535_353_535];
    let r_k = vec![646_464_646, 757_575_757];
    let chals = vec![868_686_868, 979_797_979];

    let honest_pf = prove_wy_chunk_gruen(
        1, c.c, cols, &l_flat, &uw_flat, &rhs_flat, &[], &r_i, &r_k, &chals,
    );
    assert!(verify_wy_chunk_gruen(
        1, c.c, cols, &l_flat, &uw_flat, &rhs_flat, &honest_pf
    ));

    // 1. Mutate `UW` against the honest proof:
    let mut uw_bad = uw_flat.clone();
    uw_bad[9] = badd(uw_bad[9], 1);
    assert!(!verify_wy_chunk_gruen(
        1, c.c, cols, &l_flat, &uw_bad, &rhs_flat, &honest_pf
    ));

    // 2. Even if a cheating prover re-runs `prove_wy_chunk_gruen` on `uw_bad`, `L * uw_bad != RHS - uw_bad`:
    let dishonest_pf = prove_wy_chunk_gruen(
        1, c.c, cols, &l_flat, &uw_bad, &rhs_flat, &[], &r_i, &r_k, &chals,
    );
    assert!(!verify_wy_chunk_gruen(
        1,
        c.c,
        cols,
        &l_flat,
        &uw_bad,
        &rhs_flat,
        &dishonest_pf
    ));
}

/// **Falsifier A1b (`wyChunk_nonStrictLower_falsifier`):**
/// Violating `IsStrictLowerTri L` by setting `L_{0,0} = -1` (`P - 1`) makes `I + L` singular on
/// row 0 (`1 + L_{0,0} = 0`), admitting TWO DISTINCT witnesses `UW_1 != UW_2` that BOTH satisfy
/// `(I + L) · UW = RHS` and pass unchecked bilinear sumcheck, while `verify_wy_chunk_gruen`
/// rejects `L_bad` via its `is_strict_lower_tri_flat` guard!
#[test]
fn falsifier_a1b_non_strict_lower_l00_neg_one_collision_witness() {
    let c = load_conformance();
    let cols = c.dv + c.dk;

    // Construct L_bad with L_bad[0][0] = P - 1 (-1 mod P) and strictly lower entries elsewhere:
    let mut l_bad = vec![vec![0u64; c.c]; c.c];
    l_bad[0][0] = P - 1;
    l_bad[2][1] = 5;
    l_bad[3][2] = 7;
    assert!(!is_strict_lower_tri_2d(&l_bad));

    // Choose two distinct witnesses UW_1 != UW_2 differing at (0, 0) (`0` vs `1` on row 0,
    // and forward-substituted below so `(I + L_bad)*UW_1 == (I + L_bad)*UW_2 == 0`!):
    let uw1 = vec![vec![0u64; cols]; c.c];
    let mut uw2 = vec![vec![0u64; cols]; c.c];
    uw2[0][0] = 1; // Since (I + L_bad)[0,0] = 0 and L_bad[i,0] = 0 for i > 0, (I + L_bad)*uw2 == 0!
    let rhs_zero = vec![vec![0u64; cols]; c.c];

    let mut i_plus_l_bad = l_bad.clone();
    for idx in 0..c.c {
        i_plus_l_bad[idx][idx] = badd(i_plus_l_bad[idx][idx], 1);
    }
    assert_ne!(uw1, uw2);
    assert_eq!(matmul_bb(&i_plus_l_bad, &uw1), rhs_zero);
    assert_eq!(matmul_bb(&i_plus_l_bad, &uw2), rhs_zero);

    let l_bad_flat = flatten_2d(&l_bad);
    let uw1_flat = flatten_2d(&uw1);
    let uw2_flat = flatten_2d(&uw2);
    let rhs_flat = flatten_2d(&rhs_zero);
    let r_i = vec![123_456, 654_321];
    let r_k = vec![234_567, 765_432];
    let chals = vec![345_678, 876_543];

    let pf1 = prove_wy_chunk_gruen(
        1, c.c, cols, &l_bad_flat, &uw1_flat, &rhs_flat, &[], &r_i, &r_k, &chals,
    );
    let pf2 = prove_wy_chunk_gruen(
        1, c.c, cols, &l_bad_flat, &uw2_flat, &rhs_flat, &[], &r_i, &r_k, &chals,
    );

    // Unchecked bilinear sumcheck accepts BOTH colliding witnesses:
    assert!(verify_wy_bilinear_unchecked_l(
        1, c.c, cols, &l_bad_flat, &uw1_flat, &rhs_flat, &pf1
    ));
    assert!(verify_wy_bilinear_unchecked_l(
        1, c.c, cols, &l_bad_flat, &uw2_flat, &rhs_flat, &pf2
    ));

    // Deployed `verify_wy_chunk_gruen` REJECTS both because `L_bad` fails `IsStrictLowerTri`:
    assert!(!verify_wy_chunk_gruen(
        1, c.c, cols, &l_bad_flat, &uw1_flat, &rhs_flat, &pf1
    ));
    assert!(!verify_wy_chunk_gruen(
        1, c.c, cols, &l_bad_flat, &uw2_flat, &rhs_flat, &pf2
    ));
}

#[test]
fn release_benchmark_qwen38_flash_next_full_gdn_layer() {
    // Source-exact Qwen3.8-Flash-Next GDN layer dimensions (`arXiv:2608.30320` Table 1):
    // H_k = 16, H_v = 48 (3:1 GVA), d_k = 128, d_v = 128, C = 64 (`UW` is 48 × 64 × 256).
    let h_k = 16usize;
    let h_v = 48usize;
    let c_len = 64usize;
    let d_k = 128usize;
    let d_v = 128usize;
    let cols = d_v + d_k; // 256

    let q_flat: Vec<u64> = (0..(h_k * c_len * d_k))
        .map(|i| (i as u64 * 1_000_003 + 17) % P)
        .collect();
    let k_flat: Vec<u64> = (0..(h_k * c_len * d_k))
        .map(|i| (i as u64 * 2_000_003 + 29) % P)
        .collect();
    let v_flat: Vec<u64> = (0..(h_v * c_len * d_v))
        .map(|i| (i as u64 * 3_000_017 + 43) % P)
        .collect();
    let mut alpha_flat: Vec<u64> = (0..(h_v * c_len))
        .map(|i| (i as u64 * 97_531 + 5) % P)
        .collect();
    alpha_flat[0 * c_len + 31] = 0; // include zero-decay step in head 0!
    let beta_flat: Vec<u64> = (0..(h_v * c_len))
        .map(|i| (i as u64 * 86_429 + 11) % P)
        .collect();
    let s_init_flat: Vec<u64> = (0..(h_v * d_k * d_v))
        .map(|i| (i as u64 * 12_347 + 3) % P)
        .collect();

    // Warmup:
    let warm = gdn_chunkwise_wy_layer_bb(
        h_k,
        h_v,
        c_len,
        d_k,
        d_v,
        &q_flat,
        &k_flat,
        &v_flat,
        &alpha_flat,
        &beta_flat,
        &s_init_flat,
    );

    // Cross-check head 0 (which contains `alpha == 0` at step 31) against sequential `gdnStep`:
    let q0: Vec<Vec<u64>> = (0..c_len)
        .map(|t| q_flat[t * d_k..(t + 1) * d_k].to_vec())
        .collect();
    let k0: Vec<Vec<u64>> = (0..c_len)
        .map(|t| k_flat[t * d_k..(t + 1) * d_k].to_vec())
        .collect();
    let v0: Vec<Vec<u64>> = (0..c_len)
        .map(|t| v_flat[t * d_v..(t + 1) * d_v].to_vec())
        .collect();
    let s0: Vec<Vec<u64>> = (0..d_k)
        .map(|d| s_init_flat[d * d_v..(d + 1) * d_v].to_vec())
        .collect();
    let (y0_seq, s0_seq) = gdn_sequential_head_bb(
        &q0,
        &k0,
        &v0,
        &alpha_flat[..c_len],
        &beta_flat[..c_len],
        &s0,
    );
    assert_eq!(&warm.y_flat[..c_len * d_v], flatten_2d(&y0_seq).as_slice());
    assert_eq!(
        &warm.s_final_flat[..d_k * d_v],
        flatten_2d(&s0_seq).as_slice()
    );

    let r_h: Vec<u64> = (0..6).map(|b| (b + 1) * 135_791_113).collect(); // H_pad = 64 -> 6 Gruen rounds
    let r_i: Vec<u64> = (0..6).map(|b| (b + 1) * 246_802_468).collect(); // C = 64 -> 6 bits
    let r_k: Vec<u64> = (0..8).map(|b| (b + 1) * 369_258_147).collect(); // d_v+d_k = 256 -> 8 bits
    let chals: Vec<u64> = (0..12).map(|b| (b + 1) * 159_753_486).collect(); // 6 + 6 = 12 quadratic rounds

    let reps = 5usize;
    let mut dts_wy = Vec::with_capacity(reps);
    let mut dts_prove = Vec::with_capacity(reps);
    let mut dts_verify = Vec::with_capacity(reps);
    let mut last_ok = false;

    for _ in 0..reps {
        let t0 = Instant::now();
        let wy = black_box(gdn_chunkwise_wy_layer_bb(
            h_k,
            h_v,
            c_len,
            d_k,
            d_v,
            black_box(&q_flat),
            black_box(&k_flat),
            black_box(&v_flat),
            black_box(&alpha_flat),
            black_box(&beta_flat),
            black_box(&s_init_flat),
        ));
        dts_wy.push(t0.elapsed().as_secs_f64());

        let t1 = Instant::now();
        let pf = black_box(prove_wy_chunk_gruen(
            h_v,
            c_len,
            cols,
            black_box(&wy.l_flat),
            black_box(&wy.uw_flat),
            black_box(&wy.rhs_flat),
            black_box(&r_h),
            black_box(&r_i),
            black_box(&r_k),
            black_box(&chals),
        ));
        dts_prove.push(t1.elapsed().as_secs_f64());

        let t2 = Instant::now();
        last_ok = black_box(verify_wy_chunk_gruen(
            h_v,
            c_len,
            cols,
            black_box(&wy.l_flat),
            black_box(&wy.uw_flat),
            black_box(&wy.rhs_flat),
            black_box(&pf),
        ));
        dts_verify.push(t2.elapsed().as_secs_f64());
    }
    assert!(last_ok);
    dts_wy.sort_by(|a, b| a.partial_cmp(b).unwrap());
    dts_prove.sort_by(|a, b| a.partial_cmp(b).unwrap());
    dts_verify.sort_by(|a, b| a.partial_cmp(b).unwrap());

    println!(
        "[BENCH Qwen3.8-Flash-Next 1L GDN (H_k=16, H_v=48, d=128, C=64)] wy_witness_solve={:.3}ms | gruen_mode2_prove(12r)={:.3}ms | verify(incl_F1_bind)={:.3}ms | total_1L_chunk={:.3}ms (per_tok={:.3}ms)",
        dts_wy[reps / 2] * 1e3,
        dts_prove[reps / 2] * 1e3,
        dts_verify[reps / 2] * 1e3,
        (dts_wy[reps / 2] + dts_prove[reps / 2]) * 1e3,
        (dts_wy[reps / 2] + dts_prove[reps / 2]) * 1e3 / (c_len as f64),
    );
}
