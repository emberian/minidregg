//! Conformance, falsifier-teeth, MXFP4 7-bucket 0-mul Horner, and `--release` benchmark suite for
//! `prover/src/gruen_einsum.rs` against the Lean-authored vector
//! `prover/testdata/gruen_einsumcheck_conformance.json` (`Compiler/GruenEinSumcheckConformance.lean`).

use std::hint::black_box;
use std::path::Path;
use std::time::Instant;

use serde::Deserialize;

use minidregg_prover::babybear::{badd, binv, bmul, bsub, P};
use minidregg_prover::gruen_einsum::{
    build_eq_suffix_tables, build_eq_suffix_tables_bb, build_eq_table_lsb_bb, decode_e2m1_x2_bb,
    e2m1_horner_buckets_bb, e2m1_horner_dot_bb, encode_e2m1_x2, eq_lin_eval, eq_mle_eval,
    eval_quad_zero_one_inf, gruen_f2_round_evals_bb, gruen_f2_round_evals_p,
    gruen_quotient_literal, mle3_eval, prove_gruen_einsum_mode2, prove_gruen_einsum_mode2_bb,
    prove_mxfp4_delayed_bjk_horner, prove_mxfp4_naive_bjk, verify_gruen_einsum_mode2,
    verify_mxfp4_bjk_mode2, EinSumcheckInstance, GruenRoundMsg, E2M1_X2_MAGS,
};
use minidregg_prover::sumcheck::{
    cubic_round_evals, mle_eval, prove_cubic_sumcheck, CubicTables, Fp,
};

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct RoundVector {
    phase: String,
    z_eq: Fp,
    zero_eq_fallback: bool,
    q0: Fp,
    q1: Fp,
    q_inf: Fp,
    q2: Fp,
    wire: Vec<Fp>,
    next_sigma: Fp,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct E2m1HornerVector {
    nibbles: Vec<u8>,
    vec: Vec<Fp>,
    buckets: Vec<Fp>,
    planes: Vec<Fp>,
    expected_dot: Fp,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct GruenConformanceFile {
    p: u64,
    mu_l: usize,
    mu_r: usize,
    mu_s: usize,
    kappa: usize,
    table_a: Vec<Vec<Vec<Fp>>>,
    table_b: Vec<Vec<Vec<Fp>>>,
    x_l: Vec<Fp>,
    x_r: Vec<Fp>,
    z_s: Vec<Fp>,
    challenges: Vec<Fp>,
    output_z: Vec<Vec<Vec<Fp>>>,
    claim: Fp,
    rounds: Vec<RoundVector>,
    s_phase_entry_claim: Fp,
    terminal_openings: Vec<Fp>,
    terminal_product: Fp,
    eq_at_c_s: Fp,
    e2m1_horner: E2m1HornerVector,
}

fn load_conformance() -> (GruenConformanceFile, EinSumcheckInstance) {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/gruen_einsumcheck_conformance.json"
    );
    let raw = std::fs::read_to_string(Path::new(path))
        .expect("read Lean-authored gruen_einsumcheck_conformance.json");
    let c: GruenConformanceFile =
        serde_json::from_str(&raw).expect("parse Lean-authored gruen_einsumcheck_conformance.json");
    assert_eq!(c.p, P);
    assert_eq!(c.z_s.len(), c.mu_s);
    assert_eq!(c.challenges.len(), c.mu_s + c.kappa);
    assert_eq!(c.rounds.len(), c.mu_s + c.kappa);
    // Interior F_{>=2} round 1 must exercise z_1 == 0!
    assert_ne!(c.z_s[0], 0);
    assert_eq!(c.z_s[1], 0, "interior F_{{>=2}} round must exercise z_1 == 0");
    assert_ne!(c.z_s[2], 0);
    let inst = EinSumcheckInstance {
        mu_l: c.mu_l,
        mu_r: c.mu_r,
        mu_s: c.mu_s,
        kappa: c.kappa,
        a: c.table_a.clone(),
        b: c.table_b.clone(),
    };
    (c, inst)
}

#[test]
fn lean_conformance_vector_literal_and_folded_agree() {
    let (c, inst) = load_conformance();
    let z_out = inst.einsum_output(c.p);
    assert_eq!(z_out, c.output_z, "einsum_output matches Lean einsumTable");
    assert_eq!(
        mle3_eval(&z_out, &c.x_l, &c.x_r, &c.z_s, c.p),
        c.claim,
        "mle3_eval matches Lean claim"
    );

    let left_tab = inst.left_table(&c.x_l, c.p);
    let right_tab = inst.right_table(&c.x_r, c.p);

    // 1. Literal mirror reproduces q(0), q(1), q(2), q(∞), and nextSigma in every round:
    let mut running_sigma = c.claim;
    for (i, rv) in c.rounds.iter().enumerate() {
        let q0_lit = gruen_quotient_literal(
            &left_tab, &right_tab, c.mu_s, c.kappa, &c.z_s, &c.challenges, i, 0, c.p,
        );
        let q1_lit = gruen_quotient_literal(
            &left_tab, &right_tab, c.mu_s, c.kappa, &c.z_s, &c.challenges, i, 1, c.p,
        );
        let q2_lit = gruen_quotient_literal(
            &left_tab, &right_tab, c.mu_s, c.kappa, &c.z_s, &c.challenges, i, 2, c.p,
        );
        assert_eq!(q0_lit, rv.q0, "literal q0 at round {i}");
        assert_eq!(q1_lit, rv.q1, "literal q1 at round {i}");
        assert_eq!(q2_lit, rv.q2, "literal q2 at round {i}");
        assert_eq!(
            eval_quad_zero_one_inf(rv.q0, rv.q1, rv.q_inf, 2, c.p),
            rv.q2,
            "quadFromZeroOneInf at t=2 round {i}"
        );
        if i < c.mu_s {
            assert_eq!(rv.phase, "f2");
            assert_eq!(rv.z_eq, c.z_s[i]);
            let lhs = badd(bmul(bsub(1, c.z_s[i]), rv.q0), bmul(c.z_s[i], rv.q1));
            assert_eq!(lhs, running_sigma, "Gruen eq-weighted round sum at round {i}");
        } else {
            assert_eq!(rv.phase, "s");
            assert_eq!(badd(rv.q0, rv.q1), running_sigma, "S-phase round sum at round {i}");
        }
        let next = eval_quad_zero_one_inf(rv.q0, rv.q1, rv.q_inf, c.challenges[i], c.p);
        assert_eq!(next, rv.next_sigma, "stripped nextSigma at round {i}");
        running_sigma = next;
    }
    assert_eq!(running_sigma, c.terminal_product);

    // 2. Both O(2^m) folded provers (generic `p` and BabyBear-specialized) match Lean wire-for-wire:
    let proof_p = prove_gruen_einsum_mode2(
        &left_tab, &right_tab, c.mu_s, c.kappa, &c.z_s, &c.challenges, c.p,
    );
    let proof_bb = prove_gruen_einsum_mode2_bb(
        &left_tab, &right_tab, c.mu_s, c.kappa, &c.z_s, &c.challenges,
    );
    assert_eq!(proof_p, proof_bb, "generic-p and BabyBear folded provers match");
    assert_eq!(proof_bb.claim, c.claim);
    assert_eq!(proof_bb.s_phase_entry_claim, c.s_phase_entry_claim);
    assert_eq!(
        vec![proof_bb.terminal_openings.0, proof_bb.terminal_openings.1],
        c.terminal_openings
    );
    assert_eq!(
        bmul(proof_bb.terminal_openings.0, proof_bb.terminal_openings.1),
        c.terminal_product
    );
    assert_eq!(
        eq_mle_eval(&c.z_s, &c.challenges[..c.mu_s], c.p),
        c.eq_at_c_s
    );

    for (i, (msg, rv)) in proof_bb.rounds.iter().zip(c.rounds.iter()).enumerate() {
        assert_eq!(msg.wire_slice(), rv.wire, "wire message at round {i}");
        assert_eq!(
            matches!(msg, GruenRoundMsg::ZeroEqFallback { .. }),
            rv.zero_eq_fallback,
            "fallback tag at round {i}"
        );
    }

    assert!(
        verify_gruen_einsum_mode2(
            c.claim,
            &proof_bb,
            |pt| (mle_eval(&left_tab, pt, c.p), mle_eval(&right_tab, pt, c.p)),
            c.p,
        ),
        "honest Mode-2 Gruen transcript verifies"
    );
}

/// **Mechanized Tooth 1 (`gruen_r_zero_q1_unconstrained`, `2024/108` fn. 23):**
/// At interior round 1 (`z_1 == 0`), `ℓ_0(1) = 0` leaves `q_1(1)` unconstrained by the round-sum
/// check `ℓ_0(0)·q(0) + ℓ_0(1)·q(1) = σ_1`. Without deterministic `ZeroEqFallback`, `q_1(1)` cannot
/// be uniquely reconstructed; sending a forged `q_1'(1) != q_1(1)` passes round 1's round-sum check
/// yet diverges at every nonzero challenge `c != 0` and is caught by round 2!
#[test]
fn tooth_1_r_zero_unconstrained_q1_without_fallback() {
    let (c, inst) = load_conformance();
    let left_tab = inst.left_table(&c.x_l, c.p);
    let right_tab = inst.right_table(&c.x_r, c.p);
    let honest = prove_gruen_einsum_mode2_bb(
        &left_tab, &right_tab, c.mu_s, c.kappa, &c.z_s, &c.challenges,
    );

    // 1. Omitting `q1` (`TwoPoint` when `z_1 == 0`) is rejected fail-closed:
    let mut missing_fallback = honest.clone();
    missing_fallback.rounds[1] = GruenRoundMsg::TwoPoint {
        q0: c.rounds[1].q0,
        q_inf: c.rounds[1].q_inf,
    };
    assert!(!verify_gruen_einsum_mode2(
        c.claim,
        &missing_fallback,
        |pt| (mle_eval(&left_tab, pt, c.p), mle_eval(&right_tab, pt, c.p)),
        c.p,
    ));

    // 2. Algebraic unconstrained-q(1) witness at round 1 (`z_1 == 0`, `σ_1 = c.rounds[0].next_sigma`):
    let sigma1 = c.rounds[0].next_sigma;
    let q0 = c.rounds[1].q0;
    let q_inf = c.rounds[1].q_inf;
    let q1_true = c.rounds[1].q1;
    let q1_forged = badd(q1_true, 1);
    assert_ne!(q1_true, q1_forged);

    // BOTH satisfy `eqLin(0, 0)*q0 + eqLin(0, 1)*q1 == sigma1`:
    let lhs_true = badd(bmul(eq_lin_eval(0, 0, P), q0), bmul(eq_lin_eval(0, 1, P), q1_true));
    let lhs_forged = badd(
        bmul(eq_lin_eval(0, 0, P), q0),
        bmul(eq_lin_eval(0, 1, P), q1_forged),
    );
    assert_eq!(lhs_true, sigma1);
    assert_eq!(lhs_forged, sigma1);

    // Yet they diverge at EVERY nonzero challenge (including `c.challenges[1]`) and fail full verify:
    for probe in [1u64, 2, 17, c.challenges[1], P - 1] {
        assert_ne!(
            eval_quad_zero_one_inf(q0, q1_true, q_inf, probe, P),
            eval_quad_zero_one_inf(q0, q1_forged, q_inf, probe, P),
            "diverges at nonzero challenge {probe}"
        );
    }
    let mut forged_fallback = honest;
    forged_fallback.rounds[1] = GruenRoundMsg::ZeroEqFallback {
        q0,
        q_inf,
        q1: q1_forged,
    };
    assert!(!verify_gruen_einsum_mode2(
        c.claim,
        &forged_fallback,
        |pt| (mle_eval(&left_tab, pt, c.p), mle_eval(&right_tab, pt, c.p)),
        c.p,
    ));
}

/// **Mechanized Tooth 2 (`gruen_d2_three_roots_vs_two_witness` & `gruen_unstripped_admits_ell_root`):**
/// Compares Mode-2 stripped direct-`q` checking (`<= d = 2` cheating challenges) against Mode-1
/// unstripped `s(c) = ℓ_r(c) · q(c)` checking (`d + 1 = 3` cheating challenges due to the extra
/// `ℓ_r(c_ell) = 0` root) on BOTH the exact Lean `ZMod 7` witness AND over BabyBear `P`.
#[test]
fn tooth_2_mode2_d_roots_vs_unstripped_d_plus_1_forgery() {
    // Part A: Exact Lean `ZMod 7` witness (`r = 2, q_true = 0, q_prov = (X - 2)(X - 3), σ_false = 5`)
    let p7 = 7u64;
    let r7 = 2u64;
    let sigma_false_7 = 5u64;
    // q_prov(X) = (X - 2)(X - 3) = X^2 - 5X + 6 = 6 + 2X + X^2 in F_7 => q(0)=6, q(1)=2, q(∞)=1
    let (q0_7, q1_7, qinf_7) = (6u64, 2u64, 1u64);
    let round_sum_7 = (eq_lin_eval(r7, 0, p7) * q0_7 + eq_lin_eval(r7, 1, p7) * q1_7) % p7;
    assert_eq!(round_sum_7, sigma_false_7, "passes F_7 round sum for false claim 5");

    let mut mode2_accepts = Vec::new();
    let mut mode1_unstripped_accepts = Vec::new();
    for c in 0..p7 {
        let qc = eval_quad_zero_one_inf(q0_7, q1_7, qinf_7, c, p7);
        let sc = (eq_lin_eval(r7, c, p7) * qc) % p7;
        if qc == 0 {
            mode2_accepts.push(c);
        }
        if sc == 0 {
            mode1_unstripped_accepts.push(c);
        }
    }
    assert_eq!(mode2_accepts, vec![2, 3], "Mode 2 accepts ONLY d = 2 roots");
    assert_eq!(
        mode1_unstripped_accepts,
        vec![2, 3, 5],
        "Unstripped Mode 1 accepts d + 1 = 3 roots (extra root c_ell = 5 where ℓ_2(5) = 0)"
    );

    // Part B: Over BabyBear `P` on round 0 of our Lean conformance vector (`r = z_s[0] = 111111111`):
    let (conf, _) = load_conformance();
    let r_bb = conf.z_s[0];
    let one_sub_2r = bsub(1, bmul(2, r_bb));
    assert_ne!(one_sub_2r, 0);
    let c_ell_bb = bmul(bsub(1, r_bb), binv(one_sub_2r));
    assert_eq!(eq_lin_eval(r_bb, c_ell_bb, P), 0, "ℓ_r(c_ell) == 0 in BabyBear");

    // Construct a degree-2 cheat `q_prov(X) = q_true(X) + (X - 2)(X - 3)` on false claim:
    let q0_t = conf.rounds[0].q0;
    let q1_t = conf.rounds[0].q1;
    let qinf_t = conf.rounds[0].q_inf;
    // Δq(X) = (X - 2)(X - 3) = 6 - 5X + X^2 => Δq(0) = 6, Δq(1) = 2, Δq(∞) = 1
    let q0_p = badd(q0_t, 6);
    let q1_p = badd(q1_t, 2);
    let qinf_p = badd(qinf_t, 1);
    let sigma_false_bb = badd(bmul(bsub(1, r_bb), q0_p), bmul(r_bb, q1_p));
    assert_ne!(sigma_false_bb, conf.claim, "incoming claim is genuinely false");

    // At c = c_ell_bb, unstripped s_prov(c_ell) == s_true(c_ell) == 0, whereas Mode 2 rejects!
    let qp_at_cell = eval_quad_zero_one_inf(q0_p, q1_p, qinf_p, c_ell_bb, P);
    let qt_at_cell = eval_quad_zero_one_inf(q0_t, q1_t, qinf_t, c_ell_bb, P);
    assert_ne!(qp_at_cell, qt_at_cell, "Mode-2 direct-q catches c_ell_bb");
    assert_eq!(
        bmul(eq_lin_eval(r_bb, c_ell_bb, P), qp_at_cell),
        bmul(eq_lin_eval(r_bb, c_ell_bb, P), qt_at_cell),
        "Unstripped Mode-1 grants a 3rd free forgery pass at c_ell_bb"
    );
}

/// **Mechanized Tooth 3 (`gruen_phase_splice_double_strip_tooth`, Jolt PR `#1474`):**
/// In Mode 2, `s_phase_entry_claim = q_{mu_s - 1}(c_{mu_s - 1})` ALREADY stripped `eqMle(z_s, c_s)`.
/// Dividing by `ℓ_{z_2}(c_2)` or `eqMle(z_s, c_s)` a second time at the `F_{>=2} -> S` boundary
/// corrupts the nonzero claim and rejects the honest proof!
#[test]
fn tooth_3_jolt_1474_double_strip_at_f2_to_s_boundary_rejected() {
    let (c, inst) = load_conformance();
    let left_tab = inst.left_table(&c.x_l, c.p);
    let right_tab = inst.right_table(&c.x_r, c.p);
    let honest = prove_gruen_einsum_mode2_bb(
        &left_tab, &right_tab, c.mu_s, c.kappa, &c.z_s, &c.challenges,
    );

    let ell_last = eq_lin_eval(c.z_s[c.mu_s - 1], c.challenges[c.mu_s - 1], P);
    assert_ne!(c.s_phase_entry_claim, 0);
    assert_ne!(ell_last, 0);
    assert_ne!(ell_last, 1);
    assert_ne!(c.eq_at_c_s, 0);
    assert_ne!(c.eq_at_c_s, 1);

    // Double-stripping by `ell_last` or `eq_at_c_s` produces a wrong Phase-2 entry claim that
    // disagrees with round 3's honest `q_3(0) + q_3(1)`:
    let double_stripped_last = bmul(binv(ell_last), c.s_phase_entry_claim);
    let double_stripped_all = bmul(binv(c.eq_at_c_s), c.s_phase_entry_claim);
    let honest_s_sum = badd(c.rounds[c.mu_s].q0, c.rounds[c.mu_s].q1);
    assert_eq!(honest_s_sum, c.s_phase_entry_claim);
    assert_ne!(double_stripped_last, honest_s_sum);
    assert_ne!(double_stripped_all, honest_s_sum);

    // Simulating a prover/verifier mismatch where S-rounds are scaled as if unstripped fails verify:
    let mut bad = honest;
    if let GruenRoundMsg::TwoPoint { q0, q_inf } = bad.rounds[c.mu_s] {
        bad.rounds[c.mu_s] = GruenRoundMsg::TwoPoint {
            q0: bmul(ell_last, q0),
            q_inf: bmul(ell_last, q_inf),
        };
    }
    assert!(!verify_gruen_einsum_mode2(
        c.claim,
        &bad,
        |pt| (mle_eval(&left_tab, pt, P), mle_eval(&right_tab, pt, P)),
        P,
    ));
}

#[test]
fn mxfp4_e2m1_horner_conformance_and_delayed_bind_bjk() {
    let (c, _) = load_conformance();

    // 1. Check every single nibble in 0..16 against naive multiplication:
    for nib in 0..16u8 {
        let v = 123_456_789u64;
        assert_eq!(
            e2m1_horner_dot_bb(&[nib], &[v]),
            bmul(decode_e2m1_x2_bb(nib), v),
            "single nibble {nib}"
        );
    }
    for &mag in &E2M1_X2_MAGS[1..] {
        let pos = encode_e2m1_x2(mag as i8);
        let neg = encode_e2m1_x2(-(mag as i8));
        assert_eq!(decode_e2m1_x2_bb(pos), mag);
        assert_eq!(decode_e2m1_x2_bb(neg), P - mag);
    }

    // 2. Reproduce Lean-decided 32-element E2M1 7-bucket 0-mul Horner conformance vector:
    let hv = &c.e2m1_horner;
    let (buckets, planes, dot) = e2m1_horner_buckets_bb(&hv.nibbles, &hv.vec);
    assert_eq!(buckets.to_vec(), hv.buckets, "7 signed E2M1 buckets match Lean");
    assert_eq!(planes.to_vec(), hv.planes, "4 Horner bit-planes match Lean");
    assert_eq!(dot, hv.expected_dot, "0-mul E2M1 Horner dot matches Lean");

    // 3. End-to-end delayed block-bind (`b -> j -> k`, `l_0 = 5`) vs naive `bmul` prover,
    //    INCLUDING an interior `r_j[1] == 0` fallback!
    let log_j = 4usize; // J = 16
    let log_k = 3usize; // K = 8
    let j_len = 1usize << log_j;
    let k_len = 1usize << log_k;

    let x_ri: Vec<u64> = (0..(k_len * 32))
        .map(|i| ((i as u64 + 1) * 97_531_246 + 13_579) % P)
        .collect();
    let q_nibbles: Vec<u8> = (0..(j_len * k_len * 32))
        .map(|i| ((i * 11 + 5) % 16) as u8)
        .collect();
    let s_scale: Vec<u64> = (0..(j_len * k_len))
        .map(|i| ((i as u64 + 3) * 31_415_926 + 7) % P)
        .collect();

    let r_j = vec![123_456_789, 0, 555_555_555, 777_777_777]; // r_j[1] == 0!
    let chals_b = [111_111, 222_222, 333_333, 444_444, 555_555];
    let chals_j = vec![666_666, 777_777, 888_888, 999_999];
    let chals_k = vec![121_212, 343_434, 565_656];

    let fast = prove_mxfp4_delayed_bjk_horner(
        &x_ri, &q_nibbles, &s_scale, log_j, log_k, &r_j, &chals_b, &chals_j, &chals_k,
    );
    let naive = prove_mxfp4_naive_bjk(
        &x_ri, &q_nibbles, &s_scale, log_j, log_k, &r_j, &chals_b, &chals_j, &chals_k,
    );
    assert_eq!(fast, naive, "delayed 0-mul Horner prover is bit-identical to naive");

    // Verify against independent MLE openings:
    let q_decoded_kbj: Vec<u64> = {
        // Build [b, k, j] or evaluate via build_eq_table_lsb_bb directly:
        q_nibbles.iter().map(|&n| decode_e2m1_x2_bb(n)).collect()
    };
    let open_oracle = |cb: &[u64; 5], cj: &[u64], ck: &[u64]| -> (u64, u64, u64) {
        let eq_b = build_eq_table_lsb_bb(cb);
        let eq_j = build_eq_table_lsb_bb(cj);
        let eq_k = build_eq_table_lsb_bb(ck);
        let mut ox = 0u64;
        for k in 0..k_len {
            for b in 0..32 {
                ox = badd(ox, bmul(x_ri[k * 32 + b], bmul(eq_k[k], eq_b[b])));
            }
        }
        let mut oq = 0u64;
        let mut os = 0u64;
        for j in 0..j_len {
            for k in 0..k_len {
                let w_jk = bmul(eq_j[j], eq_k[k]);
                os = badd(os, bmul(s_scale[j * k_len + k], w_jk));
                let mut qb = 0u64;
                for b in 0..32 {
                    qb = badd(qb, bmul(q_decoded_kbj[(j * k_len + k) * 32 + b], eq_b[b]));
                }
                oq = badd(oq, bmul(w_jk, qb));
            }
        }
        (ox, oq, os)
    };
    assert!(verify_mxfp4_bjk_mode2(fast.claim, &fast, open_oracle));

    // Mutating any round message rejects:
    let mut bad = fast.clone();
    bad.b_rounds[2][0] = badd(bad.b_rounds[2][0], 1);
    assert!(!verify_mxfp4_bjk_mode2(bad.claim, &bad, open_oracle));

    // Benchmark MXFP4 delayed block-bind + 7-bucket Horner vs naive on (J = 512, K = 128, B = 32 = 2M weights):
    let bj_log_j = 9usize; // J = 512
    let bj_log_k = 7usize; // K = 128
    let bj_j = 1usize << bj_log_j;
    let bj_k = 1usize << bj_log_k;
    let x_big: Vec<u64> = (0..(bj_k * 32)).map(|i| (i as u64 * 17 + 3) % P).collect();
    let q_big: Vec<u8> = (0..(bj_j * bj_k * 32)).map(|i| (i % 16) as u8).collect();
    let s_big: Vec<u64> = (0..(bj_j * bj_k)).map(|i| (i as u64 * 29 + 11) % P).collect();
    let rj_big: Vec<u64> = (0..bj_log_j).map(|i| (i as u64 + 1) * 100_003).collect();
    let cb_big = [101, 202, 303, 404, 505];
    let cj_big: Vec<u64> = (0..bj_log_j).map(|i| (i as u64 + 1) * 70_001).collect();
    let ck_big: Vec<u64> = (0..bj_log_k).map(|i| (i as u64 + 1) * 90_007).collect();

    let t0 = Instant::now();
    let p_naive = black_box(prove_mxfp4_naive_bjk(
        black_box(&x_big),
        black_box(&q_big),
        black_box(&s_big),
        bj_log_j,
        bj_log_k,
        &rj_big,
        &cb_big,
        &cj_big,
        &ck_big,
    ));
    let dt_naive = t0.elapsed();

    let t1 = Instant::now();
    let p_fast = black_box(prove_mxfp4_delayed_bjk_horner(
        black_box(&x_big),
        black_box(&q_big),
        black_box(&s_big),
        bj_log_j,
        bj_log_k,
        &rj_big,
        &cb_big,
        &cj_big,
        &ck_big,
    ));
    let dt_fast = t1.elapsed();
    assert_eq!(p_fast, p_naive);

    println!(
        "[BENCH MXFP4 J=512 K=128 B=32 (2.10M E2M1 weights)] naive_bjk={:.3}ms, delayed_horner_bjk={:.3}ms, speedup={:.2}x",
        dt_naive.as_secs_f64() * 1e3,
        dt_fast.as_secs_f64() * 1e3,
        dt_naive.as_secs_f64() / dt_fast.as_secs_f64()
    );
}

#[test]
fn release_benchmark_gruen_vs_cubic_m14_m18_m20() {
    for &(m, mu_s, kappa, reps) in &[(14usize, 7usize, 7usize, 9usize), (18, 9, 9, 5), (20, 10, 10, 3)] {
        let n = 1usize << m;
        let z_s: Vec<u64> = (0..mu_s)
            .map(|i| ((i as u64 + 1) * 111_111_111) % P)
            .collect();
        let chals: Vec<u64> = (0..m)
            .map(|i| ((i as u64 + 1) * 77_777_777 + 42) % P)
            .collect();

        // Build exact EinSumcheck CubicTables (`E = extendRight(eq(z_s))`, `A`, `B`, `C=0`, `D=1`):
        let eq_s = build_eq_table_lsb_bb(&z_s);
        let ns = 1usize << mu_s;
        let e_tab: Vec<u64> = (0..n).map(|idx| eq_s[idx & (ns - 1)]).collect();
        let a_tab: Vec<u64> = (0..n).map(|idx| (idx as u64 * 1_234_567 + 89) % P).collect();
        let b_tab: Vec<u64> = (0..n).map(|idx| (idx as u64 * 7_654_321 + 13) % P).collect();
        let tabs = CubicTables {
            e: e_tab,
            a: a_tab.clone(),
            b: b_tab.clone(),
            c: vec![0u64; n],
            d: vec![1u64; n],
        };

        let suf_p = build_eq_suffix_tables(&z_s, P);
        let suf_bb = build_eq_suffix_tables_bb(&z_s);
        let suf0_p = &suf_p[mu_s - 1];
        let suf0_bb = &suf_bb[mu_s - 1];

        // Warmup + cross-check round 0 Mode-1 reconstruction agrees with `cubic_round_evals`:
        let cub0 = cubic_round_evals(&tabs, P);
        let gr0_p = gruen_f2_round_evals_p(&a_tab, &b_tab, suf0_p, kappa, P);
        let gr0_bb = gruen_f2_round_evals_bb(&a_tab, &b_tab, suf0_bb, kappa);
        assert_eq!(gr0_p, gr0_bb);
        assert_eq!(bmul(bsub(1, z_s[0]), gr0_bb[0]), cub0[0], "s_0(0) == (1 - z_0)*q_0(0)");

        let mut dts_cubic_r0 = Vec::with_capacity(reps);
        let mut dts_gruen_p_r0 = Vec::with_capacity(reps);
        let mut dts_gruen_bb_r0 = Vec::with_capacity(reps);
        for _ in 0..reps {
            let t0 = Instant::now();
            black_box(cubic_round_evals(black_box(&tabs), black_box(P)));
            dts_cubic_r0.push(t0.elapsed().as_secs_f64());

            let t1 = Instant::now();
            black_box(gruen_f2_round_evals_p(
                black_box(&a_tab),
                black_box(&b_tab),
                black_box(suf0_p),
                kappa,
                black_box(P),
            ));
            dts_gruen_p_r0.push(t1.elapsed().as_secs_f64());

            let t2 = Instant::now();
            black_box(gruen_f2_round_evals_bb(
                black_box(&a_tab),
                black_box(&b_tab),
                black_box(suf0_bb),
                kappa,
            ));
            dts_gruen_bb_r0.push(t2.elapsed().as_secs_f64());
        }
        dts_cubic_r0.sort_by(|a, b| a.partial_cmp(b).unwrap());
        dts_gruen_p_r0.sort_by(|a, b| a.partial_cmp(b).unwrap());
        dts_gruen_bb_r0.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let med_cub = dts_cubic_r0[reps / 2];
        let med_gr_p = dts_gruen_p_r0[reps / 2];
        let med_gr_bb = dts_gruen_bb_r0[reps / 2];

        // Full multi-round protocol timing (`prove_cubic_sumcheck` vs `prove_gruen_einsum_mode2` & `_bb`):
        let t_full_cub = Instant::now();
        let pf_cub = black_box(prove_cubic_sumcheck(black_box(&tabs), black_box(&chals), P));
        let dt_full_cub = t_full_cub.elapsed().as_secs_f64();

        let t_full_gr_p = Instant::now();
        let pf_gr_p = black_box(prove_gruen_einsum_mode2(
            black_box(&a_tab),
            black_box(&b_tab),
            mu_s,
            kappa,
            black_box(&z_s),
            black_box(&chals),
            P,
        ));
        let dt_full_gr_p = t_full_gr_p.elapsed().as_secs_f64();

        let t_full_gr_bb = Instant::now();
        let pf_gr_bb = black_box(prove_gruen_einsum_mode2_bb(
            black_box(&a_tab),
            black_box(&b_tab),
            mu_s,
            kappa,
            black_box(&z_s),
            black_box(&chals),
        ));
        let dt_full_gr_bb = t_full_gr_bb.elapsed().as_secs_f64();

        assert_eq!(pf_cub.claim, pf_gr_bb.claim);
        assert_eq!(pf_gr_p, pf_gr_bb);

        println!(
            "[BENCH m={m} (mu_s={mu_s}, kappa={kappa})] round0: cubic_round_evals={:.3}ms | gruen_p={:.3}ms ({:.2}x) | gruen_bb={:.3}ms ({:.2}x) || full_prove: cubic={:.3}ms | gruen_p={:.3}ms ({:.2}x) | gruen_bb={:.3}ms ({:.2}x)",
            med_cub * 1e3,
            med_gr_p * 1e3,
            med_cub / med_gr_p,
            med_gr_bb * 1e3,
            med_cub / med_gr_bb,
            dt_full_cub * 1e3,
            dt_full_gr_p * 1e3,
            dt_full_cub / dt_full_gr_p,
            dt_full_gr_bb * 1e3,
            dt_full_cub / dt_full_gr_bb,
        );
    }
}
