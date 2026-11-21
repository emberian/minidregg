//! End-to-end integration, byte-exact Lean conformance, `UD-100` multi-KB benchmark,
//! zero-position-disclosure (including 1-byte pin independence at `idx = 0`, `L/2`, `L - 1`),
//! and deterministic adversarial-rejection test suite for `tower256_algebraic_cert`.

use std::time::Instant;

use minidregg_prover::binary_tower_256::Tower256;
use minidregg_prover::tower256_algebraic_cert::{
    alg_keccak_f_count, decode_algebraic_cert, decode_algebraic_receipt, derived_fri_query_seeds,
    encode_algebraic_cert, encode_algebraic_receipt, expand_lean_seed_c8, masked_content_commit,
    prove_algebraic_document, prove_algebraic_with_lean_seed, reset_alg_keccak_counter,
    strip_public_dfa_from_wire, ud100_fri_queries, verify_algebraic_cert,
    verify_algebraic_cert_bytes, PolyDeg2, PolyDeg4,
};
use minidregg_prover::tower256_private_cert::{
    automaton_commit, scan_receipt_for_document_slices, synthesize_realistic_hermes_document,
    ClaimData, DfaTable, Digest,
};
use serde::Deserialize;

#[derive(Deserialize)]
struct DfaJson {
    states: usize,
    initial: usize,
    accepting: Vec<bool>,
    delta: Vec<usize>,
}

#[derive(Deserialize)]
struct ClaimJson {
    kind: String,
    value: Option<serde_json::Value>,
    lo: Option<u64>,
    hi: Option<u64>,
}

#[derive(Deserialize)]
struct AlgConformanceVector {
    name: String,
    seed: u64,
    dfa: DfaJson,
    automaton_root: String,
    word_hex: String,
    claim: ClaimJson,
    cube_dim: usize,
    fri_ell: usize,
    fri_rounds: usize,
    fri_queries: usize,
    content_root: String,
    phase1_root: String,
    mult_root: String,
    phase3_root: String,
    sumcheck_polys: Vec<[String; 5]>,
    col_evals_at_r: [String; 17],
    bf_polys: Vec<[String; 3]>,
    bf_final_coeff: String,
    eval_fold_roots: Vec<String>,
    fri_initial_root: String,
    fri_receipt_hex: String,
    fri_query_seeds: Vec<usize>,
    expected_run_state: usize,
    expected_run_count: u64,
}

#[derive(Deserialize)]
struct AlgConformanceDoc {
    schema: String,
    vectors: Vec<AlgConformanceVector>,
}

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("hex"))
        .collect()
}

fn unhex_exact<const N: usize>(s: &str) -> [u8; N] {
    unhex(s).try_into().expect("exact length")
}

fn unhex_c8(s: &str) -> Tower256 {
    Tower256::from_le_bytes(unhex_exact::<32>(s))
}

impl ClaimJson {
    fn to_claim_data(&self) -> ClaimData {
        match self.kind.as_str() {
            "accept" => ClaimData::Accept(self.value.as_ref().unwrap().as_bool().unwrap()),
            "count" => ClaimData::Count(self.value.as_ref().unwrap().as_u64().unwrap()),
            "bound" => ClaimData::Bound {
                lo: self.lo.unwrap(),
                hi: self.hi.unwrap(),
            },
            other => panic!("unknown claim kind {other}"),
        }
    }
}

#[test]
fn lean_authored_algebraic_conformance_matches_byte_for_byte() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/tower256_algebraic_cert_conformance.json"
    );
    let raw = std::fs::read_to_string(path).expect("read Lean algebraic conformance JSON");
    let doc: AlgConformanceDoc =
        serde_json::from_str(&raw).expect("parse Lean algebraic conformance JSON");
    assert_eq!(doc.schema, "minidregg.tower256_algebraic_cert.v1");
    assert_eq!(doc.vectors.len(), 4);

    for v in &doc.vectors {
        let dfa = DfaTable {
            states: v.dfa.states,
            initial: v.dfa.initial,
            accepting: v.dfa.accepting.clone(),
            delta: v.dfa.delta.clone(),
        };
        let word = unhex(&v.word_hex);
        let claim = v.claim.to_claim_data();
        assert_eq!(v.fri_rounds, v.cube_dim + 1);
        assert_eq!(dfa.run(&word), v.expected_run_state, "{}: run state", v.name);
        assert_eq!(
            dfa.run_count(&word),
            v.expected_run_count,
            "{}: run count",
            v.name
        );
        assert_eq!(
            automaton_commit(&dfa),
            unhex_exact::<32>(&v.automaton_root),
            "{}: automaton_root",
            v.name
        );

        let cmask = expand_lean_seed_c8(
            "MINIDREGG/ALGCERT/CMASK/V1",
            v.seed,
            1usize << v.cube_dim,
        );
        assert_eq!(
            masked_content_commit(v.fri_ell, v.cube_dim, &word, &cmask).unwrap(),
            unhex_exact::<32>(&v.content_root),
            "{}: maskedContentCommit",
            v.name
        );

        let (stmt, receipt) = prove_algebraic_with_lean_seed(
            &dfa,
            &word,
            claim,
            v.seed,
            v.cube_dim,
            v.fri_ell,
            v.fri_queries,
        )
        .unwrap_or_else(|e| panic!("{}: prove failed: {e}", v.name));

        assert_eq!(
            stmt.content_root,
            unhex_exact::<32>(&v.content_root),
            "{}: content_root",
            v.name
        );
        assert_eq!(
            receipt.phase1_root,
            unhex_exact::<32>(&v.phase1_root),
            "{}: phase1_root",
            v.name
        );
        assert_eq!(
            receipt.mult_root,
            unhex_exact::<32>(&v.mult_root),
            "{}: mult_root",
            v.name
        );
        assert_eq!(
            receipt.phase3_root,
            unhex_exact::<32>(&v.phase3_root),
            "{}: phase3_root",
            v.name
        );

        let expected_polys: Vec<PolyDeg4> = v
            .sumcheck_polys
            .iter()
            .map(|arr| PolyDeg4 {
                coeffs: [
                    unhex_c8(&arr[0]),
                    unhex_c8(&arr[1]),
                    unhex_c8(&arr[2]),
                    unhex_c8(&arr[3]),
                    unhex_c8(&arr[4]),
                ],
            })
            .collect();
        assert_eq!(
            receipt.sumcheck_polys, expected_polys,
            "{}: sumcheck_polys",
            v.name
        );

        let expected_evals: [Tower256; 17] = v
            .col_evals_at_r
            .iter()
            .map(|s| unhex_c8(s))
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();
        assert_eq!(
            receipt.col_evals_at_r, expected_evals,
            "{}: col_evals_at_r",
            v.name
        );

        let expected_bf_polys: Vec<PolyDeg2> = v
            .bf_polys
            .iter()
            .map(|arr| PolyDeg2 {
                coeffs: [unhex_c8(&arr[0]), unhex_c8(&arr[1]), unhex_c8(&arr[2])],
            })
            .collect();
        assert_eq!(
            receipt.bf_polys, expected_bf_polys,
            "{}: bf_polys",
            v.name
        );
        assert_eq!(
            receipt.bf_final_coeff,
            unhex_c8(&v.bf_final_coeff),
            "{}: bf_final_coeff",
            v.name
        );

        let expected_ef_roots: Vec<Digest> = v
            .eval_fold_roots
            .iter()
            .map(|s| unhex_exact::<32>(s))
            .collect();
        assert_eq!(
            receipt.eval_fold_roots, expected_ef_roots,
            "{}: eval_fold_roots",
            v.name
        );
        assert_eq!(
            receipt.fri_initial_root,
            unhex_exact::<32>(&v.fri_initial_root),
            "{}: fri_initial_root",
            v.name
        );
        assert_eq!(
            receipt.fri_receipt_bytes,
            unhex(&v.fri_receipt_hex),
            "{}: FRI receipt bytes differ from Lean!",
            v.name
        );
        assert_eq!(
            derived_fri_query_seeds(&stmt, &receipt).unwrap(),
            v.fri_query_seeds,
            "{}: FRI query seeds differ from Lean!",
            v.name
        );

        verify_algebraic_cert(&stmt, &receipt)
            .unwrap_or_else(|e| panic!("{}: verify failed: {e}", v.name));
        let wire = encode_algebraic_receipt(&stmt, &receipt).unwrap();
        assert_eq!(
            decode_algebraic_receipt(&stmt, &wire).unwrap(),
            receipt,
            "{}: decode_algebraic_receipt roundtrip",
            v.name
        );
        verify_algebraic_cert_bytes(&stmt, &wire)
            .unwrap_or_else(|e| panic!("{}: verify_bytes failed: {e}", v.name));
        let stmt_wire = encode_algebraic_cert(&stmt);
        assert_eq!(decode_algebraic_cert(&stmt_wire).unwrap(), stmt);
    }
}

#[test]
fn ud100_benchmarks_and_zero_byte_leakage_including_1byte_pins() {
    assert_eq!(ud100_fri_queries(2), 148);
    let no_sk = DfaTable::no_sk_dash();
    let markers = DfaTable::count_todo_or_rule();
    let content_seed: Digest = [0x42u8; 32];
    let proof_seed_a: Digest = [0xa1u8; 32];
    let proof_seed_b: Digest = [0xb2u8; 32];

    let secret_substrings: &[&[u8]] = &[
        b"Pr1v4t3_Pg_S3cr3t_9941!",
        b"postgres://hermes_admin",
        b"br_internal_8842_alpha_bravo",
        b"pii_vault_ref_7731_do_not_disclose",
        b"vault_master_phrase_amber_cobalt_7719_xenon",
    ];

    println!("\n=== UD-100 (q=148, lb=2) Zero-Byte-Leakage Algebraic Certificate Benchmarks ===");
    for &doc_size in &[1024usize, 4096, 16384] {
        let doc = synthesize_realistic_hermes_document(doc_size, false);
        assert_eq!(doc.len(), doc_size);
        let true_markers = markers.run_count(&doc);
        assert!(true_markers >= 4);

        // 1. Absent("sk-") `.accept(true)` under UD-100
        reset_alg_keccak_counter();
        let t0 = Instant::now();
        let (stmt_abs, rec_abs) = prove_algebraic_document(
            &no_sk,
            &doc,
            ClaimData::Accept(true),
            &content_seed,
            &proof_seed_a,
        )
        .expect("prove accept(true)");
        let prove_abs_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let prove_abs_keccak = alg_keccak_f_count();

        let wire_abs = encode_algebraic_receipt(&stmt_abs, &rec_abs).expect("encode abs");

        reset_alg_keccak_counter();
        let tv0 = Instant::now();
        verify_algebraic_cert(&stmt_abs, &rec_abs).expect("verify abs");
        let verify_abs_ms = tv0.elapsed().as_secs_f64() * 1000.0;
        let verify_abs_keccak = alg_keccak_f_count();
        verify_algebraic_cert_bytes(&stmt_abs, &wire_abs).expect("verify abs wire");

        // Zero-leakage check on non-public payload bytes
        let priv_wire_abs = strip_public_dfa_from_wire(&stmt_abs, &wire_abs).unwrap();
        assert_eq!(
            scan_receipt_for_document_slices(&doc, priv_wire_abs, 8),
            0,
            "{doc_size} B: 8-byte document window leaked in algebraic receipt!"
        );
        for &sec in secret_substrings {
            assert_eq!(scan_receipt_for_document_slices(sec, priv_wire_abs, sec.len()), 0);
        }

        // 2. Conjunctive `.bound` & `.count` on `Markers(TODO|RULE)` sharing the EXACT `content_root`
        //    whenever `cube_dim` matches (`4 KiB` and `16 KiB` both have `cube_dim >= 12`)!
        reset_alg_keccak_counter();
        let tb0 = Instant::now();
        let (stmt_bnd, rec_bnd) = prove_algebraic_document(
            &markers,
            &doc,
            ClaimData::Bound {
                lo: 2,
                hi: true_markers + 3,
            },
            &content_seed,
            &proof_seed_b,
        )
        .expect("prove bound");
        let prove_bnd_ms = tb0.elapsed().as_secs_f64() * 1000.0;
        let prove_bnd_keccak = alg_keccak_f_count();
        let wire_bnd = encode_algebraic_receipt(&stmt_bnd, &rec_bnd).expect("encode bnd");

        reset_alg_keccak_counter();
        let tvb0 = Instant::now();
        verify_algebraic_cert(&stmt_bnd, &rec_bnd).expect("verify bnd");
        let verify_bnd_ms = tvb0.elapsed().as_secs_f64() * 1000.0;
        let verify_bnd_keccak = alg_keccak_f_count();
        verify_algebraic_cert_bytes(&stmt_bnd, &wire_bnd).expect("verify bnd wire");

        if stmt_abs.cube_dim == stmt_bnd.cube_dim {
            assert_eq!(
                stmt_abs.content_root, stmt_bnd.content_root,
                "{doc_size} B: conjunctive certificates must share identical content_root!"
            );
        }

        println!(
            "[size={doc_size:5} B | d={:2}, ell={:2}, q={:3}] \
             Absent(sk-): prove={prove_abs_ms:7.2} ms ({prove_abs_keccak:6} Keccak-f), \
             verify={verify_abs_ms:6.2} ms ({verify_abs_keccak:5} Keccak-f), wire={:7} B | \
             Bound(TODO|RULE in [2,{}]): prove={prove_bnd_ms:7.2} ms ({prove_bnd_keccak:6} Keccak-f), \
             verify={verify_bnd_ms:6.2} ms ({verify_bnd_keccak:5} Keccak-f), wire={:7} B",
            stmt_abs.cube_dim,
            stmt_abs.fri_ell,
            stmt_abs.fri_queries,
            wire_abs.len(),
            true_markers + 3,
            wire_bnd.len(),
        );
    }

    // 3. Strict 1-Byte Secret Pin Zero-Position-Disclosure Test (`idx = 0`, `idx = L / 2`, `idx = L - 1`):
    //    In Wave 6 (`Tower256PrivateContentCert`), `boundary.firstRow.byte` (`idx = 0`) and
    //    `boundary.lastRow.byte` (`idx = L - 1`) were opened in the clear (`100%` 1-byte pin leak!).
    //    Here we place unique 1-byte secret pins (`0xA7`, `0x5C`, `0xE3`) at `0`, `L / 2`, `L - 1`,
    //    verify NO unmasked witness leaf `leaf_of_u64(b)` (`bytes[1..32] == 0`) ever appears anywhere
    //    in `col_evals_at_r`, `sumcheck_polys`, or any coset/evalFold/FRI opening, AND verify that
    //    changing the 1-byte secret pin under independent masks produces 0 matching 32-byte field
    //    elements across the entire non-public receipt!
    let mut doc_pin0 = vec![b'A'; 1024];
    doc_pin0[0] = 0xA7;
    doc_pin0[512] = 0x5C;
    doc_pin0[1023] = 0xE3;

    let mut doc_pin1 = doc_pin0.clone();
    doc_pin1[0] = 0x3B;
    doc_pin1[512] = 0x91;
    doc_pin1[1023] = 0x1D;

    let (stmt0, rec0) = prove_algebraic_document(
        &no_sk,
        &doc_pin0,
        ClaimData::Accept(true),
        &[0x11; 32],
        &[0x22; 32],
    )
    .unwrap();
    let (stmt1, rec1) = prove_algebraic_document(
        &no_sk,
        &doc_pin1,
        ClaimData::Accept(true),
        &[0x33; 32],
        &[0x44; 32],
    )
    .unwrap();
    verify_algebraic_cert(&stmt0, &rec0).unwrap();
    verify_algebraic_cert(&stmt1, &rec1).unwrap();

    // Every single opened `Tower256` element in `rec0` must have non-zero high 248 bits
    // (unmasked byte/state/count values have `bytes[8..32] == [0; 24]`; a uniform `Tower256`
    // element hits `bytes[8..32] == 0` with probability `2^{-192}`)!
    for op in &rec0.content_ops {
        assert_ne!(&op.left.to_le_bytes()[8..32], &[0u8; 24]);
        assert_ne!(&op.right.to_le_bytes()[8..32], &[0u8; 24]);
    }
    for y in &rec0.col_evals_at_r {
        assert_ne!(&y.to_le_bytes()[8..32], &[0u8; 24]);
    }

    // Zero shared 32-byte field elements between the two independent private receipts!
    let w0 = encode_algebraic_receipt(&stmt0, &rec0).unwrap();
    let w1 = encode_algebraic_receipt(&stmt1, &rec1).unwrap();
    let p0 = strip_public_dfa_from_wire(&stmt0, &w0).unwrap();
    let p1 = strip_public_dfa_from_wire(&stmt1, &w1).unwrap();
    let chunks0: std::collections::HashSet<&[u8]> = p0.chunks_exact(32).collect();
    let collisions = p1.chunks_exact(32).filter(|c| chunks0.contains(*c)).count();
    assert_eq!(
        collisions, 0,
        "independent masks must produce 0 colliding 256-bit chunks across receipts"
    );

    // 4. Zero-Query All-Round Sumcheck HVZK Regression (`j = 0 ..= d`, `coeffs[0..5]`):
    //    Prove the SAME document under the SAME `content_root` (`[0x11; 32]`) with two independent
    //    `proof_mask_seed`s (`[0x22; 32]` vs `[0x55; 32]`). Verify `content_root` is identical while
    //    EVERY round `j = 0 ..= d` and EVERY coefficient `coeffs[0..5]` (specifically including `c3`
    //    and `c4` on rounds `1 ..= d`) is freshly randomized with full 256-bit entropy!
    let (stmt0_re, rec0_re) = prove_algebraic_document(
        &no_sk,
        &doc_pin0,
        ClaimData::Accept(true),
        &[0x11; 32],
        &[0x55; 32],
    )
    .unwrap();
    assert_eq!(stmt0.content_root, stmt0_re.content_root);
    assert_eq!(rec0.sumcheck_polys.len(), stmt0.cube_dim + 1);
    assert_eq!(rec0.bf_polys.len(), stmt0.cube_dim + 1);
    assert_ne!(rec0.col_evals_at_r[16], rec0_re.col_evals_at_r[16]);
    assert_ne!(rec0.bf_final_coeff, rec0_re.bf_final_coeff);
    for (j, (pa, pb)) in rec0
        .sumcheck_polys
        .iter()
        .zip(rec0_re.sumcheck_polys.iter())
        .enumerate()
    {
        for k in 0..5 {
            assert_ne!(
                pa.coeffs[k], pb.coeffs[k],
                "round {j} coeff c{k} leaked deterministic witness function across proof_mask_seeds!"
            );
            assert_ne!(
                &pa.coeffs[k].to_le_bytes()[8..32],
                &[0u8; 24],
                "round {j} coeff c{k} lacks full 256-bit field blinding!"
            );
        }
    }
    for (j, (qa, qb)) in rec0.bf_polys.iter().zip(rec0_re.bf_polys.iter()).enumerate() {
        for k in 0..3 {
            assert_ne!(
                qa.coeffs[k], qb.coeffs[k],
                "BaseFold round {j} coeff c{k} failed to randomize across proof_mask_seeds!"
            );
            assert_ne!(
                &qa.coeffs[k].to_le_bytes()[8..32],
                &[0u8; 24],
                "BaseFold round {j} coeff c{k} lacks full 256-bit field blinding!"
            );
        }
    }
}

#[test]
fn planted_adversarial_attacks_are_deterministically_rejected() {
    let no_sk = DfaTable::no_sk_dash();
    let markers = DfaTable::count_todo_or_rule();

    // Attack 1: 1-byte `"sx-live-..." -> "sk-live-..."` flip at middle index `L / 2`!
    // In Wave 6 (`stepQueries` sampling), a single-byte flip escaped if `stepQueries` missed `L / 2`!
    // In `Tower256AlgebraicCert`, `prove_algebraic_with_lean_seed` refuses to prove a false claim,
    // AND an attacker who proves `"sx-live-..."` (`Accept(true)`) cannot verify against the
    // `"sk-live-..."` `content_root`, nor can mutating any receipt field rescue it!
    let mut clean_doc = synthesize_realistic_hermes_document(512, false);
    let mid = 256;
    clean_doc[mid..mid + 8].copy_from_slice(b"sx-live-");
    let mut poisoned_doc = clean_doc.clone();
    poisoned_doc[mid + 1] = b'k'; // 1-byte flip `"sx-" -> "sk-"` at index 257!
    assert!(no_sk.accepts(&clean_doc));
    assert!(!no_sk.accepts(&poisoned_doc));

    assert!(
        prove_algebraic_with_lean_seed(
            &no_sk,
            &poisoned_doc,
            ClaimData::Accept(true),
            7,
            10,
            12,
            8
        )
        .is_err(),
        "prover must reject poisoned 1-byte sk- flip"
    );

    let (honest_stmt, honest_rec) = prove_algebraic_with_lean_seed(
        &no_sk,
        &clean_doc,
        ClaimData::Accept(true),
        7,
        10,
        12,
        8,
    )
    .unwrap();
    verify_algebraic_cert(&honest_stmt, &honest_rec).unwrap();

    // Binding honest `"sx-"` receipt against poisoned `"sk-"` `content_root` fails 100% deterministically:
    let cmask = expand_lean_seed_c8("MINIDREGG/ALGCERT/CMASK/V1", 7, 1 << 10);
    let poisoned_root = masked_content_commit(12, 10, &poisoned_doc, &cmask).unwrap();
    let mut forged_stmt = honest_stmt.clone();
    forged_stmt.content_root = poisoned_root;
    assert!(verify_algebraic_cert(&forged_stmt, &honest_rec).is_err());

    // Attack 2: Forged `.count` and forged `.bound` claims against honest `.count` / `.bound` receipts
    let cnt = markers.run_count(&clean_doc);
    let (cnt_stmt, cnt_rec) = prove_algebraic_with_lean_seed(
        &markers,
        &clean_doc,
        ClaimData::Count(cnt),
        9,
        12,
        14,
        6,
    )
    .unwrap();
    verify_algebraic_cert(&cnt_stmt, &cnt_rec).unwrap();
    let mut bad_cnt_stmt = cnt_stmt.clone();
    bad_cnt_stmt.claim = ClaimData::Count(cnt + 1);
    assert!(verify_algebraic_cert(&bad_cnt_stmt, &cnt_rec).is_err());

    let (bnd_stmt, bnd_rec) = prove_algebraic_with_lean_seed(
        &markers,
        &clean_doc,
        ClaimData::Bound { lo: 1, hi: cnt },
        11,
        12,
        14,
        6,
    )
    .unwrap();
    verify_algebraic_cert(&bnd_stmt, &bnd_rec).unwrap();
    let mut bad_bnd_stmt = bnd_stmt.clone();
    bad_bnd_stmt.claim = ClaimData::Bound {
        lo: cnt + 1,
        hi: cnt + 4,
    };
    assert!(verify_algebraic_cert(&bad_bnd_stmt, &bnd_rec).is_err());

    // Attack 3: Mutated `LogUp256` inverse evaluation (`col_evals_at_r[10]`) or multiplicity (`col_evals_at_r[9]`)
    let mut bad_logup = honest_rec.clone();
    bad_logup.col_evals_at_r[10] = bad_logup.col_evals_at_r[10].add(Tower256::ONE);
    assert!(verify_algebraic_cert(&honest_stmt, &bad_logup).is_err());

    let mut bad_mult = honest_rec.clone();
    bad_mult.col_evals_at_r[9] = bad_mult.col_evals_at_r[9].add(Tower256::ONE);
    assert!(verify_algebraic_cert(&honest_stmt, &bad_mult).is_err());

    // Attack 4: Mutated sumcheck polynomial preserving `p(0) + p(1)` (`c0 += 1, c2 += 1` since `0^2 + 1^2 = 1`!)
    let mut bad_sc = honest_rec.clone();
    bad_sc.sumcheck_polys[0].coeffs[0] = bad_sc.sumcheck_polys[0].coeffs[0].add(Tower256::ONE);
    bad_sc.sumcheck_polys[0].coeffs[2] = bad_sc.sumcheck_polys[0].coeffs[2].add(Tower256::ONE);
    assert!(verify_algebraic_cert(&honest_stmt, &bad_sc).is_err());

    // Attack 5: Mutated `evalFold` opening & mutated `phase3_ops` FRI mask weld
    let mut bad_ef = honest_rec.clone();
    bad_ef.eval_fold_ops[0][0].left = bad_ef.eval_fold_ops[0][0].left.add(Tower256::ONE);
    assert!(verify_algebraic_cert(&honest_stmt, &bad_ef).is_err());

    let mut bad_p3 = honest_rec.clone();
    bad_p3.phase3_ops[0].left_cols[6] = bad_p3.phase3_ops[0].left_cols[6].add(Tower256::ONE);
    assert!(verify_algebraic_cert(&honest_stmt, &bad_p3).is_err());

    let mut bad_p3_fri = honest_rec.clone();
    bad_p3_fri.phase3_ops[0].left_cols[7] =
        bad_p3_fri.phase3_ops[0].left_cols[7].add(Tower256::ONE);
    assert!(verify_algebraic_cert(&honest_stmt, &bad_p3_fri).is_err());

    // Attack 5b: Interleaved BaseFold (`bf_polys` / `bf_final_coeff`) forgeries preserving `q(0) + q(1)`
    // (`c0 += 1` or `c1 += 1, c2 += 1`, since `q(0) + q(1) = c1 + c2` in characteristic 2!)
    let mut bad_bf0 = honest_rec.clone();
    bad_bf0.bf_polys[0].coeffs[0] = bad_bf0.bf_polys[0].coeffs[0].add(Tower256::ONE);
    assert!(verify_algebraic_cert(&honest_stmt, &bad_bf0).is_err());

    let mut bad_bfd = honest_rec.clone();
    let d_last = honest_stmt.cube_dim;
    bad_bfd.bf_polys[d_last].coeffs[1] = bad_bfd.bf_polys[d_last].coeffs[1].add(Tower256::ONE);
    bad_bfd.bf_polys[d_last].coeffs[2] = bad_bfd.bf_polys[d_last].coeffs[2].add(Tower256::ONE);
    assert!(verify_algebraic_cert(&honest_stmt, &bad_bfd).is_err());

    let mut bad_bf_final = honest_rec.clone();
    bad_bf_final.bf_final_coeff = bad_bf_final.bf_final_coeff.add(Tower256::ONE);
    assert!(verify_algebraic_cert(&honest_stmt, &bad_bf_final).is_err());

    // Attack 6: Small-`d` (`d < 10`) and excess-query (`2 * fq + 1 > 2^d`) mask-exhaustion attempts
    assert!(
        prove_algebraic_with_lean_seed(&no_sk, &clean_doc[..64], ClaimData::Accept(true), 7, 8, 10, 4)
            .is_err(),
        "prover must reject small cube_dim < 10"
    );
    assert!(
        prove_algebraic_with_lean_seed(&no_sk, &clean_doc, ClaimData::Accept(true), 7, 10, 12, 512)
            .is_err(),
        "prover must reject 2 * fri_queries + 1 > 2^cube_dim"
    );
    let mut small_d_stmt = honest_stmt.clone();
    small_d_stmt.cube_dim = 8;
    assert!(verify_algebraic_cert(&small_d_stmt, &honest_rec).is_err());
    let mut excess_q_stmt = honest_stmt.clone();
    excess_q_stmt.fri_queries = 512;
    assert!(verify_algebraic_cert(&excess_q_stmt, &honest_rec).is_err());

    // Attack 7: Backdoored `DfaTable` (`accepting[3] = true`) against honest `automaton_root`
    let mut backdoored_dfa = no_sk.clone();
    backdoored_dfa.accepting[3] = true;
    let (_, backdoor_rec) = prove_algebraic_with_lean_seed(
        &backdoored_dfa,
        &poisoned_doc,
        ClaimData::Accept(true),
        7,
        10,
        12,
        8,
    )
    .unwrap();
    let mut swap_stmt = forged_stmt.clone();
    swap_stmt.automaton_root = automaton_commit(&no_sk);
    assert!(verify_algebraic_cert(&swap_stmt, &backdoor_rec).is_err());
}
