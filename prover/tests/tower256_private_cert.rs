//! Integration, Lean conformance, zero-leakage audit, and multi-KB soundness test suite for
//! `minidregg_prover::tower256_private_cert` and CLI `prove_private_cert`.

use std::process::Command;
use std::time::Instant;

use minidregg_prover::tower256_private_cert::{
    automaton_commit, build_trace_rows, decode_private_cert, decode_private_receipt, delta_commit,
    derived_step_indices, encode_private_cert, encode_private_receipt, expand_randomness,
    keccak_f_count, pack_salted_leaf, prove_private_document, prove_private_with_randomness,
    reset_keccak_counter, salted_content_commit, scan_receipt_for_document_slices,
    synthesize_realistic_hermes_document, verify_private_cert, verify_private_cert_bytes,
    ClaimData, Digest, DfaTable, RowMask, Salt248,
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
struct ConformanceVector {
    name: String,
    dfa: DfaJson,
    automaton_root: String,
    delta_root: String,
    word_hex: String,
    salts_hex: Vec<String>,
    row_masks_hex: Vec<String>,
    content_root: String,
    trace_root: String,
    claim: ClaimJson,
    fri_ell: usize,
    fri_rounds: usize,
    fri_queries: usize,
    step_queries: usize,
    fri_initial_root: String,
    fri_receipt_hex: String,
    step_indices: Vec<usize>,
    expected_run_state: usize,
    expected_run_count: u64,
}

#[derive(Deserialize)]
struct ConformanceDoc {
    schema: String,
    vectors: Vec<ConformanceVector>,
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
fn lean_authored_conformance_vectors_match_byte_for_byte() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/tower256_private_cert_conformance.json"
    );
    let raw = std::fs::read_to_string(path).expect("read Lean conformance JSON");
    let doc: ConformanceDoc = serde_json::from_str(&raw).expect("parse Lean conformance JSON");
    assert_eq!(doc.schema, "minidregg.tower256_private_cert.v1");
    assert!(doc.vectors.len() >= 4, "expected at least 4 Lean vectors");

    for v in &doc.vectors {
        let dfa = DfaTable {
            states: v.dfa.states,
            initial: v.dfa.initial,
            accepting: v.dfa.accepting.clone(),
            delta: v.dfa.delta.clone(),
        };
        let word = unhex(&v.word_hex);
        let salts: Vec<Salt248> = v.salts_hex.iter().map(|h| unhex_exact::<31>(h)).collect();
        let masks: Vec<RowMask> = v
            .row_masks_hex
            .iter()
            .map(|h| unhex_exact::<23>(h))
            .collect();
        let claim = v.claim.to_claim_data();

        assert_eq!(dfa.run(&word), v.expected_run_state, "{}: run state", v.name);
        assert_eq!(
            dfa.run_count(&word),
            v.expected_run_count,
            "{}: run count",
            v.name
        );
        assert_eq!(
            delta_commit(&dfa),
            unhex_exact::<32>(&v.delta_root),
            "{}: delta_root",
            v.name
        );
        assert_eq!(
            automaton_commit(&dfa),
            unhex_exact::<32>(&v.automaton_root),
            "{}: automaton_root",
            v.name
        );
        assert_eq!(
            salted_content_commit(&word, &salts).unwrap(),
            unhex_exact::<32>(&v.content_root),
            "{}: saltedContentCommit",
            v.name
        );

        let (stmt, receipt) = prove_private_with_randomness(
            &dfa,
            &word,
            &salts,
            &masks,
            claim,
            v.fri_ell,
            v.fri_rounds,
            v.fri_queries,
            v.step_queries,
        )
        .unwrap_or_else(|e| panic!("{}: prove failed: {e}", v.name));

        assert_eq!(
            stmt.content_root,
            unhex_exact::<32>(&v.content_root),
            "{}: stmt.content_root",
            v.name
        );
        assert_eq!(
            receipt.trace_root,
            unhex_exact::<32>(&v.trace_root),
            "{}: receipt.trace_root",
            v.name
        );
        assert_eq!(
            receipt.fri_initial_root,
            unhex_exact::<32>(&v.fri_initial_root),
            "{}: receipt.fri_initial_root",
            v.name
        );
        assert_eq!(
            receipt.fri_receipt_bytes,
            unhex(&v.fri_receipt_hex),
            "{}: FRI receipt bytes differ from Lean!",
            v.name
        );
        assert_eq!(
            derived_step_indices(&stmt, &receipt).unwrap(),
            v.step_indices,
            "{}: Fiat-Shamir derived step indices differ from Lean!",
            v.name
        );

        verify_private_cert(&stmt, &receipt)
            .unwrap_or_else(|e| panic!("{}: verify failed: {e}", v.name));
        let wire = encode_private_receipt(&receipt);
        verify_private_cert_bytes(&stmt, &wire)
            .unwrap_or_else(|e| panic!("{}: verify_bytes failed: {e}", v.name));
    }
}

#[test]
fn multi_kb_case_a_zero_leakage_audit_and_planted_attacks() {
    let no_sk = DfaTable::no_sk_dash();
    let count_markers = DfaTable::count_todo_or_rule();
    let seed_a: Digest = [0x77u8; 32];
    let seed_b: Digest = [0x77u8; 32]; // Same salt seed so both certificates share the EXACT same content_root!

    // Explicit sensitive substrings present inside `synthesize_realistic_hermes_document`
    let secret_substrings: &[&[u8]] = &[
        b"Pr1v4t3_Pg_S3cr3t_9941!",
        b"postgres://hermes_admin",
        b"br_internal_8842_alpha_bravo",
        b"pii_vault_ref_7731_do_not_disclose",
        b"vault_master_phrase_amber_cobalt_7719_xenon",
        b"https://api.internal.corp/v2/audit",
    ];

    println!("\n=== Multi-KB Private Content Certificate Benchmarks & Zero-Leakage Audit ===");
    for &doc_size in &[1024usize, 4096, 16384] {
        let doc = synthesize_realistic_hermes_document(doc_size, false);
        assert_eq!(doc.len(), doc_size);
        for &secret in secret_substrings {
            assert!(
                doc.windows(secret.len()).any(|w| w == secret),
                "test setup: secret {:?} must be inside the private {} B document",
                std::str::from_utf8(secret).unwrap(),
                doc_size
            );
        }

        let true_marker_count = count_markers.run_count(&doc);
        assert!(
            (1..=250).contains(&true_marker_count),
            "realistic marker count in range: got {true_marker_count}"
        );

        // 1. Prove Case A1: `.accept true` (`Absent("sk-")`) on the private document
        reset_keccak_counter();
        let t0 = Instant::now();
        let (stmt_abs, rec_abs) =
            prove_private_document(&no_sk, &doc, ClaimData::Accept(true), &seed_a, 6, 8)
                .expect("prove Absent(sk-)");
        let rec_abs_bytes = encode_private_receipt(&rec_abs);
        let prove_abs_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let prove_abs_keccak = keccak_f_count();

        reset_keccak_counter();
        let t1 = Instant::now();
        verify_private_cert_bytes(&stmt_abs, &rec_abs_bytes).expect("verify Absent(sk-)");
        let verify_abs_ms = t1.elapsed().as_secs_f64() * 1000.0;
        let verify_abs_keccak = keccak_f_count();

        // 2. Prove Case A2: `.bound 1 50` (for 1KiB/4KiB; or `[1, 200]` for 16KiB, plus exact `.bound 1 50` on 4KiB!)
        let hi_bound = if doc_size <= 4096 { 50 } else { 200 };
        assert!(
            true_marker_count >= 1 && true_marker_count <= hi_bound,
            "marker count {true_marker_count} within 1..={hi_bound}"
        );
        reset_keccak_counter();
        let t2 = Instant::now();
        let (stmt_bnd, rec_bnd) = prove_private_document(
            &count_markers,
            &doc,
            ClaimData::Bound {
                lo: 1,
                hi: hi_bound,
            },
            &seed_b,
            6,
            8,
        )
        .expect("prove Bound(TODO|RULE)");
        let rec_bnd_bytes = encode_private_receipt(&rec_bnd);
        let prove_bnd_ms = t2.elapsed().as_secs_f64() * 1000.0;
        let prove_bnd_keccak = keccak_f_count();

        verify_private_cert_bytes(&stmt_bnd, &rec_bnd_bytes).expect("verify Bound(TODO|RULE)");

        // Both certificates weld to the EXACT SAME `saltedContentCommit` root (`L1` / `cert_and`!)
        assert_eq!(
            stmt_abs.content_root, stmt_bnd.content_root,
            "conjunction over one saltedContentCommit root"
        );

        // Also prove `.count true_marker_count` works end-to-end
        let (stmt_cnt, rec_cnt) = prove_private_document(
            &count_markers,
            &doc,
            ClaimData::Count(true_marker_count),
            &seed_b,
            6,
            8,
        )
        .expect("prove exact Count");
        let rec_cnt_bytes = encode_private_receipt(&rec_cnt);
        verify_private_cert_bytes(&stmt_cnt, &rec_cnt_bytes).expect("verify exact Count");

        // 3. ZERO-LEAKAGE AUDIT SCAN across ALL three receipts!
        for (tag, buf) in [
            ("absent", &rec_abs_bytes),
            ("bound", &rec_bnd_bytes),
            ("count", &rec_cnt_bytes),
        ] {
            for &secret in secret_substrings {
                assert!(
                    !buf.windows(secret.len()).any(|w| w == secret),
                    "ZERO-LEAKAGE VIOLATION ({tag}, {doc_size}B): secret {:?} appeared in receipt!",
                    std::str::from_utf8(secret).unwrap()
                );
            }
            // Exhaustively scan EVERY 6-byte slice of the entire private document against the entire receipt!
            let leaked_slices = scan_receipt_for_document_slices(&doc, buf, 6);
            assert_eq!(
                leaked_slices, 0,
                "ZERO-LEAKAGE VIOLATION ({tag}, {doc_size}B): {leaked_slices} >=6-byte plaintext slices leaked!"
            );
        }

        println!(
            "[doc={:5} B] Absent: prove={:6.2}ms ({} Keccak-f) verify={:5.2}ms ({} Keccak-f) receipt={} B | Bound(1..={}): prove={:6.2}ms ({} Keccak-f) receipt={} B | >=6B leaks=0",
            doc_size,
            prove_abs_ms,
            prove_abs_keccak,
            verify_abs_ms,
            verify_abs_keccak,
            rec_abs_bytes.len(),
            hi_bound,
            prove_bnd_ms,
            prove_bnd_keccak,
            rec_bnd_bytes.len(),
        );

        // 4. ADVERSARIAL SOUNDNESS ATTACKS (every single forgery must be deterministically rejected!)
        // Attack A: 1-byte secret injection turning `"sx-live-..."` into `"sk-live-..."`!
        let mut nearly_dirty = doc.clone();
        let inj_pos = doc_size / 2;
        nearly_dirty[inj_pos..inj_pos + 12].copy_from_slice(b"sx-live-9999");
        let (_, rec_nearly) =
            prove_private_document(&no_sk, &nearly_dirty, ClaimData::Accept(true), &seed_a, 6, 8)
                .expect("sx-live is clean");
        let rec_nearly_bytes = encode_private_receipt(&rec_nearly);

        // Flip ONLY 1 BYTE (`'x'` -> `'k'`) to inject `"sk-live-9999"`!
        let mut dirty_1byte = nearly_dirty.clone();
        dirty_1byte[inj_pos + 1] = b'k';
        assert!(!no_sk.accepts(&dirty_1byte));

        // A1: Prover refuses to issue `.accept true` on the 1-byte-injected document
        assert!(
            prove_private_document(&no_sk, &dirty_1byte, ClaimData::Accept(true), &seed_a, 6, 8)
                .is_err(),
            "prover must refuse .accept true on 1-byte sk-live injection"
        );
        // A2: Replaying `rec_nearly` against the 1-byte-injected document's `contentRoot` fails deterministically
        let (salts_d, _) = expand_randomness(&seed_a, dirty_1byte.len());
        let dirty_root = salted_content_commit(&dirty_1byte, &salts_d).unwrap();
        let mut forged_stmt = stmt_abs.clone();
        forged_stmt.content_root = dirty_root;
        assert!(
            verify_private_cert_bytes(&forged_stmt, &rec_nearly_bytes).is_err(),
            "replaying clean receipt against 1-byte-injected contentRoot must fail"
        );
        // A3: Honest `.accept false` receipt on `dirty_1byte` flipped to claim `.accept true` fails deterministically
        let (mut stmt_dirty_false, rec_dirty_false) =
            prove_private_document(&no_sk, &dirty_1byte, ClaimData::Accept(false), &seed_a, 6, 8)
                .expect(".accept false holds on dirty doc");
        stmt_dirty_false.claim = ClaimData::Accept(true);
        assert!(
            verify_private_cert(&stmt_dirty_false, &rec_dirty_false).is_err(),
            "claiming .accept true on dirty execution trace must fail"
        );

        // Attack B: Forged `.count` and `.bound` claims
        let mut bad_cnt_stmt = stmt_cnt.clone();
        bad_cnt_stmt.claim = ClaimData::Count(true_marker_count + 1);
        assert!(verify_private_cert_bytes(&bad_cnt_stmt, &rec_cnt_bytes).is_err());

        let mut bad_bnd_hi = stmt_bnd.clone();
        bad_bnd_hi.claim = ClaimData::Bound {
            lo: 0,
            hi: true_marker_count - 1,
        };
        assert!(verify_private_cert_bytes(&bad_bnd_hi, &rec_bnd_bytes).is_err());

        let mut bad_bnd_lo = stmt_bnd.clone();
        bad_bnd_lo.claim = ClaimData::Bound {
            lo: true_marker_count + 1,
            hi: true_marker_count + 50,
        };
        assert!(verify_private_cert_bytes(&bad_bnd_lo, &rec_bnd_bytes).is_err());

        // Attack C: Edited DFA table (making dead state 3 escape to 0) against honest `automatonRoot`
        let mut backdoor_dfa = no_sk.clone();
        backdoor_dfa.delta[256 * 3 + usize::from(b'l')] = 0;
        let (mut stmt_bd, rec_bd) = prove_private_document(
            &backdoor_dfa,
            &dirty_1byte,
            ClaimData::Accept(true),
            &seed_a,
            6,
            8,
        )
        .expect("backdoor dfa accepts dirty doc");
        stmt_bd.automaton_root = automaton_commit(&no_sk);
        assert!(
            verify_private_cert(&stmt_bd, &rec_bd).is_err(),
            "backdoored DFA must be rejected against honest automatonRoot"
        );

        // Attack D: Mutating FRI receipt byte or boundary/step opening
        let mut corrupted_fri = rec_abs.clone();
        let mid = corrupted_fri.fri_receipt_bytes.len() / 2;
        corrupted_fri.fri_receipt_bytes[mid] ^= 0x01;
        assert!(verify_private_cert(&stmt_abs, &corrupted_fri).is_err());

        let mut corrupted_step = rec_abs.clone();
        corrupted_step.step_openings[0].row.next ^= 1;
        assert!(verify_private_cert(&stmt_abs, &corrupted_step).is_err());

        // Statement & receipt wire round-trip
        let st_bytes = encode_private_cert(&stmt_abs);
        assert_eq!(decode_private_cert(&st_bytes).unwrap(), stmt_abs);
        assert_eq!(decode_private_receipt(&rec_abs_bytes).unwrap(), rec_abs);
    }

    // Confirm leaf salt hiding property empirically: two distinct bytes with distinct random salts produce
    // 256-bit leaves with no trivial byte leakage after hashing, and `build_trace_rows` tracks exact counts.
    let s0 = [0xaa; 31];
    let s1 = [0x55; 31];
    assert_ne!(pack_salted_leaf(b's', &s0), pack_salted_leaf(b's', &s1));
    assert_eq!(build_trace_rows(&no_sk, b"sk-", &[[0; 23]; 3])[2].next, 3);
}

#[test]
fn cli_prove_verify_and_audit_real_file_end_to_end() {
    let bin = env!("CARGO_BIN_EXE_prove_private_cert");
    let dir = std::env::temp_dir().join(format!("zkcert_cli_test_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let doc_path = dir.join("hermes_private_4k.txt");
    let cert_abs = dir.join("cert_abs.bin");
    let rec_abs = dir.join("rec_abs.bin");
    let cert_bnd = dir.join("cert_bnd.bin");
    let rec_bnd = dir.join("rec_bnd.bin");

    let doc = synthesize_realistic_hermes_document(4096, false);
    std::fs::write(&doc_path, &doc).unwrap();

    // 1. CLI `prove` Absent("sk-")
    let status = Command::new(bin)
        .args([
            "prove",
            "--input",
            doc_path.to_str().unwrap(),
            "--policy",
            "no-sk",
            "--claim",
            "accept-true",
            "--out-cert",
            cert_abs.to_str().unwrap(),
            "--out-receipt",
            rec_abs.to_str().unwrap(),
            "--seed-hex",
            "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        ])
        .status()
        .expect("run prove_private_cert prove");
    assert!(status.success());

    // 2. CLI `verify` & `audit`
    let status = Command::new(bin)
        .args([
            "verify",
            "--cert",
            cert_abs.to_str().unwrap(),
            "--receipt",
            rec_abs.to_str().unwrap(),
        ])
        .status()
        .expect("run prove_private_cert verify");
    assert!(status.success());

    let status = Command::new(bin)
        .args([
            "audit",
            "--input",
            doc_path.to_str().unwrap(),
            "--cert",
            cert_abs.to_str().unwrap(),
            "--receipt",
            rec_abs.to_str().unwrap(),
            "--min-slice",
            "6",
        ])
        .status()
        .expect("run prove_private_cert audit");
    assert!(status.success());

    // 3. CLI `prove` Bound(1, 50) on TODO|RULE markers
    let status = Command::new(bin)
        .args([
            "prove",
            "--input",
            doc_path.to_str().unwrap(),
            "--policy",
            "count-markers",
            "--claim",
            "bound:1:50",
            "--out-cert",
            cert_bnd.to_str().unwrap(),
            "--out-receipt",
            rec_bnd.to_str().unwrap(),
            "--seed-hex",
            "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        ])
        .status()
        .expect("run prove_private_cert bound");
    assert!(status.success());

    let status = Command::new(bin)
        .args([
            "audit",
            "--input",
            doc_path.to_str().unwrap(),
            "--cert",
            cert_bnd.to_str().unwrap(),
            "--receipt",
            rec_bnd.to_str().unwrap(),
            "--min-slice",
            "6",
        ])
        .status()
        .expect("run prove_private_cert bound audit");
    assert!(status.success());

    // 4. Inject `"sk-live-..."` into file -> CLI `prove` with `accept-true` MUST exit nonzero!
    let dirty_path = dir.join("hermes_dirty_4k.txt");
    let dirty_doc = synthesize_realistic_hermes_document(4096, true);
    std::fs::write(&dirty_path, &dirty_doc).unwrap();
    let status_bad = Command::new(bin)
        .args([
            "prove",
            "--input",
            dirty_path.to_str().unwrap(),
            "--policy",
            "no-sk",
            "--claim",
            "accept-true",
            "--out-cert",
            dir.join("bad_cert.bin").to_str().unwrap(),
            "--out-receipt",
            dir.join("bad_rec.bin").to_str().unwrap(),
        ])
        .status()
        .expect("run prove_private_cert on dirty file");
    assert!(!status_bad.success(), "CLI must reject dirty file for accept-true");

    let _ = std::fs::remove_dir_all(&dir);
}
