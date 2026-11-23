//! Conformance, adversarial soundness/splice/streaming-boundary teeth, and `--release`
//! multi-KB throughput benchmarks for `minidregg_prover::policy_transducer` against the
//! Lean-authored vectors in `testdata/policy_transducer_conformance.json`.

use std::time::Instant;

use minidregg_prover::policy_transducer::{
    absent_plain_bytes, all_rules_safe, ambig_mini_json_cfg, compiled_default_redactor,
    compiled_mini_json_parser, content_commit, content_commit_unoptimized_ref,
    default_secret_rules, exec_attr_replay, is_api_key_body_byte, ll1_deterministic, mini_json_cfg,
    no_continuation, occurs_in_bytes, prove_mini_rewrite_and_extract, redact_bytes,
    safe_replacement, verify_rewrite_and_extract_conformance_only, CompiledByteLl1Parser, CompiledRedactor,
    ExactNat, MiniValue, RedactRule, RewriteCertStmt, RewriteCertWitness, TransducerError,
};
use serde::Deserialize;

#[derive(Deserialize)]
struct ConformanceBundle {
    schema: String,
    #[serde(rename = "ll1Checks")]
    ll1_checks: Ll1ChecksJson,
    #[serde(rename = "e2eVectors")]
    e2e_vectors: Vec<E2eVectorJson>,
    #[serde(rename = "redactionVectors")]
    redaction_vectors: Vec<RedactionVectorJson>,
    #[serde(rename = "ambigSpliceVector")]
    ambig_splice_vector: AmbigSpliceJson,
}

#[derive(Deserialize)]
struct Ll1ChecksJson {
    #[serde(rename = "miniJsonCfgRuleCount")]
    mini_json_cfg_rule_count: usize,
    #[serde(rename = "miniJsonCfgDeterministic")]
    mini_json_cfg_deterministic: bool,
    #[serde(rename = "ambigMiniJsonCfgRuleCount")]
    ambig_mini_json_cfg_rule_count: usize,
    #[serde(rename = "ambigMiniJsonCfgDeterministic")]
    ambig_mini_json_cfg_deterministic: bool,
    #[serde(rename = "defaultSecretRulesSafe")]
    default_secret_rules_safe: bool,
}

#[derive(Deserialize)]
struct E2eVectorJson {
    name: String,
    #[serde(rename = "rawHex")]
    raw_hex: String,
    #[serde(rename = "rawLen")]
    raw_len: usize,
    #[serde(rename = "rawContentRootHex")]
    raw_content_root_hex: String,
    #[serde(rename = "cleanHex")]
    clean_hex: String,
    #[serde(rename = "cleanLen")]
    clean_len: usize,
    #[serde(rename = "cleanContentRootHex")]
    clean_content_root_hex: String,
    #[serde(rename = "ruleIndices")]
    rule_indices: Vec<usize>,
    ast: serde_json::Value,
}

#[derive(Deserialize)]
struct RedactionVectorJson {
    name: String,
    #[serde(rename = "rawHex")]
    raw_hex: String,
    #[serde(rename = "rawLen")]
    raw_len: usize,
    #[serde(rename = "rawContentRootHex")]
    raw_content_root_hex: String,
    #[serde(rename = "cleanHex")]
    clean_hex: String,
    #[serde(rename = "cleanLen")]
    clean_len: usize,
    #[serde(rename = "cleanContentRootHex")]
    clean_content_root_hex: String,
}

#[derive(Deserialize)]
struct AmbigSpliceJson {
    #[serde(rename = "payloadHex")]
    payload_hex: String,
    #[serde(rename = "payloadLen")]
    payload_len: usize,
    #[serde(rename = "payloadContentRootHex")]
    payload_content_root_hex: String,
    #[serde(rename = "benignRuleIndices")]
    benign_rule_indices: Vec<usize>,
    #[serde(rename = "benignAst")]
    benign_ast: serde_json::Value,
    #[serde(rename = "destructiveRuleIndices")]
    destructive_rule_indices: Vec<usize>,
    #[serde(rename = "destructiveAst")]
    destructive_ast: serde_json::Value,
    #[serde(rename = "ambigGrammarDeterministic")]
    ambig_grammar_deterministic: bool,
    #[serde(rename = "canonicalMiniJsonAccepts")]
    canonical_mini_json_accepts: bool,
}

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0, "hex string must have even length");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("valid hex byte"))
        .collect()
}

fn unhex32(s: &str) -> [u8; 32] {
    unhex(s).try_into().expect("32-byte digest")
}

fn parse_exact_nat_json(v: &serde_json::Value) -> ExactNat {
    if let Some(u) = v.as_u64() {
        ExactNat::from(u)
    } else {
        ExactNat::from_decimal_str(&v.to_string()).expect("decimal ExactNat")
    }
}

fn parse_mini_value_json(v: &serde_json::Value) -> MiniValue {
    match v["kind"].as_str().expect("kind field") {
        "tool_call" => MiniValue::ToolCall {
            tool: unhex(v["toolHex"].as_str().unwrap()),
            target: unhex(v["targetHex"].as_str().unwrap()),
            amount: parse_exact_nat_json(&v["amount"]),
        },
        "cot_tool_call" => MiniValue::CotToolCall {
            cot: unhex(v["cotHex"].as_str().unwrap()),
            tool: unhex(v["toolHex"].as_str().unwrap()),
            target: unhex(v["targetHex"].as_str().unwrap()),
            amount: parse_exact_nat_json(&v["amount"]),
        },
        "batch" => {
            let items = v["items"]
                .as_array()
                .unwrap()
                .iter()
                .map(parse_mini_value_json)
                .collect();
            MiniValue::Batch(items)
        }
        "bytes" => MiniValue::Bytes(unhex(v["hex"].as_str().unwrap())),
        "nat" => MiniValue::Nat(parse_exact_nat_json(&v["val"])),
        "byte" => MiniValue::Byte(v["val"].as_u64().unwrap() as u8),
        "unit" => MiniValue::Unit,
        other => panic!("unsupported MiniValue kind: {other}"),
    }
}

fn load_conformance() -> ConformanceBundle {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/policy_transducer_conformance.json"
    );
    let raw = std::fs::read_to_string(path).expect("read Lean conformance JSON");
    serde_json::from_str(&raw).expect("parse Lean conformance JSON")
}

#[test]
fn lean_conformance_json_matches_rust_bit_for_bit() {
    let bundle = load_conformance();
    assert_eq!(bundle.schema, "minidregg/policy_transducer_conformance/v1");

    let mini_cfg = mini_json_cfg();
    let ambig_cfg = ambig_mini_json_cfg();
    let rules = default_secret_rules();

    assert_eq!(mini_cfg.rules.len(), bundle.ll1_checks.mini_json_cfg_rule_count);
    assert_eq!(
        ll1_deterministic(&mini_cfg),
        bundle.ll1_checks.mini_json_cfg_deterministic
    );
    assert!(bundle.ll1_checks.mini_json_cfg_deterministic);

    assert_eq!(
        ambig_cfg.rules.len(),
        bundle.ll1_checks.ambig_mini_json_cfg_rule_count
    );
    assert_eq!(
        ll1_deterministic(&ambig_cfg),
        bundle.ll1_checks.ambig_mini_json_cfg_deterministic
    );
    assert!(!bundle.ll1_checks.ambig_mini_json_cfg_deterministic);

    assert_eq!(all_rules_safe(&rules), bundle.ll1_checks.default_secret_rules_safe);
    assert!(bundle.ll1_checks.default_secret_rules_safe);

    let parser = compiled_mini_json_parser();
    let redactor = compiled_default_redactor();

    for vec in &bundle.e2e_vectors {
        let raw_bytes = unhex(&vec.raw_hex);
        let expected_clean = unhex(&vec.clean_hex);
        let expected_raw_root = unhex32(&vec.raw_content_root_hex);
        let expected_clean_root = unhex32(&vec.clean_content_root_hex);
        let expected_ast = parse_mini_value_json(&vec.ast);

        assert_eq!(raw_bytes.len(), vec.raw_len, "{}: raw length", vec.name);
        assert_eq!(expected_clean.len(), vec.clean_len, "{}: clean length", vec.name);

        // Verify both cached-table and unoptimized cSHAKE256 Merkle roots match Lean bit-for-bit:
        assert_eq!(content_commit(&raw_bytes), expected_raw_root, "{}: raw root", vec.name);
        assert_eq!(
            content_commit_unoptimized_ref(&raw_bytes),
            expected_raw_root,
            "{}: unoptimized raw root",
            vec.name
        );

        let got_clean = redactor.redact(&raw_bytes);
        assert_eq!(got_clean, expected_clean, "{}: redacted bytes", vec.name);
        assert_eq!(content_commit(&got_clean), expected_clean_root, "{}: clean root", vec.name);
        assert_eq!(
            content_commit_unoptimized_ref(&got_clean),
            expected_clean_root,
            "{}: unoptimized clean root",
            vec.name
        );

        // Every target secret pattern must be absent from w_clean:
        for r in &rules {
            assert!(
                absent_plain_bytes(&got_clean, &r.pat),
                "{}: pattern {} leaked into w_clean",
                vec.name,
                r.name
            );
        }

        // Exact rule-index replay and compiled LL(1) parser agreement with Lean:
        let replayed_ast = exec_attr_replay(&mini_cfg, &vec.rule_indices, &got_clean)
            .unwrap_or_else(|e| panic!("{}: replay failed: {e}", vec.name));
        assert_eq!(replayed_ast, expected_ast, "{}: replayed AST", vec.name);

        let (parsed_rules, parsed_ast) = parser
            .parse(&got_clean)
            .unwrap_or_else(|e| panic!("{}: LL(1) parse failed: {e}", vec.name));
        assert_eq!(parsed_rules, vec.rule_indices, "{}: exact rule sequence", vec.name);
        assert_eq!(parsed_ast, expected_ast, "{}: parsed AST", vec.name);

        // End-to-end RewriteCert prover & verifier:
        let (stmt, wit) = prove_mini_rewrite_and_extract(redactor, parser, &raw_bytes)
            .expect("honest RewriteCert prove");
        assert_eq!(stmt.raw_root, expected_raw_root);
        assert_eq!(stmt.clean_root, expected_clean_root);
        assert_eq!(stmt.claimed_ast, expected_ast);
        verify_rewrite_and_extract_conformance_only(&mini_cfg, &rules, &stmt, &wit)
            .expect("honest RewriteCert verify");
    }

    for rvec in &bundle.redaction_vectors {
        let raw_bytes = unhex(&rvec.raw_hex);
        let expected_clean = unhex(&rvec.clean_hex);
        assert_eq!(raw_bytes.len(), rvec.raw_len);
        assert_eq!(content_commit(&raw_bytes), unhex32(&rvec.raw_content_root_hex));
        let got_clean = redactor.redact(&raw_bytes);
        assert_eq!(got_clean.len(), rvec.clean_len);
        assert_eq!(got_clean, expected_clean, "{}: clean mismatch", rvec.name);
        assert_eq!(content_commit(&got_clean), unhex32(&rvec.clean_content_root_hex));
        for r in &rules {
            assert!(absent_plain_bytes(&got_clean, &r.pat));
        }
    }
}

#[test]
fn adversarial_ambiguous_grammar_splice_and_forgery_teeth() {
    let bundle = load_conformance();
    let sp = &bundle.ambig_splice_vector;
    let payload = unhex(&sp.payload_hex);
    assert_eq!(payload.len(), sp.payload_len);
    assert_eq!(content_commit(&payload), unhex32(&sp.payload_content_root_hex));

    let ambig_cfg = ambig_mini_json_cfg();
    assert!(!sp.ambig_grammar_deterministic);
    assert!(!ll1_deterministic(&ambig_cfg));

    // Both benign ("read_status") and destructive ("wipe_prod") certificates replay on the EXACT SAME payload!
    let ast_benign = exec_attr_replay(&ambig_cfg, &sp.benign_rule_indices, &payload)
        .expect("benign splice replay succeeds on ambiguous grammar");
    let ast_destructive = exec_attr_replay(&ambig_cfg, &sp.destructive_rule_indices, &payload)
        .expect("destructive splice replay succeeds on ambiguous grammar");
    assert_eq!(ast_benign, parse_mini_value_json(&sp.benign_ast));
    assert_eq!(ast_destructive, parse_mini_value_json(&sp.destructive_ast));
    assert_ne!(ast_benign, ast_destructive, "distinct Mini tool ASTs on identical bytes");

    // CompiledByteLl1Parser and verify_rewrite_and_extract_conformance_only refuse `ambig_cfg` at the gate:
    assert_eq!(
        CompiledByteLl1Parser::compile(ambig_mini_json_cfg(), 6, |nt| nt as usize).err(),
        Some(TransducerError::GrammarNotLl1)
    );
    let ambig_stmt = RewriteCertStmt {
        raw_root: content_commit(&payload),
        raw_length: payload.len(),
        clean_root: content_commit(&payload),
        clean_length: payload.len(),
        claimed_ast: ast_benign,
    };
    let ambig_wit = RewriteCertWitness {
        w_raw: payload.clone(),
        w_clean: payload.clone(),
        rule_indices: sp.benign_rule_indices.clone(),
    };
    assert_eq!(
        verify_rewrite_and_extract_conformance_only(&ambig_cfg, &default_secret_rules(), &ambig_stmt, &ambig_wit),
        Err(TransducerError::GrammarNotLl1)
    );

    // Canonical LL(1) `miniJsonCfg` rejects duplicate `"tool"` keys outright:
    assert!(!sp.canonical_mini_json_accepts);
    assert!(compiled_mini_json_parser().parse(&payload).is_err());

    // Leading-zero non-canonical RFC 8259 integer is rejected:
    let leading_zero = br#"{"tool":"ping","target":"node_a","amount":01}"#;
    assert!(compiled_mini_json_parser().parse(leading_zero).is_err());

    // Boundary-recreation falsifier tooth (`P = "ab"`, `repl = ""` on `"aabb"` -> `"ab"`):
    let unsafe_rule = RedactRule {
        name: "unsafe_del_ab",
        pat: b"ab".to_vec(),
        body_pred: no_continuation,
        repl: Vec::new(),
    };
    assert!(!safe_replacement(&unsafe_rule.pat, &unsafe_rule.repl));
    assert!(!all_rules_safe(std::slice::from_ref(&unsafe_rule)));
    let recreated = redact_bytes(std::slice::from_ref(&unsafe_rule), b"aabb");
    assert_eq!(recreated, b"ab");
    assert!(occurs_in_bytes(&recreated, b"ab"));

    // RewriteCert soundness teeth on Vector 1:
    let mini_cfg = mini_json_cfg();
    let rules = default_secret_rules();
    let v1_raw = unhex(&bundle.e2e_vectors[0].raw_hex);
    let (honest_stmt, honest_wit) = prove_mini_rewrite_and_extract(
        compiled_default_redactor(),
        compiled_mini_json_parser(),
        &v1_raw,
    )
    .unwrap();

    // Tooth A: Passing unredacted raw transcript as `w_clean` (even with self-consistent clean root):
    let unredacted_stmt = RewriteCertStmt {
        clean_root: content_commit(&v1_raw),
        clean_length: v1_raw.len(),
        ..honest_stmt.clone()
    };
    let unredacted_wit = RewriteCertWitness {
        w_clean: v1_raw.clone(),
        ..honest_wit.clone()
    };
    assert_eq!(
        verify_rewrite_and_extract_conformance_only(&mini_cfg, &rules, &unredacted_stmt, &unredacted_wit),
        Err(TransducerError::RedactionMismatch)
    );

    // Tooth B: Forging benign AST `"read_only"` on `"backup_snapshot"` bytes:
    let forged_stmt = RewriteCertStmt {
        claimed_ast: MiniValue::CotToolCall {
            cot: b"Found key [REDACTED_API_KEY] and [REDACTED_BEARER] in [REDACTED_TPL]env}}".to_vec(),
            tool: b"read_only".to_vec(),
            target: b"vault\\prod\"01".to_vec(),
            amount: ExactNat::from(2500),
        },
        ..honest_stmt.clone()
    };
    assert_eq!(
        verify_rewrite_and_extract_conformance_only(&mini_cfg, &rules, &forged_stmt, &honest_wit),
        Err(TransducerError::AstMismatch)
    );

    // Tooth C: 1-bit tamper in `w_raw` caught by `cSHAKE256` root:
    let mut tampered_wit = honest_wit.clone();
    tampered_wit.w_raw[10] ^= 0x01;
    assert_eq!(
        verify_rewrite_and_extract_conformance_only(&mini_cfg, &rules, &honest_stmt, &tampered_wit),
        Err(TransducerError::RawRootMismatch)
    );

    // Tooth D: Dense-column trailing-zero root alias (`"xab"` vs `"xab\0"` have identical cSHAKE256 root!)
    // caught by explicit `raw_length`:
    assert_eq!(content_commit(b"xab"), content_commit(b"xab\0"));
    let mut alias_raw = honest_wit.w_raw.clone();
    // Pad to next non-power-of-two boundary if both share depth_of:
    // Length 3 (`depth_of(3)=2`) vs length 4 (`depth_of(4)=2`)!
    assert_eq!(content_commit(&[b'{', b'"', b't']), content_commit(&[b'{', b'"', b't', 0]));
    alias_raw.push(0);
    let alias_wit = RewriteCertWitness {
        w_raw: alias_raw,
        ..honest_wit
    };
    assert_eq!(
        verify_rewrite_and_extract_conformance_only(&mini_cfg, &rules, &honest_stmt, &alias_wit),
        Err(TransducerError::RawLengthMismatch {
            expected: honest_stmt.raw_length,
            actual: honest_stmt.raw_length + 1,
        })
    );

    // Tooth E (Neon Audit #1): Exact unbounded `Nat` (`2^64 = 18446744073709551616`) —
    // never overflows/panics and deterministically refuses mod-`2^64` wraparound to `0`:
    let big_amt_raw = br#"{"tool":"pay","target":"x","amount":18446744073709551616}"#;
    let (big_stmt, big_wit) = prove_mini_rewrite_and_extract(
        compiled_default_redactor(),
        compiled_mini_json_parser(),
        big_amt_raw,
    )
    .expect("exact >2^64 integer parses cleanly");
    let expected_2p64 = ExactNat::from_decimal_str("18446744073709551616").unwrap();
    assert_eq!(expected_2p64.as_u64(), None);
    assert_eq!(expected_2p64.to_string(), "18446744073709551616");
    assert_eq!(
        big_stmt.claimed_ast,
        MiniValue::ToolCall {
            tool: b"pay".to_vec(),
            target: b"x".to_vec(),
            amount: expected_2p64,
        }
    );
    verify_rewrite_and_extract_conformance_only(&mini_cfg, &rules, &big_stmt, &big_wit).unwrap();
    let wrapped_zero_stmt = RewriteCertStmt {
        claimed_ast: MiniValue::ToolCall {
            tool: b"pay".to_vec(),
            target: b"x".to_vec(),
            amount: ExactNat::ZERO,
        },
        ..big_stmt
    };
    assert_eq!(
        verify_rewrite_and_extract_conformance_only(&mini_cfg, &rules, &wrapped_zero_stmt, &big_wit),
        Err(TransducerError::AstMismatch)
    );

    // Tooth F (Neon Audit #5): Defensive nonterminal table bounds check (`rules[0].rhs[0]` is `WS = 12 >= 5`):
    assert_eq!(
        CompiledByteLl1Parser::compile(mini_json_cfg(), 5, |nt| nt as usize).err(),
        Some(TransducerError::NonterminalOutOfBounds { id: 12, count: 5 })
    );
}

#[test]
fn adversarial_streaming_chunk_boundary_splits_and_overlaps() {
    let redactor = compiled_default_redactor();
    let rules = default_secret_rules();

    let adversarial_corpus = concat!(
        "Start CoT: checking overlapping sk-sk-sk-proj-998877_AaBbCc-DdEe! ",
        "Near-miss prefixes: sk, skx, Bea, BearerX, -----END RSA PRIVATE KEY-----, {single_brace}. ",
        "Actual PEM: -----BEGIN OPENSSH PRIVATE KEY-----body_after_lower! ",
        "Actual Bearer: Bearer eyJhbGciOiJFZERTQSJ9.eyJzdWIiOiJhZ2VudCJ9.sig_1+2/3== end. ",
        "Nested templates: {{{{inject_me}}}} and {{{triple}} and ghp_0123456789abcdefABCDEF_ghp_nested! ",
        "Trailing partial secret at very end of stream: sk-live-final_token_at_eof"
    )
    .as_bytes();

    let expected_batch = redactor.redact(adversarial_corpus);
    for r in &rules {
        assert!(
            absent_plain_bytes(&expected_batch, &r.pat),
            "batch redaction leaked {}",
            r.name
        );
    }
    // Idempotence check:
    assert_eq!(redactor.redact(&expected_batch), expected_batch);

    // 1. Fixed chunk sizes from 1 byte (worst-case every-byte boundary split!) through 128 bytes:
    for chunk_size in [1usize, 2, 3, 4, 5, 7, 11, 13, 19, 31, 64, 128] {
        let mut streamer = redactor.streaming();
        let mut streamed_out = Vec::with_capacity(expected_batch.len());
        for chunk in adversarial_corpus.chunks(chunk_size) {
            streamer.push_chunk(chunk, &mut streamed_out);
        }
        streamer.finish(&mut streamed_out);
        assert_eq!(
            streamed_out, expected_batch,
            "streaming mismatch at chunk_size={chunk_size}"
        );
    }

    // 2. Surgical adversarial splits right inside `sk-...`, `sk-sk-...`, `-----BEGIN `, and `{{`:
    let surgical_chunks: &[&[u8]] = &[
        b"{\"cot\":\"key1=",
        b"s",
        b"k",
        b"-",
        b"s",
        b"k",
        b"-",
        b"proj",
        b"-AbCd_123",
        b"456! pem=",
        b"-----",
        b"BEGIN",
        b" ",
        b"RSA ",
        b"PRIVATE KEY-----",
        b" tpl={",
        b"{",
        b"{x}} bearer=Bea",
        b"rer ",
        b"tok.123",
        b"\",\"tool\":\"exec\",\"target\":\"ok\",\"amount\":7}",
    ];
    let full_surgical: Vec<u8> = surgical_chunks.iter().flat_map(|c| c.iter().copied()).collect();
    let expected_surgical = redactor.redact(&full_surgical);

    let mut streamer = redactor.streaming();
    let mut got_surgical = Vec::new();
    for ch in surgical_chunks {
        streamer.push_chunk(ch, &mut got_surgical);
    }
    streamer.finish(&mut got_surgical);
    assert_eq!(got_surgical, expected_surgical);

    // Verify the streamed & sanitized JSON parses cleanly into a unique MiniValue AST!
    let (_, ast) = compiled_mini_json_parser()
        .parse(&got_surgical)
        .expect("sanitized streamed JSON parses");
    assert_eq!(
        ast,
        MiniValue::CotToolCall {
            cot: b"key1=[REDACTED_API_KEY]! pem=[REDACTED_PEM]tpl=[REDACTED_TPL]{x}} bearer=[REDACTED_BEARER]".to_vec(),
            tool: b"exec".to_vec(),
            target: b"ok".to_vec(),
            amount: ExactNat::from(7),
        }
    );

    // 3. Neon Audit #2 (`tok:secret` split right after non-body `:` byte):
    let custom_tok = CompiledRedactor::new(vec![RedactRule {
        name: "tok",
        pat: b"tok:".to_vec(),
        body_pred: is_api_key_body_byte,
        repl: b"[X]".to_vec(),
    }]);
    assert_eq!(custom_tok.redact(b"tok:secret"), b"[X]");
    let mut tok_stream = custom_tok.streaming();
    let mut tok_out = Vec::new();
    tok_stream.push_chunk(b"tok:", &mut tok_out);
    tok_stream.push_chunk(b"secret", &mut tok_out);
    tok_stream.finish(&mut tok_out);
    assert_eq!(tok_out, b"[X]");

    // 4. Neon Audit #3 (`O(N)` incremental continuation scan on 32 KiB 1-byte-chunked secret):
    let mut long_secret = Vec::with_capacity(32772);
    long_secret.extend_from_slice(b"sk-");
    long_secret.resize(3 + 32768, b'A');
    long_secret.push(b'!');
    let t_long = Instant::now();
    let mut long_stream = redactor.streaming();
    let mut long_out = Vec::new();
    for b in &long_secret {
        long_stream.push_chunk(std::slice::from_ref(b), &mut long_out);
    }
    long_stream.finish(&mut long_out);
    assert_eq!(long_out, b"[REDACTED_API_KEY]!");
    assert!(
        t_long.elapsed().as_millis() < 250,
        "1-byte chunked 32 KiB continuation must remain O(N) fast"
    );
}

fn build_realistic_agent_batch_transcript(target_bytes: usize, include_secrets: bool) -> Vec<u8> {
    let mut out = Vec::with_capacity(target_bytes + 512);
    out.extend_from_slice(b"[\n");
    let mut idx = 0usize;
    while out.len() + 320 < target_bytes {
        if idx > 0 {
            out.extend_from_slice(b",\n");
        }
        let item = if include_secrets {
            format!(
                "  {{\"cot\":\"Step {idx}: inspected env vars; scrubbed sk-proj-LiveKey{idx:04}_AbCdEfGhIjKlMnOpQrStUvWxYz and auth Bearer eyJhbGciOiJIUzI1NiJ9.step{idx}.sig plus tpl {{{{ctx_{idx}}}}} before calling tool\",\"tool\":\"deploy_service\",\"target\":\"cluster\\\\us_east\\\\pod_\\\"{idx}\\\"\",\"amount\":{}}}",
                (idx * 37 + 100)
            )
        } else {
            format!(
                "  {{\"cot\":\"Step {idx}: verified clean deployment manifest checksums and replica health metrics across availability zones without sensitive credentials\",\"tool\":\"deploy_service\",\"target\":\"cluster\\\\us_east\\\\pod_\\\"{idx}\\\"\",\"amount\":{}}}",
                (idx * 37 + 100)
            )
        };
        out.extend_from_slice(item.as_bytes());
        idx += 1;
    }
    out.extend_from_slice(b"\n]\n");
    out
}

#[test]
fn release_benchmark_multi_kb_agent_cot_and_json_tool_calls() {
    let redactor = compiled_default_redactor();
    let parser = compiled_mini_json_parser();
    let mini_cfg = mini_json_cfg();
    let rules = default_secret_rules();

    println!("\n=== Policy Transducer & RewriteCert Benchmarks ( multi-KB CoT + JSON Tool-Call Transcripts ) ===");

    for &(size_kb, dirty) in &[(4usize, true), (16, true), (64, true), (64, false), (256, true)] {
        let raw = build_realistic_agent_batch_transcript(size_kb * 1024, dirty);
        let n_bytes = raw.len();

        // Warmup & correctness verification:
        let clean = redactor.redact(&raw);
        if !dirty {
            assert_eq!(clean, raw, "clean transcript must be 100% unmodified");
        } else {
            assert_ne!(clean, raw);
            for r in &rules {
                assert!(absent_plain_bytes(&clean, &r.pat));
            }
        }
        let mut stream_check = Vec::with_capacity(clean.len());
        let mut st = redactor.streaming();
        for ch in raw.chunks(64) {
            st.push_chunk(ch, &mut stream_check);
        }
        st.finish(&mut stream_check);
        assert_eq!(stream_check, clean);

        let (rule_indices, ast) = parser.parse(&clean).expect("valid batch JSON");
        let ast_fast = parser.parse_ast_only(&clean).expect("fast AST parse");
        assert_eq!(ast, ast_fast);
        let replayed = exec_attr_replay(&mini_cfg, &rule_indices, &clean).expect("replay");
        assert_eq!(replayed, ast);

        // Benchmark iterations scaled by transcript size:
        let iters_fast = if size_kb <= 16 { 500usize } else if size_kb <= 64 { 150 } else { 40 };
        let iters_e2e = if size_kb <= 16 { 40usize } else if size_kb <= 64 { 12 } else { 4 };

        // 1. Batch redaction throughput:
        let t0 = Instant::now();
        let mut sink = 0usize;
        for _ in 0..iters_fast {
            let c = redactor.redact(&raw);
            sink ^= c.len();
        }
        let dt_redact = t0.elapsed().as_secs_f64();
        let mbs_redact = (n_bytes as f64 * iters_fast as f64) / dt_redact / 1e6;

        // 2. Streaming (64-byte token chunks) redaction throughput:
        let t1 = Instant::now();
        let mut out_buf = Vec::with_capacity(clean.len() + 64);
        for _ in 0..iters_fast {
            out_buf.clear();
            let mut s = redactor.streaming();
            for ch in raw.chunks(64) {
                s.push_chunk(ch, &mut out_buf);
            }
            s.finish(&mut out_buf);
            sink ^= out_buf.len();
        }
        let dt_stream = t1.elapsed().as_secs_f64();
        let mbs_stream = (n_bytes as f64 * iters_fast as f64) / dt_stream / 1e6;

        // 3. Compiled LL(1) AST extraction throughput (`parse_ast_only` & cert-producing `parse`):
        let t2 = Instant::now();
        for _ in 0..iters_fast {
            let a = parser.parse_ast_only(&clean).unwrap();
            if let MiniValue::Batch(items) = a {
                sink ^= items.len();
            }
        }
        let dt_parse_ast = t2.elapsed().as_secs_f64();
        let mbs_parse_ast = (clean.len() as f64 * iters_fast as f64) / dt_parse_ast / 1e6;

        let t3 = Instant::now();
        for _ in 0..iters_fast {
            let (rs, _) = parser.parse(&clean).unwrap();
            sink ^= rs.len();
        }
        let dt_parse_cert = t3.elapsed().as_secs_f64();
        let mbs_parse_cert = (clean.len() as f64 * iters_fast as f64) / dt_parse_cert / 1e6;

        // 4. Pushdown Replay Verifier throughput (`exec_attr_replay`):
        let t4 = Instant::now();
        for _ in 0..iters_fast {
            let a = exec_attr_replay(&mini_cfg, &rule_indices, &clean).unwrap();
            if let MiniValue::Batch(items) = a {
                sink ^= items.len();
            }
        }
        let dt_replay = t4.elapsed().as_secs_f64();
        let mbs_replay = (clean.len() as f64 * iters_fast as f64) / dt_replay / 1e6;

        // 5. Full E2E `RewriteCert` (2x cSHAKE256 Merkle roots + redact + LL(1) parse + verify):
        let t5 = Instant::now();
        for _ in 0..iters_e2e {
            let (stmt, wit) = prove_mini_rewrite_and_extract(redactor, parser, &raw).unwrap();
            verify_rewrite_and_extract_conformance_only(&mini_cfg, &rules, &stmt, &wit).unwrap();
            sink ^= stmt.clean_length;
        }
        let dt_e2e = t5.elapsed().as_secs_f64();
        let ms_e2e_per_call = (dt_e2e * 1e3) / (iters_e2e as f64);
        let mbs_e2e = (n_bytes as f64 * iters_e2e as f64) / dt_e2e / 1e6;

        std::hint::black_box(sink);
        let tag = if dirty { "dirty" } else { "clean" };
        println!(
            "  [{size_kb:3} KiB {tag:5} | raw={n_bytes:6} B, clean={:6} B, rules={:6}] \
             redact={mbs_redact:7.1} MB/s | stream64={mbs_stream:7.1} MB/s | \
             ll1_ast={mbs_parse_ast:6.1} MB/s (cert={mbs_parse_cert:6.1} MB/s) | \
             replay={mbs_replay:6.1} MB/s | e2e_cshake_cert={ms_e2e_per_call:6.2} ms ({mbs_e2e:5.2} MB/s)",
            clean.len(),
            rule_indices.len()
        );
    }
}
