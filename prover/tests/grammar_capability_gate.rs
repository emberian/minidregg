//! Integration, Lean 4.35.0 JSON conformance, 3-hop capability attenuation, adversarial
//! escalation teeth, and `< 20 ms` 4 KiB zero-leakage sealed `Hyperdocument` patch gate suite.

use std::collections::HashSet;
use std::time::Instant;

use minidregg_prover::grammar_capability::{
    automaton_bound_entails, cap_term_val_fn, check_dfa_sublanguage, check_policy_attenuation,
    decode_public_sealed_patch_bundle, derive_hyperdoc_cell_salts, dfa_accept_all, dfa_complement,
    dfa_count_op_brace, dfa_intersection, dfa_no_shell_sub, dfa_no_sql_drop,
    encode_public_sealed_patch_bundle, fast_salted_content_commit, grammar_policy_attenuates,
    make_cap_policy, policy_chain_attenuates, prove_public_sealed_patch_bundle, root_cap_policy,
    root_cap_policy_with_max_ops, rule_dup_key_first_wins, rule_dup_key_last_wins,
    rule_tool_wipe_prod, seal_hyperdoc_fragment_bytes, service_cap_policy,
    service_cap_policy_with_max_ops, subagent_tool_cap_policy, subagent_tool_cap_policy_with_max_ops,
    unseal_and_verify_hyperdoc_fragment, verify_policy_admits, verify_public_sealed_patch_bundle,
    verify_reachability_cert, verify_sealed_hyperdoc_patch, AttenuationRefusal, AutomatonBound,
    CapNT, CapOp, CapabilityMeta, CompiledLeafVerifier, DelegatedGrammarHop, GateRejection,
    GrammarPolicy, RevocationKey, SealedAtomEdit, SealedHyperdocPatchStmt,
    SealedHyperdocPatchWitness, SemanticsHandle, SublanguageResult, CAP_SEMANTICS_ID,
};
use minidregg_prover::policy_transducer::{ExactNat, MiniValue};
use minidregg_prover::tower256_private_cert::{
    automaton_commit, expand_randomness, salted_content_commit, scan_receipt_for_document_slices,
    DfaTable, Digest, Salt248,
};
use serde::Deserialize;

#[derive(Deserialize)]
struct ExpectedAstJson {
    tool_hex: String,
    target_hex: String,
    amount: u64,
}

#[derive(Deserialize)]
struct GrammarCapConformanceDoc {
    schema: String,
    root_rule_count: usize,
    service_rule_count: usize,
    subagent_rule_count: usize,
    subagent_attenuates_service: bool,
    service_attenuates_root: bool,
    three_hop_chain_valid: bool,
    tooth_widen_range_refused: bool,
    tooth_drop_sk_refused: bool,
    tooth_wipe_prod_refused: bool,
    tooth_dup_key_refused: bool,
    cex_accept_all_vs_no_sk_hex: String,
    cex_no_sql_vs_no_sk_hex: String,
    cex_accept_all_vs_no_shell_hex: String,
    no_sk_automaton_root: String,
    no_sql_automaton_root: String,
    no_shell_automaton_root: String,
    count_brace_automaton_root: String,
    patch_payload_hex: String,
    patch_len: usize,
    salts_hex: Vec<String>,
    salted_patch_root: String,
    subagent_rule_indices: Vec<usize>,
    expected_ast: ExpectedAstJson,
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

fn sample_three_hop_caps(doc_id: u64) -> (CapabilityMeta, CapabilityMeta, CapabilityMeta) {
    let root_cap = CapabilityMeta {
        id: 100,
        root: 100,
        parent: None,
        issuer: 1,
        holder_subject: 10,
        target_object_ids: vec![doc_id, doc_id + 1],
        allow_mutate: true,
        allow_delegate: true,
        max_cost: 8192,
        not_before: 1,
        not_after: 100,
        issuer_epoch: 7,
        policy_id: 42,
        policy_epoch: 3,
        ancestors: vec![],
        channels: vec![9],
    };
    let lead_cap = CapabilityMeta {
        id: 101,
        root: 100,
        parent: Some(100),
        issuer: 1,
        holder_subject: 20,
        target_object_ids: vec![doc_id],
        allow_mutate: true,
        allow_delegate: true,
        max_cost: 6144,
        not_before: 5,
        not_after: 80,
        issuer_epoch: 7,
        policy_id: 42,
        policy_epoch: 3,
        ancestors: vec![100],
        channels: vec![9],
    };
    let coder_cap = CapabilityMeta {
        id: 102,
        root: 100,
        parent: Some(101),
        issuer: 1,
        holder_subject: 30,
        target_object_ids: vec![doc_id],
        allow_mutate: true,
        allow_delegate: false,
        max_cost: 4096,
        not_before: 10,
        not_after: 50,
        issuer_epoch: 7,
        policy_id: 42,
        policy_epoch: 3,
        ancestors: vec![101, 100],
        channels: vec![9],
    };
    (root_cap, lead_cap, coder_cap)
}

#[test]
fn lean_json_conformance_and_four_escalation_teeth() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/grammar_capability_conformance.json"
    );
    let raw = std::fs::read_to_string(path).expect("read Lean grammar_capability_conformance.json");
    let doc: GrammarCapConformanceDoc =
        serde_json::from_str(&raw).expect("parse Lean conformance JSON");
    assert_eq!(doc.schema, "minidregg.grammar_capability_conformance.v1");

    let root_pol = root_cap_policy();
    let svc_pol = service_cap_policy();
    let sub_pol = subagent_tool_cap_policy();

    // 1. Exact rule-count & DFA commitment root agreement with Lean 4.35.0:
    assert_eq!(root_pol.grammar().rules.len(), doc.root_rule_count);
    assert_eq!(svc_pol.grammar().rules.len(), doc.service_rule_count);
    assert_eq!(sub_pol.grammar().rules.len(), doc.subagent_rule_count);

    assert_eq!(
        automaton_commit(&DfaTable::no_sk_dash()),
        unhex_exact::<32>(&doc.no_sk_automaton_root)
    );
    assert_eq!(
        automaton_commit(&dfa_no_sql_drop()),
        unhex_exact::<32>(&doc.no_sql_automaton_root)
    );
    assert_eq!(
        automaton_commit(&dfa_no_shell_sub()),
        unhex_exact::<32>(&doc.no_shell_automaton_root)
    );
    assert_eq!(
        automaton_commit(&dfa_count_op_brace()),
        unhex_exact::<32>(&doc.count_brace_automaton_root)
    );

    // 2. Conformance agreement + sub-millisecond (`< 1 ms`) 3-hop capability chain attenuation benchmark:
    assert_eq!(
        grammar_policy_attenuates(&sub_pol, &svc_pol),
        doc.subagent_attenuates_service
    );
    assert_eq!(
        grammar_policy_attenuates(&svc_pol, &root_pol),
        doc.service_attenuates_root
    );
    assert_eq!(
        policy_chain_attenuates(&[&root_pol, &svc_pol, &sub_pol]),
        doc.three_hop_chain_valid
    );

    let t_att = Instant::now();
    let iters = 50usize;
    for _ in 0..iters {
        assert!(policy_chain_attenuates(&[&root_pol, &svc_pol, &sub_pol]));
    }
    let att_ms = t_att.elapsed().as_secs_f64() * 1000.0 / (iters as f64);
    println!(
        "[bench] 3-hop Root -> TeamLead -> UntrustedCoderAgent attenuation check: {:.3} ms (< 1.0 ms target)",
        att_ms
    );
    assert!(
        att_ms < 1.0,
        "expected < 1 ms attenuation check, got {att_ms:.3} ms"
    );

    // 3. Exact shortest lexicographic counterexample agreement with Lean:
    assert_eq!(
        check_dfa_sublanguage(&dfa_accept_all(), &DfaTable::no_sk_dash()).unwrap(),
        SublanguageResult::Counterexample(unhex(&doc.cex_accept_all_vs_no_sk_hex))
    );
    assert_eq!(
        check_dfa_sublanguage(&dfa_no_sql_drop(), &DfaTable::no_sk_dash()).unwrap(),
        SublanguageResult::Counterexample(unhex(&doc.cex_no_sql_vs_no_sk_hex))
    );
    assert_eq!(
        check_dfa_sublanguage(&dfa_accept_all(), &dfa_no_shell_sub()).unwrap(),
        SublanguageResult::Counterexample(unhex(&doc.cex_accept_all_vs_no_shell_hex))
    );

    // Also test genuine product-DFA intersection: `(no_sk AND no_sql)` is a strict sublanguage of `no_sk`,
    // with an independently verified `ProductReachabilityCert` (and duplicate pairs rejected)!
    let prod_sk_sql =
        dfa_intersection(&DfaTable::no_sk_dash(), &dfa_no_sql_drop(), 1024).expect("product DFA");
    let inc = check_dfa_sublanguage(&prod_sk_sql, &DfaTable::no_sk_dash()).unwrap();
    match inc {
        SublanguageResult::Included(mut cert) => {
            assert!(verify_reachability_cert(
                &cert,
                &prod_sk_sql,
                &DfaTable::no_sk_dash()
            ));
            let dup = cert.reachable_pairs[0];
            cert.reachable_pairs.push(dup);
            assert!(
                !verify_reachability_cert(&cert, &prod_sk_sql, &DfaTable::no_sk_dash()),
                "duplicate pair in reachability cert must be rejected"
            );
        }
        SublanguageResult::Counterexample(w) => panic!("unexpected counterexample {w:?}"),
    }

    // Multi-guard intersection counterexample synthesis: if child has BOTH `no_sql_drop` AND
    // `MustReject(no_shell_sub)` (so child ONLY accepts words containing `"$("` without `"DROP "`),
    // dropping `no_sk_dash` synthesizes the exact 5-byte shortest counterexample `"$(sk-"`!
    let multi_guard_child = make_cap_policy(
        svc_pol.grammar().rules.clone(),
        svc_pol.redact_rules.clone(),
        vec![
            AutomatonBound::MustAccept(dfa_no_sql_drop()),
            AutomatonBound::MustReject(dfa_no_shell_sub()),
            AutomatonBound::RangeHits {
                dfa: dfa_count_op_brace(),
                lo: 1,
                hi: 5,
            },
        ],
    );
    assert_eq!(
        check_policy_attenuation(&multi_guard_child, &svc_pol),
        Err(AttenuationRefusal::UnentailedParentBound {
            parent_bound_index: 0,
            shortest_counterexample: Some(b"$(sk-".to_vec()),
        })
    );
    assert!(dfa_complement(&dfa_no_shell_sub()).accepts(b"$(sk-"));

    // Semantics tampering with a spoofed `SemanticsHandle` claiming `CAP_SEMANTICS_ID` is refused:
    fn spoofed_eval_op(_op: &CapOp, _vs: &[MiniValue]) -> MiniValue {
        MiniValue::Unit
    }
    let spoofed_sem =
        SemanticsHandle::register(CAP_SEMANTICS_ID, cap_term_val_fn, spoofed_eval_op, None);
    let tampered_sem_child = GrammarPolicy::new(
        &spoofed_sem,
        sub_pol.grammar().initial,
        sub_pol.grammar().rules.clone(),
        sub_pol.redact_rules.clone(),
        sub_pol.bounds.clone(),
    );
    assert!(matches!(
        check_policy_attenuation(&tampered_sem_child, &svc_pol),
        Err(AttenuationRefusal::SemanticsMismatch { .. })
    ));

    // 4. Constructive Privilege-Escalation Teeth (i)–(iv) matching Lean:
    // Tooth (i): widening `.rangeHits 1 5` to `.rangeHits 1 6`
    let escalated_range = service_cap_policy_with_max_ops(6);
    assert_eq!(
        !grammar_policy_attenuates(&escalated_range, &svc_pol),
        doc.tooth_widen_range_refused
    );
    assert_eq!(
        check_policy_attenuation(&escalated_range, &svc_pol),
        Err(AttenuationRefusal::UnentailedParentBound {
            parent_bound_index: 2,
            shortest_counterexample: None,
        })
    );

    // Tooth (ii): dropping `Absent("sk-")` guard -> synthesizes shortest counterexample `"sk-"`!
    let dropped_sk = make_cap_policy(
        svc_pol.grammar().rules.clone(),
        svc_pol.redact_rules.clone(),
        vec![
            AutomatonBound::MustAccept(dfa_no_sql_drop()),
            AutomatonBound::RangeHits {
                dfa: dfa_count_op_brace(),
                lo: 1,
                hi: 5,
            },
        ],
    );
    assert_eq!(
        !grammar_policy_attenuates(&dropped_sk, &svc_pol),
        doc.tooth_drop_sk_refused
    );
    assert_eq!(
        check_policy_attenuation(&dropped_sk, &svc_pol),
        Err(AttenuationRefusal::UnentailedParentBound {
            parent_bound_index: 0,
            shortest_counterexample: Some(b"sk-".to_vec()),
        })
    );

    // Tooth (iii): adding unauthorized `"wipe_prod"` production
    let mut wipe_rules = sub_pol.grammar().rules.clone();
    wipe_rules.push(rule_tool_wipe_prod());
    let wipe_pol = make_cap_policy(
        wipe_rules,
        sub_pol.redact_rules.clone(),
        sub_pol.bounds.clone(),
    );
    assert_eq!(
        !grammar_policy_attenuates(&wipe_pol, &svc_pol),
        doc.tooth_wipe_prod_refused
    );
    assert!(matches!(
        check_policy_attenuation(&wipe_pol, &svc_pol),
        Err(AttenuationRefusal::UnauthorizedProductionRule { .. })
    ));

    // Tooth (iv): injecting duplicate-key ambiguity (`ll1_deterministic == false`)
    let mut dup_parent_rules = root_pol.grammar().rules.clone();
    dup_parent_rules.extend([
        rule_tool_wipe_prod(),
        rule_dup_key_first_wins(),
        rule_dup_key_last_wins(),
    ]);
    let dup_parent = make_cap_policy(
        dup_parent_rules,
        root_pol.redact_rules.clone(),
        root_pol.bounds.clone(),
    );
    let mut dup_child_rules = sub_pol.grammar().rules.clone();
    dup_child_rules.extend([
        rule_tool_wipe_prod(),
        rule_dup_key_first_wins(),
        rule_dup_key_last_wins(),
    ]);
    let dup_child = make_cap_policy(
        dup_child_rules,
        sub_pol.redact_rules.clone(),
        sub_pol.bounds.clone(),
    );
    assert_eq!(
        !grammar_policy_attenuates(&dup_child, &dup_parent),
        doc.tooth_dup_key_refused
    );
    assert_eq!(
        check_policy_attenuation(&dup_child, &dup_parent),
        Err(AttenuationRefusal::ChildGrammarNotLl1)
    );

    // 5. Bit-exact `saltedContentCommit`, LL(1) rule-index certificate, & AST agreement with Lean:
    let payload = unhex(&doc.patch_payload_hex);
    assert_eq!(payload.len(), doc.patch_len);
    let salts: Vec<Salt248> = doc.salts_hex.iter().map(|h| unhex_exact::<31>(h)).collect();
    let expected_root = unhex_exact::<32>(&doc.salted_patch_root);
    assert_eq!(salted_content_commit(&payload, &salts).unwrap(), expected_root);

    let leaf_verifier =
        CompiledLeafVerifier::compile(&sub_pol, CapNT::COUNT, CapNT::to_id).unwrap();
    let (parsed_rules, parsed_ast) = leaf_verifier.parser.parse(&payload).unwrap();
    assert_eq!(parsed_rules, doc.subagent_rule_indices);

    let expected_ast = MiniValue::ToolCall {
        tool: unhex(&doc.expected_ast.tool_hex),
        target: unhex(&doc.expected_ast.target_hex),
        amount: ExactNat::from_u64(doc.expected_ast.amount),
    };
    assert_eq!(parsed_ast, expected_ast);
    assert!(verify_policy_admits(
        &sub_pol,
        &payload,
        &parsed_rules,
        &expected_ast
    ));
    // Map rule indices into `root_pol` and verify identical unique AST at root!
    let root_rule_indices: Vec<usize> = parsed_rules
        .iter()
        .map(|&idx| {
            let r = &sub_pol.grammar().rules[idx];
            root_pol
                .grammar()
                .rules
                .iter()
                .position(|pr| pr == r)
                .expect("subagent rule must exist in root")
        })
        .collect();
    assert!(verify_policy_admits(
        &root_pol,
        &payload,
        &root_rule_indices,
        &expected_ast
    ));
}

/// Synthesize a realistic `4,096 B` (`4 KiB`) JSON batch patch admitted by the subagent policy,
/// carrying sensitive internal slug identifiers (`sandbox/hermes-vault-shard-...`) so we can audit
/// zero `>=6B` slice leakage on the public receipt bundle!
fn synthesize_4kib_subagent_batch_patch() -> Vec<u8> {
    let mut buf = Vec::with_capacity(4096);
    buf.push(b'[');
    let mut item_idx = 0usize;
    while buf.len() + 140 < 4096 {
        if item_idx > 0 {
            buf.extend_from_slice(b", ");
        }
        let tool = if item_idx % 2 == 0 {
            "patch_atom"
        } else {
            "read_doc"
        };
        let amt = (item_idx % 5) + 1;
        let item = format!(
            "{{\"tool\":\"{tool}\",\"target\":\"sandbox/private-cell-alpha-{item_idx:03}\",\"amount\":{amt}}}"
        );
        buf.extend_from_slice(item.as_bytes());
        item_idx += 1;
    }
    buf.push(b']');
    assert!(buf.len() <= 4096, "batch exceeded 4096 bytes: {}", buf.len());
    // Pad trailing RFC 8259 whitespace (`' '` / `'\n'`) accepted by `Root -> WS Expr WS` to exact 4,096 B!
    while buf.len() < 4096 {
        buf.push(if buf.len() % 64 == 0 { b'\n' } else { b' ' });
    }
    assert_eq!(buf.len(), 4096);
    buf
}

#[test]
fn four_kib_blinded_hyperdoc_patch_gate_bench_and_zero_leakage_audit() {
    let root_pol = root_cap_policy_with_max_ops(100);
    let svc_pol = service_cap_policy_with_max_ops(64);
    let sub_pol = subagent_tool_cap_policy_with_max_ops(56);

    // 1. Sub-millisecond 3-hop chain check on batch-capable policies:
    let t0 = Instant::now();
    assert!(policy_chain_attenuates(&[&root_pol, &svc_pol, &sub_pol]));
    let chain_ms = t0.elapsed().as_secs_f64() * 1000.0;
    assert!(chain_ms < 1.0, "chain attenuation took {chain_ms:.3} ms");

    // 2. Synthesize 4,096 B (`4 KiB`) blinded subagent patch + salts + sealed Hyperdocument atom:
    let patch_4k = synthesize_4kib_subagent_batch_patch();
    let cell_blinding_key: Digest = [0xA5u8; 32];
    let schema: Digest = [0x3Cu8; 32];
    let doc_id = 500u64;
    let atom_id = 501u64;
    let op_id = 9001u64;

    let salts_4k = derive_hyperdoc_cell_salts(
        &cell_blinding_key,
        doc_id,
        atom_id,
        &schema,
        op_id,
        patch_4k.len(),
    );
    let (_, masks_sk) = expand_randomness(&[0x42u8; 32], patch_4k.len());
    let (_, masks_sql) = expand_randomness(&[0x43u8; 32], patch_4k.len());
    let (_, masks_shell) = expand_randomness(&[0x44u8; 32], patch_4k.len());
    let (_, masks_brace) = expand_randomness(&[0x45u8; 32], patch_4k.len());
    let salted_root = salted_content_commit(&patch_4k, &salts_4k).unwrap();
    assert_eq!(
        fast_salted_content_commit(&patch_4k, &salts_4k).unwrap(),
        salted_root
    );

    let leaf_verifier =
        CompiledLeafVerifier::compile(&sub_pol, CapNT::COUNT, CapNT::to_id).unwrap();
    let (rule_indices, claimed_ast) = leaf_verifier.parser.parse(&patch_4k).unwrap();
    let (ciphertext, wrapping) = seal_hyperdoc_fragment_bytes(
        &cell_blinding_key,
        doc_id,
        atom_id,
        &schema,
        op_id,
        &salted_root,
        &patch_4k,
    );
    // Domain-separation audit: `ciphertext[..32] ^ wrapping[..32]` MUST NOT recover plaintext!
    let xor_probe: Vec<u8> = ciphertext[..32]
        .iter()
        .zip(wrapping.iter())
        .map(|(&c, &w)| c ^ w)
        .collect();
    assert_ne!(
        xor_probe.as_slice(),
        &patch_4k[..32],
        "wrapping must be domain-separated from encryption keystream"
    );

    let (root_cap, lead_cap, coder_cap) = sample_three_hop_caps(doc_id);
    let stmt = SealedHyperdocPatchStmt {
        document_id: doc_id,
        atom_id,
        schema,
        operation_id: op_id,
        author_subject: 30,
        author_capability_id: 102,
        height: 25,
        cost: 4096,
        expected_root_cap_id: 100,
        expected_issuer: 1,
        policy_id: 42,
        expected_policy_epoch: 3,
        expected_issuer_epoch: 7,
        revoked: HashSet::new(),
        patch_len: patch_4k.len(),
        salted_patch_root: salted_root,
        claimed_ast: claimed_ast.clone(),
        root_policy: &root_pol,
        edit: SealedAtomEdit {
            document_id: doc_id,
            atom_id,
            schema,
            author_subject: 30,
            author_capability_id: 102,
            operation_id: op_id,
            wrapped_by_subject: 30,
            wrapped_by_capability_id: 102,
            wrapped_at_operation_id: op_id,
            ciphertext: ciphertext.clone(),
            wrapping: wrapping.clone(),
            cleartext_payload: Vec::new(),
        },
    };
    let wit = SealedHyperdocPatchWitness {
        chain: vec![
            DelegatedGrammarHop {
                capability: root_cap.clone(),
                policy: &root_pol,
            },
            DelegatedGrammarHop {
                capability: lead_cap.clone(),
                policy: &svc_pol,
            },
            DelegatedGrammarHop {
                capability: coder_cap.clone(),
                policy: &sub_pol,
            },
        ],
        patch_bytes: patch_4k.clone(),
        patch_salts: salts_4k.clone(),
        rule_indices: rule_indices.clone(),
        succinct_guards: Vec::new(),
        cell_blinding_key: Some(cell_blinding_key),
    };

    // Verify authenticated decryption + `salted_patch_root` binding on `ciphertext`/`wrapping`:
    let recovered_pt = unseal_and_verify_hyperdoc_fragment(
        &cell_blinding_key,
        doc_id,
        atom_id,
        &schema,
        op_id,
        &salted_root,
        &ciphertext,
        &wrapping,
        None,
    )
    .expect("honest sealed fragment must authenticate, decrypt, and match salted_patch_root");
    assert_eq!(recovered_pt, patch_4k);

    // Warmup + measure `< 20 ms` 4 KiB blinded patch gate verification:
    verify_sealed_hyperdoc_patch(&stmt, &wit).expect("honest 4 KiB sealed patch must verify");
    let t_ver = Instant::now();
    let runs = 5usize;
    for _ in 0..runs {
        verify_sealed_hyperdoc_patch(&stmt, &wit).unwrap();
    }
    let ver_4k_ms = t_ver.elapsed().as_secs_f64() * 1000.0 / (runs as f64);
    println!(
        "[bench] 4 KiB (4,096 B) blinded Hyperdocument patch gate verification: {:.2} ms (< 20.0 ms target)",
        ver_4k_ms
    );
    assert!(
        ver_4k_ms < 20.0,
        "expected < 20 ms 4 KiB blinded patch verification, got {ver_4k_ms:.2} ms"
    );

    // 3. Adversarial Gate Rejection Suite (revocation, stale epoch, cleartext leak, root tamper, secret leak):
    // (a) Revoking intermediate TeamLead (`id = 101`) blocks downstream coder agent:
    let mut rev_stmt_revoked = HashSet::new();
    rev_stmt_revoked.insert(RevocationKey::Capability(101));
    let mut bad_stmt = SealedHyperdocPatchStmt {
        revoked: rev_stmt_revoked,
        claimed_ast: claimed_ast.clone(),
        edit: stmt.edit.clone(),
        ..stmt
    };
    assert_eq!(
        verify_sealed_hyperdoc_patch(&bad_stmt, &wit),
        Err(GateRejection::RevokedOrStaleEpoch { hop_index: 1 })
    );

    // (b) Rotating `expected_policy_epoch` from 3 to 4 rejects immediately:
    bad_stmt.revoked.clear();
    bad_stmt.expected_policy_epoch = 4;
    assert_eq!(
        verify_sealed_hyperdoc_patch(&bad_stmt, &wit),
        Err(GateRejection::RevokedOrStaleEpoch { hop_index: 0 })
    );

    // (c) Non-empty cleartext payload in `SealedAtomEdit` violates `K-NARROW-HIDE`:
    bad_stmt.expected_policy_epoch = 3;
    bad_stmt.edit.cleartext_payload = vec![b'X'];
    assert_eq!(
        verify_sealed_hyperdoc_patch(&bad_stmt, &wit),
        Err(GateRejection::CleartextPayloadNotEmpty)
    );

    // (d) 1-byte tampered `salted_patch_root` rejected:
    bad_stmt.edit.cleartext_payload.clear();
    bad_stmt.salted_patch_root[0] ^= 0x01;
    assert_eq!(
        verify_sealed_hyperdoc_patch(&bad_stmt, &wit),
        Err(GateRejection::SaltedPatchRootMismatch)
    );

    // (e) Non-delegatable leaf capability (`coder_cap.allow_delegate == false`) cannot re-delegate
    // to another subject (`holder_subject = 99`), and unanchored root capability is rejected:
    let illegal_fourth_cap = CapabilityMeta {
        id: 103,
        parent: Some(102),
        holder_subject: 99,
        ancestors: vec![102, 101, 100],
        ..coder_cap.clone()
    };
    let illegal_wit = SealedHyperdocPatchWitness {
        chain: vec![
            DelegatedGrammarHop {
                capability: root_cap.clone(),
                policy: &root_pol,
            },
            DelegatedGrammarHop {
                capability: lead_cap.clone(),
                policy: &svc_pol,
            },
            DelegatedGrammarHop {
                capability: coder_cap.clone(),
                policy: &sub_pol,
            },
            DelegatedGrammarHop {
                capability: illegal_fourth_cap,
                policy: &sub_pol,
            },
        ],
        patch_bytes: patch_4k.clone(),
        patch_salts: salts_4k.clone(),
        rule_indices: rule_indices.clone(),
        succinct_guards: Vec::new(),
        cell_blinding_key: Some(cell_blinding_key),
    };
    let mut fourth_stmt = SealedHyperdocPatchStmt {
        author_subject: 99,
        author_capability_id: 103,
        revoked: HashSet::new(),
        claimed_ast: claimed_ast.clone(),
        edit: SealedAtomEdit {
            author_subject: 99,
            author_capability_id: 103,
            wrapped_by_subject: 99,
            wrapped_by_capability_id: 103,
            ..stmt.edit.clone()
        },
        ..stmt
    };
    assert_eq!(
        verify_sealed_hyperdoc_patch(&fourth_stmt, &illegal_wit),
        Err(GateRejection::CapabilityEdgeNotAttenuated { hop_index: 3 })
    );
    fourth_stmt.expected_root_cap_id = 999;
    assert_eq!(
        verify_sealed_hyperdoc_patch(&fourth_stmt, &wit),
        Err(GateRejection::RootAuthorityAnchorMismatch)
    );

    // (f) Bait-and-switch attack (`#112`): proving `salted_patch_root` on benign `patch_4k` while
    // encrypting evil bytes of equal length into `ciphertext` is rejected by BOTH custodian gate
    // (`CiphertextSealMismatch`) and decryptor (`unseal_and_verify_hyperdoc_fragment`)!
    let mut evil_plain = vec![b'X'; patch_4k.len()];
    evil_plain[..24].copy_from_slice(b"{\"tool\":\"wipe_prod\"}    ");
    let (evil_ct, evil_wrap) = seal_hyperdoc_fragment_bytes(
        &cell_blinding_key,
        doc_id,
        atom_id,
        &schema,
        op_id,
        &salted_root,
        &evil_plain,
    );
    let bait_stmt = SealedHyperdocPatchStmt {
        claimed_ast: claimed_ast.clone(),
        edit: SealedAtomEdit {
            ciphertext: evil_ct.clone(),
            wrapping: evil_wrap.clone(),
            ..stmt.edit.clone()
        },
        ..stmt
    };
    assert_eq!(
        verify_sealed_hyperdoc_patch(&bait_stmt, &wit),
        Err(GateRejection::CiphertextSealMismatch)
    );
    assert!(unseal_and_verify_hyperdoc_fragment(
        &cell_blinding_key,
        doc_id,
        atom_id,
        &schema,
        op_id,
        &salted_root,
        &evil_ct,
        &evil_wrap,
        None,
    )
    .is_err());

    // 4. Public Observer Zero-Leakage Bundle (`Tower256` `PrivateReceipt`s + `cSHAKE256` sealed atom):
    let leaf_guard_bounds = sub_pol.bounds.clone();
    assert!(automaton_bound_entails(
        &leaf_guard_bounds[3],
        &root_pol.bounds[1]
    ));

    let t_pub_prove = Instant::now();
    let pub_bundle = prove_public_sealed_patch_bundle(
        doc_id,
        atom_id,
        schema,
        op_id,
        &cell_blinding_key,
        &patch_4k,
        &salts_4k,
        &[masks_sk, masks_sql, masks_shell, masks_brace],
        &leaf_guard_bounds,
        6,
        8,
    )
    .expect("prove 4 KiB public sealed patch bundle");
    let pub_prove_ms = t_pub_prove.elapsed().as_secs_f64() * 1000.0;

    let wire_bytes = encode_public_sealed_patch_bundle(&pub_bundle);
    let decoded_bundle =
        decode_public_sealed_patch_bundle(&wire_bytes).expect("round-trip decode wire bundle");
    assert_eq!(decoded_bundle, pub_bundle);

    let t_pub_ver = Instant::now();
    verify_public_sealed_patch_bundle(&decoded_bundle, &sub_pol, &root_pol)
        .expect("verify 4 KiB public sealed patch bundle");
    let pub_ver_ms = t_pub_ver.elapsed().as_secs_f64() * 1000.0;

    let leaked_6b = scan_receipt_for_document_slices(&wire_bytes, &patch_4k, 6);
    println!(
        "[bench] 4 KiB public observer bundle: prove={:.2} ms, verify={:.2} ms, wire={} B, leaked >=6B slices={}",
        pub_prove_ms,
        pub_ver_ms,
        wire_bytes.len(),
        leaked_6b
    );
    assert!(
        pub_ver_ms < 20.0,
        "public observer bundle verify exceeded 20 ms: {pub_ver_ms:.2} ms"
    );
    assert_eq!(
        leaked_6b, 0,
        "public sealed Hyperdocument bundle leaked {leaked_6b} >=6B slices of the 4 KiB patch!"
    );
}
