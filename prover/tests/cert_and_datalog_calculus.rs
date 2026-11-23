//! Conformance (Lean-pinned toy), falsifiers, `--release` benchmarks and the
//! ComposedByteTurnCert for `minidregg_prover::datalog_and_cert_calculus`.
//!
//! The toy vector lives in `testdata/cert_datalog_conformance.json`; regenerate it with
//! `CERT_DATALOG_REGEN=1 cargo test --release --test cert_and_datalog_calculus conformance_json`.

#![deny(warnings)]

use std::collections::HashSet;
use std::time::Instant;

use minidregg_prover::datalog_and_cert_calculus::*;
use serde_json::{json, Value};

const JSON_PATH: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/cert_datalog_conformance.json");

// -----------------------------------------------------------------------------------
// Toy helpers
// -----------------------------------------------------------------------------------

fn toy_index_of(a: u32) -> usize {
    TOY_LEAF_KEYS.iter().position(|&k| k == a as u64 + 1).expect("toy EDB atom")
}

fn memb(tree: &EdbTree<ToyHasher>, a: u32, rank: u64) -> ToyClaim {
    let j = toy_index_of(a);
    Claim {
        atom: Atom::prop(a),
        pos: true,
        rank,
        just: Just::Memb { j: j as u64, salt: TOY_LEAF_SALTS[j], path: tree.path(j) },
    }
}

fn rule(a: u32, rank: u64, rule_id: u32) -> ToyClaim {
    Claim { atom: Atom::prop(a), pos: true, rank, just: Just::Rule { rule_id, subst: vec![] } }
}

fn unf(a: u32, rank: u64, u: &[u32]) -> ToyClaim {
    Claim { atom: Atom::prop(a), pos: false, rank, just: Just::Unf { u: u.iter().map(|&x| Atom::prop(x)).collect() } }
}

fn gap(tree: &EdbTree<ToyHasher>, a: u32, rank: u64, i: u64, left: usize, right: usize) -> ToyClaim {
    let leaves = tree.leaves();
    Claim {
        atom: Atom::prop(a),
        pos: false,
        rank,
        just: Just::Gap {
            i,
            left: leaves[left].clone(),
            left_path: tree.path(left),
            right: leaves[right].clone(),
            right_path: tree.path(right),
        },
    }
}

struct HandCert {
    name: &'static str,
    query: u32,
    sign: bool,
    accept: bool,
    claims: Vec<ToyClaim>,
    note: &'static str,
}

fn hand_certs(tree: &EdbTree<ToyHasher>) -> Vec<HandCert> {
    vec![
        HandCert {
            name: "cert_alert_bob",
            query: 41,
            sign: true,
            accept: true,
            claims: vec![
                memb(tree, 8, 2),
                memb(tree, 4, 2),
                memb(tree, 2, 2),
                memb(tree, 3, 2),
                rule(21, 5, 1),
                unf(31, 10, &[31]),
                rule(41, 20, 7),
            ],
            note: "41 :- 8, not 31; 31 refuted by Unf[31] (its only instance 31 :- 21, not 4 is blocked by Pos 4 r2 < 10)",
        },
        HandCert {
            name: "cert_alert_alice_false",
            query: 40,
            sign: false,
            accept: true,
            claims: vec![
                memb(tree, 1, 2),
                rule(20, 5, 0),
                gap(tree, 10, 0, 8, 8, 9),
                rule(30, 15, 3),
                unf(40, 30, &[40]),
            ],
            note: "not 40 by Unf[40]: 40 :- 7, not 30 blocked by Pos 30 r15; not 10 by Gap i=8 (keys 10 < 11 < 63)",
        },
        HandCert {
            name: "cert_p_false",
            query: 50,
            sign: false,
            accept: true,
            claims: vec![unf(50, 1, &[50])],
            note: "50 :- 50 is blocked because 50 is in u",
        },
        HandCert {
            name: "cert_cyclic",
            query: 50,
            sign: true,
            accept: false,
            claims: vec![rule(50, 1, 9)],
            note: "falsifier: self-justification 50 :- 50 needs a Pos 50 claim of rank < 1",
        },
        HandCert {
            name: "cert_nonadjacent_gap",
            query: 2,
            sign: false,
            accept: false,
            claims: vec![gap(tree, 2, 0, 1, 1, 3)],
            note: "falsifier: claimed i=1 but the right opening is leaf 3 (path of index 3 recomputed at index 2 misses the root). A loose (i,j) verifier would accept (keys 2 < 3 < 4, both openings valid) although atom 2 is in the EDB (key 3 at leaf 2).",
        },
        HandCert {
            name: "cert_bottom_gap",
            query: 0,
            sign: false,
            accept: true,
            claims: vec![gap(tree, 0, 0, 0, 0, 1)],
            note: "The bottom sentinel and the first fact bracket key 1.",
        },
        HandCert {
            name: "cert_surplus_sibling",
            query: 8,
            sign: true,
            accept: false,
            claims: {
                let mut c = memb(tree, 8, 0);
                if let Just::Memb { path, .. } = &mut c.just {
                    path.push(0);
                }
                vec![c]
            },
            note: "A depth-four opening has exactly four siblings.",
        },
    ]
}

fn claim_to_json(c: &ToyClaim) -> Value {
    let just = match &c.just {
        Just::Memb { j, salt, path } => json!({"kind": "memb", "j": j, "salt": salt, "path": path}),
        Just::Rule { rule_id, subst } => json!({"kind": "rule", "ruleId": rule_id, "subst": subst}),
        Just::Gap { i, left, left_path, right, right_path } => json!({
            "kind": "gap", "i": i,
            "leftKey": left.key, "leftSalt": left.salt, "leftPath": left_path,
            "rightKey": right.key, "rightSalt": right.salt, "rightPath": right_path,
        }),
        Just::Unf { u } => json!({"kind": "unf", "u": u.iter().map(|a| a.pred).collect::<Vec<_>>()}),
    };
    json!({"atom": c.atom.pred, "pos": c.pos, "rank": c.rank, "just": just})
}

fn u64s(v: &Value) -> Vec<u64> {
    v.as_array().expect("array").iter().map(|x| x.as_u64().expect("u64")).collect()
}

fn claim_from_json(v: &Value) -> ToyClaim {
    let j = &v["just"];
    let n = |k: &str| j[k].as_u64().expect("u64");
    let just = match j["kind"].as_str().expect("kind") {
        "memb" => Just::Memb { j: n("j"), salt: n("salt"), path: u64s(&j["path"]) },
        "rule" => Just::Rule { rule_id: n("ruleId") as u32, subst: u64s(&j["subst"]) },
        "gap" => Just::Gap {
            i: n("i"),
            left: Leaf { key: n("leftKey"), salt: n("leftSalt") },
            left_path: u64s(&j["leftPath"]),
            right: Leaf { key: n("rightKey"), salt: n("rightSalt") },
            right_path: u64s(&j["rightPath"]),
        },
        "unf" => Just::Unf { u: u64s(&j["u"]).into_iter().map(|a| Atom::prop(a as u32)).collect() },
        k => panic!("unknown kind {k}"),
    };
    Claim {
        atom: Atom::prop(v["atom"].as_u64().expect("atom") as u32),
        pos: v["pos"].as_bool().expect("pos"),
        rank: v["rank"].as_u64().expect("rank"),
        just,
    }
}

fn generated_queries() -> impl Iterator<Item = (u32, bool)> {
    let original = [41, 40, 50, 31];
    original.into_iter().chain((0..TOY_NUM_PREDS as u32).filter(move |p| !original.contains(p)))
        .map(|p| (p, TOY_EDB.contains(&p) || TOY_MODEL_TRUE.contains(&p)))
}
const TOY_MODEL_TRUE: [u32; 6] = [20, 21, 22, 30, 32, 41];
const TOY_MODEL_FALSE: [u32; 4] = [31, 40, 42, 50];

fn build_conformance_json() -> Value {
    let tree = toy_tree();
    let program = toy_program();
    let model = solve(&program, &toy_edb()).expect("toy solve");
    let certs: Vec<Value> = hand_certs(&tree)
        .iter()
        .map(|hc| {
            let mut v = json!({
                "name": hc.name, "query": hc.query, "sign": hc.sign,
                "expect": if hc.accept { "accept" } else { "reject" },
                "claims": hc.claims.iter().map(claim_to_json).collect::<Vec<_>>(),
                "note": hc.note,
            });
            if hc.name == "cert_nonadjacent_gap" {
                v["looseVerifierWouldAccept"] = json!(true);
                v["rightIndexActual"] = json!(3);
                v["atomInEdb"] = json!(true);
            }
            v
        })
        .collect();
    let generated: Vec<Value> = generated_queries()
        .map(|(q, s)| {
            let c = generate_cert(&ToyHasher, &program, &model, &tree, &Atom::prop(q), s).expect("toy gen");
            json!({"query": q, "sign": s, "expect": "accept", "claims": c.iter().map(claim_to_json).collect::<Vec<_>>()})
        })
        .collect();
    json!({
        "schema": "minidregg.w11.cert_datalog_conformance.v1",
        "provenance": "Generated by conformance_json_is_reproducible. The overlay checks the literal claims against the Lean verifier and proves the signed model answer for every generated query. maxLevel and rankWidth describe the Rust solver.",
        "toy": {
            "depth": TOY_DEPTH,
            "modulus": TOY_P,
            "leafHash": "(k*1000003 + s*7919 + 17) % 2147483647",
            "nodeHash": "(l*65599 + r*31 + 3) % 2147483647",
            "pathOrder": "top-down: root-level sibling first; rec(d+1,i,leaf,sib::rest) = if i < 2^d then node(rec(d,i,leaf,rest), sib) else node(sib, rec(d,i-2^d,leaf,rest))",
            "bottom": 0,
            "top": TOY_TOP,
            "atomEncoding": "0-ary predicate code a; enc(a) = a + 1",
            "edbRule": "a < 20",
            "strata": [{"lo": 0, "hi": 19, "stratum": 0}, {"lo": 20, "hi": 29, "stratum": 1}, {"lo": 30, "hi": 39, "stratum": 2}, {"lo": 40, "hi": 49, "stratum": 3}, {"lo": 50, "hi": 50, "stratum": 1}],
            "edb": TOY_EDB,
            "leafKeys": TOY_LEAF_KEYS,
            "leafSalts": TOY_LEAF_SALTS,
            "leafHashes": tree.leaf_hashes(),
            "root": tree.root(),
            "expectedRoot": TOY_EXPECTED_ROOT,
            "paths": (0..16).map(|i| json!({"index": i, "siblings": tree.path(i)})).collect::<Vec<_>>(),
            "rules": TOY_RULES.iter().enumerate().map(|(i, (h, p, n))| json!({"id": i, "head": h, "pos": p, "neg": n})).collect::<Vec<_>>(),
            "modelTrue": TOY_MODEL_TRUE,
            "modelFalse": TOY_MODEL_FALSE,
            "maxLevel": model.max_level(),
            "rankWidth": model.max_level() + 3,
            "certs": certs,
            "generatedCerts": generated,
            "stratifierFalsifier": {"rules": [{"head": 60, "pos": [], "neg": [60]}], "expect": "reject"},
        },
    })
}

fn load_json() -> Value {
    let s = std::fs::read_to_string(JSON_PATH).expect("read conformance JSON");
    serde_json::from_str(&s).expect("parse conformance JSON")
}

// -----------------------------------------------------------------------------------
// Toy conformance
// -----------------------------------------------------------------------------------

#[test]
fn conformance_json_is_reproducible() {
    let built = build_conformance_json();
    if std::env::var("CERT_DATALOG_REGEN").is_ok() {
        let mut s = serde_json::to_string_pretty(&built).expect("serialize");
        s.push('\n');
        std::fs::write(JSON_PATH, s).expect("write conformance JSON");
    }
    assert_eq!(load_json(), built, "checked-in conformance JSON is stale");
}

#[test]
fn toy_root_leaf_hashes_and_paths_match_json() {
    let j = load_json();
    let t = &j["toy"];
    let h = ToyHasher;
    let keys = u64s(&t["leafKeys"]);
    let salts = u64s(&t["leafSalts"]);
    assert_eq!(keys, TOY_LEAF_KEYS.to_vec());
    assert_eq!(salts, TOY_LEAF_SALTS.to_vec());
    let hashes: Vec<u64> = keys.iter().zip(&salts).map(|(k, s)| h.leaf(k, s)).collect();
    assert_eq!(hashes, u64s(&t["leafHashes"]));
    let tree = toy_tree();
    assert_eq!(tree.root(), TOY_EXPECTED_ROOT);
    assert_eq!(t["root"].as_u64(), Some(839_753_907));
    let com = tree.commitment();
    for p in t["paths"].as_array().expect("paths") {
        let i = p["index"].as_u64().expect("index");
        let sib = u64s(&p["siblings"]);
        assert_eq!(sib, tree.path(i as usize));
        let leaf = Leaf { key: keys[i as usize], salt: salts[i as usize] };
        assert_eq!(recompute_root(&h, com.depth, i, &leaf, &sib), Some(TOY_EXPECTED_ROOT));
        // too-short path and out-of-range index reject
        assert_eq!(recompute_root(&h, com.depth, i, &leaf, &sib[1..]), None);
        assert_eq!(recompute_root(&h, com.depth, 16, &leaf, &sib), None);
    }
}

#[test]
fn toy_model_matches_json() {
    let j = load_json();
    let program = toy_program();
    let model = solve(&program, &toy_edb()).expect("solve");
    for a in u64s(&j["toy"]["modelTrue"]) {
        assert!(model.holds(&Atom::prop(a as u32)), "{a} should hold");
    }
    for a in u64s(&j["toy"]["modelFalse"]) {
        assert!(!model.holds(&Atom::prop(a as u32)), "{a} should not hold");
    }
    let idb_true: Vec<u32> = (20..TOY_NUM_PREDS as u32).filter(|&a| model.holds(&Atom::prop(a))).collect();
    assert_eq!(idb_true, TOY_MODEL_TRUE.to_vec());
}

#[test]
fn toy_hand_cert_verdicts_match_json() {
    let j = load_json();
    let program = toy_program();
    let com = toy_tree().commitment();
    let certs = j["toy"]["certs"].as_array().expect("certs");
    assert_eq!(certs.len(), 7);
    for c in certs {
        let claims: Vec<ToyClaim> = c["claims"].as_array().expect("claims").iter().map(claim_from_json).collect();
        let q = Atom::prop(c["query"].as_u64().expect("query") as u32);
        let sign = c["sign"].as_bool().expect("sign");
        let r = verify_cert(&ToyHasher, &program, &com, &claims, &q, sign);
        let expect = c["expect"].as_str() == Some("accept");
        assert_eq!(r.is_ok(), expect, "{}: {:?}", c["name"], r);
    }
}

/// A deliberately loose gap verifier taking two independent indices (i, j).
fn loose_gap_accepts(com: &EdbCommitment<u64>, c: &ToyClaim, right_index: u64) -> bool {
    let h = ToyHasher;
    let Just::Gap { i, left, left_path, right, right_path } = &c.just else { return false };
    let key = h.enc(&c.atom).expect("enc");
    recompute_root(&h, com.depth, *i, left, left_path) == Some(com.root)
        && recompute_root(&h, com.depth, right_index, right, right_path) == Some(com.root)
        && left.key < key
        && key < right.key
}

#[test]
fn toy_nonadjacent_gap_rejected_but_loose_verifier_would_accept() {
    let tree = toy_tree();
    let com = tree.commitment();
    let program = toy_program();
    let c = gap(&tree, 2, 0, 1, 1, 3);
    assert!(loose_gap_accepts(&com, &c, 3), "loose (i,j) verifier accepts");
    assert!(solve(&program, &toy_edb()).expect("solve").holds(&Atom::prop(2)), "yet atom 2 is in the EDB");
    let r = verify_cert(&ToyHasher, &program, &com, &[c], &Atom::prop(2), false);
    assert_eq!(r, Err(CertError::Claim { index: 0, kind: CertErrorKind::GapOpening }));
}

#[test]
fn toy_generated_certs_verify_and_match_json() {
    let j = load_json();
    let tree = toy_tree();
    let com = tree.commitment();
    let program = toy_program();
    let model = solve(&program, &toy_edb()).expect("solve");
    assert_eq!(model.max_level(), 1);
    for (k, (q, s)) in generated_queries().enumerate() {
        let c = generate_cert(&ToyHasher, &program, &model, &tree, &Atom::prop(q), s).expect("gen");
        verify_cert(&ToyHasher, &program, &com, &c, &Atom::prop(q), s).expect("generated cert verifies");
        let from_json: Vec<ToyClaim> =
            j["toy"]["generatedCerts"][k]["claims"].as_array().expect("claims").iter().map(claim_from_json).collect();
        assert_eq!(from_json, c);
        let bytes = encode_cert(&c);
        assert_eq!(decode_cert::<u64, u64, u64>(&bytes).as_ref(), Some(&c));
        // wrong sign: not in model
        assert!(generate_cert(&ToyHasher, &program, &model, &tree, &Atom::prop(q), !s).is_err());
        // a cert for q never certifies the opposite sign
        assert_eq!(verify_cert(&ToyHasher, &program, &com, &c, &Atom::prop(q), !s), Err(CertError::QueryNotClaimed));
    }
}

#[test]
fn toy_tamper_falsifiers() {
    let tree = toy_tree();
    let com = tree.commitment();
    let program = toy_program();
    let bob = hand_certs(&tree).remove(0).claims;
    let q = Atom::prop(41);
    let v = |c: &[ToyClaim]| verify_cert(&ToyHasher, &program, &com, c, &q, true);
    assert!(v(&bob).is_ok());
    // drop the Neg 31 claim
    let mut c = bob.clone();
    c.remove(5);
    assert!(matches!(v(&c), Err(CertError::Claim { kind: CertErrorKind::NegBodyUnclaimed(_), .. })));
    // rank not strictly below
    let mut c = bob.clone();
    c[0].rank = 20; // Pos 8 no longer strictly below Pos 41 r20
    assert!(matches!(v(&c), Err(CertError::Claim { index: 6, kind: CertErrorKind::PosBodyUnclaimed(_) })));
    let mut c = bob.clone();
    c[1].rank = 10; // Pos 4 no longer strictly below Unf[31] r10
    assert!(matches!(v(&c), Err(CertError::Claim { index: 5, kind: CertErrorKind::UnfUnblocked { rule: 4, .. } })));
    // corrupt a path sibling / truncate a path / wrong salt / wrong index
    for f in 0..5 {
        let mut c = bob.clone();
        if let Just::Memb { j, salt, path } = &mut c[0].just {
            match f {
                0 => path[2] ^= 1,
                1 => {
                    path.remove(0);
                }
                2 => *salt += 1,
                3 => *j ^= 1,
                _ => path.push(0),
            }
        }
        assert_eq!(v(&c), Err(CertError::Claim { index: 0, kind: CertErrorKind::MembOpening }), "mutation {f}");
    }
    // Gap for an EDB-present atom (4 has key 5 at leaf 4): any adjacent pair fails the order check
    for i in 0..15usize {
        let g = gap(&tree, 4, 0, i as u64, i, i + 1);
        let r = verify_cert(&ToyHasher, &program, &com, &[g], &Atom::prop(4), false);
        assert_eq!(r, Err(CertError::Claim { index: 0, kind: CertErrorKind::GapOrder }));
    }
    // Both sentinel regions have honest adjacent openings. Each path length is exact.
    for (atom, left) in [(0, 0), (19, 8)] {
        let q = Atom::prop(atom);
        let c = gap(&tree, atom, 0, left, left as usize, left as usize + 1);
        verify_cert(&ToyHasher, &program, &com, std::slice::from_ref(&c), &q, false).unwrap();
        for side in [false, true] {
            let mut bad = c.clone();
            if let Just::Gap { left_path, right_path, .. } = &mut bad.just {
                (if side { left_path } else { right_path }).push(0);
            }
            assert!(matches!(verify_cert(&ToyHasher, &program, &com, &[bad], &q, false),
                Err(CertError::Claim { kind: CertErrorKind::GapOpening, .. })));
        }
    }
    // Gap index out of range
    let mut g = gap(&tree, 10, 0, 8, 8, 9);
    if let Just::Gap { i, .. } = &mut g.just {
        *i = 15;
    }
    assert_eq!(
        verify_cert(&ToyHasher, &program, &com, &[g], &Atom::prop(10), false),
        Err(CertError::Claim { index: 0, kind: CertErrorKind::GapIndex })
    );
    // Unf for a true atom: its instance is unblocked
    let r = verify_cert(&ToyHasher, &program, &com, &[unf(41, 1, &[41])], &Atom::prop(41), false);
    assert!(matches!(r, Err(CertError::Claim { kind: CertErrorKind::UnfUnblocked { rule: 7, .. }, .. })));
    // Unf containing an EDB atom
    let r = verify_cert(&ToyHasher, &program, &com, &[unf(50, 1, &[50, 3])], &Atom::prop(50), false);
    assert!(matches!(r, Err(CertError::Claim { kind: CertErrorKind::UnfNotIdb(_), .. })));
    // wrong-sign constructors
    let mut c = memb(&tree, 8, 2);
    c.pos = false;
    assert_eq!(
        verify_cert(&ToyHasher, &program, &com, &[c], &Atom::prop(8), false),
        Err(CertError::Claim { index: 0, kind: CertErrorKind::MembSign })
    );
    // Rule claim for an EDB atom
    let r = verify_cert(&ToyHasher, &program, &com, &[rule(8, 9, 0)], &Atom::prop(8), true);
    assert_eq!(r, Err(CertError::Claim { index: 0, kind: CertErrorKind::RuleNotIdb }));
    // Query not claimed
    assert_eq!(v(&bob[..5]), Err(CertError::QueryNotClaimed));
}

#[test]
fn unf_checks_every_matching_head_instance() {
    use Term::{Const, Var};
    let diagonal = Pattern::new(1, vec![Var(0), Var(0)]);
    let seven = Pattern::new(1, vec![Var(0), Const(7)]);
    let rules = vec![
        Rule::new(diagonal.clone(), vec![diagonal], vec![]),
        Rule::new(seven, vec![Pattern::new(0, vec![Var(0)])], vec![]),
    ];
    let p = Program::new(vec![1, 2], vec![true, false], vec![0, u32::MAX], rules).unwrap();
    let edb = vec![Atom::new(0, vec![7])];
    let tree = commit_sha3(&p, &edb);
    let model = solve(&p, &edb).unwrap();
    for (args, truth) in [(vec![7, 7], true), (vec![6, 7], false), (vec![6, 6], false), (vec![7, 6], false)] {
        let q = Atom::new(1, args);
        let cs = generate_cert(&Sha3Hasher, &p, &model, &tree, &q, truth).unwrap();
        verify_cert(&Sha3Hasher, &p, &tree.commitment(), &cs, &q, truth).unwrap();
    }
    let q = Atom::new(1, vec![7, 7]);
    let c = Claim { atom: q.clone(), pos: false, rank: 1, just: Just::Unf { u: vec![q.clone()] } };
    assert_eq!(verify_cert(&Sha3Hasher, &p, &tree.commitment(), &[c], &q, false),
        Err(CertError::Claim { index: 0, kind: CertErrorKind::UnfUnblocked { rule: 1, head: q } }));
}

#[test]
fn stratifier_rejects_self_negation() {
    let (arity, is_edb, rules) = toy_self_negation_rules();
    assert_eq!(compute_strata(&arity, &is_edb, &rules), Err(ProgramError::Unstratifiable { pred: 60 }));
    for s60 in 0..4 {
        let strata: Vec<u32> = (0..61u32).map(|a| if a == 60 { s60 } else { toy_stratum(a) }).collect();
        assert_eq!(
            Program::new(arity.clone(), is_edb.clone(), strata, rules.clone()).err(),
            Some(ProgramError::NegStratum { rule: 0 })
        );
    }
    // the toy rules themselves are stratifiable, and least strata respect the given ones
    let rules: Vec<Rule> = toy_program().rules().to_vec();
    let st = compute_strata(&[0; TOY_NUM_PREDS], &(0..TOY_NUM_PREDS as u32).map(|a| a < 20).collect::<Vec<_>>(), &rules)
        .expect("stratifiable");
    for a in 0..TOY_NUM_PREDS as u32 {
        assert!(st[a as usize] <= toy_stratum(a));
    }
}

#[test]
fn program_wellformedness_rejections() {
    use Term::{Const, Var};
    let arity = vec![1, 1, 1];
    let is_edb = vec![true, false, false];
    let strata = vec![0, 1, 2];
    let p = |pred, args| Pattern::new(pred, args);
    let mk = |r: Rule| Program::new(arity.clone(), is_edb.clone(), strata.clone(), vec![r]).err();
    let huge = p(0, vec![Var(u16::MAX as u32)]);
    assert_eq!(mk(Rule::new(p(1, vec![Const(1)]), vec![huge], vec![])),
        Some(ProgramError::SubstitutionTooLarge { rule: 0 }));
    // unsafe head variable
    assert_eq!(mk(Rule::new(p(1, vec![Var(1)]), vec![p(0, vec![Var(0)])], vec![])), Some(ProgramError::Unsafe { rule: 0, var: 1 }));
    // unsafe negated variable
    assert_eq!(
        mk(Rule::new(p(1, vec![Var(0)]), vec![p(0, vec![Var(0)])], vec![p(0, vec![Var(2)])])),
        Some(ProgramError::Unsafe { rule: 0, var: 2 })
    );
    // EDB head
    assert_eq!(mk(Rule::new(p(0, vec![Const(1)]), vec![], vec![])), Some(ProgramError::EdbHead { rule: 0 }));
    // positive body from a higher stratum
    assert_eq!(mk(Rule::new(p(1, vec![Var(0)]), vec![p(2, vec![Var(0)])], vec![])), Some(ProgramError::PosStratum { rule: 0 }));
    // arity mismatch
    assert_eq!(
        mk(Rule::new(p(1, vec![Var(0), Var(0)]), vec![p(0, vec![Var(0)])], vec![])),
        Some(ProgramError::ArityMismatch { rule: 0, pred: 1 })
    );
    // EDB at nonzero stratum
    assert_eq!(
        Program::new(arity.clone(), is_edb.clone(), vec![1, 1, 2], vec![]).err(),
        Some(ProgramError::EdbNotStratumZero { pred: 0 })
    );
    // policy head-coverage classification
    let pol = policy_program();
    let hc: Vec<bool> = (0..pol.rules().len()).map(|r| pol.is_head_covering(r)).collect();
    assert_eq!(hc, vec![true, false, true, false, true, true, true]);
}

#[test]
fn toy_timing() {
    let t0 = Instant::now();
    let tree = toy_tree();
    let t_commit = t0.elapsed();
    let program = toy_program();
    let t1 = Instant::now();
    let model = solve(&program, &toy_edb()).expect("solve");
    let t_solve = t1.elapsed();
    let q = Atom::prop(41);
    let t2 = Instant::now();
    let c = generate_cert(&ToyHasher, &program, &model, &tree, &q, true).expect("gen");
    let t_gen = t2.elapsed();
    let com = tree.commitment();
    let iters = 10_000;
    let t3 = Instant::now();
    for _ in 0..iters {
        verify_cert(&ToyHasher, &program, &com, &c, &q, true).expect("verify");
    }
    let t_ver = t3.elapsed() / iters;
    println!(
        "[bench toy] root={} commit_us={:.1} solve_us={:.1} certgen_us={:.1} claims={} cert_bytes={} verify_us={:.2}",
        tree.root(),
        t_commit.as_secs_f64() * 1e6,
        t_solve.as_secs_f64() * 1e6,
        t_gen.as_secs_f64() * 1e6,
        c.len(),
        encode_cert(&c).len(),
        t_ver.as_secs_f64() * 1e6
    );
    assert_eq!(tree.root(), TOY_EXPECTED_ROOT);
}

// -----------------------------------------------------------------------------------
// Real policy over a salted SHA3 EDB
// -----------------------------------------------------------------------------------

struct SplitMix(u64);
impl SplitMix {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

struct EdbShape {
    users: u64,
    resources: u64,
    groups: u64,
    grant: usize,
    member: usize,
    group_grant: usize,
    delegates: usize,
    admin: usize,
    revoked: usize,
    request: usize,
}

const BIG: EdbShape = EdbShape {
    users: 20_000,
    resources: 2_000,
    groups: 1_000,
    grant: 30_000,
    member: 20_000,
    group_grant: 5_000,
    delegates: 10_000,
    admin: 50,
    revoked: 2_000,
    request: 32_950,
};

const SMALL: EdbShape = EdbShape {
    users: 400,
    resources: 40,
    groups: 20,
    grant: 600,
    member: 400,
    group_grant: 100,
    delegates: 200,
    admin: 3,
    revoked: 40,
    request: 659,
};

fn synthetic_policy_edb(shape: &EdbShape, seed: u64) -> Vec<Atom> {
    use policy_preds::*;
    let mut rng = SplitMix(seed);
    let mut out = Vec::new();
    let mut fill = |pred: u32, n: usize, rng: &mut SplitMix, gen: &mut dyn FnMut(&mut SplitMix) -> Vec<u64>| {
        let mut seen = HashSet::new();
        while seen.len() < n {
            let a = gen(rng);
            if seen.insert(a.clone()) {
                out.push(Atom::new(pred, a));
            }
        }
        seen.into_iter().collect::<Vec<_>>()
    };
    let (u, r, g) = (shape.users, shape.resources, shape.groups);
    let grants = fill(GRANT, shape.grant, &mut rng, &mut |x| vec![x.below(u), x.below(r)]);
    fill(MEMBER, shape.member, &mut rng, &mut |x| vec![x.below(u), x.below(g)]);
    fill(GROUP_GRANT, shape.group_grant, &mut rng, &mut |x| vec![x.below(g), x.below(r)]);
    fill(DELEGATES, shape.delegates, &mut rng, &mut |x| vec![x.below(u), x.below(u)]);
    fill(ADMIN, shape.admin, &mut rng, &mut |x| vec![x.below(u)]);
    fill(REVOKED, shape.revoked, &mut rng, &mut |x| vec![x.below(u)]);
    let mut grants_sorted = grants;
    grants_sorted.sort();
    fill(REQUEST, shape.request, &mut rng, &mut |x| {
        if x.below(2) == 0 {
            grants_sorted[x.below(grants_sorted.len() as u64) as usize].clone()
        } else {
            vec![x.below(u), x.below(r)]
        }
    });
    out
}

const MASTER: [u8; 32] = [0x5A; 32];

fn commit_sha3(program: &Program, edb: &[Atom]) -> EdbTree<Sha3Hasher> {
    EdbTree::commit_facts(&Sha3Hasher, program, edb, |k, pos| sha3_leaf_salt(&MASTER, pos, k)).expect("commit")
}

struct Queries {
    allowed_member: Atom,
    allowed_trusted: Option<Atom>,
    not_alert: Atom,
    not_allowed_revoked: Atom,
    alert_revoked: Atom,
    not_can: Atom,
}

fn pick_queries(model: &Model) -> Queries {
    use policy_preds::*;
    let atoms = |p: u32| model.tuples(p).iter().map(move |t| Atom::new(p, t.to_vec()));
    let via = |a: &Atom, rule: u32| {
        let can = Atom::new(CAN, a.args.clone());
        model.provenance(&can).map(|(r, _)| r == rule).unwrap_or(false)
    };
    let allowed_member = atoms(ALLOWED).find(|a| via(a, 1)).expect("allowed via member");
    let allowed_trusted = atoms(ALLOWED)
        .filter(|a| via(a, 4))
        .max_by_key(|a| model.level(&Atom::new(TRUSTED, vec![a.args[0]])).unwrap_or(0));
    let not_alert = atoms(REQUEST)
        .find(|a| model.holds(&Atom::new(ALLOWED, a.args.clone())))
        .map(|a| Atom::new(ALERT, a.args))
        .expect("allowed request");
    let revoked: HashSet<u64> = model.tuples(REVOKED).iter().map(|t| t[0]).collect();
    let not_allowed_revoked = atoms(CAN)
        .find(|a| revoked.contains(&a.args[0]))
        .map(|a| Atom::new(ALLOWED, a.args))
        .expect("revoked user with can");
    let alert_revoked = atoms(ALERT).find(|a| revoked.contains(&a.args[0])).expect("revoked alert");
    let not_can = (0..)
        .map(|r| Atom::new(CAN, vec![1, r]))
        .find(|a| !model.holds(a))
        .expect("some can false");
    Queries { allowed_member, allowed_trusted, not_alert, not_allowed_revoked, alert_revoked, not_can }
}

#[test]
fn policy_sha3_certs_and_falsifiers() {
    use policy_preds::*;
    let program = policy_program();
    let edb = synthetic_policy_edb(&SMALL, 7);
    let tree = commit_sha3(&program, &edb);
    let com = tree.commitment();
    let model = solve(&program, &edb).expect("solve");
    let q = pick_queries(&model);
    let h = Sha3Hasher;
    let mut list = vec![
        (q.allowed_member.clone(), true),
        (q.not_alert.clone(), false),
        (q.not_allowed_revoked.clone(), false),
        (q.alert_revoked.clone(), true),
    ];
    if let Some(a) = &q.allowed_trusted {
        list.push((a.clone(), true));
    }
    for (a, s) in &list {
        let c = generate_cert(&h, &program, &model, &tree, a, *s).expect("gen");
        verify_cert(&h, &program, &com, &c, a, *s).expect("verify");
        let bytes = encode_cert(&c);
        let back: Vec<Sha3Claim> = decode_cert(&bytes).expect("decode");
        assert_eq!(back, c);
        assert!(decode_cert::<Vec<u8>, [u8; 32], [u8; 32]>(&bytes[..bytes.len() - 1]).is_none());
        let mut extra = bytes.clone();
        extra.push(0);
        assert!(decode_cert::<Vec<u8>, [u8; 32], [u8; 32]>(&extra).is_none());
        // every claim is load-bearing for at least the query claim: dropping the last (query) claim fails
        let r = verify_cert(&h, &program, &com, &c[..c.len() - 1], a, *s);
        assert!(r.is_err());
    }
    // ¬can is not certifiable: can has non-head-covering rules (fail-closed)
    assert!(matches!(
        generate_cert(&h, &program, &model, &tree, &q.not_can, false),
        Err(CertGenError::NonHeadCovering { .. })
    ));
    let forged = vec![Claim { atom: q.not_can.clone(), pos: false, rank: 1, just: Just::Unf { u: vec![q.not_can.clone()] } }];
    assert!(matches!(
        verify_cert(&h, &program, &com, &forged, &q.not_can, false),
        Err(CertError::Claim { kind: CertErrorKind::UnfNonHeadCovering { .. }, .. })
    ));
    // Gap claim for a revoked user (fact present) fails at every adjacent pair around its key
    let u = q.not_allowed_revoked.args[0];
    let rev = Atom::new(REVOKED, vec![u]);
    let j = tree.find_key(&h.enc(&rev).expect("enc")).expect("present");
    for i in [j - 1, j] {
        let leaves = tree.leaves();
        let g = Claim {
            atom: rev.clone(),
            pos: false,
            rank: 0,
            just: Just::Gap {
                i: i as u64,
                left: leaves[i].clone(),
                left_path: tree.path(i),
                right: leaves[i + 1].clone(),
                right_path: tree.path(i + 1),
            },
        };
        assert_eq!(
            verify_cert(&h, &program, &com, &[g], &rev, false),
            Err(CertError::Claim { index: 0, kind: CertErrorKind::GapOrder })
        );
    }
    // a cert verified against a different EDB root (different salts) rejects
    let other = EdbTree::commit_facts(&h, &program, &edb, |k, pos| sha3_leaf_salt(&[1; 32], pos, k)).expect("commit");
    let c = generate_cert(&h, &program, &model, &tree, &q.allowed_member, true).expect("gen");
    assert!(verify_cert(&h, &program, &other.commitment(), &c, &q.allowed_member, true).is_err());
    // the key encoding is order-preserving within a predicate and sentinel-bounded
    let k1 = h.enc(&Atom::new(GRANT, vec![1, 2])).expect("enc");
    let k2 = h.enc(&Atom::new(GRANT, vec![1, 256])).expect("enc");
    assert!(h.bot() < k1 && k1 < k2 && k2 < h.top());
}

fn ms(d: std::time::Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

#[test]
fn bench_policy_100k_sha3_edb() {
    use policy_preds::*;
    let program = policy_program();
    let edb = synthetic_policy_edb(&BIG, 0xC0FFEE);
    assert_eq!(edb.len(), 100_000);
    let h = Sha3Hasher;
    let t0 = Instant::now();
    let tree = commit_sha3(&program, &edb);
    let t_commit = t0.elapsed();
    let com = tree.commitment();
    let t1 = Instant::now();
    let model = solve(&program, &edb).expect("solve");
    let t_solve = t1.elapsed();
    println!(
        "[bench edb] facts={} depth={} leaves={} commit_ms={:.1} solve_ms={:.1} max_level={} trusted={} can={} allowed={} alert={}",
        edb.len(),
        tree.depth(),
        tree.leaves().len(),
        ms(t_commit),
        ms(t_solve),
        model.max_level(),
        model.count(TRUSTED),
        model.count(CAN),
        model.count(ALLOWED),
        model.count(ALERT)
    );
    let q = pick_queries(&model);
    let mut list: Vec<(&str, Atom, bool)> = vec![
        ("allowed(u,r) via member/group_grant", q.allowed_member.clone(), true),
        ("not alert(u,r) [allowed request]", q.not_alert.clone(), false),
        ("not allowed(u,r) [revoked user]", q.not_allowed_revoked.clone(), false),
        ("alert(u,r) [revoked user's request]", q.alert_revoked.clone(), true),
    ];
    if let Some(a) = &q.allowed_trusted {
        list.push(("allowed(u,r) via deepest trusted delegation chain", a.clone(), true));
    }
    for (label, a, s) in &list {
        let t2 = Instant::now();
        let c = generate_cert(&h, &program, &model, &tree, a, *s).expect("gen");
        let t_gen = t2.elapsed();
        let bytes = encode_cert(&c);
        let t3 = Instant::now();
        verify_cert(&h, &program, &com, &c, a, *s).expect("verify");
        let t_first = t3.elapsed();
        let iters = 200u32;
        let t4 = Instant::now();
        for _ in 0..iters {
            verify_cert(&h, &program, &com, &c, a, *s).expect("verify");
        }
        let t_ver = t4.elapsed() / iters;
        let t5 = Instant::now();
        for _ in 0..iters {
            let d: Vec<Sha3Claim> = decode_cert(&bytes).expect("decode");
            verify_cert(&h, &program, &com, &d, a, *s).expect("verify");
        }
        let t_dv = t5.elapsed() / iters;
        println!(
            "[bench query] {label}: query={:?} sign={} claims={} cert_bytes={} certgen_ms={:.3} verify_ms={:.4} (first {:.4}) decode+verify_ms={:.4}",
            a,
            s,
            c.len(),
            bytes.len(),
            ms(t_gen),
            ms(t_ver),
            ms(t_first),
            ms(t_dv)
        );
        assert!(ms(t_ver) < 1.0, "verifier target < 1 ms");
    }
    let t6 = Instant::now();
    assert!(matches!(
        generate_cert(&h, &program, &model, &tree, &q.not_can, false),
        Err(CertGenError::NonHeadCovering { .. })
    ));
    println!("[bench query] not can(u,r): rejected NonHeadCovering in {:.3} ms (fail-closed)", ms(t6.elapsed()));
}

// -----------------------------------------------------------------------------------
// ComposedByteTurnCert
// -----------------------------------------------------------------------------------

struct TurnFixture {
    program: Program,
    tree: EdbTree<Sha3Hasher>,
    model: Model,
    dfa: ByteDfa,
    bpe: BpeTable,
}

const USER: u64 = 42;
const REVOKED_USER: u64 = 13;
const TOOL: u64 = 7;
const REVOKED_BYTES: &[u8] = b"user 13 calls tool 7: list the files in the project\n";
const TURN_BYTES: &[u8] = b"user 42 calls tool 7: list the files in the project\n";

fn turn_fixture() -> TurnFixture {
    use policy_preds::*;
    let program = policy_program();
    let edb = vec![
        Atom::new(GRANT, vec![USER, TOOL]),
        Atom::new(GRANT, vec![REVOKED_USER, TOOL]),
        Atom::new(REVOKED, vec![REVOKED_USER]),
        Atom::new(MEMBER, vec![5, 1]),
        Atom::new(GROUP_GRANT, vec![1, TOOL]),
        Atom::new(GROUP_GRANT, vec![0, 9]),
        Atom::new(ADMIN, vec![99]),
        Atom::new(DELEGATES, vec![99, 98]),
        Atom::new(REQUEST, vec![REVOKED_USER, TOOL]),
    ];
    let tree = commit_sha3(&program, &edb);
    let model = solve(&program, &edb).expect("solve");
    TurnFixture { program, tree, model, dfa: ByteDfa::no_secret_ascii(), bpe: BpeTable::demo() }
}

fn ctx(f: &TurnFixture) -> TurnContext<'_> {
    TurnContext { program: &f.program, edb: f.tree.commitment(), dfa: &f.dfa, bpe: &f.bpe, read_request: text_request_ids }
}

fn prove(f: &TurnFixture, bytes: &[u8], user: u64) -> Result<ComposedByteTurnCert, TurnError> {
    prove_composed_turn(&ctx(f), &f.tree, &f.model, bytes, [0x11; 32], user, TOOL)
}

#[test]
fn turn_rejects_inconsistent_inputs() {
    let f = turn_fixture();
    let c = prove(&f, TURN_BYTES, USER).unwrap();
    let mut cx = ctx(&f);
    cx.edb.depth += 1;
    assert_eq!(prove_composed_turn(&cx, &f.tree, &f.model, TURN_BYTES, [0; 32], USER, TOOL),
        Err(TurnError::EdbMismatch));
    let mut cx = ctx(&f);
    let mut dfa = f.dfa.clone();
    dfa.delta.pop();
    cx.dfa = &dfa;
    assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::DfaTable));
    let wrong = solve(&toy_program(), &toy_edb()).unwrap();
    assert_eq!(prove_composed_turn(&ctx(&f), &f.tree, &wrong, TURN_BYTES, [0; 32], USER, TOOL),
        Err(TurnError::ProverDatalog(CertGenError::ProgramMismatch)));
}

#[test]
fn request_header_has_one_canonical_pair() {
    assert_eq!(text_request_ids(b"user 0 calls tool 18446744073709551615: "), Some((0, u64::MAX)));
    for bad in [
        &b"user 01 calls tool 7: payload"[..],
        b"user +1 calls tool 7: payload",
        b"user 1 calls tool 18446744073709551616: payload",
        b"user 1 calls tool 7 payload",
    ] {
        assert_eq!(text_request_ids(bad), None);
    }
}

#[test]
fn composed_turn_accepts_honest() {
    let f = turn_fixture();
    let t0 = Instant::now();
    let c = prove(&f, TURN_BYTES, USER).expect("prove");
    let t_prove = t0.elapsed();
    let t1 = Instant::now();
    verify_composed_turn(&ctx(&f), &c).expect("verify");
    let t_ver = t1.elapsed();
    assert!(c.bpe.tokens.len() < TURN_BYTES.len(), "BPE merges fire");
    assert_eq!(f.bpe.decode(&c.bpe.tokens).as_deref(), Some(TURN_BYTES));
    // a second user via member/group_grant also authorizes
    let c5 = prove_composed_turn(&ctx(&f), &f.tree, &f.model, b"user 5 calls tool 7: list files", [3; 32], 5, TOOL).expect("prove user 5");
    verify_composed_turn(&ctx(&f), &c5).expect("verify user 5");
    assert_eq!(prove(&f, TURN_BYTES, 5).unwrap_err(), TurnError::AuthBinding);
    let mut mismatch = c.clone();
    mismatch.user = 5;
    mismatch.auth.user = 5;
    mismatch.auth.claims = c5.auth.claims;
    mismatch.transcript = turn_transcript(&mismatch);
    assert_eq!(verify_composed_turn(&ctx(&f), &mismatch), Err(TurnError::AuthBinding));
    println!(
        "[bench turn] bytes={} tokens={} datalog_claims={} datalog_cert_bytes={} prove_ms={:.3} verify_ms={:.3}",
        c.bytes.len(),
        c.bpe.tokens.len(),
        c.auth.claims.len(),
        encode_cert(&c.auth.claims).len(),
        ms(t_prove),
        ms(t_ver)
    );
}

#[test]
fn composed_turn_rejects_mismatched_byte_roots() {
    let f = turn_fixture();
    let cx = ctx(&f);
    let honest = prove(&f, TURN_BYTES, USER).expect("prove");
    let other = prove(&f, b"user 42 calls tool 7: list the other files\n", USER).expect("prove other");
    for (sub, which) in [("bpe", 0), ("dfa", 1), ("auth", 2)] {
        let mut c = honest.clone();
        match which {
            0 => c.bpe = other.bpe.clone(),
            1 => c.dfa = other.dfa.clone(),
            _ => c.auth = other.auth.clone(),
        }
        c.transcript = turn_transcript(&c);
        assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::ByteRootMismatch { sub }));
    }
    // swap the opened bytes but keep the old root
    let mut c = honest.clone();
    c.bytes = other.bytes.clone();
    assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::ByteCommitment));
    // transcript tamper
    let mut c = honest.clone();
    c.transcript[0] ^= 1;
    assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::Transcript));
}

#[test]
fn composed_turn_rejects_tokens_of_different_bytes() {
    let f = turn_fixture();
    let cx = ctx(&f);
    let honest = prove(&f, TURN_BYTES, USER).expect("prove");
    let mut c = honest.clone();
    c.bpe.tokens = f.bpe.encode(b"user 42 calls tool 7: delete the files in the project\n");
    c.transcript = turn_transcript(&c);
    assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::BpeDecode));
    // decodes to the right bytes but is not the canonical encoding
    let mut c = honest.clone();
    c.bpe.tokens = TURN_BYTES.iter().map(|&b| b as u32).collect();
    c.transcript = turn_transcript(&c);
    assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::BpeNotCanonical));
    // a different BPE table digest
    let mut c = honest;
    c.bpe.table_digest[0] ^= 1;
    c.transcript = turn_transcript(&c);
    assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::BpeDigest));
}

#[test]
fn composed_turn_rejects_dfa_rejecting_bytes() {
    let f = turn_fixture();
    let cx = ctx(&f);
    let bad: &[u8] = b"user 42 calls tool 7 with key sk-live-0123\n";
    assert_eq!(prove(&f, bad, USER).err(), Some(TurnError::DfaRejects));
    // forge: commit the bad bytes and reuse an honest-shaped cert
    let mut c = prove(&f, TURN_BYTES, USER).expect("prove");
    c.bytes = bad.to_vec();
    c.byte_root = commit_turn_bytes(&c.salt, bad);
    c.dfa.byte_root = c.byte_root;
    c.bpe.byte_root = c.byte_root;
    c.auth.byte_root = c.byte_root;
    c.bpe.tokens = f.bpe.encode(bad);
    c.dfa.trace = f.dfa.run(bad);
    c.transcript = turn_transcript(&c);
    assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::DfaRejects));
    // a fake accepting trace does not follow delta
    c.dfa.trace = vec![0; bad.len() + 1];
    c.transcript = turn_transcript(&c);
    assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::DfaTrace));
    // non-printable byte
    assert_eq!(prove(&f, b"tool 7 \x00\n", USER).err(), Some(TurnError::DfaRejects));
}

#[test]
fn composed_turn_rejects_revoked_user() {
    use policy_preds::*;
    let f = turn_fixture();
    let cx = ctx(&f);
    let h = Sha3Hasher;
    assert!(matches!(
        prove(&f, REVOKED_BYTES, REVOKED_USER),
        Err(TurnError::ProverDatalog(CertGenError::NotInModel { .. }))
    ));
    // Preserve a consistent opening for the revoked request while testing the policy.
    let bind_revoked = |c: &mut ComposedByteTurnCert| {
        c.bytes = REVOKED_BYTES.to_vec();
        c.byte_root = commit_turn_bytes(&c.salt, &c.bytes);
        c.dfa.byte_root = c.byte_root;
        c.auth.byte_root = c.byte_root;
        c.bpe.byte_root = c.byte_root;
        c.bpe.tokens = f.bpe.encode(&c.bytes);
        c.dfa.trace = f.dfa.run(&c.bytes);
    };
    // Relabel an honest claim list to the revoked user.
    let mut c = prove(&f, TURN_BYTES, USER).expect("prove");
    c.user = REVOKED_USER;
    bind_revoked(&mut c);
    c.auth.user = REVOKED_USER;
    c.transcript = turn_transcript(&c);
    assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::Datalog(CertError::QueryNotClaimed)));
    // user bound in the transcript but not in the auth sub-cert
    let mut c = prove(&f, TURN_BYTES, USER).expect("prove");
    c.user = REVOKED_USER;
    c.transcript = turn_transcript(&c);
    assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::AuthBinding));
    // forge allowed(13,7) with a Gap "proving" ¬revoked(13)
    let grant = Atom::new(GRANT, vec![REVOKED_USER, TOOL]);
    let can = Atom::new(CAN, vec![REVOKED_USER, TOOL]);
    let rev = Atom::new(REVOKED, vec![REVOKED_USER]);
    let allowed = Atom::new(ALLOWED, vec![REVOKED_USER, TOOL]);
    let jg = f.tree.find_key(&h.enc(&grant).expect("enc")).expect("grant present");
    let jr = f.tree.find_key(&h.enc(&rev).expect("enc")).expect("revoked present");
    let leaves = f.tree.leaves();
    let claims: Vec<Sha3Claim> = vec![
        Claim { atom: grant, pos: true, rank: 3, just: Just::Memb { j: jg as u64, salt: leaves[jg].salt, path: f.tree.path(jg) } },
        Claim { atom: can, pos: true, rank: 10, just: Just::Rule { rule_id: 0, subst: vec![REVOKED_USER, TOOL] } },
        Claim {
            atom: rev,
            pos: false,
            rank: 0,
            just: Just::Gap {
                i: (jr - 1) as u64,
                left: leaves[jr - 1].clone(),
                left_path: f.tree.path(jr - 1),
                right: leaves[jr].clone(),
                right_path: f.tree.path(jr),
            },
        },
        Claim { atom: allowed, pos: true, rank: 20, just: Just::Rule { rule_id: 5, subst: vec![REVOKED_USER, TOOL] } },
    ];
    let mut c = prove(&f, TURN_BYTES, USER).expect("prove");
    c.user = REVOKED_USER;
    bind_revoked(&mut c);
    c.auth.user = REVOKED_USER;
    c.auth.claims = claims;
    c.transcript = turn_transcript(&c);
    assert_eq!(
        verify_composed_turn(&cx, &c),
        Err(TurnError::Datalog(CertError::Claim { index: 2, kind: CertErrorKind::GapOrder }))
    );
    // an auth cert against a different EDB commitment
    let mut c = prove(&f, TURN_BYTES, USER).expect("prove");
    c.auth.edb.depth += 1;
    c.transcript = turn_transcript(&c);
    assert_eq!(verify_composed_turn(&cx, &c), Err(TurnError::EdbMismatch));
}
