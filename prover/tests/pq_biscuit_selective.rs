//! Byte-exact Lean 4.35.0 conformance, explicit security regressions (`CAP-01`, `CAP-10`,
//! `CAP-12`, unrevealed-attribute hiding), and `--release` microbenchmarks for
//! `minidregg_prover::pq_biscuit`.

use std::time::Instant;

use minidregg_prover::pq_biscuit::{
    attenuate_token, build_attr_leaves, build_selective_openings, chain_id, cshake32,
    extract_issuer_authority, extract_subject, issue_root_token, lineage_of, merkle_root,
    root_lineage, verify_presentation, verify_selective_disclosure, verify_token, AttenuationBlock,
    Digest32, IssuerSecret, PqSigBackend, RevocationSet, RevocationWitnessError, SaltedAttribute,
    VerifyError, WotsCshake256,
};
use serde::Deserialize;

#[derive(Deserialize)]
struct PqBiscuitConformanceDoc {
    schema: String,
    issuer_seed_hex: String,
    holder0_seed_hex: String,
    holder1_seed_hex: String,
    holder2_seed_hex: String,
    issuer_pk_hex: String,
    holder0_pk_hex: String,
    holder1_pk_hex: String,
    holder2_pk_hex: String,
    nonce_hex: String,
    salts_hex: Vec<String>,
    attr_merkle_root_hex: String,
    block0_sig_hex: String,
    hop1_sig_hex: String,
    hop2_sig_hex: String,
    root_lineage_hex: String,
    hop1_lineage_hex: String,
    tail_lineage_hex: String,
    chain_id0_hex: String,
    chain_id1_hex: String,
    chain_id2_hex: String,
    revocation_root_hex: String,
    presentation_valid: bool,
    revocation_root_order_independent: bool,
    ancestor_revocation_kills_descendant: bool,
    extracted_subject: String,
    disclosed_indices: Vec<usize>,
}

fn unhex(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0);
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("valid hex"))
        .collect()
}

fn unhex32(s: &str) -> Digest32 {
    unhex(s).try_into().expect("32-byte digest")
}

fn to_hex(bs: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(bs.len() * 2);
    for &b in bs {
        s.push(HEX[(b >> 4) as usize] as char);
        s.push(HEX[(b & 0x0f) as usize] as char);
    }
    s
}

#[test]
fn lean_conformance_vector_byte_exact() {
    let raw = include_str!("../testdata/pq_biscuit_conformance.json");
    let doc: PqBiscuitConformanceDoc =
        serde_json::from_str(raw).expect("parse Lean conformance JSON");
    assert_eq!(doc.schema, "minidregg.pq_biscuit_conformance.v1");
    assert!(doc.presentation_valid);
    assert!(doc.revocation_root_order_independent);
    assert!(doc.ancestor_revocation_kills_descendant);

    let scheme = WotsCshake256;
    let issuer_seed = unhex(&doc.issuer_seed_hex);
    let holder0_seed = unhex(&doc.holder0_seed_hex);
    let holder1_seed = unhex(&doc.holder1_seed_hex);
    let holder2_seed = unhex(&doc.holder2_seed_hex);

    let issuer = IssuerSecret::new(issuer_seed);
    let issuer_pk = issuer.public_key(&scheme);
    let holder0_pk = scheme.pk_of(&holder0_seed);
    let holder1_pk = scheme.pk_of(&holder1_seed);
    let holder2_pk = scheme.pk_of(&holder2_seed);

    assert_eq!(to_hex(&issuer_pk), doc.issuer_pk_hex);
    assert_eq!(to_hex(&holder0_pk), doc.holder0_pk_hex);
    assert_eq!(to_hex(&holder1_pk), doc.holder1_pk_hex);
    assert_eq!(to_hex(&holder2_pk), doc.holder2_pk_hex);

    let attrs = vec![
        SaltedAttribute {
            key: b"acct".to_vec(),
            value: b"alice".to_vec(),
            salt: unhex32(&doc.salts_hex[0]),
        },
        SaltedAttribute {
            key: b"role".to_vec(),
            value: b"researcher".to_vec(),
            salt: unhex32(&doc.salts_hex[1]),
        },
        SaltedAttribute {
            key: b"clearance".to_vec(),
            value: b"L3".to_vec(),
            salt: unhex32(&doc.salts_hex[2]),
        },
        SaltedAttribute {
            key: b"region".to_vec(),
            value: b"us-west".to_vec(),
            salt: unhex32(&doc.salts_hex[3]),
        },
    ];
    let leaves = build_attr_leaves(2, &attrs);
    let attr_root = merkle_root(2, &leaves);
    assert_eq!(to_hex(&attr_root), doc.attr_merkle_root_hex);

    let nonce = unhex32(&doc.nonce_hex);
    let tok0 = issue_root_token(
        &scheme,
        &issuer,
        b"alice".to_vec(),
        holder0_pk,
        attr_root,
        nonce,
        0x0F,
        2000,
    );
    let tok1 = attenuate_token(
        &scheme,
        &tok0,
        &holder0_seed,
        0x07,
        1500,
        holder1_pk,
        b"acct=admin".to_vec(),
    );
    let tok2 = attenuate_token(
        &scheme,
        &tok1,
        &holder1_seed,
        0x03,
        1200,
        holder2_pk,
        b"scope=read_doc".to_vec(),
    );

    assert_eq!(to_hex(&tok2.block0_sig), doc.block0_sig_hex);
    assert_eq!(to_hex(&tok2.hops[0].sig_bytes), doc.hop1_sig_hex);
    assert_eq!(to_hex(&tok2.hops[1].sig_bytes), doc.hop2_sig_hex);
    assert_eq!(to_hex(&root_lineage(&tok2.block0)), doc.root_lineage_hex);
    assert_eq!(
        to_hex(&lineage_of(&tok2.block0, &tok2.hops[..1])),
        doc.hop1_lineage_hex
    );
    assert_eq!(
        to_hex(&lineage_of(&tok2.block0, &tok2.hops)),
        doc.tail_lineage_hex
    );

    let cid0 = chain_id(&tok2.block0, &tok2.hops, 0);
    let cid1 = chain_id(&tok2.block0, &tok2.hops, 1);
    let cid2 = chain_id(&tok2.block0, &tok2.hops, 2);
    assert_eq!(to_hex(&cid0), doc.chain_id0_hex);
    assert_eq!(to_hex(&cid1), doc.chain_id1_hex);
    assert_eq!(to_hex(&cid2), doc.chain_id2_hex);

    let rs_unsorted = RevocationSet::from_raw(&[cid2, cid0, cid1]);
    let rs_sorted = RevocationSet::from_raw(&[cid0, cid1, cid2]);
    assert_eq!(rs_unsorted, rs_sorted);
    assert_eq!(to_hex(&rs_unsorted.root()), doc.revocation_root_hex);

    let openings = build_selective_openings(2, &attrs, &doc.disclosed_indices);
    let va = verify_presentation(&scheme, &issuer_pk, &RevocationSet::empty(), 1000, &tok2, &openings)
        .expect("Lean conformance presentation must verify");
    assert_eq!(va.subject, doc.extracted_subject.as_bytes());
    assert_eq!(va.rights, 0x03);
    assert_eq!(va.expires_at, 1200);
}

#[test]
fn regression_cap01_root_key_isolation_and_block0_unforgeability() {
    let scheme = WotsCshake256;
    let issuer_secret_bytes = b"TOP-SECRET-ISSUER-KEY-MATERIAL!!".to_vec();
    let issuer = IssuerSecret::new(issuer_secret_bytes.clone());
    let issuer_pk = issuer.public_key(&scheme);
    let holder0_sk = b"holder-0-delegated-secret-key-00".to_vec();
    let holder1_sk = b"holder-1-delegated-secret-key-01".to_vec();

    let tok0 = issue_root_token(
        &scheme,
        &issuer,
        b"alice".to_vec(),
        scheme.pk_of(&holder0_sk),
        [0x11; 32],
        [0x22; 32],
        0x07,
        5000,
    );
    let tok1 = attenuate_token(
        &scheme,
        &tok0,
        &holder0_sk,
        0x03,
        4000,
        scheme.pk_of(&holder1_sk),
        b"scope=read".to_vec(),
    );

    // Serialized HolderToken MUST NOT contain any substring of the issuer's secret key.
    let wire = tok1.serialize_bytes();
    assert!(
        !wire.windows(issuer_secret_bytes.len()).any(|w| w == issuer_secret_bytes.as_slice()),
        "CAP-01 violation: issuer secret bytes found in serialized HolderToken"
    );

    // Valid token verifies under issuer_pk alone.
    assert!(verify_token(&scheme, &issuer_pk, &RevocationSet::empty(), 1000, &tok1).is_ok());

    // Tampering block0 subject, rights, or attr_merkle_root without issuer secret fails.
    let mut forged_subj = tok1.clone();
    forged_subj.block0.subject = b"admin".to_vec();
    assert_eq!(
        verify_token(&scheme, &issuer_pk, &RevocationSet::empty(), 1000, &forged_subj),
        Err(VerifyError::InvalidBlock0Signature)
    );

    let mut forged_rights = tok1.clone();
    forged_rights.block0.rights = 0xFF;
    assert_eq!(
        verify_token(&scheme, &issuer_pk, &RevocationSet::empty(), 1000, &forged_rights),
        Err(VerifyError::InvalidBlock0Signature)
    );

    let mut forged_root = tok1.clone();
    forged_root.block0.attr_merkle_root[0] ^= 0x80;
    assert_eq!(
        verify_token(&scheme, &issuer_pk, &RevocationSet::empty(), 1000, &forged_root),
        Err(VerifyError::InvalidBlock0Signature)
    );
}

#[test]
fn regression_cap10_unsorted_revocation_witness_and_ancestor_cone() {
    let scheme = WotsCshake256;
    let issuer = IssuerSecret::new(b"cap10-issuer-seed-32-bytes-00000".to_vec());
    let issuer_pk = issuer.public_key(&scheme);
    let h0_sk = b"cap10-holder0-seed-32-bytes-0000".to_vec();
    let h1_sk = b"cap10-holder1-seed-32-bytes-0000".to_vec();
    let h2_sk = b"cap10-holder2-seed-32-bytes-0000".to_vec();

    let tok0 = issue_root_token(
        &scheme,
        &issuer,
        b"bob".to_vec(),
        scheme.pk_of(&h0_sk),
        [0x33; 32],
        [0x44; 32],
        0x0F,
        5000,
    );
    let tok1 = attenuate_token(&scheme, &tok0, &h0_sk, 0x07, 4000, scheme.pk_of(&h1_sk), b"hop1".to_vec());
    let tok2 = attenuate_token(&scheme, &tok1, &h1_sk, 0x07, 4000, scheme.pk_of(&h2_sk), b"noop".to_vec());

    // Reproduce exact CAP-10 unsorted binary_search bug on a 3-element unsorted slice.
    let id_a = [0x10; 32];
    let id_b = [0x20; 32];
    let id_c = [0x30; 32];
    let unsorted = vec![id_c, id_a, id_b];
    assert!(unsorted.binary_search(&id_c).is_err(), "naive unsorted binary_search misses id_c");

    // Canonical RevocationSet::from_raw catches id_c regardless of insertion order.
    let rs_canonical = RevocationSet::from_raw(&unsorted);
    let rs_sorted_in = RevocationSet::from_raw(&[id_a, id_b, id_c]);
    assert!(rs_canonical.contains(&id_c));
    assert_eq!(rs_canonical.root(), rs_sorted_in.root());

    // Fail-closed witness verification REJECTS the unsorted witness (even with matching canonical root!).
    assert_eq!(
        RevocationSet::from_verified_witness(&unsorted, &rs_canonical.root()),
        Err(RevocationWitnessError::UnsortedOrDuplicateWitness)
    );
    assert!(RevocationSet::from_verified_witness(rs_canonical.keys(), &rs_canonical.root()).is_ok());

    // Ancestor-cone revocation (CAP-10 + CAP-13): revoking tok1 kills tok2 (appended no-op hop)!
    let cid1 = chain_id(&tok1.block0, &tok1.hops, 1);
    let rs_rev = RevocationSet::from_raw(&[id_c, cid1, id_a]);
    assert_eq!(
        verify_token(&scheme, &issuer_pk, &rs_rev, 1000, &tok1),
        Err(VerifyError::RevokedAtDepth(1))
    );
    assert_eq!(
        verify_token(&scheme, &issuer_pk, &rs_rev, 1000, &tok2),
        Err(VerifyError::RevokedAtDepth(1))
    );
    // Revoking block 0 kills the entire cone at depth 0.
    let cid0 = chain_id(&tok0.block0, &tok0.hops, 0);
    let rs_rev0 = RevocationSet::from_raw(&[cid0]);
    assert_eq!(
        verify_token(&scheme, &issuer_pk, &rs_rev0, 1000, &tok2),
        Err(VerifyError::RevokedAtDepth(0))
    );
}

#[test]
fn regression_cap12_block0_authority_pin_kills_acct_admin_and_escalation() {
    let scheme = WotsCshake256;
    let issuer = IssuerSecret::new(b"cap12-issuer-seed-32-bytes-00000".to_vec());
    let issuer_pk = issuer.public_key(&scheme);
    let h0_sk = b"cap12-holder0-seed-32-bytes-0000".to_vec();
    let h1_sk = b"cap12-holder1-seed-32-bytes-0000".to_vec();

    let tok0 = issue_root_token(
        &scheme,
        &issuer,
        b"alice".to_vec(),
        scheme.pk_of(&h0_sk),
        [0x55; 32],
        [0x66; 32],
        0x03,
        1000,
    );

    // Holder appends a valid narrow hop carrying `"acct=admin"` trying to hijack subject (CAP-12).
    let tok_spoof = attenuate_token(
        &scheme,
        &tok0,
        &h0_sk,
        0x01,
        900,
        scheme.pk_of(&h1_sk),
        b"acct=admin".to_vec(),
    );
    assert_eq!(extract_subject(&tok_spoof), b"alice");
    assert_eq!(extract_issuer_authority(&tok_spoof).subject, b"alice");
    let va = verify_token(&scheme, &issuer_pk, &RevocationSet::empty(), 500, &tok_spoof)
        .expect("narrow hop with inert acct=admin caveat verifies under alice");
    assert_eq!(va.subject, b"alice", "CAP-12: subject MUST stay pinned to block 0");
    assert_eq!(va.rights, 0x01);
    assert_eq!(va.expires_at, 900);

    // Rights escalation in hop 1 (0x03 -> 0x07) MUST be rejected.
    let tok_esc_rights = attenuate_token(
        &scheme,
        &tok0,
        &h0_sk,
        0x07,
        900,
        scheme.pk_of(&h1_sk),
        b"acct=admin".to_vec(),
    );
    assert_eq!(
        verify_token(&scheme, &issuer_pk, &RevocationSet::empty(), 500, &tok_esc_rights),
        Err(VerifyError::RightsEscalation { hop: 1 })
    );

    // Expiry extension in hop 1 (1000 -> 2000) MUST be rejected.
    let tok_esc_exp = attenuate_token(
        &scheme,
        &tok0,
        &h0_sk,
        0x01,
        2000,
        scheme.pk_of(&h1_sk),
        b"acct=admin".to_vec(),
    );
    assert_eq!(
        verify_token(&scheme, &issuer_pk, &RevocationSet::empty(), 500, &tok_esc_exp),
        Err(VerifyError::ExpiryEscalation { hop: 1 })
    );

    // Unsigned hop injection MUST be rejected.
    let mut tok_bad_sig = tok_spoof.clone();
    tok_bad_sig.hops.push(AttenuationBlock {
        rights: 0x01,
        expires_at: 800,
        next_holder_pk: vec![0xAA; 32],
        caveat_tag: b"forged".to_vec(),
        sig_bytes: vec![0x00; 67 * 32],
    });
    assert_eq!(
        verify_token(&scheme, &issuer_pk, &RevocationSet::empty(), 500, &tok_bad_sig),
        Err(VerifyError::InvalidHopSignature { hop: 2 })
    );
}

#[test]
fn regression_unrevealed_attribute_hiding_and_selective_binding() {
    let salt0 = cshake32(b"HIDE.TEST.SALT", b"s0");
    let salt1 = cshake32(b"HIDE.TEST.SALT", b"s1");
    let salt2_a = cshake32(b"HIDE.TEST.SALT", b"s2-a");
    let salt2_b = cshake32(b"HIDE.TEST.SALT", b"s2-b");
    let salt3 = cshake32(b"HIDE.TEST.SALT", b"s3");

    let secret_ssn = b"999-00-1234";
    let attrs_a = vec![
        SaltedAttribute { key: b"acct".to_vec(), value: b"alice".to_vec(), salt: salt0 },
        SaltedAttribute { key: b"role".to_vec(), value: b"auditor".to_vec(), salt: salt1 },
        SaltedAttribute { key: b"ssn".to_vec(), value: secret_ssn.to_vec(), salt: salt2_a },
        SaltedAttribute { key: b"tier".to_vec(), value: b"gold".to_vec(), salt: salt3 },
    ];
    let attrs_b = vec![
        SaltedAttribute { key: b"acct".to_vec(), value: b"alice".to_vec(), salt: salt0 },
        SaltedAttribute { key: b"role".to_vec(), value: b"auditor".to_vec(), salt: salt1 },
        SaltedAttribute { key: b"ssn".to_vec(), value: secret_ssn.to_vec(), salt: salt2_b },
        SaltedAttribute { key: b"tier".to_vec(), value: b"gold".to_vec(), salt: salt3 },
    ];

    let leaves_a = build_attr_leaves(2, &attrs_a);
    let leaves_b = build_attr_leaves(2, &attrs_b);
    // Same hidden attribute value with fresh 256-bit salt produces completely distinct leaf commitment (blocks offline rainbow tables).
    assert_ne!(leaves_a[2], leaves_b[2]);

    let root_a = merkle_root(2, &leaves_a);
    let openings = build_selective_openings(2, &attrs_a, &[1, 3]);
    assert!(verify_selective_disclosure(&root_a, &openings));

    // Disclosed openings NEVER contain unrevealed attribute value or salt bytes.
    for op in &openings {
        assert_ne!(op.idx, 2);
        assert!(!op.key.windows(3).any(|w| w == b"ssn"));
        assert!(!op.value.windows(secret_ssn.len()).any(|w| w == secret_ssn));
        assert_ne!(op.salt, salt2_a);
        for &(_, ref sib) in &op.path {
            assert_ne!(sib, &salt2_a);
        }
    }

    // Tampering a disclosed value or salt fails verification.
    let mut bad_val = openings.clone();
    bad_val[0].value = b"superadmin".to_vec();
    assert!(!verify_selective_disclosure(&root_a, &bad_val));

    let mut bad_salt = openings.clone();
    bad_salt[0].salt[0] ^= 0x01;
    assert!(!verify_selective_disclosure(&root_a, &bad_salt));
}

#[test]
fn release_microbenchmarks_pq_biscuit() {
    let scheme = WotsCshake256;
    let issuer = IssuerSecret::new(b"bench-issuer-seed-32-bytes-00000".to_vec());
    let issuer_pk = issuer.public_key(&scheme);
    let h0_sk = b"bench-holder0-seed-32-bytes-0000".to_vec();
    let h1_sk = b"bench-holder1-seed-32-bytes-0000".to_vec();
    let h0_pk = scheme.pk_of(&h0_sk);
    let h1_pk = scheme.pk_of(&h1_sk);
    let h2_pk = scheme.pk_of(&b"bench-holder2-seed-32-bytes-0000".to_vec());

    // 16 attributes (height 4), disclosing 4 attributes.
    let attrs: Vec<SaltedAttribute> = (0..16usize)
        .map(|i| SaltedAttribute {
            key: format!("attr_{i}").into_bytes(),
            value: format!("val_{i:04}").into_bytes(),
            salt: cshake32(b"BENCH.SALT", &(i as u32).to_be_bytes()),
        })
        .collect();
    let leaves = build_attr_leaves(4, &attrs);
    let attr_root = merkle_root(4, &leaves);
    let nonce = cshake32(b"BENCH.NONCE", b"0");

    // 1024-entry canonical revocation set.
    let raw_rev: Vec<Digest32> = (0..1024u32)
        .map(|i| cshake32(b"BENCH.REV", &i.to_be_bytes()))
        .collect();
    let rev_set = RevocationSet::from_raw(&raw_rev);

    let iters = 100usize;

    let t0 = Instant::now();
    let mut tok0 = issue_root_token(&scheme, &issuer, b"alice".to_vec(), h0_pk.clone(), attr_root, nonce, 0xFF, 9999);
    for _ in 1..iters {
        tok0 = issue_root_token(&scheme, &issuer, b"alice".to_vec(), h0_pk.clone(), attr_root, nonce, 0xFF, 9999);
    }
    let issue_us = t0.elapsed().as_secs_f64() * 1e6 / iters as f64;

    let t1 = Instant::now();
    let mut tok1 = attenuate_token(&scheme, &tok0, &h0_sk, 0x3F, 8000, h1_pk.clone(), b"hop1".to_vec());
    for _ in 1..iters {
        tok1 = attenuate_token(&scheme, &tok0, &h0_sk, 0x3F, 8000, h1_pk.clone(), b"hop1".to_vec());
    }
    let atten_us = t1.elapsed().as_secs_f64() * 1e6 / iters as f64;

    let tok2 = attenuate_token(&scheme, &tok1, &h1_sk, 0x0F, 7000, h2_pk, b"hop2".to_vec());
    let openings = build_selective_openings(4, &attrs, &[0, 5, 10, 15]);

    let t2 = Instant::now();
    for _ in 0..iters {
        let va = verify_presentation(&scheme, &issuer_pk, &rev_set, 5000, &tok2, &openings)
            .expect("bench presentation");
        assert_eq!(va.rights, 0x0F);
    }
    let verify_us = t2.elapsed().as_secs_f64() * 1e6 / iters as f64;

    let rev_iters = 50usize;
    let t3 = Instant::now();
    for _ in 0..rev_iters {
        let rs = RevocationSet::from_raw(&raw_rev);
        assert_eq!(rs.keys().len(), 1024);
    }
    let rev_canon_us = t3.elapsed().as_secs_f64() * 1e6 / rev_iters as f64;

    eprintln!(
        "[pq_biscuit --release bench] issue_root={:.1} us | attenuate_1hop={:.1} us | verify_2hop+4of16_selective+1024rev={:.1} us | rev1024_canon={:.1} us | wire_2hop={} B",
        issue_us,
        atten_us,
        verify_us,
        rev_canon_us,
        tok2.serialize_bytes().len()
    );
}
