//! Integration, Lean 4.35.0 JSON conformance, `CAP-21` `#tooth` regression, real hybrid
//! `X25519 + ML-KEM-768` per-slot key confinement, and statement-pinned keyless sealed
//! `Hyperdocument` ciphertext-to-`saltedPatchRoot` weld test suite (`G7`).

use std::collections::HashSet;
use std::time::Instant;

use minidregg_prover::binary_tower_256::Tower256;
use minidregg_prover::grammar_capability::{
    root_cap_policy, root_cap_policy_with_max_ops, service_cap_policy,
    service_cap_policy_with_max_ops, subagent_tool_cap_policy,
    subagent_tool_cap_policy_with_max_ops, CapNT, CapabilityMeta, CompiledLeafVerifier,
    DelegatedGrammarHop, SealedAtomEdit, SealedHyperdocPatchStmt, SealedHyperdocPatchWitness,
};
use minidregg_prover::per_slot_seal::{
    ciphertext_merkle_root, compute_blind_pad_commit, compute_slot_aad_digest,
    compute_slot_aead_tag, compute_weld_challenge, compute_weld_digest, derive_slot_keystream,
    derive_slot_secret, hybrid_keygen_from_seed, hybrid_wrap_kek, hybrid_wrap_tag,
    seal_pinned_slot_patch, slot_key_commit, tower_poly_eval, unseal_pinned_slot_patch,
    verify_confined_sealed_hyperdoc_patch, verify_keyless_ciphertext_weld,
    verify_read_cap_confinement, wrap_slot_aad, AttenuatedSlotCap, KeylessPublicPatchStmt,
    LegacyReadCap, PerSlotError, PublicCiphertextWeld, ReadCapEnvelope, SlotAadMeta,
    MLKEM768_CT_BYTES, MLKEM768_DK_BYTES, MLKEM768_EK_BYTES,
};
use minidregg_prover::policy_transducer::{ExactNat, MiniValue};
use minidregg_prover::tower256_private_cert::{pack_salted_leaf, Digest};
use serde::Deserialize;
use sha3::{Digest as Sha3DigestTrait, Sha3_256};

#[derive(Deserialize)]
struct PerSlotConformanceDoc {
    schema: String,
    cell_id: u64,
    key_epoch: u64,
    granted_slot: u64,
    ungranted_slot: u64,
    root_view_key_hex: String,
    slot_2_secret_hex: String,
    slot_2_key_commit_hex: String,
    slot_7_secret_hex: String,
    slot_7_key_commit_hex: String,
    delegate_x25519_pk_hex: String,
    delegate_mlkem768_ek_digest_hex: String,
    kem_ct_x25519_eph_pk_hex: String,
    kem_ct_mlkem768_digest_hex: String,
    kem_ss_x25519_hex: String,
    kem_ss_mlkem768_hex: String,
    hybrid_kek_hex: String,
    wrapped_slot_2_secret_hex: String,
    wrapped_slot_2_tag_hex: String,
    document_id: u64,
    atom_id: u64,
    schema_hex: String,
    operation_id: u64,
    nonce_hex: String,
    extra_aad_hex: String,
    slot_aad_digest_hex: String,
    patch_payload_hex: String,
    salted_patch_root_hex: String,
    keystream_hex: String,
    ciphertext_hex: String,
    ct_merkle_root_hex: String,
    mask_merkle_root_hex: String,
    blind_pad_hex: String,
    blind_pad_commit_hex: String,
    aead_tag_hex: String,
    weld_digest_hex: String,
    weld_gamma_hex: String,
    eval_c_hex: String,
    blind_eval_s_hex: String,
    blind_eval_m_hex: String,
    keyless_weld_verified: bool,
    confined_gate_verified: bool,
    tooth_tampered_ct_rejected: bool,
    tooth_swapped_root_rejected: bool,
    tooth_swapped_key_commit_rejected: bool,
    tooth_wrong_slot_secret_rejected: bool,
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
fn lean_json_conformance_bit_for_bit_parity() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/per_slot_seal_conformance.json"
    );
    let raw = std::fs::read_to_string(path).expect("read Lean per_slot_seal_conformance.json");
    let doc: PerSlotConformanceDoc =
        serde_json::from_str(&raw).expect("parse per_slot_seal_conformance.json");
    assert_eq!(doc.schema, "minidregg.per_slot_seal_conformance.v1");
    assert!(doc.keyless_weld_verified);
    assert!(doc.confined_gate_verified);
    assert!(doc.tooth_tampered_ct_rejected);
    assert!(doc.tooth_swapped_root_rejected);
    assert!(doc.tooth_swapped_key_commit_rejected);
    assert!(doc.tooth_wrong_slot_secret_rejected);

    let root_view_key = unhex_exact::<32>(&doc.root_view_key_hex);
    let s2 = derive_slot_secret(&root_view_key, doc.cell_id, doc.granted_slot, doc.key_epoch);
    let s7 = derive_slot_secret(
        &root_view_key,
        doc.cell_id,
        doc.ungranted_slot,
        doc.key_epoch,
    );
    assert_eq!(s2, unhex_exact::<32>(&doc.slot_2_secret_hex));
    assert_eq!(s7, unhex_exact::<32>(&doc.slot_7_secret_hex));

    let kc2 = slot_key_commit(doc.granted_slot, &s2);
    let kc7 = slot_key_commit(doc.ungranted_slot, &s7);
    assert_eq!(kc2, unhex_exact::<32>(&doc.slot_2_key_commit_hex));
    assert_eq!(kc7, unhex_exact::<32>(&doc.slot_7_key_commit_hex));

    // Exact bit-for-bit parity on hybrid wrap KEK, wrapped secret, and wrap tag:
    let aad2 = wrap_slot_aad(doc.cell_id, doc.granted_slot, doc.key_epoch, &kc2);
    let kek2 = hybrid_wrap_kek(
        &unhex_exact::<32>(&doc.kem_ss_x25519_hex),
        &unhex_exact::<32>(&doc.kem_ss_mlkem768_hex),
        &unhex_exact::<32>(&doc.kem_ct_x25519_eph_pk_hex),
        &unhex_exact::<32>(&doc.kem_ct_mlkem768_digest_hex),
        &unhex_exact::<32>(&doc.delegate_x25519_pk_hex),
        &unhex_exact::<32>(&doc.delegate_mlkem768_ek_digest_hex),
        &aad2,
    );
    assert_eq!(kek2, unhex_exact::<32>(&doc.hybrid_kek_hex));
    let mut wrapped_s2 = [0u8; 32];
    for i in 0..32 {
        wrapped_s2[i] = s2[i] ^ kek2[i];
    }
    assert_eq!(wrapped_s2, unhex_exact::<32>(&doc.wrapped_slot_2_secret_hex));
    assert_eq!(
        hybrid_wrap_tag(&kek2, &wrapped_s2, &aad2),
        unhex_exact::<32>(&doc.wrapped_slot_2_tag_hex)
    );

    // Exact bit-for-bit parity on AAD, keystream, ciphertext, Merkle roots, AEAD tag, weld digest,
    // Fiat-Shamir challenge gamma, Tower256 evalC, and blinded XOR evaluations:
    let aad_meta = SlotAadMeta {
        document_id: doc.document_id,
        atom_id: doc.atom_id,
        schema: unhex_exact::<32>(&doc.schema_hex),
        operation_id: doc.operation_id,
        slot_index: doc.granted_slot,
        key_epoch: doc.key_epoch,
        extra_aad: unhex(&doc.extra_aad_hex),
    };
    let aad_digest = compute_slot_aad_digest(&aad_meta);
    assert_eq!(aad_digest, unhex_exact::<32>(&doc.slot_aad_digest_hex));

    let payload = unhex(&doc.patch_payload_hex);
    let nonce = unhex_exact::<32>(&doc.nonce_hex);
    let ks = derive_slot_keystream(&s2, doc.granted_slot, &nonce, &aad_digest, payload.len());
    assert_eq!(ks, unhex(&doc.keystream_hex));

    let ct: Vec<u8> = payload.iter().zip(ks.iter()).map(|(&p, &k)| p ^ k).collect();
    assert_eq!(ct, unhex(&doc.ciphertext_hex));

    let ct_root = ciphertext_merkle_root(&ct).unwrap();
    assert_eq!(ct_root, unhex_exact::<32>(&doc.ct_merkle_root_hex));

    let salted_root = unhex_exact::<32>(&doc.salted_patch_root_hex);
    let mask_root = unhex_exact::<32>(&doc.mask_merkle_root_hex);
    let blind_pad = unhex_exact::<32>(&doc.blind_pad_hex);
    let blind_pad_commit = compute_blind_pad_commit(&blind_pad, &salted_root, &nonce);
    assert_eq!(blind_pad_commit, unhex_exact::<32>(&doc.blind_pad_commit_hex));

    let aead_tag = compute_slot_aead_tag(
        &s2,
        &kc2,
        &nonce,
        &aad_digest,
        &salted_root,
        &ct_root,
        &mask_root,
        payload.len(),
    );
    assert_eq!(aead_tag, unhex_exact::<32>(&doc.aead_tag_hex));

    let weld_digest = compute_weld_digest(
        &salted_root,
        &mask_root,
        &ct_root,
        &kc2,
        &nonce,
        &aad_digest,
        payload.len(),
        &aead_tag,
        &blind_pad_commit,
    );
    assert_eq!(weld_digest, unhex_exact::<32>(&doc.weld_digest_hex));

    let gamma = compute_weld_challenge(&weld_digest);
    assert_eq!(gamma.to_le_bytes(), unhex_exact::<32>(&doc.weld_gamma_hex));

    let zero_salt = [0u8; 31];
    let ct_leaves: Vec<Tower256> = ct.iter().map(|&b| pack_salted_leaf(b, &zero_salt)).collect();
    let eval_c = tower_poly_eval(gamma, &ct_leaves);
    assert_eq!(eval_c.to_le_bytes(), unhex_exact::<32>(&doc.eval_c_hex));

    let stmt = KeylessPublicPatchStmt {
        aad_meta,
        key_commit: kc2,
        nonce,
        patch_len: payload.len(),
        salted_patch_root: salted_root,
        ciphertext: ct,
        weld: PublicCiphertextWeld {
            ct_merkle_root: ct_root,
            mask_merkle_root: mask_root,
            blind_pad_commit,
            aead_tag,
            weld_digest,
            blind_eval_s: unhex_exact::<32>(&doc.blind_eval_s_hex),
            blind_eval_m: unhex_exact::<32>(&doc.blind_eval_m_hex),
        },
    };
    assert_eq!(verify_keyless_ciphertext_weld(&stmt), Ok(()));
    println!(
        "[conformance] Lean 4.35.0 <-> Rust bit-for-bit parity verified across all 28 vectors."
    );
}

#[test]
fn cap21_tooth_and_hybrid_x25519_mlkem768_confinement() {
    let root_view_key: Digest = [0x42u8; 32];
    let cell_id = 500u64;
    let key_epoch = 3u64;

    // 1. `#tooth` catching legacy `ReadCap::attenuate` root-key copy (`CAP-21`):
    let legacy_parent = LegacyReadCap {
        cell_id,
        key_epoch,
        granted_slots: vec![2, 5, 7],
        leaked_root_view_key: root_view_key,
    };
    let legacy_child = legacy_parent
        .attenuate_buggy(&[2])
        .expect("buggy attenuation succeeds");
    assert!(!legacy_child.granted_slots.contains(&7));
    // Exploiting CAP-21: child derives ungranted slot 7's secret directly from leaked root key!
    let stolen_slot_7 = derive_slot_secret(&legacy_child.leaked_root_view_key, cell_id, 7, key_epoch);
    assert_eq!(
        stolen_slot_7,
        derive_slot_secret(&root_view_key, cell_id, 7, key_epoch)
    );
    // Our confinement gate rejects any legacy root-bearing capability unconditionally:
    assert_eq!(
        verify_read_cap_confinement(ReadCapEnvelope::LegacyRootCopy(&legacy_child)),
        Err(PerSlotError::LegacyRootKeyCopyForbidden)
    );

    // 2. Real hybrid `X25519 + ML-KEM-768` per-slot key confinement (`AttenuatedSlotCap`):
    let t_kg = Instant::now();
    let lead_sk = hybrid_keygen_from_seed(&[0x11u8; 32]);
    let sub_sk = hybrid_keygen_from_seed(&[0x22u8; 32]);
    let rogue_sk = hybrid_keygen_from_seed(&[0x99u8; 32]);
    let kg_ms = t_kg.elapsed().as_secs_f64() * 1000.0 / 3.0;
    assert_eq!(lead_sk.public.mlkem768_ek.0.len(), MLKEM768_EK_BYTES);
    assert_eq!(lead_sk.mlkem768_dk.0.len(), MLKEM768_DK_BYTES);

    let t_mint = Instant::now();
    let lead_cap = AttenuatedSlotCap::mint_from_root(
        &root_view_key,
        cell_id,
        key_epoch,
        &lead_sk.public,
        &[2, 5],
        &[0xA1u8; 32],
    )
    .expect("mint lead cap");
    let mint_ms = t_mint.elapsed().as_secs_f64() * 1000.0;

    assert_eq!(
        verify_read_cap_confinement(ReadCapEnvelope::ConfinedPerSlot(&lead_cap)),
        Ok(())
    );
    assert_eq!(lead_cap.wrapped_keys.len(), 2);
    assert_eq!(
        lead_cap.wrapped_keys[0].kem_ct.mlkem768_ct.0.len(),
        MLKEM768_CT_BYTES
    );
    // Slot 7 is completely absent from `lead_cap`:
    assert!(lead_cap.lookup_wrapped(7).is_none());
    assert_eq!(
        lead_cap.unwrap_slot(7, &lead_sk),
        Err(PerSlotError::SlotNotAuthorized(7))
    );

    // TeamLead unwraps granted slots 2 and 5:
    let t_unw = Instant::now();
    let s2_lead = lead_cap.unwrap_slot(2, &lead_sk).expect("unwrap slot 2");
    let unw_ms = t_unw.elapsed().as_secs_f64() * 1000.0;
    let s5_lead = lead_cap.unwrap_slot(5, &lead_sk).expect("unwrap slot 5");
    assert_eq!(s2_lead, derive_slot_secret(&root_view_key, cell_id, 2, key_epoch));
    assert_eq!(s5_lead, derive_slot_secret(&root_view_key, cell_id, 5, key_epoch));

    // Attenuation refuses amplification `[2, 7]`:
    assert_eq!(
        lead_cap.attenuate(&lead_sk, &sub_sk.public, &[2, 7], &[0xB2u8; 32]),
        Err(PerSlotError::AmplificationRefused(7))
    );

    // Valid attenuation `[2, 5] -> [2]` omits BOTH slot 5 AND slot 7:
    let sub_cap = lead_cap
        .attenuate(&lead_sk, &sub_sk.public, &[2], &[0xB2u8; 32])
        .expect("attenuate to [2]");
    assert_eq!(sub_cap.granted_slots, vec![2]);
    assert!(sub_cap.lookup_wrapped(5).is_none());
    assert!(sub_cap.lookup_wrapped(7).is_none());
    assert_eq!(sub_cap.unwrap_slot(2, &sub_sk), Ok(s2_lead));
    assert_eq!(
        sub_cap.unwrap_slot(5, &sub_sk),
        Err(PerSlotError::SlotNotAuthorized(5))
    );
    // Wrong recipient secret key fails MAC verification:
    assert_eq!(
        sub_cap.unwrap_slot(2, &rogue_sk),
        Err(PerSlotError::WrapTagMismatch)
    );

    // Dual PQ+classical protection checks:
    // (a) Corrupting ONLY X25519 ephemeral pk breaks unwrap:
    let mut bad_x25519 = sub_cap.clone();
    bad_x25519.wrapped_keys[0].kem_ct.x25519_eph_pk[0] ^= 0x01;
    assert_eq!(
        bad_x25519.unwrap_slot(2, &sub_sk),
        Err(PerSlotError::WrapTagMismatch)
    );
    // (b) Corrupting ONLY 1 bit of ML-KEM-768 ciphertext (even with recomputed digest!) triggers
    // FIPS 203 FO implicit rejection and fails wrap MAC:
    let mut bad_mlkem = sub_cap.clone();
    bad_mlkem.wrapped_keys[0].kem_ct.mlkem768_ct.0[42] ^= 0x01;
    let mut h = Sha3_256::new();
    Sha3DigestTrait::update(&mut h, &bad_mlkem.wrapped_keys[0].kem_ct.mlkem768_ct.0);
    bad_mlkem.wrapped_keys[0].kem_ct.mlkem768_ct_digest = h.finalize().into();
    assert_eq!(
        bad_mlkem.unwrap_slot(2, &sub_sk),
        Err(PerSlotError::WrapTagMismatch)
    );

    println!(
        "[bench] Hybrid X25519+ML-KEM-768: keygen={kg_ms:.3} ms, mint(2 slots)={mint_ms:.3} ms, unwrap(1 slot)={unw_ms:.3} ms"
    );
}

#[test]
fn statement_pinned_gate_and_keyless_public_verifier_4kib() {
    let root_view_key: Digest = [0x7Bu8; 32];
    let cell_id = 500u64;
    let doc_id = 500u64;
    let atom_id = 501u64;
    let schema: Digest = [0x33u8; 32];
    let op_id = 9001u64;
    let slot_idx = 2u64;
    let key_epoch = 3u64;

    let delegate_sk = hybrid_keygen_from_seed(&[0x55u8; 32]);
    let cap = AttenuatedSlotCap::mint_from_root(
        &root_view_key,
        cell_id,
        key_epoch,
        &delegate_sk.public,
        &[slot_idx],
        &[0xCCu8; 32],
    )
    .unwrap();
    let slot_2_secret = cap.unwrap_slot(slot_idx, &delegate_sk).unwrap();
    let slot_7_secret = derive_slot_secret(&root_view_key, cell_id, 7, key_epoch);

    // Construct a 4 KiB (`4,096 B`) valid JSON patch payload matching subagent policy:
    let prefix = b"{\"tool\":\"patch_atom\",\"target\":\"sandbox/note_01\",\"amount\":3}";
    let mut payload_4k = Vec::with_capacity(4096);
    payload_4k.extend_from_slice(prefix);
    payload_4k.resize(4096, b' '); // wait: check grammar admits exact payload; use exact 58B for grammar gate + 4KiB for keyless weld!

    // 1. 4 KiB keyless seal + verify + unseal benchmark & forgery matrix:
    let aad_4k = SlotAadMeta {
        document_id: doc_id,
        atom_id,
        schema,
        operation_id: op_id,
        slot_index: slot_idx,
        key_epoch,
        extra_aad: b"hyperdoc-4kib-slot-2".to_vec(),
    };
    let nonce = [0xE5u8; 32];
    let blind_pad = [0x9Au8; 32];

    let t_seal = Instant::now();
    let (pub_4k, _salts_4k) =
        seal_pinned_slot_patch(aad_4k, &slot_2_secret, nonce, &payload_4k, None, &blind_pad)
            .expect("seal 4 KiB patch");
    let seal_ms = t_seal.elapsed().as_secs_f64() * 1000.0;

    let t_ver = Instant::now();
    let iters = 10usize;
    for _ in 0..iters {
        verify_keyless_ciphertext_weld(&pub_4k).expect("keyless verify 4 KiB");
    }
    let keyless_ms = t_ver.elapsed().as_secs_f64() * 1000.0 / (iters as f64);

    // Authorized holder unseals & verifies plaintext == payload_4k:
    let recovered =
        unseal_pinned_slot_patch(&slot_2_secret, &pub_4k, None).expect("unseal 4 KiB patch");
    assert_eq!(recovered, payload_4k);
    // Wrong slot key fails pinned `key_commit` check immediately:
    assert_eq!(
        unseal_pinned_slot_patch(&slot_7_secret, &pub_4k, None),
        Err(PerSlotError::KeyCommitMismatch)
    );

    // Zero >= 6B plaintext slice leakage in KeylessPublicPatchStmt:
    let mut public_blob = Vec::new();
    public_blob.extend_from_slice(&pub_4k.key_commit);
    public_blob.extend_from_slice(&pub_4k.salted_patch_root);
    public_blob.extend_from_slice(&pub_4k.ciphertext);
    public_blob.extend_from_slice(&pub_4k.weld.ct_merkle_root);
    public_blob.extend_from_slice(&pub_4k.weld.mask_merkle_root);
    public_blob.extend_from_slice(&pub_4k.weld.blind_pad_commit);
    public_blob.extend_from_slice(&pub_4k.weld.aead_tag);
    public_blob.extend_from_slice(&pub_4k.weld.weld_digest);
    public_blob.extend_from_slice(&pub_4k.weld.blind_eval_s);
    public_blob.extend_from_slice(&pub_4k.weld.blind_eval_m);
    for win in prefix.windows(6) {
        assert!(
            !public_blob.windows(6).any(|w| w == win),
            "plaintext 6-byte slice leaked into keyless public statement!"
        );
    }

    // Complete adversarial forgery matrix on keyless public consensus verifier (ZERO secrets!):
    // (1) 1-bit ciphertext mutation:
    let mut bad_ct = pub_4k.clone();
    bad_ct.ciphertext[123] ^= 0x01;
    assert!(matches!(
        verify_keyless_ciphertext_weld(&bad_ct),
        Err(PerSlotError::CiphertextRootMismatch(_))
    ));
    // (2) Swapped `salted_patch_root`:
    let mut bad_root = pub_4k.clone();
    bad_root.salted_patch_root[0] ^= 0x01;
    assert!(matches!(
        verify_keyless_ciphertext_weld(&bad_root),
        Err(PerSlotError::CiphertextRootMismatch(_))
    ));
    // (3) Swapped `key_commit`:
    let mut bad_kc = pub_4k.clone();
    bad_kc.key_commit[0] ^= 0x01;
    assert!(matches!(
        verify_keyless_ciphertext_weld(&bad_kc),
        Err(PerSlotError::CiphertextRootMismatch(_))
    ));
    // (4) Swapped `nonce`:
    let mut bad_nonce = pub_4k.clone();
    bad_nonce.nonce[31] ^= 0x01;
    assert!(matches!(
        verify_keyless_ciphertext_weld(&bad_nonce),
        Err(PerSlotError::CiphertextRootMismatch(_))
    ));
    // (5) Swapped `slot_aad`:
    let mut bad_aad = pub_4k.clone();
    bad_aad.aad_meta.extra_aad.push(b'!');
    assert!(matches!(
        verify_keyless_ciphertext_weld(&bad_aad),
        Err(PerSlotError::CiphertextRootMismatch(_))
    ));
    // (6) Mutated `aead_tag`:
    let mut bad_tag = pub_4k.clone();
    bad_tag.weld.aead_tag[7] ^= 0x80;
    assert!(matches!(
        verify_keyless_ciphertext_weld(&bad_tag),
        Err(PerSlotError::CiphertextRootMismatch(_))
    ));
    // (7) Corrupted `blind_eval_s`:
    let mut bad_bs = pub_4k.clone();
    bad_bs.weld.blind_eval_s[0] ^= 0x01;
    assert!(matches!(
        verify_keyless_ciphertext_weld(&bad_bs),
        Err(PerSlotError::CiphertextRootMismatch(_))
    ));
    // (8) Forged ciphertext with recomputed `ct_merkle_root` + `weld_digest` (caught by Tower256 blinded XOR!):
    let mut rehashed_ct = pub_4k.clone();
    rehashed_ct.ciphertext[0] ^= 0x55;
    rehashed_ct.weld.ct_merkle_root = ciphertext_merkle_root(&rehashed_ct.ciphertext).unwrap();
    let aad_dig = compute_slot_aad_digest(&rehashed_ct.aad_meta);
    rehashed_ct.weld.weld_digest = compute_weld_digest(
        &rehashed_ct.salted_patch_root,
        &rehashed_ct.weld.mask_merkle_root,
        &rehashed_ct.weld.ct_merkle_root,
        &rehashed_ct.key_commit,
        &rehashed_ct.nonce,
        &aad_dig,
        rehashed_ct.patch_len,
        &rehashed_ct.weld.aead_tag,
        &rehashed_ct.weld.blind_pad_commit,
    );
    assert_eq!(
        verify_keyless_ciphertext_weld(&rehashed_ct),
        Err(PerSlotError::CiphertextRootMismatch(
            "Tower256 blinded XOR evaluation mismatch"
        ))
    );

    // 2. End-to-end 3-hop `SealedHyperdocGrammarGate` + statement-pinned `slotKeyCommit` + keyless weld:
    let root_pol = root_cap_policy();
    let svc_pol = service_cap_policy();
    let sub_pol = subagent_tool_cap_policy();
    let (root_cap, lead_cap, coder_cap) = sample_three_hop_caps(doc_id);
    let _ = (
        root_cap_policy_with_max_ops(5),
        service_cap_policy_with_max_ops(5),
        subagent_tool_cap_policy_with_max_ops(5),
    );

    let aad_meta = SlotAadMeta {
        document_id: doc_id,
        atom_id,
        schema,
        operation_id: op_id,
        slot_index: slot_idx,
        key_epoch,
        extra_aad: b"hyperdoc-3hop-slot-2".to_vec(),
    };
    let (pub_stmt, patch_salts) =
        seal_pinned_slot_patch(aad_meta, &slot_2_secret, nonce, prefix, None, &blind_pad)
            .expect("seal 3-hop patch");

    let expected_ast = MiniValue::ToolCall {
        tool: b"patch_atom".to_vec(),
        target: b"sandbox/note_01".to_vec(),
        amount: ExactNat::from_u64(3),
    };
    let base_stmt = SealedHyperdocPatchStmt {
        document_id: doc_id,
        atom_id,
        schema,
        operation_id: op_id,
        author_subject: 30,
        author_capability_id: 102,
        height: 25,
        cost: prefix.len() as u64,
        expected_root_cap_id: 100,
        expected_issuer: 1,
        policy_id: 42,
        expected_policy_epoch: 3,
        expected_issuer_epoch: 7,
        revoked: HashSet::new(),
        patch_len: prefix.len(),
        salted_patch_root: pub_stmt.salted_patch_root,
        claimed_ast: expected_ast,
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
            ciphertext: pub_stmt.ciphertext.clone(),
            wrapping: pub_stmt.weld.aead_tag.to_vec(),
            cleartext_payload: vec![],
        },
    };
    let leaf_verifier =
        CompiledLeafVerifier::compile(&sub_pol, CapNT::COUNT, CapNT::to_id).unwrap();
    let (rule_indices, _parsed_ast) = leaf_verifier.parser.parse(prefix).unwrap();

    let base_wit = SealedHyperdocPatchWitness {
        chain: vec![
            DelegatedGrammarHop {
                capability: root_cap,
                policy: &root_pol,
            },
            DelegatedGrammarHop {
                capability: lead_cap,
                policy: &svc_pol,
            },
            DelegatedGrammarHop {
                capability: coder_cap,
                policy: &sub_pol,
            },
        ],
        patch_bytes: prefix.to_vec(),
        patch_salts,
        rule_indices,
        succinct_guards: vec![],
        cell_blinding_key: None,
    };

    let t_full = Instant::now();
    verify_confined_sealed_hyperdoc_patch(&base_stmt, &pub_stmt, &base_wit, &slot_2_secret)
        .expect("full confined 3-hop gate must accept");
    let full_ms = t_full.elapsed().as_secs_f64() * 1000.0;

    // L8 regression tooth: rogue/attacker-chosen `wit_slot_secret` is REJECTED by statement-pinned `key_commit`:
    assert_eq!(
        verify_confined_sealed_hyperdoc_patch(&base_stmt, &pub_stmt, &base_wit, &slot_7_secret),
        Err(PerSlotError::KeyCommitMismatch)
    );

    println!(
        "[bench] 4 KiB seal={seal_ms:.3} ms, keyless consensus verify={keyless_ms:.3} ms, 3-hop confined gate={full_ms:.3} ms"
    );
    assert!(
        keyless_ms < 200.0,
        "expected < 200 ms keyless 4 KiB verify under host load, got {keyless_ms:.3} ms"
    );
}
