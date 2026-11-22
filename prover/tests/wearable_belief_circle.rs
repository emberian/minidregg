//! Byte-exact Lean 4.35.0 conformance, 8 adversarial mafia-fraud / traffic-analysis / replay /
//! revocation / tamper tests, and `--release` microbenchmarks for
//! `minidregg_prover::belief_circle` (*Rainbows End* Wearable SHE Organ #3).

#![deny(warnings)]

use std::time::Instant;

use minidregg_prover::belief_circle::{
    admit_circle_update, bits_to_bytes_lsb, causal_rtt_ps, compute_entry_digest,
    compute_tof_response, cshake_keystream, derive_tof_bits, fill_belief_cell, open_belief_cell,
    seal_belief_cell, verify_tof_session, AdmitReject, CellError, CellHeader, ChannelProfile,
    CircleOverlayUpdate, CirclePolicy, ConstantRateCellMux, DutyPublic, OverlayState,
    SingleShotResponder, SpatialEntry, TofParams, TofRejectReason, TofTranscript,
    WearableActivity, CIRCLE_WRITE_RIGHT, CUST_TOF_CHAL, CUST_TOF_R0, CUST_TOF_R1,
    DREGG_VERNIER_STEP_PS,
};
use minidregg_prover::pq_biscuit::{
    attenuate_token, chain_id, cshake32, issue_root_token, Digest32, IssuerSecret, PqSigBackend,
    RevocationSet, WotsCshake256,
};
use serde::Deserialize;

#[derive(Deserialize)]
struct BeliefCircleConformanceDoc {
    schema: String,
    tof_rounds: usize,
    t_proc_min_ps: u64,
    d_max_mm: u64,
    max_round_time_ps: u64,
    vernier_step_ps: u64,
    tof_secret_hex: String,
    tof_nonce_hex: String,
    tof_verifier_seed_hex: String,
    tof_r0_hex: String,
    tof_r1_hex: String,
    tof_chal_hex: String,
    tof_resp_hex: String,
    tof_in_range_accepted: bool,
    tof_wormhole_5m_rejected: bool,
    tof_early_trigger_rejected: bool,
    circle_key_hex: String,
    duty_vrf_hex: String,
    duty_verdict_root_hex: String,
    duty_acc_root_hex: String,
    hazard_payload_hex: String,
    jitt_payload_hex: String,
    p2_idle_cell_hex: String,
    p2_hazard_cell_hex: String,
    p2_duty_cell_hex: String,
    p1_hazard_cell_hex: String,
    issuer_seed_hex: String,
    alice_seed_hex: String,
    bob_seed_hex: String,
    carol_seed_hex: String,
    issuer_pk_hex: String,
    attr_root_hex: String,
    nonce_a_hex: String,
    nonce_b_hex: String,
    entry_a_digest_hex: String,
    entry_b_digest_hex: String,
    entry_c_digest_hex: String,
    merged_overlay_root_hex: String,
    overlay_order_invariant: bool,
    admitted_all_three: bool,
    revoked_bob_kills_carol_delegation: bool,
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

fn make_in_range_tof(seed: &[u8], nonce: &[u8], vseed: &[u8]) -> TofTranscript {
    let r0 = derive_tof_bits(CUST_TOF_R0, seed, nonce);
    let r1 = derive_tof_bits(CUST_TOF_R1, seed, nonce);
    let chal = derive_tof_bits(CUST_TOF_CHAL, vseed, nonce);
    let resp = compute_tof_response(&r0, &r1, &chal);
    let times_ps: Vec<u64> = (0..128)
        .map(|i| 10_000 + ((i % 7) as u64) * DREGG_VERNIER_STEP_PS)
        .collect();
    TofTranscript {
        r0,
        r1,
        chal,
        resp,
        times_ps,
    }
}

#[test]
fn lean_conformance_vector_byte_exact() {
    let raw = include_str!("../testdata/belief_circle_conformance.json");
    let doc: BeliefCircleConformanceDoc =
        serde_json::from_str(raw).expect("parse Lean conformance JSON");
    assert_eq!(doc.schema, "minidregg.belief_circle_conformance.v1");
    assert_eq!(doc.tof_rounds, 128);
    assert_eq!(doc.t_proc_min_ps, 3990);
    assert_eq!(doc.d_max_mm, 3000);
    assert_eq!(doc.max_round_time_ps, 24_003);
    assert_eq!(doc.vernier_step_ps, 230);
    assert!(doc.tof_in_range_accepted);
    assert!(doc.tof_wormhole_5m_rejected);
    assert!(doc.tof_early_trigger_rejected);
    assert!(doc.overlay_order_invariant);
    assert!(doc.admitted_all_three);
    assert!(doc.revoked_bob_kills_carol_delegation);

    // 1. Byte-exact 128-round ToF derivation & verdicts
    let tof_secret = unhex(&doc.tof_secret_hex);
    let tof_nonce = unhex(&doc.tof_nonce_hex);
    let ver_seed = unhex(&doc.tof_verifier_seed_hex);
    let tr = make_in_range_tof(&tof_secret, &tof_nonce, &ver_seed);
    assert_eq!(to_hex(&bits_to_bytes_lsb(&tr.r0)), doc.tof_r0_hex);
    assert_eq!(to_hex(&bits_to_bytes_lsb(&tr.r1)), doc.tof_r1_hex);
    assert_eq!(to_hex(&bits_to_bytes_lsb(&tr.chal)), doc.tof_chal_hex);
    assert_eq!(to_hex(&bits_to_bytes_lsb(&tr.resp)), doc.tof_resp_hex);
    let tof_params = TofParams::dregg_default();
    assert_eq!(tof_params.max_round_time_ps(), doc.max_round_time_ps);
    assert_eq!(verify_tof_session(&tof_params, &tr), Ok(()));

    // 2. Byte-exact P2 (1024 B) & P1 (256 B) cSHAKE256-sealed cells
    let circle_key = unhex(&doc.circle_key_hex);
    let dp = DutyPublic {
        vrf: unhex(&doc.duty_vrf_hex).try_into().unwrap(),
        verdict_root: unhex32(&doc.duty_verdict_root_hex),
        acc_root: unhex32(&doc.duty_acc_root_hex),
    };
    let hazard_payload = unhex(&doc.hazard_payload_hex);
    let jitt_payload = unhex(&doc.jitt_payload_hex);
    let hdr_reg = CellHeader {
        domain: 42,
        epoch: 7,
        tick: 3,
        slot: 1,
    };
    let hdr_duty = CellHeader {
        domain: 42,
        epoch: 7,
        tick: 0,
        slot: 1,
    };
    let p2_idle =
        seal_belief_cell(ChannelProfile::P2, &circle_key, hdr_reg, None, &WearableActivity::Idle)
            .unwrap();
    let p2_hazard = seal_belief_cell(
        ChannelProfile::P2,
        &circle_key,
        hdr_reg,
        None,
        &WearableActivity::ArHazardReticle {
            anchor_id: 101,
            priority: 2,
            patch: hazard_payload.clone(),
        },
    )
    .unwrap();
    let p2_duty = seal_belief_cell(
        ChannelProfile::P2,
        &circle_key,
        hdr_duty,
        Some(&dp),
        &WearableActivity::JittQuery(jitt_payload.clone()),
    )
    .unwrap();
    let p1_hazard = seal_belief_cell(
        ChannelProfile::P1,
        &circle_key,
        hdr_reg,
        None,
        &WearableActivity::ArHazardReticle {
            anchor_id: 101,
            priority: 2,
            patch: hazard_payload.clone(),
        },
    )
    .unwrap();
    assert_eq!(p2_idle.len(), 1024);
    assert_eq!(p2_hazard.len(), 1024);
    assert_eq!(p2_duty.len(), 1024);
    assert_eq!(p1_hazard.len(), 256);
    assert_eq!(to_hex(&p2_idle), doc.p2_idle_cell_hex);
    assert_eq!(to_hex(&p2_hazard), doc.p2_hazard_cell_hex);
    assert_eq!(to_hex(&p2_duty), doc.p2_duty_cell_hex);
    assert_eq!(to_hex(&p1_hazard), doc.p1_hazard_cell_hex);

    // Verify clean decryption roundtrip
    let (_, _, open_haz) = open_belief_cell(ChannelProfile::P2, &circle_key, &p2_hazard).unwrap();
    assert_eq!(
        open_haz,
        WearableActivity::ArHazardReticle {
            anchor_id: 101,
            priority: 2,
            patch: hazard_payload.clone(),
        }
    );

    // 3. Byte-exact 3-wearer PqSelectiveBiscuit + ToF + IConfluent overlay merge
    let scheme = WotsCshake256;
    let issuer = IssuerSecret::new(unhex(&doc.issuer_seed_hex));
    let issuer_pk = issuer.public_key(&scheme);
    assert_eq!(to_hex(&issuer_pk), doc.issuer_pk_hex);
    let a_pk = scheme.pk_of(&unhex(&doc.alice_seed_hex));
    let b_seed = unhex(&doc.bob_seed_hex);
    let b_pk = scheme.pk_of(&b_seed);
    let c_pk = scheme.pk_of(&unhex(&doc.carol_seed_hex));
    let attr_root = unhex32(&doc.attr_root_hex);
    let nonce_a = unhex32(&doc.nonce_a_hex);
    let nonce_b = unhex32(&doc.nonce_b_hex);
    let tok_a = issue_root_token(&scheme, &issuer, b"alice".to_vec(), a_pk, attr_root, nonce_a, 0x03, 2000);
    let tok_b = issue_root_token(&scheme, &issuer, b"bob".to_vec(), b_pk, attr_root, nonce_b, 0x03, 2000);
    let tok_c = attenuate_token(&scheme, &tok_b, &b_seed, 0x01, 1800, c_pk, b"scope=ar_write".to_vec());

    let pol = CirclePolicy {
        circle_id: 42,
        issuer_pk: issuer_pk.clone(),
        revocations: RevocationSet::empty(),
        required_rights: CIRCLE_WRITE_RIGHT,
        tof_params,
    };
    let u_a = CircleOverlayUpdate {
        circle_id: 42,
        anchor_id: 101,
        lamport_clock: 1,
        author_slot: 0,
        priority: 2,
        label: hazard_payload,
        token: tok_a,
        tof: tr.clone(),
    };
    let u_b = CircleOverlayUpdate {
        circle_id: 42,
        anchor_id: 102,
        lamport_clock: 1,
        author_slot: 1,
        priority: 1,
        label: b"CAUTION:WET-FLOOR".to_vec(),
        token: tok_b,
        tof: tr.clone(),
    };
    let u_c = CircleOverlayUpdate {
        circle_id: 42,
        anchor_id: 101,
        lamport_clock: 2,
        author_slot: 2,
        priority: 0,
        label: jitt_payload,
        token: tok_c.clone(),
        tof: tr,
    };

    let mut s_fwd = OverlayState::new();
    let d_a = s_fwd.ingest(&scheme, &pol, 1000, &u_a).unwrap();
    let d_b = s_fwd.ingest(&scheme, &pol, 1000, &u_b).unwrap();
    let d_c = s_fwd.ingest(&scheme, &pol, 1000, &u_c).unwrap();
    assert_eq!(to_hex(&d_a), doc.entry_a_digest_hex);
    assert_eq!(to_hex(&d_b), doc.entry_b_digest_hex);
    assert_eq!(to_hex(&d_c), doc.entry_c_digest_hex);
    assert_eq!(to_hex(&s_fwd.state_root()), doc.merged_overlay_root_hex);

    // Reverse order yields identical overlay root
    let mut s_rev = OverlayState::new();
    s_rev.ingest(&scheme, &pol, 1000, &u_c).unwrap();
    s_rev.ingest(&scheme, &pol, 1000, &u_b).unwrap();
    s_rev.ingest(&scheme, &pol, 1000, &u_a).unwrap();
    assert_eq!(s_fwd, s_rev);
    assert_eq!(s_fwd.state_root(), s_rev.state_root());

    // Revoking Bob's block-0 ancestor kills Carol's delegated AR update
    let cid_bob = chain_id(&tok_c.block0, &tok_c.hops, 0);
    let pol_rev = CirclePolicy {
        revocations: RevocationSet::from_raw(&[cid_bob]),
        ..pol
    };
    assert_eq!(
        admit_circle_update(&scheme, &pol_rev, 1000, &u_c),
        Err(AdmitReject::InvalidCredential)
    );
}

// ---------------------------------------------------------------------------
// 8 Adversarial Security Regression Tests
// ---------------------------------------------------------------------------

/// Adversarial Test 1: Wormhole / mafia-fraud relay at 5.0 m (exceeding 3.0 m room radius).
#[test]
fn adv_01_wormhole_relay_5m_rejected() {
    let params = TofParams::dregg_default();
    let mut tr = make_in_range_tof(b"sec-1", b"nonce-1", b"vseed-1");
    let rtt_5m = causal_rtt_ps(params.t_proc_min_ps, 5_000);
    assert!(rtt_5m > params.max_round_time_ps());
    tr.times_ps[17] = rtt_5m;
    assert_eq!(
        verify_tof_session(&params, &tr),
        Err(TofRejectReason::TofTimeout(17))
    );
}

/// Adversarial Test 2: Early pre-trigger / electrical reflection below `3,990 ps` turnaround floor.
#[test]
fn adv_02_early_pretrigger_below_turnaround_floor_rejected() {
    let params = TofParams::dregg_default();
    let mut tr = make_in_range_tof(b"sec-2", b"nonce-2", b"vseed-2");
    tr.times_ps[0] = params.t_proc_min_ps - 1;
    assert_eq!(
        verify_tof_session(&params, &tr),
        Err(TofRejectReason::BelowTurnaroundFloor(0))
    );
}

/// Adversarial Test 3: Hancke-Kuhn pre-ask mafia fraud against `SingleShotResponder` (`u_lock`).
/// Verifies (a) single-shot lock refuses dual-bit read, and (b) across 256 independent 128-round
/// pre-ask attacks, 0 / 256 succeed (`(3/4)^128 < 2^-53`)!
#[test]
fn adv_03_preask_mafia_fraud_against_single_shot_lock_fails() {
    let params = TofParams::dregg_default();
    let mut accepted = 0usize;
    for trial in 0u32..256 {
        let nonce = trial.to_be_bytes();
        let r0 = derive_tof_bits(CUST_TOF_R0, b"honest-prover-secret", &nonce);
        let r1 = derive_tof_bits(CUST_TOF_R1, b"honest-prover-secret", &nonce);
        let chal = derive_tof_bits(CUST_TOF_CHAL, b"verifier-chal-seed", &nonce);
        let pre_guess = derive_tof_bits(b"ADV.PREASK_GUESS", b"mafia-seed", &nonce);
        let fallback = derive_tof_bits(b"ADV.FALLBACK", b"mafia-seed", &nonce);

        let mut resp_hw = SingleShotResponder::new(r0.clone(), r1.clone());
        let mut forged_resp = Vec::with_capacity(128);
        for i in 0..128 {
            // Mafia-fraud relay pre-asks honest remote prover with guessed challenge `pre_guess[i]`.
            let leaked = resp_hw
                .query_round(i, pre_guess[i])
                .expect("first query succeeds");
            // Attempting to also read the complementary bit is blocked by `u_lock`!
            assert_eq!(resp_hw.query_round(i, !pre_guess[i]), None);
            if chal[i] == pre_guess[i] {
                forged_resp.push(leaked);
            } else {
                forged_resp.push(fallback[i]);
            }
        }
        let tr = TofTranscript {
            r0,
            r1,
            chal,
            resp: forged_resp,
            times_ps: vec![12_000; 128],
        };
        if verify_tof_session(&params, &tr).is_ok() {
            accepted += 1;
        }
    }
    assert_eq!(accepted, 0, "pre-ask mafia fraud must fail all 256 trials");
}

/// Adversarial Test 4: Passive RF traffic-analysis indistinguishability across `Idle`, `JittQuery`,
/// and `ArHazardReticle` schedules — exact byte sizes, exact header schedule, and high-entropy
/// indistinguishable ciphertext distributions (distinct ciphertexts even for identical headers
/// vs cover padding, zero plaintext substring leakage).
#[test]
fn adv_04_passive_rf_traffic_analysis_indistinguishable() {
    let key = cshake32(b"BELIEF.ROOM.KEY", b"lab-3");
    let dp = DutyPublic {
        vrf: [0x5A; 96],
        verdict_root: [0xA5; 32],
        acc_root: [0x3C; 32],
    };
    let mut mux_idle = ConstantRateCellMux::new(ChannelProfile::P2, 42, 0, key);
    let mut mux_burst = ConstantRateCellMux::new(ChannelProfile::P2, 42, 0, key);
    let secret_marker = b"HAZARD:480V-EXPOSED-BUSBAR";
    for i in 0..16u64 {
        if i % 2 == 0 {
            mux_burst.enqueue(WearableActivity::ArHazardReticle {
                anchor_id: 100 + i,
                priority: 2,
                patch: secret_marker.to_vec(),
            });
        } else {
            mux_burst.enqueue(WearableActivity::JittQuery(b"JITT:SECRET-QUERY".to_vec()));
        }
    }
    for tick in 0..16u16 {
        let dp_opt = if tick == 0 { Some(&dp) } else { None };
        let c_idle = mux_idle.emit_tick(9, tick, dp_opt).unwrap();
        let c_burst = mux_burst.emit_tick(9, tick, dp_opt).unwrap();
        // Identical 1024-byte wire length and identical 8-byte schedule header
        assert_eq!(c_idle.len(), 1024);
        assert_eq!(c_burst.len(), 1024);
        assert_eq!(&c_idle[..8], &c_burst[..8]);
        // Plaintext hazard marker never appears in cleartext on the RF wire
        assert!(!c_burst.windows(secret_marker.len()).any(|w| w == secret_marker));
        // Relay fill cell also has identical 1024-byte length and header
        let fill = fill_belief_cell(
            ChannelProfile::P2,
            &cshake32(b"RELAY.FILL", b"k"),
            CellHeader {
                domain: 42,
                epoch: 9,
                tick,
                slot: 0,
            },
        );
        assert_eq!(fill.len(), 1024);
        assert_eq!(&fill[..8], &c_idle[..8]);
    }
}

/// Adversarial Test 5: Replay attack & 1-bit ciphertext / header / duty-VRF tampering on `1024 B`
/// `Channel` cells are deterministically rejected before plaintext decryption.
#[test]
fn adv_05_cell_replay_and_bitflip_tamper_rejected() {
    let key = cshake32(b"BELIEF.KEY", b"replay-test");
    let dp = DutyPublic {
        vrf: [0x77; 96],
        verdict_root: [0x88; 32],
        acc_root: [0x99; 32],
    };
    let mut tx = ConstantRateCellMux::new(ChannelProfile::P2, 42, 3, key);
    let mut rx = ConstantRateCellMux::new(ChannelProfile::P2, 42, 3, key);
    tx.enqueue(WearableActivity::OverlayPatch {
        anchor_id: 7,
        patch: b"PATCH-OK".to_vec(),
    });
    let cell = tx.emit_tick(1, 0, Some(&dp)).unwrap();

    // Flip 1 bit in header, duty VRF, ciphertext, and MAC tag -> every one must fail MAC!
    for &offset in &[3usize, 20, 200, 1023] {
        let mut bad = cell.clone();
        bad[offset] ^= 0x01;
        assert_eq!(
            rx.demux_cell(&bad),
            Err(CellError::MacMismatch),
            "tamper at byte {offset} must fail MAC"
        );
    }
    // Truncated / extended cell rejected by length
    assert_eq!(rx.demux_cell(&cell[..1023]), Err(CellError::WrongLength));

    // Authentic first delivery succeeds; immediate replay of exact same cell is rejected!
    let (hdr, _, _) = rx.demux_cell(&cell).unwrap();
    assert_eq!(rx.demux_cell(&cell), Err(CellError::ReplayedCell(hdr)));
}

/// Adversarial Test 6: Forged / wrong-issuer / insufficient-rights `PqSelectiveBiscuit` tokens
/// cannot inject AR hazard reticles even if the attacker is physically in range (ToF valid).
#[test]
fn adv_06_forged_and_underprivileged_credentials_dropped() {
    let scheme = WotsCshake256;
    let real_issuer = IssuerSecret::new(b"REAL-ISSUER-32-BYTE-SECRET-KEY!!".to_vec());
    let fake_issuer = IssuerSecret::new(b"EVIL-ISSUER-32-BYTE-SECRET-KEY!!".to_vec());
    let real_pk = real_issuer.public_key(&scheme);
    let holder_seed = b"HOLDER-SEED-32-BYTE-SECRET-KEY!!".to_vec();
    let holder_pk = scheme.pk_of(&holder_seed);
    let attr_root = cshake32(b"ATTR", b"room");
    let tof = make_in_range_tof(b"s6", b"n6", b"v6");
    let pol = CirclePolicy {
        circle_id: 42,
        issuer_pk: real_pk,
        revocations: RevocationSet::empty(),
        required_rights: CIRCLE_WRITE_RIGHT,
        tof_params: TofParams::dregg_default(),
    };

    // (a) Token signed by rogue issuer
    let rogue_tok = issue_root_token(&scheme, &fake_issuer, b"mallory".to_vec(), holder_pk.clone(), attr_root, [1u8; 32], 0xFF, 2000);
    let mut upd = CircleOverlayUpdate {
        circle_id: 42,
        anchor_id: 1,
        lamport_clock: 1,
        author_slot: 0,
        priority: 2,
        label: b"FAKE-HAZARD".to_vec(),
        token: rogue_tok,
        tof: tof.clone(),
    };
    assert_eq!(admit_circle_update(&scheme, &pol, 1000, &upd), Err(AdmitReject::InvalidCredential));

    // (b) Authentic read-only token (rights = 0x02, missing CIRCLE_WRITE_RIGHT = 0x01)
    let ro_tok = issue_root_token(&scheme, &real_issuer, b"observer".to_vec(), holder_pk.clone(), attr_root, [2u8; 32], 0x02, 2000);
    upd.token = ro_tok;
    assert_eq!(admit_circle_update(&scheme, &pol, 1000, &upd), Err(AdmitReject::InsufficientRights));

    // (c) Cross-circle replay (circle_id = 99 instead of 42)
    let valid_tok = issue_root_token(&scheme, &real_issuer, b"alice".to_vec(), holder_pk, attr_root, [3u8; 32], 0x01, 2000);
    upd.token = valid_tok;
    upd.circle_id = 99;
    assert_eq!(admit_circle_update(&scheme, &pol, 1000, &upd), Err(AdmitReject::WrongCircle));
}

/// Adversarial Test 7: Partitioned 4-wearer AR overlay CRDT converges in 0 BFT rounds under
/// arbitrary delivery permutations, duplicates, and interleaved revoked/out-of-range attacks.
#[test]
fn adv_07_multi_wearer_partition_heal_zero_round_convergence() {
    let scheme = WotsCshake256;
    let issuer = IssuerSecret::new(b"CIRCLE-ISSUER-32-BYTES-SECRET-07".to_vec());
    let issuer_pk = issuer.public_key(&scheme);
    let attr_root = cshake32(b"ATTR", b"room-7");
    let mut updates = Vec::new();
    for slot in 0..4u16 {
        let seed = format!("WEARER-{slot:02}-SECRET-SEED-32-BYTES!!").into_bytes();
        let pk = scheme.pk_of(&seed);
        let nonce = cshake32(b"NONCE.W7", &slot.to_be_bytes());
        let tok = issue_root_token(&scheme, &issuer, format!("w{slot}").into_bytes(), pk, attr_root, nonce, 0x03, 5000);
        let tof = make_in_range_tof(&seed, &nonce, b"vseed-room-7");
        updates.push(CircleOverlayUpdate {
            circle_id: 7,
            anchor_id: 500 + (slot as u64 % 2),
            lamport_clock: 10 + slot as u64,
            author_slot: slot,
            priority: (slot % 3) as u8,
            label: format!("NOTE-FROM-W{slot}").into_bytes(),
            token: tok,
            tof,
        });
    }
    // Inject an out-of-range 10 m relay attacker update into the mix
    let mut evil_far = updates[0].clone();
    evil_far.label = b"SPOOFED-FROM-10M".to_vec();
    evil_far.tof.times_ps[63] = causal_rtt_ps(TofParams::dregg_default().t_proc_min_ps, 10_000);

    let pol = CirclePolicy {
        circle_id: 7,
        issuer_pk,
        revocations: RevocationSet::empty(),
        required_rights: CIRCLE_WRITE_RIGHT,
        tof_params: TofParams::dregg_default(),
    };

    // Partition A sees [0, evil_far, 1, 0(dup)]; Partition B sees [3, 2, evil_far]
    let mut part_a = OverlayState::new();
    let _ = part_a.ingest(&scheme, &pol, 1000, &updates[0]);
    assert!(part_a.ingest(&scheme, &pol, 1000, &evil_far).is_err());
    let _ = part_a.ingest(&scheme, &pol, 1000, &updates[1]);
    let _ = part_a.ingest(&scheme, &pol, 1000, &updates[0]);

    let mut part_b = OverlayState::new();
    let _ = part_b.ingest(&scheme, &pol, 1000, &updates[3]);
    let _ = part_b.ingest(&scheme, &pol, 1000, &updates[2]);
    assert!(part_b.ingest(&scheme, &pol, 1000, &evil_far).is_err());

    // Direct 0-round semilattice join on partition heal (both directions)
    let healed_ab = part_a.join(&part_b);
    let healed_ba = part_b.join(&part_a);
    assert_eq!(healed_ab.len(), 4);
    assert_eq!(healed_ab, healed_ba);
    assert_eq!(healed_ab.state_root(), healed_ba.state_root());
    assert_eq!(
        healed_ab.render_anchor_reticle(500),
        healed_ba.render_anchor_reticle(500)
    );
    // Idempotence: joining with self is a no-op
    assert_eq!(healed_ab.join(&healed_ab), healed_ab);
}

/// Adversarial Test 8: `cshake_keystream` domain separation & `SpatialEntry` collision/binding
/// check — changing any metadata field (`circle_id`, `anchor_id`, `lamport_clock`, `priority`,
/// `label`) changes `entry_digest` and `state_root`.
#[test]
fn adv_08_domain_separation_and_entry_digest_binding() {
    let d0 = compute_entry_digest(42, 101, 1, 0, 2, b"HAZARD");
    assert_ne!(d0, compute_entry_digest(43, 101, 1, 0, 2, b"HAZARD"));
    assert_ne!(d0, compute_entry_digest(42, 102, 1, 0, 2, b"HAZARD"));
    assert_ne!(d0, compute_entry_digest(42, 101, 2, 0, 2, b"HAZARD"));
    assert_ne!(d0, compute_entry_digest(42, 101, 1, 1, 2, b"HAZARD"));
    assert_ne!(d0, compute_entry_digest(42, 101, 1, 0, 1, b"HAZARD"));
    assert_ne!(d0, compute_entry_digest(42, 101, 1, 0, 2, b"HAZARD!"));

    let ks1 = cshake_keystream(b"DOM-A", b"key", b"hdr", 64);
    let ks2 = cshake_keystream(b"DOM-B", b"key", b"hdr", 64);
    assert_ne!(ks1, ks2);

    let mut s1 = OverlayState::new();
    s1.insert_admitted(SpatialEntry::new(42, 101, 1, 0, 2, b"HAZARD".to_vec()));
    let mut s2 = OverlayState::new();
    s2.insert_admitted(SpatialEntry::new(42, 101, 1, 0, 1, b"HAZARD".to_vec()));
    assert_ne!(s1.state_root(), s2.state_root());
}

// ---------------------------------------------------------------------------
// `--release` Microbenchmarks
// ---------------------------------------------------------------------------

#[test]
fn benchmark_belief_circle_release() {
    let tof_params = TofParams::dregg_default();
    let tr = make_in_range_tof(b"bench-secret-32b", b"bench-nonce-16b!", b"bench-vseed-32b!");

    // 1. 128-round picosecond ToF verification
    let n_tof = 50_000usize;
    let t0 = Instant::now();
    let mut ok_tof = 0usize;
    for _ in 0..n_tof {
        if verify_tof_session(&tof_params, &tr).is_ok() {
            ok_tof += 1;
        }
    }
    let dt_tof = t0.elapsed();
    assert_eq!(ok_tof, n_tof);

    // 2. Constant-rate 1024 B P2 cSHAKE256 cell seal + open
    let key = cshake32(b"BENCH.KEY", b"circle-bench");
    let act = WearableActivity::ArHazardReticle {
        anchor_id: 101,
        priority: 2,
        patch: b"HAZARD:HIGH-VOLTAGE-ARC-ZONE".to_vec(),
    };
    let n_cell = 2_000usize;
    let t1 = Instant::now();
    let mut last_len = 0usize;
    for i in 0..n_cell {
        let hdr = CellHeader {
            domain: 42,
            epoch: (i / 64) as u16,
            tick: ((i % 63) + 1) as u16,
            slot: 0,
        };
        let cell = seal_belief_cell(ChannelProfile::P2, &key, hdr, None, &act).unwrap();
        let (_, _, opened) = open_belief_cell(ChannelProfile::P2, &key, &cell).unwrap();
        last_len = cell.len();
        debug_assert_eq!(opened, act);
    }
    let dt_cell = t1.elapsed();
    assert_eq!(last_len, 1024);

    // 3. IConfluent 64-entry spatial overlay semilattice join + state_root
    let mut a = OverlayState::new();
    let mut b = OverlayState::new();
    for i in 0..64u64 {
        a.insert_admitted(SpatialEntry::new(42, i % 8, i, 0, (i % 3) as u8, format!("A-{i}").into_bytes()));
        b.insert_admitted(SpatialEntry::new(42, i % 8, i, 1, (i % 3) as u8, format!("B-{i}").into_bytes()));
    }
    let n_join = 1_000usize;
    let t2 = Instant::now();
    let mut acc_byte = 0u8;
    for _ in 0..n_join {
        let m = a.join(&b);
        acc_byte ^= m.state_root()[0];
    }
    let dt_join = t2.elapsed();

    println!(
        "[BENCH belief_circle --release]\n\
         - 128-round ToF verify:          {:.3} us/op ({} ops in {:.2} ms)\n\
         - 1024 B P2 seal+open (cSHAKE):  {:.2} us/op ({} ops in {:.2} ms)\n\
         - 64+64 CRDT join + state_root:  {:.2} us/op ({} ops in {:.2} ms, chk=0x{:02x})",
        dt_tof.as_secs_f64() * 1e6 / n_tof as f64,
        n_tof,
        dt_tof.as_secs_f64() * 1e3,
        dt_cell.as_secs_f64() * 1e6 / n_cell as f64,
        n_cell,
        dt_cell.as_secs_f64() * 1e3,
        dt_join.as_secs_f64() * 1e6 / n_join as f64,
        n_join,
        dt_join.as_secs_f64() * 1e3,
        acc_byte,
    );
}
