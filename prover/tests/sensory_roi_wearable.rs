//! Wave 10 Tier 1A End-to-End Conformance, Real `1280x720` Streaming + ZK Blur/Ambient Benchmarks,
//! and Adversarial Security Suite for Wearable SHE Organ #4 ("Epiphany Lens" v2).
//!
//! Covers:
//! - Byte-exact Lean `v4.35.0` conformance (`Assurance/SensoryRoiZeroKnowledge.lean` <-> `sensory_roi_cert.rs`)
//! - Asymmetric post-quantum `WotsCshake256` / XMSS header signing & non-forgeability (ZERO `hw_key`)
//! - Raw-only tile Merkle ROI reveal (ZERO `sumCommit`, ZERO bystander leakage)
//! - Real `BabyBearExt4` HVZK sumcheck + `UD-100` (`rate = 1/4`, `q = 148`, `16`-bit PoW) BaseFold/FRI:
//!   - `BlurDownscaleZkProof` (Boolean `log2(tile_len)`-bit remainder range check, ZERO intra-tile leakage)
//!   - `AmbientEnvelopeZkProof` (ZERO per-tile sums on wire, `TVD = 0` on ideal sumcheck view)

#![deny(warnings)]

use std::time::Instant;

use minidregg_prover::pq_biscuit::{PqSigBackend, WotsCshake256};
use minidregg_prover::sensory_roi_cert::{
    prove_ambient_envelope_zk, prove_blur_downscale_zk, seal_csi2_plane_streaming,
    seal_sensor_frame, sum_bytes, verify_ambient_envelope_zk, verify_blur_downscale_zk,
    verify_frame_header, verify_roi_reveal_cert, AmbientEnvelopeZkProof, BlurDownscaleZkProof,
    CachedCshakeCores, Digest, EnclavePublicKey, EnclaveSigningKey, Ext4, FrameContext,
    RawSensorTile, RoiRevealCert, RoiTileOpening, Salt256, SensorFrameHeader, SensorModality,
    SensoryRoiError, TileSubsetSpec, P_U32,
};
use serde::Deserialize;

#[derive(Deserialize)]
struct ConformanceVectorV2 {
    schema: String,
    empty_leaf_hex: String,
    csi2_frame: Csi2FrameVecV2,
    i2s_audio_frame: AudioFrameVecV2,
    lean_self_checks: LeanSelfChecksV2,
}

#[derive(Deserialize)]
struct Csi2FrameVecV2 {
    wots_seed_hex: String,
    enclave_pk_hex: String,
    sensor_id: u64,
    frame_seq: u64,
    timestamp_ns: u64,
    grid_width: u32,
    grid_height: u32,
    tile_len: u32,
    merkle_depth: u32,
    tile_merkle_root_hex: String,
    rt_raw_hex: String,
    signing_payload_hex: String,
    wots_sig_hex: String,
    raw_commits_hex: Vec<String>,
    tiles_pixels_hex: Vec<String>,
    tiles_raw_salts_hex: Vec<String>,
    roi_tile0_path_hex: Vec<String>,
    expected_blur_means: Vec<u8>,
    expected_ambient_total: u64,
}

#[derive(Deserialize)]
struct AudioFrameVecV2 {
    wots_seed_hex: String,
    enclave_pk_hex: String,
    sensor_id: u64,
    frame_seq: u64,
    timestamp_ns: u64,
    grid_width: u32,
    grid_height: u32,
    tile_len: u32,
    merkle_depth: u32,
    tile_merkle_root_hex: String,
    rt_raw_hex: String,
    signing_payload_hex: String,
    wots_sig_hex: String,
    windows_pixels_hex: Vec<String>,
    windows_raw_salts_hex: Vec<String>,
    expected_ambient_total: u64,
}

#[derive(Deserialize)]
struct LeanSelfChecksV2 {
    wots_header_ok: bool,
    roi_ok: bool,
    splice_refused: bool,
    replay_refused: bool,
    forged_sig_refused: bool,
    blur_div_ok: bool,
    fresh_salts_ok: bool,
}

fn hex_decode(s: &str) -> Vec<u8> {
    assert_eq!(s.len() % 2, 0, "odd hex string");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("valid hex"))
        .collect()
}

fn hex_digest(s: &str) -> Digest {
    hex_decode(s).try_into().expect("32-byte digest")
}

fn synth_salt(frame_seq: u64, tile_idx: usize) -> Salt256 {
    let mut s = [0u8; 32];
    s[0..8].copy_from_slice(&frame_seq.to_le_bytes());
    s[8..16].copy_from_slice(&(tile_idx as u64).to_le_bytes());
    for (i, slot) in s[16..32].iter_mut().enumerate() {
        *slot = ((tile_idx as u64).wrapping_mul(31) ^ ((i + 16) as u64 * 17) ^ (frame_seq * 73)) as u8;
    }
    s
}

/// Byte-exact conformance against Lean 4.35.0 `Assurance/SensoryRoiZeroKnowledge.lean` (v2)
/// + live real-ZK `BlurDownscaleZkProof` & `AmbientEnvelopeZkProof` execution on the exact Lean frames!
#[test]
fn lean_435_byte_exact_conformance() {
    let raw_json = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/sensory_roi_conformance.json"
    ))
    .expect("read sensory_roi_conformance.json");
    let vec: ConformanceVectorV2 = serde_json::from_str(&raw_json).expect("parse v2 conformance json");
    assert_eq!(vec.schema, "minidregg.sensory_roi_conformance.v2");
    assert!(vec.lean_self_checks.wots_header_ok);
    assert!(vec.lean_self_checks.roi_ok);
    assert!(vec.lean_self_checks.splice_refused);
    assert!(vec.lean_self_checks.replay_refused);
    assert!(vec.lean_self_checks.forged_sig_refused);
    assert!(vec.lean_self_checks.blur_div_ok);
    assert!(vec.lean_self_checks.fresh_salts_ok);

    let cores = CachedCshakeCores::new();
    assert_eq!(cores.empty_leaf(), hex_digest(&vec.empty_leaf_hex));

    // 1. CSI-2 2x2 16x16 frame: bit-for-bit Lean <-> Rust parity on WOTS+ PK, raw commits, Merkle root, payload & sig
    let cf = &vec.csi2_frame;
    let csi2_seed = hex_decode(&cf.wots_seed_hex);
    let csi2_sk_lean = EnclaveSigningKey::from_wots_seed(csi2_seed.clone());
    let csi2_pk = csi2_sk_lean.public_key();
    assert_eq!(csi2_pk.root, hex_digest(&cf.enclave_pk_hex));

    let lean_hdr_csi2 = SensorFrameHeader {
        ctx: FrameContext {
            sensor_id: cf.sensor_id,
            frame_seq: cf.frame_seq,
            timestamp_ns: cf.timestamp_ns,
        },
        grid_width: cf.grid_width,
        grid_height: cf.grid_height,
        tile_len: cf.tile_len,
        merkle_depth: cf.merkle_depth,
        modality: SensorModality::Csi2Tile16x16,
        tile_merkle_root: hex_digest(&cf.tile_merkle_root_hex),
        rt_raw: hex_digest(&cf.rt_raw_hex),
        enclave_pk: csi2_pk,
        ots_index: 0,
        ots_pk: csi2_pk.root,
        wots_sig: hex_decode(&cf.wots_sig_hex),
        ots_auth_path: Vec::new(),
    };
    assert_eq!(lean_hdr_csi2.signing_payload(), hex_decode(&cf.signing_payload_hex));
    assert_eq!(
        WotsCshake256.sign(&csi2_seed, &lean_hdr_csi2.signing_payload()),
        lean_hdr_csi2.wots_sig
    );
    verify_frame_header(&cores, &csi2_pk, &lean_hdr_csi2).expect("verify Lean WOTS+ CSI-2 header");

    let csi2_tiles: Vec<RawSensorTile> = (0..cf.tiles_pixels_hex.len())
        .map(|i| RawSensorTile {
            pixels: hex_decode(&cf.tiles_pixels_hex[i]),
            raw_salt: hex_digest(&cf.tiles_raw_salts_hex[i]),
        })
        .collect();
    // Use a FRESH distinct XMSS signing key for the live Rust frame (which carries a real PCS `rt_raw`
    // rather than Lean's `demo_rt_raw`), NEVER reusing Lean's one-time WOTS seed on a 2nd message!
    let live_csi2_sk = EnclaveSigningKey::from_xmss_master_seed(&cores, &[0xC1u8; 32], 1);
    let live_csi2_pk = live_csi2_sk.public_key();
    let frame = seal_sensor_frame(
        &cores,
        &live_csi2_sk,
        lean_hdr_csi2.ctx,
        cf.grid_width,
        cf.grid_height,
        cf.merkle_depth,
        SensorModality::Csi2Tile16x16,
        csi2_tiles,
        &[0x19u8; 32],
    )
    .expect("seal live CSI-2 frame");
    assert_eq!(frame.header.tile_merkle_root, hex_digest(&cf.tile_merkle_root_hex));
    for (i, hex_rc) in cf.raw_commits_hex.iter().enumerate() {
        assert_eq!(frame.raw_commits[i], hex_digest(hex_rc));
    }
    let expected_p0: Vec<Digest> = cf.roi_tile0_path_hex.iter().map(|s| hex_digest(s)).collect();
    assert_eq!(frame.open_merkle_path(0), expected_p0);

    // Verify ROI reveal, BlurDownscaleZkProof, and AmbientEnvelopeZkProof against the live sensor-signed `rt_raw`!
    let roi_cert = frame.open_roi_cert(&[0]);
    verify_roi_reveal_cert(&cores, &live_csi2_pk, &frame.header, &roi_cert).expect("verify ROI");

    let raw_flat = frame.raw_pixels_flat();
    let blur_all = prove_blur_downscale_zk(
        &cores,
        &frame.header,
        &frame.raw_pcs,
        &raw_flat,
        &TileSubsetSpec::AllTiles,
        &[0x2Au8; 32],
    )
    .expect("prove CSI-2 blur ZK");
    assert_eq!(blur_all.blurred_pixels, cf.expected_blur_means);
    verify_blur_downscale_zk(&cores, &live_csi2_pk, &frame.header, &TileSubsetSpec::AllTiles, &blur_all)
        .expect("verify CSI-2 blur ZK");

    let amb_all = prove_ambient_envelope_zk(
        &cores,
        &frame.header,
        &frame.raw_pcs,
        &raw_flat,
        &TileSubsetSpec::AllTiles,
        cf.expected_ambient_total + 100,
        &[0x3Bu8; 32],
    )
    .expect("prove CSI-2 ambient ZK");
    assert_eq!(amb_all.claimed_total, cf.expected_ambient_total);
    verify_ambient_envelope_zk(
        &cores,
        &live_csi2_pk,
        &frame.header,
        &TileSubsetSpec::AllTiles,
        cf.expected_ambient_total + 100,
        &amb_all,
    )
    .expect("verify CSI-2 ambient ZK");

    // 2. I2S 2-window audio frame: bit-for-bit Lean <-> Rust parity + live AmbientEnvelopeZkProof
    let af = &vec.i2s_audio_frame;
    let audio_seed = hex_decode(&af.wots_seed_hex);
    let audio_sk_lean = EnclaveSigningKey::from_wots_seed(audio_seed.clone());
    let audio_pk = audio_sk_lean.public_key();
    assert_eq!(audio_pk.root, hex_digest(&af.enclave_pk_hex));

    let lean_hdr_audio = SensorFrameHeader {
        ctx: FrameContext {
            sensor_id: af.sensor_id,
            frame_seq: af.frame_seq,
            timestamp_ns: af.timestamp_ns,
        },
        grid_width: af.grid_width,
        grid_height: af.grid_height,
        tile_len: af.tile_len,
        merkle_depth: af.merkle_depth,
        modality: SensorModality::I2sAudioWindow,
        tile_merkle_root: hex_digest(&af.tile_merkle_root_hex),
        rt_raw: hex_digest(&af.rt_raw_hex),
        enclave_pk: audio_pk,
        ots_index: 0,
        ots_pk: audio_pk.root,
        wots_sig: hex_decode(&af.wots_sig_hex),
        ots_auth_path: Vec::new(),
    };
    assert_eq!(lean_hdr_audio.signing_payload(), hex_decode(&af.signing_payload_hex));
    assert_eq!(
        WotsCshake256.sign(&audio_seed, &lean_hdr_audio.signing_payload()),
        lean_hdr_audio.wots_sig
    );
    verify_frame_header(&cores, &audio_pk, &lean_hdr_audio).expect("verify Lean WOTS+ audio header");

    let audio_tiles: Vec<RawSensorTile> = (0..af.windows_pixels_hex.len())
        .map(|i| RawSensorTile {
            pixels: hex_decode(&af.windows_pixels_hex[i]),
            raw_salt: hex_digest(&af.windows_raw_salts_hex[i]),
        })
        .collect();
    let live_audio_sk = EnclaveSigningKey::from_xmss_master_seed(&cores, &[0xC2u8; 32], 1);
    let live_audio_pk = live_audio_sk.public_key();
    let aframe = seal_sensor_frame(
        &cores,
        &live_audio_sk,
        lean_hdr_audio.ctx,
        af.grid_width,
        af.grid_height,
        af.merkle_depth,
        SensorModality::I2sAudioWindow,
        audio_tiles,
        &[0x4Cu8; 32],
    )
    .expect("seal live audio frame");
    assert_eq!(aframe.header.tile_merkle_root, hex_digest(&af.tile_merkle_root_hex));
    let audio_flat = aframe.raw_pixels_flat();
    let amb_audio = prove_ambient_envelope_zk(
        &cores,
        &aframe.header,
        &aframe.raw_pcs,
        &audio_flat,
        &TileSubsetSpec::AllTiles,
        af.expected_ambient_total,
        &[0x5Du8; 32],
    )
    .expect("prove audio ambient ZK");
    assert_eq!(amb_audio.claimed_total, af.expected_ambient_total);
    verify_ambient_envelope_zk(
        &cores,
        &live_audio_pk,
        &aframe.header,
        &TileSubsetSpec::AllTiles,
        af.expected_ambient_total,
        &amb_audio,
    )
    .expect("verify audio ambient ZK");
}

/// Real `1280x720` (`80x45 = 3,600` `16x16` tiles, `921,600` pixels -> `N_raw = 2^{20}`) streaming
/// seal (XMSS-WOTS + `rt_raw` RS commitment) + ROI + full-frame `BlurDownscaleZkProof` +
/// `AmbientEnvelopeZkProof` end-to-end benchmark!
#[test]
fn bench_720p_streaming_seal_and_real_zk_blur_ambient() {
    let cores = CachedCshakeCores::new();
    let enclave_sk = EnclaveSigningKey::from_xmss_master_seed(&cores, &[0x9Bu8; 32], 3);
    let enclave_pk = enclave_sk.public_key();

    let width = 1280usize;
    let height = 720usize;
    let n_tiles = (width / 16) * (height / 16);
    assert_eq!(n_tiles, 3_600);

    let mut y_plane = vec![0u8; width * height];
    for (i, px) in y_plane.iter_mut().enumerate() {
        *px = ((i.wrapping_mul(37) ^ (i >> 5)) & 0xFF) as u8;
    }
    let raw_salts: Vec<Salt256> = (0..n_tiles).map(|i| synth_salt(100, i)).collect();

    let ctx = FrameContext {
        sensor_id: 0xC512_7200,
        frame_seq: 100,
        timestamp_ns: 1_732_234_567_000_000_000,
    };
    let t_seal = Instant::now();
    let handle = seal_csi2_plane_streaming(
        &cores,
        &enclave_sk,
        ctx,
        width,
        height,
        &y_plane,
        &raw_salts,
        &[0x71u8; 32],
    )
    .expect("720p seal ok");
    let seal_ms = t_seal.elapsed().as_secs_f64() * 1000.0;

    // 64 authorized frustum ROI tiles + 3,536 non-ROI blurred/ambient tiles!
    let roi_indices: Vec<u32> = (0..64u32).map(|k| (18 + k / 8) * 80 + (36 + k % 8)).collect();
    let roi_cert = handle.open_roi_cert(&raw_salts, &roi_indices);
    let t_roi = Instant::now();
    verify_roi_reveal_cert(&cores, &enclave_pk, &handle.header, &roi_cert).expect("720p ROI verify");
    let roi_verify_ms = t_roi.elapsed().as_secs_f64() * 1000.0;

    let non_roi = TileSubsetSpec::ExcludeRoi(roi_indices);

    let t_bp = Instant::now();
    let blur_prf = prove_blur_downscale_zk(
        &cores,
        &handle.header,
        &handle.raw_pcs,
        &handle.raw_flat,
        &non_roi,
        &[0x72u8; 32],
    )
    .expect("720p blur ZK prove");
    let blur_prove_ms = t_bp.elapsed().as_secs_f64() * 1000.0;
    let blur_wire = blur_prf.to_wire_bytes();
    let blur_dec = BlurDownscaleZkProof::from_wire_bytes(&blur_wire).expect("blur decode");
    let t_bv = Instant::now();
    verify_blur_downscale_zk(&cores, &enclave_pk, &handle.header, &non_roi, &blur_dec)
        .expect("720p blur ZK verify");
    let blur_verify_ms = t_bv.elapsed().as_secs_f64() * 1000.0;

    let t_ap = Instant::now();
    let amb_prf = prove_ambient_envelope_zk(
        &cores,
        &handle.header,
        &handle.raw_pcs,
        &handle.raw_flat,
        &non_roi,
        250_000_000,
        &[0x73u8; 32],
    )
    .expect("720p ambient ZK prove");
    let amb_prove_ms = t_ap.elapsed().as_secs_f64() * 1000.0;
    let amb_wire = amb_prf.to_wire_bytes();
    let amb_dec = AmbientEnvelopeZkProof::from_wire_bytes(&amb_wire).expect("ambient decode");
    let t_av = Instant::now();
    verify_ambient_envelope_zk(
        &cores,
        &enclave_pk,
        &handle.header,
        &non_roi,
        250_000_000,
        &amb_dec,
    )
    .expect("720p ambient ZK verify");
    let amb_verify_ms = t_av.elapsed().as_secs_f64() * 1000.0;

    println!(
        "[720p REAL-ZK BENCH] 1280x720 (3,600 tiles, N_raw=2^20, rate=1/4, q=148, 16b PoW, bare UD-100):\n  \
         seal(tile_root+rt_raw+XMSS-WOTS) = {seal_ms:.2} ms\n  \
         ROI verify (64 tiles)            = {roi_verify_ms:.3} ms\n  \
         BlurDownscaleZkProof (3,536 t)   = prove {blur_prove_ms:.2} ms | verify {blur_verify_ms:.2} ms | wire {:.1} KiB\n  \
         AmbientEnvelopeZkProof (3,536 t) = prove {amb_prove_ms:.2} ms | verify {amb_verify_ms:.2} ms | wire {:.1} KiB",
        blur_wire.len() as f64 / 1024.0,
        amb_wire.len() as f64 / 1024.0,
    );
}

fn build_4tile_fixture() -> (
    CachedCshakeCores,
    EnclaveSigningKey,
    EnclavePublicKey,
    minidregg_prover::sensory_roi_cert::SealedSensorFrame,
) {
    let cores = CachedCshakeCores::new();
    let sk = EnclaveSigningKey::from_xmss_master_seed(&cores, &[0x77u8; 32], 2);
    let pk = sk.public_key();
    let ctx = FrameContext {
        sensor_id: 0x0E91_0004,
        frame_seq: 55,
        timestamp_ns: 1_732_234_567_500_000_000,
    };
    let tiles = vec![
        RawSensorTile {
            pixels: (0..256).map(|k| ((k * 3 + 11) % 256) as u8).collect(),
            raw_salt: synth_salt(55, 0),
        },
        RawSensorTile {
            pixels: b"BYSTANDER_FACE_SECRET_BIOMETRIC_VECTOR_DO_NOT_LEAK_0123456789___".repeat(4),
            raw_salt: synth_salt(55, 1),
        },
        RawSensorTile {
            pixels: (0..256).map(|k| ((k * 5 + 7) % 256) as u8).collect(),
            raw_salt: synth_salt(55, 2),
        },
        RawSensorTile {
            pixels: b"BYSTANDER_LAPTOP_SCREEN_API_KEY_SK_LIVE_999999999999999999999999".repeat(4),
            raw_salt: synth_salt(55, 3),
        },
    ];
    let frame = seal_sensor_frame(
        &cores,
        &sk,
        ctx,
        2,
        2,
        2,
        SensorModality::Csi2Tile16x16,
        tiles,
        &[0x88u8; 32],
    )
    .expect("seal 4-tile fixture");
    (cores, sk, pk, frame)
}

/// Adv 1: Asymmetric PQ `WotsCshake256` / XMSS non-forgeability, depth-pinning & OTS budget enforcement.
#[test]
fn adv1_asymmetric_pq_enclave_non_forgeability_and_xmss_depth_pin() {
    let (cores, _sk, pk, frame) = build_4tile_fixture();
    verify_frame_header(&cores, &pk, &frame.header).expect("honest header ok");

    // 1-bit flip in WOTS+ signature refused
    let mut bad_sig = frame.header.clone();
    bad_sig.wots_sig[0] ^= 0x01;
    assert_eq!(
        verify_frame_header(&cores, &pk, &bad_sig).unwrap_err(),
        SensoryRoiError::InvalidEnclaveSignature
    );

    // Wrong enclave public key refused
    let wrong_pk = EnclavePublicKey {
        root: [0xFFu8; 32],
        tree_depth: pk.tree_depth,
    };
    assert_eq!(
        verify_frame_header(&cores, &wrong_pk, &frame.header).unwrap_err(),
        SensoryRoiError::EnclaveKeyMismatch
    );

    // Depth-confusion attack (trying to verify XMSS leaf as tree_depth=0) refused
    let mut spoof_depth = frame.header.clone();
    spoof_depth.enclave_pk = EnclavePublicKey {
        root: frame.header.ots_pk,
        tree_depth: 0,
    };
    spoof_depth.ots_auth_path.clear();
    assert_eq!(
        verify_frame_header(&cores, &pk, &spoof_depth).unwrap_err(),
        SensoryRoiError::EnclaveKeyMismatch
    );

    // OTS one-time-key reuse prevention: single-WOTS enclave refuses signing a 2nd frame!
    let single_sk = EnclaveSigningKey::from_wots_seed(vec![0x33u8; 32]);
    let t = vec![RawSensorTile {
        pixels: vec![42u8; 64],
        raw_salt: synth_salt(1, 0),
    }];
    let ctx = FrameContext {
        sensor_id: 1,
        frame_seq: 1,
        timestamp_ns: 1,
    };
    seal_sensor_frame(&cores, &single_sk, ctx, 1, 1, 0, SensorModality::I2sAudioWindow, t.clone(), &[1u8; 32])
        .expect("1st sign ok");
    assert_eq!(
        seal_sensor_frame(&cores, &single_sk, ctx, 1, 1, 0, SensorModality::I2sAudioWindow, t, &[2u8; 32])
            .err(),
        Some(SensoryRoiError::OtsBudgetExhausted)
    );
}

/// Adv 2: Deepfake 1-pixel LSB splice inside an authorized ROI tile is refused.
#[test]
fn adv2_synthetic_one_pixel_lsb_splice_refused() {
    let (cores, _sk, pk, frame) = build_4tile_fixture();
    let mut cert = frame.open_roi_cert(&[0]);
    cert.openings[0].pixels[137] ^= 0x01;
    assert_eq!(
        verify_roi_reveal_cert(&cores, &pk, &frame.header, &cert).unwrap_err(),
        SensoryRoiError::MerklePathMismatch { tile_idx: 0 }
    );
}

/// Adv 3: Cross-timestamp / cross-sequence header tamper & cross-frame tile replay refused.
#[test]
fn adv3_cross_timestamp_and_seq_replay_refused() {
    let (cores, sk, pk, frame) = build_4tile_fixture();
    let cert = frame.open_roi_cert(&[0]);

    let mut forged_ts = frame.header.clone();
    forged_ts.ctx.timestamp_ns += 1;
    assert_eq!(
        verify_roi_reveal_cert(&cores, &pk, &forged_ts, &cert).unwrap_err(),
        SensoryRoiError::InvalidEnclaveSignature
    );

    let mut tiles_f2 = frame.tiles.clone();
    tiles_f2[0].raw_salt = synth_salt(56, 0);
    let f2 = seal_sensor_frame(
        &cores,
        &sk,
        FrameContext {
            frame_seq: frame.header.ctx.frame_seq + 1,
            timestamp_ns: frame.header.ctx.timestamp_ns + 16_666_667,
            ..frame.header.ctx
        },
        2,
        2,
        2,
        SensorModality::Csi2Tile16x16,
        tiles_f2,
        &[0x89u8; 32],
    )
    .expect("seal f2 with next XMSS OTS key");
    assert_eq!(f2.header.ots_index, 1);
    assert_eq!(
        verify_roi_reveal_cert(&cores, &pk, &f2.header, &cert).unwrap_err(),
        SensoryRoiError::MerklePathMismatch { tile_idx: 0 }
    );
}

/// Adv 4: Grafting an authentic tile from coordinate `0` into `2` is refused.
#[test]
fn adv4_tile_coordinate_graft_refused() {
    let (cores, _sk, pk, frame) = build_4tile_fixture();
    let grafted = RoiRevealCert {
        openings: vec![RoiTileOpening {
            tile_idx: 2,
            pixels: frame.tiles[0].pixels.clone(),
            raw_salt: frame.tiles[0].raw_salt,
            merkle_path: frame.open_merkle_path(2),
        }],
    };
    assert_eq!(
        verify_roi_reveal_cert(&cores, &pk, &frame.header, &grafted).unwrap_err(),
        SensoryRoiError::MerklePathMismatch { tile_idx: 2 }
    );
}

/// Adv 5: Reused per-tile hardware TRNG `raw_salt` is refused.
#[test]
fn adv5_raw_salt_reuse_refused() {
    let cores = CachedCshakeCores::new();
    let sk = EnclaveSigningKey::from_wots_seed(vec![0x55u8; 32]);
    let ctx = FrameContext {
        sensor_id: 1,
        frame_seq: 1,
        timestamp_ns: 1,
    };
    let dup = vec![
        RawSensorTile {
            pixels: vec![10; 256],
            raw_salt: synth_salt(1, 0),
        },
        RawSensorTile {
            pixels: vec![20; 256],
            raw_salt: synth_salt(1, 0),
        },
    ];
    assert_eq!(
        seal_sensor_frame(&cores, &sk, ctx, 2, 1, 1, SensorModality::Csi2Tile16x16, dup, &[0u8; 32])
            .err(),
        Some(SensoryRoiError::SaltReuseDetected { tile_idx: 1 })
    );
}

/// Adv 6: Forged blur mean (`B[t] ± 1`), smuggled excluded-slot blur byte, and cross-frame blur splice refused.
#[test]
fn adv6_forged_blur_mean_and_smuggled_slot_refused() {
    let (cores, sk, pk, frame) = build_4tile_fixture();
    let raw_flat = frame.raw_pixels_flat();
    let sub = TileSubsetSpec::ExcludeRoi(vec![0]);
    let prf = prove_blur_downscale_zk(&cores, &frame.header, &frame.raw_pcs, &raw_flat, &sub, &[0xA1u8; 32])
        .expect("blur prove ok");
    verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &prf).expect("honest blur ok");

    // 1. Forge B[2] += 1 -> Fiat-Shamir + sumcheck catches immediately!
    let mut bad_mean = prf.clone();
    bad_mean.blurred_pixels[2] = bad_mean.blurred_pixels[2].wrapping_add(1);
    assert!(verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &bad_mean).is_err());

    // 2. Smuggle non-zero metadata into excluded ROI tile slot 0 -> rejected before transcript!
    let mut smuggled = prf.clone();
    smuggled.blurred_pixels[0] = 7;
    assert!(matches!(
        verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &smuggled),
        Err(SensoryRoiError::InvalidBlurPublicArray(_))
    ));

    // 3. Splice valid blur proof from frame 1 onto a different frame 2 -> refused!
    let mut tiles2 = frame.tiles.clone();
    tiles2[2].pixels[0] ^= 0x01;
    let frame2 = seal_sensor_frame(
        &cores,
        &sk,
        FrameContext {
            frame_seq: 56,
            ..frame.header.ctx
        },
        2,
        2,
        2,
        SensorModality::Csi2Tile16x16,
        tiles2,
        &[0xA2u8; 32],
    )
    .unwrap();
    assert!(verify_blur_downscale_zk(&cores, &pk, &frame2.header, &sub, &prf).is_err());
}

/// Adv 7: Forged ambient total (`+1`), threshold violation, and out-of-range claim refused.
#[test]
fn adv7_forged_ambient_total_and_threshold_refused() {
    let (cores, _sk, pk, frame) = build_4tile_fixture();
    let raw_flat = frame.raw_pixels_flat();
    let sub = TileSubsetSpec::AllTiles;
    let true_total: u64 = frame.tiles.iter().map(|t| sum_bytes(&t.pixels) as u64).sum();

    // Threshold strictly below true_total refused at prove time
    assert_eq!(
        prove_ambient_envelope_zk(
            &cores,
            &frame.header,
            &frame.raw_pcs,
            &raw_flat,
            &sub,
            true_total - 1,
            &[0xB1u8; 32],
        )
        .err(),
        Some(SensoryRoiError::ThresholdExceeded {
            claimed: true_total,
            threshold: true_total - 1
        })
    );

    let prf = prove_ambient_envelope_zk(
        &cores,
        &frame.header,
        &frame.raw_pcs,
        &raw_flat,
        &sub,
        true_total + 1000,
        &[0xB2u8; 32],
    )
    .expect("ambient prove ok");
    verify_ambient_envelope_zk(&cores, &pk, &frame.header, &sub, true_total + 1000, &prf)
        .expect("honest ambient ok");

    // Claimed total + 1 refused
    let mut bad_tot = prf.clone();
    bad_tot.claimed_total += 1;
    assert!(
        verify_ambient_envelope_zk(&cores, &pk, &frame.header, &sub, true_total + 1000, &bad_tot)
            .is_err()
    );

    // Mismatched verifier threshold refused
    assert!(matches!(
        verify_ambient_envelope_zk(&cores, &pk, &frame.header, &sub, true_total + 500, &prf),
        Err(SensoryRoiError::ThresholdExceeded { .. })
    ));

    // Out-of-range claimed_total > 4 * 256 * 255 refused
    let mut oob = prf.clone();
    oob.claimed_total = 4 * 256 * 255 + 1;
    oob.threshold = oob.claimed_total;
    assert!(matches!(
        verify_ambient_envelope_zk(&cores, &pk, &frame.header, &sub, oob.threshold, &oob),
        Err(SensoryRoiError::ClaimedTotalOutOfRange { .. })
    ));
}

/// Adv 8: Exhaustive algebraic/BaseFold/FRI/PoW/Merkle-multiproof tamper matrix (every component load-bearing!).
#[test]
fn adv8_basefold_fri_pow_and_transcript_tamper_refused() {
    let (cores, _sk, pk, frame) = build_4tile_fixture();
    let raw_flat = frame.raw_pixels_flat();
    let sub = TileSubsetSpec::ExcludeRoi(vec![0, 3]);
    let prf = prove_blur_downscale_zk(&cores, &frame.header, &frame.raw_pcs, &raw_flat, &sub, &[0xC1u8; 32])
        .expect("blur prove ok");

    // 1. PoW nonce tamper
    let mut p = prf.clone();
    p.pcs_opening.pow_nonce ^= 1;
    assert_eq!(
        verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &p).unwrap_err(),
        SensoryRoiError::InvalidPowGrinding
    );

    // 2. Outer round-0 poly tamper
    let mut p = prf.clone();
    p.round0_poly[0] = p.round0_poly[0].add(Ext4::ONE);
    assert!(verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &p).is_err());

    // 3. Blinded terminal eval `hat_v_bits[0]` tamper
    let mut p = prf.clone();
    p.hat_v_bits[0] = p.hat_v_bits[0].add(Ext4::ONE);
    assert!(verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &p).is_err());

    // 4. Z-padding `y_z` tamper
    let mut p = prf.clone();
    p.pcs_opening.y_z = p.pcs_opening.y_z.add(Ext4::ONE);
    assert!(verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &p).is_err());

    // 5. Coefficient sumcheck `e_hat[0]` tamper
    let mut p = prf.clone();
    p.pcs_opening.e_hat[0] = p.pcs_opening.e_hat[0].add(Ext4::ONE);
    assert!(verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &p).is_err());

    // 6. BaseFold `final_const` tamper
    let mut p = prf.clone();
    p.pcs_opening.final_const = p.pcs_opening.final_const.add(Ext4::ONE);
    assert!(verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &p).is_err());

    // 7. FRI opened pair value tamper
    let mut p = prf.clone();
    p.pcs_opening.fri_levels[0].opened_pairs[0][0] =
        p.pcs_opening.fri_levels[0].opened_pairs[0][0].add(Ext4::ONE);
    assert!(verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &p).is_err());

    // 8. Stage-0 `rt_raw` opened column value tamper
    let mut p = prf.clone();
    p.pcs_opening.raw_col_vals[0] = (p.pcs_opening.raw_col_vals[0] + 1) % P_U32;
    assert!(verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &p).is_err());

    // 9. Stage-0 `rt_raw` Merkle multiproof sibling tamper
    let mut p = prf.clone();
    p.pcs_opening.raw_multiproof.siblings[0][0] ^= 0x80;
    assert!(verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &p).is_err());
}

/// Adv 9: Canonical wire deserialization rejects non-canonical BabyBear limbs `>= P`, truncation, and trailing bytes.
#[test]
fn adv9_canonical_wire_deserialization_strict() {
    let (cores, _sk, _pk, frame) = build_4tile_fixture();
    let raw_flat = frame.raw_pixels_flat();
    let amb = prove_ambient_envelope_zk(
        &cores,
        &frame.header,
        &frame.raw_pcs,
        &raw_flat,
        &TileSubsetSpec::AllTiles,
        500_000,
        &[0xD1u8; 32],
    )
    .unwrap();
    let wire = amb.to_wire_bytes();

    // Trailing byte rejected
    let mut with_tail = wire.clone();
    with_tail.push(0x00);
    assert!(matches!(
        AmbientEnvelopeZkProof::from_wire_bytes(&with_tail),
        Err(SensoryRoiError::MalformedWireProof(_))
    ));

    // Truncated byte rejected
    assert!(matches!(
        AmbientEnvelopeZkProof::from_wire_bytes(&wire[..wire.len() - 1]),
        Err(SensoryRoiError::MalformedWireProof(_))
    ));

    // Non-canonical `Ext4` limb `P_U32` injected at `gmask_sum` offset (8 + 8 + 8 + 32 = 56) rejected
    let mut non_canon = wire.clone();
    non_canon[56..60].copy_from_slice(&P_U32.to_le_bytes());
    assert_eq!(
        AmbientEnvelopeZkProof::from_wire_bytes(&non_canon).unwrap_err(),
        SensoryRoiError::NonCanonicalFieldElement
    );
}

/// Adv 10: Zero-bystander-leakage wire audit AND v1-cleartext-refutation / v2 witness-indistinguishability
/// (`Frame A: [25600, 0]` vs `Frame B: [12800, 12800]`, exact counterpart of Lean `tooth_cleartext_tile_sum_leaks_spatial_luminance`!).
#[test]
fn adv10_zero_bystander_and_zero_tile_sum_wire_audit() {
    let (cores, _sk, pk, frame) = build_4tile_fixture();
    let raw_flat = frame.raw_pixels_flat();
    let roi_cert = frame.open_roi_cert(&[0]);
    let sub = TileSubsetSpec::ExcludeRoi(vec![0]);
    let blur_prf = prove_blur_downscale_zk(&cores, &frame.header, &frame.raw_pcs, &raw_flat, &sub, &[0xE1u8; 32])
        .unwrap();
    let amb_prf = prove_ambient_envelope_zk(
        &cores,
        &frame.header,
        &frame.raw_pcs,
        &raw_flat,
        &sub,
        500_000,
        &[0xE2u8; 32],
    )
    .unwrap();
    verify_roi_reveal_cert(&cores, &pk, &frame.header, &roi_cert).unwrap();
    verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &blur_prf).unwrap();
    verify_ambient_envelope_zk(&cores, &pk, &frame.header, &sub, 500_000, &amb_prf).unwrap();

    let roi_wire = roi_cert.to_wire_bytes();
    let blur_wire = blur_prf.to_wire_bytes();
    let amb_wire = amb_prf.to_wire_bytes();

    for forbidden in [
        b"BYSTANDER_FACE".as_slice(),
        b"SECRET_BIOMETRIC".as_slice(),
        b"BYSTANDER_LAPTOP".as_slice(),
        b"SK_LIVE_9999".as_slice(),
        &frame.tiles[1].raw_salt,
        &frame.tiles[2].raw_salt,
        &frame.tiles[3].raw_salt,
    ] {
        assert!(!roi_wire.windows(forbidden.len()).any(|w| w == forbidden));
        assert!(!blur_wire.windows(forbidden.len()).any(|w| w == forbidden));
        assert!(!amb_wire.windows(forbidden.len()).any(|w| w == forbidden));
    }

    // Exact counterpart of Lean `tooth_cleartext_tile_sum_leaks_spatial_luminance`:
    // Frame A (`tile 0 = 25600, tile 1 = 0`) vs Frame B (`tile 0 = 12800, tile 1 = 12800`), both total `25600`!
    let sk_ab = EnclaveSigningKey::from_xmss_master_seed(&cores, &[0xEEu8; 32], 1);
    let pk_ab = sk_ab.public_key();
    let ctx_a = FrameContext { sensor_id: 9, frame_seq: 1, timestamp_ns: 100 };
    let ctx_b = FrameContext { sensor_id: 9, frame_seq: 2, timestamp_ns: 200 };
    let frame_a = seal_sensor_frame(
        &cores,
        &sk_ab,
        ctx_a,
        2,
        1,
        1,
        SensorModality::Csi2Tile16x16,
        vec![
            RawSensorTile { pixels: vec![100u8; 256], raw_salt: synth_salt(1, 0) },
            RawSensorTile { pixels: vec![0u8; 256], raw_salt: synth_salt(1, 1) },
        ],
        &[0xE3u8; 32],
    )
    .unwrap();
    let frame_b = seal_sensor_frame(
        &cores,
        &sk_ab,
        ctx_b,
        2,
        1,
        1,
        SensorModality::Csi2Tile16x16,
        vec![
            RawSensorTile { pixels: vec![50u8; 256], raw_salt: synth_salt(2, 0) },
            RawSensorTile { pixels: vec![50u8; 256], raw_salt: synth_salt(2, 1) },
        ],
        &[0xE4u8; 32],
    )
    .unwrap();

    let prf_a = prove_ambient_envelope_zk(
        &cores,
        &frame_a.header,
        &frame_a.raw_pcs,
        &frame_a.raw_pixels_flat(),
        &TileSubsetSpec::AllTiles,
        30_000,
        &[0xE5u8; 32],
    )
    .unwrap();
    let prf_b = prove_ambient_envelope_zk(
        &cores,
        &frame_b.header,
        &frame_b.raw_pcs,
        &frame_b.raw_pixels_flat(),
        &TileSubsetSpec::AllTiles,
        30_000,
        &[0xE6u8; 32],
    )
    .unwrap();
    assert_eq!(prf_a.claimed_total, 25_600);
    assert_eq!(prf_b.claimed_total, 25_600);
    verify_ambient_envelope_zk(&cores, &pk_ab, &frame_a.header, &TileSubsetSpec::AllTiles, 30_000, &prf_a)
        .expect("Frame A ambient ZK ok");
    verify_ambient_envelope_zk(&cores, &pk_ab, &frame_b.header, &TileSubsetSpec::AllTiles, 30_000, &prf_b)
        .expect("Frame B ambient ZK ok");

    let wa = prf_a.to_wire_bytes();
    let wb = prf_b.to_wire_bytes();
    // ZERO per-tile sums on the wire: wire structure is identical, and `12800` does not leak in `wb`!
    assert_eq!(prf_a.sumcheck_rounds.len(), prf_b.sumcheck_rounds.len());
    assert_eq!(prf_a.pcs_opening.raw_col_vals.len(), prf_b.pcs_opening.raw_col_vals.len());
    assert!(
        !wb[24..].windows(4).any(|w| w == 12_800u32.to_le_bytes()),
        "cleartext per-tile sum 12800 leaked into AmbientEnvelopeZkProof!"
    );
    println!(
        "[ZERO-TILE-SUM AUDIT] Frame A ([25600, 0]) wire = {} B, Frame B ([12800, 12800]) wire = {} B (0 per-tile sums on wire)",
        wa.len(),
        wb.len()
    );
}

/// Adv 11 (`gpt-6.2-astra` regression): `tile_len = 1` (`m_u = 0`, `hat_v_bits.len() == 0`) completeness
/// and wire roundtrip for BOTH `1x1` and `2x2` frames across blur and ambient ZK proofs.
#[test]
fn adv11_tile_len_one_completeness_and_wire_roundtrip() {
    let cores = CachedCshakeCores::new();
    let sk = EnclaveSigningKey::from_xmss_master_seed(&cores, &[0xF1u8; 32], 2);
    let pk = sk.public_key();

    for &(gw, gh, depth, px_list) in &[
        (1u32, 1u32, 0u32, [173u8].as_slice()),
        (2u32, 2u32, 2u32, [0u8, 42, 128, 255].as_slice()),
    ] {
        let tiles: Vec<RawSensorTile> = px_list
            .iter()
            .enumerate()
            .map(|(i, &p)| RawSensorTile {
                pixels: vec![p],
                raw_salt: synth_salt(gw as u64 * 10 + gh as u64, i),
            })
            .collect();
        let ctx = FrameContext {
            sensor_id: 0x0101,
            frame_seq: (gw * 10 + gh) as u64,
            timestamp_ns: 999_000 + gw as u64,
        };
        let frame = seal_sensor_frame(
            &cores,
            &sk,
            ctx,
            gw,
            gh,
            depth,
            SensorModality::I2sAudioWindow,
            tiles,
            &[0xF2u8; 32],
        )
        .expect("seal tile_len=1 frame");
        let raw_flat = frame.raw_pixels_flat();

        let blur = prove_blur_downscale_zk(
            &cores,
            &frame.header,
            &frame.raw_pcs,
            &raw_flat,
            &TileSubsetSpec::AllTiles,
            &[0xF3u8; 32],
        )
        .expect("prove tile_len=1 blur");
        assert!(blur.hat_v_bits.is_empty());
        assert_eq!(blur.blurred_pixels, px_list);
        let bw = blur.to_wire_bytes();
        let blur_dec = BlurDownscaleZkProof::from_wire_bytes(&bw).expect("decode tile_len=1 blur");
        assert_eq!(blur_dec, blur);
        verify_blur_downscale_zk(&cores, &pk, &frame.header, &TileSubsetSpec::AllTiles, &blur_dec)
            .expect("verify tile_len=1 blur");

        let total: u64 = px_list.iter().map(|&b| b as u64).sum();
        let amb = prove_ambient_envelope_zk(
            &cores,
            &frame.header,
            &frame.raw_pcs,
            &raw_flat,
            &TileSubsetSpec::AllTiles,
            total,
            &[0xF4u8; 32],
        )
        .expect("prove tile_len=1 ambient");
        let aw = amb.to_wire_bytes();
        let amb_dec = AmbientEnvelopeZkProof::from_wire_bytes(&aw).expect("decode tile_len=1 ambient");
        assert_eq!(amb_dec, amb);
        verify_ambient_envelope_zk(&cores, &pk, &frame.header, &TileSubsetSpec::AllTiles, total, &amb_dec)
            .expect("verify tile_len=1 ambient");
    }
}

/// Adv 12 (`gpt-6.2-astra` regression):
/// 1. Direct Rust struct verification rejects non-canonical limbs `>= P_U32` without panicking.
/// 2. `RawPcsCommitment` enforces its atomic cumulative opening budget (`<= shape.c` opened columns)
///    across both blur & ambient proofs AND across `.clone()`d handles.
/// 3. Exhausted single-WOTS key refuses repeated calls cleanly without counter wrap.
#[test]
fn adv12_direct_struct_non_canonical_and_opening_budget_exhausted() {
    let (cores, _sk, pk, frame) = build_4tile_fixture();
    let raw_flat = frame.raw_pixels_flat();
    let sub = TileSubsetSpec::AllTiles;

    // 1st opening (296 / 1024 columns)
    let blur = prove_blur_downscale_zk(&cores, &frame.header, &frame.raw_pcs, &raw_flat, &sub, &[0x11u8; 32])
        .expect("1st opening ok");
    assert_eq!(frame.raw_pcs.opened_columns_used(), 296);

    // Direct-struct non-canonical check on `hat_v_bits[0]` (formerly hit `1 - bk` underflow panic!)
    let mut nc_bit = blur.clone();
    nc_bit.hat_v_bits[0] = Ext4([P_U32, 0, 0, 0]);
    assert_eq!(
        verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &nc_bit).unwrap_err(),
        SensoryRoiError::NonCanonicalFieldElement
    );

    // Direct-struct non-canonical check on `raw_col_vals[0]`
    let mut nc_col = blur.clone();
    nc_col.pcs_opening.raw_col_vals[0] = P_U32;
    assert_eq!(
        verify_blur_downscale_zk(&cores, &pk, &frame.header, &sub, &nc_col).unwrap_err(),
        SensoryRoiError::NonCanonicalFieldElement
    );

    // 2nd opening (592 / 1024 columns)
    let amb = prove_ambient_envelope_zk(&cores, &frame.header, &frame.raw_pcs, &raw_flat, &sub, 500_000, &[0x12u8; 32])
        .expect("2nd opening ok");
    assert_eq!(frame.raw_pcs.opened_columns_used(), 592);

    // Direct-struct non-canonical check on ambient `gmask_sum`
    let mut nc_amb = amb.clone();
    nc_amb.gmask_sum = Ext4([0, P_U32, 0, 0]);
    assert_eq!(
        verify_ambient_envelope_zk(&cores, &pk, &frame.header, &sub, 500_000, &nc_amb).unwrap_err(),
        SensoryRoiError::NonCanonicalFieldElement
    );

    // 3rd opening (888 / 1024 columns) via a CLONED `RawPcsCommitment` shares the same atomic budget!
    let cloned_pcs = frame.raw_pcs.clone();
    prove_ambient_envelope_zk(&cores, &frame.header, &cloned_pcs, &raw_flat, &sub, 500_000, &[0x13u8; 32])
        .expect("3rd opening ok");
    assert_eq!(frame.raw_pcs.opened_columns_used(), 888);

    // 4th opening (888 + 296 = 1184 > 1024) MUST be refused on both original and clone!
    assert_eq!(
        prove_blur_downscale_zk(&cores, &frame.header, &frame.raw_pcs, &raw_flat, &sub, &[0x14u8; 32]).unwrap_err(),
        SensoryRoiError::RawCommitmentOpeningBudgetExhausted {
            opened_cols: 888,
            capacity_cols: 1024,
        }
    );
    assert_eq!(
        prove_ambient_envelope_zk(&cores, &frame.header, &cloned_pcs, &raw_flat, &sub, 500_000, &[0x15u8; 32])
            .unwrap_err(),
        SensoryRoiError::RawCommitmentOpeningBudgetExhausted {
            opened_cols: 888,
            capacity_cols: 1024,
        }
    );

    // Repeated exhausted WOTS calls stay bounded and return `OtsBudgetExhausted`.
    let single_sk = EnclaveSigningKey::from_wots_seed(vec![0x99u8; 32]);
    let t = vec![RawSensorTile { pixels: vec![7u8; 16], raw_salt: synth_salt(99, 0) }];
    let ctx = FrameContext { sensor_id: 9, frame_seq: 1, timestamp_ns: 1 };
    seal_sensor_frame(&cores, &single_sk, ctx, 1, 1, 0, SensorModality::I2sAudioWindow, t.clone(), &[1u8; 32])
        .expect("1st sign ok");
    for _ in 0..3 {
        assert_eq!(
            seal_sensor_frame(&cores, &single_sk, ctx, 1, 1, 0, SensorModality::I2sAudioWindow, t.clone(), &[2u8; 32])
                .err(),
            Some(SensoryRoiError::OtsBudgetExhausted)
        );
    }
}
