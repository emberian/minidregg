//! End-to-end conformance, `1280x720` (`80x45 = 3,600` tiles, `60 fps` budget) streaming
//! benchmark, and 8 adversarial deepfake / bystander-recovery tests for Wearable SHE Organ #4
//! ("Epiphany Lens" — `Assurance/SensoryRoiZeroKnowledge.lean` <-> `sensory_roi_cert.rs`).

#![deny(warnings)]

use std::time::Instant;

use minidregg_prover::babybear::{badd, P as BABYBEAR_P};
use minidregg_prover::sensory_roi_cert::{
    apply_zero_sum_mask, make_zero_sum_mask, seal_csi2_plane_streaming, seal_sensor_frame,
    shift_zero_sum_mask, sum_bytes, verify_blur_envelope_cert, verify_roi_reveal_cert,
    BlurEnvelopeCert, BlurTileEntry, CachedCshakeCores, Digest, FrameContext, RawSensorTile,
    RoiRevealCert, RoiTileOpening, Salt256, SensorModality, SensoryRoiError,
};
use serde::Deserialize;

#[derive(Deserialize)]
struct ConformanceVector {
    schema: String,
    hw_key_hex: String,
    empty_leaf_hex: String,
    csi2_frame: Csi2FrameVec,
    i2s_audio_frame: AudioFrameVec,
    lean_self_checks: LeanSelfChecks,
}

#[derive(Deserialize)]
struct Csi2FrameVec {
    sensor_id: u64,
    frame_seq: u64,
    timestamp_ns: u64,
    grid_width: u32,
    grid_height: u32,
    merkle_depth: u32,
    merkle_root_hex: String,
    header_tag_hex: String,
    tile_leaves_hex: Vec<String>,
    tiles_pixels_hex: Vec<String>,
    tiles_raw_salts_hex: Vec<String>,
    tiles_sum_salts_hex: Vec<String>,
    roi_tile0_path_hex: Vec<String>,
    blur_tile2_sum: u32,
    blur_tile2_mean: u32,
    blur_tile2_sealed_raw_commit_hex: String,
    blur_tile2_path_hex: Vec<String>,
}

#[derive(Deserialize)]
struct AudioFrameVec {
    sensor_id: u64,
    frame_seq: u64,
    timestamp_ns: u64,
    grid_width: u32,
    grid_height: u32,
    merkle_depth: u32,
    merkle_root_hex: String,
    header_tag_hex: String,
    windows_pixels_hex: Vec<String>,
    windows_raw_salts_hex: Vec<String>,
    windows_sum_salts_hex: Vec<String>,
    envelope_sum: u64,
    mask_scalar: u64,
    masked_terms_bb: Vec<u64>,
}

#[derive(Deserialize)]
struct LeanSelfChecks {
    roi_ok: bool,
    splice_refused: bool,
    replay_refused: bool,
    blur_ok: bool,
    forged_blur_refused: bool,
    audio_envelope_ok: bool,
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

fn synth_salt(frame_seq: u64, kind: u8, tile_idx: usize) -> Salt256 {
    let mut s = [0u8; 32];
    s[0..8].copy_from_slice(&frame_seq.to_le_bytes());
    s[8] = kind;
    s[9..17].copy_from_slice(&(tile_idx as u64).to_le_bytes());
    // Mix deterministic non-zero entropy bytes across all 32 bytes.
    for i in 17..32 {
        s[i] = ((tile_idx as u64).wrapping_mul(31) ^ (i as u64 * 17) ^ (kind as u64 * 73)) as u8;
    }
    s
}

/// Byte-exact conformance against Lean 4.35.0 `Assurance/SensoryRoiZeroKnowledge.lean`.
#[test]
fn lean_435_byte_exact_conformance() {
    let raw_json = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/testdata/sensory_roi_conformance.json"
    ))
    .expect("read sensory_roi_conformance.json");
    let vec: ConformanceVector = serde_json::from_str(&raw_json).expect("parse conformance json");
    assert_eq!(vec.schema, "minidregg.sensory_roi_conformance.v1");
    assert!(vec.lean_self_checks.roi_ok);
    assert!(vec.lean_self_checks.splice_refused);
    assert!(vec.lean_self_checks.replay_refused);
    assert!(vec.lean_self_checks.blur_ok);
    assert!(vec.lean_self_checks.forged_blur_refused);
    assert!(vec.lean_self_checks.audio_envelope_ok);
    assert!(vec.lean_self_checks.fresh_salts_ok);

    let cores = CachedCshakeCores::new();
    let hw_key = hex_decode(&vec.hw_key_hex);
    assert_eq!(cores.empty_leaf(), hex_digest(&vec.empty_leaf_hex));

    // 1. CSI-2 2x2 16x16 frame
    let cf = &vec.csi2_frame;
    let csi2_tiles: Vec<RawSensorTile> = (0..cf.tiles_pixels_hex.len())
        .map(|i| RawSensorTile {
            pixels: hex_decode(&cf.tiles_pixels_hex[i]),
            raw_salt: hex_digest(&cf.tiles_raw_salts_hex[i]),
            sum_salt: hex_digest(&cf.tiles_sum_salts_hex[i]),
        })
        .collect();
    let frame = seal_sensor_frame(
        &cores,
        &hw_key,
        FrameContext {
            sensor_id: cf.sensor_id,
            frame_seq: cf.frame_seq,
            timestamp_ns: cf.timestamp_ns,
        },
        cf.grid_width,
        cf.grid_height,
        cf.merkle_depth,
        SensorModality::Csi2Tile16x16,
        csi2_tiles,
    )
    .expect("seal Lean CSI-2 frame");

    assert_eq!(frame.header.merkle_root, hex_digest(&cf.merkle_root_hex));
    assert_eq!(frame.header.header_tag, hex_digest(&cf.header_tag_hex));
    for (i, hex_leaf) in cf.tile_leaves_hex.iter().enumerate() {
        assert_eq!(frame.merkle_layers[0][i], hex_digest(hex_leaf));
    }

    let path0 = frame.open_merkle_path(0);
    let expected_p0: Vec<Digest> = cf.roi_tile0_path_hex.iter().map(|s| hex_digest(s)).collect();
    assert_eq!(path0, expected_p0);
    let roi_cert = frame.open_roi_cert(&[0]);
    verify_roi_reveal_cert(&cores, &hw_key, &frame.header, &roi_cert).expect("verify Lean ROI");

    assert_eq!(frame.tile_sums[2], cf.blur_tile2_sum);
    assert_eq!(frame.tile_sums[2] / 256, cf.blur_tile2_mean);
    assert_eq!(
        frame.raw_commits[2],
        hex_digest(&cf.blur_tile2_sealed_raw_commit_hex)
    );
    let expected_p2: Vec<Digest> = cf.blur_tile2_path_hex.iter().map(|s| hex_digest(s)).collect();
    assert_eq!(frame.open_merkle_path(2), expected_p2);
    let blur_cert = frame.open_blur_cert(&[2], &[0]).expect("open Lean blur cert");
    verify_blur_envelope_cert(&cores, &hw_key, &frame.header, &blur_cert).expect("verify Lean blur");

    // 2. I2S 2-window audio envelope frame
    let af = &vec.i2s_audio_frame;
    let audio_tiles: Vec<RawSensorTile> = (0..af.windows_pixels_hex.len())
        .map(|i| RawSensorTile {
            pixels: hex_decode(&af.windows_pixels_hex[i]),
            raw_salt: hex_digest(&af.windows_raw_salts_hex[i]),
            sum_salt: hex_digest(&af.windows_sum_salts_hex[i]),
        })
        .collect();
    let aframe = seal_sensor_frame(
        &cores,
        &hw_key,
        FrameContext {
            sensor_id: af.sensor_id,
            frame_seq: af.frame_seq,
            timestamp_ns: af.timestamp_ns,
        },
        af.grid_width,
        af.grid_height,
        af.merkle_depth,
        SensorModality::I2sAudioWindow,
        audio_tiles,
    )
    .expect("seal Lean I2S frame");
    assert_eq!(aframe.header.merkle_root, hex_digest(&af.merkle_root_hex));
    assert_eq!(aframe.header.header_tag, hex_digest(&af.header_tag_hex));
    let mask = make_zero_sum_mask(2, &[af.mask_scalar]).unwrap();
    let ac = aframe.open_blur_cert(&[0, 1], &mask).unwrap();
    assert_eq!(ac.claimed_envelope_sum, af.envelope_sum);
    assert_eq!(ac.masked_terms, af.masked_terms_bb);
    verify_blur_envelope_cert(&cores, &hw_key, &aframe.header, &ac).expect("verify Lean I2S");
}

/// Real `1280x720` (`80x45 = 3,600` `16x16` tiles, `60 fps` budget) streaming sealer & verifier bench.
#[test]
fn bench_720p_streaming_sealer_and_verifier_within_60fps_budget() {
    let cores = CachedCshakeCores::new();
    let hw_key = [0x9Bu8; 32];
    let width = 1280usize;
    let height = 720usize;
    let n_tiles = (width / 16) * (height / 16);
    assert_eq!(n_tiles, 3_600);

    let mut y_plane = vec![0u8; width * height];
    for (i, px) in y_plane.iter_mut().enumerate() {
        *px = ((i.wrapping_mul(37) ^ (i >> 5)) & 0xFF) as u8;
    }
    let raw_salts: Vec<Salt256> = (0..n_tiles).map(|i| synth_salt(100, 1, i)).collect();
    let sum_salts: Vec<Salt256> = (0..n_tiles).map(|i| synth_salt(100, 2, i)).collect();

    // Warmup 1 frame to populate caches/thread-pool.
    let ctx0 = FrameContext {
        sensor_id: 0xC512_7200,
        frame_seq: 99,
        timestamp_ns: 1_732_234_567_000_000_000,
    };
    let _ = seal_csi2_plane_streaming(
        &cores, &hw_key, ctx0, width, height, &y_plane, &raw_salts, &sum_salts,
    )
    .expect("warmup seal");

    // Measure 10 frames and take median/mean seal time.
    let rounds = 10usize;
    let t0 = Instant::now();
    let mut handle = None;
    for r in 0..rounds {
        let ctx = FrameContext {
            sensor_id: 0xC512_7200,
            frame_seq: 100 + r as u64,
            timestamp_ns: 1_732_234_567_000_000_000 + (r as u64) * 16_666_667,
        };
        handle = Some(
            seal_csi2_plane_streaming(
                &cores, &hw_key, ctx, width, height, &y_plane, &raw_salts, &sum_salts,
            )
            .expect("720p seal"),
        );
    }
    let seal_ms = t0.elapsed().as_secs_f64() * 1000.0 / (rounds as f64);
    let handle = handle.unwrap();

    // Build an authorized central AR frustum ROI (64 tiles = 128x128px sign/QR) + 64 blurred context tiles.
    let roi_indices: Vec<u32> = (0..64u32).map(|k| (18 + k / 8) * 80 + (36 + k % 8)).collect();
    let blur_indices: Vec<u32> = (0..64u32).map(|k| (10 + k / 8) * 80 + (10 + k % 8)).collect();
    let roi_cert = handle.open_roi_cert(&y_plane, &raw_salts, &sum_salts, &roi_indices);
    let mask_scalars: Vec<u64> = (0..63u64).map(|k| 100_003 + k * 7919).collect();
    let zero_mask = make_zero_sum_mask(blur_indices.len(), &mask_scalars).unwrap();
    let blur_cert = handle
        .open_blur_cert(&sum_salts, &blur_indices, &zero_mask)
        .unwrap();

    let tv = Instant::now();
    let v_rounds = 20usize;
    for _ in 0..v_rounds {
        verify_roi_reveal_cert(&cores, &hw_key, &handle.header, &roi_cert).unwrap();
        verify_blur_envelope_cert(&cores, &hw_key, &handle.header, &blur_cert).unwrap();
    }
    let verify_ms = tv.elapsed().as_secs_f64() * 1000.0 / (v_rounds as f64);

    println!(
        "[720p BENCH] 1280x720 (80x45 = 3,600 tiles, depth 12): seal = {seal_ms:.3} ms/frame (budget < 4.0 ms), verify (64 ROI + 64 blur) = {verify_ms:.3} ms (budget < 2.0 ms)"
    );
    assert!(
        seal_ms < 4.0,
        "720p streaming seal exceeded 4.0 ms budget: {seal_ms:.3} ms"
    );
    assert!(
        verify_ms < 2.0,
        "ROI + blur verification exceeded 2.0 ms budget: {verify_ms:.3} ms"
    );
}

fn build_4tile_fixture() -> (CachedCshakeCores, Vec<u8>, minidregg_prover::sensory_roi_cert::SealedSensorFrame) {
    let cores = CachedCshakeCores::new();
    let hw_key = vec![0x77u8; 32];
    let ctx = FrameContext {
        sensor_id: 0x0E91_0004,
        frame_seq: 55,
        timestamp_ns: 1_732_234_567_500_000_000,
    };
    let tiles = vec![
        RawSensorTile {
            pixels: (0..256).map(|k| ((k * 3 + 11) % 256) as u8).collect(),
            raw_salt: synth_salt(55, 1, 0),
            sum_salt: synth_salt(55, 2, 0),
        },
        RawSensorTile {
            pixels: b"BYSTANDER_FACE_SECRET_BIOMETRIC_VECTOR_DO_NOT_LEAK_0123456789___"
                .repeat(4),
            raw_salt: synth_salt(55, 1, 1),
            sum_salt: synth_salt(55, 2, 1),
        },
        RawSensorTile {
            pixels: (0..256).map(|k| ((k * 5 + 7) % 256) as u8).collect(),
            raw_salt: synth_salt(55, 1, 2),
            sum_salt: synth_salt(55, 2, 2),
        },
        RawSensorTile {
            pixels: b"BYSTANDER_LAPTOP_SCREEN_API_KEY_SK_LIVE_999999999999999999999999"
                .repeat(4),
            raw_salt: synth_salt(55, 1, 3),
            sum_salt: synth_salt(55, 2, 3),
        },
    ];
    let frame = seal_sensor_frame(
        &cores,
        &hw_key,
        ctx,
        2,
        2,
        2,
        SensorModality::Csi2Tile16x16,
        tiles,
    )
    .expect("seal 4-tile fixture");
    (cores, hw_key, frame)
}

/// Adversarial Test 1: Deepfake 1-pixel LSB splice inside an authorized ROI tile is refused.
#[test]
fn adv1_synthetic_one_pixel_lsb_splice_refused() {
    let (cores, hw_key, frame) = build_4tile_fixture();
    let mut cert = frame.open_roi_cert(&[0]);
    cert.openings[0].pixels[137] ^= 0x01; // 1-bit synthetic pixel edit
    let err = verify_roi_reveal_cert(&cores, &hw_key, &frame.header, &cert).unwrap_err();
    assert_eq!(err, SensoryRoiError::MerklePathMismatch { tile_idx: 0 });
}

/// Adversarial Test 2: Cross-timestamp / cross-sequence replay of an authentic frame cert is refused.
#[test]
fn adv2_cross_timestamp_and_seq_replay_refused() {
    let (cores, hw_key, frame) = build_4tile_fixture();
    let cert = frame.open_roi_cert(&[0]);
    let mut forged_ts = frame.header.clone();
    forged_ts.ctx.timestamp_ns += 1;
    assert_eq!(
        verify_roi_reveal_cert(&cores, &hw_key, &forged_ts, &cert).unwrap_err(),
        SensoryRoiError::HeaderAttestationMismatch
    );
    // Even if re-signed as a NEW frame header at timestamp_ns + 1, replaying tile 0's opening fails!
    let mut tiles_f2 = frame.tiles.clone();
    tiles_f2[0].raw_salt = synth_salt(56, 1, 0);
    tiles_f2[0].sum_salt = synth_salt(56, 2, 0);
    let f2 = seal_sensor_frame(
        &cores,
        &hw_key,
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
    )
    .unwrap();
    assert_eq!(
        verify_roi_reveal_cert(&cores, &hw_key, &f2.header, &cert).unwrap_err(),
        SensoryRoiError::MerklePathMismatch { tile_idx: 0 }
    );
}

/// Adversarial Test 3: Grafting an authentic tile from coordinate `i1` into `i2` is refused.
#[test]
fn adv3_tile_coordinate_graft_refused() {
    let (cores, hw_key, frame) = build_4tile_fixture();
    let grafted = RoiRevealCert {
        openings: vec![RoiTileOpening {
            tile_idx: 2, // Claim tile 0's authentic pixels & salts sit at tile 2!
            pixels: frame.tiles[0].pixels.clone(),
            raw_salt: frame.tiles[0].raw_salt,
            sum_salt: frame.tiles[0].sum_salt,
            merkle_path: frame.open_merkle_path(2),
        }],
    };
    assert_eq!(
        verify_roi_reveal_cert(&cores, &hw_key, &frame.header, &grafted).unwrap_err(),
        SensoryRoiError::MerklePathMismatch { tile_idx: 2 }
    );
}

/// Adversarial Test 4: Reused or unmasked per-tile hardware TRNG salts are refused.
#[test]
fn adv4_unmasked_salt_reuse_refused() {
    let cores = CachedCshakeCores::new();
    let hw_key = vec![0x77u8; 32];
    let ctx = FrameContext {
        sensor_id: 1,
        frame_seq: 1,
        timestamp_ns: 1,
    };
    // Case A: raw_salt == sum_salt within one tile
    let dup_within = vec![RawSensorTile {
        pixels: vec![10; 256],
        raw_salt: synth_salt(1, 1, 0),
        sum_salt: synth_salt(1, 1, 0),
    }];
    assert_eq!(
        seal_sensor_frame(&cores, &hw_key, ctx, 1, 1, 0, SensorModality::Csi2Tile16x16, dup_within)
            .err(),
        Some(SensoryRoiError::SaltReuseDetected { tile_idx: 0 })
    );
    // Case B: two tiles share raw_salt
    let dup_across = vec![
        RawSensorTile {
            pixels: vec![10; 256],
            raw_salt: synth_salt(1, 1, 0),
            sum_salt: synth_salt(1, 2, 0),
        },
        RawSensorTile {
            pixels: vec![20; 256],
            raw_salt: synth_salt(1, 1, 0),
            sum_salt: synth_salt(1, 2, 1),
        },
    ];
    assert_eq!(
        seal_sensor_frame(&cores, &hw_key, ctx, 2, 1, 1, SensorModality::Csi2Tile16x16, dup_across)
            .err(),
        Some(SensoryRoiError::SaltReuseDetected { tile_idx: 1 })
    );
}

/// Adversarial Test 5: Forged privacy-blur `16x16 -> 1x1` mean or `+1` tile sum is refused.
#[test]
fn adv5_forged_blur_mean_and_sum_refused() {
    let (cores, hw_key, frame) = build_4tile_fixture();
    let mut bad_mean = frame.open_blur_cert(&[2], &[0]).unwrap();
    bad_mean.entries[0].mean_value += 1;
    assert!(matches!(
        verify_blur_envelope_cert(&cores, &hw_key, &frame.header, &bad_mean),
        Err(SensoryRoiError::InvalidBlurMean { tile_idx: 2, .. })
    ));

    let mut bad_sum = frame.open_blur_cert(&[2], &[0]).unwrap();
    bad_sum.entries[0].tile_sum += 1;
    bad_sum.entries[0].mean_value = bad_sum.entries[0].tile_sum / bad_sum.entries[0].tile_len;
    bad_sum.claimed_envelope_sum += 1;
    bad_sum.masked_terms[0] = badd(bad_sum.masked_terms[0], 1);
    assert_eq!(
        verify_blur_envelope_cert(&cores, &hw_key, &frame.header, &bad_sum).unwrap_err(),
        SensoryRoiError::MerklePathMismatch { tile_idx: 2 }
    );
}

/// Adversarial Test 6: Forged ambient-dB envelope, `BabyBear` sumcheck tampering, & duplicate-tile inflation refused.
#[test]
fn adv6_forged_ambient_db_envelope_and_dup_tile_refused() {
    let (cores, hw_key, frame) = build_4tile_fixture();
    let mask = make_zero_sum_mask(2, &[555_555]).unwrap();
    let mut bad_bb = frame.open_blur_cert(&[0, 2], &mask).unwrap();
    bad_bb.masked_terms[0] = badd(bad_bb.masked_terms[0], 1);
    assert!(matches!(
        verify_blur_envelope_cert(&cores, &hw_key, &frame.header, &bad_bb),
        Err(SensoryRoiError::BabyBearSumcheckMismatch { .. })
    ));

    // Duplicate tile 2 twice to try doubling the ambient-dB energy sum
    let e2 = frame.open_blur_cert(&[2], &[0]).unwrap().entries[0].clone();
    let dup_cert = BlurEnvelopeCert {
        entries: vec![e2.clone(), e2.clone()],
        claimed_envelope_sum: (e2.tile_sum as u64) * 2,
        masked_terms: vec![e2.tile_sum as u64, e2.tile_sum as u64],
    };
    assert_eq!(
        verify_blur_envelope_cert(&cores, &hw_key, &frame.header, &dup_cert).unwrap_err(),
        SensoryRoiError::DuplicateTileIndex(2)
    );
}

/// Adversarial Test 7: Zero-bystander-leakage wire-byte & view-independence audit.
#[test]
fn adv7_zero_bystander_pixel_and_salt_leakage_audit() {
    let (cores, hw_key, frame) = build_4tile_fixture();
    let roi_cert = frame.open_roi_cert(&[0]);
    let blur_cert = frame.open_blur_cert(&[2], &[0]).unwrap();
    verify_roi_reveal_cert(&cores, &hw_key, &frame.header, &roi_cert).unwrap();
    verify_blur_envelope_cert(&cores, &hw_key, &frame.header, &blur_cert).unwrap();

    let roi_wire = roi_cert.to_wire_bytes();
    let blur_wire = blur_cert.to_wire_bytes();

    // Neither bystander face (tile 1) nor bystander laptop screen (tile 3) nor their salts appear anywhere!
    for forbidden in [
        b"BYSTANDER_FACE".as_slice(),
        b"SECRET_BIOMETRIC".as_slice(),
        b"BYSTANDER_LAPTOP".as_slice(),
        b"SK_LIVE_9999".as_slice(),
        &frame.tiles[1].raw_salt,
        &frame.tiles[1].sum_salt,
        &frame.tiles[3].raw_salt,
        &frame.tiles[3].sum_salt,
        &frame.tiles[2].raw_salt, // Even for blurred tile 2, raw_salt & raw pixels NEVER appear!
    ] {
        assert!(
            !roi_wire.windows(forbidden.len()).any(|w| w == forbidden),
            "bystander/secret byte slice leaked into ROI wire cert!"
        );
        assert!(
            !blur_wire.windows(forbidden.len()).any(|w| w == forbidden),
            "bystander/secret byte slice leaked into Blur wire cert!"
        );
    }

    // Mutating tile 1 & tile 3 bystander pixels leaves opened item 0 in RoiRevealView byte-identical!
    let mut mutated_tiles = frame.tiles.clone();
    mutated_tiles[1].pixels.fill(0xAA);
    mutated_tiles[3].pixels.fill(0x55);
    let mutated_frame = seal_sensor_frame(
        &cores,
        &hw_key,
        frame.header.ctx,
        2,
        2,
        2,
        SensorModality::Csi2Tile16x16,
        mutated_tiles,
    )
    .unwrap();
    let (_, view_orig) = frame.roi_view(|i| i == 0);
    let (_, view_mut) = mutated_frame.roi_view(|i| i == 0);
    assert_eq!(view_orig[0], view_mut[0]); // Opened ROI tile 0 identical
    assert_ne!(view_orig[1], view_mut[1]); // Sealed bystander tile 1 changed only its 32-byte digest
    assert_ne!(view_orig[3], view_mut[3]); // Sealed bystander tile 3 changed only its 32-byte digest
    assert_eq!(view_orig[2], view_mut[2]); // Untouched sealed tile 2 identical
}

/// Adversarial Test 8: Unconditional zero-sum `BabyBear` masking bijection (`TVD = 0` formant hiding).
#[test]
fn adv8_zero_sum_babybear_mask_bijection_hides_speech_formants() {
    // Two completely different 64-sample I2S audio windows ("secret spoken word" vs flat ambient hum)
    // with the EXACT same ambient-dB energy sum `E_win = 3200`.
    let spoken_formants: Vec<u8> = (0..64)
        .map(|i| if i % 2 == 0 { 90 } else { 10 })
        .collect();
    let flat_ambient: Vec<u8> = vec![50u8; 64];
    assert_eq!(sum_bytes(&spoken_formants), 3200);
    assert_eq!(sum_bytes(&flat_ambient), 3200);
    assert_ne!(spoken_formants, flat_ambient);

    let scalars: Vec<u64> = (0..63u64).map(|k| 123_456_789u64 + k * 999_983).collect();
    let mask = make_zero_sum_mask(64, &scalars).unwrap();
    let view_spoken = apply_zero_sum_mask(&spoken_formants, &mask).unwrap();

    // Exact sum preservation over BabyBear with zero modular wrap-around
    let mut sum_bb = 0u64;
    for &y in &view_spoken {
        sum_bb = badd(sum_bb, y);
    }
    assert_eq!(sum_bb, 3200);
    assert!(3200 < BABYBEAR_P);

    // Explicit bijection maps `mask` -> `shifted_mask` so `flat_ambient` produces the EXACT SAME view!
    let shifted_mask = shift_zero_sum_mask(&spoken_formants, &flat_ambient, &mask).unwrap();
    let view_ambient = apply_zero_sum_mask(&flat_ambient, &shifted_mask).unwrap();
    assert_eq!(view_spoken, view_ambient);

    // Involution check (bijection on zero-sum masks => exact TVD = 0!)
    let roundtrip_mask = shift_zero_sum_mask(&flat_ambient, &spoken_formants, &shifted_mask).unwrap();
    assert_eq!(roundtrip_mask, mask);

    // Extra negative check: forged BlurTileEntry with out-of-range sum > tile_len * 255 refused
    let (cores, hw_key, frame) = build_4tile_fixture();
    let bad_range = BlurEnvelopeCert {
        entries: vec![BlurTileEntry {
            tile_idx: 2,
            tile_sum: 256 * 255 + 1,
            tile_len: 256,
            mean_value: 255,
            sum_salt: frame.tiles[2].sum_salt,
            sealed_raw_commit: frame.raw_commits[2],
            merkle_path: frame.open_merkle_path(2),
        }],
        claimed_envelope_sum: 256 * 255 + 1,
        masked_terms: vec![256 * 255 + 1],
    };
    assert!(matches!(
        verify_blur_envelope_cert(&cores, &hw_key, &frame.header, &bad_range),
        Err(SensoryRoiError::InvalidBlurSum { tile_idx: 2, .. })
    ));
}
