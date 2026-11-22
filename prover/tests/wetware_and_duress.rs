//! Conformance, theorem-mirror, `#tooth` and `--release` benchmark tests for
//! `minidregg_prover::wetware_duress_guard` against `Theory/WetwareSafetyAndDuress.lean`.

#![deny(warnings)]

use std::time::Instant;

use minidregg_prover::hash_kernels::cshake256_xof;
use minidregg_prover::wetware_duress_guard::*;
use serde_json::Value;
use sha3::{Digest, Sha3_256};

fn conformance() -> Value {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/testdata/wetware_duress_conformance.json");
    serde_json::from_str(&std::fs::read_to_string(path).expect("read conformance json"))
        .expect("parse conformance json")
}

fn bytes(v: &Value) -> Vec<u8> {
    v.as_array().unwrap().iter().map(|x| x.as_u64().unwrap() as u8).collect()
}

fn params(v: &Value) -> ScrubParams {
    ScrubParams {
        q: v["q"].as_u64().unwrap() as u8,
        dmax: v["dmax"].as_u64().unwrap() as u8,
        hold: v["hold"].as_u64().unwrap() as u8,
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

// ---------------------------------------------------------------------------
// Observer (independent of the scrubber): Lean `odir` / `revAt` over a trace.
// ---------------------------------------------------------------------------

/// `revAt o t` for every `t` of a trace `o` (with `o[0] = p0`).
fn reversals(o: &[u8]) -> Vec<bool> {
    let mut rev = vec![false; o.len()];
    let mut odir = DIR_FLAT;
    for t in 1..o.len() {
        if o[t] != o[t - 1] {
            let s = dir_of(o[t - 1], o[t]);
            rev[t] = is_rev(odir, s);
            odir = s;
        }
    }
    rev
}

/// `PhotosafeTrace`: slew bound + reversal spacing; returns the max reversals in any window.
fn check_photosafe(o: &[u8], p: ScrubParams, window: usize) -> usize {
    for t in 1..o.len() {
        let d = (o[t] as i32 - o[t - 1] as i32).abs();
        assert!(d <= p.dmax as i32, "slew {d} > {} at {t}", p.dmax);
    }
    let rev = reversals(o);
    let idx: Vec<usize> = (0..o.len()).filter(|&t| rev[t]).collect();
    for w in idx.windows(2) {
        assert!(w[1] - w[0] >= p.hold as usize, "reversals {} and {} too close", w[0], w[1]);
    }
    let mut worst = 0;
    for a in 0..o.len().saturating_sub(window) {
        worst = worst.max(rev[a..a + window].iter().filter(|&&b| b).count());
    }
    worst
}

fn trace(p0: u8, emitted: &[u8]) -> Vec<u8> {
    let mut o = vec![p0];
    o.extend_from_slice(emitted);
    o
}

// ---------------------------------------------------------------------------
// Part A: conformance with the Lean pins
// ---------------------------------------------------------------------------

#[test]
fn scrubber_matches_lean_pinned_vectors() {
    let c = conformance();
    let vs = c["scrubber_vectors"].as_array().unwrap();
    assert_eq!(vs.len(), 7);
    for v in vs {
        let p = params(&v["params"]);
        let p0 = v["p0"].as_u64().unwrap() as u8;
        let input = bytes(&v["input"]);
        let want = bytes(&v["emitted"]);
        let got = scrub_stream(p, p0, &input).unwrap();
        assert_eq!(got, want, "vector {}", v["name"]);
        // FrameScrubber on a 1-channel frame is the same machine.
        let mut fs = FrameScrubber::new(p, 1, p0).unwrap();
        let framed: Vec<u8> = input
            .iter()
            .map(|&x| {
                let mut b = [x];
                fs.scrub_frame(&mut b).unwrap();
                b[0]
            })
            .collect();
        assert_eq!(framed, want, "framed vector {}", v["name"]);
    }
    // The triangle is safe canonical: the Lean fixpoint theorem says it passes unchanged.
    let tri = vs.iter().find(|v| v["name"] == "triangle_safe_canonical").unwrap();
    assert_eq!(bytes(&tri["input"]), bytes(&tri["emitted"]));
    // The two stego streams differ raw and agree scrubbed.
    let a = vs.iter().find(|v| v["name"] == "stego_lsb_key_A").unwrap();
    let b = vs.iter().find(|v| v["name"] == "stego_lsb_key_B").unwrap();
    assert_ne!(bytes(&a["input"]), bytes(&b["input"]));
    assert_eq!(bytes(&a["emitted"]), bytes(&b["emitted"]));
}

#[test]
fn audio_and_cadence_match_lean_pins() {
    let c = conformance();
    for v in c["cadence"].as_array().unwrap() {
        let got = snap_release(v["period"].as_u64().unwrap(), v["tau"].as_u64().unwrap()).unwrap();
        assert_eq!(got, v["release"].as_u64().unwrap());
    }
    for v in c["audio"].as_array().unwrap() {
        let k = v["k"].as_u64().unwrap() as u32;
        let s = v["s"].as_u64().unwrap() as u16;
        assert_eq!(quant_audio(k, s).unwrap() as u64, v["q"].as_u64().unwrap());
    }
    // i16 PCM view agrees with the offset-binary model for every sample and k.
    for k in 0..16u32 {
        for s in (i16::MIN..=i16::MAX).step_by(7) {
            let off = (s as i32 + 32768) as u16;
            let q = quant_audio(k, off).unwrap() as i32 - 32768;
            assert_eq!(quant_audio_i16(k, s).unwrap() as i32, q);
        }
    }
    assert_eq!(snap_release(0, 5), Err(WetwareError::ZeroPeriod));
    assert_eq!(quant_audio(16, 5), Err(WetwareError::AudioShift(16)));
}

// ---------------------------------------------------------------------------
// Part A: theorem mirrors over random streams (executed evidence, not proof)
// ---------------------------------------------------------------------------

fn random_stream(drbg: &mut XofDrbg, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    drbg.fill(&mut v);
    // Mix in adversarial structure: strobes at random periods.
    let mut sel = [0u8; 2];
    drbg.fill(&mut sel);
    let period = 2 + (sel[0] % 20) as usize;
    if sel[1] % 2 == 0 {
        for (t, x) in v.iter_mut().enumerate() {
            *x = if (t / (period / 2).max(1)) % 2 == 0 { *x & 3 } else { 252 | (*x & 3) };
        }
    }
    v
}

#[test]
fn scrubber_enforces_slew_and_reversal_bound_fuzz() {
    let mut drbg = XofDrbg::new(b"photosafe-fuzz");
    for p in [WEARABLE60, ScrubParams { q: 8, dmax: 24, hold: 6 }, ScrubParams { q: 1, dmax: 7, hold: 30 }] {
        for _ in 0..400 {
            let xs = random_stream(&mut drbg, 600);
            let p0 = quant(p.q, xs[0]);
            let o = trace(p0, &scrub_stream(p, p0, &xs).unwrap());
            let worst = check_photosafe(&o, p, 60);
            // revSpaced_count_le: at most ceil(60 / hold) reversals in any 60-frame window.
            assert!(worst <= 60usize.div_ceil(p.hold as usize));
            if p == WEARABLE60 {
                assert!(worst <= 5, "wearable60_at_most_5_reversals_per_second");
            }
            for &y in &o {
                assert_eq!(y % p.q, 0, "scrubber_output_is_lattice_byte");
            }
        }
    }
}

#[test]
fn scrubber_kills_subthreshold_stego_fuzz() {
    let mut drbg = XofDrbg::new(b"stego-fuzz");
    let p = WEARABLE60;
    for _ in 0..400 {
        let xs = random_stream(&mut drbg, 300);
        let mut lsb = vec![0u8; xs.len()];
        drbg.fill(&mut lsb);
        let twin: Vec<u8> = xs.iter().zip(&lsb).map(|(&x, &r)| (x & !3) | (r & 3)).collect();
        assert_eq!(scrub_stream(p, 128, &xs).unwrap(), scrub_stream(p, 128, &twin).unwrap());
    }
    // Cadence jitter: any sub-period offset releases on the same boundary.
    let period = 16_667u64;
    for n in 0..200u64 {
        let mut j = [0u8; 4];
        drbg.fill(&mut j);
        let j = u32::from_le_bytes(j) as u64 % period;
        assert_eq!(snap_release(period, n * period).unwrap(), snap_release(period, n * period + j).unwrap());
    }
}

#[test]
fn scrubber_idempotent_on_safe_canonical_fuzz() {
    let mut drbg = XofDrbg::new(b"idempotence-fuzz");
    for p in [WEARABLE60, ScrubParams { q: 8, dmax: 24, hold: 6 }] {
        for _ in 0..300 {
            let xs = random_stream(&mut drbg, 400);
            let once = scrub_stream(p, 0, &xs).unwrap();
            let twice = scrub_stream(p, 0, &once).unwrap();
            assert_eq!(once, twice);
        }
    }
}

// ---------------------------------------------------------------------------
// Part A: #tooth
// ---------------------------------------------------------------------------

fn strobe15(n: usize) -> Vec<u8> {
    (0..n).map(|t| if t % 4 < 2 { 0 } else { 252 }).collect()
}

#[test]
fn tooth_15hz_strobe() {
    let raw = strobe15(120);
    let rev = reversals(&trace(0, &raw));
    assert!(rev[5] && rev[7], "raw strobe reverses every 2 frames");
    let o = trace(0, &scrub_stream(WEARABLE60, 0, &raw).unwrap());
    assert!(check_photosafe(&o, WEARABLE60, 60) <= 5);
    assert_eq!(o[7], 0, "tooth_15hz_strobe_caught: second edge held");
    // tooth_hold_off_load_bearing: without the hold-off the strobe reaches the eye.
    let no_hold = ScrubParams { q: 4, dmax: 16, hold: 1 };
    let o2 = trace(0, &scrub_stream(no_hold, 0, &raw).unwrap());
    let r2 = reversals(&o2);
    assert!(r2[5] && r2[7]);
}

#[test]
fn tooth_lsb_keystream() {
    let cover = |t: usize| 128 + 4 * (t % 8) as u8;
    let bits = |key: u8, t: usize| (key >> (2 * (t % 4))) & 3;
    let a: Vec<u8> = (0..64).map(|t| cover(t) + bits(0xB4, t)).collect();
    let b: Vec<u8> = (0..64).map(|t| cover(t) + bits(0x1F, t)).collect();
    assert_ne!(a, b);
    assert_eq!(scrub_stream(WEARABLE60, 128, &a).unwrap(), scrub_stream(WEARABLE60, 128, &b).unwrap());
    // tooth_no_quant_leaks.
    let nq = ScrubParams { q: 1, dmax: 16, hold: 12 };
    assert_ne!(scrub_stream(nq, 128, &a).unwrap(), scrub_stream(nq, 128, &b).unwrap());
}

/// `tooth_per_channel_rgb_misses_luma_flicker`: two reversal-free channels whose sum flickers
/// at 30 Hz; the guard must run on luma, where it does bound the flicker.
#[test]
fn tooth_per_channel_rgb_misses_luma_flicker() {
    let r: Vec<u8> = (0..24).map(|t| 16 * ((t + 1) / 2) as u8).collect();
    let g: Vec<u8> = (0..24).map(|t| 200 - 16 * (t / 2) as u8).collect();
    let rs = scrub_stream(WEARABLE60, 0, &r).unwrap();
    let gs = scrub_stream(WEARABLE60, 200, &g).unwrap();
    assert!(reversals(&trace(0, &rs)).iter().all(|&b| !b));
    assert!(reversals(&trace(200, &gs)).iter().all(|&b| !b));
    let luma_after_rgb_guard: Vec<u8> = rs.iter().zip(&gs).map(|(&a, &b)| ((a as u16 + b as u16) / 2) as u8).collect();
    let rv = reversals(&trace(100, &luma_after_rgb_guard));
    assert!(rv.windows(2).any(|w| w[0] && w[1]), "per-RGB guarding lets 30 Hz luma flicker through");
    // Guarding the luma plane itself bounds it.
    let luma_raw: Vec<u8> = r.iter().zip(&g).map(|(&a, &b)| ((a as u16 + b as u16) / 2) as u8).collect();
    let o = trace(100, &scrub_stream(WEARABLE60, 100, &luma_raw).unwrap());
    assert!(check_photosafe(&o, WEARABLE60, 60) <= 5);
}

#[test]
fn invalid_params_refused() {
    for p in [
        ScrubParams { q: 0, dmax: 16, hold: 12 },
        ScrubParams { q: 4, dmax: 15, hold: 12 },
        ScrubParams { q: 4, dmax: 16, hold: 0 },
    ] {
        assert_eq!(scrub_stream(p, 0, &[1]), Err(WetwareError::InvalidParams(p)));
    }
    assert_eq!(FrameScrubber::new(WEARABLE60, 4, 3).unwrap_err(), WetwareError::InitialLevelOffLattice(3));
    let mut fs = FrameScrubber::new(WEARABLE60, 4, 0).unwrap();
    assert_eq!(fs.scrub_frame(&mut [0u8; 3]), Err(WetwareError::FrameLength { expected: 4, got: 3 }));
}

// ---------------------------------------------------------------------------
// Part B: vault
// ---------------------------------------------------------------------------

#[test]
fn cshake256_nist_kat() {
    let c = conformance();
    let k = &c["cshake256_kat"];
    let input: Vec<u8> = (0..4).collect();
    let out = cshake256_xof(k["customization"].as_str().unwrap().as_bytes(), &input, 64);
    assert_eq!(hex(&out), k["output_hex"].as_str().unwrap());
}

const N: usize = 16;

fn body(tag: &str) -> Body {
    let mut b = [0u8; BODY_BYTES];
    b[..tag.len()].copy_from_slice(tag.as_bytes());
    b
}

fn build(nonce_seed: &[u8], with_sovereign: bool) -> (DuressVault, Root, Root) {
    let mut drbg = XofDrbg::new(nonce_seed);
    let mut nonce = [0u8; NONCE_BYTES];
    drbg.fill(&mut nonce);
    let dk = derive_root(b"duress passphrase", &nonce);
    let sk = derive_root(b"sovereign passphrase", &nonce);
    let decoys = [(1usize, body("decoy:worldtree-root-A")), (6, body("decoy:credential-B"))];
    let sov = [(3usize, body("SOVR:root-key-1")), (11, body("SOVR:root-key-2"))];
    let mut occ: Vec<Occupant<'_>> = decoys.iter().map(|&(slot, b)| Occupant { root: &dk, slot, body: b }).collect();
    if with_sovereign {
        occ.extend(sov.iter().map(|&(slot, b)| Occupant { root: &sk, slot, body: b }));
    }
    let v = DuressVault::create(nonce, N, &occ, &mut |buf| drbg.fill(buf)).unwrap();
    (v, dk, sk)
}

#[test]
fn duress_unlock_correct_and_roots_separated() {
    let (v, dk, sk) = build(b"vault-1", true);
    let d = v.unlock(&dk);
    assert_eq!(d, vec![(1, body("decoy:worldtree-root-A")), (6, body("decoy:credential-B"))]);
    let s = v.unlock(&sk);
    assert_eq!(s, vec![(3, body("SOVR:root-key-1")), (11, body("SOVR:root-key-2"))]);
    // The duress view is identical with and without a sovereign root.
    let (v0, dk0, _) = build(b"vault-1", false);
    assert_eq!(v0.unlock(&dk0), d);
    // Fixed geometry: identical image length.
    assert_eq!(v.to_bytes().len(), v0.to_bytes().len());
    assert_eq!(v.to_bytes().len(), DuressVault::image_len(N));
    assert_eq!(DuressVault::from_bytes(&v.to_bytes(), N).unwrap(), v);
    assert!(DuressVault::from_bytes(&v.to_bytes()[1..], N).is_err());
}

#[test]
fn duress_write_never_touches_unowned_slots() {
    let (mut v, dk, sk) = build(b"vault-2", true);
    assert_eq!(v.rewrite_owned(&dk, 3, &body("overwrite")), Err(DuressError::NotOwned(3)));
    assert_eq!(v.rewrite_owned(&dk, 2, &body("overwrite")), Err(DuressError::NotOwned(2)));
    v.rewrite_owned(&dk, 6, &body("decoy:credential-B2")).unwrap();
    assert_eq!(v.unlock(&sk).len(), 2, "sovereign slots survive duress-side writes");
    assert_eq!(v.unlock(&dk)[1], (6, body("decoy:credential-B2")));
    let mut nonce = [0u8; 32];
    XofDrbg::new(b"x").fill(&mut nonce);
    let dup = [Occupant { root: &dk, slot: 2, body: body("a") }, Occupant { root: &sk, slot: 2, body: body("b") }];
    assert_eq!(DuressVault::create(nonce, 4, &dup, &mut |_| {}), Err(DuressError::DuplicateSlot(2)));
    assert_eq!(DuressVault::create(nonce, 0, &[], &mut |_| {}), Err(DuressError::ZeroSlots));
}

/// Executed sanity check, not a proof: hidden-slot bytes from sovereign blocks and from chaff
/// have indistinguishable byte histograms (chi-square, 255 dof) to an observer holding `dk`.
#[test]
fn hidden_slots_byte_statistics() {
    let mut hist_sov = [0u64; 256];
    let mut hist_chaff = [0u64; 256];
    for k in 0..400u32 {
        let seed = format!("stat-{k}");
        let (v, dk, _) = build(seed.as_bytes(), true);
        let opened: Vec<usize> = v.unlock(&dk).iter().map(|x| x.0).collect();
        for (i, b) in v.slots.iter().enumerate() {
            if opened.contains(&i) {
                continue;
            }
            let h = if i == 3 || i == 11 { &mut hist_sov } else { &mut hist_chaff };
            for &x in b.iter() {
                h[x as usize] += 1;
            }
        }
    }
    let chi = |h: &[u64; 256]| {
        let n: u64 = h.iter().sum();
        let e = n as f64 / 256.0;
        h.iter().map(|&c| (c as f64 - e).powi(2) / e).sum::<f64>()
    };
    let (cs, cc) = (chi(&hist_sov), chi(&hist_chaff));
    println!("chi2(sovereign)={cs:.1} chi2(chaff)={cc:.1} (255 dof; p=1e-6 critical ≈ 370)");
    assert!(cs < 370.0 && cc < 370.0);
}

/// `#tooth` (`tooth_shared_salt_kdf_breaks`): a root-unseparated pad (derived from the shared
/// public salt alone) lets the duress holder strip it and spot the sovereign format header.
#[test]
fn tooth_shared_salt_pad_breaks_deniability() {
    let (v, _, _) = build(b"vault-3", false);
    let nonce = v.nonce;
    let shared_pad = |i: u32| cshake256_xof(b"BROKEN/PAD", &slot_salt(&nonce, i), SLOT_BYTES);
    let mut broken = v.clone();
    for &i in &[3u32, 11] {
        let b = body("SOVR:root-key");
        for k in 0..SLOT_BYTES {
            broken.slots[i as usize][k] = (if k < BODY_BYTES { b[k] } else { 0 }) ^ shared_pad(i)[k];
        }
    }
    let flag = |vault: &DuressVault| -> Vec<usize> {
        (0..N)
            .filter(|&i| {
                let p = shared_pad(i as u32);
                (0..4).all(|k| vault.slots[i][k] ^ p[k] == b"SOVR"[k])
            })
            .collect()
    };
    assert_eq!(flag(&broken), vec![3, 11], "broken scheme: advantage ≈ 1");
    let (good, _, _) = build(b"vault-3", true);
    assert!(flag(&good).is_empty(), "separated pads: the header test sees only noise");
}

/// `#tooth` (`tooth_variable_geometry_breaks`): a table that stores only occupied slots
/// reveals the sovereign population by length alone.
#[test]
fn tooth_variable_geometry_breaks_deniability() {
    let (v, dk, _) = build(b"vault-4", true);
    let (v0, _, _) = build(b"vault-4", false);
    let compact = |vault: &DuressVault, sov: bool| -> usize {
        let opened = vault.unlock(&dk).len();
        NONCE_BYTES + (opened + if sov { 2 } else { 0 }) * SLOT_BYTES
    };
    assert_ne!(compact(&v, true), compact(&v0, false));
    assert_eq!(v.to_bytes().len(), v0.to_bytes().len());
}

#[test]
fn vault_regression_vector() {
    let c = conformance();
    let (v, _, _) = build(b"regression", true);
    let got = hex(&Sha3_256::digest(v.to_bytes()));
    let want = c["vault_regression"]["sha3_256_hex"].as_str().unwrap();
    println!("vault regression sha3_256 = {got}");
    assert_eq!(got, want);
}

// ---------------------------------------------------------------------------
// --release benchmarks
// ---------------------------------------------------------------------------

#[test]
fn bench_60fps_scrubber_and_vault() {
    let release = !cfg!(debug_assertions);
    for &(w, h, label) in &[(1280usize, 720usize, "720p"), (1920, 1080, "1080p")] {
        let ch = w * h * 4;
        let mut fs = FrameScrubber::new(WEARABLE60, ch, 0).unwrap();
        let mut drbg = XofDrbg::new(b"bench-frames");
        let mut base = vec![0u8; ch];
        drbg.fill(&mut base);
        let frames = if release { 120 } else { 2 };
        let mut buf = vec![0u8; ch];
        let t0 = Instant::now();
        for f in 0..frames {
            // 15 Hz full-swing strobe overlaid on noise: the worst case for the branchy path.
            let on = (f / 2) % 2 == 1;
            for (o, &b) in buf.iter_mut().zip(&base) {
                *o = if on { b | 0xC0 } else { b & 0x3F };
            }
            fs.scrub_frame(&mut buf).unwrap();
        }
        let ms = t0.elapsed().as_secs_f64() * 1e3 / frames as f64;
        println!(
            "BENCH scrubber {label} planar Y'CbCrA 4:4:4 ({ch} B/frame): {ms:.3} ms/frame = {:.1} fps (budget 16.667 ms) [{}]",
            1e3 / ms,
            if release { "release" } else { "debug" }
        );
        if release && label == "720p" {
            assert!(ms < 16.667, "720p RGBA scrub must fit the 60 fps frame budget");
        }
    }
    let n = 64;
    let t0 = Instant::now();
    let iters = if release { 50 } else { 2 };
    let mut opened = 0;
    for k in 0..iters {
        let mut drbg = XofDrbg::new(format!("bench-vault-{k}").as_bytes());
        let mut nonce = [0u8; 32];
        drbg.fill(&mut nonce);
        let dk = derive_root(b"d", &nonce);
        let occ = [Occupant { root: &dk, slot: 5, body: body("decoy") }];
        let v = DuressVault::create(nonce, n, &occ, &mut |b| drbg.fill(b)).unwrap();
        opened += v.unlock(&dk).len();
    }
    assert_eq!(opened, iters);
    let ms = t0.elapsed().as_secs_f64() * 1e3 / iters as f64;
    println!("BENCH vault N={n}: create+unlock {ms:.3} ms per vault");
}

// ---------------------------------------------------------------------------
// Part C: RFC 7693 BLAKE2b & RFC 9106 Argon2id (v = 0x13)
// ---------------------------------------------------------------------------

#[test]
fn blake2b_rfc7693_kats_and_boundaries() {
    let c = conformance();
    for v in c["blake2b_kats"].as_array().unwrap() {
        let input = v["input_ascii"].as_str().unwrap().as_bytes();
        let out_len = v["out_len"].as_u64().unwrap() as usize;
        let want = v["output_hex"].as_str().unwrap();
        let got = blake2b(out_len, input).unwrap();
        assert_eq!(hex(&got), want, "blake2b KAT {}", v["name"]);
    }
    // Exact 128-byte, 129-byte, and 256-byte block-boundary checks (Python hashlib.blake2b oracle).
    let b128: Vec<u8> = (0u8..128).collect();
    assert_eq!(
        hex(&blake2b(64, &b128).unwrap()),
        "2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0e8ccff439ac333b040f19b0c4ddd11a61e24ac1fe0f10a039806c5dcc0da3d115"
    );
    let b129: Vec<u8> = (0u8..129).collect();
    assert_eq!(
        hex(&blake2b(64, &b129).unwrap()),
        "f59711d44a031d5f97a9413c065d1e614c417ede998590325f49bad2fd444d3e4418be19aec4e11449ac1a57207898bc57d76a1bcf3566292c20c683a5c4648f"
    );
    let b256: Vec<u8> = (0u16..256).map(|i| i as u8).collect();
    assert_eq!(
        hex(&blake2b(32, &b256).unwrap()),
        "39a7eb9fedc19aabc83425c6755dd90e6f9d0c804964a1f4aaeea3b9fb599835"
    );
    assert_eq!(blake2b(0, b"x"), Err(DuressError::InvalidBlake2bOutLen(0)));
    assert_eq!(blake2b(65, b"x"), Err(DuressError::InvalidBlake2bOutLen(65)));
}

#[test]
fn argon2id_rfc9106_section_5_3_official_kat() {
    let c = conformance();
    let k = &c["argon2id_rfc9106_kat"];
    let pwd = vec![k["password_byte"].as_u64().unwrap() as u8; k["password_len"].as_u64().unwrap() as usize];
    let salt = vec![k["salt_byte"].as_u64().unwrap() as u8; k["salt_len"].as_u64().unwrap() as usize];
    let secret = vec![k["secret_byte"].as_u64().unwrap() as u8; k["secret_len"].as_u64().unwrap() as usize];
    let ad = vec![k["ad_byte"].as_u64().unwrap() as u8; k["ad_len"].as_u64().unwrap() as usize];
    let params = Argon2idParams {
        m_kib: k["m_kib"].as_u64().unwrap() as u32,
        t_passes: k["t_passes"].as_u64().unwrap() as u32,
        p_lanes: k["p_lanes"].as_u64().unwrap() as u32,
    };
    let tag_len = k["tag_len"].as_u64().unwrap() as usize;
    let tag = argon2id_raw(&pwd, &salt, &secret, &ad, params, tag_len).unwrap();
    assert_eq!(hex(&tag), k["tag_hex"].as_str().unwrap());
}

#[test]
fn argon2id_edge_cases_and_parameter_validation() {
    let salt = [0x42u8; 16];
    // Multi-block H' output lengths (65, 96, 100 bytes) & segment_length > 128 (m=2048, p=1 => seg_len=512),
    // plus non-aligned memory (m=39, p=4 => m'=32 != m), pinned against OpenSSL 4.1.0 `openssl kdf ARGON2ID`.
    let p_big_seg = Argon2idParams { m_kib: 2048, t_passes: 2, p_lanes: 1 };
    let t65 = argon2id_raw(b"pw", &salt, b"", b"", p_big_seg, 65).unwrap();
    let t96 = argon2id_raw(b"pw", &salt, b"", b"", p_big_seg, 96).unwrap();
    let t100 = argon2id_raw(b"pw", &salt, b"", b"", p_big_seg, 100).unwrap();
    assert_eq!(
        hex(&t65),
        "750f63dde0ca50658cacec37ddcef760739e23012f4cebfb7d2d6f76e589eee1e63ddd5c6939f484ecbd8689344102c9a6ea69e5c2308d0002ca03839f9f95a5ef"
    );
    assert_eq!(
        hex(&t96),
        "8fe8489b485e9fa0302dd89549c90daa7835d10e0d8b6cf6a064b568cbd6f64135bc50b8ef608d64d8e5b8e524f0e44c5c2d9f55ef47f715e4bf35282938d04e1f3d020ad0823702ebee0de2234fe3aaac22289dec0c48477f2741cefaa4b746"
    );
    assert_eq!(
        hex(&t100),
        "30753667b67a20d19cbed98862c4b4cbd721ac9a11eaed0bb6acfbdd818d92b5a494bda6a78feb4e34b5474f2e86e401c28b92b0873e41adc84f1e206da02e0f519607a8cb6792916aab6413db1f1d4f3d3f826a6904d3084418decf3334c86b3a77dfc7"
    );
    let p_unaligned = Argon2idParams { m_kib: 39, t_passes: 3, p_lanes: 4 };
    let t_unaligned = argon2id_raw(b"test", &[0x07u8; 16], b"", b"", p_unaligned, 32).unwrap();
    assert_eq!(hex(&t_unaligned), "f9bafa6a4330d7fb4240e663509041468d155d9a6914295d0d6dc26328dd62db");

    // Invalid parameter rejections.
    assert!(argon2id_raw(b"p", &salt, b"", b"", Argon2idParams { m_kib: 32, t_passes: 1, p_lanes: 0 }, 32).is_err());
    assert!(argon2id_raw(b"p", &salt, b"", b"", Argon2idParams { m_kib: 32, t_passes: 0, p_lanes: 1 }, 32).is_err());
    assert!(argon2id_raw(b"p", &salt, b"", b"", Argon2idParams { m_kib: 31, t_passes: 1, p_lanes: 4 }, 32).is_err());
    assert!(argon2id_raw(b"p", &[1u8; 7], b"", b"", ARGON2ID_TEST_FAST, 32).is_err());
    assert!(argon2id_raw(b"p", &salt, b"", b"", ARGON2ID_TEST_FAST, 3).is_err());

    // Vault root derivation sensitivity.
    let vs1 = [0x11u8; VOLUME_SALT_BYTES];
    let vs2 = [0x12u8; VOLUME_SALT_BYTES];
    let r1 = derive_vault_root_argon2id(b"decoy-pass", &vs1, ARGON2ID_TEST_FAST).unwrap();
    let r2 = derive_vault_root_argon2id(b"decoy-pass", &vs1, ARGON2ID_TEST_FAST).unwrap();
    let r3 = derive_vault_root_argon2id(b"sovereign-pass", &vs1, ARGON2ID_TEST_FAST).unwrap();
    let r4 = derive_vault_root_argon2id(b"decoy-pass", &vs2, ARGON2ID_TEST_FAST).unwrap();
    assert_eq!(r1, r2);
    assert_ne!(r1, r3);
    assert_ne!(r1, r4);
}

// ---------------------------------------------------------------------------
// Part D: MultiSnapshotDuressVault (write-all oblivious K-snapshot vault)
// ---------------------------------------------------------------------------

#[test]
fn multi_snapshot_disjoint_slot_maps_and_k_epoch_lifecycle() {
    let mut drbg = XofDrbg::new(b"ms-lifecycle");
    let mut vs = [0u8; VOLUME_SALT_BYTES];
    drbg.fill(&mut vs);
    let dk = derive_vault_root_argon2id(b"decoy-passphrase", &vs, ARGON2ID_TEST_FAST).unwrap();
    let sk = derive_vault_root_argon2id(b"sovereign-passphrase", &vs, ARGON2ID_TEST_FAST).unwrap();

    let n = 16;
    let d_slots = derive_decoy_slots(&dk, &vs, n, 3).unwrap();
    let s_slots = derive_sovereign_slots_disjoint(&sk, &vs, n, &d_slots, 3).unwrap();
    assert_eq!(d_slots.len(), 3);
    assert_eq!(s_slots.len(), 3);
    for &ds in &d_slots {
        assert!(!s_slots.contains(&ds), "I_decoy and I_sov must be strictly disjoint");
    }
    // Exact full-capacity boundary and over-capacity error.
    let s_full = derive_sovereign_slots_disjoint(&sk, &vs, n, &d_slots, n - 3).unwrap();
    assert_eq!(s_full.len(), n - 3);
    assert_eq!(
        derive_sovereign_slots_disjoint(&sk, &vs, n, &d_slots, n - 2),
        Err(DuressError::InsufficientSlots { requested: n - 2, available: n - 3 })
    );

    let d_init = vec![
        (d_slots[0], body("decoy:note-0")),
        (d_slots[1], body("decoy:note-1")),
        (d_slots[2], body("decoy:note-2")),
    ];
    let s_init = vec![
        (s_slots[0], body("SOVR:seed-A")),
        (s_slots[1], body("SOVR:seed-B")),
    ];

    let mut dual = MultiSnapshotDuressVault::create_dual(
        vs, n, &dk, &d_init, &sk, &s_init, &mut |b| drbg.fill(b),
    )
    .unwrap();
    let mut decoy_only = MultiSnapshotDuressVault::create_decoy_only(
        vs, n, &dk, &d_init, &mut |b| drbg.fill(b),
    )
    .unwrap();

    assert_eq!(dual.epoch, 0);
    assert_eq!(dual.unlock(&dk), d_init);
    assert_eq!(dual.unlock(&sk), s_init);
    assert_eq!(dual.to_bytes().len(), MultiSnapshotDuressVault::image_len(n));
    assert_eq!(dual.to_bytes().len(), decoy_only.to_bytes().len());
    assert_eq!(MultiSnapshotDuressVault::from_bytes(&dual.to_bytes(), n).unwrap(), dual);

    // Run K = 5 commits, capturing every historical snapshot in BOTH worlds.
    let mut dual_snaps = vec![dual.clone()];
    let mut decoy_snaps = vec![decoy_only.clone()];
    for step in 1..=5u64 {
        let d_write = vec![(d_slots[0], body(&format!("decoy:note-0-e{step}")))];
        let s_write = if step == 2 {
            vec![(s_slots[0], body("SOVR:seed-A-updated"))]
        } else if step == 4 {
            // Dynamically allocate third sovereign slot outside I_decoy.
            vec![(s_slots[2], body("SOVR:seed-C-new"))]
        } else {
            vec![]
        };
        dual.commit_dual(&dk, &d_write, &sk, &s_write, &mut |b| drbg.fill(b)).unwrap();
        decoy_only.commit_decoy_only(&dk, &d_write, &mut |b| drbg.fill(b)).unwrap();
        assert_eq!(dual.epoch, step);
        assert_eq!(decoy_only.epoch, step);
        // Decoy view matches identically at every epoch.
        assert_eq!(dual.unlock(&dk), decoy_only.unlock(&dk));
        dual_snaps.push(dual.clone());
        decoy_snaps.push(decoy_only.clone());
    }

    // Final sovereign state preserved + updated across all 5 epochs.
    let final_sov = dual.unlock(&sk);
    assert_eq!(final_sov.len(), 3);
    assert!(final_sov.contains(&(s_slots[0], body("SOVR:seed-A-updated"))));
    assert!(final_sov.contains(&(s_slots[1], body("SOVR:seed-B"))));
    assert!(final_sov.contains(&(s_slots[2], body("SOVR:seed-C-new"))));

    // Write-all forensic invariant: at EVERY epoch transition e -> e+1, ALL N blocks changed
    // in BOTH dual and decoy-only worlds (zero static non-decoy blocks to diff!).
    for w in dual_snaps.windows(2) {
        for i in 0..n {
            assert_ne!(w[0].slots[i], w[1].slots[i], "dual epoch {}->{}: slot {i} stayed static", w[0].epoch, w[1].epoch);
        }
    }
    for w in decoy_snaps.windows(2) {
        for i in 0..n {
            assert_ne!(w[0].slots[i], w[1].slots[i], "decoy epoch {}->{}: slot {i} stayed static", w[0].epoch, w[1].epoch);
        }
    }
}

#[test]
fn multi_snapshot_coercion_shred_and_collision_guards() {
    let mut drbg = XofDrbg::new(b"ms-guards");
    let mut vs = [0u8; VOLUME_SALT_BYTES];
    drbg.fill(&mut vs);
    let dk = derive_vault_root_argon2id(b"decoy", &vs, ARGON2ID_TEST_FAST).unwrap();
    let sk = derive_vault_root_argon2id(b"sov", &vs, ARGON2ID_TEST_FAST).unwrap();
    let wrong = derive_vault_root_argon2id(b"wrong", &vs, ARGON2ID_TEST_FAST).unwrap();

    // Identical roots & colliding slots rejected.
    assert_eq!(
        MultiSnapshotDuressVault::create_dual(vs, 8, &dk, &[(0, body("d"))], &dk, &[(1, body("s"))], &mut |b| drbg.fill(b)),
        Err(DuressError::IdenticalRoots)
    );
    assert_eq!(
        MultiSnapshotDuressVault::create_dual(vs, 8, &dk, &[(2, body("d"))], &sk, &[(2, body("s"))], &mut |b| drbg.fill(b)),
        Err(DuressError::SlotCollision(2))
    );

    let mut v = MultiSnapshotDuressVault::create_dual(
        vs, 8, &dk, &[(1, body("d1"))], &sk, &[(5, body("s5"))], &mut |b| drbg.fill(b),
    )
    .unwrap();

    // commit_dual rejects writing sovereign into a decoy slot, unowned decoy slot, or identical roots.
    assert_eq!(
        v.commit_dual(&dk, &[], &sk, &[(1, body("collide"))], &mut |b| drbg.fill(b)),
        Err(DuressError::SlotCollision(1))
    );
    assert_eq!(
        v.commit_dual(&dk, &[(5, body("unowned"))], &sk, &[], &mut |b| drbg.fill(b)),
        Err(DuressError::NotOwned(5))
    );
    assert_eq!(
        v.commit_dual(&dk, &[], &dk, &[], &mut |b| drbg.fill(b)),
        Err(DuressError::IdenticalRoots)
    );
    // Wrong root rejected before wiping (both decoy root and mistyped sovereign root!).
    assert_eq!(v.commit_decoy_only(&wrong, &[], &mut |b| drbg.fill(b)), Err(DuressError::NoOwnedSlots));
    assert_eq!(
        v.commit_dual(&dk, &[], &wrong, &[], &mut |b| drbg.fill(b)),
        Err(DuressError::NoOwnedSovereignSlots)
    );
    assert_eq!(v.unlock(&sk), vec![(5, body("s5"))], "mistyped sovereign root must never wipe compartment");

    // Empty compartment & oversized geometry / rollback guards.
    assert_eq!(
        MultiSnapshotDuressVault::create_decoy_only(vs, 8, &dk, &[], &mut |b| drbg.fill(b)),
        Err(DuressError::EmptyCompartment)
    );
    assert_eq!(
        MultiSnapshotDuressVault::from_bytes(&[], usize::MAX / SLOT_BYTES + 1),
        Err(DuressError::TooManySlots(usize::MAX / SLOT_BYTES + 1))
    );
    assert_eq!(
        MultiSnapshotDuressVault::from_bytes_min_epoch(&v.to_bytes(), 8, 1),
        Err(DuressError::EpochRollback { got: 0, min_epoch: 1 })
    );
    assert_eq!(MultiSnapshotDuressVault::from_bytes_min_epoch(&v.to_bytes(), 8, 0).unwrap(), v);

    // Epoch overflow guard: refuse to wrap epoch (which would reuse pads!).
    let mut maxed = v.clone();
    maxed.epoch = u64::MAX;
    assert_eq!(maxed.commit_decoy_only(&dk, &[], &mut |b| drbg.fill(b)), Err(DuressError::EpochOverflow));
    assert_eq!(maxed.commit_dual(&dk, &[], &sk, &[], &mut |b| drbg.fill(b)), Err(DuressError::EpochOverflow));

    // Honest coercion availability trade-off: pure commit_decoy_only (without sk) overwrites all
    // non-decoy slots with fresh chaff, shredding the unmounted sovereign slot while preserving
    // decoy state and multi-snapshot deniability. Re-initializing requires init_sovereign_compartment.
    let before = v.clone();
    v.commit_decoy_only(&dk, &[(1, body("d1-under-duress"))], &mut |b| drbg.fill(b)).unwrap();
    assert_eq!(v.epoch, 1);
    assert_eq!(v.unlock(&dk), vec![(1, body("d1-under-duress"))]);
    assert!(v.unlock(&sk).is_empty(), "pure decoy-only write-all commit shreds unmounted sovereign slots");
    for i in 0..8 {
        assert_ne!(before.slots[i], v.slots[i]);
    }
    v.init_sovereign_compartment(&dk, &sk, &[(6, body("s6-restored"))], &mut |b| drbg.fill(b)).unwrap();
    assert_eq!(v.epoch, 2);
    assert_eq!(v.unlock(&dk), vec![(1, body("d1-under-duress"))]);
    assert_eq!(v.unlock(&sk), vec![(6, body("s6-restored"))]);
}

/// `#tooth` (`tooth_single_slot_update_leaks_across_two_snapshots`):
/// v1 in-place updates leave non-touched chaff static, so `snap_0[i] != snap_1[i]` outside
/// `I_decoy` exposes the exact hidden sovereign slot index and count.
#[test]
fn tooth_v1_single_slot_update_leaks_across_two_snapshots() {
    let (mut v1_decoy_only, dk0, _) = build(b"v1-2snap", false);
    let snap0_d = v1_decoy_only.clone();
    v1_decoy_only.rewrite_owned(&dk0, 1, &body("decoy:edited")).unwrap();
    let decoy_ids: Vec<usize> = v1_decoy_only.unlock(&dk0).iter().map(|x| x.0).collect();
    let changed_decoy_world: Vec<usize> = (0..N)
        .filter(|&i| !decoy_ids.contains(&i) && snap0_d.slots[i] != v1_decoy_only.slots[i])
        .collect();
    assert!(changed_decoy_world.is_empty(), "v1 decoy-only leaves all non-decoy slots static");

    // Now in the dual world, user edits decoy slot 1 AND sovereign slot 3 in place:
    let (mut v1_dual, dk, sk) = build(b"v1-2snap", true);
    let snap0_s = v1_dual.clone();
    v1_dual.rewrite_owned(&dk, 1, &body("decoy:edited")).unwrap();
    v1_dual.rewrite_owned(&sk, 3, &body("SOVR:updated-secret")).unwrap();
    let changed_dual_world: Vec<usize> = (0..N)
        .filter(|&i| !decoy_ids.contains(&i) && snap0_s.slots[i] != v1_dual.slots[i])
        .collect();
    assert_eq!(changed_dual_world, vec![3], "v1 2-snapshot diff pinpoints exact modified sovereign slot!");
}

/// `#tooth` (`tooth_reused_epoch_pad_leaks_across_two_snapshots`):
/// sealing twice at the SAME epoch reuses the exact pad (identical ciphertext for unchanged body;
/// direct plaintext XOR for changed body).
#[test]
fn tooth_reused_epoch_pad_leaks() {
    let vs = [0x77u8; VOLUME_SALT_BYTES];
    let sk = derive_vault_root_argon2id(b"sov", &vs, ARGON2ID_TEST_FAST).unwrap();
    let b1 = body("SOVR:secret-v1");
    let b2 = body("SOVR:secret-v2");
    let c1_e0 = seal_slot_epoch(&sk, &vs, 0, 3, &b1);
    let c1_e0_reused = seal_slot_epoch(&sk, &vs, 0, 3, &b1);
    let c2_e0_reused = seal_slot_epoch(&sk, &vs, 0, 3, &b2);
    assert_eq!(c1_e0, c1_e0_reused, "same epoch leaks equality");
    for k in 0..BODY_BYTES {
        assert_eq!(c1_e0[k] ^ c2_e0_reused[k], b1[k] ^ b2[k], "same epoch leaks plaintext XOR");
    }
    // Advancing epoch 0 -> 1 breaks both leaks.
    let c1_e1 = seal_slot_epoch(&sk, &vs, 1, 3, &b1);
    assert_ne!(c1_e0, c1_e1);
}

#[test]
fn multi_snapshot_byte_and_diff_statistics() {
    let mut drbg = XofDrbg::new(b"ms-stats");
    let mut vs = [0u8; VOLUME_SALT_BYTES];
    drbg.fill(&mut vs);
    let dk = derive_vault_root_argon2id(b"decoy-stat", &vs, ARGON2ID_TEST_FAST).unwrap();
    let sk = derive_vault_root_argon2id(b"sov-stat", &vs, ARGON2ID_TEST_FAST).unwrap();
    let n = 16;
    let mut v = MultiSnapshotDuressVault::create_dual(
        vs,
        n,
        &dk,
        &[(0, body("d0")), (1, body("d1"))],
        &sk,
        &[(4, body("s4")), (9, body("s9"))],
        &mut |b| drbg.fill(b),
    )
    .unwrap();
    let mut hist_sov_xor = [0u64; 256];
    let mut hist_chaff_xor = [0u64; 256];
    let mut prev = v.slots.clone();
    for e in 1..=200u64 {
        v.commit_dual(&dk, &[(0, body(&format!("d0-{e}")))], &sk, &[], &mut |b| drbg.fill(b)).unwrap();
        for i in 2..n {
            let h = if i == 4 || i == 9 { &mut hist_sov_xor } else { &mut hist_chaff_xor };
            for k in 0..SLOT_BYTES {
                h[(prev[i][k] ^ v.slots[i][k]) as usize] += 1;
            }
        }
        prev = v.slots.clone();
    }
    let chi = |h: &[u64; 256]| {
        let total: u64 = h.iter().sum();
        let expected = total as f64 / 256.0;
        h.iter().map(|&c| (c as f64 - expected).powi(2) / expected).sum::<f64>()
    };
    let (cs, cc) = (chi(&hist_sov_xor), chi(&hist_chaff_xor));
    println!("multi-snapshot epoch-diff chi2(sovereign)={cs:.1} chi2(chaff)={cc:.1} (255 dof; p=1e-6 crit ≈ 370)");
    assert!(cs < 370.0 && cc < 370.0);
}

#[test]
fn bench_argon2id_and_multi_snapshot_vault() {
    let release = !cfg!(debug_assertions);
    let vs = [0x99u8; VOLUME_SALT_BYTES];
    // Always verify RFC 9106 §4 64 MiB default profile in --release; use fast profile in debug.
    let params = if release { ARGON2ID_WEARABLE_DEFAULT } else { ARGON2ID_TEST_FAST };
    let t0 = Instant::now();
    let dk = derive_vault_root_argon2id(b"wearable-decoy-passphrase", &vs, params).unwrap();
    let kdf_ms = t0.elapsed().as_secs_f64() * 1e3;
    println!(
        "BENCH Argon2id (m={} KiB, t={}, p={}): {:.2} ms [{}]",
        params.m_kib,
        params.t_passes,
        params.p_lanes,
        kdf_ms,
        if release { "release" } else { "debug" }
    );
    let sk = derive_vault_root_argon2id(b"wearable-sov-passphrase", &vs, ARGON2ID_TEST_FAST).unwrap();
    let mut drbg = XofDrbg::new(b"bench-ms");
    let n = 64;
    let mut v = MultiSnapshotDuressVault::create_dual(
        vs,
        n,
        &dk,
        &[(0, body("d0")), (1, body("d1"))],
        &sk,
        &[(10, body("s10")), (20, body("s20"))],
        &mut |b| drbg.fill(b),
    )
    .unwrap();
    let commits = if release { 100 } else { 5 };
    let t1 = Instant::now();
    for c in 0..commits {
        v.commit_dual(&dk, &[(0, body(&format!("d0-{c}")))], &sk, &[(10, body(&format!("s10-{c}")))], &mut |b| drbg.fill(b))
            .unwrap();
    }
    let commit_ms = t1.elapsed().as_secs_f64() * 1e3 / commits as f64;
    println!(
        "BENCH MultiSnapshotDuressVault N={n} commit_dual (write-all 64 slots): {:.3} ms/commit [{}]",
        commit_ms,
        if release { "release" } else { "debug" }
    );
}
