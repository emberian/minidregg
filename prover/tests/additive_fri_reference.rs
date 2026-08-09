//! End-to-end teeth and manual benchmarks for the full-opening additive round.
//!
use std::hint::black_box;
use std::time::{Duration, Instant};

use minidregg_prover::additive_fri_reference::{
    commit_tower_word, fold_last_direction, prove_round, tower_element_encoding, tower_leaf_digest,
    verify_round, AdditiveFriError, TOWER_LEAF_V1_TAG,
};
use minidregg_prover::additive_ntt;
use minidregg_prover::binary_tower::{additive_fold_pair, TowerElem};
use minidregg_prover::poseidon::{demo_spec, BABY_BEAR_P};

fn e(level: u8, bits: u64) -> TowerElem {
    TowerElem::new(level, bits).unwrap()
}

fn coordinate_basis(level: u8, k: usize) -> Vec<TowerElem> {
    (0..k).map(|i| e(level, 1u64 << i)).collect()
}

fn fixture(level: u8, n: usize, salt: u64) -> Vec<TowerElem> {
    let width = 1usize << level;
    let mask = if width == 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    };
    let mut state = salt;
    (0..n)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            e(level, state & mask)
        })
        .collect()
}

#[test]
fn canonical_tower_leaf_encoding_is_exact_and_level_separated() {
    let value = e(6, 0x0123_4567_89ab_cdef);
    assert_eq!(
        tower_element_encoding(value),
        [TOWER_LEAF_V1_TAG, 6, 0xcdef, 0x89ab, 0x4567, 0x0123]
    );
    let spec = demo_spec();
    assert_ne!(
        tower_leaf_digest(e(2, 1), &spec, BABY_BEAR_P).unwrap(),
        tower_leaf_digest(e(3, 1), &spec, BABY_BEAR_P).unwrap(),
        "the same bit string at different tower levels must not alias"
    );
    assert!(tower_element_encoding(value)
        .iter()
        .all(|&field| field < BABY_BEAR_P));
}

#[test]
fn fast_batch_fold_is_exactly_the_landed_pair_formula() {
    let level = 3;
    let k = 6;
    let n = 1usize << k;
    let basis = coordinate_basis(level, k);
    let offset = e(level, 0x53);
    let challenge = e(level, 0xa6);
    let word = fixture(level, n, 0x243f_6a88);
    let folded = fold_last_direction(&word, &basis, offset, challenge).unwrap();
    let half = n / 2;

    for i in 0..half {
        let mut x = offset;
        for (j, beta) in basis[..k - 1].iter().copied().enumerate() {
            if i & (1usize << j) != 0 {
                x = x.add(beta).unwrap();
            }
        }
        assert_eq!(
            folded[i],
            additive_fold_pair(basis[k - 1], challenge, x, word[i], word[half + i]).unwrap()
        );
    }
}

#[test]
fn full_opening_round_trip_binds_both_words_and_every_fold() {
    let level = 3;
    let k = 6;
    let n = 1usize << k;
    let basis = coordinate_basis(level, k);
    let coefficients = fixture(level, n, 0x1319_8a2e);
    let spec = demo_spec();
    let (claim, proof) = prove_round(
        &coefficients,
        &basis,
        e(level, 0x5a),
        e(level, 0xc3),
        &spec,
        BABY_BEAR_P,
    )
    .unwrap();
    assert!(verify_round(&claim, &proof, &spec, BABY_BEAR_P));
    assert_eq!(proof.input_word.len(), n);
    assert_eq!(proof.folded_word.len(), n / 2);
    assert_eq!(
        commit_tower_word(&proof.input_word, &spec, BABY_BEAR_P).unwrap(),
        claim.input_root
    );
    assert_eq!(
        commit_tower_word(&proof.folded_word, &spec, BABY_BEAR_P).unwrap(),
        claim.folded_root
    );

    for i in 0..proof.input_word.len() {
        let mut bad = proof.clone();
        bad.input_word[i] = bad.input_word[i].add(e(level, 1)).unwrap();
        assert!(!verify_round(&claim, &bad, &spec, BABY_BEAR_P));
    }
    for i in 0..proof.folded_word.len() {
        let mut bad = proof.clone();
        bad.folded_word[i] = bad.folded_word[i].add(e(level, 1)).unwrap();
        assert!(!verify_round(&claim, &bad, &spec, BABY_BEAR_P));
    }
}

#[test]
fn claim_parameter_and_commitment_tampers_reject() {
    let level = 3;
    let k = 4;
    let n = 1usize << k;
    let basis = coordinate_basis(level, k);
    let coefficients = fixture(level, n, 0xa409_3822);
    let spec = demo_spec();
    let (claim, proof) = prove_round(
        &coefficients,
        &basis,
        e(level, 0),
        e(level, 0x42),
        &spec,
        BABY_BEAR_P,
    )
    .unwrap();

    let mut bad = claim.clone();
    bad.challenge = bad.challenge.add(e(level, 1)).unwrap();
    assert!(!verify_round(&bad, &proof, &spec, BABY_BEAR_P));
    let mut bad = claim.clone();
    bad.offset = bad.offset.add(e(level, 1)).unwrap();
    assert!(!verify_round(&bad, &proof, &spec, BABY_BEAR_P));
    let mut bad = claim.clone();
    bad.basis.swap(0, 1);
    assert!(!verify_round(&bad, &proof, &spec, BABY_BEAR_P));
    let mut bad = claim.clone();
    bad.input_root.limbs[0] = (bad.input_root.limbs[0] + 1) % BABY_BEAR_P;
    assert!(!verify_round(&bad, &proof, &spec, BABY_BEAR_P));
    let mut bad = claim.clone();
    bad.folded_root.limbs[0] = BABY_BEAR_P;
    assert!(!verify_round(&bad, &proof, &spec, BABY_BEAR_P));
}

#[test]
fn identity_polynomial_folds_to_the_challenge_constant() {
    let level = 3;
    let k = 5;
    let n = 1usize << k;
    let basis = coordinate_basis(level, k);
    let mut coefficients = vec![e(level, 0); n];
    coefficients[1] = e(level, 1); // novel basis index 1 is W_0=X.
    let challenge = e(level, 0xd7);
    let spec = demo_spec();
    let (_, proof) = prove_round(
        &coefficients,
        &basis,
        e(level, 0x23),
        challenge,
        &spec,
        BABY_BEAR_P,
    )
    .unwrap();
    assert!(proof.folded_word.iter().all(|&value| value == challenge));
}

#[test]
fn malformed_shapes_and_runtime_contracts_fail_closed() {
    let spec = demo_spec();
    assert_eq!(
        commit_tower_word(&[], &spec, BABY_BEAR_P),
        Err(AdditiveFriError::EmptyWord)
    );
    assert!(matches!(
        fold_last_direction(&[e(2, 0)], &[], e(2, 0), e(2, 0)),
        Err(AdditiveFriError::NoFoldDirection)
    ));
    assert!(matches!(
        fold_last_direction(&[e(2, 0); 4], &[e(2, 1), e(2, 1)], e(2, 0), e(2, 0)),
        Err(AdditiveFriError::DependentBasis { index: 1 })
    ));
    assert!(matches!(
        tower_leaf_digest(e(2, 0), &spec, 13),
        Err(AdditiveFriError::UnsupportedModulus(13))
    ));
}

fn elapsed_per_iteration(mut f: impl FnMut(), iterations: u32) -> Duration {
    let start = Instant::now();
    for _ in 0..iterations {
        f();
    }
    start.elapsed() / iterations
}

/// Run with:
/// `cargo test --release --test additive_fri_reference benchmark -- --ignored --nocapture`
#[test]
#[ignore = "manual fold and full-opening prove/verify throughput"]
fn benchmark_fold_and_full_opening_roundtrip() {
    println!("n,fold_us,fold_melems_s,prove_verify_us");
    for (k, fold_iterations, round_iterations) in [(4, 5000, 20), (6, 1000, 5), (8, 200, 1)] {
        let level = 4;
        let n = 1usize << k;
        let basis = coordinate_basis(level, k);
        let coefficients = fixture(level, n, 0x082e_fa98 ^ k as u64);
        let offset = e(level, 0x5a5a);
        let challenge = e(level, 0xa55a);
        let spec = demo_spec();
        let word = additive_ntt::forward(&coefficients, &basis, offset).unwrap();

        let fold = elapsed_per_iteration(
            || {
                black_box(fold_last_direction(
                    black_box(&word),
                    black_box(&basis),
                    black_box(offset),
                    black_box(challenge),
                ))
                .unwrap();
            },
            fold_iterations,
        );
        let roundtrip = elapsed_per_iteration(
            || {
                let (claim, proof) = prove_round(
                    black_box(&coefficients),
                    black_box(&basis),
                    black_box(offset),
                    black_box(challenge),
                    black_box(&spec),
                    BABY_BEAR_P,
                )
                .unwrap();
                assert!(verify_round(
                    black_box(&claim),
                    black_box(&proof),
                    black_box(&spec),
                    BABY_BEAR_P
                ));
            },
            round_iterations,
        );
        let fold_us = fold.as_secs_f64() * 1e6;
        println!(
            "{n},{fold_us:.2},{:.3},{:.2}",
            (n / 2) as f64 / fold.as_secs_f64() / 1e6,
            roundtrip.as_secs_f64() * 1e6
        );
    }
}
