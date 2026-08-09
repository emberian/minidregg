//! Dense conformance and executable performance teeth for the additive NTT.
//!
use std::hint::black_box;
use std::time::{Duration, Instant};

use minidregg_prover::additive_ntt::{
    forward, forward_dense_reference, forward_in_place, inverse, AdditiveNttError,
};
use minidregg_prover::binary_tower::TowerElem;

fn e(level: u8, bits: u64) -> TowerElem {
    TowerElem::new(level, bits).unwrap()
}

fn coordinate_basis(level: u8, k: usize) -> Vec<TowerElem> {
    (0..k).map(|i| e(level, 1u64 << i)).collect()
}

fn triangular_basis(level: u8, k: usize) -> Vec<TowerElem> {
    (0..k).map(|i| e(level, (1u64 << (i + 1)) - 1)).collect()
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
fn rejects_bad_shapes_levels_and_dependent_directions() {
    let zero = e(2, 0);
    assert_eq!(
        forward_in_place(&mut [], &[], zero),
        Err(AdditiveNttError::EmptyInput)
    );
    assert_eq!(
        forward_in_place(&mut [zero; 3], &[], zero),
        Err(AdditiveNttError::LengthNotPowerOfTwo(3))
    );
    assert!(matches!(
        forward_in_place(&mut [zero; 4], &[e(2, 1)], zero),
        Err(AdditiveNttError::BasisLengthMismatch { .. })
    ));
    assert!(matches!(
        forward_in_place(&mut [zero; 2], &[e(1, 1)], zero),
        Err(AdditiveNttError::FieldLevelMismatch { role: "basis", .. })
    ));
    assert_eq!(
        forward_in_place(&mut [zero; 2], &[zero], zero),
        Err(AdditiveNttError::DependentBasis { index: 0 })
    );
    assert_eq!(
        forward_in_place(&mut [zero; 4], &[e(2, 1), e(2, 1)], zero),
        Err(AdditiveNttError::DependentBasis { index: 1 })
    );
    assert_eq!(
        forward_in_place(&mut [e(0, 0); 4], &[e(0, 1), e(0, 1)], e(0, 0)),
        Err(AdditiveNttError::DomainTooLarge {
            basis_len: 2,
            dimension: 1
        })
    );
}

#[test]
fn gf16_keystone_is_an_exact_lean_definition_vector() {
    // beta = [1, x1] gives W_0=X and W_1=X^2+X.  Coefficient and domain
    // indices are bit vectors [c0,c1] in the Lean novelBasis/domainPoint sums.
    let basis = [e(2, 1), TowerElem::fp_generator(1).unwrap()];
    let coefficients = [e(2, 1), e(2, 2), e(2, 4), e(2, 8)];
    let transformed = forward(&coefficients, &basis, e(2, 0)).unwrap();
    assert_eq!(
        transformed.iter().map(|x| x.bits()).collect::<Vec<_>>(),
        vec![1, 3, 14, 13]
    );
    assert_eq!(
        transformed,
        forward_dense_reference(&coefficients, &basis, e(2, 0)).unwrap()
    );
}

#[test]
fn fast_schedule_matches_dense_novel_basis_sum_on_affine_cosets() {
    let level = 3;
    for k in 0..=6 {
        let n = 1usize << k;
        for basis in [coordinate_basis(level, k), triangular_basis(level, k)] {
            for offset_bits in [0, 0x53, 0xa6] {
                let coefficients = fixture(level, n, 0x243f_6a88 ^ offset_bits);
                let offset = e(level, offset_bits);
                assert_eq!(
                    forward(&coefficients, &basis, offset).unwrap(),
                    forward_dense_reference(&coefficients, &basis, offset).unwrap(),
                    "dense mismatch at k={k}, offset={offset_bits:#x}"
                );
            }
        }
    }
}

#[test]
fn inverse_round_trips_every_supported_domain_size_in_gf256() {
    let level = 3;
    for k in 0..=8 {
        let n = 1usize << k;
        let coefficients = fixture(level, n, 0x1319_8a2e ^ k as u64);
        for basis in [coordinate_basis(level, k), triangular_basis(level, k)] {
            for offset_bits in [0, 0x5a] {
                let offset = e(level, offset_bits);
                let evaluations = forward(&coefficients, &basis, offset).unwrap();
                assert_eq!(inverse(&evaluations, &basis, offset).unwrap(), coefficients);
            }
        }
    }
}

#[test]
fn transform_of_each_unit_coefficient_is_the_corresponding_novel_polynomial() {
    let level = 3;
    let k = 4;
    let n = 1usize << k;
    let basis = coordinate_basis(level, k);
    let zero = e(level, 0);
    for coefficient_index in 0..n {
        let mut coefficients = vec![zero; n];
        coefficients[coefficient_index] = e(level, 1);
        assert_eq!(
            forward(&coefficients, &basis, zero).unwrap(),
            forward_dense_reference(&coefficients, &basis, zero).unwrap()
        );
    }
}

fn elapsed_per_iteration(mut f: impl FnMut(), iterations: u32) -> Duration {
    let start = Instant::now();
    for _ in 0..iterations {
        f();
    }
    start.elapsed() / iterations
}

/// Run with:
/// `cargo test --release --test additive_ntt_runtime benchmark -- --ignored --nocapture`
#[test]
#[ignore = "manual wall-clock comparison of the fast schedule and dense oracle"]
fn benchmark_fast_against_dense() {
    println!("n,fast_us,dense_us,speedup");
    for (k, fast_iterations, dense_iterations) in
        [(4, 2000, 200), (6, 500, 30), (8, 100, 3), (10, 20, 1)]
    {
        let level = 4;
        let n = 1usize << k;
        let basis = coordinate_basis(level, k);
        let coefficients = fixture(level, n, 0xa409_3822 ^ k as u64);
        let offset = e(level, 0x5a5a);

        let fast = elapsed_per_iteration(
            || {
                black_box(forward(
                    black_box(&coefficients),
                    black_box(&basis),
                    black_box(offset),
                ))
                .unwrap();
            },
            fast_iterations,
        );
        let dense = elapsed_per_iteration(
            || {
                black_box(forward_dense_reference(
                    black_box(&coefficients),
                    black_box(&basis),
                    black_box(offset),
                ))
                .unwrap();
            },
            dense_iterations,
        );
        let fast_us = fast.as_secs_f64() * 1e6;
        let dense_us = dense.as_secs_f64() * 1e6;
        println!("{n},{fast_us:.2},{dense_us:.2},{:.1}x", dense_us / fast_us);
    }
}
