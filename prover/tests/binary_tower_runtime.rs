//! Executable teeth for `src/binary_tower.rs`.
//!
//! The path import keeps this lane isolated from concurrent `lib.rs` work.  The
//! final crate export is one line: `pub mod binary_tower;`.

#[path = "../src/binary_tower.rs"]
mod binary_tower;

use binary_tower::{additive_fold_map, additive_fold_pair, TowerElem, TowerError, MAX_LEVEL};

fn e(level: u8, bits: u64) -> TowerElem {
    TowerElem::new(level, bits).unwrap()
}

#[test]
fn representation_rejects_truncation_and_level_mixups() {
    assert_eq!(
        TowerElem::new(MAX_LEVEL + 1, 0),
        Err(TowerError::LevelTooLarge(MAX_LEVEL + 1))
    );
    assert!(matches!(
        TowerElem::new(2, 0x10),
        Err(TowerError::NonCanonical { .. })
    ));
    assert!(matches!(
        e(1, 1).mul(e(2, 1)),
        Err(TowerError::LevelMismatch { .. })
    ));
    assert_eq!(e(0, 1).unpack(), Err(TowerError::NoPreviousLevel));
    assert_eq!(e(2, 0).inverse(), Err(TowerError::DivisionByZero));
    let embedded = e(1, 3).embed_to(3).unwrap();
    assert_eq!((embedded.level(), embedded.bits()), (3, 3));
}

#[test]
fn gf4_exact_table_matches_fan_paar_base() {
    // Basis [1,x0], relation x0^2 + x0 + 1 = 0.
    const EXPECTED: [[u64; 4]; 4] = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]];
    for a in 0..4 {
        for b in 0..4 {
            assert_eq!(
                e(1, a).mul(e(1, b)).unwrap().bits(),
                EXPECTED[a as usize][b as usize]
            );
        }
    }
    let x0 = TowerElem::fp_generator(0).unwrap();
    assert_eq!(x0.bits(), 2);
    assert_eq!(x0.square().bits(), 3);
    assert_eq!(
        (0..4)
            .scan(e(1, 1), |p, _| {
                let out = *p;
                *p = p.mul(x0).unwrap();
                Some(out.bits())
            })
            .collect::<Vec<_>>(),
        vec![1, 2, 3, 1]
    );
}

#[test]
fn gf16_exact_generator_vector_matches_second_relation() {
    // Basis [1,x0,y=x1,x0*y], relation y^2 + x0*y + 1 = 0.
    let y = TowerElem::fp_generator(1).unwrap();
    assert_eq!(y.bits(), 4);
    assert_eq!(y.square().bits(), 9); // 1 + x0*y
    let mut power = e(2, 1);
    let mut vector = Vec::new();
    for _ in 0..5 {
        vector.push(power.bits());
        power = power.mul(y).unwrap();
    }
    assert_eq!(vector, vec![1, 4, 9, 10, 6]);
}

#[test]
fn pack_unpack_and_generator_relations_hold_at_every_runtime_level() {
    for child in 0..MAX_LEVEL {
        let sample_mask = if child <= 3 {
            (1u64 << (1usize << child)) - 1
        } else {
            0xffff
        };
        let low = e(child, 0x9e37 & sample_mask);
        let high = e(child, 0x6d2b & sample_mask);
        let packed = TowerElem::pack(low, high).unwrap();
        assert_eq!(packed.unpack().unwrap(), (low, high));

        let generator = TowerElem::fp_generator(child).unwrap();
        let coeff = TowerElem::mul_coefficient(child).unwrap().embed().unwrap();
        let relation = generator
            .square()
            .add(coeff.mul(generator).unwrap())
            .unwrap()
            .add(TowerElem::one(child + 1).unwrap())
            .unwrap();
        assert!(relation.is_zero(), "Fan--Paar relation failed at k={child}");
    }
}

#[test]
fn gf16_is_a_field_and_mul_by_generator_is_the_same_operation() {
    let generator = TowerElem::fp_generator(1).unwrap();
    for a in 0..16 {
        let x = e(2, a);
        assert_eq!(x.mul(generator).unwrap(), x.mul_by_generator().unwrap());
        for b in 0..16 {
            let y = e(2, b);
            assert_eq!(x.mul(y).unwrap(), y.mul(x).unwrap());
            for c in 0..16 {
                let z = e(2, c);
                assert_eq!(
                    x.mul(y).unwrap().mul(z).unwrap(),
                    x.mul(y.mul(z).unwrap()).unwrap()
                );
                assert_eq!(
                    x.mul(y.add(z).unwrap()).unwrap(),
                    x.mul(y).unwrap().add(x.mul(z).unwrap()).unwrap()
                );
            }
        }
        if a != 0 {
            assert_eq!(
                x.mul(x.inverse().unwrap()).unwrap(),
                TowerElem::one(2).unwrap()
            );
        }
    }
}

#[test]
fn trace_separates_generators_from_embedded_subfields() {
    for level in 1..=MAX_LEVEL {
        let generator = TowerElem::fp_generator(level - 1).unwrap();
        assert_eq!(generator.absolute_trace(), TowerElem::one(level).unwrap());
    }
    // Exhaustively exercise Tr(T_3/GF(2)) in GF(256).
    for bits in 0..256 {
        let tr = e(3, bits).absolute_trace();
        assert!(tr.bits() == 0 || tr.bits() == 1);
    }
    // The trace of every element embedded through one quadratic step is zero.
    for level in 0..=3 {
        let size = 1u64 << (1usize << level);
        for bits in 0..size {
            let embedded = e(level, bits).embed().unwrap();
            assert_eq!(
                embedded.absolute_trace(),
                TowerElem::zero(level + 1).unwrap()
            );
        }
    }
}

#[test]
fn additive_fold_map_has_exact_two_point_fibers_in_gf16() {
    let beta = TowerElem::fp_generator(1).unwrap();
    for xbits in 0..16 {
        let x = e(2, xbits);
        assert_eq!(
            additive_fold_map(beta, x).unwrap(),
            additive_fold_map(beta, x.add(beta).unwrap()).unwrap()
        );
        for ybits in 0..16 {
            let y = e(2, ybits);
            let same = additive_fold_map(beta, x).unwrap() == additive_fold_map(beta, y).unwrap();
            assert_eq!(same, y == x || y == x.add(beta).unwrap());
        }
    }
}

#[test]
fn additive_pair_fold_is_coset_invariant_and_folds_identity_to_lambda() {
    for beta_bits in 1..16 {
        let beta = e(2, beta_bits);
        for lambda_bits in 0..16 {
            let lambda = e(2, lambda_bits);
            for xbits in 0..16 {
                let x = e(2, xbits);
                let shifted = x.add(beta).unwrap();
                let at_x = additive_fold_pair(beta, lambda, x, x, shifted).unwrap();
                let at_shifted = additive_fold_pair(beta, lambda, shifted, shifted, x).unwrap();
                assert_eq!(at_x, at_shifted);
                assert_eq!(at_x, lambda, "friFold id must be the constant lambda");
            }
        }
    }
}

#[test]
fn additive_pair_fold_halves_every_affine_polynomial() {
    let beta = TowerElem::fp_generator(1).unwrap();
    for a_bits in 0..16 {
        let a = e(2, a_bits);
        for b_bits in 0..16 {
            let b = e(2, b_bits);
            for lambda_bits in 0..16 {
                let lambda = e(2, lambda_bits);
                let expected = a.add(b.mul(lambda).unwrap()).unwrap();
                for xbits in 0..16 {
                    let x = e(2, xbits);
                    let shifted = x.add(beta).unwrap();
                    let fx = a.add(b.mul(x).unwrap()).unwrap();
                    let fx_shifted = a.add(b.mul(shifted).unwrap()).unwrap();
                    assert_eq!(
                        additive_fold_pair(beta, lambda, x, fx, fx_shifted).unwrap(),
                        expected
                    );
                }
            }
        }
    }
}
