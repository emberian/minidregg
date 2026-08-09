//! Runtime teeth for `[PROVER-challenge-field-unification]`.

use minidregg_prover::field4::{badd, bmul, P};
use minidregg_prover::field6::{Ext6, EXT6_W};
use minidregg_prover::gate_kernels::{
    batch_lifted_residuals, evaluate_mle, table_sum, GateKernelError,
};

fn e(limbs: [u64; 6]) -> Ext6 {
    Ext6::try_from_limbs(limbs).expect("test vector is canonical")
}

fn base(value: u64) -> Ext6 {
    Ext6::try_from_base(value).expect("test base value is canonical")
}

fn prng(seed: &mut u64) -> u64 {
    *seed = seed
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    (*seed >> 16) % P
}

fn random_ext6(seed: &mut u64) -> Ext6 {
    e([
        prng(seed),
        prng(seed),
        prng(seed),
        prng(seed),
        prng(seed),
        prng(seed),
    ])
}

fn literal_mle(table: &[Ext6], point: &[Ext6]) -> Ext6 {
    table
        .iter()
        .enumerate()
        .fold(Ext6::ZERO, |sum, (index, &value)| {
            let weight =
                point
                    .iter()
                    .enumerate()
                    .fold(Ext6::ONE, |product, (coordinate, &challenge)| {
                        let factor = if (index >> coordinate) & 1 == 1 {
                            challenge
                        } else {
                            Ext6::ONE.sub(challenge)
                        };
                        product.mul(factor)
                    });
            sum.add(value.mul(weight))
        })
}

#[test]
fn ext6_known_products_and_defining_relation_match_lean_vectors() {
    let a = e([
        123456789, 987654321, 555555555, 2013265920, 314159265, 271828182,
    ]);
    let b = e([1999999999, 42, 1414213562, 777000777, 1618033988, 42424242]);
    assert_eq!(
        a.mul(b).limbs(),
        &[1935082458, 589685295, 173991560, 1528914995, 1641578725, 1780603210]
    );

    let a_edge = e([P - 1, P - 2, P - 3, P - 4, P - 5, P - 6]);
    let b_edge = e([1, 2, 3, P - 1, P - 2, P - 3]);
    assert_eq!(
        a_edge.mul(b_edge).limbs(),
        &[P - 342, 120, 858, 822, 540, P - 18]
    );

    let u = e([0, 1, 0, 0, 0, 0]);
    assert_eq!(u.pow(6), base(EXT6_W));
}

#[test]
fn ext6_ring_laws_and_base_embedding_have_teeth() {
    let mut seed = 0x6e78_7436_u64;
    for _ in 0..1_000 {
        let a = random_ext6(&mut seed);
        let b = random_ext6(&mut seed);
        let c = random_ext6(&mut seed);
        assert_eq!(a.add(b), b.add(a));
        assert_eq!(a.mul(b), b.mul(a));
        assert_eq!(a.mul(b).mul(c), a.mul(b.mul(c)));
        assert_eq!(a.mul(b.add(c)), a.mul(b).add(a.mul(c)));
        assert_eq!(a.sub(b).add(b), a);
        assert_eq!(a.mul(Ext6::ONE), a);
        assert_eq!(a.mul(Ext6::ZERO), Ext6::ZERO);

        let x = prng(&mut seed);
        let y = prng(&mut seed);
        assert_eq!(base(x).add(base(y)), base(badd(x, y)));
        assert_eq!(base(x).mul(base(y)), base(bmul(x, y)));
    }
}

#[test]
fn ext6_canonical_decoder_rejects_every_bad_lane() {
    for lane in 0..6 {
        let mut limbs = [0; 6];
        limbs[lane] = P;
        let error = Ext6::try_from_limbs(limbs).expect_err("limb equal to p is noncanonical");
        assert_eq!(error.lane, lane);
        assert_eq!(error.value, P);
    }
    assert!(Ext6::try_from_base(P).is_err());
}

#[test]
fn irreducibility_rabin_certificate_is_executable() {
    // For f = X^6 - 31, repeated q-Frobenius sends X to r^k X.
    let u = e([0, 1, 0, 0, 0, 0]);
    let expected = [1314723124, 1314723123, P - 1, 698542797, 698542798, 1];
    let mut frobenius = u;
    for &coefficient in &expected {
        frobenius = frobenius.pow(P);
        assert_eq!(frobenius, u.base_mul(coefficient));
    }
    assert_eq!(frobenius, u, "X^(q^6) - X vanishes modulo f");

    // The q^2 and q^3 differences are cX.  These are explicit Bezout
    // certificates with f, so both required Rabin gcds are one.
    let minus_inv_31 = 1948321859;
    assert_eq!(bmul(P - EXT6_W, minus_inv_31), 1);
    for (c, b) in [(1314723122, 1068264225), (P - 2, 1980793890)] {
        assert_eq!(badd(minus_inv_31, bmul(b, c)), 0);
    }
}

#[test]
fn generic_sumcheck_matches_literal_ext6_mle_through_dimension_eight() {
    let mut seed = 0x5ca1_ab1e_u64;
    for dimension in 0..=8 {
        let table: Vec<Ext6> = (0..1usize << dimension)
            .map(|_| random_ext6(&mut seed))
            .collect();
        let point: Vec<Ext6> = (0..dimension).map(|_| random_ext6(&mut seed)).collect();
        let fast_terminal = evaluate_mle(&table, &point).unwrap();
        let literal_terminal = literal_mle(&table, &point);
        assert_eq!(fast_terminal, literal_terminal, "dimension {dimension}");
    }
}

#[test]
fn extension_gamma_batches_lifted_base_residuals() {
    // Defect polynomial -1 + gamma has its unique escape at gamma = 1,
    // whether the challenge is in the base field or Ext6.  A non-base u
    // challenge produces genuine cross-lane residuals and does not escape.
    let residuals = [P - 1, 1];
    let at_one = batch_lifted_residuals::<Ext6>(&residuals, Ext6::ONE).unwrap();
    assert_eq!(table_sum(&at_one).unwrap(), Ext6::ZERO);

    let u = e([0, 1, 0, 0, 0, 0]);
    let at_u = batch_lifted_residuals::<Ext6>(&residuals, u).unwrap();
    assert_eq!(at_u[1], u);
    assert!(!table_sum(&at_u).unwrap().is_zero());

    assert_eq!(
        batch_lifted_residuals::<Ext6>(&[P], u),
        Err(GateKernelError::NonCanonicalBase { index: 0, value: P })
    );
}
