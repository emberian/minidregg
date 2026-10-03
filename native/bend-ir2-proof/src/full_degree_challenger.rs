//! Profile-owned degree-four challenge conditioning, shared by actual prover
//! and verifier. The P3 randomization polynomial uses base-field columns
//! combined by powers of the batching challenge. Requiring those powers to
//! span the extension removes the subfield rank-degeneracy case. This changes
//! the transcript protocol and does NOT establish whole-transcript ZK or its
//! soundness bound. No shared/vendor backend is modified.
use p3_baby_bear::BabyBear as F;
use p3_challenger::{CanObserve, CanSample, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing,
    extension::BinomialExtensionField};
type E = BinomialExtensionField<F, 4>;

/// Exact Gaussian rank of the extension power basis over BabyBear.
pub fn powers_span_extension(value: E) -> bool {
    let powers = [E::ONE, value, value * value, value * value * value];
    let mut rows = [[F::ZERO; 4]; 4];
    for (column, power) in powers.iter().enumerate() {
        let coefficients: &[F] = power.as_basis_coefficients_slice();
        for row in 0..4 { rows[row][column] = coefficients[row]; }
    }
    for column in 0..4 {
        let Some(pivot) = (column..4).find(|&row| !rows[row][column].is_zero()) else { return false; };
        rows.swap(column, pivot);
        let inverse = rows[column][column].inverse();
        for entry in column..4 { rows[column][entry] *= inverse; }
        for row in column + 1..4 {
            let factor = rows[row][column];
            for entry in column..4 {
                let subtract = factor * rows[column][entry]; rows[row][entry] -= subtract;
            }
        }
    }
    true
}

#[derive(Clone)]
pub struct FullDegreeChallenger<C> { inner: C }
impl<C> FullDegreeChallenger<C> { pub fn new(inner: C) -> Self { Self { inner } } }
impl<C, T> CanObserve<T> for FullDegreeChallenger<C> where C: CanObserve<T> {
    fn observe(&mut self, value: T) { self.inner.observe(value); }
}
impl<C, T> CanSample<T> for FullDegreeChallenger<C> where C: CanSample<T> {
    fn sample(&mut self) -> T { self.inner.sample() }
}
impl<C> CanSampleBits<usize> for FullDegreeChallenger<C> where C: CanSampleBits<usize> {
    fn sample_bits(&mut self, bits: usize) -> usize { self.inner.sample_bits(bits) }
}
impl<C> FieldChallenger<F> for FullDegreeChallenger<C> where C: FieldChallenger<F> {
    fn sample_algebra_element<A: BasedVectorSpace<F>>(&mut self) -> A {
        // This explicit profile uses BabyBear and its actual binomial degree4
        // extension only, pinned by Config. DIMENSION alone is not an algebra
        // identity check; this wrapper is not a generic extension-field adapter.
        assert!(A::DIMENSION == 1 || A::DIMENSION == 4, "unsupported challenge dimension");
        for _ in 0..128 {
            let coefficients: Vec<F> = (0..A::DIMENSION).map(|_| self.inner.sample()).collect();
            if A::DIMENSION == 1 || powers_span_extension(E::from_basis_coefficients_slice(&coefficients).unwrap()) {
                return A::from_basis_coefficients_slice(&coefficients).unwrap();
            }
        }
        // Trait has no fallible draw. The offline harness fails closed; a
        // future service receiver must contain this failure as a refusal.
        panic!("degree-four challenge conditioning exhausted bounded attempts");
    }
}
impl<C> GrindingChallenger for FullDegreeChallenger<C>
where C: GrindingChallenger<Witness = F> {
    type Witness = F;
    fn grind(&mut self, bits: usize) -> F { self.inner.grind(bits) }
    fn check_witness(&mut self, bits: usize, witness: F) -> bool { self.inner.check_witness(bits, witness) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn base_and_quadratic_subfield_challenges_are_refused() {
        assert!(!powers_span_extension(E::from(F::new(7))));
        // X^2 belongs to the quadratic subfield of the binomial degree4 field.
        let x_squared = E::from_basis_coefficients_slice(&[F::ZERO,F::ZERO,F::ONE,F::ZERO]).unwrap();
        assert!(!powers_span_extension(x_squared));
        let generator = E::from_basis_coefficients_slice(&[F::new(8),F::ONE,F::ZERO,F::ZERO]).unwrap();
        assert!(powers_span_extension(generator));
    }
    #[derive(Clone)]
    struct Scripted { values: std::collections::VecDeque<F>, consumed: usize }
    impl CanObserve<F> for Scripted { fn observe(&mut self, _: F) {} }
    impl CanSample<F> for Scripted {
        fn sample(&mut self) -> F { self.consumed += 1; self.values.pop_front().unwrap() }
    }
    impl CanSampleBits<usize> for Scripted {
        fn sample_bits(&mut self, _: usize) -> usize { panic!("not used by extension draws") }
    }
    impl FieldChallenger<F> for Scripted {}
    #[test]
    fn paired_draw_rejects_bad_basis_and_consumes_same_transcript() {
        let script = Scripted { values: [7,0,0,0,8,1,0,0].into_iter().map(F::new).collect(), consumed: 0 };
        let mut prover = FullDegreeChallenger::new(script.clone());
        let mut verifier = FullDegreeChallenger::new(script);
        let a: E = prover.sample_algebra_element();
        let b: E = verifier.sample_algebra_element();
        assert_eq!(a, b);
        assert!(powers_span_extension(a));
        assert_eq!(prover.inner.consumed, 8);
        assert_eq!(verifier.inner.consumed, 8);
    }

    #[test]
    fn base_field_draw_consumes_exactly_one_unchanged_sample() {
        let script = Scripted { values: [7,11].into_iter().map(F::new).collect(), consumed: 0 };
        let mut challenger = FullDegreeChallenger::new(script);
        let first: F = challenger.sample_algebra_element();
        let second: F = challenger.sample_algebra_element();
        assert_eq!(first, F::new(7)); assert_eq!(second, F::new(11));
        assert_eq!(challenger.inner.consumed, 2);
    }
    #[test]
    fn exhausted_conditioning_fails_closed_after_exact_bound() {
        let script = Scripted { values: vec![F::ZERO; 4*128].into(), consumed: 0 };
        let mut challenger = FullDegreeChallenger::new(script);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _: E = challenger.sample_algebra_element();
        }));
        assert!(outcome.is_err());
        assert_eq!(challenger.inner.consumed, 4*128);
    }

}
