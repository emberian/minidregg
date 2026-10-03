//! Calls the actual pinned PCS/DFT and verifier; does not replace either with
//! the Lean algebraic model. This is a correspondence regression, not ZK.
#[path = "../src/config.rs"] mod config;
#[path = "../src/masking_budget.rs"] mod masking_budget;
#[path = "../src/full_degree_challenger.rs"] mod full_degree_challenger;
use p3_baby_bear::BabyBear as F;
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{Field, PrimeCharacteristicRing, coset::TwoAdicMultiplicativeCoset};
use p3_matrix::{Matrix, dense::RowMajorMatrix};
use p3_uni_stark::{StarkGenericConfig, recompose_quotient_from_chunks};
type C = config::Config;
type E = <C as StarkGenericConfig>::Challenge;
type Challenger = <C as StarkGenericConfig>::Challenger;
type Backend = <C as StarkGenericConfig>::Pcs;

#[test]
fn native_quotient_masks_preserve_verifier_recomposition() {
    let config = config::for_capacity(masking_budget::TraceCapacity::checked(32).unwrap()).unwrap();
    // More than two chunks checks the dependent last-mask sum, not only a pair.
    for chunks in [2usize, 4] {
        let h = 32usize;
        let log_degree = (h * chunks).ilog2() as usize;
        let whole = TwoAdicMultiplicativeCoset::new(F::ONE, log_degree).unwrap();
        let domains = whole.split_domains(chunks);
        let inputs = domains.iter().map(|&domain|
            (domain, RowMajorMatrix::new(vec![F::ZERO; h * 4], 4)));
        let ldes = <Backend as Pcs<E, Challenger>>::get_quotient_ldes(config.pcs(), inputs, chunks);
        let height = ldes[0].height();
        let log_height = height.ilog2() as usize;
        let opening_domain = TwoAdicMultiplicativeCoset::new(F::GENERATOR, log_height).unwrap();
        let mut point = opening_domain.first_point();
        assert!(ldes.iter().any(|matrix| matrix.values.chunks(matrix.width())
            .any(|row| row[..4].iter().any(|value| !value.is_zero()))),
            "the PCS must actually mask the zero quotient");
        for row in 0..height {
            // get_quotient_ldes returns bit-reversed rows; verifier sees ordinary points.
            let reversed = row.reverse_bits() >> (usize::BITS as usize - log_height);
            let opened: Vec<Vec<E>> = ldes.iter().map(|matrix|
                matrix.values[reversed * matrix.width()..reversed * matrix.width() + 4]
                    .iter().copied().map(E::from).collect()).collect();
            let result = recompose_quotient_from_chunks::<C>(&domains, &opened, E::from(point));
            assert_eq!(result, E::ZERO, "masked chunks must recompose to the original zero quotient");
            point = opening_domain.next_point(point).unwrap();
        }
    }
}
