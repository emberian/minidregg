//! Concrete linear observation falsifiers for the source-derived mask budget.
//! Covers the trace-opening map only, not quotient/FRI transcript simulation.
use p3_baby_bear::BabyBear as F;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, TwoAdicField,
    extension::BinomialExtensionField};
type E = BinomialExtensionField<F, 4>;

// Return one solution and rank; None means the requested observation shift
// cannot be produced by any mask. Gaussian elimination is test-side evidence,
// not a runtime admission oracle or a replacement for the general theorem.
fn solve(mut rows: Vec<Vec<F>>, mut rhs: Vec<F>, columns: usize) -> Option<(usize, Vec<F>)> {
    let mut pivot_columns = vec![];
    for column in 0..columns {
        let pivot_row = pivot_columns.len();
        let Some(found) = (pivot_row..rows.len()).find(|&i| !rows[i][column].is_zero()) else { continue; };
        rows.swap(pivot_row, found); rhs.swap(pivot_row, found);
        let inverse = rows[pivot_row][column].inverse();
        for c in column..columns { rows[pivot_row][c] *= inverse; }
        rhs[pivot_row] *= inverse;
        for row in 0..rows.len() {
            if row == pivot_row { continue; }
            let factor = rows[row][column];
            for c in column..columns {
                let subtract = factor * rows[pivot_row][c];
                rows[row][c] -= subtract;
            }
            let subtract = factor * rhs[pivot_row]; rhs[row] -= subtract;
        }
        pivot_columns.push(column);
    }
    for row in pivot_columns.len()..rows.len() {
        if rows[row].iter().all(|x| x.is_zero()) && !rhs[row].is_zero() { return None; }
    }
    let mut answer = vec![F::ZERO; columns];
    for (row, &column) in pivot_columns.iter().enumerate() { answer[column] = rhs[row]; }
    Some((pivot_columns.len(), answer))
}

fn observation_map(trace_rows: usize, mask_coefficients: usize) -> Vec<Vec<F>> {
    let z = E::from_basis_coefficients_slice(&[F::new(8), F::ONE, F::ZERO, F::ZERO]).unwrap();
    let g = F::two_adic_generator(trace_rows.ilog2() as usize);
    let mut rows = vec![];
    for point in [z, z * E::from(g)] {
        let vanish = point.exp_u64(trace_rows as u64) - E::ONE;
        let columns: Vec<E> = (0..mask_coefficients)
            .map(|j| vanish * point.exp_u64(j as u64)).collect();
        for coordinate in 0..4 {
            rows.push(columns.iter().map(|x| {
                let coordinates: &[F] = x.as_basis_coefficients_slice(); coordinates[coordinate]
            }).collect());
        }
    }
    // Nineteen distinct members of the backend's shifted LDE domain. Actual
    // Fiat-Shamir indices are random; this deliberately isn't called a proof
    // of coverage for every possible query set.
    let lde_generator = F::two_adic_generator(trace_rows.ilog2() as usize + 1 + 6);
    for index in 0..19 {
        let point = F::GENERATOR * lde_generator.exp_u64(index);
        let vanish = point.exp_u64(trace_rows as u64) - F::ONE;
        rows.push((0..mask_coefficients).map(|j| vanish * point.exp_u64(j as u64)).collect());
    }
    rows
}

#[test]
fn minimum_and_normal_trace_masks_cover_concrete_opening_map() {
    for trace_rows in [32, 256] {
        let matrix = observation_map(trace_rows, trace_rows);
        let target: Vec<F> = (0..27).map(|i| F::from_bool(i == 0 || i == 4 || i >= 8)).collect();
        let (rank, offset) = solve(matrix.clone(), target.clone(), trace_rows).unwrap();
        assert_eq!(rank, 27);
        // Changing constant witness zero to one can be exactly hidden by this
        // mask translation at every represented extension/base observation.
        for (row, target) in matrix.iter().zip(target) {
            let actual: F = row.iter().zip(&offset).map(|(a,b)| *a * *b).sum();
            assert_eq!(actual, target);
        }
    }
}

#[test]
fn one_row_mask_cannot_cover_nonbase_opening() {
    let matrix = observation_map(1, 1);
    // With H={1}, vanishing mask coefficient cannot cancel constant one at a
    // nonbase point. This is the algebraic obstruction in the actual raw proof.
    let target: Vec<F> = (0..27).map(|i| F::from_bool(i == 0 || i == 4 || i >= 8)).collect();
    assert!(solve(matrix, target, 1).is_none());
}
