//! Empirical crossover for two ways to evaluate one equality-weighted sparse table.
//!
//! The case schedule is emitted by `Compiler.SparseEqualityWorkProfile`; this
//! binary rejects any other schema.  It measures opaque Rust arithmetic only.
//! `mle_sparseTable` proves the two abstract plans have one Lean target, but no
//! theorem connects either native result to that target.

use std::error::Error;
use std::hint::black_box;
use std::io;
use std::mem::size_of;
use std::path::Path;
use std::time::{Duration, Instant};

use minidregg_prover::binary_tower_256::Tower256;
use minidregg_prover::tower256_kernels::{dot_product, equality_weights, scatter_weights};

const PROFILE_SCHEMA: &str = "minidregg/sparse-equality-work-profile/v1";
const PROFILE_HEADER: &str = "schema,log_domain,domain_points,active_rows,iterations,dense_mul_count,sparse_mul_count,dense_extra_bytes";

#[derive(Clone, Copy, Debug)]
struct Case {
    log_domain: usize,
    domain_points: usize,
    active_rows: usize,
    iterations: u32,
    dense_mul_count: usize,
    sparse_mul_count: usize,
    dense_extra_bytes: usize,
}

fn invalid(detail: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, detail.into())
}

fn parse_usize(value: &str, role: &str, line: usize) -> Result<usize, io::Error> {
    value
        .parse()
        .map_err(|_| invalid(format!("line {line}: invalid {role} `{value}`")))
}

fn parse_profile(path: &Path) -> Result<Vec<Case>, Box<dyn Error>> {
    let text = std::fs::read_to_string(path)?;
    let mut lines = text.lines();
    if lines.next() != Some(PROFILE_HEADER) {
        return Err(invalid("profile header or version does not match the Lean emitter").into());
    }

    let mut cases = Vec::new();
    for (offset, line) in lines.enumerate() {
        let line_number = offset + 2;
        let columns = line.split(',').collect::<Vec<_>>();
        if columns.len() != 8 || columns[0] != PROFILE_SCHEMA {
            return Err(invalid(format!(
                "line {line_number}: expected eight columns under schema {PROFILE_SCHEMA}"
            ))
            .into());
        }
        let log_domain = parse_usize(columns[1], "log_domain", line_number)?;
        let domain_points = parse_usize(columns[2], "domain_points", line_number)?;
        let active_rows = parse_usize(columns[3], "active_rows", line_number)?;
        let iterations_usize = parse_usize(columns[4], "iterations", line_number)?;
        let iterations = u32::try_from(iterations_usize)
            .map_err(|_| invalid(format!("line {line_number}: iterations exceed u32")))?;
        let case = Case {
            log_domain,
            domain_points,
            active_rows,
            iterations,
            dense_mul_count: parse_usize(columns[5], "dense_mul_count", line_number)?,
            sparse_mul_count: parse_usize(columns[6], "sparse_mul_count", line_number)?,
            dense_extra_bytes: parse_usize(columns[7], "dense_extra_bytes", line_number)?,
        };
        if case.log_domain == 0
            || !case.domain_points.is_power_of_two()
            || case.domain_points.trailing_zeros() as usize != case.log_domain
            || case.active_rows == 0
            || case.active_rows > case.domain_points
            || case.iterations == 0
            || size_of::<Tower256>() != 32
        {
            return Err(
                invalid(format!("line {line_number}: malformed work shape {case:?}")).into(),
            );
        }
        cases.push(case);
    }
    if cases.is_empty() {
        return Err(invalid("Lean profile contains no benchmark cases").into());
    }
    Ok(cases)
}

fn next_word(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

fn next_tower(state: &mut u64) -> Tower256 {
    Tower256::from_limbs([
        next_word(state),
        next_word(state),
        next_word(state),
        next_word(state),
    ])
}

fn fixture(case: Case) -> (Vec<Tower256>, Vec<usize>, Vec<Tower256>) {
    let mut state = 0x243f_6a88_85a3_08d3u64 ^ case.active_rows as u64;
    let point = (0..case.log_domain)
        .map(|_| next_tower(&mut state))
        .collect::<Vec<_>>();

    // Multiplication by an odd number permutes every `2^m` address space, so
    // this prefix contains no duplicate addresses.
    let mask = case.domain_points - 1;
    let addresses = (0..case.active_rows)
        .map(|row| row.wrapping_mul(40_503).wrapping_add(17) & mask)
        .collect::<Vec<_>>();
    let values = (0..case.active_rows)
        .map(|_| next_tower(&mut state))
        .collect::<Vec<_>>();
    (point, addresses, values)
}

fn dense_plan(
    point: &[Tower256],
    addresses: &[usize],
    values: &[Tower256],
    domain_points: usize,
) -> Tower256 {
    let equality = equality_weights(point).expect("Lean profile supplies a representable cube");
    let table = scatter_weights(addresses, values, domain_points)
        .expect("fixture addresses and values have a valid shape");
    dot_product(&equality, &table).expect("dense vectors have the same length")
}

fn sparse_plan(point: &[Tower256], addresses: &[usize], values: &[Tower256]) -> Tower256 {
    addresses
        .iter()
        .zip(values)
        .fold(Tower256::ZERO, |sum, (&address, &value)| {
            let equality =
                point
                    .iter()
                    .enumerate()
                    .fold(Tower256::ONE, |product, (bit, &coordinate)| {
                        let factor = if address & (1usize << bit) == 0 {
                            Tower256::ONE.add(coordinate)
                        } else {
                            coordinate
                        };
                        product.mul(factor)
                    });
            sum.add(value.mul(equality))
        })
}

fn elapsed_per_iteration(iterations: u32, mut work: impl FnMut() -> Tower256) -> Duration {
    let start = Instant::now();
    for _ in 0..iterations {
        black_box(work());
    }
    start.elapsed() / iterations
}

fn main() -> Result<(), Box<dyn Error>> {
    let profile_path = std::env::args_os()
        .nth(1)
        .ok_or_else(|| invalid("usage: sparse_equality_bench LEAN_PROFILE.csv"))?;
    let cases = parse_profile(Path::new(&profile_path))?;

    println!(
        "schema,log_domain,domain_points,active_rows,density,dense_mul_count,sparse_mul_count,dense_extra_bytes,dense_us,sparse_us,dense_over_sparse,winner"
    );
    for case in cases {
        let (point, addresses, values) = fixture(case);
        let dense = dense_plan(&point, &addresses, &values, case.domain_points);
        let sparse = sparse_plan(&point, &addresses, &values);
        if dense != sparse {
            return Err(invalid(format!(
                "native plans disagree at log_domain={}, active_rows={}",
                case.log_domain, case.active_rows
            ))
            .into());
        }

        black_box(dense_plan(&point, &addresses, &values, case.domain_points));
        black_box(sparse_plan(&point, &addresses, &values));
        let dense_time = elapsed_per_iteration(case.iterations, || {
            dense_plan(
                black_box(&point),
                black_box(&addresses),
                black_box(&values),
                case.domain_points,
            )
        });
        let sparse_time = elapsed_per_iteration(case.iterations, || {
            sparse_plan(black_box(&point), black_box(&addresses), black_box(&values))
        });
        let dense_us = dense_time.as_secs_f64() * 1e6;
        let sparse_us = sparse_time.as_secs_f64() * 1e6;
        let ratio = dense_us / sparse_us;
        let winner = if ratio > 1.0 { "sparse" } else { "dense" };
        println!(
            "{PROFILE_SCHEMA},{},{},{},{:.8},{},{},{},{:.2},{:.2},{:.4},{winner}",
            case.log_domain,
            case.domain_points,
            case.active_rows,
            case.active_rows as f64 / case.domain_points as f64,
            case.dense_mul_count,
            case.sparse_mul_count,
            case.dense_extra_bytes,
            dense_us,
            sparse_us,
            ratio,
        );
    }
    Ok(())
}
