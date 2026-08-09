//! Manual generated-dispatch overhead benchmark for authenticated work `9101`.
//!
//! The schedule, fixture-pattern identity, seed, work/profile/codec pins, and a
//! canonical `1 · 1` sentinel request/response are emitted by Lean.  Before any
//! timing, the binary checks the sentinel and requires every measured generated
//! dispatch result to be byte-identical to the same direct Tower256 dot-product
//! kernel.  These are empirical diagnostics, never refinement evidence.

use std::error::Error;
use std::hint::black_box;
use std::io;
use std::time::Instant;

use minidregg_prover::binary_tower_256::Tower256;
use minidregg_prover::semantic_artifact_v1::{
    dispatch_native, NativeWorkRequestDto, WORK_0_BENCHMARK_PATTERN, WORK_0_BENCHMARK_SCHEDULE,
    WORK_0_BENCHMARK_SCHEMA, WORK_0_BENCHMARK_SEED, WORK_0_BENCHMARK_SENTINEL_REQUEST,
    WORK_0_BENCHMARK_SENTINEL_RESPONSE, WORK_0_CARRIER_PROFILE_ID_DECIMAL, WORK_0_ID_DECIMAL,
    WORK_0_REQUEST_CODEC_ID_DECIMAL, WORK_0_REQUEST_COORDINATE_WIDTH, WORK_0_REQUEST_COUNT_WIDTH,
    WORK_0_REQUEST_VECTOR_ARITY, WORK_0_RESPONSE_CODEC_ID_DECIMAL, WORK_0_RESPONSE_WIDTH,
};
use minidregg_prover::tower256_kernels::dot_product;

fn invalid(detail: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, detail.into())
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

fn fixture(vector_length: usize) -> (Vec<Tower256>, Vec<Tower256>) {
    let mut left_state = WORK_0_BENCHMARK_SEED ^ vector_length as u64;
    let mut right_state = WORK_0_BENCHMARK_SEED.rotate_left(29) ^ !(vector_length as u64);
    let left = (0..vector_length)
        .map(|_| next_tower(&mut left_state))
        .collect();
    let right = (0..vector_length)
        .map(|_| next_tower(&mut right_state))
        .collect();
    (left, right)
}

fn encode_request(left: &[Tower256], right: &[Tower256]) -> Result<Vec<u8>, io::Error> {
    if left.len() != right.len() || WORK_0_REQUEST_COUNT_WIDTH != 4 {
        return Err(invalid(
            "fixture does not satisfy the emitted request shape",
        ));
    }
    let count = u32::try_from(left.len()).map_err(|_| invalid("vector length exceeds u32"))?;
    let payload = left
        .len()
        .checked_mul(WORK_0_REQUEST_COORDINATE_WIDTH)
        .and_then(|width| width.checked_mul(WORK_0_REQUEST_VECTOR_ARITY))
        .ok_or_else(|| invalid("request length overflows usize"))?;
    let mut bytes = Vec::with_capacity(WORK_0_REQUEST_COUNT_WIDTH + payload);
    bytes.extend_from_slice(&count.to_le_bytes());
    for value in left {
        bytes.extend_from_slice(&value.to_le_bytes());
    }
    for value in right {
        bytes.extend_from_slice(&value.to_le_bytes());
    }
    Ok(bytes)
}

fn dispatch_bytes(request_bytes: &[u8]) -> Result<Box<[u8]>, Box<dyn Error>> {
    let request = NativeWorkRequestDto::from_ids(
        WORK_0_ID_DECIMAL,
        WORK_0_CARRIER_PROFILE_ID_DECIMAL,
        WORK_0_REQUEST_CODEC_ID_DECIMAL,
        WORK_0_RESPONSE_CODEC_ID_DECIMAL,
        request_bytes.to_vec().into_boxed_slice(),
    )
    .map_err(|error| {
        invalid(format!(
            "generated request error: {:?}: {}",
            error.kind, error.detail
        ))
    })?;
    Ok(dispatch_native(request)
        .map_err(|error| {
            invalid(format!(
                "native dispatch error: {:?}: {}",
                error.kind, error.detail
            ))
        })?
        .into_response_bytes())
}

fn validate_sentinel() -> Result<(), Box<dyn Error>> {
    let response = dispatch_bytes(WORK_0_BENCHMARK_SENTINEL_REQUEST)?;
    if response.as_ref() != WORK_0_BENCHMARK_SENTINEL_RESPONSE {
        return Err(invalid("generated dispatch failed the Lean-encoded 1 · 1 sentinel").into());
    }
    Ok(())
}

fn elapsed_batch_ns(batch_repetitions: usize, mut work: impl FnMut()) -> u128 {
    let start = Instant::now();
    for _ in 0..batch_repetitions {
        work();
    }
    start.elapsed().as_nanos()
}

fn median(mut values: Vec<f64>) -> f64 {
    values.sort_by(f64::total_cmp);
    values[values.len() / 2]
}

fn main() -> Result<(), Box<dyn Error>> {
    if WORK_0_BENCHMARK_PATTERN != "xorshift64-four-limb/v1"
        || WORK_0_RESPONSE_WIDTH != WORK_0_BENCHMARK_SENTINEL_RESPONSE.len()
        || WORK_0_BENCHMARK_SCHEDULE.is_empty()
    {
        return Err(invalid("unsupported or malformed Lean benchmark constants").into());
    }
    validate_sentinel()?;

    println!(
        "schema,work_id,carrier_profile_id,request_codec_id,response_codec_id,pattern,vector_length,batch_repetitions,samples,request_bytes,direct_ns_per_call,dispatch_ns_per_call,dispatch_overhead_ns,dispatch_over_direct,direct_calls_per_s,dispatch_calls_per_s,direct_coordinates_per_s,dispatch_coordinates_per_s,dispatch_request_mib_per_s"
    );
    for &(vector_length, batch_repetitions, samples) in WORK_0_BENCHMARK_SCHEDULE {
        if vector_length == 0 || batch_repetitions == 0 || samples == 0 {
            return Err(invalid("Lean benchmark schedule contains a zero dimension").into());
        }
        let (left, right) = fixture(vector_length);
        let request_bytes = encode_request(&left, &right)?;
        let direct_expected = dot_product(&left, &right)?.to_le_bytes();
        let dispatched = dispatch_bytes(&request_bytes)?;
        if dispatched.as_ref() != direct_expected {
            return Err(invalid(format!(
                "direct and generated-dispatch bytes differ at vector length {vector_length}"
            ))
            .into());
        }

        black_box(dot_product(&left, &right)?);
        black_box(dispatch_bytes(&request_bytes)?);
        let mut direct_samples = Vec::with_capacity(samples);
        let mut dispatch_samples = Vec::with_capacity(samples);
        for sample in 0..samples {
            let time_direct = || {
                elapsed_batch_ns(batch_repetitions, || {
                    black_box(
                        dot_product(black_box(&left), black_box(&right))
                            .expect("validated vectors retain equal length"),
                    );
                })
            };
            let time_dispatch = || {
                elapsed_batch_ns(batch_repetitions, || {
                    black_box(
                        dispatch_bytes(black_box(&request_bytes))
                            .expect("validated generated request remains executable"),
                    );
                })
            };
            let (direct_total, dispatch_total) = if sample % 2 == 0 {
                (time_direct(), time_dispatch())
            } else {
                let dispatch = time_dispatch();
                (time_direct(), dispatch)
            };
            direct_samples.push(direct_total as f64 / batch_repetitions as f64);
            dispatch_samples.push(dispatch_total as f64 / batch_repetitions as f64);
        }

        let direct_ns = median(direct_samples);
        let dispatch_ns = median(dispatch_samples);
        let direct_calls = 1e9 / direct_ns;
        let dispatch_calls = 1e9 / dispatch_ns;
        let request_mib = request_bytes.len() as f64 / (1024.0 * 1024.0);
        println!(
            "{WORK_0_BENCHMARK_SCHEMA},{WORK_0_ID_DECIMAL},{WORK_0_CARRIER_PROFILE_ID_DECIMAL},{WORK_0_REQUEST_CODEC_ID_DECIMAL},{WORK_0_RESPONSE_CODEC_ID_DECIMAL},{WORK_0_BENCHMARK_PATTERN},{vector_length},{batch_repetitions},{samples},{},{direct_ns:.2},{dispatch_ns:.2},{:.2},{:.6},{direct_calls:.2},{dispatch_calls:.2},{:.2},{:.2},{:.2}",
            request_bytes.len(),
            dispatch_ns - direct_ns,
            dispatch_ns / direct_ns,
            direct_calls * vector_length as f64,
            dispatch_calls * vector_length as f64,
            dispatch_calls * request_mib,
        );
    }
    Ok(())
}
