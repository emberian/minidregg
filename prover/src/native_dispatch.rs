//! Fallible opaque byte adapters selected by Lean-generated dispatch.
//!
//! This module contains no work/profile identifiers, transcript state,
//! proposition, verifier verdict, or acceptance token.  The generated module
//! chooses the only callable operation and pins its request/response codecs.
//! This adapter merely parses that codec, invokes an unverified computational
//! kernel, and returns bytes or a local error.  Lean remains the sole decoder,
//! checker, and acceptor of the returned bytes.

use core::fmt;

use crate::babybear::{badd, bmul, P};
use crate::binary_tower_256::{Tower256, Tower256Error};
use crate::evm_stage0_add_aux::{
    WORK_2_DESCRIPTOR_N_VARS, WORK_2_DESCRIPTOR_N_WIRES, WORK_2_FIELD_MODULUS, WORK_2_ROWS,
};
use crate::semantic_artifact_arithmetic::{WORK_1_FIXED_CANDIDATE_RESPONSE, WORK_1_REQUEST_WIDTH};
use crate::semantic_artifact_v1::{
    WORK_0_REQUEST_COORDINATE_WIDTH, WORK_0_REQUEST_COUNT_WIDTH, WORK_0_REQUEST_VECTOR_ARITY,
};
use crate::tower256_kernels::{dot_product, Tower256KernelError};

/// Local parsing or execution failures.  None is a semantic rejection verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeDispatchError {
    LengthOverflow,
    EncodedLength { actual: usize, expected: usize },
    Coordinate(Tower256Error),
    Kernel(Tower256KernelError),
    /// The generated row table was emitted for a different modulus than this kernel's field.
    FieldModulus { table: u64, kernel: u64 },
    /// The header counts cannot describe a wire vector (`n_vars > n_wires`).
    HeaderShape { n_vars: usize, n_wires: usize },
    /// A request word or row constant is not a canonical residue.
    WordAboveModulus { index: usize, value: u32 },
    /// A row reads a wire that neither the request nor an earlier row has written.
    ReadBeforeWrite { row: usize, wire: u32 },
    /// A row writes a wire that already holds a value.
    Rewrite { row: usize, wire: u32 },
    /// A row names a wire at or past the declared wire count.
    WireOutOfRange { row: usize, wire: u32 },
    /// A row carries an operand kind or gate op the generated encoding does not define.
    RowEncoding { row: usize },
    /// A wire no row wrote; the evaluator fabricates no default for it.
    UnwrittenWire { wire: usize },
}

impl fmt::Display for NativeDispatchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LengthOverflow => write!(f, "native request length overflows usize"),
            Self::EncodedLength { actual, expected } => write!(
                f,
                "native request has {actual} bytes, expected exactly {expected}"
            ),
            Self::Coordinate(error) => error.fmt(f),
            Self::Kernel(error) => error.fmt(f),
            Self::FieldModulus { table, kernel } => write!(
                f,
                "generated row table is over modulus {table}, kernel field is {kernel}"
            ),
            Self::HeaderShape { n_vars, n_wires } => {
                write!(f, "descriptor header has {n_vars} variables but {n_wires} wires")
            }
            Self::WordAboveModulus { index, value } => {
                write!(f, "word {index} = {value} is not a canonical residue")
            }
            Self::ReadBeforeWrite { row, wire } => {
                write!(f, "row {row} reads wire {wire} before any row wrote it")
            }
            Self::Rewrite { row, wire } => write!(f, "row {row} rewrites wire {wire}"),
            Self::WireOutOfRange { row, wire } => {
                write!(f, "row {row} names wire {wire} outside the declared wire count")
            }
            Self::RowEncoding { row } => {
                write!(f, "row {row} uses an operand kind or gate op outside the encoding")
            }
            Self::UnwrittenWire { wire } => write!(f, "no row wrote wire {wire}"),
        }
    }
}

impl std::error::Error for NativeDispatchError {}

impl From<Tower256Error> for NativeDispatchError {
    fn from(value: Tower256Error) -> Self {
        Self::Coordinate(value)
    }
}

impl From<Tower256KernelError> for NativeDispatchError {
    fn from(value: Tower256KernelError) -> Self {
        Self::Kernel(value)
    }
}

/// Execute the Lean-emitted
/// `u32_le(count) || left[count][32] || right[count][32]` codec.
///
/// The arithmetic is intentionally unverified native compute.  Even a
/// successful return is only a 32-byte candidate for Lean's canonical decoder
/// and selected checker.
pub fn tower256_dot_product_bytes(request: &[u8]) -> Result<Vec<u8>, NativeDispatchError> {
    let count_bytes: [u8; WORK_0_REQUEST_COUNT_WIDTH] = request
        .get(..WORK_0_REQUEST_COUNT_WIDTH)
        .ok_or(NativeDispatchError::EncodedLength {
            actual: request.len(),
            expected: WORK_0_REQUEST_COUNT_WIDTH,
        })?
        .try_into()
        .expect("the exact four-byte prefix was selected");
    let count = u32::from_le_bytes(count_bytes) as usize;
    let payload_width = count
        .checked_mul(WORK_0_REQUEST_COORDINATE_WIDTH)
        .and_then(|width| width.checked_mul(WORK_0_REQUEST_VECTOR_ARITY))
        .ok_or(NativeDispatchError::LengthOverflow)?;
    let expected = WORK_0_REQUEST_COUNT_WIDTH
        .checked_add(payload_width)
        .ok_or(NativeDispatchError::LengthOverflow)?;
    if request.len() != expected {
        return Err(NativeDispatchError::EncodedLength {
            actual: request.len(),
            expected,
        });
    }

    let split = WORK_0_REQUEST_COUNT_WIDTH + count * WORK_0_REQUEST_COORDINATE_WIDTH;
    let decode_vector = |bytes: &[u8]| -> Result<Vec<Tower256>, NativeDispatchError> {
        bytes
            .chunks_exact(WORK_0_REQUEST_COORDINATE_WIDTH)
            .map(|coordinate| Tower256::try_from_le_slice(coordinate).map_err(Into::into))
            .collect()
    };
    let left = decode_vector(&request[WORK_0_REQUEST_COUNT_WIDTH..split])?;
    let right = decode_vector(&request[split..])?;
    let candidate = dot_product(&left, &right)?;
    Ok(candidate.to_le_bytes().to_vec())
}

/// Return the exact Lean-emitted descriptor candidate for the fixed empty
/// add-1 request.  This adapter neither interprets the bytes nor asserts that
/// they satisfy anything; the generated dispatcher and Lean checker own those
/// decisions.
pub fn baby_bear_add1_zero_witness_bytes(request: &[u8]) -> Result<Vec<u8>, NativeDispatchError> {
    if request.len() != WORK_1_REQUEST_WIDTH {
        return Err(NativeDispatchError::EncodedLength {
            actual: request.len(),
            expected: WORK_1_REQUEST_WIDTH,
        });
    }
    Ok(WORK_1_FIXED_CANDIDATE_RESPONSE.to_vec())
}

/// One generated gate row: `(op, a_kind, a, b_kind, b, out)` — `op` 0 = add, 1 = mul;
/// an operand is `(0, value)` for a constant or `(1, index)` for a wire.  The encoding
/// is Lean's (`NativeGlueGen.rowOfGate`, left-invertible there); this module only reads it.
pub type DescriptorRow = (u8, u8, u32, u8, u32, u32);

/// Evaluate a Lean-emitted gate-row table over `n_vars` request words and return all
/// `n_wires` wires as u32 LE words.
///
/// Rows are visited in emission order; each reads two operands (a constant, or a wire the
/// request or an earlier row wrote) and writes exactly one fresh wire.  Every deviation —
/// a non-canonical word, a read before write, a second write, an index past `n_wires`, an
/// operand kind or op outside the encoding, a wire left unwritten — is a local execution
/// error.  None is a verdict: the reply is a candidate for Lean's `descriptorHoldsCheck`,
/// and no zero-check is evaluated here.  The arithmetic is BabyBear (`badd`/`bmul`); the
/// table's modulus must be this kernel's field.
pub fn evaluate_descriptor_rows(
    rows: &[DescriptorRow],
    n_vars: usize,
    n_wires: usize,
    modulus: u64,
    request: &[u8],
) -> Result<Vec<u8>, NativeDispatchError> {
    if modulus != P {
        return Err(NativeDispatchError::FieldModulus {
            table: modulus,
            kernel: P,
        });
    }
    if n_vars > n_wires {
        return Err(NativeDispatchError::HeaderShape { n_vars, n_wires });
    }
    let expected = n_vars
        .checked_mul(4)
        .ok_or(NativeDispatchError::LengthOverflow)?;
    if request.len() != expected {
        return Err(NativeDispatchError::EncodedLength {
            actual: request.len(),
            expected,
        });
    }

    let mut wires: Vec<Option<u64>> = vec![None; n_wires];
    for (index, word) in request.chunks_exact(4).enumerate() {
        let value = u32::from_le_bytes(word.try_into().expect("chunks_exact(4) yields 4 bytes"));
        if u64::from(value) >= P {
            return Err(NativeDispatchError::WordAboveModulus { index, value });
        }
        wires[index] = Some(u64::from(value));
    }

    fn read(
        wires: &[Option<u64>],
        row: usize,
        kind: u8,
        operand: u32,
    ) -> Result<u64, NativeDispatchError> {
        match kind {
            0 => {
                if u64::from(operand) >= P {
                    return Err(NativeDispatchError::WordAboveModulus {
                        index: row,
                        value: operand,
                    });
                }
                Ok(u64::from(operand))
            }
            1 => {
                let index = operand as usize;
                let slot = wires
                    .get(index)
                    .ok_or(NativeDispatchError::WireOutOfRange { row, wire: operand })?;
                slot.ok_or(NativeDispatchError::ReadBeforeWrite { row, wire: operand })
            }
            _ => Err(NativeDispatchError::RowEncoding { row }),
        }
    }

    for (row, &(op, a_kind, a, b_kind, b, out)) in rows.iter().enumerate() {
        let left = read(&wires, row, a_kind, a)?;
        let right = read(&wires, row, b_kind, b)?;
        let value = match op {
            0 => badd(left, right),
            1 => bmul(left, right),
            _ => return Err(NativeDispatchError::RowEncoding { row }),
        };
        let out_index = out as usize;
        let slot = wires
            .get_mut(out_index)
            .ok_or(NativeDispatchError::WireOutOfRange { row, wire: out })?;
        if slot.is_some() {
            return Err(NativeDispatchError::Rewrite { row, wire: out });
        }
        *slot = Some(value);
    }

    let mut response = Vec::with_capacity(n_wires * 4);
    for (wire, value) in wires.iter().enumerate() {
        let value = value.ok_or(NativeDispatchError::UnwrittenWire { wire })?;
        response.extend_from_slice(&(value as u32).to_le_bytes());
    }
    Ok(response)
}

/// Execute the Lean-emitted Stage-0 work (EVM u256 add, work `9103`): 833 u32 LE variable
/// words in, the 4,131-word candidate wire vector out, by evaluating the generated
/// `WORK_2_ROWS` table in order.  No descriptor is parsed and no zero-check is evaluated;
/// Lean decodes the reply and `descriptorHoldsCheck` judges it.
pub fn evm_stage0_add_aux_bytes(request: &[u8]) -> Result<Vec<u8>, NativeDispatchError> {
    evaluate_descriptor_rows(
        WORK_2_ROWS,
        WORK_2_DESCRIPTOR_N_VARS,
        WORK_2_DESCRIPTOR_N_WIRES,
        WORK_2_FIELD_MODULUS,
        request,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantic_artifact_arithmetic as arithmetic;
    use crate::semantic_artifact_v1::{
        dispatch_native, NativeErrorKind, NativeWorkRequestDto, WORK_0_CARRIER_PROFILE_ID_DECIMAL,
        WORK_0_ID_DECIMAL, WORK_0_REQUEST_CODEC_ID_DECIMAL, WORK_0_RESPONSE_CODEC_ID_DECIMAL,
    };

    fn encoded_request(left: &[Tower256], right: &[Tower256]) -> Vec<u8> {
        assert_eq!(left.len(), right.len());
        let mut bytes = Vec::with_capacity(
            WORK_0_REQUEST_COUNT_WIDTH
                + WORK_0_REQUEST_VECTOR_ARITY * WORK_0_REQUEST_COORDINATE_WIDTH * left.len(),
        );
        bytes.extend_from_slice(&(left.len() as u32).to_le_bytes());
        for value in left {
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        for value in right {
            bytes.extend_from_slice(&value.to_le_bytes());
        }
        bytes
    }

    #[test]
    fn generated_dispatch_reaches_only_the_pinned_dot_product() {
        let left = [
            Tower256::from_limbs([3, 5, 7, 11]),
            Tower256::from_limbs([13, 17, 19, 23]),
        ];
        let right = [
            Tower256::from_limbs([29, 31, 37, 41]),
            Tower256::from_limbs([43, 47, 53, 59]),
        ];
        let request = NativeWorkRequestDto::from_ids(
            WORK_0_ID_DECIMAL,
            WORK_0_CARRIER_PROFILE_ID_DECIMAL,
            WORK_0_REQUEST_CODEC_ID_DECIMAL,
            WORK_0_RESPONSE_CODEC_ID_DECIMAL,
            encoded_request(&left, &right).into_boxed_slice(),
        )
        .unwrap();
        let reply = dispatch_native(request).unwrap();
        let expected = dot_product(&left, &right).unwrap().to_le_bytes();
        assert_eq!(reply.response_bytes(), expected);
    }

    #[test]
    fn generated_constructor_cannot_change_profile_or_codec_pins() {
        let request = NativeWorkRequestDto::tower256_dot_product(
            encoded_request(&[], &[]).into_boxed_slice(),
        );
        assert_eq!(request.work_id_decimal(), WORK_0_ID_DECIMAL);
        assert_eq!(
            request.carrier_profile_id_decimal(),
            WORK_0_CARRIER_PROFILE_ID_DECIMAL
        );
        assert_eq!(
            request.request_codec_id_decimal(),
            WORK_0_REQUEST_CODEC_ID_DECIMAL
        );
        assert_eq!(
            request.response_codec_id_decimal(),
            WORK_0_RESPONSE_CODEC_ID_DECIMAL
        );
    }

    #[test]
    fn noncanonical_pins_and_malformed_bytes_are_errors_not_verdicts() {
        let wrong_profile = NativeWorkRequestDto::from_ids(
            WORK_0_ID_DECIMAL,
            "handwritten-profile",
            WORK_0_REQUEST_CODEC_ID_DECIMAL,
            WORK_0_RESPONSE_CODEC_ID_DECIMAL,
            Vec::new().into_boxed_slice(),
        )
        .unwrap_err();
        assert_eq!(wrong_profile.kind, NativeErrorKind::MalformedRequest);

        let malformed =
            NativeWorkRequestDto::tower256_dot_product(vec![1, 0, 0, 0].into_boxed_slice());
        let failure = dispatch_native(malformed).unwrap_err();
        assert_eq!(failure.kind, NativeErrorKind::ExecutionFailure);
    }

    #[test]
    fn generated_arithmetic_dispatch_returns_only_the_lean_emitted_candidate() {
        let request = arithmetic::NativeWorkRequestDto::from_ids(
            arithmetic::WORK_1_ID_DECIMAL,
            arithmetic::WORK_1_CARRIER_PROFILE_ID_DECIMAL,
            arithmetic::WORK_1_REQUEST_CODEC_ID_DECIMAL,
            arithmetic::WORK_1_RESPONSE_CODEC_ID_DECIMAL,
            Vec::new().into_boxed_slice(),
        )
        .unwrap();
        let reply = arithmetic::dispatch_native(request).unwrap();
        assert_eq!(
            reply.response_bytes(),
            arithmetic::WORK_1_FIXED_CANDIDATE_RESPONSE
        );
    }

    #[test]
    fn arithmetic_nonempty_request_is_a_transport_error() {
        let malformed = arithmetic::NativeWorkRequestDto::baby_bear_add1_zero_witness(
            vec![0].into_boxed_slice(),
        );
        let failure = arithmetic::dispatch_native(malformed).unwrap_err();
        assert_eq!(failure.kind, arithmetic::NativeErrorKind::ExecutionFailure);
    }
}
