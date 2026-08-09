//! Fallible opaque byte adapters selected by Lean-generated dispatch.
//!
//! This module contains no work/profile identifiers, transcript state,
//! proposition, verifier verdict, or acceptance token.  The generated module
//! chooses the only callable operation and pins its request/response codecs.
//! This adapter merely parses that codec, invokes an unverified computational
//! kernel, and returns bytes or a local error.  Lean remains the sole decoder,
//! checker, and acceptor of the returned bytes.

use core::fmt;

use crate::binary_tower_256::{Tower256, Tower256Error};
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

#[cfg(test)]
mod tests {
    use super::*;
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
}
