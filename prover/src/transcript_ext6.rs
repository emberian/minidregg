//! Capability-gated transcript records for atomic BabyBear⁶ challenges.
//!
//! This module deliberately cannot manufacture an extension challenge by
//! calling a scalar squeeze six times.  Its backend must expose one *joint*
//! six-coordinate draw and advertise at least six joint entropy coordinates.
//! Construction also requires enough capacity for the repository's 248-bit ROM
//! range.  Those are explicit backend obligations, not claims about the current
//! width-two demo transcript, which cannot implement this contract honestly.
//!
//! Every instance starts by absorbing a versioned field-suite record that pins
//! BabyBear, `u⁶ = 31`, and little-endian coefficient order.  Records are
//! length-delimited and domain-separated before they reach the backend.

use core::fmt;

use crate::binary_transcript::{BinaryShake256Transcript, TranscriptSuite};
use crate::descriptor::Fp;
use crate::field4::P;
use crate::field6::Ext6;
use crate::wide::Digest;

/// Minimum joint output support needed for a uniform BabyBear⁶ coordinate.
pub const EXT6_JOINT_COORDINATES: usize = 6;

/// Capacity used by the candidate ROM collision budget.
pub const EXT6_MIN_CAPACITY_BITS: usize = 248;

const RECORD_TAG: Fp = 0x5852_4543; // "XREC"
const FIELD_SUITE_DOMAIN: Fp = 0x5846_4944; // "XFID"
const CHALLENGE_REQUEST_DOMAIN: Fp = 0x5843_4851; // "XCHQ"

/// Exact transcript identity for the extension field.
///
/// BabyBear's modulus is encoded as its two base-2¹⁶ digits because the
/// integer modulus itself is zero as a BabyBear element.
pub const EXT6_FIELD_SUITE: [Fp; 9] = [
    1,           // suite version
    0x4242_5231, // "BBR1"
    1,           // p mod 2^16
    30_720,      // p / 2^16 (p = 0x78000001)
    6,           // extension degree
    0x4249_4e4f, // "BINO": binomial modulus
    31,          // u^6 - 31
    0x4c45_4330, // "LEC0": c0, ..., c5
    EXT6_JOINT_COORDINATES as Fp,
];

/// A backend that realizes one atomic, joint six-coordinate oracle response.
///
/// `JOINT_CHALLENGE_COORDINATES` is the number of independent BabyBear
/// coordinates the backend's *single draw* can support, not the number of
/// scalar values its API happens to return. `CAPACITY_BITS` is the collision
/// capacity of the deployed sponge/RO realization.  A deterministic test double
/// can exercise schedule conformance, but does not thereby prove these security
/// properties for a production backend.
pub trait WideExt6Backend {
    const JOINT_CHALLENGE_COORDINATES: usize;
    const CAPACITY_BITS: usize;

    /// Absorb canonical BabyBear elements into the backend transcript.
    fn absorb(&mut self, canonical_fields: &[Fp]) -> Result<(), String>;

    /// Produce all six canonical coefficient lanes in one joint oracle draw.
    fn squeeze_joint_ext6(&mut self) -> Result<[Fp; 6], String>;
}

/// Byte-native cSHAKE256 realization of the atomic Ext6 backend contract.
///
/// This makes the clear-reference Ext6 phase executable without pretending
/// that six calls to the legacy width-two field sponge form a joint draw.  It
/// is also the natural backend for a byte/binary outer protocol.  A recursive
/// BabyBear verifier can later substitute the separately specified wide
/// Poseidon2 backend without changing [`Ext6Transcript`]'s record schedule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryShakeExt6Backend {
    transcript: BinaryShake256Transcript,
}

impl BinaryShakeExt6Backend {
    pub fn new(protocol_label: &[u8]) -> Self {
        Self {
            transcript: BinaryShake256Transcript::new(protocol_label),
        }
    }

    pub fn into_inner(self) -> BinaryShake256Transcript {
        self.transcript
    }
}

impl WideExt6Backend for BinaryShakeExt6Backend {
    const JOINT_CHALLENGE_COORDINATES: usize = EXT6_JOINT_COORDINATES;
    // cSHAKE256/SHAKE256 has a 512-bit sponge capacity.
    const CAPACITY_BITS: usize = 512;

    fn absorb(&mut self, canonical_fields: &[Fp]) -> Result<(), String> {
        let mut bytes = Vec::with_capacity(8 + 4 * canonical_fields.len());
        bytes.extend_from_slice(&(canonical_fields.len() as u64).to_le_bytes());
        for &value in canonical_fields {
            if value >= P {
                return Err(format!("non-canonical BabyBear record element {value}"));
            }
            bytes.extend_from_slice(&(value as u32).to_le_bytes());
        }
        self.transcript.observe_bytes(b"ext6/base-record", &bytes);
        Ok(())
    }

    fn squeeze_joint_ext6(&mut self) -> Result<[Fp; 6], String> {
        Ok(*self.transcript.sample_ext6(b"ext6/joint-challenge").limbs())
    }
}

impl<T: WideExt6Backend + ?Sized> WideExt6Backend for &mut T {
    const JOINT_CHALLENGE_COORDINATES: usize = T::JOINT_CHALLENGE_COORDINATES;
    const CAPACITY_BITS: usize = T::CAPACITY_BITS;

    fn absorb(&mut self, canonical_fields: &[Fp]) -> Result<(), String> {
        (**self).absorb(canonical_fields)
    }

    fn squeeze_joint_ext6(&mut self) -> Result<[Fp; 6], String> {
        (**self).squeeze_joint_ext6()
    }
}

/// Fail-closed transcript construction or backend failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ext6TranscriptError {
    InsufficientJointCoordinates {
        required: usize,
        actual: usize,
    },
    InsufficientCapacity {
        required_bits: usize,
        actual_bits: usize,
    },
    NonCanonicalRecord {
        index: usize,
        value: Fp,
    },
    NonCanonicalDomain(Fp),
    RecordTooLong(usize),
    DrawCounterExhausted,
    NonCanonicalChallenge {
        lane: usize,
        value: Fp,
    },
    Backend(String),
}

impl fmt::Display for Ext6TranscriptError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InsufficientJointCoordinates { required, actual } => write!(
                f,
                "Ext6 transcript needs {required} joint coordinates, backend advertises {actual}"
            ),
            Self::InsufficientCapacity {
                required_bits,
                actual_bits,
            } => write!(
                f,
                "Ext6 transcript needs {required_bits} capacity bits, backend advertises {actual_bits}"
            ),
            Self::NonCanonicalRecord { index, value } => {
                write!(f, "transcript record element {index} is non-canonical: {value}")
            }
            Self::NonCanonicalDomain(value) => {
                write!(f, "transcript record domain is non-canonical: {value}")
            }
            Self::RecordTooLong(length) => {
                write!(f, "transcript record length {length} does not fit BabyBear")
            }
            Self::DrawCounterExhausted => write!(f, "Ext6 challenge counter exhausted"),
            Self::NonCanonicalChallenge { lane, value } => {
                write!(f, "Ext6 challenge lane {lane} is non-canonical: {value}")
            }
            Self::Backend(message) => write!(f, "wide transcript backend: {message}"),
        }
    }
}

impl std::error::Error for Ext6TranscriptError {}

/// A transcript that exposes no scalar squeeze operation.
pub struct Ext6Transcript<B> {
    backend: B,
    draw_counter: u64,
}

impl<B: WideExt6Backend> Ext6Transcript<B> {
    /// Validate the backend's security profile and bind the exact field suite.
    pub fn new(backend: B) -> Result<Self, Ext6TranscriptError> {
        if B::JOINT_CHALLENGE_COORDINATES < EXT6_JOINT_COORDINATES {
            return Err(Ext6TranscriptError::InsufficientJointCoordinates {
                required: EXT6_JOINT_COORDINATES,
                actual: B::JOINT_CHALLENGE_COORDINATES,
            });
        }
        if B::CAPACITY_BITS < EXT6_MIN_CAPACITY_BITS {
            return Err(Ext6TranscriptError::InsufficientCapacity {
                required_bits: EXT6_MIN_CAPACITY_BITS,
                actual_bits: B::CAPACITY_BITS,
            });
        }
        let mut transcript = Self {
            backend,
            draw_counter: 0,
        };
        transcript.absorb_record(FIELD_SUITE_DOMAIN, &EXT6_FIELD_SUITE)?;
        Ok(transcript)
    }

    /// Absorb one length-delimited, domain-separated base-field record.
    pub fn absorb_record(&mut self, domain: Fp, values: &[Fp]) -> Result<(), Ext6TranscriptError> {
        if domain >= P {
            return Err(Ext6TranscriptError::NonCanonicalDomain(domain));
        }
        if values.len() as u128 >= P as u128 {
            return Err(Ext6TranscriptError::RecordTooLong(values.len()));
        }
        if let Some((index, &value)) = values.iter().enumerate().find(|(_, value)| **value >= P) {
            return Err(Ext6TranscriptError::NonCanonicalRecord { index, value });
        }
        let mut encoded = Vec::with_capacity(values.len() + 3);
        encoded.extend_from_slice(&[RECORD_TAG, domain, values.len() as Fp]);
        encoded.extend_from_slice(values);
        self.backend
            .absorb(&encoded)
            .map_err(Ext6TranscriptError::Backend)
    }

    /// Absorb extension elements in canonical c0..c5 order.
    pub fn absorb_ext6_record(
        &mut self,
        domain: Fp,
        values: &[Ext6],
    ) -> Result<(), Ext6TranscriptError> {
        let limb_count = values
            .len()
            .checked_mul(EXT6_JOINT_COORDINATES)
            .ok_or(Ext6TranscriptError::RecordTooLong(usize::MAX))?;
        if limb_count as u128 >= P as u128 {
            return Err(Ext6TranscriptError::RecordTooLong(limb_count));
        }
        let mut limbs = Vec::with_capacity(limb_count);
        for value in values {
            limbs.extend_from_slice(value.limbs());
        }
        self.absorb_record(domain, &limbs)
    }

    /// Absorb a canonical nine-limb commitment without narrowing it.
    pub fn absorb_digest(
        &mut self,
        domain: Fp,
        digest: &Digest,
    ) -> Result<(), Ext6TranscriptError> {
        if let Some((index, &value)) = digest
            .limbs
            .iter()
            .enumerate()
            .find(|(_, value)| **value >= P)
        {
            return Err(Ext6TranscriptError::NonCanonicalRecord { index, value });
        }
        self.absorb_record(domain, &digest.limbs)
    }

    /// Draw one jointly sampled BabyBear⁶ element.
    ///
    /// The request record binds the semantic domain and draw counter before the
    /// backend's atomic six-coordinate call. There is intentionally no method
    /// here that exposes one scalar coordinate at a time.
    pub fn squeeze_ext6(&mut self, domain: Fp) -> Result<Ext6, Ext6TranscriptError> {
        let counter = self.draw_counter;
        if counter >= P {
            return Err(Ext6TranscriptError::DrawCounterExhausted);
        }
        self.absorb_record(CHALLENGE_REQUEST_DOMAIN, &[domain, counter])?;
        let limbs = self
            .backend
            .squeeze_joint_ext6()
            .map_err(Ext6TranscriptError::Backend)?;
        self.draw_counter += 1;
        Ext6::try_from_limbs(limbs).map_err(|error| Ext6TranscriptError::NonCanonicalChallenge {
            lane: error.lane,
            value: error.value,
        })
    }
}
