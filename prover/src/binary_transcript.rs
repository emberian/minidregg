//! Prefix-framed Fiat--Shamir transcript for the binary additive prover.
//!
//! Each challenge hashes the complete observed prefix plus a typed request and
//! a monotone counter.  cSHAKE256's XOF supplies the six independently sampled
//! BabyBear coordinates needed by `Ext6`; no repeated squeeze from a narrow
//! field state is involved.  Wide binary challenges use one separately framed
//! request and one atomic 32-byte XOF read into `GF(2^256)`.

use sha3::digest::XofReader;

use crate::{
    binary_hash::{
        append_labeled_frame, cshake256_reader, BinaryRoot, TRANSCRIPT_CUSTOMIZATION,
        TRANSCRIPT_PREFIX,
    },
    binary_tower_256::Tower256,
    field4::P,
    field6::Ext6,
};

const PROTOCOL_FRAME: u8 = 1;
const BYTES_FRAME: u8 = 2;
const ROOT_FRAME: u8 = 3;
const U64_FRAME: u8 = 4;
const CHALLENGE_FRAME: u8 = 5;
const GF2_256_CHALLENGE_FRAME: u8 = 6;

/// Common transcript interface for versioned proof suites.
pub trait TranscriptSuite {
    type Root;

    const SUITE_ID: &'static [u8];

    fn new(protocol_label: &[u8]) -> Self;
    fn observe_bytes(&mut self, label: &[u8], bytes: &[u8]);
    fn observe_root(&mut self, label: &[u8], root: &Self::Root);
    fn observe_u64(&mut self, label: &[u8], value: u64);
    fn sample_gf2_64(&mut self, label: &[u8]) -> u64;
    fn sample_gf2_256(&mut self, label: &[u8]) -> Tower256;
    fn sample_ext6(&mut self, label: &[u8]) -> Ext6;
}

/// Transcript state for [`crate::binary_hash::BinaryShake256V1`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryShake256Transcript {
    prefix: Vec<u8>,
    challenge_counter: u64,
}

impl BinaryShake256Transcript {
    pub const SUITE_ID: &'static [u8] = b"BinaryShake256V1";

    fn challenge_reader(&mut self, label: &[u8]) -> impl XofReader {
        self.typed_challenge_reader(CHALLENGE_FRAME, label)
    }

    fn typed_challenge_reader(&mut self, request_frame: u8, label: &[u8]) -> impl XofReader {
        let counter = self.challenge_counter;
        self.challenge_counter = self
            .challenge_counter
            .checked_add(1)
            .expect("Fiat-Shamir challenge counter exhausted");

        let mut request = self.prefix.clone();
        append_labeled_frame(&mut request, request_frame, label, &counter.to_le_bytes());
        cshake256_reader(TRANSCRIPT_CUSTOMIZATION, &request)
    }
}

impl TranscriptSuite for BinaryShake256Transcript {
    type Root = BinaryRoot;

    const SUITE_ID: &'static [u8] = BinaryShake256Transcript::SUITE_ID;

    fn new(protocol_label: &[u8]) -> Self {
        let mut prefix = TRANSCRIPT_PREFIX.to_vec();
        append_labeled_frame(&mut prefix, PROTOCOL_FRAME, Self::SUITE_ID, protocol_label);
        Self {
            prefix,
            challenge_counter: 0,
        }
    }

    fn observe_bytes(&mut self, label: &[u8], bytes: &[u8]) {
        append_labeled_frame(&mut self.prefix, BYTES_FRAME, label, bytes);
    }

    fn observe_root(&mut self, label: &[u8], root: &BinaryRoot) {
        append_labeled_frame(&mut self.prefix, ROOT_FRAME, label, root.as_bytes());
    }

    fn observe_u64(&mut self, label: &[u8], value: u64) {
        append_labeled_frame(&mut self.prefix, U64_FRAME, label, &value.to_le_bytes());
    }

    fn sample_gf2_64(&mut self, label: &[u8]) -> u64 {
        let mut reader = self.challenge_reader(label);
        let mut bytes = [0u8; 8];
        reader.read(&mut bytes);
        u64::from_le_bytes(bytes)
    }

    fn sample_gf2_256(&mut self, label: &[u8]) -> Tower256 {
        // The type-specific frame prevents cross-type prefix reuse, while one
        // reader and one read make this a single 256-bit transcript draw.
        let mut reader = self.typed_challenge_reader(GF2_256_CHALLENGE_FRAME, label);
        let mut bytes = [0u8; 32];
        reader.read(&mut bytes);
        Tower256::from_le_bytes(bytes)
    }

    fn sample_ext6(&mut self, label: &[u8]) -> Ext6 {
        let mut reader = self.challenge_reader(label);
        let mut limbs = [0u64; 6];
        for limb in &mut limbs {
            loop {
                let mut bytes = [0u8; 4];
                reader.read(&mut bytes);
                let candidate = u32::from_le_bytes(bytes) & 0x7fff_ffff;
                if (candidate as u64) < P {
                    *limb = candidate as u64;
                    break;
                }
            }
        }
        Ext6::try_from_limbs(limbs).expect("rejection sampling returns canonical Ext6 limbs")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary_hash::{BinaryHashDomain, BinaryShake256V1, HashSuite};

    #[test]
    fn binary_shake256_v1_smoke_vector() {
        let suite = BinaryShake256V1;
        let left = suite.hash_leaf(BinaryHashDomain::AdditiveFri, 0, b"left");
        let right = suite.hash_leaf(BinaryHashDomain::AdditiveFri, 1, b"right");
        let root = suite.hash_node(BinaryHashDomain::AdditiveFri, 0, &left, &right);

        let mut transcript = BinaryShake256Transcript::new(b"additive-fri-smoke");
        transcript.observe_u64(b"domain-size", 16);
        transcript.observe_root(b"round-root", &root);
        let gf2 = transcript.sample_gf2_64(b"fold-challenge");
        let ext6 = transcript.sample_ext6(b"assurance-challenge");

        assert_eq!(
            root.as_bytes(),
            &[
                191, 193, 186, 112, 160, 253, 112, 207, 97, 162, 213, 34, 71, 45, 252, 75, 78, 207,
                202, 49, 115, 227, 251, 5, 217, 111, 191, 142, 56, 129, 105, 223, 43, 248, 14, 231,
                109, 16, 8, 225, 23, 78, 201, 43, 168, 91, 27, 12,
            ]
        );
        assert_eq!(gf2, 1_768_011_751_979_524_905);
        assert_eq!(
            ext6.limbs(),
            &[
                384_250_378,
                571_709_401,
                1_824_692_999,
                877_489_773,
                1_812_432_266,
                1_760_341_227,
            ]
        );
    }
}
