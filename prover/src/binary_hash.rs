//! Versioned, byte-native commitment hashing for the binary additive prover.
//!
//! This suite deliberately does not reuse the BabyBear `wide::Digest`: a root
//! is 48 bytes from cSHAKE256, and every input is framed before hashing.  The
//! fixed width gives a 384-bit output while the distinct customization strings
//! keep commitment and transcript uses of Keccak in separate domains.

use core::fmt;

use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    CShake256, CShake256Core, CShake256Reader,
};

/// Wire width of a binary-suite commitment root.
pub const BINARY_ROOT_BYTES: usize = 48;

pub(crate) const COMMITMENT_CUSTOMIZATION: &[u8] = b"minidregg/BinaryShake256V1/commitment";
pub(crate) const TRANSCRIPT_CUSTOMIZATION: &[u8] = b"minidregg/BinaryShake256V1/transcript";

const COMMITMENT_PREFIX: &[u8] = b"MDRG-BINARY-COMMIT-V1";
pub(crate) const TRANSCRIPT_PREFIX: &[u8] = b"MDRG-BINARY-TRANSCRIPT-V1";

const LEAF_FRAME: u8 = 1;
const PAYLOAD_FRAME: u8 = 2;
const NODE_FRAME: u8 = 3;
const LEFT_ROOT_FRAME: u8 = 4;
const RIGHT_ROOT_FRAME: u8 = 5;

/// Semantic commitment domains.  The discriminants are wire-format values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum BinaryHashDomain {
    AdditiveFri = 1,
    Trace = 2,
    Accumulator = 3,
}

impl BinaryHashDomain {
    const fn wire_tag(self) -> u8 {
        self as u8
    }
}

/// A typed cSHAKE256 commitment root.  Every 48-byte string is canonical.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BinaryRoot([u8; BINARY_ROOT_BYTES]);

impl BinaryRoot {
    pub const fn from_bytes(bytes: [u8; BINARY_ROOT_BYTES]) -> Self {
        Self(bytes)
    }

    pub fn try_from_slice(bytes: &[u8]) -> Result<Self, BinaryRootLengthError> {
        let bytes: [u8; BINARY_ROOT_BYTES] =
            bytes.try_into().map_err(|_| BinaryRootLengthError {
                actual: bytes.len(),
            })?;
        Ok(Self(bytes))
    }

    pub const fn as_bytes(&self) -> &[u8; BINARY_ROOT_BYTES] {
        &self.0
    }

    pub const fn into_bytes(self) -> [u8; BINARY_ROOT_BYTES] {
        self.0
    }
}

impl fmt::Debug for BinaryRoot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("BinaryRoot(")?;
        for byte in self.0 {
            write!(f, "{byte:02x}")?;
        }
        f.write_str(")")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BinaryRootLengthError {
    pub actual: usize,
}

impl fmt::Display for BinaryRootLengthError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "binary root has {} bytes, expected {BINARY_ROOT_BYTES}",
            self.actual
        )
    }
}

impl std::error::Error for BinaryRootLengthError {}

/// Commitment interface consumed by additive protocols.
pub trait HashSuite {
    type Root: Copy + Eq + fmt::Debug;

    const SUITE_ID: &'static [u8];

    fn hash_leaf(&self, domain: BinaryHashDomain, index: u64, payload: &[u8]) -> Self::Root;

    fn hash_node(
        &self,
        domain: BinaryHashDomain,
        level: u32,
        left: &Self::Root,
        right: &Self::Root,
    ) -> Self::Root;
}

/// The byte-native suite selected for the GF(2^64) additive prover.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct BinaryShake256V1;

impl BinaryShake256V1 {
    pub const SUITE_ID: &'static [u8] = b"BinaryShake256V1";

    fn finish_commitment(input: &[u8]) -> BinaryRoot {
        let mut reader = cshake256_reader(COMMITMENT_CUSTOMIZATION, input);
        let mut root = [0u8; BINARY_ROOT_BYTES];
        reader.read(&mut root);
        BinaryRoot(root)
    }
}

impl HashSuite for BinaryShake256V1 {
    type Root = BinaryRoot;

    const SUITE_ID: &'static [u8] = BinaryShake256V1::SUITE_ID;

    fn hash_leaf(&self, domain: BinaryHashDomain, index: u64, payload: &[u8]) -> BinaryRoot {
        let mut input = COMMITMENT_PREFIX.to_vec();
        append_labeled_frame(
            &mut input,
            LEAF_FRAME,
            &[domain.wire_tag()],
            &index.to_le_bytes(),
        );
        append_labeled_frame(&mut input, PAYLOAD_FRAME, b"payload", payload);
        Self::finish_commitment(&input)
    }

    fn hash_node(
        &self,
        domain: BinaryHashDomain,
        level: u32,
        left: &BinaryRoot,
        right: &BinaryRoot,
    ) -> BinaryRoot {
        let mut input = COMMITMENT_PREFIX.to_vec();
        append_labeled_frame(
            &mut input,
            NODE_FRAME,
            &[domain.wire_tag()],
            &level.to_le_bytes(),
        );
        append_labeled_frame(&mut input, LEFT_ROOT_FRAME, b"left", left.as_bytes());
        append_labeled_frame(&mut input, RIGHT_ROOT_FRAME, b"right", right.as_bytes());
        Self::finish_commitment(&input)
    }
}

/// Append one injective frame: type, label length, label, payload length,
/// payload.  Fixed-width little-endian lengths make concatenations unambiguous.
pub(crate) fn append_labeled_frame(
    out: &mut Vec<u8>,
    frame_type: u8,
    label: &[u8],
    payload: &[u8],
) {
    out.push(frame_type);
    out.extend_from_slice(&(label.len() as u64).to_le_bytes());
    out.extend_from_slice(label);
    out.extend_from_slice(&(payload.len() as u64).to_le_bytes());
    out.extend_from_slice(payload);
}

pub(crate) fn cshake256_reader(customization: &[u8], input: &[u8]) -> CShake256Reader {
    let core = CShake256Core::new(customization);
    let mut hasher = CShake256::from_core(core);
    hasher.update(input);
    hasher.finalize_xof()
}
