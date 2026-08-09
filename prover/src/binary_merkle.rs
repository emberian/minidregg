//! Typed Merkle commitments for byte-native binary proof suites.
//!
//! This module is intentionally oblivious to BabyBear and `wide::Digest`.
//! Leaves are arbitrary canonical byte strings, roots and siblings retain the
//! hash suite's root type, and every opening is checked against the exact
//! power-of-two tree height.  It is the commitment substrate for the additive
//! GF(2) prover.

use core::fmt;

use crate::binary_hash::{BinaryHashDomain, HashSuite};

/// One exact-height authentication path, ordered from leaf to root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryMerklePath<R> {
    pub siblings: Vec<R>,
}

/// A complete tree retained by a prover while Fiat--Shamir queries are drawn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BinaryMerkleTree<R> {
    domain: BinaryHashDomain,
    levels: Vec<Vec<R>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BinaryMerkleError {
    EmptyTree,
    NonPowerOfTwo { leaves: usize },
    IndexOutOfRange { index: usize, leaves: usize },
    PathHeight { expected: usize, actual: usize },
}

impl fmt::Display for BinaryMerkleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyTree => write!(f, "a binary Merkle tree needs at least one leaf"),
            Self::NonPowerOfTwo { leaves } => {
                write!(f, "binary Merkle leaf count {leaves} is not a power of two")
            }
            Self::IndexOutOfRange { index, leaves } => {
                write!(f, "binary Merkle index {index} is outside {leaves} leaves")
            }
            Self::PathHeight { expected, actual } => write!(
                f,
                "binary Merkle path height {actual} does not match expected {expected}"
            ),
        }
    }
}

impl std::error::Error for BinaryMerkleError {}

impl<R: Copy + Eq + fmt::Debug> BinaryMerkleTree<R> {
    /// Commit canonical leaf payloads in their public natural order.
    pub fn build<S: HashSuite<Root = R>>(
        suite: &S,
        domain: BinaryHashDomain,
        payloads: &[impl AsRef<[u8]>],
    ) -> Result<Self, BinaryMerkleError> {
        if payloads.is_empty() {
            return Err(BinaryMerkleError::EmptyTree);
        }
        if !payloads.len().is_power_of_two() {
            return Err(BinaryMerkleError::NonPowerOfTwo {
                leaves: payloads.len(),
            });
        }

        let leaves = payloads
            .iter()
            .enumerate()
            .map(|(index, payload)| suite.hash_leaf(domain, index as u64, payload.as_ref()))
            .collect::<Vec<_>>();
        let mut levels = vec![leaves];
        let mut node_level = 0u32;
        while levels.last().expect("leaf level exists").len() > 1 {
            let next = levels
                .last()
                .expect("previous level exists")
                .chunks_exact(2)
                .map(|pair| suite.hash_node(domain, node_level, &pair[0], &pair[1]))
                .collect();
            levels.push(next);
            node_level += 1;
        }
        Ok(Self { domain, levels })
    }

    pub fn domain(&self) -> BinaryHashDomain {
        self.domain
    }

    pub fn leaf_count(&self) -> usize {
        self.levels[0].len()
    }

    pub fn height(&self) -> usize {
        self.levels.len() - 1
    }

    pub fn root(&self) -> R {
        self.levels
            .last()
            .and_then(|level| level.first())
            .copied()
            .expect("a constructed binary Merkle tree is nonempty")
    }

    pub fn open(&self, index: usize) -> Result<BinaryMerklePath<R>, BinaryMerkleError> {
        if index >= self.leaf_count() {
            return Err(BinaryMerkleError::IndexOutOfRange {
                index,
                leaves: self.leaf_count(),
            });
        }
        let mut cursor = index;
        let mut siblings = Vec::with_capacity(self.height());
        for level in self.levels.iter().take(self.height()) {
            siblings.push(level[cursor ^ 1]);
            cursor >>= 1;
        }
        Ok(BinaryMerklePath { siblings })
    }
}

/// Verify one canonical payload at an exact index and tree size.
///
/// Shape errors are distinguished from an authentication mismatch so callers
/// can reject malformed proof encodings before doing any hashing.
pub fn verify_binary_opening<S: HashSuite>(
    suite: &S,
    domain: BinaryHashDomain,
    leaf_count: usize,
    index: usize,
    payload: &[u8],
    path: &BinaryMerklePath<S::Root>,
    expected_root: &S::Root,
) -> Result<bool, BinaryMerkleError> {
    if leaf_count == 0 {
        return Err(BinaryMerkleError::EmptyTree);
    }
    if !leaf_count.is_power_of_two() {
        return Err(BinaryMerkleError::NonPowerOfTwo { leaves: leaf_count });
    }
    if index >= leaf_count {
        return Err(BinaryMerkleError::IndexOutOfRange {
            index,
            leaves: leaf_count,
        });
    }
    let expected_height = leaf_count.trailing_zeros() as usize;
    if path.siblings.len() != expected_height {
        return Err(BinaryMerkleError::PathHeight {
            expected: expected_height,
            actual: path.siblings.len(),
        });
    }

    let mut cursor = index;
    let mut node = suite.hash_leaf(domain, index as u64, payload);
    for (level, sibling) in path.siblings.iter().enumerate() {
        node = if cursor & 1 == 0 {
            suite.hash_node(domain, level as u32, &node, sibling)
        } else {
            suite.hash_node(domain, level as u32, sibling, &node)
        };
        cursor >>= 1;
    }
    Ok(&node == expected_root)
}
