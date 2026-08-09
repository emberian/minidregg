//! Parameterized byte-hash and Merkle arithmetic.
//!
//! This module owns no hash suite, semantic domain, wire profile, or verifier
//! verdict.  Generated control supplies every customization string, prefix,
//! domain, frame tag, label, encoded index/level, and root width.  Merkle
//! routines return constructed data or a recomputed root; comparison with an
//! expected root belongs to the caller.

use core::fmt;

use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    CShake256, CShake256Core,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HashKernelError {
    LengthDoesNotFitU64 { length: usize },
    ZeroRootWidth,
    RootWidth { expected: usize, actual: usize },
    EmptyTree,
    NonPowerOfTwo { leaves: usize },
    IndexOutOfRange { index: usize, leaves: usize },
    PathHeight { expected: usize, actual: usize },
}

impl fmt::Display for HashKernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LengthDoesNotFitU64 { length } => {
                write!(f, "frame length {length} does not fit in u64")
            }
            Self::ZeroRootWidth => write!(f, "a hash root must contain at least one byte"),
            Self::RootWidth { expected, actual } => {
                write!(f, "hash root has {actual} bytes, expected {expected}")
            }
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

impl std::error::Error for HashKernelError {}

/// Append one injective frame: tag, label length, label, payload length,
/// payload.  The caller owns the tag and both byte strings.
pub fn append_labeled_frame(
    out: &mut Vec<u8>,
    frame_tag: u8,
    label: &[u8],
    payload: &[u8],
) -> Result<(), HashKernelError> {
    let label_len =
        u64::try_from(label.len()).map_err(|_| HashKernelError::LengthDoesNotFitU64 {
            length: label.len(),
        })?;
    let payload_len =
        u64::try_from(payload.len()).map_err(|_| HashKernelError::LengthDoesNotFitU64 {
            length: payload.len(),
        })?;
    out.push(frame_tag);
    out.extend_from_slice(&label_len.to_le_bytes());
    out.extend_from_slice(label);
    out.extend_from_slice(&payload_len.to_le_bytes());
    out.extend_from_slice(payload);
    Ok(())
}

/// Read exactly `output_len` bytes from cSHAKE256.
pub fn cshake256_xof(customization: &[u8], input: &[u8], output_len: usize) -> Vec<u8> {
    let core = CShake256Core::new(customization);
    let mut hasher = CShake256::from_core(core);
    hasher.update(input);
    let mut reader = hasher.finalize_xof();
    let mut output = vec![0u8; output_len];
    reader.read(&mut output);
    output
}

/// Hash one leaf using only caller-supplied framing material.
#[allow(clippy::too_many_arguments)]
pub fn cshake256_hash_leaf(
    customization: &[u8],
    prefix: &[u8],
    domain: &[u8],
    leaf_frame_tag: u8,
    payload_frame_tag: u8,
    payload_label: &[u8],
    encoded_index: &[u8],
    payload: &[u8],
    root_width: usize,
) -> Result<Vec<u8>, HashKernelError> {
    require_root_width(root_width)?;
    let mut input = prefix.to_vec();
    append_labeled_frame(&mut input, leaf_frame_tag, domain, encoded_index)?;
    append_labeled_frame(&mut input, payload_frame_tag, payload_label, payload)?;
    Ok(cshake256_xof(customization, &input, root_width))
}

/// Hash one internal node using only caller-supplied framing material.
#[allow(clippy::too_many_arguments)]
pub fn cshake256_hash_node(
    customization: &[u8],
    prefix: &[u8],
    domain: &[u8],
    node_frame_tag: u8,
    left_root_frame_tag: u8,
    right_root_frame_tag: u8,
    left_root_label: &[u8],
    right_root_label: &[u8],
    encoded_level: &[u8],
    left: &[u8],
    right: &[u8],
    root_width: usize,
) -> Result<Vec<u8>, HashKernelError> {
    require_root_width(root_width)?;
    require_exact_width(left, root_width)?;
    require_exact_width(right, root_width)?;
    let mut input = prefix.to_vec();
    append_labeled_frame(&mut input, node_frame_tag, domain, encoded_level)?;
    append_labeled_frame(&mut input, left_root_frame_tag, left_root_label, left)?;
    append_labeled_frame(&mut input, right_root_frame_tag, right_root_label, right)?;
    Ok(cshake256_xof(customization, &input, root_width))
}

/// One exact-height authentication path, ordered from leaf to root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerklePath {
    pub siblings: Vec<Vec<u8>>,
}

/// Complete prover-side tree data with no semantic domain attached.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MerkleTree {
    root_width: usize,
    levels: Vec<Vec<Vec<u8>>>,
}

impl MerkleTree {
    pub fn root_width(&self) -> usize {
        self.root_width
    }

    pub fn leaf_count(&self) -> usize {
        self.levels[0].len()
    }

    pub fn height(&self) -> usize {
        self.levels.len() - 1
    }

    pub fn root(&self) -> &[u8] {
        &self.levels[self.levels.len() - 1][0]
    }
}

/// Build a power-of-two binary Merkle tree from caller-owned leaf and node
/// hash functions.
pub fn build_merkle<L, N>(
    payloads: &[impl AsRef<[u8]>],
    root_width: usize,
    mut hash_leaf: L,
    mut hash_node: N,
) -> Result<MerkleTree, HashKernelError>
where
    L: FnMut(usize, &[u8]) -> Result<Vec<u8>, HashKernelError>,
    N: FnMut(u32, &[u8], &[u8]) -> Result<Vec<u8>, HashKernelError>,
{
    require_tree_shape(payloads.len(), root_width)?;
    let leaves = payloads
        .iter()
        .enumerate()
        .map(|(index, payload)| {
            let root = hash_leaf(index, payload.as_ref())?;
            require_exact_width(&root, root_width)?;
            Ok(root)
        })
        .collect::<Result<Vec<_>, HashKernelError>>()?;
    let mut levels = vec![leaves];
    let mut node_level = 0u32;
    while levels[levels.len() - 1].len() > 1 {
        let next = levels[levels.len() - 1]
            .chunks_exact(2)
            .map(|pair| {
                let root = hash_node(node_level, &pair[0], &pair[1])?;
                require_exact_width(&root, root_width)?;
                Ok(root)
            })
            .collect::<Result<Vec<_>, HashKernelError>>()?;
        levels.push(next);
        node_level += 1;
    }
    Ok(MerkleTree { root_width, levels })
}

/// Return the authentication path for an exact leaf index.
pub fn open_merkle(tree: &MerkleTree, index: usize) -> Result<MerklePath, HashKernelError> {
    if index >= tree.leaf_count() {
        return Err(HashKernelError::IndexOutOfRange {
            index,
            leaves: tree.leaf_count(),
        });
    }
    let mut cursor = index;
    let mut siblings = Vec::with_capacity(tree.height());
    for level in tree.levels.iter().take(tree.height()) {
        siblings.push(level[cursor ^ 1].clone());
        cursor >>= 1;
    }
    Ok(MerklePath { siblings })
}

/// Recompute one root without receiving or comparing against an expected root.
pub fn recompute_merkle_root<L, N>(
    leaf_count: usize,
    index: usize,
    payload: &[u8],
    path: &MerklePath,
    root_width: usize,
    mut hash_leaf: L,
    mut hash_node: N,
) -> Result<Vec<u8>, HashKernelError>
where
    L: FnMut(usize, &[u8]) -> Result<Vec<u8>, HashKernelError>,
    N: FnMut(u32, &[u8], &[u8]) -> Result<Vec<u8>, HashKernelError>,
{
    require_tree_shape(leaf_count, root_width)?;
    if index >= leaf_count {
        return Err(HashKernelError::IndexOutOfRange {
            index,
            leaves: leaf_count,
        });
    }
    let expected_height = leaf_count.trailing_zeros() as usize;
    if path.siblings.len() != expected_height {
        return Err(HashKernelError::PathHeight {
            expected: expected_height,
            actual: path.siblings.len(),
        });
    }
    let mut node = hash_leaf(index, payload)?;
    require_exact_width(&node, root_width)?;
    let mut cursor = index;
    for (level, sibling) in path.siblings.iter().enumerate() {
        require_exact_width(sibling, root_width)?;
        node = if cursor & 1 == 0 {
            hash_node(level as u32, &node, sibling)?
        } else {
            hash_node(level as u32, sibling, &node)?
        };
        require_exact_width(&node, root_width)?;
        cursor >>= 1;
    }
    Ok(node)
}

fn require_tree_shape(leaf_count: usize, root_width: usize) -> Result<(), HashKernelError> {
    require_root_width(root_width)?;
    if leaf_count == 0 {
        Err(HashKernelError::EmptyTree)
    } else if !leaf_count.is_power_of_two() {
        Err(HashKernelError::NonPowerOfTwo { leaves: leaf_count })
    } else {
        Ok(())
    }
}

fn require_root_width(root_width: usize) -> Result<(), HashKernelError> {
    if root_width == 0 {
        Err(HashKernelError::ZeroRootWidth)
    } else {
        Ok(())
    }
}

fn require_exact_width(root: &[u8], root_width: usize) -> Result<(), HashKernelError> {
    if root.len() == root_width {
        Ok(())
    } else {
        Err(HashKernelError::RootWidth {
            expected: root_width,
            actual: root.len(),
        })
    }
}
