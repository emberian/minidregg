//! `[PROVER-commit]` half 2 — the binary Merkle commitment over the trace,
//! compressed with the `poseidon` permutation.
//!
//! Substrate, said out loud: UNVERIFIED COMPUTE following the verified emit seam.
//! The SHAPE this realizes is `Loom/Commitment.lean`'s `OpeningScheme` —
//! `commit_trace` is `commit`, `open` is `openAt`, `verify_open` is `verifyOpen`,
//! and the round-trip test is `verifyOpen_commit` (completeness) EXERCISED on
//! vectors. What this file does NOT provide: `PositionBinding` (one root, one
//! value per position) is a THEOREM-SHAPED property that in deployment rests on
//! collision resistance of the instantiated hash — `[COMMIT-CR]`, a cryptographic
//! assumption about parameters this rung does not have (`[PROVER-poseidon-params]`).
//! A tampered-leaf test failing to verify is a spot check that the binding is
//! non-vacuous on the vector, not a binding proof. No Rust semantics exists;
//! nothing here is verification or refinement.
//!
//! Construction: leaves are the trace's field elements in wire order (the rung-2
//! trace is one wire vector; a columns-of-a-matrix layout arrives with the later
//! rungs).  Leaves, padding, and internal nodes use distinct domains and every
//! digest is nine canonical BabyBear limbs (`wide.rs`).  This removes the former
//! single-field root representation.  It does **not** establish 248-bit
//! collision resistance: the underlying permutation parameters remain the demo
//! `[PROVER-poseidon-params]` / `[COMMIT-CR]` residual.

use crate::descriptor::Fp;
use crate::poseidon::{PermSpec, BABY_BEAR_P};
use crate::wide::{hash_fields, hash_pair, Digest, DigestDomain};

/// The Merkle tree, all levels: `levels[0]` is the (padded) leaf-digest level,
/// each next level halves, `levels.last()` is `[root]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MerkleTree {
    /// Number of real (unpadded) leaves committed.
    pub n_leaves: usize,
    /// Digest levels, leaf level first, root level (length 1) last.
    pub levels: Vec<Vec<Digest>>,
}

impl MerkleTree {
    /// The root — the commitment.
    pub fn root(&self) -> Digest {
        self.levels.last().expect("tree has a root level")[0]
    }
}

/// A scalar trace leaf, separated from FRI leaves, padding, and internal nodes.
pub fn hash_trace_leaf(spec: &PermSpec, value: Fp, p: u64) -> Digest {
    hash_fields(spec, DigestDomain::TraceLeaf, &[value], p)
}

/// Build a binary Merkle tree from already domain-separated leaf digests.
///
/// The dedicated padding digest ensures a real zero leaf cannot equal padding
/// merely because both carry the same scalar payload.
pub fn commit_digests(spec: &PermSpec, leaves: &[Digest], p: u64) -> (Digest, MerkleTree) {
    assert!(!leaves.is_empty(), "cannot commit an empty leaf sequence");
    assert!(
        leaves.iter().all(Digest::is_canonical),
        "commitment leaves must be canonical"
    );
    let n_leaves = leaves.len();
    let padded = n_leaves.next_power_of_two();
    let padding = hash_fields(spec, DigestDomain::MerklePadding, &[], p);
    let mut level = leaves.to_vec();
    level.resize(padded, padding);
    let mut levels = vec![level];
    while levels.last().expect("leaf level exists").len() > 1 {
        let prev = levels.last().expect("previous level exists");
        let next: Vec<Digest> = prev
            .chunks_exact(2)
            .map(|pair| hash_pair(spec, pair[0], pair[1], p))
            .collect();
        levels.push(next);
    }
    let tree = MerkleTree { n_leaves, levels };
    (tree.root(), tree)
}

/// **Commit** — `OpeningScheme.commit`, realized: hash every trace element to a
/// leaf digest, pad to a power of two with the dedicated padding-domain digest,
/// then compress pairwise to the root.
/// Deterministic (a pure fold; the determinism test re-commits and compares).
/// Panics on an empty trace — there is nothing to commit.
pub fn commit_trace(spec: &PermSpec, trace: &[Fp], p: u64) -> (Digest, MerkleTree) {
    assert!(!trace.is_empty(), "cannot commit an empty trace");
    assert!(
        trace.iter().all(|&value| value < p),
        "trace leaves must be canonical"
    );
    let leaves: Vec<Digest> = trace
        .iter()
        .map(|&value| hash_trace_leaf(spec, value, p))
        .collect();
    commit_digests(spec, &leaves, p)
}

/// **Open** — `OpeningScheme.openAt`, realized: the authentication path for leaf
/// `index`, as the sibling digest at every level, leaf level first. The path
/// length is the tree height; `index`'s bits (LSB first) say which side each
/// sibling is on. Panics if `index` is out of range.
pub fn open(tree: &MerkleTree, index: usize) -> Vec<Digest> {
    assert!(
        index < tree.n_leaves,
        "open: leaf index {index} out of range ({})",
        tree.n_leaves
    );
    let mut path = Vec::with_capacity(tree.levels.len() - 1);
    let mut i = index;
    for level in &tree.levels[..tree.levels.len() - 1] {
        path.push(level[i ^ 1]);
        i >>= 1;
    }
    path
}

/// **Verify** — `OpeningScheme.verifyOpen`, realized: recompute the leaf digest
/// from the claimed VALUE, fold the path up (the index's bits choosing sides),
/// compare with the root. Also rejects an index that does not fit the path's
/// height. Completeness on honest openings (`verifyOpen_commit`) is exercised by
/// the round-trip test; binding rests on `[COMMIT-CR]`, not on this function.
pub fn verify_digest_open(
    root: Digest,
    index: usize,
    leaf_digest: Digest,
    path: &[Digest],
    spec: &PermSpec,
    p: u64,
) -> bool {
    if p != BABY_BEAR_P
        || spec.width < 2
        || spec.validate(p).is_err()
        || path.len() >= usize::BITS as usize
        || index >> path.len() != 0
    {
        return false;
    }
    // Proof-controlled malformed limbs must reject before reaching `perm`,
    // whose executor intentionally asserts canonical field inputs.
    if !root.is_canonical()
        || !leaf_digest.is_canonical()
        || path.iter().any(|sibling| !sibling.is_canonical())
    {
        return false;
    }
    let mut digest = leaf_digest;
    let mut i = index;
    for &sib in path {
        digest = if i & 1 == 0 {
            hash_pair(spec, digest, sib, p)
        } else {
            hash_pair(spec, sib, digest, p)
        };
        i >>= 1;
    }
    digest == root
}

/// Verify an opening of one scalar trace leaf.
pub fn verify_open(
    root: Digest,
    index: usize,
    leaf: Fp,
    path: &[Digest],
    spec: &PermSpec,
    p: u64,
) -> bool {
    if leaf >= p {
        return false;
    }
    verify_digest_open(root, index, hash_trace_leaf(spec, leaf, p), path, spec, p)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poseidon::{demo_spec, BABY_BEAR_P};

    fn sample_trace() -> Vec<Fp> {
        // 6 leaves — deliberately not a power of two, exercising the padding.
        vec![13, 1, 0, 1, 1, 123_456_789]
    }

    #[test]
    fn root_is_deterministic() {
        let spec = demo_spec();
        let t = sample_trace();
        let (r1, tree1) = commit_trace(&spec, &t, BABY_BEAR_P);
        let (r2, tree2) = commit_trace(&spec, &t, BABY_BEAR_P);
        assert_eq!(r1, r2);
        assert_eq!(tree1, tree2);
        // 6 leaves pad to 8: levels of 8, 4, 2, 1.
        assert_eq!(
            tree1.levels.iter().map(Vec::len).collect::<Vec<_>>(),
            vec![8, 4, 2, 1]
        );
    }

    #[test]
    fn padding_is_not_a_real_zero_leaf() {
        let spec = demo_spec();
        let (_, tree) = commit_trace(&spec, &[9, 8, 0], BABY_BEAR_P);
        assert_ne!(
            tree.levels[0][2], tree.levels[0][3],
            "domain-separated padding must differ from a live zero leaf"
        );
    }

    #[test]
    fn every_leaf_opens_and_verifies() {
        let spec = demo_spec();
        let t = sample_trace();
        let (root, tree) = commit_trace(&spec, &t, BABY_BEAR_P);
        for (i, &leaf) in t.iter().enumerate() {
            let path = open(&tree, i);
            assert_eq!(path.len(), 3);
            assert!(
                verify_open(root, i, leaf, &path, &spec, BABY_BEAR_P),
                "honest opening of leaf {i} must verify (verifyOpen_commit, exercised)"
            );
        }
    }

    #[test]
    fn tampered_leaf_fails() {
        let spec = demo_spec();
        let t = sample_trace();
        let (root, tree) = commit_trace(&spec, &t, BABY_BEAR_P);
        for (i, &leaf) in t.iter().enumerate() {
            let path = open(&tree, i);
            let tampered = (leaf + 1) % BABY_BEAR_P;
            assert!(
                !verify_open(root, i, tampered, &path, &spec, BABY_BEAR_P),
                "tampered leaf {i} must not verify"
            );
        }
    }

    #[test]
    fn tampered_path_and_root_fail() {
        let spec = demo_spec();
        let t = sample_trace();
        let (root, tree) = commit_trace(&spec, &t, BABY_BEAR_P);
        let mut path = open(&tree, 2);
        path[1].limbs[0] = (path[1].limbs[0] + 1) % BABY_BEAR_P;
        assert!(!verify_open(root, 2, t[2], &path, &spec, BABY_BEAR_P));
        let path = open(&tree, 2);
        let mut bad_root = root;
        bad_root.limbs[0] = (bad_root.limbs[0] + 1) % BABY_BEAR_P;
        assert!(!verify_open(bad_root, 2, t[2], &path, &spec, BABY_BEAR_P));
    }

    #[test]
    fn wrong_index_fails() {
        let spec = demo_spec();
        let t = sample_trace();
        let (root, tree) = commit_trace(&spec, &t, BABY_BEAR_P);
        let path = open(&tree, 2);
        // right leaf value, wrong claimed position
        assert!(!verify_open(root, 3, t[2], &path, &spec, BABY_BEAR_P));
        // index beyond the path's height
        assert!(!verify_open(root, 8, t[2], &path, &spec, BABY_BEAR_P));
    }

    #[test]
    fn single_leaf_tree() {
        let spec = demo_spec();
        let (root, tree) = commit_trace(&spec, &[42], BABY_BEAR_P);
        let path = open(&tree, 0);
        assert!(path.is_empty());
        assert!(verify_open(root, 0, 42, &path, &spec, BABY_BEAR_P));
        assert!(!verify_open(root, 0, 43, &path, &spec, BABY_BEAR_P));
    }

    #[test]
    fn noncanonical_proof_data_rejects_without_panicking() {
        let spec = demo_spec();
        let t = sample_trace();
        let (root, tree) = commit_trace(&spec, &t, BABY_BEAR_P);

        let mut bad_path = open(&tree, 2);
        bad_path[0].limbs[4] = BABY_BEAR_P;
        assert!(!verify_open(root, 2, t[2], &bad_path, &spec, BABY_BEAR_P));

        let mut bad_root = root;
        bad_root.limbs[8] = BABY_BEAR_P;
        assert!(!verify_open(
            bad_root,
            2,
            t[2],
            &open(&tree, 2),
            &spec,
            BABY_BEAR_P
        ));
    }
}
