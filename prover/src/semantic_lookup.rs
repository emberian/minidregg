//! Receipt-facing binding for the Tower256 indexed-lookup proof.
//!
//! `logup_tower256` now proves Booleanity and lookup correctness against one
//! exact ordered vector of address-column roots.  This module turns that
//! vector into a fixed-size semantic clause: it binds the canonical statement
//! digest and the index-bundle root, then verifies the native proof against an
//! independently supplied root from the semantic trace/receipt.
//!
//! This is the concrete `[LOGUP256-INDEX-ROOT-LINK]` adapter.  It does not
//! claim that a larger receipt has already accumulated this clause; that
//! remains `[PCH-OUTER-ACCUMULATOR]`.

use core::fmt;

use sha3::{Digest as _, Sha3_256};

use crate::{
    binary_hash::BinaryRoot,
    logup_tower256::{
        semantic_index_bundle_root, verify_logup256_single_bound, Logup256Error, Logup256Proof,
        Logup256Statement,
    },
    semantic_receipt::{semantic_id, SemanticId},
    semantic_turn_receipt::NativeClauseBinding,
};

const CLAUSE_TAG: &[u8] = b"MDRG-SEMANTIC-LOOKUP-CLAUSE-V1";
const RELATION_LABEL: &[u8] = b"minidregg/relation/tower256-logup-indexed/v2";

/// Public binding carried by a semantic receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticLookupClause {
    pub statement_id: SemanticId,
    pub index_bundle_root: BinaryRoot,
    pub statement: Logup256Statement,
    pub proof: Logup256Proof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticLookupError {
    Native(Logup256Error),
    IndexBundleMismatch,
    StatementDigestMismatch,
    LengthOverflow,
}

impl From<Logup256Error> for SemanticLookupError {
    fn from(value: Logup256Error) -> Self {
        Self::Native(value)
    }
}

impl fmt::Display for SemanticLookupError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Native(error) => error.fmt(f),
            Self::IndexBundleMismatch => {
                write!(f, "semantic lookup clause names a different index bundle")
            }
            Self::StatementDigestMismatch => {
                write!(f, "semantic lookup clause statement digest mismatch")
            }
            Self::LengthOverflow => write!(f, "semantic lookup statement length overflow"),
        }
    }
}

impl std::error::Error for SemanticLookupError {}

/// Bind already-produced native proof material into the canonical public
/// clause.  Verification remains mandatory; this constructor does not turn a
/// proof object into an accept bit.
pub fn bind_semantic_lookup_clause(
    statement: Logup256Statement,
    proof: Logup256Proof,
) -> Result<SemanticLookupClause, SemanticLookupError> {
    let index_bundle_root = semantic_index_bundle_root(&statement)?;
    let statement_id = semantic_lookup_statement_id(&statement)?;
    Ok(SemanticLookupClause {
        statement_id,
        index_bundle_root,
        statement,
        proof,
    })
}

/// Verify the clause against the index-bundle root supplied by the semantic
/// trace/receipt.  Both the full native statement and proof are replayed.
pub fn verify_semantic_lookup_clause(
    expected_index_bundle_root: &BinaryRoot,
    clause: &SemanticLookupClause,
) -> Result<bool, SemanticLookupError> {
    if &clause.index_bundle_root != expected_index_bundle_root
        || clause.statement.index_bundle_root != clause.index_bundle_root
    {
        return Ok(false);
    }
    if semantic_lookup_statement_id(&clause.statement)? != clause.statement_id {
        return Ok(false);
    }
    Ok(verify_logup256_single_bound(
        expected_index_bundle_root,
        &clause.statement,
        &clause.proof,
    )?)
}

/// Stable relation identifier used in the typed receipt's ordered native
/// clause list.
pub fn semantic_lookup_relation_id() -> SemanticId {
    semantic_id(RELATION_LABEL)
}

/// Project a verified-proof candidate into the fixed-size binding carried by
/// the typed receipt header.  As with [`bind_semantic_lookup_clause`], this is
/// only a canonical projection; verification remains mandatory.
pub fn semantic_lookup_native_binding(clause: &SemanticLookupClause) -> NativeClauseBinding {
    NativeClauseBinding {
        relation_id: semantic_lookup_relation_id(),
        statement_id: clause.statement_id,
        commitment_root: clause.index_bundle_root,
    }
}

/// Verify a Tower256 lookup clause using only the corresponding binding from
/// the typed receipt.  There is no independent expected-root parameter: the
/// receipt commits the relation id, statement id, and exact ordered index-root
/// bundle, and all three must match before the native proof is replayed.
pub fn verify_semantic_lookup_native_binding(
    binding: &NativeClauseBinding,
    clause: &SemanticLookupClause,
) -> Result<bool, SemanticLookupError> {
    if binding.relation_id != semantic_lookup_relation_id()
        || binding.statement_id != clause.statement_id
        || binding.commitment_root != clause.index_bundle_root
    {
        return Ok(false);
    }
    verify_semantic_lookup_clause(&binding.commitment_root, clause)
}

/// Canonical public statement digest.  Every shape field and every native
/// commitment root is included in fixed order.
pub fn semantic_lookup_statement_id(
    statement: &Logup256Statement,
) -> Result<SemanticId, SemanticLookupError> {
    let row_count =
        u64::try_from(statement.row_count).map_err(|_| SemanticLookupError::LengthOverflow)?;
    let table_count =
        u64::try_from(statement.table_count).map_err(|_| SemanticLookupError::LengthOverflow)?;
    let num_queries =
        u64::try_from(statement.num_queries).map_err(|_| SemanticLookupError::LengthOverflow)?;
    let root_count = u64::try_from(statement.index_roots.len())
        .map_err(|_| SemanticLookupError::LengthOverflow)?;
    let mut hash = Sha3_256::new();
    hash.update(CLAUSE_TAG);
    hash.update(row_count.to_le_bytes());
    hash.update(table_count.to_le_bytes());
    hash.update(statement.log_blowup.to_le_bytes());
    hash.update(num_queries.to_le_bytes());
    hash.update(statement.table_root.as_bytes());
    hash.update(statement.index_bundle_root.as_bytes());
    hash.update(root_count.to_le_bytes());
    for (bit, root) in statement.index_roots.iter().enumerate() {
        hash.update((bit as u64).to_le_bytes());
        hash.update(root.as_bytes());
    }
    hash.update(statement.y_root.as_bytes());
    Ok(hash.finalize().into())
}
