//! Policy AST extraction & deterministic secret-redaction byte transducers
//! (bound to Lean conformance vectors in `testdata/policy_transducer_conformance.json`).
//!
//! Mirrors the verified Lean 4 specifications in:
//! - `Theory/VerifiedAstTransducer.lean` (`AttrCfg`, `ll1Deterministic`, `execAttrReplay`,
//!   `ll1Parse`, `miniJsonCfg`, `ambigMiniJsonCfg`, `RedactRule`, `redactBytes`, `allRulesSafe`),
//! - `Compiler/PolicyAstTransducerEmit.lean` (`RewriteCertStmt`, `RewriteCertWitness`,
//!   `verifyRewriteAndExtract`, `contentCommit` over SP 800-185 `cSHAKE256` cube-Merkle trees).

use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::sync::OnceLock;

use crate::hash_kernels::cshake256_xof;

/// 32-byte little-endian `cSHAKE256` digest (`Tower256ContentCert.Digest`).
pub type Digest32 = [u8; 32];

/// Errors surfaced by the native policy transducer and `RewriteCert` verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransducerError {
    GrammarNotLl1,
    TooManyRules { count: usize },
    NonterminalOutOfBounds { id: usize, count: usize },
    UnsafeRedactionRules,
    InvalidRuleIndex { step: usize, rule_idx: usize, rule_count: usize },
    RuleLhsMismatch { step: usize },
    TerminalMismatch { expected: String, found: String },
    UnexpectedEof,
    UnconsumedInput { remaining: usize },
    UnconsumedRules { remaining: usize },
    ValueStackUnderflow { needed: usize, available: usize },
    InvalidFinalValueStack { len: usize },
    NoMatchingLl1Rule { lookahead: String },
    FuelExhausted,
    RawLengthMismatch { expected: usize, actual: usize },
    RawRootMismatch,
    CleanLengthMismatch { expected: usize, actual: usize },
    CleanRootMismatch,
    RedactionMismatch,
    AstMismatch,
}

impl fmt::Display for TransducerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::GrammarNotLl1 => write!(f, "grammar failed LL(1) disjoint-predict-set check"),
            Self::TooManyRules { count } => {
                write!(f, "grammar rule count {count} exceeds u16 dispatch limit")
            }
            Self::NonterminalOutOfBounds { id, count } => {
                write!(f, "nonterminal id {id} >= table size {count}")
            }
            Self::UnsafeRedactionRules => write!(f, "redaction policy failed SafeReplacement check"),
            Self::InvalidRuleIndex { step, rule_idx, rule_count } => write!(
                f,
                "replay step {step}: rule index {rule_idx} >= rule count {rule_count}"
            ),
            Self::RuleLhsMismatch { step } => {
                write!(f, "replay step {step}: rule LHS does not match top nonterminal")
            }
            Self::TerminalMismatch { expected, found } => {
                write!(f, "terminal mismatch: expected {expected}, found {found}")
            }
            Self::UnexpectedEof => write!(f, "unexpected end of input during replay"),
            Self::UnconsumedInput { remaining } => {
                write!(f, "stack emptied with {remaining} unconsumed input tokens")
            }
            Self::UnconsumedRules { remaining } => {
                write!(f, "stack emptied with {remaining} unconsumed certificate rules")
            }
            Self::ValueStackUnderflow { needed, available } => write!(
                f,
                "semantic reduction needed {needed} values, stack has {available}"
            ),
            Self::InvalidFinalValueStack { len } => {
                write!(f, "replay finished with {len} synthesized values (expected 1)")
            }
            Self::NoMatchingLl1Rule { lookahead } => {
                write!(f, "LL(1) predictive parser found no matching rule at lookahead {lookahead}")
            }
            Self::FuelExhausted => write!(f, "LL(1) predictive parser exhausted step fuel"),
            Self::RawLengthMismatch { expected, actual } => {
                write!(f, "raw transcript length mismatch: expected {expected}, got {actual}")
            }
            Self::RawRootMismatch => write!(f, "raw transcript cSHAKE256 content root mismatch"),
            Self::CleanLengthMismatch { expected, actual } => {
                write!(f, "clean transcript length mismatch: expected {expected}, got {actual}")
            }
            Self::CleanRootMismatch => {
                write!(f, "clean transcript cSHAKE256 content root mismatch")
            }
            Self::RedactionMismatch => {
                write!(f, "w_clean does not equal canonical redact_bytes(rules, w_raw)")
            }
            Self::AstMismatch => write!(f, "extracted AST does not match statement claimed_ast"),
        }
    }
}

impl std::error::Error for TransducerError {}

// ============================================================================
// §1. Tower256 cSHAKE256 Cube-Merkle Content Commitment (`contentCommit`)
// ============================================================================

const LEAF_PREFIX: u8 = 0x01;
const LEAF_NAME: &[u8] = b"MINIDREGG/TOWER256/MERKLE/LEAF/V1";
const NODE_PREFIX: u8 = 0x02;
const NODE_NAME: &[u8] = b"MINIDREGG/TOWER256/MERKLE/NODE/V1";
const MAX_CACHED_ZERO_DEPTH: usize = 26;

fn encode_length_unary(out: &mut Vec<u8>, n: usize) {
    out.resize(out.len() + n, 0);
    out.push(1);
}

fn envelope_bytes(out: &mut Vec<u8>, payload: &[u8]) {
    encode_length_unary(out, payload.len());
    out.extend_from_slice(payload);
}

fn make_customization(prefix: u8, name: &[u8]) -> Vec<u8> {
    let mut c = Vec::with_capacity(1 + name.len());
    c.push(prefix);
    c.extend_from_slice(name);
    c
}

fn xof_digest32(customization: &[u8], input: &[u8]) -> Digest32 {
    cshake256_xof(customization, input, 32)
        .try_into()
        .expect("cSHAKE256 32-byte XOF")
}

/// Compute `Nat.clog 2 n` (`Tower256ContentCert.depthOf`).
#[inline]
pub fn depth_of(n: usize) -> usize {
    if n <= 1 {
        0
    } else {
        (usize::BITS - (n - 1).leading_zeros()) as usize
    }
}

struct ContentMerkleTables {
    node_cust: Vec<u8>,
    byte_leaves: [Digest32; 256],
    zero_subtrees: [Digest32; MAX_CACHED_ZERO_DEPTH],
}

static CONTENT_MERKLE_TABLES: OnceLock<ContentMerkleTables> = OnceLock::new();

fn merkle_tables() -> &'static ContentMerkleTables {
    CONTENT_MERKLE_TABLES.get_or_init(|| {
        let leaf_cust = make_customization(LEAF_PREFIX, LEAF_NAME);
        let node_cust = make_customization(NODE_PREFIX, NODE_NAME);
        let mut byte_leaves = [[0u8; 32]; 256];
        for b in 0..256usize {
            let mut c8_le = [0u8; 32];
            c8_le[0] = b as u8;
            let mut input = Vec::with_capacity(1 + 33 + 32);
            input.push(0u8);
            envelope_bytes(&mut input, &c8_le);
            byte_leaves[b] = xof_digest32(&leaf_cust, &input);
        }
        let mut zero_subtrees = [[0u8; 32]; MAX_CACHED_ZERO_DEPTH];
        zero_subtrees[0] = byte_leaves[0];
        for h in 1..MAX_CACHED_ZERO_DEPTH {
            let prev = zero_subtrees[h - 1];
            let mut input = Vec::with_capacity(1 + 2 * (33 + 32));
            input.push(1u8);
            envelope_bytes(&mut input, &prev);
            envelope_bytes(&mut input, &prev);
            zero_subtrees[h] = xof_digest32(&node_cust, &input);
        }
        ContentMerkleTables {
            node_cust,
            byte_leaves,
            zero_subtrees,
        }
    })
}

#[inline]
fn hash_merkle_node(node_cust: &[u8], left: &Digest32, right: &Digest32) -> Digest32 {
    let mut input = [0u8; 1 + 2 * (32 + 1 + 32)];
    // Exact layout: `1 :: (32 zeros ++ [1] ++ left[32]) ++ (32 zeros ++ [1] ++ right[32])` = 131 bytes!
    input[0] = 1u8;
    // input[1..33] are already 0
    input[33] = 1u8;
    input[34..66].copy_from_slice(left);
    // input[66..98] are already 0
    input[98] = 1u8;
    input[99..131].copy_from_slice(right);
    xof_digest32(node_cust, &input)
}

fn content_root_strided(
    tabs: &ContentMerkleTables,
    bytes: &[u8],
    total_leaves: usize,
    offset: usize,
    stride: usize,
    rem_depth: usize,
) -> Digest32 {
    if offset >= bytes.len() && rem_depth < MAX_CACHED_ZERO_DEPTH {
        // Every address `offset + k * stride` in this subtree has `index >= offset >= bytes.len()`,
        // so every leaf in this subtree is `leafOfNat 0`!
        return tabs.zero_subtrees[rem_depth];
    }
    if stride >= total_leaves {
        let b = bytes.get(offset).copied().unwrap_or(0);
        tabs.byte_leaves[b as usize]
    } else {
        let left = content_root_strided(tabs, bytes, total_leaves, offset, stride * 2, rem_depth - 1);
        let right = content_root_strided(
            tabs,
            bytes,
            total_leaves,
            offset + stride,
            stride * 2,
            rem_depth - 1,
        );
        hash_merkle_node(&tabs.node_cust, &left, &right)
    }
}

/// Compute `Tower256ContentCert.contentCommit(bytes)` (`cSHAKE256` LSB-split cube-Merkle root).
pub fn content_commit(bytes: &[u8]) -> Digest32 {
    let tabs = merkle_tables();
    let d = depth_of(bytes.len());
    let total_leaves = 1usize << d;
    content_root_strided(tabs, bytes, total_leaves, 0, 1, d)
}

/// Direct uncached reference implementation of `Tower256ContentCert.contentCommit` for cross-checking.
pub fn content_commit_unoptimized_ref(bytes: &[u8]) -> Digest32 {
    let leaf_cust = make_customization(LEAF_PREFIX, LEAF_NAME);
    let node_cust = make_customization(NODE_PREFIX, NODE_NAME);
    let d = depth_of(bytes.len());
    let total_leaves = 1usize << d;
    fn rec(
        leaf_cust: &[u8],
        node_cust: &[u8],
        bytes: &[u8],
        total_leaves: usize,
        offset: usize,
        stride: usize,
    ) -> Digest32 {
        if stride >= total_leaves {
            let mut c8_le = [0u8; 32];
            c8_le[0] = bytes.get(offset).copied().unwrap_or(0);
            let mut input = vec![0u8];
            envelope_bytes(&mut input, &c8_le);
            xof_digest32(leaf_cust, &input)
        } else {
            let l = rec(leaf_cust, node_cust, bytes, total_leaves, offset, stride * 2);
            let r = rec(leaf_cust, node_cust, bytes, total_leaves, offset + stride, stride * 2);
            let mut input = vec![1u8];
            envelope_bytes(&mut input, &l);
            envelope_bytes(&mut input, &r);
            xof_digest32(node_cust, &input)
        }
    }
    rec(&leaf_cust, &node_cust, bytes, total_leaves, 0, 1)
}

// ============================================================================
// §2. Generic Attributed Context-Free Grammar, `ll1_deterministic`, & Replay
// ============================================================================

/// Grammar symbol (`Mathlib.Symbol T NT`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CfgSym<T, NT> {
    Terminal(T),
    Nonterminal(NT),
}

/// Attributed production rule `lhs -> rhs` with semantic operator `op`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttrRule<T, NT, SemOp> {
    pub lhs: NT,
    pub rhs: Vec<CfgSym<T, NT>>,
    pub op: SemOp,
}

/// Attributed Context-Free Grammar (`Theory.VerifiedAstTransducer.AttrCfg`).
pub struct AttrCfg<T, NT, SemOp, Val> {
    pub initial: NT,
    pub rules: Vec<AttrRule<T, NT, SemOp>>,
    pub term_val: fn(T) -> Val,
    pub eval_op: fn(&SemOp, &[Val]) -> Val,
    pub eval_in_place: Option<fn(&SemOp, &mut Vec<Val>, usize)>,
}

#[derive(Clone, Debug)]
enum WorkItem<T, NT, SemOp> {
    Sym(CfgSym<T, NT>),
    Reduce(SemOp, usize),
}

fn dedup_push<X: PartialEq + Clone>(vec: &mut Vec<X>, item: X) {
    if !vec.contains(&item) {
        vec.push(item);
    }
}

fn dedup_extend<X: PartialEq + Clone>(vec: &mut Vec<X>, items: &[X]) {
    for it in items {
        dedup_push(vec, it.clone());
    }
}

fn list_subset<X: PartialEq>(xs: &[X], ys: &[X]) -> bool {
    xs.iter().all(|x| ys.contains(x))
}

fn list_disjoint<X: PartialEq>(xs: &[X], ys: &[X]) -> bool {
    xs.iter().all(|x| !ys.contains(x))
}

fn sym_nullable<T, NT: PartialEq>(null_nts: &[NT], sym: &CfgSym<T, NT>) -> bool {
    match sym {
        CfgSym::Terminal(_) => false,
        CfgSym::Nonterminal(a) => null_nts.contains(a),
    }
}

fn seq_nullable<T, NT: PartialEq>(null_nts: &[NT], syms: &[CfgSym<T, NT>]) -> bool {
    syms.iter().all(|s| sym_nullable(null_nts, s))
}

fn seq_first<T: PartialEq + Clone, NT: Eq + Hash>(
    null_nts: &[NT],
    first_tab: &HashMap<NT, Vec<T>>,
    syms: &[CfgSym<T, NT>],
) -> Vec<T> {
    let mut out = Vec::new();
    for s in syms {
        match s {
            CfgSym::Terminal(t) => {
                out.push(t.clone());
                break;
            }
            CfgSym::Nonterminal(a) => {
                if let Some(fs) = first_tab.get(a) {
                    out.extend(fs.iter().cloned());
                }
                if !null_nts.contains(a) {
                    break;
                }
            }
        }
    }
    out
}

fn rule_predict<T: PartialEq + Clone, NT: Eq + Hash, SemOp>(
    null_nts: &[NT],
    first_tab: &HashMap<NT, Vec<T>>,
    follow_tab: &HashMap<NT, Vec<Option<T>>>,
    rule: &AttrRule<T, NT, SemOp>,
) -> Vec<Option<T>> {
    let mut out: Vec<Option<T>> = seq_first(null_nts, first_tab, &rule.rhs)
        .into_iter()
        .map(Some)
        .collect();
    if seq_nullable(null_nts, &rule.rhs) {
        if let Some(fol) = follow_tab.get(&rule.lhs) {
            out.extend(fol.iter().cloned());
        }
    }
    out
}

pub struct ComputedLl1Tables<T, NT> {
    pub null_nts: Vec<NT>,
    pub first_tab: HashMap<NT, Vec<T>>,
    pub follow_tab: HashMap<NT, Vec<Option<T>>>,
}

/// Compute `(NULLABLE, FIRST, FOLLOW)` tables (`Theory.VerifiedAstTransducer.computeLl1Tables`).
pub fn compute_ll1_tables<T, NT, SemOp, Val>(
    cfg: &AttrCfg<T, NT, SemOp, Val>,
) -> ComputedLl1Tables<T, NT>
where
    T: Eq + Hash + Clone,
    NT: Eq + Hash + Clone,
{
    let mut nts = vec![cfg.initial.clone()];
    for r in &cfg.rules {
        dedup_push(&mut nts, r.lhs.clone());
        for s in &r.rhs {
            if let CfgSym::Nonterminal(a) = s {
                dedup_push(&mut nts, a.clone());
            }
        }
    }
    let rounds = nts.len() + 1;
    let mut null_nts: Vec<NT> = Vec::new();
    for _ in 0..rounds {
        for r in &cfg.rules {
            if seq_nullable(&null_nts, &r.rhs) {
                dedup_push(&mut null_nts, r.lhs.clone());
            }
        }
    }

    let mut first_tab: HashMap<NT, Vec<T>> = nts.iter().map(|a| (a.clone(), Vec::new())).collect();
    for _ in 0..rounds {
        for r in &cfg.rules {
            let rhs_f = seq_first(&null_nts, &first_tab, &r.rhs);
            let entry = first_tab.entry(r.lhs.clone()).or_default();
            dedup_extend(entry, &rhs_f);
        }
    }

    let mut follow_tab: HashMap<NT, Vec<Option<T>>> = nts
        .iter()
        .map(|a| {
            let init = if *a == cfg.initial { vec![None] } else { Vec::new() };
            (a.clone(), init)
        })
        .collect();
    for _ in 0..rounds {
        for r in &cfg.rules {
            let lhs_fol = follow_tab.get(&r.lhs).cloned().unwrap_or_default();
            for idx in 0..r.rhs.len() {
                if let CfgSym::Nonterminal(b) = &r.rhs[idx] {
                    let suf = &r.rhs[idx + 1..];
                    let add_first: Vec<Option<T>> = seq_first(&null_nts, &first_tab, suf)
                        .into_iter()
                        .map(Some)
                        .collect();
                    let entry = follow_tab.entry(b.clone()).or_default();
                    dedup_extend(entry, &add_first);
                    if seq_nullable(&null_nts, suf) {
                        dedup_extend(entry, &lhs_fol);
                    }
                }
            }
        }
    }

    ComputedLl1Tables {
        null_nts,
        first_tab,
        follow_tab,
    }
}

/// Executable LL(1) disjoint-predict-set determinacy checker (`ll1Deterministic : AttrCfg -> Bool`).
pub fn ll1_deterministic<T, NT, SemOp, Val>(cfg: &AttrCfg<T, NT, SemOp, Val>) -> bool
where
    T: Eq + Hash + Clone,
    NT: Eq + Hash + Clone,
{
    let tabs = compute_ll1_tables(cfg);
    let init_ok = tabs
        .follow_tab
        .get(&cfg.initial)
        .map(|f| f.contains(&None))
        .unwrap_or(false);
    if !init_ok {
        return false;
    }

    for r in &cfg.rules {
        if seq_nullable(&tabs.null_nts, &r.rhs) && !tabs.null_nts.contains(&r.lhs) {
            return false;
        }
        let rhs_first = seq_first(&tabs.null_nts, &tabs.first_tab, &r.rhs);
        let lhs_first = tabs.first_tab.get(&r.lhs).map(Vec::as_slice).unwrap_or(&[]);
        if !list_subset(&rhs_first, lhs_first) {
            return false;
        }
        let lhs_fol = tabs.follow_tab.get(&r.lhs).map(Vec::as_slice).unwrap_or(&[]);
        for idx in 0..r.rhs.len() {
            if let CfgSym::Nonterminal(b) = &r.rhs[idx] {
                let suf = &r.rhs[idx + 1..];
                let suf_first: Vec<Option<T>> = seq_first(&tabs.null_nts, &tabs.first_tab, suf)
                    .into_iter()
                    .map(Some)
                    .collect();
                let b_fol = tabs.follow_tab.get(b).map(Vec::as_slice).unwrap_or(&[]);
                if !list_subset(&suf_first, b_fol) {
                    return false;
                }
                if seq_nullable(&tabs.null_nts, suf) && !list_subset(lhs_fol, b_fol) {
                    return false;
                }
            }
        }
    }

    let predicts: Vec<Vec<Option<T>>> = cfg
        .rules
        .iter()
        .map(|r| rule_predict(&tabs.null_nts, &tabs.first_tab, &tabs.follow_tab, r))
        .collect();
    for i in 0..cfg.rules.len() {
        for j in (i + 1)..cfg.rules.len() {
            if cfg.rules[i].lhs == cfg.rules[j].lhs
                && !list_disjoint(&predicts[i], &predicts[j])
            {
                return false;
            }
        }
    }
    true
}

/// Linear-time attributed pushdown stack replay (`Theory.VerifiedAstTransducer.execAttrReplay`).
pub fn exec_attr_replay<T, NT, SemOp, Val>(
    cfg: &AttrCfg<T, NT, SemOp, Val>,
    rule_indices: &[usize],
    input: &[T],
) -> Result<Val, TransducerError>
where
    T: PartialEq + Copy + fmt::Debug,
    NT: PartialEq + Copy + fmt::Debug,
    SemOp: Clone,
{
    let mut cstk: Vec<WorkItem<T, NT, SemOp>> =
        vec![WorkItem::Sym(CfgSym::Nonterminal(cfg.initial))];
    let mut vstk: Vec<Val> = Vec::with_capacity(64);
    let mut rule_pos = 0usize;
    let mut input_pos = 0usize;

    while let Some(top) = cstk.pop() {
        match top {
            WorkItem::Sym(CfgSym::Terminal(expected)) => {
                let Some(&actual) = input.get(input_pos) else {
                    return Err(TransducerError::UnexpectedEof);
                };
                if actual != expected {
                    return Err(TransducerError::TerminalMismatch {
                        expected: format!("{expected:?}"),
                        found: format!("{actual:?}"),
                    });
                }
                input_pos += 1;
                vstk.push((cfg.term_val)(expected));
            }
            WorkItem::Sym(CfgSym::Nonterminal(nt)) => {
                let Some(&ridx) = rule_indices.get(rule_pos) else {
                    return Err(TransducerError::InvalidRuleIndex {
                        step: rule_pos,
                        rule_idx: usize::MAX,
                        rule_count: cfg.rules.len(),
                    });
                };
                let Some(rule) = cfg.rules.get(ridx) else {
                    return Err(TransducerError::InvalidRuleIndex {
                        step: rule_pos,
                        rule_idx: ridx,
                        rule_count: cfg.rules.len(),
                    });
                };
                if rule.lhs != nt {
                    return Err(TransducerError::RuleLhsMismatch { step: rule_pos });
                }
                rule_pos += 1;
                cstk.push(WorkItem::Reduce(rule.op.clone(), rule.rhs.len()));
                for sym in rule.rhs.iter().rev() {
                    cstk.push(WorkItem::Sym(*sym));
                }
            }
            WorkItem::Reduce(op, k) => {
                if vstk.len() < k {
                    return Err(TransducerError::ValueStackUnderflow {
                        needed: k,
                        available: vstk.len(),
                    });
                }
                if let Some(f) = cfg.eval_in_place {
                    f(&op, &mut vstk, k);
                } else {
                    let split_at = vstk.len() - k;
                    let reduced = (cfg.eval_op)(&op, &vstk[split_at..]);
                    vstk.truncate(split_at);
                    vstk.push(reduced);
                }
            }
        }
    }

    if rule_pos != rule_indices.len() {
        return Err(TransducerError::UnconsumedRules {
            remaining: rule_indices.len() - rule_pos,
        });
    }
    if input_pos != input.len() {
        return Err(TransducerError::UnconsumedInput {
            remaining: input.len() - input_pos,
        });
    }
    if vstk.len() != 1 {
        return Err(TransducerError::InvalidFinalValueStack { len: vstk.len() });
    }
    Ok(vstk.pop().expect("single AST value"))
}

/// Precompiled `O(1)`-dispatch byte-level LL(1) parser table (`257` lookahead slots per nonterminal).
pub struct CompiledByteLl1Parser<NT, SemOp, Val> {
    cfg: AttrCfg<u8, NT, SemOp, Val>,
    nt_to_id: fn(NT) -> usize,
    dispatch: Vec<[u16; 257]>,
}

const NO_RULE: u16 = u16::MAX;

#[inline]
fn tok_slot(tok: Option<u8>) -> usize {
    match tok {
        None => 0,
        Some(b) => (b as usize) + 1,
    }
}

impl<NT, SemOp, Val> CompiledByteLl1Parser<NT, SemOp, Val>
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: Clone,
{
    pub fn compile(
        cfg: AttrCfg<u8, NT, SemOp, Val>,
        nt_count: usize,
        nt_to_id: fn(NT) -> usize,
    ) -> Result<Self, TransducerError> {
        if cfg.rules.len() >= NO_RULE as usize {
            return Err(TransducerError::TooManyRules {
                count: cfg.rules.len(),
            });
        }
        let init_id = nt_to_id(cfg.initial);
        if init_id >= nt_count {
            return Err(TransducerError::NonterminalOutOfBounds {
                id: init_id,
                count: nt_count,
            });
        }
        for r in &cfg.rules {
            let lhs_id = nt_to_id(r.lhs);
            if lhs_id >= nt_count {
                return Err(TransducerError::NonterminalOutOfBounds {
                    id: lhs_id,
                    count: nt_count,
                });
            }
            for s in &r.rhs {
                if let CfgSym::Nonterminal(nt) = *s {
                    let id = nt_to_id(nt);
                    if id >= nt_count {
                        return Err(TransducerError::NonterminalOutOfBounds {
                            id,
                            count: nt_count,
                        });
                    }
                }
            }
        }
        if !ll1_deterministic(&cfg) {
            return Err(TransducerError::GrammarNotLl1);
        }
        let tabs = compute_ll1_tables(&cfg);
        let mut dispatch = vec![[NO_RULE; 257]; nt_count];
        for (ridx, rule) in cfg.rules.iter().enumerate() {
            let pred = rule_predict(&tabs.null_nts, &tabs.first_tab, &tabs.follow_tab, rule);
            let row = &mut dispatch[nt_to_id(rule.lhs)];
            for tok in pred {
                row[tok_slot(tok)] = ridx as u16;
            }
        }
        Ok(Self {
            cfg,
            nt_to_id,
            dispatch,
        })
    }

    pub fn cfg(&self) -> &AttrCfg<u8, NT, SemOp, Val> {
        &self.cfg
    }

    /// Parse raw byte slice `input` in `O(|input|)` table-driven steps, returning `(rule_indices, ast)`.
    pub fn parse(&self, input: &[u8]) -> Result<(Vec<usize>, Val), TransducerError> {
        let mut cstk: Vec<WorkItem<u8, NT, SemOp>> = Vec::with_capacity(64);
        cstk.push(WorkItem::Sym(CfgSym::Nonterminal(self.cfg.initial)));
        let mut vstk: Vec<Val> = Vec::with_capacity(64);
        let mut rule_indices: Vec<usize> = Vec::with_capacity(input.len() * 2 + 16);
        let mut pos = 0usize;
        let max_fuel = (input.len() + 1) * (self.cfg.rules.len() + 8) + 16;
        let mut steps = 0usize;

        while let Some(top) = cstk.pop() {
            steps += 1;
            if steps > max_fuel {
                return Err(TransducerError::FuelExhausted);
            }
            match top {
                WorkItem::Sym(CfgSym::Terminal(expected)) => {
                    let Some(&actual) = input.get(pos) else {
                        return Err(TransducerError::UnexpectedEof);
                    };
                    if actual != expected {
                        return Err(TransducerError::TerminalMismatch {
                            expected: format!("0x{expected:02x}"),
                            found: format!("0x{actual:02x}"),
                        });
                    }
                    pos += 1;
                    vstk.push((self.cfg.term_val)(expected));
                }
                WorkItem::Sym(CfgSym::Nonterminal(nt)) => {
                    let lookahead = input.get(pos).copied();
                    let ridx_u16 = self.dispatch[(self.nt_to_id)(nt)][tok_slot(lookahead)];
                    if ridx_u16 == NO_RULE {
                        return Err(TransducerError::NoMatchingLl1Rule {
                            lookahead: format!("{lookahead:?}"),
                        });
                    }
                    let ridx = ridx_u16 as usize;
                    let rule = &self.cfg.rules[ridx];
                    rule_indices.push(ridx);
                    cstk.push(WorkItem::Reduce(rule.op.clone(), rule.rhs.len()));
                    for sym in rule.rhs.iter().rev() {
                        cstk.push(WorkItem::Sym(*sym));
                    }
                }
                WorkItem::Reduce(op, k) => {
                    if vstk.len() < k {
                        return Err(TransducerError::ValueStackUnderflow {
                            needed: k,
                            available: vstk.len(),
                        });
                    }
                    if let Some(f) = self.cfg.eval_in_place {
                        f(&op, &mut vstk, k);
                    } else {
                        let split_at = vstk.len() - k;
                        let reduced = (self.cfg.eval_op)(&op, &vstk[split_at..]);
                        vstk.truncate(split_at);
                        vstk.push(reduced);
                    }
                }
            }
        }

        if pos != input.len() {
            return Err(TransducerError::UnconsumedInput {
                remaining: input.len() - pos,
            });
        }
        if vstk.len() != 1 {
            return Err(TransducerError::InvalidFinalValueStack { len: vstk.len() });
        }
        Ok((rule_indices, vstk.pop().expect("single AST")))
    }

    /// Fast AST-only extraction skipping certificate rule-index vector construction.
    pub fn parse_ast_only(&self, input: &[u8]) -> Result<Val, TransducerError> {
        let mut cstk: Vec<WorkItem<u8, NT, SemOp>> = Vec::with_capacity(64);
        cstk.push(WorkItem::Sym(CfgSym::Nonterminal(self.cfg.initial)));
        let mut vstk: Vec<Val> = Vec::with_capacity(64);
        let mut pos = 0usize;

        while let Some(top) = cstk.pop() {
            match top {
                WorkItem::Sym(CfgSym::Terminal(expected)) => {
                    let Some(&actual) = input.get(pos) else {
                        return Err(TransducerError::UnexpectedEof);
                    };
                    if actual != expected {
                        return Err(TransducerError::TerminalMismatch {
                            expected: format!("0x{expected:02x}"),
                            found: format!("0x{actual:02x}"),
                        });
                    }
                    pos += 1;
                    vstk.push((self.cfg.term_val)(expected));
                }
                WorkItem::Sym(CfgSym::Nonterminal(nt)) => {
                    let lookahead = input.get(pos).copied();
                    let ridx_u16 = self.dispatch[(self.nt_to_id)(nt)][tok_slot(lookahead)];
                    if ridx_u16 == NO_RULE {
                        return Err(TransducerError::NoMatchingLl1Rule {
                            lookahead: format!("{lookahead:?}"),
                        });
                    }
                    let rule = &self.cfg.rules[ridx_u16 as usize];
                    cstk.push(WorkItem::Reduce(rule.op.clone(), rule.rhs.len()));
                    for sym in rule.rhs.iter().rev() {
                        cstk.push(WorkItem::Sym(*sym));
                    }
                }
                WorkItem::Reduce(op, k) => {
                    if let Some(f) = self.cfg.eval_in_place {
                        f(&op, &mut vstk, k);
                    } else {
                        let split_at = vstk.len() - k;
                        let reduced = (self.cfg.eval_op)(&op, &vstk[split_at..]);
                        vstk.truncate(split_at);
                        vstk.push(reduced);
                    }
                }
            }
        }

        if pos != input.len() {
            return Err(TransducerError::UnconsumedInput {
                remaining: input.len() - pos,
            });
        }
        Ok(vstk.pop().expect("single AST"))
    }
}

// ============================================================================
// §3. `Mini` JSON Tool-Call Grammar & Ambiguous Duplicate-Key Splice Grammar
// ============================================================================

/// Exact arbitrary-precision natural number matching Lean 4 `Nat` (`0` = empty limb vector;
/// canonical base-`1_000_000_000` little-endian limbs with nonzero top limb).
/// Eliminates any `u64` wraparound or overflow divergence against Lean `Nat` on large JSON integers.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExactNat(Vec<u32>);

const RADIX_1E9: u64 = 1_000_000_000;

impl ExactNat {
    pub const ZERO: Self = Self(Vec::new());

    pub fn from_u64(mut v: u64) -> Self {
        let mut limbs = Vec::new();
        while v > 0 {
            limbs.push((v % RADIX_1E9) as u32);
            v /= RADIX_1E9;
        }
        Self(limbs)
    }

    pub fn mul10_add(&mut self, digit: u8) {
        debug_assert!(digit < 10);
        if self.0.is_empty() {
            if digit > 0 {
                self.0.push(digit as u32);
            }
            return;
        }
        let mut carry = digit as u64;
        for limb in &mut self.0 {
            let cur = (*limb as u64) * 10 + carry;
            *limb = (cur % RADIX_1E9) as u32;
            carry = cur / RADIX_1E9;
        }
        if carry > 0 {
            self.0.push(carry as u32);
        }
    }

    pub fn from_decimal_digits(d0: u8, ds: &[u8]) -> Self {
        let mut n = Self::from_u64(d0 as u64);
        for &d in ds {
            n.mul10_add(d);
        }
        n
    }

    pub fn from_decimal_digits_rev(d0: u8, rev_ds: &[u8]) -> Self {
        let mut n = Self::from_u64(d0 as u64);
        for &d in rev_ds.iter().rev() {
            n.mul10_add(d);
        }
        n
    }

    pub fn from_decimal_str(s: &str) -> Option<Self> {
        if s.is_empty() {
            return None;
        }
        if s == "0" {
            return Some(Self::ZERO);
        }
        let bytes = s.as_bytes();
        if bytes[0] == b'0' {
            return None;
        }
        let mut out = Self::ZERO;
        for &b in bytes {
            if !b.is_ascii_digit() {
                return None;
            }
            out.mul10_add(b - b'0');
        }
        Some(out)
    }

    pub fn as_u64(&self) -> Option<u64> {
        let mut acc = 0u64;
        for &limb in self.0.iter().rev() {
            acc = acc.checked_mul(RADIX_1E9)?.checked_add(limb as u64)?;
        }
        Some(acc)
    }
}

impl From<u64> for ExactNat {
    fn from(v: u64) -> Self {
        Self::from_u64(v)
    }
}

impl fmt::Display for ExactNat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Some(&top) = self.0.last() else {
            return write!(f, "0");
        };
        write!(f, "{top}")?;
        for &limb in self.0.iter().rev().skip(1) {
            write!(f, "{limb:09}")?;
        }
        Ok(())
    }
}

/// Extracted `Mini` AST value (`Theory.VerifiedAstTransducer.MiniValue`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MiniValue {
    Byte(u8),
    Bytes(Vec<u8>),
    Digits(Vec<u8>),
    Nat(ExactNat),
    ToolCall {
        tool: Vec<u8>,
        target: Vec<u8>,
        amount: ExactNat,
    },
    CotToolCall {
        cot: Vec<u8>,
        tool: Vec<u8>,
        target: Vec<u8>,
        amount: ExactNat,
    },
    Batch(Vec<MiniValue>),
    Unit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MiniNT {
    Root = 0,
    TopExpr = 1,
    ObjDispatch = 2,
    ToolRest = 3,
    CotRest = 4,
    BatchBody = 5,
    BatchTail = 6,
    StrVal = 7,
    Chars = 8,
    Esc = 9,
    NatVal = 10,
    Digits = 11,
    WS = 12,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MiniOp {
    PassAt(usize),
    UnitOp,
    StrUnquote,
    CharsNil,
    CharsCons(u8),
    CharsEsc,
    EscConst(u8),
    NatZero,
    NatPos(u8),
    DigitsNil,
    DigitsCons(u8),
    MkToolRest,
    MkCotRest,
    BatchEmpty,
    BatchCons,
    BatchFinish,
}

fn eval_mini_op(op: &MiniOp, vs: &[MiniValue]) -> MiniValue {
    match *op {
        MiniOp::PassAt(i) => vs.get(i).cloned().unwrap_or(MiniValue::Unit),
        MiniOp::UnitOp => MiniValue::Unit,
        MiniOp::StrUnquote => match vs.get(1) {
            Some(MiniValue::Bytes(rev_chars)) => {
                let mut out = rev_chars.clone();
                out.reverse();
                MiniValue::Bytes(out)
            }
            _ => MiniValue::Bytes(Vec::new()),
        },
        MiniOp::CharsNil => MiniValue::Bytes(Vec::new()),
        MiniOp::CharsCons(b) => match vs.get(1) {
            Some(MiniValue::Bytes(rev_tail)) => {
                let mut out = rev_tail.clone();
                out.push(b);
                MiniValue::Bytes(out)
            }
            _ => MiniValue::Bytes(vec![b]),
        },
        MiniOp::CharsEsc => match (vs.get(1), vs.get(2)) {
            (Some(MiniValue::Byte(b)), Some(MiniValue::Bytes(rev_tail))) => {
                let mut out = rev_tail.clone();
                out.push(*b);
                MiniValue::Bytes(out)
            }
            _ => MiniValue::Bytes(Vec::new()),
        },
        MiniOp::EscConst(b) => MiniValue::Byte(b),
        MiniOp::NatZero => MiniValue::Nat(ExactNat::ZERO),
        MiniOp::NatPos(d0) => match vs.get(1) {
            Some(MiniValue::Digits(rev_ds)) => {
                MiniValue::Nat(ExactNat::from_decimal_digits_rev(d0, rev_ds))
            }
            _ => MiniValue::Nat(ExactNat::from_u64(d0 as u64)),
        },
        MiniOp::DigitsNil => MiniValue::Digits(Vec::new()),
        MiniOp::DigitsCons(d) => match vs.get(1) {
            Some(MiniValue::Digits(rev_ds)) => {
                let mut out = rev_ds.clone();
                out.push(d);
                MiniValue::Digits(out)
            }
            _ => MiniValue::Digits(vec![d]),
        },
        MiniOp::MkToolRest => match (vs.get(7), vs.get(22), vs.get(37)) {
            (
                Some(MiniValue::Bytes(tool)),
                Some(MiniValue::Bytes(target)),
                Some(MiniValue::Nat(amount)),
            ) => MiniValue::ToolCall {
                tool: tool.clone(),
                target: target.clone(),
                amount: amount.clone(),
            },
            _ => MiniValue::Unit,
        },
        MiniOp::MkCotRest => match (vs.get(6), vs.get(19), vs.get(34), vs.get(49)) {
            (
                Some(MiniValue::Bytes(cot)),
                Some(MiniValue::Bytes(tool)),
                Some(MiniValue::Bytes(target)),
                Some(MiniValue::Nat(amount)),
            ) => MiniValue::CotToolCall {
                cot: cot.clone(),
                tool: tool.clone(),
                target: target.clone(),
                amount: amount.clone(),
            },
            _ => MiniValue::Unit,
        },
        MiniOp::BatchEmpty => MiniValue::Batch(Vec::new()),
        MiniOp::BatchCons => match vs {
            [item, _, MiniValue::Batch(rev_rest)] => {
                let mut out = rev_rest.clone();
                out.push(item.clone());
                MiniValue::Batch(out)
            }
            [_, _, item, _, MiniValue::Batch(rev_rest)] => {
                let mut out = rev_rest.clone();
                out.push(item.clone());
                MiniValue::Batch(out)
            }
            _ => MiniValue::Batch(Vec::new()),
        },
        MiniOp::BatchFinish => match vs.get(2) {
            Some(MiniValue::Batch(rev_items)) => {
                let mut out = rev_items.clone();
                out.reverse();
                MiniValue::Batch(out)
            }
            _ => MiniValue::Batch(Vec::new()),
        },
    }
}

/// Zero-clone `O(1)` amortized in-place stack reducer for `MiniOp`.
fn eval_mini_op_in_place(op: &MiniOp, vstk: &mut Vec<MiniValue>, k: usize) {
    let base = vstk.len() - k;
    match *op {
        MiniOp::UnitOp => {
            vstk.truncate(base);
            vstk.push(MiniValue::Unit);
        }
        MiniOp::PassAt(i) => {
            let v = if base + i < vstk.len() {
                std::mem::replace(&mut vstk[base + i], MiniValue::Unit)
            } else {
                MiniValue::Unit
            };
            vstk.truncate(base);
            vstk.push(v);
        }
        MiniOp::CharsNil => {
            vstk.truncate(base);
            vstk.push(MiniValue::Bytes(Vec::new()));
        }
        MiniOp::CharsCons(b) => {
            let mut tail = match std::mem::replace(&mut vstk[base + 1], MiniValue::Unit) {
                MiniValue::Bytes(v) => v,
                _ => Vec::new(),
            };
            tail.push(b);
            vstk.truncate(base);
            vstk.push(MiniValue::Bytes(tail));
        }
        MiniOp::CharsEsc => {
            let esc_b = match vstk[base + 1] {
                MiniValue::Byte(b) => b,
                _ => 0,
            };
            let mut tail = match std::mem::replace(&mut vstk[base + 2], MiniValue::Unit) {
                MiniValue::Bytes(v) => v,
                _ => Vec::new(),
            };
            tail.push(esc_b);
            vstk.truncate(base);
            vstk.push(MiniValue::Bytes(tail));
        }
        MiniOp::StrUnquote => {
            let mut chars = match std::mem::replace(&mut vstk[base + 1], MiniValue::Unit) {
                MiniValue::Bytes(v) => v,
                _ => Vec::new(),
            };
            chars.reverse();
            vstk.truncate(base);
            vstk.push(MiniValue::Bytes(chars));
        }
        MiniOp::EscConst(b) => {
            vstk.truncate(base);
            vstk.push(MiniValue::Byte(b));
        }
        MiniOp::NatZero => {
            vstk.truncate(base);
            vstk.push(MiniValue::Nat(ExactNat::ZERO));
        }
        MiniOp::DigitsNil => {
            vstk.truncate(base);
            vstk.push(MiniValue::Digits(Vec::new()));
        }
        MiniOp::DigitsCons(d) => {
            let mut ds = match std::mem::replace(&mut vstk[base + 1], MiniValue::Unit) {
                MiniValue::Digits(v) => v,
                _ => Vec::new(),
            };
            ds.push(d);
            vstk.truncate(base);
            vstk.push(MiniValue::Digits(ds));
        }
        MiniOp::NatPos(d0) => {
            let n = match &vstk[base + 1] {
                MiniValue::Digits(rev_ds) => ExactNat::from_decimal_digits_rev(d0, rev_ds),
                _ => ExactNat::from_u64(d0 as u64),
            };
            vstk.truncate(base);
            vstk.push(MiniValue::Nat(n));
        }
        MiniOp::MkToolRest => {
            let t = std::mem::replace(&mut vstk[base + 7], MiniValue::Unit);
            let tgt = std::mem::replace(&mut vstk[base + 22], MiniValue::Unit);
            let amt = std::mem::replace(&mut vstk[base + 37], MiniValue::Unit);
            let out = match (t, tgt, amt) {
                (MiniValue::Bytes(tool), MiniValue::Bytes(target), MiniValue::Nat(amount)) => {
                    MiniValue::ToolCall {
                        tool,
                        target,
                        amount,
                    }
                }
                _ => MiniValue::Unit,
            };
            vstk.truncate(base);
            vstk.push(out);
        }
        MiniOp::MkCotRest => {
            let c = std::mem::replace(&mut vstk[base + 6], MiniValue::Unit);
            let t = std::mem::replace(&mut vstk[base + 19], MiniValue::Unit);
            let tgt = std::mem::replace(&mut vstk[base + 34], MiniValue::Unit);
            let amt = std::mem::replace(&mut vstk[base + 49], MiniValue::Unit);
            let out = match (c, t, tgt, amt) {
                (
                    MiniValue::Bytes(cot),
                    MiniValue::Bytes(tool),
                    MiniValue::Bytes(target),
                    MiniValue::Nat(amount),
                ) => MiniValue::CotToolCall {
                    cot,
                    tool,
                    target,
                    amount,
                },
                _ => MiniValue::Unit,
            };
            vstk.truncate(base);
            vstk.push(out);
        }
        MiniOp::BatchEmpty => {
            vstk.truncate(base);
            vstk.push(MiniValue::Batch(Vec::new()));
        }
        MiniOp::BatchCons => {
            let item_idx = if k == 3 { base } else { base + 2 };
            let rest_idx = base + k - 1;
            let item = std::mem::replace(&mut vstk[item_idx], MiniValue::Unit);
            let mut rest = match std::mem::replace(&mut vstk[rest_idx], MiniValue::Unit) {
                MiniValue::Batch(v) => v,
                _ => Vec::new(),
            };
            rest.push(item);
            vstk.truncate(base);
            vstk.push(MiniValue::Batch(rest));
        }
        MiniOp::BatchFinish => {
            let mut items = match std::mem::replace(&mut vstk[base + 2], MiniValue::Unit) {
                MiniValue::Batch(v) => v,
                _ => Vec::new(),
            };
            items.reverse();
            vstk.truncate(base);
            vstk.push(MiniValue::Batch(items));
        }
    }
}

fn lit_syms<NT: Copy>(s: &[u8]) -> Vec<CfgSym<u8, NT>> {
    s.iter().map(|&b| CfgSym::Terminal(b)).collect()
}

/// Construct the exact 139-rule `miniJsonCfg` matching Lean's rule index order 1-for-1.
pub fn mini_json_cfg() -> AttrCfg<u8, MiniNT, MiniOp, MiniValue> {
    use CfgSym::{Nonterminal as Nt, Terminal as T};
    use MiniNT::*;

    let mut tool_rest_rhs = Vec::new();
    tool_rest_rhs.extend(lit_syms(b"ool\""));
    tool_rest_rhs.extend([Nt(WS), T(b':'), Nt(WS), Nt(StrVal), Nt(WS), T(b','), Nt(WS)]);
    tool_rest_rhs.extend(lit_syms(b"\"target\""));
    tool_rest_rhs.extend([Nt(WS), T(b':'), Nt(WS), Nt(StrVal), Nt(WS), T(b','), Nt(WS)]);
    tool_rest_rhs.extend(lit_syms(b"\"amount\""));
    tool_rest_rhs.extend([Nt(WS), T(b':'), Nt(WS), Nt(NatVal), Nt(WS), T(b'}')]);

    let mut cot_rest_rhs = Vec::new();
    cot_rest_rhs.extend(lit_syms(b"ot\""));
    cot_rest_rhs.extend([Nt(WS), T(b':'), Nt(WS), Nt(StrVal), Nt(WS), T(b','), Nt(WS)]);
    cot_rest_rhs.extend(lit_syms(b"\"tool\""));
    cot_rest_rhs.extend([Nt(WS), T(b':'), Nt(WS), Nt(StrVal), Nt(WS), T(b','), Nt(WS)]);
    cot_rest_rhs.extend(lit_syms(b"\"target\""));
    cot_rest_rhs.extend([Nt(WS), T(b':'), Nt(WS), Nt(StrVal), Nt(WS), T(b','), Nt(WS)]);
    cot_rest_rhs.extend(lit_syms(b"\"amount\""));
    cot_rest_rhs.extend([Nt(WS), T(b':'), Nt(WS), Nt(NatVal), Nt(WS), T(b'}')]);

    let mut rules = vec![
        AttrRule { lhs: Root, rhs: vec![Nt(WS), Nt(TopExpr), Nt(WS)], op: MiniOp::PassAt(1) },
        AttrRule { lhs: TopExpr, rhs: vec![T(b'{'), Nt(WS), T(b'"'), Nt(ObjDispatch)], op: MiniOp::PassAt(3) },
        AttrRule { lhs: TopExpr, rhs: vec![T(b'['), Nt(WS), Nt(BatchBody), T(b']')], op: MiniOp::BatchFinish },
        AttrRule { lhs: ObjDispatch, rhs: vec![T(b't'), Nt(ToolRest)], op: MiniOp::PassAt(1) },
        AttrRule { lhs: ObjDispatch, rhs: vec![T(b'c'), Nt(CotRest)], op: MiniOp::PassAt(1) },
        AttrRule { lhs: ToolRest, rhs: tool_rest_rhs, op: MiniOp::MkToolRest },
        AttrRule { lhs: CotRest, rhs: cot_rest_rhs, op: MiniOp::MkCotRest },
        AttrRule { lhs: BatchBody, rhs: vec![Nt(TopExpr), Nt(WS), Nt(BatchTail)], op: MiniOp::BatchCons },
        AttrRule { lhs: BatchBody, rhs: vec![], op: MiniOp::BatchEmpty },
        AttrRule { lhs: BatchTail, rhs: vec![T(b','), Nt(WS), Nt(TopExpr), Nt(WS), Nt(BatchTail)], op: MiniOp::BatchCons },
        AttrRule { lhs: BatchTail, rhs: vec![], op: MiniOp::BatchEmpty },
        AttrRule { lhs: WS, rhs: vec![T(b' '), Nt(WS)], op: MiniOp::UnitOp },
        AttrRule { lhs: WS, rhs: vec![T(b'\t'), Nt(WS)], op: MiniOp::UnitOp },
        AttrRule { lhs: WS, rhs: vec![T(b'\n'), Nt(WS)], op: MiniOp::UnitOp },
        AttrRule { lhs: WS, rhs: vec![T(b'\r'), Nt(WS)], op: MiniOp::UnitOp },
        AttrRule { lhs: WS, rhs: vec![], op: MiniOp::UnitOp },
        AttrRule { lhs: StrVal, rhs: vec![T(b'"'), Nt(Chars), T(b'"')], op: MiniOp::StrUnquote },
        AttrRule { lhs: Chars, rhs: vec![T(b'\\'), Nt(Esc), Nt(Chars)], op: MiniOp::CharsEsc },
        AttrRule { lhs: Chars, rhs: vec![], op: MiniOp::CharsNil },
        AttrRule { lhs: Esc, rhs: vec![T(b'"')], op: MiniOp::EscConst(b'"') },
        AttrRule { lhs: Esc, rhs: vec![T(b'\\')], op: MiniOp::EscConst(b'\\') },
        AttrRule { lhs: Esc, rhs: vec![T(b'/')], op: MiniOp::EscConst(b'/') },
        AttrRule { lhs: Esc, rhs: vec![T(b'n')], op: MiniOp::EscConst(b'\n') },
        AttrRule { lhs: Esc, rhs: vec![T(b'r')], op: MiniOp::EscConst(b'\r') },
        AttrRule { lhs: Esc, rhs: vec![T(b't')], op: MiniOp::EscConst(b'\t') },
        AttrRule { lhs: NatVal, rhs: vec![T(b'0')], op: MiniOp::NatZero },
        AttrRule { lhs: Digits, rhs: vec![], op: MiniOp::DigitsNil },
    ];

    for k in 0..9u8 {
        let d = k + 1;
        rules.push(AttrRule {
            lhs: NatVal,
            rhs: vec![T(b'0' + d), Nt(Digits)],
            op: MiniOp::NatPos(d),
        });
    }
    for d in 0..10u8 {
        rules.push(AttrRule {
            lhs: Digits,
            rhs: vec![T(b'0' + d), Nt(Digits)],
            op: MiniOp::DigitsCons(d),
        });
    }
    for k in 0..95u8 {
        let b = 0x20 + k;
        if b != b'"' && b != b'\\' {
            rules.push(AttrRule {
                lhs: Chars,
                rhs: vec![T(b), Nt(Chars)],
                op: MiniOp::CharsCons(b),
            });
        }
    }

    AttrCfg {
        initial: Root,
        rules,
        term_val: MiniValue::Byte,
        eval_op: eval_mini_op,
        eval_in_place: Some(eval_mini_op_in_place),
    }
}

/// Cached compiled `O(1)`-dispatch LL(1) parser for `miniJsonCfg`.
pub fn compiled_mini_json_parser() -> &'static CompiledByteLl1Parser<MiniNT, MiniOp, MiniValue> {
    static PARSER: OnceLock<CompiledByteLl1Parser<MiniNT, MiniOp, MiniValue>> = OnceLock::new();
    PARSER.get_or_init(|| {
        CompiledByteLl1Parser::compile(mini_json_cfg(), 13, |nt| nt as usize)
            .expect("miniJsonCfg is kernel-proved LL(1)")
    })
}

/// Nonterminals and operators of the ambiguous duplicate-key splice grammar (`ambigMiniJsonCfg`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AmbigNT {
    Root = 0,
    ToolFields = 1,
    StrVal = 2,
    Chars = 3,
    NatVal = 4,
    Digits = 5,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AmbigOp {
    PassAt(usize),
    FirstWins,
    LastWins,
    SingleKey,
    StrUnq,
    CharsNil,
    CharsCons(u8),
    NatZero,
    NatPos(u8),
    DigitsNil,
    DigitsCons(u8),
}

fn eval_ambig_op(op: &AmbigOp, vs: &[MiniValue]) -> MiniValue {
    match *op {
        AmbigOp::PassAt(i) => vs.get(i).cloned().unwrap_or(MiniValue::Unit),
        AmbigOp::SingleKey => match (vs.get(7), vs.get(18), vs.get(29)) {
            (
                Some(MiniValue::Bytes(t)),
                Some(MiniValue::Bytes(tgt)),
                Some(MiniValue::Nat(n)),
            ) => MiniValue::ToolCall {
                tool: t.clone(),
                target: tgt.clone(),
                amount: n.clone(),
            },
            _ => MiniValue::Unit,
        },
        AmbigOp::FirstWins => match (vs.get(7), vs.get(27), vs.get(38)) {
            (
                Some(MiniValue::Bytes(t1)),
                Some(MiniValue::Bytes(tgt)),
                Some(MiniValue::Nat(n)),
            ) => MiniValue::ToolCall {
                tool: t1.clone(),
                target: tgt.clone(),
                amount: n.clone(),
            },
            _ => MiniValue::Unit,
        },
        AmbigOp::LastWins => match (vs.get(16), vs.get(27), vs.get(38)) {
            (
                Some(MiniValue::Bytes(t2)),
                Some(MiniValue::Bytes(tgt)),
                Some(MiniValue::Nat(n)),
            ) => MiniValue::ToolCall {
                tool: t2.clone(),
                target: tgt.clone(),
                amount: n.clone(),
            },
            _ => MiniValue::Unit,
        },
        AmbigOp::StrUnq => vs.get(1).cloned().unwrap_or_else(|| MiniValue::Bytes(Vec::new())),
        AmbigOp::CharsNil => MiniValue::Bytes(Vec::new()),
        AmbigOp::CharsCons(b) => match vs.get(1) {
            Some(MiniValue::Bytes(tail)) => {
                let mut out = Vec::with_capacity(1 + tail.len());
                out.push(b);
                out.extend_from_slice(tail);
                MiniValue::Bytes(out)
            }
            _ => MiniValue::Bytes(vec![b]),
        },
        AmbigOp::NatZero => MiniValue::Nat(ExactNat::ZERO),
        AmbigOp::NatPos(d0) => match vs.get(1) {
            Some(MiniValue::Digits(ds)) => MiniValue::Nat(ExactNat::from_decimal_digits(d0, ds)),
            _ => MiniValue::Nat(ExactNat::from_u64(d0 as u64)),
        },
        AmbigOp::DigitsNil => MiniValue::Digits(Vec::new()),
        AmbigOp::DigitsCons(d) => match vs.get(1) {
            Some(MiniValue::Digits(ds)) => {
                let mut out = Vec::with_capacity(1 + ds.len());
                out.push(d);
                out.extend_from_slice(ds);
                MiniValue::Digits(out)
            }
            _ => MiniValue::Digits(vec![d]),
        },
    }
}

/// Construct the exact 64-rule `ambigMiniJsonCfg` matching Lean's rule index order 1-for-1.
pub fn ambig_mini_json_cfg() -> AttrCfg<u8, AmbigNT, AmbigOp, MiniValue> {
    use AmbigNT::*;
    use CfgSym::{Nonterminal as Nt, Terminal as T};

    let mut single_rhs = Vec::new();
    single_rhs.extend(lit_syms(b"\"tool\":"));
    single_rhs.push(Nt(StrVal));
    single_rhs.extend(lit_syms(b",\"target\":"));
    single_rhs.push(Nt(StrVal));
    single_rhs.extend(lit_syms(b",\"amount\":"));
    single_rhs.push(Nt(NatVal));

    let mut dup_rhs = Vec::new();
    dup_rhs.extend(lit_syms(b"\"tool\":"));
    dup_rhs.push(Nt(StrVal));
    dup_rhs.extend(lit_syms(b",\"tool\":"));
    dup_rhs.push(Nt(StrVal));
    dup_rhs.extend(lit_syms(b",\"target\":"));
    dup_rhs.push(Nt(StrVal));
    dup_rhs.extend(lit_syms(b",\"amount\":"));
    dup_rhs.push(Nt(NatVal));

    let mut rules = vec![
        AttrRule { lhs: Root, rhs: vec![T(b'{'), Nt(ToolFields), T(b'}')], op: AmbigOp::PassAt(1) },
        AttrRule { lhs: ToolFields, rhs: single_rhs, op: AmbigOp::SingleKey },
        AttrRule { lhs: ToolFields, rhs: dup_rhs.clone(), op: AmbigOp::FirstWins },
        AttrRule { lhs: ToolFields, rhs: dup_rhs, op: AmbigOp::LastWins },
        AttrRule { lhs: StrVal, rhs: vec![T(b'"'), Nt(Chars), T(b'"')], op: AmbigOp::StrUnq },
        AttrRule { lhs: Chars, rhs: vec![], op: AmbigOp::CharsNil },
        AttrRule { lhs: NatVal, rhs: vec![T(b'0')], op: AmbigOp::NatZero },
        AttrRule { lhs: Digits, rhs: vec![], op: AmbigOp::DigitsNil },
    ];

    for k in 0..9u8 {
        let d = k + 1;
        rules.push(AttrRule {
            lhs: NatVal,
            rhs: vec![T(b'0' + d), Nt(Digits)],
            op: AmbigOp::NatPos(d),
        });
    }
    for d in 0..10u8 {
        rules.push(AttrRule {
            lhs: Digits,
            rhs: vec![T(b'0' + d), Nt(Digits)],
            op: AmbigOp::DigitsCons(d),
        });
    }
    for k in 0..26u8 {
        let b = b'a' + k;
        rules.push(AttrRule {
            lhs: Chars,
            rhs: vec![T(b), Nt(Chars)],
            op: AmbigOp::CharsCons(b),
        });
    }
    for k in 0..10u8 {
        let b = b'0' + k;
        rules.push(AttrRule {
            lhs: Chars,
            rhs: vec![T(b), Nt(Chars)],
            op: AmbigOp::CharsCons(b),
        });
    }
    rules.push(AttrRule {
        lhs: Chars,
        rhs: vec![T(b'_'), Nt(Chars)],
        op: AmbigOp::CharsCons(b'_'),
    });

    AttrCfg {
        initial: Root,
        rules,
        term_val: MiniValue::Byte,
        eval_op: eval_ambig_op,
        eval_in_place: None,
    }
}

// ============================================================================
// §4. Deterministic Multi-Pattern Secret-Redaction Transducer (`redact_bytes`)
// ============================================================================

/// Byte-level secret-redaction rule (`Theory.VerifiedAstTransducer.RedactRule UInt8`).
/// Matches Lean's 4-field `RedactRule` structure identically (no manual continuation flags).
#[derive(Clone)]
pub struct RedactRule {
    pub name: &'static str,
    pub pat: Vec<u8>,
    pub body_pred: fn(u8) -> bool,
    pub repl: Vec<u8>,
}

/// Check `OccursInPlain` (`P` occurs at some byte offset in `w`).
pub fn occurs_in_bytes(w: &[u8], pat: &[u8]) -> bool {
    if pat.is_empty() {
        return true;
    }
    w.windows(pat.len()).any(|win| win == pat)
}

/// Check `AbsentPlain` (`P` occurs at zero byte offsets in `w`).
pub fn absent_plain_bytes(w: &[u8], pat: &[u8]) -> bool {
    !occurs_in_bytes(w, pat)
}

/// Decidable no-boundary-recreation check (`Theory.VerifiedAstTransducer.SafeReplacement`).
pub fn safe_replacement(pat: &[u8], repl: &[u8]) -> bool {
    if repl.is_empty() || !absent_plain_bytes(repl, pat) {
        return false;
    }
    for k in 1..pat.len() {
        let p1 = &pat[..k];
        let p2 = &pat[k..];
        if repl.starts_with(p2) || p2.starts_with(repl) || repl.ends_with(p1) {
            return false;
        }
    }
    true
}

/// Policy-wide safety check (`Theory.VerifiedAstTransducer.allRulesSafe`).
pub fn all_rules_safe(rules: &[RedactRule]) -> bool {
    rules.iter().all(|rt| {
        !rt.pat.is_empty() && rules.iter().all(|r| safe_replacement(&rt.pat, &r.repl))
    })
}

#[inline]
pub fn is_api_key_body_byte(b: u8) -> bool {
    b.is_ascii_uppercase() || b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_' || b == b'-'
}

#[inline]
pub fn is_bearer_body_byte(b: u8) -> bool {
    is_api_key_body_byte(b) || b == b'.' || b == b'~' || b == b'+' || b == b'/' || b == b'='
}

#[inline]
pub fn is_pem_header_byte(b: u8) -> bool {
    b.is_ascii_uppercase() || b.is_ascii_digit() || b == b' ' || b == b'-'
}

#[inline]
pub fn no_continuation(_: u8) -> bool {
    false
}

/// Production 5-class secret-redaction policy (`Theory.VerifiedAstTransducer.defaultSecretRules`).
pub fn default_secret_rules() -> Vec<RedactRule> {
    vec![
        RedactRule {
            name: "api_key",
            pat: b"sk-".to_vec(),
            body_pred: is_api_key_body_byte,
            repl: b"[REDACTED_API_KEY]".to_vec(),
        },
        RedactRule {
            name: "bearer",
            pat: b"Bearer ".to_vec(),
            body_pred: is_bearer_body_byte,
            repl: b"[REDACTED_BEARER]".to_vec(),
        },
        RedactRule {
            name: "pem_key",
            pat: b"-----BEGIN ".to_vec(),
            body_pred: is_pem_header_byte,
            repl: b"[REDACTED_PEM]".to_vec(),
        },
        RedactRule {
            name: "template_open",
            pat: b"{{".to_vec(),
            body_pred: no_continuation,
            repl: b"[REDACTED_TPL]".to_vec(),
        },
        RedactRule {
            name: "github_pat",
            pat: b"ghp_".to_vec(),
            body_pred: is_api_key_body_byte,
            repl: b"[REDACTED_GH_PAT]".to_vec(),
        },
    ]
}

#[inline]
fn rule_match_len(rule: &RedactRule, rem: &[u8]) -> Option<usize> {
    if rule.pat.is_empty() || !rem.starts_with(&rule.pat) {
        return None;
    }
    let mut len = rule.pat.len();
    while len < rem.len() && (rule.body_pred)(rem[len]) {
        len += 1;
    }
    Some(len)
}

#[inline]
fn pick_longest_match<'a>(rules: &'a [RedactRule], rem: &[u8]) -> Option<(&'a [u8], usize)> {
    let mut best: Option<(&'a [u8], usize)> = None;
    for r in rules {
        if let Some(len) = rule_match_len(r, rem) {
            match best {
                None => best = Some((&r.repl, len)),
                Some((_, best_len)) if best_len < len => best = Some((&r.repl, len)),
                _ => {}
            }
        }
    }
    best
}

/// Fast compiled batch & streaming secret-redaction engine with 256-entry starter-byte filter
/// and automatically derived `rule_has_cont` (`∃ b:u8, (r.body_pred)(b)`).
pub struct CompiledRedactor {
    rules: Vec<RedactRule>,
    rule_has_cont: Vec<bool>,
    starter_byte: [bool; 256],
}

impl CompiledRedactor {
    pub fn new(rules: Vec<RedactRule>) -> Self {
        let mut starter_byte = [false; 256];
        let mut rule_has_cont = Vec::with_capacity(rules.len());
        for r in &rules {
            if let Some(&b0) = r.pat.first() {
                starter_byte[b0 as usize] = true;
            }
            rule_has_cont.push((0u8..=255).any(|b| (r.body_pred)(b)));
        }
        Self {
            rules,
            rule_has_cont,
            starter_byte,
        }
    }

    pub fn rules(&self) -> &[RedactRule] {
        &self.rules
    }

    /// Exact deterministic longest-match byte-stream sanitizer (`redactBytes`).
    /// Skips clean byte runs in `O(1)` per byte via `starter_byte`, copying clean slices in bulk.
    pub fn redact(&self, input: &[u8]) -> Vec<u8> {
        let mut out = Vec::with_capacity(input.len());
        let mut pos = 0usize;
        let mut clean_start = 0usize;

        while pos < input.len() {
            if !self.starter_byte[input[pos] as usize] {
                pos += 1;
                continue;
            }
            if let Some((repl, match_len)) = pick_longest_match(&self.rules, &input[pos..]) {
                if clean_start < pos {
                    out.extend_from_slice(&input[clean_start..pos]);
                }
                out.extend_from_slice(repl);
                pos += match_len;
                clean_start = pos;
            } else {
                pos += 1;
            }
        }
        if clean_start < input.len() {
            out.extend_from_slice(&input[clean_start..]);
        }
        out
    }

    /// Create a chunked streaming sanitizer guaranteed bit-identical to `self.redact(&full_bytes)`.
    pub fn streaming(&self) -> StreamingRedactor<'_> {
        let n_rules = self.rules.len();
        StreamingRedactor {
            engine: self,
            buf: Vec::with_capacity(256),
            pos: 0,
            cached_pos_valid: false,
            rule_state: vec![StreamRuleState::Unchecked; n_rules],
        }
    }
}

/// Cached compiled default 5-class policy redactor.
pub fn compiled_default_redactor() -> &'static CompiledRedactor {
    static REDACTOR: OnceLock<CompiledRedactor> = OnceLock::new();
    REDACTOR.get_or_init(|| CompiledRedactor::new(default_secret_rules()))
}

/// Convenience wrapper executing `Theory.VerifiedAstTransducer.redactBytes`.
pub fn redact_bytes(rules: &[RedactRule], input: &[u8]) -> Vec<u8> {
    CompiledRedactor::new(rules.to_vec()).redact(input)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StreamRuleState {
    Unchecked,
    Dead,
    PrefixPending,
    Growing { scanned_len: usize },
    Finalized { match_len: usize },
}

/// Stateful streaming chunked redactor handling arbitrary token/network chunk splits
/// with amortized `O(N)` incremental continuation scanning (never rescans already-verified
/// continuation bytes when small chunks arrive during a long secret run!).
pub struct StreamingRedactor<'a> {
    engine: &'a CompiledRedactor,
    buf: Vec<u8>,
    pos: usize,
    cached_pos_valid: bool,
    rule_state: Vec<StreamRuleState>,
}

impl<'a> StreamingRedactor<'a> {
    #[inline]
    fn reset_rule_states(&mut self) {
        if self.cached_pos_valid {
            self.rule_state.fill(StreamRuleState::Unchecked);
            self.cached_pos_valid = false;
        }
    }

    /// Feed a new chunk of raw agent bytes and append all finalized sanitized bytes to `out`.
    pub fn push_chunk(&mut self, chunk: &[u8], out: &mut Vec<u8>) {
        if chunk.is_empty() {
            return;
        }
        if self.pos > 0 && self.pos == self.buf.len() {
            self.buf.clear();
            self.pos = 0;
            self.reset_rule_states();
        }
        self.buf.extend_from_slice(chunk);

        let mut clean_run_start = self.pos;
        while self.pos < self.buf.len() {
            let b0 = self.buf[self.pos];
            if !self.engine.starter_byte[b0 as usize] {
                self.reset_rule_states();
                self.pos += 1;
                continue;
            }

            let rem = &self.buf[self.pos..];
            let mut need_more = false;
            let mut best: Option<(&[u8], usize)> = None;

            for (ri, r) in self.engine.rules.iter().enumerate() {
                if r.pat.is_empty() {
                    self.rule_state[ri] = StreamRuleState::Dead;
                    continue;
                }
                let st = if self.cached_pos_valid {
                    self.rule_state[ri]
                } else {
                    StreamRuleState::Unchecked
                };

                let next_st = match st {
                    StreamRuleState::Dead => StreamRuleState::Dead,
                    StreamRuleState::Finalized { match_len } => {
                        StreamRuleState::Finalized { match_len }
                    }
                    StreamRuleState::Unchecked | StreamRuleState::PrefixPending => {
                        if rem.len() < r.pat.len() {
                            if r.pat.starts_with(rem) {
                                StreamRuleState::PrefixPending
                            } else {
                                StreamRuleState::Dead
                            }
                        } else if rem.starts_with(&r.pat) {
                            if !self.engine.rule_has_cont[ri] {
                                StreamRuleState::Finalized {
                                    match_len: r.pat.len(),
                                }
                            } else {
                                let mut len = r.pat.len();
                                while len < rem.len() && (r.body_pred)(rem[len]) {
                                    len += 1;
                                }
                                if len == rem.len() {
                                    StreamRuleState::Growing { scanned_len: len }
                                } else {
                                    StreamRuleState::Finalized { match_len: len }
                                }
                            }
                        } else {
                            StreamRuleState::Dead
                        }
                    }
                    StreamRuleState::Growing { scanned_len } => {
                        let mut len = scanned_len;
                        while len < rem.len() && (r.body_pred)(rem[len]) {
                            len += 1;
                        }
                        if len == rem.len() {
                            StreamRuleState::Growing { scanned_len: len }
                        } else {
                            StreamRuleState::Finalized { match_len: len }
                        }
                    }
                };
                self.rule_state[ri] = next_st;

                match next_st {
                    StreamRuleState::PrefixPending | StreamRuleState::Growing { .. } => {
                        need_more = true;
                    }
                    StreamRuleState::Finalized { match_len } => match best {
                        None => best = Some((&r.repl, match_len)),
                        Some((_, best_len)) if best_len < match_len => {
                            best = Some((&r.repl, match_len))
                        }
                        _ => {}
                    },
                    StreamRuleState::Dead | StreamRuleState::Unchecked => {}
                }
            }
            self.cached_pos_valid = true;

            if need_more {
                break;
            }

            self.reset_rule_states();
            if let Some((repl, match_len)) = best {
                if clean_run_start < self.pos {
                    out.extend_from_slice(&self.buf[clean_run_start..self.pos]);
                }
                out.extend_from_slice(repl);
                self.pos += match_len;
                clean_run_start = self.pos;
            } else {
                self.pos += 1;
            }
        }

        if clean_run_start < self.pos {
            out.extend_from_slice(&self.buf[clean_run_start..self.pos]);
        }

        if self.pos > 4096 {
            self.buf.drain(..self.pos);
            self.pos = 0;
            // Note: `self.rule_state` offsets inside `rem = &self.buf[self.pos..]` are relative to
            // `self.pos`, so draining `..self.pos` preserves `scanned_len` & `match_len` identically!
        }
    }

    /// Flush EOF and append any remaining buffered bytes (sanitized) to `out`.
    pub fn finish(mut self, out: &mut Vec<u8>) {
        if self.pos < self.buf.len() {
            let tail = self.engine.redact(&self.buf[self.pos..]);
            out.extend_from_slice(&tail);
            self.buf.clear();
            self.pos = 0;
        }
    }
}

// ============================================================================
// §5. Content-Bound `RewriteCert` Prover & Verifier (`PolicyAstTransducerEmit`)
// ============================================================================

/// Public `RewriteCert` statement (`Compiler.PolicyAstTransducerEmit.RewriteCertStmt`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RewriteCertStmt<Val> {
    pub raw_root: Digest32,
    pub raw_length: usize,
    pub clean_root: Digest32,
    pub clean_length: usize,
    pub claimed_ast: Val,
}

/// Witness for `RewriteCertStmt` (`Compiler.PolicyAstTransducerEmit.RewriteCertWitness`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RewriteCertWitness {
    pub w_raw: Vec<u8>,
    pub w_clean: Vec<u8>,
    pub rule_indices: Vec<usize>,
}

/// Honest prover for `Mini` JSON policy sanitization + `cSHAKE256` commitment + LL(1) AST extraction.
pub fn prove_mini_rewrite_and_extract(
    redactor: &CompiledRedactor,
    parser: &CompiledByteLl1Parser<MiniNT, MiniOp, MiniValue>,
    w_raw: &[u8],
) -> Result<(RewriteCertStmt<MiniValue>, RewriteCertWitness), TransducerError> {
    if !all_rules_safe(redactor.rules()) {
        return Err(TransducerError::UnsafeRedactionRules);
    }
    let w_clean = redactor.redact(w_raw);
    let (rule_indices, claimed_ast) = parser.parse(&w_clean)?;
    let raw_root = content_commit(w_raw);
    let clean_root = content_commit(&w_clean);
    let stmt = RewriteCertStmt {
        raw_root,
        raw_length: w_raw.len(),
        clean_root,
        clean_length: w_clean.len(),
        claimed_ast,
    };
    let wit = RewriteCertWitness {
        w_raw: w_raw.to_vec(),
        w_clean,
        rule_indices,
    };
    Ok((stmt, wit))
}

/// Differential-test oracle for `Compiler.PolicyAstTransducerEmit.verifyRewriteAndExtract`,
/// which owns admission of RewriteCert statements.
#[doc(hidden)]
pub fn verify_rewrite_and_extract_conformance_only<NT, SemOp, Val>(
    cfg: &AttrCfg<u8, NT, SemOp, Val>,
    rules: &[RedactRule],
    stmt: &RewriteCertStmt<Val>,
    wit: &RewriteCertWitness,
) -> Result<(), TransducerError>
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: Clone,
    Val: PartialEq,
{
    if !ll1_deterministic(cfg) {
        return Err(TransducerError::GrammarNotLl1);
    }
    if !all_rules_safe(rules) {
        return Err(TransducerError::UnsafeRedactionRules);
    }
    if wit.w_raw.len() != stmt.raw_length {
        return Err(TransducerError::RawLengthMismatch {
            expected: stmt.raw_length,
            actual: wit.w_raw.len(),
        });
    }
    if content_commit(&wit.w_raw) != stmt.raw_root {
        return Err(TransducerError::RawRootMismatch);
    }
    if wit.w_clean.len() != stmt.clean_length {
        return Err(TransducerError::CleanLengthMismatch {
            expected: stmt.clean_length,
            actual: wit.w_clean.len(),
        });
    }
    if content_commit(&wit.w_clean) != stmt.clean_root {
        return Err(TransducerError::CleanRootMismatch);
    }
    let expected_clean = redact_bytes(rules, &wit.w_raw);
    if wit.w_clean != expected_clean {
        return Err(TransducerError::RedactionMismatch);
    }
    let extracted = exec_attr_replay(cfg, &wit.rule_indices, &wit.w_clean)?;
    if extracted != stmt.claimed_ast {
        return Err(TransducerError::AstMismatch);
    }
    Ok(())
}
