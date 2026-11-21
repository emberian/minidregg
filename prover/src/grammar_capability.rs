//! Grammar-typed capabilities, decidable DFA/LL(1) sublanguage attenuation, and sealed
//! `Hyperdocument` blinded-patch gate.
//!
//! Mirrors the kernel-verified Lean 4.35.0 specifications in:
//! - `Theory/GrammarTypedCapability.lean` (`DfaSpec`, `ReachSafe`, `dfaSublanguageDecide`,
//!   `dfaCounterexample?`, `AutomatonBound`, `automatonBoundEntails`, `GrammarPolicy`,
//!   `grammarPolicyAttenuates`, `policyChainAttenuates`, `rootCapPolicy -> serviceCapPolicy -> subagentToolCapPolicy`),
//! - `Assurance/SealedHyperdocGrammarGate.lean` (`SealedHyperdocPatchStmt`, `checkSealedAtomEdit`,
//!   `checkDelegatedCapChain`, `verifySealedHyperdocPatch`, `SuccinctGuardBundle`).

use std::collections::HashSet;
use std::fmt;
use std::hash::Hash;

use crate::hash_kernels::cshake256_xof;
use crate::policy_transducer::{
    all_rules_safe, exec_attr_replay, is_api_key_body_byte, is_bearer_body_byte, ll1_deterministic,
    AttrCfg, AttrRule, CfgSym, CompiledByteLl1Parser, CompiledRedactor, ExactNat, MiniValue,
    RedactRule, TransducerError,
};
use crate::tower256_private_cert::{
    automaton_commit, decode_private_cert, encode_private_cert, encode_private_receipt,
    prove_private_with_randomness, salted_content_commit, verify_private_cert_bytes, ClaimData,
    DfaTable, Digest, PrivateCertError, RowMask, Salt248,
};

// ============================================================================
// §1. Errors & Core Product-DFA Inclusion / Shortest-Counterexample Solver
// ============================================================================

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CapabilityError {
    InvalidDfa(PrivateCertError),
    StateProductOverflow,
    PrivateCert(PrivateCertError),
    Transducer(TransducerError),
    MalformedBundle(&'static str),
}

impl fmt::Display for CapabilityError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidDfa(e) => write!(f, "invalid DFA specification: {e}"),
            Self::StateProductOverflow => write!(f, "product DFA state space overflow"),
            Self::PrivateCert(e) => write!(f, "private content certificate error: {e}"),
            Self::Transducer(e) => write!(f, "AST/redaction transducer error: {e}"),
            Self::MalformedBundle(msg) => write!(f, "malformed public gate bundle: {msg}"),
        }
    }
}

impl std::error::Error for CapabilityError {}

impl From<PrivateCertError> for CapabilityError {
    fn from(e: PrivateCertError) -> Self {
        Self::PrivateCert(e)
    }
}

impl From<TransducerError> for CapabilityError {
    fn from(e: TransducerError) -> Self {
        Self::Transducer(e)
    }
}

/// Verified inductive reachability certificate (`Theory.GrammarTypedCapability.ReachSafe`):
/// stores all reachable `(child_state, parent_state)` pairs in `child x parent`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProductReachabilityCert {
    pub reachable_pairs: Vec<(usize, usize)>,
}

/// Outcome of deciding $L(\text{child}) \subseteq L(\text{parent})$.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SublanguageResult {
    /// $L(\text{child}) \subseteq L(\text{parent})$ holds, witnessed by `ReachSafe`.
    Included(ProductReachabilityCert),
    /// $L(\text{child}) \not\subseteq L(\text{parent})$, witnessed by the **unique shortest,
    /// lexicographically smallest** byte string $w \in L(\text{child}) \setminus L(\text{parent})$.
    Counterexample(Vec<u8>),
}

impl SublanguageResult {
    #[inline]
    pub fn is_included(&self) -> bool {
        matches!(self, Self::Included(_))
    }

    pub fn counterexample(&self) -> Option<&[u8]> {
        match self {
            Self::Included(_) => None,
            Self::Counterexample(w) => Some(w),
        }
    }
}

#[derive(Clone, Copy)]
struct BfsNode {
    sc: u32,
    sp: u32,
    parent_idx: u32,
    via_byte: u8,
}

/// Maximum product-DFA state space (`4,194,304` pairs) permitted during BFS/certificate checks.
pub const MAX_PRODUCT_STATES: usize = 4_194_304;

/// Decide $L(\text{child}) \subseteq L(\text{parent})$ via exact FIFO breadth-first search over
/// bytes `0u8..=255u8`.
///
/// - If included, returns `SublanguageResult::Included(ProductReachabilityCert)`.
/// - If violated, returns `SublanguageResult::Counterexample(w)` where `w` is guaranteed to be
///   the **shortest, lexicographically smallest** byte string accepted by `child` and rejected
///   by `parent`.
pub fn check_dfa_sublanguage(
    child: &DfaTable,
    parent: &DfaTable,
) -> Result<SublanguageResult, CapabilityError> {
    child.validate().map_err(CapabilityError::InvalidDfa)?;
    parent.validate().map_err(CapabilityError::InvalidDfa)?;

    let prod_states = child
        .states
        .checked_mul(parent.states)
        .filter(|&n| n <= MAX_PRODUCT_STATES)
        .ok_or(CapabilityError::StateProductOverflow)?;

    let mut visited = vec![false; prod_states];
    let mut queue: Vec<BfsNode> = Vec::with_capacity(prod_states.min(4096));

    let init_id = child.initial * parent.states + parent.initial;
    visited[init_id] = true;
    queue.push(BfsNode {
        sc: child.initial as u32,
        sp: parent.initial as u32,
        parent_idx: u32::MAX,
        via_byte: 0,
    });

    let mut head = 0usize;
    while head < queue.len() {
        let cur = queue[head];
        let sc = cur.sc as usize;
        let sp = cur.sp as usize;

        if child.accepting[sc] && !parent.accepting[sp] {
            let mut rev_word = Vec::new();
            let mut cursor = head as u32;
            while queue[cursor as usize].parent_idx != u32::MAX {
                let node = queue[cursor as usize];
                rev_word.push(node.via_byte);
                cursor = node.parent_idx;
            }
            rev_word.reverse();
            return Ok(SublanguageResult::Counterexample(rev_word));
        }

        let row_c = &child.delta[256 * sc..256 * sc + 256];
        let row_p = &parent.delta[256 * sp..256 * sp + 256];
        for b in 0usize..256 {
            let nxc = row_c[b];
            let nxp = row_p[b];
            let nxt_id = nxc * parent.states + nxp;
            if !visited[nxt_id] {
                visited[nxt_id] = true;
                queue.push(BfsNode {
                    sc: nxc as u32,
                    sp: nxp as u32,
                    parent_idx: head as u32,
                    via_byte: b as u8,
                });
            }
        }
        head += 1;
    }

    let reachable_pairs = queue
        .iter()
        .map(|n| (n.sc as usize, n.sp as usize))
        .collect();
    Ok(SublanguageResult::Included(ProductReachabilityCert {
        reachable_pairs,
    }))
}

/// Independently verify a `ProductReachabilityCert` (`ReachSafe` invariant check in `O(|cert| * 256)`).
/// Rejects duplicate pairs and state products exceeding `MAX_PRODUCT_STATES`.
pub fn verify_reachability_cert(
    cert: &ProductReachabilityCert,
    child: &DfaTable,
    parent: &DfaTable,
) -> bool {
    if child.validate().is_err() || parent.validate().is_err() {
        return false;
    }
    let Some(prod_states) = child
        .states
        .checked_mul(parent.states)
        .filter(|&n| n <= MAX_PRODUCT_STATES)
    else {
        return false;
    };
    let mut in_cert = vec![false; prod_states];
    for &(sc, sp) in &cert.reachable_pairs {
        if sc >= child.states || sp >= parent.states {
            return false;
        }
        if child.accepting[sc] && !parent.accepting[sp] {
            return false;
        }
        let idx = sc * parent.states + sp;
        if in_cert[idx] {
            return false;
        }
        in_cert[idx] = true;
    }
    if !in_cert[child.initial * parent.states + parent.initial] {
        return false;
    }
    for &(sc, sp) in &cert.reachable_pairs {
        let row_c = &child.delta[256 * sc..256 * sc + 256];
        let row_p = &parent.delta[256 * sp..256 * sp + 256];
        for b in 0usize..256 {
            if !in_cert[row_c[b] * parent.states + row_p[b]] {
                return false;
            }
        }
    }
    true
}

/// Reachable product-DFA language intersection $L(a) \cap L(b)$ (`states <= max_states`, `<= 65536`).
pub fn dfa_intersection(a: &DfaTable, b: &DfaTable, max_states: usize) -> Option<DfaTable> {
    if a.validate().is_err() || b.validate().is_err() {
        return None;
    }
    let cap = max_states.min(65_536);
    let prod = a.states.checked_mul(b.states)?;
    if prod > MAX_PRODUCT_STATES {
        return None;
    }
    let mut state_map = vec![usize::MAX; prod];
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    let init_pair = a.initial * b.states + b.initial;
    state_map[init_pair] = 0;
    pairs.push((a.initial, b.initial));

    let mut delta: Vec<usize> = Vec::new();
    let mut head = 0usize;
    while head < pairs.len() {
        let (sa, sb) = pairs[head];
        let row_a = &a.delta[256 * sa..256 * sa + 256];
        let row_b = &b.delta[256 * sb..256 * sb + 256];
        let base = delta.len();
        delta.resize(base + 256, 0);
        for byte in 0..256usize {
            let na = row_a[byte];
            let nb = row_b[byte];
            let pid = na * b.states + nb;
            let nxt = if state_map[pid] != usize::MAX {
                state_map[pid]
            } else {
                let id = pairs.len();
                if id >= cap {
                    return None;
                }
                state_map[pid] = id;
                pairs.push((na, nb));
                id
            };
            delta[base + byte] = nxt;
        }
        head += 1;
    }
    let accepting = pairs
        .iter()
        .map(|&(sa, sb)| a.accepting[sa] && b.accepting[sb])
        .collect();
    Some(DfaTable {
        states: pairs.len(),
        initial: 0,
        accepting,
        delta,
    })
}

/// Language complement DFA (`Theory.GrammarTypedCapability.DfaSpec.complement`).
pub fn dfa_complement(dfa: &DfaTable) -> DfaTable {
    DfaTable {
        states: dfa.states,
        initial: dfa.initial,
        accepting: dfa.accepting.iter().map(|&b| !b).collect(),
        delta: dfa.delta.clone(),
    }
}

// ============================================================================
// §2. Policy DFAs, `AutomatonBound`, & Decidable Guard Entailment
// ============================================================================

/// 1-state universal DFA accepting all byte strings $\Sigma^*$.
pub fn dfa_accept_all() -> DfaTable {
    DfaTable {
        states: 1,
        initial: 0,
        accepting: vec![true],
        delta: vec![0usize; 256],
    }
}

/// 6-state padded-complement DFA `Absent("DROP ")` (`noSqlDropDfa` in Lean).
pub fn dfa_no_sql_drop() -> DfaTable {
    let states = 6;
    let mut delta = vec![0usize; states * 256];
    for s in 0..states {
        for b in 0..256usize {
            delta[256 * s + b] = if s == 5 {
                5
            } else if s == 4 && b == usize::from(b' ') {
                5
            } else if s == 3 && b == usize::from(b'P') {
                4
            } else if s == 2 && b == usize::from(b'O') {
                3
            } else if s == 1 && b == usize::from(b'R') {
                2
            } else if b == usize::from(b'D') {
                1
            } else {
                0
            };
        }
    }
    DfaTable {
        states,
        initial: 0,
        accepting: vec![true, true, true, true, true, false],
        delta,
    }
}

/// 3-state padded-complement DFA `Absent("$(")` (`noShellSubDfa` in Lean).
pub fn dfa_no_shell_sub() -> DfaTable {
    let states = 3;
    let mut delta = vec![0usize; states * 256];
    for s in 0..states {
        for b in 0..256usize {
            delta[256 * s + b] = if s == 2 {
                2
            } else if s == 1 && b == usize::from(b'(') {
                2
            } else if b == usize::from(b'$') {
                1
            } else {
                0
            };
        }
    }
    DfaTable {
        states,
        initial: 0,
        accepting: vec![true, true, false],
        delta,
    }
}

/// 2-state JSON object-brace `'{'` operation counter (`countOpBraceDfa` in Lean).
pub fn dfa_count_op_brace() -> DfaTable {
    let states = 2;
    let mut delta = vec![0usize; states * 256];
    for s in 0..states {
        for b in 0..256usize {
            delta[256 * s + b] = usize::from(b == usize::from(b'{'));
        }
    }
    DfaTable {
        states,
        initial: 0,
        accepting: vec![false, true],
        delta,
    }
}

/// 5-mode automaton guard (`Theory.GrammarTypedCapability.AutomatonBound`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AutomatonBound {
    MustAccept(DfaTable),
    MustReject(DfaTable),
    MaxHits { dfa: DfaTable, hi: u64 },
    ExactHits { dfa: DfaTable, n: u64 },
    RangeHits { dfa: DfaTable, lo: u64, hi: u64 },
}

impl AutomatonBound {
    pub fn dfa(&self) -> &DfaTable {
        match self {
            Self::MustAccept(d)
            | Self::MustReject(d)
            | Self::MaxHits { dfa: d, .. }
            | Self::ExactHits { dfa: d, .. }
            | Self::RangeHits { dfa: d, .. } => d,
        }
    }

    pub fn well_formed(&self) -> bool {
        if self.dfa().validate().is_err() {
            return false;
        }
        match self {
            Self::RangeHits { lo, hi, .. } => lo <= hi,
            _ => true,
        }
    }

    pub fn holds(&self, word: &[u8]) -> bool {
        match self {
            Self::MustAccept(d) => d.accepts(word),
            Self::MustReject(d) => !d.accepts(word),
            Self::MaxHits { dfa, hi } => dfa.run_count(word) <= *hi,
            Self::ExactHits { dfa, n } => dfa.run_count(word) == *n,
            Self::RangeHits { dfa, lo, hi } => {
                let c = dfa.run_count(word);
                *lo <= c && c <= *hi
            }
        }
    }

    /// Canonical mapping to `Tower256ContentCert.ClaimData` (`boundToClaim` in Lean).
    pub fn to_claim_data(&self) -> ClaimData {
        match self {
            Self::MustAccept(_) => ClaimData::Accept(true),
            Self::MustReject(_) => ClaimData::Accept(false),
            Self::MaxHits { hi, .. } => ClaimData::Bound { lo: 0, hi: *hi },
            Self::ExactHits { n, .. } => ClaimData::Count(*n),
            Self::RangeHits { lo, hi, .. } => ClaimData::Bound { lo: *lo, hi: *hi },
        }
    }

    fn to_accept_dfa(&self) -> Option<DfaTable> {
        match self {
            Self::MustAccept(d) => Some(d.clone()),
            Self::MustReject(d) => Some(dfa_complement(d)),
            _ => None,
        }
    }

    fn count_interval(&self) -> Option<(&DfaTable, u64, u64)> {
        match self {
            Self::MaxHits { dfa, hi } => Some((dfa, 0, *hi)),
            Self::ExactHits { dfa, n } => Some((dfa, *n, *n)),
            Self::RangeHits { dfa, lo, hi } => Some((dfa, *lo, *hi)),
            _ => None,
        }
    }
}

/// Exact mirror of `Theory.GrammarTypedCapability.automatonBoundEntails`.
pub fn automaton_bound_entails(child: &AutomatonBound, parent: &AutomatonBound) -> bool {
    if !child.well_formed() || !parent.well_formed() {
        return false;
    }
    if let (Some(dc), Some(dp)) = (child.to_accept_dfa(), parent.to_accept_dfa()) {
        return check_dfa_sublanguage(&dc, &dp)
            .map(|r| r.is_included())
            .unwrap_or(false);
    }
    if let (Some((dc, lo_c, hi_c)), Some((dp, lo_p, hi_p))) =
        (child.count_interval(), parent.count_interval())
    {
        if lo_p == 0 {
            return hi_c <= hi_p
                && check_dfa_sublanguage(dp, dc)
                    .map(|r| r.is_included())
                    .unwrap_or(false);
        }
        return lo_p <= lo_c
            && hi_c <= hi_p
            && check_dfa_sublanguage(dc, dp)
                .map(|r| r.is_included())
                .unwrap_or(false)
            && check_dfa_sublanguage(dp, dc)
                .map(|r| r.is_included())
                .unwrap_or(false);
    }
    false
}

/// Guard-list attenuation (`Theory.GrammarTypedCapability.boundsAttenuate`).
pub fn bounds_attenuate(child_bounds: &[AutomatonBound], parent_bounds: &[AutomatonBound]) -> bool {
    child_bounds.iter().all(AutomatonBound::well_formed)
        && parent_bounds.iter().all(AutomatonBound::well_formed)
        && parent_bounds
            .iter()
            .all(|bp| child_bounds.iter().any(|bc| automaton_bound_entails(bc, bp)))
}

// ============================================================================
// §3. `GrammarPolicy`, Diagnostic Escalation Witness, & `grammar_policy_attenuates`
// ============================================================================

#[inline]
fn occurs_in_bytes(haystack: &[u8], needle: &[u8]) -> bool {
    if needle.is_empty() {
        return true;
    }
    haystack.windows(needle.len()).any(|w| w == needle)
}

/// Redaction-policy attenuation (`Theory.GrammarTypedCapability.redactRulesAttenuate`).
pub fn redact_rules_attenuate(child_rules: &[RedactRule], parent_rules: &[RedactRule]) -> bool {
    all_rules_safe(child_rules)
        && all_rules_safe(parent_rules)
        && parent_rules.iter().all(|rp| {
            child_rules
                .iter()
                .any(|rc| occurs_in_bytes(&rp.pat, &rc.pat))
        })
}

/// Syntactic & automata-predicated capability policy (`Theory.GrammarTypedCapability.GrammarPolicy`).
pub struct GrammarPolicy<NT, SemOp, Val> {
    pub semantics_id: &'static str,
    pub grammar: AttrCfg<u8, NT, SemOp, Val>,
    pub redact_rules: Vec<RedactRule>,
    pub bounds: Vec<AutomatonBound>,
}

/// Detailed diagnostic reason when `check_policy_attenuation` refuses an escalation attempt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AttenuationRefusal {
    SemanticsMismatch {
        child: &'static str,
        parent: &'static str,
    },
    ChildGrammarNotLl1,
    ParentGrammarNotLl1,
    InitialNonterminalMismatch,
    UnauthorizedProductionRule {
        child_rule_index: usize,
    },
    RedactPolicyNotAttenuated,
    MalformedAutomatonBound,
    UnentailedParentBound {
        parent_bound_index: usize,
        shortest_counterexample: Option<Vec<u8>>,
    },
}

impl<NT, SemOp, Val> GrammarPolicy<NT, SemOp, Val>
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: PartialEq + Clone,
{
    pub fn well_formed(&self) -> bool {
        ll1_deterministic(&self.grammar)
            && all_rules_safe(&self.redact_rules)
            && self.bounds.iter().all(AutomatonBound::well_formed)
    }
}

/// Detailed capability attenuation check returning `Ok(())` iff `grammarPolicyAttenuates = true`,
/// or a structured `AttenuationRefusal` (including the shortest counterexample $w$ when an
/// acceptance/rejection guard such as `Absent("sk-")` is dropped or weakened!).
pub fn check_policy_attenuation<NT, SemOp, Val>(
    child: &GrammarPolicy<NT, SemOp, Val>,
    parent: &GrammarPolicy<NT, SemOp, Val>,
) -> Result<(), AttenuationRefusal>
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: PartialEq + Clone,
{
    let same_eval_in_place = match (child.grammar.eval_in_place, parent.grammar.eval_in_place) {
        (None, None) => true,
        (Some(fc), Some(fp)) => std::ptr::fn_addr_eq(fc, fp),
        _ => false,
    };
    if child.semantics_id != parent.semantics_id
        || !std::ptr::fn_addr_eq(child.grammar.term_val, parent.grammar.term_val)
        || !std::ptr::fn_addr_eq(child.grammar.eval_op, parent.grammar.eval_op)
        || !same_eval_in_place
    {
        return Err(AttenuationRefusal::SemanticsMismatch {
            child: child.semantics_id,
            parent: parent.semantics_id,
        });
    }
    if !ll1_deterministic(&child.grammar) {
        return Err(AttenuationRefusal::ChildGrammarNotLl1);
    }
    if !ll1_deterministic(&parent.grammar) {
        return Err(AttenuationRefusal::ParentGrammarNotLl1);
    }
    if child.grammar.initial != parent.grammar.initial {
        return Err(AttenuationRefusal::InitialNonterminalMismatch);
    }
    for (idx, r) in child.grammar.rules.iter().enumerate() {
        if !parent.grammar.rules.contains(r) {
            return Err(AttenuationRefusal::UnauthorizedProductionRule {
                child_rule_index: idx,
            });
        }
    }
    if !redact_rules_attenuate(&child.redact_rules, &parent.redact_rules) {
        return Err(AttenuationRefusal::RedactPolicyNotAttenuated);
    }
    if !child.bounds.iter().all(AutomatonBound::well_formed)
        || !parent.bounds.iter().all(AutomatonBound::well_formed)
    {
        return Err(AttenuationRefusal::MalformedAutomatonBound);
    }
    for (p_idx, bp) in parent.bounds.iter().enumerate() {
        if !child.bounds.iter().any(|bc| automaton_bound_entails(bc, bp)) {
            // Synthesize shortest lexicographic counterexample in (\bigcap_i L(dc_i)) \setminus L(dp):
            let shortest_counterexample = bp.to_accept_dfa().and_then(|dp| {
                let mut combined = dfa_accept_all();
                for bc in &child.bounds {
                    if let Some(dc) = bc.to_accept_dfa() {
                        combined = dfa_intersection(&combined, &dc, 65_536)?;
                    }
                }
                match check_dfa_sublanguage(&combined, &dp) {
                    Ok(SublanguageResult::Counterexample(w)) => Some(w),
                    _ => None,
                }
            });
            return Err(AttenuationRefusal::UnentailedParentBound {
                parent_bound_index: p_idx,
                shortest_counterexample,
            });
        }
    }
    Ok(())
}

/// Boolean capability attenuator (`Theory.GrammarTypedCapability.grammarPolicyAttenuates`).
pub fn grammar_policy_attenuates<NT, SemOp, Val>(
    child: &GrammarPolicy<NT, SemOp, Val>,
    parent: &GrammarPolicy<NT, SemOp, Val>,
) -> bool
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: PartialEq + Clone,
{
    check_policy_attenuation(child, parent).is_ok()
}

/// Multi-hop capability policy chain checker (`Theory.GrammarTypedCapability.policyChainAttenuates`).
pub fn policy_chain_attenuates<NT, SemOp, Val>(chain: &[&GrammarPolicy<NT, SemOp, Val>]) -> bool
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: PartialEq + Clone,
{
    match chain {
        [] => false,
        [single] => single.well_formed(),
        _ => chain
            .windows(2)
            .all(|pair| grammar_policy_attenuates(pair[1], pair[0]))
            && chain.last().unwrap().well_formed(),
    }
}

/// Verify `PolicyAdmits` (`execPolicyVerify` in Lean).
pub fn verify_policy_admits<NT, SemOp, Val>(
    policy: &GrammarPolicy<NT, SemOp, Val>,
    payload: &[u8],
    rule_indices: &[usize],
    claimed_ast: &Val,
) -> bool
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: PartialEq + Clone,
    Val: PartialEq,
{
    if !policy.well_formed() {
        return false;
    }
    let scrubbed = CompiledRedactor::new(policy.redact_rules.clone()).redact(payload);
    if scrubbed.as_slice() != payload {
        return false;
    }
    if !policy.bounds.iter().all(|b| b.holds(payload)) {
        return false;
    }
    match exec_attr_replay(&policy.grammar, rule_indices, payload) {
        Ok(ast) => &ast == claimed_ast,
        Err(_) => false,
    }
}

// ============================================================================
// §4. Exact Mirror of Lean's 3-Hop Capability Hierarchy (`CapNT`, `CapOp`)
// ============================================================================

pub const CAP_SEMANTICS_ID: &str = "minidregg/cap_semantics/v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CapNT {
    Root = 0,
    Expr = 1,
    AfterCommaT = 2,
    BatchTail = 3,
    ToolName = 4,
    TargetPath = 5,
    Slug = 6,
    BoundedAmt = 7,
    AmtTail1 = 8,
    AmtTail2 = 9,
    WS = 10,
}

impl CapNT {
    pub const COUNT: usize = 11;

    #[inline]
    pub fn to_id(self) -> usize {
        self as usize
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CapOp {
    PassAt(usize),
    UnitOp,
    ConstBytes(Vec<u8>),
    PrefixSlug(Vec<u8>),
    SlugNil,
    SlugCons(u8),
    NatZero,
    AmtHead(u8),
    DigitsNil,
    DigitsCons(u8),
    DigitsSingle(u8),
    MkExprObj,
    MkAfterNorm,
    MkDupFirst,
    MkDupLast,
    MkBatchHead,
    MkBatchTail,
    BatchNil,
}

fn cap_term_val(b: u8) -> MiniValue {
    MiniValue::Byte(b)
}

pub fn eval_cap_op(op: &CapOp, vs: &[MiniValue]) -> MiniValue {
    match op {
        CapOp::PassAt(i) => vs.get(*i).cloned().unwrap_or(MiniValue::Unit),
        CapOp::UnitOp => MiniValue::Unit,
        CapOp::ConstBytes(bs) => MiniValue::Bytes(bs.clone()),
        CapOp::PrefixSlug(pfx) => {
            let mut out = pfx.clone();
            if let Some(MiniValue::Bytes(slug)) = vs.last() {
                out.extend_from_slice(slug);
            }
            MiniValue::Bytes(out)
        }
        CapOp::SlugNil => MiniValue::Bytes(Vec::new()),
        CapOp::SlugCons(b) => match vs.get(1) {
            Some(MiniValue::Bytes(tail)) => {
                let mut out = Vec::with_capacity(1 + tail.len());
                out.push(*b);
                out.extend_from_slice(tail);
                MiniValue::Bytes(out)
            }
            _ => MiniValue::Bytes(vec![*b]),
        },
        CapOp::NatZero => MiniValue::Nat(ExactNat::ZERO),
        CapOp::AmtHead(d0) => match vs.get(1) {
            Some(MiniValue::Digits(ds)) => MiniValue::Nat(ExactNat::from_decimal_digits(*d0, ds)),
            _ => MiniValue::Nat(ExactNat::from_u64(u64::from(*d0))),
        },
        CapOp::DigitsNil => MiniValue::Digits(Vec::new()),
        CapOp::DigitsCons(d) => match vs.get(1) {
            Some(MiniValue::Digits(ds)) => {
                let mut out = Vec::with_capacity(1 + ds.len());
                out.push(*d);
                out.extend_from_slice(ds);
                MiniValue::Digits(out)
            }
            _ => MiniValue::Digits(vec![*d]),
        },
        CapOp::DigitsSingle(d) => MiniValue::Digits(vec![*d]),
        CapOp::MkAfterNorm => match (vs.get(10), vs.get(26)) {
            (Some(MiniValue::Bytes(tgt)), Some(MiniValue::Nat(amt))) => MiniValue::Batch(vec![
                MiniValue::Bytes(tgt.clone()),
                MiniValue::Nat(amt.clone()),
            ]),
            _ => MiniValue::Unit,
        },
        CapOp::MkDupFirst => match (vs.get(25), vs.get(41)) {
            (Some(MiniValue::Bytes(tgt)), Some(MiniValue::Nat(amt))) => MiniValue::Batch(vec![
                MiniValue::Bytes(tgt.clone()),
                MiniValue::Nat(amt.clone()),
            ]),
            _ => MiniValue::Unit,
        },
        CapOp::MkDupLast => match (vs.get(8), vs.get(25), vs.get(41)) {
            (
                Some(MiniValue::Bytes(tool2)),
                Some(MiniValue::Bytes(tgt)),
                Some(MiniValue::Nat(amt)),
            ) => MiniValue::Batch(vec![
                MiniValue::Bytes(tool2.clone()),
                MiniValue::Bytes(tgt.clone()),
                MiniValue::Nat(amt.clone()),
            ]),
            _ => MiniValue::Unit,
        },
        CapOp::MkExprObj => match (vs.get(12), vs.get(19)) {
            (Some(MiniValue::Bytes(tool1)), Some(MiniValue::Batch(items))) => match items.as_slice()
            {
                [MiniValue::Bytes(tgt), MiniValue::Nat(amt)] => MiniValue::ToolCall {
                    tool: tool1.clone(),
                    target: tgt.clone(),
                    amount: amt.clone(),
                },
                [MiniValue::Bytes(tool2), MiniValue::Bytes(tgt), MiniValue::Nat(amt)] => {
                    MiniValue::ToolCall {
                        tool: tool2.clone(),
                        target: tgt.clone(),
                        amount: amt.clone(),
                    }
                }
                _ => MiniValue::Unit,
            },
            _ => MiniValue::Unit,
        },
        CapOp::MkBatchHead | CapOp::MkBatchTail => match (vs.get(2), vs.get(4)) {
            (Some(head), Some(MiniValue::Batch(tail))) => {
                let mut out = Vec::with_capacity(1 + tail.len());
                out.push(head.clone());
                out.extend_from_slice(tail);
                MiniValue::Batch(out)
            }
            _ => MiniValue::Batch(Vec::new()),
        },
        CapOp::BatchNil => MiniValue::Batch(Vec::new()),
    }
}

fn cap_lit(s: &[u8]) -> Vec<CfgSym<u8, CapNT>> {
    s.iter().map(|&b| CfgSym::Terminal(b)).collect()
}

fn cap_slug_bytes() -> Vec<u8> {
    let mut out = Vec::with_capacity(38);
    for k in 0..26u8 {
        out.push(b'a' + k);
    }
    for k in 0..10u8 {
        out.push(b'0' + k);
    }
    out.push(b'_');
    out.push(b'-');
    out
}

pub fn rule_tool_read() -> AttrRule<u8, CapNT, CapOp> {
    AttrRule {
        lhs: CapNT::ToolName,
        rhs: cap_lit(b"read_doc"),
        op: CapOp::ConstBytes(b"read_doc".to_vec()),
    }
}

pub fn rule_tool_patch() -> AttrRule<u8, CapNT, CapOp> {
    AttrRule {
        lhs: CapNT::ToolName,
        rhs: cap_lit(b"patch_atom"),
        op: CapOp::ConstBytes(b"patch_atom".to_vec()),
    }
}

pub fn rule_tool_audit() -> AttrRule<u8, CapNT, CapOp> {
    AttrRule {
        lhs: CapNT::ToolName,
        rhs: cap_lit(b"audit_log"),
        op: CapOp::ConstBytes(b"audit_log".to_vec()),
    }
}

pub fn rule_tool_deploy() -> AttrRule<u8, CapNT, CapOp> {
    AttrRule {
        lhs: CapNT::ToolName,
        rhs: cap_lit(b"deploy_svc"),
        op: CapOp::ConstBytes(b"deploy_svc".to_vec()),
    }
}

pub fn rule_tool_wipe_prod() -> AttrRule<u8, CapNT, CapOp> {
    AttrRule {
        lhs: CapNT::ToolName,
        rhs: cap_lit(b"wipe_prod"),
        op: CapOp::ConstBytes(b"wipe_prod".to_vec()),
    }
}

pub fn rule_tgt_sandbox() -> AttrRule<u8, CapNT, CapOp> {
    let mut rhs = cap_lit(b"sandbox/");
    rhs.push(CfgSym::Nonterminal(CapNT::Slug));
    AttrRule {
        lhs: CapNT::TargetPath,
        rhs,
        op: CapOp::PrefixSlug(b"sandbox/".to_vec()),
    }
}

pub fn rule_tgt_docs() -> AttrRule<u8, CapNT, CapOp> {
    let mut rhs = cap_lit(b"docs/");
    rhs.push(CfgSym::Nonterminal(CapNT::Slug));
    AttrRule {
        lhs: CapNT::TargetPath,
        rhs,
        op: CapOp::PrefixSlug(b"docs/".to_vec()),
    }
}

pub fn rule_tgt_vault() -> AttrRule<u8, CapNT, CapOp> {
    let mut rhs = cap_lit(b"vault/");
    rhs.push(CfgSym::Nonterminal(CapNT::Slug));
    AttrRule {
        lhs: CapNT::TargetPath,
        rhs,
        op: CapOp::PrefixSlug(b"vault/".to_vec()),
    }
}

fn rule_after_norm() -> AttrRule<u8, CapNT, CapOp> {
    use CfgSym::{Nonterminal as Nt, Terminal as T};
    let mut rhs = cap_lit(b"arget\"");
    rhs.extend_from_slice(&[
        Nt(CapNT::WS),
        T(b':'),
        Nt(CapNT::WS),
        T(b'"'),
        Nt(CapNT::TargetPath),
        T(b'"'),
        Nt(CapNT::WS),
        T(b','),
        Nt(CapNT::WS),
    ]);
    rhs.extend(cap_lit(b"\"amount\""));
    rhs.extend_from_slice(&[
        Nt(CapNT::WS),
        T(b':'),
        Nt(CapNT::WS),
        Nt(CapNT::BoundedAmt),
        Nt(CapNT::WS),
        T(b'}'),
    ]);
    AttrRule {
        lhs: CapNT::AfterCommaT,
        rhs,
        op: CapOp::MkAfterNorm,
    }
}

pub fn rule_dup_key_first_wins() -> AttrRule<u8, CapNT, CapOp> {
    use CfgSym::{Nonterminal as Nt, Terminal as T};
    let mut rhs = cap_lit(b"ool\"");
    rhs.extend_from_slice(&[
        Nt(CapNT::WS),
        T(b':'),
        Nt(CapNT::WS),
        T(b'"'),
        Nt(CapNT::ToolName),
        T(b'"'),
        Nt(CapNT::WS),
        T(b','),
        Nt(CapNT::WS),
    ]);
    rhs.extend(cap_lit(b"\"target\""));
    rhs.extend_from_slice(&[
        Nt(CapNT::WS),
        T(b':'),
        Nt(CapNT::WS),
        T(b'"'),
        Nt(CapNT::TargetPath),
        T(b'"'),
        Nt(CapNT::WS),
        T(b','),
        Nt(CapNT::WS),
    ]);
    rhs.extend(cap_lit(b"\"amount\""));
    rhs.extend_from_slice(&[
        Nt(CapNT::WS),
        T(b':'),
        Nt(CapNT::WS),
        Nt(CapNT::BoundedAmt),
        Nt(CapNT::WS),
        T(b'}'),
    ]);
    AttrRule {
        lhs: CapNT::AfterCommaT,
        rhs,
        op: CapOp::MkDupFirst,
    }
}

pub fn rule_dup_key_last_wins() -> AttrRule<u8, CapNT, CapOp> {
    let mut r = rule_dup_key_first_wins();
    r.op = CapOp::MkDupLast;
    r
}

fn cap_core_frame_rules() -> Vec<AttrRule<u8, CapNT, CapOp>> {
    use CfgSym::{Nonterminal as Nt, Terminal as T};
    let mut expr_obj = vec![T(b'{'), Nt(CapNT::WS)];
    expr_obj.extend(cap_lit(b"\"tool\""));
    expr_obj.extend_from_slice(&[
        Nt(CapNT::WS),
        T(b':'),
        Nt(CapNT::WS),
        T(b'"'),
        Nt(CapNT::ToolName),
        T(b'"'),
        Nt(CapNT::WS),
        T(b','),
        Nt(CapNT::WS),
        T(b'"'),
        T(b't'),
        Nt(CapNT::AfterCommaT),
    ]);

    let mut rules = vec![
        AttrRule {
            lhs: CapNT::Root,
            rhs: vec![Nt(CapNT::WS), Nt(CapNT::Expr), Nt(CapNT::WS)],
            op: CapOp::PassAt(1),
        },
        AttrRule {
            lhs: CapNT::Expr,
            rhs: expr_obj,
            op: CapOp::MkExprObj,
        },
        rule_after_norm(),
        AttrRule {
            lhs: CapNT::Expr,
            rhs: vec![
                T(b'['),
                Nt(CapNT::WS),
                Nt(CapNT::Expr),
                Nt(CapNT::WS),
                Nt(CapNT::BatchTail),
                T(b']'),
            ],
            op: CapOp::MkBatchHead,
        },
        AttrRule {
            lhs: CapNT::BatchTail,
            rhs: vec![
                T(b','),
                Nt(CapNT::WS),
                Nt(CapNT::Expr),
                Nt(CapNT::WS),
                Nt(CapNT::BatchTail),
            ],
            op: CapOp::MkBatchTail,
        },
        AttrRule {
            lhs: CapNT::BatchTail,
            rhs: vec![],
            op: CapOp::BatchNil,
        },
        AttrRule {
            lhs: CapNT::WS,
            rhs: vec![T(b' '), Nt(CapNT::WS)],
            op: CapOp::UnitOp,
        },
        AttrRule {
            lhs: CapNT::WS,
            rhs: vec![T(b'\n'), Nt(CapNT::WS)],
            op: CapOp::UnitOp,
        },
        AttrRule {
            lhs: CapNT::WS,
            rhs: vec![],
            op: CapOp::UnitOp,
        },
        AttrRule {
            lhs: CapNT::Slug,
            rhs: vec![],
            op: CapOp::SlugNil,
        },
        AttrRule {
            lhs: CapNT::BoundedAmt,
            rhs: vec![T(b'0')],
            op: CapOp::NatZero,
        },
        AttrRule {
            lhs: CapNT::AmtTail1,
            rhs: vec![],
            op: CapOp::DigitsNil,
        },
        AttrRule {
            lhs: CapNT::AmtTail2,
            rhs: vec![],
            op: CapOp::DigitsNil,
        },
    ];
    for b in cap_slug_bytes() {
        rules.push(AttrRule {
            lhs: CapNT::Slug,
            rhs: vec![T(b), Nt(CapNT::Slug)],
            op: CapOp::SlugCons(b),
        });
    }
    rules
}

fn amt_head_rules(max_first_digit: u8) -> Vec<AttrRule<u8, CapNT, CapOp>> {
    (0..max_first_digit)
        .map(|k| {
            let d = k + 1;
            AttrRule {
                lhs: CapNT::BoundedAmt,
                rhs: vec![
                    CfgSym::Terminal(b'0' + d),
                    CfgSym::Nonterminal(CapNT::AmtTail1),
                ],
                op: CapOp::AmtHead(d),
            }
        })
        .collect()
}

fn amt_tail1_digit_rules() -> Vec<AttrRule<u8, CapNT, CapOp>> {
    (0..10u8)
        .map(|d| AttrRule {
            lhs: CapNT::AmtTail1,
            rhs: vec![
                CfgSym::Terminal(b'0' + d),
                CfgSym::Nonterminal(CapNT::AmtTail2),
            ],
            op: CapOp::DigitsCons(d),
        })
        .collect()
}

fn amt_tail2_digit_rules() -> Vec<AttrRule<u8, CapNT, CapOp>> {
    (0..10u8)
        .map(|d| AttrRule {
            lhs: CapNT::AmtTail2,
            rhs: vec![CfgSym::Terminal(b'0' + d)],
            op: CapOp::DigitsSingle(d),
        })
        .collect()
}

pub fn make_cap_cfg(rules: Vec<AttrRule<u8, CapNT, CapOp>>) -> AttrCfg<u8, CapNT, CapOp, MiniValue> {
    AttrCfg {
        initial: CapNT::Root,
        rules,
        term_val: cap_term_val,
        eval_op: eval_cap_op,
        eval_in_place: None,
    }
}

pub fn root_redact_rules() -> Vec<RedactRule> {
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
    ]
}

pub fn subagent_redact_rules() -> Vec<RedactRule> {
    let mut r = root_redact_rules();
    r.push(RedactRule {
        name: "github_pat",
        pat: b"ghp_".to_vec(),
        body_pred: is_api_key_body_byte,
        repl: b"[REDACTED_GH_PAT]".to_vec(),
    });
    r
}

/// Hop 0 (`rootCapPolicy` in Lean; parameterized by `max_ops` defaulting to `10`).
pub fn root_cap_policy_with_max_ops(max_ops: u64) -> GrammarPolicy<CapNT, CapOp, MiniValue> {
    let mut rules = cap_core_frame_rules();
    rules.extend([
        rule_tool_read(),
        rule_tool_patch(),
        rule_tool_audit(),
        rule_tool_deploy(),
        rule_tgt_sandbox(),
        rule_tgt_docs(),
        rule_tgt_vault(),
    ]);
    rules.extend(amt_head_rules(9));
    rules.extend(amt_tail1_digit_rules());
    rules.extend(amt_tail2_digit_rules());
    GrammarPolicy {
        semantics_id: CAP_SEMANTICS_ID,
        grammar: make_cap_cfg(rules),
        redact_rules: root_redact_rules(),
        bounds: vec![
            AutomatonBound::MustAccept(DfaTable::no_sk_dash()),
            AutomatonBound::RangeHits {
                dfa: dfa_count_op_brace(),
                lo: 1,
                hi: max_ops,
            },
        ],
    }
}

pub fn root_cap_policy() -> GrammarPolicy<CapNT, CapOp, MiniValue> {
    root_cap_policy_with_max_ops(10)
}

/// Hop 1 (`serviceCapPolicy` — TeamLead in Lean; parameterized by `max_ops` defaulting to `5`).
pub fn service_cap_policy_with_max_ops(max_ops: u64) -> GrammarPolicy<CapNT, CapOp, MiniValue> {
    let mut rules = cap_core_frame_rules();
    rules.extend([
        rule_tool_read(),
        rule_tool_patch(),
        rule_tool_audit(),
        rule_tgt_sandbox(),
        rule_tgt_docs(),
    ]);
    rules.extend(amt_head_rules(9));
    rules.extend(amt_tail1_digit_rules());
    GrammarPolicy {
        semantics_id: CAP_SEMANTICS_ID,
        grammar: make_cap_cfg(rules),
        redact_rules: root_redact_rules(),
        bounds: vec![
            AutomatonBound::MustAccept(DfaTable::no_sk_dash()),
            AutomatonBound::MustAccept(dfa_no_sql_drop()),
            AutomatonBound::RangeHits {
                dfa: dfa_count_op_brace(),
                lo: 1,
                hi: max_ops,
            },
        ],
    }
}

pub fn service_cap_policy() -> GrammarPolicy<CapNT, CapOp, MiniValue> {
    service_cap_policy_with_max_ops(5)
}

/// Hop 2 (`subagentToolCapPolicy` — UntrustedCoderAgent in Lean; `max_ops` defaults to `2`).
pub fn subagent_tool_cap_policy_with_max_ops(
    max_ops: u64,
) -> GrammarPolicy<CapNT, CapOp, MiniValue> {
    let mut rules = cap_core_frame_rules();
    rules.extend([rule_tool_read(), rule_tool_patch(), rule_tgt_sandbox()]);
    rules.extend(amt_head_rules(5));
    GrammarPolicy {
        semantics_id: CAP_SEMANTICS_ID,
        grammar: make_cap_cfg(rules),
        redact_rules: subagent_redact_rules(),
        bounds: vec![
            AutomatonBound::MustAccept(DfaTable::no_sk_dash()),
            AutomatonBound::MustAccept(dfa_no_sql_drop()),
            AutomatonBound::MustAccept(dfa_no_shell_sub()),
            AutomatonBound::RangeHits {
                dfa: dfa_count_op_brace(),
                lo: 1,
                hi: max_ops,
            },
        ],
    }
}

pub fn subagent_tool_cap_policy() -> GrammarPolicy<CapNT, CapOp, MiniValue> {
    subagent_tool_cap_policy_with_max_ops(2)
}

// ============================================================================
// §5. Sealed `Hyperdocument` Blinded-Patch Gate & Zero-Leakage Public Bundle
// ============================================================================

const FRAGMENT_STREAM_CUST_PREFIX: u8 = 0x09;
const FRAGMENT_STREAM_CUST_NAME: &[u8] = b"MINIDREGG/HYPERDOC/SEALED_ATOM_STREAM/V1";
const FRAGMENT_WRAP_CUST_PREFIX: u8 = 0x0A;
const FRAGMENT_WRAP_CUST_NAME: &[u8] = b"MINIDREGG/HYPERDOC/SEALED_ATOM_WRAP/V1";
const PUBLIC_BUNDLE_MAGIC: &[u8; 8] = b"MDHGCB01";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RevocationKey {
    Capability(u64),
    Channel(u64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CapabilityMeta {
    pub id: u64,
    pub root: u64,
    pub parent: Option<u64>,
    pub issuer: u64,
    pub holder_subject: u64,
    pub target_object_ids: Vec<u64>,
    pub allow_mutate: bool,
    pub allow_delegate: bool,
    pub max_cost: u64,
    pub not_before: u64,
    pub not_after: u64,
    pub issuer_epoch: u64,
    pub policy_id: u64,
    pub policy_epoch: u64,
    pub ancestors: Vec<u64>,
    pub channels: Vec<u64>,
}

impl CapabilityMeta {
    /// Check capability edge `parent -> self` (`checkCapEdge` in `Assurance/SealedHyperdocGrammarGate.lean`):
    /// requires distinct IDs, exact ancestor insertion (`ancestors == insert parent.id parent.ancestors`),
    /// scope/validity narrowing, AND either holder self-attenuation (`holder_subject == parent.holder_subject`)
    /// OR authorized subject delegation (`parent.allow_delegate`).
    pub fn attenuates(&self, parent: &Self) -> bool {
        let holder_authorized =
            self.holder_subject == parent.holder_subject || parent.allow_delegate;
        self.id != parent.id
            && holder_authorized
            && self.parent == Some(parent.id)
            && self.root == parent.root
            && self.issuer == parent.issuer
            && self
                .target_object_ids
                .iter()
                .all(|t| parent.target_object_ids.contains(t))
            && (!self.allow_mutate || parent.allow_mutate)
            && (!self.allow_delegate || parent.allow_delegate)
            && self.max_cost <= parent.max_cost
            && parent.not_before <= self.not_before
            && self.not_after <= parent.not_after
            && self.issuer_epoch == parent.issuer_epoch
            && self.policy_id == parent.policy_id
            && self.policy_epoch == parent.policy_epoch
            && self.ancestors.contains(&parent.id)
            && parent.ancestors.iter().all(|a| self.ancestors.contains(a))
            && self
                .ancestors
                .iter()
                .all(|a| *a == parent.id || parent.ancestors.contains(a))
            && parent.channels.iter().all(|c| self.channels.contains(c))
    }

    pub fn is_valid_root(&self, expected_root_cap_id: u64, expected_issuer: u64) -> bool {
        self.id == expected_root_cap_id
            && self.issuer == expected_issuer
            && self.parent.is_none()
            && self.root == self.id
            && self.ancestors.is_empty()
    }

    pub fn fresh_and_unrevoked(
        &self,
        revoked: &HashSet<RevocationKey>,
        policy_id: u64,
        expected_policy_epoch: u64,
        expected_issuer_epoch: u64,
    ) -> bool {
        self.policy_id == policy_id
            && self.policy_epoch == expected_policy_epoch
            && self.issuer_epoch == expected_issuer_epoch
            && !revoked.contains(&RevocationKey::Capability(self.id))
            && self
                .ancestors
                .iter()
                .all(|&a| !revoked.contains(&RevocationKey::Capability(a)))
            && self
                .channels
                .iter()
                .all(|&c| !revoked.contains(&RevocationKey::Channel(c)))
    }
}

/// Sealed `Hyperdocument` `AtomRecord` edit (`AtomKind.sealedObject` with `K-NARROW-HIDE`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SealedAtomEdit {
    pub document_id: u64,
    pub atom_id: u64,
    pub schema: Digest,
    pub author_subject: u64,
    pub author_capability_id: u64,
    pub operation_id: u64,
    pub wrapped_by_subject: u64,
    pub wrapped_by_capability_id: u64,
    pub wrapped_at_operation_id: u64,
    pub ciphertext: Vec<u8>,
    pub wrapping: Vec<u8>,
    /// Durable cleartext `AtomRecord.payload` — MUST be empty (`AtomKind.validPayload`).
    pub cleartext_payload: Vec<u8>,
}

/// Encrypt a patch payload into a sealed `AuthoredFragment` `(ciphertext, wrapping)` under
/// `cell_blinding_key` and `(document_id, atom_id, schema, operation_id, salted_patch_root)` using
/// **domain-separated** SP 800-185 `cSHAKE256` XOF customizations (`0x09` stream vs `0x0A` MAC/wrap
/// tag over `ciphertext`), guaranteeing `wrapping` leaks zero keystream bits.
pub fn seal_hyperdoc_fragment_bytes(
    cell_blinding_key: &Digest,
    document_id: u64,
    atom_id: u64,
    schema: &Digest,
    operation_id: u64,
    salted_patch_root: &Digest,
    plaintext: &[u8],
) -> (Vec<u8>, Vec<u8>) {
    let mut stream_cust = Vec::with_capacity(1 + FRAGMENT_STREAM_CUST_NAME.len());
    stream_cust.push(FRAGMENT_STREAM_CUST_PREFIX);
    stream_cust.extend_from_slice(FRAGMENT_STREAM_CUST_NAME);

    let mut context = Vec::with_capacity(32 + 8 + 8 + 32 + 8 + 32);
    context.extend_from_slice(cell_blinding_key);
    context.extend_from_slice(&document_id.to_le_bytes());
    context.extend_from_slice(&atom_id.to_le_bytes());
    context.extend_from_slice(schema);
    context.extend_from_slice(&operation_id.to_le_bytes());
    context.extend_from_slice(salted_patch_root);

    let keystream = cshake256_xof(&stream_cust, &context, plaintext.len());
    let ciphertext: Vec<u8> = plaintext
        .iter()
        .zip(keystream.iter())
        .map(|(&p, &k)| p ^ k)
        .collect();

    let mut wrap_cust = Vec::with_capacity(1 + FRAGMENT_WRAP_CUST_NAME.len());
    wrap_cust.push(FRAGMENT_WRAP_CUST_PREFIX);
    wrap_cust.extend_from_slice(FRAGMENT_WRAP_CUST_NAME);
    let mut wrap_input = context;
    wrap_input.extend_from_slice(&(ciphertext.len() as u64).to_le_bytes());
    wrap_input.extend_from_slice(&ciphertext);
    let wrapping = cshake256_xof(&wrap_cust, &wrap_input, 32);
    (ciphertext, wrapping)
}

/// Public statement for `verify_sealed_hyperdoc_patch` (`SealedHyperdocPatchStmt` in Lean).
pub struct SealedHyperdocPatchStmt<'a, NT, SemOp, Val> {
    pub document_id: u64,
    pub atom_id: u64,
    pub schema: Digest,
    pub operation_id: u64,
    pub author_subject: u64,
    pub author_capability_id: u64,
    pub height: u64,
    pub cost: u64,
    pub expected_root_cap_id: u64,
    pub expected_issuer: u64,
    pub policy_id: u64,
    pub expected_policy_epoch: u64,
    pub expected_issuer_epoch: u64,
    pub revoked: HashSet<RevocationKey>,
    pub patch_len: usize,
    pub salted_patch_root: Digest,
    pub claimed_ast: Val,
    pub root_policy: &'a GrammarPolicy<NT, SemOp, Val>,
    pub edit: SealedAtomEdit,
}

pub struct DelegatedGrammarHop<'a, NT, SemOp, Val> {
    pub capability: CapabilityMeta,
    pub policy: &'a GrammarPolicy<NT, SemOp, Val>,
}

/// Optional serialized `Tower256` `PrivateReceipt` guard bundle over `salted_patch_root`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuccinctGuardWire {
    pub bound: AutomatonBound,
    pub cert_bytes: Vec<u8>,
    pub receipt_bytes: Vec<u8>,
}

pub struct SealedHyperdocPatchWitness<'a, NT, SemOp, Val> {
    pub chain: Vec<DelegatedGrammarHop<'a, NT, SemOp, Val>>,
    pub patch_bytes: Vec<u8>,
    pub patch_salts: Vec<Salt248>,
    pub rule_indices: Vec<usize>,
    pub succinct_guards: Vec<SuccinctGuardWire>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GateRejection {
    EmptyPatch,
    EmptyChain,
    CleartextPayloadNotEmpty,
    SealedAtomMetadataMismatch,
    RootAuthorityAnchorMismatch,
    AuthorBindingMismatch,
    CapabilityExpiredOrNotYetValid,
    InsufficientCapabilityScopeOrBudget,
    RevokedOrStaleEpoch { hop_index: usize },
    CapabilityEdgeNotAttenuated { hop_index: usize },
    RootPolicyNotAttenuated(AttenuationRefusal),
    PolicyHopNotAttenuated {
        hop_index: usize,
        reason: AttenuationRefusal,
    },
    PatchLengthMismatch,
    SaltsLengthMismatch,
    SaltedPatchRootMismatch,
    PayloadNotPreScrubbed,
    AutomatonBoundViolated { bound_index: usize },
    AstReplayFailed(TransducerError),
    ClaimedAstMismatch,
    SuccinctGuardInvalid(&'static str),
}

/// Fast precompiled leaf policy verifier (reusable across turns for `< 15 ms` 4 KiB verification).
pub struct CompiledLeafVerifier<NT, SemOp, Val> {
    pub parser: CompiledByteLl1Parser<NT, SemOp, Val>,
    pub redactor: CompiledRedactor,
}

impl<NT, SemOp, Val> CompiledLeafVerifier<NT, SemOp, Val>
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: Clone,
{
    pub fn compile(
        policy: &GrammarPolicy<NT, SemOp, Val>,
        nt_count: usize,
        nt_to_id: fn(NT) -> usize,
    ) -> Result<Self, TransducerError> {
        if !all_rules_safe(&policy.redact_rules) {
            return Err(TransducerError::UnsafeRedactionRules);
        }
        let parser = CompiledByteLl1Parser::compile(
            AttrCfg {
                initial: policy.grammar.initial,
                rules: policy.grammar.rules.clone(),
                term_val: policy.grammar.term_val,
                eval_op: policy.grammar.eval_op,
                eval_in_place: policy.grammar.eval_in_place,
            },
            nt_count,
            nt_to_id,
        )?;
        let redactor = CompiledRedactor::new(policy.redact_rules.clone());
        Ok(Self { parser, redactor })
    }
}

fn check_sealed_atom_edit<NT, SemOp, Val>(
    stmt: &SealedHyperdocPatchStmt<'_, NT, SemOp, Val>,
) -> Result<(), GateRejection> {
    if !stmt.edit.cleartext_payload.is_empty() {
        return Err(GateRejection::CleartextPayloadNotEmpty);
    }
    if stmt.edit.atom_id != stmt.atom_id
        || stmt.edit.document_id != stmt.document_id
        || stmt.edit.schema != stmt.schema
        || stmt.edit.author_subject != stmt.author_subject
        || stmt.edit.author_capability_id != stmt.author_capability_id
        || stmt.edit.operation_id != stmt.operation_id
        || stmt.edit.wrapped_by_subject != stmt.author_subject
        || stmt.edit.wrapped_by_capability_id != stmt.author_capability_id
        || stmt.edit.wrapped_at_operation_id != stmt.operation_id
        || stmt.edit.ciphertext.len() != stmt.patch_len
        || stmt.edit.wrapping.len() != 32
    {
        return Err(GateRejection::SealedAtomMetadataMismatch);
    }
    Ok(())
}

/// Verify the capability + `GrammarPolicy` chain (`checkDelegatedCapChain` in Lean):
/// runs root-authority anchoring, leaf scope & byte-cost checks (`cost >= patch_len`), epoch/revocation
/// checks, capability edge delegation/attenuation, and full LL(1) + product-DFA policy attenuation.
pub fn verify_delegated_cap_chain<NT, SemOp, Val>(
    stmt: &SealedHyperdocPatchStmt<'_, NT, SemOp, Val>,
    chain: &[DelegatedGrammarHop<'_, NT, SemOp, Val>],
) -> Result<(), GateRejection>
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: PartialEq + Clone,
{
    let Some(root_hop) = chain.first() else {
        return Err(GateRejection::EmptyChain);
    };
    let leaf_hop = chain.last().expect("non-empty");

    if !root_hop
        .capability
        .is_valid_root(stmt.expected_root_cap_id, stmt.expected_issuer)
    {
        return Err(GateRejection::RootAuthorityAnchorMismatch);
    }
    if leaf_hop.capability.id != stmt.author_capability_id
        || leaf_hop.capability.holder_subject != stmt.author_subject
    {
        return Err(GateRejection::AuthorBindingMismatch);
    }
    if stmt.height < leaf_hop.capability.not_before || stmt.height > leaf_hop.capability.not_after {
        return Err(GateRejection::CapabilityExpiredOrNotYetValid);
    }
    let patch_len_u64 = u64::try_from(stmt.patch_len).unwrap_or(u64::MAX);
    if !leaf_hop.capability.allow_mutate
        || !leaf_hop
            .capability
            .target_object_ids
            .contains(&stmt.document_id)
        || stmt.cost < patch_len_u64
        || stmt.cost > leaf_hop.capability.max_cost
    {
        return Err(GateRejection::InsufficientCapabilityScopeOrBudget);
    }

    if let Err(reason) = check_policy_attenuation(root_hop.policy, stmt.root_policy) {
        return Err(GateRejection::RootPolicyNotAttenuated(reason));
    }

    for (idx, hop) in chain.iter().enumerate() {
        if !hop.capability.fresh_and_unrevoked(
            &stmt.revoked,
            stmt.policy_id,
            stmt.expected_policy_epoch,
            stmt.expected_issuer_epoch,
        ) {
            return Err(GateRejection::RevokedOrStaleEpoch { hop_index: idx });
        }
    }

    for (idx, pair) in chain.windows(2).enumerate() {
        let parent = &pair[0];
        let child = &pair[1];
        if !child.capability.attenuates(&parent.capability) {
            return Err(GateRejection::CapabilityEdgeNotAttenuated { hop_index: idx + 1 });
        }
        if let Err(reason) = check_policy_attenuation(child.policy, parent.policy) {
            return Err(GateRejection::PolicyHopNotAttenuated {
                hop_index: idx + 1,
                reason,
            });
        }
    }
    Ok(())
}

fn verify_succinct_guard_wires<NT, SemOp, Val>(
    stmt: &SealedHyperdocPatchStmt<'_, NT, SemOp, Val>,
    guards: &[SuccinctGuardWire],
) -> Result<(), GateRejection> {
    for g in guards {
        if !g.bound.well_formed() {
            return Err(GateRejection::SuccinctGuardInvalid("malformed guard DFA"));
        }
        let cert = decode_private_cert(&g.cert_bytes)
            .map_err(|_| GateRejection::SuccinctGuardInvalid("decode cert failed"))?;
        if cert.content_root != stmt.salted_patch_root
            || cert.record_length != stmt.patch_len
            || cert.automaton_root != automaton_commit(g.bound.dfa())
            || cert.claim != g.bound.to_claim_data()
        {
            return Err(GateRejection::SuccinctGuardInvalid(
                "succinct cert statement mismatch",
            ));
        }
        verify_private_cert_bytes(&cert, &g.receipt_bytes)
            .map_err(|_| GateRejection::SuccinctGuardInvalid("PrivateReceipt check failed"))?;
    }
    Ok(())
}

/// **Full Sealed `Hyperdocument` Blinded-Patch Verifier (`verifySealedHyperdocPatch` in Lean).**
pub fn verify_sealed_hyperdoc_patch<NT, SemOp, Val>(
    stmt: &SealedHyperdocPatchStmt<'_, NT, SemOp, Val>,
    wit: &SealedHyperdocPatchWitness<'_, NT, SemOp, Val>,
) -> Result<(), GateRejection>
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: PartialEq + Clone,
    Val: PartialEq,
{
    if stmt.patch_len == 0 {
        return Err(GateRejection::EmptyPatch);
    }
    check_sealed_atom_edit(stmt)?;
    verify_delegated_cap_chain(stmt, &wit.chain)?;

    let leaf_hop = wit.chain.last().expect("verified non-empty");

    if wit.patch_bytes.len() != stmt.patch_len {
        return Err(GateRejection::PatchLengthMismatch);
    }
    if wit.patch_salts.len() != stmt.patch_len {
        return Err(GateRejection::SaltsLengthMismatch);
    }
    let computed_root = salted_content_commit(&wit.patch_bytes, &wit.patch_salts)
        .map_err(|_| GateRejection::SaltsLengthMismatch)?;
    if computed_root != stmt.salted_patch_root {
        return Err(GateRejection::SaltedPatchRootMismatch);
    }

    let redactor = CompiledRedactor::new(leaf_hop.policy.redact_rules.clone());
    if redactor.redact(&wit.patch_bytes) != wit.patch_bytes {
        return Err(GateRejection::PayloadNotPreScrubbed);
    }
    for (b_idx, b) in leaf_hop.policy.bounds.iter().enumerate() {
        if !b.holds(&wit.patch_bytes) {
            return Err(GateRejection::AutomatonBoundViolated { bound_index: b_idx });
        }
    }
    let ast = exec_attr_replay(
        &leaf_hop.policy.grammar,
        &wit.rule_indices,
        &wit.patch_bytes,
    )
    .map_err(GateRejection::AstReplayFailed)?;
    if ast != stmt.claimed_ast {
        return Err(GateRejection::ClaimedAstMismatch);
    }

    verify_succinct_guard_wires(stmt, &wit.succinct_guards)?;
    Ok(())
}

// ============================================================================
// §6. Root-Only Zero-Leakage Public Observer Bundle (`0` Leaked `>=6B` Slices!)
// ============================================================================

/// Public observer receipt for the **automaton-bound projection** (`SuccinctGuardBundle` in Lean)
/// of a sealed `Hyperdocument` patch: carries ONLY the domain-separated `cSHAKE256`-encrypted
/// `SealedAtomEdit` `(ciphertext, wrapping)`, `salted_patch_root`, `patch_len`, and succinct
/// `Tower256` `PrivateReceipt` proofs — **zero** raw `patch_bytes` or `patch_salts`!
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PublicSealedPatchBundle {
    pub document_id: u64,
    pub atom_id: u64,
    pub schema: Digest,
    pub operation_id: u64,
    pub patch_len: usize,
    pub salted_patch_root: Digest,
    pub ciphertext: Vec<u8>,
    pub wrapping: Vec<u8>,
    pub succinct_guards: Vec<SuccinctGuardWire>,
}

/// Prove succinct `Tower256` `PrivateReceipt`s for a list of `AutomatonBound`s sharing the exact
/// same `(patch_len, salted_patch_root)` and pack a zero-leakage `PublicSealedPatchBundle`.
pub fn prove_public_sealed_patch_bundle(
    document_id: u64,
    atom_id: u64,
    schema: Digest,
    operation_id: u64,
    cell_blinding_key: &Digest,
    patch_bytes: &[u8],
    patch_salts: &[Salt248],
    row_masks_per_guard: &[Vec<RowMask>],
    bounds: &[AutomatonBound],
    fri_queries: usize,
    step_queries: usize,
) -> Result<PublicSealedPatchBundle, CapabilityError> {
    if patch_bytes.is_empty() {
        return Err(CapabilityError::MalformedBundle("patch_bytes must be non-empty"));
    }
    if row_masks_per_guard.len() != bounds.len() {
        return Err(CapabilityError::MalformedBundle(
            "row_masks_per_guard length must match bounds length",
        ));
    }
    if !bounds.iter().all(AutomatonBound::well_formed) {
        return Err(CapabilityError::MalformedBundle(
            "malformed AutomatonBound in prove_public_sealed_patch_bundle",
        ));
    }
    let salted_patch_root = salted_content_commit(patch_bytes, patch_salts)?;
    let (ciphertext, wrapping) = seal_hyperdoc_fragment_bytes(
        cell_blinding_key,
        document_id,
        atom_id,
        &schema,
        operation_id,
        &salted_patch_root,
        patch_bytes,
    );
    let td = crate::tower256_private_cert::depth_of(patch_bytes.len()).max(1);
    let fri_ell = td + 1;
    let fri_rounds = td.saturating_sub(2).max(1);

    let mut succinct_guards = Vec::with_capacity(bounds.len());
    for (idx, bound) in bounds.iter().enumerate() {
        let (cert, receipt) = prove_private_with_randomness(
            bound.dfa(),
            patch_bytes,
            patch_salts,
            &row_masks_per_guard[idx],
            bound.to_claim_data(),
            fri_ell,
            fri_rounds,
            fri_queries,
            step_queries,
        )?;
        succinct_guards.push(SuccinctGuardWire {
            bound: bound.clone(),
            cert_bytes: encode_private_cert(&cert),
            receipt_bytes: encode_private_receipt(&receipt),
        });
    }

    Ok(PublicSealedPatchBundle {
        document_id,
        atom_id,
        schema,
        operation_id,
        patch_len: patch_bytes.len(),
        salted_patch_root,
        ciphertext,
        wrapping,
        succinct_guards,
    })
}

fn encode_automaton_bound(out: &mut Vec<u8>, bound: &AutomatonBound) {
    let dfa = bound.dfa();
    out.extend_from_slice(&(dfa.states as u64).to_le_bytes());
    out.extend_from_slice(&(dfa.initial as u64).to_le_bytes());
    for &acc in &dfa.accepting {
        out.push(u8::from(acc));
    }
    for &nxt in &dfa.delta {
        out.extend_from_slice(&(nxt as u32).to_le_bytes());
    }
    match bound {
        AutomatonBound::MustAccept(_) => out.push(0),
        AutomatonBound::MustReject(_) => out.push(1),
        AutomatonBound::MaxHits { hi, .. } => {
            out.push(2);
            out.extend_from_slice(&hi.to_le_bytes());
        }
        AutomatonBound::ExactHits { n, .. } => {
            out.push(3);
            out.extend_from_slice(&n.to_le_bytes());
        }
        AutomatonBound::RangeHits { lo, hi, .. } => {
            out.push(4);
            out.extend_from_slice(&lo.to_le_bytes());
            out.extend_from_slice(&hi.to_le_bytes());
        }
    }
}

fn read_u64_le(bytes: &[u8], cursor: &mut usize) -> Result<u64, CapabilityError> {
    let end = cursor
        .checked_add(8)
        .filter(|&e| e <= bytes.len())
        .ok_or(CapabilityError::MalformedBundle("truncated u64 field"))?;
    let val = u64::from_le_bytes(bytes[*cursor..end].try_into().unwrap());
    *cursor = end;
    Ok(val)
}

fn read_slice<'a>(bytes: &'a [u8], cursor: &mut usize, len: usize) -> Result<&'a [u8], CapabilityError> {
    let end = cursor
        .checked_add(len)
        .filter(|&e| e <= bytes.len())
        .ok_or(CapabilityError::MalformedBundle("truncated byte slice"))?;
    let s = &bytes[*cursor..end];
    *cursor = end;
    Ok(s)
}

fn decode_automaton_bound(bytes: &[u8], cursor: &mut usize) -> Result<AutomatonBound, CapabilityError> {
    let states = usize::try_from(read_u64_le(bytes, cursor)?)
        .map_err(|_| CapabilityError::MalformedBundle("states overflow"))?;
    if states == 0 || states > 65_536 {
        return Err(CapabilityError::MalformedBundle("invalid DFA states count"));
    }
    let initial = usize::try_from(read_u64_le(bytes, cursor)?)
        .map_err(|_| CapabilityError::MalformedBundle("initial overflow"))?;
    let acc_raw = read_slice(bytes, cursor, states)?;
    let mut accepting = Vec::with_capacity(states);
    for &b in acc_raw {
        match b {
            0 => accepting.push(false),
            1 => accepting.push(true),
            _ => return Err(CapabilityError::MalformedBundle("invalid accepting byte")),
        }
    }
    let delta_len = states
        .checked_mul(256)
        .ok_or(CapabilityError::MalformedBundle("delta size overflow"))?;
    let delta_raw = read_slice(bytes, cursor, delta_len * 4)?;
    let mut delta = Vec::with_capacity(delta_len);
    for chunk in delta_raw.chunks_exact(4) {
        delta.push(u32::from_le_bytes(chunk.try_into().unwrap()) as usize);
    }
    let dfa = DfaTable {
        states,
        initial,
        accepting,
        delta,
    };
    dfa.validate().map_err(CapabilityError::InvalidDfa)?;
    let tag = read_slice(bytes, cursor, 1)?[0];
    let bound = match tag {
        0 => AutomatonBound::MustAccept(dfa),
        1 => AutomatonBound::MustReject(dfa),
        2 => AutomatonBound::MaxHits {
            dfa,
            hi: read_u64_le(bytes, cursor)?,
        },
        3 => AutomatonBound::ExactHits {
            dfa,
            n: read_u64_le(bytes, cursor)?,
        },
        4 => {
            let lo = read_u64_le(bytes, cursor)?;
            let hi = read_u64_le(bytes, cursor)?;
            AutomatonBound::RangeHits { dfa, lo, hi }
        }
        _ => return Err(CapabilityError::MalformedBundle("unknown AutomatonBound tag")),
    };
    if !bound.well_formed() {
        return Err(CapabilityError::MalformedBundle("decoded malformed AutomatonBound"));
    }
    Ok(bound)
}

/// Serialize `PublicSealedPatchBundle` to canonical self-contained wire bytes (including `g.bound`).
pub fn encode_public_sealed_patch_bundle(b: &PublicSealedPatchBundle) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(PUBLIC_BUNDLE_MAGIC);
    out.extend_from_slice(&b.document_id.to_le_bytes());
    out.extend_from_slice(&b.atom_id.to_le_bytes());
    out.extend_from_slice(&b.schema);
    out.extend_from_slice(&b.operation_id.to_le_bytes());
    out.extend_from_slice(&(b.patch_len as u64).to_le_bytes());
    out.extend_from_slice(&b.salted_patch_root);
    out.extend_from_slice(&(b.ciphertext.len() as u64).to_le_bytes());
    out.extend_from_slice(&b.ciphertext);
    out.extend_from_slice(&(b.wrapping.len() as u64).to_le_bytes());
    out.extend_from_slice(&b.wrapping);
    out.extend_from_slice(&(b.succinct_guards.len() as u64).to_le_bytes());
    for g in &b.succinct_guards {
        encode_automaton_bound(&mut out, &g.bound);
        out.extend_from_slice(&(g.cert_bytes.len() as u64).to_le_bytes());
        out.extend_from_slice(&g.cert_bytes);
        out.extend_from_slice(&(g.receipt_bytes.len() as u64).to_le_bytes());
        out.extend_from_slice(&g.receipt_bytes);
    }
    out
}

/// Decode canonical `PublicSealedPatchBundle` wire bytes with strict bounds checks.
pub fn decode_public_sealed_patch_bundle(
    bytes: &[u8],
) -> Result<PublicSealedPatchBundle, CapabilityError> {
    let mut cursor = 0usize;
    let magic = read_slice(bytes, &mut cursor, 8)?;
    if magic != PUBLIC_BUNDLE_MAGIC {
        return Err(CapabilityError::MalformedBundle("invalid bundle magic"));
    }
    let document_id = read_u64_le(bytes, &mut cursor)?;
    let atom_id = read_u64_le(bytes, &mut cursor)?;
    let schema: Digest = read_slice(bytes, &mut cursor, 32)?.try_into().unwrap();
    let operation_id = read_u64_le(bytes, &mut cursor)?;
    let patch_len = usize::try_from(read_u64_le(bytes, &mut cursor)?)
        .map_err(|_| CapabilityError::MalformedBundle("patch_len overflow"))?;
    if patch_len == 0 || patch_len > (1 << 24) {
        return Err(CapabilityError::MalformedBundle("invalid patch_len"));
    }
    let salted_patch_root: Digest = read_slice(bytes, &mut cursor, 32)?.try_into().unwrap();
    let ct_len = usize::try_from(read_u64_le(bytes, &mut cursor)?)
        .map_err(|_| CapabilityError::MalformedBundle("ciphertext len overflow"))?;
    if ct_len != patch_len {
        return Err(CapabilityError::MalformedBundle("ciphertext len != patch_len"));
    }
    let ciphertext = read_slice(bytes, &mut cursor, ct_len)?.to_vec();
    let wrap_len = usize::try_from(read_u64_le(bytes, &mut cursor)?)
        .map_err(|_| CapabilityError::MalformedBundle("wrapping len overflow"))?;
    if wrap_len != 32 {
        return Err(CapabilityError::MalformedBundle("wrapping must be 32 bytes"));
    }
    let wrapping = read_slice(bytes, &mut cursor, wrap_len)?.to_vec();
    let guard_count = usize::try_from(read_u64_le(bytes, &mut cursor)?)
        .map_err(|_| CapabilityError::MalformedBundle("guard count overflow"))?;
    if guard_count > 256 {
        return Err(CapabilityError::MalformedBundle("too many succinct guards"));
    }
    let mut succinct_guards = Vec::with_capacity(guard_count);
    for _ in 0..guard_count {
        let bound = decode_automaton_bound(bytes, &mut cursor)?;
        let cert_len = usize::try_from(read_u64_le(bytes, &mut cursor)?)
            .map_err(|_| CapabilityError::MalformedBundle("cert len overflow"))?;
        if cert_len > (1 << 20) {
            return Err(CapabilityError::MalformedBundle("cert_bytes too large"));
        }
        let cert_bytes = read_slice(bytes, &mut cursor, cert_len)?.to_vec();
        let rec_len = usize::try_from(read_u64_le(bytes, &mut cursor)?)
            .map_err(|_| CapabilityError::MalformedBundle("receipt len overflow"))?;
        if rec_len > (1 << 24) {
            return Err(CapabilityError::MalformedBundle("receipt_bytes too large"));
        }
        let receipt_bytes = read_slice(bytes, &mut cursor, rec_len)?.to_vec();
        succinct_guards.push(SuccinctGuardWire {
            bound,
            cert_bytes,
            receipt_bytes,
        });
    }
    if cursor != bytes.len() {
        return Err(CapabilityError::MalformedBundle("trailing bytes in bundle"));
    }
    Ok(PublicSealedPatchBundle {
        document_id,
        atom_id,
        schema,
        operation_id,
        patch_len,
        salted_patch_root,
        ciphertext,
        wrapping,
        succinct_guards,
    })
}

/// Verify a `PublicSealedPatchBundle` against an attenuated capability pair (`leaf_policy` -> `root_policy`)
/// without touching `patch_bytes` or `patch_salts` (`succinctGuardBundle_sound_or_miss_or_collision`):
/// verifies non-empty patch, `wrapping.len() == 32`, `grammar_policy_attenuates(leaf_policy, root_policy)`,
/// every attached `SuccinctGuardWire`, AND coverage of **every** `leaf_policy.bounds` guard (which by
/// `bounds_attenuate` transitively entails every `root_policy.bounds` guard as well!).
pub fn verify_public_sealed_patch_bundle<NT, SemOp, Val>(
    bundle: &PublicSealedPatchBundle,
    leaf_policy: &GrammarPolicy<NT, SemOp, Val>,
    root_policy: &GrammarPolicy<NT, SemOp, Val>,
) -> Result<(), CapabilityError>
where
    NT: Eq + Hash + Copy + fmt::Debug,
    SemOp: PartialEq + Clone,
{
    if bundle.patch_len == 0 {
        return Err(CapabilityError::MalformedBundle("patch_len must be > 0"));
    }
    if bundle.ciphertext.len() != bundle.patch_len {
        return Err(CapabilityError::MalformedBundle("ciphertext length mismatch"));
    }
    if bundle.wrapping.len() != 32 {
        return Err(CapabilityError::MalformedBundle("wrapping must be 32 bytes"));
    }
    if !grammar_policy_attenuates(leaf_policy, root_policy) {
        return Err(CapabilityError::MalformedBundle(
            "leaf policy does not attenuate root policy",
        ));
    }
    for g in &bundle.succinct_guards {
        if !g.bound.well_formed() {
            return Err(CapabilityError::MalformedBundle("malformed guard DFA"));
        }
        let cert = decode_private_cert(&g.cert_bytes)?;
        if cert.content_root != bundle.salted_patch_root
            || cert.record_length != bundle.patch_len
            || cert.automaton_root != automaton_commit(g.bound.dfa())
            || cert.claim != g.bound.to_claim_data()
        {
            return Err(CapabilityError::MalformedBundle(
                "succinct guard statement mismatch",
            ));
        }
        verify_private_cert_bytes(&cert, &g.receipt_bytes)?;
    }
    for bl in &leaf_policy.bounds {
        if !bundle
            .succinct_guards
            .iter()
            .any(|g| automaton_bound_entails(&g.bound, bl))
        {
            return Err(CapabilityError::MalformedBundle(
                "missing succinct guard entailing leaf policy bound",
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bfs_shortest_lexicographic_counterexamples_exact() {
        let all = dfa_accept_all();
        let no_sk = DfaTable::no_sk_dash();
        let no_sql = dfa_no_sql_drop();
        let no_shell = dfa_no_shell_sub();

        let res_sk = check_dfa_sublanguage(&all, &no_sk).unwrap();
        assert_eq!(res_sk, SublanguageResult::Counterexample(b"sk-".to_vec()));

        let res_sql_vs_sk = check_dfa_sublanguage(&no_sql, &no_sk).unwrap();
        assert_eq!(
            res_sql_vs_sk,
            SublanguageResult::Counterexample(b"sk-".to_vec())
        );

        let res_shell = check_dfa_sublanguage(&all, &no_shell).unwrap();
        assert_eq!(res_shell, SublanguageResult::Counterexample(b"$(".to_vec()));

        // Inclusion holds on `no_sk` vs `all` and `no_sk` vs `no_sk`:
        let res_inc = check_dfa_sublanguage(&no_sk, &all).unwrap();
        match res_inc {
            SublanguageResult::Included(cert) => {
                assert!(verify_reachability_cert(&cert, &no_sk, &all));
            }
            SublanguageResult::Counterexample(w) => panic!("unexpected cex: {w:?}"),
        }
    }
}
