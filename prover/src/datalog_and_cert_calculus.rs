//! Certificate composition calculus & Merkelized-EDB stratified Datalog derivation/gap verifier.
//!
//! Unverified Rust mirror of the Lean `Assurance/CertificateAndDatalogCalculus.lean` (W11 Lane 4).
//! Acceptance semantics are pinned to the Lean side by `testdata/cert_datalog_conformance.json`
//! (the toy program, its 16-leaf Merkle EDB with root `839753907`, and the hand certificates).
//!
//! # Shapes (exactly the Lean ones)
//!
//! * **Merkle EDB.** `2^d` leaves `(key, salt)`, MSB-first split:
//!   `root(0,f) = H_leaf(f[0])`, `root(d+1,f) = H_node(root(d,f[..half]), root(d,f[half..]))`.
//!   A path is the sibling list **top-down** (root-level sibling first), of length exactly `d`;
//!   [`recompute_root`] rejects (returns `None`) a path of the wrong length or `i >= 2^d`.
//!   Leaf layout: index 0 is the bottom sentinel `(⊥, salt)`, indices `1..=n` hold the facts
//!   sorted strictly ascending by key, then top sentinels `(⊤, salt)` pad to `2^d` (at least one).
//! * **Datalog.** Stratified programs with negation ([`Program::new`] checks heads are IDB,
//!   `st(pos) <= st(head)`, `st(neg) < st(head)`, EDB at stratum 0, safety); [`compute_strata`]
//!   rejects unstratifiable programs (`p :- ¬p`). [`solve`] is a semi-naive bottom-up solver with
//!   lazily built hash indexes, recording for each derived fact its first-derivation round
//!   (`level`) and justification `(rule_id, subst)`.
//! * **Certificate** = list of [`Claim`] `{atom, pos, rank, just}` with `just` one of
//!   `Memb` (positive EDB: Merkle opening of `(enc atom, salt)`), `Rule` (positive IDB: rule
//!   instance whose body claims have strictly smaller rank), `Gap` (negative EDB: two openings at
//!   **adjacent** indices `i, i+1` with `left.key < enc atom < right.key`), `Unf` (negative IDB:
//!   an unfounded set `u ∋ atom` all of whose rule instances are blocked). [`verify_cert`] checks
//!   every claim and that some claim is `(query, sign)`. Rank strictness forbids `p :- p`.
//!
//! # Fail-closed `Unf` enumeration
//!
//! Lean proves the `Unf` rule over the *ground* program. Rust enumerates rule instances whose head
//! lies in `u` by matching the rule head; this equals the grounding only when every body variable
//! occurs in the head (**head-covering**, ≤ 1 instance per `(rule, head atom)`). If any rule whose
//! head predicate matches an atom of `u` is not head-covering, the verifier REJECTS the `Unf`
//! claim ([`CertErrorKind::UnfNonHeadCovering`]) and the generator returns
//! [`CertGenError::NonHeadCovering`]. In the policy program, `can` and `trusted` have
//! non-head-covering rules (`can(u,r) :- member(u,g), group_grant(g,r)`;
//! `trusted(b) :- trusted(a), delegates(a,b)`), so `¬can(..)` / `¬trusted(..)` are not
//! certifiable here; `allowed` and `alert` rules are head-covering, so `¬allowed` (when blocked by
//! a `revoked` fact) and `¬alert` are.
//!
//! # Generator ranks (stratum-local rounds)
//!
//! Lean uses least positive derivation depth. Both choices satisfy the strict rank check.
//! With `W = max_level + 3`: `Gap` rank 0; `Unf` claim for a stratum-`s` atom rank `s·W + 1`;
//! positive claim of an atom of stratum `s` at derivation level `ℓ` rank `s·W + 2 + ℓ` (EDB facts
//! are level 1 of stratum 0; stratum-0 IDB starts at level 2). Only claims reachable from the
//! query are emitted. The generator uses the solver's first derivation for each positive atom
//! (it does not search alternative derivations), and for `Unf` picks, per blocked instance, a
//! true negated atom first, then a false lower-stratum positive atom, then adds a false
//! same-stratum IDB atom to `u`.
//!
//! # Real hash and key encoding ([`Sha3Hasher`])
//!
//! `K = Vec<u8>` with `⊥ = []`, `⊤ = [0xFF]`. A fact key is `enc(pred, args) = [pred as u8] ||
//! be64(arg_0) || ... || be64(arg_{k-1})` (fixed-width 8-byte big-endian ids; `pred < 0xFF`).
//! Injective: the tag fixes the predicate and the remaining length is `8·k`. Every fact key is
//! nonempty with first byte `< 0xFF`, so `⊥ < key < ⊤` lexicographically; big-endian ids make
//! key order agree with numeric tuple order within a predicate.
//! `leaf = SHA3-256("minidregg.w11.edb.leaf\0" || salt32 || u32le(len key) || key)`,
//! `node = SHA3-256("minidregg.w11.edb.node\0" || l || r)`.
//! Salts are 32 bytes per leaf; [`sha3_leaf_salt`] derives them as a PRF of a secret master seed
//! (`SHA3-256("minidregg.w11.edb.salt\0" || master || u64le(position) || u32le(len key) || key)`);
//! a deployment should use a CSPRNG or keep the master secret.
//!
//! # Leakage (what a certificate reveals)
//!
//! Keys are plaintext and ordered. The leaf hash includes a salt. For the minimal padded tree
//! of `commit_facts`, public depth d implies 2^(d-1) < n+2 <= 2^d. Members disclose their
//! key, salt, index j (j-1 smaller facts) and sibling hashes. A gap discloses both keys and
//! salts, adjacent indices, the absence interval and exactly i facts below the query. Opening
//! the first top sentinel gives the exact fact count. Repeated openings link positions and
//! shared path digests. Rules disclose substitutions, and Unf discloses its whole set.
//! Hiding unopened keys requires secret unpredictable salts and a hash-hiding assumption.
//! The deterministic public test master provides reproducibility only.
//!
//! # ComposedByteTurnCert
//!
//! One shared salted byte commitment `byte_root = SHA3-256("minidregg.w11.turn.bytes\0" || salt32
//! || u64le(len) || bytes)` with the bytes **opened to the verifier** (the salt hides the bytes from
//! anyone who sees only the root, e.g. a log of roots; it does not hide them from this verifier).
//! It binds (a) a byte-DFA run certificate, (b) a Datalog authorization certificate for
//! `allowed(user, tool)`, (c) a canonical-BPE token-projection certificate. All three sub-certs name
//! the byte root, and a transcript digest binds root, EDB commitment, user, tool, table digests and
//! the sub-cert payloads. The verifier context projects the user/tool pair from the opened
//! bytes. The fixture uses the canonical header accepted by [`text_request_ids`]. See [`verify_composed_turn`].

#![deny(warnings)]

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use sha3::{Digest, Sha3_256};

// ===================================================================================
// Wire encoding
// ===================================================================================

/// Canonical byte encoding used for certificate serialization ([`encode_cert`]).
pub trait Wire: Sized {
    fn write(&self, out: &mut Vec<u8>);
    fn read(inp: &mut &[u8]) -> Option<Self>;
}

fn take<'a>(inp: &mut &'a [u8], n: usize) -> Option<&'a [u8]> {
    if inp.len() < n {
        return None;
    }
    let (a, b) = inp.split_at(n);
    *inp = b;
    Some(a)
}
fn read_u8(inp: &mut &[u8]) -> Option<u8> {
    take(inp, 1).map(|b| b[0])
}
fn read_u16(inp: &mut &[u8]) -> Option<u16> {
    take(inp, 2).map(|b| u16::from_le_bytes([b[0], b[1]]))
}
fn read_u32(inp: &mut &[u8]) -> Option<u32> {
    take(inp, 4).map(|b| u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
}

impl Wire for u64 {
    fn write(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.to_le_bytes());
    }
    fn read(inp: &mut &[u8]) -> Option<Self> {
        let b = take(inp, 8)?;
        let mut a = [0u8; 8];
        a.copy_from_slice(b);
        Some(u64::from_le_bytes(a))
    }
}
impl Wire for [u8; 32] {
    fn write(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(self);
    }
    fn read(inp: &mut &[u8]) -> Option<Self> {
        let b = take(inp, 32)?;
        let mut a = [0u8; 32];
        a.copy_from_slice(b);
        Some(a)
    }
}
impl Wire for Vec<u8> {
    fn write(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&(self.len() as u32).to_le_bytes());
        out.extend_from_slice(self);
    }
    fn read(inp: &mut &[u8]) -> Option<Self> {
        let n = read_u32(inp)? as usize;
        take(inp, n).map(|b| b.to_vec())
    }
}

// ===================================================================================
// Datalog syntax
// ===================================================================================

/// Ground atom: predicate id and constant arguments.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Atom {
    pub pred: u32,
    pub args: Vec<u64>,
}

impl Atom {
    pub fn new(pred: u32, args: Vec<u64>) -> Self {
        Atom { pred, args }
    }
    /// 0-ary atom (used by the toy).
    pub fn prop(pred: u32) -> Self {
        Atom { pred, args: Vec::new() }
    }
}

/// Rule term: variable (dense index) or constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    Var(u32),
    Const(u64),
}

/// Non-ground atom pattern.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pattern {
    pub pred: u32,
    pub args: Vec<Term>,
}

impl Pattern {
    pub fn new(pred: u32, args: Vec<Term>) -> Self {
        Pattern { pred, args }
    }
    pub fn prop(pred: u32) -> Self {
        Pattern { pred, args: Vec::new() }
    }
    /// Instantiate under a total substitution (`None` if a variable index is out of range).
    pub fn instantiate(&self, subst: &[u64]) -> Option<Atom> {
        let mut args = Vec::with_capacity(self.args.len());
        for t in &self.args {
            args.push(match *t {
                Term::Const(c) => c,
                Term::Var(v) => *subst.get(v as usize)?,
            });
        }
        Some(Atom { pred: self.pred, args })
    }
    fn vars(&self) -> impl Iterator<Item = u32> + '_ {
        self.args.iter().filter_map(|t| match *t {
            Term::Var(v) => Some(v),
            Term::Const(_) => None,
        })
    }
}

/// `head :- pos_1, .., pos_m, ¬neg_1, .., ¬neg_k`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    pub head: Pattern,
    pub pos: Vec<Pattern>,
    pub neg: Vec<Pattern>,
}

impl Rule {
    pub fn new(head: Pattern, pos: Vec<Pattern>, neg: Vec<Pattern>) -> Self {
        Rule { head, pos, neg }
    }
}

/// Program well-formedness errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramError {
    LengthMismatch,
    ArityTooLarge { pred: u32 },
    EdbNotStratumZero { pred: u32 },
    PredOutOfRange { rule: usize, pred: u32 },
    ArityMismatch { rule: usize, pred: u32 },
    EdbHead { rule: usize },
    PosStratum { rule: usize },
    NegStratum { rule: usize },
    Unsafe { rule: usize, var: u32 },
    Unstratifiable { pred: u32 },
    SubstitutionTooLarge { rule: usize },
}

/// A checked stratified program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    arity: Vec<usize>,
    is_edb: Vec<bool>,
    stratum: Vec<u32>,
    rules: Vec<Rule>,
    num_vars: Vec<usize>,
    head_covering: Vec<bool>,
    rules_by_head: Vec<Vec<usize>>,
}

fn check_pattern(n: usize, arity: &[usize], rule: usize, p: &Pattern) -> Result<(), ProgramError> {
    if p.pred as usize >= n {
        return Err(ProgramError::PredOutOfRange { rule, pred: p.pred });
    }
    if p.args.len() != arity[p.pred as usize] {
        return Err(ProgramError::ArityMismatch { rule, pred: p.pred });
    }
    Ok(())
}

impl Program {
    /// Check well-formedness: lengths, arities (≤ 64), EDB at stratum 0, heads IDB,
    /// `st(pos) <= st(head)`, `st(neg) < st(head)`, safety (every head/neg variable occurs in a
    /// positive body atom). Also records per-rule variable count and head-coverage.
    pub fn new(
        arity: Vec<usize>,
        is_edb: Vec<bool>,
        stratum: Vec<u32>,
        rules: Vec<Rule>,
    ) -> Result<Self, ProgramError> {
        let n = arity.len();
        if is_edb.len() != n || stratum.len() != n {
            return Err(ProgramError::LengthMismatch);
        }
        for p in 0..n {
            if arity[p] > 64 {
                return Err(ProgramError::ArityTooLarge { pred: p as u32 });
            }
            if is_edb[p] && stratum[p] != 0 {
                return Err(ProgramError::EdbNotStratumZero { pred: p as u32 });
            }
        }
        let mut num_vars = Vec::with_capacity(rules.len());
        let mut head_covering = Vec::with_capacity(rules.len());
        let mut rules_by_head = vec![Vec::new(); n];
        for (rid, r) in rules.iter().enumerate() {
            check_pattern(n, &arity, rid, &r.head)?;
            for p in r.pos.iter().chain(r.neg.iter()) {
                check_pattern(n, &arity, rid, p)?;
            }
            let h = r.head.pred as usize;
            if is_edb[h] {
                return Err(ProgramError::EdbHead { rule: rid });
            }
            if r.pos.iter().any(|p| stratum[p.pred as usize] > stratum[h]) {
                return Err(ProgramError::PosStratum { rule: rid });
            }
            if r.neg.iter().any(|p| stratum[p.pred as usize] >= stratum[h]) {
                return Err(ProgramError::NegStratum { rule: rid });
            }
            let pos_vars: HashSet<u32> = r.pos.iter().flat_map(|p| p.vars()).collect();
            for v in r.head.vars().chain(r.neg.iter().flat_map(|p| p.vars())) {
                if !pos_vars.contains(&v) {
                    return Err(ProgramError::Unsafe { rule: rid, var: v });
                }
            }
            let head_vars: HashSet<u32> = r.head.vars().collect();
            let covering = r
                .pos
                .iter()
                .chain(r.neg.iter())
                .flat_map(|p| p.vars())
                .all(|v| head_vars.contains(&v));
            let max_var = r
                .head
                .vars()
                .chain(r.pos.iter().flat_map(|p| p.vars()))
                .chain(r.neg.iter().flat_map(|p| p.vars()))
                .max();
            if max_var.is_some_and(|v| v >= u16::MAX as u32) {
                return Err(ProgramError::SubstitutionTooLarge { rule: rid });
            }
            num_vars.push(max_var.map_or(0, |v| v as usize + 1));
            head_covering.push(covering);
            rules_by_head[h].push(rid);
        }
        Ok(Program { arity, is_edb, stratum, rules, num_vars, head_covering, rules_by_head })
    }

    pub fn num_preds(&self) -> usize {
        self.arity.len()
    }
    pub fn rules(&self) -> &[Rule] {
        &self.rules
    }
    pub fn is_edb(&self, pred: u32) -> bool {
        self.is_edb.get(pred as usize).copied().unwrap_or(false)
    }
    pub fn stratum(&self, pred: u32) -> u32 {
        self.stratum[pred as usize]
    }
    pub fn arity(&self, pred: u32) -> usize {
        self.arity[pred as usize]
    }
    pub fn num_vars(&self, rule: usize) -> usize {
        self.num_vars[rule]
    }
    /// Every body variable occurs in the head (≤ 1 instance per `(rule, head atom)`).
    pub fn is_head_covering(&self, rule: usize) -> bool {
        self.head_covering[rule]
    }
    pub fn max_stratum(&self) -> u32 {
        self.stratum.iter().copied().max().unwrap_or(0)
    }
    /// Well-formed atom: predicate in range, arity matches.
    pub fn atom_ok(&self, a: &Atom) -> bool {
        (a.pred as usize) < self.arity.len() && a.args.len() == self.arity[a.pred as usize]
    }
    /// Ground instance `rule[rule_id] · subst` as `(head, pos body, neg body)`.
    pub fn instance(&self, rule_id: usize, subst: &[u64]) -> Option<(Atom, Vec<Atom>, Vec<Atom>)> {
        let r = self.rules.get(rule_id)?;
        if subst.len() != self.num_vars[rule_id] {
            return None;
        }
        let head = r.head.instantiate(subst)?;
        let pos = r.pos.iter().map(|p| p.instantiate(subst)).collect::<Option<Vec<_>>>()?;
        let neg = r.neg.iter().map(|p| p.instantiate(subst)).collect::<Option<Vec<_>>>()?;
        Some((head, pos, neg))
    }
    /// For a head-covering rule, the unique substitution whose head instance is `atom`, if any.
    fn match_head(&self, rule_id: usize, atom: &Atom) -> Option<Vec<u64>> {
        let r = &self.rules[rule_id];
        if r.head.pred != atom.pred || r.head.args.len() != atom.args.len() {
            return None;
        }
        let mut b: Vec<Option<u64>> = vec![None; self.num_vars[rule_id]];
        for (t, &c) in r.head.args.iter().zip(atom.args.iter()) {
            match *t {
                Term::Const(k) => {
                    if k != c {
                        return None;
                    }
                }
                Term::Var(v) => match b[v as usize] {
                    Some(x) if x != c => return None,
                    _ => b[v as usize] = Some(c),
                },
            }
        }
        Some(b.into_iter().map(|x| x.unwrap_or(0)).collect())
    }
}

/// Least stratification (or `Unstratifiable` when a negative cycle exists, e.g. `p :- ¬p`).
pub fn compute_strata(
    arity: &[usize],
    is_edb: &[bool],
    rules: &[Rule],
) -> Result<Vec<u32>, ProgramError> {
    let n = arity.len();
    if is_edb.len() != n {
        return Err(ProgramError::LengthMismatch);
    }
    for (rid, r) in rules.iter().enumerate() {
        check_pattern(n, arity, rid, &r.head)?;
        for p in r.pos.iter().chain(r.neg.iter()) {
            check_pattern(n, arity, rid, p)?;
        }
        if is_edb[r.head.pred as usize] {
            return Err(ProgramError::EdbHead { rule: rid });
        }
    }
    let mut st = vec![0u32; n];
    loop {
        let mut changed = false;
        for r in rules {
            let h = r.head.pred as usize;
            for p in &r.pos {
                if st[p.pred as usize] > st[h] {
                    st[h] = st[p.pred as usize];
                    changed = true;
                }
            }
            for p in &r.neg {
                if st[p.pred as usize] + 1 > st[h] {
                    st[h] = st[p.pred as usize] + 1;
                    changed = true;
                }
            }
            if st[h] as usize > n {
                return Err(ProgramError::Unstratifiable { pred: h as u32 });
            }
        }
        if !changed {
            return Ok(st);
        }
    }
}

// ===================================================================================
// Solver
// ===================================================================================

#[derive(Default)]
struct Relation {
    tuples: Vec<Box<[u64]>>,
    lookup: HashMap<Box<[u64]>, u32>,
    level: Vec<u32>,
    prov: Vec<Option<(u32, Box<[u64]>)>>,
    indexes: HashMap<u64, HashMap<Box<[u64]>, Vec<u32>>>,
}

fn project(t: &[u64], mask: u64) -> Box<[u64]> {
    t.iter().enumerate().filter(|(i, _)| mask >> i & 1 == 1).map(|(_, &x)| x).collect()
}

impl Relation {
    fn insert(&mut self, t: Box<[u64]>, level: u32, prov: Option<(u32, Box<[u64]>)>) -> bool {
        if self.lookup.contains_key(&t) {
            return false;
        }
        let idx = self.tuples.len() as u32;
        for (mask, ix) in self.indexes.iter_mut() {
            ix.entry(project(&t, *mask)).or_default().push(idx);
        }
        self.lookup.insert(t.clone(), idx);
        self.tuples.push(t);
        self.level.push(level);
        self.prov.push(prov);
        true
    }
    fn ensure_index(&mut self, mask: u64) {
        if self.indexes.contains_key(&mask) {
            return;
        }
        let mut ix: HashMap<Box<[u64]>, Vec<u32>> = HashMap::new();
        for (i, t) in self.tuples.iter().enumerate() {
            ix.entry(project(t, mask)).or_default().push(i as u32);
        }
        self.indexes.insert(mask, ix);
    }
}

#[derive(Clone, Copy)]
enum ArgOp {
    Const(u64),
    Bound(u32),
    Bind(u32),
    Check(u32),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Access {
    Scan,
    Lookup,
    Index,
}

struct Step {
    pred: u32,
    ops: Vec<ArgOp>,
    mask: u64,
    access: Access,
    delta: bool,
}

struct Plan {
    rule: usize,
    steps: Vec<Step>,
}

fn build_plan(rule_id: usize, r: &Rule, num_vars: usize, order: &[usize], delta: Option<usize>) -> Plan {
    let mut bound = vec![false; num_vars];
    let mut steps = Vec::new();
    for &pi in order {
        let p = &r.pos[pi];
        let mut ops = Vec::with_capacity(p.args.len());
        let mut mask = 0u64;
        let mut newly: Vec<u32> = Vec::new();
        for (i, t) in p.args.iter().enumerate() {
            match *t {
                Term::Const(c) => {
                    ops.push(ArgOp::Const(c));
                    mask |= 1 << i;
                }
                Term::Var(v) => {
                    if bound[v as usize] {
                        ops.push(ArgOp::Bound(v));
                        mask |= 1 << i;
                    } else if newly.contains(&v) {
                        ops.push(ArgOp::Check(v));
                    } else {
                        ops.push(ArgOp::Bind(v));
                        newly.push(v);
                    }
                }
            }
        }
        for v in newly {
            bound[v as usize] = true;
        }
        let full = if p.args.len() == 64 { u64::MAX } else { (1u64 << p.args.len()) - 1 };
        let access = if mask == full {
            Access::Lookup
        } else if mask == 0 {
            Access::Scan
        } else {
            Access::Index
        };
        steps.push(Step { pred: p.pred, ops, mask, access, delta: delta == Some(pi) });
    }
    Plan { rule: rule_id, steps }
}

struct Derived {
    pred: u32,
    tuple: Box<[u64]>,
    rule: u32,
    subst: Box<[u64]>,
}

struct JoinCtx<'a> {
    rels: &'a [Relation],
    plan: &'a Plan,
    rule: &'a Rule,
    snap: &'a [u32],
    dlo: &'a [u32],
}

fn inst_vec(p: &Pattern, b: &[u64]) -> Vec<u64> {
    p.args
        .iter()
        .map(|t| match *t {
            Term::Const(c) => c,
            Term::Var(v) => b[v as usize],
        })
        .collect()
}

fn join(ctx: &JoinCtx, i: usize, binding: &mut Vec<u64>, out: &mut Vec<Derived>) {
    if i == ctx.plan.steps.len() {
        for n in &ctx.rule.neg {
            let t = inst_vec(n, binding);
            if ctx.rels[n.pred as usize].lookup.contains_key(&t[..]) {
                return;
            }
        }
        let h = &ctx.rule.head;
        let t = inst_vec(h, binding);
        if ctx.rels[h.pred as usize].lookup.contains_key(&t[..]) {
            return;
        }
        out.push(Derived {
            pred: h.pred,
            tuple: t.into_boxed_slice(),
            rule: ctx.plan.rule as u32,
            subst: binding.clone().into_boxed_slice(),
        });
        return;
    }
    let step = &ctx.plan.steps[i];
    let pi = step.pred as usize;
    let rel = &ctx.rels[pi];
    let hi = ctx.snap[pi];
    let lo = if step.delta { ctx.dlo[pi] } else { 0 };
    if lo >= hi {
        return;
    }
    let key = || -> Vec<u64> {
        step.ops
            .iter()
            .filter_map(|op| match *op {
                ArgOp::Const(c) => Some(c),
                ArgOp::Bound(v) => Some(binding[v as usize]),
                _ => None,
            })
            .collect()
    };
    let try_tuple = |idx: u32, binding: &mut Vec<u64>, out: &mut Vec<Derived>| {
        let t = &rel.tuples[idx as usize];
        for (pos, op) in step.ops.iter().enumerate() {
            match *op {
                ArgOp::Bind(v) => binding[v as usize] = t[pos],
                ArgOp::Check(v) => {
                    if binding[v as usize] != t[pos] {
                        return;
                    }
                }
                _ => {}
            }
        }
        join(ctx, i + 1, binding, out);
    };
    match step.access {
        Access::Scan => {
            for idx in lo..hi {
                try_tuple(idx, binding, out);
            }
        }
        Access::Lookup => {
            let k = key();
            if let Some(&idx) = rel.lookup.get(&k[..]) {
                if idx >= lo && idx < hi {
                    try_tuple(idx, binding, out);
                }
            }
        }
        Access::Index => {
            let k = key();
            if let Some(list) = rel.indexes.get(&step.mask).and_then(|ix| ix.get(&k[..])) {
                let start = list.partition_point(|&x| x < lo);
                for &idx in &list[start..] {
                    if idx >= hi {
                        break;
                    }
                    try_tuple(idx, binding, out);
                }
            }
        }
    }
}

/// Solver input errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SolveError {
    Malformed(Atom),
    NotEdb(Atom),
}

/// The perfect model with per-fact level and first-derivation justification.
pub struct Model {
    program: Program,
    rels: Vec<Relation>,
    max_level: u32,
}

impl Model {
    pub fn holds(&self, a: &Atom) -> bool {
        self.rels.get(a.pred as usize).map(|r| r.lookup.contains_key(&a.args[..])).unwrap_or(false)
    }
    fn idx(&self, a: &Atom) -> Option<(usize, usize)> {
        let r = self.rels.get(a.pred as usize)?;
        r.lookup.get(&a.args[..]).map(|&i| (a.pred as usize, i as usize))
    }
    /// Derivation round (EDB facts: 1).
    pub fn level(&self, a: &Atom) -> Option<u32> {
        self.idx(a).map(|(p, i)| self.rels[p].level[i])
    }
    /// First-derivation `(rule_id, subst)` of an IDB fact.
    pub fn provenance(&self, a: &Atom) -> Option<(u32, &[u64])> {
        let (p, i) = self.idx(a)?;
        self.rels[p].prov[i].as_ref().map(|(r, s)| (*r, &s[..]))
    }
    pub fn max_level(&self) -> u32 {
        self.max_level
    }
    pub fn count(&self, pred: u32) -> usize {
        self.rels[pred as usize].tuples.len()
    }
    pub fn tuples(&self, pred: u32) -> &[Box<[u64]>] {
        &self.rels[pred as usize].tuples
    }
}

/// Stratified semi-naive bottom-up evaluation.
pub fn solve(program: &Program, edb: &[Atom]) -> Result<Model, SolveError> {
    let n = program.num_preds();
    let mut rels: Vec<Relation> = (0..n).map(|_| Relation::default()).collect();
    for a in edb {
        if !program.atom_ok(a) {
            return Err(SolveError::Malformed(a.clone()));
        }
        if !program.is_edb(a.pred) {
            return Err(SolveError::NotEdb(a.clone()));
        }
        rels[a.pred as usize].insert(a.args.clone().into_boxed_slice(), 1, None);
    }
    let mut max_level = 1u32;
    let strata: BTreeSet<_> = program.rules.iter().map(|r| program.stratum(r.head.pred)).collect();
    for s in strata {
        let rule_ids: Vec<usize> = (0..program.rules.len())
            .filter(|&r| program.stratum(program.rules[r].head.pred) == s)
            .collect();
        let rec = |p: u32| !program.is_edb(p) && program.stratum(p) == s;
        let mut full_plans = Vec::new();
        let mut delta_plans = Vec::new();
        for &rid in &rule_ids {
            let r = &program.rules[rid];
            let nv = program.num_vars[rid];
            let order: Vec<usize> = (0..r.pos.len()).collect();
            full_plans.push(build_plan(rid, r, nv, &order, None));
            for d in 0..r.pos.len() {
                if rec(r.pos[d].pred) {
                    let mut o = vec![d];
                    o.extend((0..r.pos.len()).filter(|&x| x != d));
                    delta_plans.push(build_plan(rid, r, nv, &o, Some(d)));
                }
            }
        }
        for pl in full_plans.iter().chain(delta_plans.iter()) {
            for st in &pl.steps {
                if st.access == Access::Index {
                    rels[st.pred as usize].ensure_index(st.mask);
                }
            }
        }
        let offset = if s == 0 { 1 } else { 0 };
        let mut dlo: Vec<u32> = vec![0; n];
        let mut round = 1u32;
        loop {
            let snap: Vec<u32> = rels.iter().map(|r| r.tuples.len() as u32).collect();
            let plans = if round == 1 { &full_plans } else { &delta_plans };
            let mut out = Vec::new();
            for pl in plans {
                let r = &program.rules[pl.rule];
                let ctx = JoinCtx { rels: &rels, plan: pl, rule: r, snap: &snap, dlo: &dlo };
                let mut b = vec![0u64; program.num_vars[pl.rule]];
                join(&ctx, 0, &mut b, &mut out);
            }
            let level = round + offset;
            let mut any = false;
            for d in out {
                if rels[d.pred as usize].insert(d.tuple, level, Some((d.rule, d.subst))) {
                    any = true;
                }
            }
            if !any {
                break;
            }
            max_level = max_level.max(level);
            dlo = snap;
            round += 1;
        }
    }
    Ok(Model { program: program.clone(), rels, max_level })
}

// ===================================================================================
// Merkle EDB
// ===================================================================================

/// Hash/key interface of the Merkle EDB.
pub trait EdbHasher {
    type K: Ord + Clone + Debug + Hash + Wire;
    type S: Clone + Debug + Eq + Wire;
    type D: Clone + Eq + Debug + Wire;
    fn bot(&self) -> Self::K;
    fn top(&self) -> Self::K;
    fn leaf(&self, key: &Self::K, salt: &Self::S) -> Self::D;
    fn node(&self, l: &Self::D, r: &Self::D) -> Self::D;
    /// Injective fact-key encoding with `⊥ < enc(a) < ⊤`; `None` if the atom is not encodable.
    fn enc(&self, atom: &Atom) -> Option<Self::K>;
}

/// Toy hasher (conformance only): `P = 2^31-1`, `leaf(k,s) = (k*1000003 + s*7919 + 17) % P`,
/// `node(l,r) = (l*65599 + r*31 + 3) % P`, `⊥ = 0`, `⊤ = 63`, `enc(a) = a + 1` for 0-ary atoms.
#[derive(Clone, Copy, Debug, Default)]
pub struct ToyHasher;

pub const TOY_P: u64 = 2_147_483_647;
pub const TOY_TOP: u64 = 63;

impl EdbHasher for ToyHasher {
    type K = u64;
    type S = u64;
    type D = u64;
    fn bot(&self) -> u64 {
        0
    }
    fn top(&self) -> u64 {
        TOY_TOP
    }
    fn leaf(&self, k: &u64, s: &u64) -> u64 {
        ((*k as u128 * 1_000_003 + *s as u128 * 7919 + 17) % TOY_P as u128) as u64
    }
    fn node(&self, l: &u64, r: &u64) -> u64 {
        ((*l as u128 * 65599 + *r as u128 * 31 + 3) % TOY_P as u128) as u64
    }
    fn enc(&self, a: &Atom) -> Option<u64> {
        if a.args.is_empty() && (a.pred as u64) + 1 < TOY_TOP {
            Some(a.pred as u64 + 1)
        } else {
            None
        }
    }
}

pub const EDB_LEAF_DOMAIN: &[u8] = b"minidregg.w11.edb.leaf\0";
pub const EDB_NODE_DOMAIN: &[u8] = b"minidregg.w11.edb.node\0";
pub const EDB_SALT_DOMAIN: &[u8] = b"minidregg.w11.edb.salt\0";

fn sha3(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    for p in parts {
        h.update(p);
    }
    h.finalize().into()
}

/// Salted SHA3-256 EDB hasher (see module docs for the domains and key encoding).
#[derive(Clone, Copy, Debug, Default)]
pub struct Sha3Hasher;

impl EdbHasher for Sha3Hasher {
    type K = Vec<u8>;
    type S = [u8; 32];
    type D = [u8; 32];
    fn bot(&self) -> Vec<u8> {
        Vec::new()
    }
    fn top(&self) -> Vec<u8> {
        vec![0xFF]
    }
    fn leaf(&self, k: &Vec<u8>, s: &[u8; 32]) -> [u8; 32] {
        sha3(&[EDB_LEAF_DOMAIN, s, &(k.len() as u32).to_le_bytes(), k])
    }
    fn node(&self, l: &[u8; 32], r: &[u8; 32]) -> [u8; 32] {
        sha3(&[EDB_NODE_DOMAIN, l, r])
    }
    fn enc(&self, a: &Atom) -> Option<Vec<u8>> {
        if a.pred >= 0xFF {
            return None;
        }
        let mut k = Vec::with_capacity(1 + 8 * a.args.len());
        k.push(a.pred as u8);
        for x in &a.args {
            k.extend_from_slice(&x.to_be_bytes());
        }
        Some(k)
    }
}

/// Per-leaf salt as a PRF of a secret master seed, the leaf position and its key.
pub fn sha3_leaf_salt(master: &[u8; 32], position: usize, key: &[u8]) -> [u8; 32] {
    sha3(&[
        EDB_SALT_DOMAIN,
        master,
        &(position as u64).to_le_bytes(),
        &(key.len() as u32).to_le_bytes(),
        key,
    ])
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Leaf<K, S> {
    pub key: K,
    pub salt: S,
}

/// Public EDB commitment: Merkle root and depth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EdbCommitment<D> {
    pub root: D,
    pub depth: u32,
}

/// `rec(d, i, leaf, path)` (path top-down). `None` if `path.len() != d` or `i >= 2^d`.
pub fn recompute_root<H: EdbHasher>(
    h: &H,
    depth: u32,
    index: u64,
    leaf: &Leaf<H::K, H::S>,
    path: &[H::D],
) -> Option<H::D> {
    if depth >= 64 || path.len() != depth as usize || index >= (1u64 << depth) {
        return None;
    }
    let d = depth as usize;
    let mut acc = h.leaf(&leaf.key, &leaf.salt);
    for t in 0..d {
        let sib = &path[d - 1 - t];
        acc = if (index >> t) & 1 == 0 { h.node(&acc, sib) } else { h.node(sib, &acc) };
    }
    Some(acc)
}

fn opening_ok<H: EdbHasher>(
    h: &H,
    com: &EdbCommitment<H::D>,
    index: u64,
    leaf: &Leaf<H::K, H::S>,
    path: &[H::D],
) -> bool {
    recompute_root(h, com.depth, index, leaf, path).map(|r| r == com.root).unwrap_or(false)
}

/// EDB construction errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EdbError {
    WrongLeafCount,
    DepthTooLarge,
    BadBottom,
    NoTop,
    NotStrictlySorted { index: usize },
    KeyOutOfRange { index: usize },
    Unencodable(Atom),
    NotEdb(Atom),
}

/// Sorted salted Merkle tree over the EDB.
pub struct EdbTree<H: EdbHasher> {
    depth: u32,
    leaves: Vec<Leaf<H::K, H::S>>,
    levels: Vec<Vec<H::D>>,
}

impl<H: EdbHasher> EdbTree<H> {
    /// Build from an explicit leaf vector, checking the Lean layout (⊥ at 0, strictly ascending
    /// fact keys strictly between ⊥ and ⊤, then ≥ 1 ⊤ padding).
    pub fn from_leaves(h: &H, depth: u32, leaves: Vec<Leaf<H::K, H::S>>) -> Result<Self, EdbError> {
        if depth >= 40 {
            return Err(EdbError::DepthTooLarge);
        }
        if leaves.len() != 1usize << depth {
            return Err(EdbError::WrongLeafCount);
        }
        let (bot, top) = (h.bot(), h.top());
        if leaves[0].key != bot {
            return Err(EdbError::BadBottom);
        }
        let first_top = leaves.iter().position(|l| l.key == top).ok_or(EdbError::NoTop)?;
        for i in 1..leaves.len() {
            if i < first_top {
                if !(leaves[i].key > bot && leaves[i].key < top) {
                    return Err(EdbError::KeyOutOfRange { index: i });
                }
                if leaves[i].key <= leaves[i - 1].key {
                    return Err(EdbError::NotStrictlySorted { index: i });
                }
            } else if leaves[i].key != top {
                return Err(EdbError::KeyOutOfRange { index: i });
            }
        }
        let mut levels = vec![leaves.iter().map(|l| h.leaf(&l.key, &l.salt)).collect::<Vec<_>>()];
        for t in 0..depth as usize {
            let prev = &levels[t];
            let next: Vec<H::D> = prev.chunks(2).map(|c| h.node(&c[0], &c[1])).collect();
            levels.push(next);
        }
        Ok(EdbTree { depth, leaves, levels })
    }

    /// Commit a fact set: encode, sort, dedupe, pad to the least `2^d >= n + 2`.
    /// `salt(key, position)` supplies each leaf salt (sentinels included).
    pub fn commit_facts(
        h: &H,
        program: &Program,
        facts: &[Atom],
        mut salt: impl FnMut(&H::K, usize) -> H::S,
    ) -> Result<Self, EdbError> {
        let mut keys = Vec::with_capacity(facts.len());
        for a in facts {
            if !program.is_edb(a.pred) || !program.atom_ok(a) {
                return Err(EdbError::NotEdb(a.clone()));
            }
            keys.push(h.enc(a).ok_or_else(|| EdbError::Unencodable(a.clone()))?);
        }
        keys.sort();
        keys.dedup();
        let mut depth = 0u32;
        while (1usize << depth) < keys.len() + 2 {
            depth += 1;
        }
        let total = 1usize << depth;
        let mut leaves = Vec::with_capacity(total);
        let bot = h.bot();
        leaves.push(Leaf { salt: salt(&bot, 0), key: bot });
        for k in keys {
            let p = leaves.len();
            leaves.push(Leaf { salt: salt(&k, p), key: k });
        }
        let top = h.top();
        while leaves.len() < total {
            let p = leaves.len();
            leaves.push(Leaf { salt: salt(&top, p), key: top.clone() });
        }
        Self::from_leaves(h, depth, leaves)
    }

    pub fn depth(&self) -> u32 {
        self.depth
    }
    pub fn root(&self) -> H::D {
        self.levels[self.depth as usize][0].clone()
    }
    pub fn commitment(&self) -> EdbCommitment<H::D> {
        EdbCommitment { root: self.root(), depth: self.depth }
    }
    pub fn leaves(&self) -> &[Leaf<H::K, H::S>] {
        &self.leaves
    }
    pub fn leaf_hashes(&self) -> &[H::D] {
        &self.levels[0]
    }
    /// Sibling path for leaf `i`, top-down.
    pub fn path(&self, i: usize) -> Vec<H::D> {
        (0..self.depth as usize).rev().map(|t| self.levels[t][(i >> t) ^ 1].clone()).collect()
    }
    /// `Ok(index)` if the key is a leaf; `Err(insertion point)` otherwise.
    pub fn find_key(&self, k: &H::K) -> Result<usize, usize> {
        self.leaves.binary_search_by(|l| l.key.cmp(k))
    }
}

// ===================================================================================
// Certificates
// ===================================================================================

/// Claim justification (exactly the Lean constructors).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Just<K, S, D> {
    /// Positive EDB fact: opening of `(enc atom, salt)` at index `j`.
    Memb { j: u64, salt: S, path: Vec<D> },
    /// Positive IDB fact: `rule[rule_id] · subst`.
    Rule { rule_id: u32, subst: Vec<u64> },
    /// Negative EDB fact: adjacent openings at `i`, `i + 1` bracketing `enc atom`.
    Gap { i: u64, left: Leaf<K, S>, left_path: Vec<D>, right: Leaf<K, S>, right_path: Vec<D> },
    /// Negative IDB fact: unfounded set `u ∋ atom`.
    Unf { u: Vec<Atom> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim<K, S, D> {
    pub atom: Atom,
    pub pos: bool,
    pub rank: u64,
    pub just: Just<K, S, D>,
}

pub type ToyClaim = Claim<u64, u64, u64>;
pub type Sha3Claim = Claim<Vec<u8>, [u8; 32], [u8; 32]>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertErrorKind {
    MalformedAtom,
    Unencodable,
    MembSign,
    MembNotEdb,
    MembOpening,
    RuleSign,
    RuleNotIdb,
    RuleInstance,
    RuleHeadMismatch,
    PosBodyUnclaimed(Atom),
    NegBodyUnclaimed(Atom),
    GapSign,
    GapNotEdb,
    GapIndex,
    GapOpening,
    GapOrder,
    UnfSign,
    UnfNotMember,
    UnfNotIdb(Atom),
    UnfNonHeadCovering { rule: usize },
    UnfUnblocked { rule: usize, head: Atom },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertError {
    Claim { index: usize, kind: CertErrorKind },
    QueryNotClaimed,
}

/// Verify every claim against the program and EDB commitment, and that some claim is
/// `(query, sign)`. Cost `O(|cert| · d)` hashes plus hash-map lookups.
pub fn verify_cert<H: EdbHasher>(
    h: &H,
    program: &Program,
    com: &EdbCommitment<H::D>,
    claims: &[Claim<H::K, H::S, H::D>],
    query: &Atom,
    sign: bool,
) -> Result<(), CertError> {
    let mut min_rank: HashMap<(&Atom, bool), u64> = HashMap::with_capacity(claims.len());
    for c in claims {
        let e = min_rank.entry((&c.atom, c.pos)).or_insert(c.rank);
        if c.rank < *e {
            *e = c.rank;
        }
    }
    let below = |a: &Atom, pos: bool, rank: u64| min_rank.get(&(a, pos)).map(|&r| r < rank).unwrap_or(false);
    for (index, c) in claims.iter().enumerate() {
        let err = |kind| Err(CertError::Claim { index, kind });
        if !program.atom_ok(&c.atom) {
            return err(CertErrorKind::MalformedAtom);
        }
        let edb = program.is_edb(c.atom.pred);
        match &c.just {
            Just::Memb { j, salt, path } => {
                if !c.pos {
                    return err(CertErrorKind::MembSign);
                }
                if !edb {
                    return err(CertErrorKind::MembNotEdb);
                }
                let Some(key) = h.enc(&c.atom) else { return err(CertErrorKind::Unencodable) };
                if !opening_ok(h, com, *j, &Leaf { key, salt: salt.clone() }, path) {
                    return err(CertErrorKind::MembOpening);
                }
            }
            Just::Rule { rule_id, subst } => {
                if !c.pos {
                    return err(CertErrorKind::RuleSign);
                }
                if edb {
                    return err(CertErrorKind::RuleNotIdb);
                }
                let Some((head, pos, neg)) = program.instance(*rule_id as usize, subst) else {
                    return err(CertErrorKind::RuleInstance);
                };
                if head != c.atom {
                    return err(CertErrorKind::RuleHeadMismatch);
                }
                for b in pos {
                    if !below(&b, true, c.rank) {
                        return err(CertErrorKind::PosBodyUnclaimed(b));
                    }
                }
                for b in neg {
                    if !below(&b, false, c.rank) {
                        return err(CertErrorKind::NegBodyUnclaimed(b));
                    }
                }
            }
            Just::Gap { i, left, left_path, right, right_path } => {
                if c.pos {
                    return err(CertErrorKind::GapSign);
                }
                if !edb {
                    return err(CertErrorKind::GapNotEdb);
                }
                if com.depth >= 64 || i.checked_add(1).map(|x| x >= (1u64 << com.depth)).unwrap_or(true) {
                    return err(CertErrorKind::GapIndex);
                }
                if !opening_ok(h, com, *i, left, left_path) || !opening_ok(h, com, *i + 1, right, right_path) {
                    return err(CertErrorKind::GapOpening);
                }
                let Some(key) = h.enc(&c.atom) else { return err(CertErrorKind::Unencodable) };
                if !(h.bot() <= left.key && left.key < key && key < right.key && right.key <= h.top()) {
                    return err(CertErrorKind::GapOrder);
                }
            }
            Just::Unf { u } => {
                if c.pos {
                    return err(CertErrorKind::UnfSign);
                }
                if !u.contains(&c.atom) {
                    return err(CertErrorKind::UnfNotMember);
                }
                for a in u {
                    if !program.atom_ok(a) || program.is_edb(a.pred) {
                        return err(CertErrorKind::UnfNotIdb(a.clone()));
                    }
                }
                // Fail closed before enumerating: every rule for a predicate of `u` must be
                // head-covering, else Rust's enumeration may miss ground instances.
                for a in u {
                    for &rid in &program.rules_by_head[a.pred as usize] {
                        if !program.head_covering[rid] {
                            return err(CertErrorKind::UnfNonHeadCovering { rule: rid });
                        }
                    }
                }
                let uset: HashSet<&Atom> = u.iter().collect();
                for a in u {
                    for &rid in &program.rules_by_head[a.pred as usize] {
                        let Some(subst) = program.match_head(rid, a) else { continue };
                        let Some((_, pos, neg)) = program.instance(rid, &subst) else {
                            return err(CertErrorKind::UnfUnblocked { rule: rid, head: a.clone() });
                        };
                        let blocked = pos.iter().any(|b| uset.contains(b) || below(b, false, c.rank))
                            || neg.iter().any(|b| below(b, true, c.rank));
                        if !blocked {
                            return err(CertErrorKind::UnfUnblocked { rule: rid, head: a.clone() });
                        }
                    }
                }
            }
        }
    }
    if claims.iter().any(|c| c.pos == sign && c.atom == *query) {
        Ok(())
    } else {
        Err(CertError::QueryNotClaimed)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CertGenError {
    ProgramMismatch,
    /// The requested `(atom, sign)` does not hold in the model.
    NotInModel { atom: Atom, pos: bool },
    Unencodable(Atom),
    MissingProvenance(Atom),
    /// `¬atom` would need an `Unf` over a predicate with a non-head-covering rule.
    NonHeadCovering { atom: Atom, rule: usize },
    NoBlocker { atom: Atom, rule: usize },
    EdbLayout(Atom),
}

struct CertGen<'a, H: EdbHasher> {
    h: &'a H,
    program: &'a Program,
    model: &'a Model,
    tree: &'a EdbTree<H>,
    w: u64,
    claims: Vec<Claim<H::K, H::S, H::D>>,
    done: HashSet<(Atom, bool)>,
    failed: HashMap<Atom, CertGenError>,
}

impl<'a, H: EdbHasher> CertGen<'a, H> {
    fn pos(&mut self, a: &Atom) -> Result<(), CertGenError> {
        if self.done.contains(&(a.clone(), true)) {
            return Ok(());
        }
        let Some(level) = self.model.level(a) else {
            return Err(CertGenError::NotInModel { atom: a.clone(), pos: true });
        };
        let st = self.program.stratum(a.pred) as u64;
        let rank = st * self.w + 2 + level as u64;
        let just = if self.program.is_edb(a.pred) {
            let key = self.h.enc(a).ok_or_else(|| CertGenError::Unencodable(a.clone()))?;
            let j = self.tree.find_key(&key).map_err(|_| CertGenError::EdbLayout(a.clone()))?;
            Just::Memb { j: j as u64, salt: self.tree.leaves[j].salt.clone(), path: self.tree.path(j) }
        } else {
            let (rid, subst) = self.model.provenance(a).ok_or_else(|| CertGenError::MissingProvenance(a.clone()))?;
            let subst = subst.to_vec();
            let (_, pos, neg) = self
                .program
                .instance(rid as usize, &subst)
                .ok_or_else(|| CertGenError::MissingProvenance(a.clone()))?;
            for b in &pos {
                self.pos(b)?;
            }
            for b in &neg {
                self.neg(b)?;
            }
            Just::Rule { rule_id: rid, subst }
        };
        self.claims.push(Claim { atom: a.clone(), pos: true, rank, just });
        self.done.insert((a.clone(), true));
        Ok(())
    }

    fn neg(&mut self, a: &Atom) -> Result<(), CertGenError> {
        if self.done.contains(&(a.clone(), false)) {
            return Ok(());
        }
        if let Some(e) = self.failed.get(a) {
            return Err(e.clone());
        }
        let r = self.neg_inner(a);
        if let Err(e) = &r {
            self.failed.insert(a.clone(), e.clone());
        }
        r
    }

    fn neg_inner(&mut self, a: &Atom) -> Result<(), CertGenError> {
        if !self.program.atom_ok(a) || self.model.holds(a) {
            return Err(CertGenError::NotInModel { atom: a.clone(), pos: false });
        }
        let (rank, just) = if self.program.is_edb(a.pred) {
            let key = self.h.enc(a).ok_or_else(|| CertGenError::Unencodable(a.clone()))?;
            let ins = match self.tree.find_key(&key) {
                Err(ins) if ins >= 1 && ins < self.tree.leaves.len() => ins,
                _ => return Err(CertGenError::EdbLayout(a.clone())),
            };
            let i = ins - 1;
            (
                0,
                Just::Gap {
                    i: i as u64,
                    left: self.tree.leaves[i].clone(),
                    left_path: self.tree.path(i),
                    right: self.tree.leaves[i + 1].clone(),
                    right_path: self.tree.path(i + 1),
                },
            )
        } else {
            let st = self.program.stratum(a.pred);
            let mut u = vec![a.clone()];
            let mut inu: HashSet<Atom> = HashSet::new();
            inu.insert(a.clone());
            let mut k = 0;
            while k < u.len() {
                let x = u[k].clone();
                k += 1;
                for &rid in &self.program.rules_by_head[x.pred as usize] {
                    if !self.program.head_covering[rid] {
                        return Err(CertGenError::NonHeadCovering { atom: x.clone(), rule: rid });
                    }
                    let Some(subst) = self.program.match_head(rid, &x) else { continue };
                    let (_, pos, neg) = self
                        .program
                        .instance(rid, &subst)
                        .ok_or(CertGenError::NoBlocker { atom: x.clone(), rule: rid })?;
                    let mut blocked = false;
                    for c in &neg {
                        if self.model.holds(c) && self.pos(c).is_ok() {
                            blocked = true;
                            break;
                        }
                    }
                    if !blocked {
                        for b in &pos {
                            let same = !self.program.is_edb(b.pred) && self.program.stratum(b.pred) == st;
                            if !same && !self.model.holds(b) && self.neg(b).is_ok() {
                                blocked = true;
                                break;
                            }
                        }
                    }
                    if !blocked {
                        for b in &pos {
                            let same = !self.program.is_edb(b.pred) && self.program.stratum(b.pred) == st;
                            if same && !self.model.holds(b) {
                                if inu.insert(b.clone()) {
                                    u.push(b.clone());
                                }
                                blocked = true;
                                break;
                            }
                        }
                    }
                    if !blocked {
                        return Err(CertGenError::NoBlocker { atom: x.clone(), rule: rid });
                    }
                }
            }
            (st as u64 * self.w + 1, Just::Unf { u })
        };
        self.claims.push(Claim { atom: a.clone(), pos: false, rank, just });
        self.done.insert((a.clone(), false));
        Ok(())
    }
}

/// Generate a certificate for `(query, sign)` (only claims reachable from the query).
pub fn generate_cert<H: EdbHasher>(
    h: &H,
    program: &Program,
    model: &Model,
    tree: &EdbTree<H>,
    query: &Atom,
    sign: bool,
) -> Result<Vec<Claim<H::K, H::S, H::D>>, CertGenError> {
    if &model.program != program {
        return Err(CertGenError::ProgramMismatch);
    }
    let mut g = CertGen {
        h,
        program,
        model,
        tree,
        w: model.max_level() as u64 + 3,
        claims: Vec::new(),
        done: HashSet::new(),
        failed: HashMap::new(),
    };
    if sign {
        g.pos(query)?;
    } else {
        g.neg(query)?;
    }
    Ok(g.claims)
}

// ---------- certificate serialization ----------

pub const CERT_MAGIC: &[u8; 8] = b"MDW11CD1";

fn write_atom(a: &Atom, out: &mut Vec<u8>) {
    out.extend_from_slice(&a.pred.to_le_bytes());
    out.extend_from_slice(&(a.args.len() as u16).to_le_bytes());
    for x in &a.args {
        x.write(out);
    }
}
fn read_atom(inp: &mut &[u8]) -> Option<Atom> {
    let pred = read_u32(inp)?;
    let n = read_u16(inp)? as usize;
    let mut args = Vec::with_capacity(n.min(inp.len() / 8));
    for _ in 0..n {
        args.push(u64::read(inp)?);
    }
    Some(Atom { pred, args })
}
fn write_path<D: Wire>(p: &[D], out: &mut Vec<u8>) {
    out.extend_from_slice(&(p.len() as u16).to_le_bytes());
    for d in p {
        d.write(out);
    }
}
fn read_path<D: Wire>(inp: &mut &[u8]) -> Option<Vec<D>> {
    let n = read_u16(inp)? as usize;
    let mut v = Vec::with_capacity(n.min(inp.len()));
    for _ in 0..n {
        v.push(D::read(inp)?);
    }
    Some(v)
}

/// Canonical certificate bytes: `magic || u32 count || claim*`, claim =
/// `atom(u32 pred, u16 n, u64le args) || u8 pos || u64le rank || u8 tag || body` with
/// tag 0 `Memb(u64 j, salt, path)`, 1 `Rule(u32 id, u16 n, u64le*)`,
/// 2 `Gap(u64 i, key, salt, path, key, salt, path)`, 3 `Unf(u32 n, atom*)`;
/// path = `u16 len || digest*`; keys/salts/digests by their [`Wire`] encoding.
pub fn encode_cert<K: Wire, S: Wire, D: Wire>(claims: &[Claim<K, S, D>]) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(CERT_MAGIC);
    out.extend_from_slice(&(claims.len() as u32).to_le_bytes());
    for c in claims {
        write_atom(&c.atom, &mut out);
        out.push(c.pos as u8);
        c.rank.write(&mut out);
        match &c.just {
            Just::Memb { j, salt, path } => {
                out.push(0);
                j.write(&mut out);
                salt.write(&mut out);
                write_path(path, &mut out);
            }
            Just::Rule { rule_id, subst } => {
                out.push(1);
                out.extend_from_slice(&rule_id.to_le_bytes());
                out.extend_from_slice(&(subst.len() as u16).to_le_bytes());
                for x in subst {
                    x.write(&mut out);
                }
            }
            Just::Gap { i, left, left_path, right, right_path } => {
                out.push(2);
                i.write(&mut out);
                left.key.write(&mut out);
                left.salt.write(&mut out);
                write_path(left_path, &mut out);
                right.key.write(&mut out);
                right.salt.write(&mut out);
                write_path(right_path, &mut out);
            }
            Just::Unf { u } => {
                out.push(3);
                out.extend_from_slice(&(u.len() as u32).to_le_bytes());
                for a in u {
                    write_atom(a, &mut out);
                }
            }
        }
    }
    out
}

/// Inverse of [`encode_cert`]; rejects bad magic, unknown tags, truncation and trailing bytes.
pub fn decode_cert<K: Wire, S: Wire, D: Wire>(bytes: &[u8]) -> Option<Vec<Claim<K, S, D>>> {
    let mut inp = bytes;
    if take(&mut inp, 8)? != CERT_MAGIC {
        return None;
    }
    let n = read_u32(&mut inp)? as usize;
    let mut claims = Vec::with_capacity(n.min(inp.len() / 16));
    for _ in 0..n {
        let atom = read_atom(&mut inp)?;
        let pos = match read_u8(&mut inp)? {
            0 => false,
            1 => true,
            _ => return None,
        };
        let rank = u64::read(&mut inp)?;
        let just = match read_u8(&mut inp)? {
            0 => Just::Memb { j: u64::read(&mut inp)?, salt: S::read(&mut inp)?, path: read_path(&mut inp)? },
            1 => {
                let rule_id = read_u32(&mut inp)?;
                let k = read_u16(&mut inp)? as usize;
                let mut subst = Vec::with_capacity(k.min(inp.len() / 8));
                for _ in 0..k {
                    subst.push(u64::read(&mut inp)?);
                }
                Just::Rule { rule_id, subst }
            }
            2 => {
                let i = u64::read(&mut inp)?;
                let left = Leaf { key: K::read(&mut inp)?, salt: S::read(&mut inp)? };
                let left_path = read_path(&mut inp)?;
                let right = Leaf { key: K::read(&mut inp)?, salt: S::read(&mut inp)? };
                let right_path = read_path(&mut inp)?;
                Just::Gap { i, left, left_path, right, right_path }
            }
            3 => {
                let k = read_u32(&mut inp)? as usize;
                let mut u = Vec::with_capacity(k.min(inp.len() / 6));
                for _ in 0..k {
                    u.push(read_atom(&mut inp)?);
                }
                Just::Unf { u }
            }
            _ => return None,
        };
        claims.push(Claim { atom, pos, rank, just });
    }
    if inp.is_empty() {
        Some(claims)
    } else {
        None
    }
}

// ===================================================================================
// Conformance toy (mirrors the Lean toy exactly)
// ===================================================================================

pub const TOY_DEPTH: u32 = 4;
pub const TOY_NUM_PREDS: usize = 51;
pub const TOY_LEAF_KEYS: [u64; 16] = [0, 2, 3, 4, 5, 6, 8, 9, 10, 63, 63, 63, 63, 63, 63, 63];
pub const TOY_LEAF_SALTS: [u64; 16] = [0, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 0, 0, 0, 0, 0, 0, 0];
pub const TOY_EXPECTED_ROOT: u64 = 839_753_907;
/// Toy EDB atom codes (keys `a + 1`).
pub const TOY_EDB: [u32; 8] = [1, 2, 3, 4, 5, 7, 8, 9];

/// Toy stratum: `a<20 → 0; 20..=29 → 1; 30..=39 → 2; 40..=49 → 3; 50 → 1`.
pub fn toy_stratum(a: u32) -> u32 {
    match a {
        0..=19 => 0,
        20..=29 => 1,
        30..=39 => 2,
        40..=49 => 3,
        _ => 1,
    }
}

/// Toy ground rules as `(head, pos, neg)`, rule id = position:
/// `r0 20:-1, r1 21:-2,3, r2 22:-5, r3 30:-20,¬10, r4 31:-21,¬4, r5 32:-22,¬6,
///  r6 40:-7,¬30, r7 41:-8,¬31, r8 42:-9,¬32, r9 50:-50`.
pub const TOY_RULES: [(u32, &[u32], &[u32]); 10] = [
    (20, &[1], &[]),
    (21, &[2, 3], &[]),
    (22, &[5], &[]),
    (30, &[20], &[10]),
    (31, &[21], &[4]),
    (32, &[22], &[6]),
    (40, &[7], &[30]),
    (41, &[8], &[31]),
    (42, &[9], &[32]),
    (50, &[50], &[]),
];

fn ground_rule(head: u32, pos: &[u32], neg: &[u32]) -> Rule {
    Rule::new(
        Pattern::prop(head),
        pos.iter().map(|&p| Pattern::prop(p)).collect(),
        neg.iter().map(|&p| Pattern::prop(p)).collect(),
    )
}

pub fn toy_program() -> Program {
    let rules = TOY_RULES.iter().map(|(h, p, n)| ground_rule(*h, p, n)).collect();
    Program::new(
        vec![0; TOY_NUM_PREDS],
        (0..TOY_NUM_PREDS as u32).map(|a| a < 20).collect(),
        (0..TOY_NUM_PREDS as u32).map(toy_stratum).collect(),
        rules,
    )
    .expect("toy program is well-formed")
}

/// The stratifier falsifier `60 :- ¬60` over 0-ary preds `0..=60` (stratum check and
/// least-stratification both reject).
pub fn toy_self_negation_rules() -> (Vec<usize>, Vec<bool>, Vec<Rule>) {
    (vec![0; 61], (0..61u32).map(|a| a < 20).collect(), vec![ground_rule(60, &[], &[60])])
}

pub fn toy_tree() -> EdbTree<ToyHasher> {
    let leaves = TOY_LEAF_KEYS.iter().zip(TOY_LEAF_SALTS.iter()).map(|(&key, &salt)| Leaf { key, salt }).collect();
    EdbTree::from_leaves(&ToyHasher, TOY_DEPTH, leaves).expect("toy leaves are well-formed")
}

pub fn toy_edb() -> Vec<Atom> {
    TOY_EDB.iter().map(|&a| Atom::prop(a)).collect()
}

// ===================================================================================
// Authorization / revocation policy (3 strata over the EDB)
// ===================================================================================

/// Predicate ids of [`policy_program`].
pub mod policy_preds {
    pub const GRANT: u32 = 0; // grant(u, r)
    pub const MEMBER: u32 = 1; // member(u, g)
    pub const GROUP_GRANT: u32 = 2; // group_grant(g, r)
    pub const DELEGATES: u32 = 3; // delegates(a, b)
    pub const ADMIN: u32 = 4; // admin(u)
    pub const REVOKED: u32 = 5; // revoked(u)
    pub const REQUEST: u32 = 6; // request(u, r)
    pub const TRUSTED: u32 = 7; // stratum 1
    pub const CAN: u32 = 8; // stratum 1
    pub const ALLOWED: u32 = 9; // stratum 2
    pub const ALERT: u32 = 10; // stratum 3
    pub const NUM: usize = 11;
}

/// ```text
/// r0 can(U,R)     :- grant(U,R).                         head-covering
/// r1 can(U,R)     :- member(U,G), group_grant(G,R).      NOT head-covering (G)
/// r2 trusted(U)   :- admin(U).                           head-covering
/// r3 trusted(B)   :- trusted(A), delegates(A,B).         NOT head-covering (A), recursive
/// r4 can(U,R)     :- trusted(U), group_grant(0,R).       head-covering
/// r5 allowed(U,R) :- can(U,R), ¬revoked(U).              head-covering   (stratum 2)
/// r6 alert(U,R)   :- request(U,R), ¬allowed(U,R).        head-covering   (stratum 3)
/// ```
pub fn policy_program() -> Program {
    use policy_preds::*;
    let v = Term::Var;
    let p = |pred: u32, args: Vec<Term>| Pattern::new(pred, args);
    let (u, r, g, a, b) = (v(0), v(1), v(2), v(0), v(1));
    let rules = vec![
        Rule::new(p(CAN, vec![u, r]), vec![p(GRANT, vec![u, r])], vec![]),
        Rule::new(p(CAN, vec![u, r]), vec![p(MEMBER, vec![u, g]), p(GROUP_GRANT, vec![g, r])], vec![]),
        Rule::new(p(TRUSTED, vec![u]), vec![p(ADMIN, vec![u])], vec![]),
        Rule::new(p(TRUSTED, vec![b]), vec![p(TRUSTED, vec![a]), p(DELEGATES, vec![a, b])], vec![]),
        Rule::new(p(CAN, vec![u, r]), vec![p(TRUSTED, vec![u]), p(GROUP_GRANT, vec![Term::Const(0), r])], vec![]),
        Rule::new(p(ALLOWED, vec![u, r]), vec![p(CAN, vec![u, r])], vec![p(REVOKED, vec![u])]),
        Rule::new(p(ALERT, vec![u, r]), vec![p(REQUEST, vec![u, r])], vec![p(ALLOWED, vec![u, r])]),
    ];
    let arity = vec![2, 2, 2, 2, 1, 1, 2, 1, 2, 2, 2];
    let is_edb = (0..NUM as u32).map(|x| x <= REQUEST).collect();
    let stratum = vec![0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 3];
    Program::new(arity, is_edb, stratum, rules).expect("policy program is well-formed")
}

// ===================================================================================
// ComposedByteTurnCert
// ===================================================================================

pub const TURN_BYTES_DOMAIN: &[u8] = b"minidregg.w11.turn.bytes\0";
pub const TURN_TRANSCRIPT_DOMAIN: &[u8] = b"minidregg.w11.turn.transcript\0";
pub const DFA_DOMAIN: &[u8] = b"minidregg.w11.dfa\0";
pub const BPE_DOMAIN: &[u8] = b"minidregg.w11.bpe.table\0";

/// Salted byte commitment shared by all turn sub-certificates.
pub fn commit_turn_bytes(salt: &[u8; 32], bytes: &[u8]) -> [u8; 32] {
    sha3(&[TURN_BYTES_DOMAIN, salt, &(bytes.len() as u64).to_le_bytes(), bytes])
}

/// Complete byte DFA (`delta[state * 256 + byte]`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ByteDfa {
    pub num_states: u32,
    pub start: u32,
    pub accepting: Vec<bool>,
    pub delta: Vec<u32>,
}

impl ByteDfa {
    /// Printable ASCII (`0x20..=0x7E`, `\n`) not containing the substring `"sk-"`.
    /// States: 0 base, 1 after `s`, 2 after `sk`, 3 dead.
    pub fn no_secret_ascii() -> Self {
        let mut delta = vec![3u32; 4 * 256];
        for st in 0..3u32 {
            for b in 0..256u32 {
                let ok = (0x20..=0x7E).contains(&b) || b == b'\n' as u32;
                let next = if !ok {
                    3
                } else if b == b's' as u32 {
                    1
                } else if st == 1 && b == b'k' as u32 {
                    2
                } else if st == 2 && b == b'-' as u32 {
                    3
                } else {
                    0
                };
                delta[(st * 256 + b) as usize] = next;
            }
        }
        ByteDfa { num_states: 4, start: 0, accepting: vec![true, true, true, false], delta }
    }
    pub fn digest(&self) -> [u8; 32] {
        let mut buf = Vec::with_capacity(8 + self.accepting.len() + 4 * self.delta.len());
        buf.extend_from_slice(&self.num_states.to_le_bytes());
        buf.extend_from_slice(&self.start.to_le_bytes());
        buf.extend(self.accepting.iter().map(|&b| b as u8));
        for d in &self.delta {
            buf.extend_from_slice(&d.to_le_bytes());
        }
        sha3(&[DFA_DOMAIN, &buf])
    }
    fn well_formed(&self) -> bool {
        let n = self.num_states as usize;
        self.start < self.num_states && self.accepting.len() == n
            && n.checked_mul(256) == Some(self.delta.len())
            && self.delta.iter().all(|&s| s < self.num_states)
    }
    /// State trace of length `bytes.len() + 1`.
    pub fn run(&self, bytes: &[u8]) -> Vec<u32> {
        let mut t = Vec::with_capacity(bytes.len() + 1);
        let mut s = self.start;
        t.push(s);
        for &b in bytes {
            s = self.delta[(s as usize) * 256 + b as usize];
            t.push(s);
        }
        t
    }
}

/// Merge-rank BPE table: merge `i` creates token `256 + i` from `(left, right)`.
#[derive(Clone, Debug)]
pub struct BpeTable {
    merges: Vec<(u32, u32)>,
    rank: HashMap<(u32, u32), u32>,
    expand: Vec<Vec<u8>>,
}

impl BpeTable {
    /// Build from merges given as byte strings; each side must already be a token.
    pub fn from_string_merges(pairs: &[(&[u8], &[u8])]) -> Option<Self> {
        let mut by_str: HashMap<Vec<u8>, u32> = (0..256u32).map(|b| (vec![b as u8], b)).collect();
        let mut expand: Vec<Vec<u8>> = (0..256u32).map(|b| vec![b as u8]).collect();
        let mut merges = Vec::new();
        let mut rank = HashMap::new();
        for (i, (l, r)) in pairs.iter().enumerate() {
            let li = *by_str.get(*l)?;
            let ri = *by_str.get(*r)?;
            let mut s = l.to_vec();
            s.extend_from_slice(r);
            if by_str.contains_key(&s) || rank.contains_key(&(li, ri)) {
                return None;
            }
            let id = 256 + i as u32;
            by_str.insert(s.clone(), id);
            expand.push(s);
            merges.push((li, ri));
            rank.insert((li, ri), i as u32);
        }
        Some(BpeTable { merges, rank, expand })
    }
    /// A small demo table.
    pub fn demo() -> Self {
        let m: [(&[u8], &[u8]); 14] = [
            (b"t", b"h"),
            (b"th", b"e"),
            (b"i", b"n"),
            (b"t", b"o"),
            (b"o", b"l"),
            (b"to", b"ol"),
            (b"s", b"t"),
            (b"l", b"i"),
            (b"li", b"st"),
            (b"e", b" "),
            (b" ", b"t"),
            (b"u", b"s"),
            (b"e", b"r"),
            (b"us", b"er"),
        ];
        BpeTable::from_string_merges(&m).expect("demo BPE table is well-formed")
    }
    pub fn digest(&self) -> [u8; 32] {
        let mut buf = Vec::with_capacity(4 + 8 * self.merges.len());
        buf.extend_from_slice(&(self.merges.len() as u32).to_le_bytes());
        for (l, r) in &self.merges {
            buf.extend_from_slice(&l.to_le_bytes());
            buf.extend_from_slice(&r.to_le_bytes());
        }
        sha3(&[BPE_DOMAIN, &buf])
    }
    /// Canonical encode: repeatedly apply the lowest-rank adjacent merge to all its
    /// non-overlapping occurrences, left to right.
    pub fn encode(&self, bytes: &[u8]) -> Vec<u32> {
        let mut toks: Vec<u32> = bytes.iter().map(|&b| b as u32).collect();
        loop {
            let best = toks.windows(2).filter_map(|w| self.rank.get(&(w[0], w[1])).copied()).min();
            let Some(rk) = best else { return toks };
            let pair = self.merges[rk as usize];
            let id = 256 + rk;
            let mut out = Vec::with_capacity(toks.len());
            let mut i = 0;
            while i < toks.len() {
                if i + 1 < toks.len() && (toks[i], toks[i + 1]) == pair {
                    out.push(id);
                    i += 2;
                } else {
                    out.push(toks[i]);
                    i += 1;
                }
            }
            toks = out;
        }
    }
    pub fn decode(&self, toks: &[u32]) -> Option<Vec<u8>> {
        let mut out = Vec::new();
        for &t in toks {
            out.extend_from_slice(self.expand.get(t as usize)?);
        }
        Some(out)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DfaAcceptCert {
    pub byte_root: [u8; 32],
    pub dfa_digest: [u8; 32],
    pub trace: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BpeProjectionCert {
    pub byte_root: [u8; 32],
    pub table_digest: [u8; 32],
    pub tokens: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DatalogAuthCert {
    pub byte_root: [u8; 32],
    pub edb: EdbCommitment<[u8; 32]>,
    pub user: u64,
    pub tool: u64,
    pub claims: Vec<Sha3Claim>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComposedByteTurnCert {
    pub byte_root: [u8; 32],
    pub salt: [u8; 32],
    pub bytes: Vec<u8>,
    pub user: u64,
    pub tool: u64,
    pub dfa: DfaAcceptCert,
    pub bpe: BpeProjectionCert,
    pub auth: DatalogAuthCert,
    pub transcript: [u8; 32],
}

/// Public verifier context: the policy, the committed EDB, the DFA and BPE tables.
pub struct TurnContext<'a> {
    pub program: &'a Program,
    pub edb: EdbCommitment<[u8; 32]>,
    pub dfa: &'a ByteDfa,
    pub bpe: &'a BpeTable,
    /// Deterministic application grammar for the opened turn.
    pub read_request: fn(&[u8]) -> Option<(u64, u64)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TurnError {
    ByteCommitment,
    ByteRootMismatch { sub: &'static str },
    DfaTable,
    DfaDigest,
    DfaTrace,
    DfaRejects,
    BpeDigest,
    BpeDecode,
    BpeNotCanonical,
    AuthBinding,
    EdbMismatch,
    Datalog(CertError),
    Transcript,
    ProverDatalog(CertGenError),
}

/// Parse the demo header `user <u64> calls tool <u64>: ` followed by an opaque payload.
pub fn text_request_ids(bytes: &[u8]) -> Option<(u64, u64)> {
    fn decimal(bytes: &[u8]) -> Option<(u64, &[u8])> {
        let n = bytes.iter().take_while(|b| b.is_ascii_digit()).count();
        let (digits, rest) = bytes.split_at(n);
        if digits.is_empty() || (n > 1 && digits[0] == b'0') {
            return None;
        }
        let value = std::str::from_utf8(digits).ok()?.parse().ok()?;
        Some((value, rest))
    }
    let (user, rest) = decimal(bytes.strip_prefix(b"user ")?)?;
    let (tool, rest) = decimal(rest.strip_prefix(b" calls tool ")?)?;
    rest.strip_prefix(b": ")?;
    Some((user, tool))
}

fn u32s(v: &[u32]) -> Vec<u8> {
    v.iter().flat_map(|x| x.to_le_bytes()).collect()
}

/// Transcript digest binding the byte root, EDB commitment, user, tool, table digests and the
/// three sub-certificate payloads.
pub fn turn_transcript(cert: &ComposedByteTurnCert) -> [u8; 32] {
    sha3(&[
        TURN_TRANSCRIPT_DOMAIN,
        &cert.byte_root,
        &cert.auth.edb.root,
        &cert.auth.edb.depth.to_le_bytes(),
        &cert.user.to_le_bytes(),
        &cert.tool.to_le_bytes(),
        &cert.dfa.dfa_digest,
        &cert.bpe.table_digest,
        &sha3(&[&u32s(&cert.dfa.trace)]),
        &sha3(&[&u32s(&cert.bpe.tokens)]),
        &sha3(&[&encode_cert(&cert.auth.claims)]),
    ])
}

/// Honest prover for a turn: `bytes` must be DFA-accepted and `allowed(user, tool)` certifiable.
pub fn prove_composed_turn(
    ctx: &TurnContext,
    tree: &EdbTree<Sha3Hasher>,
    model: &Model,
    bytes: &[u8],
    salt: [u8; 32],
    user: u64,
    tool: u64,
) -> Result<ComposedByteTurnCert, TurnError> {
    if tree.commitment() != ctx.edb {
        return Err(TurnError::EdbMismatch);
    }
    if !ctx.dfa.well_formed() {
        return Err(TurnError::DfaTable);
    }
    let byte_root = commit_turn_bytes(&salt, bytes);
    let trace = ctx.dfa.run(bytes);
    if !ctx.dfa.accepting[*trace.last().expect("nonempty trace") as usize] {
        return Err(TurnError::DfaRejects);
    }
    if (ctx.read_request)(bytes) != Some((user, tool)) {
        return Err(TurnError::AuthBinding);
    }
    let query = Atom::new(policy_preds::ALLOWED, vec![user, tool]);
    let claims =
        generate_cert(&Sha3Hasher, ctx.program, model, tree, &query, true).map_err(TurnError::ProverDatalog)?;
    let mut cert = ComposedByteTurnCert {
        byte_root,
        salt,
        bytes: bytes.to_vec(),
        user,
        tool,
        dfa: DfaAcceptCert { byte_root, dfa_digest: ctx.dfa.digest(), trace },
        bpe: BpeProjectionCert { byte_root, table_digest: ctx.bpe.digest(), tokens: ctx.bpe.encode(bytes) },
        auth: DatalogAuthCert { byte_root, edb: tree.commitment(), user, tool, claims },
        transcript: [0; 32],
    };
    cert.transcript = turn_transcript(&cert);
    Ok(cert)
}

/// Verify all three sub-certificates against the SAME byte root, with the Datalog query
/// `allowed(user, tool)` bound to the transcript's user/tool.
pub fn verify_composed_turn(ctx: &TurnContext, c: &ComposedByteTurnCert) -> Result<(), TurnError> {
    if commit_turn_bytes(&c.salt, &c.bytes) != c.byte_root {
        return Err(TurnError::ByteCommitment);
    }
    if c.dfa.byte_root != c.byte_root {
        return Err(TurnError::ByteRootMismatch { sub: "dfa" });
    }
    if c.bpe.byte_root != c.byte_root {
        return Err(TurnError::ByteRootMismatch { sub: "bpe" });
    }
    if c.auth.byte_root != c.byte_root {
        return Err(TurnError::ByteRootMismatch { sub: "auth" });
    }
    // (a) DFA run over the committed bytes.
    if !ctx.dfa.well_formed() {
        return Err(TurnError::DfaTable);
    }
    if c.dfa.dfa_digest != ctx.dfa.digest() {
        return Err(TurnError::DfaDigest);
    }
    let t = &c.dfa.trace;
    if t.len() != c.bytes.len() + 1 || t[0] != ctx.dfa.start || t.iter().any(|&s| s >= ctx.dfa.num_states) {
        return Err(TurnError::DfaTrace);
    }
    for (i, &b) in c.bytes.iter().enumerate() {
        if ctx.dfa.delta[t[i] as usize * 256 + b as usize] != t[i + 1] {
            return Err(TurnError::DfaTrace);
        }
    }
    if !ctx.dfa.accepting[t[c.bytes.len()] as usize] {
        return Err(TurnError::DfaRejects);
    }
    // (c) BPE projection.
    if c.bpe.table_digest != ctx.bpe.digest() {
        return Err(TurnError::BpeDigest);
    }
    if ctx.bpe.decode(&c.bpe.tokens).as_deref() != Some(&c.bytes[..]) {
        return Err(TurnError::BpeDecode);
    }
    if ctx.bpe.encode(&c.bytes) != c.bpe.tokens {
        return Err(TurnError::BpeNotCanonical);
    }
    // (b) Datalog authorization bound to the transcript's user/tool.
    if c.auth.user != c.user || c.auth.tool != c.tool || (ctx.read_request)(&c.bytes) != Some((c.user, c.tool)) {
        return Err(TurnError::AuthBinding);
    }
    if c.auth.edb != ctx.edb {
        return Err(TurnError::EdbMismatch);
    }
    let query = Atom::new(policy_preds::ALLOWED, vec![c.user, c.tool]);
    verify_cert(&Sha3Hasher, ctx.program, &ctx.edb, &c.auth.claims, &query, true).map_err(TurnError::Datalog)?;
    if turn_transcript(c) != c.transcript {
        return Err(TurnError::Transcript);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_signed_queries_in_small_stratified_programs() {
        // E is extensional. A and B form a possible positive cycle; C can depend on ¬B.
        let choices = [
            ground_rule(1, &[0], &[]),
            ground_rule(1, &[2], &[]),
            ground_rule(2, &[1], &[]),
            ground_rule(2, &[], &[]),
            ground_rule(3, &[0], &[2]),
        ];
        for mask in 0..(1 << choices.len()) {
            let rules = choices.iter().enumerate().filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, rule)| rule.clone()).collect();
            let p = Program::new(vec![0; 4], vec![true, false, false, false], vec![0, 0, 0, 1], rules).unwrap();
            for e in [false, true] {
                let facts = if e { vec![Atom::prop(0)] } else { vec![] };
                let model = solve(&p, &facts).unwrap();
                let tree = EdbTree::commit_facts(&ToyHasher, &p, &facts, |_, i| i as u64).unwrap();
                let a = mask & 1 != 0 && e || mask & 2 != 0 && mask & 8 != 0;
                let b = mask & 8 != 0 || mask & 4 != 0 && a;
                for (pred, truth) in [e, a, b, mask & 16 != 0 && e && !b].into_iter().enumerate() {
                    let q = Atom::prop(pred as u32);
                    assert_eq!(model.holds(&q), truth);
                    let cs = generate_cert(&ToyHasher, &p, &model, &tree, &q, truth).unwrap();
                    verify_cert(&ToyHasher, &p, &tree.commitment(), &cs, &q, truth).unwrap();
                    assert!(verify_cert(&ToyHasher, &p, &tree.commitment(), &cs, &q, !truth).is_err());
                    assert!(generate_cert(&ToyHasher, &p, &model, &tree, &q, !truth).is_err());
                }
            }
        }
    }
}
