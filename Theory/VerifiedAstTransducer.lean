/-
# `Theory/VerifiedAstTransducer.lean` — Verified Unambiguous LL(1) AST Extraction & Deterministic Secret-Redaction Byte Transducer

Closes two foundational gaps in boolean formal-language gating (`w ∈ L(G)` in `CfgCompact.lean`
and pure substring rejection `Absent` in `ContentCertificate.lean`):

1. **Unambiguous Attributed Pushdown Replay (`AttrCfg`, `AttrReplay`, `ll1Deterministic`, `attrReplay_unique_of_ll1`):**
   - Generalizes pushdown rule replay to an S-attributed stack transducer (`AttrStackReplay` /
     `AttrReplay g rs w ast`) with a linear-time structurally recursive checker (`execAttrReplay_iff`),
     soundness into Mathlib's `ContextFreeGrammar.language` (`attrReplay_mem_language`), and an
     executable `AttrCfg → Bool` LL(1) disjoint-predict-set determinacy checker (`ll1Deterministic`).
   - Kernel-proves **`attrReplay_unique_of_ll1`**: whenever `ll1Deterministic g = true`, any two
     accepting replays on the same input `w` produce the **exact same AST and rule sequence**
     (`ast₁ = ast₂ ∧ rs₁ = rs₂`).
   - Instantiates a real byte-level (`UInt8`) **RFC 8259 JSON Tool-Call / `Mini` Command Grammar**
     (`miniJsonCfg`: whitespace, string escape decoding `\"`, `\\`, `\/`, `\n`, `\r`, `\t`,
     canonical integers `0 | [1-9][0-9]*`, single tool frames, CoT+tool frames, and batch arrays)
     proved `ll1Deterministic miniJsonCfg = true`, alongside a constructive **duplicate-key JSON
     splice attack** (`ambigMiniJsonCfg`: `ll1Deterministic = false`, yielding `ast₁ ≠ ast₂` —
     `"read_status"` vs `"wipe_prod"` — on the exact same byte string `w ∈ L(G)`).

2. **Verified Multi-Pattern Secret-Redaction Byte Transducer (`RedactRule`, `redactBytes`):**
   - Formalizes a deterministic left-to-right longest-match byte-stream sanitizer supporting
     prefix + greedy token-run classes (`sk-...`, `Bearer ...`, `-----BEGIN ...`, `ghp_...`, `{{`).
   - Proves relational transducer determinism (`redactBytes_deterministic`), universal multi-rule
     absence (`redactBytes_scrubs_all` under decidable `SafeReplacement`, plus boundary-recreation
     falsifier tooth `redactBytes_unsafe_repl_falsifier`), clean-input non-mangling
     (`redactBytes_preserves_clean`), and strict idempotence (`redactBytes_idempotent`).

Import boundary: `Theory/` tier (`Mathlib.*` only).
-/
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

namespace Minidregg.Theory.VerifiedAstTransducer

open ContextFreeGrammar

set_option autoImplicit false

/-! ## §1. Attributed Context-Free Grammars & Pushdown AST Transducer -/

/-- A production rule `lhs → rhs` annotated with a first-order semantic operator `op : SemOp`. -/
structure AttrRule (T NT SemOp : Type) where
  lhs : NT
  rhs : List (Symbol T NT)
  op  : SemOp
  deriving DecidableEq, Repr

/-- Erase the semantic operator of an `AttrRule` to Mathlib's `ContextFreeRule`. -/
def AttrRule.toCfgRule {T NT SemOp : Type} (r : AttrRule T NT SemOp) : ContextFreeRule T NT :=
  ⟨r.lhs, r.rhs⟩

/-- **Attributed Context-Free Grammar (`AttrCfg`)**:
pairs a finite production list over `(T, NT)` with terminal leaf interpretation `termVal : T → Val`
and bottom-up operator evaluation `evalOp : SemOp → List Val → Val`. -/
structure AttrCfg (T NT SemOp Val : Type) where
  initial : NT
  rules   : List (AttrRule T NT SemOp)
  termVal : T → Val
  evalOp  : SemOp → List Val → Val

/-- Underlying Mathlib `ContextFreeGrammar T` of an `AttrCfg`. -/
abbrev AttrCfg.toCfg {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT]
    (g : AttrCfg T NT SemOp Val) : ContextFreeGrammar T where
  NT := NT
  initial := g.initial
  rules := (g.rules.map AttrRule.toCfgRule).toFinset

/-- Control-stack items for single-pass pushdown AST synthesis:
either a grammar symbol to expand/match, or a deferred `k`-ary reduction marker. -/
inductive WorkItem (T NT SemOp : Type) where
  | sym    : Symbol T NT → WorkItem T NT SemOp
  | reduce : SemOp → Nat → WorkItem T NT SemOp
  deriving DecidableEq, Repr

/-- Extract remaining grammar symbols on the control stack (erasing `.reduce` markers). -/
def symsOfStack {T NT SemOp : Type} : List (WorkItem T NT SemOp) → List (Symbol T NT)
  | [] => []
  | .sym s :: rest => s :: symsOfStack rest
  | .reduce _ _ :: rest => symsOfStack rest

@[simp] theorem symsOfStack_nil {T NT SemOp : Type} :
    symsOfStack ([] : List (WorkItem T NT SemOp)) = [] := rfl

@[simp] theorem symsOfStack_sym {T NT SemOp : Type} (s : Symbol T NT)
    (rest : List (WorkItem T NT SemOp)) :
    symsOfStack (.sym s :: rest) = s :: symsOfStack rest := rfl

@[simp] theorem symsOfStack_reduce {T NT SemOp : Type} (op : SemOp) (k : Nat)
    (rest : List (WorkItem T NT SemOp)) :
    symsOfStack (.reduce op k :: rest) = symsOfStack rest := rfl

@[simp] theorem symsOfStack_append {T NT SemOp : Type}
    (xs ys : List (WorkItem T NT SemOp)) :
    symsOfStack (xs ++ ys) = symsOfStack xs ++ symsOfStack ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases x <;> simp [ih]

@[simp] theorem symsOfStack_map_sym {T NT SemOp : Type} (rhs : List (Symbol T NT)) :
    symsOfStack (rhs.map (WorkItem.sym (SemOp := SemOp))) = rhs := by
  induction rhs with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- **Attributed Pushdown Stack Replay (`AttrStackReplay`)**:
from control stack `cstk` and synthesized value stack `vstk`, leftmost rule sequence `rs`
consumes `input` and reduces `vstk` to `[ast]`. -/
inductive AttrStackReplay {T NT SemOp Val : Type} (g : AttrCfg T NT SemOp Val) :
    List (AttrRule T NT SemOp) → List T → List (WorkItem T NT SemOp) → List Val → Val → Prop
  | done (ast : Val) :
      AttrStackReplay g [] [] [] [ast] ast
  | term {rs : List (AttrRule T NT SemOp)} {w : List T}
      {cstk : List (WorkItem T NT SemOp)} {vstk : List Val} {ast : Val} (t : T) :
      AttrStackReplay g rs w cstk (g.termVal t :: vstk) ast →
      AttrStackReplay g rs (t :: w) (.sym (.terminal t) :: cstk) vstk ast
  | rule {r : AttrRule T NT SemOp} {rs : List (AttrRule T NT SemOp)} {w : List T}
      {cstk : List (WorkItem T NT SemOp)} {vstk : List Val} {ast : Val}
      (hr : r ∈ g.rules) :
      AttrStackReplay g rs w
        (r.rhs.map .sym ++ .reduce r.op r.rhs.length :: cstk) vstk ast →
      AttrStackReplay g (r :: rs) w (.sym (.nonterminal r.lhs) :: cstk) vstk ast
  | reduce {rs : List (AttrRule T NT SemOp)} {w : List T}
      {cstk : List (WorkItem T NT SemOp)} {vsRev vstk : List Val} {ast : Val}
      (op : SemOp) (k : Nat) (hlen : vsRev.length = k) :
      AttrStackReplay g rs w cstk (g.evalOp op vsRev.reverse :: vstk) ast →
      AttrStackReplay g rs w (.reduce op k :: cstk) (vsRev ++ vstk) ast

/-- **Top-level Attributed Replay (`AttrReplay g rs w ast`)**:
starting from `[.sym (.nonterminal g.initial)]` and empty value stack `[]`, certificate `rs`
accepts word `w` and synthesizes AST `ast`. -/
def AttrReplay {T NT SemOp Val : Type} (g : AttrCfg T NT SemOp Val)
    (rs : List (AttrRule T NT SemOp)) (w : List T) (ast : Val) : Prop :=
  AttrStackReplay g rs w [.sym (.nonterminal g.initial)] [] ast

/-- **Soundness into Mathlib `ContextFreeGrammar` (`attrStackReplay_derives`)**:
every accepting attributed stack replay witnesses a genuine Mathlib CFG derivation. -/
theorem attrStackReplay_derives {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT]
    {g : AttrCfg T NT SemOp Val}
    {rs : List (AttrRule T NT SemOp)} {w : List T}
    {cstk : List (WorkItem T NT SemOp)} {vstk : List Val} {ast : Val}
    (h : AttrStackReplay g rs w cstk vstk ast) :
    g.toCfg.Derives (symsOfStack cstk) (w.map Symbol.terminal) := by
  induction h with
  | done _ => exact Relation.ReflTransGen.refl
  | term t _ ih =>
      simpa [symsOfStack] using ih.append_left [Symbol.terminal t]
  | @rule r _ w' cstk' _ _ hr _ ih =>
      have hsym : symsOfStack (r.rhs.map .sym ++ WorkItem.reduce r.op r.rhs.length :: cstk') =
          r.rhs ++ symsOfStack cstk' := by simp
      have ih' : g.toCfg.Derives (r.rhs ++ symsOfStack cstk') (w'.map Symbol.terminal) :=
        hsym ▸ ih
      refine Produces.trans_derives ⟨r.toCfgRule, ?_, ?_⟩ ih'
      · exact List.mem_toFinset.mpr (List.mem_map_of_mem hr)
      · exact ContextFreeRule.Rewrites.head (symsOfStack cstk')
  | reduce _ _ _ _ ih =>
      exact ih

/-- **`attrReplay_mem_language`** — tie-back to boolean CFG membership (`CfgCompact.compact_sound`):
an accepted `AttrReplay` proves `w ∈ g.toCfg.language`. -/
theorem attrReplay_mem_language {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT]
    {g : AttrCfg T NT SemOp Val} {rs : List (AttrRule T NT SemOp)} {w : List T} {ast : Val}
    (h : AttrReplay g rs w ast) : w ∈ g.toCfg.language := by
  rw [mem_language_iff]
  exact attrStackReplay_derives h

/-! ### Structurally Recursive Linear-Time Replay Engine & Equivalence -/

/-- Structural tail pass when `rs = []`: shrinks `cstk` on every step without `WellFounded.fix`. -/
def execNoRules {T NT SemOp Val : Type} [DecidableEq T]
    (g : AttrCfg T NT SemOp Val) :
    List T → List (WorkItem T NT SemOp) → List Val → Option Val
  | [], [], [ast] => some ast
  | _, [], _ => none
  | t' :: w, .sym (.terminal t) :: cstk, vstk =>
      if t' = t then execNoRules g w cstk (g.termVal t :: vstk) else none
  | [], .sym (.terminal _) :: _, _ => none
  | _, .sym (.nonterminal _) :: _, _ => none
  | w, .reduce op k :: cstk, vstk =>
      if k ≤ vstk.length then
        execNoRules g w cstk (g.evalOp op (vstk.take k).reverse :: vstk.drop k)
      else none

/-- Inner structural pass over `cstk` until the next `.nonterminal` consumes rule `r` and calls `onRule`. -/
def execStepUntilRule {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT] [DecidableEq SemOp]
    (g : AttrCfg T NT SemOp Val) (r : AttrRule T NT SemOp)
    (onRule : List T → List (WorkItem T NT SemOp) → List Val → Option Val) :
    List T → List (WorkItem T NT SemOp) → List Val → Option Val
  | _, [], _ => none
  | t' :: w', .sym (.terminal t) :: cstk', vstk' =>
      if t' = t then execStepUntilRule g r onRule w' cstk' (g.termVal t :: vstk') else none
  | [], .sym (.terminal _) :: _, _ => none
  | w', .sym (.nonterminal A) :: cstk', vstk' =>
      if r ∈ g.rules ∧ r.lhs = A then
        onRule w' (r.rhs.map .sym ++ .reduce r.op r.rhs.length :: cstk') vstk'
      else none
  | w', .reduce op k :: cstk', vstk' =>
      if k ≤ vstk'.length then
        execStepUntilRule g r onRule w' cstk' (g.evalOp op (vstk'.take k).reverse :: vstk'.drop k)
      else none

/-- Structural recursion over `rs`: zero `WellFounded.fix`, instantaneous kernel WHNF reduction. -/
def execAttrStackReplay {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT] [DecidableEq SemOp]
    (g : AttrCfg T NT SemOp Val) :
    List (AttrRule T NT SemOp) → List T → List (WorkItem T NT SemOp) → List Val → Option Val
  | [], w, cstk, vstk => execNoRules g w cstk vstk
  | r :: rs, w, cstk, vstk => execStepUntilRule g r (execAttrStackReplay g rs) w cstk vstk

/-- Top-level executable attributed replay: returns `some ast` iff `rs` validly parses `w` into `ast`. -/
def execAttrReplay {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT] [DecidableEq SemOp]
    (g : AttrCfg T NT SemOp Val) (rs : List (AttrRule T NT SemOp)) (w : List T) : Option Val :=
  execAttrStackReplay g rs w [.sym (.nonterminal g.initial)] []

private theorem execNoRules_sound {T NT SemOp Val : Type} [DecidableEq T]
    (g : AttrCfg T NT SemOp Val) :
    ∀ (cstk : List (WorkItem T NT SemOp)) (w : List T) (vstk : List Val) (ast : Val),
      execNoRules g w cstk vstk = some ast →
        AttrStackReplay g [] w cstk vstk ast := by
  intro cstk
  induction cstk with
  | nil =>
      intro w vstk ast h
      cases w with
      | nil =>
          cases vstk with
          | nil => simp [execNoRules] at h
          | cons v vs =>
              cases vs with
              | nil =>
                  simp only [execNoRules, Option.some.injEq] at h
                  subst h
                  exact .done v
              | cons _ _ => simp [execNoRules] at h
      | cons _ _ => simp [execNoRules] at h
  | cons item cstk ih =>
      intro w vstk ast h
      cases item with
      | sym s =>
          cases s with
          | terminal t =>
              cases w with
              | nil => simp [execNoRules] at h
              | cons t' w' =>
                  by_cases heq : t' = t
                  · subst heq
                    simp only [execNoRules, ↓reduceIte] at h
                    exact .term t' (ih w' (g.termVal t' :: vstk) ast h)
                  · simp [execNoRules, heq] at h
          | nonterminal _ =>
              simp [execNoRules] at h
      | reduce op k =>
          by_cases hle : k ≤ vstk.length
          · simp only [execNoRules, hle, ↓reduceIte] at h
            have hsplit : vstk.take k ++ vstk.drop k = vstk := List.take_append_drop k vstk
            rw [← hsplit]
            exact .reduce op k (List.length_take_of_le hle) (ih w _ ast h)
          · simp [execNoRules, hle] at h

private theorem execStepUntilRule_sound {T NT SemOp Val : Type}
    [DecidableEq T] [DecidableEq NT] [DecidableEq SemOp]
    (g : AttrCfg T NT SemOp Val) (r : AttrRule T NT SemOp)
    (rs : List (AttrRule T NT SemOp))
    (onRule : List T → List (WorkItem T NT SemOp) → List Val → Option Val)
    (hon : ∀ w' cstk' vstk' ast,
      onRule w' cstk' vstk' = some ast → AttrStackReplay g rs w' cstk' vstk' ast) :
    ∀ (cstk : List (WorkItem T NT SemOp)) (w : List T) (vstk : List Val) (ast : Val),
      execStepUntilRule g r onRule w cstk vstk = some ast →
        AttrStackReplay g (r :: rs) w cstk vstk ast := by
  intro cstk
  induction cstk with
  | nil =>
      intro w vstk ast h
      simp [execStepUntilRule] at h
  | cons item cstk ih =>
      intro w vstk ast h
      cases item with
      | sym s =>
          cases s with
          | terminal t =>
              cases w with
              | nil => simp [execStepUntilRule] at h
              | cons t' w' =>
                  by_cases heq : t' = t
                  · subst heq
                    simp only [execStepUntilRule, ↓reduceIte] at h
                    exact .term t' (ih w' (g.termVal t' :: vstk) ast h)
                  · simp [execStepUntilRule, heq] at h
          | nonterminal A =>
              by_cases hcond : r ∈ g.rules ∧ r.lhs = A
              · simp only [execStepUntilRule, hcond, and_self, ↓reduceIte] at h
                rcases hcond with ⟨hr, hlhs⟩
                subst hlhs
                exact .rule hr (hon w _ vstk ast h)
              · simp [execStepUntilRule, hcond] at h
      | reduce op k =>
          by_cases hle : k ≤ vstk.length
          · simp only [execStepUntilRule, hle, ↓reduceIte] at h
            have hsplit : vstk.take k ++ vstk.drop k = vstk := List.take_append_drop k vstk
            rw [← hsplit]
            exact .reduce op k (List.length_take_of_le hle) (ih w _ ast h)
          · simp [execStepUntilRule, hle] at h

theorem execAttrStackReplay_sound {T NT SemOp Val : Type}
    [DecidableEq T] [DecidableEq NT] [DecidableEq SemOp]
    (g : AttrCfg T NT SemOp Val) :
    ∀ (rs : List (AttrRule T NT SemOp)) (w : List T)
      (cstk : List (WorkItem T NT SemOp)) (vstk : List Val) (ast : Val),
      execAttrStackReplay g rs w cstk vstk = some ast →
        AttrStackReplay g rs w cstk vstk ast := by
  intro rs
  induction rs with
  | nil =>
      intro w cstk vstk ast h
      exact execNoRules_sound g cstk w vstk ast h
  | cons r rs ih =>
      intro w cstk vstk ast h
      exact execStepUntilRule_sound g r rs (execAttrStackReplay g rs) ih cstk w vstk ast h

theorem execAttrStackReplay_complete {T NT SemOp Val : Type}
    [DecidableEq T] [DecidableEq NT] [DecidableEq SemOp]
    {g : AttrCfg T NT SemOp Val}
    {rs : List (AttrRule T NT SemOp)} {w : List T}
    {cstk : List (WorkItem T NT SemOp)} {vstk : List Val} {ast : Val}
    (h : AttrStackReplay g rs w cstk vstk ast) :
    execAttrStackReplay g rs w cstk vstk = some ast := by
  induction h with
  | done _ => rfl
  | @term rs w cstk vstk ast t _ ih =>
      cases rs with
      | nil => simpa [execAttrStackReplay, execNoRules] using ih
      | cons r rs' => simpa [execAttrStackReplay, execStepUntilRule] using ih
  | rule hr _ ih =>
      simpa [execAttrStackReplay, execStepUntilRule, hr] using ih
  | @reduce rs w cstk vsRev vstk ast op k hlen _ ih =>
      have hle : k ≤ (vsRev ++ vstk).length := by simp [hlen]
      have htake : (vsRev ++ vstk).take k = vsRev := by subst hlen; exact List.take_left
      have hdrop : (vsRev ++ vstk).drop k = vstk := by subst hlen; exact List.drop_left
      cases rs with
      | nil =>
          simp only [execAttrStackReplay, execNoRules, hle, ↓reduceIte, htake, hdrop]
          exact ih
      | cons r rs' =>
          simp only [execAttrStackReplay, execStepUntilRule, hle, ↓reduceIte, htake, hdrop]
          exact ih

/-- Exact equivalence between executable `execAttrReplay` and inductive `AttrReplay`. -/
theorem execAttrReplay_iff {T NT SemOp Val : Type}
    [DecidableEq T] [DecidableEq NT] [DecidableEq SemOp]
    (g : AttrCfg T NT SemOp Val) (rs : List (AttrRule T NT SemOp)) (w : List T) (ast : Val) :
    execAttrReplay g rs w = some ast ↔ AttrReplay g rs w ast :=
  ⟨execAttrStackReplay_sound g rs w _ [] ast, execAttrStackReplay_complete⟩

instance instDecidableAttrReplay {T NT SemOp Val : Type}
    [DecidableEq T] [DecidableEq NT] [DecidableEq SemOp] [DecidableEq Val]
    (g : AttrCfg T NT SemOp Val) (rs : List (AttrRule T NT SemOp)) (w : List T) (ast : Val) :
    Decidable (AttrReplay g rs w ast) :=
  decidable_of_iff (execAttrReplay g rs w = some ast) (execAttrReplay_iff g rs w ast)

/-! ## §2. Executable LL(1) Disjoint-Predict-Set Checker & Uniqueness Theorem -/

section LL1

def dedupInsert {α : Type} [DecidableEq α] (x : α) (xs : List α) : List α :=
  if x ∈ xs then xs else x :: xs

def dedupUnion {α : Type} [DecidableEq α] (xs ys : List α) : List α :=
  ys.foldl (fun acc y => dedupInsert y acc) xs

/-- Insert all missing elements of `ys` into `xs`, returning `(merged, changed)` strictly so
kernel call-by-name `whnf` forces every list spine on each fixed-point pass (zero thunk buildup!). -/
def strictUnionChanged {α : Type} [DecidableEq α] : List α → List α → List α × Bool
  | xs, [] => (xs, false)
  | xs, y :: ys =>
      if y ∈ xs then
        strictUnionChanged xs ys
      else
        let (rest, _) := strictUnionChanged (y :: xs) ys
        (rest, true)

def listSubset {α : Type} [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => decide (x ∈ ys))

def listDisjoint {α : Type} [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => !decide (x ∈ ys))

theorem listSubset_iff {α : Type} [DecidableEq α] (xs ys : List α) :
    listSubset xs ys = true ↔ ∀ x ∈ xs, x ∈ ys := by
  simp [listSubset, List.all_eq_true]

theorem listDisjoint_iff {α : Type} [DecidableEq α] (xs ys : List α) :
    listDisjoint xs ys = true ↔ ∀ x ∈ xs, x ∉ ys := by
  simp [listDisjoint, List.all_eq_true]

def assocLookup {K V : Type} [DecidableEq K] (k : K) : List (K × List V) → List V
  | [] => []
  | (k', vs) :: rest => if k = k' then vs else assocLookup k rest

def assocUnionChanged {K V : Type} [DecidableEq K] [DecidableEq V]
    (k : K) (newVs : List V) : List (K × List V) → List (K × List V) × Bool
  | [] =>
      let (u, ch) := strictUnionChanged [] newVs
      if ch then ([(k, u)], true) else ([(k, [])], false)
  | (k', vs) :: rest =>
      if k = k' then
        let (u, ch) := strictUnionChanged vs newVs
        if ch then ((k', u) :: rest, true) else ((k', vs) :: rest, false)
      else
        let (rest', ch) := assocUnionChanged k newVs rest
        if ch then ((k', vs) :: rest', true) else ((k', vs) :: rest', false)

/-- Strict early-stopping fixed-point driver (`≤ fuel` passes). -/
def fixPasses {α : Type} : Nat → (α → α × Bool) → α → α
  | 0, _, cur => cur
  | fuel + 1, step, cur =>
      let (next, changed) := step cur
      if changed then fixPasses fuel step next else next

def symNullable {T NT : Type} [DecidableEq NT] (nullNTs : List NT) : Symbol T NT → Bool
  | .terminal _ => false
  | .nonterminal A => decide (A ∈ nullNTs)

def seqNullable {T NT : Type} [DecidableEq NT] (nullNTs : List NT) (syms : List (Symbol T NT)) : Bool :=
  syms.all (symNullable nullNTs)

@[simp] theorem seqNullable_nil {T NT : Type} [DecidableEq NT] (nullNTs : List NT) :
    seqNullable nullNTs ([] : List (Symbol T NT)) = true := rfl

@[simp] theorem seqNullable_cons {T NT : Type} [DecidableEq NT] (nullNTs : List NT)
    (s : Symbol T NT) (rest : List (Symbol T NT)) :
    seqNullable nullNTs (s :: rest) = (symNullable nullNTs s && seqNullable nullNTs rest) := rfl

theorem seqNullable_append {T NT : Type} [DecidableEq NT] (nullNTs : List NT)
    (xs ys : List (Symbol T NT)) :
    seqNullable nullNTs (xs ++ ys) = (seqNullable nullNTs xs && seqNullable nullNTs ys) := by
  simp [seqNullable, List.all_append]

def seqFirst {T NT : Type} [DecidableEq T] [DecidableEq NT]
    (nullNTs : List NT) (firstTab : List (NT × List T)) : List (Symbol T NT) → List T
  | [] => []
  | .terminal t :: _ => [t]
  | .nonterminal A :: rest =>
      if A ∈ nullNTs then assocLookup A firstTab ++ seqFirst nullNTs firstTab rest
      else assocLookup A firstTab

theorem mem_seqFirst_append {T NT : Type} [DecidableEq T] [DecidableEq NT]
    (nullNTs : List NT) (firstTab : List (NT × List T))
    (xs ys : List (Symbol T NT)) (a : T) :
    a ∈ seqFirst nullNTs firstTab (xs ++ ys) ↔
      a ∈ seqFirst nullNTs firstTab xs ∨
        (seqNullable nullNTs xs = true ∧ a ∈ seqFirst nullNTs firstTab ys) := by
  induction xs with
  | nil => simp [seqFirst, seqNullable]
  | cons s xs ih =>
      cases s with
      | terminal t =>
          simp [seqFirst, seqNullable, symNullable]
      | nonterminal A =>
          by_cases hA : A ∈ nullNTs
          · have hdec : symNullable (T := T) nullNTs (.nonterminal A) = true := by
              simp [symNullable, hA]
            simp only [List.cons_append, seqFirst, hA, ↓reduceIte, List.mem_append, ih,
              seqNullable_cons, hdec, Bool.true_and]
            tauto
          · have hdec : symNullable (T := T) nullNTs (.nonterminal A) = false := by
              simp [symNullable, hA]
            simp [List.cons_append, seqFirst, hA, seqNullable_cons, hdec]

def rulePredict {T NT SemOp : Type} [DecidableEq T] [DecidableEq NT]
    (nullNTs : List NT) (firstTab : List (NT × List T)) (followTab : List (NT × List (Option T)))
    (r : AttrRule T NT SemOp) : List (Option T) :=
  (seqFirst nullNTs firstTab r.rhs).map some ++
    (if seqNullable nullNTs r.rhs then assocLookup r.lhs followTab else [])

def collectNTs {T NT SemOp Val : Type} [DecidableEq NT] (g : AttrCfg T NT SemOp Val) : List NT :=
  let fromSym : Symbol T NT → List NT
    | .terminal _ => []
    | .nonterminal A => [A]
  g.rules.foldl
    (fun acc r =>
      let acc' := dedupInsert r.lhs acc
      r.rhs.foldl (fun a s => dedupUnion a (fromSym s)) acc')
    [g.initial]

/-- Strict fixed-point table builder with early convergence (zero lazy thunk chains in WHNF). -/
def computeLl1Tables {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT]
    (g : AttrCfg T NT SemOp Val) :
    List NT × List (NT × List T) × List (NT × List (Option T)) :=
  let nts := collectNTs g
  let rounds := nts.length + 1
  let rec stepNull (rules : List (AttrRule T NT SemOp)) (cur : List NT) (ch : Bool) :
      List NT × Bool :=
    match rules with
    | [] => (cur, ch)
    | r :: rs =>
        if r.lhs ∉ cur && seqNullable cur r.rhs then
          stepNull rs (r.lhs :: cur) true
        else
          stepNull rs cur ch
  let nullNTs := fixPasses rounds (fun cur => stepNull g.rules cur false) []

  let rec stepFirst (rules : List (AttrRule T NT SemOp)) (cur : List (NT × List T)) (ch : Bool) :
      List (NT × List T) × Bool :=
    match rules with
    | [] => (cur, ch)
    | r :: rs =>
        let (cur', c) := assocUnionChanged r.lhs (seqFirst nullNTs cur r.rhs) cur
        if c then stepFirst rs cur' true else stepFirst rs cur' ch
  let initFirst : List (NT × List T) := nts.map (fun A => (A, []))
  let firstTab := fixPasses rounds (fun cur => stepFirst g.rules cur false) initFirst

  let rec stepFollowRhs (lhs : NT) (cur : List (NT × List (Option T))) (ch : Bool) :
      List (Symbol T NT) → List (NT × List (Option T)) × Bool
    | [] => (cur, ch)
    | .terminal _ :: suf => stepFollowRhs lhs cur ch suf
    | .nonterminal B :: suf =>
        let addFirst := (seqFirst nullNTs firstTab suf).map some
        let addFol := if seqNullable nullNTs suf then assocLookup lhs cur else []
        let (cur', c) := assocUnionChanged B (addFirst ++ addFol) cur
        if c then stepFollowRhs lhs cur' true suf else stepFollowRhs lhs cur' ch suf
  let rec stepFollowRules (rules : List (AttrRule T NT SemOp))
      (cur : List (NT × List (Option T))) (ch : Bool) :
      List (NT × List (Option T)) × Bool :=
    match rules with
    | [] => (cur, ch)
    | r :: rs =>
        let (cur', c) := stepFollowRhs r.lhs cur ch r.rhs
        if c then stepFollowRules rs cur' true else stepFollowRules rs cur' false
  let initFollow : List (NT × List (Option T)) :=
    nts.map (fun A => (A, if A = g.initial then [none] else []))
  let followTab := fixPasses rounds (fun cur => stepFollowRules g.rules cur false) initFollow
  (nullNTs, firstTab, followTab)

def checkRhsFollowClosed {T NT : Type} [DecidableEq T] [DecidableEq NT]
    (nullNTs : List NT) (firstTab : List (NT × List T)) (followTab : List (NT × List (Option T)))
    (lhs : NT) : List (Symbol T NT) → Bool
  | [] => true
  | .terminal _ :: suf => checkRhsFollowClosed nullNTs firstTab followTab lhs suf
  | .nonterminal B :: suf =>
      listSubset ((seqFirst nullNTs firstTab suf).map some) (assocLookup B followTab) &&
      (if seqNullable nullNTs suf then
        listSubset (assocLookup lhs followTab) (assocLookup B followTab)
       else true) &&
      checkRhsFollowClosed nullNTs firstTab followTab lhs suf

def checkRulesDisjoint {T NT SemOp : Type} [DecidableEq T] [DecidableEq NT]
    (nullNTs : List NT) (firstTab : List (NT × List T)) (followTab : List (NT × List (Option T))) :
    List (AttrRule T NT SemOp) → Bool
  | [] => true
  | r :: rs =>
      let p := rulePredict nullNTs firstTab followTab r
      rs.all (fun r' =>
        if r.lhs = r'.lhs then
          listDisjoint p (rulePredict nullNTs firstTab followTab r')
        else true) &&
      checkRulesDisjoint nullNTs firstTab followTab rs

def checkLl1Tables {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT]
    (g : AttrCfg T NT SemOp Val)
    (nullNTs : List NT) (firstTab : List (NT × List T))
    (followTab : List (NT × List (Option T))) : Bool :=
  decide (none ∈ assocLookup g.initial followTab) &&
  g.rules.all (fun r =>
    (if seqNullable nullNTs r.rhs then decide (r.lhs ∈ nullNTs) else true) &&
    listSubset (seqFirst nullNTs firstTab r.rhs) (assocLookup r.lhs firstTab) &&
    checkRhsFollowClosed nullNTs firstTab followTab r.lhs r.rhs) &&
  checkRulesDisjoint nullNTs firstTab followTab g.rules

/-- **Executable LL(1) Disjoint-Predict-Set Determinacy Checker (`ll1Deterministic : AttrCfg → Bool`)**. -/
def ll1Deterministic {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT]
    (g : AttrCfg T NT SemOp Val) : Bool :=
  let (nullNTs, firstTab, followTab) := computeLl1Tables g
  checkLl1Tables g nullNTs firstTab followTab

/-! ### Proof of `attrReplay_unique_of_ll1` -/

private theorem rhsFollowClosed_split {T NT : Type} [DecidableEq T] [DecidableEq NT]
    {nullNTs : List NT} {firstTab : List (NT × List T)} {followTab : List (NT × List (Option T))}
    {lhs B : NT} :
    ∀ (pre suf : List (Symbol T NT)),
      checkRhsFollowClosed nullNTs firstTab followTab lhs (pre ++ .nonterminal B :: suf) = true →
      (∀ x ∈ (seqFirst nullNTs firstTab suf).map some, x ∈ assocLookup B followTab) ∧
      (seqNullable nullNTs suf = true →
        ∀ x ∈ assocLookup lhs followTab, x ∈ assocLookup B followTab) := by
  intro pre
  induction pre with
  | nil =>
      intro suf h
      simp only [List.nil_append, checkRhsFollowClosed, Bool.and_eq_true, listSubset_iff] at h
      rcases h with ⟨⟨hf, hfol⟩, _⟩
      refine ⟨hf, fun hnull => ?_⟩
      simpa [hnull, listSubset_iff] using hfol
  | cons s pre ih =>
      intro suf h
      cases s with
      | terminal _ =>
          simp only [List.cons_append, checkRhsFollowClosed] at h
          exact ih suf h
      | nonterminal _ =>
          simp only [List.cons_append, checkRhsFollowClosed, Bool.and_eq_true] at h
          exact ih suf h.2

private def FollowSafe {T NT : Type} [DecidableEq T] [DecidableEq NT]
    (nullNTs : List NT) (firstTab : List (NT × List T)) (followTab : List (NT × List (Option T)))
    (syms : List (Symbol T NT)) : Prop :=
  ∀ (pre suf : List (Symbol T NT)) (B : NT),
    syms = pre ++ .nonterminal B :: suf →
      (∀ x ∈ (seqFirst nullNTs firstTab suf).map some, x ∈ assocLookup B followTab) ∧
      (seqNullable nullNTs suf = true → none ∈ assocLookup B followTab)

private theorem followSafe_initial {T NT : Type} [DecidableEq T] [DecidableEq NT]
    {nullNTs : List NT} {firstTab : List (NT × List T)} {followTab : List (NT × List (Option T))}
    {init : NT} (hinit : none ∈ assocLookup init followTab) :
    FollowSafe nullNTs firstTab followTab [.nonterminal init] := by
  intro pre suf B heq
  cases pre with
  | nil =>
      simp only [List.nil_append, List.cons.injEq, Symbol.nonterminal.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact ⟨by simp [seqFirst], fun _ => hinit⟩
  | cons a pre' =>
      cases pre' <;> simp at heq

private theorem followSafe_term {T NT : Type} [DecidableEq T] [DecidableEq NT]
    {nullNTs : List NT} {firstTab : List (NT × List T)} {followTab : List (NT × List (Option T))}
    {t : T} {rest : List (Symbol T NT)}
    (hsafe : FollowSafe nullNTs firstTab followTab (.terminal t :: rest)) :
    FollowSafe nullNTs firstTab followTab rest := by
  intro pre suf B heq
  exact hsafe (.terminal t :: pre) suf B (by simp [heq])

private theorem followSafe_rule {T NT SemOp : Type} [DecidableEq T] [DecidableEq NT]
    {nullNTs : List NT} {firstTab : List (NT × List T)} {followTab : List (NT × List (Option T))}
    {r : AttrRule T NT SemOp} {rest : List (Symbol T NT)}
    (hrFol : checkRhsFollowClosed nullNTs firstTab followTab r.lhs r.rhs = true)
    (hsafe : FollowSafe nullNTs firstTab followTab (.nonterminal r.lhs :: rest)) :
    FollowSafe nullNTs firstTab followTab (r.rhs ++ rest) := by
  have ⟨hlhsFirst, hlhsEof⟩ := hsafe [] rest r.lhs rfl
  intro pre suf B heq
  rcases List.append_eq_append_iff.mp heq with ⟨pre', _, hrest⟩ | ⟨suf₁, hrhs, hsuf⟩
  · -- `B` lies inside `rest = pre' ++ .nonterminal B :: suf`
    exact hsafe (.nonterminal r.lhs :: pre') suf B (by simp [hrest])
  · -- `B` lies inside `r.rhs` (`r.rhs = pre ++ suf₁` and `.nonterminal B :: suf = suf₁ ++ rest`)
    cases suf₁ with
    | nil =>
        simp only [List.nil_append] at hsuf
        exact hsafe [.nonterminal r.lhs] suf B (by simp [← hsuf])
    | cons s₀ suf₁' =>
        simp only [List.cons_append] at hsuf
        injection hsuf with hs₀ hsufEq
        subst hs₀ hsufEq
        have ⟨hbFirst, hbFol⟩ := rhsFollowClosed_split pre suf₁' (hrhs ▸ hrFol)
        refine ⟨?_, ?_⟩
        · intro x hx
          rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
          rcases (mem_seqFirst_append nullNTs firstTab suf₁' rest a).mp ha with ha₁ | ⟨hnull₁, ha₂⟩
          · exact hbFirst (some a) (List.mem_map_of_mem ha₁)
          · exact hbFol hnull₁ (some a) (hlhsFirst (some a) (List.mem_map_of_mem ha₂))
        · intro hnullAll
          rw [seqNullable_append, Bool.and_eq_true] at hnullAll
          exact hbFol hnullAll.1 none (hlhsEof hnullAll.2)

private theorem replay_nil_seqNullable {T NT SemOp Val : Type} [DecidableEq NT]
    {g : AttrCfg T NT SemOp Val} {nullNTs : List NT}
    (hnullClosed : ∀ r ∈ g.rules, seqNullable nullNTs r.rhs = true → r.lhs ∈ nullNTs)
    {rs : List (AttrRule T NT SemOp)} {w : List T}
    {cstk : List (WorkItem T NT SemOp)} {vstk : List Val} {ast : Val}
    (h : AttrStackReplay g rs w cstk vstk ast) (hw : w = []) :
    seqNullable nullNTs (symsOfStack cstk) = true := by
  induction h with
  | done _ => rfl
  | term _ _ _ => cases hw
  | @rule r _ _ cstk _ _ hr _ ih =>
      have ih' := ih hw
      simp only [symsOfStack_append, symsOfStack_map_sym, symsOfStack_reduce,
        seqNullable_append, Bool.and_eq_true] at ih'
      simp only [symsOfStack_sym, seqNullable_cons, symNullable, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hnullClosed r hr ih'.1, ih'.2⟩
  | reduce _ _ _ _ ih =>
      exact ih hw

private theorem replay_cons_seqFirst {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT]
    {g : AttrCfg T NT SemOp Val} {nullNTs : List NT} {firstTab : List (NT × List T)}
    (hnullClosed : ∀ r ∈ g.rules, seqNullable nullNTs r.rhs = true → r.lhs ∈ nullNTs)
    (hfirstClosed : ∀ r ∈ g.rules, ∀ x ∈ seqFirst nullNTs firstTab r.rhs,
      x ∈ assocLookup r.lhs firstTab)
    {rs : List (AttrRule T NT SemOp)} {w : List T}
    {cstk : List (WorkItem T NT SemOp)} {vstk : List Val} {ast : Val}
    (h : AttrStackReplay g rs w cstk vstk ast) {a : T} {w' : List T} (hw : w = a :: w') :
    a ∈ seqFirst nullNTs firstTab (symsOfStack cstk) := by
  induction h with
  | done _ => cases hw
  | term t _ _ =>
      injection hw with hta _
      subst hta
      simp [symsOfStack, seqFirst]
  | @rule r _ _ cstk _ _ hr _ ih =>
      have ih' := ih hw
      simp only [symsOfStack_append, symsOfStack_map_sym, symsOfStack_reduce] at ih'
      rcases (mem_seqFirst_append nullNTs firstTab r.rhs (symsOfStack cstk) a).mp ih' with
        haRhs | ⟨hnullRhs, haRest⟩
      · have haLhs := hfirstClosed r hr a haRhs
        by_cases hmem : r.lhs ∈ nullNTs
        · simp [symsOfStack, seqFirst, hmem, haLhs]
        · simp [symsOfStack, seqFirst, hmem, haLhs]
      · have hmem : r.lhs ∈ nullNTs := hnullClosed r hr hnullRhs
        simp [symsOfStack, seqFirst, hmem, haRest]
  | reduce _ _ _ _ ih =>
      exact ih hw

private theorem head_mem_rulePredict {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT]
    {g : AttrCfg T NT SemOp Val} {nullNTs : List NT}
    {firstTab : List (NT × List T)} {followTab : List (NT × List (Option T))}
    (hnullClosed : ∀ r ∈ g.rules, seqNullable nullNTs r.rhs = true → r.lhs ∈ nullNTs)
    (hfirstClosed : ∀ r ∈ g.rules, ∀ x ∈ seqFirst nullNTs firstTab r.rhs,
      x ∈ assocLookup r.lhs firstTab)
    {r : AttrRule T NT SemOp} {rs : List (AttrRule T NT SemOp)} {w : List T}
    {cstk : List (WorkItem T NT SemOp)} {vstk : List Val} {ast : Val}
    (hsafe : FollowSafe nullNTs firstTab followTab (.nonterminal r.lhs :: symsOfStack cstk))
    (h : AttrStackReplay g rs w (r.rhs.map .sym ++ .reduce r.op r.rhs.length :: cstk) vstk ast) :
    w.head? ∈ rulePredict nullNTs firstTab followTab r := by
  have ⟨hlhsFirst, hlhsEof⟩ := hsafe [] (symsOfStack cstk) r.lhs rfl
  cases w with
  | nil =>
      have hnull := replay_nil_seqNullable hnullClosed h rfl
      simp only [symsOfStack_append, symsOfStack_map_sym, symsOfStack_reduce,
        seqNullable_append, Bool.and_eq_true] at hnull
      simp only [List.head?_nil, rulePredict, hnull.1, ↓reduceIte, List.mem_append]
      exact Or.inr (hlhsEof hnull.2)
  | cons a w' =>
      have hfirst := replay_cons_seqFirst hnullClosed hfirstClosed h rfl
      simp only [symsOfStack_append, symsOfStack_map_sym, symsOfStack_reduce] at hfirst
      simp only [List.head?_cons, rulePredict, List.mem_append]
      rcases (mem_seqFirst_append nullNTs firstTab r.rhs (symsOfStack cstk) a).mp hfirst with
        haRhs | ⟨hnullRhs, haRest⟩
      · exact Or.inl (List.mem_map_of_mem haRhs)
      · simp only [hnullRhs, ↓reduceIte]
        exact Or.inr (hlhsFirst (some a) (List.mem_map_of_mem haRest))

private theorem eq_of_checkRulesDisjoint {T NT SemOp : Type} [DecidableEq T] [DecidableEq NT]
    {nullNTs : List NT} {firstTab : List (NT × List T)} {followTab : List (NT × List (Option T))}
    {rules : List (AttrRule T NT SemOp)}
    (hdisj : checkRulesDisjoint nullNTs firstTab followTab rules = true)
    {r₁ r₂ : AttrRule T NT SemOp} (hr₁ : r₁ ∈ rules) (hr₂ : r₂ ∈ rules)
    (hlhs : r₁.lhs = r₂.lhs) {tok : Option T}
    (ht₁ : tok ∈ rulePredict nullNTs firstTab followTab r₁)
    (ht₂ : tok ∈ rulePredict nullNTs firstTab followTab r₂) :
    r₁ = r₂ := by
  induction rules with
  | nil => cases hr₁
  | cons r rs ih =>
      simp only [checkRulesDisjoint, Bool.and_eq_true, List.all_eq_true] at hdisj
      rcases hdisj with ⟨hhead, htail⟩
      rcases List.mem_cons.mp hr₁ with rfl | hm₁
      · rcases List.mem_cons.mp hr₂ with rfl | hm₂
        · rfl
        · have hd := hhead r₂ hm₂
          simp only [hlhs, ↓reduceIte, listDisjoint_iff] at hd
          exact False.elim (hd tok ht₁ ht₂)
      · rcases List.mem_cons.mp hr₂ with rfl | hm₂
        · have hd := hhead r₁ hm₁
          simp only [hlhs.symm, ↓reduceIte, listDisjoint_iff] at hd
          exact False.elim (hd tok ht₂ ht₁)
        · exact ih htail hm₁ hm₂

private theorem attrStackReplay_unique_of_tables {T NT SemOp Val : Type}
    [DecidableEq T] [DecidableEq NT]
    {g : AttrCfg T NT SemOp Val} {nullNTs : List NT}
    {firstTab : List (NT × List T)} {followTab : List (NT × List (Option T))}
    (hnullClosed : ∀ r ∈ g.rules, seqNullable nullNTs r.rhs = true → r.lhs ∈ nullNTs)
    (hfirstClosed : ∀ r ∈ g.rules, ∀ x ∈ seqFirst nullNTs firstTab r.rhs,
      x ∈ assocLookup r.lhs firstTab)
    (hfolClosed : ∀ r ∈ g.rules,
      checkRhsFollowClosed nullNTs firstTab followTab r.lhs r.rhs = true)
    (hdisj : checkRulesDisjoint nullNTs firstTab followTab g.rules = true)
    {rs₁ rs₂ : List (AttrRule T NT SemOp)} {w : List T}
    {cstk : List (WorkItem T NT SemOp)} {vstk : List Val} {ast₁ ast₂ : Val}
    (hsafe : FollowSafe nullNTs firstTab followTab (symsOfStack cstk))
    (h₁ : AttrStackReplay g rs₁ w cstk vstk ast₁)
    (h₂ : AttrStackReplay g rs₂ w cstk vstk ast₂) :
    ast₁ = ast₂ ∧ rs₁ = rs₂ := by
  induction h₁ generalizing rs₂ ast₂ with
  | done _ =>
      cases h₂ with
      | done _ => exact ⟨rfl, rfl⟩
  | term t _ ih =>
      cases h₂ with
      | term _ h₂' =>
          exact ih (followSafe_term (by simpa [symsOfStack] using hsafe)) h₂'
  | @rule r₁ rs₁' w cstk' vstk ast₁ hr₁ h₁' ih =>
      generalize hcEq : WorkItem.sym (SemOp := SemOp) (.nonterminal r₁.lhs) :: cstk' = cstkFull at h₂
      cases h₂ with
      | done _ => cases hcEq
      | term _ _ => cases hcEq
      | reduce _ _ _ _ => cases hcEq
      | @rule r₂ rs₂' _ cstk₂ _ _ hr₂ h₂' =>
          simp only [List.cons.injEq, WorkItem.sym.injEq, Symbol.nonterminal.injEq] at hcEq
          rcases hcEq with ⟨hlhs, hcstk⟩
          subst hcstk
          have hsafeTop : FollowSafe nullNTs firstTab followTab
              (.nonterminal r₁.lhs :: symsOfStack cstk') := by
            simpa [symsOfStack] using hsafe
          have ht₁ := head_mem_rulePredict hnullClosed hfirstClosed hsafeTop h₁'
          have ht₂ := head_mem_rulePredict hnullClosed hfirstClosed
            (hlhs ▸ hsafeTop) h₂'
          have hreq : r₁ = r₂ :=
            eq_of_checkRulesDisjoint hdisj hr₁ hr₂ hlhs ht₁ ht₂
          subst hreq
          have hsafeNext : FollowSafe nullNTs firstTab followTab
              (symsOfStack (r₁.rhs.map .sym ++ .reduce r₁.op r₁.rhs.length :: cstk')) := by
            simpa using followSafe_rule (hfolClosed r₁ hr₁) hsafeTop
          obtain ⟨hast, hrs⟩ := ih hsafeNext h₂'
          exact ⟨hast, congrArg (List.cons r₁) hrs⟩
  | @reduce rs₁ w cstk' vsRev₁ vstk₁' ast₁ op k hlen₁ _ ih =>
      generalize hcEq : WorkItem.reduce (T := T) (NT := NT) op k :: cstk' = cstkFull at h₂
      generalize hvEq : vsRev₁ ++ vstk₁' = vstkFull at h₂
      cases h₂ with
      | done _ => cases hcEq
      | term _ _ => cases hcEq
      | rule _ _ => cases hcEq
      | @reduce _ _ cstk₂ vsRev₂ vstk₂' _ op₂ k₂ hlen₂ h₂' =>
          simp only [List.cons.injEq, WorkItem.reduce.injEq] at hcEq
          rcases hcEq with ⟨⟨rfl, rfl⟩, rfl⟩
          obtain ⟨rfl, rfl⟩ := List.append_inj hvEq.symm (hlen₂.trans hlen₁.symm)
          exact ih hsafe h₂'

/-- **`attrReplay_unique_of_ll1`** — Main Determinacy & Unambiguity Theorem:
If `ll1Deterministic g = true`, then every input `w` admits **at most one** accepting rule sequence
`rs` and **at most one** extracted AST `ast`. -/
theorem attrReplay_unique_of_ll1 {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT]
    (g : AttrCfg T NT SemOp Val)
    {rs₁ rs₂ : List (AttrRule T NT SemOp)} {w : List T} {ast₁ ast₂ : Val}
    (hll1 : ll1Deterministic g = true)
    (h₁ : AttrReplay g rs₁ w ast₁)
    (h₂ : AttrReplay g rs₂ w ast₂) :
    ast₁ = ast₂ ∧ rs₁ = rs₂ := by
  unfold ll1Deterministic checkLl1Tables at hll1
  rcases htab : computeLl1Tables g with ⟨nullNTs, firstTab, followTab⟩
  rw [htab] at hll1
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hll1
  rcases hll1 with ⟨⟨hinit, hrules⟩, hdisj⟩
  have hnullClosed : ∀ r ∈ g.rules, seqNullable nullNTs r.rhs = true → r.lhs ∈ nullNTs := by
    intro r hr hnull
    have h := (hrules r hr).1.1
    simpa [hnull] using h
  have hfirstClosed : ∀ r ∈ g.rules, ∀ x ∈ seqFirst nullNTs firstTab r.rhs,
      x ∈ assocLookup r.lhs firstTab := by
    intro r hr
    exact (listSubset_iff _ _).mp (hrules r hr).1.2
  have hfolClosed : ∀ r ∈ g.rules,
      checkRhsFollowClosed nullNTs firstTab followTab r.lhs r.rhs = true :=
    fun r hr => (hrules r hr).2
  exact attrStackReplay_unique_of_tables hnullClosed hfirstClosed hfolClosed hdisj
    (by simpa [symsOfStack] using followSafe_initial hinit) h₁ h₂

def ll1PredictStep {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT]
    (g : AttrCfg T NT SemOp Val)
    (nullNTs : List NT) (firstTab : List (NT × List T))
    (followTab : List (NT × List (Option T))) :
    Nat → List T → List (WorkItem T NT SemOp) → List Val → List (AttrRule T NT SemOp) →
      Option (List (AttrRule T NT SemOp) × Val)
  | _, [], [], [ast], revRs => some (revRs.reverse, ast)
  | 0, _, _, _, _ => none
  | _ + 1, _, [], _, _ => none
  | fuel + 1, t' :: w, .sym (.terminal t) :: cstk, vstk, revRs =>
      if t' = t then
        ll1PredictStep g nullNTs firstTab followTab fuel w cstk (g.termVal t :: vstk) revRs
      else none
  | _ + 1, [], .sym (.terminal _) :: _, _, _ => none
  | fuel + 1, w, .sym (.nonterminal A) :: cstk, vstk, revRs =>
      let tok := w.head?
      match g.rules.find? (fun r =>
        decide (r.lhs = A) && decide (tok ∈ rulePredict nullNTs firstTab followTab r)) with
      | none => none
      | some r =>
          ll1PredictStep g nullNTs firstTab followTab fuel w
            (r.rhs.map .sym ++ .reduce r.op r.rhs.length :: cstk) vstk (r :: revRs)
  | fuel + 1, w, .reduce op k :: cstk, vstk, revRs =>
      if k ≤ vstk.length then
        let vsRev := vstk.take k
        let vstk' := vstk.drop k
        ll1PredictStep g nullNTs firstTab followTab fuel w cstk
          (g.evalOp op vsRev.reverse :: vstk') revRs
      else none

def ll1Parse {T NT SemOp Val : Type} [DecidableEq T] [DecidableEq NT]
    (g : AttrCfg T NT SemOp Val) (w : List T) : Option (List (AttrRule T NT SemOp) × Val) :=
  let (nullNTs, firstTab, followTab) := computeLl1Tables g
  let fuel := (w.length + 1) * (g.rules.length + 8) + 16
  ll1PredictStep g nullNTs firstTab followTab fuel w [.sym (.nonterminal g.initial)] [] []

end LL1

/-! ## §3. Real Byte-Level JSON Tool-Call / `Mini` Command Grammar & Ambiguous Splice Attack -/

/-- Pure kernel-reducible ASCII byte conversion (`String.toList` avoids opaque `@[extern] String.toUTF8`). -/
def asciiBytes (s : String) : List UInt8 :=
  s.toList.map (fun c => UInt8.ofNat c.toNat)

/-- Extracted first-order AST carrier for `Mini` JSON tool calls and batch envelopes. -/
inductive MiniValue where
  | vByte        : UInt8 → MiniValue
  | vBytes       : List UInt8 → MiniValue
  | vDigits      : List Nat → MiniValue
  | vNat         : Nat → MiniValue
  | vToolCall    : (tool : List UInt8) → (target : List UInt8) → (amount : Nat) → MiniValue
  | vCotToolCall : (cot : List UInt8) → (tool : List UInt8) → (target : List UInt8) → (amount : Nat) → MiniValue
  | vBatchNil    : MiniValue
  | vBatchCons   : MiniValue → MiniValue → MiniValue
  | vUnit        : MiniValue
  deriving DecidableEq, Repr

def MiniValue.ofBatchList : List MiniValue → MiniValue
  | [] => .vBatchNil
  | x :: xs => .vBatchCons x (MiniValue.ofBatchList xs)

def MiniValue.toBatchList : MiniValue → List MiniValue
  | .vBatchCons x rest => x :: rest.toBatchList
  | _ => []

inductive MiniNT where
  | Root
  | TopExpr
  | ObjDispatch
  | ToolRest
  | CotRest
  | BatchBody
  | BatchTail
  | StrVal
  | Chars
  | Esc
  | NatVal
  | Digits
  | WS
  deriving DecidableEq, Repr

inductive MiniOp where
  | passAt      : Nat → MiniOp
  | unitOp      : MiniOp
  | strUnquote  : MiniOp
  | charsNil    : MiniOp
  | charsCons   : UInt8 → MiniOp
  | charsEsc    : MiniOp
  | escConst    : UInt8 → MiniOp
  | natZero     : MiniOp
  | natPos      : Nat → MiniOp
  | digitsNil   : MiniOp
  | digitsCons  : Nat → MiniOp
  | mkToolRest  : MiniOp
  | mkCotRest   : MiniOp
  | batchEmpty  : MiniOp
  | batchCons   : MiniOp
  deriving DecidableEq, Repr

def evalMiniOp : MiniOp → List MiniValue → MiniValue
  | .passAt idx, vs => vs.getD idx .vUnit
  | .unitOp, _ => .vUnit
  | .strUnquote, vs => vs.getD 1 (.vBytes [])
  | .charsNil, _ => .vBytes []
  | .charsCons b, vs =>
      match vs.getD 1 (.vBytes []) with
      | .vBytes bs => .vBytes (b :: bs)
      | _ => .vBytes [b]
  | .charsEsc, vs =>
      match vs.getD 1 (.vByte 0), vs.getD 2 (.vBytes []) with
      | .vByte b, .vBytes bs => .vBytes (b :: bs)
      | _, _ => .vBytes []
  | .escConst b, _ => .vByte b
  | .natZero, _ => .vNat 0
  | .natPos d0, vs =>
      match vs.getD 1 (.vDigits []) with
      | .vDigits ds => .vNat ((d0 :: ds).foldl (fun acc d => acc * 10 + d) 0)
      | _ => .vNat d0
  | .digitsNil, _ => .vDigits []
  | .digitsCons d, vs =>
      match vs.getD 1 (.vDigits []) with
      | .vDigits ds => .vDigits (d :: ds)
      | _ => .vDigits [d]
  | .mkToolRest, vs =>
      match vs.getD 7 (.vBytes []), vs.getD 22 (.vBytes []), vs.getD 37 (.vNat 0) with
      | .vBytes tool, .vBytes target, .vNat amt => .vToolCall tool target amt
      | _, _, _ => .vUnit
  | .mkCotRest, vs =>
      match vs.getD 6 (.vBytes []), vs.getD 19 (.vBytes []), vs.getD 34 (.vBytes []), vs.getD 49 (.vNat 0) with
      | .vBytes cot, .vBytes tool, .vBytes target, .vNat amt => .vCotToolCall cot tool target amt
      | _, _, _, _ => .vUnit
  | .batchEmpty, _ => .vBatchNil
  | .batchCons, vs =>
      match vs with
      | [item, _, rest] => .vBatchCons item rest
      | [_, _, item, _, rest] => .vBatchCons item rest
      | _ => .vBatchNil

def litSyms (s : String) : List (Symbol UInt8 MiniNT) :=
  (asciiBytes s).map (Symbol.terminal (N := MiniNT))

def safeJsonStringBytes : List UInt8 :=
  (List.range 95).filterMap fun k =>
    let b : UInt8 := UInt8.ofNat (0x20 + k)
    if b == 0x22 || b == 0x5C then none else some b

/-- **Production Byte-Level RFC 8259 JSON Tool-Call / `Mini` Command Grammar (`miniJsonCfg`)**. -/
def miniJsonCfg : AttrCfg UInt8 MiniNT MiniOp MiniValue where
  initial := .Root
  termVal := MiniValue.vByte
  evalOp  := evalMiniOp
  rules   :=
    let t := Symbol.terminal (T := UInt8) (N := MiniNT)
    let nt := Symbol.nonterminal (T := UInt8) (N := MiniNT)
    [ ⟨.Root, [nt .WS, nt .TopExpr, nt .WS], .passAt 1⟩,
      ⟨.TopExpr, [t 0x7B, nt .WS, t 0x22, nt .ObjDispatch], .passAt 3⟩,
      ⟨.TopExpr, [t 0x5B, nt .WS, nt .BatchBody, t 0x5D], .passAt 2⟩,
      ⟨.ObjDispatch, t 0x74 :: [nt .ToolRest], .passAt 1⟩,
      ⟨.ObjDispatch, t 0x63 :: [nt .CotRest], .passAt 1⟩,
      ⟨.ToolRest,
        litSyms "ool\"" ++ [nt .WS, t 0x3A, nt .WS, nt .StrVal, nt .WS, t 0x2C, nt .WS] ++
        litSyms "\"target\"" ++ [nt .WS, t 0x3A, nt .WS, nt .StrVal, nt .WS, t 0x2C, nt .WS] ++
        litSyms "\"amount\"" ++ [nt .WS, t 0x3A, nt .WS, nt .NatVal, nt .WS, t 0x7D],
        .mkToolRest⟩,
      ⟨.CotRest,
        litSyms "ot\"" ++ [nt .WS, t 0x3A, nt .WS, nt .StrVal, nt .WS, t 0x2C, nt .WS] ++
        litSyms "\"tool\"" ++ [nt .WS, t 0x3A, nt .WS, nt .StrVal, nt .WS, t 0x2C, nt .WS] ++
        litSyms "\"target\"" ++ [nt .WS, t 0x3A, nt .WS, nt .StrVal, nt .WS, t 0x2C, nt .WS] ++
        litSyms "\"amount\"" ++ [nt .WS, t 0x3A, nt .WS, nt .NatVal, nt .WS, t 0x7D],
        .mkCotRest⟩,
      ⟨.BatchBody, [nt .TopExpr, nt .WS, nt .BatchTail], .batchCons⟩,
      ⟨.BatchBody, [], .batchEmpty⟩,
      ⟨.BatchTail, [t 0x2C, nt .WS, nt .TopExpr, nt .WS, nt .BatchTail], .batchCons⟩,
      ⟨.BatchTail, [], .batchEmpty⟩,
      ⟨.WS, [t 0x20, nt .WS], .unitOp⟩,
      ⟨.WS, [t 0x09, nt .WS], .unitOp⟩,
      ⟨.WS, [t 0x0A, nt .WS], .unitOp⟩,
      ⟨.WS, [t 0x0D, nt .WS], .unitOp⟩,
      ⟨.WS, [], .unitOp⟩,
      ⟨.StrVal, [t 0x22, nt .Chars, t 0x22], .strUnquote⟩,
      ⟨.Chars, [t 0x5C, nt .Esc, nt .Chars], .charsEsc⟩,
      ⟨.Chars, [], .charsNil⟩,
      ⟨.Esc, [t 0x22], .escConst 0x22⟩,
      ⟨.Esc, [t 0x5C], .escConst 0x5C⟩,
      ⟨.Esc, [t 0x2F], .escConst 0x2F⟩,
      ⟨.Esc, [t 0x6E], .escConst 0x0A⟩,
      ⟨.Esc, [t 0x72], .escConst 0x0D⟩,
      ⟨.Esc, [t 0x74], .escConst 0x09⟩,
      ⟨.NatVal, [t 0x30], .natZero⟩,
      ⟨.Digits, [], .digitsNil⟩ ] ++
    ((List.range 9).map fun k =>
      let d := k + 1
      ⟨.NatVal, [t (UInt8.ofNat (0x30 + d)), nt .Digits], .natPos d⟩) ++
    ((List.range 10).map fun d =>
      ⟨.Digits, [t (UInt8.ofNat (0x30 + d)), nt .Digits], .digitsCons d⟩) ++
    (safeJsonStringBytes.map fun b =>
      ⟨.Chars, [t b, nt .Chars], .charsCons b⟩)

set_option maxRecDepth 20000 in
/-- **Kernel-verified LL(1) determinacy of the byte-level JSON Tool-Call grammar (`by decide`)!** -/
theorem miniJsonCfg_is_ll1 : ll1Deterministic miniJsonCfg = true := by decide

def sampleEscapedToolJson : List UInt8 :=
  asciiBytes "  {\n  \"tool\" : \"write_audit\",\n  \"target\" : \"logs\\\\2026\\\"q4\\n\",\n  \"amount\" : 10500\n}\n"

def expectedEscapedToolAst : MiniValue :=
  .vToolCall (asciiBytes "write_audit") (asciiBytes "logs\\2026\"q4\n") 10500

def sampleEscapedToolRules : List (AttrRule UInt8 MiniNT MiniOp) :=
  match ll1Parse miniJsonCfg sampleEscapedToolJson with
  | some (rs, _) => rs
  | none => []

set_option maxRecDepth 20000 in
theorem miniJsonCfg_extracts_escaped_tool :
    AttrReplay miniJsonCfg sampleEscapedToolRules sampleEscapedToolJson expectedEscapedToolAst := by
  rw [← execAttrReplay_iff]
  decide

theorem miniJsonCfg_escaped_tool_unique
    {rs : List (AttrRule UInt8 MiniNT MiniOp)} {ast : MiniValue}
    (h : AttrReplay miniJsonCfg rs sampleEscapedToolJson ast) :
    ast = expectedEscapedToolAst ∧ rs = sampleEscapedToolRules :=
  attrReplay_unique_of_ll1 miniJsonCfg miniJsonCfg_is_ll1 h miniJsonCfg_extracts_escaped_tool

def sampleBatchToolJson : List UInt8 :=
  asciiBytes "[{\"tool\":\"ping\",\"target\":\"node_a\",\"amount\":0}, {\"tool\":\"sync\",\"target\":\"node_b\",\"amount\":42}]"

def expectedBatchToolAst : MiniValue :=
  MiniValue.ofBatchList
    [ .vToolCall (asciiBytes "ping") (asciiBytes "node_a") 0,
      .vToolCall (asciiBytes "sync") (asciiBytes "node_b") 42 ]

def sampleBatchToolRules : List (AttrRule UInt8 MiniNT MiniOp) :=
  match ll1Parse miniJsonCfg sampleBatchToolJson with
  | some (rs, _) => rs
  | none => []

set_option maxRecDepth 20000 in
theorem miniJsonCfg_extracts_batch :
    AttrReplay miniJsonCfg sampleBatchToolRules sampleBatchToolJson expectedBatchToolAst := by
  rw [← execAttrReplay_iff]
  decide

def nonCanonicalLeadingZeroJson : List UInt8 :=
  asciiBytes "{\"tool\":\"ping\",\"target\":\"node_a\",\"amount\":01}"

set_option maxRecDepth 20000 in
theorem miniJsonCfg_rejects_leading_zero :
    ll1Parse miniJsonCfg nonCanonicalLeadingZeroJson = none := by decide

/-! ### Constructive Ambiguous-Grammar Splice Attack (`ambigMiniJsonCfg`) -/

inductive AmbigNT where
  | Root
  | ToolFields
  | StrVal
  | Chars
  | NatVal
  | Digits
  deriving DecidableEq, Repr

inductive AmbigOp where
  | passAt    : Nat → AmbigOp
  | firstWins : AmbigOp
  | lastWins  : AmbigOp
  | singleKey : AmbigOp
  | strUnq    : AmbigOp
  | charsNil  : AmbigOp
  | charsCons : UInt8 → AmbigOp
  | natZero   : AmbigOp
  | natPos    : Nat → AmbigOp
  | digitsNil : AmbigOp
  | digitsCons : Nat → AmbigOp
  deriving DecidableEq, Repr

def evalAmbigOp : AmbigOp → List MiniValue → MiniValue
  | .passAt i, vs => vs.getD i .vUnit
  | .singleKey, vs =>
      match vs.getD 7 (.vBytes []), vs.getD 18 (.vBytes []), vs.getD 29 (.vNat 0) with
      | .vBytes t, .vBytes tgt, .vNat n => .vToolCall t tgt n
      | _, _, _ => .vUnit
  | .firstWins, vs =>
      match vs.getD 7 (.vBytes []), vs.getD 27 (.vBytes []), vs.getD 38 (.vNat 0) with
      | .vBytes t1, .vBytes tgt, .vNat n => .vToolCall t1 tgt n
      | _, _, _ => .vUnit
  | .lastWins, vs =>
      match vs.getD 16 (.vBytes []), vs.getD 27 (.vBytes []), vs.getD 38 (.vNat 0) with
      | .vBytes t2, .vBytes tgt, .vNat n => .vToolCall t2 tgt n
      | _, _, _ => .vUnit
  | .strUnq, vs => vs.getD 1 (.vBytes [])
  | .charsNil, _ => .vBytes []
  | .charsCons b, vs =>
      match vs.getD 1 (.vBytes []) with
      | .vBytes bs => .vBytes (b :: bs)
      | _ => .vBytes [b]
  | .natZero, _ => .vNat 0
  | .natPos d0, vs =>
      match vs.getD 1 (.vDigits []) with
      | .vDigits ds => .vNat ((d0 :: ds).foldl (fun acc d => acc * 10 + d) 0)
      | _ => .vNat d0
  | .digitsNil, _ => .vDigits []
  | .digitsCons d, vs =>
      match vs.getD 1 (.vDigits []) with
      | .vDigits ds => .vDigits (d :: ds)
      | _ => .vDigits [d]

def ambigLit (s : String) : List (Symbol UInt8 AmbigNT) :=
  (asciiBytes s).map (Symbol.terminal (N := AmbigNT))

def ambigIdentBytes : List UInt8 :=
  (List.range 26).map (fun k => UInt8.ofNat (0x61 + k)) ++
  (List.range 10).map (fun k => UInt8.ofNat (0x30 + k)) ++
  [0x5F]

def ambigFirstWinsRule : AttrRule UInt8 AmbigNT AmbigOp :=
  ⟨.ToolFields,
    ambigLit "\"tool\":" ++ [.nonterminal .StrVal] ++
    ambigLit ",\"tool\":" ++ [.nonterminal .StrVal] ++
    ambigLit ",\"target\":" ++ [.nonterminal .StrVal] ++
    ambigLit ",\"amount\":" ++ [.nonterminal .NatVal],
    .firstWins⟩

def ambigLastWinsRule : AttrRule UInt8 AmbigNT AmbigOp :=
  ⟨.ToolFields,
    ambigLit "\"tool\":" ++ [.nonterminal .StrVal] ++
    ambigLit ",\"tool\":" ++ [.nonterminal .StrVal] ++
    ambigLit ",\"target\":" ++ [.nonterminal .StrVal] ++
    ambigLit ",\"amount\":" ++ [.nonterminal .NatVal],
    .lastWins⟩

def ambigSingleKeyRule : AttrRule UInt8 AmbigNT AmbigOp :=
  ⟨.ToolFields,
    ambigLit "\"tool\":" ++ [.nonterminal .StrVal] ++
    ambigLit ",\"target\":" ++ [.nonterminal .StrVal] ++
    ambigLit ",\"amount\":" ++ [.nonterminal .NatVal],
    .singleKey⟩

def ambigMiniJsonCfg : AttrCfg UInt8 AmbigNT AmbigOp MiniValue where
  initial := .Root
  termVal := MiniValue.vByte
  evalOp  := evalAmbigOp
  rules   :=
    let t := Symbol.terminal (T := UInt8) (N := AmbigNT)
    let nt := Symbol.nonterminal (T := UInt8) (N := AmbigNT)
    [ ⟨.Root, [t 0x7B, nt .ToolFields, t 0x7D], .passAt 1⟩,
      ambigSingleKeyRule,
      ambigFirstWinsRule,
      ambigLastWinsRule,
      ⟨.StrVal, [t 0x22, nt .Chars, t 0x22], .strUnq⟩,
      ⟨.Chars, [], .charsNil⟩,
      ⟨.NatVal, [t 0x30], .natZero⟩,
      ⟨.Digits, [], .digitsNil⟩ ] ++
    ((List.range 9).map fun k =>
      let d := k + 1
      ⟨.NatVal, [t (UInt8.ofNat (0x30 + d)), nt .Digits], .natPos d⟩) ++
    ((List.range 10).map fun d =>
      ⟨.Digits, [t (UInt8.ofNat (0x30 + d)), nt .Digits], .digitsCons d⟩) ++
    (ambigIdentBytes.map fun b =>
      ⟨.Chars, [t b, nt .Chars], .charsCons b⟩)

def ambigStrRules (s : String) : List (AttrRule UInt8 AmbigNT AmbigOp) :=
  ⟨.StrVal, [.terminal 0x22, .nonterminal .Chars, .terminal 0x22], .strUnq⟩ ::
    ((asciiBytes s).map (fun b =>
      ⟨.Chars, [.terminal b, .nonterminal .Chars], .charsCons b⟩)) ++
    [⟨.Chars, [], .charsNil⟩]

def ambigSplicePayload : List UInt8 :=
  asciiBytes "{\"tool\":\"read_status\",\"tool\":\"wipe_prod\",\"target\":\"db_main\",\"amount\":1}"

def ambigBenignAst : MiniValue :=
  .vToolCall (asciiBytes "read_status") (asciiBytes "db_main") 1

def ambigDestructiveAst : MiniValue :=
  .vToolCall (asciiBytes "wipe_prod") (asciiBytes "db_main") 1

def ambigRootRule : AttrRule UInt8 AmbigNT AmbigOp :=
  ⟨.Root, [.terminal 0x7B, .nonterminal .ToolFields, .terminal 0x7D], .passAt 1⟩

def ambigNat1Rules : List (AttrRule UInt8 AmbigNT AmbigOp) :=
  [ ⟨.NatVal, [.terminal 0x31, .nonterminal .Digits], .natPos 1⟩,
    ⟨.Digits, [], .digitsNil⟩ ]

def ambigBenignCert : List (AttrRule UInt8 AmbigNT AmbigOp) :=
  [ambigRootRule, ambigFirstWinsRule] ++
  ambigStrRules "read_status" ++
  ambigStrRules "wipe_prod" ++
  ambigStrRules "db_main" ++
  ambigNat1Rules

def ambigDestructiveCert : List (AttrRule UInt8 AmbigNT AmbigOp) :=
  [ambigRootRule, ambigLastWinsRule] ++
  ambigStrRules "read_status" ++
  ambigStrRules "wipe_prod" ++
  ambigStrRules "db_main" ++
  ambigNat1Rules

set_option maxRecDepth 20000 in
/-- **Constructive Ambiguous-Grammar Splice Attack (`ambigMiniJsonCfg_splice_attack`)**. -/
theorem ambigMiniJsonCfg_splice_attack :
    ll1Deterministic ambigMiniJsonCfg = false ∧
    AttrReplay ambigMiniJsonCfg ambigBenignCert ambigSplicePayload ambigBenignAst ∧
    AttrReplay ambigMiniJsonCfg ambigDestructiveCert ambigSplicePayload ambigDestructiveAst ∧
    ambigBenignAst ≠ ambigDestructiveAst ∧
    ambigSplicePayload ∈ ambigMiniJsonCfg.toCfg.language ∧
    ll1Parse miniJsonCfg ambigSplicePayload = none := by
  have hBen : AttrReplay ambigMiniJsonCfg ambigBenignCert ambigSplicePayload ambigBenignAst := by
    rw [← execAttrReplay_iff]; decide
  have hDes : AttrReplay ambigMiniJsonCfg ambigDestructiveCert ambigSplicePayload ambigDestructiveAst := by
    rw [← execAttrReplay_iff]; decide
  exact ⟨by decide, hBen, hDes, by decide, attrReplay_mem_language hBen, by decide⟩

/-! ## §4. Verified Deterministic Secret-Redaction Byte Transducer (`RedactionTransducer`) -/

section RedactionTransducer

def SubstringAtW {Sym : Type} (w : List Sym) (i : Nat) (P : List Sym) : Prop :=
  i + P.length ≤ w.length ∧ (w.drop i).take P.length = P

instance instDecidableSubstringAtW {Sym : Type} [DecidableEq Sym]
    (w : List Sym) (i : Nat) (P : List Sym) : Decidable (SubstringAtW w i P) := by
  unfold SubstringAtW; infer_instance

def OccursInW {Sym : Type} (w P : List Sym) : Prop :=
  ∃ i : Nat, SubstringAtW w i P

def AbsentW {Sym : Type} (w P : List Sym) : Prop :=
  ∀ i : Nat, ¬ SubstringAtW w i P

def occursInBool {Sym : Type} [DecidableEq Sym] (w P : List Sym) : Bool :=
  (List.range (w.length + 1)).any (fun i => decide (SubstringAtW w i P))

def absentBool {Sym : Type} [DecidableEq Sym] (w P : List Sym) : Bool :=
  !occursInBool w P

theorem occursInBool_iff {Sym : Type} [DecidableEq Sym] (w P : List Sym) :
    occursInBool w P = true ↔ OccursInW w P := by
  simp only [occursInBool, List.any_eq_true, List.mem_range, decide_eq_true_eq, OccursInW]
  constructor
  · rintro ⟨i, _, hsub⟩; exact ⟨i, hsub⟩
  · rintro ⟨i, hlen, htake⟩; exact ⟨i, by omega, hlen, htake⟩

theorem absentBool_iff {Sym : Type} [DecidableEq Sym] (w P : List Sym) :
    absentBool w P = true ↔ AbsentW w P := by
  simp only [absentBool, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, occursInBool_iff]
  unfold OccursInW AbsentW
  push Not
  rfl

instance instDecidableOccursInW {Sym : Type} [DecidableEq Sym] (w P : List Sym) :
    Decidable (OccursInW w P) :=
  decidable_of_iff (occursInBool w P = true) (occursInBool_iff w P)

instance instDecidableAbsentW {Sym : Type} [DecidableEq Sym] (w P : List Sym) :
    Decidable (AbsentW w P) :=
  decidable_of_iff (absentBool w P = true) (absentBool_iff w P)

/-- **Decidable No-Boundary-Recreation Predicate (`SafeReplacement P repl`)**. -/
def SafeReplacement {Sym : Type} [DecidableEq Sym] (P repl : List Sym) : Bool :=
  !repl.isEmpty &&
  absentBool repl P &&
  (List.range P.length).all (fun k =>
    if 0 < k then
      let p₁ := P.take k
      let p₂ := P.drop k
      !List.isPrefixOf p₂ repl && !List.isPrefixOf repl p₂ && !List.isSuffixOf p₁ repl
    else true)

private theorem list_isPrefixOf_iff_take {Sym : Type} [DecidableEq Sym] (xs ys : List Sym) :
    List.isPrefixOf xs ys = true ↔ xs.length ≤ ys.length ∧ ys.take xs.length = xs := by
  rw [List.isPrefixOf_iff_prefix]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨by simp, List.take_left⟩
  · rintro ⟨_, htake⟩
    refine ⟨ys.drop xs.length, ?_⟩
    conv_rhs => rw [← List.take_append_drop xs.length ys]
    rw [htake]

private theorem list_isSuffixOf_iff_drop {Sym : Type} [DecidableEq Sym] (xs ys : List Sym) :
    List.isSuffixOf xs ys = true ↔ xs.length ≤ ys.length ∧ ys.drop (ys.length - xs.length) = xs := by
  rw [List.isSuffixOf_iff_suffix]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨by simp, ?_⟩
    have hsub : (s ++ xs).length - xs.length = s.length := by simp
    rw [hsub, List.drop_left]
  · rintro ⟨_, hdrop⟩
    refine ⟨ys.take (ys.length - xs.length), ?_⟩
    conv_rhs => rw [← List.take_append_drop (ys.length - xs.length) ys]
    rw [hdrop]

/-- **Splitting Lemma (`absentW_append_repl`)**. -/
theorem absentW_append_repl {Sym : Type} [DecidableEq Sym]
    {P repl u v : List Sym}
    (hsafe : SafeReplacement P repl = true)
    (hu : AbsentW u P) (hv : AbsentW v P) :
    AbsentW (u ++ repl ++ v) P := by
  unfold SafeReplacement at hsafe
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, absentBool_iff,
    List.all_eq_true, List.mem_range] at hsafe
  rcases hsafe with ⟨⟨hreplNe, hreplAbs⟩, hsplits⟩
  have _ : 0 < P.length := by
    by_contra h0
    have hpNil : P = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hpNil
    exact hu 0 ⟨by simp, by simp⟩
  have _ : 0 < repl.length := List.length_pos_of_ne_nil hreplNe
  intro i ⟨hlen, htake⟩
  rw [List.append_assoc] at hlen htake
  by_cases hiu : i + P.length ≤ u.length
  · have hd : (u ++ (repl ++ v)).drop i = u.drop i ++ (repl ++ v) :=
      List.drop_append_of_le_length (by omega)
    have ht : (u.drop i ++ (repl ++ v)).take P.length = (u.drop i).take P.length :=
      List.take_append_of_le_length (by simp [List.length_drop]; omega)
    rw [hd, ht] at htake
    exact hu i ⟨hiu, htake⟩
  · by_cases hur : u.length + repl.length ≤ i
    · let i' := i - (u.length + repl.length)
      have hd1 : (u ++ (repl ++ v)).drop i = (repl ++ v).drop (i - u.length) := by
        rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
      have hd2 : (repl ++ v).drop (i - u.length) = v.drop i' := by
        rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append]
        congr 1; omega
      rw [hd1, hd2] at htake
      have hvlen : i' + P.length ≤ v.length := by
        simp only [List.length_append] at hlen; omega
      exact hv i' ⟨hvlen, htake⟩
    · by_cases hilt : i < u.length
      · let k := u.length - i
        have hk0 : 0 < k := by omega
        have hkP : k < P.length := by omega
        have hsp := hsplits k hkP
        simp only [hk0, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hsp
        rcases hsp with ⟨⟨hnoPref1, hnoPref2⟩, _⟩
        have hd : (u ++ (repl ++ v)).drop i = u.drop i ++ (repl ++ v) :=
          List.drop_append_of_le_length (by omega)
        have hlenDropU : (u.drop i).length = k := by simp [k]
        have htSplit : (u.drop i ++ (repl ++ v)).take P.length =
            u.drop i ++ (repl ++ v).take (P.length - k) := by
          rw [List.take_append, List.take_of_length_le (by omega), hlenDropU]
        have hcomb : u.drop i ++ (repl ++ v).take (P.length - k) = P.take k ++ P.drop k := by
          calc u.drop i ++ (repl ++ v).take (P.length - k)
              = ((u ++ (repl ++ v)).drop i).take P.length := by rw [hd, htSplit]
            _ = P := htake
            _ = P.take k ++ P.drop k := (List.take_append_drop k P).symm
        have hlenEq : (u.drop i).length = (P.take k).length := by
          rw [hlenDropU, List.length_take_of_le (by omega)]
        obtain ⟨_, hp2Eq⟩ := List.append_inj hcomb hlenEq
        by_cases hcmp : P.length - k ≤ repl.length
        · have hpref : List.isPrefixOf (P.drop k) repl = true := by
            rw [list_isPrefixOf_iff_take]
            have hplen : (P.drop k).length = P.length - k := List.length_drop
            refine ⟨by omega, ?_⟩
            rw [hplen, ← List.take_append_of_le_length (l₂ := v) hcmp]
            exact hp2Eq
          exact absurd hpref (by simp [hnoPref1])
        · have hpref : List.isPrefixOf repl (P.drop k) = true := by
            rw [list_isPrefixOf_iff_take]
            have hplen : (P.drop k).length = P.length - k := List.length_drop
            refine ⟨by omega, ?_⟩
            rw [← hp2Eq, List.take_take, Nat.min_eq_left (by omega),
              List.take_append_of_le_length (le_refl _), List.take_length]
          exact absurd hpref (by simp [hnoPref2])
      · let j := i - u.length
        have _ : j < repl.length := by omega
        have hd1 : (u ++ (repl ++ v)).drop i = repl.drop j ++ v := by
          rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
            List.drop_append_of_le_length (by omega)]
        rw [hd1] at htake
        by_cases hjr : j + P.length ≤ repl.length
        · have ht : (repl.drop j ++ v).take P.length = (repl.drop j).take P.length :=
            List.take_append_of_le_length (by simp [List.length_drop]; omega)
          rw [ht] at htake
          exact hreplAbs j ⟨hjr, htake⟩
        · let k := repl.length - j
          have hk0 : 0 < k := by omega
          have hkP : k < P.length := by omega
          have hsp := hsplits k hkP
          simp only [hk0, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hsp
          have hnoSuf := hsp.2
          have hlenDropR : (repl.drop j).length = k := by simp [k]
          have htSplit : (repl.drop j ++ v).take P.length =
              repl.drop j ++ v.take (P.length - k) := by
            rw [List.take_append, List.take_of_length_le (by omega), hlenDropR]
          have hcomb : repl.drop j ++ v.take (P.length - k) = P.take k ++ P.drop k := by
            calc repl.drop j ++ v.take (P.length - k)
                = (repl.drop j ++ v).take P.length := htSplit.symm
              _ = P := htake
              _ = P.take k ++ P.drop k := (List.take_append_drop k P).symm
          have hlenEq : (repl.drop j).length = (P.take k).length := by
            rw [hlenDropR, List.length_take_of_le (by omega)]
          obtain ⟨hp1Eq, _⟩ := List.append_inj hcomb hlenEq
          have hsuf : List.isSuffixOf (P.take k) repl = true := by
            rw [list_isSuffixOf_iff_drop]
            have htkLen : (P.take k).length = k := List.length_take_of_le (by omega)
            refine ⟨by omega, ?_⟩
            rw [htkLen]
            have hsub : repl.length - k = j := by omega
            rw [hsub, hp1Eq]
          exact absurd hsuf (by simp [hnoSuf])

/-- **A Secret-Redaction Rule (`RedactRule Sym`)**. -/
structure RedactRule (Sym : Type) where
  name     : String
  pat      : List Sym
  bodyPred : Sym → Bool
  repl     : List Sym

def ruleMatchLen {Sym : Type} [DecidableEq Sym] (r : RedactRule Sym) (w : List Sym) : Option Nat :=
  if !r.pat.isEmpty && List.isPrefixOf r.pat w then
    some (r.pat.length + ((w.drop r.pat.length).takeWhile r.bodyPred).length)
  else
    none

theorem ruleMatchLen_pos {Sym : Type} [DecidableEq Sym] {r : RedactRule Sym} {w : List Sym}
    {len : Nat} (h : ruleMatchLen r w = some len) : 1 ≤ len := by
  unfold ruleMatchLen at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hcond
    have hp : 0 < r.pat.length := List.length_pos_of_ne_nil hcond.1
    injection h with hlen
    omega
  · simp at h

def pickLongestMatchAux {Sym : Type} [DecidableEq Sym]
    (w : List Sym) : List (RedactRule Sym) → Option (List Sym × Nat) → Option (List Sym × Nat)
  | [], acc => acc
  | r :: rs, acc =>
      match ruleMatchLen r w with
      | none => pickLongestMatchAux w rs acc
      | some len =>
          let nextAcc := match acc with
            | none => some (r.repl, len)
            | some (bestRepl, bestLen) =>
                if bestLen < len then some (r.repl, len) else some (bestRepl, bestLen)
          pickLongestMatchAux w rs nextAcc

def pickLongestMatch {Sym : Type} [DecidableEq Sym]
    (rules : List (RedactRule Sym)) (w : List Sym) : Option (List Sym × Nat) :=
  pickLongestMatchAux w rules none

private theorem pickLongestMatchAux_inv {Sym : Type} [DecidableEq Sym]
    (allRules : List (RedactRule Sym)) (w : List Sym) :
    ∀ (rs : List (RedactRule Sym)) (acc : Option (List Sym × Nat)),
      (∀ r ∈ rs, r ∈ allRules) →
      (∀ repl len, acc = some (repl, len) → 1 ≤ len ∧ ∃ r ∈ allRules, r.repl = repl) →
      ∀ repl len, pickLongestMatchAux w rs acc = some (repl, len) →
        1 ≤ len ∧ ∃ r ∈ allRules, r.repl = repl := by
  intro rs
  induction rs with
  | nil =>
      intro acc _ hacc repl len h
      exact hacc repl len h
  | cons r rs ih =>
      intro acc hsub hacc repl len h
      simp only [pickLongestMatchAux] at h
      have hrMem : r ∈ allRules := hsub r (List.mem_cons_self ..)
      have hrsSub : ∀ x ∈ rs, x ∈ allRules := fun x hx => hsub x (List.mem_cons_of_mem _ hx)
      cases hm : ruleMatchLen r w with
      | none =>
          rw [hm] at h
          exact ih acc hrsSub hacc repl len h
      | some mlen =>
          rw [hm] at h
          have hpos : 1 ≤ mlen := ruleMatchLen_pos hm
          refine ih _ hrsSub (fun rp ln hnext => ?_) repl len h
          cases haccEq : acc with
          | none =>
              rw [haccEq] at hnext
              injection hnext with hpair
              injection hpair with hrp hln
              exact ⟨hln ▸ hpos, r, hrMem, hrp⟩
          | some best =>
              rw [haccEq] at hnext
              rcases best with ⟨bestRepl, bestLen⟩
              simp only at hnext
              split at hnext
              · injection hnext with hpair
                injection hpair with hrp hln
                exact ⟨hln ▸ hpos, r, hrMem, hrp⟩
              · exact hacc rp ln (haccEq.trans hnext)

theorem pickLongestMatch_pos_and_mem {Sym : Type} [DecidableEq Sym]
    {rules : List (RedactRule Sym)} {w : List Sym} {repl : List Sym} {len : Nat}
    (h : pickLongestMatch rules w = some (repl, len)) :
    1 ≤ len ∧ ∃ r ∈ rules, r.repl = repl :=
  pickLongestMatchAux_inv rules w rules none (fun _ hx => hx) (by simp) repl len h

private theorem pickLongestMatchAux_ne_none_of_acc {Sym : Type} [DecidableEq Sym]
    (w : List Sym) :
    ∀ (rs : List (RedactRule Sym)) (p : List Sym × Nat),
      pickLongestMatchAux w rs (some p) ≠ none := by
  intro rs
  induction rs with
  | nil => intro p; simp [pickLongestMatchAux]
  | cons r rs ih =>
      intro ⟨rp, ln⟩
      simp only [pickLongestMatchAux]
      cases ruleMatchLen r w with
      | none => exact ih (rp, ln)
      | some mlen =>
          by_cases hlt : ln < mlen
          · simpa [hlt] using ih (r.repl, mlen)
          · simpa [hlt] using ih (rp, ln)

private theorem pickLongestMatchAux_ne_none_of_mem {Sym : Type} [DecidableEq Sym]
    (w : List Sym) {rt : RedactRule Sym} {mlen : Nat}
    (hm : ruleMatchLen rt w = some mlen) :
    ∀ (rs : List (RedactRule Sym)) (acc : Option (List Sym × Nat)),
      rt ∈ rs → pickLongestMatchAux w rs acc ≠ none := by
  intro rs
  induction rs with
  | nil => intro _ hmem; cases hmem
  | cons r rs ih =>
      intro acc hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp only [pickLongestMatchAux, hm]
        cases acc with
        | none => exact pickLongestMatchAux_ne_none_of_acc w rs (rt.repl, mlen)
        | some best =>
            rcases best with ⟨br, bl⟩
            by_cases hlt : bl < mlen
            · simpa [hlt] using pickLongestMatchAux_ne_none_of_acc w rs (rt.repl, mlen)
            · simpa [hlt] using pickLongestMatchAux_ne_none_of_acc w rs (br, bl)
      · simp only [pickLongestMatchAux]
        cases ruleMatchLen r w with
        | none => exact ih acc htail
        | some _ => exact ih _ htail

theorem pickLongestMatch_ne_none_of_prefix {Sym : Type} [DecidableEq Sym]
    {rules : List (RedactRule Sym)} {rt : RedactRule Sym} {w : List Sym}
    (hrt : rt ∈ rules) (hne : rt.pat ≠ []) (hpref : List.isPrefixOf rt.pat w = true) :
    pickLongestMatch rules w ≠ none := by
  have hm : ruleMatchLen rt w =
      some (rt.pat.length + ((w.drop rt.pat.length).takeWhile rt.bodyPred).length) := by
    unfold ruleMatchLen
    have hneB : (!rt.pat.isEmpty && List.isPrefixOf rt.pat w) = true := by
      simp [hne, hpref]
    simp [hneB]
  exact pickLongestMatchAux_ne_none_of_mem w hm rules none hrt

def redactBytesFuel {Sym : Type} [DecidableEq Sym] (rules : List (RedactRule Sym)) :
    Nat → List Sym → List Sym
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, b :: ws =>
      match pickLongestMatch rules (b :: ws) with
      | some (repl, len) => repl ++ redactBytesFuel rules fuel ((b :: ws).drop len)
      | none => b :: redactBytesFuel rules fuel ws

private theorem redactBytesFuel_eq_of_le {Sym : Type} [DecidableEq Sym]
    (rules : List (RedactRule Sym)) :
    ∀ (f₁ f₂ : Nat) (w : List Sym), w.length ≤ f₁ → w.length ≤ f₂ →
      redactBytesFuel rules f₁ w = redactBytesFuel rules f₂ w := by
  intro f₁
  induction f₁ with
  | zero =>
      intro f₂ w h₁ _
      have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hw
      cases f₂ <;> rfl
  | succ f₁ ih =>
      intro f₂ w h₁ h₂
      cases w with
      | nil =>
          cases f₂ <;> rfl
      | cons b ws =>
          cases f₂ with
          | zero => simp at h₂
          | succ f₂' =>
              simp only [redactBytesFuel]
              cases hm : pickLongestMatch rules (b :: ws) with
              | none =>
                  simp only [List.length_cons] at h₁ h₂
                  exact congrArg (List.cons b) (ih f₂' ws (by omega) (by omega))
              | some pair =>
                  rcases pair with ⟨repl, len⟩
                  have _ : 1 ≤ len := (pickLongestMatch_pos_and_mem hm).1
                  simp only [List.length_cons] at h₁ h₂
                  exact congrArg (repl ++ ·)
                    (ih f₂' ((b :: ws).drop len)
                      (by simp [List.length_drop]; omega)
                      (by simp [List.length_drop]; omega))

/-- **Executable Deterministic Byte-Stream Sanitizer (`redactBytes`)**. -/
def redactBytes {Sym : Type} [DecidableEq Sym] (rules : List (RedactRule Sym)) (w : List Sym) : List Sym :=
  redactBytesFuel rules w.length w

@[simp] theorem redactBytes_nil {Sym : Type} [DecidableEq Sym] (rules : List (RedactRule Sym)) :
    redactBytes rules [] = [] := rfl

theorem redactBytes_cons_match {Sym : Type} [DecidableEq Sym]
    {rules : List (RedactRule Sym)} {b : Sym} {ws repl : List Sym} {len : Nat}
    (hm : pickLongestMatch rules (b :: ws) = some (repl, len)) :
    redactBytes rules (b :: ws) = repl ++ redactBytes rules ((b :: ws).drop len) := by
  have _ : 1 ≤ len := (pickLongestMatch_pos_and_mem hm).1
  unfold redactBytes
  simp only [List.length_cons, redactBytesFuel, hm]
  congr 1
  exact redactBytesFuel_eq_of_le rules ws.length (((b :: ws).drop len).length) _
    (by simp [List.length_drop]; omega) (le_refl _)

theorem redactBytes_cons_none {Sym : Type} [DecidableEq Sym]
    {rules : List (RedactRule Sym)} {b : Sym} {ws : List Sym}
    (hm : pickLongestMatch rules (b :: ws) = none) :
    redactBytes rules (b :: ws) = b :: redactBytes rules ws := by
  unfold redactBytes
  simp [List.length_cons, redactBytesFuel, hm]

/-- Inductive relational specification `RedactsTo rules w wOut` of the byte-stream transducer. -/
inductive RedactsTo {Sym : Type} [DecidableEq Sym] (rules : List (RedactRule Sym)) :
    List Sym → List Sym → Prop
  | nil : RedactsTo rules [] []
  | matchStep {b : Sym} {ws outRest repl : List Sym} {len : Nat}
      (hm : pickLongestMatch rules (b :: ws) = some (repl, len))
      (hrest : RedactsTo rules ((b :: ws).drop len) outRest) :
      RedactsTo rules (b :: ws) (repl ++ outRest)
  | passStep {b : Sym} {ws outRest : List Sym}
      (hm : pickLongestMatch rules (b :: ws) = none)
      (hrest : RedactsTo rules ws outRest) :
      RedactsTo rules (b :: ws) (b :: outRest)

private theorem redactsTo_redactBytes_len {Sym : Type} [DecidableEq Sym]
    (rules : List (RedactRule Sym)) :
    ∀ (n : Nat) (w : List Sym), w.length ≤ n → RedactsTo rules w (redactBytes rules w) := by
  intro n
  induction n with
  | zero =>
      intro w hw
      have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      exact .nil
  | succ n ih =>
      intro w hw
      cases w with
      | nil => exact .nil
      | cons b ws =>
          simp only [List.length_cons] at hw
          cases hm : pickLongestMatch rules (b :: ws) with
          | none =>
              rw [redactBytes_cons_none hm]
              exact .passStep hm (ih ws (by omega))
          | some pair =>
              rcases pair with ⟨repl, len⟩
              have _ : 1 ≤ len := (pickLongestMatch_pos_and_mem hm).1
              rw [redactBytes_cons_match hm]
              exact .matchStep hm (ih ((b :: ws).drop len) (by simp [List.length_drop]; omega))

theorem redactsTo_redactBytes {Sym : Type} [DecidableEq Sym]
    (rules : List (RedactRule Sym)) (w : List Sym) :
    RedactsTo rules w (redactBytes rules w) :=
  redactsTo_redactBytes_len rules w.length w (le_refl _)

/-- **`redactBytes_deterministic`** — Relational Determinacy of the Redaction Transducer. -/
theorem redactBytes_deterministic {Sym : Type} [DecidableEq Sym]
    {rules : List (RedactRule Sym)} {w out₁ out₂ : List Sym}
    (h₁ : RedactsTo rules w out₁) (h₂ : RedactsTo rules w out₂) :
    out₁ = out₂ := by
  induction h₁ generalizing out₂ with
  | nil =>
      cases h₂
      rfl
  | matchStep hm₁ _ ih =>
      cases h₂ with
      | matchStep hm₂ hrest₂ =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hm₁.symm.trans hm₂))
          exact congrArg _ (ih hrest₂)
      | passStep hm₂ _ =>
          rw [hm₁] at hm₂; simp at hm₂
  | passStep hm₁ _ ih =>
      cases h₂ with
      | matchStep hm₂ _ =>
          rw [hm₁] at hm₂; simp at hm₂
      | passStep _ hrest₂ =>
          exact congrArg _ (ih hrest₂)

theorem redactsTo_iff_redactBytes {Sym : Type} [DecidableEq Sym]
    (rules : List (RedactRule Sym)) (w out : List Sym) :
    RedactsTo rules w out ↔ out = redactBytes rules w :=
  ⟨fun h => redactBytes_deterministic h (redactsTo_redactBytes rules w),
   fun h => h ▸ redactsTo_redactBytes rules w⟩

private theorem absentW_unmatched_prefix {Sym : Type} [DecidableEq Sym]
    {rules : List (RedactRule Sym)} {rt : RedactRule Sym}
    (hrt : rt ∈ rules) (hne : rt.pat ≠ [])
    {u w : List Sym}
    (hnone : ∀ j < u.length, pickLongestMatch rules ((u ++ w).drop j) = none) :
    AbsentW u rt.pat := by
  have _ : 0 < rt.pat.length := List.length_pos_of_ne_nil hne
  intro j ⟨hjlen, htake⟩
  have hjlt : j < u.length := by omega
  have hpref : List.isPrefixOf rt.pat ((u ++ w).drop j) = true := by
    rw [list_isPrefixOf_iff_take]
    have hd : (u ++ w).drop j = u.drop j ++ w := List.drop_append_of_le_length (by omega)
    rw [hd]
    refine ⟨by simp [List.length_drop]; omega, ?_⟩
    rw [List.take_append_of_le_length (by simp [List.length_drop]; omega)]
    exact htake
  exact pickLongestMatch_ne_none_of_prefix hrt hne hpref (hnone j hjlt)

private theorem redactBytes_acc_scrubs {Sym : Type} [DecidableEq Sym]
    {rules : List (RedactRule Sym)} {rt : RedactRule Sym}
    (hrt : rt ∈ rules) (hne : rt.pat ≠ [])
    (hsafe : ∀ r ∈ rules, SafeReplacement rt.pat r.repl = true) :
    ∀ (n : Nat) (w u : List Sym), w.length ≤ n →
      (∀ j < u.length, pickLongestMatch rules ((u ++ w).drop j) = none) →
      AbsentW (u ++ redactBytes rules w) rt.pat := by
  intro n
  induction n with
  | zero =>
      intro w u hw hnone
      have hnil : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      rw [redactBytes_nil, List.append_nil]
      exact absentW_unmatched_prefix (w := []) hrt hne hnone
  | succ n ih =>
      intro w u hw hnone
      cases w with
      | nil =>
          rw [redactBytes_nil, List.append_nil]
          exact absentW_unmatched_prefix (w := []) hrt hne hnone
      | cons b ws =>
          simp only [List.length_cons] at hw
          cases hm : pickLongestMatch rules (b :: ws) with
          | none =>
              rw [redactBytes_cons_none hm]
              have hassoc : u ++ b :: redactBytes rules ws = (u ++ [b]) ++ redactBytes rules ws := by
                simp
              rw [hassoc]
              refine ih ws (u ++ [b]) (by omega) (fun j hj => ?_)
              have haw : (u ++ [b]) ++ ws = u ++ (b :: ws) := by simp
              rw [haw]
              simp only [List.length_append, List.length_singleton] at hj
              by_cases hjlt : j < u.length
              · exact hnone j hjlt
              · have hjeq : j = u.length := by omega
                subst hjeq
                simpa [List.drop_left] using hm
          | some pair =>
              rcases pair with ⟨repl, len⟩
              have _ : 1 ≤ len := (pickLongestMatch_pos_and_mem hm).1
              rw [redactBytes_cons_match hm, ← List.append_assoc]
              have huAbs : AbsentW u rt.pat := absentW_unmatched_prefix hrt hne hnone
              have hvAbs : AbsentW (redactBytes rules ((b :: ws).drop len)) rt.pat := by
                simpa using ih ((b :: ws).drop len) []
                  (by simp [List.length_drop]; omega)
                  (fun j hj => absurd hj (Nat.not_lt_zero j))
              obtain ⟨_, r, hrMem, rfl⟩ := pickLongestMatch_pos_and_mem hm
              exact absentW_append_repl (hsafe r hrMem) huAbs hvAbs

/-- **`redactBytes_scrubs_all`** — Universal Multi-Pattern Secret Scrubbing Theorem. -/
theorem redactBytes_scrubs_all {Sym : Type} [DecidableEq Sym]
    (rules : List (RedactRule Sym)) (rt : RedactRule Sym)
    (hrt : rt ∈ rules) (hne : rt.pat ≠ [])
    (hsafe : ∀ r ∈ rules, SafeReplacement rt.pat r.repl = true)
    (w : List Sym) :
    AbsentW (redactBytes rules w) rt.pat := by
  simpa using redactBytes_acc_scrubs hrt hne hsafe w.length w [] (le_refl _)
    (fun j hj => absurd hj (Nat.not_lt_zero j))

/-- **`redactBytes_preserves_clean`** — Zero Mangling of Clean Transcripts / Code / Prose. -/
theorem redactBytes_preserves_clean {Sym : Type} [DecidableEq Sym]
    (rules : List (RedactRule Sym)) (w : List Sym)
    (hclean : ∀ r ∈ rules, AbsentW w r.pat) :
    redactBytes rules w = w := by
  induction w with
  | nil => rfl
  | cons b ws ih =>
      have hnoMatch : pickLongestMatch rules (b :: ws) = none := by
        cases hm : pickLongestMatch rules (b :: ws) with
        | none => rfl
        | some _ =>
            exfalso
            have hex : ∃ r ∈ rules, ∃ len, ruleMatchLen r (b :: ws) = some len := by
              by_contra hall
              push Not at hall
              have hauxNone : ∀ rs, (∀ r ∈ rs, ∀ len, ruleMatchLen r (b :: ws) ≠ some len) →
                  pickLongestMatchAux (b :: ws) rs none = none := by
                intro rs hrs
                induction rs with
                | nil => rfl
                | cons r rs' ihrs =>
                    simp only [pickLongestMatchAux]
                    cases hrm : ruleMatchLen r (b :: ws) with
                    | none =>
                        exact ihrs (fun x hx l => hrs x (List.mem_cons_of_mem _ hx) l)
                    | some l =>
                        exact absurd hrm (hrs r (List.mem_cons_self ..) l)
              have h0 := hauxNone rules hall
              unfold pickLongestMatch at hm
              rw [h0] at hm
              simp at hm
            rcases hex with ⟨r, hrMem, _, hrm⟩
            unfold ruleMatchLen at hrm
            split at hrm
            · rename_i hcond
              simp only [Bool.and_eq_true] at hcond
              obtain ⟨hlen, htake⟩ := (list_isPrefixOf_iff_take r.pat (b :: ws)).mp hcond.2
              exact hclean r hrMem 0 ⟨by simpa using hlen, by simpa using htake⟩
            · simp at hrm
      have hcleanTail : ∀ r ∈ rules, AbsentW ws r.pat := by
        intro r hr i ⟨hlen, htake⟩
        exact hclean r hr (i + 1) ⟨by simp; omega, by simpa using htake⟩
      rw [redactBytes_cons_none hnoMatch]
      exact congrArg (List.cons b) (ih hcleanTail)

def allRulesSafe {Sym : Type} [DecidableEq Sym] (rules : List (RedactRule Sym)) : Bool :=
  rules.all (fun rt =>
    !rt.pat.isEmpty && rules.all (fun r => SafeReplacement rt.pat r.repl))

theorem allRulesSafe_unpack {Sym : Type} [DecidableEq Sym] {rules : List (RedactRule Sym)}
    (h : allRulesSafe rules = true) :
    ∀ rt ∈ rules, rt.pat ≠ [] ∧ ∀ r ∈ rules, SafeReplacement rt.pat r.repl = true := by
  unfold allRulesSafe at h
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  exact h

/-- **`redactBytes_idempotent`** — Strict Sanitizer Idempotence. -/
theorem redactBytes_idempotent {Sym : Type} [DecidableEq Sym]
    (rules : List (RedactRule Sym)) (hsafe : allRulesSafe rules = true) (w : List Sym) :
    redactBytes rules (redactBytes rules w) = redactBytes rules w := by
  have hunpack := allRulesSafe_unpack hsafe
  exact redactBytes_preserves_clean rules (redactBytes rules w) fun rt hrt =>
    redactBytes_scrubs_all rules rt hrt (hunpack rt hrt).1 (hunpack rt hrt).2 w

/-! ### Production Multi-Pattern Secret Classes & Boundary-Recreation Falsifier Tooth -/

def isApiKeyBodyByte (b : UInt8) : Bool :=
  (0x41 ≤ b && b ≤ 0x5A) || (0x61 ≤ b && b ≤ 0x7A) || (0x30 ≤ b && b ≤ 0x39) ||
  b == 0x5F || b == 0x2D

def isBearerBodyByte (b : UInt8) : Bool :=
  isApiKeyBodyByte b || b == 0x2E || b == 0x7E || b == 0x2B || b == 0x2F || b == 0x3D

def isPemHeaderByte (b : UInt8) : Bool :=
  (0x41 ≤ b && b ≤ 0x5A) || (0x30 ≤ b && b ≤ 0x39) || b == 0x20 || b == 0x2D

def noContinuation (_ : UInt8) : Bool := false

/-- Production 5-class secret-redaction policy (`sk-`, `Bearer `, `-----BEGIN `, `{{`, `ghp_`). -/
def defaultSecretRules : List (RedactRule UInt8) :=
  [ ⟨"api_key", asciiBytes "sk-", isApiKeyBodyByte, asciiBytes "[REDACTED_API_KEY]"⟩,
    ⟨"bearer", asciiBytes "Bearer ", isBearerBodyByte, asciiBytes "[REDACTED_BEARER]"⟩,
    ⟨"pem_key", asciiBytes "-----BEGIN ", isPemHeaderByte, asciiBytes "[REDACTED_PEM]"⟩,
    ⟨"template_open", asciiBytes "{{", noContinuation, asciiBytes "[REDACTED_TPL]"⟩,
    ⟨"github_pat", asciiBytes "ghp_", isApiKeyBodyByte, asciiBytes "[REDACTED_GH_PAT]"⟩ ]

set_option maxRecDepth 20000 in
theorem defaultSecretRules_allSafe : allRulesSafe defaultSecretRules = true := by decide

def sampleDirtyAgentBytes : List UInt8 :=
  asciiBytes "CoT: key=sk-sk-secret_99, auth=Bearer eyJhbGci.payload, tpl={{user}}, pem=-----BEGIN RSA PRIVATE KEY-----!"

def expectedRedactedAgentBytes : List UInt8 :=
  asciiBytes "CoT: key=[REDACTED_API_KEY], auth=[REDACTED_BEARER], tpl=[REDACTED_TPL]user}}, pem=[REDACTED_PEM]!"

set_option maxRecDepth 20000 in
theorem defaultSecretRules_redacts_dirty_sample :
    redactBytes defaultSecretRules sampleDirtyAgentBytes = expectedRedactedAgentBytes ∧
    (∀ r ∈ defaultSecretRules, AbsentW (redactBytes defaultSecretRules sampleDirtyAgentBytes) r.pat) := by
  refine ⟨by decide, fun r hr => ?_⟩
  have hunpack := allRulesSafe_unpack defaultSecretRules_allSafe r hr
  exact redactBytes_scrubs_all defaultSecretRules r hr hunpack.1 hunpack.2 sampleDirtyAgentBytes

def sampleCleanCodeBytes : List UInt8 :=
  asciiBytes "fn check_desk(task: usize) -> usize { if task > 0 { task - 1 } else { 0 } }"

set_option maxRecDepth 20000 in
theorem defaultSecretRules_preserves_clean_code :
    redactBytes defaultSecretRules sampleCleanCodeBytes = sampleCleanCodeBytes := by decide

def unsafeDeleteABRule : RedactRule UInt8 :=
  ⟨"unsafe_del_ab", asciiBytes "ab", noContinuation, []⟩

theorem redactBytes_unsafe_repl_falsifier :
    SafeReplacement unsafeDeleteABRule.pat unsafeDeleteABRule.repl = false ∧
    redactBytes [unsafeDeleteABRule] (asciiBytes "aabb") = asciiBytes "ab" ∧
    OccursInW (redactBytes [unsafeDeleteABRule] (asciiBytes "aabb")) unsafeDeleteABRule.pat ∧
    ¬ AbsentW (redactBytes [unsafeDeleteABRule] (asciiBytes "aabb")) unsafeDeleteABRule.pat := by
  decide

end RedactionTransducer

/-! ## §5. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Theory.VerifiedAstTransducer.attrReplay_mem_language' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attrReplay_mem_language
/-- info: 'Minidregg.Theory.VerifiedAstTransducer.execAttrReplay_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms execAttrReplay_iff
/-- info: 'Minidregg.Theory.VerifiedAstTransducer.attrReplay_unique_of_ll1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms attrReplay_unique_of_ll1
/-- info: 'Minidregg.Theory.VerifiedAstTransducer.miniJsonCfg_is_ll1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms miniJsonCfg_is_ll1
/-- info: 'Minidregg.Theory.VerifiedAstTransducer.miniJsonCfg_escaped_tool_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms miniJsonCfg_escaped_tool_unique
/-- info: 'Minidregg.Theory.VerifiedAstTransducer.ambigMiniJsonCfg_splice_attack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ambigMiniJsonCfg_splice_attack
/-- info: 'Minidregg.Theory.VerifiedAstTransducer.absentW_append_repl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absentW_append_repl
/-- info: 'Minidregg.Theory.VerifiedAstTransducer.redactBytes_deterministic' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms redactBytes_deterministic
/-- info: 'Minidregg.Theory.VerifiedAstTransducer.redactBytes_scrubs_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms redactBytes_scrubs_all
/-- info: 'Minidregg.Theory.VerifiedAstTransducer.redactBytes_preserves_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms redactBytes_preserves_clean
/-- info: 'Minidregg.Theory.VerifiedAstTransducer.redactBytes_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms redactBytes_idempotent
/-- info: 'Minidregg.Theory.VerifiedAstTransducer.redactBytes_unsafe_repl_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms redactBytes_unsafe_repl_falsifier

end Minidregg.Theory.VerifiedAstTransducer
