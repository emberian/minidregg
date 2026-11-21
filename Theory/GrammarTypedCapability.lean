/-
# `Theory/GrammarTypedCapability.lean` — Grammar-Typed Capabilities & Decidable Sublanguage Attenuation

Upgrades capability scope narrowing (`Theory/CredentialAuthorityFamily.lean`) and unambiguous
LL(1) AST + byte-redaction transducers (`Theory/VerifiedAstTransducer.lean`) into a full
**Syntactic & Automata-Predicated Capability Algebra (`GrammarPolicy`)** with executable,
kernel-reducible, sound-and-complete **Decidable Sublanguage Attenuation**:

1. **Byte-Level Finite Automata & Hit-Counting Guards (`DfaSpec`, `AutomatonBound`):**
   - Formalizes dense byte DFAs (`DfaSpec`: `states`, `initial`, `accepting`, `delta`) with
     complement (`DfaSpec.complement`), word acceptance (`DfaSpec.accepts`), and accepting-visit
     counting (`DfaSpec.hitCount`), plus the 5-mode guard algebra `AutomatonBound`
     (`.mustAccept`, `.mustReject`, `.maxHits hi`, `.exactHits n`, `.rangeHits lo hi`).

2. **Decidable Product-DFA Reachability, Inclusion, & Counterexample Synthesis:**
   - Implements a lockstep 256-byte product-DFA engine (`dfaProductCheck`, `dfaSublanguageDecide`)
     free of `WellFounded.fix`, backed by the inductive reachability invariant `ReachSafe`.
   - Proves **both soundness and completeness** (`dfaProductCheck_iff`, `dfaSublanguageDecide_iff`),
     yielding reflexivity (`dfaSublanguageDecide_refl`), transitivity (`dfaSublanguageDecide_trans`),
     and semantic hit-count dominance/equivalence across distinct DFAs (`hitCount_le_of_sublanguage`,
     `hitCount_eq_of_bislanguage`), alongside an executable FIFO BFS counterexample synthesizer
     (`dfaCounterexample?`, `dfaCounterexample?_sound`).

3. **Unambiguous LL(1) Sub-Grammar & Redaction-Fixed-Point Capability Attenuation:**
   - Defines `GrammarPolicy` combining an LL(1) `AttrCfg` over shared `AttrSemantics`,
     `SafeReplacement` `RedactRule`s (`w = redactBytes rules w`), and `List AutomatonBound`.
   - Proves `grammarPolicyAttenuates_sound`, `grammarPolicyAttenuates_refl`,
     `grammarPolicyAttenuates_trans`, and multi-hop `policyChainAttenuates_sound`: any payload `w`
     and `ast` admitted by a leaf capability is provably admitted by every ancestor up to the root
     capability with the **identical unique AST** (`ast_parent = ast_child`), immune to syntactic
     privilege escalation or duplicate-key AST smuggling, and welded to `TypedAuthorization.Capability`.

4. **3-Hop Capability Hierarchy & 4 Constructive Privilege-Escalation Falsifiers (`by decide`):**
   - Instantiates `rootCapPolicy → serviceCapPolicy → subagentToolCapPolicy` restricting `"tool"`
     names, `"target"` namespace prefixes, `"amount"` magnitudes, secret absence, and batch counts,
     and kernel-proves refusal of: (i) widening `.rangeHits 1 5` to `.rangeHits 1 6`,
     (ii) dropping `Absent("sk-")` (with `dfaCounterexample?` synthesizing minimal `"sk-"`),
     (iii) adding an unauthorized `"wipe_prod"` production, and (iv) injecting duplicate-key
     ambiguity (`ll1Deterministic = false`).

Import boundary: `Theory/` tier (`Mathlib.*` + `Theory.*` only).
-/
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Theory.VerifiedAstTransducer
import Theory.CredentialAuthorityFamily
import Theory.Hyperdocument
import Theory.HyperdocumentOperations

namespace Minidregg.Theory.GrammarTypedCapability

open ContextFreeGrammar
open Minidregg.Theory.VerifiedAstTransducer
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## §1. Dense Byte-Level Finite Automata (`DfaSpec`) & Hit-Counting Semantics -/

/-- Canonical enumeration of all 256 byte values `0..255`. -/
def allBytes : List UInt8 :=
  (List.range 256).map UInt8.ofNat

theorem mem_allBytes (b : UInt8) : b ∈ allBytes := by
  unfold allBytes
  exact List.mem_map.mpr ⟨b.toNat, List.mem_range.mpr b.toNat_lt, UInt8.ofNat_toNat⟩

/-- A dense byte-level deterministic finite automaton: `delta[256 * s + b.toNat]` is the
successor state of `s` on byte `b : UInt8`. Field-for-field isomorphic to
`Compiler.Tower256ContentCert.DfaTable` while residing purely in `Theory/`. -/
structure DfaSpec where
  states    : Nat
  initial   : Nat
  accepting : List Bool
  delta     : List Nat
  deriving DecidableEq, Repr

namespace DfaSpec

/-- Structural well-formedness of a `DfaSpec`. -/
def WellFormed (d : DfaSpec) : Prop :=
  0 < d.states ∧ d.states ≤ 2 ^ 16 ∧ d.initial < d.states ∧
    d.accepting.length = d.states ∧ d.delta.length = d.states * 256 ∧
    ∀ x ∈ d.delta, x < d.states

/-- Executable boolean check equivalent to `DfaSpec.WellFormed`. -/
def wellFormedB (d : DfaSpec) : Bool :=
  decide (0 < d.states) &&
  decide (d.states ≤ 2 ^ 16) &&
  decide (d.initial < d.states) &&
  decide (d.accepting.length = d.states) &&
  decide (d.delta.length = d.states * 256) &&
  d.delta.all (fun x => decide (x < d.states))

theorem wellFormedB_iff (d : DfaSpec) : d.wellFormedB = true ↔ d.WellFormed := by
  simp only [wellFormedB, WellFormed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  tauto

instance instDecidableWellFormed (d : DfaSpec) : Decidable d.WellFormed :=
  decidable_of_iff (d.wellFormedB = true) (wellFormedB_iff d)

/-- Single-byte transition from state `s` on byte `b`. -/
def step (d : DfaSpec) (s : Nat) (b : UInt8) : Nat :=
  d.delta.getD (256 * s + b.toNat) 0

theorem step_lt {d : DfaSpec} (hd : d.WellFormed) {s : Nat} (hs : s < d.states) (b : UInt8) :
    d.step s b < d.states := by
  rcases hd with ⟨_, _, _, _, hlen, hall⟩
  have hb := b.toNat_lt
  have hidx : 256 * s + b.toNat < d.delta.length := by omega
  unfold step
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
  exact hall _ (List.getElem_mem hidx)

/-- Multi-byte transition fold starting from state `s`. -/
def runFrom (d : DfaSpec) (s : Nat) (w : List UInt8) : Nat :=
  w.foldl d.step s

@[simp] theorem runFrom_nil (d : DfaSpec) (s : Nat) : d.runFrom s [] = s := rfl

@[simp] theorem runFrom_cons (d : DfaSpec) (s : Nat) (b : UInt8) (w : List UInt8) :
    d.runFrom s (b :: w) = d.runFrom (d.step s b) w := rfl

theorem runFrom_append (d : DfaSpec) (s : Nat) (u v : List UInt8) :
    d.runFrom s (u ++ v) = d.runFrom (d.runFrom s u) v :=
  List.foldl_append

theorem runFrom_lt {d : DfaSpec} (hd : d.WellFormed) :
    ∀ {s : Nat} (_ : s < d.states) (w : List UInt8), d.runFrom s w < d.states
  | _, hs, [] => hs
  | _, hs, b :: w => runFrom_lt hd (d.step_lt hd hs b) w

/-- State reached from `d.initial` after reading `w`. -/
def run (d : DfaSpec) (w : List UInt8) : Nat :=
  d.runFrom d.initial w

theorem run_lt {d : DfaSpec} (hd : d.WellFormed) (w : List UInt8) : d.run w < d.states :=
  d.runFrom_lt hd hd.2.2.1 w

theorem run_append_singleton (d : DfaSpec) (w : List UInt8) (b : UInt8) :
    d.run (w ++ [b]) = d.step (d.run w) b := by
  simp [run, runFrom_append]

/-- Whether state `s` is marked accepting in `d`. -/
def isAccepting (d : DfaSpec) (s : Nat) : Bool :=
  d.accepting.getD s false

/-- Whether `d` accepts byte word `w`. -/
def accepts (d : DfaSpec) (w : List UInt8) : Bool :=
  d.isAccepting (d.run w)

/-- Language complement DFA: flips accepting flags while keeping states, initial, and transitions. -/
def complement (d : DfaSpec) : DfaSpec :=
  { d with accepting := d.accepting.map Bool.not }

theorem complement_wellFormed {d : DfaSpec} (hd : d.WellFormed) : d.complement.WellFormed := by
  rcases hd with ⟨hpos, hmax, hinit, hacc, hdel, hall⟩
  exact ⟨hpos, hmax, hinit, by simp [complement, hacc], hdel, hall⟩

theorem complement_wellFormedB (d : DfaSpec) : d.complement.wellFormedB = d.wellFormedB := by
  apply Bool.eq_iff_iff.mpr
  rw [wellFormedB_iff, wellFormedB_iff]
  refine ⟨fun h => ?_, complement_wellFormed⟩
  rcases h with ⟨hpos, hmax, hinit, hacc, hdel, hall⟩
  exact ⟨hpos, hmax, hinit, by simpa [complement] using hacc, hdel, hall⟩

@[simp] theorem complement_step (d : DfaSpec) (s : Nat) (b : UInt8) :
    d.complement.step s b = d.step s b := rfl

@[simp] theorem complement_runFrom (d : DfaSpec) (s : Nat) (w : List UInt8) :
    d.complement.runFrom s w = d.runFrom s w := rfl

@[simp] theorem complement_run (d : DfaSpec) (w : List UInt8) :
    d.complement.run w = d.run w := rfl

theorem complement_isAccepting {d : DfaSpec} (hd : d.WellFormed) {s : Nat} (hs : s < d.states) :
    d.complement.isAccepting s = !d.isAccepting s := by
  have hsa : s < d.accepting.length := hd.2.2.2.1 ▸ hs
  simp [complement, isAccepting, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hsa]

theorem complement_accepts {d : DfaSpec} (hd : d.WellFormed) (w : List UInt8) :
    d.complement.accepts w = !d.accepts w := by
  unfold accepts
  rw [complement_run, complement_isAccepting hd (d.run_lt hd w)]

/-- Step hit indicator: `1` if `next` is accepting, `0` otherwise. -/
def stepHit (d : DfaSpec) (next : Nat) : Nat :=
  if d.isAccepting next then 1 else 0

/-- Joint `(state, cumulativeHits)` fold over `w`. -/
def runStateCountFrom (d : DfaSpec) : Nat → Nat → List UInt8 → Nat × Nat
  | s, c, [] => (s, c)
  | s, c, b :: rest =>
      let next := d.step s b
      runStateCountFrom d next (c + d.stepHit next) rest

theorem runStateCountFrom_fst (d : DfaSpec) :
    ∀ (s c : Nat) (w : List UInt8), (d.runStateCountFrom s c w).1 = d.runFrom s w
  | _, _, [] => rfl
  | s, c, b :: rest => runStateCountFrom_fst d (d.step s b) (c + d.stepHit (d.step s b)) rest

theorem runStateCountFrom_snd_add (d : DfaSpec) :
    ∀ (s c : Nat) (w : List UInt8),
      (d.runStateCountFrom s c w).2 = c + (d.runStateCountFrom s 0 w).2
  | _, c, [] => by simp [runStateCountFrom]
  | s, c, b :: rest => by
      simp only [runStateCountFrom]
      rw [runStateCountFrom_snd_add d (d.step s b) (c + d.stepHit (d.step s b)) rest,
          runStateCountFrom_snd_add d (d.step s b) (0 + d.stepHit (d.step s b)) rest]
      omega

theorem runStateCountFrom_append_singleton (d : DfaSpec) :
    ∀ (s c : Nat) (w : List UInt8) (b : UInt8),
      d.runStateCountFrom s c (w ++ [b]) =
        let cur := d.runStateCountFrom s c w
        let next := d.step cur.1 b
        (next, cur.2 + d.stepHit next)
  | s, c, [], b => by simp [runStateCountFrom]
  | s, c, x :: rest, b =>
      runStateCountFrom_append_singleton d (d.step s x) (c + d.stepHit (d.step s x)) rest b

/-- Total number of byte steps in `w` landing in an accepting state of `d`. -/
def hitCount (d : DfaSpec) (w : List UInt8) : Nat :=
  (d.runStateCountFrom d.initial 0 w).2

@[simp] theorem hitCount_nil (d : DfaSpec) : d.hitCount [] = 0 := rfl

theorem hitCount_append_singleton (d : DfaSpec) (u : List UInt8) (b : UInt8) :
    d.hitCount (u ++ [b]) = d.hitCount u + (if d.accepts (u ++ [b]) then 1 else 0) := by
  unfold hitCount
  rw [runStateCountFrom_append_singleton]
  dsimp only
  rw [runStateCountFrom_fst]
  change (d.runStateCountFrom d.initial 0 u).2 + d.stepHit (d.step (d.run u) b) = _
  rw [← run_append_singleton]
  rfl

end DfaSpec

/-! ## §2. Product-DFA Reachability Invariant (`ReachSafe`), Inclusion, & Counterexamples -/

/-- **Inductive Product-DFA Reachability Invariant (`ReachSafe`)**:
`vis` contains `(dc.initial, dp.initial)`, satisfies `pred` on every pair, and is closed under
simultaneous transitions across all 256 byte symbols. -/
def ReachSafe (pred : Nat → Nat → Bool) (dc dp : DfaSpec) (vis : List (Nat × Nat)) : Prop :=
  (dc.initial, dp.initial) ∈ vis ∧
  (∀ p ∈ vis, pred p.1 p.2 = true) ∧
  (∀ p ∈ vis, ∀ b : UInt8, (dc.step p.1 b, dp.step p.2 b) ∈ vis)

theorem reachSafe_mem_runFrom {pred : Nat → Nat → Bool} {dc dp : DfaSpec}
    {vis : List (Nat × Nat)} (h : ReachSafe pred dc dp vis) :
    ∀ {sc sp : Nat}, (sc, sp) ∈ vis → ∀ (w : List UInt8),
      (dc.runFrom sc w, dp.runFrom sp w) ∈ vis
  | _, _, hmem, [] => hmem
  | sc, sp, hmem, b :: w =>
      reachSafe_mem_runFrom h (h.2.2 (sc, sp) hmem b) w

/-- Any `ReachSafe` invariant witnesses `pred (dc.run w) (dp.run w) = true` for every word `w`. -/
theorem reachSafe_sound_run {pred : Nat → Nat → Bool} {dc dp : DfaSpec}
    {vis : List (Nat × Nat)} (h : ReachSafe pred dc dp vis) (w : List UInt8) :
    pred (dc.run w) (dp.run w) = true :=
  h.2.1 _ (reachSafe_mem_runFrom h h.1 w)

/-- Lockstep 256-entry transition-row expander: scans `dc.delta.drop (256 * sc)` and
`dp.delta.drop (256 * sp)` in `O(1)` per byte without repeated list indexing in `whnf`. -/
def expandRowLockstep :
    Nat → List Nat → List Nat → List (Nat × Nat) → List (Nat × Nat) →
      List (Nat × Nat) × List (Nat × Nat)
  | 0, _, _, vis, q => (vis, q)
  | rem + 1, cs, ps, vis, q =>
      let nxt := (cs.headD 0, ps.headD 0)
      if nxt ∈ vis then
        expandRowLockstep rem cs.tail ps.tail vis q
      else
        expandRowLockstep rem cs.tail ps.tail (nxt :: vis) (nxt :: q)

private theorem list_getD_zero_eq_headD (xs : List Nat) : xs.getD 0 0 = xs.headD 0 := by
  cases xs <;> rfl

private theorem list_getD_succ_eq_tail (xs : List Nat) (j : Nat) :
    xs.getD (j + 1) 0 = xs.tail.getD j 0 := by
  cases xs <;> rfl

private theorem list_drop_getD_eq (xs : List Nat) (off j : Nat) :
    (xs.drop off).getD j 0 = xs.getD (off + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem expandRowLockstep_sub_vis :
    ∀ (rem : Nat) (cs ps : List Nat) (vis q : List (Nat × Nat)),
      ∀ x ∈ vis, x ∈ (expandRowLockstep rem cs ps vis q).1
  | 0, _, _, _, _, _, hx => hx
  | rem + 1, cs, ps, vis, q, x, hx => by
      simp only [expandRowLockstep]
      split
      · exact expandRowLockstep_sub_vis rem cs.tail ps.tail vis q x hx
      · exact expandRowLockstep_sub_vis rem cs.tail ps.tail _ _ x (List.mem_cons_of_mem _ hx)

private theorem expandRowLockstep_sub_q :
    ∀ (rem : Nat) (cs ps : List Nat) (vis q : List (Nat × Nat)),
      ∀ x ∈ q, x ∈ (expandRowLockstep rem cs ps vis q).2
  | 0, _, _, _, _, _, hx => hx
  | rem + 1, cs, ps, vis, q, x, hx => by
      simp only [expandRowLockstep]
      split
      · exact expandRowLockstep_sub_q rem cs.tail ps.tail vis q x hx
      · exact expandRowLockstep_sub_q rem cs.tail ps.tail _ _ x (List.mem_cons_of_mem _ hx)

private theorem expandRowLockstep_new_in_q :
    ∀ (rem : Nat) (cs ps : List Nat) (vis q : List (Nat × Nat)) (x : Nat × Nat),
      x ∈ (expandRowLockstep rem cs ps vis q).1 → x ∉ vis →
        x ∈ (expandRowLockstep rem cs ps vis q).2
  | 0, _, _, _, _, _, hmem, hnot => absurd hmem hnot
  | rem + 1, cs, ps, vis, q, x, hmem, hnot => by
      simp only [expandRowLockstep] at hmem ⊢
      split at hmem <;> rename_i hcond
      · simp only [hcond, ↓reduceIte]
        exact expandRowLockstep_new_in_q rem cs.tail ps.tail vis q x hmem hnot
      · simp only [hcond, ↓reduceIte]
        by_cases hxeq : x = (cs.headD 0, ps.headD 0)
        · subst hxeq
          exact expandRowLockstep_sub_q rem cs.tail ps.tail _ _ _ (List.mem_cons_self ..)
        · exact expandRowLockstep_new_in_q rem cs.tail ps.tail _ _ x hmem
            (fun hm => by rcases List.mem_cons.mp hm with rfl | hm'
                          · exact hxeq rfl
                          · exact hnot hm')

private theorem expandRowLockstep_contains_idx :
    ∀ (rem : Nat) (cs ps : List Nat) (vis q : List (Nat × Nat)) (j : Nat),
      j < rem → (cs.getD j 0, ps.getD j 0) ∈ (expandRowLockstep rem cs ps vis q).1
  | 0, _, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | rem + 1, cs, ps, vis, q, 0, _ => by
      simp only [expandRowLockstep, list_getD_zero_eq_headD]
      split <;> rename_i hmem
      · exact expandRowLockstep_sub_vis rem cs.tail ps.tail vis q _ hmem
      · exact expandRowLockstep_sub_vis rem cs.tail ps.tail _ _ _ (List.mem_cons_self ..)
  | rem + 1, cs, ps, vis, q, j + 1, hj => by
      simp only [expandRowLockstep, list_getD_succ_eq_tail]
      split
      · exact expandRowLockstep_contains_idx rem cs.tail ps.tail vis q j (by omega)
      · exact expandRowLockstep_contains_idx rem cs.tail ps.tail _ _ j (by omega)

private theorem expandRowLockstep_preserves_reach_and_nodup
    (dc dp : DfaSpec) (p : Nat × Nat)
    (hpReach : ∃ w : List UInt8, (dc.run w, dp.run w) = p) :
    ∀ (k : Nat), k ≤ 256 → ∀ (vis q : List (Nat × Nat)),
      vis.Nodup → q.Nodup → (∀ x ∈ q, x ∈ vis) →
      (∀ x ∈ vis, ∃ w : List UInt8, (dc.run w, dp.run w) = x) →
      (expandRowLockstep k (dc.delta.drop (256 * p.1 + (256 - k)))
        (dp.delta.drop (256 * p.2 + (256 - k))) vis q).1.Nodup ∧
      (expandRowLockstep k (dc.delta.drop (256 * p.1 + (256 - k)))
        (dp.delta.drop (256 * p.2 + (256 - k))) vis q).2.Nodup ∧
      (∀ x ∈ (expandRowLockstep k (dc.delta.drop (256 * p.1 + (256 - k)))
        (dp.delta.drop (256 * p.2 + (256 - k))) vis q).2,
        x ∈ (expandRowLockstep k (dc.delta.drop (256 * p.1 + (256 - k)))
          (dp.delta.drop (256 * p.2 + (256 - k))) vis q).1) ∧
      (∀ x ∈ (expandRowLockstep k (dc.delta.drop (256 * p.1 + (256 - k)))
        (dp.delta.drop (256 * p.2 + (256 - k))) vis q).1,
        ∃ w : List UInt8, (dc.run w, dp.run w) = x) ∧
      (expandRowLockstep k (dc.delta.drop (256 * p.1 + (256 - k)))
        (dp.delta.drop (256 * p.2 + (256 - k))) vis q).1.length + q.length =
        vis.length + (expandRowLockstep k (dc.delta.drop (256 * p.1 + (256 - k)))
          (dp.delta.drop (256 * p.2 + (256 - k))) vis q).2.length := by
  intro k
  induction k with
  | zero =>
      intro _ vis q hvnd hqnd hqsub hreach
      simp only [expandRowLockstep]
      exact ⟨hvnd, hqnd, hqsub, hreach, trivial⟩
  | succ k ih =>
      intro hk vis q hvnd hqnd hqsub hreach
      let bNat := 256 - (k + 1)
      have hbLt : bNat < 256 := by omega
      let b : UInt8 := UInt8.ofNat bNat
      have hbToNat : b.toNat = bNat := UInt8.toNat_ofNat_of_lt hbLt
      let cs := dc.delta.drop (256 * p.1 + bNat)
      let ps := dp.delta.drop (256 * p.2 + bNat)
      have hheadC : cs.headD 0 = dc.step p.1 b := by
        rw [← list_getD_zero_eq_headD, list_drop_getD_eq, Nat.add_zero, ← hbToNat]; rfl
      have hheadP : ps.headD 0 = dp.step p.2 b := by
        rw [← list_getD_zero_eq_headD, list_drop_getD_eq, Nat.add_zero, ← hbToNat]; rfl
      have htailC : cs.tail = dc.delta.drop (256 * p.1 + (256 - k)) := by
        simp only [cs, List.tail_drop]; congr 1; omega
      have htailP : ps.tail = dp.delta.drop (256 * p.2 + (256 - k)) := by
        simp only [ps, List.tail_drop]; congr 1; omega
      have hnxtReach : ∃ w : List UInt8, (dc.run w, dp.run w) = (cs.headD 0, ps.headD 0) := by
        rcases hpReach with ⟨w, hpEq⟩
        refine ⟨w ++ [b], ?_⟩
        rw [hheadC, hheadP, ← hpEq, dc.run_append_singleton, dp.run_append_singleton]
      change (expandRowLockstep (k + 1) cs ps vis q).1.Nodup ∧
        (expandRowLockstep (k + 1) cs ps vis q).2.Nodup ∧
        (∀ x ∈ (expandRowLockstep (k + 1) cs ps vis q).2,
          x ∈ (expandRowLockstep (k + 1) cs ps vis q).1) ∧
        (∀ x ∈ (expandRowLockstep (k + 1) cs ps vis q).1,
          ∃ w : List UInt8, (dc.run w, dp.run w) = x) ∧
        (expandRowLockstep (k + 1) cs ps vis q).1.length + q.length =
          vis.length + (expandRowLockstep (k + 1) cs ps vis q).2.length
      simp only [expandRowLockstep]
      by_cases hmem : (cs.headD 0, ps.headD 0) ∈ vis
      · simp only [hmem, ↓reduceIte, htailC, htailP]
        exact ih (by omega) vis q hvnd hqnd hqsub hreach
      · simp only [hmem, ↓reduceIte, htailC, htailP]
        have hnotQ : (cs.headD 0, ps.headD 0) ∉ q := fun hq => hmem (hqsub _ hq)
        have hvnd' : ((cs.headD 0, ps.headD 0) :: vis).Nodup := List.nodup_cons.mpr ⟨hmem, hvnd⟩
        have hqnd' : ((cs.headD 0, ps.headD 0) :: q).Nodup := List.nodup_cons.mpr ⟨hnotQ, hqnd⟩
        have hqsub' : ∀ x ∈ (cs.headD 0, ps.headD 0) :: q, x ∈ (cs.headD 0, ps.headD 0) :: vis := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (hqsub x hx')
        have hreach' : ∀ x ∈ (cs.headD 0, ps.headD 0) :: vis,
            ∃ w : List UInt8, (dc.run w, dp.run w) = x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact hnxtReach
          · exact hreach x hx'
        obtain ⟨h1, h2, h3, h4, h5⟩ := ih (by omega) _ _ hvnd' hqnd' hqsub' hreach'
        refine ⟨h1, h2, h3, h4, ?_⟩
        simp only [List.length_cons] at h5
        omega

/-- Structural fuel-bounded product-DFA exploration loop (zero `WellFounded.fix`). -/
def dfaProductLoop (pred : Nat → Nat → Bool) (dc dp : DfaSpec) :
    Nat → List (Nat × Nat) → List (Nat × Nat) → Bool
  | _, _, [] => true
  | 0, _, _ :: _ => false
  | fuel + 1, vis, p :: q =>
      if pred p.1 p.2 then
        match expandRowLockstep 256 (dc.delta.drop (256 * p.1)) (dp.delta.drop (256 * p.2)) vis q with
        | (vis', q') => dfaProductLoop pred dc dp fuel vis' q'
      else
        false

/-- **Generic Product-DFA Reachability Checker (`dfaProductCheck`)**:
verifies `pred` on all reachable product states of `dc × dp`. -/
def dfaProductCheck (pred : Nat → Nat → Bool) (dc dp : DfaSpec)
    (fuel : Nat := dc.states * dp.states + 1) : Bool :=
  let init := (dc.initial, dp.initial)
  dfaProductLoop pred dc dp fuel [init] [init]

private def FrontierInv (pred : Nat → Nat → Bool) (dc dp : DfaSpec)
    (vis q : List (Nat × Nat)) : Prop :=
  (dc.initial, dp.initial) ∈ vis ∧
  (∀ x ∈ vis, x ∈ q ∨ pred x.1 x.2 = true) ∧
  (∀ x ∈ vis, x ∈ q ∨ ∀ b : UInt8, (dc.step x.1 b, dp.step x.2 b) ∈ vis)

private theorem dfaProductLoop_sound {pred : Nat → Nat → Bool} {dc dp : DfaSpec} :
    ∀ (fuel : Nat) (vis q : List (Nat × Nat)),
      FrontierInv pred dc dp vis q →
      dfaProductLoop pred dc dp fuel vis q = true →
      ∃ visFinal, ReachSafe pred dc dp visFinal
  | _, vis, [], hinv, _ =>
      ⟨vis, hinv.1,
       fun p hp => (hinv.2.1 p hp).resolve_left List.not_mem_nil,
       fun p hp => (hinv.2.2 p hp).resolve_left List.not_mem_nil⟩
  | 0, _, _ :: _, _, hloop => by simp [dfaProductLoop] at hloop
  | fuel + 1, vis, p :: q, hinv, hloop => by
      simp only [dfaProductLoop] at hloop
      by_cases hpred : pred p.1 p.2 = true
      · simp only [hpred, ↓reduceIte] at hloop
        let res := expandRowLockstep 256 (dc.delta.drop (256 * p.1)) (dp.delta.drop (256 * p.2)) vis q
        have hstepAll : ∀ b : UInt8, (dc.step p.1 b, dp.step p.2 b) ∈ res.1 := by
          intro b
          have hidx := expandRowLockstep_contains_idx 256
            (dc.delta.drop (256 * p.1)) (dp.delta.drop (256 * p.2)) vis q b.toNat b.toNat_lt
          simpa [res, list_drop_getD_eq, DfaSpec.step] using hidx
        have hinv' : FrontierInv pred dc dp res.1 res.2 := by
          refine ⟨expandRowLockstep_sub_vis 256 _ _ vis q _ hinv.1, ?_, ?_⟩
          · intro x hx
            by_cases hxin : x ∈ vis
            · rcases hinv.2.1 x hxin with hxq | hxp
              · rcases List.mem_cons.mp hxq with rfl | hxq'
                · exact Or.inr hpred
                · exact Or.inl (expandRowLockstep_sub_q 256 _ _ vis q x hxq')
              · exact Or.inr hxp
            · exact Or.inl (expandRowLockstep_new_in_q 256 _ _ vis q x hx hxin)
          · intro x hx
            by_cases hxin : x ∈ vis
            · rcases hinv.2.2 x hxin with hxq | hxs
              · rcases List.mem_cons.mp hxq with rfl | hxq'
                · exact Or.inr hstepAll
                · exact Or.inl (expandRowLockstep_sub_q 256 _ _ vis q x hxq')
              · exact Or.inr fun b => expandRowLockstep_sub_vis 256 _ _ vis q _ (hxs b)
            · exact Or.inl (expandRowLockstep_new_in_q 256 _ _ vis q x hx hxin)
        exact dfaProductLoop_sound fuel res.1 res.2 hinv' hloop
      · simp [hpred] at hloop

/-- **Soundness of `dfaProductCheck` (at ANY `fuel`)**: produces a `ReachSafe` invariant and
guarantees `pred (dc.run w) (dp.run w) = true` for every byte word `w`. -/
theorem dfaProductCheck_sound_reachSafe {pred : Nat → Nat → Bool} {dc dp : DfaSpec} {fuel : Nat}
    (h : dfaProductCheck pred dc dp fuel = true) :
    ∃ vis, ReachSafe pred dc dp vis := by
  refine dfaProductLoop_sound fuel [(dc.initial, dp.initial)] [(dc.initial, dp.initial)] ?_ h
  exact ⟨List.mem_singleton_self _,
         fun _ hx => Or.inl hx,
         fun _ hx => Or.inl hx⟩

theorem dfaProductCheck_sound {pred : Nat → Nat → Bool} {dc dp : DfaSpec} {fuel : Nat}
    (h : dfaProductCheck pred dc dp fuel = true) (w : List UInt8) :
    pred (dc.run w) (dp.run w) = true := by
  obtain ⟨vis, hvis⟩ := dfaProductCheck_sound_reachSafe h
  exact reachSafe_sound_run hvis w

private theorem nodup_vis_length_le {dc dp : DfaSpec} (hdc : dc.WellFormed) (hdp : dp.WellFormed)
    {vis : List (Nat × Nat)} (hvnd : vis.Nodup)
    (hreach : ∀ x ∈ vis, ∃ w : List UInt8, (dc.run w, dp.run w) = x) :
    vis.length ≤ dc.states * dp.states := by
  have hsub : vis.toFinset ⊆ Finset.range dc.states ×ˢ Finset.range dp.states := by
    intro x hx
    obtain ⟨w, rfl⟩ := hreach x (List.mem_toFinset.mp hx)
    simp [dc.run_lt hdc w, dp.run_lt hdp w]
  have hcard := Finset.card_le_card hsub
  simpa [List.toFinset_card_of_nodup hvnd] using hcard

private theorem dfaProductLoop_complete {pred : Nat → Nat → Bool} {dc dp : DfaSpec}
    (hdc : dc.WellFormed) (hdp : dp.WellFormed)
    (hall : ∀ w : List UInt8, pred (dc.run w) (dp.run w) = true) :
    ∀ (fuel : Nat) (vis q : List (Nat × Nat)),
      vis.Nodup → q.Nodup → (∀ x ∈ q, x ∈ vis) →
      (∀ x ∈ vis, ∃ w : List UInt8, (dc.run w, dp.run w) = x) →
      q.length + dc.states * dp.states ≤ fuel + vis.length →
      dfaProductLoop pred dc dp fuel vis q = true
  | _, _, [], _, _, _, _, _ => by simp [dfaProductLoop]
  | 0, vis, _ :: _, hvnd, _, _, hreach, hbud => by
      have hvle := nodup_vis_length_le hdc hdp hvnd hreach
      simp only [List.length_cons] at hbud
      omega
  | fuel + 1, vis, p :: q, hvnd, hqnd, hqsub, hreach, hbud => by
      have hpVis : p ∈ vis := hqsub p (List.mem_cons_self ..)
      obtain ⟨wp, hwp⟩ := hreach p hpVis
      have hpred : pred p.1 p.2 = true := by rw [← hwp]; exact hall wp
      simp only [dfaProductLoop, hpred, ↓reduceIte]
      have hqnd' : q.Nodup := (List.nodup_cons.mp hqnd).2
      have hqsub' : ∀ x ∈ q, x ∈ vis := fun x hx => hqsub x (List.mem_cons_of_mem _ hx)
      have hexp := expandRowLockstep_preserves_reach_and_nodup dc dp p ⟨wp, hwp⟩
        256 (le_refl 256) vis q hvnd hqnd' hqsub' hreach
      simp only [Nat.sub_self, Nat.add_zero] at hexp
      obtain ⟨hvnd1, hqnd1, hqsub1, hreach1, hlenEq⟩ := hexp
      simp only [List.length_cons] at hbud
      exact dfaProductLoop_complete hdc hdp hall fuel _ _ hvnd1 hqnd1 hqsub1 hreach1 (by omega)

/-- **Completeness & Exact Equivalence of `dfaProductCheck`** on well-formed DFAs:
`dfaProductCheck pred dc dp` returns `true` iff `pred (dc.run w) (dp.run w) = true` for all `w`. -/
theorem dfaProductCheck_iff {pred : Nat → Nat → Bool} {dc dp : DfaSpec}
    (hdc : dc.WellFormed) (hdp : dp.WellFormed) :
    dfaProductCheck pred dc dp = true ↔ ∀ w : List UInt8, pred (dc.run w) (dp.run w) = true := by
  refine ⟨fun h w => dfaProductCheck_sound h w, fun hall => ?_⟩
  unfold dfaProductCheck
  refine dfaProductLoop_complete hdc hdp hall (dc.states * dp.states + 1)
    [(dc.initial, dp.initial)] [(dc.initial, dp.initial)]
    (List.nodup_singleton _) (List.nodup_singleton _) (fun _ h => h) ?_ (by simp; omega)
  intro x hx
  rw [List.mem_singleton.mp hx]
  exact ⟨[], rfl⟩

/-- **Executable Product-DFA Sublanguage Checker (`dfaSublanguageDecide`)**:
certifies $L(d_{\text{child}}) \subseteq L(d_{\text{parent}})$ by verifying via `ReachSafe` that no
reachable product state $(s_c, s_p)$ has `dc.isAccepting s_c = true ∧ dp.isAccepting s_p = false`. -/
def dfaSublanguageDecide (dc dp : DfaSpec) (fuel : Nat := dc.states * dp.states + 1) : Bool :=
  dfaProductCheck (fun sc sp => !(dc.isAccepting sc && !dp.isAccepting sp)) dc dp fuel

/-- **`dfaSublanguageDecide_sound`** — Capstone Sublanguage Inclusion Soundness Theorem:
at ANY fuel, `dfaSublanguageDecide dc dp fuel = true` guarantees $L(d_c) \subseteq L(d_p)$. -/
theorem dfaSublanguageDecide_sound {dc dp : DfaSpec} {fuel : Nat}
    (h : dfaSublanguageDecide dc dp fuel = true) (w : List UInt8)
    (hc : dc.accepts w = true) :
    dp.accepts w = true := by
  have hp := dfaProductCheck_sound h w
  unfold DfaSpec.accepts at hc ⊢
  rw [hc] at hp
  simpa using hp

/-- **Exact Soundness & Completeness of `dfaSublanguageDecide`** on well-formed DFAs. -/
theorem dfaSublanguageDecide_iff {dc dp : DfaSpec}
    (hdc : dc.WellFormed) (hdp : dp.WellFormed) :
    dfaSublanguageDecide dc dp = true ↔ ∀ w : List UInt8, dc.accepts w = true → dp.accepts w = true := by
  unfold dfaSublanguageDecide
  rw [dfaProductCheck_iff hdc hdp]
  constructor
  · intro h w hc
    have hw := h w
    unfold DfaSpec.accepts at hc ⊢
    rw [hc] at hw
    simpa using hw
  · intro h w
    by_cases hc : dc.isAccepting (dc.run w) = true
    · have hp := h w hc
      unfold DfaSpec.accepts at hp
      simp [hc, hp]
    · simp [hc]

theorem dfaSublanguageDecide_refl {d : DfaSpec} (hd : d.WellFormed) :
    dfaSublanguageDecide d d = true :=
  (dfaSublanguageDecide_iff hd hd).mpr fun _ h => h

theorem dfaSublanguageDecide_trans {d₁ d₂ d₃ : DfaSpec}
    (h₁ : d₁.WellFormed) (_h₂ : d₂.WellFormed) (h₃ : d₃.WellFormed)
    (h12 : dfaSublanguageDecide d₁ d₂ = true)
    (h23 : dfaSublanguageDecide d₂ d₃ = true) :
    dfaSublanguageDecide d₁ d₃ = true :=
  (dfaSublanguageDecide_iff h₁ h₃).mpr fun w hw =>
    dfaSublanguageDecide_sound h23 w (dfaSublanguageDecide_sound h12 w hw)

/-- Language inclusion $L(d_1) \subseteq L(d_2)$ implies prefix hit-count dominance
`d₁.hitCount w ≤ d₂.hitCount w` for every word `w`. -/
theorem hitCount_le_of_sublanguage {d₁ d₂ : DfaSpec} {fuel : Nat}
    (hsub : dfaSublanguageDecide d₁ d₂ fuel = true) (w : List UInt8) :
    d₁.hitCount w ≤ d₂.hitCount w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton u b ih =>
      rw [d₁.hitCount_append_singleton, d₂.hitCount_append_singleton]
      by_cases h1 : d₁.accepts (u ++ [b]) = true
      · have h2 : d₂.accepts (u ++ [b]) = true := dfaSublanguageDecide_sound hsub _ h1
        simp [h1, h2]; omega
      · simp [h1]; omega

/-- Mutual language inclusion ($L(d_1) = L(d_2)$) implies exact hit-count equality
`d₁.hitCount w = d₂.hitCount w` for every word `w`, even across non-isomorphic DFAs. -/
theorem hitCount_eq_of_bislanguage {d₁ d₂ : DfaSpec} {f₁ f₂ : Nat}
    (h12 : dfaSublanguageDecide d₁ d₂ f₁ = true)
    (h21 : dfaSublanguageDecide d₂ d₁ f₂ = true) (w : List UInt8) :
    d₁.hitCount w = d₂.hitCount w :=
  Nat.le_antisymm (hitCount_le_of_sublanguage h12 w) (hitCount_le_of_sublanguage h21 w)

/-! ### Executable FIFO BFS Counterexample Synthesizer (`dfaCounterexample?`) -/

/-- Expand all 256 byte transitions from `(p, revW)` into `(vis, backRev)` in increasing byte order. -/
def expandCexRow :
    Nat → List Nat → List Nat → List UInt8 → List (Nat × Nat) →
      List ((Nat × Nat) × List UInt8) →
      List (Nat × Nat) × List ((Nat × Nat) × List UInt8)
  | 0, _, _, _, vis, back => (vis, back)
  | rem + 1, cs, ps, revW, vis, back =>
      let b : UInt8 := UInt8.ofNat (256 - (rem + 1))
      let nxt := (cs.headD 0, ps.headD 0)
      if nxt ∈ vis then
        expandCexRow rem cs.tail ps.tail revW vis back
      else
        expandCexRow rem cs.tail ps.tail revW (nxt :: vis) ((nxt, b :: revW) :: back)

/-- Two-list FIFO BFS queue exploring words in shortest-length, lexicographic byte order. -/
def dfaCexLoop (dc dp : DfaSpec) :
    Nat → List (Nat × Nat) → List ((Nat × Nat) × List UInt8) →
      List ((Nat × Nat) × List UInt8) → Option (List UInt8)
  | 0, _, _, _ => none
  | _ + 1, _, [], [] => none
  | fuel + 1, vis, [], back =>
      dfaCexLoop dc dp fuel vis back.reverse []
  | fuel + 1, vis, (p, revW) :: front, back =>
      if dc.isAccepting p.1 && !dp.isAccepting p.2 then
        some revW.reverse
      else
        match expandCexRow 256 (dc.delta.drop (256 * p.1)) (dp.delta.drop (256 * p.2))
            revW vis back with
        | (vis', back') => dfaCexLoop dc dp fuel vis' front back'

/-- **Executable Product-DFA Counterexample Synthesizer (`dfaCounterexample?`)**:
returns `some w` witnessing $w \in L(d_c) \setminus L(d_p)$ via FIFO BFS over `0..255`. -/
def dfaCounterexample? (dc dp : DfaSpec) (fuel : Nat := 2 * dc.states * dp.states + 2) :
    Option (List UInt8) :=
  let init := (dc.initial, dp.initial)
  dfaCexLoop dc dp fuel [init] [(init, [])] []

private theorem expandCexRow_inv (dc dp : DfaSpec) (p : Nat × Nat) (revW : List UInt8)
    (hp : (dc.run revW.reverse, dp.run revW.reverse) = p) :
    ∀ (k : Nat), k ≤ 256 → ∀ (vis : List (Nat × Nat))
      (back : List ((Nat × Nat) × List UInt8)),
      (∀ st rw, (st, rw) ∈ back → (dc.run rw.reverse, dp.run rw.reverse) = st) →
      ∀ st rw, (st, rw) ∈ (expandCexRow k (dc.delta.drop (256 * p.1 + (256 - k)))
          (dp.delta.drop (256 * p.2 + (256 - k))) revW vis back).2 →
        (dc.run rw.reverse, dp.run rw.reverse) = st := by
  intro k
  induction k with
  | zero =>
      intro _ _ back hback st rw hmem
      exact hback st rw hmem
  | succ k ih =>
      intro hk vis back hback st rw hmem
      let bNat := 256 - (k + 1)
      have hbLt : bNat < 256 := by omega
      let b : UInt8 := UInt8.ofNat bNat
      have hbToNat : b.toNat = bNat := UInt8.toNat_ofNat_of_lt hbLt
      let cs := dc.delta.drop (256 * p.1 + bNat)
      let ps := dp.delta.drop (256 * p.2 + bNat)
      have hheadC : cs.headD 0 = dc.step p.1 b := by
        rw [← list_getD_zero_eq_headD, list_drop_getD_eq, Nat.add_zero, ← hbToNat]; rfl
      have hheadP : ps.headD 0 = dp.step p.2 b := by
        rw [← list_getD_zero_eq_headD, list_drop_getD_eq, Nat.add_zero, ← hbToNat]; rfl
      have htailC : cs.tail = dc.delta.drop (256 * p.1 + (256 - k)) := by
        simp only [cs, List.tail_drop]; congr 1; omega
      have htailP : ps.tail = dp.delta.drop (256 * p.2 + (256 - k)) := by
        simp only [ps, List.tail_drop]; congr 1; omega
      change (st, rw) ∈ (expandCexRow (k + 1) cs ps revW vis back).2 at hmem
      simp only [expandCexRow] at hmem
      by_cases hcMem : (cs.headD 0, ps.headD 0) ∈ vis
      · simp only [hcMem, ↓reduceIte, htailC, htailP] at hmem
        exact ih (by omega) vis back hback st rw hmem
      · simp only [hcMem, ↓reduceIte, htailC, htailP] at hmem
        refine ih (by omega) _ _ (fun st' rw' hq => ?_) st rw hmem
        rcases List.mem_cons.mp hq with heq | hq'
        · cases heq
          simp only [List.reverse_cons, dc.run_append_singleton, dp.run_append_singleton,
            hheadC, hheadP]
          rw [← hp]
        · exact hback st' rw' hq'

private theorem dfaCexLoop_sound (dc dp : DfaSpec) :
    ∀ (fuel : Nat) (vis : List (Nat × Nat))
      (front back : List ((Nat × Nat) × List UInt8)) (w : List UInt8),
      (∀ q rw, (q, rw) ∈ front → (dc.run rw.reverse, dp.run rw.reverse) = q) →
      (∀ q rw, (q, rw) ∈ back → (dc.run rw.reverse, dp.run rw.reverse) = q) →
      dfaCexLoop dc dp fuel vis front back = some w →
      dc.accepts w = true ∧ dp.accepts w = false := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ h; simp [dfaCexLoop] at h
  | succ fuel ih =>
      intro vis front back w hfront hback h
      cases front with
      | nil =>
          cases back with
          | nil => simp [dfaCexLoop] at h
          | cons b bs =>
              simp only [dfaCexLoop] at h
              exact ih vis (b :: bs).reverse [] w
                (fun q rw hm => hback q rw (List.mem_reverse.mp hm))
                (fun _ _ hm => False.elim (List.not_mem_nil hm)) h
      | cons head rest =>
          rcases head with ⟨p, revW⟩
          have hp := hfront p revW (List.mem_cons_self ..)
          simp only [dfaCexLoop] at h
          by_cases hbad : (dc.isAccepting p.1 && !dp.isAccepting p.2) = true
          · simp only [hbad, ↓reduceIte, Option.some.injEq] at h
            subst h
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hbad
            rcases Prod.mk.inj hp with ⟨hrC, hrP⟩
            exact ⟨by simpa [DfaSpec.accepts, hrC] using hbad.1,
                   by simpa [DfaSpec.accepts, hrP] using hbad.2⟩
          · simp only [hbad, Bool.false_eq_true, ↓reduceIte] at h
            have hexp := expandCexRow_inv dc dp p revW hp 256 (le_refl 256) vis back hback
            simp only [Nat.sub_self, Nat.add_zero] at hexp
            exact ih _ rest _ w
              (fun q rw hm => hfront q rw (List.mem_cons_of_mem _ hm)) hexp h

/-- **Soundness of `dfaCounterexample?`**: every returned word `w` is a genuine separating witness
accepted by `dc` and rejected by `dp` ($w \in L(d_c) \setminus L(d_p)$). -/
theorem dfaCounterexample?_sound {dc dp : DfaSpec} {fuel : Nat} {w : List UInt8}
    (h : dfaCounterexample? dc dp fuel = some w) :
    dc.accepts w = true ∧ dp.accepts w = false := by
  refine dfaCexLoop_sound dc dp fuel _ _ [] w ?_ (fun _ _ hm => False.elim (List.not_mem_nil hm)) h
  intro q rw hm
  rcases List.mem_singleton.mp hm with ⟨rfl, rfl⟩
  rfl

/-! ## §3. Syntactic & Automata-Predicated Capability Algebra (`AutomatonBound`, `GrammarPolicy`) -/

/-- **5-Mode Automaton Guard (`AutomatonBound`)**:
constrains byte-stream language acceptance/rejection or accepting-visit counts over a `DfaSpec`. -/
inductive AutomatonBound where
  | mustAccept (dfa : DfaSpec)
  | mustReject (dfa : DfaSpec)
  | maxHits    (dfa : DfaSpec) (hi : Nat)
  | exactHits  (dfa : DfaSpec) (n : Nat)
  | rangeHits  (dfa : DfaSpec) (lo hi : Nat)
  deriving DecidableEq, Repr

namespace AutomatonBound

/-- Underlying `DfaSpec` of an `AutomatonBound`. -/
def dfa : AutomatonBound → DfaSpec
  | .mustAccept d => d
  | .mustReject d => d
  | .maxHits d _ => d
  | .exactHits d _ => d
  | .rangeHits d _ _ => d

/-- Executable evaluation of an `AutomatonBound` on byte payload `w`. -/
def holds : AutomatonBound → List UInt8 → Bool
  | .mustAccept d, w => d.accepts w
  | .mustReject d, w => !d.accepts w
  | .maxHits d hi, w => decide (d.hitCount w ≤ hi)
  | .exactHits d n, w => decide (d.hitCount w = n)
  | .rangeHits d lo hi, w => decide (lo ≤ d.hitCount w ∧ d.hitCount w ≤ hi)

/-- Structural well-formedness of an `AutomatonBound` (well-formed DFA + non-inverted interval). -/
def wellFormedB : AutomatonBound → Bool
  | .mustAccept d => d.wellFormedB
  | .mustReject d => d.wellFormedB
  | .maxHits d _ => d.wellFormedB
  | .exactHits d _ => d.wellFormedB
  | .rangeHits d lo hi => d.wellFormedB && decide (lo ≤ hi)

theorem dfa_wellFormed_of_wellFormedB {b : AutomatonBound} (h : b.wellFormedB = true) :
    b.dfa.WellFormed := by
  cases b <;> simp only [wellFormedB, Bool.and_eq_true] at h
  · exact (DfaSpec.wellFormedB_iff _).mp h
  · exact (DfaSpec.wellFormedB_iff _).mp h
  · exact (DfaSpec.wellFormedB_iff _).mp h
  · exact (DfaSpec.wellFormedB_iff _).mp h
  · exact (DfaSpec.wellFormedB_iff _).mp h.1

/-- Normalize `.mustAccept d` and `.mustReject d` into an effective acceptance DFA (`d` vs `d.complement`). -/
def toAcceptDfa? : AutomatonBound → Option DfaSpec
  | .mustAccept d => some d
  | .mustReject d => some d.complement
  | _ => none

/-- Normalize `.maxHits`, `.exactHits`, and `.rangeHits` into `(dfa, lo, hi)`. -/
def countInterval? : AutomatonBound → Option (DfaSpec × Nat × Nat)
  | .maxHits d hi => some (d, 0, hi)
  | .exactHits d n => some (d, n, n)
  | .rangeHits d lo hi => some (d, lo, hi)
  | _ => none

theorem toAcceptDfa?_none_iff_countInterval?_some (b : AutomatonBound) :
    b.toAcceptDfa? = none ↔ (b.countInterval?).isSome = true := by
  cases b <;> simp [toAcceptDfa?, countInterval?]

theorem toAcceptDfa?_spec {b : AutomatonBound} {dEff : DfaSpec}
    (hwf : b.dfa.WellFormed) (h : b.toAcceptDfa? = some dEff) :
    dEff.WellFormed ∧ ∀ w, b.holds w = dEff.accepts w := by
  cases b with
  | mustAccept d =>
      simp only [toAcceptDfa?, Option.some.injEq] at h
      subst h
      exact ⟨hwf, fun _ => rfl⟩
  | mustReject d =>
      simp only [toAcceptDfa?, Option.some.injEq] at h
      subst h
      exact ⟨DfaSpec.complement_wellFormed hwf, fun w => (DfaSpec.complement_accepts hwf w).symm⟩
  | maxHits _ _ | exactHits _ _ | rangeHits _ _ _ =>
      simp [toAcceptDfa?] at h

theorem countInterval?_spec {b : AutomatonBound} {d : DfaSpec} {lo hi : Nat}
    (h : b.countInterval? = some (d, lo, hi)) :
    d = b.dfa ∧ ∀ w, (b.holds w = true ↔ lo ≤ d.hitCount w ∧ d.hitCount w ≤ hi) := by
  cases b with
  | mustAccept _ | mustReject _ =>
      simp [countInterval?] at h
  | maxHits d' hi' =>
      simp only [countInterval?, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, fun w => by simp [holds]⟩
  | exactHits d' n' =>
      simp only [countInterval?, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, fun w => by simp [holds]; omega⟩
  | rangeHits d' lo' hi' =>
      simp only [countInterval?, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      exact ⟨rfl, fun w => by simp [holds]⟩

end AutomatonBound

/-- **Decidable Single-Bound Entailment (`automatonBoundEntails bc bp`)**:
certifies that child guard `bc` semantically implies parent guard `bp` on all byte words `w`. -/
def automatonBoundEntails (bc bp : AutomatonBound) : Bool :=
  bc.wellFormedB && bp.wellFormedB &&
  match bc.toAcceptDfa?, bp.toAcceptDfa? with
  | some dc, some dp => dfaSublanguageDecide dc dp
  | _, _ =>
      match bc.countInterval?, bp.countInterval? with
      | some (dc, loC, hiC), some (dp, loP, hiP) =>
          if loP = 0 then
            decide (hiC ≤ hiP) && dfaSublanguageDecide dp dc
          else
            decide (loP ≤ loC ∧ hiC ≤ hiP) &&
              dfaSublanguageDecide dc dp && dfaSublanguageDecide dp dc
      | _, _ => false

theorem automatonBoundEntails_sound {bc bp : AutomatonBound}
    (hent : automatonBoundEntails bc bp = true) (w : List UInt8)
    (hc : bc.holds w = true) :
    bp.holds w = true := by
  unfold automatonBoundEntails at hent
  simp only [Bool.and_eq_true] at hent
  rcases hent with ⟨⟨hwfCb, hwfPb⟩, hbody⟩
  have hwfC := AutomatonBound.dfa_wellFormed_of_wellFormedB hwfCb
  have hwfP := AutomatonBound.dfa_wellFormed_of_wellFormedB hwfPb
  cases hAccC : bc.toAcceptDfa? with
  | some dc =>
      cases hAccP : bp.toAcceptDfa? with
      | some dp =>
          rw [hAccC, hAccP] at hbody
          obtain ⟨_, hEqC⟩ := AutomatonBound.toAcceptDfa?_spec hwfC hAccC
          obtain ⟨_, hEqP⟩ := AutomatonBound.toAcceptDfa?_spec hwfP hAccP
          rw [hEqC] at hc
          rw [hEqP]
          exact dfaSublanguageDecide_sound hbody w hc
      | none =>
          have hCntC : bc.countInterval? = none := by cases bc <;> simp_all [AutomatonBound.toAcceptDfa?, AutomatonBound.countInterval?]
          simp [hAccC, hAccP, hCntC] at hbody
  | none =>
      have hCntCSome : (bc.countInterval?).isSome = true :=
        (AutomatonBound.toAcceptDfa?_none_iff_countInterval?_some bc).mp hAccC
      obtain ⟨⟨dc, loC, hiC⟩, hCntC⟩ := Option.isSome_iff_exists.mp hCntCSome
      cases hAccP : bp.toAcceptDfa? with
      | some _ =>
          have hCntP : bp.countInterval? = none := by cases bp <;> simp_all [AutomatonBound.toAcceptDfa?, AutomatonBound.countInterval?]
          simp [hAccC, hAccP, hCntC, hCntP] at hbody
      | none =>
          have hCntPSome : (bp.countInterval?).isSome = true :=
            (AutomatonBound.toAcceptDfa?_none_iff_countInterval?_some bp).mp hAccP
          obtain ⟨⟨dp, loP, hiP⟩, hCntP⟩ := Option.isSome_iff_exists.mp hCntPSome
          rw [hAccC, hAccP, hCntC, hCntP] at hbody
          obtain ⟨rfl, hSpecC⟩ := AutomatonBound.countInterval?_spec hCntC
          obtain ⟨rfl, hSpecP⟩ := AutomatonBound.countInterval?_spec hCntP
          obtain ⟨hloC, hhiC⟩ := (hSpecC w).mp hc
          rw [hSpecP]
          by_cases hloP0 : loP = 0
          · subst hloP0
            simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hbody
            have hle := hitCount_le_of_sublanguage hbody.2 w
            exact ⟨Nat.zero_le _, by omega⟩
          · simp only [hloP0, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hbody
            have heq := hitCount_eq_of_bislanguage hbody.1.2 hbody.2 w
            omega

theorem automatonBoundEntails_refl {b : AutomatonBound} (hwf : b.wellFormedB = true) :
    automatonBoundEntails b b = true := by
  have hd := AutomatonBound.dfa_wellFormed_of_wellFormedB hwf
  unfold automatonBoundEntails
  cases hAcc : b.toAcceptDfa? with
  | some dEff =>
      obtain ⟨hdEff, _⟩ := AutomatonBound.toAcceptDfa?_spec hd hAcc
      simp [hwf, dfaSublanguageDecide_refl hdEff]
  | none =>
      have hCntSome : (b.countInterval?).isSome = true :=
        (AutomatonBound.toAcceptDfa?_none_iff_countInterval?_some b).mp hAcc
      obtain ⟨⟨d, lo, hi⟩, hCnt⟩ := Option.isSome_iff_exists.mp hCntSome
      obtain ⟨rfl, _⟩ := AutomatonBound.countInterval?_spec hCnt
      by_cases hlo : lo = 0 <;>
        simp [hwf, hCnt, hlo, dfaSublanguageDecide_refl hd]

theorem automatonBoundEntails_trans {b₁ b₂ b₃ : AutomatonBound}
    (h12 : automatonBoundEntails b₁ b₂ = true)
    (h23 : automatonBoundEntails b₂ b₃ = true) :
    automatonBoundEntails b₁ b₃ = true := by
  unfold automatonBoundEntails at h12 h23 ⊢
  simp only [Bool.and_eq_true] at h12 h23
  rcases h12 with ⟨⟨hwf1b, hwf2b⟩, hb12⟩
  rcases h23 with ⟨⟨_, hwf3b⟩, hb23⟩
  have hwf1 := AutomatonBound.dfa_wellFormed_of_wellFormedB hwf1b
  have hwf2 := AutomatonBound.dfa_wellFormed_of_wellFormedB hwf2b
  have hwf3 := AutomatonBound.dfa_wellFormed_of_wellFormedB hwf3b
  simp only [hwf1b, hwf3b, Bool.true_and]
  cases hA1 : b₁.toAcceptDfa? with
  | some d1 =>
      cases hA2 : b₂.toAcceptDfa? with
      | some d2 =>
          cases hA3 : b₃.toAcceptDfa? with
          | some d3 =>
              rw [hA1, hA2] at hb12
              rw [hA2, hA3] at hb23
              obtain ⟨hd1, _⟩ := AutomatonBound.toAcceptDfa?_spec hwf1 hA1
              obtain ⟨hd2, _⟩ := AutomatonBound.toAcceptDfa?_spec hwf2 hA2
              obtain ⟨hd3, _⟩ := AutomatonBound.toAcceptDfa?_spec hwf3 hA3
              exact dfaSublanguageDecide_trans hd1 hd2 hd3 hb12 hb23
          | none =>
              have hC2 : b₂.countInterval? = none := by cases b₂ <;> simp_all [AutomatonBound.toAcceptDfa?, AutomatonBound.countInterval?]
              simp [hA2, hA3, hC2] at hb23
      | none =>
          have hC1 : b₁.countInterval? = none := by cases b₁ <;> simp_all [AutomatonBound.toAcceptDfa?, AutomatonBound.countInterval?]
          simp [hA1, hA2, hC1] at hb12
  | none =>
      have hC1s := (AutomatonBound.toAcceptDfa?_none_iff_countInterval?_some b₁).mp hA1
      obtain ⟨⟨d1, lo1, hi1⟩, hC1⟩ := Option.isSome_iff_exists.mp hC1s
      cases hA2 : b₂.toAcceptDfa? with
      | some _ =>
          have hC2 : b₂.countInterval? = none := by cases b₂ <;> simp_all [AutomatonBound.toAcceptDfa?, AutomatonBound.countInterval?]
          simp [hA1, hA2, hC1, hC2] at hb12
      | none =>
          have hC2s := (AutomatonBound.toAcceptDfa?_none_iff_countInterval?_some b₂).mp hA2
          obtain ⟨⟨d2, lo2, hi2⟩, hC2⟩ := Option.isSome_iff_exists.mp hC2s
          cases hA3 : b₃.toAcceptDfa? with
          | some _ =>
              have hC3 : b₃.countInterval? = none := by cases b₃ <;> simp_all [AutomatonBound.toAcceptDfa?, AutomatonBound.countInterval?]
              simp [hA2, hA3, hC2, hC3] at hb23
          | none =>
              have hC3s := (AutomatonBound.toAcceptDfa?_none_iff_countInterval?_some b₃).mp hA3
              obtain ⟨⟨d3, lo3, hi3⟩, hC3⟩ := Option.isSome_iff_exists.mp hC3s
              rw [hA1, hA2, hC1, hC2] at hb12
              rw [hA2, hA3, hC2, hC3] at hb23
              rw [hC1, hC3]
              obtain ⟨rfl, _⟩ := AutomatonBound.countInterval?_spec hC1
              obtain ⟨rfl, _⟩ := AutomatonBound.countInterval?_spec hC2
              obtain ⟨rfl, _⟩ := AutomatonBound.countInterval?_spec hC3
              by_cases hlo3 : lo3 = 0
              · simp only [hlo3, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hb23 ⊢
                by_cases hlo2 : lo2 = 0
                · simp only [hlo2, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hb12
                  exact ⟨by omega, dfaSublanguageDecide_trans hwf3 hwf2 hwf1 hb23.2 hb12.2⟩
                · simp only [hlo2, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hb12
                  exact ⟨by omega, dfaSublanguageDecide_trans hwf3 hwf2 hwf1 hb23.2 hb12.2⟩
              · simp only [hlo3, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hb23 ⊢
                have hlo2 : lo2 ≠ 0 := by omega
                simp only [hlo2, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hb12
                exact ⟨⟨⟨by omega, by omega⟩,
                  dfaSublanguageDecide_trans hwf1 hwf2 hwf3 hb12.1.2 hb23.1.2⟩,
                  dfaSublanguageDecide_trans hwf3 hwf2 hwf1 hb23.2 hb12.2⟩

/-- Guard-list attenuation: all bounds are well-formed and every parent guard is entailed by
some child guard. -/
def boundsAttenuate (childBounds parentBounds : List AutomatonBound) : Bool :=
  childBounds.all AutomatonBound.wellFormedB &&
  parentBounds.all AutomatonBound.wellFormedB &&
  parentBounds.all (fun bp => childBounds.any (fun bc => automatonBoundEntails bc bp))

theorem boundsAttenuate_sound {childBounds parentBounds : List AutomatonBound}
    (h : boundsAttenuate childBounds parentBounds = true) {w : List UInt8}
    (hc : ∀ bc ∈ childBounds, bc.holds w = true) :
    ∀ bp ∈ parentBounds, bp.holds w = true := by
  unfold boundsAttenuate at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
  intro bp hbp
  obtain ⟨bc, hbc, hent⟩ := h.2 bp hbp
  exact automatonBoundEntails_sound hent w (hc bc hbc)

theorem boundsAttenuate_refl {bounds : List AutomatonBound}
    (hwf : bounds.all AutomatonBound.wellFormedB = true) :
    boundsAttenuate bounds bounds = true := by
  unfold boundsAttenuate
  simp only [hwf, Bool.true_and, List.all_eq_true, List.any_eq_true]
  intro b hb
  exact ⟨b, hb, automatonBoundEntails_refl ((List.all_eq_true.mp hwf) b hb)⟩

theorem boundsAttenuate_trans {b₁ b₂ b₃ : List AutomatonBound}
    (h12 : boundsAttenuate b₁ b₂ = true)
    (h23 : boundsAttenuate b₂ b₃ = true) :
    boundsAttenuate b₁ b₃ = true := by
  unfold boundsAttenuate at h12 h23 ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h12 h23 ⊢
  refine ⟨⟨h12.1.1, h23.1.2⟩, fun bp₃ hbp₃ => ?_⟩
  obtain ⟨bp₂, hbp₂, hent23⟩ := h23.2 bp₃ hbp₃
  obtain ⟨bp₁, hbp₁, hent12⟩ := h12.2 bp₂ hbp₂
  exact ⟨bp₁, hbp₁, automatonBoundEntails_trans hent12 hent23⟩

/-! ### Redaction-Rule Fixed-Point Characterization & Attenuation (`redactRulesAttenuate`) -/

theorem occursInW_refl {Sym : Type} (P : List Sym) : OccursInW P P :=
  ⟨0, by simp, by simp⟩

theorem occursInW_trans {Sym : Type} {A B C : List Sym}
    (hab : OccursInW B A) (hbc : OccursInW C B) : OccursInW C A := by
  rcases hab with ⟨i, hlenAB, htakeAB⟩
  rcases hbc with ⟨j, hlenBC, htakeBC⟩
  refine ⟨j + i, by omega, ?_⟩
  have h1 : ((C.drop j).drop i).take A.length = A := by
    rw [← htakeBC, List.drop_take, List.take_take, Nat.min_eq_left (by omega)] at htakeAB
    exact htakeAB
  rwa [List.drop_drop] at h1

theorem absentW_of_occursInW {Sym : Type} {P_parent P_child w : List Sym}
    (hocc : OccursInW P_parent P_child) (habs : AbsentW w P_child) :
    AbsentW w P_parent := by
  intro i hsub
  exact let ⟨k, hk⟩ := occursInW_trans hocc ⟨i, hsub⟩; habs k hk

/-- Under `allRulesSafe rules = true`, `w = redactBytes rules w` holds iff every trigger pattern
`r.pat` (`r ∈ rules`) is absent from `w`. -/
theorem redactFixedPoint_iff_absent (rules : List (RedactRule UInt8))
    (hsafe : allRulesSafe rules = true) (w : List UInt8) :
    w = redactBytes rules w ↔ ∀ r ∈ rules, AbsentW w r.pat := by
  constructor
  · intro hfp r hr
    have hunpack := allRulesSafe_unpack hsafe r hr
    have hsc := redactBytes_scrubs_all rules r hr hunpack.1 hunpack.2 w
    rwa [← hfp] at hsc
  · intro habs
    exact (redactBytes_preserves_clean rules w habs).symm

/-- Decidable redaction-policy attenuation: both policies satisfy `allRulesSafe`, and every parent
secret pattern contains (or equals) some child secret pattern, so child fixed points are automatically
parent fixed points. -/
def redactRulesAttenuate (childRules parentRules : List (RedactRule UInt8)) : Bool :=
  allRulesSafe childRules &&
  allRulesSafe parentRules &&
  parentRules.all (fun rp => childRules.any (fun rc => occursInBool rp.pat rc.pat))

theorem redactRulesAttenuate_sound {childRules parentRules : List (RedactRule UInt8)}
    (hatt : redactRulesAttenuate childRules parentRules = true) {w : List UInt8}
    (hfp : w = redactBytes childRules w) :
    allRulesSafe parentRules = true ∧
    w = redactBytes parentRules w ∧
    ∀ rp ∈ parentRules, AbsentW w rp.pat := by
  unfold redactRulesAttenuate at hatt
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, occursInBool_iff] at hatt
  rcases hatt with ⟨⟨hsafeC, hsafeP⟩, hcov⟩
  have habsC := (redactFixedPoint_iff_absent childRules hsafeC w).mp hfp
  have habsP : ∀ rp ∈ parentRules, AbsentW w rp.pat := by
    intro rp hrp
    obtain ⟨rc, hrc, hocc⟩ := hcov rp hrp
    exact absentW_of_occursInW hocc (habsC rc hrc)
  exact ⟨hsafeP, (redactFixedPoint_iff_absent parentRules hsafeP w).mpr habsP, habsP⟩

theorem redactRulesAttenuate_refl {rules : List (RedactRule UInt8)}
    (hsafe : allRulesSafe rules = true) :
    redactRulesAttenuate rules rules = true := by
  unfold redactRulesAttenuate
  simp only [hsafe, Bool.true_and, List.all_eq_true, List.any_eq_true, occursInBool_iff]
  intro r hr
  exact ⟨r, hr, occursInW_refl r.pat⟩

theorem redactRulesAttenuate_trans {r₁ r₂ r₃ : List (RedactRule UInt8)}
    (h12 : redactRulesAttenuate r₁ r₂ = true)
    (h23 : redactRulesAttenuate r₂ r₃ = true) :
    redactRulesAttenuate r₁ r₃ = true := by
  unfold redactRulesAttenuate at h12 h23 ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, occursInBool_iff] at h12 h23 ⊢
  refine ⟨⟨h12.1.1, h23.1.2⟩, fun rp₃ hrp₃ => ?_⟩
  obtain ⟨rp₂, hrp₂, hocc23⟩ := h23.2 rp₃ hrp₃
  obtain ⟨rp₁, hrp₁, hocc12⟩ := h12.2 rp₂ hrp₂
  exact ⟨rp₁, hrp₁, occursInW_trans hocc12 hocc23⟩

/-! ### Sub-Grammar Monotonicity, `GrammarPolicy`, & Capstone No-Escalation Theorems -/

/-- General rule-inclusion monotonicity for `AttrStackReplay`: if `g₁` and `g₂` share `termVal` and
`evalOp` and `g₁.rules ⊆ g₂.rules`, every replay in `g₁` replays identically in `g₂` with the
exact same synthesized AST `ast`. -/
theorem attrStackReplay_mono_rules {T NT SemOp Val : Type}
    {g₁ g₂ : AttrCfg T NT SemOp Val}
    (hterm : g₁.termVal = g₂.termVal)
    (heval : g₁.evalOp = g₂.evalOp)
    (hsub : ∀ r ∈ g₁.rules, r ∈ g₂.rules)
    {rs : List (AttrRule T NT SemOp)} {w : List T}
    {cstk : List (WorkItem T NT SemOp)} {vstk : List Val} {ast : Val}
    (h : AttrStackReplay g₁ rs w cstk vstk ast) :
    AttrStackReplay g₂ rs w cstk vstk ast := by
  induction h with
  | done ast => exact .done ast
  | term t _ ih => rw [hterm] at ih; exact .term t ih
  | rule hr _ ih => exact .rule (hsub _ hr) ih
  | reduce op k hlen _ ih => rw [heval] at ih; exact .reduce op k hlen ih

theorem attrReplay_mono_rules {T NT SemOp Val : Type}
    {g₁ g₂ : AttrCfg T NT SemOp Val}
    (hinit : g₁.initial = g₂.initial)
    (hterm : g₁.termVal = g₂.termVal)
    (heval : g₁.evalOp = g₂.evalOp)
    (hsub : ∀ r ∈ g₁.rules, r ∈ g₂.rules)
    {rs : List (AttrRule T NT SemOp)} {w : List T} {ast : Val}
    (h : AttrReplay g₁ rs w ast) :
    AttrReplay g₂ rs w ast := by
  unfold AttrReplay at h ⊢
  rw [← hinit]
  exact attrStackReplay_mono_rules hterm heval hsub h

/-- Shared first-order AST operator interpretation (`termVal`, `evalOp`), keeping `GrammarPolicy`
100% first-order and guaranteeing semantic evaluation preservation across sub-grammars by type. -/
structure AttrSemantics (SemOp Val : Type) where
  termVal : UInt8 → Val
  evalOp  : SemOp → List Val → Val

/-- **Syntactic & Automata-Predicated Capability Policy (`GrammarPolicy`)**:
combines an unambiguous LL(1) attributed grammar `(initial, rules)` over `sem`, canonical
`SafeReplacement` `RedactRule`s (`w = redactBytes redactRules w`), and `List AutomatonBound`. -/
structure GrammarPolicy (NT : Type) {SemOp Val : Type} (sem : AttrSemantics SemOp Val) where
  initial     : NT
  rules       : List (AttrRule UInt8 NT SemOp)
  redactRules : List (RedactRule UInt8)
  bounds      : List AutomatonBound

namespace GrammarPolicy

/-- Induced `AttrCfg UInt8 NT SemOp Val` of a `GrammarPolicy`. -/
def cfg {NT SemOp Val : Type} {sem : AttrSemantics SemOp Val}
    (pol : GrammarPolicy NT sem) : AttrCfg UInt8 NT SemOp Val where
  initial := pol.initial
  rules   := pol.rules
  termVal := sem.termVal
  evalOp  := sem.evalOp

/-- Executable well-formedness check for a standalone `GrammarPolicy`. -/
def wellFormedB {NT SemOp Val : Type} [DecidableEq NT] {sem : AttrSemantics SemOp Val}
    (pol : GrammarPolicy NT sem) : Bool :=
  ll1Deterministic pol.cfg &&
  allRulesSafe pol.redactRules &&
  pol.bounds.all AutomatonBound.wellFormedB

end GrammarPolicy

/-- **Semantic Admission Judgment (`PolicyAdmits pol w rs ast`)**:
payload `w` and rule certificate `rs` extract unique `ast` under `pol` when:
1. `pol.cfg` is LL(1) deterministic,
2. `pol.redactRules` satisfies `allRulesSafe` and `w` is already clean (`w = redactBytes rules w`),
3. every `AutomatonBound` guard in `pol.bounds` is well-formed and holds on `w`, and
4. `AttrReplay pol.cfg rs w ast` holds. -/
def PolicyAdmits {NT SemOp Val : Type} [DecidableEq NT] {sem : AttrSemantics SemOp Val}
    (pol : GrammarPolicy NT sem) (w : List UInt8)
    (rs : List (AttrRule UInt8 NT SemOp)) (ast : Val) : Prop :=
  ll1Deterministic pol.cfg = true ∧
  allRulesSafe pol.redactRules = true ∧
  w = redactBytes pol.redactRules w ∧
  (∀ b ∈ pol.bounds, b.holds w = true) ∧
  AttrReplay pol.cfg rs w ast ∧
  (∀ b ∈ pol.bounds, b.wellFormedB = true)

/-- Executable boolean verifier equivalent to `PolicyAdmits`. -/
def execPolicyVerify {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] [DecidableEq Val]
    {sem : AttrSemantics SemOp Val}
    (pol : GrammarPolicy NT sem) (w : List UInt8)
    (rs : List (AttrRule UInt8 NT SemOp)) (ast : Val) : Bool :=
  ll1Deterministic pol.cfg &&
  allRulesSafe pol.redactRules &&
  decide (w = redactBytes pol.redactRules w) &&
  pol.bounds.all (fun b => b.holds w) &&
  decide (execAttrReplay pol.cfg rs w = some ast) &&
  pol.bounds.all AutomatonBound.wellFormedB

theorem execPolicyVerify_iff {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] [DecidableEq Val]
    {sem : AttrSemantics SemOp Val}
    (pol : GrammarPolicy NT sem) (w : List UInt8)
    (rs : List (AttrRule UInt8 NT SemOp)) (ast : Val) :
    execPolicyVerify pol w rs ast = true ↔ PolicyAdmits pol w rs ast := by
  simp only [execPolicyVerify, PolicyAdmits, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, execAttrReplay_iff]
  tauto

/-- **Executable Strict Syntactic & Automata Capability Attenuator (`grammarPolicyAttenuates`)**:
checks LL(1) determinacy of both child and parent, identical start nonterminal, rule-subset
sub-grammar inclusion (`child.rules ⊆ parent.rules`), redaction pattern coverage, and
product-DFA / interval guard entailment across `bounds`. -/
def grammarPolicyAttenuates {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp]
    {sem : AttrSemantics SemOp Val}
    (child parent : GrammarPolicy NT sem) : Bool :=
  ll1Deterministic child.cfg &&
  ll1Deterministic parent.cfg &&
  decide (child.initial = parent.initial) &&
  listSubset child.rules parent.rules &&
  redactRulesAttenuate child.redactRules parent.redactRules &&
  boundsAttenuate child.bounds parent.bounds

/-- **`grammarPolicyAttenuates_sound`** — Capstone Monotonicity & No-Escalation Theorem:
If `grammarPolicyAttenuates child parent = true`, then EVERY byte payload `w` and `ast` admitted
by `child` is provably admitted by `parent` (`PolicyAdmits parent w rs ast`), scrubs all parent
secret patterns, lies in `parent.cfg.toCfg.language`, AND extracts the **identical unique AST**
(`∀ rs' ast', AttrReplay parent.cfg rs' w ast' → ast' = ast ∧ rs' = rs`). -/
theorem grammarPolicyAttenuates_sound {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp]
    {sem : AttrSemantics SemOp Val}
    {child parent : GrammarPolicy NT sem}
    (hatt : grammarPolicyAttenuates child parent = true)
    {w : List UInt8} {rs : List (AttrRule UInt8 NT SemOp)} {ast : Val}
    (hadm : PolicyAdmits child w rs ast) :
    PolicyAdmits parent w rs ast ∧
    (∀ rp ∈ parent.redactRules, AbsentW w rp.pat) ∧
    w ∈ parent.cfg.toCfg.language ∧
    (∀ (rs' : List (AttrRule UInt8 NT SemOp)) (ast' : Val),
      AttrReplay parent.cfg rs' w ast' → ast' = ast ∧ rs' = rs) := by
  unfold grammarPolicyAttenuates at hatt
  simp only [Bool.and_eq_true, decide_eq_true_eq, listSubset_iff] at hatt
  rcases hatt with ⟨⟨⟨⟨⟨_, hll1P⟩, hinit⟩, hsubRules⟩, hredAtt⟩, hbndAtt⟩
  rcases hadm with ⟨_, _, hfpC, hbndC, hrepC, _⟩
  obtain ⟨hsafeP, hfpP, habsP⟩ := redactRulesAttenuate_sound hredAtt hfpC
  have hbndP := boundsAttenuate_sound hbndAtt hbndC
  have hwfBndP : ∀ b ∈ parent.bounds, b.wellFormedB = true := by
    unfold boundsAttenuate at hbndAtt
    simp only [Bool.and_eq_true, List.all_eq_true] at hbndAtt
    exact hbndAtt.1.2
  have hrepP : AttrReplay parent.cfg rs w ast :=
    attrReplay_mono_rules (g₁ := child.cfg) (g₂ := parent.cfg) hinit rfl rfl hsubRules hrepC
  exact ⟨⟨hll1P, hsafeP, hfpP, hbndP, hrepP, hwfBndP⟩,
         habsP,
         attrReplay_mem_language hrepP,
         fun rs' ast' hrep' => attrReplay_unique_of_ll1 parent.cfg hll1P hrep' hrepP⟩

theorem grammarPolicyAttenuates_refl {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp]
    {sem : AttrSemantics SemOp Val}
    {pol : GrammarPolicy NT sem}
    (hwf : pol.wellFormedB = true) :
    grammarPolicyAttenuates pol pol = true := by
  unfold GrammarPolicy.wellFormedB at hwf
  simp only [Bool.and_eq_true] at hwf
  rcases hwf with ⟨⟨hll1, hsafe⟩, hbnds⟩
  unfold grammarPolicyAttenuates
  simp [hll1, listSubset_iff, redactRulesAttenuate_refl hsafe, boundsAttenuate_refl hbnds]

/-- **`grammarPolicyAttenuates_trans`** — Exact Boolean Transitivity of Capability Attenuation:
arbitrary multi-hop capability delegation chains compose transitively without escalation. -/
theorem grammarPolicyAttenuates_trans {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp]
    {sem : AttrSemantics SemOp Val}
    {young middle old : GrammarPolicy NT sem}
    (h12 : grammarPolicyAttenuates young middle = true)
    (h23 : grammarPolicyAttenuates middle old = true) :
    grammarPolicyAttenuates young old = true := by
  unfold grammarPolicyAttenuates at h12 h23 ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, listSubset_iff] at h12 h23 ⊢
  rcases h12 with ⟨⟨⟨⟨⟨hll1Y, _⟩, hinit12⟩, hsub12⟩, hred12⟩, hbnd12⟩
  rcases h23 with ⟨⟨⟨⟨⟨_, hll1O⟩, hinit23⟩, hsub23⟩, hred23⟩, hbnd23⟩
  exact ⟨⟨⟨⟨⟨hll1Y, hll1O⟩, hinit12.trans hinit23⟩,
    fun r hr => hsub23 r (hsub12 r hr)⟩,
    redactRulesAttenuate_trans hred12 hred23⟩,
    boundsAttenuate_trans hbnd12 hbnd23⟩

/-- Executable top-down delegation chain checker from `rootPolicy` down to `leafPolicy`. -/
def policyChainAttenuates {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp]
    {sem : AttrSemantics SemOp Val} :
    List (GrammarPolicy NT sem) → Bool
  | [] => false
  | [pol] => pol.wellFormedB
  | parent :: child :: rest =>
      grammarPolicyAttenuates child parent && policyChainAttenuates (child :: rest)

theorem policyChainAttenuates_leaf_to_root {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp]
    {sem : AttrSemantics SemOp Val} :
    ∀ (rootPol leafPol : GrammarPolicy NT sem) (mid : List (GrammarPolicy NT sem)),
      policyChainAttenuates (rootPol :: (mid ++ [leafPol])) = true →
      grammarPolicyAttenuates leafPol rootPol = true
  | rootPol, leafPol, [], h => by
      change (grammarPolicyAttenuates leafPol rootPol && leafPol.wellFormedB) = true at h
      exact (Bool.and_eq_true _ _).mp h |>.1
  | rootPol, leafPol, nextPol :: rest, h => by
      change (grammarPolicyAttenuates nextPol rootPol &&
        policyChainAttenuates (nextPol :: (rest ++ [leafPol]))) = true at h
      obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
      have htail := policyChainAttenuates_leaf_to_root nextPol leafPol rest h2
      exact grammarPolicyAttenuates_trans htail h1

private theorem getLast?_cons_snoc {α : Type} (a x : α) :
    ∀ (xs : List α), (a :: (xs ++ [x])).getLast? = some x
  | [] => rfl
  | b :: rest => by
      rw [List.cons_append, List.getLast?_cons_cons]
      exact getLast?_cons_snoc b x rest

/-- Multi-hop delegation chain soundness: if `chain` starts at `rootPol` and ends at `leafPol`
with `policyChainAttenuates chain = true`, every payload admitted by `leafPol` is admitted by
`rootPol` with the identical unique AST (`ast' = ast`). -/
theorem policyChainAttenuates_sound {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp]
    {sem : AttrSemantics SemOp Val}
    {chain : List (GrammarPolicy NT sem)}
    {rootPol leafPol : GrammarPolicy NT sem}
    (hhead : chain.head? = some rootPol)
    (hlast : chain.getLast? = some leafPol)
    (hchain : policyChainAttenuates chain = true)
    {w : List UInt8} {rs : List (AttrRule UInt8 NT SemOp)} {ast : Val}
    (hadm : PolicyAdmits leafPol w rs ast) :
    PolicyAdmits rootPol w rs ast ∧
    (∀ rp ∈ rootPol.redactRules, AbsentW w rp.pat) ∧
    w ∈ rootPol.cfg.toCfg.language ∧
    (∀ (rs' : List (AttrRule UInt8 NT SemOp)) (ast' : Val),
      AttrReplay rootPol.cfg rs' w ast' → ast' = ast ∧ rs' = rs) := by
  cases chain with
  | nil => simp at hhead
  | cons hd tl =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      cases tl using List.reverseRecOn with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst hlast
          simp only [policyChainAttenuates] at hchain
          exact grammarPolicyAttenuates_sound (grammarPolicyAttenuates_refl hchain) hadm
      | append_singleton mid lastElem =>
          rw [getLast?_cons_snoc] at hlast
          injection hlast with hlastEq
          subst hlastEq
          have hatt := policyChainAttenuates_leaf_to_root hd lastElem mid hchain
          exact grammarPolicyAttenuates_sound hatt hadm

/-! ### Weld to `TypedAuthorization.Capability` & `Capability.Lineage` -/

set_option linter.dupNamespace false in
/-- A first-order `Capability kind` paired with a `GrammarPolicy` constraining payload syntax,
secret absence, and automaton hit bounds. -/
structure GrammarTypedCapability (kind : ResourceKind) (NT : Type)
    {SemOp Val : Type} (sem : AttrSemantics SemOp Val) where
  capability : Capability kind
  policy     : GrammarPolicy NT sem

/-- Proof-relevant multi-hop lineage welding `TypedAuthorization.Capability.Lineage` with
`grammarPolicyAttenuates` on every delegation/attenuation edge. -/
inductive GrammarCapLineage {kind : ResourceKind} {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] {sem : AttrSemantics SemOp Val}
    (parentage : Parentage) :
    GrammarTypedCapability kind NT sem → Type
  | root (gc : GrammarTypedCapability kind NT sem)
      (parentNone : gc.capability.parent = none)
      (rootSelf : gc.capability.root = gc.capability.id)
      (wf : gc.policy.wellFormedB = true) :
      GrammarCapLineage parentage gc
  | attenuate (child parent : GrammarTypedCapability kind NT sem)
      (parentLineage : GrammarCapLineage parentage parent)
      (capEdge : child.capability.StrictAttenuates parent.capability parentage)
      (polEdge : grammarPolicyAttenuates child.policy parent.policy = true) :
      GrammarCapLineage parentage child
  | delegate (child parent : GrammarTypedCapability kind NT sem)
      (request : Request kind)
      (parentLineage : GrammarCapLineage parentage parent)
      (shape : CredentialAuthorityFamily.DelegationShape request child.capability parent.capability parentage)
      (polEdge : grammarPolicyAttenuates child.policy parent.policy = true) :
      GrammarCapLineage parentage child

def GrammarCapLineage.rootCap {kind : ResourceKind} {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] {sem : AttrSemantics SemOp Val}
    {parentage : Parentage} {gc : GrammarTypedCapability kind NT sem} :
    GrammarCapLineage parentage gc → GrammarTypedCapability kind NT sem
  | .root rootGc _ _ _ => rootGc
  | .attenuate _ _ p _ _ => p.rootCap
  | .delegate _ _ _ p _ _ => p.rootCap

theorem GrammarCapLineage.attenuates_root {kind : ResourceKind} {NT SemOp Val : Type}
    [DecidableEq NT] [DecidableEq SemOp] {sem : AttrSemantics SemOp Val}
    {parentage : Parentage} {gc : GrammarTypedCapability kind NT sem}
    (lin : GrammarCapLineage parentage gc) :
    Capability.LineageBounds gc.capability lin.rootCap.capability parentage ∧
    grammarPolicyAttenuates gc.policy lin.rootCap.policy = true := by
  induction lin with
  | root rootGc _ _ wf =>
      exact ⟨Capability.LineageBounds.refl rootGc.capability parentage,
             grammarPolicyAttenuates_refl wf⟩
  | attenuate child parent _ capEdge polEdge ih =>
      exact ⟨capEdge.payload.lineageBounds.trans ih.1,
             grammarPolicyAttenuates_trans polEdge ih.2⟩
  | delegate child parent _ _ shape polEdge ih =>
      exact ⟨shape.payload.lineageBounds.trans ih.1,
             grammarPolicyAttenuates_trans polEdge ih.2⟩

/-! ## §4. Concrete 3-Hop Capability Hierarchy & 4 Privilege-Escalation Falsifiers (`by decide`) -/

/-! ### 4.1 Concrete Policy DFAs (`acceptAllDfa`, `noSkDashDfa`, `noSqlDropDfa`, `countOpBraceDfa`) -/

/-- 1-state universal DFA accepting all byte strings $\Sigma^*$. -/
def acceptAllDfa : DfaSpec where
  states    := 1
  initial   := 0
  accepting := [true]
  delta     := List.replicate 256 0

/-- 4-state padded-complement DFA `Absent("sk-")` (`'s'=115, 'k'=107, '-'=45`). -/
def noSkDashDfa : DfaSpec where
  states    := 4
  initial   := 0
  accepting := [true, true, true, false]
  delta     := (List.range (4 * 256)).map fun key =>
    let s := key / 256
    let b := key % 256
    if s = 3 then 3
    else if s = 2 ∧ b = 45 then 3
    else if s = 1 ∧ b = 107 then 2
    else if b = 115 then 1
    else 0

/-- 6-state padded-complement DFA `Absent("DROP ")` (`'D'=68, 'R'=82, 'O'=79, 'P'=80, ' '=32`). -/
def noSqlDropDfa : DfaSpec where
  states    := 6
  initial   := 0
  accepting := [true, true, true, true, true, false]
  delta     := (List.range (6 * 256)).map fun key =>
    let s := key / 256
    let b := key % 256
    if s = 5 then 5
    else if s = 4 ∧ b = 32 then 5
    else if s = 3 ∧ b = 80 then 4
    else if s = 2 ∧ b = 79 then 3
    else if s = 1 ∧ b = 82 then 2
    else if b = 68 then 1
    else 0

/-- 3-state padded-complement DFA `Absent("$(")` (`'$'=36, '('=40`, shell command substitution). -/
def noShellSubDfa : DfaSpec where
  states    := 3
  initial   := 0
  accepting := [true, true, false]
  delta     := (List.range (3 * 256)).map fun key =>
    let s := key / 256
    let b := key % 256
    if s = 2 then 2
    else if s = 1 ∧ b = 40 then 2
    else if b = 36 then 1
    else 0

/-- 2-state JSON object-brace `{` (`123`) operation counter DFA (`countOpBraceDfa`).
Every `'{'` transitions to accepting state `1`, all other bytes transition to state `0`. -/
def countOpBraceDfa : DfaSpec where
  states    := 2
  initial   := 0
  accepting := [false, true]
  delta     := (List.range (2 * 256)).map fun key =>
    if key % 256 = 123 then 1 else 0

set_option maxRecDepth 40000 in
theorem policyDfas_wellFormed :
    acceptAllDfa.WellFormed ∧
    noSkDashDfa.WellFormed ∧
    noSqlDropDfa.WellFormed ∧
    noShellSubDfa.WellFormed ∧
    countOpBraceDfa.WellFormed := by
  simp only [← DfaSpec.wellFormedB_iff]
  decide

/-! ### 4.2 Sub-Grammar Family over `(CapNT, CapOp, MiniValue)` -/

inductive CapNT where
  | Root
  | Expr
  | AfterCommaT
  | BatchTail
  | ToolName
  | TargetPath
  | Slug
  | BoundedAmt
  | AmtTail1
  | AmtTail2
  | WS
  deriving DecidableEq, Repr

inductive CapOp where
  | passAt       : Nat → CapOp
  | unitOp       : CapOp
  | constBytes   : List UInt8 → CapOp
  | prefixSlug   : List UInt8 → CapOp
  | slugNil      : CapOp
  | slugCons     : UInt8 → CapOp
  | natZero      : CapOp
  | amtHead      : Nat → CapOp
  | digitsNil    : CapOp
  | digitsCons   : Nat → CapOp
  | digitsSingle : Nat → CapOp
  | mkExprObj    : CapOp
  | mkAfterNorm  : CapOp
  | mkDupFirst   : CapOp
  | mkDupLast    : CapOp
  | mkBatchHead  : CapOp
  | mkBatchTail  : CapOp
  | batchNil     : CapOp
  deriving DecidableEq, Repr

def evalCapOp : CapOp → List MiniValue → MiniValue
  | .passAt i, vs => vs.getD i .vUnit
  | .unitOp, _ => .vUnit
  | .constBytes bs, _ => .vBytes bs
  | .prefixSlug pfx, vs =>
      match vs.getLast? with
      | some (.vBytes slug) => .vBytes (pfx ++ slug)
      | _ => .vBytes pfx
  | .slugNil, _ => .vBytes []
  | .slugCons b, vs =>
      match vs.getD 1 (.vBytes []) with
      | .vBytes bs => .vBytes (b :: bs)
      | _ => .vBytes [b]
  | .natZero, _ => .vNat 0
  | .amtHead d0, vs =>
      match vs.getD 1 (.vDigits []) with
      | .vDigits ds => .vNat ((d0 :: ds).foldl (fun acc d => acc * 10 + d) 0)
      | _ => .vNat d0
  | .digitsNil, _ => .vDigits []
  | .digitsCons d, vs =>
      match vs.getD 1 (.vDigits []) with
      | .vDigits ds => .vDigits (d :: ds)
      | _ => .vDigits [d]
  | .digitsSingle d, _ => .vDigits [d]
  | .mkAfterNorm, vs =>
      -- `"arget\"" WS ":" WS "\"" TargetPath "\"" WS "," WS "\"amount\"" WS ":" WS BoundedAmt WS "}"`
      -- indices: 0..5 = `arget"`, 6=WS, 7=`:`, 8=WS, 9=`"`, 10=TargetPath, 11=`"`, 12=WS, 13=`,`, 14=WS,
      -- 15..22 = `"amount"`, 23=WS, 24=`:`, 25=WS, 26=BoundedAmt, 27=WS, 28=`}`
      match vs.getD 10 (.vBytes []), vs.getD 26 (.vNat 0) with
      | .vBytes tgt, .vNat amt => .vBatchCons (.vBytes tgt) (.vNat amt)
      | _, _ => .vUnit
  | .mkDupFirst, vs =>
      -- `"ool\"" WS ":" WS "\"" ToolName "\"" WS "," WS "\"target\"" WS ":" WS "\"" TargetPath "\"" WS "," WS "\"amount\"" WS ":" WS BoundedAmt WS "}"`
      -- indices: 0..3 = `ool"`, 4=WS, 5=`:`, 6=WS, 7=`"`, 8=Tool2, 9=`"`, 10=WS, 11=`,`, 12=WS,
      -- 13..20 = `"target"`, 21=WS, 22=`:`, 23=WS, 24=`"`, 25=TargetPath, 26=`"`, 27=WS, 28=`,`, 29=WS,
      -- 30..37 = `"amount"`, 38=WS, 39=`:`, 40=WS, 41=BoundedAmt, 42=WS, 43=`}`
      match vs.getD 25 (.vBytes []), vs.getD 41 (.vNat 0) with
      | .vBytes tgt, .vNat amt => .vBatchCons (.vBytes tgt) (.vNat amt)
      | _, _ => .vUnit
  | .mkDupLast, vs =>
      -- Carry `Tool2` so outer `.mkExprObj` selects `Tool2` instead of `Tool1`!
      match vs.getD 8 (.vBytes []), vs.getD 25 (.vBytes []), vs.getD 41 (.vNat 0) with
      | .vBytes tool2, .vBytes tgt, .vNat amt =>
          .vBatchCons (.vBytes tool2) (.vBatchCons (.vBytes tgt) (.vNat amt))
      | _, _, _ => .vUnit
  | .mkExprObj, vs =>
      -- `"{" WS "\"tool\"" WS ":" WS "\"" ToolName "\"" WS "," WS "\"t" AfterCommaT`
      -- indices: 0=`{`, 1=WS, 2..7=`"tool"`, 8=WS, 9=`:`, 10=WS, 11=`"`, 12=ToolName,
      -- 13=`"`, 14=WS, 15=`,`, 16=WS, 17=`"`, 18=`t`, 19=AfterCommaT
      match vs.getD 12 (.vBytes []), vs.getD 19 .vUnit with
      | .vBytes tool1, .vBatchCons (.vBytes tgt) (.vNat amt) =>
          .vToolCall tool1 tgt amt
      | _, .vBatchCons (.vBytes tool2) (.vBatchCons (.vBytes tgt) (.vNat amt)) =>
          .vToolCall tool2 tgt amt
      | _, _ => .vUnit
  | .mkBatchHead, vs =>
      -- `"[" WS Expr WS BatchTail "]"` -> indices: 2=Expr, 4=BatchTail
      .vBatchCons (vs.getD 2 .vUnit) (vs.getD 4 .vBatchNil)
  | .mkBatchTail, vs =>
      -- `"," WS Expr WS BatchTail` -> indices: 2=Expr, 4=BatchTail
      .vBatchCons (vs.getD 2 .vUnit) (vs.getD 4 .vBatchNil)
  | .batchNil, _ => .vBatchNil

def capSemantics : AttrSemantics CapOp MiniValue where
  termVal := MiniValue.vByte
  evalOp  := evalCapOp

def capLit (s : String) : List (Symbol UInt8 CapNT) :=
  (asciiBytes s).map (Symbol.terminal (N := CapNT))

/-- Compact slug character set (`a..z`, `0..9`, `_`, `-`). -/
def capSlugBytes : List UInt8 :=
  (List.range 26).map (fun k => UInt8.ofNat (0x61 + k)) ++
  (List.range 10).map (fun k => UInt8.ofNat (0x30 + k)) ++
  [0x5F, 0x2D]

-- Individual named capability rules for modular sub-grammar composition:
def rToolRead : AttrRule UInt8 CapNT CapOp :=
  ⟨.ToolName, capLit "read_doc", .constBytes (asciiBytes "read_doc")⟩

def rToolPatch : AttrRule UInt8 CapNT CapOp :=
  ⟨.ToolName, capLit "patch_atom", .constBytes (asciiBytes "patch_atom")⟩

def rToolAudit : AttrRule UInt8 CapNT CapOp :=
  ⟨.ToolName, capLit "audit_log", .constBytes (asciiBytes "audit_log")⟩

def rToolDeploy : AttrRule UInt8 CapNT CapOp :=
  ⟨.ToolName, capLit "deploy_svc", .constBytes (asciiBytes "deploy_svc")⟩

/-- Unauthorized destructive tool production (`"wipe_prod"`). -/
def rToolWipeProd : AttrRule UInt8 CapNT CapOp :=
  ⟨.ToolName, capLit "wipe_prod", .constBytes (asciiBytes "wipe_prod")⟩

def rTgtSandbox : AttrRule UInt8 CapNT CapOp :=
  ⟨.TargetPath, capLit "sandbox/" ++ [.nonterminal .Slug], .prefixSlug (asciiBytes "sandbox/")⟩

def rTgtDocs : AttrRule UInt8 CapNT CapOp :=
  ⟨.TargetPath, capLit "docs/" ++ [.nonterminal .Slug], .prefixSlug (asciiBytes "docs/")⟩

def rTgtVault : AttrRule UInt8 CapNT CapOp :=
  ⟨.TargetPath, capLit "vault/" ++ [.nonterminal .Slug], .prefixSlug (asciiBytes "vault/")⟩

def rAfterNorm : AttrRule UInt8 CapNT CapOp :=
  let t := Symbol.terminal (T := UInt8) (N := CapNT)
  let nt := Symbol.nonterminal (T := UInt8) (N := CapNT)
  ⟨.AfterCommaT,
    capLit "arget\"" ++ [nt .WS, t 0x3A, nt .WS, t 0x22, nt .TargetPath, t 0x22, nt .WS, t 0x2C, nt .WS] ++
    capLit "\"amount\"" ++ [nt .WS, t 0x3A, nt .WS, nt .BoundedAmt, nt .WS, t 0x7D],
    .mkAfterNorm⟩

def rDupKeyFirstWins : AttrRule UInt8 CapNT CapOp :=
  let t := Symbol.terminal (T := UInt8) (N := CapNT)
  let nt := Symbol.nonterminal (T := UInt8) (N := CapNT)
  ⟨.AfterCommaT,
    capLit "ool\"" ++ [nt .WS, t 0x3A, nt .WS, t 0x22, nt .ToolName, t 0x22, nt .WS, t 0x2C, nt .WS] ++
    capLit "\"target\"" ++ [nt .WS, t 0x3A, nt .WS, t 0x22, nt .TargetPath, t 0x22, nt .WS, t 0x2C, nt .WS] ++
    capLit "\"amount\"" ++ [nt .WS, t 0x3A, nt .WS, nt .BoundedAmt, nt .WS, t 0x7D],
    .mkDupFirst⟩

def rDupKeyLastWins : AttrRule UInt8 CapNT CapOp :=
  { rDupKeyFirstWins with op := .mkDupLast }

def capCoreFrameRules : List (AttrRule UInt8 CapNT CapOp) :=
  let t := Symbol.terminal (T := UInt8) (N := CapNT)
  let nt := Symbol.nonterminal (T := UInt8) (N := CapNT)
  [ ⟨.Root, [nt .WS, nt .Expr, nt .WS], .passAt 1⟩,
    ⟨.Expr,
      [t 0x7B, nt .WS] ++ capLit "\"tool\"" ++
      [nt .WS, t 0x3A, nt .WS, t 0x22, nt .ToolName, t 0x22, nt .WS, t 0x2C, nt .WS, t 0x22, t 0x74, nt .AfterCommaT],
      .mkExprObj⟩,
    rAfterNorm,
    ⟨.Expr, [t 0x5B, nt .WS, nt .Expr, nt .WS, nt .BatchTail, t 0x5D], .mkBatchHead⟩,
    ⟨.BatchTail, [t 0x2C, nt .WS, nt .Expr, nt .WS, nt .BatchTail], .mkBatchTail⟩,
    ⟨.BatchTail, [], .batchNil⟩,
    ⟨.WS, [t 0x20, nt .WS], .unitOp⟩,
    ⟨.WS, [t 0x0A, nt .WS], .unitOp⟩,
    ⟨.WS, [], .unitOp⟩,
    ⟨.Slug, [], .slugNil⟩,
    ⟨.BoundedAmt, [t 0x30], .natZero⟩,
    ⟨.AmtTail1, [], .digitsNil⟩,
    ⟨.AmtTail2, [], .digitsNil⟩ ] ++
  (capSlugBytes.map fun b => ⟨.Slug, [t b, nt .Slug], .slugCons b⟩)

def amtHeadRules (maxFirstDigit : Nat) : List (AttrRule UInt8 CapNT CapOp) :=
  (List.range maxFirstDigit).map fun k =>
    let d := k + 1
    ⟨.BoundedAmt, [.terminal (UInt8.ofNat (0x30 + d)), .nonterminal .AmtTail1], .amtHead d⟩

def amtTail1DigitRules : List (AttrRule UInt8 CapNT CapOp) :=
  (List.range 10).map fun d =>
    ⟨.AmtTail1, [.terminal (UInt8.ofNat (0x30 + d)), .nonterminal .AmtTail2], .digitsCons d⟩

def amtTail2DigitRules : List (AttrRule UInt8 CapNT CapOp) :=
  (List.range 10).map fun d =>
    ⟨.AmtTail2, [.terminal (UInt8.ofNat (0x30 + d))], .digitsSingle d⟩

/-! ### 4.3 3-Hop Delegation Chain: `rootCapPolicy → serviceCapPolicy → subagentToolCapPolicy` -/

def rootRedactRules : List (RedactRule UInt8) :=
  [ ⟨"api_key", asciiBytes "sk-", isApiKeyBodyByte, asciiBytes "[REDACTED_API_KEY]"⟩,
    ⟨"bearer", asciiBytes "Bearer ", isBearerBodyByte, asciiBytes "[REDACTED_BEARER]"⟩ ]

def subagentRedactRules : List (RedactRule UInt8) :=
  rootRedactRules ++
  [ ⟨"github_pat", asciiBytes "ghp_", isApiKeyBodyByte, asciiBytes "[REDACTED_GH_PAT]"⟩ ]

/-- **Hop 0 (`rootCapPolicy`):** allows `{read_doc, patch_atom, audit_log, deploy_svc}`,
targets `{sandbox/*, docs/*, vault/*}`, `amount ∈ [0..999]`, `1..10` ops, and `Absent("sk-")`. -/
def rootCapPolicy : GrammarPolicy CapNT capSemantics where
  initial     := .Root
  rules       := capCoreFrameRules ++
                 [rToolRead, rToolPatch, rToolAudit, rToolDeploy,
                  rTgtSandbox, rTgtDocs, rTgtVault] ++
                 amtHeadRules 9 ++ amtTail1DigitRules ++ amtTail2DigitRules
  redactRules := rootRedactRules
  bounds      := [ .mustAccept noSkDashDfa,
                   .rangeHits countOpBraceDfa 1 10 ]

/-- **Hop 1 (`serviceCapPolicy` — TeamLead):** narrows tools to `{read_doc, patch_atom, audit_log}`,
targets to `{sandbox/*, docs/*}`, `amount ∈ [0..99]`, `1..5` ops, and adds `Absent("DROP ")`. -/
def serviceCapPolicy : GrammarPolicy CapNT capSemantics where
  initial     := .Root
  rules       := capCoreFrameRules ++
                 [rToolRead, rToolPatch, rToolAudit,
                  rTgtSandbox, rTgtDocs] ++
                 amtHeadRules 9 ++ amtTail1DigitRules
  redactRules := rootRedactRules
  bounds      := [ .mustAccept noSkDashDfa,
                   .mustAccept noSqlDropDfa,
                   .rangeHits countOpBraceDfa 1 5 ]

/-- **Hop 2 (`subagentToolCapPolicy` — UntrustedCoderAgent):** narrows tools strictly to
`{read_doc, patch_atom}`, targets strictly to `{sandbox/*}`, `amount ∈ [0..5]`, `1..2` ops,
adds `ghp_` redaction rule, and adds `Absent("$(")` shell-injection guard. -/
def subagentToolCapPolicy : GrammarPolicy CapNT capSemantics where
  initial     := .Root
  rules       := capCoreFrameRules ++
                 [rToolRead, rToolPatch, rTgtSandbox] ++
                 amtHeadRules 5
  redactRules := subagentRedactRules
  bounds      := [ .mustAccept noSkDashDfa,
                   .mustAccept noSqlDropDfa,
                   .mustAccept noShellSubDfa,
                   .rangeHits countOpBraceDfa 1 2 ]

def sampleSubagentPayload : List UInt8 :=
  asciiBytes "{\"tool\":\"patch_atom\",\"target\":\"sandbox/note_01\",\"amount\":3}"

def expectedSubagentAst : MiniValue :=
  .vToolCall (asciiBytes "patch_atom") (asciiBytes "sandbox/note_01") 3

def sampleSubagentRuleSeq : List (AttrRule UInt8 CapNT CapOp) :=
  match ll1Parse subagentToolCapPolicy.cfg sampleSubagentPayload with
  | some (rs, _) => rs
  | none => []

set_option maxRecDepth 40000 in
/-- **Kernel-Verified 3-Hop Delegation Chain & End-to-End Subagent Admission (`by decide`):**
`subagentToolCapPolicy` attenuates `serviceCapPolicy`, which attenuates `rootCapPolicy`;
`sampleSubagentPayload` is admitted at the leaf capability and therefore provably admitted at
`rootCapPolicy` with the identical unique AST `expectedSubagentAst`. -/
theorem threeHop_delegation_verified :
    grammarPolicyAttenuates subagentToolCapPolicy serviceCapPolicy = true ∧
    grammarPolicyAttenuates serviceCapPolicy rootCapPolicy = true ∧
    policyChainAttenuates [rootCapPolicy, serviceCapPolicy, subagentToolCapPolicy] = true ∧
    PolicyAdmits subagentToolCapPolicy sampleSubagentPayload sampleSubagentRuleSeq expectedSubagentAst ∧
    PolicyAdmits rootCapPolicy sampleSubagentPayload sampleSubagentRuleSeq expectedSubagentAst := by
  have h12 : grammarPolicyAttenuates subagentToolCapPolicy serviceCapPolicy = true := by decide
  have h23 : grammarPolicyAttenuates serviceCapPolicy rootCapPolicy = true := by decide
  have hch : policyChainAttenuates [rootCapPolicy, serviceCapPolicy, subagentToolCapPolicy] = true := by
    simp [policyChainAttenuates, h12, h23]
    decide
  have hleaf : PolicyAdmits subagentToolCapPolicy sampleSubagentPayload sampleSubagentRuleSeq expectedSubagentAst := by
    rw [← execPolicyVerify_iff]
    decide
  have hroot := (policyChainAttenuates_sound (chain := [rootCapPolicy, serviceCapPolicy, subagentToolCapPolicy])
    rfl rfl hch hleaf).1
  exact ⟨h12, h23, hch, hleaf, hroot⟩

/-! ### 4.4 Four Constructive Privilege-Escalation Falsifier Teeth (`by decide`) -/

/-- **Escalation Attempt (i):** Widening `.rangeHits countOpBraceDfa 1 5` to `.rangeHits countOpBraceDfa 1 6`. -/
def escalatedRangeCap : GrammarPolicy CapNT capSemantics :=
  { serviceCapPolicy with
    bounds := [ .mustAccept noSkDashDfa,
                .mustAccept noSqlDropDfa,
                .rangeHits countOpBraceDfa 1 6 ] }

def sixOpEscalationPayload : List UInt8 :=
  asciiBytes "[{\"tool\":\"read_doc\",\"target\":\"sandbox/a\",\"amount\":0},{\"tool\":\"read_doc\",\"target\":\"sandbox/a\",\"amount\":0},{\"tool\":\"read_doc\",\"target\":\"sandbox/a\",\"amount\":0},{\"tool\":\"read_doc\",\"target\":\"sandbox/a\",\"amount\":0},{\"tool\":\"read_doc\",\"target\":\"sandbox/a\",\"amount\":0},{\"tool\":\"read_doc\",\"target\":\"sandbox/a\",\"amount\":0}]"

set_option maxRecDepth 40000 in
/-- **Falsifier Tooth (i) — Widening `.rangeHits 1 5` to `.rangeHits 1 6` Refused (`by decide`).** -/
theorem escalation_tooth_widen_rangeHits_refused :
    grammarPolicyAttenuates escalatedRangeCap serviceCapPolicy = false ∧
    (AutomatonBound.rangeHits countOpBraceDfa 1 6).holds sixOpEscalationPayload = true ∧
    (AutomatonBound.rangeHits countOpBraceDfa 1 5).holds sixOpEscalationPayload = false := by
  decide

/-- **Escalation Attempt (ii):** Dropping the `Absent("sk-")` (`noSkDashDfa`) guard. -/
def droppedSkGuardCap : GrammarPolicy CapNT capSemantics :=
  { serviceCapPolicy with
    bounds := [ .mustAccept noSqlDropDfa,
                .rangeHits countOpBraceDfa 1 5 ] }

/-- Minimal-length optimality of `"sk-"` (`length = 3`): every word of length `< 3` is accepted
by `noSkDashDfa`, so no counterexample shorter than `3` bytes exists. -/
theorem noSkDash_short_words_accepted :
    (noSkDashDfa.accepts [] = true) ∧
    (∀ a : UInt8, noSkDashDfa.accepts [a] = true) ∧
    (∀ a b : UInt8, noSkDashDfa.accepts [a, b] = true) := by
  have hstep : ∀ s : Nat, s < 3 → ∀ c : UInt8,
      (s = 0 → noSkDashDfa.step s c < 2) ∧
      (s < 2 → noSkDashDfa.step s c < 3) := by
    intro s hs c
    have hc := c.toNat_lt
    have hkey : 256 * s + c.toNat < 4 * 256 := by omega
    have hdiv : (256 * s + c.toNat) / 256 = s := by omega
    have hmod : (256 * s + c.toNat) % 256 = c.toNat := by omega
    simp only [DfaSpec.step, noSkDashDfa, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hkey, Option.map_some, Option.getD_some, hdiv, hmod]
    constructor <;> intro hcond <;> split_ifs <;> omega
  have hacc : ∀ s : Nat, s < 3 → noSkDashDfa.isAccepting s = true := by
    intro s hs
    match s with
    | 0 | 1 | 2 => rfl
  have hinit0 : noSkDashDfa.initial = 0 := rfl
  refine ⟨rfl, fun a => ?_, fun a b => ?_⟩
  · have h1 := (hstep 0 (by omega) a).1 rfl
    rw [DfaSpec.accepts, DfaSpec.run, hinit0, DfaSpec.runFrom_cons, DfaSpec.runFrom_nil]
    exact hacc _ (by omega)
  · have h1 := (hstep 0 (by omega) a).1 rfl
    have h2 := (hstep _ (by omega) b).2 h1
    rw [DfaSpec.accepts, DfaSpec.run, hinit0, DfaSpec.runFrom_cons, DfaSpec.runFrom_cons,
      DfaSpec.runFrom_nil]
    exact hacc _ h2

set_option maxRecDepth 40000 in
/-- **Falsifier Tooth (ii) — Dropping `Absent("sk-")` Refused & Minimal `"sk-"` Synthesized (`by decide`).** -/
theorem escalation_tooth_drop_sk_guard_refused :
    grammarPolicyAttenuates droppedSkGuardCap serviceCapPolicy = false ∧
    dfaSublanguageDecide acceptAllDfa noSkDashDfa = false ∧
    dfaSublanguageDecide noSqlDropDfa noSkDashDfa = false ∧
    dfaCounterexample? acceptAllDfa noSkDashDfa = some (asciiBytes "sk-") ∧
    dfaCounterexample? noSqlDropDfa noSkDashDfa = some (asciiBytes "sk-") ∧
    noSkDashDfa.accepts (asciiBytes "sk-") = false := by
  decide

/-- **Escalation Attempt (iii):** Adding unauthorized `"wipe_prod"` grammar production `rToolWipeProd`. -/
def wipeProdEscalatedCap : GrammarPolicy CapNT capSemantics :=
  { subagentToolCapPolicy with
    rules := subagentToolCapPolicy.rules ++ [rToolWipeProd] }

def wipeProdPayload : List UInt8 :=
  asciiBytes "{\"tool\":\"wipe_prod\",\"target\":\"sandbox/tmp\",\"amount\":1}"

set_option maxRecDepth 40000 in
/-- **Falsifier Tooth (iii) — Unauthorized `"wipe_prod"` Production Refused (`by decide`):**
even though `wipeProdEscalatedCap` remains LL(1) deterministic, `grammarPolicyAttenuates` rejects
it because `rToolWipeProd ∉ serviceCapPolicy.rules`. -/
theorem escalation_tooth_wipe_prod_refused :
    ll1Deterministic wipeProdEscalatedCap.cfg = true ∧
    grammarPolicyAttenuates wipeProdEscalatedCap serviceCapPolicy = false ∧
    (ll1Parse wipeProdEscalatedCap.cfg wipeProdPayload).isSome = true ∧
    ll1Parse serviceCapPolicy.cfg wipeProdPayload = none := by
  decide

/-- **Escalation Attempt (iv):** Injecting duplicate-key ambiguity (`rDupKeyFirstWins` + `rDupKeyLastWins`). -/
def dupKeyParentCap : GrammarPolicy CapNT capSemantics :=
  { rootCapPolicy with
    rules := rootCapPolicy.rules ++ [rToolWipeProd, rDupKeyFirstWins, rDupKeyLastWins] }

def dupKeyAmbigChildCap : GrammarPolicy CapNT capSemantics :=
  { subagentToolCapPolicy with
    rules := subagentToolCapPolicy.rules ++ [rToolWipeProd, rDupKeyFirstWins, rDupKeyLastWins] }

def dupKeyCapPayload : List UInt8 :=
  asciiBytes "{\"tool\":\"read_doc\",\"tool\":\"wipe_prod\",\"target\":\"sandbox/db\",\"amount\":1}"

def dupKeyFirstCert : List (AttrRule UInt8 CapNT CapOp) :=
  let t := Symbol.terminal (T := UInt8) (N := CapNT)
  let nt := Symbol.nonterminal (T := UInt8) (N := CapNT)
  [ ⟨.Root, [nt .WS, nt .Expr, nt .WS], .passAt 1⟩,
    ⟨.WS, [], .unitOp⟩,
    ⟨.Expr,
      [t 0x7B, nt .WS] ++ capLit "\"tool\"" ++
      [nt .WS, t 0x3A, nt .WS, t 0x22, nt .ToolName, t 0x22, nt .WS, t 0x2C, nt .WS, t 0x22, t 0x74, nt .AfterCommaT],
      .mkExprObj⟩,
    ⟨.WS, [], .unitOp⟩, ⟨.WS, [], .unitOp⟩, ⟨.WS, [], .unitOp⟩,
    rToolRead,
    ⟨.WS, [], .unitOp⟩, ⟨.WS, [], .unitOp⟩,
    rDupKeyFirstWins,
    ⟨.WS, [], .unitOp⟩, ⟨.WS, [], .unitOp⟩,
    rToolWipeProd,
    ⟨.WS, [], .unitOp⟩, ⟨.WS, [], .unitOp⟩, ⟨.WS, [], .unitOp⟩, ⟨.WS, [], .unitOp⟩,
    rTgtSandbox,
    ⟨.Slug, [t 0x64, nt .Slug], .slugCons 0x64⟩,
    ⟨.Slug, [t 0x62, nt .Slug], .slugCons 0x62⟩,
    ⟨.Slug, [], .slugNil⟩,
    ⟨.WS, [], .unitOp⟩, ⟨.WS, [], .unitOp⟩, ⟨.WS, [], .unitOp⟩, ⟨.WS, [], .unitOp⟩,
    ⟨.BoundedAmt, [t 0x31, nt .AmtTail1], .amtHead 1⟩,
    ⟨.AmtTail1, [], .digitsNil⟩,
    ⟨.WS, [], .unitOp⟩,
    ⟨.WS, [], .unitOp⟩ ]

def dupKeyLastCert : List (AttrRule UInt8 CapNT CapOp) :=
  dupKeyFirstCert.map fun r => if r = rDupKeyFirstWins then rDupKeyLastWins else r

set_option maxRecDepth 40000 in
/-- **Falsifier Tooth (iv) — Duplicate-Key Ambiguity Refused (`by decide`):**
even when `dupKeyAmbigChildCap.rules ⊆ dupKeyParentCap.rules`, `grammarPolicyAttenuates` rejects
the edge because `ll1Deterministic = false`, blocking the two-AST duplicate-key splice attack
(`"read_doc"` vs `"wipe_prod"` on the exact same byte string `dupKeyCapPayload`). -/
theorem escalation_tooth_duplicate_key_ambiguity_refused :
    listSubset dupKeyAmbigChildCap.rules dupKeyParentCap.rules = true ∧
    ll1Deterministic dupKeyAmbigChildCap.cfg = false ∧
    grammarPolicyAttenuates dupKeyAmbigChildCap dupKeyParentCap = false ∧
    AttrReplay dupKeyAmbigChildCap.cfg dupKeyFirstCert dupKeyCapPayload
      (.vToolCall (asciiBytes "read_doc") (asciiBytes "sandbox/db") 1) ∧
    AttrReplay dupKeyAmbigChildCap.cfg dupKeyLastCert dupKeyCapPayload
      (.vToolCall (asciiBytes "wipe_prod") (asciiBytes "sandbox/db") 1) ∧
    ll1Parse subagentToolCapPolicy.cfg dupKeyCapPayload = none := by
  have h1 : AttrReplay dupKeyAmbigChildCap.cfg dupKeyFirstCert dupKeyCapPayload
      (.vToolCall (asciiBytes "read_doc") (asciiBytes "sandbox/db") 1) := by
    rw [← execAttrReplay_iff]; decide
  have h2 : AttrReplay dupKeyAmbigChildCap.cfg dupKeyLastCert dupKeyCapPayload
      (.vToolCall (asciiBytes "wipe_prod") (asciiBytes "sandbox/db") 1) := by
    rw [← execAttrReplay_iff]; decide
  exact ⟨by decide, by decide, by decide, h1, h2, by decide⟩

/-! ## §5. Axiom Audit (`#guard_msgs` Pins) -/

/-- info: 'Minidregg.Theory.GrammarTypedCapability.dfaProductCheck_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dfaProductCheck_iff

/-- info: 'Minidregg.Theory.GrammarTypedCapability.dfaSublanguageDecide_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dfaSublanguageDecide_sound

/-- info: 'Minidregg.Theory.GrammarTypedCapability.dfaSublanguageDecide_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dfaSublanguageDecide_iff

/-- info: 'Minidregg.Theory.GrammarTypedCapability.dfaSublanguageDecide_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dfaSublanguageDecide_trans

/-- info: 'Minidregg.Theory.GrammarTypedCapability.dfaCounterexample?_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dfaCounterexample?_sound

/-- info: 'Minidregg.Theory.GrammarTypedCapability.automatonBoundEntails_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms automatonBoundEntails_sound

/-- info: 'Minidregg.Theory.GrammarTypedCapability.grammarPolicyAttenuates_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grammarPolicyAttenuates_sound

/-- info: 'Minidregg.Theory.GrammarTypedCapability.grammarPolicyAttenuates_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grammarPolicyAttenuates_trans

/-- info: 'Minidregg.Theory.GrammarTypedCapability.policyChainAttenuates_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms policyChainAttenuates_sound

/-- info: 'Minidregg.Theory.GrammarTypedCapability.GrammarCapLineage.attenuates_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GrammarCapLineage.attenuates_root

/-- info: 'Minidregg.Theory.GrammarTypedCapability.threeHop_delegation_verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms threeHop_delegation_verified

/-- info: 'Minidregg.Theory.GrammarTypedCapability.escalation_tooth_widen_rangeHits_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms escalation_tooth_widen_rangeHits_refused

/-- info: 'Minidregg.Theory.GrammarTypedCapability.escalation_tooth_drop_sk_guard_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms escalation_tooth_drop_sk_guard_refused

/-- info: 'Minidregg.Theory.GrammarTypedCapability.escalation_tooth_wipe_prod_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms escalation_tooth_wipe_prod_refused

/-- info: 'Minidregg.Theory.GrammarTypedCapability.escalation_tooth_duplicate_key_ambiguity_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms escalation_tooth_duplicate_key_ambiguity_refused

end Minidregg.Theory.GrammarTypedCapability
