/-
# Pred.CoordinationDial — the coordination dial as a COMPUTED PRICE on the ONE `Pred` AST.

`docs/DISTRIBUTED-DESIGN.md` §3.4, discharging `Theory/Confluence.lean`'s
`[CONFLUENCE-pred-dial]`: a guard does not *have* a price, it is *priced by where it
lives*. Here the guard is the one syntactic `Pred` (`Pred/Core.lean`), the place is the
v0 merge discipline (slot-wise max, grow-only), and the price is a `Verdict` computed by
`dial`, proved sound against `Theory.Confluence.IConfluent` of the guard's `eval`-derived
invariant, and handed to the finality ladder (`Theory.Finality.tier1_requires_iconfluent`).

## Design — the invariant without a twin evaluator

`Pred.State` is a `List (Slot × Int)`, not a lattice. The function view
`View := Slot → WithBot ℤ` IS one (`Pi` join over `WithBot`, pointwise max with `⊥` =
absent). `toFun` lifts a state's fail-closed `get` to it. The invariant a guard installs
on the view is defined THROUGH `eval`, never re-evaluated on the view:

    Inv p old f := ∃ s, toFun s = f ∧ eval p old s = true

Two facts make this a property of `f` rather than of a representative, and both are
proved against `eval` itself: `eval_congr_toFun` — on the new-state fragment (`eq`,
`le`, `memberOf`, closed under `not`/`all`/`any`) `eval` reads `new` only through
`toFun new` (and not `old` at all) — and `inv_rep_independent`, the ∃/∀ agreement over
the fiber. No canonical list representation is needed: `mergeState` is the list-level
merge with `toFun (mergeState s t) = toFun s ⊔ toFun t` (`toFun_mergeState`), which is all
`IConfluent` asks. Keys may repeat in a merged list; `get` reads the first and every
occurrence carries the join, so the view is unaffected.

## The classifier and its two-sided proof

Under slot-wise max the join of two states is, at every slot, one-or-the-other
(`get_mergeState_cases`), so any predicate reading ONE slot — an atom or its negation —
is merge-closed (`single_slot_closed`), and a conjunction of merge-closed parts is
merge-closed. `dial` issues `.free` exactly on that fragment; `dial_sound` proves every
`.free` verdict I-confluent by induction on the AST. The refusals are loud (ATLAS law
10), never a silent `true`: `.ordering` for `any`/compound `not` (the tooth
`demoAny_not_confluent` shows this is necessity, not conservatism — the invariant of
`any [eq a 1, eq b 1]` is genuinely non-confluent at the computed join), `.stepShaped`
for `monotone`/`writeOnce` (step predicates over `(old, new)`, not state invariants),
`.thirdParty` for `witnessed`.

Residual:
  * `[DIAL-pn]` the PN-counter merge (concurrent debits; needs per-replica state in the
    cell schema) — the case where `le` becomes a ceiling that FORCES ordering, cf.
    `Theory.Confluence.Witness.decrements_ceiling_breaks`.
  * `[DIAL-declared-merge]` per-slot merge rules declared by the cell's program instead
    of the global max.
  * `[DIAL-relational]` relational (cross-slot) guards decided by the merge.
  * `[DIAL-price]` the price as a quantale value rather than a four-point verdict.
-/
import Mathlib.Order.WithBot
import Mathlib.Order.Lattice
import Pred.Core
import Theory.Confluence
import Theory.Finality

namespace Minidregg.Pred.CoordinationDial

open Minidregg.Theory

/-! ## §1 — The function view. -/

/-- The lattice carrier: a slot map, `⊥` = absent. Join is pointwise max. -/
abbrev View := Slot → WithBot ℤ

/-- A fail-closed read as a lattice element. -/
def ofRead : Option Int → WithBot ℤ
  | some v => (v : WithBot ℤ)
  | none => ⊥

/-- The function view of a state: `get` lifted, absent = `⊥`. -/
def toFun (s : State) : View := fun k => ofRead (s.get k)

theorem ofRead_injective : Function.Injective ofRead := by
  intro a b h
  cases a <;> cases b <;> simp_all [ofRead]

/-! ## §2 — The v0 merge: slot-wise max, grow-only. -/

/-- Slot-wise max on fail-closed reads: `absent ⊔ x = x`. -/
def joinRead : Option Int → Option Int → Option Int
  | some a, some b => some (a ⊔ b)
  | some a, none => some a
  | none, b => b

theorem ofRead_joinRead (a b : Option Int) : ofRead (joinRead a b) = ofRead a ⊔ ofRead b := by
  cases a <;> cases b <;> simp [ofRead, joinRead, WithBot.coe_sup]

/-- The merge on the list substrate: every key of either state, valued at the join of
the two fail-closed reads. -/
def mergeState (s t : State) : State :=
  ⟨(s.slots ++ t.slots).map fun q => (q.1, (joinRead (s.get q.1) (t.get q.1)).getD q.2)⟩

theorem get_eq_find (s : State) (k : Slot) :
    s.get k = (s.slots.find? fun p => p.1 == k).map (·.2) := rfl

/-- The merged state reads the join of the two reads, at every slot. -/
theorem get_mergeState (s t : State) (k : Slot) :
    (mergeState s t).get k = joinRead (s.get k) (t.get k) := by
  have hcomp : ((fun p : Slot × Int => p.1 == k) ∘
      fun q : Slot × Int => (q.1, (joinRead (s.get q.1) (t.get q.1)).getD q.2)) =
      fun q => q.1 == k := rfl
  rw [get_eq_find, mergeState, List.find?_map, hcomp, List.find?_append]
  rcases hs : s.slots.find? (fun q => q.1 == k) with _ | q
  · rcases ht : t.slots.find? (fun q => q.1 == k) with _ | r
    · simp [get_eq_find, hs, ht, joinRead]
    · have hr : r.1 = k := by simpa using List.find?_some ht
      simp [get_eq_find, hs, ht, hr, joinRead]
  · have hq : q.1 = k := by simpa using List.find?_some hs
    simp only [Option.some_or, Option.map_some, hq, get_eq_find s k, hs]
    cases t.get k <;> simp [joinRead]

/-- **The list merge realizes the lattice join.** -/
theorem toFun_mergeState (s t : State) : toFun (mergeState s t) = toFun s ⊔ toFun t := by
  funext k
  simp only [toFun, Pi.sup_apply, get_mergeState, ofRead_joinRead]

/-- At every slot the merge is one-or-the-other. -/
theorem get_mergeState_cases (s t : State) (k : Slot) :
    (mergeState s t).get k = s.get k ∨ (mergeState s t).get k = t.get k := by
  rw [get_mergeState]
  rcases s.get k with _ | a
  · right; rfl
  · rcases t.get k with _ | b
    · left; rfl
    · rcases le_total a b with h | h
      · right; simp [joinRead, sup_eq_right.mpr h]
      · left; simp [joinRead, sup_eq_left.mpr h]

/-! ## §3 — What `eval` reads: the single-slot and new-state fragments. -/

/-- The slot a predicate reads, when it reads exactly one (atoms and their negations). -/
def singleSlot : Pred → Option Slot
  | .eq k _ => some k
  | .le k _ => some k
  | .memberOf k _ => some k
  | .not q => singleSlot q
  | _ => none

/-- A single-slot predicate's verdict depends on the new state only through that slot's
read, and not on `old` at all. -/
theorem eval_congr_slot : ∀ (p : Pred) {k : Slot}, singleSlot p = some k →
    ∀ {old old' s s' : State}, s.get k = s'.get k → eval p old s = eval p old' s'
  | .eq k' v, k, hk, _, _, s, s', h => by
      obtain rfl : k' = k := by simpa [singleSlot] using hk
      simp only [eval, evalWith, h]
  | .le k' v, k, hk, _, _, s, s', h => by
      obtain rfl : k' = k := by simpa [singleSlot] using hk
      simp only [eval, evalWith, h]
  | .memberOf k' xs, k, hk, _, _, s, s', h => by
      obtain rfl : k' = k := by simpa [singleSlot] using hk
      simp only [eval, evalWith, h]
  | .not q, k, hk, old, old', s, s', h => by
      rw [eval_not, eval_not,
        eval_congr_slot q (by simpa [singleSlot] using hk) (old := old) (old' := old') h]
  | .writeOnce _, _, hk, _, _, _, _, _ => by simp [singleSlot] at hk
  | .monotone _, _, hk, _, _, _, _, _ => by simp [singleSlot] at hk
  | .witnessed _, _, hk, _, _, _, _, _ => by simp [singleSlot] at hk
  | .allL _, _, hk, _, _, _, _, _ => by simp [singleSlot] at hk
  | .anyL _, _, hk, _, _, _, _, _ => by simp [singleSlot] at hk

mutual
/-- The new-state fragment: atoms reading `new` only, closed under the Boolean closure.
Excludes the step predicates (`writeOnce`, `monotone`) and `witnessed`. -/
def NewOnly : Pred → Bool
  | .eq _ _ => true
  | .le _ _ => true
  | .memberOf _ _ => true
  | .writeOnce _ => false
  | .monotone _ => false
  | .witnessed _ => false
  | .not q => NewOnly q
  | .allL ps => NewOnlyList ps
  | .anyL ps => NewOnlyList ps
def NewOnlyList : PredList → Bool
  | .nil => true
  | .cons q rest => NewOnly q && NewOnlyList rest
end

mutual
/-- **`eval` reads `new` only through `toFun new`** on the new-state fragment, and does
not read `old`. This is what makes an invariant on the view well-defined without a
second evaluator. -/
theorem eval_congr_toFun : ∀ (p : Pred), NewOnly p = true →
    ∀ {old old' s s' : State}, toFun s = toFun s' → eval p old s = eval p old' s'
  | .eq k v, _, old, old', _, _, h =>
      eval_congr_slot (.eq k v) rfl (old := old) (old' := old') (ofRead_injective (congrFun h k))
  | .le k v, _, old, old', _, _, h =>
      eval_congr_slot (.le k v) rfl (old := old) (old' := old') (ofRead_injective (congrFun h k))
  | .memberOf k xs, _, old, old', _, _, h =>
      eval_congr_slot (.memberOf k xs) rfl (old := old) (old' := old')
        (ofRead_injective (congrFun h k))
  | .writeOnce _, hp, _, _, _, _, _ => by simp [NewOnly] at hp
  | .monotone _, hp, _, _, _, _, _ => by simp [NewOnly] at hp
  | .witnessed _, hp, _, _, _, _, _ => by simp [NewOnly] at hp
  | .not q, hp, old, old', _, _, h => by
      rw [eval_not, eval_not,
        eval_congr_toFun q (by simpa [NewOnly] using hp) (old := old) (old' := old') h]
  | .allL ps, hp, old, old', _, _, h => by
      simp only [eval, evalWith]
      exact evalAll_congr_toFun ps (by simpa [NewOnly] using hp) (old := old) (old' := old') h
  | .anyL ps, hp, old, old', _, _, h => by
      simp only [eval, evalWith]
      exact evalAny_congr_toFun ps (by simpa [NewOnly] using hp) (old := old) (old' := old') h
theorem evalAll_congr_toFun : ∀ (ps : PredList), NewOnlyList ps = true →
    ∀ {old old' s s' : State}, toFun s = toFun s' →
      evalWithAll failClosed ps old s = evalWithAll failClosed ps old' s'
  | .nil, _, _, _, _, _, _ => rfl
  | .cons q rest, hp, old, old', _, _, h => by
      have hqr : NewOnly q = true ∧ NewOnlyList rest = true := by simpa [NewOnlyList] using hp
      have e := eval_congr_toFun q hqr.1 (old := old) (old' := old') h
      simp only [eval] at e
      simp only [evalWithAll, e, evalAll_congr_toFun rest hqr.2 (old := old) (old' := old') h]
theorem evalAny_congr_toFun : ∀ (ps : PredList), NewOnlyList ps = true →
    ∀ {old old' s s' : State}, toFun s = toFun s' →
      evalWithAny failClosed ps old s = evalWithAny failClosed ps old' s'
  | .nil, _, _, _, _, _, _ => rfl
  | .cons q rest, hp, old, old', _, _, h => by
      have hqr : NewOnly q = true ∧ NewOnlyList rest = true := by simpa [NewOnlyList] using hp
      have e := eval_congr_toFun q hqr.1 (old := old) (old' := old') h
      simp only [eval] at e
      simp only [evalWithAny, e, evalAny_congr_toFun rest hqr.2 (old := old) (old' := old') h]
end

/-! ## §4 — The invariant on the view, `eval`-derived. -/

/-- The invariant guard `p` installs on the view: some state with this view passes
`eval`. On the new-state fragment this is a property of the view alone
(`inv_rep_independent`). -/
def Inv (p : Pred) (old : State) : Confluence.Invariant View :=
  fun f => ∃ s, toFun s = f ∧ eval p old s = true

/-- **Representation independence.** On the new-state fragment, for a view that is some
state's view, "some representative passes" and "every representative passes" agree, for
any `old`. -/
theorem inv_rep_independent (p : Pred) (hp : NewOnly p = true) (old old' : State) {f : View}
    (hf : ∃ s, toFun s = f) :
    Inv p old f ↔ ∀ s, toFun s = f → eval p old' s = true := by
  obtain ⟨s₀, rfl⟩ := hf
  constructor
  · rintro ⟨s, hs, hev⟩ u hu
    rw [eval_congr_toFun p hp (old := old') (old' := old) (hu.trans hs.symm)]
    exact hev
  · intro h
    exact ⟨s₀, rfl,
      (eval_congr_toFun p hp (old := old) (old' := old') rfl).trans (h s₀ rfl)⟩

/-- Merge-closure of a single-slot predicate: at its slot the merge reads one of the two
states, so a verdict true on both is true on the merge. -/
theorem single_slot_closed (p : Pred) {k : Slot} (hk : singleSlot p = some k)
    (old old' old'' s t : State) (hs : eval p old s = true) (ht : eval p old' t = true) :
    eval p old'' (mergeState s t) = true := by
  rcases get_mergeState_cases s t k with h | h
  · rw [eval_congr_slot p hk (old := old'') (old' := old) h]; exact hs
  · rw [eval_congr_slot p hk (old := old'') (old' := old') h]; exact ht

/-! ## §5 — The dial. -/

/-- The price. `free` is the only verdict that licenses tier 1; the other three are the
loud refusals, in increasing severity (`combine` takes the max). -/
inductive Verdict
  /-- Coordination-free: the invariant is merge-closed under slot-wise max. -/
  | free
  /-- Needs ordering: a disjunction or compound negation; not merge-closed in general. -/
  | ordering
  /-- Not a state invariant at all: a step predicate over `(old, new)`. -/
  | stepShaped
  /-- A third-party claim; no first-party discharge. -/
  | thirdParty
  deriving DecidableEq, Repr

/-- The louder refusal wins. -/
def Verdict.combine : Verdict → Verdict → Verdict
  | .free, b => b
  | a, .free => a
  | .thirdParty, _ => .thirdParty
  | _, .thirdParty => .thirdParty
  | .stepShaped, _ => .stepShaped
  | _, .stepShaped => .stepShaped
  | .ordering, .ordering => .ordering

theorem Verdict.combine_eq_free {a b : Verdict} :
    a.combine b = .free ↔ a = .free ∧ b = .free := by
  cases a <;> cases b <;> decide

mutual
/-- **The dial.** Atoms are free; `all` combines its parts; `not` of a single-slot
predicate is free (still single-slot), any other `not` and every `any` need ordering;
`monotone`/`writeOnce` are step-shaped; `witnessed` is third-party. -/
def dial : Pred → Verdict
  | .eq _ _ => .free
  | .le _ _ => .free
  | .memberOf _ _ => .free
  | .writeOnce _ => .stepShaped
  | .monotone _ => .stepShaped
  | .witnessed _ => .thirdParty
  | .not q => if (singleSlot q).isSome then .free else Verdict.combine .ordering (dial q)
  | .allL ps => dialList ps
  | .anyL ps => Verdict.combine .ordering (dialList ps)
def dialList : PredList → Verdict
  | .nil => .free
  | .cons q rest => Verdict.combine (dial q) (dialList rest)
end

/-- The Boolean reading of the dial. -/
def coordinationFree (p : Pred) : Bool := decide (dial p = .free)

/-- Merge-closure: `eval`-true on both states implies `eval`-true on their merge. -/
def MergeClosed (p : Pred) : Prop :=
  ∀ old s t, eval p old s = true → eval p old t = true → eval p old (mergeState s t) = true

mutual
theorem dial_free_closed : ∀ (p : Pred), dial p = .free → MergeClosed p
  | .eq k v, _ => fun old s t hs ht => single_slot_closed (.eq k v) rfl old old old s t hs ht
  | .le k v, _ => fun old s t hs ht => single_slot_closed (.le k v) rfl old old old s t hs ht
  | .memberOf k xs, _ => fun old s t hs ht =>
      single_slot_closed (.memberOf k xs) rfl old old old s t hs ht
  | .writeOnce _, h => by simp [dial] at h
  | .monotone _, h => by simp [dial] at h
  | .witnessed _, h => by simp [dial] at h
  | .not q, h => fun old s t hs ht => by
      have hk : (singleSlot q).isSome = true := by
        by_contra hne
        simp [dial, hne, Verdict.combine_eq_free] at h
      obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hk
      exact single_slot_closed (.not q) (by simpa [singleSlot] using hk) old old old s t hs ht
  | .allL ps, h => fun old s t hs ht => by
      simp only [eval, evalWith] at hs ht ⊢
      exact dialList_free_closed ps (by simpa [dial] using h) old s t hs ht
  | .anyL ps, h => by simp [dial, Verdict.combine_eq_free] at h
theorem dialList_free_closed : ∀ (ps : PredList), dialList ps = .free →
    ∀ old s t, evalWithAll failClosed ps old s = true →
      evalWithAll failClosed ps old t = true →
      evalWithAll failClosed ps old (mergeState s t) = true
  | .nil, _ => fun _ _ _ _ _ => rfl
  | .cons q rest, h => fun old s t hs ht => by
      have hqr := Verdict.combine_eq_free.mp (by simpa [dialList] using h)
      simp only [evalWithAll, Bool.and_eq_true] at hs ht ⊢
      exact ⟨dial_free_closed q hqr.1 old s t hs.1 ht.1,
        dialList_free_closed rest hqr.2 old s t hs.2 ht.2⟩
end

/-- **Soundness.** A `free` verdict is an I-confluent invariant on the view. -/
theorem dial_sound (p : Pred) (old : State) (h : dial p = .free) :
    Confluence.IConfluent (Inv p old) := by
  rintro f g ⟨s, rfl, hs⟩ ⟨t, rfl, ht⟩
  exact ⟨mergeState s t, toFun_mergeState s t, dial_free_closed p h old s t hs ht⟩

/-! ## §6 — The finality link. -/

/-- The tier the dial assigns: `free` runs causal; every refusal is sent to τ-BFT. -/
def dialTier (p : Pred) : Finality.Tier := if dial p = .free then .causal else .bft

theorem dialTier_sound (old : State) :
    ∀ p ∈ (Set.univ : Set Pred), dialTier p = .causal →
      Confluence.IConfluent (Inv p old) := by
  intro p _ hp
  by_cases h : dial p = .free
  · exact dial_sound p old h
  · simp [dialTier, h] at hp

/-- **Tier 1 through the dial.** A causal rule installed at the dial's verdict for `p`
has an I-confluent invariant — `Theory.Finality.tier1_requires_iconfluent` with the
dial as the classifier and `dial_sound` as its soundness. -/
theorem dial_tier1_sound (p : Pred) (old : State) (rule : Finality.FinalityRule View)
    (hcausal : rule.tier = .causal) (hmatch : rule.tier = dialTier p) :
    Confluence.IConfluent (Inv p old) :=
  Finality.tier1_requires_iconfluent (fun q => Inv q old) Set.univ p (Set.mem_univ p) rule
    hcausal dialTier hmatch (dialTier_sound old)

/-! ## §7 — Keystones, computed. -/

namespace Witness

/-- A ceiling and a membership: both single-slot atoms, conjoined. -/
def demoFree : Pred := Pred.all [.le "bal" 10, .memberOf "kind" [1, 2]]
def sA : State := ⟨[("bal", 3), ("kind", 1)]⟩
def sB : State := ⟨[("bal", 7), ("kind", 2)]⟩

theorem demoFree_dial : dial demoFree = .free ∧ coordinationFree demoFree = true := by decide

/-- Both states pass, the join reads the maxima, and the join passes. -/
theorem demoFree_computed :
    eval demoFree sA sA = true ∧ eval demoFree sB sB = true ∧
      (mergeState sA sB).get "bal" = some 7 ∧ (mergeState sA sB).get "kind" = some 2 ∧
      eval demoFree sA (mergeState sA sB) = true := by
  decide

/-- Satisfiable pole: the free verdict's invariant is I-confluent, for every `old`. -/
theorem demoFree_confluent (old : State) : Confluence.IConfluent (Inv demoFree old) :=
  dial_sound demoFree old demoFree_dial.1

/-- The invariant fires on the lattice join of the two views. -/
theorem demoFree_join_lawful : Inv demoFree sA (toFun sA ⊔ toFun sB) :=
  demoFree_confluent sA _ _ ⟨sA, rfl, by decide⟩ ⟨sB, rfl, by decide⟩

/-- The `any` tooth: `a = 1 ∨ b = 1`. -/
def demoAny : Pred := Pred.any [.eq "a" 1, .eq "b" 1]
def x : State := ⟨[("a", 1), ("b", 5)]⟩
def y : State := ⟨[("a", 5), ("b", 1)]⟩

theorem demoAny_dial : dial demoAny = .ordering ∧ coordinationFree demoAny = false := by decide

/-- Both states pass; the join reads `a = 5, b = 5` and fails. -/
theorem demoAny_computed :
    eval demoAny x x = true ∧ eval demoAny y y = true ∧
      (mergeState x y).get "a" = some 5 ∧ (mergeState x y).get "b" = some 5 ∧
      eval demoAny x (mergeState x y) = false := by
  decide

/-- Teeth: the refusal is necessity — the invariant of `demoAny` is NOT I-confluent. Any
state whose view is the join of the two views fails `eval`, by `eval_congr_toFun`. -/
theorem demoAny_not_confluent (old : State) : ¬ Confluence.IConfluent (Inv demoAny old) := by
  intro h
  have hp : NewOnly demoAny = true := by decide
  obtain ⟨u, hu, hev⟩ := h (toFun x) (toFun y)
    ⟨x, rfl, (eval_congr_toFun demoAny hp (old := old) (old' := x) rfl).trans (by decide)⟩
    ⟨y, rfl, (eval_congr_toFun demoAny hp (old := old) (old' := y) rfl).trans (by decide)⟩
  rw [← toFun_mergeState] at hu
  rw [eval_congr_toFun demoAny hp (old := old) (old' := x) hu] at hev
  exact absurd hev (by decide)

/-- The step-shaped refusal is loud: `monotone` is not silently `true`. -/
theorem monotone_refused :
    dial (.monotone "n") = .stepShaped ∧ coordinationFree (.monotone "n") = false ∧
      dial (Pred.all [.le "bal" 10, .monotone "n"]) = .stepShaped := by
  decide

example : dial (.writeOnce "n") = .stepShaped := by decide
example : dial (.witnessed ⟨"vk"⟩) = .thirdParty := by decide
/-- A negated atom is still single-slot, hence free. -/
example : dial (.not (.le "bal" 10)) = .free := by decide
/-- A negated conjunction is a disjunction: ordering. -/
example : dial (.not demoFree) = .ordering := by decide

/-- A causal rule over views: committed and canonical iff `bal` is present. -/
def causalRule : Finality.FinalityRule View where
  tier := .causal
  config := ⟨1, 0, Finality.Config.halfQuorum 1 0⟩
  committed f := f "bal" ≠ ⊥
  canonical f := f "bal" ≠ ⊥
  commit_canonical _ h := h

/-- The finality link fires on the free guard. -/
example : Confluence.IConfluent (Inv demoFree sA) :=
  dial_tier1_sound demoFree sA causalRule rfl (by decide)

/-- And is not available for the `any` guard: the dial sends it to τ-BFT. -/
example : dialTier demoAny = .bft := by decide

end Witness

/-! ## §8 — Axiom pins. -/

/-- info: 'Minidregg.Pred.CoordinationDial.toFun_mergeState' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms toFun_mergeState

/-- info: 'Minidregg.Pred.CoordinationDial.eval_congr_toFun' depends on axioms: [propext] -/
#guard_msgs in #print axioms eval_congr_toFun

/-- info: 'Minidregg.Pred.CoordinationDial.inv_rep_independent' depends on axioms: [propext] -/
#guard_msgs in #print axioms inv_rep_independent

/-- info: 'Minidregg.Pred.CoordinationDial.single_slot_closed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms single_slot_closed

/-- info: 'Minidregg.Pred.CoordinationDial.dial_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms dial_sound

/-- info: 'Minidregg.Pred.CoordinationDial.dial_tier1_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms dial_tier1_sound

/-- info: 'Minidregg.Pred.CoordinationDial.Witness.demoFree_confluent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Witness.demoFree_confluent

/-- info: 'Minidregg.Pred.CoordinationDial.Witness.demoAny_not_confluent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Witness.demoAny_not_confluent

/-- info: 'Minidregg.Pred.CoordinationDial.Witness.monotone_refused' depends on axioms: [propext] -/
#guard_msgs in #print axioms Witness.monotone_refused

end Minidregg.Pred.CoordinationDial
