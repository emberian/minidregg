/-
# Pred.HashEq — what `hashEq values blinder commit` decides

The atom (Pred/Core) is commit–reveal at the kernel: a cell's `commit` field holds
`cSHAKE256(cell ‖ n ‖ names ‖ values ‖ blinder)` written while the values and `blinder` are not
on the Store; the reveal writes them and the law requires `hashEq` between them and the
commitment. One commitment opens a whole tuple (a sealed order's price and quantity). This file
states what that decision means:

* `hashEq_sound` — the verdict in source terms (no `eval` on the right).
* `hashEq_admits` — every honest opening is admitted (the atom is satisfiable).
* `hashEq_binds_or_collides` — two admitted steps showing the same commit value open to the
  same opening, or cSHAKE256 has a collision. Corollaries: `hashEq_reveal_binds` (a tuple
  cannot be re-opened to another tuple), `hashEq_reveal_binds_each` (nor can any one of its
  fields), and `hashEq_context_bound` (a commitment cannot be replayed into another cell, other
  field names, or the same fields in another order or arity).
* `hashEq_opens_every_field` / `hashEq_absent_value_refused` — no partial opening: an admitted
  reveal carries every field of the tuple, and a reveal missing one is refused.
* `lengthHash_admits_any_reveal` — the refutable pole: at a length hash every value opens
  every commitment, so the binding above is carried by the hash and nothing else.
* `HashEqHiding H` — the hiding property, **assumed, not proved** at the deployed hash, and
  `hiding_at_equality_is_a_collision`: the assumption cannot be read as equality of digests. Its
  poles at toy hashes: `lengthHash_hashEqHiding` (satisfied) and `identity_not_hashEqHiding`.

The openings here are controller facts about one projected state, not authenticated-map
openings: `Theory.AuthMap`'s `verify_sound` binds a value to a root through a path; this atom
binds a value to a field the same state already carries, and reads no root.
-/
import Pred.Core

namespace Minidregg.Pred

open HashEqDigest

set_option autoImplicit false

/-! ## §1. The verdict in source terms -/

/-- `getAll` returns one value per slot. -/
theorem State.getAll_length {s : State} : ∀ {vs : List Slot} {xs : List Int},
    s.getAll vs = some xs → xs.length = vs.length
  | [], xs, h => by simp only [State.getAll, Option.some.injEq] at h; subst h; rfl
  | v :: vs, xs, h => by
    simp only [State.getAll] at h
    split at h
    next x xs' _ hxs => cases h; simp [State.getAll_length hxs]
    next => cases h

/-- `getAll` reads every slot of the list. -/
theorem State.getAll_mem {s : State} : ∀ {vs : List Slot} {xs : List Int},
    s.getAll vs = some xs → ∀ v ∈ vs, (s.get v).isSome
  | [], _, _, v, hv => nomatch hv
  | w :: vs, xs, h, v, hv => by
    simp only [State.getAll] at h
    split at h
    next x xs' hw hxs =>
      cases hv with
      | head => simp [hw]
      | tail _ hv => exact State.getAll_mem hxs v hv
    next => cases h

/-- An absent slot makes the whole read absent. -/
theorem State.getAll_absent {s : State} {v : Slot} (h : s.get v = none) :
    ∀ {vs : List Slot}, v ∈ vs → s.getAll vs = none
  | w :: vs, hv => by
    simp only [State.getAll]
    cases hv with
    | head => simp [h]
    | tail _ hv => rw [State.getAll_absent h hv]; split <;> simp_all

/-- `hashEqOpening` returns exactly the opening built from the state's reads, when admissible. -/
theorem hashEqOpening_eq_some {s : State} {vs : List Slot} {b c : Slot} {o : Opening} :
    hashEqOpening s vs b c = some o ↔
      s.get hashEqCellSlot = some o.cell ∧ s.getAll vs = some o.values ∧
      s.get b = some o.blinder ∧
      o.valueSlots = vs ∧ o.blinderSlot = b ∧ o.commitSlot = c ∧ o.Admissible := by
  constructor
  · intro h
    unfold hashEqOpening at h
    split at h
    next cell x r h1 h2 h3 =>
      dsimp only at h
      split at h
      next hadm =>
        cases h
        exact ⟨h1, h2, h3, rfl, rfl, rfl, hadm⟩
      next => cases h
    next => cases h
  · rintro ⟨h1, h2, h3, rfl, rfl, rfl, hadm⟩
    cases o
    unfold hashEqOpening
    simp only at h1 h2 h3 hadm ⊢
    rw [h1, h2, h3]
    simp [hadm]

/-- `hashEqHolds` under any hash is "the opening exists and the commit slot holds its digest". -/
theorem hashEqHolds_iff (H : Hash) (s : State) (vs : List Slot) (b c : Slot) :
    hashEqHolds H s vs b c = true ↔
      ∃ o, hashEqOpening s vs b c = some o ∧ s.get c = some (digestWith H o) := by
  unfold hashEqHolds
  cases ho : hashEqOpening s vs b c <;> cases hc : s.get c <;> simp [eq_comm]

/-- **`hashEq_sound`** — the deployed verdict, in source terms. -/
theorem hashEq_sound (vs : List Slot) (b c : Slot) (old new : State) :
    eval (.hashEq vs b c) old new = true ↔
      ∃ cell xs r,
        new.get "request/target" = some cell ∧ new.getAll vs = some xs ∧ new.get b = some r ∧
        (⟨cell, vs, b, c, xs, r⟩ : Opening).Admissible ∧
        new.get c = some (digestWith deployed ⟨cell, vs, b, c, xs, r⟩) := by
  simp only [eval, evalWith]
  rw [hashEqHolds_iff]
  constructor
  · rintro ⟨o, ho, hc⟩
    obtain ⟨h1, h2, h3, rfl, rfl, rfl, hadm⟩ := hashEqOpening_eq_some.mp ho
    exact ⟨o.cell, o.values, o.blinder, h1, h2, h3, hadm, hc⟩
  · rintro ⟨cell, xs, r, h1, h2, h3, hadm, hc⟩
    exact ⟨_, hashEqOpening_eq_some (o := ⟨cell, vs, b, c, xs, r⟩) |>.mpr
      ⟨h1, h2, h3, rfl, rfl, rfl, hadm⟩, hc⟩

/-- **Admitted when honest.** Any state carrying an admissible opening and its digest is
admitted, whatever the old state. -/
theorem hashEq_admits (o : Opening) (hadm : o.Admissible) (old new : State)
    (hcell : new.get "request/target" = some o.cell) (hv : new.getAll o.valueSlots = some o.values)
    (hb : new.get o.blinderSlot = some o.blinder)
    (hc : new.get o.commitSlot = some (digestWith deployed o)) :
    eval (.hashEq o.valueSlots o.blinderSlot o.commitSlot) old new = true :=
  (hashEq_sound _ _ _ old new).mpr ⟨o.cell, o.values, o.blinder, hcell, hv, hb, hadm, hc⟩

/-- **No partial opening.** An admitted reveal carries every field of the tuple. -/
theorem hashEq_opens_every_field {vs : List Slot} {b c : Slot} {old new : State}
    (h : eval (.hashEq vs b c) old new = true) : ∀ v ∈ vs, (new.get v).isSome := by
  obtain ⟨_, _, _, -, h2, -⟩ := (hashEq_sound vs b c old new).mp h
  exact State.getAll_mem h2

/-! ## §2. Fail-closed -/

theorem hashEq_absent_cell_refused (vs : List Slot) (b c : Slot) (old new : State)
    (h : new.get "request/target" = none) : eval (.hashEq vs b c) old new = false := by
  cases he : eval (.hashEq vs b c) old new
  · rfl
  · obtain ⟨_, _, _, h1, -⟩ := (hashEq_sound vs b c old new).mp he
    rw [h] at h1; cases h1

/-- **A reveal missing one field of the tuple is refused**, whatever the others hold. -/
theorem hashEq_absent_value_refused {v : Slot} {vs : List Slot} (hv : v ∈ vs) (b c : Slot)
    (old new : State) (h : new.get v = none) : eval (.hashEq vs b c) old new = false := by
  cases he : eval (.hashEq vs b c) old new
  · rfl
  · obtain ⟨_, _, _, -, h2, -⟩ := (hashEq_sound vs b c old new).mp he
    rw [State.getAll_absent h hv] at h2; cases h2

theorem hashEq_absent_blinder_refused (vs : List Slot) (b c : Slot) (old new : State)
    (h : new.get b = none) : eval (.hashEq vs b c) old new = false := by
  cases he : eval (.hashEq vs b c) old new
  · rfl
  · obtain ⟨_, _, _, -, -, h3, -⟩ := (hashEq_sound vs b c old new).mp he
    rw [h] at h3; cases h3

/-- A blinder outside `[0, 2^256)` is not a 32-byte blinder, and the atom refuses it. -/
theorem hashEq_wide_blinder_refused (vs : List Slot) (b c : Slot) (old new : State) (r : Int)
    (h : new.get b = some r) (hr : ¬(0 ≤ r ∧ r < 2 ^ 256)) :
    eval (.hashEq vs b c) old new = false := by
  cases he : eval (.hashEq vs b c) old new
  · rfl
  · obtain ⟨_, _, r', -, -, h3, hadm, -⟩ := (hashEq_sound vs b c old new).mp he
    rw [h] at h3; cases h3
    exact absurd ⟨hadm.2.2.2.2.2.2.2.2.1, hadm.2.2.2.2.2.2.2.2.2⟩ hr

/-! ## §3. Binding — the statements of Bread's `SealedAuction`, re-proved on Mini's states -/

/-- **Binds or collides.** Two admitted `hashEq` steps whose commit slots hold the same integer
have the same opening — the same cell, the same field names in the same order, the same values
and the same blinder — unless cSHAKE256 (at this customization) has a collision. -/
theorem hashEq_binds_or_collides {vs vs' : List Slot} {b c b' c' : Slot}
    {old new old' new' : State}
    (h : eval (.hashEq vs b c) old new = true) (h' : eval (.hashEq vs' b' c') old' new' = true)
    (same : new.get c = new'.get c') :
    (∃ o, hashEqOpening new vs b c = some o ∧ hashEqOpening new' vs' b' c' = some o) ∨
      Collision deployed := by
  simp only [eval, evalWith] at h h'
  obtain ⟨o, ho, hc⟩ := (hashEqHolds_iff _ _ _ _ _).mp h
  obtain ⟨o', ho', hc'⟩ := (hashEqHolds_iff _ _ _ _ _).mp h'
  have hadm := (hashEqOpening_eq_some.mp ho).2.2.2.2.2.2
  have hadm' := (hashEqOpening_eq_some.mp ho').2.2.2.2.2.2
  rw [hc, hc'] at same
  rcases binds_or_collides deployed hadm hadm' (Option.some.inj same) with heq | hcol
  · subst heq; exact .inl ⟨o, ho, ho'⟩
  · exact .inr hcol

/-- **`reveal_binds_committed`** on Mini: under one set of field names, a commit value admits at
most one (tuple, blinder) — a bidder cannot reveal a different order than the one committed,
unless cSHAKE256 collides. -/
theorem hashEq_reveal_binds {vs : List Slot} {b c : Slot} {old new old' new' : State}
    (h : eval (.hashEq vs b c) old new = true) (h' : eval (.hashEq vs b c) old' new' = true)
    (same : new.get c = new'.get c) :
    (new.getAll vs = new'.getAll vs ∧ new.get b = new'.get b) ∨ Collision deployed := by
  rcases hashEq_binds_or_collides h h' same with ⟨o, ho, ho'⟩ | hcol
  · have e := hashEqOpening_eq_some.mp ho
    have e' := hashEqOpening_eq_some.mp ho'
    exact .inl ⟨by rw [e.2.1, e'.2.1], by rw [e.2.2.1, e'.2.2.1]⟩
  · exact .inr hcol

/-- **Each field binds.** Two admitted reveals of one commitment agree on every field of the
tuple, unless cSHAKE256 collides: a bidder cannot keep the price and change the quantity. -/
theorem hashEq_reveal_binds_each {vs : List Slot} {b c : Slot} {old new old' new' : State}
    (h : eval (.hashEq vs b c) old new = true) (h' : eval (.hashEq vs b c) old' new' = true)
    (same : new.get c = new'.get c) :
    (∀ v ∈ vs, new.get v = new'.get v) ∨ Collision deployed := by
  rcases hashEq_reveal_binds h h' same with ⟨hall, -⟩ | hcol
  · refine .inl (fun v hv => ?_)
    obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp
      (show (new.getAll vs).isSome from by
        obtain ⟨_, xs, _, -, h2, -⟩ := (hashEq_sound vs b c old new).mp h; simp [h2])
    have hxs' : new'.getAll vs = some xs := hall ▸ hxs
    exact getAll_agree hxs hxs' hv
  · exact .inr hcol
where
  /-- Two states whose reads of a list agree, agree on each slot of it. -/
  getAll_agree {s s' : State} : ∀ {vs : List Slot} {xs : List Int},
      s.getAll vs = some xs → s'.getAll vs = some xs → ∀ {v : Slot}, v ∈ vs → s.get v = s'.get v
    | [], _, _, _, _, hv => nomatch hv
    | w :: vs, xs, h, h', v, hv => by
      simp only [State.getAll] at h h'
      split at h
      next x ys hw hys =>
        split at h'
        next x' ys' hw' hys' =>
          cases h; cases h'
          cases hv with
          | head => rw [hw, hw']
          | tail _ hv => exact getAll_agree hys hys' hv
        next => cases h'
      next => cases h

/-- **`hashEq_context_bound`** — a commitment cannot be replayed into another cell, other field
names, or the same fields in another order or arity: if the same commit value is admitted at two
contexts that differ, cSHAKE256 has a collision. (The values need not agree; the opening is public
after a reveal, so the attack this names is copying it.) -/
theorem hashEq_context_bound {vs vs' : List Slot} {b c b' c' : Slot} {old new old' new' : State}
    (h : eval (.hashEq vs b c) old new = true) (h' : eval (.hashEq vs' b' c') old' new' = true)
    (same : new.get c = new'.get c')
    (differ : new.get "request/target" ≠ new'.get "request/target" ∨ vs ≠ vs' ∨ b ≠ b' ∨
      c ≠ c') :
    Collision deployed := by
  rcases hashEq_binds_or_collides h h' same with ⟨o, ho, ho'⟩ | hcol
  · exfalso
    obtain ⟨c1, -, -, hv, hb, hc, -⟩ := hashEqOpening_eq_some.mp ho
    obtain ⟨c1', -, -, hv', hb', hc', -⟩ := hashEqOpening_eq_some.mp ho'
    have hcell : new.get "request/target" = new'.get "request/target" := by
      simp only [hashEqCellSlot] at c1 c1'; rw [c1, c1']
    rcases differ with d | d | d | d
    · exact d hcell
    · exact d (hv.symm.trans hv')
    · exact d (hb.symm.trans hb')
    · exact d (hc.symm.trans hc')
  · exact hcol

/-! ## §4. The refutable pole — binding is the hash's, not the encoding's -/

/-- **At a length hash every reveal opens every commitment** made in the same cell under the same
field names: the verdict does not depend on the values or the blinder at all. So the deployed
binding above is exactly cSHAKE256's collision resistance — the floor is refutable. -/
theorem lengthHash_admits_any_reveal {s s' : State} {vs : List Slot} {b c : Slot}
    {o o' : Opening}
    (ho : hashEqOpening s vs b c = some o) (ho' : hashEqOpening s' vs b c = some o')
    (sameCell : o'.cell = o.cell) (same : s'.get c = s.get c) :
    hashEqHolds lengthHash s' vs b c = hashEqHolds lengthHash s vs b c := by
  obtain ⟨-, -, -, hv, hb, hc, hadm⟩ := hashEqOpening_eq_some.mp ho
  obtain ⟨-, -, -, hv', hb', hc', hadm'⟩ := hashEqOpening_eq_some.mp ho'
  have arity : o'.values.length = o.values.length := by
    rw [hadm.2.2.2.1, hadm'.2.2.2.1, hv, hv']
  have hdig : digestWith lengthHash o' = digestWith lengthHash o := by
    have : o' = { o with values := o'.values, blinder := o'.blinder } := by
      cases o; cases o'; simp_all
    rw [this, lengthHash_binding_fails _ _ _ arity]
  unfold hashEqHolds
  rw [ho, ho', same]
  cases s.get c <;> simp [hdig]

/-! ## §5. Hiding — ASSUMED, not proved

What hides a sealed bid before its reveal is that the Store and the retained ingress carry only
`commit`, and that `commit` reveals nothing feasible about the values when `blinder` is 32 uniform
bytes. The second half is a computational property of cSHAKE256 — under the random-oracle model a
`q`-query distinguisher's advantage is about `q / 2^256` — and this tree has no model in which to
state "feasible". So it is named here as an assumption over a hash and a supplied
indistinguishability relation; the deployed reading is `HashEqHiding deployed`, discharged nowhere.

Both poles are stated at the one relation this tree can decide, equality, and at toy hashes: the
length hash satisfies it (`lengthHash_hashEqHiding`), the identity "hash" refutes it
(`identity_not_hashEqHiding`). At equality the satisfying pole is necessarily a non-binding hash:
`hiding_at_equality_is_a_collision` turns hiding at `=` into a collision of the same hash, which is
why the deployed instance is meaningful only at a computational relation. -/

/-- **ASSUMED, NOT PROVED (at `deployed`).** For a fixed cell and field names, the commit under `H`
as a function of a uniform 32-byte blinder is `Indistinguishable` between any two tuples of the same
arity in the domain. Meaningful only at a computational `Indistinguishable` (the private-cell
envelope's "hiding under the ROM"); this tree supplies none. -/
def HashEqHiding (H : Hash) (Indistinguishable : (Int → Int) → (Int → Int) → Prop) : Prop :=
  ∀ (cell : Int) (vs : List Slot) (b c : Slot) (xs xs' : List Int),
    (⟨cell, vs, b, c, xs, 0⟩ : Opening).Admissible →
    (⟨cell, vs, b, c, xs', 0⟩ : Opening).Admissible →
    Indistinguishable (fun r => digestWith H ⟨cell, vs, b, c, xs, r⟩)
      (fun r => digestWith H ⟨cell, vs, b, c, xs', r⟩)

/-- Cell `0`, slots `["v"]`/`b`/`c`, blinder `0`: admissible at every value in the domain. -/
theorem opening_vbc_admissible (x : Int) (h0 : -2 ^ 255 ≤ x) (h1 : x < 2 ^ 255) :
    (⟨0, ["v"], "b", "c", [x], 0⟩ : Opening).Admissible := by
  refine ⟨Int.le_refl _, show (0 : Int) < 2 ^ 64 by decide,
    show (["v"] : List String).length < 2 ^ 32 by decide, rfl, ?_, ?_, ?_, ?_,
    Int.le_refl _, show (0 : Int) < 2 ^ 256 by decide⟩
  · intro s hs; simp only [List.mem_singleton] at hs; subst hs; decide
  · show (utf8 "b").length < 2 ^ 32; decide
  · show (utf8 "c").length < 2 ^ 32; decide
  · intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact ⟨h0, h1⟩

/-- The assumption cannot be read as *equality*: hiding at `=` would make two different tuples
commit identically, which is itself a collision of the same hash (at `deployed`, of cSHAKE256). -/
theorem hiding_at_equality_is_a_collision (H : Hash) (h : HashEqHiding H (· = ·)) : Collision H := by
  have a0 := opening_vbc_admissible 0 (by decide) (by decide)
  have a1 := opening_vbc_admissible 1 (by decide) (by decide)
  rcases binds_or_collides H a0 a1 (congrFun (h 0 ["v"] "b" "c" [0] [1] a0 a1) 0) with hab | hcol
  · simp at hab
  · exact hcol

/-- **Satisfiable** (toy hash): under the length hash the commit does not depend on the value, so the
hiding schema holds at the strongest relation, equality. The same hash is the refuting pole of binding
(`lengthHash_admits_any_reveal`). -/
theorem lengthHash_hashEqHiding : HashEqHiding lengthHash (· = ·) := by
  intro cell vs b c xs xs' h h'
  funext r
  have arity : xs'.length = xs.length := h'.2.2.2.1.trans h.2.2.2.1.symm
  exact (lengthHash_binding_fails _ _ _ arity).symm

/-- **Refutable** (toy hash): the identity "hash" puts the value's bytes in the commit, and values
`0` and `1` commit differently at blinder `0`. -/
theorem identity_not_hashEqHiding : ¬ HashEqHiding id (· = ·) := by
  intro h
  have e := congrFun (h 0 ["v"] "b" "c" [0] [1] (opening_vbc_admissible 0 (by decide) (by decide))
    (opening_vbc_admissible 1 (by decide) (by decide))) 0
  revert e
  decide +kernel

/-! ## §6. Axiom pins -/

/-- info: 'Minidregg.Pred.hashEq_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_sound
/-- info: 'Minidregg.Pred.hashEq_admits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_admits
/-- info: 'Minidregg.Pred.hashEq_opens_every_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_opens_every_field
/-- info: 'Minidregg.Pred.hashEq_absent_value_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_absent_value_refused
/-- info: 'Minidregg.Pred.hashEq_binds_or_collides' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_binds_or_collides
/-- info: 'Minidregg.Pred.hashEq_reveal_binds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_reveal_binds
/-- info: 'Minidregg.Pred.hashEq_reveal_binds_each' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_reveal_binds_each
/-- info: 'Minidregg.Pred.hashEq_context_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_context_bound
/-- info: 'Minidregg.Pred.lengthHash_admits_any_reveal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms lengthHash_admits_any_reveal
/-- info: 'Minidregg.Pred.hashEq_wide_blinder_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_wide_blinder_refused
/-- info: 'Minidregg.Pred.hiding_at_equality_is_a_collision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hiding_at_equality_is_a_collision
/-- info: 'Minidregg.Pred.lengthHash_hashEqHiding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms lengthHash_hashEqHiding
/-- info: 'Minidregg.Pred.identity_not_hashEqHiding' depends on axioms: [propext] -/
#guard_msgs in #print axioms identity_not_hashEqHiding

end Minidregg.Pred
