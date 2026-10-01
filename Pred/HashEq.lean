/-
# Pred.HashEq — what `hashEq value blinder commit` decides

The atom (Pred/Core) is commit–reveal at the kernel: a cell's `commit` field holds
`cSHAKE256(cell ‖ names ‖ value ‖ blinder)` written while `value` and `blinder` are not
on the Store; the reveal writes them and the law requires `hashEq` between them and the
commitment. This file states what that decision means:

* `hashEq_sound` — the verdict in source terms (no `eval` on the right).
* `hashEq_admits` — every honest opening is admitted (the atom is satisfiable).
* `hashEq_binds_or_collides` — two admitted steps showing the same commit value open to the
  same opening, or cSHAKE256 has a collision. Corollaries: `hashEq_reveal_binds` (a value
  cannot be re-opened to another value) and `hashEq_context_bound` (a commitment cannot be
  replayed into another cell or another field triple).
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

/-- `hashEqOpening` returns exactly the opening built from the state's reads, when admissible. -/
theorem hashEqOpening_eq_some {s : State} {v b c : Slot} {o : Opening} :
    hashEqOpening s v b c = some o ↔
      s.get hashEqCellSlot = some o.cell ∧ s.get v = some o.value ∧ s.get b = some o.blinder ∧
      o.valueSlot = v ∧ o.blinderSlot = b ∧ o.commitSlot = c ∧ o.Admissible := by
  constructor
  · intro h
    unfold hashEqOpening at h
    split at h
    next cell x r h1 h2 h3 =>
      dsimp only at h
      split_ifs at h with hadm
      cases h
      exact ⟨h1, h2, h3, rfl, rfl, rfl, hadm⟩
    next => cases h
  · rintro ⟨h1, h2, h3, rfl, rfl, rfl, hadm⟩
    cases o
    unfold hashEqOpening
    simp only at h1 h2 h3 hadm ⊢
    rw [h1, h2, h3]
    simp [hadm]

/-- `hashEqHolds` under any hash is "the opening exists and the commit slot holds its digest". -/
theorem hashEqHolds_iff (H : Hash) (s : State) (v b c : Slot) :
    hashEqHolds H s v b c = true ↔
      ∃ o, hashEqOpening s v b c = some o ∧ s.get c = some (digestWith H o) := by
  unfold hashEqHolds
  cases ho : hashEqOpening s v b c <;> cases hc : s.get c <;> simp [eq_comm]

/-- **`hashEq_sound`** — the deployed verdict, in source terms. -/
theorem hashEq_sound (v b c : Slot) (old new : State) :
    eval (.hashEq v b c) old new = true ↔
      ∃ cell x r,
        new.get "request/target" = some cell ∧ new.get v = some x ∧ new.get b = some r ∧
        (⟨cell, v, b, c, x, r⟩ : Opening).Admissible ∧
        new.get c = some (digestWith deployed ⟨cell, v, b, c, x, r⟩) := by
  simp only [eval, evalWith]
  rw [hashEqHolds_iff]
  constructor
  · rintro ⟨o, ho, hc⟩
    obtain ⟨h1, h2, h3, rfl, rfl, rfl, hadm⟩ := hashEqOpening_eq_some.mp ho
    exact ⟨o.cell, o.value, o.blinder, h1, h2, h3, hadm, hc⟩
  · rintro ⟨cell, x, r, h1, h2, h3, hadm, hc⟩
    exact ⟨_, hashEqOpening_eq_some (o := ⟨cell, v, b, c, x, r⟩) |>.mpr
      ⟨h1, h2, h3, rfl, rfl, rfl, hadm⟩, hc⟩

/-- **Admitted when honest.** Any state carrying an admissible opening and its digest is
admitted, whatever the old state. -/
theorem hashEq_admits (o : Opening) (hadm : o.Admissible) (old new : State)
    (hcell : new.get "request/target" = some o.cell) (hv : new.get o.valueSlot = some o.value)
    (hb : new.get o.blinderSlot = some o.blinder)
    (hc : new.get o.commitSlot = some (digestWith deployed o)) :
    eval (.hashEq o.valueSlot o.blinderSlot o.commitSlot) old new = true :=
  (hashEq_sound _ _ _ old new).mpr ⟨o.cell, o.value, o.blinder, hcell, hv, hb, hadm, hc⟩

/-! ## §2. Fail-closed -/

theorem hashEq_absent_cell_refused (v b c : Slot) (old new : State)
    (h : new.get "request/target" = none) : eval (.hashEq v b c) old new = false := by
  cases he : eval (.hashEq v b c) old new
  · rfl
  · obtain ⟨_, _, _, h1, -⟩ := (hashEq_sound v b c old new).mp he
    rw [h] at h1; cases h1

theorem hashEq_absent_value_refused (v b c : Slot) (old new : State)
    (h : new.get v = none) : eval (.hashEq v b c) old new = false := by
  cases he : eval (.hashEq v b c) old new
  · rfl
  · obtain ⟨_, _, _, -, h2, -⟩ := (hashEq_sound v b c old new).mp he
    rw [h] at h2; cases h2

theorem hashEq_absent_blinder_refused (v b c : Slot) (old new : State)
    (h : new.get b = none) : eval (.hashEq v b c) old new = false := by
  cases he : eval (.hashEq v b c) old new
  · rfl
  · obtain ⟨_, _, _, -, -, h3, -⟩ := (hashEq_sound v b c old new).mp he
    rw [h] at h3; cases h3

/-- A blinder outside `[0, 2^256)` is not a 32-byte blinder, and the atom refuses it. -/
theorem hashEq_wide_blinder_refused (v b c : Slot) (old new : State) (r : Int)
    (h : new.get b = some r) (hr : ¬(0 ≤ r ∧ r < 2 ^ 256)) :
    eval (.hashEq v b c) old new = false := by
  cases he : eval (.hashEq v b c) old new
  · rfl
  · obtain ⟨_, _, r', -, -, h3, hadm, -⟩ := (hashEq_sound v b c old new).mp he
    rw [h] at h3; cases h3
    exact absurd ⟨hadm.2.2.2.2.2.2.2.1, hadm.2.2.2.2.2.2.2.2⟩ hr

/-! ## §3. Binding — the statements of Bread's `SealedAuction`, re-proved on Mini's states -/

/-- **Binds or collides.** Two admitted `hashEq` steps whose commit slots hold the same integer
have the same opening — the same cell, the same three field names, the same value and the same
blinder — unless cSHAKE256 (at this customization) has a collision. -/
theorem hashEq_binds_or_collides {v b c v' b' c' : Slot} {old new old' new' : State}
    (h : eval (.hashEq v b c) old new = true) (h' : eval (.hashEq v' b' c') old' new' = true)
    (same : new.get c = new'.get c') :
    (∃ o, hashEqOpening new v b c = some o ∧ hashEqOpening new' v' b' c' = some o) ∨
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

/-- **`reveal_binds_committed`** on Mini: under one field triple, a commit value admits at most one (value, blinder) — a bidder cannot reveal a different bid than the one
committed, unless cSHAKE256 collides. -/
theorem hashEq_reveal_binds {v b c : Slot} {old new old' new' : State}
    (h : eval (.hashEq v b c) old new = true) (h' : eval (.hashEq v b c) old' new' = true)
    (same : new.get c = new'.get c) :
    (new.get v = new'.get v ∧ new.get b = new'.get b) ∨ Collision deployed := by
  rcases hashEq_binds_or_collides h h' same with ⟨o, ho, ho'⟩ | hcol
  · have e := hashEqOpening_eq_some.mp ho
    have e' := hashEqOpening_eq_some.mp ho'
    exact .inl ⟨by rw [e.2.1, e'.2.1], by rw [e.2.2.1, e'.2.2.1]⟩
  · exact .inr hcol

/-- **`hashEq_context_bound`** — a commitment cannot be replayed into another cell or another
field triple: if the same commit value is admitted at two contexts that differ (cell, or any of
the three field names), cSHAKE256 has a collision. (The values need not agree; the opening is
public after a reveal, so the attack this names is copying both.) -/
theorem hashEq_context_bound {v b c v' b' c' : Slot} {old new old' new' : State}
    (h : eval (.hashEq v b c) old new = true) (h' : eval (.hashEq v' b' c') old' new' = true)
    (same : new.get c = new'.get c')
    (differ : new.get "request/target" ≠ new'.get "request/target" ∨ v ≠ v' ∨ b ≠ b' ∨ c ≠ c') :
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
field triple: the verdict does not depend on the value or the blinder at all. So the deployed
binding above is exactly cSHAKE256's collision resistance — the floor is refutable. -/
theorem lengthHash_admits_any_reveal {s s' : State} {v b c : Slot} {o o' : Opening}
    (ho : hashEqOpening s v b c = some o) (ho' : hashEqOpening s' v b c = some o')
    (sameCell : o'.cell = o.cell) (same : s'.get c = s.get c) :
    hashEqHolds lengthHash s' v b c = hashEqHolds lengthHash s v b c := by
  obtain ⟨-, -, -, hv, hb, hc, -⟩ := hashEqOpening_eq_some.mp ho
  obtain ⟨-, -, -, hv', hb', hc', -⟩ := hashEqOpening_eq_some.mp ho'
  have hdig : digestWith lengthHash o' = digestWith lengthHash o := by
    have : o' = { o with value := o'.value, blinder := o'.blinder } := by
      cases o; cases o'; simp_all
    rw [this, lengthHash_binding_fails]
  unfold hashEqHolds
  rw [ho, ho', same]
  cases s.get c <;> simp [hdig]

/-! ## §5. Hiding — ASSUMED, not proved

What hides a sealed bid before its reveal is that the Store and the retained ingress carry only
`commit`, and that `commit` reveals nothing feasible about `value` when `blinder` is 32 uniform
bytes. The second half is a computational property of cSHAKE256 — under the random-oracle model a
`q`-query distinguisher's advantage is about `q / 2^256` — and this tree has no model in which to
state "feasible". So it is named here as an assumption over a hash and a supplied
indistinguishability relation; the deployed reading is `HashEqHiding deployed`, discharged nowhere.

Both poles are stated at the one relation this tree can decide, equality, and at toy hashes: the
length hash satisfies it (`lengthHash_hashEqHiding`), the identity "hash" refutes it
(`identity_not_hashEqHiding`). At equality the satisfying pole is necessarily a non-binding hash:
`hiding_at_equality_is_a_collision` turns hiding at `=` into a collision of the same hash, which is
why the deployed instance is meaningful only at a computational relation. -/

/-- **ASSUMED, NOT PROVED (at `deployed`).** For a fixed cell and field triple, the commit under `H`
as a function of a uniform 32-byte blinder is `Indistinguishable` between any two values in the
domain. Meaningful only at a computational `Indistinguishable` (the private-cell envelope's "hiding
under the ROM"); this tree supplies none. -/
def HashEqHiding (H : Hash) (Indistinguishable : (Int → Int) → (Int → Int) → Prop) : Prop :=
  ∀ (cell : Int) (v b c : Slot) (x x' : Int),
    (⟨cell, v, b, c, x, 0⟩ : Opening).Admissible → (⟨cell, v, b, c, x', 0⟩ : Opening).Admissible →
    Indistinguishable (fun r => digestWith H ⟨cell, v, b, c, x, r⟩)
      (fun r => digestWith H ⟨cell, v, b, c, x', r⟩)

/-- Cell `0`, slots `v`/`b`/`c`, blinder `0`: admissible at every value in the domain. -/
theorem opening_vbc_admissible (x : Int) (h0 : -2 ^ 255 ≤ x) (h1 : x < 2 ^ 255) :
    (⟨0, "v", "b", "c", x, 0⟩ : Opening).Admissible := by
  refine ⟨le_refl _, by norm_num, ?_, ?_, ?_, h0, h1, le_refl _, by norm_num⟩
  · show (utf8 "v").length < 2 ^ 32; decide
  · show (utf8 "b").length < 2 ^ 32; decide
  · show (utf8 "c").length < 2 ^ 32; decide

/-- The assumption cannot be read as *equality*: hiding at `=` would make two different values
commit identically, which is itself a collision of the same hash (at `deployed`, of cSHAKE256). -/
theorem hiding_at_equality_is_a_collision (H : Hash) (h : HashEqHiding H (· = ·)) : Collision H := by
  have a0 := opening_vbc_admissible 0 (by norm_num) (by norm_num)
  have a1 := opening_vbc_admissible 1 (by norm_num) (by norm_num)
  rcases binds_or_collides H a0 a1 (congrFun (h 0 "v" "b" "c" 0 1 a0 a1) 0) with hab | hcol
  · simp at hab
  · exact hcol

/-- **Satisfiable** (toy hash): under the length hash the commit does not depend on the value, so the
hiding schema holds at the strongest relation, equality. The same hash is the refuting pole of binding
(`lengthHash_admits_any_reveal`). -/
theorem lengthHash_hashEqHiding : HashEqHiding lengthHash (· = ·) := by
  intro cell v b c x x' _ _
  funext r
  simp only [digestWith, lengthHash, preimage_length]

/-- **Refutable** (toy hash): the identity "hash" puts the value's bytes in the commit, and values
`0` and `1` commit differently at blinder `0`. -/
theorem identity_not_hashEqHiding : ¬ HashEqHiding id (· = ·) := by
  intro h
  have e := congrFun (h 0 "v" "b" "c" 0 1 (opening_vbc_admissible 0 (by norm_num) (by norm_num))
    (opening_vbc_admissible 1 (by norm_num) (by norm_num))) 0
  revert e
  decide +kernel

/-! ## §6. Axiom pins -/

/-- info: 'Minidregg.Pred.hashEq_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_sound
/-- info: 'Minidregg.Pred.hashEq_admits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_admits
/-- info: 'Minidregg.Pred.hashEq_binds_or_collides' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_binds_or_collides
/-- info: 'Minidregg.Pred.hashEq_reveal_binds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_reveal_binds
/-- info: 'Minidregg.Pred.hashEq_context_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_context_bound
/-- info: 'Minidregg.Pred.lengthHash_admits_any_reveal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms lengthHash_admits_any_reveal
/-- info: 'Minidregg.Pred.hashEq_wide_blinder_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hashEq_wide_blinder_refused
/-- info: 'Minidregg.Pred.hiding_at_equality_is_a_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hiding_at_equality_is_a_collision
/-- info: 'Minidregg.Pred.lengthHash_hashEqHiding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms lengthHash_hashEqHiding
/-- info: 'Minidregg.Pred.identity_not_hashEqHiding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms identity_not_hashEqHiding

end Minidregg.Pred
