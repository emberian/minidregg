/-
# The order clause an input-range refusal names

`inputsInRange` refuses a law when ANY present order atom compares two
integers further apart than the profile's width decides. It walks every atom,
including children of `not` and `any`, whatever their Boolean outcome: the
verdict must not depend on evaluation order, and an atom a guard makes
irrelevant today is the deciding one on the next step. That is kept.

What changes is that the refusal names the atom. `rangeLeaf` walks
`inputsInRange`'s own recursion and returns the path of the first atom it
refuses; `rangeLeaf_none_iff` says it names nothing exactly when the range
check passes, and `rangeLeaf_sound` that the named subterm is an order atom
whose own range check fails. `LawLeaf.ofRange` packages the atom with the two
integers it compares, and `ofRange_out_of_range` proves those two integers are
outside the scalar width's band.
-/
import Compiler.PredCompile
import Compiler.RefusalReason
import Theory.AssertAxioms

namespace Minidregg.Pred

/-- The four atoms an order profile range-checks. -/
def Pred.isOrderAtom : Pred → Bool
  | .le _ _ | .monotone _ | .leSlots _ _ | .leSlotsOff _ _ _ => true
  | _ => false

end Minidregg.Pred

namespace Minidregg.Compiler

open Minidregg.Pred

set_option autoImplicit false

mutual
/-- The path to the first order atom of `p` whose range check fails, or `none`. -/
def rangeLeaf (profile : CompilerProfile) (p : Pred) (old new : State) : Option (List Nat) :=
  match p with
  | .not q => (rangeLeaf profile q old new).map (0 :: ·)
  | .allL ps => rangeLeafL profile ps old new
  | .anyL ps => rangeLeafL profile ps old new
  | .le s v => if inputsInRange profile (.le s v) old new then none else some []
  | .monotone s => if inputsInRange profile (.monotone s) old new then none else some []
  | .leSlots a b => if inputsInRange profile (.leSlots a b) old new then none else some []
  | .leSlotsOff a b c =>
      if inputsInRange profile (.leSlotsOff a b c) old new then none else some []
  | .eq _ _ | .memberOf _ _ | .writeOnce _ | .eqSlots _ _ | .witnessed _ => none
/-- The first child (by index) of a list holding an out-of-range order atom. -/
def rangeLeafL (profile : CompilerProfile) (ps : PredList) (old new : State) :
    Option (List Nat) :=
  match ps with
  | .nil => none
  | .cons q rest =>
      match rangeLeaf profile q old new with
      | some path => some (0 :: path)
      | none => (rangeLeafL profile rest old new).map shiftHead
end

mutual
/-- The explanation is the range decision: nothing is named exactly when it passes. -/
theorem rangeLeaf_none_iff (profile : CompilerProfile) :
    (p : Pred) → (old new : State) →
      (rangeLeaf profile p old new = none ↔ inputsInRange profile p old new = true)
  | .le _ _, _, _ | .monotone _, _, _ | .leSlots _ _, _, _ | .leSlotsOff _ _ _, _, _ => by
      simp only [rangeLeaf]; split <;> simp_all
  | .eq _ _, _, _ | .memberOf _ _, _, _ | .writeOnce _, _, _ | .eqSlots _ _, _, _
  | .witnessed _, _, _ => by simp [rangeLeaf, inputsInRange]
  | .not q, old, new => by
      simp only [rangeLeaf, inputsInRange, Option.map_eq_none_iff]
      exact rangeLeaf_none_iff profile q old new
  | .allL ps, old, new => by
      simp only [rangeLeaf, inputsInRange]
      exact rangeLeafL_none_iff profile ps old new
  | .anyL ps, old, new => by
      simp only [rangeLeaf, inputsInRange]
      exact rangeLeafL_none_iff profile ps old new
theorem rangeLeafL_none_iff (profile : CompilerProfile) :
    (ps : PredList) → (old new : State) →
      (rangeLeafL profile ps old new = none ↔ inputsInRangeL profile ps old new = true)
  | .nil, _, _ => by simp [rangeLeafL, inputsInRangeL]
  | .cons q rest, old, new => by
      have hq := rangeLeaf_none_iff profile q old new
      have hr := rangeLeafL_none_iff profile rest old new
      simp only [rangeLeafL, inputsInRangeL, Bool.and_eq_true]
      cases h : rangeLeaf profile q old new with
      | some path =>
          have : inputsInRange profile q old new ≠ true := fun t => by
            rw [← hq] at t; rw [h] at t; cases t
          simp [this]
      | none =>
          have : inputsInRange profile q old new = true := hq.mp h
          simp [this, Option.map_eq_none_iff, hr]
end

mutual
/-- The named subterm is an order atom of the law, and its own range check fails. -/
theorem rangeLeaf_sound (profile : CompilerProfile) :
    (p : Pred) → (old new : State) → (path : List Nat) → rangeLeaf profile p old new = some path →
      ∃ q, p.subterm path = some q ∧ q.isOrderAtom = true ∧
        inputsInRange profile q old new = false
  | .le _ _, _, _, _, h | .monotone _, _, _, _, h | .leSlots _ _, _, _, _, h
  | .leSlotsOff _ _ _, _, _, _, h => by
      simp only [rangeLeaf] at h
      split at h
      · cases h
      · rename_i out
        cases h
        exact ⟨_, rfl, rfl, by simpa using out⟩
  | .eq _ _, _, _, _, h | .memberOf _ _, _, _, _, h | .writeOnce _, _, _, _, h
  | .eqSlots _ _, _, _, _, h | .witnessed _, _, _, _, h => by simp [rangeLeaf] at h
  | .not q, old, new, path, h => by
      simp only [rangeLeaf] at h
      obtain ⟨sub, found, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨atom, at_, isAtom, out⟩ := rangeLeaf_sound profile q old new sub found
      exact ⟨atom, by simpa [Pred.subterm] using at_, isAtom, out⟩
  | .allL ps, old, new, path, h => by
      simp only [rangeLeaf] at h
      obtain ⟨i, rest, atom, rfl, at_, isAtom, out⟩ := rangeLeafL_sound profile ps old new path h
      exact ⟨atom, by simpa [Pred.subterm] using at_, isAtom, out⟩
  | .anyL ps, old, new, path, h => by
      simp only [rangeLeaf] at h
      obtain ⟨i, rest, atom, rfl, at_, isAtom, out⟩ := rangeLeafL_sound profile ps old new path h
      exact ⟨atom, by simpa [Pred.subterm] using at_, isAtom, out⟩
theorem rangeLeafL_sound (profile : CompilerProfile) :
    (ps : PredList) → (old new : State) → (path : List Nat) →
      rangeLeafL profile ps old new = some path →
      ∃ i rest q, path = i :: rest ∧ PredList.subterm ps i rest = some q ∧
        q.isOrderAtom = true ∧ inputsInRange profile q old new = false
  | .nil, _, _, _, h => by simp [rangeLeafL] at h
  | .cons q qs, old, new, path, h => by
      simp only [rangeLeafL] at h
      cases found : rangeLeaf profile q old new with
      | some sub =>
          rw [found] at h
          cases h
          obtain ⟨atom, at_, isAtom, out⟩ := rangeLeaf_sound profile q old new sub found
          exact ⟨0, sub, atom, rfl, by simpa [PredList.subterm] using at_, isAtom, out⟩
      | none =>
          rw [found] at h
          obtain ⟨tail, later, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨i, rest, atom, rfl, at_, isAtom, out⟩ := rangeLeafL_sound profile qs old new tail later
          exact ⟨i + 1, rest, atom, rfl, by simpa [PredList.subterm] using at_, isAtom, out⟩
end

/-- The two integers an order atom compares (left, right), exactly as `inputsInRange`
reads them; `leSlotsOff`'s offset is added to the right operand. -/
def orderOperands (p : Pred) (old new : State) : Int × Int :=
  match p with
  | .le s v => (intOf new s, v)
  | .monotone s => (intOf old s, intOf new s)
  | .leSlots a b => (intOf new a, intOf new b)
  | .leSlotsOff a b c => (intOf new a, intOf new b + c)
  | _ => (0, 0)

/-- At a scalar width, an order atom whose range check fails compares two integers
outside the band `[-2^width, 2^width)` of differences. -/
theorem orderOperands_out_of_range {width : Nat} {q : Pred} {old new : State}
    (atom : q.isOrderAtom = true) (out : inputsInRange (.scalar width) q old new = false) :
    ¬ (-(2 : Int) ^ width ≤ (orderOperands q old new).2 - (orderOperands q old new).1 ∧
        (orderOperands q old new).2 - (orderOperands q old new).1 < (2 : Int) ^ width) := by
  cases q <;> simp only [Pred.isOrderAtom, Bool.false_eq_true] at atom <;>
    simp only [inputsInRange, orderOperands, CompilerProfile.scalar, decide_eq_false_iff_not,
      PredOrder.InputsInRange] at out ⊢ <;>
    exact fun inside => out (fun _ => inside)

namespace LawLeaf

/-- The out-of-range order atom of `law` on the step `old → new`, with the two integers
it compares; `none` exactly when the range check passes. -/
def ofRange (profile : CompilerProfile) (law : Pred) (old new : State) : Option LawLeaf := do
  let path ← rangeLeaf profile law old new
  let atom ← law.subterm path
  let operands := orderOperands atom old new
  pure ⟨path, atom, some operands.1, some operands.2⟩

theorem ofRange_none_iff (profile : CompilerProfile) (law : Pred) (old new : State) :
    ofRange profile law old new = none ↔ inputsInRange profile law old new = true := by
  rw [← rangeLeaf_none_iff]
  unfold ofRange
  cases named : rangeLeaf profile law old new with
  | none => simp
  | some path =>
      obtain ⟨atom, found, _, _⟩ := rangeLeaf_sound profile law old new path named
      simp [found]

/-- The named atom sits in the law at its path, is an order atom whose range check
fails, and the two values named are the integers it compares. -/
theorem ofRange_names_atom (profile : CompilerProfile) (law : Pred) (old new : State)
    (leaf : LawLeaf) (named : ofRange profile law old new = some leaf) :
    law.subterm leaf.path = some leaf.clause ∧ leaf.clause.isOrderAtom = true ∧
      inputsInRange profile leaf.clause old new = false ∧
      leaf.before = some (orderOperands leaf.clause old new).1 ∧
      leaf.after = some (orderOperands leaf.clause old new).2 := by
  unfold ofRange at named
  cases found : rangeLeaf profile law old new with
  | none => simp [found] at named
  | some path =>
      obtain ⟨atom, at_, isAtom, out⟩ := rangeLeaf_sound profile law old new path found
      simp only [found, at_, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at named
      subst named
      exact ⟨at_, isAtom, out, rfl, rfl⟩

/-- At a scalar width, the two named values really are out of range: their difference
lies outside `[-2^width, 2^width)`. -/
theorem ofRange_out_of_range {width : Nat} (law : Pred) (old new : State) (leaf : LawLeaf)
    (named : ofRange (.scalar width) law old new = some leaf) :
    ∃ left right, leaf.before = some left ∧ leaf.after = some right ∧
      ¬ (-(2 : Int) ^ width ≤ right - left ∧ right - left < (2 : Int) ^ width) := by
  obtain ⟨_, atom, out, before, after⟩ := ofRange_names_atom _ law old new leaf named
  exact ⟨_, _, before, after, orderOperands_out_of_range atom out⟩

end LawLeaf

/-! ## Two integers with one field image

The compiled law reads every integer of the step as a field element, so the
compiler also requires `castInjOn` over every integer the step carries (`intsOf`),
including slots the law does not mention. Over `ZMod (2^127 - 1)` two integers of
`R` never share an image; beyond it they can (a pair delta of `2^127` reads as
`1`). `castAlias` names such a pair; it decides nothing, and is computed only once
the cast check has already refused. -/

section CastAlias
variable (F : Type) [Field F] [DecidableEq F]

/-- The first pair of distinct integers of `I` with the same image in `F`. -/
def castAliasPair (I : List Int) : Option (Int × Int) :=
  (I.dedup.flatMap fun x => I.dedup.map fun y => (x, y)).find?
    fun pr => pr.1 != pr.2 && decide ((pr.1 : F) = (pr.2 : F))

/-- `none` when the cast check passes; otherwise the colliding pair. -/
def castAlias (I : List Int) : Option (Int × Int) :=
  if castInjOn F I then none else castAliasPair F I

theorem castAliasPair_sound (I : List Int) (x y : Int) (h : castAliasPair F I = some (x, y)) :
    x ∈ I ∧ y ∈ I ∧ x ≠ y ∧ (x : F) = (y : F) := by
  unfold castAliasPair at h
  have hmem := List.mem_of_find?_eq_some h
  have hsat := List.find?_some h
  simp only [List.mem_flatMap, List.mem_map, List.mem_dedup] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  simp only [Prod.mk.injEq] at hab
  obtain ⟨rfl, rfl⟩ := hab
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hsat
  exact ⟨ha, hb, hsat.1, hsat.2⟩

theorem castAliasPair_complete (I : List Int) (h : ¬ castInjOn F I) :
    castAliasPair F I ≠ none := by
  intro none_
  apply h
  intro a ha b hb same
  by_contra differ
  unfold castAliasPair at none_
  have := List.find?_eq_none.mp none_ (a, b)
    (by simp only [List.mem_flatMap, List.mem_map, List.mem_dedup]; exact ⟨a, ha, b, hb, rfl⟩)
  simp [differ, same] at this

theorem castAlias_none_iff (I : List Int) : castAlias F I = none ↔ castInjOn F I := by
  unfold castAlias
  by_cases h : castInjOn F I
  · simp [h]
  · simp only [h, if_false, iff_false]
    exact castAliasPair_complete F I h

theorem castAlias_sound (I : List Int) (x y : Int) (h : castAlias F I = some (x, y)) :
    x ∈ I ∧ y ∈ I ∧ x ≠ y ∧ (x : F) = (y : F) := by
  unfold castAlias at h
  split at h
  · cases h
  · exact castAliasPair_sound F I x y h

end CastAlias

/-- Two integers of the step with one field image, named. -/
def Refusal.castAlias (x y : Int) : Refusal :=
  ⟨.lawInputRange,
    s!"values {x} and {y} have the same image in the native field (outside the band the compiled law decides)",
    none⟩

#assert_axioms castAlias_none_iff
#assert_axioms castAlias_sound
#assert_axioms rangeLeaf_none_iff
#assert_axioms rangeLeaf_sound
#assert_axioms LawLeaf.ofRange_none_iff
#assert_axioms LawLeaf.ofRange_names_atom
#assert_axioms LawLeaf.ofRange_out_of_range

end Minidregg.Compiler
