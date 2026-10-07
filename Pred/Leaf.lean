/-
# Pred.Leaf — the clause a refusal names.

`Pred.eval` is structural, so a refused step has a structural explanation: the path from
the root to the first clause that is false on its own. `firstFailingLeaf` walks `eval`'s own
recursion (same oracle, same `old`/`new` pair) and returns that path; it decides nothing
new. `firstFailingLeaf_none_iff_eval` says it reports nothing exactly when `eval` accepts,
and `firstFailingLeaf_some_leaf` says the subterm it names is a leaf that `eval` rejects on
the very same step.

## What a leaf is

A path is the list of child indices from the root; `allL` numbers its children from `0`.
The walk descends only through conjunctions, to the first false child, and stops at anything
else: an atom, a negation, or a disjunction. A law is written as clauses joined by `;`
(one `allL`), and each clause a friend writes is usually a disjunction guarded to the write
verb (`any [ field 0 monotone, not (verb == write) ]`), all of whose children are false
when it refuses. Descending into it would name the guard, not the clause, so the whole
disjunction is the leaf. `open` (`allL []`) is never false; `sealed` (`anyL []`) is its own
leaf.

Core Lean only (Init) — within the Pred boundary.
-/
import Pred.Core

namespace Minidregg.Pred

set_option autoImplicit false

mutual
/-- The subterm of `p` at `path`, or `none` if the path leaves the tree. -/
def Pred.subterm : Pred → List Nat → Option Pred
  | p, [] => some p
  | .not q, 0 :: rest => Pred.subterm q rest
  | .allL ps, i :: rest => PredList.subterm ps i rest
  | .anyL ps, i :: rest => PredList.subterm ps i rest
  | _, _ :: _ => none
/-- The subterm at `rest` below the `i`-th child of a child list. -/
def PredList.subterm : PredList → Nat → List Nat → Option Pred
  | .nil, _, _ => none
  | .cons q _, 0, rest => Pred.subterm q rest
  | .cons _ qs, i + 1, rest => PredList.subterm qs i rest
end

/-- The nodes a refusal can name: everything but a conjunction, which is always explained
by one of its children. -/
def Pred.isLeaf : Pred → Bool
  | .allL _ => false
  | _ => true

/-- Move a child-list path one position to the right. -/
def shiftHead : List Nat → List Nat
  | [] => []
  | i :: rest => (i + 1) :: rest

mutual
/-- The path to the first failing leaf of `p` on the step `old → new` under the oracle `O`,
or `none` when `evalWith O p old new` accepts. -/
def leafWith (O : Oracle) (p : Pred) (old new : State) : Option (List Nat) :=
  match p with
  | .allL ps => leafWithAll O ps old new
  | .eq s v        => if evalWith O (.eq s v) old new then none else some []
  | .le s v        => if evalWith O (.le s v) old new then none else some []
  | .memberOf s xs => if evalWith O (.memberOf s xs) old new then none else some []
  | .writeOnce s   => if evalWith O (.writeOnce s) old new then none else some []
  | .monotone s    => if evalWith O (.monotone s) old new then none else some []
  | .witnessed vk  => if evalWith O (.witnessed vk) old new then none else some []
  | .eqSlots a b   => if evalWith O (.eqSlots a b) old new then none else some []
  | .leSlots a b   => if evalWith O (.leSlots a b) old new then none else some []
  | .leSlotsOff a b k => if evalWith O (.leSlotsOff a b k) old new then none else some []
  | .sumEq l r     => if evalWith O (.sumEq l r) old new then none else some []
  | .hashEq v b c  => if evalWith O (.hashEq v b c) old new then none else some []
  | .ran program   => if evalWith O (.ran program) old new then none else some []
  | .not q         => if evalWith O (.not q) old new then none else some []
  | .anyL ps       => if evalWith O (.anyL ps) old new then none else some []
/-- The first failing child of a conjunction, as a path whose head is the child's index. -/
def leafWithAll (O : Oracle) (ps : PredList) (old new : State) : Option (List Nat) :=
  match ps with
  | .nil => none
  | .cons q rest =>
      match leafWith O q old new with
      | some path => some (0 :: path)
      | none => (leafWithAll O rest old new).map shiftHead
end

mutual
theorem leafWith_none_iff (O : Oracle) :
    (p : Pred) → (old new : State) → (leafWith O p old new = none ↔ evalWith O p old new = true)
  | .eq _ _, _, _ | .le _ _, _, _ | .memberOf _ _, _, _ | .writeOnce _, _, _
  | .monotone _, _, _ | .witnessed _, _, _ | .eqSlots _ _, _, _ | .leSlots _ _, _, _
  | .leSlotsOff _ _ _, _, _ | .sumEq _ _, _, _ | .hashEq _ _ _, _, _ | .ran _, _, _ | .not _, _, _
  | .anyL _, _, _ => by
      simp only [leafWith]; split <;> simp_all
  | .allL ps, old, new => by
      simp only [leafWith, evalWith]
      exact leafWithAll_none_iff O ps old new
theorem leafWithAll_none_iff (O : Oracle) :
    (ps : PredList) → (old new : State) →
      (leafWithAll O ps old new = none ↔ evalWithAll O ps old new = true)
  | .nil, _, _ => by simp [leafWithAll, evalWithAll]
  | .cons q rest, old, new => by
      have hq := leafWith_none_iff O q old new
      have hr := leafWithAll_none_iff O rest old new
      simp only [leafWithAll, evalWithAll, Bool.and_eq_true]
      cases h : leafWith O q old new with
      | some path =>
          have : evalWith O q old new ≠ true := fun t => by rw [← hq] at t; rw [h] at t; cases t
          simp [this]
      | none =>
          have : evalWith O q old new = true := hq.mp h
          simp [this, Option.map_eq_none_iff, hr]
end

mutual
theorem leafWith_sound (O : Oracle) :
    (p : Pred) → (old new : State) → (path : List Nat) → leafWith O p old new = some path →
      ∃ q, p.subterm path = some q ∧ q.isLeaf = true ∧ evalWith O q old new = false
  | .eq _ _, _, _, _, h | .le _ _, _, _, _, h | .memberOf _ _, _, _, _, h
  | .writeOnce _, _, _, _, h | .monotone _, _, _, _, h | .witnessed _, _, _, _, h
  | .eqSlots _ _, _, _, _, h | .leSlots _ _, _, _, _, h | .leSlotsOff _ _ _, _, _, _, h
  | .sumEq _ _, _, _, _, h
  | .hashEq _ _ _, _, _, _, h | .ran _, _, _, _, h | .not _, _, _, _, h | .anyL _, _, _, _, h => by
      simp only [leafWith] at h
      split at h
      · cases h
      · rename_i rejected
        cases h
        exact ⟨_, rfl, rfl, by simpa using rejected⟩
  | .allL ps, old, new, path, h => by
      simp only [leafWith] at h
      obtain ⟨i, rest, q, rfl, sub, leaf, fails⟩ := leafWithAll_sound O ps old new path h
      exact ⟨q, by simpa [Pred.subterm] using sub, leaf, fails⟩
theorem leafWithAll_sound (O : Oracle) :
    (ps : PredList) → (old new : State) → (path : List Nat) → leafWithAll O ps old new = some path →
      ∃ i rest q, path = i :: rest ∧ PredList.subterm ps i rest = some q ∧ q.isLeaf = true ∧
        evalWith O q old new = false
  | .nil, _, _, _, h => by simp [leafWithAll] at h
  | .cons q qs, old, new, path, h => by
      simp only [leafWithAll] at h
      cases found : leafWith O q old new with
      | some sub =>
          rw [found] at h
          cases h
          obtain ⟨leaf, at_, isLeaf, fails⟩ := leafWith_sound O q old new sub found
          exact ⟨0, sub, leaf, rfl, by simpa [PredList.subterm] using at_, isLeaf, fails⟩
      | none =>
          rw [found] at h
          obtain ⟨tail, later, rfl⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨i, rest, leaf, rfl, at_, isLeaf, fails⟩ := leafWithAll_sound O qs old new tail later
          exact ⟨i + 1, rest, leaf, rfl, by simpa [PredList.subterm] using at_, isLeaf, fails⟩
end

/-- **`firstFailingLeaf`** — the path to the first failing leaf of the first-party `eval`
(`witnessed` fails closed, exactly as in `eval`), or `none` when the step is admitted. -/
def firstFailingLeaf (p : Pred) (old new : State) : Option (List Nat) :=
  leafWith failClosed p old new

/-- The explanation is the decision: it names nothing exactly when `eval` accepts. -/
theorem firstFailingLeaf_none_iff_eval (p : Pred) (old new : State) :
    firstFailingLeaf p old new = none ↔ eval p old new = true :=
  leafWith_none_iff failClosed p old new

/-- The named subterm exists, is a leaf, and `eval` rejects it on the same step. -/
theorem firstFailingLeaf_some_leaf (p : Pred) (old new : State) (path : List Nat)
    (named : firstFailingLeaf p old new = some path) :
    ∃ q, p.subterm path = some q ∧ q.isLeaf = true ∧ eval q old new = false :=
  leafWith_sound failClosed p old new path named

/-! ## Both poles on the J13 law

`field 2 monotone; field 2 in {0,1,2}` over the projection's own slot names
(`Kernel.DeclaredResourceProjection.fieldName 2 "after"`). -/

namespace LeafSample

/-- The write guard every game clause carries (`request/verb` 2 is `write`,
`CredentialAuthorityEntryCodec.verbTag`). -/
def onWrite (clause : Pred) : Pred := Pred.any [clause, .not (.eq "request/verb" 2)]

def boardLaw : Pred :=
  Pred.all [onWrite (.monotone "resource/field/2/after"),
    onWrite (.memberOf "resource/field/2/after" [0, 1, 2])]

/-- The projected step of a write moving field 2 from `a` to `b`: the old view reads the
committed value, the new view the candidate. -/
def before (a : Int) : State :=
  ⟨[("request/verb", 2), ("resource/field/2/before", a), ("resource/field/2/after", a)]⟩
def after (a b : Int) : State :=
  ⟨[("request/verb", 2), ("resource/field/2/before", a), ("resource/field/2/after", b),
    ("resource/field/2/delta", b - a)]⟩

/-- A read of field 2 at `a`: both views carry the committed value. -/
def read (a : Int) : State :=
  ⟨[("request/verb", 1), ("resource/field/2/before", a), ("resource/field/2/after", a)]⟩

theorem admitted_one_to_two : firstFailingLeaf boardLaw (before 1) (after 1 2) = none := by decide

theorem refused_two_to_one : firstFailingLeaf boardLaw (before 2) (after 2 1) = some [0] := by decide

theorem refused_two_to_one_names_clause :
    boardLaw.subterm [0] = some (onWrite (.monotone "resource/field/2/after")) := by decide

theorem refused_out_of_set : firstFailingLeaf boardLaw (before 2) (after 2 5) = some [1] := by decide

theorem read_admitted : firstFailingLeaf boardLaw (read 2) (read 2) = none := by decide

theorem sealed_names_itself : firstFailingLeaf (Pred.any []) (read 1) (read 1) = some [] := by
  decide

theorem open_admits : firstFailingLeaf (Pred.all []) (before 2) (after 2 1) = none := by decide

theorem negation_named : firstFailingLeaf (.not (Pred.all [])) (read 1) (read 1) = some [] := by
  decide

end LeafSample

/-- info: 'Minidregg.Pred.firstFailingLeaf_none_iff_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms firstFailingLeaf_none_iff_eval

/-- info: 'Minidregg.Pred.firstFailingLeaf_some_leaf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms firstFailingLeaf_some_leaf

/-- info: 'Minidregg.Pred.LeafSample.refused_two_to_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms LeafSample.refused_two_to_one

end Minidregg.Pred
