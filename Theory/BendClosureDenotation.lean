/- Unique exact decoding of the actual immutable Bend heap. These proofs
compare literal stored rows and the publication CodeDenotes relation. They do
not infer Value/Data from pointer residency or erase Q0 captured terms. -/
import Theory.BendClosureCodeRefinement

namespace Minidregg.Theory.BendClosureArena
open BendTT
set_option autoImplicit false

theorem Denotes.functional {program : Program} {heap : Heap} {pointer : Nat}
    {left right : Term} (leftExact : Denotes program heap pointer left)
    (rightExact : Denotes program heap pointer right) : left = right := by
  have unique : ∀ other, Denotes program heap pointer other → left = other := by
    apply @Denotes.rec program heap
      (fun pointer term _ => ∀ other, Denotes program heap pointer other → term = other)
      (fun pointer values _ => ∀ other, EnvironmentDenotes program heap pointer other → values = other)
      ?_ ?_ ?_ ?_ ?_ pointer left leftExact
    · intro pointer code environment term values row source captured capturedIH other otherExact
      cases otherExact with
      | closure row' source' captured' =>
        have same := Option.some.inj (row.symm.trans row')
        cases same
        rw [source.functional source', capturedIH _ captured']
      | pair row' _ _ => simp_all
      | application row' _ _ => simp_all
    · intro pointer q first second A B row firstExact secondExact firstIH secondIH other otherExact
      cases otherExact with
      | closure row' _ _ => simp_all
      | pair row' first' second' =>
        have same := Option.some.inj (row.symm.trans row')
        cases same
        rw [firstIH _ first', secondIH _ second']
      | application row' _ _ => simp_all
    · intro pointer q function argument F X row functionExact argumentExact functionIH argumentIH other otherExact
      cases otherExact with
      | closure row' _ _ => simp_all
      | pair row' _ _ => simp_all
      | application row' function' argument' =>
        have same := Option.some.inj (row.symm.trans row')
        cases same
        rw [functionIH _ function', argumentIH _ argument']
    · intro pointer row other otherExact
      cases otherExact with
      | nil => rfl
      | cons row' _ _ => simp_all
    · intro pointer value tail term values row valueExact tailExact valueIH tailIH other otherExact
      cases otherExact with
      | nil row' => simp_all
      | cons row' value' tail' =>
        have same := Option.some.inj (row.symm.trans row')
        cases same
        rw [valueIH _ value', tailIH _ tail']

  exact unique right rightExact

theorem EnvironmentDenotes.functional {program : Program} {heap : Heap} {pointer : Nat}
    {left right : Env} (leftExact : EnvironmentDenotes program heap pointer left)
    (rightExact : EnvironmentDenotes program heap pointer right) : left = right := by
  have unique : ∀ other, EnvironmentDenotes program heap pointer other → left = other := by
    apply @EnvironmentDenotes.rec program heap
      (fun pointer term _ => ∀ other, Denotes program heap pointer other → term = other)
      (fun pointer values _ => ∀ other, EnvironmentDenotes program heap pointer other → values = other)
      ?_ ?_ ?_ ?_ ?_ pointer left leftExact
    · intro pointer code environment term values row source captured capturedIH other otherExact
      cases otherExact with
      | closure row' source' captured' =>
        have same := Option.some.inj (row.symm.trans row')
        cases same
        rw [source.functional source', capturedIH _ captured']
      | pair row' _ _ => simp_all
      | application row' _ _ => simp_all
    · intro pointer q first second A B row firstExact secondExact firstIH secondIH other otherExact
      cases otherExact with
      | closure row' _ _ => simp_all
      | pair row' first' second' =>
        have same := Option.some.inj (row.symm.trans row')
        cases same
        rw [firstIH _ first', secondIH _ second']
      | application row' _ _ => simp_all
    · intro pointer q function argument F X row functionExact argumentExact functionIH argumentIH other otherExact
      cases otherExact with
      | closure row' _ _ => simp_all
      | pair row' _ _ => simp_all
      | application row' function' argument' =>
        have same := Option.some.inj (row.symm.trans row')
        cases same
        rw [functionIH _ function', argumentIH _ argument']
    · intro pointer row other otherExact
      cases otherExact with
      | nil => rfl
      | cons row' _ _ => simp_all
    · intro pointer value tail term values row valueExact tailExact valueIH tailIH other otherExact
      cases otherExact with
      | nil row' => simp_all
      | cons row' value' tail' =>
        have same := Option.some.inj (row.symm.trans row')
        cases same
        rw [valueIH _ value', tailIH _ tail']

  exact unique right rightExact

#assert_axioms Denotes.functional
#assert_axioms EnvironmentDenotes.functional
end Minidregg.Theory.BendClosureArena

