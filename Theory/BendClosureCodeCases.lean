/- Constructor inversion for the validator-produced source correspondence.
These inspect actual ROM lookups while retaining the complete source children. -/
import Theory.BendClosureCodeRefinement

namespace Minidregg.Theory.BendClosureArena
open BendTT
set_option autoImplicit false

theorem CodeDenotes.application_fields {program : Program} {pointer : Nat} {source : Term}
    (q : Quan) (function argument : Nat) (exact : CodeDenotes program pointer source)
    (found : program.code[pointer]? = some (.app q function argument)) :
    ∃ (f x : Term), source = .App q f x ∧ CodeDenotes program function f ∧ CodeDenotes program argument x := by
  cases exact <;> simp_all

theorem CodeDenotes.annotation_fields {program : Program} {pointer : Nat} {source : Term}
    (value type : Nat) (exact : CodeDenotes program pointer source)
    (found : program.code[pointer]? = some (.ann value type)) :
    ∃ (x t : Term), source = .Ann x t ∧ CodeDenotes program value x ∧ CodeDenotes program type t := by
  cases exact <;> simp_all

theorem CodeDenotes.let_fields {program : Program} {pointer : Nat} {source : Term}
    (q : Quan) (value body : Nat) (exact : CodeDenotes program pointer source)
    (found : program.code[pointer]? = some (.lett q value body)) :
    ∃ (v f : Term), source = .Let q v f ∧ CodeDenotes program value v ∧ CodeDenotes program body f := by
  cases exact <;> simp_all

theorem CodeDenotes.pair_fields {program : Program} {pointer : Nat} {source : Term}
    (q : Quan) (first second : Nat) (exact : CodeDenotes program pointer source)
    (found : program.code[pointer]? = some (.tup q first second)) :
    ∃ (a b : Term), source = .Tup q a b ∧ CodeDenotes program first a ∧ CodeDenotes program second b := by
  cases exact <;> simp_all

theorem CodeDenotes.rewrite_fields {program : Program} {pointer : Nat} {source : Term}
    (evidence motive body : Nat) (exact : CodeDenotes program pointer source)
    (found : program.code[pointer]? = some (.rwt evidence motive body)) :
    ∃ (e p f : Term), source = .Rwt e p f ∧ CodeDenotes program evidence e ∧ CodeDenotes program motive p ∧ CodeDenotes program body f := by
  cases exact <;> simp_all

theorem CodeDenotes.code_exists {program : Program} {pointer : Nat} {source : Term}
    (exact : CodeDenotes program pointer source) : ∃ instruction, program.code[pointer]? = some instruction := by
  cases exact <;> exact ⟨_,by assumption⟩

#assert_axioms CodeDenotes.application_fields
#assert_axioms CodeDenotes.annotation_fields
#assert_axioms CodeDenotes.let_fields
#assert_axioms CodeDenotes.pair_fields
#assert_axioms CodeDenotes.rewrite_fields
#assert_axioms CodeDenotes.code_exists
end Minidregg.Theory.BendClosureArena
