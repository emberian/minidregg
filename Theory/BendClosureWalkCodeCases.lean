/- Actual case-tree ROM and heap inversions for the reachable-state invariant. -/
import Theory.BendClosureReadySpine

namespace Minidregg.Theory.BendClosureArena
open BendTT
set_option autoImplicit false

theorem CodeDenotes.lambda_fields {program : Program} {pointer : Nat} {source : Term}
    (q : Quan) (body : Nat) (exact : CodeDenotes program pointer source)
    (found : program.code[pointer]? = some (.lam q body)) :
    ∃ f, source = .Lam q f ∧ CodeDenotes program body f := by
  cases exact <;> simp_all

theorem CodeDenotes.projection_fields {program : Program} {pointer : Nat} {source : Term}
    (handler : Nat) (exact : CodeDenotes program pointer source)
    (found : program.code[pointer]? = some (.prj handler)) :
    ∃ f, source = .Prj f ∧ CodeDenotes program handler f := by
  cases exact <;> simp_all

#assert_axioms CodeDenotes.lambda_fields
#assert_axioms CodeDenotes.projection_fields
end Minidregg.Theory.BendClosureArena

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem RetainedReady.pair_fields {book : Book} {program : Program} {heap : Heap}
    {pointer first second : Nat} {q : Quan} {source : Term}
    (ready : RetainedReady book program heap pointer source)
    (found : heap.get? pointer = some (.pair q first second)) :
    ∃ a b, source = .Tup q a b ∧ RetainedReady book program heap first a ∧
      RetainedReady book program heap second b ∧ Value book (.Tup q a b) := by
  cases ready with
  | closure other code captured => rw [found] at other; cases other
  | application other left right value => rw [found] at other; cases other
  | pair other left right value =>
    rw [found] at other
    cases other
    exact ⟨_,_,rfl,left,right,value⟩

#assert_axioms RetainedReady.pair_fields
end Minidregg.Theory.BendClosureSimulation
