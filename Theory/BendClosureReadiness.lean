/- Readiness follows retained environment edges, not all application rows.
An original call may be reducible while it is being unspined/walked. This
relation justifies evaluatePointer's fast return for captured pair/application
pointers, while allowing closure pointers to reopen exact Q0 thunks. -/
import Theory.BendClosureSimulation

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

inductive ReadyEnvironment (book : Book) (program : Program) (heap : Heap) :
    Nat → Env → Prop
  | nil {pointer : Nat} :
      heap.get? pointer = some .nil → ReadyEnvironment book program heap pointer []
  | cons {pointer value tail : Nat} {source : Term} {values : Env} :
      heap.get? pointer = some (.environment value tail) →
      ReadyPointer book program heap value source →
      ReadyEnvironment book program heap tail values →
      ReadyEnvironment book program heap pointer (source :: values)

theorem ReadyEnvironment.denotes {book : Book} {program : Program} {heap : Heap}
    {pointer : Nat} {values : Env} (ready : ReadyEnvironment book program heap pointer values) :
    EnvironmentDenotes program heap pointer values := by
  induction ready with
  | nil row => exact .nil row
  | cons row head tail ih => exact .cons row head.1 ih

theorem ReadyEnvironment.extends {book : Book} {program : Program} {old next : Heap}
    {pointer : Nat} {values : Env} (ready : ReadyEnvironment book program old pointer values)
    (extension : Extends old next) : ReadyEnvironment book program next pointer values := by
  induction ready with
  | nil row => exact .nil (extension _ _ row)
  | cons row head tail ih => exact .cons (extension _ _ row) (head.extends extension) ih

theorem ReadyEnvironment.lookup {book : Book} {program : Program} {heap : Heap}
    (index : Nat) {environment : Nat} {values : Env} {source : Term}
    (ready : ReadyEnvironment book program heap environment values)
    (found : values[index]? = some source) :
    ∃ pointer, LookupPath heap index environment pointer ∧
      ReadyPointer book program heap pointer source := by
  induction index generalizing environment values with
  | zero =>
    cases ready with
    | nil row => simp at found
    | cons row head tail =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst source
      exact ⟨_, .zero row, head⟩
  | succ index ih =>
    cases ready with
    | nil row => simp at found
    | cons row head tail =>
      simp only [List.getElem?_cons_succ] at found
      obtain ⟨pointer, path, exact⟩ := ih tail found
      exact ⟨pointer, .succ row path, exact⟩

/-- A Value is ready regardless of its concrete term-row representation.
The converse is deliberately false: a closure may be a retained dead thunk. -/
theorem ready_of_value {book : Book} {program : Program} {heap : Heap}
    {pointer : Nat} {source : Term} (exact : Denotes program heap pointer source)
    (value : Value book source) : ReadyPointer book program heap pointer source :=
  ⟨exact, Or.inr value⟩

theorem ready_closure {book : Book} {program : Program} {heap : Heap}
    {pointer pc environment : Nat} {source : Term} {values : Env}
    (row : heap.get? pointer = some (.closure pc environment))
    (code : CodeDenotes program pc source)
    (captured : EnvironmentDenotes program heap environment values) :
    ReadyPointer book program heap pointer (Term.sub (Env.sub values) source) :=
  ⟨.closure row code captured, Or.inl ⟨pc, environment, row⟩⟩

/-- For the two fast-return row forms, readiness supplies actual source Value.
No such inference is made for a closure row. -/
theorem ready_fast_value {book : Book} {program : Program} {heap : Heap}
    {pointer : Nat} {source : Term}
    (ready : ReadyPointer book program heap pointer source)
    (notClosure : ∀ pc environment, heap.get? pointer ≠ some (.closure pc environment)) :
    Value book source := by
  rcases ready.2 with closure | value
  · obtain ⟨pc, environment, row⟩ := closure
    exact False.elim (notClosure pc environment row)
  · exact value

#assert_axioms ReadyEnvironment.denotes
#assert_axioms ReadyEnvironment.extends
#assert_axioms ReadyEnvironment.lookup
#assert_axioms ready_of_value
#assert_axioms ready_closure
#assert_axioms ready_fast_value
end Minidregg.Theory.BendClosureSimulation

