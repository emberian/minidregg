/- Concrete live affine beta step of the actual closure machine. -/
import Theory.BendClosureControlSteps
import Theory.BendClosureAllocation

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

/-- The exact cache update made by the controller when an environment row
is appended. Environment rows never certify a source Data term. -/
def afterEnvironment (state : State) (heap : Heap) (pointer : Nat) : State :=
  {state with heap, data := (state.data.toList.zipIdx.map fun p =>
    if p.2 = pointer then false else p.1).toArray}

theorem bind_q1 (limits : Limits) (library : Library) (state : State)
    (value environment pointer : Nat) (heap : Heap)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.environment value environment) = .ok (pointer, heap)) :
    (BendClosureMachine.bind limits library .Q1 value environment).run state =
      .ok (pointer, afterEnvironment state heap pointer) := by
  simp [BendClosureMachine.bind, isData, BendClosureMachine.allocate, allocated, afterEnvironment]
  rfl

theorem step_beta_q1 (limits : Limits) (library : Library) (state : State)
    (function argument pc environment body nextEnvironment : Nat) (heap : Heap)
    (control : state.control = .apply .Q1 function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.lam .Q1 body))
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.environment argument environment) = .ok (nextEnvironment, heap)) :
    step limits library state =
      {afterEnvironment state heap nextEnvironment with control := .evaluate body nextEnvironment, sourceSteps := state.sourceSteps + 1} := by
  simp [step, control, BendClosureMachine.apply, row, functionRow, code, instruction,
    BendClosureMachine.bind, isData, BendClosureMachine.allocate, allocated, sourceStep, go,
    afterEnvironment]
  rfl

/-- Full before/after source reification for one actual beta microstep, in an
arbitrary represented stack. Q1 avoids Data duplication but still evaluates
its live argument. Both code and captured environment are exact premises. -/
theorem beta_q1_source {book : Book} (limits : Limits) (library : Library)
    (state : State) (function argument pc environment body nextEnvironment : Nat)
    (heap : Heap) (source argumentSource : Term) (values : Env)
    (contexts : List (Context book))
    (control : state.control = .apply .Q1 function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.lam .Q1 body))
    (bodyExact : CodeDenotes library.program body source)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (argumentExact : Denotes library.program state.heap argument argumentSource)
    (argumentValue : Value book argumentSource)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.environment argument environment) = .ok (nextEnvironment, heap)) :
    let beforeSource := plug contexts
      (.App .Q1 (Term.sub (Env.sub values) (.Lam .Q1 source)) argumentSource)
    let afterSource := plug contexts (Term.sub (Env.sub (argumentSource :: values)) source)
    StateDenotes book library.program state beforeSource ∧
      StateDenotes book library.program (step limits library state) afterSource ∧
      Eval book beforeSource afterSource ∧
      (step limits library state).sourceSteps = state.sourceSteps + 1 := by
  dsimp only
  have extension := allocate_extends allocated
  have newCaptured : EnvironmentDenotes library.program heap nextEnvironment
      (argumentSource :: values) :=
    allocate_environment (.cons argumentExact captured) allocated
  have functionExact : Denotes library.program state.heap function
      (Term.sub (Env.sub values) (.Lam .Q1 source)) :=
    .closure functionRow (.lam instruction bodyExact) captured
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply StateDenotes.exact (contexts := contexts)
    · rw [control]
      exact .apply functionExact argumentExact .lam (fun _ => argumentValue)
    · exact stack
    · intro pointer impossible
      rw [control] at impossible
      cases impossible
  · rw [step_beta_q1 limits library state function argument pc environment body
      nextEnvironment heap control functionRow instruction allocated]
    exact evaluate_state (contexts := contexts) rfl (.exact bodyExact newCaptured)
      (stack.extends extension)
  · apply plug_eval contexts
    rw [captured_body_inst]
    exact .beta rfl (fun _ => argumentValue) (by intro impossible; cases impossible)
  · rw [step_beta_q1 limits library state function argument pc environment body
      nextEnvironment heap control functionRow instruction allocated]

#assert_axioms bind_q1
#assert_axioms step_beta_q1
#assert_axioms beta_q1_source

theorem step_beta (limits : Limits) (library : Library) (state : State)
    (function argument pc environment body nextEnvironment : Nat) (heap : Heap)
    (binder quantity : Quan)
    (control : state.control = .apply quantity function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.lam binder body))
    (compatible : binder.live = quantity.live)
    (copied : binder = .Q2 → state.data[argument]?.getD false = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.environment argument environment) = .ok (nextEnvironment, heap)) :
    step limits library state =
      {afterEnvironment state heap nextEnvironment with control := .evaluate body nextEnvironment, sourceSteps := state.sourceSteps + 1} := by
  cases binder <;> cases quantity <;>
    simp_all [Quan.live, step, BendClosureMachine.apply, row, code,
      BendClosureMachine.bind, isData, BendClosureMachine.allocate, sourceStep, go,
      afterEnvironment]
  all_goals rfl

/-- All source quantities: Q0 retains the unevaluated exact argument; live
arguments require Value, and a Q2 binder consumes a certified true Data bit.
Neither code denotation nor heap residency substitutes for these premises. -/
theorem beta_source {book : Book} (limits : Limits) (library : Library)
    (state : State) (function argument pc environment body nextEnvironment : Nat)
    (heap : Heap) (source argumentSource : Term) (values : Env)
    (contexts : List (Context book)) (binder quantity : Quan)
    (control : state.control = .apply quantity function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.lam binder body))
    (bodyExact : CodeDenotes library.program body source)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (argumentExact : Denotes library.program state.heap argument argumentSource)
    (argumentValue : quantity.live = true → Value book argumentSource)
    (compatible : binder.live = quantity.live)
    (copied : binder = .Q2 → state.data[argument]?.getD false = true)
    (cache : CacheCertified library.program state.heap state.data)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.environment argument environment) = .ok (nextEnvironment, heap)) :
    let beforeSource := plug contexts
      (.App quantity (Term.sub (Env.sub values) (.Lam binder source)) argumentSource)
    let afterSource := plug contexts (Term.sub (Env.sub (argumentSource :: values)) source)
    StateDenotes book library.program state beforeSource ∧
      StateDenotes book library.program (step limits library state) afterSource ∧
      Eval book beforeSource afterSource ∧
      (step limits library state).sourceSteps = state.sourceSteps + 1 := by
  dsimp only
  have extension := allocate_extends allocated
  have newCaptured : EnvironmentDenotes library.program heap nextEnvironment
      (argumentSource :: values) :=
    allocate_environment (.cons argumentExact captured) allocated
  have functionExact : Denotes library.program state.heap function
      (Term.sub (Env.sub values) (.Lam binder source)) :=
    .closure functionRow (.lam instruction bodyExact) captured
  have data : binder = .Q2 → Data argumentSource := by
    intro q2
    exact cache.sound (cache_bit_of_getD (copied q2)) argumentExact
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply StateDenotes.exact (contexts := contexts)
    · rw [control]
      exact .apply functionExact argumentExact .lam argumentValue
    · exact stack
    · intro pointer impossible
      rw [control] at impossible
      cases impossible
  · rw [step_beta limits library state function argument pc environment body
      nextEnvironment heap binder quantity control functionRow instruction compatible copied allocated]
    exact evaluate_state (contexts := contexts) rfl (.exact bodyExact newCaptured)
      (stack.extends extension)
  · apply plug_eval contexts
    rw [captured_body_inst]
    exact .beta compatible argumentValue data
  · rw [step_beta limits library state function argument pc environment body
      nextEnvironment heap binder quantity control functionRow instruction compatible copied allocated]

#assert_axioms step_beta
#assert_axioms beta_source

end Minidregg.Theory.BendClosureSimulation

