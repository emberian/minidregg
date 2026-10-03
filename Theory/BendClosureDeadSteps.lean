/- Actual Q0 capture: erased values keep their environment slots and source
syntax. The machine allocates the thunk but never evaluates it at this point. -/
import Theory.BendClosureValueSteps
import Theory.BendClosureBeta

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem closure_allocation_run (limits : Limits) (library : Library) (state : State)
    (pc environment pointer : Nat) (instruction : Code) (heap : Heap)
    (found : library.program.code[pc]? = some instruction)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure pc environment) = .ok (pointer, heap)) :
    (closure limits library pc environment).run state =
      .ok (pointer, allocationState state heap pointer (directData instruction)) := by
  cases instruction <;> simp [closure, BendClosureMachine.allocate, code, found,
    allocated, allocationState, directData] <;> rfl

theorem step_dead_pair (limits : Limits) (library : Library) (state : State)
    (pc environment first second pointer : Nat) (instruction : Code) (heap : Heap)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.tup .Q0 first second))
    (firstCode : library.program.code[first]? = some instruction)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure first environment) = .ok (pointer, heap))
    (room : state.stack.length < limits.frames) :
    step limits library state =
      {allocationState state heap pointer (directData instruction) with
        stack := .second .Q0 pointer :: state.stack, control := .evaluate second environment} := by
  cases instruction <;> simp [Quan.live, step, control, evaluate, code, found, closure,
    BendClosureMachine.allocate, firstCode, allocated, push, allocationState,
    directData, Nat.not_le_of_lt room, go] <;> rfl

theorem dead_pair_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment first second pointer : Nat) (instruction : Code) (heap : Heap)
    (a b : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.tup .Q0 first second))
    (firstCode : library.program.code[first]? = some instruction)
    (firstExact : CodeDenotes library.program first a)
    (secondExact : CodeDenotes library.program second b)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure first environment) = .ok (pointer, heap))
    (room : state.stack.length < limits.frames) :
    let source := plug contexts (Term.sub (Env.sub values) (.Tup .Q0 a b))
    StateDenotes book library.program state source ∧
      StateDenotes book library.program (step limits library state) source ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  have extension := allocate_extends allocated
  have head := allocate_term (.closure firstExact captured) allocated
  refine ⟨evaluate_state control (.exact (.tup found firstExact secondExact) captured) stack, ?_, ?_⟩
  · rw [step_dead_pair limits library state pc environment first second pointer instruction heap
      control found firstCode allocated room]
    exact evaluate_state
      (contexts := .second .Q0 (Term.sub (Env.sub values) a) (by intro impossible; cases impossible) :: contexts)
      rfl (.exact secondExact (captured.extends extension))
      (.cons (.second head (by intro impossible; cases impossible)) (stack.extends extension))
  · rw [step_dead_pair limits library state pc environment first second pointer instruction heap
      control found firstCode allocated room]
    rfl

theorem step_dead_let (limits : Limits) (library : Library) (state : State)
    (pc environment value body pointer nextEnvironment : Nat) (instruction : Code)
    (middle heap : Heap)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.lett .Q0 value body))
    (valueCode : library.program.code[value]? = some instruction)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure value environment) = .ok (pointer, middle))
    (installed : BendClosureArena.allocate limits.heap library.program.code.size
      middle (.environment pointer environment) = .ok (nextEnvironment, heap)) :
    step limits library state =
      {afterEnvironment (allocationState state middle pointer (directData instruction)) heap nextEnvironment with
        control := .evaluate body nextEnvironment, sourceSteps := state.sourceSteps + 1} := by
  cases instruction <;> simp [Quan.live, step, control, evaluate, code, found, closure,
    BendClosureMachine.allocate, valueCode, allocated, BendClosureMachine.bind, isData,
    installed, allocationState, afterEnvironment, directData, sourceStep, go] <;> rfl

theorem dead_let_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment value body pointer nextEnvironment : Nat) (instruction : Code)
    (middle heap : Heap) (v f : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.lett .Q0 value body))
    (valueCode : library.program.code[value]? = some instruction)
    (valueExact : CodeDenotes library.program value v)
    (bodyExact : CodeDenotes library.program body f)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure value environment) = .ok (pointer, middle))
    (installed : BendClosureArena.allocate limits.heap library.program.code.size
      middle (.environment pointer environment) = .ok (nextEnvironment, heap)) :
    let beforeSource := plug contexts (Term.sub (Env.sub values) (.Let .Q0 v f))
    let afterSource := plug contexts (Term.sub (Env.sub (Term.sub (Env.sub values) v :: values)) f)
    StateDenotes book library.program state beforeSource ∧
      StateDenotes book library.program (step limits library state) afterSource ∧
      Eval book beforeSource afterSource ∧
      (step limits library state).sourceSteps = state.sourceSteps + 1 := by
  dsimp only
  have firstExtension := allocate_extends allocated
  have secondExtension := allocate_extends installed
  have head := allocate_term (.closure valueExact captured) allocated
  have newCaptured := allocate_environment (.cons head (captured.extends firstExtension)) installed
  refine ⟨evaluate_state control (.exact (.lett found valueExact bodyExact) captured) stack, ?_, ?_, ?_⟩
  · rw [step_dead_let limits library state pc environment value body pointer nextEnvironment
      instruction middle heap control found valueCode allocated installed]
    exact evaluate_state (contexts := contexts) rfl (.exact bodyExact newCaptured)
      ((stack.extends firstExtension).extends secondExtension)
  · apply plug_eval contexts
    rw [captured_body_inst]
    exact .unlet (by intro impossible; cases impossible) (by intro impossible; cases impossible)
  · rw [step_dead_let limits library state pc environment value body pointer nextEnvironment
      instruction middle heap control found valueCode allocated installed]

#assert_axioms closure_allocation_run
#assert_axioms step_dead_pair
#assert_axioms dead_pair_source
#assert_axioms step_dead_let
#assert_axioms dead_let_source
end Minidregg.Theory.BendClosureSimulation
