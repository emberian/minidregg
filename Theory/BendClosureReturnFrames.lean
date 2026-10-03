/- Actual return continuations: pair construction, live let installation and
rewrite commit. Source and cache premises concern the old state only. -/
import Theory.BendClosureReturnSteps
import Theory.BendClosureBeta
import Theory.BendClosureCache

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem step_return_first (limits : Limits) (library : Library) (state : State)
    (pointer second environment : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (control : state.control = .returned pointer)
    (stack : state.stack = .first q second environment :: rest)
    (room : rest.length < limits.frames) :
    step limits library state =
      {state with stack := .second q pointer :: rest, control := .evaluate second environment} := by
  simp [step, control, returnValue, stack, push, Nat.not_le_of_lt room, go]
  rfl

theorem return_first_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pointer second environment : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (a b : Term) (contexts : List (Context book))
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .first q second environment :: rest)
    (head : Denotes library.program state.heap pointer a) (value : Value book a)
    (secondExact : ClosureDenotes library.program state.heap second environment b)
    (live : q.live = true) (stack : StackDenotes book library.program state.heap rest contexts)
    (room : rest.length < limits.frames) :
    StateDenotes book library.program state (plug contexts (.Tup q a b)) ∧
      StateDenotes book library.program (step limits library state) (plug contexts (.Tup q a b)) ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨?_, ?_, ?_⟩
  · exact returned_state (contexts := .first q b live :: contexts) control head value
      (by rw [stackShape]; exact .cons (.first secondExact live) stack)
  · rw [step_return_first limits library state pointer second environment q rest control stackShape room]
    exact evaluate_state (contexts := .second q a (fun _ => value) :: contexts) rfl secondExact
      (.cons (.second head (fun _ => value)) stack)
  · rw [step_return_first limits library state pointer second environment q rest control stackShape room]

theorem step_return_second (limits : Limits) (library : Library) (state : State)
    (pointer first result : Nat) (q : Quan) (heap : Heap) (rest : List BendClosureMachine.Frame)
    (control : state.control = .returned pointer)
    (stack : state.stack = .second q first :: rest)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.pair q first pointer) = .ok (result,heap)) :
    step limits library state =
      {allocationState state heap result
        ((!q.live || state.data[first]?.getD false) && state.data[pointer]?.getD false) with
        stack := rest, control := .returned result} := by
  simp [step, control, returnValue, stack, BendClosureMachine.allocate, allocated, allocationState, go]
  rfl

theorem return_second_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pointer first result : Nat) (q : Quan) (heap : Heap) (rest : List BendClosureMachine.Frame)
    (a b : Term) (contexts : List (Context book))
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .second q first :: rest)
    (firstExact : Denotes library.program state.heap first a)
    (firstValue : q.live = true → Value book a)
    (secondExact : Denotes library.program state.heap pointer b) (secondValue : Value book b)
    (stack : StackDenotes book library.program state.heap rest contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.pair q first pointer) = .ok (result,heap)) :
    StateDenotes book library.program state (plug contexts (.Tup q a b)) ∧
      StateDenotes book library.program (step limits library state) (plug contexts (.Tup q a b)) ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨?_, ?_, ?_⟩
  · exact returned_state (contexts := .second q a firstValue :: contexts) control secondExact secondValue
      (by rw [stackShape]; exact .cons (.second firstExact firstValue) stack)
  · rw [step_return_second limits library state pointer first result q heap rest control stackShape allocated]
    exact returned_state (contexts := contexts) rfl (allocate_term (.pair firstExact secondExact) allocated)
      (.tup firstValue secondValue) (stack.extends (allocate_extends allocated))
  · rw [step_return_second limits library state pointer first result q heap rest control stackShape allocated]
    rfl

theorem step_return_let (limits : Limits) (library : Library) (state : State)
    (pointer body environment nextEnvironment : Nat) (q : Quan) (heap : Heap)
    (rest : List BendClosureMachine.Frame)
    (control : state.control = .returned pointer)
    (stack : state.stack = .lett q body environment :: rest)
    (copied : q = .Q2 → state.data[pointer]?.getD false = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.environment pointer environment) = .ok (nextEnvironment,heap)) :
    step limits library state =
      {afterEnvironment state heap nextEnvironment with
        stack := rest, control := .evaluate body nextEnvironment, sourceSteps := state.sourceSteps + 1} := by
  cases q <;> simp_all [step, returnValue, BendClosureMachine.bind, isData,
    BendClosureMachine.allocate, afterEnvironment, sourceStep, go]
  all_goals rfl

theorem return_let_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pointer body environment nextEnvironment : Nat) (q : Quan) (heap : Heap)
    (rest : List BendClosureMachine.Frame) (v f : Term) (values : Env)
    (contexts : List (Context book))
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .lett q body environment :: rest)
    (head : Denotes library.program state.heap pointer v) (value : Value book v)
    (bodyExact : CodeDenotes library.program body f)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (live : q.live = true)
    (copied : q = .Q2 → state.data[pointer]?.getD false = true)
    (cache : CacheCertified library.program state.heap state.data)
    (stack : StackDenotes book library.program state.heap rest contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.environment pointer environment) = .ok (nextEnvironment,heap)) :
    let beforeSource := plug contexts (.Let q v (Term.sub (Subst.up (Env.sub values)) f))
    let afterSource := plug contexts (Term.sub (Env.sub (v :: values)) f)
    StateDenotes book library.program state beforeSource ∧
      StateDenotes book library.program (step limits library state) afterSource ∧
      Eval book beforeSource afterSource ∧
      (step limits library state).sourceSteps = state.sourceSteps + 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact returned_state (contexts := .lett q (Term.sub (Subst.up (Env.sub values)) f) live :: contexts)
      control head value (by rw [stackShape]; exact .cons (.lett (.exact bodyExact captured) live) stack)
  · rw [step_return_let limits library state pointer body environment nextEnvironment q heap rest
      control stackShape copied allocated]
    exact evaluate_state (contexts := contexts) rfl
      (.exact bodyExact (allocate_environment (.cons head captured) allocated))
      (stack.extends (allocate_extends allocated))
  · apply plug_eval contexts
    rw [captured_body_inst]
    exact .unlet (fun _ => value) (fun q2 => cache.sound (cache_bit_of_getD (copied q2)) head)
  · rw [step_return_let limits library state pointer body environment nextEnvironment q heap rest
      control stackShape copied allocated]

#assert_axioms step_return_first
#assert_axioms return_first_source
#assert_axioms step_return_second
#assert_axioms return_second_source
#assert_axioms step_return_let
#assert_axioms return_let_source
end Minidregg.Theory.BendClosureSimulation
