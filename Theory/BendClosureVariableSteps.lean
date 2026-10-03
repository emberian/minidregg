/- Variable lookup through the actual closure machine. Captured closures reopen
with their original environment; pair/application fast returns require source
Value. These are concrete source-preserving branches, not assumed poststates. -/
import Theory.BendClosureReadiness
import Theory.BendClosureControlSteps
import Theory.BendClosureCache

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem step_variable (limits : Limits) (library : Library) (state : State)
    (pc environment index : Nat)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.var index)) :
    step limits library state = {state with control := .lookup index environment .evaluateValue} := by
  simp [step, control, evaluate, code, found, go]
  rfl

theorem variable_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment index : Nat) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.var index))
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
    StateDenotes book library.program state (plug contexts (Env.sub values index)) ∧
    StateDenotes book library.program (step limits library state) (plug contexts (Env.sub values index)) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨?_, ?_, ?_⟩
  · exact evaluate_state control (.exact (.var found) captured) stack
  · rw [step_variable limits library state pc environment index control found]
    exact StateDenotes.exact (.lookupValue captured) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_variable limits library state pc environment index control found]

theorem step_lookup_zero_closure (limits : Limits) (library : Library) (state : State)
    (environment pointer tail pc capturedEnvironment : Nat)
    (control : state.control = .lookup 0 environment .evaluateValue)
    (found : state.heap.get? environment = some (.environment pointer tail))
    (head : state.heap.get? pointer = some (.closure pc capturedEnvironment)) :
    step limits library state = {state with control := .evaluate pc capturedEnvironment} := by
  simp [step, control, lookup, row, found, evaluatePointer, head, go]
  rfl

theorem step_lookup_zero_pair (limits : Limits) (library : Library) (state : State)
    (environment pointer tail first second : Nat) (quantity : Quan)
    (control : state.control = .lookup 0 environment .evaluateValue)
    (found : state.heap.get? environment = some (.environment pointer tail))
    (head : state.heap.get? pointer = some (.pair quantity first second)) :
    step limits library state = {state with control := .returned pointer} := by
  simp [step, control, lookup, row, found, evaluatePointer, head, go]
  rfl

theorem step_lookup_zero_application (limits : Limits) (library : Library) (state : State)
    (environment pointer tail function argument : Nat) (quantity : Quan)
    (control : state.control = .lookup 0 environment .evaluateValue)
    (found : state.heap.get? environment = some (.environment pointer tail))
    (head : state.heap.get? pointer = some (.application quantity function argument)) :
    step limits library state = {state with control := .returned pointer} := by
  simp [step, control, lookup, row, found, evaluatePointer, head, go]
  rfl

/-- All concrete representations of a retained variable are covered. In
particular a closure need not already be a Value: it is reopened, not returned.
The two direct-return cases consume the independently required readiness proof. -/
theorem lookup_zero_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (environment pointer tail : Nat) (source : Term) (values : Env)
    (contexts : List (Context book))
    (control : state.control = .lookup 0 environment .evaluateValue)
    (found : state.heap.get? environment = some (.environment pointer tail))
    (headReady : ReadyPointer book library.program state.heap pointer source)
    (captured : EnvironmentDenotes library.program state.heap tail values)
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
    StateDenotes book library.program state (plug contexts source) ∧
    StateDenotes book library.program (step limits library state) (plug contexts source) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  have initial : StateDenotes book library.program state (plug contexts source) := by
    apply StateDenotes.exact (contexts := contexts)
    · rw [control]
      simpa only [Env.sub] using ControlDenotes.lookupValue (.cons found headReady.1 captured)
    · exact stack
    · intro next impossible
      rw [control] at impossible
      cases impossible
  refine ⟨initial, ?_⟩
  have exact := headReady.1
  cases exact with
  | closure head code capturedHead =>
      rw [step_lookup_zero_closure limits library state environment pointer tail _ _ control found head]
      exact ⟨StateDenotes.exact (.evaluate (.exact code capturedHead)) stack
        (by intro next impossible; cases impossible), rfl⟩
  | pair head first second =>
      have value := ready_fast_value headReady (by
        intro pc env different
        rw [head] at different
        cases different)
      rw [step_lookup_zero_pair limits library state environment pointer tail _ _ _ control found head]
      exact ⟨StateDenotes.exact (.returned (.pair head first second) value) stack
        (by intro next impossible; cases impossible), rfl⟩
  | application head function argument =>
      have value := ready_fast_value headReady (by
        intro pc env different
        rw [head] at different
        cases different)
      rw [step_lookup_zero_application limits library state environment pointer tail _ _ _ control found head]
      exact ⟨StateDenotes.exact (.returned (.application head function argument) value) stack
        (by intro next impossible; cases impossible), rfl⟩

/-- Reference entry allocates its real closure before walking the named Book
body. It is administrative; this is not yet the later Eval.call commit. -/
theorem step_reference (limits : Limits) (library : Library) (state : State)
    (pc environment index pointer : Nat) (heap : Heap)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.ref index))
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure pc environment) = .ok (pointer, heap)) :
    step limits library state =
      {allocationState state heap pointer false with control := .unspine pointer pointer []} := by
  simp [step, control, evaluate, code, found, closure, BendClosureMachine.allocate,
    allocated, allocationState, go]
  rfl

theorem reference_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment index pointer : Nat) (heap : Heap) (name : String) (values : Env)
    (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.ref index))
    (named : library.program.names[index]? = some name)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.closure pc environment) = .ok (pointer, heap)) :
    StateDenotes book library.program state (plug contexts (.Ref name)) ∧
    StateDenotes book library.program (step limits library state) (plug contexts (.Ref name)) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  have codeExact : CodeDenotes library.program pc (.Ref name) := .ref found named
  have pointerExact : Denotes library.program heap pointer (.Ref name) :=
    allocate_term (.closure codeExact captured) allocated
  refine ⟨evaluate_state control (.exact codeExact captured) stack, ?_, ?_⟩
  · rw [step_reference limits library state pc environment index pointer heap control found allocated]
    exact StateDenotes.exact (.unspine pointerExact pointerExact .nil rfl .nil)
      (stack.extends (allocate_extends allocated))
      (by intro next impossible; cases impossible)
  · rw [step_reference limits library state pc environment index pointer heap control found allocated]
    rfl

#assert_axioms step_reference
#assert_axioms reference_source
#assert_axioms step_variable
#assert_axioms variable_source
#assert_axioms step_lookup_zero_closure
#assert_axioms step_lookup_zero_pair
#assert_axioms step_lookup_zero_application
#assert_axioms lookup_zero_source
end Minidregg.Theory.BendClosureSimulation
