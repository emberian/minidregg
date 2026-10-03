/- Retained focus at the actual evaluator/return boundary. This strengthens
source reification with recursively valid captured environments; it does not
assert termination or readiness of arbitrary resident call-spine rows. -/
import Theory.BendClosureRetainedCaptures
import Theory.BendClosureKnownArgument

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

inductive RetainedFocus (book : Book) (program : Program) (heap : Heap) : Control → Term → Prop
  | evaluate {pc environment : Nat} {source : Term} {values : Env} :
      CodeDenotes program pc source → CapturedReady book program heap environment values →
      RetainedFocus book program heap (.evaluate pc environment) (Term.sub (Env.sub values) source)
  | returned {pointer : Nat} {source : Term} :
      RetainedReady book program heap pointer source → Value book source →
      RetainedFocus book program heap (.returned pointer) source
  | apply {q : Quan} {function argument : Nat} {f x : Term} :
      RetainedReady book program heap function f → RetainedReady book program heap argument x →
      Value book f → (q.live = true → Value book x) →
      RetainedFocus book program heap (.apply q function argument) (.App q f x)
  | complete {pointer : Nat} {source : Term} :
      RetainedReady book program heap pointer source → Value book source →
      RetainedFocus book program heap (.complete pointer) source

theorem RetainedFocus.denotes {book : Book} {program : Program} {heap : Heap}
    {control : Control} {source : Term} (ready : RetainedFocus book program heap control source) :
    ControlDenotes book program heap control source := by
  cases ready with
  | evaluate code captured => exact .evaluate (.exact code captured.denotes)
  | returned pointer value => exact .returned pointer.denotes value
  | apply function argument value argValue => exact .apply function.denotes argument.denotes value argValue
  | complete pointer value => exact .complete pointer.denotes value

theorem RetainedFocus.extends {book : Book} {program : Program} {old next : Heap}
    {control : Control} {source : Term} (extension : Extends old next)
    (ready : RetainedFocus book program old control source) :
    RetainedFocus book program next control source := by
  cases ready with
  | evaluate code captured => exact .evaluate code (captured.extends extension)
  | returned pointer value => exact .returned (pointer.extends extension) value
  | apply function argument value argValue =>
    exact .apply (function.extends extension) (argument.extends extension) value argValue
  | complete pointer value => exact .complete (pointer.extends extension) value

theorem direct_value_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment pointer : Nat) (instruction : Code) (heap : Heap)
    (source : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some instruction)
    (direct : directValue instruction = true)
    (sourceExact : CodeDenotes library.program pc source)
    (captured : CapturedReady book library.program state.heap environment values)
    (stack : RetainedStack book library.program state.heap state.stack contexts)
    (cache : CacheCertified library.program state.heap state.data)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure pc environment) = .ok (pointer,heap)) :
    RetainedFocus book library.program (step limits library state).heap (step limits library state).control
      (Term.sub (Env.sub values) source) ∧
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack contexts ∧
    CacheCertified library.program (step limits library state).heap (step limits library state).data := by
  have ready := allocate_closure_ready sourceExact captured allocated
  have certified := closure_allocation_certified limits library state pc environment pointer instruction heap _
    found (.closure sourceExact captured.denotes) cache allocated
  rw [step_direct_value limits library state pc environment pointer instruction heap control found direct allocated]
  exact ⟨.returned ready (direct_value_source sourceExact found direct _),
    stack.extends (allocate_extends allocated), certified⟩

theorem known_live_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (f x : Term) (contexts : List (Context book))
    (control : state.control = .returned function)
    (stackShape : state.stack = .knownArgument q argument :: rest)
    (live : q.live = true) (room : rest.length < limits.frames)
    (functionReady : RetainedReady book library.program state.heap function f) (functionValue : Value book f)
    (argumentReady : RetainedReady book library.program state.heap argument x)
    (stack : RetainedStack book library.program state.heap rest contexts) :
    RetainedFocus book library.program (step limits library state).heap (step limits library state).control x ∧
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack
      (.argument q f functionValue live :: contexts) := by
  cases argumentReady with
  | closure rowFound code captured =>
    rw [step_known_closure limits library state function argument _ _ q rest control stackShape live room rowFound]
    exact ⟨.evaluate code captured, .cons (.argument functionReady functionValue live) stack⟩
  | pair rowFound first second value =>
    rw [step_known_pair limits library state function argument _ _ q _ rest control stackShape live room rowFound]
    exact ⟨.returned (.pair rowFound first second value) value,
      .cons (.argument functionReady functionValue live) stack⟩
  | application rowFound left right value =>
    rw [step_known_application limits library state function argument _ _ q _ rest control stackShape live room rowFound]
    exact ⟨.returned (.application rowFound left right value) value,
      .cons (.argument functionReady functionValue live) stack⟩

theorem return_function_live_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (pointer argument environment : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (f x : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .function q argument environment :: rest)
    (live : q.live = true) (room : rest.length < limits.frames)
    (functionReady : RetainedReady book library.program state.heap pointer f) (functionValue : Value book f)
    (argumentCode : CodeDenotes library.program argument x)
    (captured : CapturedReady book library.program state.heap environment values)
    (stack : RetainedStack book library.program state.heap rest contexts) :
    RetainedFocus book library.program (step limits library state).heap (step limits library state).control
      (Term.sub (Env.sub values) x) ∧
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack
      (.argument q f functionValue live :: contexts) := by
  rw [step_return_function_live limits library state pointer argument environment q rest control stackShape live room]
  exact ⟨.evaluate argumentCode captured, .cons (.argument functionReady functionValue live) stack⟩

theorem return_first_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (pointer second environment : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (a b : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .first q second environment :: rest)
    (firstReady : RetainedReady book library.program state.heap pointer a) (firstValue : Value book a)
    (secondCode : CodeDenotes library.program second b)
    (captured : CapturedReady book library.program state.heap environment values)
    (stack : RetainedStack book library.program state.heap rest contexts)
    (room : rest.length < limits.frames) :
    RetainedFocus book library.program (step limits library state).heap (step limits library state).control
      (Term.sub (Env.sub values) b) ∧
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack
      (.second q a (fun _ => firstValue) :: contexts) := by
  rw [step_return_first limits library state pointer second environment q rest control stackShape room]
  exact ⟨.evaluate secondCode captured, .cons (.second firstReady (fun _ => firstValue)) stack⟩

theorem return_argument_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (pointer function : Nat) (q : Quan) (rest : List BendClosureMachine.Frame)
    (f x : Term) (contexts : List (Context book))
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .argument q function :: rest)
    (functionReady : RetainedReady book library.program state.heap function f) (functionValue : Value book f)
    (argumentReady : RetainedReady book library.program state.heap pointer x) (argumentValue : Value book x)
    (stack : RetainedStack book library.program state.heap rest contexts) :
    RetainedFocus book library.program (step limits library state).heap (step limits library state).control (.App q f x) ∧
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack contexts := by
  rw [step_return_argument limits library state pointer function q rest control stackShape]
  exact ⟨.apply functionReady argumentReady functionValue (fun _ => argumentValue), stack⟩

#assert_axioms RetainedFocus.denotes
#assert_axioms RetainedFocus.extends
#assert_axioms direct_value_retains
#assert_axioms known_live_retains
#assert_axioms return_function_live_retains
#assert_axioms return_first_retains
#assert_axioms return_argument_retains
end Minidregg.Theory.BendClosureSimulation
