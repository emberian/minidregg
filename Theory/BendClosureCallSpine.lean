/- Actual residual application allocation and call-spine traversal. A newly
allocated original call is not falsely certified as a Value; its evaluated head
and live argument facts are retained separately until the case walk completes. -/
import Theory.BendClosureWalkArgument

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

def residualApplication : Code → Bool
  | .lam .. | .prj .. | .mat .. => false
  | _ => true

theorem step_apply_residual_closure (limits : Limits) (library : Library) (state : State)
    (function argument pc environment original : Nat) (q : Quan) (instruction : Code) (heap : Heap)
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (found : library.program.code[pc]? = some instruction)
    (residual : residualApplication instruction = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.application q function argument) = .ok (original,heap)) :
    step limits library state =
      {allocationState state heap original false with control := .unspine function original [(q,argument)]} := by
  cases instruction <;> simp only [residualApplication] at residual <;> try contradiction
  all_goals simp [step,control,BendClosureMachine.apply,row,functionRow,code,found,
    BendClosureMachine.allocate,allocated,allocationState,go]
  all_goals rfl

theorem step_apply_residual_application (limits : Limits) (library : Library) (state : State)
    (function argument left right original : Nat) (q r : Quan) (heap : Heap)
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.application r left right))
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.application q function argument) = .ok (original,heap)) :
    step limits library state =
      {allocationState state heap original false with control := .unspine function original [(q,argument)]} := by
  simp [step,control,BendClosureMachine.apply,row,functionRow,
    BendClosureMachine.allocate,allocated,allocationState,go]
  rfl

theorem apply_residual_closure_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument pc environment original : Nat) (q : Quan) (instruction : Code) (heap : Heap)
    (f x : Term) (contexts : List (Context book))
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (found : library.program.code[pc]? = some instruction)
    (residual : residualApplication instruction = true)
    (functionExact : Denotes library.program state.heap function f)
    (argumentExact : Denotes library.program state.heap argument x)
    (functionValue : Value book f) (argumentValue : q.live = true → Value book x)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.application q function argument) = .ok (original,heap)) :
    StateDenotes book library.program state (plug contexts (.App q f x)) ∧
    StateDenotes book library.program (step limits library state) (plug contexts (.App q f x)) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  have extension := allocate_extends allocated
  have originalExact := allocate_term (.application functionExact argumentExact) allocated
  refine ⟨?_,?_,?_⟩
  · exact StateDenotes.exact
      (by rw [control]; exact .apply functionExact argumentExact functionValue argumentValue) stack
      (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_apply_residual_closure limits library state function argument pc environment original q instruction heap
      control functionRow found residual allocated]
    exact StateDenotes.exact
      (.unspine (arguments := [(q,x)]) (functionExact.extends extension) originalExact
        (.cons ⟨rfl,argumentExact.extends extension⟩ .nil) rfl (.cons argumentValue .nil))
      (stack.extends extension) (by intro pointer impossible; cases impossible)
  · rw [step_apply_residual_closure limits library state function argument pc environment original q instruction heap
      control functionRow found residual allocated]
    rfl

theorem apply_residual_application_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument left right original : Nat) (q r : Quan) (heap : Heap)
    (f x : Term) (contexts : List (Context book))
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.application r left right))
    (functionExact : Denotes library.program state.heap function f)
    (argumentExact : Denotes library.program state.heap argument x)
    (functionValue : Value book f) (argumentValue : q.live = true → Value book x)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.application q function argument) = .ok (original,heap)) :
    StateDenotes book library.program state (plug contexts (.App q f x)) ∧
    StateDenotes book library.program (step limits library state) (plug contexts (.App q f x)) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  have extension := allocate_extends allocated
  have originalExact := allocate_term (.application functionExact argumentExact) allocated
  refine ⟨?_,?_,?_⟩
  · exact StateDenotes.exact
      (by rw [control]; exact .apply functionExact argumentExact functionValue argumentValue) stack
      (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_apply_residual_application limits library state function argument left right original q r heap
      control functionRow allocated]
    exact StateDenotes.exact
      (.unspine (arguments := [(q,x)]) (functionExact.extends extension) originalExact
        (.cons ⟨rfl,argumentExact.extends extension⟩ .nil) rfl (.cons argumentValue .nil))
      (stack.extends extension) (by intro pointer impossible; cases impossible)
  · rw [step_apply_residual_application limits library state function argument left right original q r heap
      control functionRow allocated]
    rfl

theorem step_unspine_application (limits : Limits) (library : Library) (state : State)
    (pointer original function argument : Nat) (q : Quan) (args : List (Quan × Nat))
    (control : state.control = .unspine pointer original args)
    (found : state.heap.get? pointer = some (.application q function argument))
    (room : args.length ≤ limits.arguments)
    (expandedRoom : ((q,argument) :: args).length ≤ limits.arguments) :
    step limits library state = {state with control := .unspine function original ((q,argument) :: args)} := by
  have bounded := bounded_arguments_ok limits args room
  have expanded := bounded_arguments_ok limits ((q,argument) :: args) expandedRoom
  simp [step,control,unspine,boundedArgs_eq,bounded,expanded,row,found,go]
  rfl

theorem unspine_application_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pointer original function argument : Nat) (q : Quan) (args : List (Quan × Nat))
    (f x origin : Term) (arguments : List Arg) (contexts : List (Context book))
    (control : state.control = .unspine pointer original args)
    (found : state.heap.get? pointer = some (.application q function argument))
    (functionExact : Denotes library.program state.heap function f)
    (argumentExact : Denotes library.program state.heap argument x)
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (originalSource : origin = Term.spine (.App q f x) arguments)
    (argumentValue : q.live = true → Value book x) (values : Values book arguments)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : args.length ≤ limits.arguments)
    (expandedRoom : ((q,argument) :: args).length ≤ limits.arguments) :
    StateDenotes book library.program state (plug contexts origin) ∧
    StateDenotes book library.program (step limits library state) (plug contexts origin) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨?_,?_,?_⟩
  · exact StateDenotes.exact
      (by
        rw [control]
        exact .unspine (.application found functionExact argumentExact)
          originalExact argsExact originalSource values) stack
      (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_unspine_application limits library state pointer original function argument q args
      control found room expandedRoom]
    exact StateDenotes.exact
      (.unspine (arguments := (q,x) :: arguments) functionExact originalExact (.cons ⟨rfl,argumentExact⟩ argsExact)
        originalSource (.cons argumentValue values)) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_unspine_application limits library state pointer original function argument q args
      control found room expandedRoom]

#assert_axioms step_apply_residual_closure
#assert_axioms step_apply_residual_application
#assert_axioms apply_residual_closure_source
#assert_axioms apply_residual_application_source
#assert_axioms step_unspine_application
#assert_axioms unspine_application_source
end Minidregg.Theory.BendClosureSimulation
