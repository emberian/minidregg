/- One-cell argument-spine administration for the actual v2 controller.
Eval.call is already counted when these controls are entered. Every tick below
preserves the exact leaf spine and the source count. -/
import Theory.BendClosureControlSteps

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem step_reverse_nil (limits : Limits) (library : Library) (state : State)
    (pc environment : Nat) (reversed : List (Quan × Nat))
    (control : state.control = .reverseArguments pc environment [] reversed) :
    step limits library state = {state with control := .installArguments pc environment reversed} := by
  simp [step, control, reverseArguments, go]
  rfl

theorem step_reverse_cons (limits : Limits) (library : Library) (state : State)
    (pc environment : Nat) (argument : Quan × Nat) (remaining reversed : List (Quan × Nat))
    (control : state.control = .reverseArguments pc environment (argument :: remaining) reversed) :
    step limits library state =
      {state with control := .reverseArguments pc environment remaining (argument :: reversed)} := by
  simp [step, control, reverseArguments, go]
  rfl

theorem step_install_nil (limits : Limits) (library : Library) (state : State)
    (pc environment : Nat)
    (control : state.control = .installArguments pc environment []) :
    step limits library state = {state with control := .evaluate pc environment} := by
  simp [step, control, installArguments, go]
  rfl

theorem step_install_cons (limits : Limits) (library : Library) (state : State)
    (pc environment : Nat) (argument : Quan × Nat) (remaining : List (Quan × Nat))
    (control : state.control = .installArguments pc environment (argument :: remaining))
    (room : state.stack.length < limits.frames) :
    step limits library state =
      {state with stack := .knownArgument argument.1 argument.2 :: state.stack, control := .installArguments pc environment remaining} := by
  simp [step, control, installArguments, push, Nat.not_le_of_lt room, go]
  rfl

theorem reverse_state {book : Book} {program : Program} {state : State}
    {pc environment : Nat} {remaining reversed : List (Quan × Nat)}
    {source : Term} {remainingSource reversedSource : List Arg}
    {contexts : List (Context book)}
    (control : state.control = .reverseArguments pc environment remaining reversed)
    (leaf : ClosureDenotes program state.heap pc environment source)
    (left : ArgumentsDenote program state.heap remaining remainingSource)
    (right : ArgumentsDenote program state.heap reversed reversedSource)
    (stack : StackDenotes book program state.heap state.stack contexts) :
    StateDenotes book program state
      (plug contexts (Term.spine source (reversedSource.reverse ++ remainingSource))) :=
  .exact (by rw [control]; exact .reverseArguments leaf left right) stack
    (by intro pointer impossible; rw [control] at impossible; cases impossible)

theorem install_state {book : Book} {program : Program} {state : State}
    {pc environment : Nat} {remaining : List (Quan × Nat)}
    {source : Term} {remainingSource : List Arg} {contexts : List (Context book)}
    (control : state.control = .installArguments pc environment remaining)
    (leaf : ClosureDenotes program state.heap pc environment source)
    (arguments : ArgumentsDenote program state.heap remaining remainingSource)
    (stack : StackDenotes book program state.heap state.stack contexts) :
    StateDenotes book program state (plug contexts (Term.spine source remainingSource.reverse)) :=
  .exact (by rw [control]; exact .installArguments leaf arguments) stack
    (by intro pointer impossible; rw [control] at impossible; cases impossible)

theorem reverse_cons_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment : Nat) (argument : Quan × Nat)
    (remaining reversed : List (Quan × Nat)) (sourceArgument : Arg)
    (remainingSource reversedSource : List Arg) (source : Term)
    (contexts : List (Context book))
    (control : state.control = .reverseArguments pc environment (argument :: remaining) reversed)
    (leaf : ClosureDenotes library.program state.heap pc environment source)
    (head : argument.1 = sourceArgument.1 ∧
      Denotes library.program state.heap argument.2 sourceArgument.2)
    (left : ArgumentsDenote library.program state.heap remaining remainingSource)
    (right : ArgumentsDenote library.program state.heap reversed reversedSource)
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
    let residual := plug contexts
      (Term.spine source (reversedSource.reverse ++ sourceArgument :: remainingSource))
    StateDenotes book library.program state residual ∧
      StateDenotes book library.program (step limits library state) residual ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  refine ⟨reverse_state control leaf (.cons head left) right stack, ?_, ?_⟩
  · rw [step_reverse_cons limits library state pc environment argument remaining reversed control]
    have next := reverse_state (book := book) (state :=
        {state with control := .reverseArguments pc environment remaining (argument :: reversed)})
      rfl leaf left (.cons head right) stack
    simpa [List.reverse_cons, List.append_assoc] using next
  · rw [step_reverse_cons limits library state pc environment argument remaining reversed control]

theorem reverse_nil_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment : Nat) (reversed : List (Quan × Nat))
    (reversedSource : List Arg) (source : Term) (contexts : List (Context book))
    (control : state.control = .reverseArguments pc environment [] reversed)
    (leaf : ClosureDenotes library.program state.heap pc environment source)
    (right : ArgumentsDenote library.program state.heap reversed reversedSource)
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
    let residual := plug contexts (Term.spine source reversedSource.reverse)
    StateDenotes book library.program state residual ∧
      StateDenotes book library.program (step limits library state) residual ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa using reverse_state control leaf (.nil : ArgumentsDenote library.program state.heap [] []) right stack
  · rw [step_reverse_nil limits library state pc environment reversed control]
    exact install_state rfl leaf right stack
  · rw [step_reverse_nil limits library state pc environment reversed control]

theorem install_cons_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment : Nat) (q : Quan) (pointer : Nat)
    (remaining : List (Quan × Nat)) (argument : Term)
    (remainingSource : List Arg) (source : Term) (contexts : List (Context book))
    (control : state.control = .installArguments pc environment ((q,pointer) :: remaining))
    (leaf : ClosureDenotes library.program state.heap pc environment source)
    (head : Denotes library.program state.heap pointer argument)
    (tail : ArgumentsDenote library.program state.heap remaining remainingSource)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : state.stack.length < limits.frames) :
    let residual := plug contexts (Term.spine source ((q,argument) :: remainingSource).reverse)
    StateDenotes book library.program state residual ∧
      StateDenotes book library.program (step limits library state) residual ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  dsimp only
  refine ⟨install_state control leaf (.cons ⟨rfl,head⟩ tail) stack, ?_, ?_⟩
  · rw [step_install_cons limits library state pc environment (q,pointer) remaining control room]
    have next := install_state (contexts := .function q argument :: contexts) (state :=
        {state with stack := .knownArgument q pointer :: state.stack, control := .installArguments pc environment remaining})
      rfl leaf tail (.cons (.knownArgument head) stack)
    simpa [List.reverse_cons, BendTT.spine_snoc, plug, Context.plug] using next
  · rw [step_install_cons limits library state pc environment (q,pointer) remaining control room]

theorem install_nil_stutter {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment : Nat) (source : Term) (contexts : List (Context book))
    (control : state.control = .installArguments pc environment [])
    (leaf : ClosureDenotes library.program state.heap pc environment source)
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
    StateDenotes book library.program state (plug contexts source) ∧
      StateDenotes book library.program (step limits library state) (plug contexts source) ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨install_state control leaf (.nil : ArgumentsDenote library.program state.heap [] []) stack, ?_, ?_⟩
  · rw [step_install_nil limits library state pc environment control]
    exact evaluate_state rfl leaf stack
  · rw [step_install_nil limits library state pc environment control]

#assert_axioms step_reverse_nil
#assert_axioms step_reverse_cons
#assert_axioms step_install_nil
#assert_axioms step_install_cons
#assert_axioms reverse_cons_stutter
#assert_axioms reverse_nil_stutter
#assert_axioms install_cons_stutter
#assert_axioms install_nil_stutter
end Minidregg.Theory.BendClosureSimulation

