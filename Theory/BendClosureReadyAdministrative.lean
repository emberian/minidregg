/- Bounded argument reversal/installation preserves recursive readiness and
its exact source residual. No hidden host reverse or atomic list traversal. -/
import Theory.BendClosureReadyReturn
import Theory.BendClosureSpineSteps

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.reverse_nil {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment : Nat) (reversed : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .reverseArguments pc environment [] reversed) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | reverseArguments code captured left right =>
      cases left
      rw [step_reverse_nil limits library state pc environment reversed control]
      simpa only [List.append_nil] using ReadyState.exact (state := {state with control := .installArguments pc environment reversed}) (.installArguments code captured right) stack cache empty
        (by intro result impossible; cases impossible)

theorem ReadyState.reverse_cons {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment : Nat) (argument : Quan × Nat) (remaining reversed : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .reverseArguments pc environment (argument :: remaining) reversed) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | reverseArguments code captured left right =>
      cases left with
      | cons head tail =>
        rw [step_reverse_cons limits library state pc environment argument remaining reversed control]
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
          ReadyState.exact (state := {state with control := .reverseArguments pc environment remaining (argument :: reversed)}) (.reverseArguments code captured tail (.cons head right)) stack cache empty
            (by intro result impossible; cases impossible)

theorem ReadyState.install_nil {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment : Nat)
    (ready : ReadyState book library.program state source)
    (control : state.control = .installArguments pc environment []) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | installArguments code captured args =>
      cases args
      rw [step_install_nil limits library state pc environment control]
      exact ReadyState.exact (.basic (.evaluate code captured)) stack cache empty
        (by intro result impossible; cases impossible)

theorem ReadyState.install_cons {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment : Nat) (q : Quan) (pointer : Nat) (remaining : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .installArguments pc environment ((q,pointer) :: remaining))
    (room : state.stack.length < limits.frames) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | installArguments code captured args =>
      cases args with
      | cons head tail =>
        rename_i sourceArgument remainingSource
        rcases sourceArgument with ⟨sourceQ,sourceTerm⟩
        have sameQ : q = sourceQ := head.1
        cases sameQ
        rw [step_install_cons limits library state pc environment (q,pointer) remaining control room]
        have next := ReadyState.exact
          (state := {state with stack := .knownArgument q pointer :: state.stack, control := .installArguments pc environment remaining})
          (contexts := .function q _ :: _)
          (.installArguments code captured tail) (.cons (.knownArgument (q := q) head.2) stack) cache empty
          (by intro result impossible; cases impossible)
        simpa only [List.reverse_cons, BendTT.spine_snoc, plug, Context.plug, head.1] using next

#assert_axioms ReadyState.reverse_nil
#assert_axioms ReadyState.reverse_cons
#assert_axioms ReadyState.install_nil
#assert_axioms ReadyState.install_cons
end Minidregg.Theory.BendClosureSimulation
