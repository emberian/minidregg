/- Actual first-definition lookup and underapplication preserve readiness.
Library correspondence is the compiler's existing certificate, not an oracle
for the next machine state. -/
import Theory.BendClosureReadySpine
import Theory.BendClosureCallLookup

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem Denotes.reference_name {program : Program} {heap : Heap}
    {pointer pc environment index : Nat} {source : Term} {name : String}
    (meaning : Denotes program heap pointer source)
    (row : heap.get? pointer = some (.closure pc environment))
    (instruction : program.code[pc]? = some (.ref index))
    (named : program.names[index]? = some name) : source = .Ref name := by
  cases meaning with
  | pair other first second => rw [row] at other; cases other
  | application other function argument => rw [row] at other; cases other
  | closure other code captured =>
    rw [row] at other
    cases other
    have same := CodeDenotes.functional code (.ref instruction named)
    cases same
    rfl

theorem ReadyState.unspine_reference {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer original pc environment index body : Nat) (args : List (Quan × Nat)) (name : String)
    (ready : ReadyState book library.program state source)
    (correspondence : library.SourceCorrespondence book)
    (control : state.control = .unspine pointer original args)
    (row : state.heap.get? pointer = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.ref index))
    (named : library.program.names[index]? = some name)
    (found : library.lookupName name = some body)
    (room : args.length ≤ limits.arguments) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | unspine head originalReady argsReady identity values =>
      have same := Denotes.reference_name head.denotes row instruction named
      cases same
      obtain ⟨definition,selected,bodyCode⟩ := lookup_source correspondence found
      have walkPrefix : WalkPrefix book _ definition.v [] _ :=
        {name, definition, originalArguments := _, origin_eq := identity,
          found := selected, values, resume := fun _ next => next}
      rw [step_unspine_reference limits library state pointer original pc environment index body args name
        control row instruction named found room]
      exact ReadyState.exact (.walk bodyCode (.nil empty) originalReady argsReady walkPrefix)
        stack cache empty (by intro result impossible; cases impossible)

theorem ReadyState.walk_underapplication {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment original : Nat) (instruction : Code)
    (ready : ReadyState book library.program state source)
    (control : state.control = .walk pc environment original [])
    (found : library.program.code[pc]? = some instruction)
    (takes : directTakes instruction = true) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | walk code captured originalReady argsReady walkPrefix =>
      cases argsReady
      have value := walkPrefix.need (direct_takes_source code found takes)
      rw [step_walk_underapplication limits library state pc environment original instruction control found takes]
      exact ReadyState.exact (.basic (.returned (originalReady.promote value) value)) stack cache empty
        (by intro result impossible; cases impossible)

#assert_axioms Denotes.reference_name
#assert_axioms ReadyState.unspine_reference
#assert_axioms ReadyState.walk_underapplication
end Minidregg.Theory.BendClosureSimulation
