/- First-definition source lookup for the actual unspine-to-Walk transition.
The empty environment is an actual immutable row witness, not a pointer-zero
convention or a claim inferred from successful code decoding. -/
import Theory.BendClosureWalkLeaf

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem label_name_ok (library : Library) (index : Nat) (name : String)
    (found : library.program.names[index]? = some name) :
    labelNameFn library index = (pure name : Work String) := by
  change (match library.program.names[index]? with
    | some name => (pure name : Work String)
    | none => throw Failure.labelPointer) = _
  rw [found]

theorem definition_lookup_ok (library : Library) (index body : Nat) (name : String)
    (named : library.program.names[index]? = some name)
    (found : library.lookupName name = some body) :
    definitionFn library index = (pure body : Work Nat) := by
  change (do
    let wanted ← labelNameFn library index
    match library.lookupName wanted with
    | some body => (pure body : Work Nat)
    | none => throw Failure.unknownDefinition) = _
  rw [label_name_ok library index name named]
  change (match library.lookupName name with
    | some body => (pure body : Work Nat)
    | none => throw Failure.unknownDefinition) = _
  rw [found]

theorem step_unspine_reference (limits : Limits) (library : Library) (state : State)
    (pointer original pc environment index body : Nat) (args : List (Quan × Nat)) (name : String)
    (control : state.control = .unspine pointer original args)
    (pointerRow : state.heap.get? pointer = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.ref index))
    (named : library.program.names[index]? = some name)
    (found : library.lookupName name = some body)
    (room : args.length ≤ limits.arguments) :
    step limits library state = {state with control := .walk body 0 original args} := by
  have bounded := bounded_arguments_ok limits args room
  have definition := definition_lookup_ok library index body name named found
  simp [step, control, unspine, boundedArgs_eq, bounded, row, pointerRow,
    code, instruction, definition_eq, definition, go]
  rfl

theorem unspine_reference_source {book : Book} (limits : Limits) (library : Library)
    (state : State) (pointer original pc environment index body : Nat)
    (args : List (Quan × Nat)) (name : String) (origin : Term) (arguments : List Arg)
    (contexts : List (Context book))
    (correspondence : library.SourceCorrespondence book)
    (control : state.control = .unspine pointer original args)
    (pointerRow : state.heap.get? pointer = some (.closure pc environment))
    (instruction : library.program.code[pc]? = some (.ref index))
    (named : library.program.names[index]? = some name)
    (found : library.lookupName name = some body)
    (headExact : Denotes library.program state.heap pointer (.Ref name))
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (originalSource : origin = Term.spine (.Ref name) arguments)
    (values : Values book arguments)
    (empty : state.heap.get? 0 = some .nil)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : args.length ≤ limits.arguments) :
    StateDenotes book library.program state (plug contexts origin) ∧
      StateDenotes book library.program (step limits library state) (plug contexts origin) ∧
      (step limits library state).sourceSteps = state.sourceSteps := by
  obtain ⟨definition, selected, codeExact⟩ := lookup_source correspondence found
  let walkPrefix : WalkPrefix book origin definition.v [] arguments :=
    {name, definition, originalArguments := arguments, origin_eq := originalSource,
      found := selected, values, resume := fun _ next => next}
  refine ⟨?_, ?_, ?_⟩
  · apply StateDenotes.exact (contexts := contexts)
    · rw [control]
      exact .unspine headExact originalExact argsExact originalSource values
    · exact stack
    · intro next impossible
      rw [control] at impossible
      cases impossible
  · rw [step_unspine_reference limits library state pointer original pc environment index body args name control pointerRow instruction named found room]
    exact StateDenotes.exact (contexts := contexts)
      (.walk codeExact (.nil empty) originalExact argsExact walkPrefix) stack
      (by intro next impossible; cases impossible)
  · rw [step_unspine_reference limits library state pointer original pc environment index body args name control pointerRow instruction named found room]

#assert_axioms label_name_ok
#assert_axioms definition_lookup_ok
#assert_axioms step_unspine_reference
#assert_axioms unspine_reference_source
end Minidregg.Theory.BendClosureSimulation
