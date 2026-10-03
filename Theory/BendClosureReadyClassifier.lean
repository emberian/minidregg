/- Every successful classifier edge derives its source grammar information
from actual ROM correspondence; no caller supplies the eventual classification. -/
import Theory.BendClosureReadyLeaf
import Theory.BendClosureCodeCases

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.walk_classify {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment original function argument index : Nat) (q : Quan) (args : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .walk pc environment original args)
    (found : library.program.code[pc]? = some (.app q function argument))
    (variableCode : library.program.code[argument]? = some (.var index)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | walk code captured originalReady argsReady walkPrefix =>
      obtain ⟨f,x,same,functionCode,argumentCode⟩ := code.application_fields q function argument found
      cases same
      have sameArgument := CodeDenotes.functional argumentCode (.var variableCode)
      cases sameArgument
      rw [step_walk_classify limits library state pc environment original function argument index q args control found variableCode]
      exact ReadyState.exact (.classify code functionCode ⟨q,f,index,rfl⟩ rfl captured originalReady argsReady walkPrefix)
        stack cache empty (by intro result impossible; cases impossible)

theorem ReadyState.classify_application {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment original cursor function argument : Nat) (q : Quan) (args : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .classify pc environment original cursor args)
    (found : library.program.code[cursor]? = some (.app q function argument)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | classify code cursorCode application classification captured originalReady argsReady walkPrefix =>
      obtain ⟨f,x,same,functionCode,argumentCode⟩ := cursorCode.application_fields q function argument found
      cases same
      rw [step_classify_application limits library state pc environment original cursor function argument q args control found]
      exact ReadyState.exact (.classify code functionCode application (by simpa only [application_head] using classification)
        captured originalReady argsReady walkPrefix) stack cache empty
        (by intro result impossible; cases impossible)

theorem ReadyState.classifier_argument {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment original cursor function argument index : Nat) (q : Quan)
    (args : List (Quan × Nat)) (instruction : Code)
    (ready : ReadyState book library.program state source)
    (control : state.control = .classify pc environment original cursor args)
    (cursorFound : library.program.code[cursor]? = some instruction) (takes : directTakes instruction = true)
    (found : library.program.code[pc]? = some (.app q function argument))
    (variableCode : library.program.code[argument]? = some (.var index))
    (room : args.length ≤ limits.arguments) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | classify code cursorCode application classification captured originalReady argsReady walkPrefix =>
      obtain ⟨f,x,same,functionCode,argumentCode⟩ := code.application_fields q function argument found
      cases same
      have sameArgument := CodeDenotes.functional argumentCode (.var variableCode)
      cases sameArgument
      have node := classification.trans (direct_takes_head cursorCode cursorFound takes)
      rw [step_classifier_argument limits library state pc environment original cursor function argument index q args instruction
        control cursorFound takes found variableCode room]
      exact ReadyState.exact (.lookupWalk functionCode captured captured originalReady argsReady (walkPrefix.app node))
        stack cache empty (by intro result impossible; cases impossible)

theorem ReadyState.walk_application_leaf {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment original function argument : Nat) (q : Quan) (args : List (Quan × Nat)) (instruction : Code)
    (ready : ReadyState book library.program state source)
    (control : state.control = .walk pc environment original args)
    (found : library.program.code[pc]? = some (.app q function argument))
    (argumentFound : library.program.code[argument]? = some instruction) (notVariable : nonVariable instruction = true)
    (room : args.length ≤ limits.arguments) (framesRoom : state.stack.length + args.length ≤ limits.frames) :
    ∃ nextSource, ReadyState book library.program (step limits library state) nextSource ∧ Eval book source nextSource := by
  cases ready with
  | @exact _ contexts focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | walk code captured originalReady argsReady walkPrefix =>
      obtain ⟨f,x,same,functionCode,argumentCode⟩ := code.application_fields q function argument found
      cases same
      have leaf := nonvariable_application_leaf argumentCode argumentFound notVariable q f
      refine ⟨_,?_,plug_eval contexts (walkPrefix.leaf leaf)⟩
      rw [step_walk_application_leaf limits library state pc environment original function argument q args instruction
        control found argumentFound notVariable room framesRoom]
      exact ReadyState.exact (.reverseArguments code captured argsReady .nil) stack cache empty
        (by intro result impossible; cases impossible)

#assert_axioms ReadyState.walk_classify
#assert_axioms ReadyState.classify_application
#assert_axioms ReadyState.classifier_argument
#assert_axioms ReadyState.walk_application_leaf
end Minidregg.Theory.BendClosureSimulation
