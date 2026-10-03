/- The whole source call commits before argument-spine administration. The
poststate is ready by construction, and the source Eval.call is derived from
the original exact Book lookup and complete WalkPrefix. -/
import Theory.BendClosureReadyWalkArgument
import Theory.BendClosureClassifierExit
import Theory.BendClosureApplicationLeaf

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.walk_leaf {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment original : Nat) (args : List (Quan × Nat)) (instruction : Code)
    (ready : ReadyState book library.program state source)
    (control : state.control = .walk pc environment original args)
    (found : library.program.code[pc]? = some instruction) (leaf : directLeaf instruction = true)
    (room : args.length ≤ limits.arguments) (framesRoom : state.stack.length + args.length ≤ limits.frames) :
    ∃ nextSource, ReadyState book library.program (step limits library state) nextSource ∧ Eval book source nextSource := by
  cases ready with
  | @exact _ contexts focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | walk code captured originalReady argsReady walkPrefix =>
      refine ⟨_,?_,plug_eval contexts (walkPrefix.leaf (direct_leaf_source code found leaf))⟩
      rw [step_walk_leaf limits library state pc environment original args instruction control found leaf room framesRoom]
      exact ReadyState.exact (.reverseArguments code captured argsReady .nil) stack cache empty
        (by intro result impossible; cases impossible)

theorem ReadyState.classifier_leaf {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment original cursor : Nat) (args : List (Quan × Nat)) (instruction originalInstruction : Code)
    (ready : ReadyState book library.program state source)
    (control : state.control = .classify pc environment original cursor args)
    (cursorFound : library.program.code[cursor]? = some instruction) (leaf : directLeaf instruction = true)
    (found : library.program.code[pc]? = some originalInstruction)
    (room : args.length ≤ limits.arguments) (framesRoom : state.stack.length + args.length ≤ limits.frames) :
    ∃ nextSource, ReadyState book library.program (step limits library state) nextSource ∧ Eval book source nextSource := by
  cases ready with
  | @exact _ contexts focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | classify code cursorCode application classification captured originalReady argsReady walkPrefix =>
      have notNode := classification.trans (direct_leaf_head cursorCode cursorFound leaf)
      refine ⟨_,?_,plug_eval contexts (walkPrefix.leaf notNode)⟩
      rw [step_classifier_leaf limits library state pc environment original cursor args instruction originalInstruction
        control cursorFound leaf found room framesRoom]
      exact ReadyState.exact (.reverseArguments code captured argsReady .nil) stack cache empty
        (by intro result impossible; cases impossible)

#assert_axioms ReadyState.walk_leaf
#assert_axioms ReadyState.classifier_leaf
end Minidregg.Theory.BendClosureSimulation
