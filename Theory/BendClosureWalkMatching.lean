/- Named case-tree matching compares the actual interned strings and retains
the original call. A miss keeps the argument for the alternative case tree. -/
import Theory.BendClosureCallSpine
import Theory.BendClosureMatchingSteps

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem step_walk_matching (limits : Limits) (library : Library) (state : State)
    (pc environment original argument label yes no argumentPC argumentEnvironment actualLabel : Nat)
    (q : Quan) (args : List (Quan × Nat)) (wantedName actualName : String)
    (control : state.control = .walk pc environment original ((q,argument) :: args))
    (instruction : library.program.code[pc]? = some (.mat label yes no))
    (argumentRow : state.heap.get? argument = some (.closure argumentPC argumentEnvironment))
    (argumentCode : library.program.code[argumentPC]? = some (.lab actualLabel))
    (wanted : library.program.names[label]? = some wantedName)
    (actual : library.program.names[actualLabel]? = some actualName)
    (live : q.live = true) (room : ((q,argument) :: args).length ≤ limits.arguments) :
    step limits library state = if actualName = wantedName then
      {state with control := .walk yes environment original args}
      else {state with control := .walk no environment original ((q,argument) :: args)} := by
  have bounded := bounded_arguments_ok limits ((q,argument) :: args) room
  by_cases same : actualName = wantedName
  all_goals simp [step,control,startWalk,walk,code,instruction,boundedArgs_eq,bounded,live,
    labelOf_eq,labelOf_view,row,argumentRow,argumentCode,actual,labelName_eq,
    label_name_ok library label wantedName wanted,same,go]
  all_goals rfl

theorem walk_matching_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment original argument label yes no argumentPC argumentEnvironment actualLabel : Nat)
    (q : Quan) (args : List (Quan × Nat)) (wantedName actualName : String)
    (h m origin : Term) (values : Env) (arguments : List Arg) (contexts : List (Context book))
    (control : state.control = .walk pc environment original ((q,argument) :: args))
    (instruction : library.program.code[pc]? = some (.mat label yes no))
    (argumentRow : state.heap.get? argument = some (.closure argumentPC argumentEnvironment))
    (argumentCode : library.program.code[argumentPC]? = some (.lab actualLabel))
    (wanted : library.program.names[label]? = some wantedName)
    (actual : library.program.names[actualLabel]? = some actualName)
    (yesExact : CodeDenotes library.program yes h) (noExact : CodeDenotes library.program no m)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (argumentExact : Denotes library.program state.heap argument (.Lab actualName))
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (walkPrefix : WalkPrefix book origin (.Mat wantedName h m) values ((q,.Lab actualName) :: arguments))
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (live : q.live = true) (room : ((q,argument) :: args).length ≤ limits.arguments) :
    StateDenotes book library.program state (plug contexts origin) ∧
    StateDenotes book library.program (step limits library state) (plug contexts origin) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨?_,?_⟩
  · exact StateDenotes.exact
      (by
        rw [control]
        exact .walk (.mat instruction wanted yesExact noExact) captured originalExact
          (.cons ⟨rfl,argumentExact⟩ argsExact) walkPrefix) stack
      (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_walk_matching limits library state pc environment original argument label yes no argumentPC
      argumentEnvironment actualLabel q args wantedName actualName control instruction argumentRow argumentCode
      wanted actual live room]
    by_cases same : actualName = wantedName
    · rw [if_pos same]
      have hit : WalkPrefix book origin (.Mat wantedName h m) values ((q,.Lab wantedName) :: arguments) := by
        simpa only [same] using walkPrefix
      exact ⟨StateDenotes.exact (.walk yesExact captured originalExact argsExact (hit.hit live)) stack
        (by intro pointer impossible; cases impossible),rfl⟩
    · rw [if_neg same]
      exact ⟨StateDenotes.exact
        (.walk noExact captured originalExact (.cons ⟨rfl,argumentExact⟩ argsExact) (walkPrefix.miss live same)) stack
        (by intro pointer impossible; cases impossible),rfl⟩

#assert_axioms step_walk_matching
#assert_axioms walk_matching_source
end Minidregg.Theory.BendClosureSimulation
