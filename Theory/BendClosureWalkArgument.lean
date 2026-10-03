/- Argument-variable lookup during named case traversal retains the same
original call. Every traversed environment row and appended argument is exact. -/
import Theory.BendClosureWalkNodes

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem step_walk_argument_zero (limits : Limits) (library : Library) (state : State)
    (cursor pointer tail function environment original : Nat) (q : Quan) (args : List (Quan × Nat))
    (control : state.control = .lookup 0 cursor (.walkArgument q function environment original args))
    (found : state.heap.get? cursor = some (.environment pointer tail))
    (room : ((q,pointer) :: args).length ≤ limits.arguments) :
    step limits library state =
      {state with control := .walk function environment original ((q,pointer) :: args)} := by
  have bounded := bounded_arguments_ok limits ((q,pointer) :: args) room
  simp [step,control,lookup,row,found,boundedArgs_eq,bounded,go]
  rfl

theorem walk_argument_zero_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (cursor pointer tail function environment original : Nat) (q : Quan) (args : List (Quan × Nat))
    (source x origin : Term) (values remaining : Env) (arguments : List Arg) (contexts : List (Context book))
    (control : state.control = .lookup 0 cursor (.walkArgument q function environment original args))
    (found : state.heap.get? cursor = some (.environment pointer tail))
    (functionExact : CodeDenotes library.program function source)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (headExact : Denotes library.program state.heap pointer x)
    (tailExact : EnvironmentDenotes library.program state.heap tail remaining)
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (walkPrefix : WalkPrefix book origin source values ((q,x) :: arguments))
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : ((q,pointer) :: args).length ≤ limits.arguments) :
    StateDenotes book library.program state (plug contexts origin) ∧
    StateDenotes book library.program (step limits library state) (plug contexts origin) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨?_,?_,?_⟩
  · exact StateDenotes.exact
      (by
        rw [control]
        exact .lookupWalk functionExact captured (.cons found headExact tailExact)
          originalExact argsExact walkPrefix) stack
      (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_walk_argument_zero limits library state cursor pointer tail function environment original q args
      control found room]
    exact StateDenotes.exact
      (.walk functionExact captured originalExact (.cons ⟨rfl,headExact⟩ argsExact) walkPrefix) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_walk_argument_zero limits library state cursor pointer tail function environment original q args
      control found room]

theorem walk_argument_successor_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (index cursor pointer tail function environment original : Nat) (q : Quan) (args : List (Quan × Nat))
    (source x origin : Term) (values remaining : Env) (arguments : List Arg) (contexts : List (Context book))
    (control : state.control = .lookup (index + 1) cursor (.walkArgument q function environment original args))
    (found : state.heap.get? cursor = some (.environment pointer tail))
    (functionExact : CodeDenotes library.program function source)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (headExact : Denotes library.program state.heap pointer x)
    (tailExact : EnvironmentDenotes library.program state.heap tail remaining)
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (walkPrefix : WalkPrefix book origin source values ((q,Env.sub remaining index) :: arguments))
    (stack : StackDenotes book library.program state.heap state.stack contexts) :
    StateDenotes book library.program state (plug contexts origin) ∧
    StateDenotes book library.program (step limits library state) (plug contexts origin) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨?_,?_,?_⟩
  · exact StateDenotes.exact
      (by
        rw [control]
        exact .lookupWalk functionExact captured (.cons found headExact tailExact)
          originalExact argsExact walkPrefix) stack
      (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_lookup_succ limits library state index cursor pointer tail
      (.walkArgument q function environment original args) control found]
    exact StateDenotes.exact
      (.lookupWalk functionExact captured tailExact originalExact argsExact walkPrefix) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_lookup_succ limits library state index cursor pointer tail
      (.walkArgument q function environment original args) control found]

#assert_axioms step_walk_argument_zero
#assert_axioms walk_argument_zero_source
#assert_axioms walk_argument_successor_source
end Minidregg.Theory.BendClosureSimulation
