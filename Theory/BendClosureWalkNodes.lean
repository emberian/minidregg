/- Actual named-call case-tree transitions. The original call is retained
while lambdas bind and projections split arguments; only the later whole-leaf
commit performs Eval.call. These are source stutters, not extra beta steps. -/
import Theory.BendClosureUnderapplication
import Theory.BendClosureRetainedReturns

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ArgumentsDenote.extends {program : Program} {old next : Heap}
    {args : List (Quan × Nat)} {sources : List Arg} (extension : Extends old next)
    (exact : ArgumentsDenote program old args sources) : ArgumentsDenote program next args sources := by
  induction exact with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.1,head.2.extends extension⟩ ih

theorem step_walk_lambda (limits : Limits) (library : Library) (state : State)
    (pc environment original argument body nextEnvironment : Nat) (args : List (Quan × Nat))
    (binder quantity : Quan) (heap : Heap)
    (control : state.control = .walk pc environment original ((quantity,argument) :: args))
    (found : library.program.code[pc]? = some (.lam binder body))
    (compatible : binder.live = quantity.live)
    (copied : binder = .Q2 → state.data[argument]?.getD false = true)
    (room : ((quantity,argument) :: args).length ≤ limits.arguments)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.environment argument environment) = .ok (nextEnvironment,heap)) :
    step limits library state =
      {afterEnvironment state heap nextEnvironment with control := .walk body nextEnvironment original args} := by
  have bounded := bounded_arguments_ok limits ((quantity,argument) :: args) room
  cases binder <;> cases quantity <;> simp only [Quan.live] at compatible <;> try contradiction
  all_goals simp [step,control,startWalk,walk,code,found,boundedArgs_eq,bounded,Quan.live,
    BendClosureMachine.bind,isData,BendClosureMachine.allocate,allocated,afterEnvironment,go,copied]
  all_goals rfl

theorem walk_lambda_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment original argument body nextEnvironment : Nat) (args : List (Quan × Nat))
    (binder quantity : Quan) (heap : Heap) (source x origin : Term) (values : Env)
    (arguments : List Arg) (contexts : List (Context book))
    (control : state.control = .walk pc environment original ((quantity,argument) :: args))
    (found : library.program.code[pc]? = some (.lam binder body))
    (bodyExact : CodeDenotes library.program body source)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (argumentExact : Denotes library.program state.heap argument x)
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (walkPrefix : WalkPrefix book origin (.Lam binder source) values ((quantity,x) :: arguments))
    (compatible : binder.live = quantity.live)
    (copied : binder = .Q2 → state.data[argument]?.getD false = true)
    (cache : CacheCertified library.program state.heap state.data)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : ((quantity,argument) :: args).length ≤ limits.arguments)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.environment argument environment) = .ok (nextEnvironment,heap)) :
    StateDenotes book library.program state (plug contexts origin) ∧
    StateDenotes book library.program (step limits library state) (plug contexts origin) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  have extension := allocate_extends allocated
  have data : binder = .Q2 → Data x := fun q2 =>
    cache.sound (cache_bit_of_getD (copied q2)) argumentExact
  have nextCaptured := allocate_environment (.cons argumentExact captured) allocated
  refine ⟨?_,?_,?_⟩
  · exact StateDenotes.exact
      (by
        rw [control]
        exact .walk (.lam found bodyExact) captured originalExact
          (.cons ⟨rfl,argumentExact⟩ argsExact) walkPrefix) stack
      (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_walk_lambda limits library state pc environment original argument body nextEnvironment args
      binder quantity heap control found compatible copied room allocated]
    exact StateDenotes.exact
      (.walk bodyExact nextCaptured (originalExact.extends extension) (argsExact.extends extension)
        (walkPrefix.lam compatible data)) (stack.extends extension)
      (by intro pointer impossible; cases impossible)
  · rw [step_walk_lambda limits library state pc environment original argument body nextEnvironment args
      binder quantity heap control found compatible copied room allocated]
    rfl

theorem walk_lambda_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment original argument body nextEnvironment : Nat) (args : List (Quan × Nat))
    (binder quantity : Quan) (heap : Heap) (x : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .walk pc environment original ((quantity,argument) :: args))
    (found : library.program.code[pc]? = some (.lam binder body))
    (captured : CapturedReady book library.program state.heap environment values)
    (argumentReady : RetainedReady book library.program state.heap argument x)
    (compatible : binder.live = quantity.live)
    (copied : binder = .Q2 → state.data[argument]?.getD false = true)
    (cache : CacheCertified library.program state.heap state.data)
    (stack : RetainedStack book library.program state.heap state.stack contexts)
    (room : ((quantity,argument) :: args).length ≤ limits.arguments)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.environment argument environment) = .ok (nextEnvironment,heap)) :
    CapturedReady book library.program (step limits library state).heap nextEnvironment (x :: values) ∧
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack contexts ∧
    CacheCertified library.program (step limits library state).heap (step limits library state).data := by
  have ready := allocate_environment_ready argumentReady captured allocated
  have certified := cache.allocate false allocated (by intro impossible; cases impossible)
  rw [step_walk_lambda limits library state pc environment original argument body nextEnvironment args
    binder quantity heap control found compatible copied room allocated]
  exact ⟨ready,stack.extends (allocate_extends allocated),certified⟩

theorem step_walk_projection (limits : Limits) (library : Library) (state : State)
    (pc environment original argument handler first second : Nat) (args : List (Quan × Nat))
    (quantity firstQ : Quan)
    (control : state.control = .walk pc environment original ((quantity,argument) :: args))
    (found : library.program.code[pc]? = some (.prj handler))
    (live : quantity.live = true)
    (rowFound : state.heap.get? argument = some (.pair firstQ first second))
    (room : ((quantity,argument) :: args).length ≤ limits.arguments)
    (expandedRoom : ((Quan.fld firstQ quantity,first) :: (quantity,second) :: args).length ≤ limits.arguments) :
    step limits library state = {state with control := .walk handler environment original ((Quan.fld firstQ quantity,first) :: (quantity,second) :: args)} := by
  have bounded := bounded_arguments_ok limits ((quantity,argument) :: args) room
  have expanded := bounded_arguments_ok limits ((Quan.fld firstQ quantity,first) :: (quantity,second) :: args) expandedRoom
  simp [step,control,startWalk,walk,code,found,boundedArgs_eq,bounded,expanded,live,row,rowFound,go]
  rfl

theorem walk_projection_source {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment original argument handler first second : Nat) (args : List (Quan × Nat))
    (quantity firstQ : Quan) (source a b origin : Term) (values : Env)
    (arguments : List Arg) (contexts : List (Context book))
    (control : state.control = .walk pc environment original ((quantity,argument) :: args))
    (found : library.program.code[pc]? = some (.prj handler))
    (handlerExact : CodeDenotes library.program handler source)
    (captured : EnvironmentDenotes library.program state.heap environment values)
    (rowFound : state.heap.get? argument = some (.pair firstQ first second))
    (firstExact : Denotes library.program state.heap first a)
    (secondExact : Denotes library.program state.heap second b)
    (originalExact : Denotes library.program state.heap original origin)
    (argsExact : ArgumentsDenote library.program state.heap args arguments)
    (walkPrefix : WalkPrefix book origin (.Prj source) values ((quantity,.Tup firstQ a b) :: arguments))
    (live : quantity.live = true)
    (stack : StackDenotes book library.program state.heap state.stack contexts)
    (room : ((quantity,argument) :: args).length ≤ limits.arguments)
    (expandedRoom : ((Quan.fld firstQ quantity,first) :: (quantity,second) :: args).length ≤ limits.arguments) :
    StateDenotes book library.program state (plug contexts origin) ∧
    StateDenotes book library.program (step limits library state) (plug contexts origin) ∧
    (step limits library state).sourceSteps = state.sourceSteps := by
  refine ⟨?_,?_,?_⟩
  · exact StateDenotes.exact
      (by
        rw [control]
        exact .walk (.prj found handlerExact) captured originalExact
          (.cons ⟨rfl,.pair rowFound firstExact secondExact⟩ argsExact) walkPrefix) stack
      (by intro pointer impossible; rw [control] at impossible; cases impossible)
  · rw [step_walk_projection limits library state pc environment original argument handler first second args
      quantity firstQ control found live rowFound room expandedRoom]
    exact StateDenotes.exact
      (.walk handlerExact captured originalExact
        (.cons ⟨rfl,firstExact⟩ (.cons ⟨rfl,secondExact⟩ argsExact)) (walkPrefix.prj live)) stack
      (by intro pointer impossible; cases impossible)
  · rw [step_walk_projection limits library state pc environment original argument handler first second args
      quantity firstQ control found live rowFound room expandedRoom]

#assert_axioms ArgumentsDenote.extends
#assert_axioms step_walk_lambda
#assert_axioms walk_lambda_source
#assert_axioms walk_lambda_retains
#assert_axioms step_walk_projection
#assert_axioms walk_projection_source
end Minidregg.Theory.BendClosureSimulation
