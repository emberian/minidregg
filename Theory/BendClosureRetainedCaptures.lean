/- Actual thunk capture preserves recursive readiness and certified Data.
These theorems distinguish retained closures from already evaluated values. -/
import Theory.BendClosureRetainedTransitions
import Theory.BendClosureDeadFunction

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem closure_allocation_certified (limits : Limits) (library : Library) (state : State)
    (pc environment pointer : Nat) (instruction : Code) (heap : Heap) (source : Term)
    (found : library.program.code[pc]? = some instruction)
    (meaning : TermRowDenotes library.program state.heap (.closure pc environment) source)
    (cache : CacheCertified library.program state.heap state.data)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure pc environment) = .ok (pointer,heap)) :
    CacheCertified library.program heap (allocationState state heap pointer (directData instruction)).data := by
  apply cache.allocate _ allocated
  intro qualified
  cases instruction <;> simp only [directData] at qualified
  all_goals try contradiction
  · exact ⟨source, meaning, meaning.label_data found⟩
  · exact ⟨source, meaning, meaning.rfl_data found⟩

theorem dead_pair_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment first second pointer : Nat) (instruction : Code) (heap : Heap)
    (a : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.tup .Q0 first second))
    (firstCode : library.program.code[first]? = some instruction)
    (firstExact : CodeDenotes library.program first a)
    (captured : CapturedReady book library.program state.heap environment values)
    (stack : RetainedStack book library.program state.heap state.stack contexts)
    (cache : CacheCertified library.program state.heap state.data)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure first environment) = .ok (pointer,heap))
    (room : state.stack.length < limits.frames) :
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack
      (.second .Q0 (Term.sub (Env.sub values) a) (by intro impossible; cases impossible) :: contexts) ∧
    CapturedReady book library.program (step limits library state).heap environment values ∧
    CacheCertified library.program (step limits library state).heap (step limits library state).data := by
  have extension := allocate_extends allocated
  have head := allocate_closure_ready firstExact captured allocated
  have certified := closure_allocation_certified limits library state first environment pointer instruction
    heap _ firstCode (.closure firstExact captured.denotes) cache allocated
  rw [step_dead_pair limits library state pc environment first second pointer instruction heap
    control found firstCode allocated room]
  exact ⟨.cons (.second head (by intro impossible; cases impossible)) (stack.extends extension),
    captured.extends extension, certified⟩

theorem dead_let_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment value body pointer nextEnvironment : Nat) (instruction : Code)
    (middle heap : Heap) (v : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.lett .Q0 value body))
    (valueCode : library.program.code[value]? = some instruction)
    (valueExact : CodeDenotes library.program value v)
    (captured : CapturedReady book library.program state.heap environment values)
    (stack : RetainedStack book library.program state.heap state.stack contexts)
    (cache : CacheCertified library.program state.heap state.data)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure value environment) = .ok (pointer,middle))
    (installed : BendClosureArena.allocate limits.heap library.program.code.size middle
      (.environment pointer environment) = .ok (nextEnvironment,heap)) :
    CapturedReady book library.program (step limits library state).heap nextEnvironment
      (Term.sub (Env.sub values) v :: values) ∧
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack contexts ∧
    CacheCertified library.program (step limits library state).heap (step limits library state).data := by
  have firstExtension := allocate_extends allocated
  have secondExtension := allocate_extends installed
  have head := allocate_closure_ready valueExact captured allocated
  have ready := allocate_environment_ready head (captured.extends firstExtension) installed
  have middleCache := closure_allocation_certified limits library state value environment pointer instruction
    middle _ valueCode (.closure valueExact captured.denotes) cache allocated
  have certified := middleCache.allocate false installed (by intro impossible; cases impossible)
  rw [step_dead_let limits library state pc environment value body pointer nextEnvironment instruction middle heap
    control found valueCode allocated installed]
  exact ⟨ready, (stack.extends firstExtension).extends secondExtension, certified⟩

theorem return_function_dead_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (function argument environment pointer : Nat) (instruction : Code) (heap : Heap)
    (rest : List BendClosureMachine.Frame) (f x : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .returned function)
    (stackShape : state.stack = .function .Q0 argument environment :: rest)
    (found : library.program.code[argument]? = some instruction)
    (argumentExact : CodeDenotes library.program argument x)
    (captured : CapturedReady book library.program state.heap environment values)
    (functionReady : RetainedReady book library.program state.heap function f)
    (stack : RetainedStack book library.program state.heap rest contexts)
    (cache : CacheCertified library.program state.heap state.data)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure argument environment) = .ok (pointer,heap)) :
    RetainedReady book library.program (step limits library state).heap function f ∧
    RetainedReady book library.program (step limits library state).heap pointer (Term.sub (Env.sub values) x) ∧
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack contexts ∧
    CacheCertified library.program (step limits library state).heap (step limits library state).data := by
  have extension := allocate_extends allocated
  have argumentReady := allocate_closure_ready argumentExact captured allocated
  have certified := closure_allocation_certified limits library state argument environment pointer instruction
    heap _ found (.closure argumentExact captured.denotes) cache allocated
  rw [step_return_function_dead limits library state function argument environment pointer instruction heap rest
    control stackShape found allocated]
  exact ⟨functionReady.extends extension, argumentReady, stack.extends extension, certified⟩

#assert_axioms closure_allocation_certified
#assert_axioms dead_pair_retains
#assert_axioms dead_let_retains
#assert_axioms return_function_dead_retains
end Minidregg.Theory.BendClosureSimulation
