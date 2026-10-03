/- Preservation producers for the reachable readiness invariant, attached to
literal Machine.step equations. These preserve future code captures, retained
values and certified Data bits; they do not assert whole-machine coverage. -/
import Theory.BendClosureRetainedFrames

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem application_retains_stack {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment function argument : Nat) (q : Quan) (x : Term) (values : Env)
    (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.app q function argument))
    (argumentCode : CodeDenotes library.program argument x)
    (captured : CapturedReady book library.program state.heap environment values)
    (stack : RetainedStack book library.program state.heap state.stack contexts)
    (room : state.stack.length < limits.frames) :
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack
      (.function q (Term.sub (Env.sub values) x) :: contexts) := by
  rw [step_application limits library state pc environment function argument q control found room]
  exact .cons (.function argumentCode captured) stack

theorem live_let_retains_stack {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment value body : Nat) (q : Quan) (f : Term) (values : Env)
    (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.lett q value body))
    (bodyCode : CodeDenotes library.program body f)
    (captured : CapturedReady book library.program state.heap environment values)
    (stack : RetainedStack book library.program state.heap state.stack contexts)
    (live : q.live = true) (room : state.stack.length < limits.frames) :
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack
      (.lett q (Term.sub (Subst.up (Env.sub values)) f) live :: contexts) := by
  rw [step_live_let limits library state pc environment value body q control found live room]
  exact .cons (.lett bodyCode captured live) stack

theorem live_pair_retains_stack {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment first second : Nat) (q : Quan) (b : Term) (values : Env)
    (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.tup q first second))
    (secondCode : CodeDenotes library.program second b)
    (captured : CapturedReady book library.program state.heap environment values)
    (stack : RetainedStack book library.program state.heap state.stack contexts)
    (live : q.live = true) (room : state.stack.length < limits.frames) :
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack
      (.first q (Term.sub (Env.sub values) b) live :: contexts) := by
  rw [step_live_pair limits library state pc environment first second q control found live room]
  exact .cons (.first secondCode captured live) stack

theorem rewrite_retains_stack {book : Book} (limits : Limits) (library : Library) (state : State)
    (pc environment evidence motive body : Nat) (f p : Term) (values : Env)
    (contexts : List (Context book))
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.rwt evidence motive body))
    (bodyCode : CodeDenotes library.program body f)
    (captured : CapturedReady book library.program state.heap environment values)
    (stack : RetainedStack book library.program state.heap state.stack contexts)
    (room : state.stack.length < limits.frames) :
    RetainedStack book library.program (step limits library state).heap (step limits library state).stack
      (.rewrite p (Term.sub (Env.sub values) f) :: contexts) := by
  rw [step_rewrite limits library state pc environment evidence motive body control found room]
  exact .cons (.rewrite bodyCode captured) stack

/-- Actual pair allocation preserves transitive pointer readiness, the rest of
the stack and the Data-cache certificate in one shared receiving theorem. -/
theorem return_pair_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (pointer first result : Nat) (q : Quan) (heap : Heap) (rest : List BendClosureMachine.Frame)
    (a b : Term) (contexts : List (Context book))
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .second q first :: rest)
    (firstReady : RetainedReady book library.program state.heap first a)
    (firstValue : q.live = true → Value book a)
    (secondReady : RetainedReady book library.program state.heap pointer b) (secondValue : Value book b)
    (stack : RetainedStack book library.program state.heap rest contexts)
    (cache : CacheCertified library.program state.heap state.data)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.pair q first pointer) = .ok (result,heap)) :
    RetainedReady book library.program (step limits library state).heap result (.Tup q a b) ∧
      RetainedStack book library.program (step limits library state).heap (step limits library state).stack contexts ∧
      CacheCertified library.program (step limits library state).heap (step limits library state).data := by
  have ready := allocate_pair_ready firstReady secondReady (.tup firstValue secondValue) allocated
  have certified := (pair_allocation_sound limits library state q first pointer result heap (.Tup q a b)
    cache (.pair firstReady.denotes secondReady.denotes) allocated).2.2
  rw [step_return_second limits library state pointer first result q heap rest control stackShape allocated]
  exact ⟨ready, stack.extends (allocate_extends allocated), certified⟩

/-- A successful live let installs the actual environment cell with its head
and whole old capture chain ready. The environment cache bit is false. -/
theorem return_let_retains {book : Book} (limits : Limits) (library : Library) (state : State)
    (pointer body environment nextEnvironment : Nat) (q : Quan) (heap : Heap)
    (rest : List BendClosureMachine.Frame) (v : Term) (values : Env) (contexts : List (Context book))
    (control : state.control = .returned pointer)
    (stackShape : state.stack = .lett q body environment :: rest)
    (headReady : RetainedReady book library.program state.heap pointer v)
    (captured : CapturedReady book library.program state.heap environment values)
    (copied : q = .Q2 → state.data[pointer]?.getD false = true)
    (stack : RetainedStack book library.program state.heap rest contexts)
    (cache : CacheCertified library.program state.heap state.data)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size
      state.heap (.environment pointer environment) = .ok (nextEnvironment,heap)) :
    CapturedReady book library.program (step limits library state).heap nextEnvironment (v :: values) ∧
      RetainedStack book library.program (step limits library state).heap (step limits library state).stack contexts ∧
      CacheCertified library.program (step limits library state).heap (step limits library state).data := by
  have ready := allocate_environment_ready headReady captured allocated
  have certified := cache.allocate false allocated (by intro impossible; cases impossible)
  rw [step_return_let limits library state pointer body environment nextEnvironment q heap rest
    control stackShape copied allocated]
  exact ⟨ready, stack.extends (allocate_extends allocated), certified⟩

#assert_axioms application_retains_stack
#assert_axioms live_let_retains_stack
#assert_axioms live_pair_retains_stack
#assert_axioms rewrite_retains_stack
#assert_axioms return_pair_retains
#assert_axioms return_let_retains
end Minidregg.Theory.BendClosureSimulation
