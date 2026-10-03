/- Readiness of the actual original-call allocation and spine peeling. The
current head and original pending application are separate runtime pointers. -/
import Theory.BendClosureReadyReturn
import Theory.BendClosureCallSpine

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem SpineReady.application_fields {book : Book} {program : Program} {heap : Heap}
    {pointer function argument : Nat} {q : Quan} {source : Term}
    (ready : SpineReady book program heap pointer source)
    (found : heap.get? pointer = some (.application q function argument)) :
    ∃ f x, source = .App q f x ∧ SpineReady book program heap function f ∧
      RetainedReady book program heap argument x ∧ (q.live = true → Value book x) := by
  cases ready with
  | head ready =>
    cases ready with
    | reference other code captured => rw [found] at other; cases other
    | value ready value =>
      cases ready with
      | closure other code captured => rw [found] at other; cases other
      | pair other first second pairValue => rw [found] at other; cases other
      | application other left right appValue =>
        rw [found] at other
        cases other
        exact ⟨_,_,rfl,.head (.value left (value_app appValue).1),right,(value_app appValue).2⟩
  | application other left right live =>
    rw [found] at other
    cases other
    exact ⟨_,_,rfl,left,right,live⟩

theorem ReadyState.apply_residual_closure {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (function argument pc environment original : Nat) (q : Quan) (instruction : Code) (heap : Heap)
    (ready : ReadyState book library.program state source)
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.closure pc environment))
    (found : library.program.code[pc]? = some instruction)
    (residual : residualApplication instruction = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.application q function argument) = .ok (original,heap)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | apply functionReady argumentReady functionValue argumentValue =>
        have extension := allocate_extends allocated
        obtain ⟨originalReady,certified⟩ := allocate_pending_call limits library state function argument original q heap
          _ _ functionReady argumentReady cache allocated
        rw [step_apply_residual_closure limits library state function argument pc environment original q instruction heap
          control functionRow found residual allocated]
        exact ReadyState.exact
          (.unspine (arguments := [(q,_)]) (.head (.value (functionReady.extends extension) functionValue)) originalReady
            (.cons ⟨rfl,argumentReady.extends extension⟩ .nil) rfl (.cons argumentValue .nil))
          (stack.extends extension) certified (extension 0 .nil empty)
          (by intro pointer impossible; cases impossible)

theorem ReadyState.apply_residual_application {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (function argument left right original : Nat) (q r : Quan) (heap : Heap)
    (ready : ReadyState book library.program state source)
    (control : state.control = .apply q function argument)
    (functionRow : state.heap.get? function = some (.application r left right))
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.application q function argument) = .ok (original,heap)) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | apply functionReady argumentReady functionValue argumentValue =>
        have extension := allocate_extends allocated
        obtain ⟨originalReady,certified⟩ := allocate_pending_call limits library state function argument original q heap
          _ _ functionReady argumentReady cache allocated
        rw [step_apply_residual_application limits library state function argument left right original q r heap
          control functionRow allocated]
        exact ReadyState.exact
          (.unspine (arguments := [(q,_)]) (.head (.value (functionReady.extends extension) functionValue)) originalReady
            (.cons ⟨rfl,argumentReady.extends extension⟩ .nil) rfl (.cons argumentValue .nil))
          (stack.extends extension) certified (extension 0 .nil empty)
          (by intro pointer impossible; cases impossible)

theorem ReadyState.unspine_application {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pointer original function argument : Nat) (q : Quan) (args : List (Quan × Nat))
    (ready : ReadyState book library.program state source)
    (control : state.control = .unspine pointer original args)
    (found : state.heap.get? pointer = some (.application q function argument))
    (room : args.length ≤ limits.arguments)
    (expandedRoom : ((q,argument) :: args).length ≤ limits.arguments) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic impossible => cases impossible
    | unspine head originalReady argsReady identity values =>
      obtain ⟨f,x,same,functionReady,argumentReady,argumentValue⟩ := head.application_fields found
      cases same
      rw [step_unspine_application limits library state pointer original function argument q args control found room expandedRoom]
      exact ReadyState.exact
        (.unspine (arguments := (q,x) :: _) functionReady originalReady
          (.cons ⟨rfl,argumentReady⟩ argsReady) identity (.cons argumentValue values))
        stack cache empty (by intro result impossible; cases impossible)

#assert_axioms SpineReady.application_fields
#assert_axioms ReadyState.apply_residual_closure
#assert_axioms ReadyState.apply_residual_application
#assert_axioms ReadyState.unspine_application
end Minidregg.Theory.BendClosureSimulation
