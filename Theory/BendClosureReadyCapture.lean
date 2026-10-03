/- Q0 capture preserves the full reachable-state invariant. Actual successful
allocations are computational premises, never assertions about the future state. -/
import Theory.BendClosureReadyCompound

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem ReadyState.dead_pair {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment first second pointer : Nat) (heap : Heap)
    (ready : ReadyState book library.program state source)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.tup .Q0 first second))
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure first environment) = .ok (pointer,heap))
    (room : state.stack.length < limits.frames) :
    ReadyState book library.program (step limits library state) source := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | evaluate sourceExact captured =>
        obtain ⟨a,b,same,firstCode,secondCode⟩ := sourceExact.pair_fields .Q0 first second found
        cases same
        obtain ⟨instruction,firstFound⟩ := firstCode.code_exists
        have extension := allocate_extends allocated
        have head := allocate_closure_ready firstCode captured allocated
        have certified := closure_allocation_certified limits library state first environment pointer instruction
          heap _ firstFound (.closure firstCode captured.denotes) cache allocated
        rw [step_dead_pair limits library state pc environment first second pointer instruction heap
          control found firstFound allocated room]
        exact ReadyState.exact (contexts := .second .Q0 (Term.sub _ a) (by intro h; cases h) :: _)
          (.basic (.evaluate secondCode (captured.extends extension)))
          (.cons (.second head (by intro h; cases h)) (stack.extends extension)) certified
          (extension 0 .nil empty) (by intro result impossible; cases impossible)

theorem ReadyState.dead_let {book : Book} (limits : Limits) (library : Library) (state : State)
    (source : Term) (pc environment value body pointer nextEnvironment : Nat) (middle heap : Heap)
    (ready : ReadyState book library.program state source)
    (control : state.control = .evaluate pc environment)
    (found : library.program.code[pc]? = some (.lett .Q0 value body))
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure value environment) = .ok (pointer,middle))
    (installed : BendClosureArena.allocate limits.heap library.program.code.size middle
      (.environment pointer environment) = .ok (nextEnvironment,heap)) :
    ∃ nextSource, ReadyState book library.program (step limits library state) nextSource ∧
      Eval book source nextSource := by
  cases ready with
  | exact focus stack cache empty complete =>
    rw [control] at focus
    cases focus with
    | basic focus =>
      cases focus with
      | evaluate sourceExact captured =>
        obtain ⟨v,f,same,valueCode,bodyCode⟩ := sourceExact.let_fields .Q0 value body found
        cases same
        obtain ⟨instruction,valueFound⟩ := valueCode.code_exists
        have firstExtension := allocate_extends allocated
        have secondExtension := allocate_extends installed
        have head := allocate_closure_ready valueCode captured allocated
        have newCaptured := allocate_environment_ready head (captured.extends firstExtension) installed
        have middleCache := closure_allocation_certified limits library state value environment pointer instruction
          middle _ valueFound (.closure valueCode captured.denotes) cache allocated
        have certified := middleCache.allocate false installed (by intro impossible; cases impossible)
        rename_i contexts values
        refine ⟨plug contexts (Term.sub (Env.sub (Term.sub (Env.sub values) v :: values)) f),?_,?_⟩
        · rw [step_dead_let limits library state pc environment value body pointer nextEnvironment instruction middle heap
            control found valueFound allocated installed]
          exact ReadyState.exact (.basic (.evaluate bodyCode newCaptured))
            ((stack.extends firstExtension).extends secondExtension) certified
            (secondExtension 0 .nil (firstExtension 0 .nil empty))
            (by intro result impossible; cases impossible)
        · apply plug_eval
          rw [captured_body_inst]
          exact .unlet (by intro impossible; cases impossible) (by intro impossible; cases impossible)

#assert_axioms ReadyState.dead_pair
#assert_axioms ReadyState.dead_let
end Minidregg.Theory.BendClosureSimulation
