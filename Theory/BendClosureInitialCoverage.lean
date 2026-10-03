/- Generated coverage for the whole direct-value entry family, including any
padding after completion. This is a general operational theorem, not a closed
fixture or a supplied Covered premise. Other entry forms still require the
full reachable invariant and are not asserted by this restricted theorem. -/
import Theory.BendClosureStartup
import Theory.BendClosureSupportedRun

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem Covered.returned_empty {book : Book} {limits : Limits} {library : Library}
    (ticks : Nat) (state : State) (pointer : Nat)
    (control : state.control = .returned pointer) (empty : state.stack = []) :
    Covered book limits library (ticks + 1) state := by
  refine ⟨?_, ?_⟩
  · intro source represented
    cases represented with
    | exact focus stack complete =>
      rw [empty] at stack
      cases stack
      rw [control] at focus
      cases focus with
      | returned term value => exact .returnEmpty state pointer _ control empty term value
  · apply Covered.complete ticks _ pointer
    rw [step_return_empty limits library state pointer control empty]

theorem Covered.direct_entry {book : Book} (limits : Limits) (library : Library)
    (state : State) (pc environment pointer : Nat) (instruction : Code) (heap : Heap) (padding : Nat)
    (control : state.control = .evaluate pc environment) (empty : state.stack = [])
    (found : library.program.code[pc]? = some instruction)
    (direct : directValue instruction = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure pc environment) = .ok (pointer,heap)) :
    Covered book limits library ((padding + 1) + 1) state := by
  refine ⟨?_, ?_⟩
  · intro source represented
    cases represented with
    | exact focus stack complete =>
      rw [empty] at stack
      cases stack
      rw [control] at focus
      cases focus with
      | evaluate closure =>
        cases closure with
        | exact code captured =>
          exact .directValue state pc environment pointer instruction heap _ _ [] control found direct
            code captured (by rw [empty]; exact .nil) allocated
  · apply Covered.returned_empty padding _ pointer
    · rw [step_direct_value limits library state pc environment pointer instruction heap control found direct allocated]
    · rw [step_direct_value limits library state pc environment pointer instruction heap control found direct allocated]
      exact empty

theorem started_direct_coverage {book : Book} (limits : Limits) (library : Library)
    (state : State) (entry pointer : Nat) (instruction : Code) (heap : Heap) (padding : Nat)
    (started : start limits library entry = .ok state)
    (found : library.program.code[entry]? = some instruction)
    (direct : directValue instruction = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure entry 0) = .ok (pointer,heap)) :
    Covered book limits library ((padding + 1) + 1) state := by
  obtain ⟨_,_,empty,control,_⟩ := start_fields limits library entry state started
  exact Covered.direct_entry limits library state entry 0 pointer instruction heap padding
    control empty found direct allocated

/-- Actual source trace from actual startup and capacity-qualified allocation;
no supplied coverage or successor/source equality occurs among the premises. -/
theorem started_direct_source {book : Book} (limits : Limits) (library : Library)
    (state : State) (entry pointer : Nat) (instruction : Code) (heap : Heap) (padding : Nat) (source : Term)
    (started : start limits library entry = .ok state)
    (entryExact : CodeDenotes library.program entry source)
    (found : library.program.code[entry]? = some instruction)
    (direct : directValue instruction = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure entry 0) = .ok (pointer,heap)) :
    ∃ count result, BendLiveMachine.Trace book count source result ∧
      StateDenotes book library.program (run limits library ((padding + 1) + 1) state) result ∧
      (run limits library ((padding + 1) + 1) state).sourceSteps = count := by
  obtain ⟨_,_,_,_,count,represented⟩ := start_ready (book := book) limits library entry state source started entryExact
  obtain ⟨n,result,trace,afterSource,afterCount⟩ := covered_run ((padding + 1) + 1) state source represented
    (started_direct_coverage limits library state entry pointer instruction heap padding started found direct allocated)
  exact ⟨n,result,trace,afterSource,by simpa only [count,Nat.zero_add] using afterCount⟩

#assert_axioms Covered.returned_empty
#assert_axioms Covered.direct_entry
#assert_axioms started_direct_coverage
#assert_axioms started_direct_source
end Minidregg.Theory.BendClosureSimulation
