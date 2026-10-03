/- Initial readiness is derived from successful Machine.start itself, not
accepted as an external runtime certificate. The entry's source correspondence
comes from the actual compiler validator; typing/authority remain separate. -/
import Theory.BendClosureRetainedReturns

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

theorem start_fields (limits : Limits) (library : Library) (entry : Nat) (state : State)
    (started : start limits library entry = .ok state) :
    state.heap.get? 0 = some .nil ∧ state.data = Array.replicate limits.heap.slots false ∧
    state.stack = [] ∧ state.control = .evaluate entry 0 ∧ state.sourceSteps = 0 := by
  unfold start at started
  split at started
  · contradiction
  · split at started
    · contradiction
    next pointer heap allocated =>
      cases started
      have pointerZero : pointer = 0 := (allocate_shape allocated).1
      have rowFound := allocate_reads_new allocated
      rw [pointerZero] at rowFound
      exact ⟨rowFound,rfl,rfl,rfl,rfl⟩

theorem start_ready {book : Book} (limits : Limits) (library : Library) (entry : Nat)
    (state : State) (source : Term)
    (started : start limits library entry = .ok state)
    (entryExact : CodeDenotes library.program entry source) :
    CapturedReady book library.program state.heap 0 [] ∧
    RetainedFocus book library.program state.heap state.control source ∧
    RetainedStack book library.program state.heap state.stack [] ∧
    CacheCertified library.program state.heap state.data ∧ state.sourceSteps = 0 ∧
    StateDenotes book library.program state source := by
  obtain ⟨emptyRow,bits,stackShape,control,count⟩ := start_fields limits library entry state started
  have captured : CapturedReady book library.program state.heap 0 [] := .nil emptyRow
  have focus : RetainedFocus book library.program state.heap state.control source := by
    rw [control]
    simpa only [env_nil, sub_var] using (RetainedFocus.evaluate entryExact captured)
  have stack : RetainedStack book library.program state.heap state.stack [] := by
    rw [stackShape]; exact .nil
  refine ⟨captured,focus,stack,?_,count,?_⟩
  · intro pointer bit
    rw [bits] at bit
    simp only [Array.getElem?_replicate] at bit
    split at bit <;> contradiction
  · exact StateDenotes.exact (contexts := []) focus.denotes stack.denotes
      (by intro pointer impossible; rw [control] at impossible; cases impossible)

#assert_axioms start_fields
#assert_axioms start_ready
end Minidregg.Theory.BendClosureSimulation
