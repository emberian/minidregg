/- Cached Data qualification for the actual StateT allocator, not an abstract
allocator contract. A term-row denotation is supplied by the reachable control
that allocates it; a true bit is then backed by actual source Data. -/
import Theory.BendClosureAllocation
import Theory.BendClosureMachine

namespace Minidregg.Theory.BendClosureSimulation
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

/-- Literal controller poststate, shared by the proof equations below. -/
def allocationState (before : State) (heap : Heap) (pointer : Nat) (qualified : Bool) : State :=
  {before with heap, data := (before.data.toList.zipIdx.map fun p =>
    if p.2 = pointer then qualified else p.1).toArray}

theorem pair_allocation_run (limits : Limits) (library : Library) (before : State)
    (q : Quan) (first second pointer : Nat) (heap : Heap)
    (accepted : BendClosureArena.allocate limits.heap library.program.code.size
      before.heap (.pair q first second) = .ok (pointer, heap)) :
    (BendClosureMachine.allocate limits library (.pair q first second)).run before =
      .ok (pointer, allocationState before heap pointer
        ((!q.live || before.data[first]?.getD false) && before.data[second]?.getD false)) := by
  simp [BendClosureMachine.allocate, accepted, allocationState]
  rfl

theorem label_allocation_run (limits : Limits) (library : Library) (before : State)
    (pc environment label pointer : Nat) (heap : Heap)
    (instruction : library.program.code[pc]? = some (.lab label))
    (accepted : BendClosureArena.allocate limits.heap library.program.code.size
      before.heap (.closure pc environment) = .ok (pointer, heap)) :
    (BendClosureMachine.allocate limits library (.closure pc environment)).run before =
      .ok (pointer, allocationState before heap pointer true) := by
  simp [BendClosureMachine.allocate, code, instruction, accepted, allocationState]
  rfl

theorem rfl_allocation_run (limits : Limits) (library : Library) (before : State)
    (pc environment pointer : Nat) (heap : Heap)
    (instruction : library.program.code[pc]? = some .rfl)
    (accepted : BendClosureArena.allocate limits.heap library.program.code.size
      before.heap (.closure pc environment) = .ok (pointer, heap)) :
    (BendClosureMachine.allocate limits library (.closure pc environment)).run before =
      .ok (pointer, allocationState before heap pointer true) := by
  simp [BendClosureMachine.allocate, code, instruction, accepted, allocationState]
  rfl

theorem pair_allocation_sound (limits : Limits) (library : Library) (before : State)
    (q : Quan) (first second pointer : Nat) (heap : Heap) (source : Term)
    (certified : CacheCertified library.program before.heap before.data)
    (meaning : TermRowDenotes library.program before.heap (.pair q first second) source)
    (accepted : BendClosureArena.allocate limits.heap library.program.code.size
      before.heap (.pair q first second) = .ok (pointer, heap)) :
    let qualified := ((!q.live || before.data[first]?.getD false) && before.data[second]?.getD false)
    let next := allocationState before heap pointer qualified
    (BendClosureMachine.allocate limits library (.pair q first second)).run before = .ok (pointer,next) ∧
      Denotes library.program next.heap pointer source ∧
      CacheCertified library.program next.heap next.data := by
  dsimp only
  refine ⟨pair_allocation_run limits library before q first second pointer heap accepted,
    allocate_term meaning accepted, ?_⟩
  apply certified.allocate _ accepted
  intro qualified
  exact ⟨source, meaning, TermRowDenotes.pair_data certified meaning qualified⟩

theorem label_allocation_sound (limits : Limits) (library : Library) (before : State)
    (pc environment label pointer : Nat) (heap : Heap) (source : Term)
    (certified : CacheCertified library.program before.heap before.data)
    (meaning : TermRowDenotes library.program before.heap (.closure pc environment) source)
    (instruction : library.program.code[pc]? = some (.lab label))
    (accepted : BendClosureArena.allocate limits.heap library.program.code.size
      before.heap (.closure pc environment) = .ok (pointer, heap)) :
    let next := allocationState before heap pointer true
    (BendClosureMachine.allocate limits library (.closure pc environment)).run before = .ok (pointer,next) ∧
      Denotes library.program next.heap pointer source ∧
      Data source ∧ CacheCertified library.program next.heap next.data := by
  dsimp only
  refine ⟨label_allocation_run limits library before pc environment label pointer heap instruction accepted,
    allocate_term meaning accepted, meaning.label_data instruction, ?_⟩
  apply certified.allocate _ accepted
  intro qualified
  exact ⟨source, meaning, meaning.label_data instruction⟩

theorem rfl_allocation_sound (limits : Limits) (library : Library) (before : State)
    (pc environment pointer : Nat) (heap : Heap) (source : Term)
    (certified : CacheCertified library.program before.heap before.data)
    (meaning : TermRowDenotes library.program before.heap (.closure pc environment) source)
    (instruction : library.program.code[pc]? = some .rfl)
    (accepted : BendClosureArena.allocate limits.heap library.program.code.size
      before.heap (.closure pc environment) = .ok (pointer, heap)) :
    let next := allocationState before heap pointer true
    (BendClosureMachine.allocate limits library (.closure pc environment)).run before = .ok (pointer,next) ∧
      Denotes library.program next.heap pointer source ∧
      Data source ∧ CacheCertified library.program next.heap next.data := by
  dsimp only
  refine ⟨rfl_allocation_run limits library before pc environment pointer heap instruction accepted,
    allocate_term meaning accepted, meaning.rfl_data instruction, ?_⟩
  apply certified.allocate _ accepted
  intro qualified
  exact ⟨source, meaning, meaning.rfl_data instruction⟩

#assert_axioms pair_allocation_run
#assert_axioms label_allocation_run
#assert_axioms rfl_allocation_run
#assert_axioms pair_allocation_sound
#assert_axioms label_allocation_sound
#assert_axioms rfl_allocation_sound
end Minidregg.Theory.BendClosureSimulation

