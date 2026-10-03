import Assurance.BendUnrolledSource
import Theory.BendClosureInitialCoverage

/- The whole direct-value entry family now receives actual startup and source
coverage PRODUCERS. Raw controller/codec conformance remains explicit. This
removes those two former semantic premises without silently claiming coverage
for calls, closures, recursion or all source programs. -/
namespace Minidregg.Assurance.BendDirectUnrolledSource
open Minidregg.Compiler Minidregg.Theory
open ObliviousNetwork ObliviousUnroll BendClosureMachine BendClosureSimulation BendTT
open BendClosureArena BendObliviousSourceJoin BendUnrolledSource
set_option autoImplicit false

theorem acceptedRun_startedDirect_source {book : Book}
    (shape : BendObliviousState.Shape) (limits : Limits) (library : Library)
    (network : Network)
    (networkExact : BendObliviousController.network shape library = some network)
    (padding : Nat) (state result : State) (origin : Term)
    (entry pointer : Nat) (instruction : Code) (heap : Heap)
    (started : start limits library entry = .ok state)
    (entryExact : CodeDenotes library.program entry origin)
    (found : library.program.code[entry]? = some instruction)
    (direct : directValue instruction = true)
    (allocated : BendClosureArena.allocate limits.heap library.program.code.size state.heap
      (.closure entry 0) = .ok (pointer,heap))
    (input output : Array Bool)
    (initialDecoded : BendObliviousCodec.decode shape input = some state)
    (conformance : ∀ tick, tick < ((padding + 1) + 1) → ∀ bits,
      circuitRun shape library tick input = some bits →
      BendObliviousCodec.decode shape bits = some (run limits library tick state) →
      ∃ next, circuitStep shape library bits = some next ∧
        BendObliviousCodec.decode shape next = some (step limits library (run limits library tick state)))
    (execution : AcceptedRun network ((padding + 1) + 1) input output)
    (decoded : BendObliviousCodec.decode shape output = some result) :
    SourceInvariant book library.program origin 0 result := by
  obtain ⟨_,_,_,_,counter,represented⟩ :=
    start_ready (book := book) limits library entry state origin started entryExact
  have initial : SourceInvariant book library.program origin 0 state :=
    ⟨0, origin, .refl origin, represented, by simpa using counter⟩
  have coverage := started_direct_coverage (book := book) limits library state entry pointer
    instruction heap padding started found direct allocated
  exact acceptedRun_source shape limits library network networkExact ((padding + 1) + 1)
    state result origin 0 input output initial coverage initialDecoded conformance execution decoded

#assert_axioms acceptedRun_startedDirect_source
end Minidregg.Assurance.BendDirectUnrolledSource
