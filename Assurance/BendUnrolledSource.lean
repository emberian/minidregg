import Compiler.BendUnrolledIR2
import Assurance.BendObliviousSourceJoin

/- The general unrolled arithmetic path consumes the SAME raw controller/source
join. Coverage, initial loader denotation and decode-step refinement remain
visible hypotheses until their producers prove them for admitted programs. -/
namespace Minidregg.Assurance.BendUnrolledSource
open Minidregg.Compiler Minidregg.Theory
open ObliviousNetwork ObliviousUnroll BendClosureMachine BendClosureSimulation BendTT
open BendObliviousSourceJoin
set_option autoImplicit false

theorem acceptedRun_circuit (shape : BendObliviousState.Shape) (library : Library)
    (network : Network) (networkExact : BendObliviousController.network shape library = some network)
    {ticks : Nat} {input output : Array Bool}
    (execution : AcceptedRun network ticks input output) :
    circuitRun shape library ticks input = some output := by
  induction execution with
  | done input => rfl
  | step evaluated handled tail ih =>
    simpa [circuitRun, circuitStep, networkExact, evaluated, handled] using ih

/-- Receiving composition into the actual source invariant. The arithmetic
producer is BendUnrolledIR2.accepted_run; this theorem does not promote its
still-open loader/coverage/controller premises into universal correctness. -/
theorem acceptedRun_source {book : Book} (shape : BendObliviousState.Shape)
    (limits : Limits) (library : Library) (network : Network)
    (networkExact : BendObliviousController.network shape library = some network)
    (ticks : Nat) (state result : State) (origin : Term) (initialCount : Nat)
    (input output : Array Bool)
    (invariant : SourceInvariant book library.program origin initialCount state)
    (coverage : Covered book limits library ticks state)
    (initialDecoded : BendObliviousCodec.decode shape input = some state)
    (conformance : ∀ tick, tick < ticks → ∀ bits,
      circuitRun shape library tick input = some bits →
      BendObliviousCodec.decode shape bits = some (run limits library tick state) →
      ∃ next, circuitStep shape library bits = some next ∧
        BendObliviousCodec.decode shape next = some (step limits library (run limits library tick state)))
    (execution : AcceptedRun network ticks input output)
    (decoded : BendObliviousCodec.decode shape output = some result) :
    SourceInvariant book library.program origin initialCount result :=
  circuit_source_invariant shape limits library ticks state result origin initialCount input output
    invariant coverage initialDecoded conformance
    (acceptedRun_circuit shape library network networkExact execution) decoded

#assert_axioms acceptedRun_circuit
#assert_axioms acceptedRun_source
end Minidregg.Assurance.BendUnrolledSource
