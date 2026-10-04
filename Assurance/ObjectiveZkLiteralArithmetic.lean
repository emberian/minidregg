import Assurance.ObjectiveBendCommittedSource
import Assurance.ObjectiveZkLiteralInstance

/- The arithmetic receiver `arithmetic_observes_source` with its three refinement
premises DISCHARGED for the actual literal graph and program `.nat 7`:
`refinement`, `initial`, `readObservation`/`readSound` are no longer parameters.
The codec is the layout's one decoder (it reads the code, field, name,
environment and record regions from the bits), restricted to certified rows.
What remains are exactly the arithmetic premises: an arbitrary field assignment
satisfying the lowered constraints of the graph unrolled at the ENVELOPE's tick
count (`rate.ticks capacity`, never a measured count), with the execution inputs
pinned to the program's initial bits. -/
namespace Minidregg.Assurance.ObjectiveZkLiteralArithmetic
open Minidregg.Compiler Minidregg.Theory
open ObliviousNetwork ObliviousUnroll BendTraceConstraints BendCommittedRun
open Minidregg.Assurance.ObjectiveZkLiteralInstance
set_option autoImplicit false

theorem graph_valid : graph.valid = true := by native_decide
theorem graph_width : graph.outputs.size = graph.inputCount + 1 := by native_decide

theorem nat7_shape : nat7.initialBits.size = graph.inputCount := by
  rw [← prepared_graph nat7]
  exact nat7.initialShape

theorem nat7_arithmetic_observes_source {F : Type} [Field F]
    (rate : ObjectiveBendCommittedSource.PhysicalRate)
    (capacity : ObjectiveInvocationClaim.Capacity) (commitment : Network)
    (prepared : BendCommittedNetwork.Prepared (build graph (rate.ticks capacity)).network commitment)
    (commitmentValid : Nat) (remainingPins : List Nat)
    (wholeValid : (requireBoth prepared.candidate.whole
      (prepared.candidate.execution.wire (build graph (rate.ticks capacity)).network.inputCount
        (build graph (rate.ticks capacity)).handledWire) commitmentValid).valid = true)
    (assignment publicInputs : Nat → F) (publicSuccess : publicInputs 0 = 1)
    (inputBounds : ∀ index < graph.inputCount,
      prepared.candidate.execution.wire (build graph (rate.ticks capacity)).network.inputCount index <
        prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size + 1)
    (inputPinned : ∀ index < graph.inputCount,
      assignment (prepared.candidate.execution.wire (build graph (rate.ticks capacity)).network.inputCount index) =
        bit (F := F) (nat7.initialBits[index]?.getD false))
    (accepted : (BendTraceDirect.lower
      (constraints (requireBoth prepared.candidate.whole
        (prepared.candidate.execution.wire (build graph (rate.ticks capacity)).network.inputCount
          (build graph (rate.ticks capacity)).handledWire) commitmentValid))
      (prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size + 1)
      ((prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) :: remainingPins)).Holds
      assignment publicInputs) :
    ∃ wholeWires : Nat → Bool,
      AcceptedRun graph (rate.ticks capacity) nat7.initialBits
        (stateValues (fun i => wholeWires (prepared.candidate.execution.wire
          (build graph (rate.ticks capacity)).network.inputCount i)) (build graph (rate.ticks capacity))) ∧
      BooleanGraph commitment (fun i => wholeWires
        (prepared.candidate.commitment.wire commitment.inputCount i)) ∧
      wholeWires commitmentValid = true ∧
      ∀ observation, regionCodec.read
        (stateValues (fun i => wholeWires (prepared.candidate.execution.wire
          (build graph (rate.ticks capacity)).network.inputCount i)) (build graph (rate.ticks capacity))) = some observation →
        ObjectiveBendOpenRecursion.Evaluates (.nat 7)
          (ObjectiveBendDemandAdequacy.observationTerm observation) :=
  ObjectiveBendCommittedSource.arithmetic_observes_source graph rate capacity commitment
    graph_valid graph_width prepared commitmentValid remainingPins wholeValid
    nat7.initialBits nat7_shape assignment publicInputs publicSuccess inputBounds inputPinned
    accepted regionCodec.toRefinement (.nat 7) (.natural 7) nat7_initial regionCodec.read
    regionCodec.read_sound

#assert_compiled graph_valid
#assert_compiled graph_width
#assert_compiled nat7_shape
#assert_compiled nat7_arithmetic_observes_source
end Minidregg.Assurance.ObjectiveZkLiteralArithmetic
