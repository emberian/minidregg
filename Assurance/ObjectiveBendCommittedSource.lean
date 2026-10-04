import Assurance.ObjectiveBendProofSource
import Compiler.BendCommittedUnroll

/- One formal receiving chain: arbitrary arithmetic witness -> both actual
shared graphs -> fixed physical run -> lazy macrosteps -> Objective source
meaning. The concrete controller/codec refinement and independently admitted
source/input identities remain producer obligations. No native PCS theorem
or full-transcript ZK claim is manufactured by this composition. -/
namespace Minidregg.Assurance.ObjectiveBendCommittedSource
open Minidregg.Compiler Minidregg.Theory
open ObliviousNetwork ObliviousUnroll BendTraceConstraints BendCommittedRun
set_option autoImplicit false

theorem arithmetic_observes_source {F : Type} [Field F]
    (original : Network) (ticks : Nat) (commitment : Network)
    (valid : original.valid = true) (width : original.outputs.size = original.inputCount + 1)
    (prepared : BendCommittedNetwork.Prepared (build original ticks).network commitment)
    (commitmentValid : Nat) (remainingPins : List Nat)
    (wholeValid : (requireBoth prepared.candidate.whole
      (prepared.candidate.execution.wire (build original ticks).network.inputCount
        (build original ticks).handledWire) commitmentValid).valid = true)
    (inputs : Array Bool) (shape : inputs.size = original.inputCount)
    (assignment publicInputs : Nat → F) (publicSuccess : publicInputs 0 = 1)
    (inputBounds : ∀ index < original.inputCount,
      prepared.candidate.execution.wire (build original ticks).network.inputCount index <
        prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size + 1)
    (inputPinned : ∀ index < original.inputCount,
      assignment (prepared.candidate.execution.wire (build original ticks).network.inputCount index) =
        bit (F := F) (inputs[index]?.getD false))
    (accepted : (BendTraceDirect.lower
      (constraints (requireBoth prepared.candidate.whole
        (prepared.candidate.execution.wire (build original ticks).network.inputCount
          (build original ticks).handledWire) commitmentValid))
      (prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size + 1)
      ((prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) :: remainingPins)).Holds
      assignment publicInputs)
    (refinement : ObjectiveBendProofSource.PackedRefinement original)
    (source : ObjectiveBendOpenRecursion.Term) (closed : ObjectiveBendDemandInvariant.Scoped 0 source)
    (initial : refinement.represents inputs (ObjectiveBendDemandMachine.initial source))
    (readObservation : Array Bool → Option ObjectiveBendOpenRecursion.Observation)
    (readSound : ∀ bits state observation, refinement.represents bits state →
      readObservation bits = some observation → state.control =
        .complete (ObjectiveBendDemandAdequacy.observationRuntime observation)) :
    ∃ wholeWires : Nat → Bool,
      AcceptedRun original ticks inputs
        (stateValues (fun i => wholeWires (prepared.candidate.execution.wire
          (build original ticks).network.inputCount i)) (build original ticks)) ∧
      BooleanGraph commitment (fun i => wholeWires
        (prepared.candidate.commitment.wire commitment.inputCount i)) ∧
      wholeWires commitmentValid = true ∧
      ∀ observation, readObservation
        (stateValues (fun i => wholeWires (prepared.candidate.execution.wire
          (build original ticks).network.inputCount i)) (build original ticks)) = some observation →
        ObjectiveBendOpenRecursion.Evaluates source
          (ObjectiveBendDemandAdequacy.observationTerm observation) := by
  obtain ⟨wires,run,graph,success⟩ := BendCommittedUnroll.accepted_run
    original ticks commitment valid width prepared commitmentValid remainingPins wholeValid
    inputs shape assignment publicInputs publicSuccess inputBounds inputPinned accepted
  refine ⟨wires,run,graph,success,?_⟩
  intro observation read
  exact ObjectiveBendProofSource.completed_observation refinement closed run initial observation
    (fun state represented => readSound _ state observation represented read)


/-- Same arbitrary-field receiving chain for lazy and higher-order results. -/
theorem arithmetic_returns_source_value {F : Type} [Field F]
    (original : Network) (ticks : Nat) (commitment : Network)
    (valid : original.valid = true) (width : original.outputs.size = original.inputCount + 1)
    (prepared : BendCommittedNetwork.Prepared (build original ticks).network commitment)
    (commitmentValid : Nat) (remainingPins : List Nat)
    (wholeValid : (requireBoth prepared.candidate.whole
      (prepared.candidate.execution.wire (build original ticks).network.inputCount
        (build original ticks).handledWire) commitmentValid).valid = true)
    (inputs : Array Bool) (shape : inputs.size = original.inputCount)
    (assignment publicInputs : Nat → F) (publicSuccess : publicInputs 0 = 1)
    (inputBounds : ∀ index < original.inputCount,
      prepared.candidate.execution.wire (build original ticks).network.inputCount index <
        prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size + 1)
    (inputPinned : ∀ index < original.inputCount,
      assignment (prepared.candidate.execution.wire (build original ticks).network.inputCount index) =
        bit (F := F) (inputs[index]?.getD false))
    (accepted : (BendTraceDirect.lower
      (constraints (requireBoth prepared.candidate.whole
        (prepared.candidate.execution.wire (build original ticks).network.inputCount
          (build original ticks).handledWire) commitmentValid))
      (prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size + 1)
      ((prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) :: remainingPins)).Holds
      assignment publicInputs)
    (refinement : ObjectiveBendProofSource.PackedRefinement original)
    (source : ObjectiveBendOpenRecursion.Term) (closed : ObjectiveBendDemandInvariant.Scoped 0 source)
    (initial : refinement.represents inputs (ObjectiveBendDemandMachine.initial source))
    (readValue : Array Bool → Option ObjectiveBendDemandMachine.RuntimeValue)
    (readSound : ∀ bits state value, refinement.represents bits state →
      readValue bits = some value → state.control =
        .complete (value)) :
    ∃ wholeWires : Nat → Bool,
      AcceptedRun original ticks inputs
        (stateValues (fun i => wholeWires (prepared.candidate.execution.wire
          (build original ticks).network.inputCount i)) (build original ticks)) ∧
      BooleanGraph commitment (fun i => wholeWires
        (prepared.candidate.commitment.wire commitment.inputCount i)) ∧
      wholeWires commitmentValid = true ∧
      ∀ value, readValue
        (stateValues (fun i => wholeWires (prepared.candidate.execution.wire
          (build original ticks).network.inputCount i)) (build original ticks)) = some value →
        ∃ final meaning,
          refinement.represents
            (stateValues (fun i => wholeWires (prepared.candidate.execution.wire
              (build original ticks).network.inputCount i)) (build original ticks)) final ∧
          ObjectiveBendDemandAdequacy.MeaningsScoped final.heap.size meaning ∧
          ObjectiveBendDemandAdequacy.HeapRealizes meaning final.heap ∧
          ObjectiveBendOpenRecursion.Evaluates source
            (ObjectiveBendDemandAdequacy.valueMeaning meaning value) := by
  obtain ⟨wires,run,graph,success⟩ := BendCommittedUnroll.accepted_run
    original ticks commitment valid width prepared commitmentValid remainingPins wholeValid
    inputs shape assignment publicInputs publicSuccess inputBounds inputPinned accepted
  refine ⟨wires,run,graph,success,?_⟩
  intro value read
  exact ObjectiveBendProofSource.completed_value refinement closed run initial value
    (fun state represented => readSound _ state value represented read)

#assert_axioms arithmetic_returns_source_value

#assert_axioms arithmetic_observes_source
end Minidregg.Assurance.ObjectiveBendCommittedSource
