import Compiler.BendCommittedNetwork
import Compiler.ObliviousUnrollSemantics

/- Success is itself constrained. A commitment to a refused run must not be
accepted merely because its canonical hash is valid. This adapter adds one
counted AND gate joining execution handled and commitment validity. -/
namespace Minidregg.Compiler.BendCommittedRun
open ObliviousNetwork BendTraceConstraints ObliviousUnroll
set_option autoImplicit false

def requireBoth (network : Network) (executionHandled commitmentValid : Nat) : Network :=
  { network with
    gates := network.gates.push (.and executionHandled commitmentValid)
    outputs := #[network.inputCount + network.gates.size] ++ network.outputs }

theorem requireBoth_value (network : Network) (executionHandled commitmentValid : Nat)
    (wires : Nat → Bool)
    (graph : BooleanGraph (requireBoth network executionHandled commitmentValid) wires) :
    wires (network.inputCount + network.gates.size) =
      (wires executionHandled && wires commitmentValid) := by
  have member : (.and executionHandled commitmentValid, network.gates.size) ∈
      (requireBoth network executionHandled commitmentValid).gates.toList.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simp [requireBoth]
  simpa [requireBoth, opValue] using graph _ member

/-- No independent source-success claim is copied from a proof label. The
single constrained success bit entails both subconditions and keeps all
original execution/hash gate equations. -/
theorem requireBoth_success (network : Network) (executionHandled commitmentValid : Nat)
    (wires : Nat → Bool)
    (graph : BooleanGraph (requireBoth network executionHandled commitmentValid) wires)
    (success : wires (network.inputCount + network.gates.size) = true) :
    BooleanGraph network wires ∧ wires executionHandled = true ∧ wires commitmentValid = true := by
  have conjunction := (requireBoth_value network executionHandled commitmentValid wires graph).symm.trans success
  have both : wires executionHandled = true ∧ wires commitmentValid = true := by
    simpa only [Bool.and_eq_true] using conjunction
  refine ⟨?_, both.1, both.2⟩
  apply graph_prefix network #[.and executionHandled commitmentValid] wires
  simpa only [requireBoth, BooleanGraph, Array.push_eq_append] using graph

/-- For an actual unrolled controller, execution output0 is its cumulative
handled bit; commitment output0 begins at execution.outputs.size. The caller
must construct the independently expected public success value as one. -/
def fromCandidate (execution : Network) (candidate : BendCommittedNetwork.Candidate) : Option Network :=
  if execution.outputs.isEmpty then none else
  if execution.outputs.size ≥ candidate.whole.outputs.size then none else
  let network := requireBoth candidate.whole
    (candidate.whole.outputs[0]?.getD 0)
    (candidate.whole.outputs[execution.outputs.size]?.getD 0)
  if network.valid then some network else none

#assert_axioms requireBoth_value
#assert_axioms requireBoth_success
end Minidregg.Compiler.BendCommittedRun
