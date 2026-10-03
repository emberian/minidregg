import Compiler.BendCommitmentFrame
import Compiler.ObliviousEmbedFast
import Compiler.BendTraceDirect
import Compiler.BendTraceSound

/- Exact shared-wire composition of an execution graph with a canonical-frame
commitment graph. Payload selectors are public wiring, not payload values.
No caller-provided hash/output witness can bypass either copied gate relation.
The payload-wire producer must still denote the actual admitted canonical
input/output codec; this module does not equate raw machine bits with bytes. -/
namespace Minidregg.Compiler.BendCommittedNetwork
open ObliviousNetwork ObliviousUnroll
open BendProofProjection
set_option autoImplicit false

structure Candidate where
  whole : Network
  execution : Placement
  commitment : Placement
  deriving Repr

def buildFrom (execution commitment : Network)
    (capacity : Nat) (payloadWires : Array Nat) : Candidate := Id.run do
  let extra := 32 * 8 + capacity + 1
  let wholeInputs := execution.inputCount + extra
  let executionPlacement : Placement := ⟨Array.range execution.inputCount, wholeInputs⟩
  let renameExecution := executionPlacement.wire execution.inputCount
  let executionGates := execution.gates.map (mapOp renameExecution)
  let salt := (Array.range (32 * 8)).map (· + execution.inputCount)
  let length := (Array.range (capacity + 1)).map (· + execution.inputCount + 32 * 8)
  let commitmentPlacement : Placement :=
    ⟨salt ++ payloadWires.map renameExecution ++ length, wholeInputs + executionGates.size⟩
  let renameCommitment := commitmentPlacement.wire commitment.inputCount
  return {
    whole :=
      { inputCount := wholeInputs
        gates := executionGates ++ commitment.gates.map (mapOp renameCommitment)
        outputs := execution.outputs.map renameExecution ++ commitment.outputs.map renameCommitment }
    execution := executionPlacement
    commitment := commitmentPlacement }

def build (execution : Network) (domain : String) (context : Context)
    (capacity : Nat) (payloadWires : Array Nat) : Candidate :=
  buildFrom execution (BendCommitmentFrame.network domain context capacity) capacity payloadWires

/-- Exact executable alias map: payload inputs are renamed execution wires,
with no intervening independently assignable copy or digest label. -/
theorem build_payload_aliases (execution : Network) (domain : String) (context : Context)
    (capacity : Nat) (payloadWires : Array Nat) :
    (build execution domain context capacity payloadWires).commitment.inputWires =
      (Array.range (32 * 8)).map (· + execution.inputCount) ++
      payloadWires.map ((build execution domain context capacity payloadWires).execution.wire execution.inputCount) ++
      (Array.range (capacity + 1)).map (· + execution.inputCount + 32 * 8) := by rfl

structure Prepared (execution commitment : Network) where
  candidate : Candidate
  valid : candidate.whole.valid = true
  executionEmbedded : candidate.execution.Embedded execution candidate.whole
  commitmentEmbedded : candidate.commitment.Embedded commitment candidate.whole

/-- The actual public graph and structural embeddings are checked before any
private proof witness is accepted. Bounds and byte width fail closed. -/
def prepare (execution : Network) (domain : String) (context : Context)
    (capacity : Nat) (payloadWires : Array Nat) :
    Option (Prepared execution (BendCommitmentFrame.network domain context capacity)) := do
  if payloadWires.size != capacity * 8 then none else do
  if !payloadWires.all (fun wire => wire < execution.inputCount + execution.gates.size) then none else do
  let commitment := BendCommitmentFrame.network domain context capacity
  let candidate := buildFrom execution commitment capacity payloadWires
  if valid : candidate.whole.valid = true then
    if executionChecked : candidate.execution.fastCheck execution candidate.whole = true then
      if commitmentChecked : candidate.commitment.fastCheck commitment candidate.whole = true then
        some ⟨candidate, valid, (placement_fastCheck _ _ _).mp executionChecked,
          (placement_fastCheck _ _ _).mp commitmentChecked⟩
      else none
    else none
  else none

/-- An arbitrary whole-graph satisfying assignment simultaneously satisfies
both actual producer graphs. Their payload inputs literally share the selected
execution wires; they are not independent witness copies with matching labels. -/
theorem Prepared.restricts {execution commitment : Network}
    (prepared : Prepared execution commitment) (wires : Nat → Bool)
    (satisfied : BendTraceConstraints.BooleanGraph prepared.candidate.whole wires) :
    BendTraceConstraints.BooleanGraph execution
      (fun i => wires (prepared.candidate.execution.wire execution.inputCount i)) ∧
    BendTraceConstraints.BooleanGraph commitment
      (fun i => wires (prepared.candidate.commitment.wire commitment.inputCount i)) :=
  ⟨embedded_graph _ _ _ prepared.executionEmbedded wires satisfied,
    embedded_graph _ _ _ prepared.commitmentEmbedded wires satisfied⟩

/-- The actual direct AIR of the composed graph forces BOTH subrelations
for arbitrary field assignments. The result is independent of honest witness
construction. A PCS theorem is still required to get this premise from Rust
proof acceptance; a hash refinement is still needed to identify the hash graph
with the byte-level commitment semantics. -/
theorem Prepared.direct_forces {F : Type} [Field F] {execution commitment : Network}
    (prepared : Prepared execution commitment) (pins : List Nat)
    (assignment publicInputs : Nat → F)
    (accepted : (BendTraceDirect.lower
      (BendTraceConstraints.constraints prepared.candidate.whole)
      (prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size) pins).Holds
        assignment publicInputs) :
    ∃ wires : Nat → Bool,
      (∀ index < prepared.candidate.whole.inputCount + prepared.candidate.whole.gates.size,
        BendTraceConstraints.bit (F := F) (wires index) = assignment index) ∧
      BendTraceConstraints.BooleanGraph execution
        (fun i => wires (prepared.candidate.execution.wire execution.inputCount i)) ∧
      BendTraceConstraints.BooleanGraph commitment
        (fun i => wires (prepared.candidate.commitment.wire commitment.inputCount i)) ∧
      (∀ entry ∈ pins.zipIdx, assignment entry.1 = publicInputs entry.2) := by
  have relation := BendTraceDirect.network_forces prepared.candidate.whole pins
    assignment publicInputs accepted
  obtain ⟨wires, graph, same⟩ := BendTraceSound.holds_extract prepared.candidate.whole
    prepared.valid assignment relation.1
  have both := prepared.restricts wires graph
  exact ⟨wires, same, both.1, both.2, relation.2⟩

#assert_axioms build_payload_aliases
#assert_axioms Prepared.direct_forces
#assert_axioms Prepared.restricts
end Minidregg.Compiler.BendCommittedNetwork
