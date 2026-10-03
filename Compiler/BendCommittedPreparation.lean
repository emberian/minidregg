import Compiler.BendCommittedNetwork

/- The checked producer returns the actual generated candidate. This prevents
consumers from confusing an arbitrary structural certificate with the concrete
execution/payload aliasing that prepare constructed. -/
namespace Minidregg.Compiler.BendCommittedPreparation
open ObliviousNetwork BendCommittedNetwork BendProofProjection
set_option autoImplicit false

theorem prepare_exact (execution : Network) (domain : String) (context : Context)
    (capacity : Nat) (payloadWires : Array Nat)
    (prepared : Prepared execution (BendCommitmentFrame.network domain context capacity))
    (accepted : prepare execution domain context capacity payloadWires = some prepared) :
    prepared.candidate = build execution domain context capacity payloadWires := by
  unfold prepare at accepted
  split at accepted <;> simp_all [build]
  rcases accepted with ⟨_, _, _, _, equality⟩
  exact congrArg (fun value => value.candidate) equality.symm

/-- The actual checked producer's hash payload inputs alias the actual selected
execution wires. No independently assigned copied payload is introduced. -/
theorem prepare_payload_aliases (execution : Network) (domain : String) (context : Context)
    (capacity : Nat) (payloadWires : Array Nat)
    (prepared : Prepared execution (BendCommitmentFrame.network domain context capacity))
    (accepted : prepare execution domain context capacity payloadWires = some prepared) :
    prepared.candidate.commitment.inputWires =
      (Array.range (32 * 8)).map (· + execution.inputCount) ++
      payloadWires.map (prepared.candidate.execution.wire execution.inputCount) ++
      (Array.range (capacity + 1)).map (· + execution.inputCount + 32 * 8) := by
  rw [prepare_exact execution domain context capacity payloadWires prepared accepted]
  exact build_payload_aliases execution domain context capacity payloadWires

#assert_axioms prepare_exact
#assert_axioms prepare_payload_aliases
end Minidregg.Compiler.BendCommittedPreparation
