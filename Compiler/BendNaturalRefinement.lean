/- Complete emitted arithmetic/source join. This consumes arbitrary proving
witnesses, actual selected world wrapper and exact Nat source types. No backend
integrity/input-range/authority theorem is fabricated from a source Book. -/
import Compiler.BendNaturalWorldSource

namespace Minidregg.Compiler.BendNaturalExpression
open Minidregg.Theory.BendTT Minidregg.Theory.BendLiveMachine
open BendSourceRepresentation
set_option autoImplicit false

/-- Arbitrary emitted wires force the exact bounded source output and semantic
count for the shared native affine pair. Observation data is supplied by the
current receiver and discarded affinely by this pure numeric method. -/
theorem descriptor_world_sound {n p : Nat} [Fact p.Prime]
    (book : Book) (entry : String) (expr : Expr n)
    (installed : Book.get book entry = some (worldDefinition entry expr))
    (natBinding : NatBookBinding book)
    (natAdd : Book.get book "Nat.add" = some natAddDef)
    (inputBits maxBits : Nat) (fits : inputBits ≤ maxBits)
    (fieldFits : 2 ^ maxBits ≤ p)
    (outputFits : expr.upper (fun _ => 2 ^ inputBits - 1) < 2 ^ maxBits)
    (wv : Nat → ZMod p)
    (holds : descriptorHolds (descriptor inputBits maxBits fits expr) wv)
    (observations : List Nat) :
    let asg : Index n maxBits → ZMod p := fun i => wv (wire i)
    let inputs := inputValues asg
    (∀ i, inputs i < 2 ^ inputBits) ∧
      (wv 0).val = expr.value inputs ∧
      Trace book (1 + expr.sourceCount inputs) (worldInvocation entry inputs observations)
        (natTerm (wv 0).val) ∧
      Typed book [] (natTerm (wv 0).val) (.Ref "Nat") := by
  let asg : Index n maxBits → ZMod p := fun i => wv (wire i)
  have accepted := (emit_accepts_iff wire wire_injective 0
    ((n + 1) + (n + 1) * maxBits) (fun i => (packed i).isLt) asg
      (constraints inputBits maxBits fits expr)).mp ⟨wv, fun _ => rfl, holds⟩
  obtain ⟨inputsBound, exactResult⟩ := constraints_integer_sound inputBits maxBits fits
    expr fieldFits outputFits asg accepted
  have outputWire : wire (n := n) (k := maxBits) (Sum.inl 0) = 0 := rfl
  change (∀ i, inputValues asg i < 2 ^ inputBits) ∧ (wv 0).val = expr.value (inputValues asg) ∧ _
  have exact : (wv 0).val = expr.value (inputValues asg) := by simpa [asg, outputWire] using exactResult
  refine ⟨inputsBound, exact, ?_, natTerm_typed book natBinding _⟩
  rw [exact]
  exact world_entry_trace book entry expr installed natAdd (inputValues asg) observations

/-- Source/circuit completeness is general over every admitted input; no honest
runtime graph or ciphertext output is assumed by this existential witness. -/
theorem source_descriptor_complete {n p : Nat} [Fact p.Prime]
    (book : Book) (entry : String) (expr : Expr n)
    (installed : Book.get book entry = some (worldDefinition entry expr))
    (natAdd : Book.get book "Nat.add" = some natAddDef)
    (inputBits maxBits : Nat) (fits : inputBits ≤ maxBits)
    (outputFits : expr.upper (fun _ => 2 ^ inputBits - 1) < 2 ^ maxBits)
    (inputs : Fin n → Nat) (bounded : ∀ i, inputs i < 2 ^ inputBits)
    (observations : List Nat) :
    Trace book (1 + expr.sourceCount inputs) (worldInvocation entry inputs observations)
      (natTerm (expr.value inputs)) ∧
    ∃ wv : Nat → ZMod p,
      (∀ i, wv (wire (k := maxBits) (Sum.inl i)) = (numbers inputs (expr.value inputs) i : ZMod p)) ∧
      descriptorHolds (descriptor inputBits maxBits fits expr) wv :=
  ⟨world_entry_trace book entry expr installed natAdd inputs observations,
    descriptor_complete inputBits maxBits fits expr outputFits inputs bounded⟩

#assert_axioms descriptor_world_sound
#assert_axioms source_descriptor_complete
end Minidregg.Compiler.BendNaturalExpression
