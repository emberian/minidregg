import Compiler.ObliviousWordSemantics

namespace Minidregg.Compiler.ObliviousVectorSemantics
open ObliviousNetwork ObliviousWords ObliviousWordSemantics
set_option autoImplicit false

/-- A constructor contract relative to the original input network. It must hold
at every extension, so sequential vector construction cannot invalidate an
operand or earlier result. The exact Builder, not a replacement evaluator,
appears in the contract. -/
def Produces (base : Network) (input : Array Bool) (builder : Builder Nat)
    (value : Bool) : Prop :=
  ∀ current, Extension base current →
    let result := builder.run current
    Extension current result.2 ∧
    result.1 < result.2.inputCount + result.2.gates.size ∧
    read result.2 input result.1 = value

/-- General actual Vector.ofFnM composition. Every returned coordinate retains
its meaning after all later gates have been emitted. -/
theorem ofFnM_produces {width : Nat} (base : Network) (input : Array Bool)
    (shape : input.size = base.inputCount) (builders : Fin width → Builder Nat)
    (values : Fin width → Bool)
    (each : ∀ bit, Produces base input (builders bit) (values bit))
    (current : Network) (extended : Extension base current) :
    let result := (Vector.ofFnM builders).run current
    Extension current result.2 ∧
    ∀ bit : Fin width,
      result.1[bit] < result.2.inputCount + result.2.gates.size ∧
      read result.2 input result.1[bit] = values bit := by
  induction width with
  | zero =>
      simp only [Vector.ofFnM_zero]
      exact ⟨Extension.refl current, fun bit => Fin.elim0 bit⟩
  | succ width ih =>
      let initialPart := (Vector.ofFnM (fun bit : Fin width => builders bit.castSucc)).run current
      have prefixFacts := ih (fun bit => builders bit.castSucc) (fun bit => values bit.castSucc)
        (fun bit => each bit.castSucc)
      have allPrefix : Extension base initialPart.2 := extended.trans prefixFacts.1
      let final := (builders (Fin.last width)).run initialPart.2
      have finalFacts := each (Fin.last width) initialPart.2 allPrefix
      rw [Vector.ofFnM_succ]
      change Extension current final.2 ∧
        ∀ bit : Fin (width + 1),
          (initialPart.1.push final.1)[bit] < final.2.inputCount + final.2.gates.size ∧
          read final.2 input (initialPart.1.push final.1)[bit] = values bit
      refine ⟨prefixFacts.1.trans finalFacts.1, ?_⟩
      intro bit
      refine Fin.lastCases ?_ (fun previous => ?_) bit
      · simpa using finalFacts.2
      · have old := prefixFacts.2 previous
        have keep := finalFacts.1.read input initialPart.1[previous]
          (shape.trans allPrefix.inputs.symm) old.1
        simpa using And.intro (finalFacts.1.bound old.1) (keep.trans old.2)

/-- Whole-word mux semantics for all widths and all prior well-addressed wires.
The public identical-wire shortcut and every actual emitted mux gate are both
included. This is the word primitive used by state rollback and selection. -/
theorem mux_produces {width : Nat} (network : Network) (input : Array Bool)
    (shape : input.size = network.inputCount) (selector : Nat) (yes no : Word width)
    (selectorBound : selector < network.inputCount + network.gates.size)
    (yesBound : ∀ bit : Fin width, yes[bit] < network.inputCount + network.gates.size)
    (noBound : ∀ bit : Fin width, no[bit] < network.inputCount + network.gates.size) :
    let result := (mux selector yes no).run network
    Extension network result.2 ∧
    ∀ bit : Fin width,
      result.1[bit] < result.2.inputCount + result.2.gates.size ∧
      read result.2 input result.1[bit] =
        if read network input selector then read network input yes[bit] else read network input no[bit] := by
  rw [mux_definition]
  apply ofFnM_produces network input shape _ _ _ network (Extension.refl network)
  intro bit current extension
  refine ⟨muxBit_extension current selector yes[bit] no[bit],
    muxBit_bound current selector yes[bit] no[bit] (extension.bound (yesBound bit)), ?_⟩
  have result := muxBit_value current input selector yes[bit] no[bit]
    (shape.trans extension.inputs.symm) (extension.bound selectorBound)
    (extension.bound (yesBound bit)) (extension.bound (noBound bit))
  rw [extension.read input selector shape selectorBound,
    extension.read input yes[bit] shape (yesBound bit),
    extension.read input no[bit] shape (noBound bit)] at result
  exact result

#assert_axioms ofFnM_produces
#assert_axioms mux_produces
end Minidregg.Compiler.ObliviousVectorSemantics
