/- Actual wire-word construction semantics. The emitted mux and shared fold
are imported from their qualified producer proofs. No second evaluator and no
claimed output relation supplied by a caller. -/
import Compiler.ObliviousWords
import Compiler.ObliviousMuxSemantics

namespace Minidregg.Compiler.ObliviousWordSemantics
open ObliviousNetwork ObliviousWords ObliviousBuilderSemantics ObliviousMuxSemantics
set_option autoImplicit false

def read (network : Network) (inputs : Array Bool) (wire : Nat) : Bool :=
  (network.evaluateWires inputs)[wire]?.getD false

/-- Semantic extension used to transport already constructed wire words. It is
proved for actual emitters below; callers do not provide final output values. -/
structure Extension (first last : Network) : Prop where
  inputs : last.inputCount = first.inputCount
  size : first.gates.size ≤ last.gates.size
  keeps : ∀ (input : Array Bool) (wire : Nat),
    wire < (first.evaluateWires input).size →
      (last.evaluateWires input)[wire]? = (first.evaluateWires input)[wire]?

theorem Extension.refl (network : Network) : Extension network network :=
  ⟨rfl,Nat.le_refl _,fun _ _ _ => rfl⟩

theorem Extension.trans {first middle last : Network}
    (left : Extension first middle) (right : Extension middle last) :
    Extension first last := by
  refine ⟨right.inputs.trans left.inputs,Nat.le_trans left.size right.size,?_⟩
  intro input wire bound
  have middleBound : wire < (middle.evaluateWires input).size := by
    rw [evaluateWires_size] at bound ⊢
    have growth := left.size
    omega
  exact (right.keeps input wire middleBound).trans (left.keeps input wire bound)

theorem Extension.bound {first last : Network} (extension : Extension first last)
    {wire : Nat} (bound : wire < first.inputCount + first.gates.size) :
    wire < last.inputCount + last.gates.size := by
  rw [extension.inputs]
  exact Nat.lt_of_lt_of_le bound (Nat.add_le_add_left extension.size _)

theorem Extension.read {first last : Network} (extension : Extension first last)
    (input : Array Bool) (wire : Nat) (shape : input.size = first.inputCount)
    (bound : wire < first.inputCount + first.gates.size) :
    read last input wire = read first input wire := by
  have actual : wire < (first.evaluateWires input).size := by
    simpa only [evaluateWires_size,shape] using bound
  exact congrArg (fun value => value.getD false) (extension.keeps input wire actual)

/-- This is literally the per-coordinate branch used by Words.mux. Its branch
condition compares PUBLIC wire identifiers, never their private Boolean values. -/
def muxBit (selector yes no : Nat) : Builder Nat :=
  if yes == no then pure yes else emitMux selector yes no

theorem mux_definition {width : Nat} (selector : Nat) (yes no : Word width) :
    mux selector yes no = Vector.ofFnM (fun bit => muxBit selector yes[bit] no[bit]) := rfl

theorem emitMux_extension (network : Network) (selector yes no : Nat) :
    Extension network ((emitMux selector yes no).run network).2 := by
  rw [emitMux_run]
  refine ⟨rfl,by simp only [Array.size_push]; omega,?_⟩
  intro input wire bound
  simpa only [emitMux_run] using emitMux_preserves network input selector yes no wire bound

theorem muxBit_extension (network : Network) (selector yes no : Nat) :
    Extension network ((muxBit selector yes no).run network).2 := by
  by_cases same : yes = no
  · simpa [muxBit,same] using Extension.refl network
  · simpa [muxBit,same] using emitMux_extension network selector yes no

theorem muxBit_bound (network : Network) (selector yes no : Nat)
    (yesBound : yes < network.inputCount + network.gates.size) :
    let result := (muxBit selector yes no).run network
    result.1 < result.2.inputCount + result.2.gates.size := by
  by_cases same : yes = no
  · simpa [muxBit,same] using yesBound
  · simp [muxBit,same,emitMux_run] <;> omega

theorem muxBit_value (network : Network) (input : Array Bool) (selector yes no : Nat)
    (shape : input.size = network.inputCount)
    (selectorBound : selector < network.inputCount + network.gates.size)
    (yesBound : yes < network.inputCount + network.gates.size)
    (noBound : no < network.inputCount + network.gates.size) :
    let result := (muxBit selector yes no).run network
    read result.2 input result.1 =
      if read network input selector then read network input yes else read network input no := by
  by_cases same : yes = no
  · subst yes
    simp only [muxBit, beq_self_eq_true, ↓reduceIte]
    change read network input no = if read network input selector then read network input no else read network input no
    split <;> rfl
  · simpa [muxBit,same,read] using
      emitMux_value network input selector yes no shape selectorBound yesBound noBound

#assert_axioms Extension.refl
#assert_axioms Extension.trans
#assert_axioms Extension.bound
#assert_axioms Extension.read
#assert_axioms mux_definition
#assert_axioms emitMux_extension
#assert_axioms muxBit_extension
#assert_axioms muxBit_bound
#assert_axioms muxBit_value
end Minidregg.Compiler.ObliviousWordSemantics
