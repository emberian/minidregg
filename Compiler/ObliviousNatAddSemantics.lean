/- General actual SSA-wire refinement for the shared full-adder Builder.
The width-two receiving corollary evaluates the actual additionNetwork, not a
second arithmetic interpreter. Wider ripple/source induction remains open. -/
import Compiler.ObliviousNatAdd
import Compiler.ObliviousMuxSemantics

namespace Minidregg.Compiler.ObliviousNatAddSemantics
open ObliviousNetwork ObliviousBuilderSemantics ObliviousMuxSemantics ObliviousNatAdd
set_option autoImplicit false

theorem fullAdder_run (network : Network) (left right carry : Nat) :
    let next := network.inputCount + network.gates.size
    (fullAdder left right carry).run network =
      (⟨next+1,next+4⟩, {network with gates:=
        ((((network.gates.push (.xor left right)).push (.xor next carry)).push
          (.and left right)).push (.and next carry)).push (.xor (next+2) (next+3))}) := by
  simp [fullAdder, ObliviousNetwork.emit, Array.size_push, Nat.add_assoc]
  rfl

/-- Every admitted existing wire has its value lifted through the exact five
emitted gates. The proof is uniform in graph, input array and wire addresses. -/
theorem fullAdder_value (network : Network) (inputs : Array Bool)
    (left right carry : Nat) (shape : inputs.size = network.inputCount)
    (leftBound : left < network.inputCount + network.gates.size)
    (rightBound : right < network.inputCount + network.gates.size)
    (carryBound : carry < network.inputCount + network.gates.size) :
    let emitted := (fullAdder left right carry).run network
    let before := network.evaluateWires inputs
    (emitted.2.evaluateWires inputs)[emitted.1.sum]?.getD false =
      sumBit (before[left]?.getD false) (before[right]?.getD false) (before[carry]?.getD false) ∧
    (emitted.2.evaluateWires inputs)[emitted.1.carry]?.getD false =
      carryBit (before[left]?.getD false) (before[right]?.getD false) (before[carry]?.getD false) := by
  let next := network.inputCount + network.gates.size
  have size : (network.evaluateWires inputs).size = next := by
    rw [evaluateWires_size, shape]
  rw [fullAdder_run]
  dsimp only
  simp only [Network.evaluateWires, Array.foldl_push]
  change
    (gateStep (gateStep (gateStep (gateStep (gateStep (network.evaluateWires inputs)
      (.xor left right)) (.xor next carry)) (.and left right)) (.and next carry))
      (.xor (next+2) (next+3)))[next+1]?.getD false =
      sumBit ((network.evaluateWires inputs)[left]?.getD false)
        ((network.evaluateWires inputs)[right]?.getD false) ((network.evaluateWires inputs)[carry]?.getD false) ∧
    (gateStep (gateStep (gateStep (gateStep (gateStep (network.evaluateWires inputs)
      (.xor left right)) (.xor next carry)) (.and left right)) (.and next carry))
      (.xor (next+2) (next+3)))[next+4]?.getD false =
      carryBit ((network.evaluateWires inputs)[left]?.getD false)
        ((network.evaluateWires inputs)[right]?.getD false) ((network.evaluateWires inputs)[carry]?.getD false)
  have leftDifferent0 : left ≠ next := by dsimp [next]; omega
  have leftDifferent1 : left ≠ next + 1 := by dsimp [next]; omega
  have leftDifferent2 : left ≠ next + 2 := by dsimp [next]; omega
  have leftDifferent3 : left ≠ next + 3 := by dsimp [next]; omega
  have leftDifferent4 : left ≠ next + 4 := by dsimp [next]; omega
  have rightDifferent0 : right ≠ next := by dsimp [next]; omega
  have rightDifferent1 : right ≠ next + 1 := by dsimp [next]; omega
  have rightDifferent2 : right ≠ next + 2 := by dsimp [next]; omega
  have rightDifferent3 : right ≠ next + 3 := by dsimp [next]; omega
  have rightDifferent4 : right ≠ next + 4 := by dsimp [next]; omega
  have carryDifferent0 : carry ≠ next := by dsimp [next]; omega
  have carryDifferent1 : carry ≠ next + 1 := by dsimp [next]; omega
  have carryDifferent2 : carry ≠ next + 2 := by dsimp [next]; omega
  have carryDifferent3 : carry ≠ next + 3 := by dsimp [next]; omega
  have carryDifferent4 : carry ≠ next + 4 := by dsimp [next]; omega
  simp [gateStep, Array.getElem?_push, Array.size_push, size, sumBit, carryBit,
    Nat.add_assoc, leftDifferent0, leftDifferent1, leftDifferent2, leftDifferent3, leftDifferent4, rightDifferent0, rightDifferent1, rightDifferent2, rightDifferent3, rightDifferent4, carryDifferent0, carryDifferent1, carryDifferent2, carryDifferent3, carryDifferent4]

/-- Exact arithmetic of the ACTUAL emitted sum/carry wires, for every admitted
network/input and all three incoming Boolean wire values. -/
theorem fullAdder_emitted_integer (network : Network) (inputs : Array Bool)
    (left right carry : Nat) (shape : inputs.size = network.inputCount)
    (leftBound : left < network.inputCount + network.gates.size)
    (rightBound : right < network.inputCount + network.gates.size)
    (carryBound : carry < network.inputCount + network.gates.size) :
    let emitted := (fullAdder left right carry).run network
    let before := network.evaluateWires inputs
    (before[left]?.getD false).toNat + (before[right]?.getD false).toNat +
      (before[carry]?.getD false).toNat =
      ((emitted.2.evaluateWires inputs)[emitted.1.sum]?.getD false).toNat +
        2 * ((emitted.2.evaluateWires inputs)[emitted.1.carry]?.getD false).toNat := by
  have values := fullAdder_value network inputs left right carry shape leftBound rightBound carryBound
  dsimp only at values ⊢
  rw [values.1,values.2]
  exact fullAdder_integer _ _ _

/-- Kernel equality to the actual generated SSA graph. This binds the finite
receiving theorem and emitted Plan to the generic construction, not metadata. -/
theorem additionNetwork2_shape : additionNetwork 2 =
    ⟨4,#[.constant false,.xor 0 2,.xor 5 4,.and 0 2,.and 5 4,.xor 7 8,
      .xor 1 3,.xor 10 9,.and 1 3,.and 10 9,.xor 12 13],#[6,11,14]⟩ := by
  simp [additionNetwork, ripple, List.finRange_succ, ObliviousWords.inputs,
    fullAdder, ObliviousNetwork.emit]
  rfl

/-- Universal four-private-bit receiving fact for the compiled width-two
primitive, including its explicit overflow bit. This is not one closed test. -/
theorem additionNetwork2_value (a0 a1 b0 b1 : Bool) :
    (additionNetwork 2).evaluate #[a0,a1,b0,b1] = some #[
      sumBit a0 b0 false,
      sumBit a1 b1 (carryBit a0 b0 false),
      carryBit a1 b1 (carryBit a0 b0 false)] := by
  rw [additionNetwork2_shape]
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;>
    simp [Network.evaluate, Network.valid, Op.fits, Network.evaluateWires, sumBit, carryBit]

theorem additionNetwork2_integer (a0 a1 b0 b1 : Bool) :
    let result := ((additionNetwork 2).evaluate #[a0,a1,b0,b1]).getD #[]
    (result[0]?.getD false).toNat + 2*(result[1]?.getD false).toNat +
      4*(result[2]?.getD false).toNat =
      a0.toNat + 2*a1.toNat + b0.toNat + 2*b1.toNat := by
  rw [additionNetwork2_value]
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> decide

#assert_axioms fullAdder_run
#assert_axioms fullAdder_value
#assert_axioms fullAdder_emitted_integer
#assert_axioms additionNetwork2_shape
#assert_axioms additionNetwork2_value
#assert_axioms additionNetwork2_integer
end Minidregg.Compiler.ObliviousNatAddSemantics
