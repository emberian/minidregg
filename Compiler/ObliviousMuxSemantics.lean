import Compiler.ObliviousBuilderSemantics

/- The actual shared Builder's three-gate multiplexer. These laws retain the
same original input array through all tentative gates, so a whole-state mux
can restore the original raw state rather than an already-modified trial. -/
namespace Minidregg.Compiler.ObliviousMuxSemantics
open ObliviousNetwork ObliviousBuilderSemantics
set_option autoImplicit false

theorem mux_boolean (selector yes no : Bool) :
    xor no (selector && xor yes no) = if selector then yes else no := by
  cases selector <;> cases yes <;> cases no <;> rfl

theorem emitMux_run (network : Network) (selector yes no : Nat) :
    let next := network.inputCount + network.gates.size
    (emitMux selector yes no).run network =
      (next + 2, { network with gates :=
        ((network.gates.push (.xor yes no)).push (.and selector next)).push (.xor no (next + 1)) }) := by
  simp [emitMux, emit, Array.size_push, Nat.add_assoc]
  rfl

theorem push_preserves (network : Network) (inputs : Array Bool) (op : Op)
    (index : Nat) (earlier : index < (network.evaluateWires inputs).size) :
    (({ network with gates := network.gates.push op }).evaluateWires inputs)[index]? =
      (network.evaluateWires inputs)[index]? := by
  rw [evaluateWires_push]
  simp only [gateStep, Array.getElem?_push, Nat.ne_of_lt earlier, if_false]

/-- The actual emitted mux returns the selected OLD wire. All three source
wire addresses are required to precede the emitted gates. -/
theorem emitMux_value (network : Network) (inputs : Array Bool)
    (selector yes no : Nat) (shape : inputs.size = network.inputCount)
    (selectorBound : selector < network.inputCount + network.gates.size)
    (yesBound : yes < network.inputCount + network.gates.size)
    (noBound : no < network.inputCount + network.gates.size) :
    let emitted := (emitMux selector yes no).run network
    let wires := network.evaluateWires inputs
    (emitted.2.evaluateWires inputs)[emitted.1]?.getD false =
      if wires[selector]?.getD false then wires[yes]?.getD false else wires[no]?.getD false := by
  let next := network.inputCount + network.gates.size
  have size : (network.evaluateWires inputs).size = next := by
    rw [evaluateWires_size, shape]
  have selectorDifferent : selector ≠ next := Nat.ne_of_lt selectorBound
  have yesDifferent : yes ≠ next := Nat.ne_of_lt yesBound
  have noDifferent : no ≠ next := Nat.ne_of_lt noBound
  have noDifferentNext : no ≠ next + 1 := by omega
  have differentNext : next ≠ next + 1 := by omega
  rw [emitMux_run]
  dsimp only
  simp only [Network.evaluateWires, Array.foldl_push]
  change (gateStep (gateStep (gateStep (network.evaluateWires inputs) (.xor yes no))
    (.and selector next)) (.xor no (next + 1)))[next + 2]?.getD false = _
  simpa only [gateStep, Array.getElem?_push, Array.size_push, size, Nat.add_assoc, selectorDifferent,
    yesDifferent, noDifferent, noDifferentNext, differentNext, if_false, if_true,
    Option.getD_some, ↓reduceIte] using
    (mux_boolean ((network.evaluateWires inputs)[selector]?.getD false)
      ((network.evaluateWires inputs)[yes]?.getD false)
      ((network.evaluateWires inputs)[no]?.getD false))

/-- No previously existing wire is modified by the emitted mux. -/
theorem emitMux_preserves (network : Network) (inputs : Array Bool)
    (selector yes no index : Nat) (earlier : index < (network.evaluateWires inputs).size) :
    let emitted := (emitMux selector yes no).run network
    (emitted.2.evaluateWires inputs)[index]? = (network.evaluateWires inputs)[index]? := by
  let next := network.inputCount + network.gates.size
  let first := { network with gates := network.gates.push (.xor yes no) }
  let second := { first with gates := first.gates.push (.and selector next) }
  have oldBound : index < inputs.size + network.gates.size := by
    simpa only [evaluateWires_size] using earlier
  have firstBound : index < (first.evaluateWires inputs).size := by
    simp only [first, evaluateWires_size, Array.size_push]
    omega
  have secondBound : index < (second.evaluateWires inputs).size := by
    simp only [second, first, evaluateWires_size, Array.size_push]
    omega
  have keepFirst := push_preserves network inputs (.xor yes no) index earlier
  have keepSecond := push_preserves first inputs (.and selector next) index firstBound
  have keepThird := push_preserves second inputs (.xor no (next + 1)) index secondBound
  rw [emitMux_run]
  exact keepThird.trans (keepSecond.trans keepFirst)

#assert_axioms mux_boolean
#assert_axioms emitMux_run
#assert_axioms push_preserves
#assert_axioms emitMux_value
#assert_axioms emitMux_preserves
end Minidregg.Compiler.ObliviousMuxSemantics
