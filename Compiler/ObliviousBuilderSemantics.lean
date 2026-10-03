import Compiler.ObliviousNetwork
import Theory.AssertAxioms

/- Shared constructor laws for the EXISTING network fold. `gateStep` below is
literally its body, with evaluateWires_eq_fold proved by reflexivity. There is
no separate evaluator, compiler output oracle, or Bend simulation assumption. -/
namespace Minidregg.Compiler.ObliviousBuilderSemantics
open ObliviousNetwork
set_option autoImplicit false

def gateStep (wires : Array Bool) (op : Op) : Array Bool :=
  wires.push (match op with
    | .constant value => value
    | .xor left right => xor (wires[left]?.getD false) (wires[right]?.getD false)
    | .and left right => wires[left]?.getD false && wires[right]?.getD false)

theorem evaluateWires_eq_fold (network : Network) (inputs : Array Bool) :
    network.evaluateWires inputs = network.gates.foldl gateStep inputs := rfl

theorem evaluateWires_size (network : Network) (inputs : Array Bool) :
    (network.evaluateWires inputs).size = inputs.size + network.gates.size := by
  rw [evaluateWires_eq_fold]
  apply Array.foldl_induction (motive := fun count (wires : Array Bool) => wires.size = inputs.size + count)
  · simp
  · intro index wires size
    simp only [gateStep, Array.size_push, size]
    omega

/-- Appending gates never modifies earlier wire values, including original
inputs. This requires no validity premise because every step only pushes. -/
theorem inputs_preserved (network : Network) (inputs : Array Bool) :
    ∀ index < inputs.size, (network.evaluateWires inputs)[index]? = inputs[index]? := by
  have invariant : (network.evaluateWires inputs).size = inputs.size + network.gates.size ∧
      ∀ index < inputs.size, (network.evaluateWires inputs)[index]? = inputs[index]? := by
    rw [evaluateWires_eq_fold]
    apply Array.foldl_induction (motive := fun count (wires : Array Bool) =>
      wires.size = inputs.size + count ∧ ∀ index < inputs.size, wires[index]? = inputs[index]?)
    · exact ⟨by simp, fun _ _ => rfl⟩
    · intro position wires previous
      constructor
      · simp only [gateStep, Array.size_push, previous.1]
        omega
      · intro index earlier
        have different : index ≠ wires.size := by omega
        simpa only [gateStep, Array.getElem?_push, different, if_false] using previous.2 index earlier
  exact invariant.2

theorem evaluateWires_append (network : Network) (suffix : Array Op) (inputs : Array Bool) :
    ({ network with gates := network.gates ++ suffix }).evaluateWires inputs =
      suffix.foldl gateStep (network.evaluateWires inputs) := by
  simp only [evaluateWires_eq_fold, Array.foldl_append]

theorem append_preserves (network : Network) (suffix : Array Op) (inputs : Array Bool)
    (index : Nat) (earlier : index < (network.evaluateWires inputs).size) :
    (({ network with gates := network.gates ++ suffix }).evaluateWires inputs)[index]? =
      (network.evaluateWires inputs)[index]? := by
  have preserved := inputs_preserved ({ inputCount := 0, gates := suffix } : Network)
    (network.evaluateWires inputs) index earlier
  simpa only [evaluateWires_eq_fold, Array.foldl_append] using preserved

theorem evaluateWires_push (network : Network) (op : Op) (inputs : Array Bool) :
    ({ network with gates := network.gates.push op }).evaluateWires inputs =
      gateStep (network.evaluateWires inputs) op := by
  simp only [evaluateWires_eq_fold, Array.foldl_push]

theorem emit_run (network : Network) (op : Op) :
    (emit op).run network =
      (network.inputCount + network.gates.size,
        { network with gates := network.gates.push op }) := rfl

/-- The actual emitted SSA wire contains the actual operation on previous
wires. The original input shape fixes the wire address, not an oracle value. -/
theorem emit_value (network : Network) (inputs : Array Bool) (op : Op)
    (shape : inputs.size = network.inputCount) :
    let emitted := (emit op).run network
    let wires := network.evaluateWires inputs
    (emitted.2.evaluateWires inputs)[emitted.1]? =
      some (match op with
        | .constant value => value
        | .xor left right => xor (wires[left]?.getD false) (wires[right]?.getD false)
        | .and left right => wires[left]?.getD false && wires[right]?.getD false) := by
  rw [emit_run]
  dsimp only
  rw [evaluateWires_push]
  have address : network.inputCount + network.gates.size =
      (network.evaluateWires inputs).size := by rw [evaluateWires_size, shape]
  rw [address]
  simp only [gateStep, Array.getElem?_push_size]

#assert_axioms evaluateWires_eq_fold
#assert_axioms evaluateWires_size
#assert_axioms inputs_preserved
#assert_axioms evaluateWires_append
#assert_axioms append_preserves
#assert_axioms evaluateWires_push
#assert_axioms emit_run
#assert_axioms emit_value
end Minidregg.Compiler.ObliviousBuilderSemantics
