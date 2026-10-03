/- A proof-friendly, public-shape ripple construction using the SAME shared
fullAdder/Op Builder. It retains every high carry, supports arbitrary width,
and never inspects secret Boolean values while generating a graph.
This additive construction is a continuation of the generic source lowering;
it does not yet replace the previously qualified Vector loop. -/
import Compiler.ObliviousNatAddSemantics

namespace Minidregg.Compiler.ObliviousNatRipple
open ObliviousNetwork ObliviousBuilderSemantics ObliviousNatAdd
open ObliviousNatAddSemantics
set_option autoImplicit false

/-- Public ordered pairs are little endian. Recursive construction makes the
shared wire-preservation induction explicit rather than enumerating widths. -/
def emitPairs (carry : Nat) : List (Nat × Nat) → Builder (Nat × List Nat)
  | [] => pure (carry,[])
  | (left,right)::tail => do
      let first ← fullAdder left right carry
      let rest ← emitPairs first.carry tail
      pure (rest.1,first.sum::rest.2)

theorem emitPairs_nil (network : Network) (carry : Nat) :
    (emitPairs carry []).run network = ((carry,[]),network) := rfl

theorem emitPairs_cons (network : Network) (carry left right : Nat)
    (tail : List (Nat × Nat)) :
    (emitPairs carry ((left,right)::tail)).run network =
      let first := (fullAdder left right carry).run network
      let rest := (emitPairs first.1.carry tail).run first.2
      ((rest.1.1,first.1.sum::rest.1.2),rest.2) := rfl

/-- Actual gate counts are width-dependent physical work, not source fuel. -/
theorem emitPairs_shape (pairs : List (Nat × Nat)) (network : Network)
    (carry : Nat) :
    let emitted := (emitPairs carry pairs).run network
    emitted.2.inputCount = network.inputCount ∧
    emitted.2.gates.size = network.gates.size + 5*pairs.length ∧
    emitted.1.2.length = pairs.length := by
  induction pairs generalizing network carry with
  | nil => simp [emitPairs_nil]
  | cons pair tail ih =>
      rcases pair with ⟨left,right⟩
      rw [emitPairs_cons]
      dsimp only
      have first := fullAdder_shape network left right carry
      have rest := ih ((fullAdder left right carry).run network).2
        ((fullAdder left right carry).run network).1.carry
      dsimp only at first rest
      simp only [List.length_cons]
      exact ⟨rest.1.trans first.1, by omega, by omega⟩

/-- Existing wire values survive the complete arbitrary-width construction,
using the same original input array throughout. No bit value is inspected by
this proof's construction; the induction follows public pair structure. -/
theorem emitPairs_preserves (pairs : List (Nat × Nat)) (network : Network)
    (carry : Nat) (inputs : Array Bool) (index : Nat)
    (earlier : index < (network.evaluateWires inputs).size) :
    let emitted := (emitPairs carry pairs).run network
    (emitted.2.evaluateWires inputs)[index]? =
      (network.evaluateWires inputs)[index]? := by
  induction pairs generalizing network carry with
  | nil => simp [emitPairs_nil]
  | cons pair tail ih =>
      rcases pair with ⟨left,right⟩
      rw [emitPairs_cons]
      dsimp only
      have firstShape := fullAdder_shape network left right carry
      dsimp only at firstShape
      have remains : index <
          (((fullAdder left right carry).run network).2.evaluateWires inputs).size := by
        rw [evaluateWires_size] at earlier ⊢
        rw [firstShape.2.1]
        omega
      exact (ih ((fullAdder left right carry).run network).2
        ((fullAdder left right carry).run network).1.carry remains).trans
        (fullAdder_preserves network inputs left right carry index earlier)

/-- Little-endian exact integer observation of actual wire values. -/
def wireValue (network : Network) (inputs : Array Bool) : List Nat → Nat
  | [] => 0
  | wire::tail => ((network.evaluateWires inputs)[wire]?.getD false).toNat +
      2 * wireValue network inputs tail

theorem wireValue_preserves (pairs : List (Nat × Nat)) (network : Network)
    (carry : Nat) (inputs : Array Bool) (wires : List Nat)
    (bounds : ∀ wire ∈ wires, wire < (network.evaluateWires inputs).size) :
    let emitted := (emitPairs carry pairs).run network
    wireValue emitted.2 inputs wires = wireValue network inputs wires := by
  induction wires with
  | nil => rfl
  | cons wire tail ih =>
      dsimp only [wireValue]
      rw [emitPairs_preserves pairs network carry inputs wire (bounds wire (by simp))]
      rw [ih (fun index member => bounds index (by simp [member]))]

/-- A width-generic actual graph producer. The first half of inputs is left,
second half right; sums are little endian followed by the final high carry. -/
def additionNetwork (width : Nat) : Network :=
  let build : Builder Unit := do
    let zero ← ObliviousNetwork.emit (.constant false)
    let (carry,sums) ← emitPairs zero ((List.range width).map fun bit => (bit,width+bit))
    modify fun network => {network with outputs := (sums ++ [carry]).toArray}
  (build.run {inputCount := 2*width}).2

#assert_axioms emitPairs_nil
#assert_axioms emitPairs_cons
#assert_axioms emitPairs_shape
#assert_axioms emitPairs_preserves
#assert_axioms wireValue_preserves
end Minidregg.Compiler.ObliviousNatRipple
