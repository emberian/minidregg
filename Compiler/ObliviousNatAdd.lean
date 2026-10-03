/- Reusable exact-width arithmetic construction on the existing shared Op DAG.
Public widths and source expressions determine the graph. Secret inputs never
branch construction. General Boolean full-adder arithmetic is proved below;
whole Builder evaluation/source refinement is an explicit receiving obligation,
not inferred from this truth-table theorem or clear examples. -/
import Compiler.ObliviousWords
import Compiler.BendNaturalCompiler

namespace Minidregg.Compiler.ObliviousNatAdd
open ObliviousNetwork ObliviousWords
open BendNaturalExpression (Expr Plan)
set_option autoImplicit false

structure AddedBit where
  sum : Nat
  carry : Nat
  deriving DecidableEq, Repr

/-- Two AND and three XOR gates. Carry terms are disjoint, so the last XOR
is their exact disjunction, including the all-three-inputs true case. -/
def fullAdder (left right carry : Nat) : Builder AddedBit := do
  let different ← emit (.xor left right)
  let sum ← emit (.xor different carry)
  let both ← emit (.and left right)
  let passing ← emit (.and different carry)
  let carry ← emit (.xor both passing)
  pure ⟨sum,carry⟩

def sumBit (left right carry : Bool) : Bool := xor (xor left right) carry
def carryBit (left right carry : Bool) : Bool :=
  xor (left && right) ((xor left right) && carry)

/-- Arbitrary bits, not a named closed test instance. This is the integer law
that a proved Builder simulation must lift over the actual emitted wires. -/
theorem fullAdder_integer (left right carry : Bool) :
    left.toNat + right.toNat + carry.toNat =
      (sumBit left right carry).toNat + 2 * (carryBit left right carry).toNat := by
  cases left <;> cases right <;> cases carry <;> decide

/-- Explicit carry plus little-endian sum; no silent wrapping. The caller
supplies an already emitted public zero wire in the SAME Network. -/
def ripple {width : Nat} (zero : Nat) (left right : Word width) :
    Builder (Nat × Word width) := do
  let mut carry := zero
  let mut out := Vector.replicate width zero
  for bit in List.finRange width do
    let added ← fullAdder left[bit] right[bit] carry
    out := out.set bit.val added.sum bit.isLt
    carry := added.carry
  pure (carry,out)

structure Lowered (width : Nat) where
  result : Word width
  /-- Every addition retains its high carry. The admitted monotone source
  domain must prove these wires false before interpreting a width-k result. -/
  overflow : Array Nat

/-- SAME reusable source Expr as AIR/FHE. The whole-source upper bound forbids
truncation; actual graph simulation and carry-false refinement remain required. -/
def lower {n width : Nat} (zero : Nat) (inputs : Fin n → Word width) :
    Expr n → Builder (Lowered width)
  | .input index => pure ⟨inputs index,#[]⟩
  | .literal value => do
      let bits ← constant width value
      pure ⟨bits,#[]⟩
  | .add left right => do
      let a ← lower zero inputs left
      let b ← lower zero inputs right
      let (carry,sum) ← ripple zero a.result b.result
      pure ⟨sum,(a.overflow ++ b.overflow).push carry⟩

/-- Input groups use the public source order, little endian, with zero padding
from admitted input width into output width. The returned outputs are result
bits first, then every carry witness. Input-bit protocol qualification is owned
by the backend and must be composed/reserved before any secret input is read. -/
def network {n : Nat} (plan : Plan n) : Network :=
  let build : Builder Unit := do
    let zero ← emit (.constant false)
    let arguments : Fin n → Word plan.outputBits := fun index =>
      Vector.ofFn fun bit => if bit.val < plan.inputBits then
        index.val * plan.inputBits + bit.val else zero
    let lowered ← lower zero arguments plan.expression
    modify fun graph => {graph with outputs := lowered.result.toArray ++ lowered.overflow}
  (build.run {inputCount := n * plan.inputBits}).2

/-- Full-width primitive conformance graph: two input words and sum bits with
carry appended as the highest bit. This does not replace source Plan binding. -/
def additionNetwork (width : Nat) : Network :=
  let build : Builder Unit := do
    let zero ← emit (.constant false)
    let (carry,sum) ← ripple zero (inputs width 0) (inputs width width)
    modify fun graph => {graph with outputs := sum.toArray.push carry}
  (build.run {inputCount := 2 * width}).2

/-- Construction admission reuses the same source range/count profile. This
alone certifies no whole-network semantics; backend registration needs that
remaining proof and an exact source/Plan/Network byte binding. -/
def compile {n : Nat} (plan : Plan n) : Option Network :=
  if BendNaturalExpression.profileAccepted (p := 2013265921) plan then
    some (network plan) else none

theorem compile_exact {n : Nat} {plan : Plan n} {graph : Network}
    (accepted : compile plan = some graph) :
    BendNaturalExpression.profileAccepted (p := 2013265921) plan = true ∧
      graph = network plan := by
  unfold compile at accepted
  split at accepted
  · rename_i admitted
    exact ⟨admitted,(Option.some.inj accepted).symm⟩
  · contradiction

#assert_axioms compile_exact
#assert_axioms fullAdder_integer
end Minidregg.Compiler.ObliviousNatAdd
