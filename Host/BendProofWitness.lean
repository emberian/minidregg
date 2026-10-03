import Compiler.BendTracePublicPins
import Compiler.BendTraceConstraints

/- Executable witness production from the ACTUAL emitted arithmetic gates.
Natural residues avoid the quadratic Function.update chain used by the old
small fixture. This is a prover helper; arbitrary-witness soundness does not
trust this helper, and every produced zero root is checked before release. -/
namespace Minidregg.Host.BendProofWitness
open Compiler
set_option autoImplicit false

def modulus : Nat := 2013265921

def read (values : Array Nat) : DWire BabyBear → Except String Nat
  | .cnst value => .ok value.val
  | .wire index => match values[index]? with
    | some value => .ok value
    | none => .error "emitted wire index outside witness"

def produce (descriptor : ConstraintDescriptor BabyBear) (initial : Array Nat) : Except String (Array Nat) := do
  if initial.size > descriptor.nWires then throw "initial wire count exceeds descriptor"
  if initial.any (fun value => value ≥ modulus) then throw "noncanonical initial residue"
  let mut values := initial ++ Array.replicate (descriptor.nWires - initial.size) 0
  for gate in descriptor.gates do
    if gate.out < initial.size || gate.out ≥ values.size then throw "invalid emitted auxiliary address"
    let left ← read values gate.a
    let right ← read values gate.b
    let value := match gate.op with
      | .add => (left + right) % modulus
      | .mul => (left * right) % modulus
    values := values.setIfInBounds gate.out value
  for root in descriptor.zeros do
    if (← read values root) != 0 then throw "emitted arithmetic root does not vanish"
  return values

def csv (values : Array Nat) : String :=
  String.intercalate "," (values.toList.map toString) ++ "\n"

end Minidregg.Host.BendProofWitness
