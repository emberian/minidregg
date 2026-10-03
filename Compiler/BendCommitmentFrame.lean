import Compiler.BendCommitmentReduction
import Compiler.BendProofCshakeBounded
import Compiler.ObliviousUnroll

/- Concrete canonical commitment preimage wiring. Context is public under the
existing two disclosure policies. Salt, payload and length are private inputs.
The payload wires can be shared with the execution/codec producer; no host hash
or claimed digest is introduced as a witness oracle. General framer/cSHAKE
refinement is still open; the exact byte equation below is unconditional. -/
namespace Minidregg.Compiler.BendCommitmentFrame
open Minidregg.Theory Tower256ConcreteBackend BendProofProjection
open ObliviousNetwork BendProofKeccak BendProofCshake BendProofCshakeBounded
set_option autoImplicit false

def frameBytes (context : Context) (coins payload : List UInt8) : List UInt8 :=
  contextStream.encode context ++ StreamCodec.nat.encode coins.length ++ coins ++
    StreamCodec.nat.encode payload.length ++ payload

theorem frameBytes_exact (context : Context) (coins payload : List UInt8) :
    frameBytes context coins payload = BendCommitmentReduction.preimage context coins payload := by
  simp [frameBytes, BendCommitmentReduction.preimage, BendCommitmentReduction.preimageCodec,
    StreamCodec.product, bytesStream, List.append_assoc]

/-- Public maximum, accounting for the exact base-255 length codec. -/
def frameCapacity (publicContext : List UInt8) (capacity : Nat) : Nat :=
  ((List.range (capacity + 1)).map fun length =>
    publicContext.length + (StreamCodec.nat.encode 32).length + 32 +
      (StreamCodec.nat.encode length).length + length).foldl max 0

/-- Layout: 32 salt bytes, capacity payload bytes, capacity+1 one-hot length
bits. Output is framed bytes followed by one-hot framed length. -/
def frameNetwork (publicContext : List UInt8) (capacity : Nat) : Network := Id.run do
  let build : Builder (Array Nat) := do
    let z ← ObliviousNetwork.emit (.constant false)
    let one ← ObliviousNetwork.emit (.constant true)
    let maxBytes := frameCapacity publicContext capacity
    let salt := messageWires 32
    let payload := (messageWires capacity).map (fun byte => byte.map (· + 32 * 8))
    let lengthWire := fun length => (32 + capacity) * 8 + length
    let mut seen := z
    let mut repeated := z
    for length in [:capacity + 1] do
      repeated ← disjoin repeated (← ObliviousNetwork.emit (.and seen (lengthWire length)))
      seen ← disjoin seen (lengthWire length)
    let selectorValid ← ObliviousNetwork.emit (.and seen (← ObliviousNetwork.emit (.xor repeated one)))
    let mut framed := Array.replicate maxBytes (Array.replicate 8 z)
    let mut lengths := Array.replicate (maxBytes + 1) z
    for length in [:capacity + 1] do
      let prefixBytes := publicContext ++ StreamCodec.nat.encode 32
      let candidate := prefixBytes.toArray.map (constantByte z one) ++ salt ++
        (StreamCodec.nat.encode length).toArray.map (constantByte z one) ++
        payload.extract 0 length
      lengths := lengths.setIfInBounds candidate.size
        (← disjoin (lengths.getD candidate.size z) (lengthWire length))
      for index in [:candidate.size] do
        let mut byte := #[]
        for bit in [:8] do
          byte := byte.push (← emitMux (lengthWire length)
            ((candidate.getD index (Array.replicate 8 z)).getD bit z)
            ((framed.getD index (Array.replicate 8 z)).getD bit z))
        framed := framed.setIfInBounds index byte
    return #[selectorValid] ++ framed.flatten ++ lengths
  let (outputs, graph) := build.run { inputCount := (32 + capacity) * 8 + capacity + 1 }
  return { graph with outputs := outputs }

/-- Actual structural gate embedding, sharing every framer output wire with
its matching hash input. The output validity bit conjoins the original selector check and the hash
selector check INSIDE the graph. No many-hot framing shortcut is admitted. -/
def network (domain : String) (context : Context) (capacity : Nat) : Network :=
  let publicContext := contextStream.encode context
  let framed := frameNetwork publicContext capacity
  let hash := networkPublicPrefix domain.toUTF8.toList (frameCapacity publicContext capacity)
  let placement : ObliviousUnroll.Placement :=
    ⟨framed.outputs.extract 1 framed.outputs.size, framed.inputCount + framed.gates.size⟩
  let rename := placement.wire hash.inputCount
  let copied := framed.gates ++ hash.gates.map (ObliviousUnroll.mapOp rename)
  let valid := framed.inputCount + copied.size
  { framed with
    gates := copied.push (.and (framed.outputs[0]?.getD 0) (rename (hash.outputs[0]?.getD 0)))
    outputs := #[valid] ++ (hash.outputs.extract 1 hash.outputs.size).map rename }

#assert_axioms frameBytes_exact
end Minidregg.Compiler.BendCommitmentFrame
