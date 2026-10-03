import Compiler.BendProofCshake

/- One PUBLIC capacity, one graph, SECRET one-hot message length. Outputs are
[valid-length] ++ digest. A consumer must constrain valid-length to true.
Unused payload bytes are ignored, not revealed or required to be public zero.
This removes the actual-length graph specialization of BendProofCshake.network.
General framing/permutation refinement and full backend hiding remain open. -/
namespace Minidregg.Compiler.BendProofCshakeBounded
open ObliviousNetwork BendProofKeccak BendProofCshake
set_option autoImplicit false

def disjoin (a b : Nat) : Builder Nat := do
  let parity ← emit (.xor a b)
  let both ← emit (.and a b)
  emit (.xor parity both)

def buildNetwork (publicPrefixConstants : Bool) (customization : List UInt8) (capacity : Nat) : Network := Id.run do
  let build : Builder (Array Nat) := do
    let z ← emit (.constant false)
    let one ← emit (.constant true)
    let lengthWire := fun length => capacity * 8 + length
    let mut seen := z
    let mut repeated := z
    for length in [:capacity + 1] do
      repeated ← disjoin repeated (← emit (.and seen (lengthWire length)))
      seen ← disjoin seen (lengthWire length)
    let valid ← emit (.and seen (← emit (.xor repeated one)))
    -- active[i] means i < the secret selected length.
    let mut active := Array.replicate capacity z
    let mut longer := z
    for reverseIndex in [:capacity] do
      let index := capacity - 1 - reverseIndex
      longer ← disjoin longer (lengthWire (index + 1))
      active := active.setIfInBounds index longer
    let prefixBytes := if customization = [] then #[] else
      (Sp800185Cshake256.customizationPrefix customization).toArray
    let mut framed := prefixBytes.map (constantByte z one)
    let suffix : UInt8 := if customization = [] then 0x1f else 0x04
    let blocks := capacity / 136 + 1
    let mut ends := #[]
    for block in [:blocks] do
      let mut isLast := z
      for offset in [:136] do
        let index := block * 136 + offset
        if index ≤ capacity then isLast ← disjoin isLast (lengthWire index)
      ends := ends.push isLast
      for offset in [:136] do
        let index := block * 136 + offset
        let atEnd := if index ≤ capacity then lengthWire index else z
        let mut byte := #[]
        for bit in [:8] do
          let mut value := z
          if index < capacity then value ← emit (.and (active.getD index z) (index * 8 + bit))
          if suffix.toNat.testBit bit then value ← emit (.xor value atEnd)
          if offset = 135 && bit = 7 then value ← emit (.xor value isLast)
          byte := byte.push value
        framed := framed.push byte
    -- Only public customization bytes are precomputed. The private sponge blocks
    -- still execute every Boolean gate, including secret-length selection.
    let prefixState := Sp800185Cshake256.absorbPadded prefixBytes.toList
    let mut state := if publicPrefixConstants then
      prefixState.map (fun word => Array.ofFn fun bit : Fin 64 =>
        if word.getLsbD bit.val then one else z)
      else Array.replicate 25 (zeroWord z)
    let mut selected := Array.replicate 256 z
    let prefixBlocks := prefixBytes.size / 136
    for block in [(if publicPrefixConstants then prefixBlocks else 0):prefixBlocks + blocks] do
      state ← xorBlock z state framed block
      state ← permutation z one state
      if block ≥ prefixBlocks then
        let choose := ends.getD (block - prefixBlocks) z
        let digest := state.flatten.extract 0 256
        let mut output := #[]
        for bit in [:256] do
          output := output.push (← emitMux choose (digest.getD bit z) (selected.getD bit z))
        selected := output
    return #[valid] ++ selected
  let (output, graph) := build.run { inputCount := capacity * 8 + capacity + 1 }
  return { graph with outputs := output }

/-- Full graph reference, including the public customization prefix. -/
def network := buildNetwork false

/-- Exact specification-derived public prefix constants. This reduces the
private graph by public-only permutation work; generic circuit refinement is
still an open proof obligation, not inferred from this optimization. -/
def networkPublicPrefix := buildNetwork true

def input (capacity : Nat) (payload : List UInt8) : Array Bool :=
  bits (payload ++ List.replicate (capacity - payload.length) 0) ++
    Array.ofFn (fun index : Fin (capacity + 1) => index.val == payload.length)
end Minidregg.Compiler.BendProofCshakeBounded
