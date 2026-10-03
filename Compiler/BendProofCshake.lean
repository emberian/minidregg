import Compiler.BendProofKeccak

/- Exact cSHAKE framing and sponge graph over the shared Boolean gates.
Message length and customization are PUBLIC constructor parameters. A private
profile must provide a fixed-capacity canonical encoding before using this
primitive; specializing it by a secret's actual length would disclose that
length. General permutation/sponge refinement remains a separate obligation. -/
namespace Minidregg.Compiler.BendProofCshake
open ObliviousNetwork BendProofKeccak
set_option autoImplicit false

abbrev ByteWires := Array Nat

def constantByte (zero one : Nat) (byte : UInt8) : ByteWires :=
  Array.ofFn fun bit : Fin 8 => if byte.toNat.testBit bit.val then one else zero

def messageWires (count : Nat) : Array ByteWires :=
  (Array.range count).map fun byte => Array.ofFn fun bit : Fin 8 => byte * 8 + bit.val

def framedWires (zero one : Nat) (customization : List UInt8) (count : Nat) : Array ByteWires :=
  let customizationWires := if customization = [] then #[] else
    (Sp800185Cshake256.customizationPrefix customization).toArray.map (constantByte zero one)
  let message := customizationWires ++ messageWires count
  let suffix : UInt8 := if customization = [] then 0x1f else 0x04
  let padding := Sp800185Cshake256.rateBytes - message.size % Sp800185Cshake256.rateBytes
  if padding = 1 then message.push (constantByte zero one (suffix ^^^ 128))
  else message ++ #[constantByte zero one suffix] ++
    Array.replicate (padding - 2) (constantByte zero one 0) ++ #[constantByte zero one 128]

def xorBlock (zero : Nat) (state : State) (bytes : Array ByteWires) (block : Nat) : Builder State := do
  let mut output := #[]
  for index in [:25] do
    let old := state.getD index (zeroWord zero)
    if index < Sp800185Cshake256.rateLanes then
      let word : Word := Array.ofFn fun bit : Fin 64 =>
        (bytes.getD (block * 136 + index * 8 + bit.val / 8) (Array.replicate 8 zero)).getD
          (bit.val % 8) zero
      output := output.push (← xorWord zero old word)
    else output := output.push old
  return output

def network (customization : List UInt8) (messageBytes : Nat) : Network := Id.run do
  let build : Builder State := do
    let zero ← emit (.constant false)
    let one ← emit (.constant true)
    let framed := framedWires zero one customization messageBytes
    let mut state := Array.replicate 25 (zeroWord zero)
    for block in [:framed.size / Sp800185Cshake256.rateBytes] do
      state ← xorBlock zero state framed block
      state ← permutation zero one state
    return state
  let (state, graph) := build.run { inputCount := messageBytes * 8 }
  return { graph with outputs := state.flatten.extract 0 256 }

def bits (bytes : List UInt8) : Array Bool :=
  (bytes.toArray.map fun byte => Array.ofFn fun bit : Fin 8 => byte.toNat.testBit bit.val).flatten

end Minidregg.Compiler.BendProofCshake
