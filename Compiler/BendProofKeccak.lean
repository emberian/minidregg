import Compiler.ObliviousNetwork
import Theory.Sp800185Cshake256Core

/- Boolean Keccak-f[1600] construction over the existing shared AND/XOR DAG.
This is the concrete permutation required by the cSHAKE statement commitment,
not a new hash choice or a new evaluator. The twenty-four constants and rotation
schedule are read from the existing SP800185 specification. General circuit
refinement, byte framing/absorption and commitment admission remain open. -/
namespace Minidregg.Compiler.BendProofKeccak
open ObliviousNetwork
set_option autoImplicit false

abbrev Word := Array Nat
abbrev State := Array Word

def zeroWord (zero : Nat) : Word := Array.replicate 64 zero

def lane (state : State) (zero x y : Nat) : Word :=
  state.getD (x % 5 + 5 * (y % 5)) (zeroWord zero)

def xorWord (zero : Nat) (left right : Word) : Builder Word := do
  let mut output := #[]
  for bit in [:64] do
    output := output.push (← emit (.xor (left.getD bit zero) (right.getD bit zero)))
  return output

def andWord (zero : Nat) (left right : Word) : Builder Word := do
  let mut output := #[]
  for bit in [:64] do
    output := output.push (← emit (.and (left.getD bit zero) (right.getD bit zero)))
  return output

def notWord (zero one : Nat) (word : Word) : Builder Word := do
  let mut output := #[]
  for bit in [:64] do
    output := output.push (← emit (.xor (word.getD bit zero) one))
  return output

/-- Little-endian bit indexing: output bit i comes from input bit i-offset. -/
def rotateLeft (zero : Nat) (word : Word) (offset : Nat) : Word :=
  Array.ofFn fun bit : Fin 64 => word.getD ((bit.val + 64 - offset % 64) % 64) zero

def theta (zero : Nat) (state : State) : Builder State := do
  let mut columns := #[]
  for x in [:5] do
    let mut parity := zeroWord zero
    for y in [:5] do
      parity ← xorWord zero parity (lane state zero x y)
    columns := columns.push parity
  let mut deltas := #[]
  for x in [:5] do
    let previous := columns.getD ((x + 4) % 5) (zeroWord zero)
    let following := columns.getD ((x + 1) % 5) (zeroWord zero)
    deltas := deltas.push (← xorWord zero previous (rotateLeft zero following 1))
  let mut output := #[]
  for index in [:25] do
    output := output.push (← xorWord zero (lane state zero (index % 5) (index / 5))
      (deltas.getD (index % 5) (zeroWord zero)))
  return output

/-- Rotation and lane permutation only rewire existing gates. -/
def rhoPi (zero : Nat) (state : State) : State :=
  (List.range 25).foldl (fun output source =>
    let x := source % 5
    let y := source / 5
    let target := y + 5 * ((2 * x + 3 * y) % 5)
    output.setIfInBounds target
      (rotateLeft zero (lane state zero x y) (Sp800185Cshake256.rotationOffset x y)))
    (Array.replicate 25 (zeroWord zero))

def chi (zero one : Nat) (state : State) : Builder State := do
  let mut output := #[]
  for index in [:25] do
    let x := index % 5
    let y := index / 5
    let complement ← notWord zero one (lane state zero (x + 1) y)
    let product ← andWord zero complement (lane state zero (x + 2) y)
    output := output.push (← xorWord zero (lane state zero x y) product)
  return output

def iota (zero one : Nat) (state : State) (constant : Sp800185Cshake256.Lane) : Builder State := do
  let mut first := #[]
  for bit in [:64] do
    let input := (lane state zero 0 0).getD bit zero
    let output ← if constant.getLsbD bit then emit (.xor input one) else pure input
    first := first.push output
  return state.setIfInBounds 0 first

def round (zero one : Nat) (state : State) (constant : Sp800185Cshake256.Lane) : Builder State := do
  let mixed ← theta zero state
  let nonlinear ← chi zero one (rhoPi zero mixed)
  iota zero one nonlinear constant

/-- A reusable subgraph constructor. Its caller owns the canonical state-wire
shape and original-input binding; no result bit is supplied as an oracle. -/
def permutation (zero one : Nat) (state : State) : Builder State :=
  Sp800185Cshake256.roundConstants.foldlM (round zero one) state

/-- Standalone public permutation graph, input/output bits lane-major then
little-endian within each 64-bit lane. All hash framing remains a separate
consumer; publishing this graph does not admit a cSHAKE commitment proof. -/
def network : Network := Id.run do
  let initial : State := Array.ofFn fun lane : Fin 25 =>
    Array.ofFn fun bit : Fin 64 => lane.val * 64 + bit.val
  let build : Builder State := do
    let zero ← emit (.constant false)
    let one ← emit (.constant true)
    permutation zero one initial
  let (result, graph) := build.run { inputCount := 1600 }
  return { graph with outputs := result.flatten }

end Minidregg.Compiler.BendProofKeccak
