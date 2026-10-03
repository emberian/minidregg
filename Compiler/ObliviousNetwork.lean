/- Executable AND/XOR DAG serialization for the bounded heap read/write circuit.
Each equality selector is emitted once, then shared by every payload bit.
This backend-independent module does not itself lower a language controller
or implement an MPC protocol. Nock compatibility and Bend use the same DAG. -/
import Compiler.ObliviousGate

namespace Minidregg.Compiler.ObliviousNetwork
open ObliviousGate
set_option autoImplicit false

inductive Op where
  | constant (value : Bool)
  | xor (left right : Nat)
  | and (left right : Nat)
  deriving DecidableEq, Repr

structure Network where
  inputCount : Nat
  gates : Array Op := #[]
  outputs : Array Nat := #[]
  deriving DecidableEq, Repr

def Op.fits (bound : Nat) : Op → Bool
  | .constant _ => true
  | .xor left right | .and left right => left < bound && right < bound

def Network.valid (network : Network) : Bool :=
  (network.gates.toList.zipIdx).all
    (fun row => row.1.fits (network.inputCount + row.2)) &&
  network.outputs.all (· < network.inputCount + network.gates.size)

/-- The literal existing SSA fold, exposed for graph/trace correspondence.
This raw fold does not validate input shape or graph bounds; evaluate does.
It is a clear conformance interpreter, not an MPC backend. -/
def Network.evaluateWires (network : Network) (inputs : Array Bool) : Array Bool :=
  network.gates.foldl (fun wires op =>
    wires.push (match op with
      | .constant value => value
      | .xor left right => xor (wires[left]?.getD false) (wires[right]?.getD false)
      | .and left right => (wires[left]?.getD false) && (wires[right]?.getD false))) inputs

/-- Clear gate interpreter for conformance checks. A backend consumes the same
public Op DAG using authenticated shared wires; this interpreter is not MPC. -/
def Network.evaluate (network : Network) (inputs : Array Bool) : Option (Array Bool) := do
  if inputs.size != network.inputCount || !network.valid then none else do
    let wires := network.evaluateWires inputs
    some (network.outputs.map fun wire => wires[wire]?.getD false)

abbrev Builder := StateM Network

def emit (op : Op) : Builder Nat := do
  let network ← get
  let wire := network.inputCount + network.gates.size
  set { network with gates := network.gates.push op }
  pure wire

def emitMux (selector yes no : Nat) : Builder Nat := do
  let difference ← emit (.xor yes no)
  let selected ← emit (.and selector difference)
  emit (.xor no selected)

def emitOr (left right : Nat) : Builder Nat := do
  let sum ← emit (.xor left right)
  let product ← emit (.and left right)
  emit (.xor sum product)

/-- Pointer wires occupy [0,pointerBits). Constants and row labels are public. -/
def emitEqual (pointerBits index trueWire : Nat) : Builder Nat := do
  let mut equal := trueWire
  for bit in [:pointerBits] do
    let matched ← if index.testBit bit then pure bit else emit (.xor bit trueWire)
    equal ← emit (.and equal matched)
  pure equal

def selectors (shape : HeapShape) (trueWire : Nat) : Builder (Array Nat) := do
  let mut result := #[]
  for index in [:shape.slots] do
    result := result.push (← emitEqual shape.pointerBits index trueWire)
  pure result

/-- Inputs: pointer bits, then all fixed-width heap rows. Outputs: valid-address
bit, then one fixed-width row (all zero when invalid). Equality selectors
are pairwise exclusive because Shape.fits excludes pointer aliasing. XOR of
masked rows therefore replaces a serial mux chain: multiplicative depth is
pointerBits + 1, independent of heap slots. Validity uses the same exclusive
selector XOR and must be checked before interpreting payload as a node. -/
def readNetwork (shape : HeapShape) : Network := Id.run do
  let width := shape.rowBits
  let build : Builder Unit := do
    let zero ← emit (.constant false)
    let one ← emit (.constant true)
    let selected ← selectors shape one
    let mut valid := zero
    for row in [:shape.slots] do
      valid ← emit (.xor valid (selected[row]?.getD zero))
    let mut outputs := #[valid]
    for bit in [:width] do
      let mut result := zero
      for row in [:shape.slots] do
        let masked ← emit (.and (selected[row]?.getD zero)
          (shape.pointerBits + row * width + bit))
        result ← emit (.xor result masked)
      outputs := outputs.push result
    modify fun network => { network with outputs := outputs }
  return (build.run { inputCount := shape.pointerBits + shape.slots * width }).2

/-- Inputs: pointer, every current row, then one replacement row. Outputs:
valid-address bit and every resulting row. Invalid addresses preserve every
row; they do not accidentally overwrite row zero. -/
def writeNetwork (shape : HeapShape) : Network := Id.run do
  let width := shape.rowBits
  let replacement := shape.pointerBits + shape.slots * width
  let build : Builder Unit := do
    let zero ← emit (.constant false)
    let one ← emit (.constant true)
    let selected ← selectors shape one
    let mut valid := zero
    let mut outputs := #[]
    for row in [:shape.slots] do
      valid ← emit (.xor valid (selected[row]?.getD zero))
      for bit in [:width] do
        outputs := outputs.push (← emitMux (selected[row]?.getD zero)
          (replacement + bit) (shape.pointerBits + row * width + bit))
    modify fun network => { network with outputs := #[valid] ++ outputs }
  return (build.run { inputCount := replacement + width }).2

/-- Native increment primitive: fixed-width little-endian atom input; outputs
carry/overflow first, then every sum bit. Overflow cannot wrap to a valid noun. -/
def incrementNetwork (width : Nat) : Network := Id.run do
  let build : Builder Unit := do
    let mut carry ← emit (.constant true)
    let mut outputs := #[]
    for bit in [:width] do
      let sum ← emit (.xor bit carry)
      carry ← emit (.and bit carry)
      outputs := outputs.push sum
    modify fun network => { network with outputs := #[carry] ++ outputs }
  return (build.run { inputCount := width }).2

structure Census where
  inputs : Nat
  outputs : Nat
  gates : Nat
  ands : Nat
  xors : Nat
  /-- All Boolean gates counted as one local layer, including XOR gates. -/
  depth : Nat
  /-- Multiplicative depth: XOR is local and does not add an AND layer. -/
  andDepth : Nat
  deriving DecidableEq, Repr

def Network.census (network : Network) : Census := Id.run do
  let mut levels := Array.replicate network.inputCount 0
  let mut products := Array.replicate network.inputCount 0
  let mut ands := 0
  let mut xors := 0
  for gate in network.gates do
    match gate with
    | .constant _ =>
      levels := levels.push 0
      products := products.push 0
    | .and left right =>
      ands := ands + 1
      products := products.push (1 + max (products[left]?.getD 0) (products[right]?.getD 0))
      levels := levels.push (1 + max (levels[left]?.getD 0) (levels[right]?.getD 0))
    | .xor left right =>
      xors := xors + 1
      products := products.push (max (products[left]?.getD 0) (products[right]?.getD 0))
      levels := levels.push (1 + max (levels[left]?.getD 0) (levels[right]?.getD 0))
  let depth := network.outputs.foldl (fun depth wire => max depth (levels[wire]?.getD 0)) 0
  let andDepth := network.outputs.foldl (fun depth wire => max depth (products[wire]?.getD 0)) 0
  return ⟨network.inputCount, network.outputs.size, network.gates.size, ands, xors, depth, andDepth⟩

end Minidregg.Compiler.ObliviousNetwork
