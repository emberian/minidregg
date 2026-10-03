/- Fixed public wire layout for the actual Bend closure controller.
SourceSteps is retained as a PRIVATE bounded word, avoiding reliance on the
not-yet-proved meter-erasure optimization. No public fee uses this word.
This is the shared input/output layout for controller blocks, not a second
evaluator. Complete decoder/simulation qualification remains explicit. -/
import Compiler.ObliviousWords
import Theory.BendClosureMachine

namespace Minidregg.Compiler.BendObliviousState
open ObliviousNetwork ObliviousWords
set_option autoImplicit false

structure Shape where
  heapSlots : Nat
  frameSlots : Nat
  argumentSlots : Nat
  wordBits : Nat
  sourceCountBits : Nat

def Shape.valid (shape : Shape) : Bool :=
  shape.heapSlots ≤ 2 ^ shape.wordBits &&
  shape.frameSlots < 2 ^ shape.wordBits &&
  shape.argumentSlots < 2 ^ shape.wordBits &&
  0 < shape.sourceCountBits

def rowBits (shape : Shape) : Nat := 5 + 2 * shape.wordBits
def frameBits (shape : Shape) : Nat := 5 + 2 * shape.wordBits
def argumentBits (shape : Shape) : Nat := 2 + shape.wordBits

/-- Control tags exactly follow the canonical continuation codec:
0 evaluate,1 lookup/evaluate,2 lookup/walk,3 returned,4 apply,5 unspine,
6 walk,7 classify,8 complete,9 refused,10 reverse,11 install. -/
structure Control (shape : Shape) where
  tag : Word 4
  quantity : Word 2
  failure : Word 5
  a : Word shape.wordBits
  b : Word shape.wordBits
  c : Word shape.wordBits
  d : Word shape.wordBits
  e : Word shape.wordBits
  firstLength : Word shape.wordBits
  secondLength : Word shape.wordBits
  first : Vector (Word (argumentBits shape)) shape.argumentSlots
  second : Vector (Word (argumentBits shape)) shape.argumentSlots

structure State (shape : Shape) where
  heap : Vector (Word (rowBits shape)) shape.heapSlots
  /-- Extra bit represents a completely full 2^wordBits heap. -/
  used : Word (shape.wordBits + 1)
  data : Word shape.heapSlots
  stack : Vector (Word (frameBits shape)) shape.frameSlots
  stackLength : Word shape.wordBits
  control : Control shape
  sourceSteps : Word shape.sourceCountBits

abbrev Layout := StateM Nat

def take (width : Nat) : Layout (Word width) := do
  let start ← get
  set (start + width)
  pure (inputs width start)

def controlInputs (shape : Shape) : Layout (Control shape) := do
  let tag ← take 4
  let quantity ← take 2
  let failure ← take 5
  let a ← take shape.wordBits
  let b ← take shape.wordBits
  let c ← take shape.wordBits
  let d ← take shape.wordBits
  let e ← take shape.wordBits
  let firstLength ← take shape.wordBits
  let secondLength ← take shape.wordBits
  let first ← Vector.ofFnM fun _ : Fin shape.argumentSlots => take (argumentBits shape)
  let second ← Vector.ofFnM fun _ : Fin shape.argumentSlots => take (argumentBits shape)
  pure ⟨tag, quantity, failure, a, b, c, d, e, firstLength, secondLength, first, second⟩

def stateInputs (shape : Shape) : Layout (State shape) := do
  let heap ← Vector.ofFnM fun _ : Fin shape.heapSlots => take (rowBits shape)
  let used ← take (shape.wordBits + 1)
  let data ← take shape.heapSlots
  let stack ← Vector.ofFnM fun _ : Fin shape.frameSlots => take (frameBits shape)
  let stackLength ← take shape.wordBits
  let control ← controlInputs shape
  let sourceSteps ← take shape.sourceCountBits
  pure ⟨heap, used, data, stack, stackLength, control, sourceSteps⟩

def flatten {slots width : Nat} (rows : Vector (Word width) slots) : Array Nat :=
  rows.toArray.foldl (fun output row => output ++ row.toArray) #[]

def Control.outputs {shape : Shape} (control : Control shape) : Array Nat :=
  control.tag.toArray ++ control.quantity.toArray ++ control.failure.toArray ++
  control.a.toArray ++ control.b.toArray ++ control.c.toArray ++
  control.d.toArray ++ control.e.toArray ++
  control.firstLength.toArray ++ control.secondLength.toArray ++
  flatten control.first ++ flatten control.second

def State.outputs {shape : Shape} (state : State shape) : Array Nat :=
  flatten state.heap ++ state.used.toArray ++ state.data.toArray ++
  flatten state.stack ++ state.stackLength.toArray ++ state.control.outputs ++
  state.sourceSteps.toArray

def stateWidth (shape : Shape) : Nat :=
  shape.heapSlots * rowBits shape + (shape.wordBits + 1) + shape.heapSlots +
  shape.frameSlots * frameBits shape + shape.wordBits +
  11 + 7 * shape.wordBits + 2 * shape.argumentSlots * argumentBits shape +
  shape.sourceCountBits

/-- Every block selects whole fixed-shape records with gates. -/
def muxControl {shape : Shape} (selector : Nat) (yes no : Control shape) :
    Builder (Control shape) := do
  pure ⟨← mux selector yes.tag no.tag, ← mux selector yes.quantity no.quantity,
    ← mux selector yes.failure no.failure,
    ← mux selector yes.a no.a, ← mux selector yes.b no.b,
    ← mux selector yes.c no.c, ← mux selector yes.d no.d,
    ← mux selector yes.e no.e,
    ← mux selector yes.firstLength no.firstLength,
    ← mux selector yes.secondLength no.secondLength,
    ← Vector.ofFnM (fun row => mux selector yes.first[row] no.first[row]),
    ← Vector.ofFnM (fun row => mux selector yes.second[row] no.second[row])⟩

def muxState {shape : Shape} (selector : Nat) (yes no : State shape) :
    Builder (State shape) := do
  pure ⟨← Vector.ofFnM (fun row => mux selector yes.heap[row] no.heap[row]),
    ← mux selector yes.used no.used, ← mux selector yes.data no.data,
    ← Vector.ofFnM (fun row => mux selector yes.stack[row] no.stack[row]),
    ← mux selector yes.stackLength no.stackLength,
    ← muxControl selector yes.control no.control,
    ← mux selector yes.sourceSteps no.sourceSteps⟩

end Minidregg.Compiler.BendObliviousState
