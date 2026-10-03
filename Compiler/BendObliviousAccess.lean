/- Shared fixed-access operations for the actual controller blocks.
All addresses are wire words; all public tables/physical rows are visited.
Validity wires remain separate from zero-filled invalid-read payloads. -/
import Compiler.BendObliviousAdministrative

namespace Minidregg.Compiler.BendObliviousAccess
open ObliviousNetwork ObliviousWords BendObliviousState
set_option autoImplicit false

def slice {width : Nat} (zero : Nat) (word : Word width) (start count : Nat) : Word count :=
  Vector.ofFn fun bit => word.toArray[start + bit.val]?.getD zero

def extend {width : Nat} (zero : Nat) (word : Word width) : Word (width+1) :=
  Vector.ofFn fun bit => word.toArray[bit.val]?.getD zero

structure RowView (shape : Shape) where
  tag : Word 3
  quantity : Word 2
  first : Word shape.wordBits
  second : Word shape.wordBits

def viewRow {shape : Shape} (zero : Nat) (row : Word (rowBits shape)) : RowView shape :=
  ⟨slice zero row 0 3,slice zero row 3 2,
    slice zero row 5 shape.wordBits,slice zero row (5+shape.wordBits) shape.wordBits⟩

def readHeap {shape : Shape} (zero one : Nat) (state : State shape)
    (address : Word shape.wordBits) : Builder (Nat × RowView shape) := do
  let (physical, packed) ← readRows zero one address state.heap
  let live ← lessThan zero one (extend zero address) state.used
  let valid ← emit (.and physical live)
  pure (valid, viewRow zero packed)

def refused {shape : Shape} (state : State shape) (reason : Nat) : Builder (State shape) := do
  let tag ← constant 4 9
  let failure ← constant 5 reason
  pure {state with control := {state.control with tag,failure}}

def argument {shape : Shape} (zero : Nat) (quantity : Word 2)
    (pointer : Word shape.wordBits) : Word (argumentBits shape) :=
  Vector.ofFn fun bit =>
    if bit.val < 2 then quantity.toArray[bit.val]?.getD zero
    else pointer.toArray[bit.val-2]?.getD zero

end Minidregg.Compiler.BendObliviousAccess
