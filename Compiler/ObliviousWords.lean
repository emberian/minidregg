/- Composable fixed-width wire operations used by the Bend controller.
Construction branches only on public widths/indices. All secret choices become
gates in the shared Op DAG. These executable builders need their general
evaluation refinement; no whole-controller correctness is claimed here. -/
import Compiler.ObliviousNetwork
import Init.Data.Vector.OfFn

namespace Minidregg.Compiler.ObliviousWords
open ObliviousNetwork
set_option autoImplicit false

abbrev Word (width : Nat) := Vector Nat width

def inputs (width base : Nat) : Word width := Vector.ofFn fun bit => base + bit.val

def constant (width value : Nat) : Builder (Word width) :=
  Vector.ofFnM fun bit => emit (.constant (value.testBit bit.val))

def notBit (one bit : Nat) : Builder Nat := emit (.xor one bit)

def equal {width : Nat} (one : Nat) (left right : Word width) : Builder Nat := do
  let mut result := one
  for bit in List.finRange width do
    let difference ← emit (.xor left[bit] right[bit])
    let same ← notBit one difference
    result ← emit (.and result same)
  pure result

def equalConstant {width : Nat} (one : Nat) (word : Word width) (value : Nat) :
    Builder Nat := do
  let mut result := one
  for bit in List.finRange width do
    let same ← if value.testBit bit.val then pure word[bit] else notBit one word[bit]
    result ← emit (.and result same)
  pure result

def mux {width : Nat} (selector : Nat) (yes no : Word width) : Builder (Word width) :=
  Vector.ofFnM fun bit =>
    if yes[bit] == no[bit] then pure yes[bit] else emitMux selector yes[bit] no[bit]

/-- Ripple unsigned comparison. The two borrow terms are disjoint, so XOR
implements their disjunction without an extra nonlinear gate. -/
def lessThan {width : Nat} (zero one : Nat) (left right : Word width) : Builder Nat := do
  let mut borrow := zero
  for bit in List.finRange width do
    let different ← emit (.xor left[bit] right[bit])
    let same ← notBit one different
    let leftZero ← notBit one left[bit]
    let starts ← emit (.and leftZero right[bit])
    let continues ← emit (.and same borrow)
    borrow ← emit (.xor starts continues)
  pure borrow

/-- Carry and full-width sum; overflow is explicit. -/
def increment {width : Nat} (one : Nat) (word : Word width) :
    Builder (Nat × Word width) := do
  let mut carry := one
  let mut result := word
  for bit in List.finRange width do
    let sum ← emit (.xor word[bit] carry)
    carry ← emit (.and word[bit] carry)
    result := result.set bit.val sum bit.isLt
  pure (carry, result)

/-- Borrow and full-width predecessor; underflow is explicit. -/
def decrement {width : Nat} (one : Nat) (word : Word width) :
    Builder (Nat × Word width) := do
  let mut borrow := one
  let mut result := word
  for bit in List.finRange width do
    let difference ← emit (.xor word[bit] borrow)
    let zero ← notBit one word[bit]
    borrow ← emit (.and zero borrow)
    result := result.set bit.val difference bit.isLt
  pure (borrow, result)

/-- Secret-address read visits every fixed physical row. Address validity is a
separate output. Public non-aliasing of row indices is a compiler obligation. -/
def readRows {slots width addressWidth : Nat} (zero one : Nat)
    (address : Word addressWidth) (rows : Vector (Word width) slots) :
    Builder (Nat × Word width) := do
  let selected ← Vector.ofFnM fun row : Fin slots =>
    equalConstant one address row.val
  let mut valid := zero
  for row in List.finRange slots do
    valid ← emit (.xor valid selected[row])
  let result ← Vector.ofFnM fun bit : Fin width => do
    let mut value := zero
    for row in List.finRange slots do
      let masked ← emit (.and selected[row] rows[row][bit])
      value ← emit (.xor value masked)
    pure value
  pure (valid, result)

/-- Gated write still visits every row. No invalid address aliases row zero;
a disabled write preserves all rows through actual mux gates. -/
def writeRows {slots width addressWidth : Nat} (one enable : Nat)
    (address : Word addressWidth) (replacement : Word width)
    (rows : Vector (Word width) slots) : Builder (Vector (Word width) slots) :=
  Vector.ofFnM fun row => do
    let selected ← equalConstant one address row.val
    let active ← emit (.and enable selected)
    mux active replacement rows[row]

def constantRows (slots width : Nat) (value : Fin slots → Nat) :
    Builder (Vector (Word width) slots) :=
  Vector.ofFnM fun row => constant width (value row)

end Minidregg.Compiler.ObliviousWords
