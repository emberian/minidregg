/- Fixed Boolean gate circuits for the bounded Nock heap access layer.
These are executable AND/XOR circuit terms, not branches on a secret address.
The full instruction/continuation controller is still a separate lowering
obligation; these circuits alone do not constitute private Nock execution. -/
import Theory.BoundedNockMachine

namespace Minidregg.Compiler.BoundedNockCircuit
set_option autoImplicit false

inductive Gate where
  | input (index : Nat)
  | constant (value : Bool)
  | xor (left right : Gate)
  | and (left right : Gate)
  | select (selector yes no : Gate)
  deriving Repr

def evaluate (inputs : Nat → Bool) : Gate → Bool
  | .input index => inputs index
  | .constant value => value
  | .xor left right => xor (evaluate inputs left) (evaluate inputs right)
  | .and left right => evaluate inputs left && evaluate inputs right
  | .select selector yes no =>
      let s := evaluate inputs selector
      let y := evaluate inputs yes
      let n := evaluate inputs no
      xor n (s && xor y n)

/-- One nonlinear AND, two local XORs. Neither arm is selected by a host branch. -/
def mux (selector yes no : Gate) : Gate :=
  .select selector yes no

theorem evaluate_mux (inputs : Nat → Bool) (selector yes no : Gate) :
    evaluate inputs (mux selector yes no) =
      if evaluate inputs selector then evaluate inputs yes else evaluate inputs no := by
  simp only [mux, evaluate]
  cases evaluate inputs selector <;> cases evaluate inputs yes <;>
    cases evaluate inputs no <;> rfl

/-- Tree census counts all gates actually described by this executable term.
A select locally shares each of its three children, then emits 3 gates.
Shared subterms are counted repeatedly; DAG common-subexpression elimination
must provide its own census/equivalence before using a smaller number. -/
def andCount : Gate → Nat
  | .input _ | .constant _ => 0
  | .xor left right => andCount left + andCount right
  | .and left right => andCount left + andCount right + 1
  | .select selector yes no => andCount selector + andCount yes + andCount no + 1

def xorCount : Gate → Nat
  | .input _ | .constant _ => 0
  | .xor left right => xorCount left + xorCount right + 1
  | .and left right => xorCount left + xorCount right
  | .select selector yes no => xorCount selector + xorCount yes + xorCount no + 2

abbrev Word (width : Nat) := Fin width → Gate
abbrev Value (width : Nat) := Fin width → Bool

def evaluateWord {width : Nat} (inputs : Nat → Bool) (word : Word width) : Value width :=
  fun bit => evaluate inputs (word bit)

def zero (width : Nat) : Word width := fun _ => .constant false

def muxWord {width : Nat} (selector : Gate) (yes no : Word width) : Word width :=
  fun bit => mux selector (yes bit) (no bit)

theorem evaluate_muxWord {width : Nat} (inputs : Nat → Bool)
    (selector : Gate) (yes no : Word width) :
    evaluateWord inputs (muxWord selector yes no) =
      if evaluate inputs selector then evaluateWord inputs yes else evaluateWord inputs no := by
  funext bit
  simp only [evaluateWord, muxWord, evaluate_mux]
  split <;> rfl

/-- A public list of slots, one secret selector per slot. The same gate schedule
runs for absence and for every address. Out-of-range selectors yield zero;
validity is a separate wire and must never silently decode zero as a valid node. -/
def readSelected {width : Nat} : List (Gate × Word width) → Word width
  | [] => zero width
  | (selector, value) :: rest => muxWord selector value (readSelected rest)

def referenceRead {width : Nat} (inputs : Nat → Bool) :
    List (Gate × Word width) → Value width
  | [] => fun _ => false
  | (selector, value) :: rest =>
      if evaluate inputs selector then evaluateWord inputs value else referenceRead inputs rest

theorem readSelected_exact {width : Nat} (inputs : Nat → Bool)
    (rows : List (Gate × Word width)) :
    evaluateWord inputs (readSelected rows) = referenceRead inputs rows := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨selector, value⟩
      simp only [readSelected, referenceRead, evaluate_muxWord, ih]

/-- Writes visit every physical row; append-only allocation supplies selectors
for one unallocated row and must separately establish heap well-formedness. -/
def writeSelected {width : Nat} (newValue : Word width)
    (rows : List (Gate × Word width)) : List (Word width) :=
  rows.map fun row => muxWord row.1 newValue row.2

theorem writeSelected_length {width : Nat} (newValue : Word width)
    (rows : List (Gate × Word width)) :
    (writeSelected newValue rows).length = rows.length := by
  simp [writeSelected]

theorem writeSelected_exact {width : Nat} (inputs : Nat → Bool)
    (newValue : Word width) (rows : List (Gate × Word width)) :
    (writeSelected newValue rows).map (evaluateWord inputs) =
      rows.map (fun row => if evaluate inputs row.1 then
        evaluateWord inputs newValue else evaluateWord inputs row.2) := by
  simp only [writeSelected, List.map_map, Function.comp_def, evaluate_muxWord]

/-- Equality circuitry scans every address bit. Little endian encoding is
public; gate construction depends only on pointer width and public slot index. -/
def equalConstant {width : Nat} (address : Word width) (index : Nat) : Gate :=
  (List.finRange width).foldr
    (fun bit rest => .and (.xor (address bit)
      (.constant (!(index.testBit bit.val)))) rest) (.constant true)

def addressRows {width pointerBits : Nat} (address : Word pointerBits)
    (rows : List (Word width)) : List (Gate × Word width) :=
  rows.zipIdx |>.map fun row => (equalConstant address row.2, row.1)

def readAddress {width pointerBits : Nat} (address : Word pointerBits)
    (rows : List (Word width)) : Word width := readSelected (addressRows address rows)

def orGate (left right : Gate) : Gate := .xor (.xor left right) (.and left right)

def validAddress {width pointerBits : Nat} (address : Word pointerBits)
    (rows : List (Word width)) : Gate :=
  (addressRows address rows).foldr (fun row rest => orGate row.1 rest) (.constant false)

/-- Wire-only node layout: occupancy, atom/cell tag, full atom word, and two
pointers. The unused payload is retained/padded rather than shape-revealing. -/
def nodeBits (atomBits pointerBits : Nat) : Nat := 2 + atomBits + 2 * pointerBits

structure HeapShape where
  slots : Nat
  atomBits : Nat
  pointerBits : Nat
  /-- Prevent slot-index aliasing in the finite address word. -/
  fits : slots ≤ 2 ^ pointerBits

/-- Component census after explicitly sharing each row equality selector.
Not a whole-evaluator cost, and not a cost claim for the unshared Gate tree.
An address test uses pointerBits ANDs; each selected payload bit one AND. -/
def sharedReadAnds (shape : HeapShape) : Nat :=
  shape.slots * (shape.pointerBits + nodeBits shape.atomBits shape.pointerBits)

def sharedWriteAnds (shape : HeapShape) : Nat := sharedReadAnds shape

/-- One packed resident heap, excluding controller/stack/equality queue and
protocol authenticators. The +7 is round-up, not truncation. -/
def heapBytes (shape : HeapShape) : Nat :=
  (shape.slots * nodeBits shape.atomBits shape.pointerBits + 7) / 8

#assert_axioms evaluate_mux
#assert_axioms evaluate_muxWord
#assert_axioms readSelected_exact
#assert_axioms writeSelected_length
#assert_axioms writeSelected_exact

end Minidregg.Compiler.BoundedNockCircuit
