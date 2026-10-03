/- Fixed physical row layout for the actual Bend closure heap.
This connects finite pointer words to Row; it is not a second evaluator.
Raw three-bit tags 6/7 and two-bit quantity 3 must be refused by a wire decoder.
Inactive fields have a canonical zero encoding. Controller/state and source
refinement remain separate from this per-row representation theorem. -/
import Theory.BendClosureArena
import Init.Data.BitVec.Lemmas

namespace Minidregg.Compiler.BendClosurePacking
open Minidregg.Theory BendTT BendClosureArena
set_option autoImplicit false

inductive RowTag where
  | vacant | nil | environment | closure | pair | application
  deriving DecidableEq, Repr

structure PackedRow (width : Nat) where
  tag : RowTag
  quantity : Quan
  first : BitVec width
  second : BitVec width
  deriving DecidableEq, Repr

def pack (width : Nat) : Row → PackedRow width
  | .vacant => ⟨.vacant, .Q0, 0, 0⟩
  | .nil => ⟨.nil, .Q0, 0, 0⟩
  | .environment first second =>
    ⟨.environment, .Q0, .ofNat width first, .ofNat width second⟩
  | .closure code environment =>
    ⟨.closure, .Q0, .ofNat width code, .ofNat width environment⟩
  | .pair quantity first second =>
    ⟨.pair, quantity, .ofNat width first, .ofNat width second⟩
  | .application quantity function argument =>
    ⟨.application, quantity, .ofNat width function, .ofNat width argument⟩

def unpack {width : Nat} (row : PackedRow width) : Row :=
  match row.tag with
  | .vacant => .vacant
  | .nil => .nil
  | .environment => .environment row.first.toNat row.second.toNat
  | .closure => .closure row.first.toNat row.second.toNat
  | .pair => .pair row.quantity row.first.toNat row.second.toNat
  | .application => .application row.quantity row.first.toNat row.second.toNat

/-- Publication/input admission must check this bound, preventing modular
truncation of a host Nat from masquerading as a valid pointer. -/
theorem unpack_pack {width : Nat} {row : Row} (fits : row.fits (2 ^ width) = true) :
    unpack (pack width row) = row := by
  cases row <;>
    simp_all [pack, unpack, Row.fits, Bool.and_eq_true, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt]

/-- Packed words discharge the repeated whole-row word-range scan. Heap size,
frontier and backward references remain independent obligations. -/
theorem unpack_fits {width : Nat} (row : PackedRow width) :
    (unpack row).fits (2 ^ width) = true := by
  have first := row.first.isLt
  have second := row.second.isLt
  cases tag : row.tag <;> simp_all [unpack, Row.fits]

def canonical {width : Nat} (row : PackedRow width) : Bool :=
  decide (pack width (unpack row) = row)

def tagCode : RowTag → Nat
  | .vacant => 0 | .nil => 1 | .environment => 2
  | .closure => 3 | .pair => 4 | .application => 5

def quantityCode : Quan → Nat
  | .Q0 => 0 | .Q1 => 1 | .Q2 => 2

def natBits (width value : Nat) : List Bool :=
  (List.range width).map value.testBit

/-- Three tag bits, two quantity bits, then two little-endian pointer words. -/
def bits {width : Nat} (row : PackedRow width) : List Bool :=
  natBits 3 (tagCode row.tag) ++ natBits 2 (quantityCode row.quantity) ++
    natBits width row.first.toNat ++ natBits width row.second.toNat

theorem bits_length {width : Nat} (row : PackedRow width) :
    (bits row).length = 5 + 2 * width := by
  simp [bits, natBits]
  omega

#assert_axioms unpack_pack
#assert_axioms unpack_fits
#assert_axioms bits_length
end Minidregg.Compiler.BendClosurePacking
