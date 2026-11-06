/-
# Theory.BinaryTowerCoordinateArith -- computable Fan--Paar arithmetic on coordinates

`Theory.BinaryTowerFanPaarCodec` represents `T_k = GaloisField 2 (2^k)` by recursive
little-endian coordinates `Coordinate k` through the noncomputable equivalence
`coordinateFieldEquiv`. This file gives that carrier its own addition and multiplication,
written as structural recursion on the level, and proves both are the field operations
transported through `coordinateFieldEquiv`:

* `Coordinate.add`: coordinatewise XOR.
* `Coordinate.mul`: the one-level Fan--Paar/Karatsuba step `towerMulStep` at every level, with
  the reduction coefficient `towerMulCoeff k` in coordinates (`Coordinate.mulCoeff`).

Both run in the kernel and in compiled code, so a checker over `Coordinate 8` decides field
equations in `Tower256` without evaluating the field.
-/

module

public import Theory.BinaryTowerFanPaarCodec

@[expose] public section

namespace Minidregg.Theory.BinaryTowerFanPaarCodec

set_option autoImplicit false

namespace Coordinate

/-- The base bit. -/
def bitOf : Coordinate 0 → Bool
  | .bit value => value

/-- Low (constant) half of a level-`k+1` coordinate. -/
def low {k : Nat} : Coordinate (k + 1) → Coordinate k
  | .pair l _ => l

/-- High half (the `fpGen k` coefficient) of a level-`k+1` coordinate. -/
def high {k : Nat} : Coordinate (k + 1) → Coordinate k
  | .pair _ h => h

@[simp] theorem pair_low_high {k : Nat} (c : Coordinate (k + 1)) :
    Coordinate.pair (low c) (high c) = c := by
  cases c; rfl

@[simp] theorem low_pair {k : Nat} (l h : Coordinate k) : low (.pair l h) = l := rfl
@[simp] theorem high_pair {k : Nat} (l h : Coordinate k) : high (.pair l h) = h := rfl

@[simp] theorem bit_bitOf (c : Coordinate 0) : Coordinate.bit (bitOf c) = c := by
  cases c; rfl

/-- Field addition in coordinates: XOR at every leaf. -/
def add : (k : Nat) → Coordinate k → Coordinate k → Coordinate k
  | 0, a, b => .bit (xor (bitOf a) (bitOf b))
  | k + 1, a, b => .pair (add k (low a) (low b)) (add k (high a) (high b))

/-- The reduction coefficient `towerMulCoeff k` in coordinates: `1` at the bottom,
`fpGen (k-1)` above. -/
def mulCoeff : (k : Nat) → Coordinate k
  | 0 => one 0
  | k + 1 => topGenerator k

/-- Field multiplication in coordinates: the Fan--Paar/Karatsuba step at every level.
`(a₁ + a₂y)(b₁ + b₂y) = (a₁b₁ + a₂b₂) + ((a₁+a₂)(b₁+b₂) + a₁b₁ + a₂b₂ + a₂b₂·g) y`. -/
def mul : (k : Nat) → Coordinate k → Coordinate k → Coordinate k
  | 0, a, b => .bit (bitOf a && bitOf b)
  | k + 1, a, b =>
      let p₁ := mul k (low a) (low b)
      let p₂ := mul k (high a) (high b)
      let s := mul k (add k (low a) (high a)) (add k (low b) (high b))
      .pair (add k p₁ p₂) (add k (add k (add k s p₁) p₂) (mul k p₂ (mulCoeff k)))

end Coordinate

/-! ## The operations are the field operations -/

theorem coordinateFieldEquiv_bit_false :
    coordinateFieldEquiv 0 (.bit false) = 0 :=
  coordinateFieldEquiv_zero 0

theorem coordinateFieldEquiv_bit_true :
    coordinateFieldEquiv 0 (.bit true) = 1 :=
  coordinateFieldEquiv_one 0

theorem coordinateFieldEquiv_bit (b : Bool) :
    coordinateFieldEquiv 0 (.bit b) = if b then 1 else 0 := by
  cases b
  · exact coordinateFieldEquiv_bit_false
  · exact coordinateFieldEquiv_bit_true

theorem coordinateFieldEquiv_succ {k : Nat} (c : Coordinate (k + 1)) :
    coordinateFieldEquiv (k + 1) c =
      towerPack k (coordinateFieldEquiv k (Coordinate.low c),
        coordinateFieldEquiv k (Coordinate.high c)) := by
  cases c; rfl

theorem coordinateFieldEquiv_mulCoeff (k : Nat) :
    coordinateFieldEquiv k (Coordinate.mulCoeff k) = towerMulCoeff k := by
  cases k with
  | zero => exact coordinateFieldEquiv_one 0
  | succ k => exact coordinateFieldEquiv_topGenerator k

/-- **Coordinate addition is field addition.** -/
theorem coordinateFieldEquiv_add (k : Nat) (a b : Coordinate k) :
    coordinateFieldEquiv k (Coordinate.add k a b) =
      coordinateFieldEquiv k a + coordinateFieldEquiv k b := by
  induction k with
  | zero =>
      cases a with
      | bit x =>
        cases b with
        | bit y =>
          show coordinateFieldEquiv 0 (.bit (xor x y)) =
            coordinateFieldEquiv 0 (.bit x) + coordinateFieldEquiv 0 (.bit y)
          rw [coordinateFieldEquiv_bit, coordinateFieldEquiv_bit, coordinateFieldEquiv_bit]
          cases x <;> cases y <;> simp [one_add_one_eq_two, binaryTower_two_eq_zero 0]
  | succ k ih =>
      rw [coordinateFieldEquiv_succ, coordinateFieldEquiv_succ a, coordinateFieldEquiv_succ b]
      simp only [Coordinate.add, Coordinate.low_pair, Coordinate.high_pair, ih, towerPack,
        map_add]
      ring

/-- **Coordinate multiplication is field multiplication.** -/
theorem coordinateFieldEquiv_mul (k : Nat) (a b : Coordinate k) :
    coordinateFieldEquiv k (Coordinate.mul k a b) =
      coordinateFieldEquiv k a * coordinateFieldEquiv k b := by
  induction k with
  | zero =>
      cases a with
      | bit x =>
        cases b with
        | bit y =>
          show coordinateFieldEquiv 0 (.bit (x && y)) =
            coordinateFieldEquiv 0 (.bit x) * coordinateFieldEquiv 0 (.bit y)
          rw [coordinateFieldEquiv_bit, coordinateFieldEquiv_bit, coordinateFieldEquiv_bit]
          cases x <;> cases y <;> simp
  | succ k ih =>
      rw [coordinateFieldEquiv_succ, coordinateFieldEquiv_succ a, coordinateFieldEquiv_succ b,
        ← towerPack_towerMulStep]
      simp only [Coordinate.mul, Coordinate.low_pair, Coordinate.high_pair, ih,
        coordinateFieldEquiv_add, coordinateFieldEquiv_mulCoeff, towerMulStep]

/-! ## Teeth: the operations are not degenerate

At GF(4) the generator `x₀ = topGenerator 0` satisfies `x₀² = x₀ + 1`, computed by the
kernel on coordinates, and `x₀ ≠ 1`, so `mul` is neither constant nor the identity. -/

example : Coordinate.mul 1 (Coordinate.topGenerator 0) (Coordinate.topGenerator 0)
    = Coordinate.add 1 (Coordinate.topGenerator 0) (Coordinate.one 1) := by decide

example : Coordinate.topGenerator 0 ≠ Coordinate.one 1 := by decide

/-- info: 'Minidregg.Theory.BinaryTowerFanPaarCodec.coordinateFieldEquiv_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms coordinateFieldEquiv_add
/-- info: 'Minidregg.Theory.BinaryTowerFanPaarCodec.coordinateFieldEquiv_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms coordinateFieldEquiv_mul

end Minidregg.Theory.BinaryTowerFanPaarCodec
