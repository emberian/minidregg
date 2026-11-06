/-
Exactness of tensor-core accumulation for field arithmetic, per accumulator kind (initiative 14, F3).

Extends the accumulator contract proposed in redregg `designs/SILICON-THEOREM-REPAIRS-2026-11-06.md`
(R2a-R2c) in four directions:
* the summation ORDER is arbitrary (`STree`): PTX leaves "accumulation order, rounding and handling of
  subnormal inputs unspecified", so the statement quantifies over every binary summation tree;
* the accumulator is any function `rnd` applied after each addition that holds integers below `2^m`
  (`HoldsBelow`): truncation, round-to-nearest.  This is a POST-ADDITION rounding machine.  A multi-term
  fused adder aligns its addends to the group's largest exponent BEFORE adding, which `rnd` cannot express
  (Codex audit 2026-11-06); `groupAdd` / `group_exact` below model that separately, and show that inside the
  bound alignment loses nothing either.  `m` per SKU, kind and path is a MEASURED premise;
* the integer `.s32` accumulator wraps (PTX: "if .satfinite is not specified, the accumulated value is
  wrapped"): the wrapped register is the sum mod 2^32 for every tree, so a signed read is exact under the
  TensorZKP bound and a PARITY read (GF(2) matrix products) is exact for every length;
* one Karatsuba level commutes with lazy (once-per-block) reduction over GF(2).

Core Lean only (no Mathlib), so the file checks standalone: `lean Theory/MmaAccumulatorExact.lean`.
Counts side: zkml-research `notes/construction-search/mma_counts.py`.
-/

namespace MmaAccumulatorExact

/-- A summation tree over integer products.  The hardware's order is one such tree. -/
inductive STree where
  | leaf : Int → STree
  | node : STree → STree → STree

/-- The exact (Kulisch) sum. -/
def STree.exact : STree → Int
  | .leaf x => x
  | .node a b => a.exact + b.exact

/-- Number of products summed. -/
def STree.size : STree → Nat
  | .leaf _ => 1
  | .node a b => a.size + b.size

/-- The hardware sum: every internal addition passes through the accumulator's `rnd`. -/
def STree.hw (rnd : Int → Int) : STree → Int
  | .leaf x => x
  | .node a b => rnd (a.hw rnd + b.hw rnd)

/-- Every product has magnitude at most `P`. -/
def STree.Bounded (P : Nat) : STree → Prop
  | .leaf x => x.natAbs ≤ P
  | .node a b => a.Bounded P ∧ b.Bounded P

/-- The only property of the floating accumulator used: it holds integers of magnitude `< 2^m`. -/
def HoldsBelow (m : Nat) (rnd : Int → Int) : Prop :=
  ∀ y : Int, y.natAbs < 2 ^ m → rnd y = y

theorem exact_natAbs_le (P : Nat) : ∀ t : STree, t.Bounded P → t.exact.natAbs ≤ t.size * P
  | .leaf x, h => by simp only [STree.exact, STree.size, Nat.one_mul]; exact h
  | .node a b, ⟨ha, hb⟩ => by
      have h1 := exact_natAbs_le P a ha
      have h2 := exact_natAbs_le P b hb
      have h3 := Int.natAbs_add_le a.exact b.exact
      simp only [STree.exact, STree.size, Nat.add_mul]
      omega

/-- **Floating accumulator, any order.**  If every product is bounded by `P` and `N·P < 2^m`, the hardware
sum over any summation tree equals the exact sum.  The bound is derived (every subtree sum is at most its
own size times `P`), never assumed per node. -/
theorem hw_exact (m P : Nat) (rnd : Int → Int) (hr : HoldsBelow m rnd) :
    ∀ t : STree, t.Bounded P → t.size * P < 2 ^ m → t.hw rnd = t.exact
  | .leaf _, _, _ => rfl
  | .node a b, ⟨ha, hb⟩, hN => by
      have hsa : a.size * P < 2 ^ m := by
        have : a.size * P ≤ (a.size + b.size) * P := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        simp only [STree.size] at hN; omega
      have hsb : b.size * P < 2 ^ m := by
        have : b.size * P ≤ (a.size + b.size) * P := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
        simp only [STree.size] at hN; omega
      have ea := hw_exact m P rnd hr a ha hsa
      have eb := hw_exact m P rnd hr b hb hsb
      have hab := exact_natAbs_le P (.node a b) ⟨ha, hb⟩
      simp only [STree.hw, ea, eb]
      exact hr _ (by simp only [STree.exact] at hab; omega)

/-! ### A concrete accumulator: truncation toward zero to `m` significant bits -/

/-- Keep the top `m` bits of `|y|`, clear the rest, restore the sign. -/
def trunc (m : Nat) (y : Int) : Int :=
  let a := y.natAbs
  let k := (Nat.log2 a + 1) - m
  let t : Int := ((a / 2 ^ k) * 2 ^ k : Nat)
  if y < 0 then -t else t

theorem trunc_holdsBelow (m : Nat) : HoldsBelow m (trunc m) := by
  intro y hy
  by_cases h0 : y.natAbs = 0
  · have : y = 0 := Int.natAbs_eq_zero.mp h0
    subst this; simp [trunc]
  · have hk : (Nat.log2 y.natAbs + 1) - m = 0 := by
      have := (Nat.log2_lt h0).2 hy
      omega
    unfold trunc
    simp only [hk, Nat.pow_zero, Nat.div_one, Nat.mul_one]
    split <;> omega

/-! ### Falsifiers: the bound is sufficient, and one block past the TRUE threshold breaks it.

For `P = 64` the bound gives `N ≤ (2^m - 1)/64`.  Length `N_bound + 1` can still be exact, because the
largest reachable sum is `2^m`, which is representable; the first failing length is `⌈2^m/64⌉ + 1`, where
the sum `2^m + 1` (one product equal to 1) needs `m + 1` bits.  At `m = 7`: bound `N ≤ 1`, `N = 2` exact,
`N = 3` fails.  `mma_counts.py` prints the same threshold for `m = 14`: bound 255, first failure 257. -/

/-- Left-to-right accumulation of a list (one admissible tree). -/
def chain : List Int → STree
  | [] => .leaf 0
  | x :: xs => xs.foldl (fun acc y => .node acc (.leaf y)) (.leaf x)

theorem m7_two_exact : (chain [64, 64]).hw (trunc 7) = (chain [64, 64]).exact := by decide
theorem m7_three_fails : (chain [64, 64, 1]).hw (trunc 7) ≠ (chain [64, 64, 1]).exact := by decide
/-- The failing instance really is past the bound (so `hw_exact` is not contradicted). -/
theorem m7_three_past_bound : ¬ ((chain [64, 64, 1]).size * 64 < 2 ^ 7) := by decide
/-- Non-vacuity of `hw_exact`: a bounded instance inside the bound, at the FP4 base-13 maximum product. -/
theorem m7_one_inside : (chain [64]).size * 64 < 2 ^ 7 ∧ (chain [64]).Bounded 64 := by
  simp [chain, STree.size, STree.Bounded]

/-! ### The integer accumulator: `.s32`, wrapping -/

def M32 : Int := 4294967296

/-- The register after every product and every addition wraps mod 2^32 (as an unsigned residue). -/
def STree.hwWrap : STree → Int
  | .leaf x => x % M32
  | .node a b => (a.hwWrap + b.hwWrap) % M32

theorem hwWrap_eq (t : STree) : t.hwWrap = t.exact % M32 := by
  induction t with
  | leaf x => rfl
  | node a b iha ihb =>
      simp only [STree.hwWrap, STree.exact, iha, ihb]
      exact (Int.add_emod a.exact b.exact M32).symm

/-- Two's-complement (signed) reading of the register. -/
def signed (r : Int) : Int := if r ≥ 2147483648 then r - M32 else r

/-- **Signed read, any order.**  Products bounded by `P`, `N·P < 2^31`, and a nonnegative TOTAL: the signed
register equals the exact sum.  TensorZKP's eq. 23 is the instance `P = 255^2`, `N ≤ 33,025`. -/
theorem s32_signed_exact (P : Nat) (t : STree) (hb : t.Bounded P) (hN : t.size * P < 2 ^ 31)
    (hnn : 0 ≤ t.exact) : signed t.hwWrap = t.exact := by
  have h := exact_natAbs_le P t hb
  rw [hwWrap_eq]
  have hlt : t.exact < 2147483648 := by omega
  have : t.exact % M32 = t.exact := Int.emod_eq_of_lt hnn (by unfold M32; omega)
  unfold signed; rw [this]; split <;> omega

/-- **Unsigned read.**  A nonnegative total below `2^32` is the register itself (zero-extended): for u8 limbs
`N ≤ 66,051`.  No bound on partial sums: wrapped intermediates still give the exact final residue. -/
theorem s32_unsigned_exact (t : STree) (hnn : 0 ≤ t.exact) (hlt : t.exact < M32) :
    t.hwWrap = t.exact := by
  rw [hwWrap_eq]; exact Int.emod_eq_of_lt hnn hlt

theorem u8_unsigned_bound : 66051 * 65025 < 2 ^ 32 ∧ ¬ (66052 * 65025 < 2 ^ 32) := by decide

/-- **Parity read, any order, any length.**  The low bit of the wrapped register is the low bit of the exact
sum: GF(2) matrix products on integer (`.s8` 0/1 or `.b1 .and.popc`) MMA need no block bound. -/
theorem s32_parity_exact (t : STree) : t.hwWrap % 2 = t.exact % 2 := by
  rw [hwWrap_eq]
  exact Int.emod_emod_of_dvd t.exact (by decide : (2 : Int) ∣ M32)

/-- TensorZKP's bound holds at 33,025 and is exceeded at 33,026. -/
theorem tensorzkp_bound : 33025 * 65025 < 2 ^ 31 ∧ ¬ (33026 * 65025 < 2 ^ 31) := by decide

/-- Falsifier for the signed read one product past the bound: the register reads negative. -/
theorem s32_signed_fails_past_bound : signed ((33026 * 65025 : Int) % M32) ≠ 33026 * 65025 := by decide

/-- Non-vacuity of the parity theorem: a sum that really wraps (exceeds 2^32) keeps its parity. -/
theorem parity_through_wrap :
    (STree.node (.leaf 4294967295) (.leaf 4294967295)).exact ≥ M32 ∧
    (STree.node (.leaf 4294967295) (.leaf 4294967295)).hwWrap % 2 =
      (STree.node (.leaf 4294967295) (.leaf 4294967295)).exact % 2 := by decide

/-! ### A multi-term group adder (Fasi et al. 2021 shape)

All addends of a group are aligned to the group's largest magnitude, keeping `m` bits below its leading bit
(truncating the rest), then added exactly and rounded once.  If every addend and the result are integers of
magnitude `< 2^m`, the alignment quantum is `1` and nothing is lost. -/

/-- The alignment quantum's exponent for a group whose largest magnitude is `a`. -/
def alignExp (m a : Nat) : Nat := (Nat.log2 a + 1) - m

/-- Truncate an addend toward zero to a multiple of `2^e`. -/
def alignTo (e : Nat) (x : Int) : Int :=
  let t : Int := ((x.natAbs / 2 ^ e) * 2 ^ e : Nat)
  if x < 0 then -t else t

def maxAbs : List Int → Nat
  | [] => 0
  | x :: xs => max x.natAbs (maxAbs xs)

def isum : List Int → Int
  | [] => 0
  | x :: xs => x + isum xs

/-- One fused group: align every addend to the group's quantum, sum, then round the result once. -/
def groupAdd (m : Nat) (rnd : Int → Int) (xs : List Int) : Int :=
  rnd (isum (xs.map (alignTo (alignExp m (maxAbs xs)))))

theorem maxAbs_lt (m : Nat) : ∀ xs : List Int, (∀ x ∈ xs, x.natAbs < 2 ^ m) → maxAbs xs < 2 ^ m
  | [], _ => Nat.two_pow_pos m
  | x :: xs, h => by
      have h1 := h x (List.mem_cons_self ..)
      have h2 := maxAbs_lt m xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [maxAbs]; omega

theorem alignTo_zero (x : Int) : alignTo 0 x = x := by
  unfold alignTo; simp only [Nat.pow_zero, Nat.div_one, Nat.mul_one]; split <;> omega

theorem map_alignTo_zero : ∀ xs : List Int, xs.map (alignTo 0) = xs
  | [] => rfl
  | x :: xs => by simp only [List.map, alignTo_zero, map_alignTo_zero xs]

/-- **Group adder exact inside the bound.**  Every addend below `2^m` and a result below `2^m`: the fused
group returns the exact sum, for any final rounding that holds integers below `2^m`. -/
theorem group_exact (m : Nat) (hm : 0 < m) (rnd : Int → Int) (hr : HoldsBelow m rnd) (xs : List Int)
    (hx : ∀ x ∈ xs, x.natAbs < 2 ^ m) (hs : (isum xs).natAbs < 2 ^ m) :
    groupAdd m rnd xs = isum xs := by
  have hmax := maxAbs_lt m xs hx
  have he : alignExp m (maxAbs xs) = 0 := by
    unfold alignExp
    by_cases h0 : maxAbs xs = 0
    · simp [h0]; omega
    · have := (Nat.log2_lt h0).2 hmax; omega
  unfold groupAdd; rw [he, map_alignTo_zero]; exact hr _ hs

/-- Non-vacuity: a mixed-magnitude group inside the bound is exact (the quantum is `1`). -/
theorem group_inside : groupAdd 7 (trunc 7) [64, 1, 3] = 68 := by decide

/-- Falsifier (outside the bound): in a 7-bit group, the addend `128` (8 bits) sets the quantum to `2`, and the
addend `1` is aligned away: `128 + 1` returns `128`. -/
theorem group_fails_outside : groupAdd 7 (trunc 7) [128, 1] ≠ isum [128, 1] := by decide

/-! ### Karatsuba commutes with lazy reduction over GF(2)

Over GF(2) (Bool, `xor` as addition), for a block of products `(a0 + a1 X)(b0 + b1 X)`, the middle
coefficient computed lazily from three accumulated sums,
`Σ (a0+a1)(b0+b1) + Σ a0 b0 + Σ a1 b1`, equals the lazily accumulated true middle coefficient
`Σ (a0 b1 + a1 b0)`.  This is the coordinate-level instance only.  For the Fan-Paar step `y² = g·y + 1` the product is
`(U + V, W + U + V + g·V)` with `U = Σ a0 b0`, `V = Σ a1 b1`, `W = Σ (a0+a1)(b0+b1)` (minidregg
`Theory/BinaryTowerFanPaar.lean:235`); every recombination including `g·V` is GF(2)-linear, so lazy
accumulation commutes at every level, but the tower-level statement is NOT proved here. -/

def xsum : List Bool → Bool
  | [] => false
  | x :: xs => xor x (xsum xs)

theorem kar_lazy_commutes (v : List (Bool × Bool × Bool × Bool)) :
    xor (xor (xsum (v.map fun ⟨a0, a1, b0, b1⟩ => (xor a0 a1) && (xor b0 b1)))
             (xsum (v.map fun ⟨a0, _, b0, _⟩ => a0 && b0)))
        (xsum (v.map fun ⟨_, a1, _, b1⟩ => a1 && b1)) =
      xsum (v.map fun ⟨a0, a1, b0, b1⟩ => xor (a0 && b1) (a1 && b0)) := by
  induction v with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨a0, a1, b0, b1⟩ := e
      simp only [List.map, xsum]
      revert ih
      generalize xsum (rest.map fun ⟨a0, a1, b0, b1⟩ => (xor a0 a1) && (xor b0 b1)) = p
      generalize xsum (rest.map fun ⟨a0, _, b0, _⟩ => a0 && b0) = q
      generalize xsum (rest.map fun ⟨_, a1, _, b1⟩ => a1 && b1) = r
      generalize xsum (rest.map fun ⟨a0, a1, b0, b1⟩ => xor (a0 && b1) (a1 && b0)) = s
      intro ih; subst ih
      cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> cases p <;> cases q <;> cases r <;> decide

end MmaAccumulatorExact
