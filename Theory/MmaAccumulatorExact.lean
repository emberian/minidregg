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

/-! ### GF(2) inner products as the parity of an exact integer sum (the rotation, 2026-11-06)

The tensor-core route for binary fields on hardware without a 1-bit MMA (Blackwell: emulated; Hopper: xor
emulated): operands 0/1 as FP8 e4m3 or FP4 e2m1 (both exact), products 0/1, accumulate in the FP
accumulator, read the parity of the exact count.  Exact while the count stays below `2^m`; with a promotion
to an integer or a parity register every block, exact at every length. -/

def bit (b : Bool) : Int := if b then 1 else 0

/-- The products of a GF(2) inner product as one (right-nested) summation tree, with a `0` initial value. -/
def prodTree : List (Bool × Bool) → STree
  | [] => .leaf 0
  | (a, b) :: rest => .node (.leaf (bit (a && b))) (prodTree rest)

/-- The GF(2) inner product. -/
def xorDot : List (Bool × Bool) → Bool
  | [] => false
  | (a, b) :: rest => xor (a && b) (xorDot rest)

theorem prodTree_bounded : ∀ v : List (Bool × Bool), (prodTree v).Bounded 1
  | [] => by simp [prodTree, STree.Bounded]
  | (a, b) :: rest => by
      refine ⟨?_, prodTree_bounded rest⟩
      cases a <;> cases b <;> simp [bit, STree.Bounded]

theorem prodTree_size : ∀ v : List (Bool × Bool), (prodTree v).size = v.length + 1
  | [] => rfl
  | (_, _) :: rest => by simp [prodTree, STree.size, prodTree_size rest]; omega

theorem prodTree_exact_nonneg : ∀ v : List (Bool × Bool), 0 ≤ (prodTree v).exact
  | [] => by decide
  | (a, b) :: rest => by
      have := prodTree_exact_nonneg rest
      simp only [prodTree, STree.exact]
      cases a <;> cases b <;> simp [bit] <;> omega

/-- The exact count's parity is the GF(2) inner product. -/
theorem prodTree_exact_parity : ∀ v : List (Bool × Bool), (prodTree v).exact % 2 = bit (xorDot v)
  | [] => by decide
  | (a, b) :: rest => by
      have ih := prodTree_exact_parity rest
      simp only [prodTree, STree.exact, xorDot]
      revert ih
      generalize (prodTree rest).exact = e
      generalize xorDot rest = x
      intro ih
      cases a <;> cases b <;> cases x <;> simp [bit] at ih ⊢ <;> omega

/-- **GF(2) inner product through a floating accumulator.**  Any accumulator that holds integers below
`2^m` (post-addition rounding, `HoldsBelow`), `N + 1 < 2^m` 0/1 products: the parity of the hardware sum is
the GF(2) inner product. -/
theorem gf2_dot_via_fp (m : Nat) (rnd : Int → Int) (hr : HoldsBelow m rnd) (v : List (Bool × Bool))
    (hN : v.length + 1 < 2 ^ m) : (prodTree v).hw rnd % 2 = bit (xorDot v) := by
  rw [hw_exact m 1 rnd hr (prodTree v) (prodTree_bounded v) (by rw [prodTree_size]; omega)]
  exact prodTree_exact_parity v

/-- The same through the wrapping `.s32` register (INT8 0/1 operands, or `.b1 and.popc`): no bound. -/
theorem gf2_dot_via_s32 (v : List (Bool × Bool)) : (prodTree v).hwWrap % 2 = bit (xorDot v) := by
  rw [s32_parity_exact]; exact prodTree_exact_parity v

theorem xorDot_append : ∀ u w : List (Bool × Bool), xorDot (u ++ w) = xor (xorDot u) (xorDot w)
  | [], w => by simp [xorDot]
  | (a, b) :: rest, w => by
      simp only [List.cons_append, xorDot, xorDot_append rest w]
      cases (a && b) <;> cases xorDot rest <;> cases xorDot w <;> rfl

/-- Parity bit of an exact integer, as a Bool. -/
def par (x : Int) : Bool := x % 2 == 1

theorem par_bit (b : Bool) : par (bit b) = b := by cases b <;> decide

/-- **Promotion: exact at every length.**  Split the products into blocks, each shorter than `2^m - 1`,
accumulate each block on the floating accumulator, and xor the blocks' parity bits (the promotion).  The
result is the GF(2) inner product of the whole vector. -/
theorem gf2_dot_blocks (m : Nat) (rnd : Int → Int) (hr : HoldsBelow m rnd) :
    ∀ blocks : List (List (Bool × Bool)), (∀ blk ∈ blocks, blk.length + 1 < 2 ^ m) →
      (blocks.map fun blk => par ((prodTree blk).hw rnd)).foldr xor false = xorDot blocks.flatten
  | [], _ => rfl
  | blk :: rest, h => by
      have h1 := gf2_dot_via_fp m rnd hr blk (h blk (List.mem_cons_self ..))
      have h2 := gf2_dot_blocks m rnd hr rest (fun b hb => h b (List.mem_cons_of_mem _ hb))
      simp only [List.map, List.foldr, List.flatten_cons, xorDot_append, h2]
      congr 1
      unfold par; rw [h1]; cases xorDot blk <;> decide

/-- Falsifier: nine products `1·1` through a 3-bit truncating accumulator (one past `2^3`): the count 9 is
held as 8 and the parity flips. -/
theorem gf2_fp_fails_past_block :
    (prodTree (List.replicate 9 (true, true))).hw (trunc 3) % 2 ≠
      bit (xorDot (List.replicate 9 (true, true))) := by decide

/-- Non-vacuity: six mixed products inside a 3-bit block (`6 + 1 < 2^3`): the parity is read correctly. -/
theorem gf2_fp_inside :
    (prodTree [(true, true), (true, false), (true, true), (false, true), (true, true), (true, true)]).hw
      (trunc 3) % 2 = bit (xorDot [(true, true), (true, false), (true, true), (false, true), (true, true),
        (true, true)]) := by decide

/-! ### Lazy reduction of any GF(2)-bilinear map

For a fixed bilinear map over GF(2) (output coordinate given by a coefficient table `T j k`), the sum of
`B(a_n, b_n)` over a block equals `T` applied once to the GF(2) outer-product sum `S j k = Σ a_n j b_n k`.
Every coordinate of a Tower256 product is such a map in any fixed basis, so the inner product is: count on
the tensor core, take parities (`gf2_dot_via_fp` per `S j k`), apply `T` once per block.  The instance for
minidregg's `Coordinate.mul` needs its bilinearity, which is not proved here. -/

def pairs (d : Nat) : List (Fin d × Fin d) :=
  (List.finRange d).flatMap fun j => (List.finRange d).map fun k => (j, k)

def bil (d : Nat) (T : Fin d → Fin d → Bool) (a b : Fin d → Bool) : Bool :=
  xsum ((pairs d).map fun jk => T jk.1 jk.2 && (a jk.1 && b jk.2))

theorem xsum_map_xor {α} (L : List α) (f g : α → Bool) :
    xsum (L.map fun x => xor (f x) (g x)) = xor (xsum (L.map f)) (xsum (L.map g)) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map, xsum, ih]
      cases f x <;> cases g x <;> cases xsum (xs.map f) <;> cases xsum (xs.map g) <;> rfl

theorem xsum_map_false {α} (L : List α) : xsum (L.map fun _ => false) = false := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp only [List.map, xsum, ih]; rfl

theorem lazy_bilinear (d : Nat) (T : Fin d → Fin d → Bool) :
    ∀ v : List ((Fin d → Bool) × (Fin d → Bool)),
      xsum (v.map fun ab => bil d T ab.1 ab.2) =
        xsum ((pairs d).map fun jk => T jk.1 jk.2 && xsum (v.map fun ab => ab.1 jk.1 && ab.2 jk.2))
  | [] => by
      simp only [List.map, xsum]
      have : ∀ jk : Fin d × Fin d, (T jk.1 jk.2 && false) = false := fun _ => by simp
      simp only [this]; exact (xsum_map_false _).symm
  | ab :: rest => by
      have ih := lazy_bilinear d T rest
      simp only [List.map, xsum]
      have hd : ∀ jk : Fin d × Fin d,
          (T jk.1 jk.2 && xor (ab.1 jk.1 && ab.2 jk.2) (xsum (rest.map fun ab => ab.1 jk.1 && ab.2 jk.2))) =
          xor (T jk.1 jk.2 && (ab.1 jk.1 && ab.2 jk.2))
              (T jk.1 jk.2 && xsum (rest.map fun ab => ab.1 jk.1 && ab.2 jk.2)) := by
        intro jk
        cases T jk.1 jk.2 <;> cases (ab.1 jk.1 && ab.2 jk.2) <;>
          cases xsum (rest.map fun ab => ab.1 jk.1 && ab.2 jk.2) <;> rfl
      simp only [hd, xsum_map_xor, ← ih]
      rfl

/-- Concrete check: GF(2)[x]/(x^2+x+1) (GF(4)), coordinates (1, x).  Product coordinate 0 is
`a0 b0 + a1 b1`, coordinate 1 is `a0 b1 + a1 b0 + a1 b1`; the lazy form agrees on a 3-term block. -/
def gf4T1 : Fin 2 → Fin 2 → Bool := fun j k => !(j.val == 0 && k.val == 0)

theorem gf4_lazy_check :
    let v : List ((Fin 2 → Bool) × (Fin 2 → Bool)) :=
      [(fun i => i.val == 1, fun _ => true), (fun _ => true, fun i => i.val == 0), (fun _ => true, fun _ => true)]
    xsum (v.map fun ab => bil 2 gf4T1 ab.1 ab.2) =
      xsum ((pairs 2).map fun jk => gf4T1 jk.1 jk.2 && xsum (v.map fun ab => ab.1 jk.1 && ab.2 jk.2)) := by
  decide

/-! ### Measured instances (H100, initiative 17 run paid-h100-mma-03, 2026-11-07)

QGMMA (wgmma e4m3 -> f32) holds integers exactly through 2^14 and not from 2^14.5, so `HoldsBelow 14` is the
measured premise; HGMMA (f16) holds `HoldsBelow 24`.  The block lengths below are the theorems' side
conditions at those widths, each with the first length past it. -/

/-- QGMMA block lengths at the measured m = 14: GF(2) counts (with the theorem's one-product slack),
base-16 e4m3 limbs (products <= 225), doubled-E2M1 base-13 limbs (products <= 64). -/
theorem qgmma_m14_blocks :
    16382 + 1 < 2 ^ 14 ∧ ¬ (16383 + 1 < 2 ^ 14) ∧
    72 * 225 < 2 ^ 14 ∧ ¬ (73 * 225 < 2 ^ 14) ∧
    255 * 64 < 2 ^ 14 ∧ ¬ (256 * 64 < 2 ^ 14) := by decide

/-- HGMMA block lengths at the measured m = 24: GF(2) counts and u8 byte limbs (products <= 65,025). -/
theorem hgmma_m24_blocks :
    16777214 + 1 < 2 ^ 24 ∧ 258 * 65025 < 2 ^ 24 ∧ ¬ (259 * 65025 < 2 ^ 24) := by decide

/-- The GF(2) inner product on QGMMA, given the measured premise: up to 16,382 products per block. -/
theorem qgmma_gf2_dot (rnd : Int → Int) (hr : HoldsBelow 14 rnd) (v : List (Bool × Bool))
    (hN : v.length ≤ 16382) : (prodTree v).hw rnd % 2 = bit (xorDot v) :=
  gf2_dot_via_fp 14 rnd hr v (by have : (2:Nat) ^ 14 = 16384 := rfl; omega)

/-- The GF(2) inner product on HGMMA, given the measured premise: up to 16,777,214 products per block. -/
theorem hgmma_gf2_dot (rnd : Int → Int) (hr : HoldsBelow 24 rnd) (v : List (Bool × Bool))
    (hN : v.length ≤ 16777214) : (prodTree v).hw rnd % 2 = bit (xorDot v) :=
  gf2_dot_via_fp 24 rnd hr v (by have : (2:Nat) ^ 24 = 16777216 := rfl; omega)

end MmaAccumulatorExact
