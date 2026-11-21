/-
# Theory.SequenceSpread -- a position spread over the leading bits of a trie path

A keyed trie whose path is a key's bytes holds two keys that share their first `d` path bits
under a chain of `d` rows, and every write to either rewrites that chain. A family whose keys
are (a sequence id, a position) written id first puts all of one sequence's items under one
256-bit prefix: the chain is as long as the id whatever the sequence holds. The cure is the
path, not the key: the position's bits, least significant first, are folded (exclusive or)
into the leading path bits of the id.

A 32-octet value is written least significant octet first and each octet's bits most
significant first, so path bit `i` of a value is its bit `pathIndex i`.

* `spread p`: the number whose path bit `i` is bit `i` of `p` (`pathBit_spread`).
* `fold s p = s ^^^ spread p`, below `2 ^ 256` (`fold_lt`), cancellable in `s`
  (`fold_cancel`: with the position known the id is recovered, so the path stays injective).
* **`fold_diverge`**: two different positions below `2 ^ k` give paths that differ within
  their first `k` bits, whatever the id. A sequence of `n` items therefore shares at most
  `log2 n` bits between any two of its items beyond what the id's own bits share with the
  rest of the trie: its items sit at the depth a random key would, not under a chain.

Witnesses. Satisfiable: `Example.spread_small` (position 1 sets the first path bit, position 2
the second). Teeth: `fold_shared` with `Example.shared_low` (positions that agree on their low
`k` bits share their first `k` path bits: the bound is tight, and an id alone, which is every
position folded with nothing, shares all 256). Premise inhabitation: `fold_diverge` asks only
`p ≠ q` below `2 ^ k` with `k ≤ 256`; `Example.diverge_inhabited` instantiates it.
-/
module

@[expose] public section

namespace Minidregg.Theory.SequenceSpread

set_option autoImplicit false

/-- The bit of a 32-octet value that path bit `i` reads: octets least significant first,
each octet's bits most significant first. -/
def pathIndex (i : Nat) : Nat := 8 * (i / 8) + (7 - i % 8)

theorem pathIndex_lt {i : Nat} (small : i < 256) : pathIndex i < 256 := by
  unfold pathIndex; omega

theorem pathIndex_involutive (i : Nat) : pathIndex (pathIndex i) = i := by
  unfold pathIndex; omega

/-- Path bit `i` of a 32-octet value. -/
def pathBit (value i : Nat) : Bool := value.testBit (pathIndex i)

/-- The number below `2 ^ n` whose bit `i` is `f i`. -/
def ofBits (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ n * (f n).toNat + ofBits f n

theorem ofBits_lt (f : Nat → Bool) : ∀ n, ofBits f n < 2 ^ n
  | 0 => by simp [ofBits]
  | n + 1 => by
      have below := ofBits_lt f n
      cases bit : f n <;> simp only [ofBits, bit, Bool.toNat_true, Bool.toNat_false, Nat.pow_succ] <;> omega

theorem testBit_ofBits (f : Nat → Bool) : ∀ (n i : Nat), i < n → (ofBits f n).testBit i = f i
  | 0, _, small => absurd small (Nat.not_lt_zero _)
  | n + 1, i, small => by
      have below := ofBits_lt f n
      by_cases last : i = n
      · subst last
        cases bit : f i
        · simp [ofBits, bit, Nat.testBit_lt_two_pow below]
        · simp only [ofBits, bit, Bool.toNat_true, Nat.mul_one]
          rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow below]; rfl
      · have inside : i < n := by omega
        cases bit : f n
        · simpa [ofBits, bit] using testBit_ofBits f n i inside
        · simp only [ofBits, bit, Bool.toNat_true, Nat.mul_one]
          rw [Nat.testBit_two_pow_add_gt inside]
          exact testBit_ofBits f n i inside

/-- The number whose path bit `i` is bit `i` of `position`, for `i < 256`. -/
def spread (position : Nat) : Nat := ofBits (fun j => position.testBit (pathIndex j)) 256

theorem spread_lt (position : Nat) : spread position < 2 ^ 256 := ofBits_lt _ 256

theorem pathBit_spread (position : Nat) {i : Nat} (small : i < 256) :
    pathBit (spread position) i = position.testBit i := by
  unfold pathBit spread
  rw [testBit_ofBits _ 256 _ (pathIndex_lt small), pathIndex_involutive]

/-- A sequence id with a position folded into its leading path bits. -/
def fold (seq position : Nat) : Nat := seq ^^^ spread position

theorem fold_lt {seq : Nat} (small : seq < 2 ^ 256) (position : Nat) : fold seq position < 2 ^ 256 :=
  Nat.xor_lt_two_pow small (spread_lt position)

theorem fold_lt_octets {seq : Nat} (small : seq < 256 ^ 32) (position : Nat) : fold seq position < 256 ^ 32 := by
  have width : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  rw [width] at small ⊢
  exact fold_lt small position

/-- With the position known, the fold determines the id. -/
theorem fold_cancel {a b position : Nat} (same : fold a position = fold b position) : a = b := by
  have undo : ∀ s, (fold s position) ^^^ spread position = s := fun s => by
    unfold fold; rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [← undo a, same, undo b]

theorem pathBit_fold (seq position : Nat) {i : Nat} (small : i < 256) :
    pathBit (fold seq position) i = (pathBit seq i ^^ position.testBit i) := by
  rw [← pathBit_spread position small]
  unfold pathBit fold
  exact Nat.testBit_xor ..

/-- **The bound.** Two different positions below `2 ^ k` give paths that differ within their
first `k` bits, whatever the id they are folded into. -/
theorem fold_diverge (seq : Nat) {p q k : Nat} (differ : p ≠ q) (pSmall : p < 2 ^ k) (qSmall : q < 2 ^ k)
    (fits : k ≤ 256) : ∃ i, i < k ∧ pathBit (fold seq p) i ≠ pathBit (fold seq q) i := by
  have ⟨i, bit⟩ : ∃ i, p.testBit i ≠ q.testBit i := by
    apply Classical.byContradiction
    intro none
    exact differ (Nat.eq_of_testBit_eq fun i => Classical.byContradiction fun h => none ⟨i, h⟩)
  have inside : i < k := by
    apply Classical.byContradiction
    intro outside
    have high : k ≤ i := Nat.le_of_not_lt outside
    exact bit ((Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le pSmall (Nat.pow_le_pow_right (by decide) high))).trans
      (Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le qSmall (Nat.pow_le_pow_right (by decide) high))).symm)
  refine ⟨i, inside, ?_⟩
  rw [pathBit_fold seq p (Nat.lt_of_lt_of_le inside fits), pathBit_fold seq q (Nat.lt_of_lt_of_le inside fits)]
  intro same
  apply bit
  cases hp : p.testBit i <;> cases hq : q.testBit i <;> simp_all

/-- **The bound is tight**: positions that agree on their low `k` bits share their first `k`
path bits. A sequence's items diverge by their positions and by nothing else. -/
theorem fold_shared (seq : Nat) {p q k : Nat} (agree : p % 2 ^ k = q % 2 ^ k) (fits : k ≤ 256) {i : Nat}
    (inside : i < k) : pathBit (fold seq p) i = pathBit (fold seq q) i := by
  have bits : p.testBit i = q.testBit i := by
    have low := congrArg (fun n => n.testBit i) agree
    simpa [Nat.testBit_mod_two_pow, inside] using low
  rw [pathBit_fold seq p (Nat.lt_of_lt_of_le inside fits), pathBit_fold seq q (Nat.lt_of_lt_of_le inside fits), bits]

namespace Example

/-- Position 1 sets the first path bit, position 2 the second. -/
theorem spread_small : pathBit (spread 1) 0 = true ∧ pathBit (spread 2) 0 = false ∧ pathBit (spread 2) 1 = true := by
  rw [pathBit_spread 1 (by decide : 0 < 256), pathBit_spread 2 (by decide : 0 < 256),
    pathBit_spread 2 (by decide : 1 < 256)]
  decide

/-- Positions 1 and 5 agree on their low two bits, so they share their first two path bits. -/
theorem shared_low : ∀ i, i < 2 → pathBit (fold 9 1) i = pathBit (fold 9 5) i :=
  fun _ inside => fold_shared 9 (by decide) (by decide) inside

theorem diverge_inhabited : ∃ i, i < 2 ∧ pathBit (fold 5 1) i ≠ pathBit (fold 5 2) i :=
  fold_diverge 5 (by decide) (by decide) (by decide) (by decide)

end Example

end Minidregg.Theory.SequenceSpread
