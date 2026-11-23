module

public import Init.Data.Nat.ToString
import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Host.Decimal

-- A chunk fits in a machine natural on the native host.
private def radix : Nat := 10 ^ 18

private def padded : Nat → Nat → List Char → List Char
  | 0, _, tail => tail
  | k + 1, r, tail => padded k (r / 10) ((r % 10).digitChar :: tail)

private theorem splitDigits (k q r : Nat) (hq : 0 < q) (hr : r < 10 ^ k) (tail : List Char) :
    Nat.toDigits 10 (10 ^ k * q + r) ++ tail = Nat.toDigits 10 q ++ padded k r tail := by
  induction k generalizing r tail with
  | zero =>
    have : r = 0 := by simpa using hr
    simp [this, padded]
  | succ k ih =>
    have hr' : r / 10 < 10 ^ k := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [Nat.pow_succ] using hr)
    have he : 10 ^ (k + 1) * q + r = 10 * (10 ^ k * q + r / 10) + r % 10 := by
      rw [Nat.pow_succ', Nat.mul_assoc, Nat.mul_add, Nat.add_assoc, Nat.div_add_mod]
    have hprefix : 0 < 10 ^ k * q + r / 10 := Nat.add_pos_left (Nat.mul_pos (Nat.pow_pos (by decide : 0 < 10)) hq) (r / 10)
    rw [he, ← Nat.toDigits_append_toDigits (by decide) hprefix (Nat.mod_lt _ (by decide)),
      Nat.toDigits_of_lt_base (Nat.mod_lt _ (by decide)), List.append_assoc]
    exact ih _ hr' _

private def digits (n : Nat) (tail : List Char) : List Char :=
  if _h : n < radix then n.repr.toList ++ tail
  else digits (n / radix) (padded 18 (n % radix) tail)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.lt_of_lt_of_le (by decide : 0 < radix) (Nat.le_of_not_gt _h)) (by decide)

private theorem digits_eq (n : Nat) (tail : List Char) :
    digits n tail = Nat.toDigits 10 n ++ tail := by
  induction n using Nat.strongRecOn generalizing tail with
  | _ n ih =>
    rw [digits]
    split
    · simp
    · rename_i large
      have hn : 0 < n / radix := Nat.div_pos (by omega) (by decide)
      rw [ih _ (Nat.div_lt_self (Nat.lt_of_lt_of_le (by decide : 0 < radix) (Nat.le_of_not_gt large)) (by decide))]
      have split := splitDigits 18 (n / radix) (n % radix) hn (Nat.mod_lt _ (by decide)) tail
      change Nat.toDigits 10 (radix * (n / radix) + n % radix) ++ tail = _ at split
      rw [Nat.div_add_mod] at split
      exact split.symm

/-- Decimal rendering for the large digests in a signed view. -/
def render (n : Nat) : String :=
  if n < radix then n.repr else String.ofList (digits n [])

theorem render_eq (n : Nat) : render n = toString n := by
  unfold render
  split
  · rfl
  · simp only [digits_eq, List.append_nil]
    exact Nat.toString_eq_ofList_toDigits.symm

#guard render 0 = "0"
#guard render 1000000000000000000000000000000000001 = "1000000000000000000000000000000000001"
#guard render 1000000000000000000 ≠ "1"

/-- info: 'Minidregg.Host.Decimal.render_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms render_eq

end Minidregg.Host.Decimal
