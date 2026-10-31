/-
# Theory.NatDigits255Fast -- base-255 digits on machine words, proved equal to `Nat.digits 255`

The stream codec writes a natural as its base-255 digits (`Nat.digits 255`)
followed by a terminator byte.  `Nat.digits` divides the whole number by 255
once per digit; on a 256-bit digest that is thirty-two big-number divisions
and allocations per encoded digest, and the Host encodes digests on every
root it computes.

`digitsBytes` splits the number into chunks of `255 ^ 7` (below `2 ^ 57`) with
one big-number division per chunk, and writes each chunk's seven digits with
`UInt64` arithmetic.  `digitsBytes_eq` proves it equal to
`(Nat.digits 255 n).map UInt8.ofNat` for every `n`; the stream codec attaches
it with `@[csimp]` (`Theory/StreamCodec.lean`). Candidate-independent (Mathlib only), so it
lives in `Theory/`; the namespace stays `Minidregg.Compiler.NatDigits255Fast` until the
namespace-rename follow-up.
-/

module

public import Mathlib.Data.Nat.Digits.Lemmas

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Compiler.NatDigits255Fast

set_option autoImplicit false

/-- `255 ^ 7`. -/
def chunk : Nat := 70110209207109375

theorem chunk_eq : chunk = 255 ^ 7 := by decide

/-- Exactly `k` base-255 digits of `r`, least significant first. -/
def fixedDigits : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, r => r % 255 :: fixedDigits k (r / 255)

theorem fixedDigits_zero (k : Nat) : fixedDigits k 0 = List.replicate k 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [fixedDigits, ih, List.replicate_succ]

/-- The digits of `r < 255 ^ k`, padded with zeros to length `k`, are its `k`
fixed digits. -/
theorem padded_eq_fixedDigits (k r : Nat) (h : r < 255 ^ k) :
    Nat.digits 255 r ++ List.replicate (k - (Nat.digits 255 r).length) 0 = fixedDigits k r := by
  induction k generalizing r with
  | zero =>
      have : r = 0 := by simpa using h
      subst this
      rfl
  | succ k ih =>
      by_cases hr : r = 0
      · subst hr
        simp [fixedDigits, fixedDigits_zero, List.replicate_succ]
      · rw [Nat.digits_def' (by decide) (Nat.pos_of_ne_zero hr)]
        have hq : r / 255 < 255 ^ k := by
          rw [Nat.div_lt_iff_lt_mul (by decide)]
          rw [Nat.pow_succ] at h
          exact h
        simp only [List.length_cons, List.cons_append, fixedDigits]
        rw [show k + 1 - ((Nat.digits 255 (r / 255)).length + 1) =
          k - (Nat.digits 255 (r / 255)).length by omega]
        rw [ih _ hq]

/-- Base-255 digits of a word, least significant first. -/
def smallDigits (x : UInt64) : List UInt8 :=
  if x = 0 then [] else (x % 255).toUInt8 :: smallDigits (x / 255)
termination_by x.toNat
decreasing_by
  rw [UInt64.toNat_div]
  have hx : x.toNat ≠ 0 := fun h => ‹¬x = 0› (UInt64.toNat_inj.mp (by simpa using h))
  have : (255 : UInt64).toNat = 255 := rfl
  rw [this]
  omega

theorem toUInt8_mod255 (x : UInt64) : (x % 255).toUInt8 = UInt8.ofNat (x.toNat % 255) := by
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt64.toNat_mod, UInt8.toNat_ofNat']
  rfl

theorem smallDigits_eq (x : UInt64) :
    smallDigits x = (Nat.digits 255 x.toNat).map UInt8.ofNat := by
  suffices h : ∀ m, ∀ x : UInt64, x.toNat = m →
      smallDigits x = (Nat.digits 255 x.toNat).map UInt8.ofNat from h _ x rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro x hm
      rw [smallDigits]
      by_cases hx : x = 0
      · subst hx
        simp
      · rw [if_neg hx]
        have hpos : 0 < x.toNat := by
          rcases Nat.eq_zero_or_pos x.toNat with h | h
          · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hx
          · exact h
        have hdiv : (x / 255).toNat = x.toNat / 255 := by
          rw [UInt64.toNat_div]
          rfl
        rw [ih (x / 255).toNat (by rw [hdiv, ← hm]; omega) (x / 255) rfl]
        rw [Nat.digits_def' (by decide) hpos, List.map_cons, toUInt8_mod255, hdiv]

/-- `k` base-255 digits of a word, then `rest`. -/
def fixedWord : Nat → UInt64 → List UInt8 → List UInt8
  | 0, _, rest => rest
  | k + 1, x, rest => (x % 255).toUInt8 :: fixedWord k (x / 255) rest

theorem fixedWord_eq (k : Nat) (x : UInt64) (rest : List UInt8) :
    fixedWord k x rest = (fixedDigits k x.toNat).map UInt8.ofNat ++ rest := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [fixedWord, ih, fixedDigits, List.map_cons, List.cons_append, toUInt8_mod255,
        UInt64.toNat_div]
      rfl

/-- `(Nat.digits 255 n).map UInt8.ofNat`, one big division per seven digits. A word-sized
natural takes the machine path straight away; the test is a shift, never a comparison
with a literal above `2 ^ 32`, which the compiler would rebuild from its decimal string
on every call. -/
def digitsBytes (n : Nat) : List UInt8 :=
  if n >>> 63 = 0 then smallDigits n.toUInt64
  else fixedWord 7 (n % chunk).toUInt64 (digitsBytes (n / chunk))
termination_by n
decreasing_by
  rename_i big
  have pos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at big)
  exact Nat.div_lt_self pos (by decide)

theorem toNat_toUInt64_of_lt (n : Nat) (h : n < chunk) : n.toUInt64.toNat = n := by
  rw [Nat.toUInt64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))

/-- **The refinement**: for every natural, the chunked word digits are the
base-255 digits. -/
theorem digitsBytes_eq (n : Nat) : digitsBytes n = (Nat.digits 255 n).map UInt8.ofNat := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rw [digitsBytes]
      by_cases word : n >>> 63 = 0
      · have small : n < 2 ^ 63 := by
          rw [Nat.shiftRight_eq_div_pow] at word
          exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos 63)).mp word
        rw [if_pos word, smallDigits_eq, Nat.toUInt64, UInt64.toNat_ofNat',
          Nat.mod_eq_of_lt (Nat.lt_trans small (by decide))]
      · rw [if_neg word]
        have hn : ¬ n < chunk := by
          intro below
          apply word
          rw [Nat.shiftRight_eq_div_pow]
          exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos 63)).mpr (Nat.lt_trans below (by decide))
        have hc : 0 < chunk := by decide
        have hq : 0 < n / chunk := Nat.div_pos (by omega) hc
        have hr : n % chunk < chunk := Nat.mod_lt _ hc
        rw [fixedWord_eq, toNat_toUInt64_of_lt _ hr, ih (n / chunk) (Nat.div_lt_self (by omega)
          (by decide)), ← padded_eq_fixedDigits 7 _ (by rw [← chunk_eq]; exact hr)]
        have hlen : (Nat.digits 255 (n % chunk)).length ≤ 7 := by
          rw [Nat.digits_length_le_iff (by decide)]
          rw [← chunk_eq]; exact hr
        rw [← List.map_append, Nat.digits_append_zeroes_append_digits (by decide) hq]
        rw [show (Nat.digits 255 (n % chunk)).length + (7 - (Nat.digits 255 (n % chunk)).length) = 7
          by omega, ← chunk_eq, Nat.mod_add_div]

end Minidregg.Compiler.NatDigits255Fast

/-- info: 'Minidregg.Compiler.NatDigits255Fast.digitsBytes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.NatDigits255Fast.digitsBytes_eq
