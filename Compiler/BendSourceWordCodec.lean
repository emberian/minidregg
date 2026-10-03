import Compiler.BendSourceCanonicalCodec
namespace Minidregg.Compiler.BendSourceRepresentation
set_option autoImplicit false

def bitsOf : Nat → Nat → List Bool
  | 0, _ => []
  | w + 1, n => decide (n % 2 = 1) :: bitsOf w (n / 2)

theorem bitsOf_length (w n : Nat) : (bitsOf w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [bitsOf, ih]

theorem wordValue_bitsOf (w n : Nat) (bound : n < 2 ^ w) :
    wordValue (bitsOf w n) = n := by
  induction w generalizing n with
  | zero => simp [bitsOf, wordValue] at *; omega
  | succ w ih =>
    have ht : n / 2 < 2 ^ w := by
      rw [pow_succ] at bound
      omega
    have hm : n % 2 < 2 := Nat.mod_lt n (by decide)
    have hd := Nat.mod_add_div n 2
    by_cases hb : n % 2 = 1 <;> simp [bitsOf, wordValue, ih (n / 2) ht, hb] <;> omega

theorem bitsOf_wordValue (bs : List Bool) : bitsOf bs.length (wordValue bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false =>
      have hm : (0 + 2 * wordValue bs) % 2 = 0 := by omega
      have hd : (0 + 2 * wordValue bs) / 2 = wordValue bs := by omega
      simp [List.length_cons, wordValue, bitsOf, hm, hd, ih]
    | true =>
      have hm : (1 + 2 * wordValue bs) % 2 = 1 := by omega
      have hd : (1 + 2 * wordValue bs) / 2 = wordValue bs := by omega
      simp [List.length_cons, wordValue, bitsOf, hm, hd, ih]

/-- Width is public and source-indexed. Oversized integers are refused before
any bit projection; admitted source Word arithmetic has a separate profile. -/
def encodeWord (width n : Nat) : Option BTerm :=
  if n < 2 ^ width then some (wordTerm (bitsOf width n)) else none

theorem encodeWord_roundtrip (width n : Nat) (bound : n < 2 ^ width) :
    ∃ bits, encodeWord width n = some (wordTerm bits) ∧
      RepWord width (wordTerm bits) bits ∧ wordValue bits = n := by
  exact ⟨bitsOf width n, by simp [encodeWord, bound],
    ⟨rfl, bitsOf_length width n⟩, wordValue_bitsOf width n bound⟩

theorem encodeWord_refuses (width n : Nat) (oversized : 2 ^ width ≤ n) :
    encodeWord width n = none := by simp [encodeWord, Nat.not_lt.mpr oversized]

def decodeWordAtWidth (width : Nat) (t : BTerm) : Option Nat := do
  let bits ← decodeWord t
  if bits.length = width then some (wordValue bits) else none

theorem decodeWordAtWidth_sound (width : Nat) (t : BTerm) (n : Nat)
    (h : decodeWordAtWidth width t = some n) :
    ∃ bits, RepWord width t bits ∧ wordValue bits = n ∧ n < 2 ^ width := by
  unfold decodeWordAtWidth at h
  cases hb : decodeWord t with
  | none => simp [hb] at h
  | some bits =>
    simp only [hb, Option.bind_some] at h
    split at h
    · rename_i hw
      cases h
      exact ⟨bits, ⟨decodeWord_sound t bits hb, hw⟩, rfl,
        hw ▸ wordValue_bound bits⟩
    · cases h

theorem decodeWordAtWidth_roundtrip (width n : Nat) (bound : n < 2 ^ width) :
    decodeWordAtWidth width (wordTerm (bitsOf width n)) = some n := by
  simp [decodeWordAtWidth, decode_wordTerm, bitsOf_length, wordValue_bitsOf width n bound]

theorem decodeWordAtWidth_refuses_wrong_width (width : Nat) (bits : List Bool)
    (wrong : bits.length ≠ width) :
    decodeWordAtWidth width (wordTerm bits) = none := by
  simp [decodeWordAtWidth, decode_wordTerm, wrong]

#assert_axioms decodeWordAtWidth_sound
#assert_axioms decodeWordAtWidth_roundtrip
#assert_axioms decodeWordAtWidth_refuses_wrong_width

#assert_axioms bitsOf_length
#assert_axioms wordValue_bitsOf
#assert_axioms bitsOf_wordValue
#assert_axioms encodeWord_roundtrip
#assert_axioms encodeWord_refuses
end Minidregg.Compiler.BendSourceRepresentation
