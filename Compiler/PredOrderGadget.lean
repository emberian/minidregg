/-
# Forced order indicators for the sole `Pred` lowering

Statement first: `ForcedIndicator` quantifies every prover assignment and requires
the output to equal the complete Boolean comparison, including false outcomes.
`WitnessAccepts` requires the executable binary witness to satisfy the same DSL
system. The focused companion supplies inhabited field/range premises and teeth.

For width `k`, range-decompose `2^k + present * (right - left)` into `k+1`
Boolean bits. The top bit is the order decision; multiply it by presence. Thus
absence means false without imposing a range on a missing operand. The actual
present source difference must satisfy `-2^k ≤ right-left < 2^k`. The inclusive
lower endpoint is valid; the upper endpoint is not. Reading bits as integers
also requires cast injectivity throughout `[0, 2^(k+1))` (`NoWrap`).

This module chooses neither a deployment field nor a product range. A receiving
profile must commit `k` and the field/semantics identity and check the bounds on
the actual source Int operands. Finite `castInjOn` on only mentioned values is
not a substitute. Values exceeding a scalar profile need a bounded-limb
extension, not a larger label on modular scalar arithmetic.

Every constraint below is composed from the existing AIR DSL and `rangeGadget`.
There is no second evaluator, Rust circuit, or positive-only slack assertion.
-/
import Compiler.AirRange

namespace Minidregg.Compiler.PredOrder

variable {F : Type} [Field F] {Idx : Type}

/-- The entire decomposition interval must embed without wrap. -/
def NoWrap (F : Type) [Field F] (k : Nat) : Prop :=
  ∀ m n : Nat, m < 2 ^ (k + 1) → n < 2 ^ (k + 1) →
    (m : F) = (n : F) → m = n

/-- Bounds apply to the actual compared integers, only when both operands exist. -/
def InputsInRange (k : Nat) (present : Bool) (a b : Int) : Prop :=
  present = true → -(2 : Int) ^ k ≤ b - a ∧ b - a < (2 : Int) ^ k

instance (k : Nat) (present : Bool) (a b : Int) :
    Decidable (InputsInRange k present a b) :=
  inferInstanceAs (Decidable
    (present = true → -(2 : Int) ^ k ≤ b - a ∧ b - a < (2 : Int) ^ k))

def sourceDelta (present : Bool) (a b : Int) : Int :=
  if present then b - a else 0

def shiftedNat (k : Nat) (present : Bool) (a b : Int) : Nat :=
  (sourceDelta present a b + (2 : Int) ^ k).toNat

/-- Canonical binary digits; this is executable witness generation, not a choice. -/
def binaryDigits : (width : Nat) → Nat → Fin width → Nat
  | 0, _, i => i.elim0
  | width + 1, n, i => Fin.cases (n % 2) (binaryDigits width (n / 2)) i

/-- Source-owned shifted difference, normalized to `2^k` when absent. -/
def shiftedTerm (k : Nat) (present left right : Term (AirSig F Idx)) :
    Term (AirSig F Idx) :=
  add' (cst ((2 : F) ^ k))
    (mul' present (add' right (mul' (cst (-1)) left)))

/-- One range gadget and one equality tying its value to the actual input terms. -/
def gadget (k : Nat) (present left right : Term (AirSig F Idx))
    (shifted : Idx) (bits : Fin (k + 1) → Idx) : ConstraintSystem F Idx :=
  rangeGadget shifted bits ++
    [add' (vr shifted) (mul' (cst (-1)) (shiftedTerm k present left right))]

def indicator (k : Nat) (present : Term (AirSig F Idx))
    (bits : Fin (k + 1) → Idx) : Term (AirSig F Idx) :=
  mul' present (vr (bits (Fin.last k)))

/-- The soundness statement includes both polarities and quantifies all auxiliaries. -/
def ForcedIndicator (k : Nat) (present left right : Term (AirSig F Idx))
    (shifted : Idx) (bits : Fin (k + 1) → Idx) : Prop :=
  ∀ (asg : Idx → F) (isPresent : Bool) (a b : Int),
    NoWrap F k → InputsInRange k isPresent a b →
    eval asg present = (if isPresent then 1 else 0) →
    eval asg left = (a : F) → eval asg right = (b : F) →
    systemAccepts asg (gadget k present left right shifted bits) →
    eval asg (indicator k present bits) =
      if isPresent && decide (a ≤ b) then 1 else 0

/-- Completeness pins only the actual source inputs and the canonical auxiliaries. -/
def WitnessAccepts (k : Nat) (present left right : Term (AirSig F Idx))
    (shifted : Idx) (bits : Fin (k + 1) → Idx) : Prop :=
  ∀ (asg : Idx → F) (isPresent : Bool) (a b : Int),
    InputsInRange k isPresent a b →
    eval asg present = (if isPresent then 1 else 0) →
    eval asg left = (a : F) → eval asg right = (b : F) →
    asg shifted = (shiftedNat k isPresent a b : F) →
    (∀ i, asg (bits i) = (binaryDigits (k + 1) (shiftedNat k isPresent a b) i : F)) →
    systemAccepts asg (gadget k present left right shifted bits)

theorem noWrap_zmod {p k : Nat} [Fact p.Prime] (hp : 2 ^ (k + 1) ≤ p) :
    NoWrap (ZMod p) k := by
  intro m n hm hn heq
  have hv := congrArg ZMod.val heq
  simpa only [ZMod.val_natCast_of_lt (lt_of_lt_of_le hm hp),
    ZMod.val_natCast_of_lt (lt_of_lt_of_le hn hp)] using hv

theorem binaryDigits_le_one (width n : Nat) :
    ∀ i, binaryDigits width n i ≤ 1 := by
  induction width generalizing n with
  | zero => intro i; exact i.elim0
  | succ width ih =>
    refine Fin.cases ?_ ?_
    · simp only [binaryDigits, Fin.cases_zero]; omega
    · intro i
      simpa only [binaryDigits, Fin.cases_succ] using ih (n / 2) i

theorem binaryDigits_sum (width n : Nat) (hn : n < 2 ^ width) :
    n = ∑ i : Fin width, binaryDigits width n i * 2 ^ (i : Nat) := by
  induction width generalizing n with
  | zero => have : n = 0 := by simpa using Nat.lt_one_iff.mp hn
            simp [this]
  | succ width ih =>
    have hhalf : n / 2 < 2 ^ width := by
      have := pow_succ 2 width
      omega
    have hsum := ih (n / 2) hhalf
    rw [Fin.sum_univ_succ]
    simp only [binaryDigits, Fin.cases_zero, Fin.cases_succ, Fin.val_zero,
      pow_zero, mul_one, Fin.val_succ]
    have hshift :
        ∑ i : Fin width, binaryDigits width (n / 2) i * 2 ^ ((i : Nat) + 1) =
          (∑ i : Fin width, binaryDigits width (n / 2) i * 2 ^ (i : Nat)) * 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
    rw [hshift, ← hsum]
    omega

/-- The top binary digit is forced by integer magnitude, for every bit assignment. -/
theorem top_digit_forced {k n : Nat} (d : Fin (k + 1) → Nat)
    (hd : ∀ i, d i ≤ 1) (hsum : n = ∑ i, d i * 2 ^ (i : Nat)) :
    d (Fin.last k) = if 2 ^ k ≤ n then 1 else 0 := by
  have hlo : (∑ i : Fin k, d i.castSucc * 2 ^ (i : Nat)) < 2 ^ k :=
    boolDigit_sum_lt (fun i : Fin k => d i.castSucc) (fun i => hd _)
  rw [Fin.sum_univ_castSucc] at hsum
  simp only [Fin.val_castSucc, Fin.val_last] at hsum
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hd (Fin.last k)) with hzero | hone
  · have hn : n < 2 ^ k := by rw [hzero] at hsum; omega
    simp [hzero, Nat.not_le.mpr hn]
  · have hn : 2 ^ k ≤ n := by rw [hone] at hsum; omega
    simp [hone, hn]

theorem shifted_int_bounds {k : Nat} {present : Bool} {a b : Int}
    (h : InputsInRange k present a b) :
    0 ≤ sourceDelta present a b + (2 : Int) ^ k ∧
      sourceDelta present a b + (2 : Int) ^ k < (2 : Int) ^ (k + 1) := by
  have hpos : 0 < (2 : Int) ^ k := pow_pos (by decide) _
  cases hp : present with
  | false => simp only [sourceDelta, Bool.false_eq_true, ↓reduceIte, zero_add]
             rw [pow_succ]
             constructor <;> omega
  | true =>
    obtain ⟨hlo, hhi⟩ := h hp
    simp only [sourceDelta, ↓reduceIte]
    rw [pow_succ]
    constructor <;> omega

theorem shiftedNat_spec {k : Nat} {present : Bool} {a b : Int}
    (h : InputsInRange k present a b) :
    (shiftedNat k present a b : Int) = sourceDelta present a b + (2 : Int) ^ k :=
  Int.toNat_of_nonneg (shifted_int_bounds h).1

theorem shiftedNat_lt {k : Nat} {present : Bool} {a b : Int}
    (h : InputsInRange k present a b) :
    shiftedNat k present a b < 2 ^ (k + 1) := by
  have hi : (shiftedNat k present a b : Int) < (2 : Int) ^ (k + 1) := by
    rw [shiftedNat_spec h]
    exact (shifted_int_bounds h).2
  exact_mod_cast hi

theorem shiftedNat_cast {k : Nat} {present : Bool} {a b : Int}
    (h : InputsInRange k present a b) :
    (shiftedNat k present a b : F) = (sourceDelta present a b : F) + (2 : F) ^ k := by
  have hf := congrArg (fun x : Int => (x : F)) (shiftedNat_spec h)
  simpa only [Int.cast_natCast, Int.cast_add, Int.cast_pow, Int.cast_ofNat] using hf

theorem shiftedNat_threshold {k : Nat} {a b : Int}
    (h : InputsInRange k true a b) :
    2 ^ k ≤ shiftedNat k true a b ↔ a ≤ b := by
  have hs := shiftedNat_spec h
  simp only [sourceDelta, ↓reduceIte] at hs
  constructor
  · intro hn
    have hi : ((2 ^ k : Nat) : Int) ≤ (shiftedNat k true a b : Int) := by
      exact_mod_cast hn
    push_cast at hi
    omega
  · intro hab
    have hi : ((2 ^ k : Nat) : Int) ≤ (shiftedNat k true a b : Int) := by
      push_cast
      omega
    exact_mod_cast hi

theorem shiftedTerm_eval {k : Nat} {asg : Idx → F}
    {present left right : Term (AirSig F Idx)} {isPresent : Bool} {a b : Int}
    (hp : eval asg present = (if isPresent then 1 else 0))
    (ha : eval asg left = (a : F)) (hb : eval asg right = (b : F)) :
    eval asg (shiftedTerm k present left right) =
      (sourceDelta isPresent a b : F) + (2 : F) ^ k := by
  simp only [shiftedTerm, eval_add', eval_mul', eval_cst, hp, ha, hb]
  cases isPresent <;> simp [sourceDelta]
  ring

theorem gadget_correct (k : Nat) (asg : Idx → F)
    (present left right : Term (AirSig F Idx))
    (shifted : Idx) (bits : Fin (k + 1) → Idx) :
    systemAccepts asg (gadget k present left right shifted bits) ↔
      systemAccepts asg (rangeGadget shifted bits) ∧
        asg shifted = eval asg (shiftedTerm k present left right) := by
  simp only [gadget, systemAccepts_append, systemAccepts_cons,
    systemAccepts_nil, and_true, accepts, eval_add', eval_mul', eval_vr, eval_cst,
    neg_one_mul, add_neg_eq_zero]

/-- Field-generic integer lift: every accepted decomposition has the correct top bit. -/
theorem range_top_forced {k n : Nat} {asg : Idx → F}
    {shifted : Idx} {bits : Fin (k + 1) → Idx}
    (hnw : NoWrap F k) (hn : n < 2 ^ (k + 1))
    (hshift : asg shifted = (n : F))
    (h : systemAccepts asg (rangeGadget shifted bits)) :
    asg (bits (Fin.last k)) = if 2 ^ k ≤ n then 1 else 0 := by
  classical
  obtain ⟨hbool, hsum⟩ := (rangeGadget_correct asg shifted bits).mp h
  let d : Fin (k + 1) → Nat := fun i => if asg (bits i) = 1 then 1 else 0
  have hd : ∀ i, d i ≤ 1 := by intro i; dsimp [d]; split <;> omega
  have hfield : (n : F) = ((∑ i, d i * 2 ^ (i : Nat) : Nat) : F) := by
    rw [← hshift, hsum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hbool i with hzero | hone
    · simp [d, hzero]
    · simp [d, hone]
  have hnat := hnw n (∑ i, d i * 2 ^ (i : Nat)) hn (boolDigit_sum_lt d hd) hfield
  have htop := top_digit_forced d hd hnat
  have hbit : asg (bits (Fin.last k)) = (d (Fin.last k) : F) := by
    rcases hbool (Fin.last k) with hzero | hone
    · simp [d, hzero]
    · simp [d, hone]
  rw [hbit, htop]
  split <;> simp

/-- Universal soundness: malicious auxiliary values cannot flip either polarity. -/
theorem forced (k : Nat) (present left right : Term (AirSig F Idx))
    (shifted : Idx) (bits : Fin (k + 1) → Idx) :
    ForcedIndicator k present left right shifted bits := by
  intro asg isPresent a b hnw hr hp ha hb h
  cases isPresent with
  | false => simp [indicator, hp]
  | true =>
    obtain ⟨hRange, hbind⟩ := (gadget_correct k asg present left right shifted bits).mp h
    have hshift : asg shifted = (shiftedNat k true a b : F) := by
      rw [hbind, shiftedTerm_eval hp ha hb, shiftedNat_cast hr]
    have htop := range_top_forced hnw (shiftedNat_lt hr) hshift hRange
    simp only [shiftedNat_threshold hr] at htop
    simpa only [indicator, eval_mul', eval_vr, hp, ↓reduceIte, one_mul,
      Bool.true_and, decide_eq_true_eq] using htop

/-- The executable witness satisfies the very same constraints, for true and false alike. -/
theorem complete (k : Nat) (present left right : Term (AirSig F Idx))
    (shifted : Idx) (bits : Fin (k + 1) → Idx) :
    WitnessAccepts k present left right shifted bits := by
  intro asg isPresent a b hr hp ha hb hshift hbits
  apply (gadget_correct k asg present left right shifted bits).mpr
  constructor
  · apply (rangeGadget_correct asg shifted bits).mpr
    constructor
    · intro i
      rw [hbits]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp
        (binaryDigits_le_one (k + 1) (shiftedNat k isPresent a b) i) with hzero | hone
      · left; simp [hzero]
      · right; simp [hone]
    · rw [hshift]
      have hs := congrArg (fun n : Nat => (n : F))
        (binaryDigits_sum (k + 1) (shiftedNat k isPresent a b) (shiftedNat_lt hr))
      push_cast at hs
      simpa only [hbits] using hs
  · rw [hshift, shiftedNat_cast hr, shiftedTerm_eval hp ha hb]

/-- Every attempted polarity flip is refused, independent of the chosen auxiliaries. -/
theorem wrong_indicator_refused {k : Nat} {asg : Idx → F}
    {present left right : Term (AirSig F Idx)} {shifted : Idx}
    {bits : Fin (k + 1) → Idx} {isPresent : Bool} {a b : Int}
    (hnw : NoWrap F k) (hr : InputsInRange k isPresent a b)
    (hp : eval asg present = (if isPresent then 1 else 0))
    (ha : eval asg left = (a : F)) (hb : eval asg right = (b : F))
    (hwrong : eval asg (indicator k present bits) ≠
      if isPresent && decide (a ≤ b) then 1 else 0) :
    ¬ systemAccepts asg (gadget k present left right shifted bits) := by
  intro h
  exact hwrong (forced k present left right shifted bits asg isPresent a b hnw hr hp ha hb h)

end Minidregg.Compiler.PredOrder
