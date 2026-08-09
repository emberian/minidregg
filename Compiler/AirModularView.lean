/-
# `Compiler/AirModularView.lean` — an exact fixed-width modular view in AIR

For a fixed public natural modulus `q`, this module realizes the nonnegative relation

`x = r + k*q`  and  `r < q`

inside the compiler's existing `ConstraintSystem`/`emit` path.  A range-checked
schoolbook constant multiplication produces `k*q`; `AirBignum.addGadget` adds the
remainder; and a second addition `r + slack = q-1` proves the strict remainder bound.
All words and multiplication carries are fixed-width little-endian radix-`2^limbBits`
vectors.  The soundness theorem states the precise prime-field no-wrap hypotheses.

This is deliberately only the unsigned constant-modulus primitive.  Signed
coefficients, a multi-coefficient compressed-linear-equation frontend, the FHEgg
schema (including rounding/noise), dynamic moduli, and generated execution authority remain the
named deployment residual; no such claim is hidden in this gadget.  The complete
remainder comparator below uses a one-limb modulus (`q < base`).  A separately proved
scalar-times-multi-limb-constant block covers the BFV-scale `q0`; composing that block
with the comparator for a full wide-modulus `ModularView` is also an explicit residual.
-/
import Compiler.AirBignum
import Compiler.EmitSerialize
import Theory.CrossModulus

namespace Minidregg.Compiler.AirModularView

open Minidregg.Compiler
open Minidregg.Theory

set_option autoImplicit false

universe u

variable {F : Type u} [Field F] {Idx : Type u}
variable {width limbBits : Nat}

/-- Wires for `product = k*q`, `x = r+product`, and `r+slack = q-1`. -/
structure ModularWires (Idx : Type u) (width limbBits : Nat) where
  x : Fin width -> Idx
  r : Fin width -> Idx
  k : Fin width -> Idx
  product : Fin width -> Idx
  xBit : Fin width -> Fin limbBits -> Idx
  rBit : Fin width -> Fin limbBits -> Idx
  kBit : Fin width -> Fin limbBits -> Idx
  productBit : Fin width -> Fin limbBits -> Idx
  mulCarry : Fin (width + 1) -> Idx
  mulCarryBit : Fin (width + 1) -> Fin limbBits -> Idx
  sumCarry : Fin (width + 1) -> Idx
  slack : Fin width -> Idx
  slackBit : Fin width -> Fin limbBits -> Idx
  bound : Fin width -> Idx
  boundBit : Fin width -> Fin limbBits -> Idx
  remCarry : Fin (width + 1) -> Idx

/-- The existing addition gadget, viewed as `r + product = x`. -/
def sumWires (w : ModularWires Idx width limbBits) :
    AirBignum.AddWires Idx width limbBits where
  x := w.r
  y := w.product
  z := w.x
  xBit := w.rBit
  yBit := w.productBit
  zBit := w.xBit
  carry := w.sumCarry

/-- The existing addition gadget, viewed as `r + slack = q-1`. -/
def remainderWires (w : ModularWires Idx width limbBits) :
    AirBignum.AddWires Idx width limbBits where
  x := w.r
  y := w.slack
  z := w.bound
  xBit := w.rBit
  yBit := w.slackBit
  zBit := w.boundBit
  carry := w.remCarry

/-- One schoolbook limb of multiplication by the public natural constant `q`. -/
def mulConstLimbTerm (q : Nat) (w : ModularWires Idx width limbBits)
    (i : Fin width) : Term (AirSig F Idx) :=
  add'
    (add' (mul' (cst (q : F)) (vr (w.k i))) (vr (w.mulCarry i.castSucc)))
    (mul' (cst (-1))
      (add' (vr (w.product i))
        (mul' (cst ((2 : F) ^ limbBits)) (vr (w.mulCarry i.succ)))))

/-- Pointwise constant-multiplication equations. -/
def mulConstEquationSystem (q : Nat) (w : ModularWires Idx width limbBits) :
    ConstraintSystem F Idx :=
  (List.finRange width).map fun i => mulConstLimbTerm q w i

/-- Multiplication by `q`, with range-checked input, product, and carry limbs. -/
def mulConstGadget (q : Nat) (w : ModularWires Idx width limbBits) :
    ConstraintSystem F Idx :=
  AirBignum.limbRangeSystem w.k w.kBit ++
  AirBignum.limbRangeSystem w.product w.productBit ++
  AirBignum.limbRangeSystem w.mulCarry w.mulCarryBit ++
  [vr (w.mulCarry 0), vr (w.mulCarry (Fin.last width))] ++
  mulConstEquationSystem q w

/-- The canonical little-endian digit at position `i`. -/
def constDigit (base width value : Nat) (i : Fin width) : Nat :=
  (Bignum.digitsLE base width value).get
    (Fin.cast (Bignum.digitsLE_length base width value).symm i)

/-- Pin a word limbwise to a fixed natural's canonical digit vector. -/
def pinWordSystem (value : Nat) (word : Fin width -> Idx) : ConstraintSystem F Idx :=
  (List.finRange width).map fun i =>
    add' (vr (word i)) (cst (-(constDigit (2 ^ limbBits) width value i : F)))

/-- The complete modular-view gadget.  The last block pins `bound` to `q-1`. -/
def modularViewGadget (q : Nat) (w : ModularWires Idx width limbBits) :
    ConstraintSystem F Idx :=
  mulConstGadget q w ++
  AirBignum.addGadget (sumWires w) ++
  AirBignum.addGadget (remainderWires w) ++
  pinWordSystem (limbBits := limbBits) (q - 1) w.bound

/-! ## Exact field readings -/

theorem mulConstLimbTerm_correct (asg : Idx -> F) (q : Nat)
    (w : ModularWires Idx width limbBits) (i : Fin width) :
    accepts asg (mulConstLimbTerm q w i) <->
      (q : F) * asg (w.k i) + asg (w.mulCarry i.castSucc) =
        asg (w.product i) + (2 : F) ^ limbBits * asg (w.mulCarry i.succ) := by
  unfold accepts mulConstLimbTerm
  simp only [eval_add', eval_mul', eval_cst, eval_vr]
  constructor <;> intro h <;> linear_combination h

theorem mulConstEquationSystem_correct (asg : Idx -> F) (q : Nat)
    (w : ModularWires Idx width limbBits) :
    systemAccepts asg (mulConstEquationSystem q w) <->
      forall i, (q : F) * asg (w.k i) + asg (w.mulCarry i.castSucc) =
        asg (w.product i) + (2 : F) ^ limbBits * asg (w.mulCarry i.succ) := by
  constructor
  · intro h i
    exact (mulConstLimbTerm_correct asg q w i).mp
      (h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  · intro h t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact (mulConstLimbTerm_correct asg q w i).mpr (h i)

theorem mulConstGadget_correct (asg : Idx -> F) (q : Nat)
    (w : ModularWires Idx width limbBits) :
    systemAccepts asg (mulConstGadget q w) <->
      (forall i, systemAccepts asg (rangeGadget (w.k i) (w.kBit i))) /\
      (forall i, systemAccepts asg (rangeGadget (w.product i) (w.productBit i))) /\
      (forall i, systemAccepts asg (rangeGadget (w.mulCarry i) (w.mulCarryBit i))) /\
      asg (w.mulCarry 0) = 0 /\
      asg (w.mulCarry (Fin.last width)) = 0 /\
      (forall i, (q : F) * asg (w.k i) + asg (w.mulCarry i.castSucc) =
        asg (w.product i) + (2 : F) ^ limbBits * asg (w.mulCarry i.succ)) := by
  rw [mulConstGadget, systemAccepts_append, systemAccepts_append,
    systemAccepts_append, systemAccepts_append, AirBignum.limbRangeSystem_correct,
    AirBignum.limbRangeSystem_correct, AirBignum.limbRangeSystem_correct,
    mulConstEquationSystem_correct]
  simp only [systemAccepts_cons, systemAccepts_nil, and_true, accepts, eval_vr]
  tauto

theorem pinWordSystem_correct (asg : Idx -> F) (value : Nat)
    (word : Fin width -> Idx) :
    systemAccepts asg (pinWordSystem (F := F) (limbBits := limbBits) value word) <->
      forall i, asg (word i) = (constDigit (2 ^ limbBits) width value i : F) := by
  constructor
  · intro h i
    have hi := h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    unfold accepts at hi
    simp only [eval_add', eval_vr, eval_cst, add_neg_eq_zero] at hi
    exact hi
  · intro h t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    unfold accepts
    simp only [eval_add', eval_vr, eval_cst, h i, add_neg_eq_zero]

theorem modularViewGadget_correct (asg : Idx -> F) (q : Nat)
    (w : ModularWires Idx width limbBits) :
    systemAccepts asg (modularViewGadget q w) <->
      systemAccepts asg (mulConstGadget q w) /\
      systemAccepts asg (AirBignum.addGadget (sumWires w)) /\
      systemAccepts asg (AirBignum.addGadget (remainderWires w)) /\
      (forall i, asg (w.bound i) =
        (constDigit (2 ^ limbBits) width (q - 1) i : F)) := by
  rw [modularViewGadget, systemAccepts_append, systemAccepts_append,
    systemAccepts_append, pinWordSystem_correct]
  tauto

/-! ## Natural-number lift and soundness -/

/-- Constant-multiplication carry equations telescope over little-endian denotation. -/
theorem mulCarryEquations_denote (base q : Nat) :
    forall {n : Nat} (k product : Fin n -> Nat) (carry : Fin (n + 1) -> Nat),
      (forall i, q * k i + carry i.castSucc = product i + base * carry i.succ) ->
      Bignum.denoteNat base (List.ofFn product) + base ^ n * carry (Fin.last n) =
        q * Bignum.denoteNat base (List.ofFn k) + carry 0 := by
  intro n
  induction n with
  | zero =>
      intro k product carry _
      simp
  | succ n ih =>
      intro k product carry heq
      have hlow := heq (0 : Fin (n + 1))
      have htail := ih (fun i => k i.succ) (fun i => product i.succ)
        (fun i => carry i.succ) (fun i => heq i.succ)
      simp only [List.ofFn_succ, Bignum.denoteNat_cons]
      rw [pow_succ]
      have hzero : (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) := by
        apply Fin.ext
        rfl
      rw [hzero] at hlow
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      dsimp only at htail
      rw [hlast] at htail
      nlinarith [hlow, htail]

private theorem nat_eq_of_zmod_eq {p a b : Nat} [NeZero p]
    (ha : a < p) (hb : b < p) (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] using hv

/-- Accepted multiplication is exact over the integers under the sharp schoolbook
no-wrap condition `base^2 <= p` and the one-limb constant condition `q < base`. -/
theorem mulConstGadget_sound {p q : Nat} [Fact p.Prime] {J : Type}
    (hq : q < 2 ^ limbBits) (hp : (2 ^ limbBits) ^ 2 <= p)
    (asg : J -> ZMod p) (w : ModularWires J width limbBits)
    (h : systemAccepts asg (mulConstGadget (F := ZMod p) q w)) :
    Bignum.Canonical (2 ^ limbBits) width (AirBignum.limbVals asg w.k) /\
    Bignum.Canonical (2 ^ limbBits) width (AirBignum.limbVals asg w.product) /\
    Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.product) =
      q * Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.k) := by
  let base := 2 ^ limbBits
  have hbasep : base <= p := by
    calc
      base <= base * base := Nat.le_mul_self base
      _ = base ^ 2 := by ring
      _ <= p := hp
  obtain ⟨hk, hprod, hcarry, hc0, hctop, heq⟩ :=
    (mulConstGadget_correct asg q w).mp h
  have ck := AirBignum.limbVals_canonical hbasep asg w.k w.kBit hk
  have cp := AirBignum.limbVals_canonical hbasep asg w.product w.productBit hprod
  refine ⟨ck, cp, ?_⟩
  have heqNat : forall i,
      q * (asg (w.k i)).val + (asg (w.mulCarry i.castSucc)).val =
        (asg (w.product i)).val + base * (asg (w.mulCarry i.succ)).val := by
    intro i
    have hklt := rangeGadget_val_lt hbasep asg (w.k i) (w.kBit i) (hk i)
    have hplt := rangeGadget_val_lt hbasep asg (w.product i) (w.productBit i) (hprod i)
    have hcin := rangeGadget_val_lt hbasep asg
      (w.mulCarry i.castSucc) (w.mulCarryBit i.castSucc) (hcarry i.castSucc)
    have hcout := rangeGadget_val_lt hbasep asg
      (w.mulCarry i.succ) (w.mulCarryBit i.succ) (hcarry i.succ)
    apply nat_eq_of_zmod_eq (p := p)
    · have hmul : q * (asg (w.k i)).val <= (base - 1) * (base - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      have hmax : (base - 1) * (base - 1) + (base - 1) < base ^ 2 := by
        let d := base - 1
        have hb : base = d + 1 := by dsimp [d]; omega
        change d * d + d < base ^ 2
        rw [hb]
        nlinarith
      have hside : q * (asg (w.k i)).val + (asg (w.mulCarry i.castSucc)).val <
          base ^ 2 := lt_of_le_of_lt (Nat.add_le_add hmul (by omega)) hmax
      exact lt_of_lt_of_le hside hp
    · have hmul : base * (asg (w.mulCarry i.succ)).val <= base * (base - 1) :=
        Nat.mul_le_mul_left base (by omega)
      have hmax : (base - 1) + base * (base - 1) < base ^ 2 := by
        let d := base - 1
        have hb : base = d + 1 := by dsimp [d]; omega
        change d + base * d < base ^ 2
        rw [hb]
        nlinarith
      have hside : (asg (w.product i)).val + base * (asg (w.mulCarry i.succ)).val <
          base ^ 2 := lt_of_le_of_lt (Nat.add_le_add (by omega) hmul) hmax
      exact lt_of_lt_of_le hside hp
    · simpa [base, ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
        using heq i
  have htel := mulCarryEquations_denote base q
    (fun i => (asg (w.k i)).val) (fun i => (asg (w.product i)).val)
    (fun i => (asg (w.mulCarry i)).val) heqNat
  have hc0v : (asg (w.mulCarry 0)).val = 0 := by rw [hc0]; exact ZMod.val_zero
  have hctopv : (asg (w.mulCarry (Fin.last width))).val = 0 := by
    rw [hctop]
    exact ZMod.val_zero
  simpa [base, AirBignum.limbVals, hc0v, hctopv] using htel

/-- Pinning canonical digits below capacity reconstructs exactly the pinned natural. -/
theorem denote_pinned_word {p value : Nat} [Fact p.Prime] {J : Type}
    (hbase : 0 < 2 ^ limbBits) (hbasep : 2 ^ limbBits <= p)
    (hvalue : value < (2 ^ limbBits) ^ width)
    (asg : J -> ZMod p) (word : Fin width -> J)
    (hpin : forall i, asg (word i) =
      (constDigit (2 ^ limbBits) width value i : ZMod p)) :
    Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg word) = value := by
  have hvals : AirBignum.limbVals asg word =
      Bignum.digitsLE (2 ^ limbBits) width value := by
    unfold AirBignum.limbVals
    apply List.ext_get
    · simp
    · intro n hnl hnr
      simp only [List.get_ofFn]
      let i : Fin width := ⟨n, by simpa using hnl⟩
      have hdigit : constDigit (2 ^ limbBits) width value i < 2 ^ limbBits :=
        Bignum.digitsLE_ranged hbase width value _
          (List.get_mem (Bignum.digitsLE (2 ^ limbBits) width value)
            (Fin.cast (Bignum.digitsLE_length (2 ^ limbBits) width value).symm i))
      change (asg (word i)).val = _
      rw [hpin i, ZMod.val_cast_of_lt (lt_of_lt_of_le hdigit hbasep)]
      rfl
  rw [hvals]
  exact Bignum.denoteNat_digitsLE hbase width value hvalue

/-- **Exact modular-view soundness.** Acceptance yields canonical fixed-width `x`, `r`,
and `k`, the integer identity `x = r + q*k`, and the canonical remainder inequality. -/
theorem modularViewGadget_sound {p q : Nat} [Fact p.Prime] {J : Type}
    (hqpos : 0 < q) (hq : q < 2 ^ limbBits)
    (hcapacity : q <= (2 ^ limbBits) ^ width)
    (hp : (2 ^ limbBits) ^ 2 <= p)
    (asg : J -> ZMod p) (w : ModularWires J width limbBits)
    (h : systemAccepts asg (modularViewGadget (F := ZMod p) q w)) :
    Bignum.Canonical (2 ^ limbBits) width (AirBignum.limbVals asg w.x) /\
    Bignum.Canonical (2 ^ limbBits) width (AirBignum.limbVals asg w.r) /\
    Bignum.Canonical (2 ^ limbBits) width (AirBignum.limbVals asg w.k) /\
    Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.x) =
      Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.r) +
        q * Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.k) /\
    Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.r) < q := by
  obtain ⟨hmul, hsum, hrem, hpin⟩ := (modularViewGadget_correct asg q w).mp h
  obtain ⟨ck, cprod, hprod⟩ := mulConstGadget_sound hq hp asg w hmul
  have hpadd : 2 * 2 ^ limbBits <= p := by
    have hb : 2 <= 2 ^ limbBits := by omega
    nlinarith [hp]
  obtain ⟨cr, -, cx, hsumNat⟩ := AirBignum.addGadget_sound hpadd asg (sumWires w) hsum
  obtain ⟨-, cslack, cbound, hremNat⟩ :=
    AirBignum.addGadget_sound hpadd asg (remainderWires w) hrem
  have hbase : 0 < 2 ^ limbBits := pow_pos (by omega) _
  have hbasep : 2 ^ limbBits <= p := by nlinarith [hp]
  have hqcap : q - 1 < (2 ^ limbBits) ^ width := by omega
  have hbound := denote_pinned_word hbase hbasep hqcap asg w.bound hpin
  change Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.x) =
    Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.r) +
      Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.product) at hsumNat
  change Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.bound) =
    Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.r) +
      Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.slack) at hremNat
  refine ⟨cx, cr, ck, ?_, ?_⟩
  · rw [hsumNat, hprod]
  · rw [hbound] at hremNat
    omega

/-- The exact theory-layer modular view extracted from the accepted one-limb-modulus
gadget.  This is a bridge to `Theory.CrossModulus`, not a second semantics. -/
theorem accepted_has_modularView {p q : Nat} [Fact p.Prime] {J : Type}
    (hqpos : 0 < q) (hq : q < 2 ^ limbBits)
    (hcapacity : q <= (2 ^ limbBits) ^ width)
    (hp : (2 ^ limbBits) ^ 2 <= p)
    (asg : J -> ZMod p) (w : ModularWires J width limbBits)
    (h : systemAccepts asg (modularViewGadget (F := ZMod p) q w)) :
    exists view : CrossModulus.ModularView q
        (Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.x)),
      view.residue = Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.r) /\
      view.quotient = Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.k) := by
  obtain ⟨-, -, -, heq, hr⟩ :=
    modularViewGadget_sound hqpos hq hcapacity hp asg w h
  refine ⟨{
    residue := Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.r)
    quotient := Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.k)
    residue_lt := hr
    recompose := ?_ }, rfl, rfl⟩
  simpa [Nat.mul_comm] using heq

/-! ## Wide public modulus, bounded scalar quotient

The full modular gadget above intentionally has `q < base`: every multiplication carry is
one base limb.  The following smaller primitive removes that restriction in the direction
needed by compressed-equation quotients.  It range-checks one `quotientBits`-bit scalar and
multiplies it by the *multi-limb* canonical constant encoding of any `q < base^width`.
The product and carries telescope exactly.  This covers an unsigned 24-bit quotient times
the 36-bit FHEgg modulus over BabyBear at radix 64; signed reconstruction remains outside
this unsigned primitive.
-/

variable {quotientBits : Nat}

/-- Wires for `product = scalar * q`, where `q` is compiled as `width` public digits. -/
structure ScalarMulWires (Idx : Type u) (width limbBits quotientBits : Nat) where
  scalar : Idx
  scalarBit : Fin quotientBits -> Idx
  product : Fin width -> Idx
  productBit : Fin width -> Fin limbBits -> Idx
  carry : Fin (width + 1) -> Idx
  carryBit : Fin (width + 1) -> Fin quotientBits -> Idx

/-- Canonical constant digits reconstruct the source natural exactly below capacity. -/
theorem constDigits_eq (base width value : Nat) :
    List.ofFn (constDigit base width value) = Bignum.digitsLE base width value := by
  apply List.ext_get
  · simp
  · intro n hn₁ hn₂
    simp only [List.get_ofFn]
    rfl

/-- One radix column of scalar multiplication by the compiled constant digit vector. -/
def scalarMulLimbTerm (modulus : Nat)
    (w : ScalarMulWires Idx width limbBits quotientBits) (i : Fin width) :
    Term (AirSig F Idx) :=
  add'
    (add'
      (mul' (cst (constDigit (2 ^ limbBits) width modulus i : F)) (vr w.scalar))
      (vr (w.carry i.castSucc)))
    (mul' (cst (-1))
      (add' (vr (w.product i))
        (mul' (cst ((2 : F) ^ limbBits)) (vr (w.carry i.succ)))))

def scalarMulEquationSystem (modulus : Nat)
    (w : ScalarMulWires Idx width limbBits quotientBits) : ConstraintSystem F Idx :=
  (List.finRange width).map fun i => scalarMulLimbTerm modulus w i

/-- Existing range gadgets plus boundary and schoolbook equations; no parallel IR. -/
def scalarMulGadget (modulus : Nat)
    (w : ScalarMulWires Idx width limbBits quotientBits) : ConstraintSystem F Idx :=
  rangeGadget w.scalar w.scalarBit ++
  AirBignum.limbRangeSystem w.product w.productBit ++
  AirBignum.limbRangeSystem w.carry w.carryBit ++
  [vr (w.carry 0), vr (w.carry (Fin.last width))] ++
  scalarMulEquationSystem modulus w

theorem scalarMulLimbTerm_correct (asg : Idx -> F) (modulus : Nat)
    (w : ScalarMulWires Idx width limbBits quotientBits) (i : Fin width) :
    accepts asg (scalarMulLimbTerm modulus w i) <->
      (constDigit (2 ^ limbBits) width modulus i : F) * asg w.scalar +
          asg (w.carry i.castSucc) =
        asg (w.product i) + (2 : F) ^ limbBits * asg (w.carry i.succ) := by
  unfold accepts scalarMulLimbTerm
  simp only [eval_add', eval_mul', eval_cst, eval_vr]
  constructor <;> intro h <;> linear_combination h

theorem scalarMulEquationSystem_correct (asg : Idx -> F) (modulus : Nat)
    (w : ScalarMulWires Idx width limbBits quotientBits) :
    systemAccepts asg (scalarMulEquationSystem modulus w) <->
      forall i, (constDigit (2 ^ limbBits) width modulus i : F) * asg w.scalar +
          asg (w.carry i.castSucc) =
        asg (w.product i) + (2 : F) ^ limbBits * asg (w.carry i.succ) := by
  constructor
  · intro h i
    exact (scalarMulLimbTerm_correct asg modulus w i).mp
      (h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  · intro h t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact (scalarMulLimbTerm_correct asg modulus w i).mpr (h i)

theorem scalarMulGadget_correct (asg : Idx -> F) (modulus : Nat)
    (w : ScalarMulWires Idx width limbBits quotientBits) :
    systemAccepts asg (scalarMulGadget modulus w) <->
      systemAccepts asg (rangeGadget w.scalar w.scalarBit) /\
      (forall i, systemAccepts asg (rangeGadget (w.product i) (w.productBit i))) /\
      (forall i, systemAccepts asg (rangeGadget (w.carry i) (w.carryBit i))) /\
      asg (w.carry 0) = 0 /\
      asg (w.carry (Fin.last width)) = 0 /\
      (forall i, (constDigit (2 ^ limbBits) width modulus i : F) * asg w.scalar +
          asg (w.carry i.castSucc) =
        asg (w.product i) + (2 : F) ^ limbBits * asg (w.carry i.succ)) := by
  rw [scalarMulGadget, systemAccepts_append, systemAccepts_append,
    systemAccepts_append, systemAccepts_append, AirBignum.limbRangeSystem_correct,
    AirBignum.limbRangeSystem_correct, scalarMulEquationSystem_correct]
  simp only [systemAccepts_cons, systemAccepts_nil, and_true, accepts, eval_vr]
  tauto

/-- Varying constant digits telescope to scalar multiplication of their denotation. -/
theorem scalarMulCarryEquations_denote (base scalar : Nat) :
    forall {n : Nat} (digit product : Fin n -> Nat) (carry : Fin (n + 1) -> Nat),
      (forall i, digit i * scalar + carry i.castSucc =
        product i + base * carry i.succ) ->
      Bignum.denoteNat base (List.ofFn product) + base ^ n * carry (Fin.last n) =
        scalar * Bignum.denoteNat base (List.ofFn digit) + carry 0 := by
  intro n
  induction n with
  | zero =>
      intro digit product carry _
      simp
  | succ n ih =>
      intro digit product carry heq
      have hlow := heq (0 : Fin (n + 1))
      have htail := ih (fun i => digit i.succ) (fun i => product i.succ)
        (fun i => carry i.succ) (fun i => heq i.succ)
      simp only [List.ofFn_succ, Bignum.denoteNat_cons]
      rw [pow_succ]
      have hzero : (0 : Fin (n + 1)).castSucc = (0 : Fin (n + 2)) := by
        apply Fin.ext
        rfl
      rw [hzero] at hlow
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      dsimp only at htail
      rw [hlast] at htail
      nlinarith [hlow, htail]

/-- **Wide-modulus integer soundness.** The two displayed inequalities are the exact
left/right field no-wrap budgets for a column. -/
theorem scalarMulGadget_sound {p modulus : Nat} [Fact p.Prime] {J : Type}
    (hbasep : 2 ^ limbBits <= p) (hquotp : 2 ^ quotientBits <= p)
    (hmodulus : modulus < (2 ^ limbBits) ^ width)
    (hleft : (2 ^ limbBits + 1) * 2 ^ quotientBits <= p)
    (hright : 2 ^ limbBits * (2 ^ quotientBits + 1) <= p)
    (asg : J -> ZMod p) (w : ScalarMulWires J width limbBits quotientBits)
    (h : systemAccepts asg (scalarMulGadget (F := ZMod p) modulus w)) :
    (asg w.scalar).val < 2 ^ quotientBits /\
    Bignum.Canonical (2 ^ limbBits) width (AirBignum.limbVals asg w.product) /\
    Bignum.denoteNat (2 ^ limbBits) (AirBignum.limbVals asg w.product) =
      modulus * (asg w.scalar).val := by
  let base := 2 ^ limbBits
  let scalarBound := 2 ^ quotientBits
  have hbase : 0 < base := pow_pos (by omega) _
  have hscalarBound : 0 < scalarBound := pow_pos (by omega) _
  obtain ⟨hscalar, hprod, hcarry, hc0, hctop, heq⟩ :=
    (scalarMulGadget_correct asg modulus w).mp h
  have hslt := rangeGadget_val_lt hquotp asg w.scalar w.scalarBit hscalar
  have cp := AirBignum.limbVals_canonical hbasep asg w.product w.productBit hprod
  refine ⟨hslt, cp, ?_⟩
  have heqNat : forall i,
      constDigit base width modulus i * (asg w.scalar).val +
          (asg (w.carry i.castSucc)).val =
        (asg (w.product i)).val + base * (asg (w.carry i.succ)).val := by
    intro i
    have hdigit : constDigit base width modulus i < base :=
      Bignum.digitsLE_ranged hbase width modulus _
        (List.get_mem (Bignum.digitsLE base width modulus)
          (Fin.cast (Bignum.digitsLE_length base width modulus).symm i))
    have hplt := rangeGadget_val_lt hbasep asg
      (w.product i) (w.productBit i) (hprod i)
    have hcin := rangeGadget_val_lt hquotp asg
      (w.carry i.castSucc) (w.carryBit i.castSucc) (hcarry i.castSucc)
    have hcout := rangeGadget_val_lt hquotp asg
      (w.carry i.succ) (w.carryBit i.succ) (hcarry i.succ)
    apply nat_eq_of_zmod_eq (p := p)
    · have hmul : constDigit base width modulus i * (asg w.scalar).val <
          base * scalarBound :=
        Nat.mul_lt_mul_of_lt_of_le hdigit (Nat.le_of_lt hslt) hscalarBound
      have hside : constDigit base width modulus i * (asg w.scalar).val +
          (asg (w.carry i.castSucc)).val < (base + 1) * scalarBound := by
        calc
          _ < base * scalarBound + scalarBound := Nat.add_lt_add hmul hcin
          _ = (base + 1) * scalarBound := by ring
      exact lt_of_lt_of_le hside hleft
    · have hmul : base * (asg (w.carry i.succ)).val < base * scalarBound :=
        Nat.mul_lt_mul_of_pos_left hcout hbase
      have hside : (asg (w.product i)).val + base * (asg (w.carry i.succ)).val <
          base * (scalarBound + 1) := by
        calc
          _ < base + base * scalarBound := Nat.add_lt_add hplt hmul
          _ = base * (scalarBound + 1) := by ring
      exact lt_of_lt_of_le hside hright
    · simpa [base, scalarBound, ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_mul,
        Nat.cast_pow] using heq i
  have htel := scalarMulCarryEquations_denote base (asg w.scalar).val
    (constDigit base width modulus) (fun i => (asg (w.product i)).val)
    (fun i => (asg (w.carry i)).val) heqNat
  have hc0v : (asg (w.carry 0)).val = 0 := by rw [hc0]; exact ZMod.val_zero
  have hctopv : (asg (w.carry (Fin.last width))).val = 0 := by
    rw [hctop]
    exact ZMod.val_zero
  rw [constDigits_eq base width modulus] at htel
  have hqden := Bignum.denoteNat_digitsLE hbase width modulus hmodulus
  simpa [base, AirBignum.limbVals, hc0v, hctopv, hqden, Nat.mul_comm] using htel

/-- The wide scalar primitive is emitted by the same proved descriptor path. -/
theorem emit_scalarMulGadget_iff (ix : Idx -> Nat) (hinj : Function.Injective ix)
    (nPublic nVars : Nat) (hbound : forall i, ix i < nVars)
    (asg : Idx -> F) (modulus : Nat)
    (w : ScalarMulWires Idx width limbBits quotientBits) :
    (exists wv : Nat -> F, (forall i, wv (ix i) = asg i) /\
      descriptorHolds (emit ix nPublic nVars (scalarMulGadget modulus w)) wv) <->
      systemAccepts asg (scalarMulGadget modulus w) :=
  emit_accepts_iff ix hinj nPublic nVars hbound asg (scalarMulGadget modulus w)

/-- FHEgg's 36-bit `q0` fits six radix-64 limbs; ten limbs leave room for its
product by an unsigned 24-bit quotient, and both column bounds fit BabyBear. -/
theorem fheggQ0_scalar24_base64_fits :
    68719403009 < (2 ^ 6) ^ 10 /\
    68719403009 * (2 ^ 24 - 1) < (2 ^ 6) ^ 10 /\
    (2 ^ 6 + 1) * 2 ^ 24 <= babyBearP /\
    2 ^ 6 * (2 ^ 24 + 1) <= babyBearP := by
  norm_num [babyBearP]

/-! ## Existing emitter seam -/

theorem emit_modularViewGadget_iff (ix : Idx -> Nat) (hinj : Function.Injective ix)
    (nPublic nVars : Nat) (hbound : forall i, ix i < nVars)
    (asg : Idx -> F) (q : Nat) (w : ModularWires Idx width limbBits) :
    (exists wv : Nat -> F, (forall i, wv (ix i) = asg i) /\
      descriptorHolds (emit ix nPublic nVars (modularViewGadget q w)) wv) <->
      systemAccepts asg (modularViewGadget q w) :=
  emit_accepts_iff ix hinj nPublic nVars hbound asg (modularViewGadget q w)

/-! ## Direct and emitted BabyBear teeth -/

/-- `width=2`, `limbBits=4`: four words, their bits/carries, and the bound witness. -/
def demoWires : ModularWires (Fin 81) 2 4 where
  x := fun i => ⟨i.val, by omega⟩
  r := fun i => ⟨2 + i.val, by omega⟩
  k := fun i => ⟨4 + i.val, by omega⟩
  product := fun i => ⟨6 + i.val, by omega⟩
  xBit := fun i j => ⟨8 + 4 * i.val + j.val, by omega⟩
  rBit := fun i j => ⟨16 + 4 * i.val + j.val, by omega⟩
  kBit := fun i j => ⟨24 + 4 * i.val + j.val, by omega⟩
  productBit := fun i j => ⟨32 + 4 * i.val + j.val, by omega⟩
  mulCarry := fun i => ⟨40 + i.val, by omega⟩
  mulCarryBit := fun i j => ⟨43 + 4 * i.val + j.val, by omega⟩
  sumCarry := fun i => ⟨55 + i.val, by omega⟩
  slack := fun i => ⟨58 + i.val, by omega⟩
  slackBit := fun i j => ⟨60 + 4 * i.val + j.val, by omega⟩
  bound := fun i => ⟨68 + i.val, by omega⟩
  boundBit := fun i j => ⟨70 + 4 * i.val + j.val, by omega⟩
  remCarry := fun i => ⟨78 + i.val, by omega⟩

def demoBit (value : Nat) (j : Fin 4) : BabyBear :=
  (((value / 2 ^ j.val) % 2 : Nat) : BabyBear)

/-- Honest witness: `200 = 5 + 15*13`, with `5 < 13`. -/
def demoAsg : Fin 81 -> BabyBear := fun i =>
  if h : i.val < 2 then (![8, 12] : Fin 2 -> Nat) ⟨i.val, h⟩ else
  if h : i.val < 4 then (![5, 0] : Fin 2 -> Nat) ⟨i.val - 2, by omega⟩ else
  if h : i.val < 6 then (![15, 0] : Fin 2 -> Nat) ⟨i.val - 4, by omega⟩ else
  if h : i.val < 8 then (![3, 12] : Fin 2 -> Nat) ⟨i.val - 6, by omega⟩ else
  if h : i.val < 16 then demoBit ((![8, 12] : Fin 2 -> Nat) ⟨(i.val - 8) / 4, by omega⟩) ⟨(i.val - 8) % 4, Nat.mod_lt _ (by omega)⟩ else
  if h : i.val < 24 then demoBit ((![5, 0] : Fin 2 -> Nat) ⟨(i.val - 16) / 4, by omega⟩) ⟨(i.val - 16) % 4, Nat.mod_lt _ (by omega)⟩ else
  if h : i.val < 32 then demoBit ((![15, 0] : Fin 2 -> Nat) ⟨(i.val - 24) / 4, by omega⟩) ⟨(i.val - 24) % 4, Nat.mod_lt _ (by omega)⟩ else
  if h : i.val < 40 then demoBit ((![3, 12] : Fin 2 -> Nat) ⟨(i.val - 32) / 4, by omega⟩) ⟨(i.val - 32) % 4, Nat.mod_lt _ (by omega)⟩ else
  if h : i.val < 43 then (![0, 12, 0] : Fin 3 -> Nat) ⟨i.val - 40, by omega⟩ else
  if h : i.val < 55 then
    demoBit ((![0, 12, 0] : Fin 3 -> Nat) ⟨(i.val - 43) / 4, by omega⟩)
      ⟨(i.val - 43) % 4, Nat.mod_lt _ (by omega)⟩ else
  if h : i.val < 58 then (0 : Nat) else
  if h : i.val < 60 then (![7, 0] : Fin 2 -> Nat) ⟨i.val - 58, by omega⟩ else
  if h : i.val < 68 then demoBit ((![7, 0] : Fin 2 -> Nat) ⟨(i.val - 60) / 4, by omega⟩) ⟨(i.val - 60) % 4, Nat.mod_lt _ (by omega)⟩ else
  if h : i.val < 70 then (![12, 0] : Fin 2 -> Nat) ⟨i.val - 68, by omega⟩ else
  if h : i.val < 78 then demoBit ((![12, 0] : Fin 2 -> Nat) ⟨(i.val - 70) / 4, by omega⟩) ⟨(i.val - 70) % 4, Nat.mod_lt _ (by omega)⟩ else
  (0 : Nat)

set_option maxRecDepth 100000 in
example : systemAccepts demoAsg (modularViewGadget 13 demoWires) := by decide

/-- Tampering with `x=200` to `x=201` while retaining the witness is rejected. -/
def demoTampered : Fin 81 -> BabyBear := fun i => if i = 0 then 9 else demoAsg i

set_option maxRecDepth 100000 in
example : ¬ systemAccepts demoTampered (modularViewGadget 13 demoWires) := by decide

set_option maxRecDepth 100000 in
example : exists wv : Nat -> BabyBear,
    (forall i : Fin 81, wv i.val = demoAsg i) /\
      descriptorHolds (emit Fin.val 4 81 (modularViewGadget 13 demoWires)) wv :=
  (emit_accepts_iff_fin 81 4 demoAsg (modularViewGadget 13 demoWires)).mpr (by decide)

set_option maxRecDepth 100000 in
example : ¬ (exists wv : Nat -> BabyBear,
    (forall i : Fin 81, wv i.val = demoTampered i) /\
      descriptorHolds (emit Fin.val 4 81 (modularViewGadget 13 demoWires)) wv) := by
  intro h
  exact (by decide : ¬ systemAccepts demoTampered (modularViewGadget 13 demoWires))
    ((emit_accepts_iff_fin 81 4 demoTampered (modularViewGadget 13 demoWires)).mp h)

#print axioms mulConstGadget_correct
#print axioms mulCarryEquations_denote
#print axioms mulConstGadget_sound
#print axioms modularViewGadget_sound
#print axioms accepted_has_modularView
#print axioms scalarMulGadget_correct
#print axioms scalarMulCarryEquations_denote
#print axioms scalarMulGadget_sound
#print axioms emit_scalarMulGadget_iff
#print axioms fheggQ0_scalar24_base64_fits
#print axioms emit_modularViewGadget_iff

end Minidregg.Compiler.AirModularView
