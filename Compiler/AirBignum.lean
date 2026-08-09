/-
# `Compiler/AirBignum.lean` — fixed-width carry addition in the emitted AIR

`Theory.Bignum` owns the candidate-independent little-endian numeral algebra.  This
module realizes one useful operation from that algebra in the compiler's *existing*
arithmetization path: three fixed-width radix-`2^limbBits` words, per-limb bit range
checks, boolean carries, and the schoolbook equations

`xᵢ + yᵢ + carryᵢ = zᵢ + 2^limbBits * carryᵢ₊₁`.

The gadget is a `ConstraintSystem`, hence `AirFlatten.flattenSystem` and `Compiler.emit`
consume it without a second IR.  `addGadget_sound` lifts an accepting BabyBear-style
prime-field assignment back to canonical `Theory.Bignum` limbs and proves the exact
integer addition when `2 * 2^limbBits <= p`; the inequality is the honest no-field-wrap
condition for one schoolbook equation.  The low and top carries are pinned to zero, so
overflow is rejected rather than reduced modulo the fixed width.
-/
import Compiler.Emit
import Theory.Bignum

namespace Minidregg.Compiler.AirBignum

open Minidregg.Compiler
open Minidregg.Theory

set_option autoImplicit false

universe u

variable {F : Type u} [Field F] {Idx : Type u}
variable {width limbBits : Nat}

/-- Wires for one fixed-width addition.  Limbs are little-endian; each limb has its
own bit-decomposition wires, and `carry` includes both boundary carries. -/
structure AddWires (Idx : Type u) (width limbBits : Nat) where
  x : Fin width -> Idx
  y : Fin width -> Idx
  z : Fin width -> Idx
  xBit : Fin width -> Fin limbBits -> Idx
  yBit : Fin width -> Fin limbBits -> Idx
  zBit : Fin width -> Fin limbBits -> Idx
  carry : Fin (width + 1) -> Idx

/-- Range-check every limb with the compiler's existing bit-decomposition gadget. -/
def limbRangeSystem (limb : Fin width -> Idx)
    (bit : Fin width -> Fin limbBits -> Idx) : ConstraintSystem F Idx :=
  (List.finRange width).flatMap fun i => rangeGadget (limb i) (bit i)

/-- Booleanity of all carry wires, including the pinned boundary carries. -/
def carryRangeSystem (w : AddWires Idx width limbBits) : ConstraintSystem F Idx :=
  (List.finRange (width + 1)).map fun i => boolGadget (w.carry i)

/-- The `i`th schoolbook equation, represented in the one arithmetic term DSL. -/
def addLimbTerm (w : AddWires Idx width limbBits) (i : Fin width) :
    Term (AirSig F Idx) :=
  add'
    (add' (add' (vr (w.x i)) (vr (w.y i))) (vr (w.carry i.castSucc)))
    (mul' (cst (-1))
      (add' (vr (w.z i))
        (mul' (cst ((2 : F) ^ limbBits)) (vr (w.carry i.succ)))))

/-- All per-limb carry equations. -/
def addEquationSystem (w : AddWires Idx width limbBits) : ConstraintSystem F Idx :=
  (List.finRange width).map fun i => addLimbTerm w i

/-- Fixed-width no-overflow addition.  Low carry and carry off the top are both zero. -/
def addGadget (w : AddWires Idx width limbBits) : ConstraintSystem F Idx :=
  limbRangeSystem w.x w.xBit ++
  limbRangeSystem w.y w.yBit ++
  limbRangeSystem w.z w.zBit ++
  carryRangeSystem w ++
  [vr (w.carry 0), vr (w.carry (Fin.last width))] ++
  addEquationSystem w

/-! ## The field reading of each generated block -/

/-- Acceptance of a flattened family of range gadgets is pointwise range acceptance. -/
theorem limbRangeSystem_correct (asg : Idx -> F) (limb : Fin width -> Idx)
    (bit : Fin width -> Fin limbBits -> Idx) :
    systemAccepts asg (limbRangeSystem limb bit) <->
      forall i, systemAccepts asg (rangeGadget (limb i) (bit i)) := by
  constructor
  · intro h i t ht
    apply h t
    rw [limbRangeSystem, List.mem_flatMap]
    exact ⟨i, List.mem_finRange i, ht⟩
  · intro h t ht
    rw [limbRangeSystem, List.mem_flatMap] at ht
    obtain ⟨i, -, ht⟩ := ht
    exact h i t ht

/-- Acceptance of carry booleanity is pointwise booleanity. -/
theorem carryRangeSystem_correct (asg : Idx -> F) (w : AddWires Idx width limbBits) :
    systemAccepts asg (carryRangeSystem w) <->
      forall i, asg (w.carry i) = 0 \/ asg (w.carry i) = 1 := by
  constructor
  · intro h i
    apply (boolGadget_correct asg (w.carry i)).mp
    apply h _
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  · intro h t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact (boolGadget_correct asg (w.carry i)).mpr (h i)

/-- The generated limb equation has exactly the advertised field meaning. -/
theorem addLimbTerm_correct (asg : Idx -> F) (w : AddWires Idx width limbBits)
    (i : Fin width) :
    accepts asg (addLimbTerm w i) <->
      asg (w.x i) + asg (w.y i) + asg (w.carry i.castSucc) =
        asg (w.z i) + (2 : F) ^ limbBits * asg (w.carry i.succ) := by
  unfold accepts addLimbTerm
  simp only [eval_add', eval_mul', eval_cst, eval_vr]
  constructor <;> intro h <;> linear_combination h

/-- Acceptance of the equation block is pointwise schoolbook addition. -/
theorem addEquationSystem_correct (asg : Idx -> F) (w : AddWires Idx width limbBits) :
    systemAccepts asg (addEquationSystem w) <->
      forall i, asg (w.x i) + asg (w.y i) + asg (w.carry i.castSucc) =
        asg (w.z i) + (2 : F) ^ limbBits * asg (w.carry i.succ) := by
  constructor
  · intro h i
    apply (addLimbTerm_correct asg w i).mp
    apply h _
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  · intro h t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact (addLimbTerm_correct asg w i).mpr (h i)

/-- Complete field-level meaning of the generated gadget. -/
theorem addGadget_correct (asg : Idx -> F) (w : AddWires Idx width limbBits) :
    systemAccepts asg (addGadget w) <->
      (forall i, systemAccepts asg (rangeGadget (w.x i) (w.xBit i))) /\
      (forall i, systemAccepts asg (rangeGadget (w.y i) (w.yBit i))) /\
      (forall i, systemAccepts asg (rangeGadget (w.z i) (w.zBit i))) /\
      (forall i, asg (w.carry i) = 0 \/ asg (w.carry i) = 1) /\
      asg (w.carry 0) = 0 /\
      asg (w.carry (Fin.last width)) = 0 /\
      (forall i, asg (w.x i) + asg (w.y i) + asg (w.carry i.castSucc) =
        asg (w.z i) + (2 : F) ^ limbBits * asg (w.carry i.succ)) := by
  rw [addGadget, systemAccepts_append, systemAccepts_append, systemAccepts_append,
    systemAccepts_append, systemAccepts_append, limbRangeSystem_correct,
    limbRangeSystem_correct, limbRangeSystem_correct, carryRangeSystem_correct,
    addEquationSystem_correct]
  simp only [systemAccepts_cons, systemAccepts_nil, and_true, eval_vr, accepts]
  tauto

/-! ## Lift back to `Theory.Bignum` and exact integer addition -/

/-- Read a little-endian limb vector from canonical `ZMod` representatives. -/
def limbVals {p : Nat} (asg : Idx -> ZMod p) (limb : Fin width -> Idx) : List Nat :=
  List.ofFn fun i => (asg (limb i)).val

/-- The carry equations telescope against the shared little-endian denotation. -/
theorem carryEquations_denote (base : Nat) :
    forall {n : Nat} (x y z : Fin n -> Nat) (carry : Fin (n + 1) -> Nat),
      (forall i, x i + y i + carry i.castSucc = z i + base * carry i.succ) ->
      Bignum.denoteNat base (List.ofFn z) + base ^ n * carry (Fin.last n) =
        Bignum.denoteNat base (List.ofFn x) + Bignum.denoteNat base (List.ofFn y) + carry 0 := by
  intro n
  induction n with
  | zero =>
      intro x y z carry _
      simp
  | succ n ih =>
      intro x y z carry heq
      have hlow := heq (0 : Fin (n + 1))
      have htail := ih (fun i => x i.succ) (fun i => y i.succ) (fun i => z i.succ)
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

/-- An accepted limb vector is canonical in the shared bignum algebra. -/
theorem limbVals_canonical {p : Nat} [Fact p.Prime] {J : Type}
    (hp : 2 ^ limbBits <= p)
    (asg : J -> ZMod p) (limb : Fin width -> J)
    (bit : Fin width -> Fin limbBits -> J)
    (h : forall i, systemAccepts asg (rangeGadget (F := ZMod p) (limb i) (bit i))) :
    Bignum.Canonical (2 ^ limbBits) width (limbVals asg limb) := by
  constructor
  · intro digit hdigit
    rw [limbVals, List.mem_ofFn] at hdigit
    obtain ⟨i, rfl⟩ := hdigit
    exact rangeGadget_val_lt hp asg (limb i) (bit i) (h i)
  · simp [limbVals]

/-- Field equality of two naturals below `p` is honest integer equality. -/
private theorem nat_eq_of_zmod_eq {p a b : Nat} [NeZero p]
    (ha : a < p) (hb : b < p) (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have := congrArg ZMod.val h
  simpa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] using this

/-- **Integer soundness and no overflow.** Under the exact per-equation no-wrap bound,
acceptance produces three canonical `Theory.Bignum` words and proves that the result's
natural-number denotation is the sum of the operands' denotations. -/
theorem addGadget_sound {p : Nat} [Fact p.Prime] {J : Type}
    (hp : 2 * 2 ^ limbBits <= p)
    (asg : J -> ZMod p) (w : AddWires J width limbBits)
    (h : systemAccepts asg (addGadget (F := ZMod p) w)) :
    Bignum.Canonical (2 ^ limbBits) width (limbVals asg w.x) /\
    Bignum.Canonical (2 ^ limbBits) width (limbVals asg w.y) /\
    Bignum.Canonical (2 ^ limbBits) width (limbVals asg w.z) /\
    Bignum.denoteNat (2 ^ limbBits) (limbVals asg w.z) =
      Bignum.denoteNat (2 ^ limbBits) (limbVals asg w.x) +
        Bignum.denoteNat (2 ^ limbBits) (limbVals asg w.y) := by
  have hpRange : 2 ^ limbBits <= p := by omega
  obtain ⟨hx, hy, hz, hc, hc0, hctop, heq⟩ := (addGadget_correct asg w).mp h
  have cx := limbVals_canonical hpRange asg w.x w.xBit hx
  have cy := limbVals_canonical hpRange asg w.y w.yBit hy
  have cz := limbVals_canonical hpRange asg w.z w.zBit hz
  refine ⟨cx, cy, cz, ?_⟩
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hcarryVal : forall i, (asg (w.carry i)).val = 0 \/ (asg (w.carry i)).val = 1 := by
    intro i
    rcases hc i with hi | hi
    · left; rw [hi]; exact ZMod.val_zero
    · right; rw [hi]; exact ZMod.val_one p
  have heqNat : forall i,
      (asg (w.x i)).val + (asg (w.y i)).val + (asg (w.carry i.castSucc)).val =
        (asg (w.z i)).val + 2 ^ limbBits * (asg (w.carry i.succ)).val := by
    intro i
    have hxlt := rangeGadget_val_lt hpRange asg (w.x i) (w.xBit i) (hx i)
    have hylt := rangeGadget_val_lt hpRange asg (w.y i) (w.yBit i) (hy i)
    have hzlt := rangeGadget_val_lt hpRange asg (w.z i) (w.zBit i) (hz i)
    have hcin : (asg (w.carry i.castSucc)).val <= 1 := by
      rcases hcarryVal i.castSucc with h | h <;> omega
    have hcout : (asg (w.carry i.succ)).val <= 1 := by
      rcases hcarryVal i.succ with h | h <;> omega
    have hcoutTerm : 2 ^ limbBits * (asg (w.carry i.succ)).val <= 2 ^ limbBits :=
      by simpa using Nat.mul_le_mul_left (2 ^ limbBits) hcout
    apply nat_eq_of_zmod_eq (p := p)
    · omega
    · omega
    · simpa [ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using heq i
  have htel := carryEquations_denote (2 ^ limbBits)
    (fun i => (asg (w.x i)).val) (fun i => (asg (w.y i)).val)
    (fun i => (asg (w.z i)).val) (fun i => (asg (w.carry i)).val) heqNat
  have hc0val : (asg (w.carry 0)).val = 0 := by rw [hc0]; exact ZMod.val_zero
  have hctopval : (asg (w.carry (Fin.last width))).val = 0 := by
    rw [hctop]
    exact ZMod.val_zero
  simpa [limbVals, hc0val, hctopval] using htel

/-! ## The existing emit seam, not a duplicate descriptor language -/

/-- The bignum gadget is consumed by the existing first-order descriptor emitter. -/
theorem emit_addGadget_iff (ix : Idx -> Nat) (hinj : Function.Injective ix)
    (nPublic nVars : Nat) (hbound : forall i, ix i < nVars)
    (asg : Idx -> F) (w : AddWires Idx width limbBits) :
    (exists wv : Nat -> F, (forall i, wv (ix i) = asg i) /\
      descriptorHolds (emit ix nPublic nVars (addGadget w)) wv) <->
      systemAccepts asg (addGadget w) :=
  emit_accepts_iff ix hinj nPublic nVars hbound asg (addGadget w)

/-! ## Computed teeth on a two-limb base-4 word over `ZMod 17` -/

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Canonical demo layout: 3 words x 2 limbs, 3 x 2 x 2 decomposition bits, 3 carries. -/
def demoWires : AddWires (Fin 21) 2 2 where
  x := fun i => ⟨i.val, by omega⟩
  y := fun i => ⟨2 + i.val, by omega⟩
  z := fun i => ⟨4 + i.val, by omega⟩
  xBit := fun i j => ⟨6 + 2 * i.val + j.val, by omega⟩
  yBit := fun i j => ⟨10 + 2 * i.val + j.val, by omega⟩
  zBit := fun i j => ⟨14 + 2 * i.val + j.val, by omega⟩
  carry := fun i => ⟨18 + i.val, by omega⟩

/-- Assignment builder for the base-4 demo. -/
def demoAsg (x y z : Fin 2 -> Nat) (carry : Fin 3 -> Nat) : Fin 21 -> ZMod 17 := fun q =>
  if h : q.val < 2 then x ⟨q.val, h⟩ else
  if h : q.val < 4 then y ⟨q.val - 2, by omega⟩ else
  if h : q.val < 6 then z ⟨q.val - 4, by omega⟩ else
  if h : q.val < 10 then
    (((x ⟨(q.val - 6) / 2, by omega⟩ / 2 ^ ((q.val - 6) % 2)) % 2 : Nat) : ZMod 17) else
  if h : q.val < 14 then
    (((y ⟨(q.val - 10) / 2, by omega⟩ / 2 ^ ((q.val - 10) % 2)) % 2 : Nat) : ZMod 17) else
  if h : q.val < 18 then
    (((z ⟨(q.val - 14) / 2, by omega⟩ / 2 ^ ((q.val - 14) % 2)) % 2 : Nat) : ZMod 17) else
  carry ⟨q.val - 18, by omega⟩

/-- Positive pole: `7 + 6 = 13`, i.e. `[3,1] + [2,1] = [1,3]`, accepts. -/
example : systemAccepts
    (demoAsg ![3, 1] ![2, 1] ![1, 3] ![0, 1, 0])
    (addGadget demoWires) := by decide

/-- Negative pole: the same result with the low carry erased is rejected. -/
example : ¬ systemAccepts
    (demoAsg ![3, 1] ![2, 1] ![1, 3] ![0, 0, 0])
    (addGadget demoWires) := by decide

/-- Overflow tooth: `15 + 1` has no accepting two-limb base-4 gadget assignment. -/
example : ¬ (exists asg : Fin 21 -> ZMod 17,
    limbVals asg demoWires.x = [3, 3] /\
    limbVals asg demoWires.y = [1, 0] /\
    systemAccepts asg (addGadget demoWires)) := by
  rintro ⟨asg, hx, hy, hacc⟩
  obtain ⟨-, -, hz, heq⟩ := addGadget_sound (by norm_num) asg demoWires hacc
  have hzlt : Bignum.denoteNat 4 (limbVals asg demoWires.z) < 4 ^ 2 := by
    simpa [hz.2] using Bignum.denoteNat_lt_pow (base := 4) (by norm_num)
      (limbVals asg demoWires.z) hz.1
  norm_num at heq
  rw [heq, hx, hy] at hzlt
  norm_num [Bignum.denoteNat] at hzlt

#print axioms addLimbTerm_correct
#print axioms addGadget_correct
#print axioms carryEquations_denote
#print axioms addGadget_sound
#print axioms emit_addGadget_iff

end Minidregg.Compiler.AirBignum
