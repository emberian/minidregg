/-
# `Compiler/WideDigestByteDecodeAir.lean` — strict raw-byte decoding for one wide limb

`Compiler.WideDigestAir` begins with nine BabyBear field limbs.  An untrusted wire
format begins one step earlier: each limb is four little-endian bytes.  Casting the
whole `u32` into BabyBear first is unsound as a decoder because the raw word `p`
would become field zero.  This module instead exposes the four bytes separately,
range-checks each as eight bits, and proves `raw < p` with a schoolbook borrow chain
before identifying the decoded field element.

For BabyBear `p = 0x78000001`, little-endian bytes are `[1, 0, 0, 120]`.  The strict
comparison is the fixed-width equation

`diffᵢ + rawᵢ + borrowᵢ = pᵢ + 256 * borrowᵢ₊₁`,

with incoming borrow one and top borrow zero.  The existing `AirRange` gadgets force
the raw/difference bytes into `[0,256)`, boolean gadgets force every borrow, and
`AirBignum.carryEquations_denote` telescopes the equations to

`p = diff + raw + 1`.

Thus an accepted witness decodes exactly and the byte string for raw `p` is
universally rejected, for every choice of auxiliary bytes, bits, and borrows.  The
gadget is a `ConstraintSystem` consumed by the existing `emit` theorem.

The remaining external interface is precise: a parser must supply four byte values
as distinct field wires.  If it first casts an unchecked `u32` into BabyBear, the
information distinguishing raw `p` from raw zero has already been destroyed and no
AIR theorem can recover it. Generated parser/descriptor glue proving that the four
pre-cast bytes populate these wires remains `[AIR-wide-digest-byte-refinement]`.
-/
import Compiler.WideDigestAir

namespace Minidregg.Compiler.WideDigestByteDecodeAir

open Minidregg.Compiler
open Minidregg.Theory

set_option autoImplicit false

def byteWidth : Nat := 4
def byteBits : Nat := 8
def byteBase : Nat := 2 ^ byteBits

theorem byteBase_eq : byteBase = 256 := by norm_num [byteBase, byteBits]

/-- Little-endian bytes of `babyBearP = 0x78000001`. -/
def babyBearByte : Fin 4 → Nat := ![1, 0, 0, 120]

theorem babyBearByte_lt (i : Fin 4) : babyBearByte i < byteBase := by
  fin_cases i <;> decide

theorem babyBearBytes_denote :
    Bignum.denoteNat byteBase (List.ofFn babyBearByte) = babyBearP := by
  decide

/-- Wires for one strict four-byte-to-BabyBear decode. -/
structure DecodeWires (Idx : Type) where
  raw : Fin 4 → Idx
  rawBit : Fin 4 → Fin 8 → Idx
  decoded : Idx
  diff : Fin 4 → Idx
  diffBit : Fin 4 → Fin 8 → Idx
  borrow : Fin 5 → Idx

variable {F : Type} [Field F] {Idx : Type}

/-- Booleanity constraints for all five borrow wires. -/
def borrowRangeSystem (w : DecodeWires Idx) : ConstraintSystem F Idx :=
  (List.finRange 5).map fun i => boolGadget (w.borrow i)

theorem borrowRangeSystem_correct (asg : Idx → F) (w : DecodeWires Idx) :
    systemAccepts asg (borrowRangeSystem w) ↔
      ∀ i, asg (w.borrow i) = 0 ∨ asg (w.borrow i) = 1 := by
  constructor
  · intro h i
    apply (boolGadget_correct asg (w.borrow i)).mp
    apply h _
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
  · intro h t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact (boolGadget_correct asg (w.borrow i)).mpr (h i)

/-- A field-wire constant pin. -/
def pinTerm (wire : Idx) (value : F) : Term (AirSig F Idx) :=
  add' (vr wire) (cst (-value))

theorem pinTerm_correct (asg : Idx → F) (wire : Idx) (value : F) :
    accepts asg (pinTerm wire value) ↔ asg wire = value := by
  unfold accepts pinTerm
  simp only [eval_add', eval_cst, eval_vr, add_neg_eq_zero]

/-- One base-256 strict-borrow equation. -/
def borrowTerm (w : DecodeWires Idx) (i : Fin 4) : Term (AirSig F Idx) :=
  add'
    (add' (add' (vr (w.diff i)) (vr (w.raw i))) (vr (w.borrow i.castSucc)))
    (mul' (cst (-1))
      (add' (cst (babyBearByte i : F))
        (mul' (cst (byteBase : F)) (vr (w.borrow i.succ)))))

theorem borrowTerm_correct (asg : Idx → F) (w : DecodeWires Idx) (i : Fin 4) :
    accepts asg (borrowTerm w i) ↔
      asg (w.diff i) + asg (w.raw i) + asg (w.borrow i.castSucc) =
        (babyBearByte i : F) + (byteBase : F) * asg (w.borrow i.succ) := by
  unfold accepts borrowTerm
  simp only [eval_add', eval_mul', eval_cst, eval_vr]
  rw [neg_one_mul, add_neg_eq_zero]

def borrowEquationSystem (w : DecodeWires Idx) : ConstraintSystem F Idx :=
  (List.finRange 4).map fun i => borrowTerm w i

theorem borrowEquationSystem_correct (asg : Idx → F) (w : DecodeWires Idx) :
    systemAccepts asg (borrowEquationSystem w) ↔
      ∀ i, asg (w.diff i) + asg (w.raw i) + asg (w.borrow i.castSucc) =
        (babyBearByte i : F) + (byteBase : F) * asg (w.borrow i.succ) := by
  constructor
  · intro h i
    exact (borrowTerm_correct asg w i).mp
      (h _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
  · intro h t ht
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ht
    exact (borrowTerm_correct asg w i).mpr (h i)

/-- The field expression for the four-byte little-endian word. -/
def byteValueField (asg : Idx → F) (raw : Fin 4 → Idx) : F :=
  asg (raw 0) + 256 * asg (raw 1) + 65536 * asg (raw 2) +
    16777216 * asg (raw 3)

/-- Pin the decoded field wire to the four-byte recomposition. -/
def decodeTerm (w : DecodeWires Idx) : Term (AirSig F Idx) :=
  add'
    (add'
      (add'
        (add' (vr (w.raw 0)) (mul' (cst 256) (vr (w.raw 1))))
        (mul' (cst 65536) (vr (w.raw 2))))
      (mul' (cst 16777216) (vr (w.raw 3))))
    (mul' (cst (-1)) (vr w.decoded))

theorem decodeTerm_correct (asg : Idx → F) (w : DecodeWires Idx) :
    accepts asg (decodeTerm w) ↔ asg w.decoded = byteValueField asg w.raw := by
  unfold accepts decodeTerm byteValueField
  simp only [eval_add', eval_mul', eval_cst, eval_vr]
  rw [neg_one_mul, add_neg_eq_zero]
  exact eq_comm

/-- The complete strict byte decoder/check. -/
def byteDecodeGadget (w : DecodeWires Idx) : ConstraintSystem F Idx :=
  AirBignum.limbRangeSystem w.raw w.rawBit ++
  AirBignum.limbRangeSystem w.diff w.diffBit ++
  borrowRangeSystem w ++
  [pinTerm (w.borrow 0) 1, pinTerm (w.borrow (Fin.last 4)) 0] ++
  borrowEquationSystem w ++ [decodeTerm w]

theorem byteDecodeGadget_correct (asg : Idx → F) (w : DecodeWires Idx) :
    systemAccepts asg (byteDecodeGadget w) ↔
      (∀ i, systemAccepts asg (rangeGadget (w.raw i) (w.rawBit i))) ∧
      (∀ i, systemAccepts asg (rangeGadget (w.diff i) (w.diffBit i))) ∧
      (∀ i, asg (w.borrow i) = 0 ∨ asg (w.borrow i) = 1) ∧
      asg (w.borrow 0) = 1 ∧
      asg (w.borrow (Fin.last 4)) = 0 ∧
      (∀ i, asg (w.diff i) + asg (w.raw i) + asg (w.borrow i.castSucc) =
        (babyBearByte i : F) + (byteBase : F) * asg (w.borrow i.succ)) ∧
      asg w.decoded = byteValueField asg w.raw := by
  rw [byteDecodeGadget, systemAccepts_append, systemAccepts_append,
    systemAccepts_append, systemAccepts_append, systemAccepts_append,
    AirBignum.limbRangeSystem_correct, AirBignum.limbRangeSystem_correct,
    borrowRangeSystem_correct, borrowEquationSystem_correct]
  simp only [systemAccepts_cons, systemAccepts_nil, and_true, pinTerm_correct,
    decodeTerm_correct]
  tauto

/-! ## Exact natural-number soundness -/

def rawVals (asg : Idx → BabyBear) (w : DecodeWires Idx) : List Nat :=
  AirBignum.limbVals asg w.raw

def diffVals (asg : Idx → BabyBear) (w : DecodeWires Idx) : List Nat :=
  AirBignum.limbVals asg w.diff

private theorem nat_eq_of_babyBear_eq {a b : Nat}
    (ha : a < babyBearP) (hb : b < babyBearP)
    (h : (a : BabyBear) = (b : BabyBear)) : a = b := by
  have hv := congrArg ZMod.val h
  simpa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] using hv

private theorem byteValueField_eq_cast (asg : Idx → BabyBear) (w : DecodeWires Idx) :
    byteValueField asg w.raw =
      (Bignum.denoteNat byteBase (rawVals asg w) : BabyBear) := by
  simp [byteValueField, rawVals, AirBignum.limbVals, byteBase, byteBits,
    Bignum.denoteNat]
  ring

/-- **Decoder soundness.** Acceptance proves the raw bytes canonical, strictly below
BabyBear's modulus, and the decoded field representative exactly equal to the raw `u32`. -/
theorem byteDecodeGadget_sound (asg : Idx → BabyBear) (w : DecodeWires Idx)
    (h : systemAccepts asg (byteDecodeGadget w)) :
    Bignum.Canonical byteBase byteWidth (rawVals asg w) ∧
    Bignum.Canonical byteBase byteWidth (diffVals asg w) ∧
    Bignum.denoteNat byteBase (rawVals asg w) < babyBearP ∧
    (asg w.decoded).val = Bignum.denoteNat byteBase (rawVals asg w) := by
  obtain ⟨hraw, hdiff, hborrow, hbr0, hbrTop, heq, hdecode⟩ :=
    (byteDecodeGadget_correct asg w).mp h
  have hcap : 2 ^ byteBits ≤ babyBearP := by norm_num [byteBits, babyBearP]
  have craw := AirBignum.limbVals_canonical hcap asg w.raw w.rawBit hraw
  have cdiff := AirBignum.limbVals_canonical hcap asg w.diff w.diffBit hdiff
  have hborrowVal : ∀ i, (asg (w.borrow i)).val = 0 ∨ (asg (w.borrow i)).val = 1 := by
    intro i
    rcases hborrow i with hi | hi
    · left; rw [hi]; exact ZMod.val_zero
    · right; rw [hi]; exact ZMod.val_one babyBearP
  have heqNat : ∀ i,
      (asg (w.diff i)).val + (asg (w.raw i)).val + (asg (w.borrow i.castSucc)).val =
        babyBearByte i + byteBase * (asg (w.borrow i.succ)).val := by
    intro i
    have hdlt := rangeGadget_val_lt hcap asg (w.diff i) (w.diffBit i) (hdiff i)
    have hrlt := rangeGadget_val_lt hcap asg (w.raw i) (w.rawBit i) (hraw i)
    have hbin : (asg (w.borrow i.castSucc)).val ≤ 1 := by
      rcases hborrowVal i.castSucc with hi | hi <;> omega
    have hbout : (asg (w.borrow i.succ)).val ≤ 1 := by
      rcases hborrowVal i.succ with hi | hi <;> omega
    have hbaseOut : byteBase * (asg (w.borrow i.succ)).val ≤ byteBase := by
      simpa using Nat.mul_le_mul_left byteBase hbout
    apply nat_eq_of_babyBear_eq
    · norm_num [babyBearP, byteBase, byteBits] at *
      omega
    · have hpbyte := babyBearByte_lt i
      norm_num [babyBearP, byteBase, byteBits] at *
      omega
    · simpa [ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_mul] using heq i
  have htel := AirBignum.carryEquations_denote byteBase
    (fun i => (asg (w.diff i)).val) (fun i => (asg (w.raw i)).val)
    babyBearByte (fun i => (asg (w.borrow i)).val) heqNat
  have hbr0Val : (asg (w.borrow 0)).val = 1 := by
    rw [hbr0]
    exact ZMod.val_one babyBearP
  have hbrTopVal : (asg (w.borrow (Fin.last 4))).val = 0 := by
    rw [hbrTop]
    exact ZMod.val_zero
  have hsum : babyBearP =
      Bignum.denoteNat byteBase (diffVals asg w) +
        Bignum.denoteNat byteBase (rawVals asg w) + 1 := by
    change Bignum.denoteNat byteBase (List.ofFn babyBearByte) +
        byteBase ^ 4 * (asg (w.borrow (Fin.last 4))).val =
      Bignum.denoteNat byteBase (List.ofFn fun i => (asg (w.diff i)).val) +
        Bignum.denoteNat byteBase (List.ofFn fun i => (asg (w.raw i)).val) +
          (asg (w.borrow 0)).val at htel
    rw [hbrTopVal, Nat.mul_zero, Nat.add_zero, hbr0Val, babyBearBytes_denote] at htel
    simpa only [rawVals, diffVals] using htel
  have hrawLt : Bignum.denoteNat byteBase (rawVals asg w) < babyBearP := by omega
  have hdecodeCast : asg w.decoded =
      (Bignum.denoteNat byteBase (rawVals asg w) : BabyBear) := by
    rw [hdecode, byteValueField_eq_cast]
  have hdecodeVal : (asg w.decoded).val =
      Bignum.denoteNat byteBase (rawVals asg w) := by
    rw [hdecodeCast, ZMod.val_cast_of_lt hrawLt]
  exact ⟨craw, cdiff, hrawLt, hdecodeVal⟩

/-- The raw bytes of `p` can never pass, regardless of all auxiliary witnesses. -/
theorem raw_babyBearP_rejected (asg : Idx → BabyBear) (w : DecodeWires Idx)
    (hraw : rawVals asg w = [1, 0, 0, 120]) :
    ¬ systemAccepts asg (byteDecodeGadget w) := by
  intro hacc
  have hlt := (byteDecodeGadget_sound asg w hacc).2.2.1
  rw [hraw] at hlt
  norm_num [Bignum.denoteNat, byteBase, byteBits, babyBearP] at hlt

/-! ## Existing emit seam and emitted rejection -/

theorem emit_byteDecode_iff (ix : Idx → Nat) (hinj : Function.Injective ix)
    (nPublic nVars : Nat) (hbound : ∀ i, ix i < nVars)
    (asg : Idx → BabyBear) (w : DecodeWires Idx) :
    (∃ wv : Nat → BabyBear, (∀ i, wv (ix i) = asg i) ∧
      descriptorHolds (emit ix nPublic nVars (byteDecodeGadget w)) wv) ↔
      systemAccepts asg (byteDecodeGadget w) :=
  emit_accepts_iff ix hinj nPublic nVars hbound asg (byteDecodeGadget w)

theorem emitted_raw_babyBearP_rejected (ix : Idx → Nat) (hinj : Function.Injective ix)
    (nPublic nVars : Nat) (hbound : ∀ i, ix i < nVars)
    (asg : Idx → BabyBear) (w : DecodeWires Idx)
    (hraw : rawVals asg w = [1, 0, 0, 120]) :
    ¬ ∃ wv : Nat → BabyBear, (∀ i, wv (ix i) = asg i) ∧
      descriptorHolds (emit ix nPublic nVars (byteDecodeGadget w)) wv := by
  intro hemitted
  exact raw_babyBearP_rejected asg w hraw
    ((emit_byteDecode_iff ix hinj nPublic nVars hbound asg w).mp hemitted)

/-! ## Computed teeth -/

inductive DemoWire
  | decoded
  | raw (i : Fin 4)
  | rawBit (i : Fin 4) (j : Fin 8)
  | diff (i : Fin 4)
  | diffBit (i : Fin 4) (j : Fin 8)
  | borrow (i : Fin 5)
deriving DecidableEq

def demoWires : DecodeWires DemoWire where
  raw := .raw
  rawBit := .rawBit
  decoded := .decoded
  diff := .diff
  diffBit := .diffBit
  borrow := .borrow

def bitAt (value : Nat) (j : Fin 8) : Nat := (value / 2 ^ j.val) % 2

/-- Honest zero: difference is `p-1 = 0x78000000`, borrow chain `1,0,0,0,0`. -/
def zeroAsg : DemoWire → BabyBear
  | .decoded => 0
  | .raw _ => 0
  | .rawBit _ _ => 0
  | .diff i => ![0, 0, 0, 120] i
  | .diffBit i j => bitAt (![0, 0, 0, 120] i) j
  | .borrow i => if i.val = 0 then 1 else 0

/-- Adjacent positive boundary: raw `p-1 = 0x78000000` decodes to field `p-1`. -/
def maxCanonicalAsg : DemoWire → BabyBear
  | .decoded => babyBearP - 1
  | .raw i => ![0, 0, 0, 120] i
  | .rawBit i j => bitAt (![0, 0, 0, 120] i) j
  | .diff _ => 0
  | .diffBit _ _ => 0
  | .borrow i => if i.val = 0 then 1 else 0

/-- A concrete raw-`p` attempt; the theorem above rejects every attempt, not just this one. -/
def rawPAsg : DemoWire → BabyBear
  | .decoded => 0
  | .raw i => babyBearByte i
  | .rawBit i j => bitAt (babyBearByte i) j
  | .diff _ => 0
  | .diffBit _ _ => 0
  | .borrow i => if i.val = 0 then 1 else 0

example : systemAccepts zeroAsg (byteDecodeGadget demoWires) := by decide
example : systemAccepts maxCanonicalAsg (byteDecodeGadget demoWires) := by decide
example : ¬ systemAccepts rawPAsg (byteDecodeGadget demoWires) := by decide

/-- info: 'Minidregg.Compiler.WideDigestByteDecodeAir.byteDecodeGadget_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byteDecodeGadget_correct
/-- info: 'Minidregg.Compiler.WideDigestByteDecodeAir.byteDecodeGadget_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms byteDecodeGadget_sound
/-- info: 'Minidregg.Compiler.WideDigestByteDecodeAir.raw_babyBearP_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_babyBearP_rejected
/-- info: 'Minidregg.Compiler.WideDigestByteDecodeAir.emit_byteDecode_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms emit_byteDecode_iff
/-- info: 'Minidregg.Compiler.WideDigestByteDecodeAir.emitted_raw_babyBearP_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms emitted_raw_babyBearP_rejected

end Minidregg.Compiler.WideDigestByteDecodeAir
