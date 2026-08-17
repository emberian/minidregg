/-
# `Compiler/EvmAddAir.lean` — the Stage-0 EVM fragment, constrained: u256 add, all the way down

**Substrate, said out loud: this is Lean-authored arithmetization.** Every gate
below comes out of `Compiler/Air`'s DSL through the proved `emit`; the tracer
and the decompiler (`Theory/EvmResidual.lean`) author no constraint. Nothing is
written in Rust; Rust may only read the JSON at the bottom.

## The chain this file closes (design note §6, Stage-0 instance)

```
  evmRun fragmentCode           (Theory/EvmFragment: the machine, anvil-conformant)
    ⇣  fragment_faithful         (Theory/EvmResidual: per-output TV, rfl)
  fragmentResidual               (the residual: cd[32] + cd[0] mod 2^256)
    ⇣  addModGadget_sound / evmAddAsg_accepts   (here: the constraint relation)
  addModGadget                   (here, DERIVED: 16×16-limb modular add over BabyBear)
    ⇣  emit_accepts_iff_fin      (Compiler/Emit: emit_faithful, reused)
  evmAddDescriptor  ⟹  evmAddDescriptor_means_semantics
```

`evmAddDescriptor_means_semantics` is the whole point: **a total wire vector
pinning the 48 public limb wires to `encode(X, Y, Z)` and satisfying the
emitted descriptor exists iff the byte-level EVM run of the 15-byte fragment on
`calldata(X, Y)` returns exactly the 32 bytes of `Z`.** The left side is a
first-order object an unverified prover consumes; the right side is the machine
semantics conformance-tested against a real EVM.

## ⚑ The 256-bit decision, faced (build log D3)

EVM words are 256-bit; BabyBear is 31-bit. This file takes the LIMB route: 16
little-endian limbs of 16 bits (16·16 = 256 exactly), each limb bit-range-checked
with the existing `rangeGadget`, boolean carries, schoolbook equations — and the
**top carry boolean but FREE**: discarding it IS the mod-2²⁵⁶ semantics
(`AirBignum.addGadget` pins it, refusing overflow; `addModGadget` here drops
that one pin and gains wraparound). The wraparound conformance vector
(`conformance_v3_wrap`, `(2²⁵⁶−1) + 5 = 4`) flows through the meaning theorem —
a `< p`-scoped "add" could not state it. 8×32 limbs are impossible over BabyBear
(`p < 2³²`); the boundary encoding's injectivity is `encodeBoundary_injective`,
a theorem, not an assumption.

## What it is NOT

* Not a proof about the *prover*. `[EMIT-sound]` unchanged: "the prover
  accepted, therefore `descriptorHolds`" inherits the FRI/STARK floor.
* Not gas-aware: the semantics side speaks about executions the deployed EVM
  completes within gas (design note §7.5, premise visible).
* The generic half (`addModGadget`, its `correct`/`sound` and the schoolbook
  completeness apparatus) is proved at ANY width/limb size/layout/prime; only
  `evmAddWires`/`evmAddDescriptor` are concrete. The witness builder
  `evmAddAsg` is executable Lean witness-gen: bits and carries COMPUTED from
  `(X, Y)`, not chosen.
-/
import Compiler.EmitSerialize
import Compiler.AirBignum
import Theory.EvmFragment
import Theory.EvmResidual

namespace Minidregg.Compiler.EvmAddAir

open Minidregg.Compiler
open Minidregg.Compiler.AirBignum
open Minidregg.Theory
open Minidregg.Theory.EvmFragment
open Minidregg.Theory.EvmResidual

set_option autoImplicit false

universe u

variable {F : Type u} [Field F] {Idx : Type u} {width limbBits : Nat}

/-! ## §1. The modular add gadget — `AirBignum`'s blocks, one pin dropped. -/

/-- **Fixed-width MODULAR addition**: limb ranges, boolean carries, schoolbook
equations, low carry pinned to zero — and the top carry left free. Every block
is `AirBignum`'s, reused; the only new choice is the absent pin, and that
absence is the mod-2^(width·limbBits) semantics. -/
def addModGadget (w : AddWires Idx width limbBits) : ConstraintSystem F Idx :=
  limbRangeSystem w.x w.xBit ++
  limbRangeSystem w.y w.yBit ++
  limbRangeSystem w.z w.zBit ++
  carryRangeSystem w ++
  [vr (w.carry 0)] ++
  addEquationSystem w

/-- Complete field-level meaning of the modular gadget (the `addGadget_correct`
mirror, minus the top-carry conjunct). -/
theorem addModGadget_correct (asg : Idx → F) (w : AddWires Idx width limbBits) :
    systemAccepts asg (addModGadget w) ↔
      (∀ i, systemAccepts asg (rangeGadget (w.x i) (w.xBit i))) ∧
      (∀ i, systemAccepts asg (rangeGadget (w.y i) (w.yBit i))) ∧
      (∀ i, systemAccepts asg (rangeGadget (w.z i) (w.zBit i))) ∧
      (∀ i, asg (w.carry i) = 0 ∨ asg (w.carry i) = 1) ∧
      asg (w.carry 0) = 0 ∧
      (∀ i, asg (w.x i) + asg (w.y i) + asg (w.carry i.castSucc) =
        asg (w.z i) + (2 : F) ^ limbBits * asg (w.carry i.succ)) := by
  rw [addModGadget, systemAccepts_append, systemAccepts_append, systemAccepts_append,
    systemAccepts_append, systemAccepts_append, limbRangeSystem_correct,
    limbRangeSystem_correct, limbRangeSystem_correct, carryRangeSystem_correct,
    addEquationSystem_correct]
  simp only [systemAccepts_cons, systemAccepts_nil, and_true, eval_vr, accepts]
  tauto

private theorem nat_eq_of_zmod_eq {p a b : Nat} [NeZero p]
    (ha : a < p) (hb : b < p) (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have := congrArg ZMod.val h
  simpa [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] using this

/-- **Integer soundness with wraparound.** Acceptance produces three canonical
`Theory.Bignum` words whose result denotation is the operands' sum REDUCED
modulo the width's capacity — the mod is forced, not assumed: the free top
carry is boolean, so the telescoped sum determines the reduction exactly. -/
theorem addModGadget_sound {p : Nat} [Fact p.Prime] {J : Type}
    (hp : 2 * 2 ^ limbBits ≤ p)
    (asg : J → ZMod p) (w : AddWires J width limbBits)
    (h : systemAccepts asg (addModGadget (F := ZMod p) w)) :
    Bignum.Canonical (2 ^ limbBits) width (limbVals asg w.x) ∧
    Bignum.Canonical (2 ^ limbBits) width (limbVals asg w.y) ∧
    Bignum.Canonical (2 ^ limbBits) width (limbVals asg w.z) ∧
    Bignum.denoteNat (2 ^ limbBits) (limbVals asg w.z) =
      (Bignum.denoteNat (2 ^ limbBits) (limbVals asg w.x) +
        Bignum.denoteNat (2 ^ limbBits) (limbVals asg w.y)) % (2 ^ limbBits) ^ width := by
  have hpRange : 2 ^ limbBits ≤ p := by omega
  obtain ⟨hx, hy, hz, hc, hc0, heq⟩ := (addModGadget_correct asg w).mp h
  have cx := limbVals_canonical hpRange asg w.x w.xBit hx
  have cy := limbVals_canonical hpRange asg w.y w.yBit hy
  have cz := limbVals_canonical hpRange asg w.z w.zBit hz
  refine ⟨cx, cy, cz, ?_⟩
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hcarryVal : ∀ i, (asg (w.carry i)).val = 0 ∨ (asg (w.carry i)).val = 1 := by
    intro i
    rcases hc i with hi | hi
    · left; rw [hi]; exact ZMod.val_zero
    · right; rw [hi]; exact ZMod.val_one p
  have heqNat : ∀ i,
      (asg (w.x i)).val + (asg (w.y i)).val + (asg (w.carry i.castSucc)).val =
        (asg (w.z i)).val + 2 ^ limbBits * (asg (w.carry i.succ)).val := by
    intro i
    have hxlt := rangeGadget_val_lt hpRange asg (w.x i) (w.xBit i) (hx i)
    have hylt := rangeGadget_val_lt hpRange asg (w.y i) (w.yBit i) (hy i)
    have hzlt := rangeGadget_val_lt hpRange asg (w.z i) (w.zBit i) (hz i)
    have hcin : (asg (w.carry i.castSucc)).val ≤ 1 := by
      rcases hcarryVal i.castSucc with h' | h' <;> omega
    have hcout : (asg (w.carry i.succ)).val ≤ 1 := by
      rcases hcarryVal i.succ with h' | h' <;> omega
    have hcoutTerm : 2 ^ limbBits * (asg (w.carry i.succ)).val ≤ 2 ^ limbBits := by
      simpa using Nat.mul_le_mul_left (2 ^ limbBits) hcout
    apply nat_eq_of_zmod_eq (p := p)
    · omega
    · omega
    · simpa [ZMod.natCast_zmod_val, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using heq i
  have htel := carryEquations_denote (2 ^ limbBits)
    (fun i => (asg (w.x i)).val) (fun i => (asg (w.y i)).val)
    (fun i => (asg (w.z i)).val) (fun i => (asg (w.carry i)).val) heqNat
  have hc0val : (asg (w.carry 0)).val = 0 := by rw [hc0]; exact ZMod.val_zero
  have hzlt : Bignum.denoteNat (2 ^ limbBits) (limbVals asg w.z) < (2 ^ limbBits) ^ width := by
    simpa [cz.2] using Bignum.denoteNat_lt_pow (base := 2 ^ limbBits)
      (pow_pos (by norm_num) limbBits) (limbVals asg w.z) cz.1
  have hsum : Bignum.denoteNat (2 ^ limbBits) (limbVals asg w.x) +
      Bignum.denoteNat (2 ^ limbBits) (limbVals asg w.y) =
        Bignum.denoteNat (2 ^ limbBits) (limbVals asg w.z) +
          (2 ^ limbBits) ^ width * (asg (w.carry (Fin.last width))).val := by
    have := htel
    simp only [limbVals] at *
    omega
  rw [hsum, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hzlt]

/-! ## §2. The schoolbook apparatus — digits and carries COMPUTED (Lean witness-gen). -/

/-- Little-endian radix-`B` digit `i` of `v`. -/
def natDigit (B v i : ℕ) : ℕ := v / B ^ i % B

theorem natDigit_lt (B v i : ℕ) (hB : 0 < B) : natDigit B v i < B :=
  Nat.mod_lt _ hB

/-- The schoolbook carry chain of a digitwise addition — the honest prover's
carry witness, computed. -/
def carryChain (B : ℕ) (x y : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (x i + y i + carryChain B x y i) / B

theorem carryChain_le_one (B : ℕ) (x y : ℕ → ℕ) (hB : 0 < B)
    (hx : ∀ i, x i < B) (hy : ∀ i, y i < B) : ∀ i, carryChain B x y i ≤ 1 := by
  intro i
  induction i with
  | zero => simp [carryChain]
  | succ i ih =>
      have hxi := hx i
      have hyi := hy i
      have : x i + y i + carryChain B x y i < 2 * B := by omega
      have := (Nat.div_lt_iff_lt_mul hB).mpr (by omega :
        x i + y i + carryChain B x y i < 2 * B)
      simpa [carryChain] using Nat.lt_succ_iff.mp (by simpa [Nat.mul_comm] using this)

/-- The digit vector of a value, as a list — equal to `Bignum.digitsLE`. -/
theorem ofFn_natDigit (B : ℕ) : ∀ (w X : ℕ),
    List.ofFn (fun i : Fin w => natDigit B X i.1) = Bignum.digitsLE B w X := by
  intro w
  induction w with
  | zero => intro X; simp [Bignum.digitsLE]
  | succ w ih =>
      intro X
      rw [List.ofFn_succ, Bignum.digitsLE]
      congr 1
      · simp [natDigit]
      · rw [← ih (X / B)]
        congr 1
        funext i
        simp only [natDigit, Fin.val_succ]
        rw [Nat.div_div_eq_div_mul, ← pow_succ']

/-- `denoteNat` of an indexed vector is the weighted big-operator sum. -/
theorem denoteNat_ofFn (B : ℕ) : ∀ (w : ℕ) (f : Fin w → ℕ),
    Bignum.denoteNat B (List.ofFn f) = ∑ i : Fin w, f i * B ^ i.1 := by
  intro w
  induction w with
  | zero => intro f; simp
  | succ w ih =>
      intro f
      rw [List.ofFn_succ, Bignum.denoteNat_cons, ih, Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      rw [Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ']
      ring

/-- Digits recompose: the base-`B` positional expansion of `v < B ^ k`. -/
theorem sum_natDigit (B : ℕ) (hB : 0 < B) (k v : ℕ) (hv : v < B ^ k) :
    ∑ i : Fin k, natDigit B v i.1 * B ^ i.1 = v := by
  rw [← denoteNat_ofFn, ofFn_natDigit B, Bignum.denoteNat_digitsLE hB k v hv]

/-- **The schoolbook completeness crux**: with the carry chain computed, each
digitwise equation lands on the digits of the WRAPPED sum — the witness the
honest prover assigns satisfies the gadget's equations at the claim the
encoder pins. Derived by telescoping (`carryEquations_denote`, reused) plus
canonical-representation uniqueness, not re-proved arithmetic. -/
theorem schoolbook_digit_eq (B : ℕ) (hB : 2 ≤ B) {w : ℕ} (X Y : ℕ)
    (hX : X < B ^ w) (hY : Y < B ^ w) (i : Fin w) :
    natDigit B X i.1 + natDigit B Y i.1
        + carryChain B (natDigit B X) (natDigit B Y) i.1
      = natDigit B ((X + Y) % B ^ w) i.1
        + B * carryChain B (natDigit B X) (natDigit B Y) (i.1 + 1) := by
  have hB0 : 0 < B := by omega
  set c := carryChain B (natDigit B X) (natDigit B Y) with hc
  -- the computed digit vector of the sum
  set z : Fin w → ℕ := fun j => (natDigit B X j.1 + natDigit B Y j.1 + c j.1) % B with hzdef
  -- the per-limb division identities, definitionally aligned with `carryChain`
  have hstep : ∀ j : Fin w, natDigit B X j.1 + natDigit B Y j.1 + c j.1
      = z j + B * c (j.1 + 1) := fun j => by
    simpa [hzdef] using (Nat.mod_add_div (natDigit B X j.1 + natDigit B Y j.1 + c j.1) B).symm
  -- telescope against the shared denotation
  have htel := carryEquations_denote B
    (fun j : Fin w => natDigit B X j.1) (fun j => natDigit B Y j.1) z
    (fun j : Fin (w + 1) => c j.1) (fun j => hstep j)
  have hdx : Bignum.denoteNat B (List.ofFn fun j : Fin w => natDigit B X j.1) = X := by
    rw [ofFn_natDigit B, Bignum.denoteNat_digitsLE hB0 w X hX]
  have hdy : Bignum.denoteNat B (List.ofFn fun j : Fin w => natDigit B Y j.1) = Y := by
    rw [ofFn_natDigit B, Bignum.denoteNat_digitsLE hB0 w Y hY]
  have hzranged : Bignum.Ranged B (List.ofFn z) := by
    intro d hd
    rw [List.mem_ofFn] at hd
    obtain ⟨j, rfl⟩ := hd
    exact Nat.mod_lt _ hB0
  have hzlt : Bignum.denoteNat B (List.ofFn z) < B ^ w := by
    simpa using Bignum.denoteNat_lt_pow hB0 (List.ofFn z) hzranged
  have hsumeq : Bignum.denoteNat B (List.ofFn z) + B ^ w * c w = X + Y := by
    simpa [hdx, hdy, hc, carryChain] using htel
  -- the computed digits ARE the wrapped sum's digits
  have hdenote : Bignum.denoteNat B (List.ofFn z) = (X + Y) % B ^ w := by
    rw [← hsumeq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hzlt]
  have hlist : List.ofFn z = List.ofFn (fun j : Fin w => natDigit B ((X + Y) % B ^ w) j.1) := by
    rw [ofFn_natDigit B]
    refine Bignum.canonical_eq_of_denoteNat_eq hB0
      ⟨hzranged, by simp⟩ (Bignum.digitsLE_canonical hB0 w _) ?_
    rw [hdenote, Bignum.denoteNat_digitsLE hB0 w _ (Nat.mod_lt _ (pow_pos hB0 w))]
  have hpoint : z i = natDigit B ((X + Y) % B ^ w) i.1 :=
    congrFun (List.ofFn_inj.mp hlist) i
  rw [← hpoint]
  exact hstep i

/-! ## §3. The concrete Stage-0 instance: 16 limbs × 16 bits over BabyBear.

Wire layout over `Fin 833`: X limbs at 0–15, Y at 16–31, Z at 32–47 (the 48
PUBLIC wires — the boundary), then 768 bit wires (48–815), then 17 carries
(816–832). `nPublic = 48`, `nVars = 833`. -/

/-- The canonical Stage-0 wire layout. -/
def evmAddWires : AddWires (Fin 833) 16 16 where
  x := fun i => ⟨i.1, by omega⟩
  y := fun i => ⟨16 + i.1, by omega⟩
  z := fun i => ⟨32 + i.1, by omega⟩
  xBit := fun i j => ⟨48 + 16 * i.1 + j.1, by omega⟩
  yBit := fun i j => ⟨304 + 16 * i.1 + j.1, by omega⟩
  zBit := fun i j => ⟨560 + 16 * i.1 + j.1, by omega⟩
  carry := fun i => ⟨816 + i.1, by omega⟩

/-- The Stage-0 constraint system — DERIVED by `addModGadget`, never a gate list. -/
def evmAddSystem : ConstraintSystem BabyBear (Fin 833) :=
  addModGadget evmAddWires

/-- **The emitted descriptor**: 48 public limb wires, 833 variables. -/
def evmAddDescriptor : ConstraintDescriptor BabyBear :=
  emit Fin.val 48 833 evmAddSystem

/-- The boundary encoding at a raw wire index (the `Fin`-free worker — every
proof about a region reduces here, where `omega` sees plain `ℕ` conditions). -/
def encodeBoundaryN (X Y Z n : ℕ) : BabyBear :=
  if n < 16 then (natDigit 65536 X n : BabyBear)
  else if n < 32 then (natDigit 65536 Y (n - 16) : BabyBear)
  else (natDigit 65536 Z (n - 32) : BabyBear)

/-- The boundary encoding: `(X, Y, Z) ↦` 48 sixteen-bit limbs. -/
def encodeBoundary (X Y Z : ℕ) : Fin 48 → BabyBear := fun i =>
  encodeBoundaryN X Y Z i.1

/-- The honest prover's assignment at a raw wire index (the `Fin`-free worker). -/
def evmAddAsgN (X Y n : ℕ) : BabyBear :=
  if n < 16 then (natDigit 65536 X n : BabyBear)
  else if n < 32 then (natDigit 65536 Y (n - 16) : BabyBear)
  else if n < 48 then (natDigit 65536 ((X + Y) % 2 ^ 256) (n - 32) : BabyBear)
  else if n < 304 then
    (natDigit 2 (natDigit 65536 X ((n - 48) / 16)) ((n - 48) % 16) : BabyBear)
  else if n < 560 then
    (natDigit 2 (natDigit 65536 Y ((n - 304) / 16)) ((n - 304) % 16) : BabyBear)
  else if n < 816 then
    (natDigit 2 (natDigit 65536 ((X + Y) % 2 ^ 256) ((n - 560) / 16)) ((n - 560) % 16) : BabyBear)
  else (carryChain 65536 (natDigit 65536 X) (natDigit 65536 Y) (n - 816) : BabyBear)

/-- **The honest prover's assignment** — executable Lean witness-gen: limbs,
bits and carries all COMPUTED from `(X, Y)`; the Z region carries the digits of
the wrapped sum, exactly what the encoder pins. -/
def evmAddAsg (X Y : ℕ) : Fin 833 → BabyBear := fun q => evmAddAsgN X Y q.1

/-! ### Region reads — the assignment through the layout, resolved. Each proof
`show`s the definitionally-reduced worker application, so the `if` conditions
are plain `ℕ` arithmetic. -/

theorem evmAddAsg_x (X Y : ℕ) (i : Fin 16) :
    evmAddAsg X Y (evmAddWires.x i) = (natDigit 65536 X i.1 : BabyBear) := by
  have hi := i.isLt
  show evmAddAsgN X Y i.1 = _
  unfold evmAddAsgN
  rw [if_pos (by omega)]

theorem evmAddAsg_y (X Y : ℕ) (i : Fin 16) :
    evmAddAsg X Y (evmAddWires.y i) = (natDigit 65536 Y i.1 : BabyBear) := by
  have hi := i.isLt
  show evmAddAsgN X Y (16 + i.1) = _
  unfold evmAddAsgN
  rw [if_neg (by omega), if_pos (by omega), show 16 + i.1 - 16 = i.1 from by omega]

theorem evmAddAsg_z (X Y : ℕ) (i : Fin 16) :
    evmAddAsg X Y (evmAddWires.z i)
      = (natDigit 65536 ((X + Y) % 2 ^ 256) i.1 : BabyBear) := by
  have hi := i.isLt
  show evmAddAsgN X Y (32 + i.1) = _
  unfold evmAddAsgN
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 32 + i.1 - 32 = i.1 from by omega]

theorem evmAddAsg_xBit (X Y : ℕ) (i j : Fin 16) :
    evmAddAsg X Y (evmAddWires.xBit i j)
      = (natDigit 2 (natDigit 65536 X i.1) j.1 : BabyBear) := by
  have hi := i.isLt
  have hj := j.isLt
  show evmAddAsgN X Y (48 + 16 * i.1 + j.1) = _
  unfold evmAddAsgN
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show (48 + 16 * i.1 + j.1 - 48) / 16 = i.1 from by omega,
    show (48 + 16 * i.1 + j.1 - 48) % 16 = j.1 from by omega]

theorem evmAddAsg_yBit (X Y : ℕ) (i j : Fin 16) :
    evmAddAsg X Y (evmAddWires.yBit i j)
      = (natDigit 2 (natDigit 65536 Y i.1) j.1 : BabyBear) := by
  have hi := i.isLt
  have hj := j.isLt
  show evmAddAsgN X Y (304 + 16 * i.1 + j.1) = _
  unfold evmAddAsgN
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega),
    show (304 + 16 * i.1 + j.1 - 304) / 16 = i.1 from by omega,
    show (304 + 16 * i.1 + j.1 - 304) % 16 = j.1 from by omega]

theorem evmAddAsg_zBit (X Y : ℕ) (i j : Fin 16) :
    evmAddAsg X Y (evmAddWires.zBit i j)
      = (natDigit 2 (natDigit 65536 ((X + Y) % 2 ^ 256) i.1) j.1 : BabyBear) := by
  have hi := i.isLt
  have hj := j.isLt
  show evmAddAsgN X Y (560 + 16 * i.1 + j.1) = _
  unfold evmAddAsgN
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos (by omega),
    show (560 + 16 * i.1 + j.1 - 560) / 16 = i.1 from by omega,
    show (560 + 16 * i.1 + j.1 - 560) % 16 = j.1 from by omega]

theorem evmAddAsg_carry (X Y : ℕ) (i : Fin 17) :
    evmAddAsg X Y (evmAddWires.carry i)
      = (carryChain 65536 (natDigit 65536 X) (natDigit 65536 Y) i.1 : BabyBear) := by
  have hi := i.isLt
  show evmAddAsgN X Y (816 + i.1) = _
  unfold evmAddAsgN
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), show 816 + i.1 - 816 = i.1 from by omega]

/-! ### Completeness: the computed witness ACCEPTS — the honest prover is never
refused, for every in-range operand pair, as one theorem (no sampling). -/

/-- One limb family's range acceptance, shared by the three regions. -/
private theorem range_accepts_of_digits {J : Type} (l : ℕ) (hl : l < 65536)
    (xi : J) (bits : Fin 16 → J) (asg : J → BabyBear)
    (hxi : asg xi = (l : BabyBear))
    (hbits : ∀ j : Fin 16, asg (bits j) = (natDigit 2 l j.1 : BabyBear)) :
    systemAccepts asg (rangeGadget xi bits) := by
  rw [rangeGadget_correct]
  constructor
  · intro j
    rw [hbits j]
    rcases Nat.mod_two_eq_zero_or_one (l / 2 ^ j.1) with h | h
    · left
      rw [show natDigit 2 l j.1 = 0 from h]
      exact Nat.cast_zero
    · right
      rw [show natDigit 2 l j.1 = 1 from h]
      exact Nat.cast_one
  · rw [hxi]
    have hsum : (∑ j : Fin 16, asg (bits j) * (2 : BabyBear) ^ (j : ℕ))
        = ((∑ j : Fin 16, natDigit 2 l j.1 * 2 ^ j.1 : ℕ) : BabyBear) := by
      push_cast
      exact Finset.sum_congr rfl fun j _ => by rw [hbits j]
    rw [hsum, sum_natDigit 2 (by norm_num) 16 l
      (lt_of_lt_of_le hl (by norm_num))]

/-- **The honest witness accepts** — completeness of the Stage-0 system at every
in-range operand pair. -/
theorem evmAddAsg_accepts (X Y : ℕ) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) :
    systemAccepts (evmAddAsg X Y) evmAddSystem := by
  have h65536 : ((65536 : ℕ) : ℕ) ^ 16 = 2 ^ 256 := by norm_num
  have hXd : ∀ i, natDigit 65536 X i < 65536 := fun i => natDigit_lt _ _ _ (by norm_num)
  have hYd : ∀ i, natDigit 65536 Y i < 65536 := fun i => natDigit_lt _ _ _ (by norm_num)
  have hZd : ∀ i, natDigit 65536 ((X + Y) % 2 ^ 256) i < 65536 :=
    fun i => natDigit_lt _ _ _ (by norm_num)
  rw [evmAddSystem, addModGadget_correct]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact range_accepts_of_digits (natDigit 65536 X i.1) (hXd i.1)
      _ _ _ (evmAddAsg_x X Y i) (fun j => evmAddAsg_xBit X Y i j)
  · intro i
    exact range_accepts_of_digits (natDigit 65536 Y i.1) (hYd i.1)
      _ _ _ (evmAddAsg_y X Y i) (fun j => evmAddAsg_yBit X Y i j)
  · intro i
    exact range_accepts_of_digits (natDigit 65536 ((X + Y) % 2 ^ 256) i.1) (hZd i.1)
      _ _ _ (evmAddAsg_z X Y i) (fun j => evmAddAsg_zBit X Y i j)
  · intro i
    rw [evmAddAsg_carry]
    have hle := carryChain_le_one 65536 (natDigit 65536 X) (natDigit 65536 Y)
      (by norm_num) hXd hYd i.1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
    · left; rw [h]; exact Nat.cast_zero
    · right; rw [h]; exact Nat.cast_one
  · rw [evmAddAsg_carry]
    exact Nat.cast_zero
  · intro i
    rw [evmAddAsg_x, evmAddAsg_y, evmAddAsg_z, evmAddAsg_carry, evmAddAsg_carry]
    have hcap : ((65536 : ℕ)) ^ 16 = 2 ^ 256 := by norm_num
    have hnat := schoolbook_digit_eq 65536 (by norm_num) X Y
      (by rw [hcap]; exact hX) (by rw [hcap]; exact hY) i
    rw [hcap] at hnat
    have hcast := congrArg (Nat.cast (R := BabyBear)) hnat
    push_cast at hcast
    rw [show ((2 : BabyBear) ^ 16) = ((65536 : ℕ) : BabyBear) from by norm_num]
    simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    exact hcast

/-! ## §4. The meaning theorem — the §6 statement, Stage-0 instance. -/

/-- The semantics side, reduced to arithmetic: the machine run returns `Z`'s
bytes iff `Z` is the wrapped sum — `fragment_faithful` (the TV theorem) plus
the codec facts, nothing else. -/
theorem fragment_run_eq_iff (X Y Z : ℕ)
    (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) (hZ : Z < 2 ^ 256) :
    evmRun fragmentFuel fragmentCode (calldataOf X Y) = .ok (beBytes Z)
      ↔ Z = (X + Y) % 2 ^ 256 := by
  have hW : wordMod = 2 ^ 256 := rfl
  have hden : fragmentResidual.denote (calldataOf X Y) = (Y + X) % 2 ^ 256 := by
    show (cdWord (calldataOf X Y) 32 + cdWord (calldataOf X Y) 0) % wordMod = _
    rw [cdWord_calldataOf_32 X (hW ▸ hY), cdWord_calldataOf_zero Y (hW ▸ hX), hW]
  rw [fragment_faithful (calldataOf X Y)]
  constructor
  · intro h
    have hb : beBytes (fragmentResidual.denote (calldataOf X Y)) = beBytes Z := by
      injection h
    have := beBytes_inj (X := fragmentResidual.denote (calldataOf X Y)) (Z := Z)
      (by rw [hden, hW]; exact Nat.mod_lt _ (by norm_num)) (hW ▸ hZ) hb
    rw [hden] at this
    omega
  · intro h
    have : fragmentResidual.denote (calldataOf X Y) = Z := by rw [hden, h]; omega
    rw [this]

/-- **`evmAddDescriptor_means_semantics` — the Stage-0 chain, closed.** A total
wire vector pinning the 48 public wires to `encode(X, Y, Z)` and satisfying the
emitted descriptor exists **iff** the byte-level EVM run of the fragment on
`calldata(X, Y)` returns exactly `Z`'s 32 bytes. Every link is a theorem:
`emit_accepts_iff_fin` (on `emit_faithful`) carries the descriptor to the
derived system; `addModGadget_sound` / `evmAddAsg_accepts` carry the system to
the wrapped-sum arithmetic; `fragment_faithful` (rfl-TV) + the codec carry the
arithmetic to the machine. Trusted base: kernel axioms + the differential
EVM-fidelity of `evmRun` + `[EMIT-sound]`'s FRI/STARK floor — enumerated in the
build log, nothing else. -/
theorem evmAddDescriptor_means_semantics (X Y Z : ℕ)
    (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) (hZ : Z < 2 ^ 256) :
    (∃ wv : ℕ → BabyBear, (∀ i : Fin 48, wv i.1 = encodeBoundary X Y Z i) ∧
        descriptorHolds evmAddDescriptor wv)
      ↔ evmRun fragmentFuel fragmentCode (calldataOf X Y) = .ok (beBytes Z) := by
  rw [fragment_run_eq_iff X Y Z hX hY hZ]
  have hcap : ((65536 : ℕ)) ^ 16 = 2 ^ 256 := by norm_num
  have hdlt : ∀ v i, natDigit 65536 v i < babyBearP :=
    fun v i => lt_trans (natDigit_lt _ _ _ (by norm_num)) (by norm_num [babyBearP])
  constructor
  · rintro ⟨wv, hpin, hd⟩
    have hacc : systemAccepts (fun i : Fin 833 => wv i.1) evmAddSystem :=
      (emit_accepts_iff_fin 833 48 (fun i : Fin 833 => wv i.1) evmAddSystem).mp
        ⟨wv, fun _ => rfl, hd⟩
    obtain ⟨cx, cy, cz, heq⟩ := addModGadget_sound
      (p := babyBearP) (by norm_num [babyBearP])
      (fun i : Fin 833 => wv i.1) evmAddWires hacc
    rw [show ((2 : ℕ) ^ 16) = 65536 from by norm_num] at heq
    -- read the pinned limb regions back as the digits of X, Y, Z
    have hvx : limbVals (fun i : Fin 833 => wv i.1) evmAddWires.x
        = Bignum.digitsLE 65536 16 X := by
      unfold limbVals
      rw [← ofFn_natDigit]
      refine congrArg List.ofFn (funext fun i => ?_)
      have hp : wv i.1 = encodeBoundaryN X Y Z i.1 := hpin ⟨i.1, by omega⟩
      unfold encodeBoundaryN at hp
      rw [if_pos (by have := i.isLt; omega)] at hp
      show (wv i.1).val = natDigit 65536 X i.1
      rw [hp, ZMod.val_cast_of_lt (hdlt X i.1)]
    have hvy : limbVals (fun i : Fin 833 => wv i.1) evmAddWires.y
        = Bignum.digitsLE 65536 16 Y := by
      unfold limbVals
      rw [← ofFn_natDigit]
      refine congrArg List.ofFn (funext fun i => ?_)
      have hp : wv (16 + i.1) = encodeBoundaryN X Y Z (16 + i.1) :=
        hpin ⟨16 + i.1, by have := i.isLt; omega⟩
      unfold encodeBoundaryN at hp
      rw [if_neg (by omega), if_pos (by have := i.isLt; omega),
        show 16 + i.1 - 16 = i.1 from by omega] at hp
      show (wv (16 + i.1)).val = natDigit 65536 Y i.1
      rw [hp, ZMod.val_cast_of_lt (hdlt Y i.1)]
    have hvz : limbVals (fun i : Fin 833 => wv i.1) evmAddWires.z
        = Bignum.digitsLE 65536 16 Z := by
      unfold limbVals
      rw [← ofFn_natDigit]
      refine congrArg List.ofFn (funext fun i => ?_)
      have hp : wv (32 + i.1) = encodeBoundaryN X Y Z (32 + i.1) :=
        hpin ⟨32 + i.1, by have := i.isLt; omega⟩
      unfold encodeBoundaryN at hp
      rw [if_neg (by omega), if_neg (by omega),
        show 32 + i.1 - 32 = i.1 from by omega] at hp
      show (wv (32 + i.1)).val = natDigit 65536 Z i.1
      rw [hp, ZMod.val_cast_of_lt (hdlt Z i.1)]
    rw [hvx, hvy, hvz,
      Bignum.denoteNat_digitsLE (by norm_num) 16 X (by rw [hcap]; exact hX),
      Bignum.denoteNat_digitsLE (by norm_num) 16 Y (by rw [hcap]; exact hY),
      Bignum.denoteNat_digitsLE (by norm_num) 16 Z (by rw [hcap]; exact hZ)] at heq
    rw [heq, hcap]
  · intro hZeq
    have hasg := evmAddAsg_accepts X Y hX hY
    obtain ⟨wv, hpins, hd⟩ :=
      (emit_accepts_iff_fin 833 48 (evmAddAsg X Y) evmAddSystem).mpr hasg
    refine ⟨wv, fun i => ?_, hd⟩
    have hi := i.isLt
    have hp : wv i.1 = evmAddAsgN X Y i.1 := hpins ⟨i.1, by omega⟩
    rw [hp]
    show evmAddAsgN X Y i.1 = encodeBoundaryN X Y Z i.1
    unfold evmAddAsgN encodeBoundaryN
    by_cases h16 : i.1 < 16
    · rw [if_pos h16, if_pos h16]
    · by_cases h32 : i.1 < 32
      · rw [if_neg h16, if_neg h16, if_pos h32, if_pos h32]
      · rw [if_neg h16, if_neg h16, if_neg h32, if_neg h32, if_pos (by omega),
          ← hZeq]

/-- *Well-formed*: the prover can size its buffers from the header. -/
theorem evmAddDescriptor_wellFormed : evmAddDescriptor.WellFormed :=
  emit_wellFormed Fin.val 48 833 (by omega) (fun i => i.isLt) evmAddSystem

set_option maxRecDepth 16384 in
/-- *Shape, decided (kernel)*: 3,298 gates, 4,131 wires (833 variables + 3,298
aux), 850 zero-checked roots (3×16×17 range assertions + 17 carry booleanities
+ 1 pin + 16 limb equations). The full 2²⁵⁶ ring costs ~3.3K gates — the
measured Stage-0 anchor for the design note's §8 pricing. -/
theorem evmAddDescriptor_shape :
    evmAddDescriptor.gates.length = 3298 ∧ evmAddDescriptor.nWires = 4131 ∧
      evmAddDescriptor.zeros.length = 850 := by decide +kernel

/-- **The boundary encoding is injective** on 256-bit triples — the "does ONLY
that program" half needs no two boundary values colliding into one accepted
vector, as a THEOREM with a name (the design note's `encode_injective`). -/
theorem encodeBoundary_injective {X Y Z X' Y' Z' : ℕ}
    (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) (hZ : Z < 2 ^ 256)
    (hX' : X' < 2 ^ 256) (hY' : Y' < 2 ^ 256) (hZ' : Z' < 2 ^ 256)
    (h : encodeBoundary X Y Z = encodeBoundary X' Y' Z') :
    X = X' ∧ Y = Y' ∧ Z = Z' := by
  have hcap : ((65536 : ℕ)) ^ 16 = 2 ^ 256 := by norm_num
  have hdlt : ∀ v i, natDigit 65536 v i < babyBearP :=
    fun v i => lt_trans (natDigit_lt _ _ _ (by norm_num)) (by norm_num [babyBearP])
  have hrec : ∀ {V V' : ℕ}, V < 2 ^ 256 → V' < 2 ^ 256 →
      (∀ i : Fin 16, natDigit 65536 V i.1 = natDigit 65536 V' i.1) → V = V' := by
    intro V V' hV hV' hdig
    have : Bignum.digitsLE 65536 16 V = Bignum.digitsLE 65536 16 V' := by
      rw [← ofFn_natDigit, ← ofFn_natDigit]
      exact congrArg _ (funext hdig)
    calc V = Bignum.denoteNat 65536 (Bignum.digitsLE 65536 16 V) :=
          (Bignum.denoteNat_digitsLE (by norm_num) 16 V (hcap ▸ hV)).symm
      _ = Bignum.denoteNat 65536 (Bignum.digitsLE 65536 16 V') := by rw [this]
      _ = V' := Bignum.denoteNat_digitsLE (by norm_num) 16 V' (hcap ▸ hV')
  refine ⟨hrec hX hX' fun i => ?_, hrec hY hY' fun i => ?_, hrec hZ hZ' fun i => ?_⟩
  · have hpt : encodeBoundaryN X Y Z i.1 = encodeBoundaryN X' Y' Z' i.1 :=
      congrFun h ⟨i.1, by have := i.isLt; omega⟩
    unfold encodeBoundaryN at hpt
    rw [if_pos (by have := i.isLt; omega), if_pos (by have := i.isLt; omega)] at hpt
    exact nat_eq_of_zmod_eq (hdlt X i.1) (hdlt X' i.1) hpt
  · have hpt : encodeBoundaryN X Y Z (16 + i.1) = encodeBoundaryN X' Y' Z' (16 + i.1) :=
      congrFun h ⟨16 + i.1, by have := i.isLt; omega⟩
    unfold encodeBoundaryN at hpt
    -- NB: the two chains resolve leftmost-outermost, so the rewrites ALTERNATE
    -- sides: LHS outer, LHS inner, RHS outer, RHS inner.
    rw [if_neg (by omega), if_pos (by have := i.isLt; omega), if_neg (by omega),
      if_pos (by have := i.isLt; omega),
      show 16 + i.1 - 16 = i.1 from by omega] at hpt
    exact nat_eq_of_zmod_eq (hdlt Y i.1) (hdlt Y' i.1) hpt
  · have hpt : encodeBoundaryN X Y Z (32 + i.1) = encodeBoundaryN X' Y' Z' (32 + i.1) :=
      congrFun h ⟨32 + i.1, by have := i.isLt; omega⟩
    unfold encodeBoundaryN at hpt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show 32 + i.1 - 32 = i.1 from by omega] at hpt
    exact nat_eq_of_zmod_eq (hdlt Z i.1) (hdlt Z' i.1) hpt

/-! ## §5. Teeth — conformance through the whole chain, and a forgery refused
at BOTH the descriptor and the denotation. Mutations asserted first. -/

/-- V1 through the chain: the small-values conformance vector is satisfiable at
the descriptor — via the meaning theorem's completeness direction, the anvil
vector, and nothing bespoke. -/
theorem evmAdd_satisfiable_v1 :
    ∃ wv : ℕ → BabyBear, (∀ i : Fin 48, wv i.1 = encodeBoundary 1 2 3 i) ∧
      descriptorHolds evmAddDescriptor wv :=
  (evmAddDescriptor_means_semantics 1 2 3
    (by norm_num) (by norm_num) (by norm_num)).mpr conformance_v1

/-- V3 through the chain: **wraparound is accepted** — `(2²⁵⁶−1) + 5 = 4` at
the descriptor, the vector a `< p`-scoped circuit could not even state. -/
theorem evmAdd_satisfiable_wrap :
    ∃ wv : ℕ → BabyBear,
      (∀ i : Fin 48, wv i.1 = encodeBoundary (2 ^ 256 - 1) 5 4 i) ∧
      descriptorHolds evmAddDescriptor wv :=
  (evmAddDescriptor_means_semantics (2 ^ 256 - 1) 5 4
    (by norm_num) (by norm_num) (by norm_num)).mpr conformance_v3_wrap

/-- *The mutation is real, asserted BEFORE the refusal is read*: the forged
claim `5` differs from the semantics' `4` on V3's inputs. -/
theorem forged_wrap_differs : (5 : ℕ) ≠ ((2 ^ 256 - 1) + 5) % 2 ^ 256 := by
  norm_num

/-- *Teeth at the DESCRIPTOR*: the forged claim `Z = 5` on V3's inputs admits
NO satisfying wire vector — and by the meaning theorem the refusal is a
statement about the machine semantics, not a coincidence of gates. -/
theorem evmAdd_forged_refused :
    ¬ ∃ wv : ℕ → BabyBear,
        (∀ i : Fin 48, wv i.1 = encodeBoundary (2 ^ 256 - 1) 5 5 i) ∧
        descriptorHolds evmAddDescriptor wv := by
  intro h
  have hrun := (evmAddDescriptor_means_semantics (2 ^ 256 - 1) 5 5
    (by norm_num) (by norm_num) (by norm_num)).mp h
  have := (fragment_run_eq_iff (2 ^ 256 - 1) 5 5
    (by norm_num) (by norm_num) (by norm_num)).mp hrun
  exact forged_wrap_differs this

/-- *…and at the DENOTATION*: the residual itself refutes the forged output on
the same inputs — the refusal happens at every layer of the chain. -/
theorem evmAdd_forged_denotation_fails :
    fragmentResidual.denote (calldataOf (2 ^ 256 - 1) 5) ≠ 5 := by
  intro h
  have := (fragment_run_eq_iff (2 ^ 256 - 1) 5 5
    (by norm_num) (by norm_num) (by norm_num)).mp
    (by rw [fragment_faithful, h])
  exact forged_wrap_differs this

/-! ## §6. The conformance artifact. Written by Lean, read by the unverified
prover; vector agreement is the whole claim at that seam — never verification. -/

#eval writeDescriptorJson "prover/testdata/evm_stage0_add_descriptor.json"
  evmAddDescriptor

/-! ## §7. Axiom accounting. -/

/-- info: 'Minidregg.Compiler.EvmAddAir.addModGadget_sound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms addModGadget_sound

/-- info: 'Minidregg.Compiler.EvmAddAir.evmAddAsg_accepts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evmAddAsg_accepts

/-- info: 'Minidregg.Compiler.EvmAddAir.evmAddDescriptor_means_semantics' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evmAddDescriptor_means_semantics

/-- info: 'Minidregg.Compiler.EvmAddAir.encodeBoundary_injective' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encodeBoundary_injective

/-- info: 'Minidregg.Compiler.EvmAddAir.evmAdd_forged_refused' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evmAdd_forged_refused

end Minidregg.Compiler.EvmAddAir
