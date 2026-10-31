/-
# `Compiler/AirCshake.lean` — cSHAKE256 over a public input length, as an Air system over `ZMod 2`

The sponge of `Sp800185Cshake256.cshake256Bytes` on `AirKeccak`'s permutation, for a PUBLIC
customization and a PUBLIC input length `len`; the input bytes are private wires, eight per
byte, never recomposed into one field element. The framing (customization prefix and the
multi-rate padding tail) depends only on the public data, so it enters as constants.

* `padded`, `padded_length`, `blocks`: the padded message and its block count, functions of
  the public data and the input; `cshake_eq`: the digest is the squeeze of its absorption.
* `spongeSystem cust len inputW trace`: per block `k`, an XOR row (`trace k 0` is the state
  so far XOR the block's bits) and `permSystem (trace k)`.
* `sponge_sound`: an accepted assignment whose input wires read `input` (`ReadsBytes`) has
  the last row reading the absorption; `cshake_sound`: its first 256 bits are the digest.
* `sponge_complete`: on an injective layout disjoint from the input wires, `spongeAsg`
  accepts and leaves every wire off the layout alone.
* `spongeSystem_length`: `blocks · 40000` constraints.
-/
module

public import Compiler.AirKeccak

@[expose] public section

namespace Minidregg.Compiler.AirCshake

open Minidregg.Compiler
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.AirKeccak

set_option autoImplicit false

/-! ## The padded message -/

def prefixOf (cust : List UInt8) : List UInt8 := if cust = [] then [] else customizationPrefix cust
def suffixOf (cust : List UInt8) : UInt8 := if cust = [] then 0x1f else 0x04

/-- The padding tail after `n` framed bytes. -/
def tailOf (n : Nat) (suffix : UInt8) : List UInt8 :=
  if rateBytes - n % rateBytes = 1 then [suffix ^^^ (128 : UInt8)]
  else [suffix] ++ List.replicate (rateBytes - n % rateBytes - 2) 0 ++ [128]

theorem padForRate_eq (bytes : List UInt8) (suffix : UInt8) :
    padForRate bytes suffix = bytes ++ tailOf bytes.length suffix := by
  unfold padForRate tailOf
  by_cases h : rateBytes - bytes.length % rateBytes = 1 <;> simp [h]

def padded (cust input : List UInt8) : List UInt8 :=
  padForRate (prefixOf cust ++ input) (suffixOf cust)

theorem cshake_eq (cust input : List UInt8) :
    cshake256Bytes cust input = squeeze32 (absorbPadded (padded cust input)) := by
  simp only [cshake256Bytes, padded, prefixOf, suffixOf]
  split <;> simp_all

theorem tailOf_length (n : Nat) (suffix : UInt8) :
    (tailOf n suffix).length = rateBytes - n % rateBytes := by
  unfold tailOf
  have : n % rateBytes < rateBytes := Nat.mod_lt _ (by decide)
  split <;> simp [rateBytes] at * <;> omega

def framedLen (cust : List UInt8) (len : Nat) : Nat := (prefixOf cust).length + len
def paddedLen (cust : List UInt8) (len : Nat) : Nat :=
  framedLen cust len + (rateBytes - framedLen cust len % rateBytes)
def blocks (cust : List UInt8) (len : Nat) : Nat := paddedLen cust len / rateBytes

theorem padded_eq (cust input : List UInt8) :
    padded cust input = prefixOf cust ++ input ++ tailOf (prefixOf cust ++ input).length (suffixOf cust) := by
  simp only [padded, padForRate_eq]

theorem padded_length (cust input : List UInt8) :
    (padded cust input).length = paddedLen cust input.length := by
  rw [padded_eq]
  simp only [List.length_append, tailOf_length, paddedLen, framedLen]

theorem paddedLen_eq (cust : List UInt8) (len : Nat) :
    paddedLen cust len = blocks cust len * rateBytes := by
  simp only [blocks, paddedLen, rateBytes]
  omega

theorem blocks_pos (cust : List UInt8) (len : Nat) : 0 < blocks cust len := by
  simp only [blocks, paddedLen, rateBytes]
  omega

/-! ## Bits of blocks and of the squeeze -/

private theorem uint8_testBit_high (b : UInt8) (k : Nat) (hk : 8 ≤ k) : b.toNat.testBit k = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le b.toNat_lt (Nat.pow_le_pow_right (by decide) hk))

private theorem term_bit (b : UInt8) (o z : Nat) :
    (decide (8 * o ≤ z) && b.toNat.testBit (z - 8 * o)) = (decide (z / 8 = o) && b.toNat.testBit (z % 8)) := by
  by_cases h : z / 8 = o
  · have h1 : 8 * o ≤ z := by omega
    have h2 : z - 8 * o = z % 8 := by omega
    simp [h, h1, h2]
  · simp only [h, decide_false, Bool.false_and]
    by_cases h1 : 8 * o ≤ z
    · simp only [h1, decide_true, Bool.true_and]
      exact uint8_testBit_high _ _ (by omega)
    · simp [h1]

theorem laneFromBlock_bit (blk : List UInt8) (l : Nat) (z : Fin 64) :
    (laneFromBlock blk l).getLsbD z = (blk.getD (8 * l + z.val / 8) 0).toNat.testBit (z.val % 8) := by
  simp only [laneFromBlock, List.range_succ, List.range_zero, List.nil_append, List.foldl_cons,
    List.foldl_nil, List.foldl_append, BitVec.getLsbD_xor, BitVec.getLsbD_ofNat,
    Nat.testBit_mul_two_pow, getLsbD_zeroLane, Bool.false_xor, z.isLt, decide_true, Bool.true_and,
    term_bit]
  have hq : z.val / 8 < 8 := by omega
  generalize z.val / 8 = q at hq ⊢
  rcases q with _ | _ | _ | _ | _ | _ | _ | _ | q <;> first | omega | simp

theorem xorRateBlock_bit (st : State) (blk : List UInt8) (t : Fin 25) (z : Fin 64) :
    bitsOf (xorRateBlock st blk) t z =
      (bitsOf st t z ^^ (decide (t.val < rateLanes) &&
        (blk.getD (8 * t.val + z.val / 8) 0).toNat.testBit (z.val % 8))) := by
  simp only [bitsOf, xorRateBlock]
  rw [getD_ofFn _ _ t.isLt]
  by_cases h : t.val < rateLanes
  · rw [if_pos h, BitVec.getLsbD_xor, laneFromBlock_bit]
    simp only [h, decide_true, Bool.true_and]
  · rw [if_neg h]
    simp only [h, decide_false, Bool.false_and, Bool.xor_false]

theorem squeeze_bit (st : State) (i : Nat) (hi : i < 32) (j : Fin 8) :
    ((squeeze32 st).getD i 0).toNat.testBit j =
      bitsOf st ⟨i / 8, by omega⟩ ⟨8 * (i % 8) + j.val, by omega⟩ := by
  have hlen : i < (List.range outputBytes).length := by simp [outputBytes]; omega
  simp only [squeeze32, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range
    (show i < outputBytes by simp [outputBytes]; omega), Option.map_some, Option.getD_some,
    stateByte, bitsOf]
  rw [UInt8.toNat_ofNat', show (2 : Nat) ^ 8 = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow,
    show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    BitVec.testBit_toNat]
  simp only [j.isLt, decide_true, Bool.true_and]
  congr 1
  omega

/-! ## The absorption, block by block -/

def block (msg : List UInt8) (k : Nat) : List UInt8 := (msg.drop (k * rateBytes)).take rateBytes

def stAfter (msg : List UInt8) (k : Nat) : State :=
  (List.range' 0 k).foldl (fun s b => keccakF1600 (xorRateBlock s (block msg b))) zeroState

theorem stAfter_zero (msg : List UInt8) : stAfter msg 0 = zeroState := rfl

theorem stAfter_succ (msg : List UInt8) (k : Nat) :
    stAfter msg (k + 1) = keccakF1600 (xorRateBlock (stAfter msg k) (block msg k)) := by
  simp [stAfter, List.range'_concat, List.foldl_append]

theorem absorbPadded_eq (msg : List UInt8) :
    absorbPadded msg = stAfter msg (msg.length / rateBytes) := by
  have := absorbFrom_eq_indexed msg (msg.length / rateBytes) 0 zeroState
  simpa [absorbPadded, stAfter, block] using this

theorem block_getD (msg : List UInt8) (k m : Nat) (hm : m < rateBytes) :
    (block msg k).getD m 0 = msg.getD (k * rateBytes + m) 0 := by
  simp [block, List.getD_eq_getElem?_getD, List.getElem?_take, hm, List.getElem?_drop]

theorem bitsOf_zeroState (t : Fin 25) (z : Fin 64) : bitsOf zeroState t z = false := by
  unfold bitsOf
  rw [show zeroState.getD t zeroLane = zeroLane from by simp [zeroState, Array.getD]]
  exact getLsbD_zeroLane _

/-! ## The constraint system -/

variable {Idx : Type}

/-- An input row reads `input`, bit by bit. -/
def ReadsBytes (asg : Idx → F2) (inputW : Nat → Fin 8 → Idx) (input : List UInt8) : Prop :=
  ∀ p < input.length, ∀ j : Fin 8, asg (inputW p j) = toF ((input.getD p 0).toNat.testBit j)

/-- Bit `j` of padded byte `p`: a public constant outside the input, else an input wire. -/
def byteBitT (cust : List UInt8) (len : Nat) (inputW : Nat → Fin 8 → Idx) (p : Nat) (j : Fin 8) :
    T (Idx := Idx) :=
  if p < (prefixOf cust).length then cst (toF (((prefixOf cust).getD p 0).toNat.testBit j))
  else if p < (prefixOf cust).length + len then vr (inputW (p - (prefixOf cust).length) j)
  else cst (toF (((tailOf ((prefixOf cust).length + len) (suffixOf cust)).getD
    (p - (prefixOf cust).length - len) 0).toNat.testBit j))

private theorem getD_append_lt (l₁ l₂ : List UInt8) (p : Nat) (h : p < l₁.length) :
    (l₁ ++ l₂).getD p 0 = l₁.getD p 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_ge (l₁ l₂ : List UInt8) (p : Nat) (h : l₁.length ≤ p) :
    (l₁ ++ l₂).getD p 0 = l₂.getD (p - l₁.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem eval_byteBitT (cust : List UInt8) (inputW : Nat → Fin 8 → Idx) (asg : Idx → F2)
    (input : List UInt8) (reads : ReadsBytes asg inputW input) (p : Nat) (j : Fin 8) :
    eval asg (byteBitT cust input.length inputW p j) =
      toF (((padded cust input).getD p 0).toNat.testBit j) := by
  rw [padded_eq]
  simp only [byteBitT]
  split
  · rename_i h
    rw [eval_cst, getD_append_lt _ _ _ (by simp; omega), getD_append_lt _ _ _ h]
  · rename_i h
    split
    · rename_i h'
      rw [eval_vr, reads _ (by omega), getD_append_lt _ _ _ (by simp; omega),
        getD_append_ge _ _ _ (by omega)]
    · rename_i h'
      rw [eval_cst, getD_append_ge _ _ _ (by simp; omega)]
      simp only [List.length_append]
      congr 4
      omega

variable (cust : List UInt8) (len : Nat) (inputW : Nat → Fin 8 → Idx)
  (trace : Nat → Fin 25 → Fin 25 → Fin 64 → Idx)

/-- The state before block `k`: zero, or the last row of block `k - 1`. -/
def prevT (k : Nat) (t : Fin 25) (z : Fin 64) : T (Idx := Idx) :=
  if k = 0 then cst 0 else vr (trace (k - 1) 24 t z)

/-- Bit `(t, z)` of block `k`: a padded byte bit in the rate lanes, zero in the capacity. -/
def blockT (k : Nat) (t : Fin 25) (z : Fin 64) : T (Idx := Idx) :=
  if t.val < rateLanes then
    byteBitT cust len inputW (k * rateBytes + (8 * t.val + z.val / 8)) ⟨z.val % 8, by omega⟩
  else cst 0

/-- Block `k`'s XOR row: `trace k 0 ⊕ prev ⊕ block ≐ 0`, 1600 linear constraints. -/
def xorRow (k : Nat) : ConstraintSystem F2 Idx :=
  (List.finRange 25).flatMap fun t => (List.finRange 64).map fun z =>
    add' (add' (vr (trace k 0 t z)) (prevT trace k t z)) (blockT cust len inputW k t z)

/-- **cSHAKE256 at a public length**: per block, its XOR row and the permutation. -/
def spongeSystem : ConstraintSystem F2 Idx :=
  (List.range (blocks cust len)).flatMap fun k => xorRow cust len inputW trace k ++ permSystem (trace k)

theorem spongeSystem_length :
    (spongeSystem cust len inputW trace).length = blocks cust len * 40000 := by
  simp [spongeSystem, xorRow, List.length_flatMap, permSystem_length, List.sum_replicate]

private theorem f2_three (a b c : F2) : a + b + c = 0 ↔ a = b + c := by
  revert a b c; decide

/-- The XOR row accepts iff its row is the previous state XOR the block. -/
theorem xorRow_accepts (asg : Idx → F2) (k : Nat) :
    systemAccepts asg (xorRow cust len inputW trace k) ↔
      ∀ t z, asg (trace k 0 t z) = eval asg (prevT trace k t z) + eval asg (blockT cust len inputW k t z) := by
  simp only [systemAccepts, xorRow, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and,
    forall_exists_index]
  constructor
  · intro h t z
    have := h _ t z rfl
    rwa [accepts, eval_add', eval_add', eval_vr, f2_three] at this
  · rintro h _ t z rfl
    rw [accepts, eval_add', eval_add', eval_vr, f2_three]
    exact h t z

private theorem eval_blockT (asg : Idx → F2) (input : List UInt8) (reads : ReadsBytes asg inputW input)
    (k : Nat) (t : Fin 25) (z : Fin 64) :
    eval asg (blockT cust input.length inputW k t z) =
      toF (decide (t.val < rateLanes) &&
        ((block (padded cust input) k).getD (8 * t.val + z.val / 8) 0).toNat.testBit (z.val % 8)) := by
  simp only [blockT]
  split
  · rename_i h
    have hm : 8 * t.val + z.val / 8 < rateBytes := by simp [rateLanes, rateBytes] at h ⊢; omega
    rw [eval_byteBitT cust inputW asg input reads, block_getD _ _ _ hm]
    simp [h]
  · rename_i h
    simp [h, eval_cst, toF]

private theorem reads_of (asg : Idx → F2) (w : Fin 25 → Fin 64 → Idx) (st : State)
    (h : ∀ t z, asg (w t z) = toF (bitsOf st t z)) : Reads asg w st := by
  funext t z
  simp only [rb, h]
  cases bitsOf st t z <;> decide

theorem accepts_block (asg : Idx → F2) (accepted : systemAccepts asg (spongeSystem cust len inputW trace))
    (k : Nat) (hk : k < blocks cust len) :
    systemAccepts asg (xorRow cust len inputW trace k) ∧ systemAccepts asg (permSystem (trace k)) :=
  ⟨fun c hc => accepted c (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_append_left _ hc⟩),
   fun c hc => accepted c (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_append_right _ hc⟩)⟩

/-- One block: an accepted XOR row over the state after `k` blocks, then an accepted
permutation, reads the state after `k + 1` blocks. -/
theorem block_step (asg : Idx → F2) (input : List UInt8) (reads : ReadsBytes asg inputW input) (k : Nat)
    (accX : systemAccepts asg (xorRow cust input.length inputW trace k))
    (accP : systemAccepts asg (permSystem (trace k)))
    (prev : ∀ t z, eval asg (prevT trace k t z) = toF (bitsOf (stAfter (padded cust input) k) t z)) :
    Reads asg (trace k 0) (xorRateBlock (stAfter (padded cust input) k) (block (padded cust input) k)) ∧
      Reads asg (trace k 24) (stAfter (padded cust input) (k + 1)) := by
  have hx : Reads asg (trace k 0)
      (xorRateBlock (stAfter (padded cust input) k) (block (padded cust input) k)) := by
    apply reads_of
    intro t z
    rw [(xorRow_accepts cust input.length inputW trace asg k).mp accX t z, prev,
      eval_blockT cust inputW asg input reads, xorRateBlock_bit, toF_xor]
  refine ⟨hx, ?_⟩
  rw [stAfter_succ]
  exact (perm_sound asg (trace k) _ hx accP).2

theorem prev_reads (asg : Idx → F2) (msg : List UInt8) (k : Nat)
    (earlier : k ≠ 0 → Reads asg (trace (k - 1) 24) (stAfter msg k)) (t : Fin 25) (z : Fin 64) :
    eval asg (prevT trace k t z) = toF (bitsOf (stAfter msg k) t z) := by
  simp only [prevT]
  split
  · rename_i h
    subst h
    rw [eval_cst, stAfter_zero, bitsOf_zeroState]; rfl
  · rename_i h
    rw [eval_vr, ← toF_rb asg (trace (k - 1) 24) t z, earlier h]

/-- **Sound**: an accepted sponge whose input row reads `input` has block `k`'s last row
reading the state after `k + 1` blocks. -/
theorem sponge_sound (asg : Idx → F2) (input : List UInt8) (reads : ReadsBytes asg inputW input)
    (accepted : systemAccepts asg (spongeSystem cust input.length inputW trace)) :
    ∀ k < blocks cust input.length, Reads asg (trace k 24) (stAfter (padded cust input) (k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    obtain ⟨accX, accP⟩ := accepts_block cust _ inputW trace asg accepted 0 hk
    exact (block_step cust inputW trace asg input reads 0 accX accP
      (prev_reads trace asg _ 0 (fun h => absurd rfl h))).2
  | succ k ih =>
    intro hk
    obtain ⟨accX, accP⟩ := accepts_block cust _ inputW trace asg accepted (k + 1) hk
    exact (block_step cust inputW trace asg input reads (k + 1) accX accP
      (prev_reads trace asg _ (k + 1) fun _ => ih (by omega))).2

theorem absorb_full (cust input : List UInt8) :
    absorbPadded (padded cust input) = stAfter (padded cust input) (blocks cust input.length) := by
  rw [absorbPadded_eq, padded_length, paddedLen_eq, Nat.mul_div_cancel _ (by decide)]

/-- **The digest**: an accepted sponge's last row carries `cshake256Bytes cust input` in its
first 256 bits, byte `i` bit `j` at lane `i / 8`, bit `8 (i mod 8) + j`. -/
theorem cshake_sound (asg : Idx → F2) (input : List UInt8) (reads : ReadsBytes asg inputW input)
    (accepted : systemAccepts asg (spongeSystem cust input.length inputW trace))
    (i : Nat) (hi : i < 32) (j : Fin 8) :
    rb asg (trace (blocks cust input.length - 1) 24) ⟨i / 8, by omega⟩ ⟨8 * (i % 8) + j.val, by omega⟩ =
      ((cshake256Bytes cust input).getD i 0).toNat.testBit j := by
  have hpos := blocks_pos cust input.length
  have last := sponge_sound cust inputW trace asg input reads accepted _ (by omega : blocks cust input.length - 1 < _)
  rw [Nat.sub_add_cancel hpos] at last
  rw [cshake_eq, absorb_full, squeeze_bit _ _ hi, last]

/-! ## Completeness: the canonical sponge assignment -/

section Complete

variable [DecidableEq Idx]

/-- A layout position: block, row, lane, bit. -/
abbrev Key := Nat × Fin 25 × Fin 25 × Fin 64

/-- Every layout position of `nb` blocks. -/
def keys (nb : Nat) : List Key :=
  (List.range nb).flatMap fun k => (List.finRange 25).flatMap fun r =>
    (List.finRange 25).flatMap fun t => (List.finRange 64).map fun z => (k, r, t, z)

theorem mem_keys (nb k : Nat) (r t : Fin 25) (z : Fin 64) : (k, r, t, z) ∈ keys nb ↔ k < nb := by
  simp [keys]

def wireOf (x : Key) : Idx := trace x.1 x.2.1 x.2.2.1 x.2.2.2

/-- Overwrite the wires of `ks` with `val`; every other wire keeps `asg`. -/
def fill (ks : List Key) (wire : Key → Idx) (val : Key → F2) (asg : Idx → F2) : Idx → F2 :=
  fun i => match ks.find? (fun x => wire x = i) with
    | some x => val x
    | none => asg i

theorem fill_hit (ks : List Key) (wire : Key → Idx) (val : Key → F2) (asg : Idx → F2)
    (inj : ∀ x ∈ ks, ∀ y ∈ ks, wire x = wire y → x = y) (x : Key) (hx : x ∈ ks) :
    fill ks wire val asg (wire x) = val x := by
  unfold fill
  split
  · rename_i y hy
    have hyx := List.find?_some hy
    simp only [decide_eq_true_eq] at hyx
    rw [inj _ (List.mem_of_find?_eq_some hy) _ hx hyx]
  · rename_i hn
    exfalso
    rw [List.find?_eq_none] at hn
    exact hn x hx (by simp)

theorem fill_miss (ks : List Key) (wire : Key → Idx) (val : Key → F2) (asg : Idx → F2) (i : Idx)
    (h : ∀ x ∈ ks, wire x ≠ i) : fill ks wire val asg i = asg i := by
  unfold fill
  split
  · rename_i y hy
    have hyx := List.find?_some hy
    simp only [decide_eq_true_eq] at hyx
    exact absurd hyx (h y (List.mem_of_find?_eq_some hy))
  · rfl

/-- The row `r` of block `k` in the specification: `r` rounds into the permutation of the
state after `k` blocks XOR block `k`. -/
def specRow (msg : List UInt8) (k : Nat) (r : Fin 25) : State :=
  after (xorRateBlock (stAfter msg k) (block msg k)) r

/-- **The canonical sponge assignment**: every layout wire carries its specification bit. -/
def spongeAsg (asg : Idx → F2) (input : List UInt8) : Idx → F2 :=
  fill (keys (blocks cust input.length)) (wireOf trace)
    (fun x => toF (bitsOf (specRow (padded cust input) x.1 x.2.1) x.2.2.1 x.2.2.2)) asg

/-- **Complete**: on a layout injective over its blocks and disjoint from the input wires, an
assignment whose input row reads `input` becomes an accepted sponge by `spongeAsg`, which keeps
every wire off the layout (the input row among them). -/
theorem sponge_complete (asg : Idx → F2) (input : List UInt8) (reads : ReadsBytes asg inputW input)
    (inj : ∀ x ∈ keys (blocks cust input.length), ∀ y ∈ keys (blocks cust input.length),
      wireOf trace x = wireOf trace y → x = y)
    (disjoint : ∀ p < input.length, ∀ j : Fin 8, ∀ x ∈ keys (blocks cust input.length),
      wireOf trace x ≠ inputW p j) :
    systemAccepts (spongeAsg cust trace asg input) (spongeSystem cust input.length inputW trace) ∧
      ∀ i, (∀ x ∈ keys (blocks cust input.length), wireOf trace x ≠ i) →
        spongeAsg cust trace asg input i = asg i := by
  set A := spongeAsg cust trace asg input with hA
  set msg := padded cust input
  have rows : ∀ k < blocks cust input.length, ∀ r : Fin 25, Reads A (trace k r) (specRow msg k r) := by
    intro k hk r
    apply reads_of
    intro t z
    exact fill_hit _ (wireOf trace) _ asg inj (k, r, t, z) ((mem_keys _ _ _ _ _).mpr hk)
  have reads' : ReadsBytes A inputW input := by
    intro p hp j
    rw [hA, spongeAsg, fill_miss _ _ _ _ _ (fun x hx => disjoint p hp j x hx)]
    exact reads p hp j
  refine ⟨?_, fun i off => fill_miss _ _ _ _ _ off⟩
  intro c hc
  obtain ⟨k, hk, hc⟩ := List.mem_flatMap.mp hc
  have hk : k < blocks cust input.length := List.mem_range.mp hk
  rcases List.mem_append.mp hc with hx | hp
  · refine (xorRow_accepts cust input.length inputW trace A k).mpr (fun t z => ?_) c hx
    have earlier : k ≠ 0 → Reads A (trace (k - 1) 24) (stAfter msg k) := by
      intro hk0
      have := rows (k - 1) (by omega) 24
      rwa [specRow, show ((24 : Fin 25) : Nat) = 24 from rfl, after_full, ← stAfter_succ,
        Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)] at this
    rw [prev_reads trace A msg k earlier, eval_blockT cust inputW A input reads', ← toF_xor,
      ← xorRateBlock_bit, ← toF_rb A (trace k 0) t z, rows k hk 0]
    rfl
  · refine (perm_accepts A (trace k)).mpr (fun r => ?_) c hp
    rw [rows k hk r.succ, rows k hk r.castSucc]
    funext t z
    simp only [specRow, Fin.val_succ, Fin.coe_castSucc, after_succ]
    exact roundB_spec _ _ t z

end Complete

#assert_axioms padForRate_eq
#assert_axioms cshake_eq
#assert_axioms laneFromBlock_bit
#assert_axioms xorRateBlock_bit
#assert_axioms squeeze_bit
#assert_axioms absorbPadded_eq
#assert_axioms spongeSystem_length
#assert_axioms sponge_sound
#assert_axioms cshake_sound
#assert_axioms sponge_complete

end Minidregg.Compiler.AirCshake
