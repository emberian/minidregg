/-
# `Compiler/AirKeccak.lean` — Keccak-f[1600] as an Air constraint system over `ZMod 2`

Over `ZMod 2` the Air DSL's `add'` is XOR and `mul'` is AND, so a constraint system is a
Boolean circuit whose every constraint root is zero-checked on its own (no residual sum).
This file grows the Keccak permutation on that rung, against the specification
`Sp800185Cshake256.round` / `keccakF1600` that every cSHAKE theorem in the repository is
about.

Terms are trees, so each round's 1600-bit state is a row of witness wires: one round is
1600 constraints `out ≐ ι(χ(ρπ(θ(in))))`, each a tree over at most 33 input wires with one
AND (χ). Shared θ subterms are shared downstream by `EmitShare.cse`.

* `bitsOf`, `roundB` — a round, bit by bit; `roundB_spec`: it is the specification's round.
* `roundSystem`, `round_accepts` — the constraint system accepts iff the output row is
  `roundB` of the input row; `round_reads` restates it against a specification state.
* `permSystem`, `perm_accepts` — acceptance is exactly every one of the 24 transitions;
  `perm_sound`: an accepted trace whose first row reads `st` ends at `keccakF1600 st`;
  `perm_complete`: on an injective trace layout, every first row extends to an accepted
  trace (the canonical trace `traceAsg`); `perm_trace_unique`: that trace is the only one.
* `roundSystem_length`, `permSystem_length` — 1600 and 38 400 constraints.
-/
module

public import Compiler.AirRange
public import Theory.Sp800185Cshake256Core

@[expose] public section

namespace Minidregg.Compiler.AirKeccak

open Minidregg.Compiler
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Sp800185Cshake256.Fast (rpSource rhoPi_getElem? xorColumn_five)

set_option autoImplicit false

/-! ## Bits of a state, and a round bit by bit -/

/-- Lane `x + 5y` (coordinates reduced mod 5). -/
def ix (x y : Nat) : Fin 25 := ⟨x % 5 + 5 * (y % 5), by omega⟩

/-- Bit `z` of a lane rotated left by `r` reads bit `rot z r` of the lane. -/
def rot (z : Fin 64) (r : Nat) : Fin 64 := ⟨(z.val + 64 - r % 64) % 64, Nat.mod_lt _ (by decide)⟩

/-- The bits of a specification state (lanes past the end read zero). -/
def bitsOf (st : State) (i : Fin 25) (z : Fin 64) : Bool := (st.getD i zeroLane).getLsbD z

/-- Column parity bit. -/
def colB (B : Fin 25 → Fin 64 → Bool) (x : Nat) (z : Fin 64) : Bool :=
  B (ix x 0) z ^^ B (ix x 1) z ^^ B (ix x 2) z ^^ B (ix x 3) z ^^ B (ix x 4) z

def thetaB (B : Fin 25 → Fin 64 → Bool) (i : Fin 25) (z : Fin 64) : Bool :=
  B i z ^^ colB B (i.val % 5 + 4) z ^^ colB B (i.val % 5 + 1) (rot z 1)

/-- The rho/pi source lane of target `t` and its rotation. -/
def srcOf (t : Fin 25) : Fin 25 := ix (rpSource t % 5) (rpSource t / 5)
def rotOf (t : Fin 25) : Nat := rotationOffset (rpSource t % 5) (rpSource t / 5)

def rhoB (B : Fin 25 → Fin 64 → Bool) (t : Fin 25) (z : Fin 64) : Bool :=
  thetaB B (srcOf t) (rot z (rotOf t))

def chiB (B : Fin 25 → Fin 64 → Bool) (t : Fin 25) (z : Fin 64) : Bool :=
  rhoB B t z ^^ (!rhoB B (ix (t.val % 5 + 1) (t.val / 5)) z && rhoB B (ix (t.val % 5 + 2) (t.val / 5)) z)

/-- One round, bit by bit. -/
def roundB (B : Fin 25 → Fin 64 → Bool) (c : Lane) (t : Fin 25) (z : Fin 64) : Bool :=
  chiB B t z ^^ (decide (t.val = 0) && c.getLsbD z)

/-! ### `roundB` is the specification's round -/

private theorem getD_ofFn {n : Nat} (f : Fin n → Lane) (i : Nat) (h : i < n) :
    (Array.ofFn f).getD i zeroLane = f ⟨i, h⟩ := by
  simp [Array.getD, h]

private theorem lane_ix (st : State) (x y : Nat) : lane st x y = st.getD (ix x y) zeroLane := rfl

private theorem ix_self (i : Fin 25) : ix (i.val % 5) (i.val / 5) = i := by
  ext; simp only [ix]; omega

private theorem getLsbD_rotateLeft_rot (v : Lane) (r : Nat) (z : Fin 64) :
    (v.rotateLeft r).getLsbD z = v.getLsbD (rot z r) := by
  rw [BitVec.getLsbD_rotateLeft]
  have hz := z.isLt
  have hr : r % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [rot]
  split
  · congr 1; omega
  · simp only [show decide ((z : Nat) < 64) = true from by simp [hz], Bool.true_and]
    congr 1; omega

private theorem getLsbD_zeroLane (z : Nat) : zeroLane.getLsbD z = false := by
  simp [zeroLane]

private theorem xorColumn_bit (st : State) (x : Nat) (z : Fin 64) :
    (xorColumn st x).getLsbD z = colB (bitsOf st) x z := by
  rw [xorColumn_five]
  simp only [BitVec.getLsbD_xor, getLsbD_zeroLane, Bool.false_xor, colB, bitsOf, lane_ix]

private theorem theta_bit (st : State) (i : Fin 25) (z : Fin 64) :
    bitsOf (theta st) i z = thetaB (bitsOf st) i z := by
  simp only [bitsOf, theta]
  rw [getD_ofFn _ _ i.isLt]
  simp only [BitVec.getLsbD_xor, getLsbD_rotateLeft_rot, thetaB, lane_ix, ix_self]
  rw [xorColumn_bit, xorColumn_bit]
  simp only [bitsOf]

private theorem rpSource_lt (t : Fin 25) : rpSource t < 25 := by
  revert t; decide

private theorem rhoPi_bit (st : State) (t : Fin 25) (z : Fin 64) :
    bitsOf (rhoPi st) t z = bitsOf st (srcOf t) (rot z (rotOf t)) := by
  have hget := rhoPi_getElem? st t t.isLt
  have hd : (rhoPi st).getD t zeroLane = Fast.rpValue st (rpSource t) := by
    simp [Array.getD_eq_getD_getElem?, hget]
  simp only [bitsOf, hd, Fast.rpValue, getLsbD_rotateLeft_rot, lane_ix, rotOf, srcOf]

private theorem chi_bit (M : State) (t : Fin 25) (z : Fin 64) :
    bitsOf (chi M) t z =
      (bitsOf M t z ^^ (!bitsOf M (ix (t.val % 5 + 1) (t.val / 5)) z &&
        bitsOf M (ix (t.val % 5 + 2) (t.val / 5)) z)) := by
  simp only [bitsOf, chi]
  rw [getD_ofFn _ _ t.isLt]
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, lane_ix, ix_self, Fin.eta,
    z.isLt, decide_true, Bool.true_and]

private theorem chi_size (M : State) : (chi M).size = 25 := by simp [chi]

/-- **A round, bit by bit, is the specification's round.** -/
theorem roundB_spec (st : State) (c : Lane) (t : Fin 25) (z : Fin 64) :
    bitsOf (round st c) t z = roundB (bitsOf st) c t z := by
  simp only [round]
  have hset : ((chi (rhoPi (theta st))).setIfInBounds 0
      (lane (chi (rhoPi (theta st))) 0 0 ^^^ c)).getD t zeroLane =
      if t.val = 0 then lane (chi (rhoPi (theta st))) 0 0 ^^^ c
      else (chi (rhoPi (theta st))).getD t zeroLane := by
    have ht : (t : Nat) < ((chi (rhoPi (theta st))).setIfInBounds 0
        (lane (chi (rhoPi (theta st))) 0 0 ^^^ c)).size := by
      rw [Array.size_setIfInBounds, chi_size]; exact t.isLt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ht, Option.getD_some,
      Array.getElem_setIfInBounds (by rw [chi_size]; exact t.isLt)]
    by_cases h0 : (t : Nat) = 0
    · simp [h0]
    · have hne : (0 : Nat) ≠ t := fun h => h0 h.symm
      simp only [hne, if_false, h0]
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [chi_size]; exact t.isLt),
        Option.getD_some]
  have hbit : bitsOf ((chi (rhoPi (theta st))).setIfInBounds 0
      (lane (chi (rhoPi (theta st))) 0 0 ^^^ c)) t z =
      (bitsOf (chi (rhoPi (theta st))) t z ^^ (decide (t.val = 0) && c.getLsbD z)) := by
    simp only [bitsOf]
    rw [hset]
    by_cases h0 : (t : Nat) = 0
    · have hix : ((ix 0 0 : Fin 25) : Nat) = t := by simp [ix, h0]
      simp only [h0, if_true, BitVec.getLsbD_xor, lane_ix, hix, decide_true, Bool.true_and]
    · simp only [h0, if_false, decide_false, Bool.false_and, Bool.xor_false]
  rw [hbit, chi_bit]
  simp only [rhoPi_bit, theta_bit, roundB, chiB, rhoB]

/-! ## The constraint system -/

abbrev F2 := ZMod 2

variable {Idx : Type}

/-- The bit an assignment puts on a wire. -/
def rb (asg : Idx → F2) (w : Fin 25 → Fin 64 → Idx) (i : Fin 25) (z : Fin 64) : Bool :=
  decide (asg (w i z) = 1)

/-- A Boolean as a field element. -/
def toF (b : Bool) : F2 := if b then 1 else 0

private theorem toF_rb (asg : Idx → F2) (w : Fin 25 → Fin 64 → Idx) (i : Fin 25) (z : Fin 64) :
    toF (rb asg w i z) = asg (w i z) := by
  have key : ∀ v : F2, (if decide (v = 1) = true then (1 : F2) else 0) = v := by decide
  exact key _

private theorem toF_xor (a b : Bool) : toF (a ^^ b) = toF a + toF b := by
  cases a <;> cases b <;> decide
private theorem toF_and (a b : Bool) : toF (a && b) = toF a * toF b := by
  cases a <;> cases b <;> decide
private theorem toF_not (a : Bool) : toF (!a) = 1 + toF a := by
  cases a <;> decide

abbrev T := Term (AirSig F2 Idx)

def bitT (w : Fin 25 → Fin 64 → Idx) (i : Fin 25) (z : Fin 64) : T (Idx := Idx) := vr (w i z)

def colT (w : Fin 25 → Fin 64 → Idx) (x : Nat) (z : Fin 64) : T (Idx := Idx) :=
  add' (add' (add' (add' (bitT w (ix x 0) z) (bitT w (ix x 1) z)) (bitT w (ix x 2) z))
    (bitT w (ix x 3) z)) (bitT w (ix x 4) z)

def thetaT (w : Fin 25 → Fin 64 → Idx) (i : Fin 25) (z : Fin 64) : T (Idx := Idx) :=
  add' (add' (bitT w i z) (colT w (i.val % 5 + 4) z)) (colT w (i.val % 5 + 1) (rot z 1))

def rhoT (w : Fin 25 → Fin 64 → Idx) (t : Fin 25) (z : Fin 64) : T (Idx := Idx) :=
  thetaT w (srcOf t) (rot z (rotOf t))

def chiT (w : Fin 25 → Fin 64 → Idx) (t : Fin 25) (z : Fin 64) : T (Idx := Idx) :=
  add' (rhoT w t z) (mul' (add' (cst 1) (rhoT w (ix (t.val % 5 + 1) (t.val / 5)) z))
    (rhoT w (ix (t.val % 5 + 2) (t.val / 5)) z))

def roundT (w : Fin 25 → Fin 64 → Idx) (c : Lane) (t : Fin 25) (z : Fin 64) : T (Idx := Idx) :=
  add' (chiT w t z) (cst (toF (decide (t.val = 0) && c.getLsbD z)))

/-- **One round**: 1600 constraints `out ⊕ round(in) ≐ 0`. -/
def roundSystem (inp out : Fin 25 → Fin 64 → Idx) (c : Lane) : ConstraintSystem F2 Idx :=
  (List.finRange 25).flatMap fun t => (List.finRange 64).map fun z =>
    add' (vr (out t z)) (roundT inp c t z)

private theorem eval_roundT (asg : Idx → F2) (w : Fin 25 → Fin 64 → Idx) (c : Lane)
    (t : Fin 25) (z : Fin 64) :
    eval asg (roundT w c t z) = toF (roundB (rb asg w) c t z) := by
  simp only [roundT, chiT, rhoT, thetaT, colT, bitT, eval_add', eval_mul', eval_cst, eval_vr,
    roundB, chiB, rhoB, thetaB, colB, toF_xor, toF_and, toF_not, toF_rb]

private theorem f2_add_eq_zero (a b : F2) : a + b = 0 ↔ a = b := by
  revert a b; decide

private theorem toF_inj (a b : Bool) : toF a = toF b ↔ a = b := by
  cases a <;> cases b <;> decide

/-- **A round accepts iff the output row is the round of the input row.** -/
theorem round_accepts (asg : Idx → F2) (inp out : Fin 25 → Fin 64 → Idx) (c : Lane) :
    systemAccepts asg (roundSystem inp out c) ↔ rb asg out = roundB (rb asg inp) c := by
  simp only [systemAccepts, roundSystem, List.mem_flatMap, List.mem_map, List.mem_finRange,
    true_and, forall_exists_index]
  constructor
  · intro h
    funext t z
    have := h _ t z rfl
    rw [accepts, eval_add', eval_vr, eval_roundT, f2_add_eq_zero, ← toF_rb asg out t z, toF_inj] at this
    exact this
  · rintro h _ t z rfl
    rw [accepts, eval_add', eval_vr, eval_roundT, f2_add_eq_zero, ← toF_rb asg out t z, toF_inj, h]

/-- A row of wires reads a specification state. -/
def Reads (asg : Idx → F2) (w : Fin 25 → Fin 64 → Idx) (st : State) : Prop := rb asg w = bitsOf st

theorem round_reads (asg : Idx → F2) (inp out : Fin 25 → Fin 64 → Idx) (c : Lane) (st : State)
    (reads : Reads asg inp st) :
    systemAccepts asg (roundSystem inp out c) ↔ Reads asg out (round st c) := by
  rw [round_accepts, Reads, reads]
  constructor
  · intro h; rw [h]; funext t z; exact (roundB_spec st c t z).symm
  · intro h; rw [h]; funext t z; exact roundB_spec st c t z

/-! ## The permutation: 24 rows of transitions -/

/-- The round constant of round `r`. -/
def constantOf (r : Fin 24) : Lane := roundConstants.getD r zeroLane

/-- **The permutation**: row `r.succ` is the round of row `r.castSucc`, for every `r`. -/
def permSystem (trace : Fin 25 → Fin 25 → Fin 64 → Idx) : ConstraintSystem F2 Idx :=
  (List.finRange 24).flatMap fun r => roundSystem (trace r.castSucc) (trace r.succ) (constantOf r)

/-- **Acceptance is exactly every transition.** -/
theorem perm_accepts (asg : Idx → F2) (trace : Fin 25 → Fin 25 → Fin 64 → Idx) :
    systemAccepts asg (permSystem trace) ↔
      ∀ r : Fin 24, rb asg (trace r.succ) = roundB (rb asg (trace r.castSucc)) (constantOf r) := by
  simp only [permSystem, systemAccepts, List.mem_flatMap, List.mem_finRange, true_and,
    forall_exists_index, and_imp]
  constructor
  · intro h r
    exact (round_accepts asg _ _ _).mp fun t ht => h t r ht
  · intro h t r ht
    exact (round_accepts asg _ _ _).mpr (h r) t ht

/-- The specification state after `k` rounds. -/
def after (st : State) (k : Nat) : State := (roundConstants.take k).foldl round st

private theorem roundConstants_length : roundConstants.length = 24 := rfl

private theorem after_succ (st : State) (r : Fin 24) :
    after st (r.val + 1) = round (after st r.val) (constantOf r) := by
  simp only [after, constantOf]
  rw [List.take_succ, List.foldl_append]
  have hr : r.val < roundConstants.length := by rw [roundConstants_length]; exact r.isLt
  rw [List.getElem?_eq_getElem hr]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]

private theorem after_full (st : State) : after st 24 = keccakF1600 st := by
  simp only [after, keccakF1600]
  rw [show roundConstants.take 24 = roundConstants from List.take_of_length_le (by decide)]

/-- **Sound**: an accepted trace whose first row reads `st` reads every round of `st`, and its
last row reads `keccakF1600 st`. -/
theorem perm_sound (asg : Idx → F2) (trace : Fin 25 → Fin 25 → Fin 64 → Idx) (st : State)
    (first : Reads asg (trace 0) st) (accepted : systemAccepts asg (permSystem trace)) :
    (∀ k : Fin 25, Reads asg (trace k) (after st k)) ∧ Reads asg (trace 24) (keccakF1600 st) := by
  have each := (perm_accepts asg trace).mp accepted
  have rows : ∀ k : Fin 25, Reads asg (trace k) (after st k) := by
    intro k
    induction k using Fin.induction with
    | zero => simpa [after] using first
    | succ r ih =>
      rw [Reads, each r, ih, Fin.val_succ, after_succ]
      funext t z
      exact (roundB_spec _ _ t z).symm
  refine ⟨rows, ?_⟩
  have := rows 24
  rwa [show ((24 : Fin 25) : Nat) = 24 from rfl, after_full] at this

/-! ## Size -/

theorem roundSystem_length (inp out : Fin 25 → Fin 64 → Idx) (c : Lane) :
    (roundSystem inp out c).length = 1600 := by
  simp [roundSystem, List.length_flatMap, List.sum_replicate]

theorem permSystem_length (trace : Fin 25 → Fin 25 → Fin 64 → Idx) :
    (permSystem trace).length = 38400 := by
  simp [permSystem, List.length_flatMap, roundSystem_length, List.sum_replicate]

/-! ### Completeness: the canonical trace -/

variable [DecidableEq Idx]

/-- The canonical trace from an assignment: rows `1..24` are overwritten by the rounds of the
state the first row reads; every other wire keeps its value. Needs an injective layout. -/
def traceAsg (asg : Idx → F2) (trace : Fin 25 → Fin 25 → Fin 64 → Idx) (st : State) : Idx → F2 :=
  fun i =>
    match (List.finRange 24).findSome? fun r => (List.finRange 25).findSome? fun t =>
        (List.finRange 64).find? (fun z => trace r.succ t z = i) |>.map fun z => (r, t, z) with
    | some (r, t, z) => toF (bitsOf (after st (r.val + 1)) t z)
    | none => asg i

/-- A layout is injective: distinct (row, lane, bit) triples are distinct wires. -/
def Injective (trace : Fin 25 → Fin 25 → Fin 64 → Idx) : Prop :=
  ∀ r t z r' t' z', trace r t z = trace r' t' z' → r = r' ∧ t = t' ∧ z = z'

private theorem traceAsg_row (asg : Idx → F2) (trace : Fin 25 → Fin 25 → Fin 64 → Idx) (st : State)
    (inj : Injective trace) (r : Fin 24) (t : Fin 25) (z : Fin 64) :
    traceAsg asg trace st (trace r.succ t z) = toF (bitsOf (after st (r.val + 1)) t z) := by
  simp only [traceAsg]
  split
  · rename_i r' t' z' hfound
    rw [List.findSome?_eq_some_iff] at hfound
    obtain ⟨_, r₀, _, _, hr₀, _⟩ := hfound
    rw [List.findSome?_eq_some_iff] at hr₀
    obtain ⟨_, t₀, _, _, ht₀, _⟩ := hr₀
    rw [Option.map_eq_some_iff] at ht₀
    obtain ⟨z₀, hz₀, hsame⟩ := ht₀
    have hmatch := List.find?_some hz₀
    simp only [decide_eq_true_eq] at hmatch
    obtain ⟨hr, ht, hz⟩ := inj _ _ _ _ _ _ hmatch
    simp only [Prod.mk.injEq] at hsame
    obtain ⟨rfl, rfl, rfl⟩ := hsame
    have : r₀ = r := Fin.succ_injective _ hr
    subst this; subst ht; subst hz; rfl
  · rename_i hnone
    exfalso
    rw [List.findSome?_eq_none_iff] at hnone
    have h1 := hnone r (List.mem_finRange r)
    rw [List.findSome?_eq_none_iff] at h1
    have h2 := h1 t (List.mem_finRange t)
    rw [Option.map_eq_none_iff, List.find?_eq_none] at h2
    exact (h2 z (List.mem_finRange z)) (by simp)

private theorem traceAsg_first (asg : Idx → F2) (trace : Fin 25 → Fin 25 → Fin 64 → Idx) (st : State)
    (inj : Injective trace) (t : Fin 25) (z : Fin 64) :
    traceAsg asg trace st (trace 0 t z) = asg (trace 0 t z) := by
  simp only [traceAsg]
  split
  · rename_i r' t' z' hfound
    exfalso
    rw [List.findSome?_eq_some_iff] at hfound
    obtain ⟨_, r₀, _, _, hr₀, _⟩ := hfound
    rw [List.findSome?_eq_some_iff] at hr₀
    obtain ⟨_, t₀, _, _, ht₀, _⟩ := hr₀
    rw [Option.map_eq_some_iff] at ht₀
    obtain ⟨z₀, hz₀, _⟩ := ht₀
    have hmatch := List.find?_some hz₀
    simp only [decide_eq_true_eq] at hmatch
    exact Fin.succ_ne_zero _ (inj _ _ _ _ _ _ hmatch).1
  · rfl

private theorem rb_toF (f : Fin 25 → Fin 64 → Bool) (asg : Idx → F2) (w : Fin 25 → Fin 64 → Idx)
    (h : ∀ t z, asg (w t z) = toF (f t z)) : rb asg w = f := by
  funext t z
  simp only [rb, h]
  cases f t z <;> decide

/-- **Complete**: on an injective layout, an assignment whose first row reads `st` becomes an
accepted trace by `traceAsg`, which leaves the first row, and every wire off the trace, alone. -/
theorem perm_complete (asg : Idx → F2) (trace : Fin 25 → Fin 25 → Fin 64 → Idx) (st : State)
    (inj : Injective trace) (first : Reads asg (trace 0) st) :
    systemAccepts (traceAsg asg trace st) (permSystem trace) ∧
      (∀ i, (∀ r t z, trace r t z ≠ i) → traceAsg asg trace st i = asg i) ∧
      (∀ t z, traceAsg asg trace st (trace 0 t z) = asg (trace 0 t z)) := by
  have rows : ∀ k : Fin 25, Reads (traceAsg asg trace st) (trace k) (after st k) := by
    intro k
    cases k using Fin.cases with
    | zero =>
      rw [Reads]; funext t z
      simp only [rb, traceAsg_first asg trace st inj]
      exact congrFun (congrFun first t) z
    | succ r =>
      exact rb_toF _ _ _ fun t z => by rw [traceAsg_row asg trace st inj]; rfl
  refine ⟨(perm_accepts _ _).mpr fun r => ?_, fun i off => ?_, traceAsg_first asg trace st inj⟩
  · rw [rows r.succ, rows r.castSucc, Fin.val_succ, after_succ]
    funext t z
    exact roundB_spec _ _ t z
  · simp only [traceAsg]
    split
    · rename_i r' t' z' hfound
      exfalso
      rw [List.findSome?_eq_some_iff] at hfound
      obtain ⟨_, r₀, _, _, hr₀, _⟩ := hfound
      rw [List.findSome?_eq_some_iff] at hr₀
      obtain ⟨_, t₀, _, _, ht₀, _⟩ := hr₀
      rw [Option.map_eq_some_iff] at ht₀
      obtain ⟨z₀, hz₀, _⟩ := ht₀
      have hmatch := List.find?_some hz₀
      simp only [decide_eq_true_eq] at hmatch
      exact off _ _ _ hmatch
    · rfl

/-- **Unique**: given the first row, every accepted trace agrees with the canonical one on
every trace wire. -/
theorem perm_trace_unique (asg asg' : Idx → F2) (trace : Fin 25 → Fin 25 → Fin 64 → Idx) (st : State)
    (first : Reads asg (trace 0) st) (first' : Reads asg' (trace 0) st)
    (accepted : systemAccepts asg (permSystem trace)) (accepted' : systemAccepts asg' (permSystem trace))
    (k : Fin 25) (t : Fin 25) (z : Fin 64) : asg (trace k t z) = asg' (trace k t z) := by
  have h := congrFun (congrFun ((perm_sound asg trace st first accepted).1 k) t) z
  have h' := congrFun (congrFun ((perm_sound asg' trace st first' accepted').1 k) t) z
  rw [← toF_rb asg (trace k) t z, ← toF_rb asg' (trace k) t z, h, h']

/-! ## Teeth: the system is not vacuous -/

/-- A wrong output row is refused: flipping one output bit of an accepted round rejects. -/
theorem round_refuses_flip (asg : Idx → F2) (inp out : Fin 25 → Fin 64 → Idx) (c : Lane)
    (accepted : systemAccepts asg (roundSystem inp out c)) (t : Fin 25) (z : Fin 64)
    (flipped : Idx → F2) (here : flipped (out t z) = asg (out t z) + 1)
    (rest : ∀ i, i ≠ out t z → flipped i = asg i)
    (fresh : ∀ i z', inp i z' ≠ out t z) :
    ¬ systemAccepts flipped (roundSystem inp out c) := by
  intro bad
  have h₁ := congrFun (congrFun ((round_accepts asg inp out c).mp accepted) t) z
  have h₂ := congrFun (congrFun ((round_accepts flipped inp out c).mp bad) t) z
  have hin : rb flipped inp = rb asg inp := by
    funext i z'; simp only [rb, rest _ (fresh i z')]
  rw [hin, ← h₁] at h₂
  simp only [rb, here] at h₂
  revert h₂
  generalize asg (out t z) = v
  revert v
  decide

#assert_axioms roundB_spec
#assert_axioms round_accepts
#assert_axioms round_reads
#assert_axioms perm_accepts
#assert_axioms perm_sound
#assert_axioms perm_complete
#assert_axioms perm_trace_unique
#assert_axioms permSystem_length
#assert_axioms round_refuses_flip

end Minidregg.Compiler.AirKeccak
