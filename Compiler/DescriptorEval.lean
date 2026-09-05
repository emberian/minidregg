/-
# `Compiler/DescriptorEval.lean` — the Lean side of the descriptor plan: aux-filling by
evaluation, and the Stage-0 candidate vectors as compiled witnesses

**Substrate, said out loud: nothing here is a semantics, and nothing here is a prover.**
`descriptorHolds` (`Compiler/Emit`) is the descriptor's satisfaction relation;
`descriptorHoldsCheck` (`Compiler/NativeKernelPlan`) is its decidable reference, the judge.
This file adds the one piece the plan's Lean side lacked: an EVALUATOR that, given the
variables, computes the aux wires an SSA descriptor forces — `fillAux` — so a full candidate
wire vector exists to hand to the checker. The evaluator authors no constraint and decides
nothing; it is a Lean function over a Lean-emitted first-order object. Native code (Lane B of
the descriptor-reader scout) may later return the same words from generated row constants;
Lean re-checks them against the descriptor either way.

## What is here

* `fillAux d vars` — `vars ++ zeros` up to `d.nWires`, then every gate of `d.gates` in list
  order writes `g.out := g.op.denote (read g.a) (read g.b)`, reads via `getD _ 0`.
* `fillAux_gates_hold` — **the general fact**: under `ConstraintDescriptor.SSA`
  (`Compiler/EmitShare`) + `ConstraintDescriptor.WellFormed` (`Compiler/Emit`) +
  `vars.size = d.nVars`, EVERY gate of `d` holds on the filled vector. Hypotheses discharged
  at every emitted descriptor by `emit_ssa` and `emit_wellFormed`.
* `fillAux_getD_of_lt` — the variables are never overwritten; `fillAux_descriptorHolds_iff` —
  on the filled vector, satisfaction IS the zero-checks.
* `fillAux_emit_holds` — **completeness at the evaluator**: for an emitted descriptor and an
  ACCEPTING assignment, the filled vector satisfies the descriptor (`emit_faithful` +
  `flatten_forces`, reused). Stage 0: `evmAddCandidate_holds` — for every in-range `(X, Y)`
  the filled candidate satisfies `evmAddDescriptor` (via `evmAddAsg_accepts`), and
  `evmAddCandidate_pins` — its public prefix is `encodeBoundary X Y ((X + Y) % 2²⁵⁶)`.
  Together these turn `evmAdd_satisfiable_v1`'s `∃ wv` into a vector one can PRINT.
* `evmAddCandidate X Y` / `evmAddClaimed X Y Z` — the honest candidate and the forgery shape
  of `evmAdd_forged_refused` (wires 32–47 overwritten with the CLAIMED `Z`'s limbs).
* Exhibits (§4): compiled `#eval` witnesses with build-failing teeth — `descriptorHoldsCheck`
  returns `true` on the five anvil vectors of `Theory/EvmFragment` §4 and `false` on the
  forged claim and on a single-wire tamper; the machine is re-run on each vector's calldata so
  the re-typed constants are pinned to `conformance_v1…v5`.
* The five Lean-authored conformance vectors `prover/testdata/evm_stage0_add_witness_v{1..5}.json`
  (4,131 canonical words each), written by a sibling of `writeDescriptorJson`.
* A census `#eval` recounting the exact-tier units from the descriptor itself.

## The law applied (ATLAS §6, law 9 — quoted)

> **`#guard` is silent `native_decide`.** Case-tests in Lean are still case-tests (848 of them
> = zero theorems about the subject). Prove the general fact; use guards as non-vacuity
> *witnesses*, graded and confessed (`#assert_compiled`).

So: the general facts are theorems (`fillAux_gates_hold`, `fillAux_emit_holds`,
`evmAddCandidate_holds`, kernel-checked, axioms pinned); the five honest vectors and the two
forgeries are compiled `#eval` witnesses — CONFESSED as computed checks of the COMPILED
`descriptorHoldsCheck` on concrete data, never as theorems, never `decide` over 3,298 gates
(`evmAddDescriptor_shape` already pays the kernel price once, for the shape). This tree has no
`#assert_compiled`; its own idiom for a graded witness is an `#eval` that THROWS on failure so
elaboration fails (`Compiler/EmitSerialize.roundTripDemo`, `Sp800185Cshake256Conformance`),
and that idiom is used here.

## What it is NOT

* Not a Rust reader, not a Rust `descriptor_holds` (both deleted `d55ef32`, decision
  2026-08-09; they stay deleted). Not a proof backend: `[EMIT-sound]` unchanged.
* `#eval` wall-clock, wherever it appears in a note, is "laptop script wall-clock, evidence
  of nothing".
-/
import Compiler.EvmAddAir
import Compiler.EmitShare
import Compiler.NativeKernelPlan

namespace Minidregg.Compiler.DescriptorEval

open Minidregg.Compiler
open Minidregg.Compiler.EvmAddAir
open Minidregg.Compiler.NativeKernelPlan (descriptorHoldsCheck descriptorHoldsCheck_eq_true_iff)
open Minidregg.Theory.EvmFragment
open Lean (Json toJson)

set_option autoImplicit false

universe u

variable {F : Type u} [Field F]

/-! ## §1. The evaluator — a fold of gate writes over one array. -/

/-- Read a descriptor operand against an array-backed wire vector: a constant is itself; a
wire index reads `getD _ 0` — the same total vector `fun i => arr.getD i 0` the checker sees. -/
def readArr (arr : Array F) : DWire F → F
  | .cnst c => c
  | .wire n => arr.getD n 0

theorem readArr_eq_read (arr : Array F) (w : DWire F) :
    readArr arr w = w.read (fun i => arr.getD i 0) := by
  cases w <;> rfl

/-- One gate, evaluated: the output wire is written with the op applied to the input reads.
`set!` is `setIfInBounds` (`Array.set!_eq_setIfInBounds`, `rfl`); well-formedness puts every
output in bounds. -/
def fillStep (arr : Array F) (g : DGate F) : Array F :=
  arr.set! g.out (g.op.denote (readArr arr g.a) (readArr arr g.b))

/-- **The aux-filler.** Pad the variables with zeros to `nWires`, then evaluate every gate in
list order. Under SSA each output is written exactly once, after everything it reads. -/
def fillAux (d : ConstraintDescriptor F) (vars : Array F) : Array F :=
  d.gates.foldl fillStep (vars ++ Array.replicate (d.nWires - d.nVars) 0)

/-! ### The fold's array facts. -/

theorem size_fillStep (arr : Array F) (g : DGate F) : (fillStep arr g).size = arr.size := by
  simp [fillStep]

theorem size_foldl_fillStep (gs : List (DGate F)) :
    ∀ arr : Array F, (gs.foldl fillStep arr).size = arr.size := by
  induction gs with
  | nil => intro arr; rfl
  | cons g gs ih => intro arr; rw [List.foldl_cons, ih, size_fillStep]

theorem fillStep_getElem?_self (arr : Array F) (g : DGate F) (h : g.out < arr.size) :
    (fillStep arr g)[g.out]? = some (g.op.denote (readArr arr g.a) (readArr arr g.b)) := by
  unfold fillStep
  rw [Array.set!_eq_setIfInBounds]
  exact Array.getElem?_setIfInBounds_self_of_lt h

theorem fillStep_getElem?_ne (arr : Array F) (g : DGate F) {i : ℕ} (h : g.out ≠ i) :
    (fillStep arr g)[i]? = arr[i]? := by
  unfold fillStep
  rw [Array.set!_eq_setIfInBounds]
  exact Array.getElem?_setIfInBounds_ne h

/-- A fold over gates none of which outputs to `i` leaves index `i` alone. -/
theorem foldl_fillStep_getElem?_of_forall_ne (gs : List (DGate F)) :
    ∀ (arr : Array F) (i : ℕ), (∀ g ∈ gs, g.out ≠ i) →
      (gs.foldl fillStep arr)[i]? = arr[i]? := by
  induction gs with
  | nil => intro arr i _; rfl
  | cons g gs ih =>
    intro arr i hne
    rw [List.foldl_cons, ih _ i (fun g' hg' => hne g' (List.mem_cons_of_mem _ hg')),
      fillStep_getElem?_ne arr g (hne g (List.mem_cons_self ..))]

/-- The head gate of a fold holds on the final vector: nothing after it writes any index
`≤` its output (outputs strictly increase), and its own inputs sit strictly below its output,
so both its inputs and its output read exactly what the step wrote. -/
theorem foldl_fillStep_holds_head (g : DGate F) (gs : List (DGate F)) (arr : Array F)
    (hin : g.a.bounded g.out ∧ g.b.bounded g.out)
    (hgt : ∀ g' ∈ gs, g.out < g'.out) (hlt : g.out < arr.size) :
    g.holds (fun i => (gs.foldl fillStep (fillStep arr g)).getD i 0) := by
  have hpres : ∀ i, i ≤ g.out →
      (gs.foldl fillStep (fillStep arr g))[i]? = (fillStep arr g)[i]? :=
    fun i hi => foldl_fillStep_getElem?_of_forall_ne gs _ i
      (fun g' hg' => by have := hgt g' hg'; omega)
  have hread : ∀ w : DWire F, w.bounded g.out →
      w.read (fun i => (gs.foldl fillStep (fillStep arr g)).getD i 0) = readArr arr w := by
    intro w hw
    cases w with
    | cnst c => rfl
    | wire n =>
      have hn : n < g.out := hw
      show (gs.foldl fillStep (fillStep arr g)).getD n 0 = arr.getD n 0
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, hpres n hn.le,
        fillStep_getElem?_ne arr g (by omega)]
  show g.op.denote (g.a.read _) (g.b.read _) =
    (gs.foldl fillStep (fillStep arr g)).getD g.out 0
  rw [hread g.a hin.1, hread g.b hin.2, Array.getD_eq_getD_getElem?, hpres _ le_rfl,
    fillStep_getElem?_self arr g hlt]
  rfl

/-- **The fold forces every gate** (list level): inputs strictly below own output, outputs
strictly increasing, outputs in bounds — then every gate holds on the final vector. -/
theorem foldl_fillStep_holds (gs : List (DGate F)) :
    ∀ arr : Array F,
      (∀ g ∈ gs, g.a.bounded g.out ∧ g.b.bounded g.out) →
      gs.Pairwise (fun g₁ g₂ => g₁.out < g₂.out) →
      (∀ g ∈ gs, g.out < arr.size) →
      ∀ g ∈ gs, g.holds (fun i => (gs.foldl fillStep arr).getD i 0) := by
  induction gs with
  | nil => intro arr _ _ _ g hg; exact nomatch hg
  | cons g gs ih =>
    intro arr hin hpw hlt g' hg'
    rw [List.pairwise_cons] at hpw
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hg' with heq | hg'
    · rw [heq]
      exact foldl_fillStep_holds_head g gs arr (hin g (List.mem_cons_self ..)) hpw.1
        (hlt g (List.mem_cons_self ..))
    · exact ih (fillStep arr g) (fun g'' h => hin g'' (List.mem_cons_of_mem _ h)) hpw.2
        (fun g'' h => by rw [size_fillStep]; exact hlt g'' (List.mem_cons_of_mem _ h)) g' hg'

/-! ## §2. The descriptor-level facts — SSA + well-formed ⇒ the filled vector's gates hold. -/

/-- **`fillAux_gates_hold` — the general fact.** For an SSA (`EmitShare`), well-formed
(`Emit`) descriptor and a variable array of size `nVars`, EVERY gate of `d` holds on the
filled vector. At an emitted descriptor the hypotheses are `emit_ssa` and `emit_wellFormed`. -/
theorem fillAux_gates_hold (d : ConstraintDescriptor F) (vars : Array F)
    (hssa : d.SSA) (hwf : d.WellFormed) (h : vars.size = d.nVars) :
    ∀ g ∈ d.gates, g.holds (fun i => (fillAux d vars).getD i 0) := by
  unfold fillAux
  refine foldl_fillStep_holds d.gates _ hssa.1 hssa.2 fun g hg => ?_
  obtain ⟨-, -, -, hlt⟩ := hwf.gates_in g hg
  have := hwf.vars_le
  rw [Array.size_append, Array.size_replicate, h]
  omega

/-- The filled vector has exactly `nWires` entries. -/
theorem fillAux_size (d : ConstraintDescriptor F) (vars : Array F)
    (hwf : d.WellFormed) (h : vars.size = d.nVars) :
    (fillAux d vars).size = d.nWires := by
  unfold fillAux
  rw [size_foldl_fillStep, Array.size_append, Array.size_replicate, h]
  have := hwf.vars_le
  omega

/-- The variables are never overwritten: below `nVars` the filled vector reads `vars` —
every gate output lands at or above `nVars` (`WellFormed.gates_in`). -/
theorem fillAux_getD_of_lt (d : ConstraintDescriptor F) (vars : Array F)
    (hwf : d.WellFormed) (h : vars.size = d.nVars) {i : ℕ} (hi : i < d.nVars) :
    (fillAux d vars).getD i 0 = vars.getD i 0 := by
  unfold fillAux
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    foldl_fillStep_getElem?_of_forall_ne _ _ i
      (fun g hg => by have := (hwf.gates_in g hg).2.2.1; omega),
    Array.getElem?_append_left (by omega)]

/-- On the filled vector, satisfaction IS the zero-checks: the 3,298 gate evaluations of a
check are forced true by construction; only the boundary reads carry information. -/
theorem fillAux_descriptorHolds_iff (d : ConstraintDescriptor F) (vars : Array F)
    (hssa : d.SSA) (hwf : d.WellFormed) (h : vars.size = d.nVars) :
    descriptorHolds d (fun i => (fillAux d vars).getD i 0) ↔
      ∀ z ∈ d.zeros, z.read (fun i => (fillAux d vars).getD i 0) = 0 :=
  ⟨And.right, fun hz => ⟨fillAux_gates_hold d vars hssa hwf h, hz⟩⟩

/-! ## §3. Completeness at the evaluator — an accepting assignment fills to a satisfying
vector (`emit_faithful` + `flatten_forces`, reused). -/

section Emitted

variable {Idx : Type u}

/-- The gate half of `emit_faithful`, on its own: the emitted gates hold under `wv` iff the
flattened gates hold under the readback. -/
theorem emit_gates_hold_iff (ix : Idx → ℕ) (nPublic nVars : ℕ) (s : ConstraintSystem F Idx)
    (wv : ℕ → F) :
    (∀ g ∈ (emit ix nPublic nVars s).gates, g.holds wv) ↔
      gatesHold (readVars ix wv) (readAux nVars wv) (flattenSystem s 0).gates := by
  unfold gatesHold
  show (∀ g ∈ ((flattenSystem s 0).gates).map (emitGate ix nVars), g.holds wv) ↔ _
  rw [List.forall_mem_map]
  exact forall₂_congr fun g _ => emitGate_holds_iff ix nVars wv g

/-- Every root of an accepted system, read under ANY aux valuation satisfying the flattened
gates, is `0` — each root is forced to its term's `eval` (`flatten_forces`, reused), and
acceptance says that `eval` is `0`. The list-lifted converse of `flattenSystem_forces`. -/
theorem flattenSystem_roots_forced (asg : Idx → F) (auxv : ℕ → F)
    (s : ConstraintSystem F Idx) (n₀ : ℕ)
    (hg : gatesHold asg auxv (flattenSystem s n₀).gates) (hacc : systemAccepts asg s) :
    ∀ r ∈ (flattenSystem s n₀).roots, r.read asg auxv = 0 := by
  induction s generalizing n₀ with
  | nil => intro r hr; exact nomatch hr
  | cons t ts ih =>
    rw [flattenSystem_cons_gates] at hg
    rw [flattenSystem_cons_roots]
    have hgt : gatesHold asg auxv (flatten t n₀).gates := fun g hgm =>
      hg g (List.mem_append_left _ hgm)
    have hgts : gatesHold asg auxv (flattenSystem ts (flatten t n₀).next).gates :=
      fun g hgm => hg g (List.mem_append_right _ hgm)
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr'
    · rw [flatten_forces asg t n₀ auxv hgt]
      exact hacc t (List.mem_cons_self ..)
    · exact ih (flatten t n₀).next hgts (fun u hu => hacc u (List.mem_cons_of_mem _ hu)) r hr'

end Emitted

/-- **`fillAux_emit_holds` — completeness at the evaluator.** At the canonical `Fin m`
layout, an ACCEPTING assignment, filled, satisfies the emitted descriptor: the gates by
`fillAux_gates_hold` (SSA and well-formedness are `emit_ssa` / `emit_wellFormed`), the
zero-checks because the filled aux region is a gate-satisfying valuation whose roots
`flatten_forces` pins to the terms' `eval`s. The vector `emit_accepts_iff` only asserts
EXISTS is now this computable one. -/
theorem fillAux_emit_holds {K : Type} [Field K] (m nPublic : ℕ) (hpub : nPublic ≤ m)
    (asg : Fin m → K) (s : ConstraintSystem K (Fin m)) (hacc : systemAccepts asg s) :
    descriptorHolds (emit Fin.val nPublic m s)
      (fun i => (fillAux (emit Fin.val nPublic m s) (Array.ofFn asg)).getD i 0) := by
  have hssa := emit_ssa (F := K) Fin.val nPublic m (fun i => i.isLt) s
  have hwf := emit_wellFormed (F := K) Fin.val nPublic m hpub (fun i => i.isLt) s
  have hsize : (Array.ofFn asg).size = (emit (F := K) Fin.val nPublic m s).nVars :=
    Array.size_ofFn
  have hgates := (emit_gates_hold_iff Fin.val nPublic m s _).mp
    (fillAux_gates_hold _ _ hssa hwf hsize)
  have hrv : readVars Fin.val
      (fun i => (fillAux (emit Fin.val nPublic m s) (Array.ofFn asg)).getD i 0) = asg :=
    funext fun i => by
      show (fillAux (emit Fin.val nPublic m s) (Array.ofFn asg)).getD i.val 0 = asg i
      rw [fillAux_getD_of_lt _ _ hwf hsize i.isLt, Array.getD_eq_getD_getElem?,
        Array.getElem?_ofFn, dif_pos i.isLt]
      rfl
  rw [emit_faithful, hrv]
  rw [hrv] at hgates
  exact ⟨hgates, flattenSystem_roots_forced asg _ s 0 hgates hacc⟩

/-! ## §4. Stage 0 — the candidate, the claimed (forgery-shaped) vector, and the exhibits. -/

/-- **The honest Stage-0 candidate**: `evmAddAsg X Y` (the executable witness-gen of
`EvmAddAir`) as the 833 variables, filled to the 4,131-wire vector. -/
def evmAddCandidate (X Y : ℕ) : Array BabyBear :=
  fillAux evmAddDescriptor (Array.ofFn (evmAddAsg X Y))

/-- **The claimed vector** — the forgery shape of `evmAdd_forged_refused`: the honest candidate
for `(X, Y)` with wires 32–47 overwritten by `encodeBoundary X Y Z`, i.e. the CLAIMED `Z`'s
limbs in place of the computed sum's (wires 0–31 already agree with `encodeBoundary`). -/
def evmAddClaimed (X Y Z : ℕ) : Array BabyBear :=
  (List.finRange 48).foldl
    (fun arr i => if 32 ≤ i.1 then arr.set! i.1 (encodeBoundary X Y Z i) else arr)
    (evmAddCandidate X Y)

/-- **The candidate satisfies the descriptor, for every in-range operand pair** — the general
fact behind the five exhibits below: `fillAux_emit_holds` at `evmAddAsg_accepts`. -/
theorem evmAddCandidate_holds (X Y : ℕ) (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256) :
    descriptorHolds evmAddDescriptor (fun i => (evmAddCandidate X Y).getD i 0) :=
  fillAux_emit_holds 833 48 (by omega) (evmAddAsg X Y) evmAddSystem
    (evmAddAsg_accepts X Y hX hY)

/-- The candidate's public prefix is the boundary encoding at the wrapped sum — the pin
`evmAddDescriptor_means_semantics` quantifies over, read off the computed vector. -/
theorem evmAddCandidate_pins (X Y : ℕ) (i : Fin 48) :
    (evmAddCandidate X Y).getD i.1 0 = encodeBoundary X Y ((X + Y) % 2 ^ 256) i := by
  have hwf := evmAddDescriptor_wellFormed
  have hsize : (Array.ofFn (evmAddAsg X Y)).size = evmAddDescriptor.nVars := Array.size_ofFn
  have hi := i.isLt
  show (fillAux evmAddDescriptor (Array.ofFn (evmAddAsg X Y))).getD i.1 0
    = encodeBoundaryN X Y ((X + Y) % 2 ^ 256) i.1
  rw [fillAux_getD_of_lt _ _ hwf hsize (by show i.1 < 833; omega),
    Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos (by show i.1 < 833; omega)]
  show evmAddAsgN X Y i.1 = encodeBoundaryN X Y ((X + Y) % 2 ^ 256) i.1
  unfold evmAddAsgN encodeBoundaryN
  by_cases h16 : i.1 < 16
  · rw [if_pos h16, if_pos h16]
  · by_cases h32 : i.1 < 32
    · rw [if_neg h16, if_neg h16, if_pos h32, if_pos h32]
    · rw [if_neg h16, if_neg h16, if_neg h32, if_neg h32, if_pos (by omega)]

/-- The checker on a candidate: `descriptorHoldsCheck` over `getD _ 0` reads. -/
def checkCandidate (c : Array BabyBear) : Bool :=
  descriptorHoldsCheck evmAddDescriptor (fun i => c.getD i 0)

/-! ### The anvil vectors (`Theory/EvmFragment` §4, `conformance_v1…v5`), re-typed here as
`(X, Y, Z)` plus the calldata the machine actually saw. V4's `Y` is the zero-padded
CALLDATALOAD word `0x1122334455667788 · 2¹⁹²` — the padding is the MACHINE's fact (covered
by `fragment_faithful`), so the descriptor sees the padded word; V5's calldata is empty. -/

/-- One conformance vector: the operands the descriptor sees, the claimed result, and the raw
calldata of the anvil call. -/
structure AnvilVector where
  name : String
  X : ℕ
  Y : ℕ
  Z : ℕ
  calldata : List ℕ

def anvilV1 : AnvilVector := ⟨"v1", 1, 2, 3, calldataOf 1 2⟩

def anvilV2 : AnvilVector :=
  let X := 0x243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89
  let Y := 0x452821e638d01377be5466cf34e90c6cc0ac29b7c97c50dd3f84d5b5b5470917
  ⟨"v2", X, Y, 0x69678c6ebe731c4ad16df0fd38597fb164b561d9f31b82ad47b3d04ea19575a0,
    calldataOf X Y⟩

def anvilV3 : AnvilVector := ⟨"v3", 2 ^ 256 - 1, 5, 4, calldataOf (2 ^ 256 - 1) 5⟩

def anvilV4 : AnvilVector :=
  let X := 0xfedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210
  ⟨"v4", X, 0x1122334455667788 * 2 ^ 192,
    0x0ffeeddccbbaa998fedcba9876543210fedcba9876543210fedcba9876543210,
    beBytes X ++ [0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88]⟩

def anvilV5 : AnvilVector := ⟨"v5", 0, 0, 0, []⟩

def anvilVectors : List AnvilVector := [anvilV1, anvilV2, anvilV3, anvilV4, anvilV5]

/-- The machine, re-run (compiled) on the vector's calldata: does it return `Z`'s bytes? -/
def machineReturns (v : AnvilVector) : Bool :=
  match evmRun fragmentFuel fragmentCode v.calldata with
  | .ok bs => decide (bs = beBytes v.Z)
  | .fail _ => false

/-! ### The conformance-vector writer — the Lean side is the only author of
`prover/testdata/evm_stage0_add_witness_v*.json`; Rust (Lane B) only reads. Format:
```
{ "p": <modulus>, "descriptor": "evm_stage0_add_descriptor.json", "vector": "v1",
  "x": "0x…", "y": "0x…", "z": "0x…", "nPublic": 48, "nVars": 833, "nWires": 4131,
  "accepted": true, "wires": [ <4131 canonical values, 0 ≤ v < p> ] }
```
`x`/`y`/`z` are hex STRINGS (256-bit values do not fit a JSON reader's integer); `wires`
are canonical `ZMod.val`s, the reader's contract exactly as for the descriptor's constants;
`accepted` is the embedded verdict of `descriptorHoldsCheck` on this very vector. -/

def hexOf (n : ℕ) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- A candidate wire vector as one JSON array of canonical values. -/
def wiresToJson (c : Array BabyBear) : Json :=
  Json.arr (c.map fun v => toJson v.val)

def witnessToJson (v : AnvilVector) (c : Array BabyBear) : Json :=
  Json.mkObj
    [ ("p", toJson babyBearP),
      ("descriptor", Json.str "evm_stage0_add_descriptor.json"),
      ("vector", Json.str v.name),
      ("x", Json.str (hexOf v.X)),
      ("y", Json.str (hexOf v.Y)),
      ("z", Json.str (hexOf v.Z)),
      ("nPublic", toJson evmAddDescriptor.nPublic),
      ("nVars", toJson evmAddDescriptor.nVars),
      ("nWires", toJson evmAddDescriptor.nWires),
      ("accepted", toJson (checkCandidate c)),
      ("wires", wiresToJson c) ]

/-- Write one witness file (creating the parent directory; repo-root-relative) — the sibling
of `writeDescriptorJson`. -/
def writeWitnessJson (path : System.FilePath) (v : AnvilVector) (c : Array BabyBear) :
    IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path ((witnessToJson v c).pretty ++ "\n")

/-! ### Exhibits — compiled, with teeth. Each `#eval` THROWS on any deviation, so elaboration
of this file fails: a `false` on an honest vector, a `true` on a forgery, a public prefix
not pinned to the claim, a machine run not returning `Z`. These are non-vacuity witnesses
of `evmAddCandidate_holds` / `evmAdd_forged_refused` at the COMPILED checker on concrete
data — computed checks, confessed as such, not theorems. -/

/-- The honest exhibit for one anvil vector, then the witness file. -/
def exhibitHonest (v : AnvilVector) : IO Unit := do
  let c := evmAddCandidate v.X v.Y
  unless c.size = evmAddDescriptor.nWires do
    throw <| IO.userError s!"{v.name}: candidate has {c.size} wires, descriptor has \
      {evmAddDescriptor.nWires}"
  unless machineReturns v do
    throw <| IO.userError s!"{v.name}: the machine does not return Z on this calldata"
  unless (List.finRange 48).all (fun i => decide (c.getD i.1 0 = encodeBoundary v.X v.Y v.Z i)) do
    throw <| IO.userError s!"{v.name}: public prefix is not encodeBoundary X Y Z"
  unless checkCandidate c do
    throw <| IO.userError s!"{v.name}: honest candidate REFUSED by descriptorHoldsCheck"
  writeWitnessJson s!"prover/testdata/evm_stage0_add_witness_{v.name}.json" v c
  IO.println s!"{v.name}: accepted — {c.size} wires, public prefix = encodeBoundary X Y Z, \
    machine returns Z; wrote prover/testdata/evm_stage0_add_witness_{v.name}.json"

#eval anvilVectors.forM exhibitHonest

/-- A forgery exhibit: the mutation is asserted first (the vector genuinely differs from the
honest candidate it was derived from), then the checker must refuse it. -/
def exhibitForgery (name : String) (honest forged : Array BabyBear) : IO Unit := do
  unless forged.size = honest.size do
    throw <| IO.userError s!"{name}: forged vector has the wrong size"
  unless forged ≠ honest do
    throw <| IO.userError s!"{name}: the mutation is vacuous (forged = honest)"
  if checkCandidate forged then
    throw <| IO.userError s!"{name}: forgery ACCEPTED by descriptorHoldsCheck"
  IO.println s!"{name}: refused"

/-! *Teeth at the checker, forged claim*: V3's inputs with the claimed `Z = 5` (the
semantics say `4`, `forged_wrap_differs`) — the computed shape of `evmAdd_forged_refused`. -/
#eval exhibitForgery "claimed Z = 5 on (2^256 - 1, 5)"
  (evmAddCandidate (2 ^ 256 - 1) 5) (evmAddClaimed (2 ^ 256 - 1) 5 5)

/-! *Teeth at the checker, single-wire tamper*: V1's candidate with ONE aux wire — the first
one, wire `nVars = 833`, the output of gate 0 — bumped by `+1`. The shape of a native reply
returning one wrong word. -/
#eval
  let c := evmAddCandidate 1 2
  let k := evmAddDescriptor.nVars
  exhibitForgery s!"V1 wire {k} + 1" c (c.set! k (c.getD k 0 + 1))

/-! ### The units, recounted from the descriptor (not copied): gates by op, wires, boundary
pins, operand kinds, constants — and the witness-variable split from the layout
`evmAddWires`, checked to partition the variables. The expected figures are asserted; the
line printed is the exact-tier answer. -/

def census : IO Unit := do
  let d := evmAddDescriptor
  let adds := (d.gates.filter fun g => g.op == .add).length
  let muls := (d.gates.filter fun g => g.op == .mul).length
  let isCnst : DWire BabyBear → Bool := fun | .cnst _ => true | .wire _ => false
  let cnstOps := d.gates.foldl (fun n g =>
    n + (if isCnst g.a then 1 else 0) + (if isCnst g.b then 1 else 0)) 0
  let wireOps := 2 * d.gates.length - cnstOps
  let cnstVals : List ℕ := d.gates.foldl (fun acc g =>
    (match g.a with | .cnst c => [c.val] | .wire _ => []) ++
    (match g.b with | .cnst c => [c.val] | .wire _ => []) ++ acc) []
  let distinct := cnstVals.eraseDups.length
  let zeroAux := (d.zeros.filter fun | .wire n => decide (d.nVars ≤ n) | .cnst _ => false).length
  let zeroVar := (d.zeros.filter fun | .wire n => decide (n < d.nVars) | .cnst _ => false).length
  -- booleanity shape `add (wire w) (cnst (-1))` on a VARIABLE wire: one per witness variable
  let boolVars := (d.gates.filterMap fun g =>
    match g.op, g.a, g.b with
    | .add, .wire w, .cnst c => if w < d.nVars ∧ c = -1 then some w else none
    | _, _, _ => none).eraseDups.length
  -- the layout's split of the 833 variables
  let w := evmAddWires
  let limbs := (List.finRange 16).flatMap fun i => [(w.x i).1, (w.y i).1, (w.z i).1]
  let bits := (List.finRange 16).flatMap fun i => (List.finRange 16).flatMap fun j =>
    [(w.xBit i j).1, (w.yBit i j).1, (w.zBit i j).1]
  let carries := (List.finRange 17).map fun i => (w.carry i).1
  let all := limbs ++ bits ++ carries
  unless all.length = d.nVars ∧ (List.range d.nVars).all (fun n => all.contains n) do
    throw <| IO.userError "layout does not partition the variables"
  let line := s!"Stage-0 units (recounted): {d.gates.length} gates = {adds} add + {muls} mul; \
    {d.nWires} wires = {d.nVars} vars ({d.nPublic} public + {d.nVars - d.nPublic} witness) + \
    {d.nWires - d.nVars} aux; {d.zeros.length} boundary pins ({zeroAux} on aux roots, \
    {zeroVar} on variables); operands: {wireOps} wire, {cnstOps} constant over {distinct} \
    distinct constants; witness vars: {bits.length} range bits + {carries.length} carries \
    (booleanity gates on {boolVars} distinct variables); a check = {d.gates.length} gate \
    evals + {d.zeros.length} reads"
  IO.println line
  unless d.gates.length = 3298 ∧ adds = 1665 ∧ muls = 1633 ∧ d.nWires = 4131 ∧
      d.nVars = 833 ∧ d.nPublic = 48 ∧ d.zeros.length = 850 ∧ bits.length = 768 ∧
      carries.length = 17 ∧ boolVars = 785 ∧ zeroVar = 1 do
    throw <| IO.userError "units differ from the figures the note quotes — re-quote them"

#eval census

/-! ## §5. Axiom accounting. -/

/-- info: 'Minidregg.Compiler.DescriptorEval.fillAux_gates_hold' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fillAux_gates_hold

/-- info: 'Minidregg.Compiler.DescriptorEval.fillAux_emit_holds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fillAux_emit_holds

/-- info: 'Minidregg.Compiler.DescriptorEval.evmAddCandidate_holds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evmAddCandidate_holds

/-- info: 'Minidregg.Compiler.DescriptorEval.evmAddCandidate_pins' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evmAddCandidate_pins

end Minidregg.Compiler.DescriptorEval
