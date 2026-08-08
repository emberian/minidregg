/-
# `Compiler/EmitSerialize.lean` — `[PROVER-serialize]`: the descriptor wire-format, made concrete

**Substrate, said out loud: this file is the LAST verified-side stop before the seam.** It
serializes `ConstraintDescriptor` — the first-order object whose faithfulness to the Lean AIR
is `emit_faithful`, a theorem — to concrete JSON text for the UNVERIFIED Rust prover
(`prover/`) to read. The prover consumes this file's output and NEVER authors a constraint.
Everything on the far side of the text is conformance-vector territory: there is no formal
semantics of Rust, so nothing over there is ever called verification or refinement.

## The format (the `[EMIT-backend]` wire-format, concretized)

```
{ "p": <modulus>, "nPublic": <ℕ>, "nVars": <ℕ>, "nWires": <ℕ>,
  "gates": [ {"op": "add"|"mul", "a": <wire>, "b": <wire>, "out": <ℕ>}, … ],
  "zeros": [ <wire>, … ] }

<wire> ::= {"c": <ℕ>}   -- field constant, canonical `ZMod.val`, 0 ≤ v < p
         | {"w": <ℕ>}   -- index into the one total wire vector
```

First-order throughout — the descriptor has no functions inside (Emit's N3-cleanliness), so
the serialization is total and lossless. Constants travel as their canonical natural
(`ZMod.val`); the reader REJECTS non-canonical constants (`v ≥ p`), keeping the format
unambiguous. The modulus is stamped in the header; the reader checks it.

## What is here

* `descriptorToJson` / `descriptorFromJson?` — writer and reader over `ZMod p`, generic in
  the prime. The round-trip is CHECKED at build time (an `#eval` with teeth: parse the
  pretty-printed text back and compare with the derived `DecidableEq` — elaboration fails on
  mismatch). A computed check, honestly said — not a kernel theorem (kernel-reducing the JSON
  printer/parser over `String` is not worth the candle).
* `[PROVER-field]` — **BabyBear `p = 2^31 − 2^27 + 1 = 2013265921`**, the deployed prover
  field (`Fact (Nat.Prime babyBearP)` proved by `norm_num`, so `BabyBear` is a genuine
  `Field` and everything upstream — `emit_faithful`, `emit_accepts_iff` — applies verbatim).
* The demo descriptor: `rangeGadget` (REUSED — 4 bits, `x` public at wire 0, bits witness at
  wires 1–4) emitted over BabyBear — 18 gates, 5 zero-checks, 23 wires; constants include
  `-1 = 2013265920`, exercising the canonical encoding. Satisfiable at
  `x = 13, bits = (1,0,1,1)` and toothed at `x = 14` — both DECIDED here, so the Rust
  conformance vectors in `prover/tests/` cross-check against Lean-established facts.
* The `#eval` writer: emits `prover/testdata/demo_descriptor.json` (repo-root-relative) at
  build time — the Lean writer is the ONLY author of that file; the Rust side only reads.
* `[PROVER-commit]` conformance (§6): `proverPermSpec` — a fixed demo `PermSpec` over
  BabyBear (width 2, `α = 5`, full·partial·full, NON-symmetric per-round-distinct matrices,
  so the vector pins the linear layer's row/column orientation and the schedule wiring) —
  with its `permExec` output KERNEL-DECIDED and written to
  `prover/testdata/poseidon_conformance.json` for the Rust `perm` to reproduce. A demo
  instantiation; the deployed constant set is `[AIR-poseidon-params]`/`[PROVER-poseidon-params]`.

## Residuals

* `[EMIT-sound]` unchanged: the Rust side satisfying `descriptor_holds` is a cross-check that
  RUNS; "the prover accepted" still inherits the FRI/STARK floor.
* The full `spendDescriptor` (2 696 666 gates, `[EMIT-share]`'s tree blowup) serializes by the
  SAME generic functions but is not written as testdata (~10⁸ bytes of JSON); the sharing/CSE
  rung shrinks it first.
-/
import Compiler.Emit
import Compiler.AirHash
import Mathlib.Tactic.NormNum.Prime
import Lean.Data.Json

namespace Minidregg.Compiler

open Lean (Json toJson)

/-! ## §1. `[PROVER-field]` — BabyBear, the deployed prover field. -/

/-- **BabyBear** `p = 2^31 − 2^27 + 1` — the deployed prover-field instantiation
(`[PROVER-field]`): 31-bit, high 2-adicity (`2^27 ∣ p − 1`), the field of the WGPU fold
kernel the prover adopts. -/
def babyBearP : ℕ := 2013265921

theorem babyBearP_eq : babyBearP = 2 ^ 31 - 2 ^ 27 + 1 := by norm_num [babyBearP]

instance : NeZero babyBearP := ⟨by norm_num [babyBearP]⟩

/-- BabyBear is prime — so `ZMod babyBearP` is a genuine `Field` and the whole emit-path
theorem stack (`emit_faithful`, `emit_accepts_iff`, `emit_wellFormed`) applies verbatim. -/
instance : Fact (Nat.Prime babyBearP) := ⟨by norm_num [babyBearP]⟩

/-- The deployed prover field. -/
abbrev BabyBear := ZMod babyBearP

/-! ## §2. The writer — descriptor → JSON, constants as canonical `ZMod.val`. -/

variable {p : ℕ}

/-- Serialize a descriptor operand: a constant as `{"c": v}` (canonical `ZMod.val`), a wire
index as `{"w": n}`. -/
def dwireToJson [NeZero p] : DWire (ZMod p) → Json
  | .cnst c => Json.mkObj [("c", toJson c.val)]
  | .wire n => Json.mkObj [("w", toJson n)]

/-- Serialize a gate op as `"add"` / `"mul"`. -/
def gateOpToJson : GateOp → Json
  | .add => Json.str "add"
  | .mul => Json.str "mul"

/-- Serialize a gate record: `{"op": …, "a": …, "b": …, "out": n}`. -/
def dgateToJson [NeZero p] (g : DGate (ZMod p)) : Json :=
  Json.mkObj [("op", gateOpToJson g.op), ("a", dwireToJson g.a), ("b", dwireToJson g.b),
    ("out", toJson g.out)]

/-- **The descriptor writer** — the whole first-order object as one JSON value, the modulus
stamped in the header. Total and lossless: the descriptor contains no functions
(`Compiler/Emit` §1), only `ℕ`s, field constants, and lists. -/
def descriptorToJson [NeZero p] (d : ConstraintDescriptor (ZMod p)) : Json :=
  Json.mkObj
    [ ("p", toJson p),
      ("nPublic", toJson d.nPublic),
      ("nVars", toJson d.nVars),
      ("nWires", toJson d.nWires),
      ("gates", Json.arr (d.gates.map dgateToJson).toArray),
      ("zeros", Json.arr (d.zeros.map dwireToJson).toArray) ]

/-! ## §3. The reader — JSON → descriptor, strict: canonical constants only, modulus
checked. -/

/-- Parse a gate op. -/
def gateOpFromJson? (j : Json) : Except String GateOp := do
  match ← j.getStr? with
  | "add" => pure .add
  | "mul" => pure .mul
  | s => throw s!"unknown gate op: {s}"

/-- Parse an operand. STRICT on constants: `v ≥ p` is rejected, not reduced — the canonical
form is the only accepted encoding. -/
def dwireFromJson? (j : Json) : Except String (DWire (ZMod p)) :=
  match j.getObjVal? "c" with
  | .ok cj => do
      let v ← cj.getNat?
      if v < p then pure (.cnst (v : ZMod p))
      else throw s!"non-canonical field constant {v} (modulus {p})"
  | .error _ => do
      pure (.wire (← (← j.getObjVal? "w").getNat?))

/-- Parse a gate record. -/
def dgateFromJson? (j : Json) : Except String (DGate (ZMod p)) := do
  pure { op := ← gateOpFromJson? (← j.getObjVal? "op"),
         a := ← dwireFromJson? (← j.getObjVal? "a"),
         b := ← dwireFromJson? (← j.getObjVal? "b"),
         out := ← (← j.getObjVal? "out").getNat? }

/-- **The descriptor reader.** Checks the stamped modulus against the expected `p` — a
descriptor over the wrong field is a parse error, not a silent reinterpretation. -/
def descriptorFromJson? (p : ℕ) [NeZero p] (j : Json) :
    Except String (ConstraintDescriptor (ZMod p)) := do
  let pj ← (← j.getObjVal? "p").getNat?
  unless pj = p do throw s!"field-modulus mismatch: descriptor stamped {pj}, expected {p}"
  pure { nPublic := ← (← j.getObjVal? "nPublic").getNat?,
         nVars := ← (← j.getObjVal? "nVars").getNat?,
         nWires := ← (← j.getObjVal? "nWires").getNat?,
         gates := ← (← (← j.getObjVal? "gates").getArr?).toList.mapM dgateFromJson?,
         zeros := ← (← (← j.getObjVal? "zeros").getArr?).toList.mapM dwireFromJson? }

/-- Write a descriptor as pretty-printed JSON text (creating the parent directory). The
path is resolved against the working directory — build from the repo root. -/
def writeDescriptorJson [NeZero p] (path : System.FilePath)
    (d : ConstraintDescriptor (ZMod p)) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path ((descriptorToJson d).pretty ++ "\n")

/-! ## §4. The demo descriptor — `rangeGadget`, 4 bits, over BabyBear.

The system is DERIVED (rangeGadget, REUSED — never a hand-written gate list), then emitted
through the proved `emit`. Layout: `x` at wire 0 (the one public input), bits `b₀…b₃` at
wires 1–4 (witness), aux at offset 5. -/

/-- The demo system: `x` is a 4-bit value — 4 booleanity assertions + the recomposition
`x = Σ bᵢ·2ⁱ`, all DSL terms (`rangeGadget`, REUSED). -/
def demoSystem : ConstraintSystem BabyBear (Fin 5) :=
  rangeGadget 0 (fun i : Fin 4 => i.succ)

/-- **The demo descriptor** — the range gadget emitted over BabyBear at the canonical
`Fin 5` layout, `nPublic = 1`. -/
def demoDescriptor : ConstraintDescriptor BabyBear :=
  emit Fin.val 1 5 demoSystem

/-- *Shape, decided*: 18 gates (2 per booleanity, 10 for the recomposition), one aux wire
per gate (`nWires = 5 + 18`), 5 zero-checked roots. The constants include
`-1 = 2013265920` — the canonical encoding is exercised by real data. -/
example : demoDescriptor.gates.length = 18 ∧ demoDescriptor.nWires = 23 ∧
    demoDescriptor.zeros.length = 5 := by decide

/-- The honest demo assignment: `x = 13`, bits `(1,0,1,1)` — `13 = 1 + 4 + 8`. -/
def demoVals : Fin 5 → BabyBear := ![13, 1, 0, 1, 1]

/-- *Satisfiable, decided*: the honest assignment accepts the demo system — the fact the
Rust conformance vector (`prover/tests/conformance.rs`, honest trace) cross-checks. -/
example : systemAccepts demoVals demoSystem := by decide

/-- *Satisfiable at the descriptor*: a total wire vector pinning the variables to `demoVals`
satisfies the emitted descriptor — `emit_accepts_iff` doing the transfer, the witness built
by the theorem. The Rust trace generator EXHIBITS this vector concretely. -/
example : ∃ wv : ℕ → BabyBear, (∀ i : Fin 5, wv i.val = demoVals i) ∧
    descriptorHolds demoDescriptor wv :=
  (emit_accepts_iff_fin 5 1 demoVals demoSystem).mpr (by decide)

/-- *Teeth, decided*: `x = 14` with bits `(1,0,1,1)` is REJECTED — NO total wire vector at
all satisfies the descriptor under the wrong public input. The fact the Rust tampered
vector cross-checks. -/
example : ¬ ∃ wv : ℕ → BabyBear,
    (∀ i : Fin 5, wv i.val = (![14, 1, 0, 1, 1] : Fin 5 → BabyBear) i) ∧
      descriptorHolds demoDescriptor wv := fun h =>
  (by decide : ¬ systemAccepts (![14, 1, 0, 1, 1] : Fin 5 → BabyBear) demoSystem)
    ((emit_accepts_iff_fin 5 1 _ demoSystem).mp h)

/-- *Well-formed*: the Rust reader can size its buffers from the header and trust the aux
region — `emit_wellFormed`, instantiated. -/
example : demoDescriptor.WellFormed :=
  emit_wellFormed Fin.val 1 5 (by omega) (fun i => i.isLt) demoSystem

/-! ## §5. Round-trip and the testdata write — build-time, with teeth (`#eval` throws ⇒
elaboration fails). -/

/-- Round-trip through the concrete TEXT (pretty-print → `Json.parse` → reader) and compare
with the derived `DecidableEq`. A computed check with build-failing teeth — honestly a
check, not a theorem. -/
def roundTripDemo : IO Unit := do
  let txt := (descriptorToJson demoDescriptor).pretty
  match Json.parse txt with
  | .error e => throw <| IO.userError s!"demo descriptor text does not re-parse: {e}"
  | .ok j =>
    match descriptorFromJson? babyBearP j with
    | .error e => throw <| IO.userError s!"demo descriptor does not round-trip: {e}"
    | .ok d =>
        unless d = demoDescriptor do
          throw <| IO.userError "demo descriptor round-trip mismatch"
        IO.println s!"round-trip OK: {d.gates.length} gates, {d.zeros.length} zeros, \
          nWires = {d.nWires}"

#eval roundTripDemo

/- The testdata write: the Lean writer is the only author of
`prover/testdata/demo_descriptor.json`; the Rust prover only ever reads it. -/
#eval writeDescriptorJson "prover/testdata/demo_descriptor.json" demoDescriptor

/-! ## §6. `[PROVER-commit]` conformance — the Poseidon reference vector.

The Rust prover's Merkle commitment compresses with a Rust re-implementation of
`AirHash`'s EXECUTOR `permExec` (the reference the verified gadget was proved equal to,
`permGadget_eval`). Rust has no formal semantics, so the seam is a CONFORMANCE VECTOR: this
section instantiates `permExec` at a fixed spec + input over BabyBear, KERNEL-DECIDES the
output, and writes spec + input + output to testdata; the Rust test then reproduces the
output with its own `perm`. Agreement on the vector is the whole claim — never refinement.

The spec is a DEMO instantiation (`[AIR-poseidon-params]`/`[PROVER-poseidon-params]` carry
the deployed constants): width 2, `α = 5`. Named wart: `p − 1 = 2^27 · 3 · 5`, so
`5 ∣ p − 1` and `x^5` is NOT a bijection on BabyBear (deployed BabyBear Poseidon2 uses
`α = 7`, where `gcd(7, p − 1) = 1`). Irrelevant to CONFORMANCE — equal outputs is the whole
test — but exactly the kind of fact `[PROVER-poseidon-params]` must get right for the
deployed set. The matrices are NON-symmetric and differ across rounds
so the vector pins the row/column orientation (`out[i] = Σⱼ M i j · sboxed j`) and the
schedule wiring — a transposed or reordered Rust mirror fails the test. -/

/-- Demo linear layer 1 (rounds 0 and 2): non-symmetric, det `= 2 ≠ 0`. -/
def proverPermM1 : Fin 2 → Fin 2 → BabyBear := ![![2, 1], ![4, 3]]

/-- Demo linear layer 2 (round 1): non-symmetric, det `= −7 ≠ 0`. -/
def proverPermM2 : Fin 2 → Fin 2 → BabyBear := ![![1, 5], ![2, 3]]

/-- **The conformance spec** — mirrored verbatim by the Rust `poseidon::demo_spec()`;
the test checks the two are equal field-by-field before checking outputs. -/
def proverPermSpec : PermSpec BabyBear 2 where
  α := 5
  rounds :=
    [ ⟨![3, 5], true,  proverPermM1⟩,
      ⟨![1, 7], false, proverPermM2⟩,
      ⟨![2, 4], true,  proverPermM1⟩ ]

/-- The conformance input — asymmetric, far from the field's edges. -/
def proverPermInput : Fin 2 → BabyBear := ![123456789, 987654321]

/-- *The reference output, KERNEL-DECIDED*: `permExec` of the conformance input. The
value the Rust `perm` must reproduce byte-for-byte. -/
example : permExec proverPermSpec proverPermInput = ![1373719630, 1740831647] := by decide

/-- *The hash squeeze, decided*: output wire 0. -/
example : hashExec proverPermSpec proverPermInput = 1373719630 := by decide

/-! The conformance-file writer — same discipline as the descriptor: the Lean side is the
only author of `prover/testdata/poseidon_conformance.json`; Rust only reads. -/

variable {w : ℕ}

/-- Serialize a `Fin w`-vector of field elements as a JSON array of canonical values. -/
def finVecToJson [NeZero p] (v : Fin w → ZMod p) : Json :=
  Json.arr ((List.finRange w).map fun i => toJson (v i).val).toArray

/-- Serialize a round: `{"rc": […], "full": bool, "m": [[…], …]}` (row-major: `m[i][j]`
is `M i j`). -/
def roundToJson [NeZero p] (r : Round (ZMod p) w) : Json :=
  Json.mkObj
    [ ("rc", finVecToJson r.rc),
      ("full", toJson r.full),
      ("m", Json.arr ((List.finRange w).map fun i => finVecToJson (r.M i)).toArray) ]

/-- Serialize a permutation spec: `{"alpha": ℕ, "width": ℕ, "rounds": […]}`. -/
def permSpecToJson [NeZero p] (spec : PermSpec (ZMod p) w) : Json :=
  Json.mkObj
    [ ("alpha", toJson spec.α),
      ("width", toJson w),
      ("rounds", Json.arr (spec.rounds.map roundToJson).toArray) ]

/-- The whole conformance file: field, spec, input, and the Lean-computed
`permExec`/`hashExec` outputs (the values the decided examples above pin). -/
def poseidonConformanceJson : Json :=
  Json.mkObj
    [ ("p", toJson babyBearP),
      ("spec", permSpecToJson proverPermSpec),
      ("input", finVecToJson proverPermInput),
      ("permOutput", finVecToJson (permExec proverPermSpec proverPermInput)),
      ("hashOutput", toJson (hashExec proverPermSpec proverPermInput).val) ]

/-- Write the conformance file (creating the parent directory; repo-root-relative). -/
def writePoseidonConformance (path : System.FilePath) : IO Unit := do
  if let some dir := path.parent then IO.FS.createDirAll dir
  IO.FS.writeFile path (poseidonConformanceJson.pretty ++ "\n")

#eval writePoseidonConformance "prover/testdata/poseidon_conformance.json"

end Minidregg.Compiler
