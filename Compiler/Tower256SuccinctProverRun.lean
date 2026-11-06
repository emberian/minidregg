/-
# Compiler.Tower256SuccinctProverRun -- the honest prover, compiled, at two shapes

`lake exe tower256-prover-run`. For each shape the honest receipt must be accepted, by `check`
and by `checkBytes` on its encoding, and its mutant must fail exactly the checks named below.
Any other outcome prints the observation and exits 1.

* `ell = 4`, `m = 2`, three queries, final degree 2. Round 0's next-level leaf is round 1's pair
  leaf (the `j + 1 < m` branch of `CReceipt.nextOf`), compared against the prover's level-1
  table. Mutant: the level-1 word is committed plus one; every opening authenticates, round 0's
  fold fails at every query, round 1 holds.
* `ell = 8`, `m = 3`, four queries, final degree 4. Mutant: round 1, query 0's shared path has
  every digest bumped; round 1, query 0's two leaves fail, round 0, query 0's derived next leaf
  fails (it is read from that path), everything else holds.
-/

import Compiler.Tower256SuccinctProver
import Compiler.Tower256FriNativeDeployment

namespace Minidregg.Compiler.Tower256SuccinctProverRun

open Minidregg.Compiler.Tower256AdditiveFriController (TranscriptPins)
open Minidregg.Compiler.Tower256AdditiveFriRawDeployment (bootstrapPins)
open Minidregg.Compiler.Tower256CoordinateMerkle
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8)
open Minidregg.Compiler.Tower256SuccinctCheck
open Minidregg.Compiler.Tower256SuccinctReceiptCodec (receiptCodec checkBytes)
open Minidregg.Compiler.Tower256SuccinctProver
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate)
open Minidregg.Compiler.Tower256FriNativeDeployment (ProveRequest requestCodecLawful)

set_option autoImplicit false

variable {ell m queryCount : Nat}

def poly (n : Nat) : List C8 := (List.range n).map fun i => Coord.ofNat 8 (3 + 5 * i + i * i)

def clauses (s : CStatement ell m) (pins : TranscriptPins) (r : CReceipt ell m queryCount) :
    Bool × Bool :=
  (decide (∀ j, r.challenges j = challengeC s pins r j),
   decide (∀ a, r.querySeed a = seedC s pins r a))

def expect (label : String) (ok : Bool) : IO Bool := do
  IO.println s!"{if ok then "ok  " else "FAIL"} {label}"
  return ok

def honestChecks (label : String) (run : Run ell m queryCount) (branchCases : Nat) :
    IO Bool := do
  let s := run.stmt
  let r := run.receipt
  let bytes := (receiptCodec ell m queryCount).encode r
  let a ← expect s!"{label}: check accepts the honest receipt" (check s bootstrapPins r)
  let b ← expect s!"{label}: checkBytes accepts its {bytes.length}-byte encoding"
    (checkBytes (queryCount := queryCount) s bootstrapPins bytes)
  let c ← expect s!"{label}: the folded last word is the final polynomial's"
    (run.foldedLastRoot == r.roots (Fin.last m))
  let d ← expect s!"{label}: every part of every opening holds"
    ((allParts s r).all fun p => p.2.2 == (true, true, true, true))
  let nb := nextBranchAgrees run
  let e ← expect s!"{label}: nextOf from round j+1 matches the committed word ({nb.1} cases)"
    (nb == (branchCases, true))
  return a && b && c && d && e

def mutantChecks (label : String) (run : Run ell m queryCount)
    (r : CReceipt ell m queryCount) (expected : List (Nat × Nat × (Bool × Bool × Bool × Bool))) :
    IO Bool := do
  let s := run.stmt
  let bytes := (receiptCodec ell m queryCount).encode r
  let a ← expect s!"{label}: check rejects" (!check s bootstrapPins r)
  let b ← expect s!"{label}: checkBytes rejects" (!checkBytes (queryCount := queryCount) s bootstrapPins bytes)
  let c ← expect s!"{label}: challenge and seed clauses hold" (clauses s bootstrapPins r == (true, true))
  let got := allParts s r
  let d ← expect s!"{label}: exactly the named opening parts fail" (got == expected)
  unless d do
    for p in got do
      IO.println s!"    round {p.1} query {p.2.1}: {p.2.2}"
  return a && b && c && d

def allTrue (m queryCount : Nat) : List (Nat × Nat × (Bool × Bool × Bool × Bool)) :=
  (List.range m).flatMap fun j => (List.range queryCount).map fun a => (j, a, (true, true, true, true))

def shapeA : IO Bool := do
  let label := "ell=4 m=2 q=3"
  let some run := prove 4 2 3 (by norm_num) (by norm_num) (Coordinate.zero 8) [8, 4, 2] bootstrapPins (poly 8) none
    | expect s!"{label}: interpolation" false
  let h ← honestChecks label run 3
  let some bad := prove 4 2 3 (by norm_num) (by norm_num) (Coordinate.zero 8) [8, 4, 2] bootstrapPins
      (poly 8) (some (1, Coordinate.one 8))
    | expect s!"{label} delta: interpolation" false
  let expected := (allTrue 2 3).map fun (j, a, p) => if j = 0 then (j, a, (true, true, true, false)) else (j, a, p)
  let mu ← mutantChecks s!"{label} delta at level 1" bad bad.receipt expected
  return h && mu

def shapeB : IO Bool := do
  let label := "ell=8 m=3 q=4"
  let some run := prove 8 3 4 (by norm_num) (by norm_num) (Coordinate.zero 8) [32, 16, 8, 4] bootstrapPins
      (poly 32) none
    | expect s!"{label}: interpolation" false
  let h ← honestChecks label run 8
  let r := run.receipt
  let bad : CReceipt 8 3 4 := { r with opening := fun j a =>
    let o := r.opening j a
    if (j : Nat) = 1 ∧ (a : Nat) = 0 then
      { o with pairPath := o.pairPath.map fun d => ⟨d.value + 1⟩ }
    else o }
  let expected := (allTrue 3 4).map fun (j, a, p) =>
    if j = 1 ∧ a = 0 then (j, a, (false, true, false, true))
    else if j = 0 ∧ a = 0 then (j, a, (true, false, true, true))
    else (j, a, p)
  let mu ← mutantChecks s!"{label} path corrupted at round 1 query 0" run bad expected
  return h && mu

/-! ## Work 9104 conformance vectors

`tower256-prover-run --vectors FILE` writes request and response bytes for the native kernel to
reproduce byte for byte. The reference answer is this prover; it is defined for the unit basis
only (the statement needs its independence proof), so every vector uses the unit basis. -/

/-- The reference response to a 9104 request: the honest receipt's bytes. -/
def proveRequest (req : ProveRequest) : Option (List UInt8) :=
  if hm : req.m ≤ req.ell then
    if hell : req.ell ≤ 256 then
      if req.beta = List.ofFn (unitBasis req.ell) then
        let pins := { bootstrapPins with statementBytes := req.statementBytes }
        (prove req.ell req.m req.queryCount hm hell req.offset req.degree pins req.inputWord
          none).map fun run => (receiptCodec req.ell req.m req.queryCount).encode run.receipt
      else none
    else none
  else none

def request (ell m queryCount : Nat) (offset : C8) (degree : List Nat) (coeffs : Nat) :
    ProveRequest where
  statementBytes := (s!"tower256-9104-vector/{ell}/{m}/{queryCount}").toUTF8.toList
  ell := ell
  m := m
  queryCount := queryCount
  beta := List.ofFn (unitBasis ell)
  offset := offset
  degree := degree
  inputWord := poly coeffs

def vectorRequests : List (String × ProveRequest) :=
  [("ell2_m1_q2", request 2 1 2 (Coordinate.zero 8) [4, 2] 4),
   ("ell3_m0_q0", request 3 0 0 (Coordinate.zero 8) [8] 8),
   ("ell4_m2_q3_offset9", request 4 2 3 (Coord.ofNat 8 9) [8, 4, 2] 8),
   ("ell6_m3_q3", request 6 3 3 (Coordinate.zero 8) [16, 8, 4, 2] 16),
   ("ell8_m3_q4", request 8 3 4 (Coordinate.zero 8) [32, 16, 8, 4] 32)]

def hex (bytes : List UInt8) : String :=
  String.join (bytes.map fun b =>
    let d := "0123456789abcdef".toList
    String.mk [d[(b.toNat / 16)]!, d[(b.toNat % 16)]!])

def writeVectors (path : String) : IO Bool := do
  let mut rows : Array String := #[]
  let mut ok := true
  for (name, req) in vectorRequests do
    match proveRequest req with
    | none =>
      IO.println s!"FAIL vector {name}: no reference receipt"
      ok := false
    | some resp =>
      IO.println s!"ok   vector {name}: request {(requestCodecLawful.encode req).length} bytes, response {resp.length} bytes"
      rows := rows.push s!"    \{\"name\": \"{name}\", \"request\": \"{hex (requestCodecLawful.encode req)}\", \"response\": \"{hex resp}\"}"
  IO.FS.writeFile path ("{\n  \"source\": \"lake exe tower256-prover-run --vectors\",\n  \"vectors\": [\n" ++
    ",\n".intercalate rows.toList ++ "\n  ]\n}\n")
  return ok

end Minidregg.Compiler.Tower256SuccinctProverRun

open Minidregg.Compiler.Tower256SuccinctProverRun in
def main (args : List String) : IO UInt32 := do
  if let ["--vectors", path] := args then
    return if (← writeVectors path) then 0 else 1
  let a ← shapeA
  let b ← shapeB
  if a && b then
    IO.println "tower256-prover-run: all observations hold"
    return 0
  else
    IO.println "tower256-prover-run: an observation failed"
    return 1
