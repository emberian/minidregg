/-
# Compiler.Tower256AlgebraicCertConformance -- Conformance Vector Emitter for `Tower256AlgebraicCert`

Separated from `Compiler.Tower256AlgebraicCert` so `Compiler.lean` can import the proved
zero-byte-leakage algebraic certificate controller without re-running `#eval` file IO.
Generates 4 complete algebraic + `LogUp256` + coset-FRI receipts across `.accept true`,
`.accept false`, `.count 2`, and `.bound 1 3`, verifies every honest receipt and 5 negative
mutants via `checkAlgebraic`, and writes `prover/testdata/tower256_algebraic_cert_conformance.json`
for byte-exact cross-language verification by `prover/tests/tower256_algebraic_cert.rs`.
-/

import Compiler.Tower256AlgebraicCert
import Lean.Data.Json

namespace Minidregg.Compiler.Tower256AlgebraicCertConformance

open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Theory.BinaryTowerFanPaarCodec (Coordinate)
open Minidregg.Compiler.Tower256CoordinateMerkle (encodeC)
open Minidregg.Compiler.Tower256FinalPolynomialCheck (C8)
open Minidregg.Compiler.Tower256ContentCert (ClaimData DfaTable bytesOf)
open Minidregg.Compiler.Tower256SuccinctReceiptCodec (receiptCodec)
open Minidregg.Compiler.Tower256PrivateContentCert
open Minidregg.Compiler.Tower256AlgebraicCert
open Lean (Json ToJson toJson)

set_option autoImplicit false

/-- Kernel-decided sanity pin on `algDegreeSchedule` (`finalDegree = 1` at `friRounds = cubeDim + 1`). -/
theorem conformance_alg_degree_schedule_pin :
    algDegreeSchedule 10 0 = 2048 ∧
    algDegreeSchedule 10 10 = 2 ∧
    algDegreeSchedule 10 11 = 1 := by
  decide

private def hexBytes (bytes : List UInt8) : String :=
  String.join (bytes.map fun b =>
    let d := "0123456789abcdef".toList
    String.ofList [d[(b.toNat / 16)]!, d[(b.toNat % 16)]!])

private def natFixedLE (len val : Nat) : List UInt8 :=
  (List.range len).map fun i => UInt8.ofNat ((val / 256 ^ i) % 256)

private def digestHex (d : Digest) : String :=
  hexBytes (natFixedLE 32 d.value)

private def c8Hex (c : C8) : String :=
  hexBytes (encodeC c)

private def claimJson : ClaimData → Json
  | .accept b => Json.mkObj [("kind", "accept"), ("value", toJson b)]
  | .count n => Json.mkObj [("kind", "count"), ("value", toJson n)]
  | .bound lo hi => Json.mkObj [("kind", "bound"), ("lo", toJson lo), ("hi", toJson hi)]

private def dfaJson (t : DfaTable) : Json :=
  Json.mkObj
    [("states", toJson t.states),
     ("initial", toJson t.initial),
     ("accepting", toJson t.accepting),
     ("delta", toJson t.delta)]

private def polyDeg4Json (p : PolyDeg4) : Json :=
  Json.arr #[toJson (c8Hex p.c0), toJson (c8Hex p.c1), toJson (c8Hex p.c2),
             toJson (c8Hex p.c3), toJson (c8Hex p.c4)]

private def polyDeg2Json (p : PolyDeg2) : Json :=
  Json.arr #[toJson (c8Hex p.c0), toJson (c8Hex p.c1), toJson (c8Hex p.c2)]

private def emitOneAlgVector (name : String) (seed : Nat) (t : DfaTable)
    (text : String) (claim : ClaimData) (cubeDim friEll friQueries : Nat) : IO Json := do
  let w := bytesOf text
  let friRounds := cubeDim + 1
  let some (stmt, receipt) := proveAlgebraic t w claim seed cubeDim friEll friQueries
    | throw (IO.userError s!"proveAlgebraic failed for {name}")
  unless checkAlgebraic stmt receipt do
    throw (IO.userError s!"checkAlgebraic rejected honest receipt for {name}")
  -- Run adversarial mutant checks on `seed == 1` via `checkAlgebraic`
  if seed == 1 then
    let wrongClaim : ClaimData := match claim with
      | .accept b => .accept (!b)
      | .count n => .count (n + 1)
      | .bound _ hi => .bound (hi + 1) (hi + 2)
    if checkAlgebraic { stmt with claim := wrongClaim } receipt then
      throw (IO.userError s!"checkAlgebraic accepted forged claim for {name}")
    let badContent : Digest := ⟨(stmt.contentRoot.value + 1) % 2 ^ 256⟩
    if checkAlgebraic { stmt with contentRoot := badContent } receipt then
      throw (IO.userError s!"checkAlgebraic accepted mutated contentRoot for {name}")
    let badP1 : Digest := ⟨(receipt.phase1Root.value + 1) % 2 ^ 256⟩
    if checkAlgebraic stmt { receipt with phase1Root := badP1 } then
      throw (IO.userError s!"checkAlgebraic accepted mutated phase1Root for {name}")
    let badMult : Digest := ⟨(receipt.multRoot.value + 1) % 2 ^ 256⟩
    if checkAlgebraic stmt { receipt with multRoot := badMult } then
      throw (IO.userError s!"checkAlgebraic accepted mutated multRoot for {name}")
    let badEval := receipt.colEvalsAtR.set! 0 (Coordinate.one 8)
    if checkAlgebraic stmt { receipt with colEvalsAtR := badEval } then
      throw (IO.userError s!"checkAlgebraic accepted mutated colEvalsAtR for {name}")
  let friBytes := (receiptCodec friEll friRounds friQueries).encode receipt.friReceipt
  let seedsList := (List.finRange friQueries).map fun a => (receipt.friReceipt.querySeed a).val
  return Json.mkObj
    [("name", toJson name),
     ("seed", toJson seed),
     ("dfa", dfaJson t),
     ("automaton_root", toJson (digestHex stmt.automatonRoot)),
     ("word_hex", toJson (hexBytes w)),
     ("claim", claimJson claim),
     ("cube_dim", toJson cubeDim),
     ("fri_ell", toJson friEll),
     ("fri_rounds", toJson friRounds),
     ("fri_queries", toJson friQueries),
     ("content_root", toJson (digestHex stmt.contentRoot)),
     ("phase1_root", toJson (digestHex receipt.phase1Root)),
     ("mult_root", toJson (digestHex receipt.multRoot)),
     ("phase3_root", toJson (digestHex receipt.phase3Root)),
     ("sumcheck_polys", Json.arr (receipt.sumcheckPolys.map polyDeg4Json)),
     ("col_evals_at_r", Json.arr (receipt.colEvalsAtR.map (toJson ∘ c8Hex))),
     ("bf_polys", Json.arr (receipt.bfPolys.map polyDeg2Json)),
     ("bf_final_coeff", toJson (c8Hex receipt.bfFinalCoeff)),
     ("eval_fold_roots", Json.arr (receipt.evalFoldRoots.map (toJson ∘ digestHex))),
     ("fri_initial_root", toJson (digestHex receipt.friInitialRoot)),
     ("fri_receipt_hex", toJson (hexBytes friBytes)),
     ("fri_query_seeds", toJson seedsList),
     ("expected_run_state", toJson (t.run w)),
     ("expected_run_count", toJson (Dfaops.runCount t w))]

private def emitAlgebraicConformanceVectors : IO Unit := do
  -- `noSkDash` has `4 * 256 = 1024 = 2^10`, `countAB` has `3 * 256 = 768 <= 2^10`, so `cubeDim = 10`, `friEll = 12`, `friQueries = 2`.
  let v1 ← emitOneAlgVector "alg_accept_true_no_sk" 1 noSkDash "ok=1" (.accept true) 10 12 2
  let v2 ← emitOneAlgVector "alg_accept_false_has_sk" 2 noSkDash "xsk-" (.accept false) 10 12 2
  let v3 ← emitOneAlgVector "alg_count_exact_ab" 3 countAB "abab" (.count 2) 10 12 2
  let v4 ← emitOneAlgVector "alg_bound_range_ab" 4 countAB "ababab" (.bound 2 4) 10 12 2
  let doc := Json.mkObj
    [("schema", "minidregg.tower256_algebraic_cert.v1"),
     ("source", "Compiler/Tower256AlgebraicCertConformance.lean"),
     ("vectors", Json.arr #[v1, v2, v3, v4])]
  IO.FS.writeFile "prover/testdata/tower256_algebraic_cert_conformance.json" (doc.pretty ++ "\n")

#eval emitAlgebraicConformanceVectors

/-- info: 'Minidregg.Compiler.Tower256AlgebraicCertConformance.conformance_alg_degree_schedule_pin' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms conformance_alg_degree_schedule_pin

end Minidregg.Compiler.Tower256AlgebraicCertConformance
