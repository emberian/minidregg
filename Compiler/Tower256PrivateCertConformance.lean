/-
# Compiler.Tower256PrivateCertConformance -- Conformance Vector Emitter for `Tower256PrivateContentCert`

Separated from `Compiler.Tower256PrivateContentCert` so `Compiler.lean` can import the proved
private-certificate controller without re-running `#eval` file IO. Precomputes `PreparedAutomaton`
(`FastCubeTree`) once per DFA, verifies every honest receipt and negative mutant via `checkPrivate`,
and writes `prover/testdata/tower256_private_cert_conformance.json` for `prover/tests/tower256_private_cert.rs`.
-/

import Compiler.Tower256PrivateContentCert
import Lean.Data.Json

namespace Minidregg.Compiler.Tower256PrivateCertConformance

open Minidregg.Theory.TypedAuthorization (Digest)
open Minidregg.Compiler.Tower256ContentCert (ClaimData DfaTable bytesOf)
open Minidregg.Compiler.Tower256SuccinctReceiptCodec (receiptCodec)
open Minidregg.Compiler.Tower256PrivateContentCert
open Lean (Json ToJson toJson)

set_option autoImplicit false

/-- Kernel-decided sanity check on the degree schedule used by the conformance vectors. -/
theorem conformance_degree_schedule_pin :
    privateDegreeSchedule 4 0 = 4 ∧
    privateDegreeSchedule 4 1 = 2 ∧
    privateDegreeSchedule 8 0 = 8 ∧
    privateDegreeSchedule 8 2 = 2 := by
  decide

private def hexBytes (bytes : List UInt8) : String :=
  String.join (bytes.map fun b =>
    let d := "0123456789abcdef".toList
    String.ofList [d[(b.toNat / 16)]!, d[(b.toNat % 16)]!])

private def natFixedLE (len val : Nat) : List UInt8 :=
  (List.range len).map fun i => UInt8.ofNat ((val / 256 ^ i) % 256)

private def digestHex (d : Digest) : String :=
  hexBytes (natFixedLE 32 d.value)

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

private def mkSalt (seed : Nat) (i : Nat) : Salt248 :=
  ⟨(0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d * (seed + 1) + 7919 * (i + 1)) % 2 ^ 248,
    Nat.mod_lt _ (by positivity)⟩

private def mkMask (seed : Nat) (i : Nat) : RowMask :=
  ⟨(0x0f1e2d3c4b5a69788796a5b4c3d2e1f0123456789abcde * (seed + 3) + 6151 * (i + 1)) % 2 ^ 184,
    Nat.mod_lt _ (by positivity)⟩

private def emitOneVector (name : String) (seed : Nat) (pa : PreparedAutomaton) (t : DfaTable)
    (text : String) (claim : ClaimData) (friEll friRounds friQueries stepQueries : Nat) : IO Json := do
  let w := bytesOf text
  let salts := (List.range w.length).map (mkSalt seed)
  let masks := (List.range w.length).map (mkMask seed)
  let some (stmt, receipt) :=
      provePrivatePrepared pa t w salts masks claim friEll friRounds friQueries stepQueries
    | throw (IO.userError s!"provePrivatePrepared failed for {name}")
  unless checkPrivate stmt receipt do
    throw (IO.userError s!"checkPrivate rejected honest receipt for {name}")
  if seed == 1 then
    let wrongClaim : ClaimData := match claim with
      | .accept b => .accept (!b)
      | .count n => .count (n + 1)
      | .bound _ hi => .bound (hi + 1) (hi + 2)
    if checkPrivate { stmt with claim := wrongClaim } receipt then
      throw (IO.userError s!"checkPrivate accepted forged claim for {name}")
    let badRoot : Digest := ⟨(stmt.contentRoot.value + 1) % 2 ^ 256⟩
    if checkPrivate { stmt with contentRoot := badRoot } receipt then
      throw (IO.userError s!"checkPrivate accepted mutated contentRoot for {name}")
    let badTrace : Digest := ⟨(receipt.traceRoot.value + 1) % 2 ^ 256⟩
    if checkPrivate stmt { receipt with traceRoot := badTrace } then
      throw (IO.userError s!"checkPrivate accepted mutated traceRoot for {name}")
    if checkPrivate { stmt with friQueries := stmt.friQueries + 1 } receipt then
      throw (IO.userError s!"checkPrivate accepted mismatched friQueries for {name}")
  let friBytes := (receiptCodec friEll friRounds friQueries).encode receipt.friReceipt
  let stepIndices := (List.range stepQueries).map (derivedStepIndex stmt receipt)
  return Json.mkObj
    [("name", toJson name),
     ("dfa", dfaJson t),
     ("automaton_root", toJson (digestHex stmt.automatonRoot)),
     ("delta_root", toJson (digestHex receipt.header.deltaRoot)),
     ("word_hex", toJson (hexBytes w)),
     ("salts_hex", toJson (salts.map fun s => hexBytes (natFixedLE 31 s.val))),
     ("row_masks_hex", toJson (masks.map fun m => hexBytes (natFixedLE 23 m.val))),
     ("content_root", toJson (digestHex stmt.contentRoot)),
     ("trace_root", toJson (digestHex receipt.traceRoot)),
     ("claim", claimJson claim),
     ("fri_ell", toJson friEll),
     ("fri_rounds", toJson friRounds),
     ("fri_queries", toJson friQueries),
     ("step_queries", toJson stepQueries),
     ("fri_initial_root", toJson (digestHex receipt.friInitialRoot)),
     ("fri_receipt_hex", toJson (hexBytes friBytes)),
     ("step_indices", toJson stepIndices),
     ("expected_run_state", toJson (t.run w)),
     ("expected_run_count", toJson (Dfaops.runCount t w))]

private def emitConformanceVectors : IO Unit := do
  let paNoSk := prepareAutomaton noSkDash
  let paAb := prepareAutomaton countAB
  let v1 ← emitOneVector "accept_true_no_sk" 1 paNoSk noSkDash "ok=1" (.accept true) 3 1 2 2
  let v2 ← emitOneVector "accept_false_has_sk" 2 paNoSk noSkDash "xsk-" (.accept false) 3 1 2 2
  let v3 ← emitOneVector "count_exact_ab" 3 paAb countAB "abab" (.count 2) 3 1 2 2
  let v4 ← emitOneVector "bound_range_ab" 4 paAb countAB "abab" (.bound 1 3) 3 1 2 2
  let doc := Json.mkObj
    [("schema", "minidregg.tower256_private_cert.v1"),
     ("source", "Compiler/Tower256PrivateCertConformance.lean"),
     ("vectors", Json.arr #[v1, v2, v3, v4])]
  IO.FS.writeFile "prover/testdata/tower256_private_cert_conformance.json" (doc.pretty ++ "\n")

#eval emitConformanceVectors

/-- info: 'Minidregg.Compiler.Tower256PrivateCertConformance.conformance_degree_schedule_pin' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms conformance_degree_schedule_pin

end Minidregg.Compiler.Tower256PrivateCertConformance
