/-
# Bounded forward-link semantic benchmark

This executable measures the actual computable four-slot content-page path:
canonical link-entry encoding, `Page.admitInsert`, typed-patch validation and
Lean cSHAKE materialization, state-codec reopen, canonical link lookup, and
physical page-route lookup.  The exercised values are variants of the closed
`Compiler.HyperdocumentContentPageMaterializer` forward-link example.

It does not time the proof-only/noncomputable first-order endpoint, an OS read,
or the Rust store.  The companion native benchmark measures the opaque
process/filesystem lifecycle.  The runner builds the endpoint, durable weld,
local-file join, and this materializer, so one exact-source evidence record
retains the proof join and both timing surfaces without pretending they are a
cross-language refinement theorem.
-/
import Compiler.HyperdocumentContentPageMaterializer

namespace Minidregg.Bench.ForwardLinkSemantic

open Minidregg.Compiler.HyperdocumentContentPageMaterializer
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def schemaName : String := "minidregg/forward-link-semantic/v1"
def samples : Nat := 31
def warmups : Nat := 3
def ordinaryRepetitions : Nat := 16
def rootRepetitions : Nat := 1

def linkIdAt (nonce : Nat) : LinkId := ⟨⟨102 + nonce⟩⟩

def linkAt (nonce : Nat) : ForwardLink :=
  { forwardLink with
    relation := ⟨1400 + nonce⟩
    operation := ⟨⟨1401 + nonce⟩⟩ }

def entryAt (nonce : Nat) : Entry := .link (linkIdAt nonce) (linkAt nonce)

def prePageAt (nonce : Nat) : Page :=
  { genesisPage with pageNumber := nonce }

def postPageAt (nonce : Nat) : Page :=
  { prePageAt nonce with slot2 := some (entryAt nonce) }

def preCellAt (nonce : Nat) : Materialized materializer :=
  CellState.materialize materializer (stateOfOption (some (prePageAt nonce)))

def postCellAt (nonce : Nat) : Materialized materializer :=
  CellState.materialize materializer (stateOfOption (some (postPageAt nonce)))

def patchAt (nonce : Nat) : CellState.Patch schema Digest where
  expectedPreRoot := (preCellAt nonce).root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some (postPageAt nonce) }]
  resourceWrites := []

def entryBytes (nonce : Nat) : List UInt8 := entryStream.encode (entryAt nonce)
def pageBytes (nonce : Nat) : List UInt8 := (postCellAt nonce).bytes

def encodedEntryExact (nonce : Nat) : Bool :=
  decide (entryStream.toLawful.decode (entryBytes nonce) = some (entryAt nonce))

def admittedExact (nonce : Nat) : Bool :=
  match (prePageAt nonce).admitInsert (entryAt nonce) with
  | .error _ => false
  | .ok post => decide (post.1 = postPageAt nonce)

def installedExact (nonce : Nat) : Bool :=
  match CellState.validate materializer (preCellAt nonce) (patchAt nonce) with
  | .rejected _ => false
  | .accepted validated =>
      decide (validated.apply.bytes = (postCellAt nonce).bytes) &&
        decide (validated.apply.root = (postCellAt nonce).root)

def reopenedExact (nonce : Nat) : Bool :=
  match stateCodec.decode (pageBytes nonce) with
  | none => false
  | some reopened => decide (pageAt reopened = some (postPageAt nonce))

def queriedExact (nonce : Nat) : Bool :=
  match (show Option LinkRecord from
    Hyperdocument.lookup (postPageAt nonce).toCanonicalState .links
      (linkIdAt nonce)) with
  | none => false
  | some found => found == (linkAt nonce).toCanonical

def routedExact (nonce : Nat) : Bool :=
  (postPageAt nonce).routeForLink (linkIdAt nonce) == some targetPage

def semanticExact (nonce : Nat) : Bool :=
  decide ((prePageAt nonce).Valid) && decide ((postPageAt nonce).Valid) &&
    encodedEntryExact nonce && admittedExact nonce && installedExact nonce &&
    reopenedExact nonce && queriedExact nonce && routedExact nonce

@[noinline] def submitEncodeWork (nonce : Nat) : Nat :=
  (entryBytes nonce).foldl (fun checksum byte => checksum + byte.toNat) 0

@[noinline] def validateInsertWork (nonce : Nat) : Nat :=
  match (prePageAt nonce).admitInsert (entryAt nonce) with
  | .error _ => 0
  | .ok post => post.1.entries.length + post.1.pageNumber

@[noinline] def logicalInstallRootWork (nonce : Nat) : Nat :=
  match CellState.validate materializer (preCellAt nonce) (patchAt nonce) with
  | .rejected _ => 0
  | .accepted validated => validated.apply.root.value % 1000003

@[noinline] def reopenWork (nonce : Nat) : Nat :=
  match stateCodec.decode (pageBytes nonce) with
  | none => 0
  | some reopened =>
      (pageAt reopened).map
        (fun page => page.entries.length + page.pageNumber) |>.getD 0

@[noinline] def canonicalQueryWork (nonce : Nat) : Nat :=
  match (show Option LinkRecord from
    Hyperdocument.lookup (postPageAt nonce).toCanonicalState .links
      (linkIdAt nonce)) with
  | none => 0
  | some record => record.relation.value + nonce

@[noinline] def routeQueryWork (nonce : Nat) : Nat :=
  match (postPageAt nonce).routeForLink (linkIdAt nonce) with
  | none => 0
  | some page => page.expectedRoot.value + page.pageNumber + nonce

def repeatChecksum (operation : Nat → Nat) : Nat → Nat → Nat
  | 0, accumulator => accumulator
  | repetitions + 1, accumulator =>
      repeatChecksum operation repetitions
        (accumulator + operation repetitions)

def insertSorted (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      if value ≤ head then value :: head :: tail
      else head :: insertSorted value tail

def sortSamples (values : List Nat) : List Nat :=
  values.foldr insertSorted []

def nearestRank (sorted : List Nat) (percentile : Nat) : Nat :=
  let rank := (percentile * sorted.length + 99) / 100
  (sorted[rank.saturatingSub 1]?).getD 0

def runUntimed (repetitions : Nat) (operation : Nat → Nat) : IO Unit := do
  let sink ← IO.mkRef 0
  let checksum := repeatChecksum operation repetitions 0
  sink.set checksum
  let forced ← sink.get
  if forced = 0 then
    throw <| IO.userError "warmup produced a zero checksum"

def runStage (stage : String) (repetitions encodedBytes : Nat)
    (operation : Nat → Nat) : IO Unit := do
  for _warmup in List.range warmups do
    runUntimed repetitions operation
  let observations ← IO.mkRef ([] : List Nat)
  for sample in List.range samples do
    let sink ← IO.mkRef 0
    let started ← IO.monoNanosNow
    let checksum := repeatChecksum operation repetitions 0
    sink.set checksum
    let forced ← sink.get
    let finished ← IO.monoNanosNow
    if forced = 0 then
      throw <| IO.userError s!"stage {stage} produced a zero checksum"
    let elapsed := finished - started
    let perOperation := elapsed / repetitions
    observations.modify (perOperation :: ·)
    let phase := if sample = 0 then "first_measured_after_warmup"
      else "repeated_after_warmup"
    IO.println s!"sample,{schemaName},{phase},{sample},{stage},{repetitions},\
      {elapsed},{perOperation},{encodedBytes},{forced}"
  let sorted := sortSamples (← observations.get)
  IO.println s!"summary,{schemaName},{stage},{samples},\
    {nearestRank sorted 50},{nearestRank sorted 95},{nearestRank sorted 99},\
    {(sorted.head?).getD 0},{(sorted.getLast?).getD 0},{repetitions},\
    {encodedBytes}"

def main : IO Unit := do
  unless semanticExact 0 do
    throw <| IO.userError "bounded forward-link semantic regression"
  let entrySize := (entryBytes 0).length
  let postSize := (pageBytes 0).length
  IO.println s!"benchmark={schemaName}"
  IO.println s!"samples={samples}"
  IO.println s!"warmups_per_stage={warmups}"
  IO.println s!"entry_bytes={entrySize}"
  IO.println s!"post_page_bytes={postSize}"
  IO.println "timing=IO.monoNanosNow in one warmed Lean process"
  IO.println "cache_state=uncontrolled; no cold-cache claim"
  IO.println "memory=not_reported; no reliable per-stage allocator/RSS attribution"
  IO.println "semantic_scope=computable bounded content page only; not OS, endpoint delivery, or Rust refinement"
  IO.println "record,schema,phase,sample,stage,repetitions,elapsed_ns,per_operation_ns,encoded_bytes,checksum"
  runStage "submit_entry_encode" ordinaryRepetitions entrySize submitEncodeWork
  runStage "validate_insert" ordinaryRepetitions postSize validateInsertWork
  runStage "logical_install_cshake_root" rootRepetitions postSize
    logicalInstallRootWork
  runStage "reopen_page_codec" ordinaryRepetitions postSize reopenWork
  runStage "canonical_link_query" ordinaryRepetitions postSize
    canonicalQueryWork
  runStage "physical_page_route_query" ordinaryRepetitions postSize
    routeQueryWork
  IO.println "record,schema,stage,samples,p50_per_operation_ns,p95_per_operation_ns,p99_per_operation_ns,min_per_operation_ns,max_per_operation_ns,repetitions,encoded_bytes"
  IO.println "semantic_status=PASS"

end Minidregg.Bench.ForwardLinkSemantic

def main : IO Unit := Minidregg.Bench.ForwardLinkSemantic.main
