/-
# Forward-link semantic benchmark on the deployed content cell

This executable measures the actual computable forward-link path on the
deployed Hyperdocument content cell (`HyperdocumentCell.contentMaterializer`,
the `StoreCodec` wire): canonical link-entry encoding, guarded-patch validity
at the pre-store, validation plus Lean cSHAKE materialization, codec reopen,
and canonical link lookup.  There is no capacity and no cross-page route: the
link is one guarded allocation in the one document cell.

It does not time the proof-only/noncomputable first-order endpoint, an OS read,
or the Rust store.  The companion native benchmark measures the opaque
process/filesystem lifecycle.  The runner builds the endpoint, durable weld,
local-file join, and the content cell, so one exact-source evidence record
retains the proof join and both timing surfaces without pretending they are a
cross-language refinement theorem.
-/
import Compiler.HyperdocumentCell

namespace Minidregg.Bench.ForwardLinkSemantic

open Minidregg.Compiler
open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

def schemaName : String := "minidregg/forward-link-semantic/v2"
def samples : Nat := 31
def warmups : Nat := 3
def ordinaryRepetitions : Nat := 16
def rootRepetitions : Nat := 1

abbrev ContentStore := Store.Store Hyperdocument.layout

def author : PrincipalRef := ⟨⟨7⟩, .object, ⟨11⟩⟩
def sourceDocument : DocumentId := ⟨⟨100⟩⟩
def rootElement : ElementId := ⟨⟨101⟩⟩

def documentRecord : DocumentRecord :=
  ⟨rootElement, ⟨14⟩, author, ⟨⟨1300⟩⟩⟩

def elementRecord : ElementRecord :=
  ⟨sourceDocument, none, .container [], author, ⟨⟨1300⟩⟩, none⟩

def linkIdAt (nonce : Nat) : LinkId := ⟨⟨102 + nonce⟩⟩

def linkAt (nonce : Nat) : LinkRecord where
  sourceDocument := sourceDocument
  source := none
  target := .external [0x68, 0x74, 0x74, 0x70, 0x73] [0x65, 0x78]
    [0x2f, 0x6c, 0x6f, 0x6f, 0x6d]
  relation := ⟨1400 + nonce⟩
  author := author
  operation := ⟨⟨1401 + nonce⟩⟩
  tombstonedAt := none

/-- The document's genesis records; the nonce varies the root element's
creation operation so repeated work is not shared across nonces. -/
def preStoreAt (nonce : Nat) : ContentStore :=
  ((0 : ContentStore).set ⟨.documents, sourceDocument⟩ (some documentRecord)).set
    ⟨.elements, rootElement⟩ (some { elementRecord with createdAt := ⟨⟨1300 + nonce⟩⟩ })

def patchAt (nonce : Nat) : Store.Patch Hyperdocument.layout :=
  [.allocate .links (linkIdAt nonce) (linkAt nonce)]

def postStoreAt (nonce : Nat) : ContentStore :=
  (preStoreAt nonce).set ⟨.links, linkIdAt nonce⟩ (some (linkAt nonce))

def preCellAt (nonce : Nat) : Materialized HyperdocumentCell.contentMaterializer :=
  CellState.materialize HyperdocumentCell.contentMaterializer (preStoreAt nonce)

def postCellAt (nonce : Nat) : Materialized HyperdocumentCell.contentMaterializer :=
  CellState.materialize HyperdocumentCell.contentMaterializer (postStoreAt nonce)

def entryBytes (nonce : Nat) : List UInt8 :=
  (identifierStream .v1 .link).encode (linkIdAt nonce) ++
    HyperdocumentCell.linkRecordStream.encode (linkAt nonce)

def postBytes (nonce : Nat) : List UInt8 := (postCellAt nonce).bytes

def encodedEntryExact (nonce : Nat) : Bool :=
  decide (HyperdocumentCell.linkRecordStream.toLawful.decode
    (HyperdocumentCell.linkRecordStream.encode (linkAt nonce)) = some (linkAt nonce))

def validExact (nonce : Nat) : Bool :=
  decide (Store.Patch.ValidFrom (preStoreAt nonce) (patchAt nonce))

def installedExact (nonce : Nat) : Bool :=
  match CellState.validate HyperdocumentCell.contentMaterializer (preCellAt nonce)
      (preCellAt nonce).root (patchAt nonce) with
  | .rejected _ => false
  | .accepted validated =>
      decide (validated.apply.bytes = (postCellAt nonce).bytes) &&
        decide (validated.apply.root = (postCellAt nonce).root)

def reopenedExact (nonce : Nat) : Bool :=
  match HyperdocumentCell.contentMaterializer.codec.decode (postBytes nonce) with
  | none => false
  | some reopened =>
      decide (Hyperdocument.lookup reopened .links (linkIdAt nonce) = some (linkAt nonce))

def queriedExact (nonce : Nat) : Bool :=
  match (show Option LinkRecord from
    Hyperdocument.lookup (postStoreAt nonce) .links (linkIdAt nonce)) with
  | none => false
  | some found => found == linkAt nonce

def semanticExact (nonce : Nat) : Bool :=
  encodedEntryExact nonce && validExact nonce && installedExact nonce &&
    reopenedExact nonce && queriedExact nonce

@[noinline] def submitEncodeWork (nonce : Nat) : Nat :=
  (entryBytes nonce).foldl (fun checksum byte => checksum + byte.toNat) 0

@[noinline] def validatePatchWork (nonce : Nat) : Nat :=
  if decide (Store.Patch.ValidFrom (preStoreAt nonce) (patchAt nonce)) then nonce + 1 else 0

@[noinline] def logicalInstallRootWork (nonce : Nat) : Nat :=
  match CellState.validate HyperdocumentCell.contentMaterializer (preCellAt nonce)
      (preCellAt nonce).root (patchAt nonce) with
  | .rejected _ => 0
  | .accepted validated => validated.apply.root.value % 1000003

@[noinline] def reopenWork (nonce : Nat) : Nat :=
  match HyperdocumentCell.contentMaterializer.codec.decode (postBytes nonce) with
  | none => 0
  | some reopened => reopened.support.card + nonce

@[noinline] def canonicalQueryWork (nonce : Nat) : Nat :=
  match (show Option LinkRecord from
    Hyperdocument.lookup (postStoreAt nonce) .links (linkIdAt nonce)) with
  | none => 0
  | some record => record.relation.value + nonce

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
  (sorted[rank - 1]?).getD 0

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
    throw <| IO.userError "forward-link content-cell semantic regression"
  let entrySize := (entryBytes 0).length
  let postSize := (postBytes 0).length
  IO.println s!"benchmark={schemaName}"
  IO.println s!"samples={samples}"
  IO.println s!"warmups_per_stage={warmups}"
  IO.println s!"entry_bytes={entrySize}"
  IO.println s!"post_cell_bytes={postSize}"
  IO.println "timing=IO.monoNanosNow in one warmed Lean process"
  IO.println "cache_state=uncontrolled; no cold-cache claim"
  IO.println "memory=not_reported; no reliable per-stage allocator/RSS attribution"
  IO.println "semantic_scope=computable deployed content cell only; not OS, endpoint delivery, or Rust refinement"
  IO.println "record,schema,phase,sample,stage,repetitions,elapsed_ns,per_operation_ns,encoded_bytes,checksum"
  runStage "submit_entry_encode" ordinaryRepetitions entrySize submitEncodeWork
  runStage "validate_patch" ordinaryRepetitions postSize validatePatchWork
  runStage "logical_install_cshake_root" rootRepetitions postSize
    logicalInstallRootWork
  runStage "reopen_store_codec" ordinaryRepetitions postSize reopenWork
  runStage "canonical_link_query" ordinaryRepetitions postSize
    canonicalQueryWork
  IO.println "record,schema,stage,samples,p50_per_operation_ns,p95_per_operation_ns,p99_per_operation_ns,min_per_operation_ns,max_per_operation_ns,repetitions,encoded_bytes"
  IO.println "semantic_status=PASS"

end Minidregg.Bench.ForwardLinkSemantic

def main : IO Unit := Minidregg.Bench.ForwardLinkSemantic.main
