/-
# Assurance.HyperdocumentIndexSyncEndpoint -- closed persistent search witness

This module closes one four-slot Hyperdocument index lifecycle.  A concrete
stable-range link is inserted by an exact causal delta, both target and range
queries are complete over all four slots, the index cell
(`HyperdocumentCell.indexMaterializer 4`, a `StoreCodec` cell) round-trips and
denotes exactly its snapshot, and an origin-neutral byte controller returns the
same bounded result after logical sync/crash/reopen.  Exact retry is recognized
without applying the delta twice, while checkpoint drift is rejected.

The reader boundary is deliberately `Except Error bytes`.  No theorem below
says that a native reader performed physical I/O, that a crawler found links
outside this index, that a network is live, that the causal head is externally
final, or that cSHAKE collision resistance has been proved.
-/
import Assurance.HyperdocumentLinkPublicationWitness
import Compiler.HyperdocumentCell

namespace Minidregg.Assurance.HyperdocumentIndexSyncEndpoint

open Minidregg.Assurance.HyperdocumentLinkPublicationWitness
open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.HyperdocumentCell (indexLayout indexMaterializer storeOfSnapshot
  snapshotOfStore snapshotOfStore_storeOfSnapshot checkpointStream indexedRowStream)
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.HyperdocumentIndexSync
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## One live stable-range backlink -/

def sourceRun : RunId := ⟨⟨8101⟩⟩
def sourceAtom : AtomId := ⟨⟨8102⟩⟩

def sourceRange : StableRange where
  start :=
    { run := sourceRun
      neighbor := some sourceAtom
      bias := .before
      death := .preferNextThenPrevious }
  finish :=
    { run := sourceRun
      neighbor := some sourceAtom
      bias := .after
      death := .preferPreviousThenNext }

def targetDocument : DocumentId := ⟨⟨8201⟩⟩
def rangeLinkId : LinkId := ⟨⟨8202⟩⟩

/-- This is canonical `LinkRecord` data using the accepted publication's exact
principal and operation provenance.  The assurance claim in this file begins
at indexing this supplied record; it does not claim a second accepted content
mutation created it. -/
def rangeRecord : LinkRecord where
  sourceDocument := Genesis.documentId
  source := some sourceRange
  target := .document targetDocument
  relation := ⟨8203⟩
  author := Genesis.author
  operation := linkDeclaration.operationId config
  tombstonedAt := none

def sourceEntry : SourceEntry := ⟨rangeLinkId, rangeRecord⟩

def derivedRow : IndexedRow where
  linkId := rangeLinkId
  sourceDocument := Genesis.documentId
  sourceRange := some sourceRange
  target := .document targetDocument
  relation := ⟨8203⟩
  operation := linkDeclaration.operationId config

@[simp] theorem sourceEntry_row : sourceEntry.row? = some derivedRow := by
  rfl

/-! ## Exact causal delta and fresh finite snapshot -/

def beforeCheckpoint : CausalCheckpoint where
  historyDomain := linkIntent.historyDomain
  document := Genesis.documentId
  head := some genesisStored.key
  sequence := 0

def afterCheckpoint : CausalCheckpoint where
  historyDomain := linkIntent.historyDomain
  document := Genesis.documentId
  head := some linkStored.key
  sequence := 1

@[simp] theorem checkpoint_follows :
    beforeCheckpoint.Follows afterCheckpoint := by
  exact ⟨rfl, rfl, rfl⟩

def emptyCorpus : Corpus 4 := fun _ => none

def beforeSnapshot : Snapshot 4 where
  sourceCheckpoint := beforeCheckpoint
  indexCheckpoint := beforeCheckpoint
  corpus := emptyCorpus
  index := rebuild emptyCorpus
  cursor := ⟨beforeCheckpoint, 4⟩

theorem before_fresh : beforeSnapshot.Fresh := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def delta : Delta 4 where
  beforeCheckpoint := beforeCheckpoint
  afterCheckpoint := afterCheckpoint
  slot := 0
  before := none
  after := some sourceEntry

@[simp] theorem delta_matches : beforeSnapshot.MatchesDelta delta := by
  exact ⟨rfl, rfl, checkpoint_follows⟩

def nextSnapshot : Snapshot 4 := beforeSnapshot.advance delta

theorem next_fresh : nextSnapshot.Fresh :=
  Snapshot.advance_fresh beforeSnapshot delta before_fresh

@[simp] theorem delta_applies :
    applyDelta beforeSnapshot delta = .applied nextSnapshot :=
  applyDelta_matched beforeSnapshot delta delta_matches

@[simp] theorem source_slot0_exact :
    nextSnapshot.corpus 0 = some sourceEntry := by
  rfl

@[simp] theorem source_slot1_empty : nextSnapshot.corpus 1 = none := by rfl
@[simp] theorem source_slot2_empty : nextSnapshot.corpus 2 = none := by rfl
@[simp] theorem source_slot3_empty : nextSnapshot.corpus 3 = none := by rfl

@[simp] theorem target_slot0_exact :
    backlinkAt nextSnapshot.index (.document targetDocument) 0 =
      some derivedRow := by
  exact backlinkAt_complete nextSnapshot next_fresh 0 sourceEntry
    source_slot0_exact rfl

@[simp] theorem range_slot0_exact :
    stableRangeAt nextSnapshot.index Genesis.documentId sourceRange 0 =
      some derivedRow := by
  exact stableRangeAt_complete nextSnapshot next_fresh 0 sourceEntry
    sourceRange source_slot0_exact rfl rfl

@[simp] theorem target_slot1_empty :
    backlinkAt nextSnapshot.index (.document targetDocument) 1 = none := by
  rfl

@[simp] theorem target_slot2_empty :
    backlinkAt nextSnapshot.index (.document targetDocument) 2 = none := by
  rfl

@[simp] theorem target_slot3_empty :
    backlinkAt nextSnapshot.index (.document targetDocument) 3 = none := by
  rfl

@[simp] theorem range_slot1_empty :
    stableRangeAt nextSnapshot.index Genesis.documentId sourceRange 1 = none := by
  rfl

@[simp] theorem range_slot2_empty :
    stableRangeAt nextSnapshot.index Genesis.documentId sourceRange 2 = none := by
  rfl

@[simp] theorem range_slot3_empty :
    stableRangeAt nextSnapshot.index Genesis.documentId sourceRange 3 = none := by
  rfl

/-- These collectors enumerate every inhabitant of `Fin 4`; their exactness is
bounded-index completeness, not a global backlink assertion. -/
def collectBacklinks (snapshot : Snapshot 4) (target : LinkTarget) :
    List IndexedRow :=
  [backlinkAt snapshot.index target 0,
    backlinkAt snapshot.index target 1,
    backlinkAt snapshot.index target 2,
    backlinkAt snapshot.index target 3].filterMap id

def collectStableRanges (snapshot : Snapshot 4) (document : DocumentId)
    (range : StableRange) : List IndexedRow :=
  [stableRangeAt snapshot.index document range 0,
    stableRangeAt snapshot.index document range 1,
    stableRangeAt snapshot.index document range 2,
    stableRangeAt snapshot.index document range 3].filterMap id

@[simp] theorem exact_target_results :
    collectBacklinks nextSnapshot (.document targetDocument) = [derivedRow] := by
  simp [collectBacklinks]

@[simp] theorem exact_range_results :
    collectStableRanges nextSnapshot Genesis.documentId sourceRange =
      [derivedRow] := by
  simp [collectStableRanges]

@[simp] theorem cursor_is_exact_complete_checkpoint :
    nextSnapshot.cursor = ⟨afterCheckpoint, 4⟩ ∧
      nextSnapshot.cursor.Complete 4 := by
  exact ⟨rfl, rfl⟩

/-! ## Canonical persistence and logical reopen -/

abbrev IndexStore := Store.Store (indexLayout 4)

def nextStore : IndexStore := storeOfSnapshot nextSnapshot
def nextBytes : List UInt8 := (indexMaterializer 4).codec.encode nextStore

@[simp] theorem cell_round_trip :
    (indexMaterializer 4).codec.decode nextBytes = some nextStore :=
  (indexMaterializer 4).codec.decode_encode nextStore

@[simp] theorem cell_reopens_exact_snapshot :
    snapshotOfStore nextStore = some nextSnapshot :=
  snapshotOfStore_storeOfSnapshot nextSnapshot

def device : Device 4 := ⟨beforeSnapshot, none⟩
def syncedDevice : Device 4 := (device.stage nextSnapshot).sync

@[simp] theorem crash_before_sync_reopens_before :
    ((device.stage nextSnapshot).crash).reopen = beforeSnapshot :=
  crash_before_sync_reopens_durable device nextSnapshot

@[simp] theorem crash_after_sync_reopens_after :
    (syncedDevice.crash).reopen = nextSnapshot :=
  crash_after_sync_reopens_next device nextSnapshot

@[simp] theorem retry_after_reopen_is_exact_replay :
    applyDelta ((syncedDevice.crash).reopen) delta =
      .replayed nextSnapshot := by
  exact sync_crash_reopen_retry device delta checkpoint_follows

/-! ## Bytes-to-bytes bounded query controller -/

inductive Query where
  | backlinks (target : LinkTarget)
  | stableRange (document : DocumentId) (range : StableRange)
  deriving DecidableEq

noncomputable def queryStream : StreamCodec Query where
  encode
    | .backlinks target => 0 :: linkTargetStream.encode target
    | .stableRange document range =>
        1 :: (identifierStream .v1 .document).encode document ++
          storedStableRangeStream.encode range
  decodePrefix
    | 0 :: bytes => do
        let (target, suffix) <- linkTargetStream.decodePrefix bytes
        some (.backlinks target, suffix)
    | 1 :: bytes => do
        let (document, afterDocument) <-
          (identifierStream .v1 .document).decodePrefix bytes
        let (range, suffix) <- storedStableRangeStream.decodePrefix afterDocument
        some (.stableRange document range, suffix)
    | _ => none
  decodePrefix_encode := by
    intro query suffix
    cases query with
    | backlinks target =>
        simp [linkTargetStream.decodePrefix_encode]
    | stableRange document range =>
        simp [List.append_assoc,
          (identifierStream .v1 .document).decodePrefix_encode,
          storedStableRangeStream.decodePrefix_encode]

structure Request where
  expectedCheckpoint : CausalCheckpoint
  query : Query
  deriving DecidableEq

noncomputable def requestStream : StreamCodec Request :=
  StreamCodec.xmap
    (StreamCodec.product checkpointStream queryStream)
    (fun request => (request.expectedCheckpoint, request.query))
    (fun wire => ⟨wire.1, wire.2⟩)
    (by intro request; rfl)

noncomputable def requestCodec : LawfulCodec Request := requestStream.toLawful
noncomputable def responseCodec : LawfulCodec (List IndexedRow) :=
  (StreamCodec.list indexedRowStream).toLawful

inductive Failure (NativeError : Type) where
  | native (error : NativeError)
  | malformedRequest
  | malformedCell
  | staleCheckpoint
  | staleIndex (status : Status)
  deriving Repr

def evaluate (snapshot : Snapshot 4) : Query -> List IndexedRow
  | .backlinks target => collectBacklinks snapshot target
  | .stableRange document range => collectStableRanges snapshot document range

/-- Native code can supply only bytes or an opaque error.  Lean owns both
decoders, all freshness checks, finite enumeration, and the response codec. -/
noncomputable def run {NativeError : Type}
    (requestBytes : List UInt8)
    (reader : Unit -> Except NativeError (List UInt8)) :
    Except (Failure NativeError) (List UInt8) :=
  match requestCodec.decode requestBytes with
  | none => .error .malformedRequest
  | some request =>
      match reader () with
      | .error error => .error (.native error)
      | .ok bytes =>
          match (indexMaterializer 4).codec.decode bytes with
          | none => .error .malformedCell
          | some store =>
              match snapshotOfStore store with
              | none => .error .malformedCell
              | some snapshot =>
                  if snapshot.sourceCheckpoint != request.expectedCheckpoint then
                    .error .staleCheckpoint
                  else
                    match status snapshot with
                    | .current =>
                        .ok (responseCodec.encode (evaluate snapshot request.query))
                    | stale => .error (.staleIndex stale)

def targetRequest : Request :=
  ⟨afterCheckpoint, .backlinks (.document targetDocument)⟩

def rangeRequest : Request :=
  ⟨afterCheckpoint, .stableRange Genesis.documentId sourceRange⟩

def cellReader (_ : Unit) : Except Empty (List UInt8) := .ok nextBytes

theorem next_current : status nextSnapshot = .current :=
  (status_current_iff nextSnapshot).2 next_fresh

@[simp] theorem next_source_checkpoint :
    nextSnapshot.sourceCheckpoint = afterCheckpoint :=
  rfl

/-- A current, checkpoint-matching index cell answers the decoded query. -/
theorem run_current {NativeError : Type} (request : Request) (bytes : List UInt8)
    (reader : Unit -> Except NativeError (List UInt8)) (store : IndexStore)
    (snapshot : Snapshot 4)
    (read : reader () = .ok bytes)
    (decoded : (indexMaterializer 4).codec.decode bytes = some store)
    (denotes : snapshotOfStore store = some snapshot)
    (checkpoint : snapshot.sourceCheckpoint = request.expectedCheckpoint)
    (current : status snapshot = .current) :
    run (requestCodec.encode request) reader =
      .ok (responseCodec.encode (evaluate snapshot request.query)) := by
  unfold run
  rw [requestCodec.decode_encode, read]
  simp only [decoded, denotes, checkpoint, bne_self_eq_false', Bool.false_eq_true,
    ↓reduceIte, current]

@[simp] theorem target_run_exact :
    run (requestCodec.encode targetRequest) cellReader =
      .ok (responseCodec.encode [derivedRow]) := by
  rw [run_current targetRequest nextBytes cellReader nextStore nextSnapshot rfl
    cell_round_trip cell_reopens_exact_snapshot next_source_checkpoint next_current]
  exact congrArg (fun rows => Except.ok (responseCodec.encode rows)) exact_target_results

@[simp] theorem range_run_exact :
    run (requestCodec.encode rangeRequest) cellReader =
      .ok (responseCodec.encode [derivedRow]) := by
  rw [run_current rangeRequest nextBytes cellReader nextStore nextSnapshot rfl
    cell_round_trip cell_reopens_exact_snapshot next_source_checkpoint next_current]
  exact congrArg (fun rows => Except.ok (responseCodec.encode rows)) exact_range_results

@[simp] theorem target_response_decodes :
    responseCodec.decode (responseCodec.encode [derivedRow]) =
      some [derivedRow] :=
  responseCodec.decode_encode [derivedRow]

/-! ## Stale-index and failure teeth -/

def futureCheckpoint : CausalCheckpoint :=
  { afterCheckpoint with sequence := 2 }

theorem after_ne_future : afterCheckpoint ≠ futureCheckpoint := by
  intro equal
  have sequence := congrArg CausalCheckpoint.sequence equal
  norm_num [afterCheckpoint, futureCheckpoint] at sequence

def staleSnapshot : Snapshot 4 :=
  { nextSnapshot with sourceCheckpoint := futureCheckpoint }

def staleStore : IndexStore := storeOfSnapshot staleSnapshot
def staleBytes : List UInt8 := (indexMaterializer 4).codec.encode staleStore

@[simp] theorem stale_round_trip :
    (indexMaterializer 4).codec.decode staleBytes = some staleStore :=
  (indexMaterializer 4).codec.decode_encode staleStore

@[simp] theorem stale_cell_reopens :
    snapshotOfStore staleStore = some staleSnapshot :=
  snapshotOfStore_storeOfSnapshot staleSnapshot

@[simp] theorem stale_source_checkpoint :
    staleSnapshot.sourceCheckpoint = futureCheckpoint :=
  rfl

@[simp] theorem stale_status : status staleSnapshot = .staleCheckpoint := by
  apply stale_checkpoint_detected
  change afterCheckpoint ≠ futureCheckpoint
  exact after_ne_future

def futureRequest : Request :=
  ⟨futureCheckpoint, .backlinks (.document targetDocument)⟩

def staleReader (_ : Unit) : Except Empty (List UInt8) := .ok staleBytes

/-- A checkpoint-matching but stale index cell is refused with its status. -/
theorem run_stale {NativeError : Type} (request : Request) (bytes : List UInt8)
    (reader : Unit -> Except NativeError (List UInt8)) (store : IndexStore)
    (snapshot : Snapshot 4) (stale : Status)
    (read : reader () = .ok bytes)
    (decoded : (indexMaterializer 4).codec.decode bytes = some store)
    (denotes : snapshotOfStore store = some snapshot)
    (checkpoint : snapshot.sourceCheckpoint = request.expectedCheckpoint)
    (staleStatus : status snapshot = stale) (notCurrent : stale ≠ .current) :
    run (requestCodec.encode request) reader = .error (.staleIndex stale) := by
  unfold run
  rw [requestCodec.decode_encode, read]
  simp only [decoded, denotes, checkpoint, bne_self_eq_false', Bool.false_eq_true,
    ↓reduceIte]
  rw [staleStatus]
  cases stale
  · exact absurd rfl notCurrent
  all_goals rfl

@[simp] theorem stale_index_rejected :
    run (requestCodec.encode futureRequest) staleReader =
      .error (.staleIndex .staleCheckpoint) :=
  run_stale futureRequest staleBytes staleReader staleStore staleSnapshot .staleCheckpoint rfl
    stale_round_trip stale_cell_reopens stale_source_checkpoint stale_status (by decide)

def malformedReader (_ : Unit) : Except Empty (List UInt8) := .ok []

@[simp] theorem malformed_cell_rejected :
    run (requestCodec.encode targetRequest) malformedReader =
      .error .malformedCell := by
  unfold run
  rw [requestCodec.decode_encode]
  have refused : (indexMaterializer 4).codec.decode [] = none := by
    change Minidregg.Compiler.StoreCodec.decode (Minidregg.Compiler.HyperdocumentCell.indexWire 4) [] = none
    unfold Minidregg.Compiler.StoreCodec.decode
    rw [if_neg]
    intro framed
    have lengths := congrArg List.length framed
    rw [Minidregg.Compiler.StoreCodec.frame_length] at lengths
    simp at lengths
  simp [malformedReader, refused]

def failedReader (_ : Unit) : Except Nat (List UInt8) := .error 503

@[simp] theorem native_error_is_opaque :
    run (requestCodec.encode targetRequest) failedReader =
      .error (.native 503) := by
  unfold run
  rw [requestCodec.decode_encode]
  rfl

/-! ## Explicit trust ceiling -/

/-- Required before this bounded logical result may be promoted to a claim of
global search completeness, physical durability, network liveness, external
finality, or cryptographic binding.  This module constructs no inhabitant. -/
structure ExternalCompletion
    (GlobalCoverage PhysicalIORefined NetworkLive ExternallyFinal
      CshakeBinding : Prop) : Prop where
  globalCoverage : GlobalCoverage
  physicalIORefined : PhysicalIORefined
  networkLive : NetworkLive
  externallyFinal : ExternallyFinal
  cshakeBinding : CshakeBinding

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentIndexSyncEndpoint.target_run_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms target_run_exact
/-- info: 'Minidregg.Assurance.HyperdocumentIndexSyncEndpoint.retry_after_reopen_is_exact_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms retry_after_reopen_is_exact_replay
/-- info: 'Minidregg.Assurance.HyperdocumentIndexSyncEndpoint.stale_index_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_index_rejected

end

end Minidregg.Assurance.HyperdocumentIndexSyncEndpoint
