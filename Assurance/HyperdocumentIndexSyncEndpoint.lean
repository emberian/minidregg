/-
# Assurance.HyperdocumentIndexSyncEndpoint -- closed persistent search witness

This module closes one four-slot Hyperdocument index lifecycle.  A concrete
stable-range link is inserted by an exact causal delta, both target and range
queries are complete over all four slots, the canonical page round-trips
through its framed codec, and an origin-neutral byte controller returns the
same bounded result after logical sync/crash/reopen.  Exact retry is recognized
without applying the delta twice, while checkpoint drift is rejected.

The reader boundary is deliberately `Except Error bytes`.  No theorem below
says that a native reader performed physical I/O, that a crawler found links
outside this page, that a network is live, that the causal head is externally
final, or that cSHAKE collision resistance has been proved.
-/
import Assurance.HyperdocumentLinkPublicationWitness
import Compiler.HyperdocumentIndexPageMaterializer

namespace Minidregg.Assurance.HyperdocumentIndexSyncEndpoint

open Minidregg.Assurance.HyperdocumentLinkPublicationWitness
open Minidregg.Compiler.HyperdocumentCodec
open Minidregg.Compiler.HyperdocumentIndexPageMaterializer
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

/-! ## Exact causal delta and fresh finite page -/

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
bounded-page completeness, not a global backlink assertion. -/
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

def nextPage : Page := Page.ofSnapshot nextSnapshot
def nextState : LogicalState schema := stateOfOption (some nextPage)
def nextBytes : List UInt8 := stateCodec.encode nextState

@[simp] theorem nextPage_source_checkpoint :
    nextPage.sourceCheckpoint = afterCheckpoint := by
  rfl

@[simp] theorem page_round_trip :
    stateCodec.decode nextBytes = some nextState :=
  stateCodec.decode_encode nextState

@[simp] theorem pageAt_nextState : pageAt nextState = some nextPage := by
  rfl

@[simp] theorem page_reopens_exact_snapshot :
    nextPage.toSnapshot = nextSnapshot :=
  Page.toSnapshot_ofSnapshot nextSnapshot

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
  | malformedPage
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
          match stateCodec.decode bytes with
          | none => .error .malformedPage
          | some state =>
              match pageAt state with
              | none => .error .malformedPage
              | some page =>
                  if page.sourceCheckpoint != request.expectedCheckpoint then
                    .error .staleCheckpoint
                  else
                    match page.status with
                    | .current =>
                        .ok (responseCodec.encode
                          (evaluate page.toSnapshot request.query))
                    | stale => .error (.staleIndex stale)

def targetRequest : Request :=
  ⟨afterCheckpoint, .backlinks (.document targetDocument)⟩

def rangeRequest : Request :=
  ⟨afterCheckpoint, .stableRange Genesis.documentId sourceRange⟩

def pageReader (_ : Unit) : Except Empty (List UInt8) := .ok nextBytes

theorem nextPage_current : nextPage.status = .current := by
  apply (status_current_iff nextPage.toSnapshot).2
  simpa [nextPage] using next_fresh

@[simp] theorem target_run_exact :
    run (requestCodec.encode targetRequest) pageReader =
      .ok (responseCodec.encode [derivedRow]) := by
  unfold run
  rw [requestCodec.decode_encode]
  simp only [pageReader, page_round_trip, pageAt_nextState, targetRequest,
    nextPage_source_checkpoint, bne_self_eq_false', Bool.false_eq_true, ↓reduceIte,
    nextPage_current]
  rw [page_reopens_exact_snapshot]
  change Except.ok (responseCodec.encode
    (collectBacklinks nextSnapshot (.document targetDocument))) = _
  rw [exact_target_results]

@[simp] theorem range_run_exact :
    run (requestCodec.encode rangeRequest) pageReader =
      .ok (responseCodec.encode [derivedRow]) := by
  unfold run
  rw [requestCodec.decode_encode]
  simp only [pageReader, page_round_trip, pageAt_nextState, rangeRequest,
    nextPage_source_checkpoint, bne_self_eq_false', Bool.false_eq_true, ↓reduceIte,
    nextPage_current]
  rw [page_reopens_exact_snapshot]
  change Except.ok (responseCodec.encode
    (collectStableRanges nextSnapshot Genesis.documentId sourceRange)) = _
  rw [exact_range_results]

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

def stalePage : Page := Page.ofSnapshot staleSnapshot
def staleState : LogicalState schema := stateOfOption (some stalePage)
def staleBytes : List UInt8 := stateCodec.encode staleState

@[simp] theorem stale_round_trip :
    stateCodec.decode staleBytes = some staleState :=
  stateCodec.decode_encode staleState

@[simp] theorem pageAt_staleState : pageAt staleState = some stalePage := by
  rfl

@[simp] theorem stalePage_source_checkpoint :
    stalePage.sourceCheckpoint = futureCheckpoint := by
  rfl

@[simp] theorem stalePage_index_checkpoint :
    stalePage.indexCheckpoint = afterCheckpoint := by
  rfl

@[simp] theorem stale_page_status : stalePage.status = .staleCheckpoint := by
  apply stale_checkpoint_detected
  simpa using after_ne_future

def futureRequest : Request :=
  ⟨futureCheckpoint, .backlinks (.document targetDocument)⟩

def staleReader (_ : Unit) : Except Empty (List UInt8) := .ok staleBytes

@[simp] theorem stale_index_rejected :
    run (requestCodec.encode futureRequest) staleReader =
      .error (.staleIndex .staleCheckpoint) := by
  unfold run
  rw [requestCodec.decode_encode]
  simp only [staleReader, stale_round_trip, pageAt_staleState, futureRequest,
    stalePage_source_checkpoint, bne_self_eq_false', Bool.false_eq_true, ↓reduceIte,
    stale_page_status]

def malformedReader (_ : Unit) : Except Empty (List UInt8) := .ok []

@[simp] theorem malformed_page_rejected :
    run (requestCodec.encode targetRequest) malformedReader =
      .error .malformedPage := by
  unfold run
  rw [requestCodec.decode_encode]
  rfl

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
