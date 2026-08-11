/-
# Assurance.HyperdocumentLinkPageDurableWeld -- accepted link to bounded bytes

The logical link-publication witness and the bounded production page codecs
previously met only by informal correspondence.  This module closes that
weld for one real accepted forward-link turn:

* the exact `LinkRecord` in the accepted semantic content post is retained by
  a bounded content-page entry;
* the exact accepted `VersionEventRecord` is re-addressed by the production
  cSHAKE event scheme and retained by a bounded event-page entry;
* empty bounded pages advance through ordinary validated typed patches;
* the resulting canonical page bytes and Lean-computed cSHAKE roots are the
  two payloads of one authority-guarded `DurableDataIntent`.

No hash injectivity is asserted.  Root-to-state reasoning is exposed only
through the two existing pair-scoped collision premises.  The durable model
is still logical: physical storage and sync remain an explicit implementation
refinement boundary at the end of the file.
-/
import Assurance.HyperdocumentLinkPublicationWitness
import Compiler.HyperdocumentContentPageMaterializer
import Compiler.HyperdocumentEventPageMaterializer
import Kernel.DurableDataIntent
import Mathlib.Data.Nat.Pairing

namespace Minidregg.Assurance.HyperdocumentLinkPageDurableWeld

open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Theory
open Minidregg.Theory.CausalVersionDag
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option maxRecDepth 4096

noncomputable section

namespace Publication

abbrev record :=
  HyperdocumentOperations.linkRecord
    (HyperdocumentLinkPublicationWitness.linkDeclaration.operationId
      HyperdocumentLinkPublicationWitness.config)
    HyperdocumentLinkPublicationWitness.Genesis.author
    HyperdocumentLinkPublicationWitness.linkPayload

abbrev eventRecord :=
  HyperdocumentLinkPublicationWitness.linkAccepted.versionEventRecord

abbrev contentPost :=
  HyperdocumentLinkPublicationWitness.linkAccepted.accepted.prepared.post

abbrev eventPost :=
  HyperdocumentLinkPublicationWitness.eventAccepted.accepted.prepared.post

abbrev linkId := HyperdocumentLinkPublicationWitness.linkId
abbrev eventKey :=
  HyperdocumentLinkPublicationWitness.eventDeclaration.key
    HyperdocumentLinkPublicationWitness.eventConfig

end Publication

/-! ## Exact bounded content delta -/

def boundedForwardLink :
    HyperdocumentContentPageMaterializer.ForwardLink where
  sourceDocument :=
    HyperdocumentLinkPublicationWitness.linkPayload.sourceDocument
  source := HyperdocumentLinkPublicationWitness.linkPayload.source
  target := .external [0x68, 0x74, 0x74, 0x70, 0x73] [0x65, 0x78]
    [0x2f, 0x6c, 0x6f, 0x6f, 0x6d]
  relation := HyperdocumentLinkPublicationWitness.linkPayload.relation
  author := HyperdocumentLinkPublicationWitness.Genesis.author
  operation :=
    HyperdocumentLinkPublicationWitness.linkDeclaration.operationId
      HyperdocumentLinkPublicationWitness.config
  tombstonedAt := none

@[simp] theorem boundedForwardLink_toCanonical :
    boundedForwardLink.toCanonical = Publication.record := by
  rfl

def contentEntry : HyperdocumentContentPageMaterializer.Entry :=
  .link Publication.linkId boundedForwardLink

def contentPrePage : HyperdocumentContentPageMaterializer.Page where
  contentDomain := HyperdocumentLinkPublicationWitness.linkIntent.historyDomain
  document := HyperdocumentLinkPublicationWitness.Genesis.documentId
  pageNumber := 0
  slot0 := none
  slot1 := none
  slot2 := none
  slot3 := none

def contentPostPage : HyperdocumentContentPageMaterializer.Page where
  contentDomain := contentPrePage.contentDomain
  document := contentPrePage.document
  pageNumber := contentPrePage.pageNumber
  slot0 := some contentEntry
  slot1 := none
  slot2 := none
  slot3 := none

theorem contentPrePage_valid : contentPrePage.Valid := by
  simp [HyperdocumentContentPageMaterializer.Page.Valid,
    HyperdocumentContentPageMaterializer.Page.addresses,
    HyperdocumentContentPageMaterializer.Page.entries, contentPrePage]

theorem contentPostPage_valid : contentPostPage.Valid := by
  constructor
  · simp [HyperdocumentContentPageMaterializer.Page.addresses,
      HyperdocumentContentPageMaterializer.Page.entries, contentPostPage,
      contentEntry]
  · simp [HyperdocumentContentPageMaterializer.Page.entries, contentPostPage,
      contentEntry, HyperdocumentContentPageMaterializer.Entry.LocalTo,
      boundedForwardLink, contentPrePage,
      HyperdocumentLinkPublicationWitness.linkPayload]

@[simp] theorem accepted_content_post_exact :
    Hyperdocument.lookup Publication.contentPost.logical .links
        Publication.linkId =
      Hyperdocument.lookup contentPostPage.toCanonicalState .links
        Publication.linkId := by
  rw [HyperdocumentLinkPublicationWitness.link_post_contains_forward]
  simp [Hyperdocument.lookup,
    HyperdocumentContentPageMaterializer.Page.toCanonicalState,
    HyperdocumentContentPageMaterializer.Page.entries, contentPostPage,
    contentEntry, HyperdocumentContentPageMaterializer.Entry.install,
    Publication.record]
  rfl

def contentPreCell :
    Materialized HyperdocumentContentPageMaterializer.materializer :=
  CellState.materialize HyperdocumentContentPageMaterializer.materializer
    (HyperdocumentContentPageMaterializer.stateOfOption (some contentPrePage))

def contentPostCell :
    Materialized HyperdocumentContentPageMaterializer.materializer :=
  CellState.materialize HyperdocumentContentPageMaterializer.materializer
    (HyperdocumentContentPageMaterializer.stateOfOption (some contentPostPage))

def contentPatch : CellState.Patch
    HyperdocumentContentPageMaterializer.schema Digest where
  expectedPreRoot := contentPreCell.root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some contentPostPage }]
  resourceWrites := []

theorem contentPatch_accepted :
    ∃ validated : CellState.ValidatedPatch
        HyperdocumentContentPageMaterializer.materializer contentPreCell
        contentPatch,
      CellState.validate HyperdocumentContentPageMaterializer.materializer
        contentPreCell contentPatch =
          CellState.ValidationOutcome.accepted validated := by
  unfold CellState.validate
  rw [dif_pos (show contentPatch.expectedPreRoot = contentPreCell.root from rfl)]
  rw [dif_pos (show contentPatch.fieldFootprint = contentPatch.namedFields by
    decide)]
  rw [dif_pos (show contentPatch.resourceFootprint = contentPatch.namedResources by
    decide)]
  exact ⟨_, rfl⟩

theorem content_accepted_post_exact
    (validated : CellState.ValidatedPatch
      HyperdocumentContentPageMaterializer.materializer contentPreCell
      contentPatch) :
    validated.apply = contentPostCell := by
  apply CellState.Materialized.ext
  change
    { fields := CellState.applyFieldWrites contentPatch.fieldWrites
        contentPreCell.logical.fields
      resources := CellState.applyResourceWrites contentPatch.resourceWrites
        contentPreCell.logical.resources } =
      HyperdocumentContentPageMaterializer.stateOfOption
        (some contentPostPage)
  congr 1
  apply DFinsupp.ext
  intro field
  cases field
  simp [CellState.applyFieldWrites, contentPatch, contentPreCell,
    HyperdocumentContentPageMaterializer.stateOfOption,
    CellState.FieldStore.assign]

/-! ## Exact bounded event delta -/

def eventEntry : HyperdocumentEventPageMaterializer.Entry where
  key := deriveVersionEventId
    HyperdocumentEventPageMaterializer.eventPreimageCodec
    HyperdocumentEventPageMaterializer.eventDerivation Publication.eventRecord
  record := Publication.eventRecord

def eventPrePage : HyperdocumentEventPageMaterializer.Page where
  historyDomain := Publication.eventRecord.historyDomain
  document := Publication.eventRecord.document
  pageNumber := 0
  slot0 := none
  slot1 := none
  slot2 := none
  slot3 := none

def eventPostPage : HyperdocumentEventPageMaterializer.Page where
  historyDomain := eventPrePage.historyDomain
  document := eventPrePage.document
  pageNumber := eventPrePage.pageNumber
  slot0 := some eventEntry
  slot1 := none
  slot2 := none
  slot3 := none

theorem eventPrePage_valid : eventPrePage.Valid := by
  constructor
  · intro entry member
    simp [HyperdocumentEventPageMaterializer.Page.entries, eventPrePage] at member
  · simp [HyperdocumentEventPageMaterializer.Page.entries, eventPrePage]

theorem eventPostPage_valid : eventPostPage.Valid := by
  constructor
  · intro entry member
    have exactEntry : entry = eventEntry := by
      simpa [HyperdocumentEventPageMaterializer.Page.entries, eventPostPage,
        _root_.id] using member
    subst entry
    exact ⟨rfl, rfl, HyperdocumentLinkPublicationWitness.linkWellFormed,
      deriveVersionEventId_address_exact
        HyperdocumentEventPageMaterializer.eventPreimageCodec
        HyperdocumentEventPageMaterializer.eventDerivation
        Publication.eventRecord⟩
  · simp [HyperdocumentEventPageMaterializer.Page.entries, eventPostPage,
      eventEntry]

@[simp] theorem bounded_event_post_contains_exact_record :
    eventPostPage.toSparseStore .events eventEntry.key =
      some Publication.eventRecord := by
  simp [HyperdocumentEventPageMaterializer.Page.toSparseStore,
    HyperdocumentEventPageMaterializer.Page.entries, eventPostPage,
    HyperdocumentEventPageMaterializer.installEntry, eventEntry,
    _root_.id]
  rfl

@[simp] theorem accepted_event_post_contains_exact_record :
    Publication.eventPost.logical.fields
      ⟨HyperdocumentEventLog.Sparse.Namespace.events, Publication.eventKey⟩ =
        some Publication.eventRecord :=
  HyperdocumentLinkPublicationWitness.event_post_contains_link_event

/-- The semantic event-log post and bounded production page retain the same
accepted record.  The physical page deliberately uses its cSHAKE-derived key;
the old witness event store used a transparent test address. -/
theorem accepted_event_to_bounded_exact :
    Publication.eventPost.logical.fields
        ⟨HyperdocumentEventLog.Sparse.Namespace.events, Publication.eventKey⟩ =
      eventPostPage.toSparseStore .events eventEntry.key := by
  rw [accepted_event_post_contains_exact_record,
    bounded_event_post_contains_exact_record]

def eventPreCell :
    Materialized HyperdocumentEventPageMaterializer.materializer :=
  CellState.materialize HyperdocumentEventPageMaterializer.materializer
    (HyperdocumentEventPageMaterializer.stateOfOption (some eventPrePage))

def eventPostCell :
    Materialized HyperdocumentEventPageMaterializer.materializer :=
  CellState.materialize HyperdocumentEventPageMaterializer.materializer
    (HyperdocumentEventPageMaterializer.stateOfOption (some eventPostPage))

def eventPatch : CellState.Patch HyperdocumentEventPageMaterializer.schema
    Digest where
  expectedPreRoot := eventPreCell.root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some eventPostPage }]
  resourceWrites := []

theorem eventPatch_accepted :
    ∃ validated : CellState.ValidatedPatch
        HyperdocumentEventPageMaterializer.materializer eventPreCell eventPatch,
      CellState.validate HyperdocumentEventPageMaterializer.materializer
        eventPreCell eventPatch = CellState.ValidationOutcome.accepted validated := by
  unfold CellState.validate
  rw [dif_pos (show eventPatch.expectedPreRoot = eventPreCell.root from rfl)]
  rw [dif_pos (show eventPatch.fieldFootprint = eventPatch.namedFields by decide)]
  rw [dif_pos (show eventPatch.resourceFootprint = eventPatch.namedResources by
    decide)]
  exact ⟨_, rfl⟩

theorem event_accepted_post_exact
    (validated : CellState.ValidatedPatch
      HyperdocumentEventPageMaterializer.materializer eventPreCell eventPatch) :
    validated.apply = eventPostCell := by
  apply CellState.Materialized.ext
  change
    { fields := CellState.applyFieldWrites eventPatch.fieldWrites
        eventPreCell.logical.fields
      resources := CellState.applyResourceWrites eventPatch.resourceWrites
        eventPreCell.logical.resources } =
      HyperdocumentEventPageMaterializer.stateOfOption (some eventPostPage)
  congr 1
  apply DFinsupp.ext
  intro field
  cases field
  simp [CellState.applyFieldWrites, eventPatch, eventPreCell,
    HyperdocumentEventPageMaterializer.stateOfOption,
    CellState.FieldStore.assign]

/-! ## Exact page frames and Lean cSHAKE roots -/

def contentPreBytes : List UInt8 := contentPreCell.bytes
def contentPostBytes : List UInt8 := contentPostCell.bytes
def eventPreBytes : List UInt8 := eventPreCell.bytes
def eventPostBytes : List UInt8 := eventPostCell.bytes

@[simp] theorem contentPostBytes_exact :
    contentPostBytes =
      HyperdocumentContentPageMaterializer.wireFrame ++
        1 :: HyperdocumentContentPageMaterializer.pageStream.encode
          contentPostPage := rfl

@[simp] theorem eventPostBytes_exact :
    eventPostBytes =
      HyperdocumentEventPageMaterializer.wireFrame ++
        1 :: HyperdocumentEventPageMaterializer.pageStream.encode
          eventPostPage := rfl

@[simp] theorem contentPostRoot_exact :
    contentPostCell.root =
      (Sp800185Cshake256.hash
        HyperdocumentContentPageMaterializer.rootCustomization
        contentPostBytes).digest := rfl

@[simp] theorem eventPostRoot_exact :
    eventPostCell.root =
      (Sp800185Cshake256.hash
        HyperdocumentEventPageMaterializer.rootCustomization
        eventPostBytes).digest := rfl

/-! ## One authority-guarded durable page intent -/

/-- The two page codecs have disjoint outer wire frames.  The durable snapshot
uses the decoder result to select the same root function used by the page's
own materializer.  Non-page bytes are authority bytes and use their own
cSHAKE customization. -/
def authorityRootCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 72, 68, 79, 67, 46, 65, 85, 84, 72, 46, 82, 79, 79,
    84, 47, 118, 49]

def authorityRootBytes (bytes : List UInt8) : Digest :=
  ⟨Nat.pair
    (Sp800185Cshake256.hash authorityRootCustomization bytes).digest.value
    bytes.length⟩

def rootBytes (bytes : List UInt8) : Digest :=
  match HyperdocumentContentPageMaterializer.stateCodec.decode bytes with
  | some _ => HyperdocumentContentPageMaterializer.rootBytes bytes
  | none =>
      match HyperdocumentEventPageMaterializer.stateCodec.decode bytes with
      | some _ => HyperdocumentEventPageMaterializer.rootBytes bytes
      | none => authorityRootBytes bytes

@[simp] theorem rootBytes_content_encode
    (state : LogicalState HyperdocumentContentPageMaterializer.schema) :
    rootBytes (HyperdocumentContentPageMaterializer.stateCodec.encode state) =
      HyperdocumentContentPageMaterializer.rootBytes
        (HyperdocumentContentPageMaterializer.stateCodec.encode state) := by
  unfold rootBytes
  rw [HyperdocumentContentPageMaterializer.stateCodec.decode_encode]

@[simp] theorem content_decoder_rejects_event_encode
    (state : LogicalState HyperdocumentEventPageMaterializer.schema) :
    HyperdocumentContentPageMaterializer.stateCodec.decode
      (HyperdocumentEventPageMaterializer.stateCodec.encode state) = none := by
  simp [HyperdocumentContentPageMaterializer.stateCodec,
    HyperdocumentContentPageMaterializer.decodeState,
    HyperdocumentEventPageMaterializer.stateCodec,
    HyperdocumentEventPageMaterializer.wireFrame]

@[simp] theorem rootBytes_event_encode
    (state : LogicalState HyperdocumentEventPageMaterializer.schema) :
    rootBytes (HyperdocumentEventPageMaterializer.stateCodec.encode state) =
      HyperdocumentEventPageMaterializer.rootBytes
        (HyperdocumentEventPageMaterializer.stateCodec.encode state) := by
  simp [rootBytes]

@[simp] theorem contentPreRoot_bound :
    rootBytes contentPreBytes = contentPreCell.root := by
  simpa [contentPreBytes, contentPreCell] using
    (rootBytes_content_encode
      (HyperdocumentContentPageMaterializer.stateOfOption
        (some contentPrePage)))

@[simp] theorem contentPostRoot_bound :
    rootBytes contentPostBytes = contentPostCell.root := by
  simpa [contentPostBytes, contentPostCell] using
    (rootBytes_content_encode
      (HyperdocumentContentPageMaterializer.stateOfOption
        (some contentPostPage)))

@[simp] theorem eventPreRoot_bound :
    rootBytes eventPreBytes = eventPreCell.root := by
  simpa [eventPreBytes, eventPreCell] using
    (rootBytes_event_encode
      (HyperdocumentEventPageMaterializer.stateOfOption (some eventPrePage)))

@[simp] theorem eventPostRoot_bound :
    rootBytes eventPostBytes = eventPostCell.root := by
  simpa [eventPostBytes, eventPostCell] using
    (rootBytes_event_encode
      (HyperdocumentEventPageMaterializer.stateOfOption (some eventPostPage)))

def contentCellId : CellId := ⟨920⟩
def eventCellId : CellId := ⟨921⟩
def authorityCellId : CellId := ⟨922⟩

def authorityBytes : List UInt8 :=
  [76, 79, 79, 77, 47, 72, 68, 79, 67, 47, 65, 85, 84, 72, 1, 9]

def beforeBytes (cellId : CellId) : List UInt8 :=
  if cellId = contentCellId then contentPreBytes
  else if cellId = eventCellId then eventPreBytes
  else if cellId = authorityCellId then authorityBytes
  else []

def beforeModel :
    DurableCommitProtocol.Snapshot TransactionId CellId StableNullifier
      ReplayEnvelope where
  roots := fun cellId => rootBytes (beforeBytes cellId)
  consumed := fun _ => false
  available := fun _ => 0
  history := []
  journal := []

def before : DataSnapshot rootBytes where
  model := beforeModel
  canonicalBytes := beforeBytes
  coherent := fun _ => rfl

@[simp] theorem before_content_root :
    before.model.roots contentCellId = rootBytes contentPreBytes := by
  simp [before, beforeModel, beforeBytes, contentCellId, eventCellId,
    authorityCellId]

@[simp] theorem before_event_root :
    before.model.roots eventCellId = rootBytes eventPreBytes := by
  simp [before, beforeModel, beforeBytes, contentCellId, eventCellId,
    authorityCellId]

@[simp] theorem before_authority_root :
    before.model.roots authorityCellId = rootBytes authorityBytes := by
  simp [before, beforeModel, beforeBytes, contentCellId, eventCellId,
    authorityCellId]

def contentWrite : DataWrite where
  cellId := contentCellId
  expectedPre := rootBytes contentPreBytes
  exactPost := rootBytes contentPostBytes
  canonicalPostBytes := contentPostBytes

def eventWrite : DataWrite where
  cellId := eventCellId
  expectedPre := rootBytes eventPreBytes
  exactPost := rootBytes eventPostBytes
  canonicalPostBytes := eventPostBytes

def authorityGuard : ReadGuard where
  cellId := authorityCellId
  expectedRoot := rootBytes authorityBytes

def nullifier : StableNullifier where
  codecVersion := 1
  domain := HyperdocumentLinkPublicationWitness.linkIntent.historyDomain
  nullifierId :=
    (HyperdocumentLinkPublicationWitness.linkDeclaration.operationId
      HyperdocumentLinkPublicationWitness.config).digest
  canonicalBytes :=
    HyperdocumentEventPageMaterializer.eventPreimageCodec.encode
      HyperdocumentLinkPublicationWitness.linkAccepted.causalPreimage

def durableEvent : StableEvent where
  codecVersion := 1
  domain := HyperdocumentLinkPublicationWitness.linkIntent.historyDomain
  eventId := eventEntry.key.digest
  canonicalBytes :=
    HyperdocumentEventPageMaterializer.versionEventRecordCodec.encode
      Publication.eventRecord

def intent : DataIntent rootBytes where
  transactionId := ⟨923⟩
  writes := [contentWrite, eventWrite]
  readGuards := [authorityGuard]
  nullifiers := [nullifier]
  exactCharge := fun _ => 0
  event := durableEvent
  postRootsBound := by
    intro write member
    simp only [List.mem_cons] at member
    rcases member with exactContent | rest
    · subst write
      change rootBytes contentPostBytes = rootBytes contentPostBytes
      rfl
    · have exactEvent : write = eventWrite := by simpa using rest
      subst write
      change rootBytes eventPostBytes = rootBytes eventPostBytes
      rfl
  guardsReadOnly := by
    intro guard member
    have guardExact : guard = authorityGuard := by simpa using member
    subst guard
    simp [authorityGuard, contentWrite, eventWrite, authorityCellId,
      contentCellId, eventCellId]

@[simp] theorem intent_writes_exact :
    intent.writes = [contentWrite, eventWrite] := rfl

@[simp] theorem ready : intent.preflight before = .ok () := by
  have guardsReady : intent.readGuardsMatchCheck before = true := by
    rw [DataIntent.readGuardsMatchCheck_eq_true_iff]
    intro guard member
    have guardExact : guard = authorityGuard := by simpa [intent] using member
    subst guard
    exact before_authority_root
  have durableReady : intent.erase.preflight before.model = .ok () := by
    have rootsReady :
        intent.erase.rootsMatchCheck before.model = true := by
      simp [DurableCommitProtocol.Intent.rootsMatchCheck, intent,
        DataIntent.erase, contentWrite, eventWrite]
    have nullifiersFresh :
        intent.erase.nullifiersFreshCheck before.model = true := by
      rw [DurableCommitProtocol.Intent.nullifiersFreshCheck_eq_true_iff]
      intro nullifier member
      rfl
    have funded : intent.erase.exactCharge.fundedCheck
        before.model.available = true := by
      rw [ResourceCost.Charge.fundedCheck_eq_true_iff]
      intro lane
      exact Nat.zero_le _
    unfold DurableCommitProtocol.Intent.preflight
    simp [rootsReady, nullifiersFresh, funded]
    simp [contentWrite, eventWrite, contentCellId, eventCellId, intent]
  simp [DataIntent.preflight, guardsReady, durableReady]

@[simp] theorem positive_install :
    DurableDataIntent.execute .complete before intent =
      .accepted (DataSnapshot.install before intent) := by
  apply DurableDataIntent.execute_complete_ready
  · simp [before, beforeModel, Snapshot.lookupRecorded]
  · exact ready

@[simp] theorem installed_content_bytes :
    (DataSnapshot.install before intent).canonicalBytes contentCellId =
      contentPostBytes := by
  simp [DataSnapshot.install, DataSnapshot.lookupPostBytes, intent,
    contentWrite, eventWrite, contentCellId, eventCellId]

@[simp] theorem installed_event_bytes :
    (DataSnapshot.install before intent).canonicalBytes eventCellId =
      eventPostBytes := by
  simp [DataSnapshot.install, DataSnapshot.lookupPostBytes, intent,
    contentWrite, eventWrite, contentCellId, eventCellId]

@[simp] theorem installed_content_root :
    (DataSnapshot.install before intent).model.roots contentCellId =
      contentPostCell.root := by
  simp [DataSnapshot.install, Snapshot.install, Snapshot.lookupPost, intent,
    contentWrite, eventWrite, contentCellId, eventCellId]
  simpa [contentPostBytes] using contentPostRoot_bound

@[simp] theorem installed_event_root :
    (DataSnapshot.install before intent).model.roots eventCellId =
      eventPostCell.root := by
  simp [DataSnapshot.install, Snapshot.install, Snapshot.lookupPost, intent,
    contentWrite, eventWrite, contentCellId, eventCellId]
  simpa [eventPostBytes] using eventPostRoot_bound

/-! ## Executable stale/mismatch teeth -/

def staleAuthorityBytes : List UInt8 := authorityBytes ++ [10]

def staleBeforeBytes (cellId : CellId) : List UInt8 :=
  if cellId = authorityCellId then staleAuthorityBytes else beforeBytes cellId

def staleBeforeModel :
    DurableCommitProtocol.Snapshot TransactionId CellId StableNullifier
      ReplayEnvelope :=
  { beforeModel with
    roots := fun cellId => rootBytes (staleBeforeBytes cellId) }

def staleBefore : DataSnapshot rootBytes where
  model := staleBeforeModel
  canonicalBytes := staleBeforeBytes
  coherent := fun _ => rfl

@[simp] theorem rootBytes_authority_exact :
    rootBytes authorityBytes = authorityRootBytes authorityBytes := by
  rfl

@[simp] theorem rootBytes_staleAuthority_exact :
    rootBytes staleAuthorityBytes = authorityRootBytes staleAuthorityBytes := by
  rfl

@[simp] theorem staleBefore_authority_root :
    staleBefore.model.roots authorityCellId =
      rootBytes staleAuthorityBytes := by
  simp [staleBefore, staleBeforeModel, staleBeforeBytes, authorityCellId]

theorem concrete_authority_roots_differ :
    rootBytes staleAuthorityBytes ≠ rootBytes authorityBytes := by
  intro equal
  rw [rootBytes_staleAuthority_exact, rootBytes_authority_exact] at equal
  have paired := congrArg Digest.value equal
  simp only [authorityRootBytes] at paired
  rw [Nat.pair_eq_pair] at paired
  have lengthsEqual := paired.2
  norm_num [staleAuthorityBytes, authorityBytes] at lengthsEqual

@[simp] theorem stale_authority_rejected :
    intent.preflight staleBefore = .error .staleReadGuard := by
  apply DurableDataIntent.stale_read_guard_rejected
  refine ⟨authorityGuard, by simp [intent], ?_⟩
  change staleBefore.model.roots authorityCellId != rootBytes authorityBytes
  rw [staleBefore_authority_root]
  simpa using concrete_authority_roots_differ

structure ContentPairSecurityCeiling : Prop where
  binding : HyperdocumentContentPageMaterializer.PairBindingPremise
    contentPreCell.logical contentPostCell.logical
  rootsDifferent : contentPreCell.root ≠ contentPostCell.root

structure EventPairSecurityCeiling : Prop where
  binding : HyperdocumentEventPageMaterializer.PairBindingPremise
    eventPreCell.logical eventPostCell.logical
  rootsDifferent : eventPreCell.root ≠ eventPostCell.root

def mismatchedContentWrite : DataWrite :=
  { contentWrite with expectedPre := rootBytes contentPostBytes }

def mismatchedIntent : DataIntent rootBytes where
  transactionId := ⟨924⟩
  writes := [mismatchedContentWrite, eventWrite]
  readGuards := [authorityGuard]
  nullifiers := [nullifier]
  exactCharge := fun _ => 0
  event := durableEvent
  postRootsBound := by
    intro write member
    simp only [List.mem_cons] at member
    rcases member with exactContent | rest
    · subst write
      rfl
    · have exactEvent : write = eventWrite := by simpa using rest
      subst write
      rfl
  guardsReadOnly := by
    intro guard member
    have guardExact : guard = authorityGuard := by simpa using member
    subst guard
    simp [authorityGuard, mismatchedContentWrite, contentWrite, eventWrite,
      authorityCellId, contentCellId, eventCellId]

@[simp] theorem mismatched_content_pre_root_rejected
    (security : ContentPairSecurityCeiling) :
    mismatchedIntent.preflight before =
      .error (.durable .stalePreRoot) := by
  have pageRootsDifferent :
      rootBytes contentPreBytes ≠ rootBytes contentPostBytes := by
    intro rootsEqual
    apply security.rootsDifferent
    rw [← contentPreRoot_bound, ← contentPostRoot_bound]
    exact rootsEqual
  have expectedMismatch :
      contentPreCell.root ≠ rootBytes contentPostBytes := by
    intro rootsEqual
    apply pageRootsDifferent
    rw [contentPreRoot_bound]
    exact rootsEqual
  have guardsReady :
      mismatchedIntent.readGuardsMatchCheck before = true := by
    rw [DataIntent.readGuardsMatchCheck_eq_true_iff]
    intro guard member
    have guardExact : guard = authorityGuard := by
      simpa [mismatchedIntent] using member
    subst guard
    exact before_authority_root
  have rootsFailed :
      mismatchedIntent.erase.rootsMatchCheck before.model = false := by
    simp [DurableCommitProtocol.Intent.rootsMatchCheck, mismatchedIntent,
      DataIntent.erase, mismatchedContentWrite, contentWrite, eventWrite]
    simpa [contentPostBytes] using expectedMismatch
  have durableRejected :
      mismatchedIntent.erase.preflight before.model =
        .error .stalePreRoot := by
    unfold DurableCommitProtocol.Intent.preflight
    simp [rootsFailed]
    simp [mismatchedIntent, mismatchedContentWrite, contentWrite, eventWrite,
      contentCellId, eventCellId]
  simp [DataIntent.preflight, guardsReady, durableRejected]

/-- The event pair has the same deliberately local security boundary.  It is
recorded even though stale-content rejection above needs only the content
pair.  A reduction may discharge these two premises independently. -/
structure PairSecurityCeiling : Prop where
  content : ContentPairSecurityCeiling
  event : EventPairSecurityCeiling

/-- Logical installation is not a physical durability proof.  A production
deployment must supply its storage/sync refinement; none is manufactured
here. -/
structure PhysicalCeiling : Type 1 where
  PhysicalState : Type
  PhysicalStep : PhysicalState -> DataIntent rootBytes -> PhysicalState -> Type
  Represents : PhysicalState -> DataSnapshot rootBytes -> Prop
  refinement : DurableDataIntent.ImplementationRefinement rootBytes
    PhysicalState PhysicalStep Represents

/-! ## Axiom pins -/

/-- info: 'Minidregg.Assurance.HyperdocumentLinkPageDurableWeld.accepted_content_post_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_content_post_exact
/-- info: 'Minidregg.Assurance.HyperdocumentLinkPageDurableWeld.eventPostRoot_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eventPostRoot_exact
/-- info: 'Minidregg.Assurance.HyperdocumentLinkPageDurableWeld.positive_install' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms positive_install
/-- info: 'Minidregg.Assurance.HyperdocumentLinkPageDurableWeld.stale_authority_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_authority_rejected

end

end Minidregg.Assurance.HyperdocumentLinkPageDurableWeld
