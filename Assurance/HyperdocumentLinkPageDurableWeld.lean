/-
# Assurance.HyperdocumentLinkPageDurableWeld -- accepted link to deployed cell bytes

The logical link-publication witness and the deployed store-cell codecs meet
here for one real accepted forward-link turn:

* the exact `LinkRecord` in the accepted semantic content post is the record
  the deployed content cell (`HyperdocumentCell.contentMaterializer`) holds;
* the exact accepted `VersionEventRecord` is re-addressed by the deployed
  cSHAKE event scheme (`HyperdocumentCell.eventScheme`) and held by the
  deployed event-log cell;
* the empty cells advance through ordinary validated guarded patches;
* the resulting canonical `StoreCodec` bytes and Lean-computed cSHAKE roots are
  the two payloads of one authority-guarded `DurableDataIntent`.

No hash injectivity is asserted.  Root-to-state reasoning is exposed only
through the two pair-scoped collision premises.  The durable model is still
logical: physical storage and sync remain an explicit implementation
refinement boundary at the end of the file.  (Formerly this welded to the
four-slot content and event pages, which are deleted.)
-/
import Assurance.HyperdocumentLinkPublicationWitness
import Compiler.HyperdocumentCell
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

/-! ## Exact content delta on the deployed content cell -/

abbrev ContentStore := Store.Store Hyperdocument.layout
abbrev EventStore := HyperdocumentEventLog.Sparse.Store

def linkAddress : Hyperdocument.Address := ⟨.links, Publication.linkId⟩

def contentPreStore : ContentStore := 0

def contentPostStore : ContentStore :=
  contentPreStore.set linkAddress (some Publication.record)

@[simp] theorem accepted_content_post_exact :
    Hyperdocument.lookup Publication.contentPost.logical .links
        Publication.linkId =
      Hyperdocument.lookup contentPostStore .links Publication.linkId := by
  rw [HyperdocumentLinkPublicationWitness.link_post_contains_forward]
  simp only [Hyperdocument.lookup, contentPostStore, linkAddress, Store.Store.set_eq]
  rfl

def contentPreCell : Materialized HyperdocumentCell.contentMaterializer :=
  CellState.materialize HyperdocumentCell.contentMaterializer contentPreStore

def contentPostCell : Materialized HyperdocumentCell.contentMaterializer :=
  CellState.materialize HyperdocumentCell.contentMaterializer contentPostStore

def contentPatch : Store.Patch Hyperdocument.layout :=
  [.allocate .links Publication.linkId Publication.record]

theorem contentPatch_accepted :
    ∃ validated : CellState.ValidatedPatch
        HyperdocumentCell.contentMaterializer contentPreCell contentPreCell.root
        contentPatch,
      CellState.validate HyperdocumentCell.contentMaterializer
        contentPreCell contentPreCell.root contentPatch =
          CellState.ValidationOutcome.accepted validated :=
  CellState.validate_accepts _ _ _ _ rfl ⟨⟨by decide, rfl⟩, trivial⟩

theorem content_accepted_post_exact
    (validated : CellState.ValidatedPatch
      HyperdocumentCell.contentMaterializer contentPreCell contentPreCell.root
      contentPatch) :
    validated.apply = contentPostCell := by
  apply CellState.Materialized.ext
  rfl

/-! ## Exact event delta on the deployed event-log cell -/

/-- The deployed cSHAKE key of the accepted event. -/
def eventKey : VersionEventId :=
  deriveVersionEventId HyperdocumentCell.eventPreimageStream.toLawful
    HyperdocumentCell.eventDerivation Publication.eventRecord

/-- The deployed key is the event scheme's address of the event's causal
preimage: exactly what the registry's event-history law checks. -/
theorem eventKey_addressed :
    eventKey.digest =
      HyperdocumentCell.eventScheme.address Publication.eventRecord.toCausalPreimage :=
  deriveVersionEventId_address_exact _ _ _

def eventPreStore : EventStore := 0

def eventPostStore : EventStore :=
  eventPreStore.set (HyperdocumentEventLog.Sparse.eventAddress eventKey)
    (some Publication.eventRecord)

@[simp] theorem deployed_event_post_contains_exact_record :
    eventPostStore (HyperdocumentEventLog.Sparse.eventAddress eventKey) =
      some Publication.eventRecord :=
  Store.Store.set_eq _ _ _

@[simp] theorem accepted_event_post_contains_exact_record :
    Publication.eventPost.logical
        (HyperdocumentEventLog.Sparse.eventAddress Publication.eventKey) =
      some Publication.eventRecord :=
  HyperdocumentLinkPublicationWitness.event_post_contains_link_event

/-- The semantic event-log post and the deployed log cell retain the same
accepted record.  The deployed cell uses its cSHAKE-derived key; the witness
event store uses a transparent test address. -/
theorem accepted_event_to_deployed_exact :
    Publication.eventPost.logical
        (HyperdocumentEventLog.Sparse.eventAddress Publication.eventKey) =
      eventPostStore (HyperdocumentEventLog.Sparse.eventAddress eventKey) := by
  rw [accepted_event_post_contains_exact_record,
    deployed_event_post_contains_exact_record]

def eventPreCell : Materialized HyperdocumentCell.eventMaterializer :=
  CellState.materialize HyperdocumentCell.eventMaterializer eventPreStore

def eventPostCell : Materialized HyperdocumentCell.eventMaterializer :=
  CellState.materialize HyperdocumentCell.eventMaterializer eventPostStore

def eventPatch : HyperdocumentEventLog.Sparse.Patch :=
  [.allocate .events eventKey Publication.eventRecord]

theorem eventPatch_accepted :
    ∃ validated : CellState.ValidatedPatch
        HyperdocumentCell.eventMaterializer eventPreCell eventPreCell.root eventPatch,
      CellState.validate HyperdocumentCell.eventMaterializer
        eventPreCell eventPreCell.root eventPatch =
          CellState.ValidationOutcome.accepted validated :=
  CellState.validate_accepts _ _ _ _ rfl ⟨⟨by decide, rfl⟩, trivial⟩

theorem event_accepted_post_exact
    (validated : CellState.ValidatedPatch
      HyperdocumentCell.eventMaterializer eventPreCell eventPreCell.root eventPatch) :
    validated.apply = eventPostCell := by
  apply CellState.Materialized.ext
  rfl

/-! ## Exact store frames and Lean cSHAKE roots -/

def contentPreBytes : List UInt8 := contentPreCell.bytes
def contentPostBytes : List UInt8 := contentPostCell.bytes
def eventPreBytes : List UInt8 := eventPreCell.bytes
def eventPostBytes : List UInt8 := eventPostCell.bytes

theorem contentPostBytes_exact :
    contentPostBytes = StoreCodec.encode HyperdocumentCell.contentWire contentPostStore :=
  rfl

theorem eventPostBytes_exact :
    eventPostBytes = StoreCodec.encode HyperdocumentCell.eventWire eventPostStore :=
  rfl

theorem contentPostRoot_exact :
    contentPostCell.root =
      (Sp800185Cshake256.hash StoreCodec.rootCustomization contentPostBytes).digest :=
  rfl

theorem eventPostRoot_exact :
    eventPostCell.root =
      (Sp800185Cshake256.hash StoreCodec.rootCustomization eventPostBytes).digest :=
  rfl

/-! ## One authority-guarded durable intent -/

/-- Store-cell bytes (either deployed wire) use the store root; other bytes
are authority bytes and use their own cSHAKE customization, paired with their
length so the stale-authority tooth below needs no collision premise. -/
def authorityRootCustomization : List UInt8 :=
  [76, 79, 79, 77, 46, 72, 68, 79, 67, 46, 65, 85, 84, 72, 46, 82, 79, 79,
    84, 47, 118, 49]

def authorityRootBytes (bytes : List UInt8) : Digest :=
  ⟨Nat.pair
    (Sp800185Cshake256.hash authorityRootCustomization bytes).digest.value
    bytes.length⟩

def rootBytes (bytes : List UInt8) : Digest :=
  if (HyperdocumentCell.contentMaterializer.codec.decode bytes).isSome ∨
      (HyperdocumentCell.eventMaterializer.codec.decode bytes).isSome then
    StoreCodec.rootBytes bytes
  else authorityRootBytes bytes

@[simp] theorem rootBytes_content_encode (store : ContentStore) :
    rootBytes (HyperdocumentCell.contentMaterializer.codec.encode store) =
      StoreCodec.rootBytes (HyperdocumentCell.contentMaterializer.codec.encode store) := by
  unfold rootBytes
  rw [if_pos (Or.inl (by rw [HyperdocumentCell.contentMaterializer.codec.decode_encode]; rfl))]

@[simp] theorem rootBytes_event_encode (store : EventStore) :
    rootBytes (HyperdocumentCell.eventMaterializer.codec.encode store) =
      StoreCodec.rootBytes (HyperdocumentCell.eventMaterializer.codec.encode store) := by
  unfold rootBytes
  rw [if_pos (Or.inr (by rw [HyperdocumentCell.eventMaterializer.codec.decode_encode]; rfl))]

@[simp] theorem contentPreRoot_bound :
    rootBytes contentPreBytes = contentPreCell.root :=
  rootBytes_content_encode contentPreStore

@[simp] theorem contentPostRoot_bound :
    rootBytes contentPostBytes = contentPostCell.root :=
  rootBytes_content_encode contentPostStore

@[simp] theorem eventPreRoot_bound :
    rootBytes eventPreBytes = eventPreCell.root :=
  rootBytes_event_encode eventPreStore

@[simp] theorem eventPostRoot_bound :
    rootBytes eventPostBytes = eventPostCell.root :=
  rootBytes_event_encode eventPostStore

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
    HyperdocumentCell.eventPreimageStream.encode
      HyperdocumentLinkPublicationWitness.linkAccepted.causalPreimage

def durableEvent : StableEvent where
  codecVersion := 1
  domain := HyperdocumentLinkPublicationWitness.linkIntent.historyDomain
  eventId := eventKey.digest
  canonicalBytes :=
    HyperdocumentCell.versionEventRecordStream.encode Publication.eventRecord

def intent : DataIntent rootBytes where
  transactionId := ⟨923⟩
  writes := [contentWrite, eventWrite]
  readGuards := [authorityGuard]
  nullifiers := [nullifier]
  exactCharge := fun _ => 0
  event := durableEvent
  subject := none
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
  simp only [DataSnapshot.install, Snapshot.install, intent,
    contentWrite, eventWrite, contentCellId, eventCellId]
  simp [Snapshot.lookupPost]

@[simp] theorem installed_event_root :
    (DataSnapshot.install before intent).model.roots eventCellId =
      eventPostCell.root := by
  simp only [DataSnapshot.install, Snapshot.install, intent,
    contentWrite, eventWrite, contentCellId, eventCellId]
  simp [Snapshot.lookupPost]

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

/-- Bytes whose first byte is not the store magic's are authority bytes. -/
theorem rootBytes_of_first_byte (first : UInt8) (rest : List UInt8) (other : first ≠ 68) :
    rootBytes (first :: rest) = authorityRootBytes (first :: rest) := by
  unfold rootBytes
  rw [if_neg]
  rintro (content | event)
  · rw [show HyperdocumentCell.contentMaterializer.codec.decode (first :: rest) = none from
      StoreCodec.decode_other_first_byte HyperdocumentCell.contentWire first rest other] at content
    cases content
  · rw [show HyperdocumentCell.eventMaterializer.codec.decode (first :: rest) = none from
      StoreCodec.decode_other_first_byte HyperdocumentCell.eventWire first rest other] at event
    cases event

@[simp] theorem rootBytes_authority_exact :
    rootBytes authorityBytes = authorityRootBytes authorityBytes :=
  rootBytes_of_first_byte 76 _ (by decide)

@[simp] theorem rootBytes_staleAuthority_exact :
    rootBytes staleAuthorityBytes = authorityRootBytes staleAuthorityBytes :=
  rootBytes_of_first_byte 76 _ (by decide)

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
  binding : CellState.PairBindingPremise HyperdocumentCell.contentMaterializer
    contentPreCell.logical contentPostCell.logical
  rootsDifferent : contentPreCell.root ≠ contentPostCell.root

structure EventPairSecurityCeiling : Prop where
  binding : CellState.PairBindingPremise HyperdocumentCell.eventMaterializer
    eventPreCell.logical eventPostCell.logical
  rootsDifferent : eventPreCell.root ≠ eventPostCell.root

/-- The binding premise suffices for the root inequality: the two content
stores differ at the link address. -/
theorem ContentPairSecurityCeiling.ofBinding
    (binding : CellState.PairBindingPremise HyperdocumentCell.contentMaterializer
      contentPreCell.logical contentPostCell.logical) :
    ContentPairSecurityCeiling where
  binding := binding
  rootsDifferent := by
    intro equal
    have stores := binding.logical_eq equal
    have atLink := congrArg (fun store : ContentStore => store linkAddress) stores
    simp only [contentPreCell, contentPostCell, CellState.materialize_logical,
      contentPostStore, contentPreStore, Store.Store.set_eq, Store.Store.zero_apply] at atLink
    cases atLink

def mismatchedContentWrite : DataWrite :=
  { contentWrite with expectedPre := rootBytes contentPostBytes }

def mismatchedIntent : DataIntent rootBytes where
  transactionId := ⟨924⟩
  writes := [mismatchedContentWrite, eventWrite]
  readGuards := [authorityGuard]
  nullifiers := [nullifier]
  exactCharge := fun _ => 0
  event := durableEvent
  subject := none
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
    simpa using expectedMismatch
  have durableRejected :
      mismatchedIntent.erase.preflight before.model =
        .error .stalePreRoot := by
    unfold DurableCommitProtocol.Intent.preflight
    simp [rootsFailed]
    simp [mismatchedIntent, mismatchedContentWrite, contentWrite, eventWrite,
      contentCellId, eventCellId]
  unfold DataIntent.preflight
  rw [guardsReady]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [if_neg (by simp [mismatchedIntent]), durableRejected]

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
