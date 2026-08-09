/-
# Assurance.HyperdocumentHistoryAdmission -- exact-head hyperdocument evidence

This module closes the gap between authenticated Hyperdocument content effects
and generic semantic-history observations.  It deliberately does not weaken a
history entry to a root or context:

* every observation and forward-link event carries a `Fin` index proving that
  its exact `VerifiedEntry` occurs in one exact `VerifiedHistoryHead`;
* finality is an external proposition indexed by that same head, entry,
  membership proof, and the entry's derived receipt root;
* quoted cells use an explicit finite Hyperdocument layout and only canonical
  semantic-receipt `.post` coordinates.  Header, `.pre`, and `.touched` cells
  therefore cannot be presented as quoted content;
* a forward-link event retains an accepted first-order Hyperdocument effect,
  and Lean proves that its canonical post cell contains the concrete
  `LinkRecord` used by the event.

PCS opening soundness, commitment binding/collision resistance, and the
Fiat--Shamir random-oracle model remain separate proof fields.  None is
replaced by a vacuous premise.  The canonical post-cell theorem is a logical acceptance
fact; this module makes no physical persistence or availability claim.
-/

import Assurance.TransclusionBacklinkHistory
import Theory.HyperdocumentOperations

namespace Minidregg.Assurance.HyperdocumentHistoryAdmission

open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.AcceptedCellEffectHistory
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.TransclusionBacklinkHistory
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome
  uOp uAtom

noncomputable section

section HistoryIndices

variable {n : Nat} {F : Type*} [Field F] [DecidableEq F]
variable {Op : Type uOp}
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext -> BindingIx -> F}
    {C : Submodule F (BoundReceiptIx n -> F)}
    {SCommit : BindingCommitment Digest F (BoundReceiptIx n) Op}

local notation "HistoryEntry" =>
  VerifiedEntry (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C)

local notation "HistoryHead" =>
  VerifiedHistoryHead (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) C SCommit

/-- Proof-relevant occurrence of one exact entry at one exact position in one
verified head.  This is stronger than matching a receipt root or context. -/
structure EntryAt (head : HistoryHead) (entry : HistoryEntry) where
  index : Fin head.entries.length
  entryExact : head.entries.get index = entry

namespace EntryAt

theorem mem {head : HistoryHead} {entry : HistoryEntry}
    (position : EntryAt head entry) : entry ∈ head.entries := by
  rw [← position.entryExact]
  exact List.get_mem head.entries position.index

/-- Looking up the receipt root at the retained index yields the exact entry
root used by finality and source identity. -/
theorem receiptRootAt_exact {head : HistoryHead} {entry : HistoryEntry}
    (position : EntryAt head entry) :
    (head.entries.get position.index).receiptRoot SCommit =
      entry.receiptRoot SCommit := by
  rw [position.entryExact]

end EntryAt

end HistoryIndices

/-! ## Canonical Hyperdocument post-state layouts -/

/-- One typed Hyperdocument cell value.  The namespace determines both the key
and value type; no untyped extension map is introduced. -/
structure PostCell where
  space : Namespace
  key : Key space
  value : Option (Value space)

namespace PostCell

def address (cell : PostCell) : Address :=
  ⟨cell.space, cell.key⟩

end PostCell

/-- A contiguous interval of the finite semantic post-state word. -/
structure PostSpan (n : Nat) where
  start : Nat
  width : Nat
  withinBounds : start + width ≤ n

namespace PostSpan

def coordinate {n : Nat} (span : PostSpan n) (offset : Fin span.width) :
    Fin n :=
  ⟨span.start + offset.val, by
    have offsetLt : offset.val < span.width := offset.isLt
    have within : span.start + span.width ≤ n := span.withinBounds
    omega⟩

/-- Literal increasing coordinates of the contiguous interval. -/
def coordinates {n : Nat} (span : PostSpan n) : List (Fin n) :=
  (List.finRange span.width).map span.coordinate

@[simp] theorem coordinates_length {n : Nat} (span : PostSpan n) :
    span.coordinates.length = span.width := by
  simp [coordinates]

end PostSpan

/-- A finite, representation-binding layout of supported Hyperdocument cells.
Each supported cell has a contiguous multi-field encoding.  Both the typed cell
table and the field-vector encoding are injective on this finite support, and
distinct cells occupy disjoint spans.  A deployment unable to prove these
finite facts must instead expose a separately priced collision premise; it may
not call an arbitrary `PostCell -> F` function canonical. -/
structure CanonicalPostLayout (n : Nat) (F : Type*) where
  cellCount : Nat
  cellAt : Fin cellCount -> PostCell
  cellAtInjective : Function.Injective cellAt
  spanAt : Fin cellCount -> PostSpan n
  encodeAt : Fin cellCount -> List F
  encodedLength : ∀ slot,
    (encodeAt slot).length = (spanAt slot).width
  spanNonempty : ∀ slot, 0 < (spanAt slot).width
  encodeAtInjective : Function.Injective encodeAt
  spansDisjoint : ∀ {left right}, left ≠ right ->
    Disjoint (spanAt left).coordinates.toFinset
      (spanAt right).coordinates.toFinset

namespace CanonicalPostLayout

variable {n : Nat} {F : Type*}

def boundCoordinates (layout : CanonicalPostLayout n F)
    (slot : Fin layout.cellCount) : List (BoundReceiptIx n) :=
  (layout.spanAt slot).coordinates.map
    (fun coordinate => .inr (coordinate, .post))

@[simp] theorem boundCoordinates_length (layout : CanonicalPostLayout n F)
    (slot : Fin layout.cellCount) :
    (layout.boundCoordinates slot).length =
      (layout.encodeAt slot).length := by
  simp [boundCoordinates, layout.encodedLength]

end CanonicalPostLayout

section CanonicalOpening

variable {n : Nat} {F : Type*} [Field F] [DecidableEq F]
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext -> BindingIx -> F}
    {C : Submodule F (BoundReceiptIx n -> F)}

local notation "HistoryEntry" =>
  VerifiedEntry (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C)

/-- A generic range/value opening specialized to represented Hyperdocument post
cells.  The exact opening and `representedPostExact` connect every supported
multi-field encoding to the exact semantic post witness; selectors and field
vectors cannot be swapped independently. -/
structure CanonicalPostOpening
    (layout : CanonicalPostLayout n F)
    (entry : HistoryEntry)
    (opening : RangeOrValueOpening n F) where
  sourceSlots : List (Fin layout.cellCount)
  coordinatesExact : opening.coordinates =
    sourceSlots.flatMap layout.boundCoordinates
  coordinatesPostOnly : ∀ coordinate ∈ opening.coordinates,
    ∃ slot ∈ sourceSlots, ∃ postCoordinate,
      postCoordinate ∈ (layout.spanAt slot).coordinates /\
      coordinate = .inr (postCoordinate, .post)
  cellsExact : opening.cells =
    sourceSlots.flatMap layout.encodeAt
  openingExact : opening.Exact entry.word
  representedPostExact : ∀ slot ∈ sourceSlots,
    (layout.spanAt slot).coordinates.map
        entry.claim.witness.core.post = layout.encodeAt slot
  valueShape : opening.shape = .value ->
    ∃ slot, sourceSlots = [slot]
  rangeShape : opening.shape = .range ->
    sourceSlots ≠ [] /\
      (sourceSlots.flatMap layout.boundCoordinates).Nodup

namespace CanonicalPostOpening

variable {layout : CanonicalPostLayout n F}
variable {entry : HistoryEntry} {opening : RangeOrValueOpening n F}

/-- A canonical post opening is an exact opening of the retained entry word. -/
theorem exact (canonical : CanonicalPostOpening layout entry opening) :
    opening.Exact entry.word :=
  canonical.openingExact

/-- Every quoted coordinate is a semantic `.post` slot selected by the exact
layout.  This is the positive theorem from which all anti-masquerade facts
follow. -/
theorem coordinates_post_only
    (canonical : CanonicalPostOpening layout entry opening)
    {coordinate : BoundReceiptIx n}
    (member : coordinate ∈ opening.coordinates) :
    ∃ slot ∈ canonical.sourceSlots, ∃ postCoordinate,
      postCoordinate ∈ (layout.spanAt slot).coordinates /\
      coordinate = .inr (postCoordinate, .post) :=
  canonical.coordinatesPostOnly coordinate member

theorem no_header_coordinate
    (canonical : CanonicalPostOpening layout entry opening)
    {coordinate : BoundReceiptIx n}
    (member : coordinate ∈ opening.coordinates) (header : BindingIx) :
    coordinate ≠ .inl header := by
  have postOnly : ∃ slot ∈ canonical.sourceSlots, ∃ postCoordinate,
      postCoordinate ∈ (layout.spanAt slot).coordinates /\
      coordinate = .inr (postCoordinate, .post) :=
    canonical.coordinatesPostOnly coordinate member
  obtain ⟨_, _, postCoordinate, _, coordinateExact⟩ := postOnly
  rw [coordinateExact]
  simp

theorem no_pre_coordinate
    (canonical : CanonicalPostOpening layout entry opening)
    {coordinate : BoundReceiptIx n}
    (member : coordinate ∈ opening.coordinates) (key : Fin n) :
    coordinate ≠ .inr (key, .pre) := by
  have postOnly : ∃ slot ∈ canonical.sourceSlots, ∃ postCoordinate,
      postCoordinate ∈ (layout.spanAt slot).coordinates /\
      coordinate = .inr (postCoordinate, .post) :=
    canonical.coordinatesPostOnly coordinate member
  obtain ⟨_, _, postCoordinate, _, coordinateExact⟩ := postOnly
  rw [coordinateExact]
  simp

theorem no_touched_coordinate
    (canonical : CanonicalPostOpening layout entry opening)
    {coordinate : BoundReceiptIx n}
    (member : coordinate ∈ opening.coordinates) (key : Fin n) :
    coordinate ≠ .inr (key, .touched) := by
  have postOnly : ∃ slot ∈ canonical.sourceSlots, ∃ postCoordinate,
      postCoordinate ∈ (layout.spanAt slot).coordinates /\
      coordinate = .inr (postCoordinate, .post) :=
    canonical.coordinatesPostOnly coordinate member
  obtain ⟨_, _, postCoordinate, _, coordinateExact⟩ := postOnly
  rw [coordinateExact]
  simp

end CanonicalPostOpening

end CanonicalOpening

/-! ## Exact-head observations -/

section Observation

variable {n : Nat} {F : Type*} [Field F] [DecidableEq F]
variable {Op : Type uOp}
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext -> BindingIx -> F}
    {C : Submodule F (BoundReceiptIx n -> F)}
    {SCommit : BindingCommitment Digest F (BoundReceiptIx n) Op}
    {DisclosureAtom : Type uAtom} [DecidableEq DisclosureAtom]

local notation "HistoryEntry" =>
  VerifiedEntry (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C)

local notation "HistoryHead" =>
  VerifiedHistoryHead (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) C SCommit

/-- Observation of one exact verified head entry through canonical post-state
coordinates only.  All cryptographic/deployment premises remain visible. -/
structure HeadObservation
    (ExactFinality : (head : HistoryHead) -> (entry : HistoryEntry) ->
      EntryAt head entry -> Digest -> Prop)
    (PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop)
    (CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop)
    (RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop)
    (layout : CanonicalPostLayout n F)
    (head : HistoryHead)
    (ref : TransclusionRef n F DisclosureAtom) where
  entry : HistoryEntry
  membership : EntryAt head entry
  committed : entry.context.outcome = .committed
  sourceDomainExact : ref.source.domain = entry.context.historyDomain
  sourceObjectExact : ref.source.object = entry.context.semanticObjectRoot
  historyEntryExact :
    ref.source.historyEntryRoot = entry.receiptRoot SCommit
  semanticRootExact : ref.source.semanticRoot = entry.context.postStateRoot
  canonicalOpening : CanonicalPostOpening layout entry ref.opening
  disclosureWithinCeiling : ref.disclosure ⊆ ref.capabilityCeiling
  finalized : ExactFinality head entry membership (entry.receiptRoot SCommit)
  pcsOpeningSound : PCSOpeningSound entry.claim ref.opening
  commitmentBinding : CommitmentBindingCR entry.claim
  fiatShamirROM : RandomOracleModel entry.claim

namespace HeadObservation

variable
    {ExactFinality : (head : HistoryHead) -> (entry : HistoryEntry) ->
      EntryAt head entry -> Digest -> Prop}
    {PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop}
    {CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop}
    {RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop}
    {layout : CanonicalPostLayout n F} {head : HistoryHead}
    {ref : TransclusionRef n F DisclosureAtom}

local notation "Observed" =>
  HeadObservation (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) (SCommit := SCommit)
    ExactFinality PCSOpeningSound
    CommitmentBindingCR RandomOracleModel layout head ref

theorem entry_mem (observation : Observed) :
    observation.entry ∈ head.entries :=
  observation.membership.mem

theorem cells_authenticated (observation : Observed) :
    ref.opening.cells =
      ref.opening.coordinates.map observation.entry.word :=
  observation.canonicalOpening.exact.cellsExact

theorem coordinates_are_post (observation : Observed)
    {coordinate : BoundReceiptIx n}
    (member : coordinate ∈ ref.opening.coordinates) :
    ∃ slot ∈ observation.canonicalOpening.sourceSlots, ∃ postCoordinate,
      postCoordinate ∈ (layout.spanAt slot).coordinates /\
      coordinate = .inr (postCoordinate, .post) :=
  observation.canonicalOpening.coordinates_post_only member

end HeadObservation

end Observation

/-! ## Accepted forward-link writes -/

section AcceptedLink

variable
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Declaration}

/-- The two first-order actions which write a forward `LinkRecord`.  Both retain
the accepted content token and the exact action equality. -/
inductive AcceptedLinkWrite
    (content : Accepted contentConfig projection authorityPre documentPre
      contentPortal contentDeclaration) : Type
  | link (payload : LinkPayload)
      (actionExact : contentDeclaration.action = .link payload)
  | transclusion (payload : TranscludePayload)
      (actionExact : contentDeclaration.action = .transclude payload)

namespace AcceptedLinkWrite

variable
    {content : Accepted contentConfig projection authorityPre documentPre
      contentPortal contentDeclaration}

def id (write : AcceptedLinkWrite content) : LinkId :=
  match write with
  | .link payload _ => payload.id
  | .transclusion payload _ => payload.forwardLinkId

def record (write : AcceptedLinkWrite content) : LinkRecord :=
  match write with
  | .link payload _ =>
      linkRecord (contentDeclaration.operationId contentConfig)
        contentDeclaration.intent.author payload
  | .transclusion payload _ =>
      transclusionForwardLink (contentDeclaration.operationId contentConfig)
        contentDeclaration.intent.author payload

def postCell (write : AcceptedLinkWrite content) : PostCell where
  space := .links
  key := write.id
  value := some write.record

/-- The accepted effect's actual canonical post cell contains the concrete
record named by the event.  This is derived from the retained first-order
action and `AcceptedCellEffect`, never supplied as another premise. -/
theorem post_contains (write : AcceptedLinkWrite content) :
    lookup content.accepted.prepared.post.logical .links write.id =
      some write.record := by
  cases write with
  | link payload actionExact =>
      simpa [id, record] using content.post_contains_link payload actionExact
  | transclusion payload actionExact =>
      simpa [id, record] using
        content.post_contains_transclusion_forward_link payload actionExact

end AcceptedLinkWrite

end AcceptedLink

/-! ## Exact-head forward-link admission -/

section LinkEvent

variable {n : Nat} {F : Type*} [Field F] [DecidableEq F]
variable {Op : Type uOp}
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext -> BindingIx -> F}
    {C : Submodule F (BoundReceiptIx n -> F)}
    {SCommit : BindingCommitment Digest F (BoundReceiptIx n) Op}

local notation "HistoryEntry" =>
  VerifiedEntry (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C)

local notation "HistoryHead" =>
  VerifiedHistoryHead (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) C SCommit

variable
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {contentConfig : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {contentPortal : Portal}
    {contentDeclaration : Declaration}
    {content : Accepted contentConfig projection authorityPre documentPre
      contentPortal contentDeclaration}
    {historyProjection : HistoryProjection
      (Minidregg.Theory.HyperdocumentOperations.family
        (M := MDoc) contentConfig) n F}

/-- An accepted forward link admitted at one exact semantic-history entry.
The opened value is the layout encoding of the same concrete `LinkRecord`
which Lean proves occurs in the accepted content post cell. -/
structure HeadLinkEvent
    (ExactFinality : (head : HistoryHead) -> (entry : HistoryEntry) ->
      EntryAt head entry -> Digest -> Prop)
    (PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop)
    (CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop)
    (RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop)
    (historyProjection : HistoryProjection
      (Minidregg.Theory.HyperdocumentOperations.family
        (M := MDoc) contentConfig) n F)
    (layout : CanonicalPostLayout n F)
    (head : HistoryHead)
    (linkRelationId : Digest) where
  entry : HistoryEntry
  membership : EntryAt head entry
  write : AcceptedLinkWrite content
  acceptedClaimExact : entry.claim =
    historyProjection.historyClaim headerCells entry.context content.accepted
  slot : Fin layout.cellCount
  cellExact : layout.cellAt slot = write.postCell
  representedPostExact :
    (layout.spanAt slot).coordinates.map entry.claim.witness.core.post =
      layout.encodeAt slot
  forward : StoredReference.ForwardLinkRealization n F write.record
  committed : entry.context.outcome = .committed
  relationExact : entry.context.semanticRelationId = linkRelationId
  acceptedPostRootExact :
    entry.context.postStateRoot = content.accepted.prepared.post.root
  finalized : ExactFinality head entry membership (entry.receiptRoot SCommit)
  openingExact :
    (RangeOrValueOpening.mk .range (layout.boundCoordinates slot)
      (layout.encodeAt slot)).Exact entry.word
  pcsOpeningSound : PCSOpeningSound entry.claim
    { shape := .range
      coordinates := layout.boundCoordinates slot
      cells := layout.encodeAt slot }
  commitmentBinding : CommitmentBindingCR entry.claim
  fiatShamirROM : RandomOracleModel entry.claim

namespace HeadLinkEvent

variable
    {ExactFinality : (head : HistoryHead) -> (entry : HistoryEntry) ->
      EntryAt head entry -> Digest -> Prop}
    {PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop}
    {CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop}
    {RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop}
    {layout : CanonicalPostLayout n F} {head : HistoryHead}
    {linkRelationId : Digest}

local notation "Event" =>
  HeadLinkEvent (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) (SCommit := SCommit)
    ExactFinality PCSOpeningSound
    CommitmentBindingCR RandomOracleModel historyProjection (content := content)
    layout head linkRelationId

def opening (event : Event) : RangeOrValueOpening n F where
  shape := .range
  coordinates := layout.boundCoordinates event.slot
  cells := layout.encodeAt event.slot

/-- The link opening is exact and post-only by construction. -/
theorem opening_exact (event : Event) :
    event.opening.Exact event.entry.word := by
  simpa [opening] using event.openingExact

theorem entry_mem (event : Event) : event.entry ∈ head.entries :=
  event.membership.mem

/-- The history word is the exact projection of the retained accepted content
effect, not merely an unrelated entry with a colliding post root. -/
theorem entry_post_is_accepted_projection (event : Event) :
    event.entry.claim.witness.core.post =
      historyProjection.project content.accepted.prepared.post := by
  have claimCore : event.entry.claim.witness.core.post =
      (historyProjection.historyClaim headerCells event.entry.context
        content.accepted).witness.core.post :=
    congrArg
      (fun claim : BoundSemanticReceiptClaim n F => claim.witness.core.post)
      event.acceptedClaimExact
  simpa only [HistoryProjection.historyClaim_core,
    HistoryProjection.core_post] using claimCore

/-- The event cannot merely name a link record.  The retained accepted effect
proves that exact record is the value of the canonical links cell in its post. -/
theorem accepted_post_contains_link (event : Event) :
    lookup content.accepted.prepared.post.logical .links event.write.id =
      some event.write.record :=
  event.write.post_contains

/-- The opened typed cell is exactly the same canonical cell whose concrete
link value occurs in the accepted post-state. -/
theorem opened_cell_exact (event : Event) :
    layout.cellAt event.slot =
      { space := .links
        key := event.write.id
        value := some event.write.record } := by
  exact event.cellExact

/-- Injectivity on the supported finite representation makes the concrete link
record load bearing: no other supported cell with the same field vector can be
substituted for it. -/
theorem cell_exact_of_same_encoding (event : Event)
    (other : Fin layout.cellCount)
    (sameEncoding : layout.encodeAt other = layout.encodeAt event.slot) :
    layout.cellAt other = event.write.postCell := by
  have sameSlot : other = event.slot :=
    CanonicalPostLayout.encodeAtInjective layout sameEncoding
  rw [sameSlot]
  exact event.cellExact

theorem opening_coordinates_post_only (event : Event)
    {coordinate : BoundReceiptIx n}
    (member : coordinate ∈ event.opening.coordinates) :
    ∃ postCoordinate ∈ (layout.spanAt event.slot).coordinates,
      coordinate = .inr (postCoordinate, .post) := by
  rw [opening, CanonicalPostLayout.boundCoordinates] at member
  obtain ⟨postCoordinate, postMember, coordinateExact⟩ :=
    List.mem_map.mp member
  rw [← coordinateExact]
  exact ⟨postCoordinate, postMember, rfl⟩

theorem opening_not_header (event : Event)
    {coordinate : BoundReceiptIx n}
    (member : coordinate ∈ event.opening.coordinates) (header : BindingIx) :
    coordinate ≠ .inl header := by
  obtain ⟨postCoordinate, _, coordinateExact⟩ :=
    event.opening_coordinates_post_only member
  rw [coordinateExact]
  simp

theorem opening_not_pre (event : Event)
    {coordinate : BoundReceiptIx n}
    (member : coordinate ∈ event.opening.coordinates) (key : Fin n) :
    coordinate ≠ .inr (key, .pre) := by
  obtain ⟨postCoordinate, _, coordinateExact⟩ :=
    event.opening_coordinates_post_only member
  rw [coordinateExact]
  simp

theorem opening_not_touched (event : Event)
    {coordinate : BoundReceiptIx n}
    (member : coordinate ∈ event.opening.coordinates) (key : Fin n) :
    coordinate ≠ .inr (key, .touched) := by
  obtain ⟨postCoordinate, _, coordinateExact⟩ :=
    event.opening_coordinates_post_only member
  rw [coordinateExact]
  simp

end HeadLinkEvent

end LinkEvent

#print axioms EntryAt.receiptRootAt_exact
#print axioms CanonicalPostOpening.exact
#print axioms CanonicalPostOpening.coordinates_post_only
#print axioms AcceptedLinkWrite.post_contains
#print axioms HeadLinkEvent.opening_exact
#print axioms HeadLinkEvent.accepted_post_contains_link
#print axioms HeadLinkEvent.cell_exact_of_same_encoding
#print axioms HeadLinkEvent.entry_post_is_accepted_projection

end


end Minidregg.Assurance.HyperdocumentHistoryAdmission
