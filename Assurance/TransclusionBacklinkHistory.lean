/-
# Assurance.TransclusionBacklinkHistory -- authenticated transclusion and links

This module supplies the schema-neutral part of a hypermedia substrate.  It is
deliberately downstream of `SemanticHistoryFamily.VerifiedEntry`: an observed
transclusion or forward link retains the complete verified entry and an exact
opening of that entry's bounded semantic word.  A root, URI, finality Boolean,
or host-maintained backlink table cannot manufacture either token.

The concrete hyperdocument schema still chooses stable range coordinates,
field encodings, the reference encoding, and the semantic relation identifier
for link events.  Finality, PCS opening soundness, commitment binding, and the
random-oracle model remain explicit deployment evidence.  They are not hidden
behind a native verifier callback and are not proved by this logical layer.

Reverse links are a deterministic filter of authenticated forward events.
The completeness theorem is intentionally scoped to the exact authenticated
domain supplied to the derivation; it makes no global-web completeness claim.
-/

import Assurance.AcceptedCellEffectHistory
import Assurance.SemanticHistoryFamily
import Theory.Hyperdocument

namespace Minidregg.Assurance.TransclusionBacklinkHistory

open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Selvage
open Minidregg.Theory
open Minidregg.Theory.CanonicalTransition
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome
  uClauseEvidence uOp uAtom u v w x y z

noncomputable section

/-! ## Durable reference and exact bounded-word opening -/

/-- Snapshot references retain the cited entry forever.  Live references also
retain the entry from which observation starts; advancing them requires an
authenticated reactive lifecycle, not an in-process refetch flag. -/
inductive Mode
  | snapshot
  | live
  deriving DecidableEq, Repr

/-- A single semantic coordinate or a stable ordered range of coordinates.
The concrete document schema is responsible for choosing stable coordinates. -/
inductive OpeningShape
  | value
  | range
  deriving DecidableEq, Repr

/-- Public identity of one exact semantic source version.  The receipt root is
the entry identity, while `semanticRoot` is the state/value root interpreted by
that entry. -/
structure SourceIdentity where
  domain : Digest
  object : Digest
  historyEntryRoot : Digest
  semanticRoot : Digest
  deriving DecidableEq, Repr

namespace SourceIdentity

theorem eq_of_fields {left right : SourceIdentity}
    (domain : left.domain = right.domain)
    (object : left.object = right.object)
    (historyEntryRoot : left.historyEntryRoot = right.historyEntryRoot)
    (semanticRoot : left.semanticRoot = right.semanticRoot) :
    left = right := by
  cases left
  cases right
  simp_all

end SourceIdentity

/-- A durable opening description.  The cells are retained because this
assurance layer deliberately keeps proof-relevant full openings. -/
structure RangeOrValueOpening (n : Nat) (F : Type*) where
  shape : OpeningShape
  coordinates : List (BoundReceiptIx n)
  cells : List F

namespace RangeOrValueOpening

variable {n : Nat} {F : Type*}

/-- Shape and cell exactness against one actual bounded semantic word. -/
structure Exact (opening : RangeOrValueOpening n F)
    (word : BoundReceiptIx n -> F) : Prop where
  cellsExact : opening.cells = opening.coordinates.map word
  valueShape : opening.shape = .value ->
    exists coordinate, opening.coordinates = [coordinate]
  rangeShape : opening.shape = .range ->
    opening.coordinates ≠ [] /\ opening.coordinates.Nodup

theorem exact_length
    {opening : RangeOrValueOpening n F} {word : BoundReceiptIx n -> F}
    (exact : opening.Exact word) :
    opening.cells.length = opening.coordinates.length := by
  rw [exact.cellsExact, List.length_map]

theorem value_has_one_cell
    {opening : RangeOrValueOpening n F} {word : BoundReceiptIx n -> F}
    (exact : opening.Exact word) (value : opening.shape = .value) :
    opening.cells.length = 1 := by
  obtain ⟨coordinate, coordinates⟩ := exact.valueShape value
  rw [exact.cellsExact, coordinates]
  rfl

end RangeOrValueOpening

/-- One durable typed transclusion reference.  Disclosure is a finite set of
semantic disclosure atoms; the capability ceiling is another set in the same
carrier, making non-amplification ordinary inclusion rather than a Boolean.

`referenceRoot` is the application-level canonical reference commitment.  A
concrete schema must define its codec/hash.  This generic layer never calls it
a cryptographic hash theorem. -/
structure TransclusionRef (n : Nat) (F : Type*)
    (DisclosureAtom : Type uAtom) where
  referenceRoot : Digest
  source : SourceIdentity
  opening : RangeOrValueOpening n F
  mode : Mode
  disclosure : Finset DisclosureAtom
  capabilityCeiling : Finset DisclosureAtom

/-- Canonical field representation selected by the concrete schema.  Its
injectivity is the representation proof used by forward-link admission. -/
structure ReferenceEncoding (n : Nat) (F : Type*)
    (DisclosureAtom : Type uAtom) where
  cells : TransclusionRef n F DisclosureAtom -> List F
  injective : Function.Injective cells

/-! ## Exact realization of the canonical first-order hyperdocument record -/

namespace StoredReference

open Minidregg.Theory.IndexedProgram

/-- Exact shape translation; the stored schema never mentions the proof field. -/
def openingShape : Hyperdocument.StoredOpeningShape -> OpeningShape
  | .value => .value
  | .range => .range

/-- Snapshot/live translation retains no host refetch semantics. -/
def mode : Hyperdocument.TransclusionMode -> Mode
  | .snapshot => .snapshot
  | .live => .live

/-- The generic source identity is a lossless projection of four separately
stored roots, not a reinterpretation of one document URI. -/
def sourceIdentity (source : Hyperdocument.StoredSourceIdentity) : SourceIdentity where
  domain := source.historyDomain
  object := source.objectRoot
  historyEntryRoot := source.historyEntryRoot
  semanticRoot := source.semanticRoot

/-- A concrete proof-field representation named by the first-order opening
descriptor.  The lawful codec owns all `n`, `F`, coordinate, and cell choices;
the stored schema therefore needs no universal-field mirror. -/
structure OpeningRepresentation (n : Nat) (F : Type*) where
  codecId : Digest
  relationId : Digest
  codec : LawfulCodec (RangeOrValueOpening n F)
  commitDescriptor : List UInt8 -> Digest

/-- Exact realization of one stored descriptor in one explicit representation.
Every equality is load bearing: matching only the commitment or only the shape
is insufficient to produce a generic transclusion reference. -/
structure ReferenceRealization {n : Nat} {F : Type*}
    (representation : OpeningRepresentation n F)
    (stored : Hyperdocument.StoredTransclusionRef) where
  opening : RangeOrValueOpening n F
  shapeExact : opening.shape = openingShape stored.opening.shape
  codecIdExact : representation.codecId = stored.opening.openingCodecId
  relationIdExact :
    representation.relationId = stored.opening.openingRelationId
  descriptorExact :
    representation.codec.encode opening = stored.opening.canonicalDescriptor
  commitmentExact :
    representation.commitDescriptor stored.opening.canonicalDescriptor =
      stored.opening.openingCommitment
  disclosureWithinCeiling :
    stored.disclosureScope ⊆ stored.capabilityCeiling

/-- The representation and its exact realization are explicit proof-relevant
input.  There is intentionally no `StoredTransclusionRef -> TransclusionRef`
shortcut which could guess `F`, coordinates, cells, or opening semantics. -/
structure RealizedReference (n : Nat) (F : Type*)
    (stored : Hyperdocument.StoredTransclusionRef) where
  representation : OpeningRepresentation n F
  realization : ReferenceRealization representation stored

namespace RealizedReference

variable {n : Nat} {F : Type*} {stored : Hyperdocument.StoredTransclusionRef}

/-- Produce the generic durable reference only through the named lawful
representation and its exact realization proof. -/
def toRef (realized : RealizedReference n F stored) :
    TransclusionRef n F Hyperdocument.DisclosureAtom where
  referenceRoot := stored.referenceRoot
  source := sourceIdentity stored.source
  opening := realized.realization.opening
  mode := StoredReference.mode stored.mode
  disclosure := stored.disclosureScope
  capabilityCeiling := stored.capabilityCeiling

@[simp] theorem toRef_referenceRoot
    (realized : RealizedReference n F stored) :
    realized.toRef.referenceRoot = stored.referenceRoot :=
  rfl

@[simp] theorem toRef_sourceDomain
    (realized : RealizedReference n F stored) :
    realized.toRef.source.domain = stored.source.historyDomain :=
  rfl

@[simp] theorem toRef_sourceObject
    (realized : RealizedReference n F stored) :
    realized.toRef.source.object = stored.source.objectRoot :=
  rfl

@[simp] theorem toRef_historyEntryRoot
    (realized : RealizedReference n F stored) :
    realized.toRef.source.historyEntryRoot = stored.source.historyEntryRoot :=
  rfl

@[simp] theorem toRef_semanticRoot
    (realized : RealizedReference n F stored) :
    realized.toRef.source.semanticRoot = stored.source.semanticRoot :=
  rfl

@[simp] theorem toRef_opening
    (realized : RealizedReference n F stored) :
    realized.toRef.opening = realized.realization.opening :=
  rfl

theorem toRef_openingShape
    (realized : RealizedReference n F stored) :
    realized.toRef.opening.shape = openingShape stored.opening.shape :=
  realized.realization.shapeExact

theorem toRef_descriptorExact
    (realized : RealizedReference n F stored) :
    realized.representation.codec.encode realized.toRef.opening =
      stored.opening.canonicalDescriptor :=
  realized.realization.descriptorExact

theorem toRef_commitmentExact
    (realized : RealizedReference n F stored) :
    realized.representation.commitDescriptor
        stored.opening.canonicalDescriptor =
      stored.opening.openingCommitment :=
  realized.realization.commitmentExact

@[simp] theorem toRef_mode
    (realized : RealizedReference n F stored) :
    realized.toRef.mode = StoredReference.mode stored.mode :=
  rfl

@[simp] theorem toRef_disclosure
    (realized : RealizedReference n F stored) :
    realized.toRef.disclosure = stored.disclosureScope :=
  rfl

@[simp] theorem toRef_capabilityCeiling
    (realized : RealizedReference n F stored) :
    realized.toRef.capabilityCeiling = stored.capabilityCeiling :=
  rfl

theorem toRef_disclosureWithinCeiling
    (realized : RealizedReference n F stored) :
    realized.toRef.disclosure ⊆ realized.toRef.capabilityCeiling :=
  realized.realization.disclosureWithinCeiling

end RealizedReference

/-- Exact adapter for the transclusion-bearing forward-link constructor.  A
document/element/range/external link cannot be silently reinterpreted as a
transclusion target, and the complete stored reference is retained. -/
structure ForwardLinkRealization (n : Nat) (F : Type*)
    (link : Hyperdocument.LinkRecord) where
  transclusionId : Hyperdocument.TransclusionId
  stored : Hyperdocument.StoredTransclusionRef
  targetExact : link.target = .transclusion transclusionId stored
  realized : RealizedReference n F stored

namespace ForwardLinkRealization

variable {n : Nat} {F : Type*} {link : Hyperdocument.LinkRecord}

def targetRef (forward : ForwardLinkRealization n F link) :
    TransclusionRef n F Hyperdocument.DisclosureAtom :=
  forward.realized.toRef

theorem target_source_exact (forward : ForwardLinkRealization n F link) :
    forward.targetRef.source = sourceIdentity forward.stored.source :=
  rfl

theorem link_binds_complete_stored_reference
    (forward : ForwardLinkRealization n F link) :
    link.target = .transclusion forward.transclusionId forward.stored :=
  forward.targetExact

end ForwardLinkRealization

end StoredReference

/-! ## Observation of an actual verified history entry -/

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

variable
    (FinalityEvidence : HistoryAdmissionContext -> Prop)
    (PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop)
    (CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop)
    (RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop)

/-- Authenticated observation of the exact source named by `ref`.  The private
constructor prevents callers from replacing a verified entry by roots or a
host verdict. -/
structure Observation (ref : TransclusionRef n F DisclosureAtom) where
  private mk ::
  entry : HistoryEntry
  committed : entry.context.outcome = .committed
  sourceDomainExact : ref.source.domain = entry.context.historyDomain
  sourceObjectExact : ref.source.object = entry.context.semanticObjectRoot
  historyEntryExact :
    ref.source.historyEntryRoot = entry.receiptRoot SCommit
  semanticRootExact : ref.source.semanticRoot = entry.context.postStateRoot
  openingExact : ref.opening.Exact entry.word
  disclosureWithinCeiling : ref.disclosure ⊆ ref.capabilityCeiling
  finalized : FinalityEvidence entry.context
  pcsOpeningSound : PCSOpeningSound entry.claim ref.opening
  commitmentBinding : CommitmentBindingCR entry.claim
  fiatShamirROM : RandomOracleModel entry.claim

local notation "Observed" =>
  Observation (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) (SCommit := SCommit)
    FinalityEvidence PCSOpeningSound CommitmentBindingCR RandomOracleModel

/-- The sole public constructor consumes a complete verified entry plus every
explicit semantic/cryptographic boundary witness. -/
def observe
    (ref : TransclusionRef n F DisclosureAtom)
    (entry : HistoryEntry)
    (committed : entry.context.outcome = .committed)
    (sourceDomainExact : ref.source.domain = entry.context.historyDomain)
    (sourceObjectExact : ref.source.object = entry.context.semanticObjectRoot)
    (historyEntryExact :
      ref.source.historyEntryRoot = entry.receiptRoot SCommit)
    (semanticRootExact : ref.source.semanticRoot = entry.context.postStateRoot)
    (openingExact : ref.opening.Exact entry.word)
    (disclosureWithinCeiling : ref.disclosure ⊆ ref.capabilityCeiling)
    (finalized : FinalityEvidence entry.context)
    (pcsOpeningSound : PCSOpeningSound entry.claim ref.opening)
    (commitmentBinding : CommitmentBindingCR entry.claim)
    (fiatShamirROM : RandomOracleModel entry.claim) :
    Observed ref :=
  ⟨entry, committed, sourceDomainExact, sourceObjectExact, historyEntryExact,
    semanticRootExact, openingExact, disclosureWithinCeiling, finalized,
    pcsOpeningSound, commitmentBinding, fiatShamirROM⟩

namespace Observation

variable
    {FinalityEvidence : HistoryAdmissionContext -> Prop}
    {PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop}
    {CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop}
    {RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop}
    {ref : TransclusionRef n F DisclosureAtom}

/-- No-amplification is retained as a directly usable theorem. -/
theorem disclosure_allowed
    (observation : Observation (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (SCommit := SCommit)
      FinalityEvidence PCSOpeningSound CommitmentBindingCR RandomOracleModel
      ref) :
    ref.disclosure ⊆ ref.capabilityCeiling :=
  observation.disclosureWithinCeiling

/-- The observed cells are exactly the selected cells of the verified word. -/
theorem cells_authenticated
    (observation : Observation (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (SCommit := SCommit)
      FinalityEvidence PCSOpeningSound CommitmentBindingCR RandomOracleModel
      ref) :
    ref.opening.cells = ref.opening.coordinates.map observation.entry.word :=
  observation.openingExact.cellsExact

end Observation

/-! ## Applying an observation through the common accepted-effect join -/

section Effect

variable
    {CellSchema : CellState.Schema.{u, v, w, x}}
    [DecidableEq CellSchema.Field] [DecidableEq CellSchema.Resource]
    {M : CellState.Materializer CellSchema Digest}
    {Nullifier : Type y}
    {effectFamily : SemanticEffectFamily.{u, v, w, x, y, z}
      CellSchema M Nullifier}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {request : Request kind} {pre : CellState.Materialized M}
    {declaration : effectFamily.Declaration}
    {outcome : effectFamily.Outcome declaration}

/-- A transclusion effect is not a second effect semantics.  It packages an
authenticated source observation with the existing common positive semantic
effect, whose exact request argument commits the durable reference root. -/
structure AppliedEffect (ref : TransclusionRef n F DisclosureAtom) where
  private mk ::
  observation : Observation (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) (SCommit := SCommit)
    FinalityEvidence PCSOpeningSound CommitmentBindingCR RandomOracleModel ref
  accepted : AcceptedCellEffect (portal := portal) (authState := authState)
    effectFamily request pre declaration outcome
  referenceArgumentExact : request.argsDigest = ref.referenceRoot

/-- Construct an applied transclusion only from an authenticated observation
and an already accepted effect at its exact dependent indices. -/
def applyEffect
    {ref : TransclusionRef n F DisclosureAtom}
    (observation : Observation (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (SCommit := SCommit)
      FinalityEvidence PCSOpeningSound CommitmentBindingCR RandomOracleModel
      ref)
    (accepted : AcceptedCellEffect (portal := portal) (authState := authState)
      effectFamily request pre declaration outcome)
    (referenceArgumentExact : request.argsDigest = ref.referenceRoot) :
    AppliedEffect (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (SCommit := SCommit)
      (CellSchema := CellSchema) (M := M) (Nullifier := Nullifier)
      (effectFamily := effectFamily) (portal := portal)
      (authState := authState) (kind := kind) (request := request)
      (pre := pre) (declaration := declaration) (outcome := outcome)
      FinalityEvidence PCSOpeningSound CommitmentBindingCR RandomOracleModel
      ref :=
  ⟨observation, accepted, referenceArgumentExact⟩

end Effect

/-! ## Forward events and exact chain welds -/

/-- One forward link proven to occur in an actual committed semantic entry.
The event opening must be both an exact opening of that entry's word and the
canonical injective representation of the complete destination reference. -/
structure LinkEvent
    (encoding : ReferenceEncoding n F DisclosureAtom)
    (linkRelationId : Digest) where
  private mk ::
  entry : HistoryEntry
  target : TransclusionRef n F DisclosureAtom
  eventOpening : RangeOrValueOpening n F
  committed : entry.context.outcome = .committed
  relationExact : entry.context.semanticRelationId = linkRelationId
  openingExact : eventOpening.Exact entry.word
  targetEncodingExact : eventOpening.cells = encoding.cells target
  targetDisclosureWithinCeiling :
    target.disclosure ⊆ target.capabilityCeiling
  finalized : FinalityEvidence entry.context
  pcsOpeningSound : PCSOpeningSound entry.claim eventOpening
  commitmentBinding : CommitmentBindingCR entry.claim
  fiatShamirROM : RandomOracleModel entry.claim

/-- Admit one forward event from the exact verified source entry. -/
def forwardLink
    (encoding : ReferenceEncoding n F DisclosureAtom)
    (linkRelationId : Digest)
    (entry : HistoryEntry)
    (target : TransclusionRef n F DisclosureAtom)
    (eventOpening : RangeOrValueOpening n F)
    (committed : entry.context.outcome = .committed)
    (relationExact : entry.context.semanticRelationId = linkRelationId)
    (openingExact : eventOpening.Exact entry.word)
    (targetEncodingExact : eventOpening.cells = encoding.cells target)
    (targetDisclosureWithinCeiling :
      target.disclosure ⊆ target.capabilityCeiling)
    (finalized : FinalityEvidence entry.context)
    (pcsOpeningSound : PCSOpeningSound entry.claim eventOpening)
    (commitmentBinding : CommitmentBindingCR entry.claim)
    (fiatShamirROM : RandomOracleModel entry.claim) :
    LinkEvent (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel encoding linkRelationId :=
  ⟨entry, target, eventOpening, committed, relationExact, openingExact,
    targetEncodingExact, targetDisclosureWithinCeiling, finalized,
    pcsOpeningSound, commitmentBinding, fiatShamirROM⟩

namespace LinkEvent

variable
    {FinalityEvidence : HistoryAdmissionContext -> Prop}
    {PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop}
    {CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop}
    {RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop}
    {encoding : ReferenceEncoding n F DisclosureAtom}
    {linkRelationId : Digest}

local notation "Event" =>
  LinkEvent (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) FinalityEvidence PCSOpeningSound
    CommitmentBindingCR RandomOracleModel encoding linkRelationId

/-- Exact source identity derived from the retained verified entry. -/
def source (event : Event) : SourceIdentity where
  domain := event.entry.context.historyDomain
  object := event.entry.context.semanticObjectRoot
  historyEntryRoot := event.entry.receiptRoot SCommit
  semanticRoot := event.entry.context.postStateRoot

/-- Injection of the reference encoding makes equal opened link cells bind the
same complete destination reference, not merely the same URI. -/
theorem target_eq_of_opening_cells_eq
    (left right : Event)
    (cellsEqual : left.eventOpening.cells = right.eventOpening.cells) :
    left.target = right.target := by
  apply encoding.injective
  rw [← left.targetEncodingExact, ← right.targetEncodingExact]
  exact cellsEqual

end LinkEvent

/-- Every field needed to weld adjacent hops is exact.  In particular, a link
to an object at one receipt cannot be followed by an arbitrary URI resolving
to another receipt of that object. -/
structure Weld
    {FinalityEvidence : HistoryAdmissionContext -> Prop}
    {PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop}
    {CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop}
    {RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop}
    {encoding : ReferenceEncoding n F DisclosureAtom}
    {linkRelationId : Digest}
    (left right : LinkEvent (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel encoding linkRelationId) : Prop where
  domainExact : left.target.source.domain = right.entry.context.historyDomain
  objectExact : left.target.source.object = right.entry.context.semanticObjectRoot
  historyEntryExact :
    left.target.source.historyEntryRoot = right.entry.receiptRoot SCommit
  semanticRootExact :
    left.target.source.semanticRoot = right.entry.context.postStateRoot

namespace Weld

variable
    {FinalityEvidence : HistoryAdmissionContext -> Prop}
    {PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop}
    {CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop}
    {RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop}
    {encoding : ReferenceEncoding n F DisclosureAtom}
    {linkRelationId : Digest}
    {left right : LinkEvent (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel encoding linkRelationId}

theorem source_exact
    (weld : Weld (SCommit := SCommit) left right) :
    left.target.source = LinkEvent.source (SCommit := SCommit) right := by
  apply SourceIdentity.eq_of_fields
  · exact weld.domainExact
  · exact weld.objectExact
  · exact weld.historyEntryExact
  · exact weld.semanticRootExact

end Weld

/-- An `hops`-event transclusion chain.  `List.IsChain` asks for a weld at
every adjacent pair, unlike pairwise URI membership or independent finality
checks. -/
structure Chain
    (FinalityEvidence : HistoryAdmissionContext -> Prop)
    (PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop)
    (CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop)
    (RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop)
    (encoding : ReferenceEncoding n F DisclosureAtom)
    (linkRelationId : Digest) (hops : Nat) where
  events : List (LinkEvent (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) FinalityEvidence PCSOpeningSound
    CommitmentBindingCR RandomOracleModel encoding linkRelationId)
  lengthExact : events.length = hops
  nonempty : events ≠ []
  adjacent : List.IsChain (Weld (SCommit := SCommit)) events

namespace Chain

variable
    {FinalityEvidence : HistoryAdmissionContext -> Prop}
    {PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop}
    {CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop}
    {RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop}
    {encoding : ReferenceEncoding n F DisclosureAtom}
    {linkRelationId : Digest} {hops : Nat}

theorem positive
    (chain : Chain (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (SCommit := SCommit)
      FinalityEvidence PCSOpeningSound CommitmentBindingCR RandomOracleModel
      encoding linkRelationId hops) :
    0 < hops := by
  rw [← chain.lengthExact]
  exact List.length_pos_of_ne_nil chain.nonempty

end Chain

/-! ## Authenticated reverse-index derivation -/

local notation "Event" =>
  LinkEvent (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) FinalityEvidence PCSOpeningSound
    CommitmentBindingCR RandomOracleModel

/-- The explicit completeness domain for reverse-link queries.  Every element
is already an authenticated `LinkEvent`; the bounds state which exact history
slice this particular derivation claims to cover. -/
structure ReverseIndexDomain
    (FinalityEvidence : HistoryAdmissionContext -> Prop)
    (PCSOpeningSound : BoundSemanticReceiptClaim n F ->
      RangeOrValueOpening n F -> Prop)
    (CommitmentBindingCR : BoundSemanticReceiptClaim n F -> Prop)
    (RandomOracleModel : BoundSemanticReceiptClaim n F -> Prop)
    (encoding : ReferenceEncoding n F DisclosureAtom)
    (linkRelationId : Digest) where
  historyDomain : Digest
  firstSequence : Nat
  pastSequence : Nat
  verifiedEntries : List HistoryEntry
  entrySliceExact : forall entry, entry ∈ verifiedEntries ->
    entry.context.historyDomain = historyDomain /\
    firstSequence <= entry.context.sequence /\
    entry.context.sequence < pastSequence
  events : List (LinkEvent (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) FinalityEvidence PCSOpeningSound
    CommitmentBindingCR RandomOracleModel encoding linkRelationId)
  eventSourceInSlice : forall event, event ∈ events ->
    event.entry ∈ verifiedEntries
  covers : forall event : LinkEvent (manifest := manifest)
      (registry := registry) (clauseEvidence := clauseEvidence)
      (family := family) (headerCells := headerCells) (C := C)
      FinalityEvidence PCSOpeningSound CommitmentBindingCR RandomOracleModel
      encoding linkRelationId,
    event.entry ∈ verifiedEntries -> event ∈ events

/-- Reverse hits are derived by equality on the complete target source
identity.  No separately mutable backlink map is accepted as evidence. -/
def reverseIndex
    {encoding : ReferenceEncoding n F DisclosureAtom}
    {linkRelationId : Digest}
    (domain : ReverseIndexDomain (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel encoding linkRelationId)
    (target : SourceIdentity) : List (Event encoding linkRelationId) :=
  domain.events.filter fun event => event.target.source = target

/-- Every returned backlink is an authenticated forward event from the exact
declared domain and points to the queried source identity. -/
theorem reverseIndex_sound
    {encoding : ReferenceEncoding n F DisclosureAtom}
    {linkRelationId : Digest}
    (domain : ReverseIndexDomain (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel encoding linkRelationId)
    (target : SourceIdentity) (event : Event encoding linkRelationId)
    (member : event ∈ reverseIndex FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel domain target) :
    event.entry ∈ domain.verifiedEntries /\
      event ∈ domain.events /\ event.target.source = target := by
  have filtered : event ∈ domain.events /\ event.target.source = target := by
    simpa [reverseIndex] using member
  exact ⟨domain.eventSourceInSlice event filtered.1, filtered⟩

/-- Completeness is exact for the declared authenticated history slice: every
event in that domain which targets the identity appears in the derived index. -/
theorem reverseIndex_complete_in_domain
    {encoding : ReferenceEncoding n F DisclosureAtom}
    {linkRelationId : Digest}
    (domain : ReverseIndexDomain (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel encoding linkRelationId)
    (target : SourceIdentity) (event : Event encoding linkRelationId)
    (sourceInCoveredSlice : event.entry ∈ domain.verifiedEntries)
    (targetExact : event.target.source = target) :
    event ∈ reverseIndex FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel domain target := by
  simp [reverseIndex, domain.covers event sourceInCoveredSlice, targetExact]

theorem reverseIndex_mem_iff
    {encoding : ReferenceEncoding n F DisclosureAtom}
    {linkRelationId : Digest}
    (domain : ReverseIndexDomain (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel encoding linkRelationId)
    (target : SourceIdentity) (event : Event encoding linkRelationId) :
    event ∈ reverseIndex FinalityEvidence PCSOpeningSound
      CommitmentBindingCR RandomOracleModel domain target <->
      event ∈ domain.events /\ event.target.source = target := by
  simp [reverseIndex]

end Observation

end

end Minidregg.Assurance.TransclusionBacklinkHistory
