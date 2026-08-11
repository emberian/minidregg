/-
# Assurance.HyperdocumentLinkReopenWitness -- one exact retained link view

This module carries the concrete accepted `.link` turn from
`HyperdocumentLinkPublicationWitness` into a finite declared-footprint receipt,
a two-entry `VerifiedHistoryHead`, one canonical post-only opening, and the
ordinary canonical content query.  The head contains the child at an exact
`Fin` index and the view is dirty for the accepted delta.

The finite receipt word is scoped to this declaration's footprint.  It does
not enumerate the infinite Hyperdocument address schema.  The commitment below
is an injective finite witness, not a deployed PCS.  PCS opening soundness,
commitment collision resistance, Fiat--Shamir/ROM, external finality, and
durable persistence remain explicit deployment premises at the end of the
module; none is inferred from the logical query or from the witness
commitment.
-/
import Assurance.HistoryHeadInhabitation
import Assurance.HyperdocumentHistoryAdmission
import Assurance.HyperdocumentLinkPublicationWitness
import Assurance.ScopedAcceptedCellEffectHistory
import Theory.HyperdocumentInterface

namespace Minidregg.Assurance.HyperdocumentLinkReopenWitness

open Minidregg.Assurance.HyperdocumentHistoryAdmission
open Minidregg.Assurance.HyperdocumentLinkPublicationWitness
open Minidregg.Assurance.ScopedAcceptedCellEffectHistory
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.TransclusionBacklinkHistory
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom
open Minidregg.Theory
open Minidregg.Theory.CanonicalReactiveView
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentInterface
open Minidregg.Theory.HyperdocumentOperations
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## The finite declared footprint and its one represented link cell -/

abbrev Fld := ZMod 5

def scalarizer : Scalarizer Hyperdocument.cellSchema Fld where
  root := fun root => root.value
  field := fun _ _ => 1
  resource := fun resource => nomatch resource

abbrev linkScope : DeclaredScope (linkDeclaration.patch config) :=
  ScopedAcceptedCellEffectHistory.HyperdocumentAdapter.scope.{0, 0}
    config linkDeclaration

abbrev width := linkScope.width

def linkAddress : Hyperdocument.Address :=
  ⟨.links, linkId⟩

theorem linkAddress_named :
    linkAddress ∈ (linkDeclaration.patch config).fieldFootprint := by
  simp [linkAddress, linkDeclaration, linkAction, linkPayload,
    HyperdocumentOperations.Declaration.patch,
    HyperdocumentOperations.Declaration.fieldWrites,
    HyperdocumentOperations.Declaration.packedWrites,
    HyperdocumentOperations.Action.packedWrites,
    HyperdocumentOperations.linkWrites,
    HyperdocumentOperations.PackedWrite.toFieldWrite,
    HyperdocumentOperations.PackedWrite.address]
  exact Finset.mem_singleton_self _

def linkCoordinate : Fin width :=
  linkScope.coordinateEquivFin
    (linkScope.fieldCoordinate linkAddress linkAddress_named)

def linkSpan : PostSpan width where
  start := linkCoordinate.val
  width := 1
  withinBounds := Nat.succ_le_iff.mpr linkCoordinate.isLt

@[simp] theorem linkSpan_coordinates :
    linkSpan.coordinates = [linkCoordinate] := by
  simp [PostSpan.coordinates, linkSpan, List.finRange_succ,
    PostSpan.coordinate]

def record : LinkRecord :=
  linkRecord (linkDeclaration.operationId config)
    Genesis.author linkPayload

def postCell : PostCell where
  space := .links
  key := linkId
  value := some record

/-- A nonempty canonical layout for the exact concrete `LinkRecord`.  Only the
declared link address is represented; no global schema enumeration occurs. -/
def layout : CanonicalPostLayout width Fld where
  cellCount := 1
  cellAt := fun _ => postCell
  cellAtInjective := fun left right _ => Subsingleton.elim left right
  spanAt := fun _ => linkSpan
  encodeAt := fun _ => [1]
  encodedLength := by intro slot; rfl
  spanNonempty := by intro slot; exact Nat.zero_lt_succ 0
  encodeAtInjective := fun left right _ => Subsingleton.elim left right
  spansDisjoint := by
    intro left right different
    exact (different (Subsingleton.elim left right)).elim

theorem layout_nonempty : 0 < layout.cellCount := by decide

def linkSlot : Fin layout.cellCount := ⟨0, by change 0 < 1; decide⟩

@[simp] theorem layout_cell_exact : layout.cellAt linkSlot = postCell := rfl

@[simp] theorem layout_encoding_exact : layout.encodeAt linkSlot = [1] := rfl

/-! ## A concrete two-entry exact semantic head -/

def manifest : Manifest where
  manifestVersion := 1
  abiId := ⟨0⟩
  semanticProgramId := ⟨0⟩
  semanticRelationId := config.semanticRelation
  receiptCodecId := ⟨0⟩
  codecs := []
  carriers := []
  bridges := []
  dialectClauses := []
  transcriptControllerDigest := ⟨0⟩
  dimensions := []
  bounds := []

def registry : ControllerRegistry.{0, 0, 0, 0} := ⟨[]⟩

def clauseEvidence : ClauseEvidenceFamily manifest registry where
  Evidence := fun _ _ _ => PEmpty.{1}

def headerCells : HistoryAdmissionContext → BindingIx → Fld :=
  fun _ _ => 0

def code : Submodule Fld (BoundReceiptIx width → Fld) := ⊤

def family : EntrySemanticsFamily.{0} width Fld where
  Evidence := fun context claim =>
    PLift (∀ denial, context.outcome = .rejected denial →
      claim.witness.core.post = claim.witness.core.pre)
  rejectedCoreAtomic := by
    intro context claim evidence denial rejected
    exact evidence.down denial rejected

def parentContext : HistoryAdmissionContext where
  manifestAddress := manifest.contentAddress
  historyDomain := linkIntent.historyDomain
  sequence := 0
  previousReceiptRoot := none
  semanticObjectRoot := Genesis.documentId.digest
  semanticRelationId := manifest.semanticRelationId
  outcome := .committed
  preStateRoot := genesisPost.root
  postStateRoot := genesisPost.root
  effectRoot := genesisDeclaration.effectDigest config
  authorizationRoot := ⟨0⟩
  disclosureRoot := ⟨0⟩
  dialectClauseRoots := []

theorem parentContext_wellFormed : parentContext.WellFormed manifest where
  manifestExact := rfl
  semanticRelationExact := rfl
  historyLink := Or.inl ⟨rfl, rfl⟩
  rejectedAtomic := trivial
  dialectClauseIdsUnique := List.nodup_nil
  dialectClausesClosed := fun _ absent => absurd absent (List.not_mem_nil)

def parentDelta : ReceiptDelta
    (linkScope.finProject scalarizer genesisPost)
    (linkScope.finProject scalarizer genesisPost) where
  touched := ∅
  frame := by intro index outside; rfl

def parentClaim : BoundSemanticReceiptClaim width Fld where
  witness :=
    { binding := headerCells parentContext
      core := ReceiptWitness.ofDelta parentDelta }
  valid := ReceiptWitness.ofDelta_satisfies parentDelta

def parentEntry : VerifiedEntry (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := code) where
  context := parentContext
  claim := parentClaim
  semantics := PLift.up (fun _ rejected => by cases rejected)
  contextWellFormed := parentContext_wellFormed
  dialectEvidence := ⟨fun index => index.elim0, fun index => index.elim0⟩
  bindingExact := rfl
  codeword := Submodule.mem_top

/-! The finite child core is generated directly from the accepted link patch.
Its public pre/post roots remain the exact typed `Digest` roots below rather
than being reconstructed from the finite word. -/

def childContext : HistoryAdmissionContext where
  manifestAddress := manifest.contentAddress
  historyDomain := linkIntent.historyDomain
  sequence := 1
  previousReceiptRoot := none -- filled after the witness commitment is defined
  semanticObjectRoot := Genesis.documentId.digest
  semanticRelationId := manifest.semanticRelationId
  outcome := .committed
  preStateRoot := genesisPost.root
  postStateRoot := linkAccepted.accepted.prepared.post.root
  effectRoot := linkDeclaration.effectDigest config
  authorizationRoot := ⟨0⟩
  disclosureRoot := ⟨0⟩
  dialectClauseRoots := []

def childCore : ReceiptWitness (Fin width) Fld :=
  ScopedAcceptedCellEffectHistory.HyperdocumentAdapter.finCore
    linkAccepted scalarizer

theorem childCore_valid : childCore.Satisfies :=
  ScopedAcceptedCellEffectHistory.HyperdocumentAdapter.finCore_valid
    linkAccepted scalarizer

/-! ## Honest finite witness commitment -/

def commitWord (word : BoundReceiptIx width → Fld) : Digest :=
  ⟨(Fintype.equivFin (BoundReceiptIx width → Fld) word).val⟩

theorem commitWord_injective : Function.Injective commitWord := by
  intro left right equal
  have vals : (Fintype.equivFin (BoundReceiptIx width → Fld) left).val =
      (Fintype.equivFin (BoundReceiptIx width → Fld) right).val :=
    congrArg Digest.value equal
  exact (Fintype.equivFin (BoundReceiptIx width → Fld)).injective
    (Fin.ext vals)

def scheme : BindingCommitment Digest Fld (BoundReceiptIx width)
    (BoundReceiptIx width → Fld) where
  commit := commitWord
  openAt := fun word _ => word
  verifyOpen root index value opening :=
    commitWord opening = root ∧ opening index = value
  verifyOpen_commit := fun word index => ⟨rfl, rfl⟩
  binding := by
    rintro root index left right leftOpening rightOpening
      ⟨leftRoot, leftValue⟩ ⟨rightRoot, rightValue⟩
    have same : leftOpening = rightOpening :=
      commitWord_injective (leftRoot.trans rightRoot.symm)
    rw [← leftValue, ← rightValue, same]

def linkedChildContext : HistoryAdmissionContext :=
  { childContext with
    previousReceiptRoot := some (parentEntry.receiptRoot scheme) }

theorem linkedChildContext_wellFormed :
    linkedChildContext.WellFormed manifest where
  manifestExact := rfl
  semanticRelationExact := rfl
  historyLink := Or.inr ⟨Nat.zero_lt_one, ⟨_, rfl⟩⟩
  rejectedAtomic := trivial
  dialectClauseIdsUnique := List.nodup_nil
  dialectClausesClosed := fun _ absent => absurd absent (List.not_mem_nil)

def childClaim : BoundSemanticReceiptClaim width Fld where
  witness :=
    { binding := headerCells linkedChildContext
      core := childCore }
  valid := childCore_valid

def childEntry : VerifiedEntry (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := code) where
  context := linkedChildContext
  claim := childClaim
  semantics := PLift.up (fun _ rejected => by cases rejected)
  contextWellFormed := linkedChildContext_wellFormed
  dialectEvidence := ⟨fun index => index.elim0, fun index => index.elim0⟩
  bindingExact := rfl
  codeword := Submodule.mem_top

def foldRoot : Digest → Fld → Digest → Digest :=
  fun _ _ _ => commitWord (parentEntry.word + childEntry.word)

def parentHead : VerifiedHistoryHead manifest registry clauseEvidence family
    headerCells code scheme :=
  VerifiedHistoryHead.start manifest registry clauseEvidence family
    headerCells code scheme foldRoot parentEntry rfl rfl

theorem appendLink : VerifiedHistoryHead.AppendLink manifest registry
    clauseEvidence family headerCells code scheme parentHead childEntry where
  historyDomainExact := rfl
  sequenceExact := rfl
  predecessorExact := rfl
  stateExact := rfl

theorem foldRecommitment : VerifiedHistoryHead.FoldRecommitment manifest
    registry clauseEvidence family headerCells code scheme parentHead childEntry
    1 where
  rootExact := by
    change commitWord (parentEntry.word + childEntry.word) =
      commitWord (parentEntry.word + 1 • childEntry.word)
    simp

def head : VerifiedHistoryHead manifest registry clauseEvidence family
    headerCells code scheme :=
  VerifiedHistoryHead.append manifest registry clauseEvidence family
    headerCells code scheme parentHead childEntry 1 appendLink foldRecommitment

@[simp] theorem head_entries : head.entries = [parentEntry, childEntry] := rfl

def childIndex : Fin head.entries.length := ⟨1, by simp⟩

def childAt : EntryAt (SCommit := scheme) head childEntry where
  index := childIndex
  entryExact := rfl

@[simp] theorem child_index_exact :
    head.entries.get childAt.index = childEntry := rfl

/-! ## Exact post-only opening -/

def opening : RangeOrValueOpening width Fld where
  shape := .range
  coordinates := layout.boundCoordinates linkSlot
  cells := layout.encodeAt linkSlot

@[simp] theorem opening_coordinates_exact :
    opening.coordinates = [.inr (linkCoordinate, .post)] := by
  change linkSpan.coordinates.map
    (fun coordinate => Sum.inr (coordinate, ReceiptSlot.post)) = _
  rw [linkSpan_coordinates]
  rfl

theorem representedPostExact :
    (layout.spanAt linkSlot).coordinates.map childEntry.claim.witness.core.post =
      layout.encodeAt linkSlot := by
  change linkSpan.coordinates.map childEntry.claim.witness.core.post = [1]
  rw [linkSpan_coordinates]
  simp only [List.map_cons, List.map_nil, List.cons.injEq]
  constructor
  · change (ScopedAcceptedCellEffectHistory.HyperdocumentAdapter.finCore
      linkAccepted scalarizer).post linkCoordinate = 1
    change linkScope.finProject scalarizer
      linkAccepted.accepted.prepared.post linkCoordinate = 1
    rw [show linkCoordinate = linkScope.coordinateEquivFin
      (linkScope.fieldCoordinate linkAddress linkAddress_named) by rfl]
    rw [ScopedAcceptedCellEffectHistory.HyperdocumentAdapter.post_lookup_exact
      linkAccepted scalarizer linkAddress linkAddress_named]
    rfl
  · trivial

theorem opening_exact : opening.Exact childEntry.word where
  cellsExact := by
    simpa [opening, CanonicalPostLayout.boundCoordinates,
      SemanticHistoryFamily.VerifiedEntry.word, BoundReceiptWitness.encode,
      ReceiptWitness.encode,
      Function.comp_def] using representedPostExact.symm
  valueShape := by intro impossible; cases impossible
  rangeShape := by
    intro range
    change layout.boundCoordinates linkSlot ≠ [] ∧
      (layout.boundCoordinates linkSlot).Nodup
    change (linkSpan.coordinates.map
      (fun coordinate => Sum.inr (coordinate, ReceiptSlot.post))) ≠ [] ∧
      (linkSpan.coordinates.map
        (fun coordinate => Sum.inr (coordinate, ReceiptSlot.post))).Nodup
    rw [linkSpan_coordinates]
    simp

def canonicalOpening : CanonicalPostOpening layout childEntry opening where
  sourceSlots := [linkSlot]
  coordinatesExact := by simp [opening]
  coordinatesPostOnly := by
    intro coordinate member
    simp only [opening, CanonicalPostLayout.boundCoordinates,
      List.mem_map] at member
    obtain ⟨postCoordinate, postMember, rfl⟩ := member
    exact ⟨linkSlot, by simp, postCoordinate, postMember, rfl⟩
  noHeaderCoordinate := by
    intro coordinate member header masquerades
    simp only [opening, CanonicalPostLayout.boundCoordinates,
      List.mem_map] at member
    obtain ⟨postCoordinate, postMember, rfl⟩ := member
    cases masquerades
  noPreCoordinate := by
    intro coordinate member key masquerades
    simp only [opening, CanonicalPostLayout.boundCoordinates,
      List.mem_map] at member
    obtain ⟨postCoordinate, postMember, rfl⟩ := member
    cases masquerades
  noTouchedCoordinate := by
    intro coordinate member key masquerades
    simp only [opening, CanonicalPostLayout.boundCoordinates,
      List.mem_map] at member
    obtain ⟨postCoordinate, postMember, rfl⟩ := member
    cases masquerades
  cellsExact := by simp [opening]
  openingExact := opening_exact
  representedPostExact := by
    intro slot member
    have slotExact : slot = linkSlot := by simpa using member
    subst slot
    exact representedPostExact
  valueShape := by intro impossible; cases impossible
  rangeShape := by
    intro equal
    constructor
    · simp
    · change (linkSpan.coordinates.map
        (fun coordinate => Sum.inr (coordinate, ReceiptSlot.post))).Nodup
      rw [linkSpan_coordinates]
      simp

/-! `WitnessFinality` is exact structural selection of this built head, not a
consensus or storage finality claim. -/

structure WitnessFinality
    (candidateHead : VerifiedHistoryHead manifest registry clauseEvidence family
      headerCells code scheme)
    (candidateEntry : VerifiedEntry (manifest := manifest)
      (registry := registry) (clauseEvidence := clauseEvidence)
      (family := family) (headerCells := headerCells) (C := code))
    (position : EntryAt (SCommit := scheme) candidateHead candidateEntry)
    (root : Digest) : Prop where
  headExact : candidateHead = head
  entryExact : candidateEntry = childEntry
  indexExact : position.index.val = childAt.index.val
  rootExact : root = childEntry.receiptRoot scheme

theorem childWitnessFinality :
    WitnessFinality head childEntry childAt (childEntry.receiptRoot scheme) where
  headExact := rfl
  entryExact := rfl
  indexExact := rfl
  rootExact := rfl

/-! ## Canonical query and reactive invalidation -/

def query : ContentQuery := .link linkId

@[simp] theorem query_exact :
    ContentQuery.project query linkAccepted.accepted.prepared.post.logical =
      some record := by
  simpa [query, ContentQuery.project, record] using
    link_post_contains_forward

theorem query_dirty : ContentQuery.lens.Dirty query
    linkAccepted.accepted.prepared.delta := by
  left
  exact ⟨linkAddress, Finset.mem_inter.mpr ⟨by simp [query, linkAddress,
    ContentQuery.lens, ContentQuery.footprint]; exact Finset.mem_singleton_self _, by
      rw [AcceptedCellEffect.prepared_fieldFootprint]
      exact linkAddress_named⟩⟩

/-- The canonical view reopened after the accepted turn is the exact concrete
link represented by the layout and retained by the indexed child entry. -/
structure ReopenedLink where
  position : EntryAt (SCommit := scheme) head childEntry
  selectedCell : layout.cellAt linkSlot = postCell
  postOnly : CanonicalPostOpening layout childEntry opening
  finality : WitnessFinality head childEntry position
    (childEntry.receiptRoot scheme)
  queryResult : ContentQuery.project query
    linkAccepted.accepted.prepared.post.logical = some record
  dirty : ContentQuery.lens.Dirty query
    linkAccepted.accepted.prepared.delta

def reopened : ReopenedLink where
  position := childAt
  selectedCell := rfl
  postOnly := canonicalOpening
  finality := childWitnessFinality
  queryResult := query_exact
  dirty := query_dirty

theorem wrong_header_cannot_masquerade
    {coordinate : BoundReceiptIx width}
    (member : coordinate ∈ opening.coordinates) (header : BindingIx) :
    coordinate ≠ .inl header :=
  canonicalOpening.noHeaderCoordinate coordinate member header

theorem wrong_pre_cannot_masquerade
    {coordinate : BoundReceiptIx width}
    (member : coordinate ∈ opening.coordinates) (key : Fin width) :
    coordinate ≠ .inr (key, .pre) :=
  canonicalOpening.noPreCoordinate coordinate member key

theorem wrong_touched_cannot_masquerade
    {coordinate : BoundReceiptIx width}
    (member : coordinate ∈ opening.coordinates) (key : Fin width) :
    coordinate ≠ .inr (key, .touched) :=
  canonicalOpening.noTouchedCoordinate coordinate member key

/-! ## Deployment premises remain independent -/

/-- Evidence required before the logical reopen may be called a deployed,
durable, cryptographically authenticated read.  No constructor is provided by
this module. -/
structure DeploymentEvidence
    (PCSOpeningSound : BoundSemanticReceiptClaim width Fld →
      RangeOrValueOpening width Fld → Prop)
    (CommitmentBindingCR : BoundSemanticReceiptClaim width Fld → Prop)
    (RandomOracleModel : BoundSemanticReceiptClaim width Fld → Prop)
    (ExternallyFinal :
      (candidateHead : VerifiedHistoryHead manifest registry clauseEvidence
        family headerCells code scheme) →
      (candidateEntry : VerifiedEntry (manifest := manifest)
        (registry := registry) (clauseEvidence := clauseEvidence)
        (family := family) (headerCells := headerCells) (C := code)) →
      EntryAt (SCommit := scheme) candidateHead candidateEntry → Digest → Prop)
    (DurablyPersisted : Digest → Prop) : Prop where
  pcsOpeningSound : PCSOpeningSound childEntry.claim opening
  commitmentBinding : CommitmentBindingCR childEntry.claim
  fiatShamirROM : RandomOracleModel childEntry.claim
  externallyFinal : ExternallyFinal head childEntry childAt
    (childEntry.receiptRoot scheme)
  durablyPersisted : DurablyPersisted linkAccepted.accepted.prepared.post.root

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentLinkReopenWitness.commitWord_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commitWord_injective
/-- info: 'Minidregg.Assurance.HyperdocumentLinkReopenWitness.child_index_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms child_index_exact
/-- info: 'Minidregg.Assurance.HyperdocumentLinkReopenWitness.opening_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms opening_exact
/-- info: 'Minidregg.Assurance.HyperdocumentLinkReopenWitness.query_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms query_exact
/-- info: 'Minidregg.Assurance.HyperdocumentLinkReopenWitness.wrong_header_cannot_masquerade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_header_cannot_masquerade

end

end Minidregg.Assurance.HyperdocumentLinkReopenWitness
