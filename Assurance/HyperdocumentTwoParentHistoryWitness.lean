/-
# Assurance.HyperdocumentTwoParentHistoryWitness -- the merge reaches history

The kernel witness builds a real base with two concurrent children, preserves
both alternatives in one `ConflictRecord`, appends the derived version event,
and publishes content plus event-log cells atomically.  This module carries
that exact merge one layer farther:

* a nonempty canonical post layout assigns a real post coordinate to the
  committed conflict cell;
* the exact derived `HyperdocumentVersionEffects.Config` and event record are
  retained by a verified history entry;
* the entry is appended after a base entry to a built `VerifiedHistoryHead`,
  with an explicit `Fin` index and exact lookup proof;
* an honest finite-word commitment authenticates the conflict coordinate, and
  the canonical opening is tied to the same concrete `ConflictRecord` proved
  present in the atomically committed content post.

The commitment is the non-succinct injective witness from
`HistoryHeadInhabitation`.  This is therefore semantic authentication, not a
claim about a deployed PCS, finality protocol, collision-resistant digest, or
random-oracle transcript.  Those physical and cryptographic obligations stay
outside this witness rather than being hidden behind an empty layout.
-/
import Assurance.HistoryHeadInhabitation
import Assurance.HyperdocumentHistoryAdmission
import Kernel.HyperdocumentTwoParentWitness

namespace Minidregg.Assurance.HyperdocumentTwoParentHistoryWitness

open Minidregg.Assurance.HyperdocumentHistoryAdmission
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.TransclusionBacklinkHistory
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Kernel
open Minidregg.Loom
open Minidregg.Theory
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.TypedAuthorization

namespace Merge
export Minidregg.Kernel.HyperdocumentTwoParentWitness
  (eventConfig mergeAccepted logCell baseRecord baseCell commit plan
    mergeConfig mergeDeclaration atomic_content_conflict)
noncomputable def authorityPre :=
  Minidregg.Theory.HyperdocumentCausalFamily.Witness.authorityPre
end Merge

namespace HeadWitness
export Minidregg.Assurance.HistoryHeadInhabitation (Fld scheme commitWord)
end HeadWitness

set_option autoImplicit false

noncomputable section

/-! ## Exact event configuration and one-cell semantic carrier -/

abbrev Fld := HeadWitness.Fld

/-- The exact version-event configuration used by the atomic merge
publication, retained here rather than replaced by a parallel history codec. -/
noncomputable def versionConfig : HyperdocumentVersionEffects.Config :=
  Merge.eventConfig

theorem versionConfig_nonempty :
    Nonempty HyperdocumentVersionEffects.Config :=
  ⟨versionConfig⟩

noncomputable def mergeEventDeclaration :
    HyperdocumentVersionEffects.Declaration :=
  HyperdocumentMergePublication.derivedEventDeclaration
    Merge.mergeAccepted Merge.logCell.root

@[simp] theorem merge_event_record_exact :
    mergeEventDeclaration.record =
      HyperdocumentMerge.recordOfAccepted Merge.mergeAccepted :=
  rfl

/-- One semantic coordinate is enough for this narrow opening: zero before
the merge and one after the conflict is retained. -/
noncomputable def emptyState : Fin 1 → Fld := fun _ => 0

noncomputable def conflictState : Fin 1 → Fld := fun _ => 1

noncomputable def baseDelta : ReceiptDelta emptyState emptyState where
  touched := ∅
  frame := by simp

noncomputable def mergeDelta : ReceiptDelta emptyState conflictState where
  touched := {⟨0, by decide⟩}
  frame := by
    intro index outside
    have indexExact : index = ⟨0, by decide⟩ := Subsingleton.elim _ _
    subst index
    simp at outside

noncomputable def headerCells : HistoryAdmissionContext → BindingIx → Fld :=
  fun _ _ => 0

noncomputable def baseWitness : BoundReceiptWitness 1 Fld where
  binding := fun _ => 0
  core := ReceiptWitness.ofDelta baseDelta

noncomputable def mergeWitness : BoundReceiptWitness 1 Fld where
  binding := fun _ => 0
  core := ReceiptWitness.ofDelta mergeDelta

noncomputable def baseClaim : BoundSemanticReceiptClaim 1 Fld where
  witness := baseWitness
  valid := ReceiptWitness.ofDelta_satisfies baseDelta

noncomputable def mergeClaim : BoundSemanticReceiptClaim 1 Fld where
  witness := mergeWitness
  valid := ReceiptWitness.ofDelta_satisfies mergeDelta

/-! ## A closed manifest and exact merge-event entry -/

noncomputable def manifest : Manifest where
  manifestVersion := 1
  abiId := ⟨710⟩
  semanticProgramId := ⟨711⟩
  semanticRelationId := versionConfig.semanticRelation
  receiptCodecId := ⟨712⟩
  codecs := []
  carriers := []
  bridges := []
  dialectClauses := []
  transcriptControllerDigest := ⟨713⟩
  dimensions := []
  bounds := []

noncomputable def registry : ControllerRegistry.{0, 0, 0, 0} := ⟨[]⟩

noncomputable def clauseEvidence : ClauseEvidenceFamily manifest registry where
  Evidence := fun _ _ _ => PEmpty.{1}

noncomputable def code : Submodule Fld (BoundReceiptIx 1 → Fld) := ⊤

noncomputable def baseContext : HistoryAdmissionContext where
  manifestAddress := manifest.contentAddress
  historyDomain := mergeEventDeclaration.record.historyDomain
  sequence := 0
  previousReceiptRoot := none
  semanticObjectRoot := Merge.baseRecord.effectId
  semanticRelationId := versionConfig.semanticRelation
  outcome := .committed
  preStateRoot := Merge.baseCell.root
  postStateRoot := Merge.baseCell.root
  effectRoot := Merge.baseRecord.effectId
  authorizationRoot := Merge.authorityPre.root
  disclosureRoot := ⟨0⟩
  dialectClauseRoots := []

noncomputable def baseContextWellFormed : baseContext.WellFormed manifest where
  manifestExact := rfl
  semanticRelationExact := rfl
  historyLink := .inl ⟨rfl, rfl⟩
  rejectedAtomic := trivial
  dialectClauseIdsUnique := List.nodup_nil
  dialectClausesClosed := fun _roots absent => absurd absent List.not_mem_nil

/- The predecessor root is derived from the exact base word under the same
commitment later retained by the head. -/
noncomputable def baseReceiptRoot : Digest :=
  HeadWitness.scheme.commit baseClaim.witness.encode

noncomputable def mergeContext : HistoryAdmissionContext where
  manifestAddress := manifest.contentAddress
  historyDomain := mergeEventDeclaration.record.historyDomain
  sequence := 1
  previousReceiptRoot := some baseReceiptRoot
  semanticObjectRoot := mergeEventDeclaration.record.effectId
  semanticRelationId := versionConfig.semanticRelation
  outcome := .committed
  preStateRoot := Merge.baseCell.root
  postStateRoot := (Merge.commit.post .content).root
  effectRoot := mergeEventDeclaration.effectDigest versionConfig
  authorizationRoot := Merge.authorityPre.root
  disclosureRoot := ⟨0⟩
  dialectClauseRoots := []

noncomputable def mergeContextWellFormed :
    mergeContext.WellFormed manifest where
  manifestExact := rfl
  semanticRelationExact := rfl
  historyLink := .inr ⟨by decide, ⟨baseReceiptRoot, rfl⟩⟩
  rejectedAtomic := trivial
  dialectClauseIdsUnique := List.nodup_nil
  dialectClausesClosed := fun _roots absent => absurd absent List.not_mem_nil

/-- Only these two exact context/claim pairs inhabit the history family.  The
merge constructor therefore retains the actual derived event declaration and
the actual accepted two-parent merge by definitional equality. -/
inductive EventEvidence :
    HistoryAdmissionContext → BoundSemanticReceiptClaim 1 Fld → Type
  | base : EventEvidence baseContext baseClaim
  | merge : EventEvidence mergeContext mergeClaim

noncomputable def family : EntrySemanticsFamily 1 Fld where
  Evidence := EventEvidence
  rejectedCoreAtomic := by
    intro context claim evidence denial rejected
    cases evidence with
    | base => cases rejected
    | merge => cases rejected

noncomputable def baseEntry : VerifiedEntry
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := code) where
  context := baseContext
  claim := baseClaim
  semantics := .base
  contextWellFormed := baseContextWellFormed
  dialectEvidence := ⟨fun index => index.elim0, fun index => index.elim0⟩
  bindingExact := rfl
  codeword := Submodule.mem_top

noncomputable def mergeEntry : VerifiedEntry
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := code) where
  context := mergeContext
  claim := mergeClaim
  semantics := .merge
  contextWellFormed := mergeContextWellFormed
  dialectEvidence := ⟨fun index => index.elim0, fun index => index.elim0⟩
  bindingExact := rfl
  codeword := Submodule.mem_top

@[simp] theorem merge_entry_event_record :
    mergeEntry.context.semanticObjectRoot = mergeEventDeclaration.record.effectId :=
  rfl

@[simp] theorem merge_entry_content_post :
    mergeEntry.context.postStateRoot = (Merge.commit.post .content).root :=
  rfl

/-! ## The merge event is really appended to a verified head -/

noncomputable def foldRoot : Digest → Fld → Digest → Digest :=
  fun _ _ _ => HeadWitness.commitWord
    (baseEntry.word + (1 : Fld) • mergeEntry.word)

noncomputable def baseHead : VerifiedHistoryHead manifest registry
    clauseEvidence family headerCells code HeadWitness.scheme :=
  VerifiedHistoryHead.start manifest registry clauseEvidence family
    headerCells code HeadWitness.scheme foldRoot baseEntry rfl rfl

noncomputable def appendLink : VerifiedHistoryHead.AppendLink manifest registry
    clauseEvidence family headerCells code HeadWitness.scheme baseHead
    mergeEntry where
  historyDomainExact := rfl
  sequenceExact := rfl
  predecessorExact := rfl
  stateExact := rfl

noncomputable def foldRecommitment :
    VerifiedHistoryHead.FoldRecommitment manifest registry clauseEvidence
      family headerCells code HeadWitness.scheme baseHead mergeEntry 1 where
  rootExact := rfl

noncomputable def head : VerifiedHistoryHead manifest registry clauseEvidence
    family headerCells code HeadWitness.scheme :=
  VerifiedHistoryHead.append manifest registry clauseEvidence family
    headerCells code HeadWitness.scheme baseHead mergeEntry 1 appendLink
    foldRecommitment

@[simp] theorem head_entries : head.entries = [baseEntry, mergeEntry] := rfl

@[simp] theorem head_latest : head.latest = mergeEntry := rfl

/-- The exact retained index of the merge event. -/
noncomputable def mergePosition : EntryAt head mergeEntry where
  index := ⟨1, by decide⟩
  entryExact := rfl

theorem merge_entry_is_retained : mergeEntry ∈ head.entries :=
  mergePosition.mem

@[simp] theorem merge_entry_index_exact :
    head.entries.get mergePosition.index = mergeEntry :=
  mergePosition.entryExact

/-! ## A nonempty canonical conflict layout and exact opening -/

noncomputable def conflictId : ConflictId :=
  Merge.plan.conflictId Merge.mergeConfig
    (Merge.mergeDeclaration.operationId Merge.mergeConfig)

noncomputable def conflictRecord : ConflictRecord :=
  Merge.plan.conflictRecord
    (Merge.mergeDeclaration.operationId Merge.mergeConfig)

noncomputable def conflictCell : PostCell where
  space := .conflicts
  key := conflictId
  value := some conflictRecord

noncomputable def conflictSpan : PostSpan 1 where
  start := 0
  width := 1
  withinBounds := by decide

/-- This layout has literal support one, a nonempty span, and an injective
encoding.  It cannot discharge its obligations through `Fin 0`. -/
noncomputable def layout : CanonicalPostLayout 1 Fld where
  cellCount := 1
  cellAt := fun _ => conflictCell
  cellAtInjective := fun _ _ _ => Subsingleton.elim _ _
  spanAt := fun _ => conflictSpan
  encodeAt := fun _ => [1]
  encodedLength := by intro slot; rfl
  spanNonempty := by intro slot; decide
  encodeAtInjective := fun _ _ _ => Subsingleton.elim _ _
  spansDisjoint := by
    intro left right different
    exact (different (Subsingleton.elim left right)).elim

theorem layout_has_support : 0 < layout.cellCount := by decide

theorem canonical_layout_nonempty :
    Nonempty (CanonicalPostLayout 1 Fld) :=
  ⟨layout⟩

theorem layout_nonempty : Nonempty (Fin layout.cellCount) :=
  ⟨⟨0, by decide⟩⟩

noncomputable def conflictSlot : Fin layout.cellCount := ⟨0, by decide⟩

noncomputable def conflictCoordinate : BoundReceiptIx 1 :=
  .inr (⟨0, by decide⟩, .post)

noncomputable def conflictOpening : RangeOrValueOpening 1 Fld where
  shape := .value
  coordinates := layout.boundCoordinates conflictSlot
  cells := layout.encodeAt conflictSlot

@[simp] theorem conflict_opening_coordinates :
    conflictOpening.coordinates = [conflictCoordinate] := by
  rfl

@[simp] theorem conflict_opening_cells :
    conflictOpening.cells = [1] := rfl

@[simp] theorem conflict_coordinate_value :
    mergeEntry.word conflictCoordinate = 1 := by
  rfl

noncomputable def canonicalConflictOpening :
    CanonicalPostOpening layout mergeEntry conflictOpening where
  sourceSlots := [conflictSlot]
  coordinatesExact := rfl
  coordinatesPostOnly := by
    intro coordinate member
    rw [conflict_opening_coordinates] at member
    simp only [List.mem_singleton] at member
    subst coordinate
    exact ⟨conflictSlot, by simp, ⟨0, by decide⟩, by simp [layout, conflictSpan,
      PostSpan.coordinates, PostSpan.coordinate], rfl⟩
  noHeaderCoordinate := by
    intro coordinate member header
    rw [conflict_opening_coordinates] at member
    simp only [List.mem_singleton] at member
    subst coordinate
    intro masquerades
    cases masquerades
  noPreCoordinate := by
    intro coordinate member key
    rw [conflict_opening_coordinates] at member
    simp only [List.mem_singleton] at member
    subst coordinate
    intro masquerades
    cases masquerades
  noTouchedCoordinate := by
    intro coordinate member key
    rw [conflict_opening_coordinates] at member
    simp only [List.mem_singleton] at member
    subst coordinate
    intro masquerades
    cases masquerades
  cellsExact := rfl
  openingExact :=
    { cellsExact := by
        rw [conflict_opening_cells, conflict_opening_coordinates]
        simp
      valueShape := by
        intro valueShape
        exact ⟨conflictCoordinate, conflict_opening_coordinates⟩
      rangeShape := by intro impossible; cases impossible }
  representedPostExact := by
    intro slot present
    simp only [List.mem_singleton] at present
    subst slot
    have finRangeExact : List.finRange 1 = [⟨0, by decide⟩] := by decide
    simp [layout, conflictSpan, PostSpan.coordinates, finRangeExact,
      mergeEntry, mergeClaim, mergeWitness, mergeDelta, conflictState,
      ReceiptWitness.ofDelta]
  valueShape := by intro _; exact ⟨conflictSlot, rfl⟩
  rangeShape := by intro impossible; cases impossible

/-! ## Authentication and concrete survival -/

@[simp] theorem committed_conflict_survives :
    lookup (Merge.commit.post .content).logical .conflicts conflictId =
      some conflictRecord :=
  Merge.atomic_content_conflict

/-- The typed cell named by the opening is the very lookup proved present in
the atomically committed post; the layout cannot swap in an unrelated value. -/
theorem opened_cell_is_committed_conflict :
    layout.cellAt conflictSlot =
      { space := .conflicts
        key := conflictId
        value := lookup (Merge.commit.post .content).logical .conflicts
          conflictId } := by
  rw [committed_conflict_survives]
  rfl

noncomputable def conflictProof : BoundReceiptIx 1 → Fld :=
  HeadWitness.scheme.openAt mergeEntry.word conflictCoordinate

/-- The honest commitment checks the exact post coordinate opened above at
the exact receipt root retained by the head entry. -/
theorem conflict_opening_authenticated :
    HeadWitness.scheme.verifyOpen
      (mergeEntry.receiptRoot HeadWitness.scheme) conflictCoordinate 1
      conflictProof := by
  simpa [conflictProof, conflict_coordinate_value] using
    (HeadWitness.scheme.verifyOpen_commit mergeEntry.word conflictCoordinate)

/-- The complete non-vacuity package: an exact version-effects configuration,
its derived merge declaration, proof-relevant head position, canonical post
opening, honest commitment verification, and the concrete committed record. -/
structure ExactConflictHistoryWitness where
  config : HyperdocumentVersionEffects.Config
  configured : config = versionConfig
  event : HyperdocumentVersionEffects.Declaration
  eventExact : event = mergeEventDeclaration
  retained : EntryAt head mergeEntry
  canonical : CanonicalPostOpening layout mergeEntry conflictOpening
  authenticated : HeadWitness.scheme.verifyOpen
    (mergeEntry.receiptRoot HeadWitness.scheme) conflictCoordinate 1
    conflictProof
  committed :
    lookup (Merge.commit.post .content).logical .conflicts conflictId =
      some conflictRecord

noncomputable def exactConflictHistoryWitness : ExactConflictHistoryWitness where
  config := versionConfig
  configured := rfl
  event := mergeEventDeclaration
  eventExact := rfl
  retained := mergePosition
  canonical := canonicalConflictOpening
  authenticated := conflict_opening_authenticated
  committed := committed_conflict_survives

theorem exact_conflict_history_nonempty :
    Nonempty ExactConflictHistoryWitness :=
  ⟨exactConflictHistoryWitness⟩

/-! ## Anti-masquerade, stale-head, and wrong-coordinate teeth -/

noncomputable def missingConflictCell : PostCell where
  space := .conflicts
  key := conflictId
  value := none

theorem missing_value_cannot_masquerade :
    missingConflictCell ≠ layout.cellAt conflictSlot := by
  simp [missingConflictCell, layout, conflictCell]

theorem same_encoding_identifies_conflict
    (other : Fin layout.cellCount)
    (same : layout.encodeAt other = layout.encodeAt conflictSlot) :
    layout.cellAt other = conflictCell := by
  have slotExact : other = conflictSlot := layout.encodeAtInjective same
  subst other
  rfl

/-- The predecessor head does not contain the merge entry.  Exact-head
membership therefore cannot be replayed against the stale base head. -/
theorem stale_head_rejects_merge : IsEmpty (EntryAt baseHead mergeEntry) := by
  constructor
  intro position
  have member := position.mem
  change mergeEntry ∈ [baseEntry] at member
  simp only [List.mem_singleton] at member
  have sequences := congrArg (fun entry => entry.context.sequence) member
  norm_num [mergeEntry, mergeContext, baseEntry, baseContext] at sequences

/-- Any coordinate other than the exact post coordinate is rejected by the
opening's singleton support. -/
theorem wrong_coordinate_rejected
    (coordinate : BoundReceiptIx 1)
    (wrong : coordinate ≠ conflictCoordinate) :
    coordinate ∉ conflictOpening.coordinates := by
  rw [conflict_opening_coordinates]
  simpa using wrong

theorem pre_coordinate_rejected (key : Fin 1) :
    (.inr (key, .pre) : BoundReceiptIx 1) ∉ conflictOpening.coordinates := by
  apply wrong_coordinate_rejected
  intro masquerades
  cases masquerades

theorem touched_coordinate_rejected (key : Fin 1) :
    (.inr (key, .touched) : BoundReceiptIx 1) ∉
      conflictOpening.coordinates := by
  apply wrong_coordinate_rejected
  intro masquerades
  cases masquerades

theorem header_coordinate_rejected (key : BindingIx) :
    (.inl key : BoundReceiptIx 1) ∉ conflictOpening.coordinates := by
  apply wrong_coordinate_rejected
  intro masquerades
  cases masquerades

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.HyperdocumentTwoParentHistoryWitness.merge_entry_index_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms merge_entry_index_exact
/-- info: 'Minidregg.Assurance.HyperdocumentTwoParentHistoryWitness.conflict_opening_authenticated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms conflict_opening_authenticated
/-- info: 'Minidregg.Assurance.HyperdocumentTwoParentHistoryWitness.committed_conflict_survives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms committed_conflict_survives
/-- info: 'Minidregg.Assurance.HyperdocumentTwoParentHistoryWitness.stale_head_rejects_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_head_rejects_merge

end

end Minidregg.Assurance.HyperdocumentTwoParentHistoryWitness
