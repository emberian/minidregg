/-
# Kernel.HyperdocumentTwoParentWitness -- a built concurrent merge turn

This file is the positive, deployed-schema witness for the Hyperdocument merge
surface.  It constructs a three-node causal history (one base and two current
siblings), materializes a different provenance-bearing value on each sibling,
selects their actual admitted common base, accepts the canonical two-source
conflict patch, appends the derived causal record to the sparse event log, and
commits the content and event incidences atomically.

The digest and codecs are deliberately the countability/byte-length witnesses
used elsewhere for carrier inhabitation.  Consequently this proves semantic
wiring and non-vacuity, not collision resistance, finality, or physical
durability.  Those ceilings remain explicit at the handler boundary.
-/
import Kernel.DeployedMaterializerWitness
import Kernel.HyperdocumentMergeAncestry
import Kernel.DurableDataIntent
import Theory.HyperdocumentCausalFamily

namespace Minidregg.Kernel.HyperdocumentTwoParentWitness

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.DeployedMaterializerWitness
open Minidregg.Theory.HyperdocumentCausalFamily.Witness
open Minidregg.Kernel.DeployedMaterializerWitness

set_option autoImplicit false

noncomputable section

/-! ## A merge-capable causal family over exact Hyperdocument cells -/

/-- Semantic evidence names the exact materialized input and output cells.
This is the multi-parent counterpart of `HyperdocumentCausalFamily.EventEvidence`;
the actual merge event below is additionally backed by `HyperdocumentMerge.Accepted`. -/
structure EventEvidence (event : CausalVersionDag.EventPreimage) where
  before : Hyperdocument.Cell hyperdocumentMaterializer
  after : Hyperdocument.Cell hyperdocumentMaterializer
  preRootExact : before.root = event.preStateRoot
  postRootExact : after.root = event.postStateRoot

/-- This witness family admits genesis, ordinary linear children, and an exact
two-parent join.  The general merge implementation still retains the stronger
parent-content, common-base, authorization, and accepted-patch evidence. -/
inductive ParentCompatible :
    List CausalVersionDag.EventPreimage -> CausalVersionDag.EventPreimage -> Type
  | genesis (child) (empty : child.parentFrontier = []) :
      ParentCompatible [] child
  | linear (parent child) (rootExact : parent.postStateRoot = child.preStateRoot) :
      ParentCompatible [parent] child
  | binary (left right child)
      (parentsExact : child.parentFrontier =
        [left.effectId, right.effectId]) :
      ParentCompatible [left, right] child

noncomputable def family : CausalVersionDag.SemanticFamily
    (Hyperdocument.Cell hyperdocumentMaterializer) where
  Evidence := EventEvidence
  ParentCompatible := ParentCompatible
  root := fun cell => cell.root
  Step := fun event before after =>
    ∃ evidence : EventEvidence event,
      before = evidence.before /\ after = evidence.after
  stepPreRoot := by
    intro event before after evidence step
    rcases step with ⟨witness, rfl, rfl⟩
    exact witness.preRootExact
  stepPostRoot := by
    intro event before after evidence step
    rcases step with ⟨witness, rfl, rfl⟩
    exact witness.postRootExact

/-- Addressing exposes the event's already domain-separated effect identity.
The codec still round-trips the complete preimage; malformed bytes map to zero.
This is transparent witness addressing, not a cryptographic hash. -/
noncomputable def eventDigest (bytes : List UInt8) : Digest :=
  match decodePreimage .v1 .versionEvent bytes with
  | some envelope =>
      match eventCodec.decode envelope.payload with
      | some event => event.effectId
      | none => ⟨0⟩
  | none => ⟨0⟩

noncomputable def eventDerivation : DigestDerivation where
  digestBytes := eventDigest

noncomputable def addressing : CausalVersionDag.ContentAddressing :=
  causalVersionAddressing eventCodec eventDerivation

@[simp] theorem address_exact (event : CausalVersionDag.EventPreimage) :
    addressing.address event = event.effectId := by
  simp [addressing, causalVersionAddressing, eventDerivation, eventDigest,
    CausalVersionDag.ContentAddressing.address]
  rw [eventCodec.decode_encode]

/-! ## One base and two exact sibling states -/

noncomputable def field : FieldKey :=
  { owner := .document documentId, name := ⟨800⟩ }

noncomputable def baseOperation : OperationId := ⟨⟨100⟩⟩
noncomputable def leftOperation : OperationId := ⟨⟨200⟩⟩
noncomputable def rightOperation : OperationId := ⟨⟨300⟩⟩

noncomputable def leftAlternative : ConflictAlternative where
  valueType := .text
  value := [0x6c, 0x65, 0x66, 0x74]
  author := author
  operation := leftOperation

noncomputable def rightAlternative : ConflictAlternative where
  valueType := .text
  value := [0x72, 0x69, 0x67, 0x68, 0x74]
  author := author
  operation := rightOperation

noncomputable def sourceRecord (alternative : ConflictAlternative) : FieldRecord where
  valueType := alternative.valueType
  value := alternative.value
  merge := .multiValue
  writtenBy := alternative.author
  writtenAt := alternative.operation

noncomputable def baseCell : Hyperdocument.Cell hyperdocumentMaterializer :=
  hyperdocumentCell

noncomputable def leftLogical : LogicalState cellSchema :=
  { baseCell.logical with
    fields := baseCell.logical.fields.write ⟨.fields, field⟩
      (sourceRecord leftAlternative) }

noncomputable def rightLogical : LogicalState cellSchema :=
  { baseCell.logical with
    fields := baseCell.logical.fields.write ⟨.fields, field⟩
      (sourceRecord rightAlternative) }

noncomputable def leftCell : Hyperdocument.Cell hyperdocumentMaterializer :=
  CellState.materialize hyperdocumentMaterializer leftLogical

noncomputable def rightCell : Hyperdocument.Cell hyperdocumentMaterializer :=
  CellState.materialize hyperdocumentMaterializer rightLogical

@[simp] theorem left_opened :
    lookup leftCell.logical .fields field = some (sourceRecord leftAlternative) := by
  exact FieldStore.write_self _ _ _

@[simp] theorem right_opened :
    lookup rightCell.logical .fields field = some (sourceRecord rightAlternative) := by
  exact FieldStore.write_self _ _ _

noncomputable def baseRecord : VersionEventRecord where
  historyDomain := ⟨15⟩
  document := documentId
  schema := { schemaId := ⟨14⟩, version := 1 }
  semanticVersion := 0
  operation := baseOperation
  parents := []
  preStateRoot := baseCell.root
  postStateRoot := baseCell.root
  requestId := ⟨101⟩
  effectId := ⟨100⟩
  author := author

noncomputable def baseId : VersionEventId := ⟨⟨100⟩⟩

noncomputable def leftRecord : VersionEventRecord where
  historyDomain := ⟨15⟩
  document := documentId
  schema := { schemaId := ⟨14⟩, version := 1 }
  semanticVersion := 1
  operation := leftOperation
  parents := [baseId]
  preStateRoot := baseCell.root
  postStateRoot := leftCell.root
  requestId := ⟨201⟩
  effectId := ⟨200⟩
  author := author

noncomputable def rightRecord : VersionEventRecord where
  historyDomain := ⟨15⟩
  document := documentId
  schema := { schemaId := ⟨14⟩, version := 1 }
  semanticVersion := 1
  operation := rightOperation
  parents := [baseId]
  preStateRoot := baseCell.root
  postStateRoot := rightCell.root
  requestId := ⟨301⟩
  effectId := ⟨300⟩
  author := author

noncomputable def addressed (record : VersionEventRecord) (wellFormed : record.CausallyWellFormed) :
    CausalVersionDag.AddressedEvent addressing where
  preimage := record.toCausalPreimage
  entryId := record.effectId
  entryIdExact := by simp [address_exact, VersionEventRecord.toCausalPreimage]
  wellFormed := wellFormed

noncomputable def baseWellFormed : baseRecord.CausallyWellFormed := by
  constructor <;> simp [baseRecord, VersionEventRecord.toCausalPreimage]

noncomputable def leftWellFormed : leftRecord.CausallyWellFormed := by
  constructor <;> simp [leftRecord, baseId, VersionEventRecord.toCausalPreimage]

noncomputable def rightWellFormed : rightRecord.CausallyWellFormed := by
  constructor <;> simp [rightRecord, baseId, VersionEventRecord.toCausalPreimage]

noncomputable def baseEvidence : EventEvidence baseRecord.toCausalPreimage :=
  ⟨baseCell, baseCell, rfl, rfl⟩

noncomputable def leftEvidence : EventEvidence leftRecord.toCausalPreimage :=
  ⟨baseCell, leftCell, rfl, rfl⟩

noncomputable def rightEvidence : EventEvidence rightRecord.toCausalPreimage :=
  ⟨baseCell, rightCell, rfl, rfl⟩

noncomputable def baseNode : CausalVersionDag.VerifiedEvent addressing family :=
  ⟨addressed baseRecord baseWellFormed, baseEvidence⟩

noncomputable def leftNode : CausalVersionDag.VerifiedEvent addressing family :=
  ⟨addressed leftRecord leftWellFormed, leftEvidence⟩

noncomputable def rightNode : CausalVersionDag.VerifiedEvent addressing family :=
  ⟨addressed rightRecord rightWellFormed, rightEvidence⟩

@[simp] theorem baseNode_preimage : baseNode.preimage = baseRecord.toCausalPreimage := rfl
@[simp] theorem leftNode_preimage : leftNode.preimage = leftRecord.toCausalPreimage := rfl
@[simp] theorem rightNode_preimage : rightNode.preimage = rightRecord.toCausalPreimage := rfl
@[simp] theorem baseNode_entryId : baseNode.entryId = ⟨100⟩ := rfl
@[simp] theorem leftNode_entryId : leftNode.entryId = ⟨200⟩ := rfl
@[simp] theorem rightNode_entryId : rightNode.entryId = ⟨300⟩ := rfl
@[simp] theorem baseNode_requestId : baseNode.requestId = ⟨101⟩ := rfl
@[simp] theorem leftNode_requestId : leftNode.requestId = ⟨201⟩ := rfl
@[simp] theorem rightNode_requestId : rightNode.requestId = ⟨301⟩ := rfl
@[simp] theorem baseNode_effectId : baseNode.effectId = ⟨100⟩ := rfl
@[simp] theorem leftNode_effectId : leftNode.effectId = ⟨200⟩ := rfl
@[simp] theorem rightNode_effectId : rightNode.effectId = ⟨300⟩ := rfl

noncomputable def anchor : CausalVersionDag.Anchor :=
  { historyDomain := ⟨15⟩, streamId := documentId.digest }

noncomputable def baseValid : CausalVersionDag.ValidAppend anchor [] baseNode where
  anchorExact := ⟨rfl, rfl⟩
  genesisShape := .inl ⟨rfl, rfl, rfl⟩
  resolvedParents := []
  resolvedParentsExact := rfl
  resolvedParentsPresent := by simp
  parentAnchorExact := by simp
  parentSchemaExact := by simp
  schemaVersionMonotone := by simp
  semanticVersionIncreases := by simp
  entryFresh := by simp
  requestFresh := by simp
  effectFresh := by simp
  parentCompatibility := .genesis _ rfl

noncomputable def leftValid : CausalVersionDag.ValidAppend anchor [baseNode] leftNode where
  anchorExact := ⟨rfl, rfl⟩
  genesisShape := .inr ⟨by simp, by simp [leftRecord,
    VersionEventRecord.toCausalPreimage, baseId]⟩
  resolvedParents := [baseNode]
  resolvedParentsExact := rfl
  resolvedParentsPresent := by simp
  parentAnchorExact := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    exact ⟨rfl, rfl⟩
  parentSchemaExact := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    rfl
  schemaVersionMonotone := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    exact Nat.le_refl 1
  semanticVersionIncreases := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    exact Nat.zero_lt_succ 0
  entryFresh := by simp
  requestFresh := by simp
  effectFresh := by simp
  parentCompatibility := .linear _ _ rfl

noncomputable def rightValid : CausalVersionDag.ValidAppend anchor [baseNode, leftNode] rightNode where
  anchorExact := ⟨rfl, rfl⟩
  genesisShape := .inr ⟨by simp, by simp [rightRecord,
    VersionEventRecord.toCausalPreimage, baseId]⟩
  resolvedParents := [baseNode]
  resolvedParentsExact := rfl
  resolvedParentsPresent := by simp
  parentAnchorExact := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    exact ⟨rfl, rfl⟩
  parentSchemaExact := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    rfl
  schemaVersionMonotone := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    decide
  semanticVersionIncreases := by
    intro parent present
    simp only [List.mem_singleton] at present
    subst parent
    decide
  entryFresh := by
    intro old present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;>
      simp
  requestFresh := by
    intro old present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;>
      simp
  effectFresh := by
    intro old present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;>
      simp
  parentCompatibility := .linear _ _ rfl

noncomputable def baseHistory : CausalVersionDag.History (scheme := addressing)
    (family := family) anchor :=
  (CausalVersionDag.History.empty anchor).append baseNode baseValid

noncomputable def leftHistory : CausalVersionDag.History (scheme := addressing)
    (family := family) anchor :=
  baseHistory.append leftNode leftValid

noncomputable def history : CausalVersionDag.History (scheme := addressing)
    (family := family) anchor :=
  leftHistory.append rightNode rightValid

@[simp] theorem history_events : history.events = [baseNode, leftNode, rightNode] :=
  rfl

@[simp] theorem current_frontier :
    CausalVersionDag.frontier history.events = {leftNode.entryId, rightNode.entryId} := by
  ext id
  simp [history, leftHistory, baseHistory, CausalVersionDag.frontier,
    CausalVersionDag.frontierStep, CausalVersionDag.History.empty, baseRecord,
    leftRecord, rightRecord, baseId, VersionEventRecord.toCausalPreimage]
  constructor <;> aesop

/-! ## Canonical merge declaration and actual parent/base evidence -/

deriving instance Countable for HyperdocumentMerge.Parent
deriving instance Countable for HyperdocumentMerge.FieldSource
deriving instance Countable for HyperdocumentMerge.FieldPlan
deriving instance Countable for HyperdocumentMerge.StableOverlay
deriving instance Countable for HyperdocumentMerge.Body
deriving instance Countable for HyperdocumentMerge.Declaration
deriving instance Countable for HyperdocumentMerge.ConflictKeyPreimage
deriving instance Countable for HyperdocumentVersionEffects.Declaration
deriving instance Nonempty for FieldOwner
deriving instance Nonempty for FieldKey
deriving instance Nonempty for VersionEventRecord
deriving instance Nonempty for HyperdocumentMerge.Body
deriving instance Nonempty for HyperdocumentMerge.Declaration
deriving instance Nonempty for HyperdocumentMerge.ConflictKeyPreimage
deriving instance Nonempty for HyperdocumentVersionEffects.Declaration

local instance : DecidableEq HyperdocumentMerge.Parent := Classical.decEq _

noncomputable def bodyCodec : LawfulCodec HyperdocumentMerge.Body := codecOfCountable HyperdocumentMerge.Body
noncomputable def mergeDeclarationCodec : LawfulCodec HyperdocumentMerge.Declaration :=
  codecOfCountable HyperdocumentMerge.Declaration
noncomputable def conflictKeyCodec : LawfulCodec HyperdocumentMerge.ConflictKeyPreimage :=
  codecOfCountable HyperdocumentMerge.ConflictKeyPreimage

noncomputable def mergeConfig : HyperdocumentMerge.Config where
  bodyCodec := bodyCodec
  declarationCodec := mergeDeclarationCodec
  requestCodec := requestCodec
  conflictKeyCodec := conflictKeyCodec
  intentAddressing := { codec := intentCodec, derivation := derivation }
  conflictDerivation := derivation
  effectDerivation := derivation
  requestDerivation := derivation
  requestDomain := ⟨700⟩
  semanticRelation := ⟨702⟩

noncomputable def leftParent : HyperdocumentMerge.Parent := ⟨⟨⟨200⟩⟩, leftRecord⟩
noncomputable def rightParent : HyperdocumentMerge.Parent := ⟨⟨⟨300⟩⟩, rightRecord⟩

noncomputable def leftSource : HyperdocumentMerge.FieldSource :=
  ⟨leftParent.key, leftAlternative⟩

noncomputable def rightSource : HyperdocumentMerge.FieldSource :=
  ⟨rightParent.key, rightAlternative⟩

noncomputable def plan : HyperdocumentMerge.FieldPlan where
  field := field
  expected := none
  base := some baseId
  regime := .multiValue
  sources := [leftSource, rightSource]

noncomputable def body : HyperdocumentMerge.Body where
  parents := [leftParent, rightParent]
  fields := [plan]
  overlays := []

noncomputable def mergeIntent : HyperdocumentOperationIntent.OperationIntent where
  historyDomain := ⟨15⟩
  document := documentId
  schema := { schemaId := ⟨14⟩, version := 1 }
  semanticVersion := 2
  parents := [leftParent.key, rightParent.key]
  author := author
  expectedContentRoot := baseCell.root
  nonce := 400
  actionBytes := bodyCodec.encode body

noncomputable def mergeDeclaration : HyperdocumentMerge.Declaration where
  intent := mergeIntent
  request := requestEnvelope
  body := body

noncomputable def mergeSemantic : HyperdocumentMerge.ValidMerge mergeConfig baseCell mergeDeclaration where
  actionBytesExact := rfl
  objectCapability := rfl
  preRootExact := rfl
  atLeastTwoParents := ⟨leftParent, rightParent, [], rfl⟩
  parentOrder := by
    change HyperdocumentMerge.Parent.CanonicalOrder [leftParent, rightParent]
    simp [leftParent, rightParent, HyperdocumentMerge.Parent.CanonicalOrder,
      HyperdocumentMerge.Parent.entryId]
  parentFrontierExact := rfl
  parentDocumentExact := by
    intro parent present
    change parent ∈ [leftParent, rightParent] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  parentSchemaExact := by
    intro parent present
    change parent ∈ [leftParent, rightParent] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> rfl
  parentVersionEarlier := by
    intro parent present
    change parent ∈ [leftParent, rightParent] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> decide
  fieldsValid := by
    intro selected present
    change selected ∈ [plan] at present
    simp only [List.mem_singleton] at present
    subst selected
    refine ⟨by simp [plan], ?_, ?_⟩
    · simp [plan, leftSource, rightSource, leftParent, rightParent]
    · intro source member
      change source ∈ [leftSource, rightSource] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨leftParent, by change leftParent ∈ [leftParent, rightParent]; simp,
          rfl, rfl, rfl⟩
      · exact ⟨rightParent, by change rightParent ∈ [leftParent, rightParent]; simp,
          rfl, rfl, rfl⟩
  fieldsUnique := by change [field].Nodup; simp
  overlaysExact := by
    intro overlay present
    change overlay ∈ [] at present
    simp at present
  overlaysDocumentExact := by
    intro overlay present
    change overlay ∈ [] at present
    simp at present
  writesUnique := by
    simp [mergeDeclaration, body, plan, HyperdocumentMerge.Declaration.packedWrites,
      HyperdocumentMerge.FieldPlan.packedWrites,
      Minidregg.Theory.HyperdocumentOperations.PackedWrite.address]
  expectedExact := by
    intro write member
    simp [mergeDeclaration, body, plan, HyperdocumentMerge.Declaration.packedWrites,
      HyperdocumentMerge.FieldPlan.packedWrites] at member
    subst write
    rfl

noncomputable def parentEvidence :
    HyperdocumentMerge.CurrentParentEvidence (MDoc := hyperdocumentMaterializer)
      history mergeDeclaration.body.parents where
  resolved := [leftNode, rightNode]
  idsExact := rfl
  recordsExact := rfl
  admitted := by simp
  current := by
    intro node member
    rw [current_frontier]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp
  realization := fun parent _ =>
    if parent = leftParent then leftCell else rightCell
  realizationRootExact := by
    intro parent present
    change parent ∈ [leftParent, rightParent] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · rw [if_pos rfl]
      rfl
    · rw [if_neg]
      · rfl
      · intro equal
        have keys := congrArg (fun parent => parent.key.digest.value) equal
        norm_num [leftParent, rightParent] at keys

theorem base_resolved_left : baseNode ∈ leftValid.resolvedParents := by
  change baseNode ∈ [baseNode]
  simp

theorem base_resolved_right : baseNode ∈ rightValid.resolvedParents := by
  change baseNode ∈ [baseNode]
  simp

noncomputable def baseToLeft : CausalVersionAncestry.DirectParent history baseNode leftNode :=
  .earlier (.latest (CausalVersionDag.Builds.append
    (CausalVersionDag.Builds.empty) baseValid) leftValid base_resolved_left)

noncomputable def baseToRight : CausalVersionAncestry.DirectParent history baseNode rightNode :=
  .latest leftHistory.builds rightValid base_resolved_right

theorem base_reaches_resolved_nonempty
    (node : CausalVersionDag.VerifiedEvent addressing family)
    (present : node ∈ parentEvidence.resolved) :
    Nonempty (CausalVersionAncestry.Reaches history baseNode node) := by
  change node ∈ [leftNode, rightNode] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · exact ⟨.strict (.direct baseToLeft)⟩
  · exact ⟨.strict (.direct baseToRight)⟩

noncomputable def commonBase : HyperdocumentMerge.CommonBase parentEvidence where
  base := baseNode
  admitted := by simp
  reachesEvery := fun node present =>
    Classical.choice (base_reaches_resolved_nonempty node present)

theorem every_common_base_is_base
    (other : HyperdocumentMerge.CommonBase parentEvidence) :
    other.base = baseNode := by
  have admitted := other.admitted
  rw [history_events] at admitted
  simp only [List.mem_cons, List.not_mem_nil, or_false] at admitted
  rcases admitted with equal | equal | equal
  · exact equal
  · have reachesRight := other.reachesEvery rightNode (by
      change rightNode ∈ [leftNode, rightNode]
      simp)
    rw [equal] at reachesRight
    rcases reachesRight.eq_or_version_lt with same | less
    · have ids := congrArg CausalVersionDag.VerifiedEvent.entryId same
      simp at ids
    · change 1 < 1 at less
      omega
  · have reachesLeft := other.reachesEvery leftNode (by
      change leftNode ∈ [leftNode, rightNode]
      simp)
    rw [equal] at reachesLeft
    rcases reachesLeft.eq_or_version_lt with same | less
    · have ids := congrArg CausalVersionDag.VerifiedEvent.entryId same
      simp at ids
    · change 1 < 1 at less
      omega

noncomputable def lowestBase : HyperdocumentMerge.LowestCommonBase parentEvidence where
  selected := commonBase
  belowEvery := by
    intro other
    rw [every_common_base_is_base other]
    exact .refl (by simp)

noncomputable def selectedBase : HyperdocumentMerge.SelectedBase parentEvidence where
  causal := lowestBase
  realization := baseCell
  realizationRootExact := rfl

noncomputable def parentContent : HyperdocumentMerge.ParentContentEvidence parentEvidence where
  fieldSources := by
    intro selected selectedPresent source sourcePresent
    change selected ∈ [plan] at selectedPresent
    simp only [List.mem_singleton] at selectedPresent
    subst selected
    change source ∈ [leftSource, rightSource] at sourcePresent
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sourcePresent
    rcases sourcePresent with rfl | rfl
    · refine ⟨leftParent, by simp [mergeDeclaration, body], rfl, ?_⟩
      simp [parentEvidence, leftSource, plan,
        HyperdocumentMerge.FieldSource.toFieldRecord, sourceRecord]
    · refine ⟨rightParent, by simp [mergeDeclaration, body], rfl, ?_⟩
      simp [parentEvidence, rightSource, plan,
        HyperdocumentMerge.FieldSource.toFieldRecord, sourceRecord, leftParent,
        rightParent]
  stableOverlays := by simp [mergeDeclaration, body]

noncomputable def mergeCapabilityAdmissible :
    capability.Admissible
      (CredentialAuthorityState.authState projection authorityPre)
      (mergeDeclaration.toRequest mergeConfig) where
  holder := rfl
  scope :=
    { target := by
        simp [capability, HyperdocumentCausalFamily.Witness.declaration,
          HyperdocumentCausalFamily.Witness.intent,
          HyperdocumentOperations.Declaration.toRequest, mergeDeclaration,
          mergeIntent, HyperdocumentMerge.Declaration.toRequest]
      verb := by simp [capability, mergeDeclaration, HyperdocumentMerge.Declaration.toRequest]
      cost := by simp [capability, mergeDeclaration, requestEnvelope,
        HyperdocumentMerge.Declaration.toRequest] }
  validFrom := by decide
  validUntil := by decide
  policyId := rfl
  policyEpoch := rfl
  policyCurrent := rfl
  issuerCurrent := rfl
  selfNotRevoked := principal.selfNotRevoked
  ancestorNotRevoked := principal.ancestorsNotRevoked
  channelNotRevoked := principal.channelsNotRevoked

noncomputable def mergeAuthorization : Authorized TypedAuthorizationWitness.permissivePortal
    (CredentialAuthorityState.authState projection authorityPre)
    (mergeDeclaration.toRequest mergeConfig) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

theorem mergeValidatedNonempty : Nonempty
    (ValidatedPatch hyperdocumentMaterializer baseCell
      (mergeDeclaration.patch mergeConfig)) := by
  generalize exactOutcome : validate hyperdocumentMaterializer baseCell
    (mergeDeclaration.patch mergeConfig) = outcome
  cases outcome with
  | accepted validated => exact ⟨validated⟩
  | rejected reason =>
      have rootExact :
          (mergeDeclaration.patch mergeConfig).expectedPreRoot = baseCell.root :=
        mergeSemantic.preRootExact
      have fieldsExact :
          (mergeDeclaration.patch mergeConfig).fieldFootprint =
            (mergeDeclaration.patch mergeConfig).namedFields :=
        (HyperdocumentMerge.Declaration.patch_namedFields _ _).symm
      have resourcesExact :
          (mergeDeclaration.patch mergeConfig).resourceFootprint =
            (mergeDeclaration.patch mergeConfig).namedResources :=
        (HyperdocumentMerge.Declaration.patch_namedResources _ _).symm
      unfold CellState.validate at exactOutcome
      rw [dif_pos rootExact, dif_pos fieldsExact, dif_pos resourcesExact] at exactOutcome
      cases exactOutcome

noncomputable def mergeAccepted : HyperdocumentMerge.Accepted history mergeConfig projection
    authorityPre baseCell TypedAuthorizationWitness.permissivePortal mergeDeclaration :=
  HyperdocumentMerge.accept principal mergeSemantic parentEvidence parentContent
    (.selected selectedBase) (by
      change ∀ selected ∈ [plan], selected.base = some baseId
      intro selected present
      simp only [List.mem_singleton] at present
      subst selected
      rfl)
    mergeCapabilityAdmissible mergeAuthorization
    (Classical.choice mergeValidatedNonempty)

@[simp] theorem conflict_is_materialized :
    lookup mergeAccepted.accepted.prepared.post.logical .conflicts
      (plan.conflictId mergeConfig
        (mergeDeclaration.operationId mergeConfig)) =
      some (plan.conflictRecord (mergeDeclaration.operationId mergeConfig)) := by
  exact mergeAccepted.post_contains_write
    ⟨.conflicts,
      { key := plan.conflictId mergeConfig
          (mergeDeclaration.operationId mergeConfig)
        expected := none
        replacement := plan.conflictRecord
          (mergeDeclaration.operationId mergeConfig) }⟩
    (by simp [mergeDeclaration, body, plan, HyperdocumentMerge.Declaration.packedWrites,
      HyperdocumentMerge.FieldPlan.packedWrites])

/-! ## Derived event acceptance and atomic two-cell publication -/

noncomputable def eventDeclarationCodec : LawfulCodec HyperdocumentVersionEffects.Declaration :=
  codecOfCountable HyperdocumentVersionEffects.Declaration

noncomputable def eventConfig : HyperdocumentVersionEffects.Config where
  declarationCodec := eventDeclarationCodec
  requestCodec := requestCodec
  effectDerivation := derivation
  requestDerivation := derivation
  eventCodec := eventCodec
  eventDerivation := eventDerivation
  requestDomain := mergeConfig.requestDomain
  semanticRelation := ⟨703⟩

noncomputable def logCell :
    CellState.Materialized (eventLogCellMaterializer.{0, 0}) :=
  Minidregg.Kernel.DeployedMaterializerWitness.eventLogCell.{0, 0}

noncomputable def expectedLogRoot : Digest := logCell.root

noncomputable def publicationInputs : HyperdocumentMerge.PublicationInputs mergeAccepted eventConfig
    expectedLogRoot where
  addressingExact := rfl
  parentCompatibility := .binary _ _ _ rfl
  eventWellFormed := by
    constructor
    · simp [HyperdocumentMerge.recordOfAccepted, mergeDeclaration, mergeIntent,
        VersionEventRecord.toCausalPreimage, leftParent, rightParent]
    · simp [HyperdocumentMerge.recordOfAccepted, mergeDeclaration, mergeIntent,
        VersionEventRecord.toCausalPreimage, leftParent, rightParent]

noncomputable def eventCapabilityAdmissible :
    capability.Admissible
      (CredentialAuthorityState.authState projection authorityPre)
      ((HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted logCell.root).toRequest
        eventConfig) where
  holder := rfl
  scope :=
    { target := by
        simp [capability, HyperdocumentCausalFamily.Witness.declaration,
          HyperdocumentCausalFamily.Witness.intent,
          HyperdocumentOperations.Declaration.toRequest,
          HyperdocumentMergePublication.derivedEventDeclaration,
          HyperdocumentMerge.eventDeclaration, HyperdocumentMerge.recordOfAccepted,
          HyperdocumentVersionEffects.Declaration.toRequest, mergeDeclaration,
          mergeIntent]
      verb := by simp [capability, HyperdocumentVersionEffects.Declaration.toRequest]
      cost := by simp [capability, HyperdocumentMergePublication.derivedEventDeclaration,
        HyperdocumentMerge.eventDeclaration, mergeDeclaration, requestEnvelope,
        HyperdocumentVersionEffects.Declaration.toRequest] }
  validFrom := by decide
  validUntil := by decide
  policyId := rfl
  policyEpoch := rfl
  policyCurrent := rfl
  issuerCurrent := rfl
  selfNotRevoked := principal.selfNotRevoked
  ancestorNotRevoked := principal.ancestorsNotRevoked
  channelNotRevoked := principal.channelsNotRevoked

noncomputable def eventAuthorization : Authorized TypedAuthorizationWitness.permissivePortal
    (CredentialAuthorityState.authState projection authorityPre)
    ((HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted logCell.root).toRequest
      eventConfig) where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

theorem eventValidatedNonempty : Nonempty
    (ValidatedPatch eventLogRepresentation.cellMaterializer logCell
      ((HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted logCell.root).patch
        eventConfig)) := by
  generalize exactOutcome : validate eventLogRepresentation.cellMaterializer
    logCell
    ((HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted logCell.root).patch
      eventConfig) = outcome
  cases outcome with
  | accepted validated => exact ⟨validated⟩
  | rejected reason =>
      have rootExact :
          ((HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted
            logCell.root).patch eventConfig).expectedPreRoot = logCell.root := rfl
      have fieldsExact :
          ((HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted
            logCell.root).patch eventConfig).fieldFootprint =
          ((HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted
            logCell.root).patch eventConfig).namedFields :=
        (HyperdocumentVersionEffects.Declaration.patch_namedFields _ _).symm
      have resourcesExact :
          ((HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted
            logCell.root).patch eventConfig).resourceFootprint =
          ((HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted
            logCell.root).patch eventConfig).namedResources :=
        (HyperdocumentVersionEffects.Declaration.patch_namedResources _ _).symm
      unfold CellState.validate at exactOutcome
      split at exactOutcome
      · split at exactOutcome
        · split at exactOutcome
          · cases exactOutcome
          · contradiction
        · contradiction
      · contradiction

noncomputable def eventAccepted : HyperdocumentMergePublication.EventAccepted mergeAccepted
    eventLogRepresentation HyperdocumentEventLog.Sparse.empty eventConfig TypedAuthorizationWitness.permissivePortal
    logCell.root :=
  HyperdocumentMergePublication.acceptEvent publicationInputs eventCapabilityAdmissible rfl
    eventAuthorization (Classical.choice eventValidatedNonempty)

noncomputable def header : HyperdocumentMergePublication.Header := ⟨⟨900⟩, ⟨901⟩⟩
noncomputable def contentCellId : Digest := ⟨902⟩
noncomputable def eventCellId : Digest := ⟨903⟩

noncomputable def boundary : Minidregg.Kernel.MultiCellHyperedge.HandlerBoundary
    (HyperdocumentMergePublication.declaration mergeAccepted eventAccepted header contentCellId
      eventCellId) where
  Evidence := fun _ _ => Unit

noncomputable def jointInput : Minidregg.Kernel.MultiCellHyperedge.JointCommitInput :=
  ⟨header.apex, ⟨904⟩⟩

noncomputable def commit := HyperdocumentMergePublication.commit mergeAccepted eventAccepted header
  contentCellId eventCellId rfl (by decide) boundary jointInput rfl ()

@[simp] theorem atomic_content_conflict :
    lookup (commit.post .content).logical .conflicts
      (plan.conflictId mergeConfig
        (mergeDeclaration.operationId mergeConfig)) =
      some (plan.conflictRecord (mergeDeclaration.operationId mergeConfig)) :=
  HyperdocumentMergePublication.commit_conflict_retained plan (by simp [mergeDeclaration, body])
    leftSource rightSource [] rfl

@[simp] theorem atomic_event_append :
    (commit.post .eventLog).logical.fields
      ⟨HyperdocumentEventLog.Sparse.Namespace.events,
        (HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted logCell.root).key
          eventConfig⟩ =
      some (HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted logCell.root).record :=
  HyperdocumentMergePublication.commit_event_post_contains

theorem atomic_conflict_cannot_disappear :
    ¬ HyperdocumentMergePublication.ConflictFreeState (commit.post .content).logical :=
  HyperdocumentMergePublication.commit_conflict_cannot_be_erased plan
    (by simp [mergeDeclaration, body]) leftSource rightSource [] rfl

/-! ## Payload-bearing durable intent and stale-authority tooth -/

noncomputable def durableEvent : DurableDataIntent.StableEvent where
  codecVersion := 1
  domain := mergeConfig.requestDomain
  eventId := header.turnId
  canonicalBytes := eventDeclarationCodec.encode
    (HyperdocumentMergePublication.derivedEventDeclaration mergeAccepted logCell.root)

noncomputable def durableIntent : DurableDataIntent.DataIntent lengthRoot where
  transactionId := header.turnId
  writes :=
    [{ cellId := contentCellId
       expectedPre := baseCell.root
       exactPost := (commit.post .content).root
       canonicalPostBytes := (commit.post .content).bytes },
     { cellId := eventCellId
       expectedPre := logCell.root
       exactPost := (commit.post .eventLog).root
       canonicalPostBytes := (commit.post .eventLog).bytes }]
  readGuards := [{ cellId := ⟨905⟩, expectedRoot := authorityPre.root }]
  nullifiers := []
  exactCharge := 0
  event := durableEvent
  postRootsBound := by intro write member; simp at member; rcases member with rfl | rfl <;> rfl
  guardsReadOnly := by intro guard member; simp at member; subst guard; decide

theorem stale_authority_rejects
    (snapshot : DurableDataIntent.DataSnapshot lengthRoot)
    (moved : snapshot.model.roots ⟨905⟩ ≠ authorityPre.root) :
    durableIntent.preflight snapshot = .error .staleReadGuard := by
  apply DurableDataIntent.stale_read_guard_rejected
  exact ⟨{ cellId := ⟨905⟩, expectedRoot := authorityPre.root }, by simp [durableIntent],
    by simpa using moved⟩

/-! ## Negative causal/frontier teeth -/

theorem base_is_not_current :
    baseNode.entryId ∉ CausalVersionDag.frontier history.events := by
  rw [current_frontier]
  decide

theorem siblings_are_distinct : leftNode ≠ rightNode := by
  intro same
  have ids := congrArg CausalVersionDag.VerifiedEvent.entryId same
  simp at ids

theorem swapped_parents_not_canonical :
    ¬ HyperdocumentMerge.Parent.CanonicalOrder [rightParent, leftParent] := by
  simp [HyperdocumentMerge.Parent.CanonicalOrder, HyperdocumentMerge.Parent.entryId, rightParent, leftParent]

/-! ## Axiom audit -/

/-- info: 'Minidregg.Kernel.HyperdocumentTwoParentWitness.atomic_content_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms atomic_content_conflict
/-- info: 'Minidregg.Kernel.HyperdocumentTwoParentWitness.atomic_event_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms atomic_event_append
/-- info: 'Minidregg.Kernel.HyperdocumentTwoParentWitness.stale_authority_rejects' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_authority_rejects

end

end Minidregg.Kernel.HyperdocumentTwoParentWitness
