/-
# Kernel.HyperdocumentMerge -- explicit offline/concurrent document joins

A merge is a first-order declaration over an ordered frontier of two or more
already admitted causal parents.  It does not ask a host callback to choose a
post-state.  Every field contribution is named together with its author and
operation provenance.  A singleton contribution becomes one exact typed field
write; two or more contributions become a stored `ConflictRecord`.  No branch
is silently selected or discarded.

Stable mark and annotation records are copied as exact dependent values, so
their stored ranges and operation identities survive the join.  Parent order is
observable in canonical bytes; the admitted policy is therefore strict order
by event digest, not a false commutativity claim.  `canonicalPair` records the
limited symmetry theorem which is actually true.

The accepted content effect below is still the ordinary `AcceptedCellEffect`.
The final section derives the exact `VersionEventRecord` and existing event-log
declaration needed by a later `MultiCellHyperedge` publication.  Physical CAS,
persistence, consensus and finality remain external handler obligations.
-/
import Kernel.HyperdocumentVersionEffects
import Theory.CausalVersionAncestry

namespace Minidregg.Kernel.HyperdocumentMerge

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.HyperdocumentOperationIntent
open Minidregg.Theory.CausalVersionAncestry

set_option autoImplicit false

universe uState uEvidence

/-! ## First-order parents and merge contributions -/

/-- The complete public record of one selected parent.  Causal admission and
current-frontier membership are proof fields on `Accepted`, not trusted flags
inside this serializable value. -/
structure Parent where
  key : VersionEventId
  record : VersionEventRecord

def Parent.entryId (parent : Parent) : Digest := parent.key.digest

/-- Canonical parent presentation policy.  Full commutativity is false because
the ordered parent frontier is committed by the operation and event codecs. -/
def Parent.CanonicalOrder (parents : List Parent) : Prop :=
  parents.Pairwise (fun left right => left.entryId.value < right.entryId.value)

/-- Binary helper used by clients before constructing a two-parent merge. -/
def canonicalPair (left right : Parent) : List Parent :=
  if left.entryId.value ≤ right.entryId.value then [left, right]
  else [right, left]

theorem canonicalPair_swap
    (left right : Parent) (distinct : left.entryId.value ≠ right.entryId.value) :
    canonicalPair left right = canonicalPair right left := by
  simp only [canonicalPair]
  split <;> split <;> simp_all <;> omega

theorem raw_pair_order_observable
    (left right : Parent) (distinct : left ≠ right) :
    [left, right] ≠ [right, left] := by
  intro equal
  have headEqual : left = right := by
    simpa using congrArg List.head? equal
  exact distinct headEqual

/-- One parent's typed contribution to a field.  `ConflictAlternative` already
retains the exact author, dependent value type/value, and `OperationId`. -/
structure FieldSource where
  parent : VersionEventId
  alternative : ConflictAlternative

/-- A field join begins from the exact currently materialized optional value.
The common causal base is retained in any conflict record. -/
structure FieldPlan where
  field : FieldKey
  expected : Option FieldRecord
  base : Option VersionEventId
  regime : MergeRegime
  sources : List FieldSource

def FieldSource.toFieldRecord (regime : MergeRegime)
    (source : FieldSource) : FieldRecord where
  valueType := source.alternative.valueType
  value := source.alternative.value
  merge := regime
  writtenBy := source.alternative.author
  writtenAt := source.alternative.operation

/-- Stable overlay contributions use the existing canonical stored records.
There is no lossy range translation in the merge layer. -/
inductive StableOverlay where
  | mark (parent : VersionEventId) (id : MarkId)
      (expected : Option MarkRecord) (replacement : MarkRecord)
  | annotation (parent : VersionEventId) (id : AnnotationId)
      (expected : Option AnnotationRecord) (replacement : AnnotationRecord)

def StableOverlay.parent : StableOverlay -> VersionEventId
  | .mark parent _ _ _ => parent
  | .annotation parent _ _ _ => parent

def StableOverlay.operation : StableOverlay -> OperationId
  | .mark _ _ _ replacement => replacement.operation
  | .annotation _ _ _ replacement => replacement.operation

def StableOverlay.document : StableOverlay -> DocumentId
  | .mark _ _ _ replacement => replacement.document
  | .annotation _ _ _ replacement => replacement.document

structure Body where
  parents : List Parent
  fields : List FieldPlan
  overlays : List StableOverlay

structure Declaration where
  intent : OperationIntent
  request : Minidregg.Theory.HyperdocumentOperations.RequestEnvelope
  body : Body

/-- A conflict address is derived from the merge operation and field identity.
The digest function remains abstract and carries no collision theorem. -/
structure ConflictKeyPreimage where
  operation : OperationId
  field : FieldKey

structure Config where
  bodyCodec : LawfulCodec Body
  declarationCodec : LawfulCodec Declaration
  requestCodec : LawfulCodec (Request .object)
  conflictKeyCodec : LawfulCodec ConflictKeyPreimage
  intentAddressing : Addressing
  conflictDerivation : DigestDerivation
  effectDerivation : DigestDerivation
  requestDerivation : DigestDerivation
  requestDomain : Digest
  semanticRelation : Digest

def Declaration.operationId (config : Config) (declaration : Declaration) :
    OperationId :=
  HyperdocumentOperationIntent.operationId
    config.intentAddressing declaration.intent

def FieldPlan.conflictId (config : Config) (operation : OperationId)
    (plan : FieldPlan) : ConflictId :=
  deriveIdentifier config.conflictDerivation
    { payload := config.conflictKeyCodec.encode
        { operation := operation, field := plan.field } }

def FieldPlan.conflictRecord (operation : OperationId)
    (plan : FieldPlan) : ConflictRecord where
  field := plan.field
  base := plan.base
  alternatives := plan.sources.map FieldSource.alternative
  regime := plan.regime
  recordedAt := operation

def FieldPlan.packedWrites (config : Config) (operation : OperationId)
    (plan : FieldPlan) : List Minidregg.Theory.HyperdocumentOperations.PackedWrite :=
  match plan.sources with
  | [] => []
  | [source] =>
      [⟨.fields,
        { key := plan.field
          expected := plan.expected
          replacement := source.toFieldRecord plan.regime }⟩]
  | _ :: _ :: _ =>
      [⟨.conflicts,
        { key := plan.conflictId config operation
          expected := none
          replacement := plan.conflictRecord operation }⟩]

def StableOverlay.packedWrite
    (overlay : StableOverlay) :
    Minidregg.Theory.HyperdocumentOperations.PackedWrite :=
  match overlay with
  | .mark _ id expected replacement =>
      ⟨.marks, { key := id, expected := expected, replacement := replacement }⟩
  | .annotation _ id expected replacement =>
      ⟨.annotations,
        { key := id, expected := expected, replacement := replacement }⟩

def Declaration.packedWrites (config : Config)
    (declaration : Declaration) :
    List Minidregg.Theory.HyperdocumentOperations.PackedWrite :=
  let operation := declaration.operationId config
  declaration.body.fields.flatMap (FieldPlan.packedWrites config operation) ++
    declaration.body.overlays.map StableOverlay.packedWrite

def Declaration.fieldWrites (config : Config) (declaration : Declaration) :
    List (CellState.FieldWrite cellSchema) :=
  (declaration.packedWrites config).map
    Minidregg.Theory.HyperdocumentOperations.PackedWrite.toFieldWrite

def Declaration.patch (config : Config) (declaration : Declaration) :
    CellState.Patch cellSchema Digest where
  expectedPreRoot := declaration.intent.expectedContentRoot
  fieldFootprint :=
    (declaration.fieldWrites config).map CellState.FieldWrite.field |>.toFinset
  resourceFootprint := ∅
  fieldWrites := declaration.fieldWrites config
  resourceWrites := []

@[simp] theorem Declaration.patch_namedFields
    (config : Config) (declaration : Declaration) :
    (declaration.patch config).namedFields =
      (declaration.patch config).fieldFootprint :=
  rfl

@[simp] theorem Declaration.patch_namedResources
    (config : Config) (declaration : Declaration) :
    (declaration.patch config).namedResources =
      (declaration.patch config).resourceFootprint := by
  simp [Declaration.patch, CellState.Patch.namedResources]

def Declaration.effectDigest (config : Config)
    (declaration : Declaration) : Digest :=
  config.effectDerivation.digestBytes
    (config.declarationCodec.encode declaration)

def Declaration.toRequest (config : Config) (declaration : Declaration) :
    Request .object where
  domain := config.requestDomain
  semantics := config.semanticRelation
  federation := declaration.request.federation
  subject := declaration.intent.author.subject
  subjectKeyEpoch := declaration.request.subjectKeyEpoch
  target := ⟨declaration.intent.document.digest.value⟩
  verb := .mutateObject
  argsDigest := (declaration.operationId config).digest
  effectsDigest := declaration.effectDigest config
  nonce := declaration.intent.nonce
  height := declaration.request.height
  preStateRoot := declaration.intent.expectedContentRoot
  policyId := declaration.request.policyId
  policyEpoch := declaration.request.policyEpoch
  cost := declaration.request.cost

def Declaration.requestId (config : Config) (declaration : Declaration) : Digest :=
  config.requestDerivation.digestBytes
    (config.requestCodec.encode (declaration.toRequest config))

/-! ## Canonical merge validity -/

def AtLeastTwo {α : Type} (values : List α) : Prop :=
  ∃ first second rest, values = first :: second :: rest

def FieldSource.ParentExact (parents : List Parent)
    (source : FieldSource) : Prop :=
  ∃ parent, parent ∈ parents ∧ parent.key = source.parent ∧
    parent.record.operation = source.alternative.operation ∧
    parent.record.author = source.alternative.author

structure FieldPlan.Valid (parents : List Parent) (plan : FieldPlan) : Prop where
  sourcesNonempty : plan.sources ≠ []
  sourceOrder : (plan.sources.map FieldSource.parent).Pairwise
    (fun left right => left.digest.value < right.digest.value)
  sourcesExact : ∀ source, source ∈ plan.sources → source.ParentExact parents

def StableOverlay.ParentExact (parents : List Parent)
    (overlay : StableOverlay) : Prop :=
  ∃ parent, parent ∈ parents ∧ parent.key = overlay.parent ∧
    parent.record.operation = overlay.operation ∧
    parent.record.document = overlay.document

def Minidregg.Theory.HyperdocumentOperations.PackedWrite.ExpectedAt
    (pre : CellState.LogicalState cellSchema)
    (write : Minidregg.Theory.HyperdocumentOperations.PackedWrite) : Prop :=
  pre.fields write.address = write.write.expected

/-- The complete merge law at one canonical content cell.  Parent admission
against a causal history is retained separately by `CurrentParentEvidence`.
This structure checks the deterministic patch and all object compatibility
facts which can be decided at the merge boundary. -/
structure ValidMerge
    {M : Hyperdocument.Materializer Digest}
    (config : Config) (pre : Hyperdocument.Cell M)
    (declaration : Declaration) : Prop where
  actionBytesExact : declaration.intent.actionBytes =
    config.bodyCodec.encode declaration.body
  objectCapability : declaration.intent.author.capabilityKind = .object
  preRootExact : declaration.intent.expectedContentRoot = pre.root
  atLeastTwoParents : AtLeastTwo declaration.body.parents
  parentOrder : Parent.CanonicalOrder declaration.body.parents
  parentFrontierExact : declaration.intent.parents =
    declaration.body.parents.map Parent.key
  parentDocumentExact : ∀ parent, parent ∈ declaration.body.parents →
    parent.record.document = declaration.intent.document
  parentSchemaExact : ∀ parent, parent ∈ declaration.body.parents →
    parent.record.schema = declaration.intent.schema
  parentVersionEarlier : ∀ parent, parent ∈ declaration.body.parents →
    parent.record.semanticVersion < declaration.intent.semanticVersion
  fieldsValid : ∀ plan, plan ∈ declaration.body.fields →
    plan.Valid declaration.body.parents
  fieldsUnique : (declaration.body.fields.map FieldPlan.field).Nodup
  overlaysExact : ∀ overlay, overlay ∈ declaration.body.overlays →
    overlay.ParentExact declaration.body.parents
  overlaysDocumentExact : ∀ overlay, overlay ∈ declaration.body.overlays →
    overlay.document = declaration.intent.document
  writesUnique :
    ((declaration.packedWrites config).map
      Minidregg.Theory.HyperdocumentOperations.PackedWrite.address).Nodup
  expectedExact : ∀ write, write ∈ declaration.packedWrites config →
    write.ExpectedAt pre.logical

/-! ## Actual causal admission/currentness evidence -/

section CausalParents

variable {State : Type uState}
variable {scheme : CausalVersionDag.ContentAddressing}
variable {causalFamily : CausalVersionDag.SemanticFamily.{uState, uEvidence} State}
variable {anchor : CausalVersionDag.Anchor}

abbrev CausalNode := CausalVersionDag.VerifiedEvent scheme causalFamily

/-- The selected ordered parent records resolve to actual nodes in one built
causal history, and every one is a current frontier tip at merge admission.
This rules out fabricated parent ids and makes the optional tips policy
explicit rather than redefining generic DAG validity. -/
structure CurrentParentEvidence
    {MDoc : Hyperdocument.Materializer Digest}
    (history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor)
    (parents : List Parent) : Type _ where
  resolved : List CausalNode
  idsExact : resolved.map CausalVersionDag.VerifiedEvent.entryId =
    parents.map Parent.entryId
  recordsExact : resolved.map CausalVersionDag.VerifiedEvent.preimage =
    parents.map (fun parent => parent.record.toCausalPreimage)
  admitted : ∀ node, node ∈ resolved → node ∈ history.events
  current : ∀ node, node ∈ resolved →
    node.entryId ∈ CausalVersionDag.frontier history.events
  /-- Exact semantic content realization of each selected causal parent. -/
  realization : ∀ parent, parent ∈ parents → Hyperdocument.Cell MDoc
  realizationRootExact : ∀ parent, ∀ present : parent ∈ parents,
    (realization parent present).root = parent.record.postStateRoot

/-! ## Proof-relevant common-base selection -/

/-- One common ancestor of every exact resolved merge parent.  The paths are
the admitted `CausalVersionAncestry.Reaches` relation in the same built history,
not a host-provided digest relation. -/
structure CommonBase
    {MDoc : Hyperdocument.Materializer Digest}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {declaredParents : List Parent}
    (parents : CurrentParentEvidence (MDoc := MDoc) history declaredParents) :
    Type _ where
  base : CausalNode
  admitted : base ∈ history.events
  reachesEvery : ∀ node, node ∈ parents.resolved →
    CausalVersionAncestry.Reaches history base node

/-- A selected base is genuinely lowest among all common bases for this exact
parent family.  General DAGs need not admit this certificate. -/
structure LowestCommonBase
    {MDoc : Hyperdocument.Materializer Digest}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {declaredParents : List Parent}
    (parents : CurrentParentEvidence (MDoc := MDoc) history declaredParents) :
    Type _ where
  selected : CommonBase parents
  belowEvery : ∀ other : CommonBase parents,
    CausalVersionAncestry.Reaches history other.base selected.base

namespace LowestCommonBase

theorem selected_unique
    {MDoc : Hyperdocument.Materializer Digest}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {declaredParents : List Parent}
    {parents : CurrentParentEvidence (MDoc := MDoc) history declaredParents}
    (first second : LowestCommonBase parents) :
    first.selected.base = second.selected.base :=
  CausalVersionAncestry.Reaches.antisymm
    (second.belowEvery first.selected) (first.belowEvery second.selected)

end LowestCommonBase

/-- A maximal common base has no distinct common descendant.  Several
incomparable maximal bases may coexist. -/
structure MaximalCommonBase
    {MDoc : Hyperdocument.Materializer Digest}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {declaredParents : List Parent}
    (parents : CurrentParentEvidence (MDoc := MDoc) history declaredParents) :
    Type _ where
  candidate : CommonBase parents
  noLower : ∀ other : CommonBase parents,
    CausalVersionAncestry.Reaches history candidate.base other.base →
      other.base = candidate.base

/-- Explicit evidence that no unique lowest base is available: two distinct
maximal common bases. -/
structure AmbiguousCommonBases
    {MDoc : Hyperdocument.Materializer Digest}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {declaredParents : List Parent}
    (parents : CurrentParentEvidence (MDoc := MDoc) history declaredParents) :
    Type _ where
  first : MaximalCommonBase parents
  second : MaximalCommonBase parents
  distinct : first.candidate.base ≠ second.candidate.base

namespace AmbiguousCommonBases

theorem excludes_lowest
    {MDoc : Hyperdocument.Materializer Digest}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {declaredParents : List Parent}
    {parents : CurrentParentEvidence (MDoc := MDoc) history declaredParents}
    (ambiguous : AmbiguousCommonBases parents) :
    LowestCommonBase parents → False := by
  intro lowest
  have firstEqual :
      lowest.selected.base = ambiguous.first.candidate.base :=
    ambiguous.first.noLower lowest.selected
      (lowest.belowEvery ambiguous.first.candidate)
  have secondEqual :
      lowest.selected.base = ambiguous.second.candidate.base :=
    ambiguous.second.noLower lowest.selected
      (lowest.belowEvery ambiguous.second.candidate)
  exact ambiguous.distinct (firstEqual.symm.trans secondEqual)

end AmbiguousCommonBases

/-- A selected base also retains its exact canonical content realization and
binds that cell root to the admitted base event's post-state root. -/
structure SelectedBase
    {MDoc : Hyperdocument.Materializer Digest}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {declaredParents : List Parent}
    (parents : CurrentParentEvidence (MDoc := MDoc) history declaredParents) :
    Type _ where
  causal : LowestCommonBase parents
  realization : Hyperdocument.Cell MDoc
  realizationRootExact : realization.root = causal.selected.base.preimage.postStateRoot

/-- Honest merge-wide base decision.  `ambiguous` and `unavailable` serialize
no base; they do not choose a winner or assert a unique LCA. -/
inductive BaseDecision
    {MDoc : Hyperdocument.Materializer Digest}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {declaredParents : List Parent}
    (parents : CurrentParentEvidence (MDoc := MDoc) history declaredParents) :
    Type _ where
  | selected (certificate : SelectedBase parents)
  | ambiguous (certificate : AmbiguousCommonBases parents)
  | unavailable (noCommon : CommonBase parents → False)

def causalEventId
    (node : CausalVersionDag.VerifiedEvent scheme causalFamily) :
    VersionEventId :=
  ⟨node.entryId⟩

/-- Every field plan must serialize exactly the merge-wide decision. -/
def BaseDecision.Exact
    {MDoc : Hyperdocument.Materializer Digest}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {declaredParents : List Parent}
    {parents : CurrentParentEvidence (MDoc := MDoc) history declaredParents}
    (decision : BaseDecision parents) (plans : List FieldPlan) : Prop :=
  match decision with
  | .selected certificate =>
      ∀ plan, plan ∈ plans →
        plan.base = some (causalEventId certificate.causal.selected.base)
  | .ambiguous _ | .unavailable _ =>
      ∀ plan, plan ∈ plans → plan.base = none

/-- Compatibility constructor for the former no-base API.  Absence is no
longer a free flag: callers must prove that no common base exists. -/
def BaseDecision.unavailableOfAbsent
    {MDoc : Hyperdocument.Materializer Digest}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {declaredParents : List Parent}
    {parents : CurrentParentEvidence (MDoc := MDoc) history declaredParents}
    {plans : List FieldPlan}
    (noCommon : CommonBase parents → False)
    (absent : ∀ plan, plan ∈ plans → plan.base = none) :
    ∃ decision : BaseDecision parents, decision.Exact plans :=
  ⟨.unavailable noCommon, absent⟩

/-- Every declared contribution is opened from the exact content realization
of its named parent.  Operation/author equality alone is deliberately
insufficient: these lookup equations are the load-bearing provenance join. -/
structure ParentContentEvidence
    {MDoc : Hyperdocument.Materializer Digest}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {declaration : Declaration}
    (parents : CurrentParentEvidence (MDoc := MDoc) history
      declaration.body.parents) : Type _ where
  fieldSources : ∀ plan, plan ∈ declaration.body.fields →
    ∀ source, source ∈ plan.sources →
      ∃ parent, ∃ present : parent ∈ declaration.body.parents,
        parent.key = source.parent ∧
        lookup (parents.realization parent present).logical .fields plan.field =
          some (source.toFieldRecord plan.regime)
  stableOverlays : ∀ overlay, overlay ∈ declaration.body.overlays →
    ∃ parent, ∃ present : parent ∈ declaration.body.parents,
      parent.key = overlay.parent ∧
      match overlay with
      | .mark _ id _ replacement =>
          lookup (parents.realization parent present).logical .marks id =
            some replacement
      | .annotation _ id _ replacement =>
          lookup (parents.realization parent present).logical .annotations id =
            some replacement

/-! ## The ordinary accepted content effect -/

def unitCodec : LawfulCodec Unit :=
  Minidregg.Theory.HyperdocumentOperations.unitCodec

def sealedOnly : DisclosureDecision Unit Unit (fun _ => Unit) -> Prop
  | .sealed => True
  | .reveal _ _ => False
  | .declassify _ _ _ => False

def family {M : Hyperdocument.Materializer Digest} (config : Config) :
    SemanticEffectFamily cellSchema M Nat where
  Declaration := Declaration
  declarationCodec := config.declarationCodec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun declaration _ => PLift
    (declaration.intent.actionBytes = config.bodyCodec.encode declaration.body)
  effectDigest := Declaration.effectDigest config
  patch := fun declaration _ => declaration.patch config
  nullifier := fun declaration _ => some declaration.intent.nonce
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

structure Accepted
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    (history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor)
    (config : Config)
    (projection : CredentialAuthorityState.ProjectionUniverse)
    (authorityPre : CredentialAuthorityState.Cell MAuth)
    (documentPre : Hyperdocument.Cell MDoc)
    (portal : Portal) (declaration : Declaration) : Type _ where
  principal : AuthenticatedPrincipal projection authorityPre
    declaration.request.height declaration.intent.author
  semantic : ValidMerge config documentPre declaration
  parents : CurrentParentEvidence (MDoc := MDoc) history declaration.body.parents
  parentContent : ParentContentEvidence parents
  baseDecision : BaseDecision parents
  basesExact : baseDecision.Exact declaration.body.fields
  namedCapabilityAdmissible :
    (Minidregg.Theory.HyperdocumentOperations.authenticatedObjectHead
      principal semantic.objectCapability).Admissible
    (CredentialAuthorityState.authState projection authorityPre)
    (declaration.toRequest config)
  accepted : AcceptedCellEffect
    (portal := portal)
    (authState := CredentialAuthorityState.authState projection authorityPre)
    (family config) (declaration.toRequest config) documentPre declaration ()

def accept
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (principal : AuthenticatedPrincipal projection authorityPre
      declaration.request.height declaration.intent.author)
    (semantic : ValidMerge config documentPre declaration)
    (parents : CurrentParentEvidence (MDoc := MDoc) history declaration.body.parents)
    (parentContent : ParentContentEvidence parents)
    (baseDecision : BaseDecision parents)
    (basesExact : baseDecision.Exact declaration.body.fields)
    (namedCapabilityAdmissible :
      (Minidregg.Theory.HyperdocumentOperations.authenticatedObjectHead
        principal semantic.objectCapability).Admissible
      (CredentialAuthorityState.authState projection authorityPre)
      (declaration.toRequest config))
    (authorization : Authorized portal
      (CredentialAuthorityState.authState projection authorityPre)
      (declaration.toRequest config))
    (validated : CellState.ValidatedPatch MDoc documentPre
      (declaration.patch config)) :
    Accepted history config projection authorityPre documentPre portal declaration where
  principal := principal
  semantic := semantic
  parents := parents
  parentContent := parentContent
  baseDecision := baseDecision
  basesExact := basesExact
  namedCapabilityAdmissible := namedCapabilityAdmissible
  accepted :=
    { authorization := authorization
      effectsDigestBound := rfl
      preRootBound := semantic.preRootExact
      modeEvidence := ⟨semantic.actionBytesExact⟩
      validated := validated
      disclosure := .sealed
      disclosureAllowed := trivial }

/-! ## Exact post, frame, and no-ghost facts -/

theorem Accepted.post_contains_write
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration)
    (write : Minidregg.Theory.HyperdocumentOperations.PackedWrite)
    (member : write ∈ declaration.packedWrites config) :
    accepted.accepted.prepared.post.logical.fields write.address =
      some write.write.replacement := by
  have writesUnique :
      ((declaration.fieldWrites config).map CellState.FieldWrite.field).Nodup := by
    simpa [Declaration.fieldWrites, List.map_map, Function.comp_def,
      Minidregg.Theory.HyperdocumentOperations.PackedWrite.toFieldWrite] using
      accepted.semantic.writesUnique
  exact Minidregg.Theory.HyperdocumentOperations.applyFieldWrites_member_of_nodup
    (declaration.fieldWrites config) documentPre.logical.fields writesUnique
    write.toFieldWrite (by
      unfold Declaration.fieldWrites
      exact List.mem_map.2 ⟨write, member, rfl⟩)

theorem Accepted.field_frame
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration)
    (address : Address)
    (outside : address ∉
      ((family (M := MDoc) config).patch declaration ()).fieldFootprint) :
    accepted.accepted.prepared.post.logical.fields address =
      documentPre.logical.fields address :=
  accepted.accepted.field_frame address outside

theorem Accepted.changed_only_declared
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration)
    (address : Address)
    (changed : accepted.accepted.prepared.post.logical.fields address ≠
      documentPre.logical.fields address) :
    address ∈
      ((family (M := MDoc) config).patch declaration ()).fieldFootprint :=
  accepted.accepted.field_changed_only_declared address changed

theorem Accepted.post_contains_mark
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration)
    (parent : VersionEventId) (id : MarkId) (expected : Option MarkRecord)
    (replacement : MarkRecord)
    (member : StableOverlay.mark parent id expected replacement ∈
      declaration.body.overlays) :
    lookup accepted.accepted.prepared.post.logical .marks id =
      some replacement := by
  have contains := accepted.post_contains_write
    (StableOverlay.packedWrite
      (.mark parent id expected replacement)) (by
      unfold Declaration.packedWrites
      apply List.mem_append_right
      exact List.mem_map.2 ⟨.mark parent id expected replacement, member, rfl⟩)
  exact contains

theorem Accepted.post_contains_annotation
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration)
    (parent : VersionEventId) (id : AnnotationId)
    (expected : Option AnnotationRecord) (replacement : AnnotationRecord)
    (member : StableOverlay.annotation parent id expected replacement ∈
      declaration.body.overlays) :
    lookup accepted.accepted.prepared.post.logical .annotations id =
      some replacement := by
  have contains := accepted.post_contains_write
    (StableOverlay.packedWrite
      (.annotation parent id expected replacement)) (by
      unfold Declaration.packedWrites
      apply List.mem_append_right
      exact List.mem_map.2
        ⟨.annotation parent id expected replacement, member, rfl⟩)
  exact contains

/-! ## Conflict retention teeth -/

def ConflictFree
    (writes : List Minidregg.Theory.HyperdocumentOperations.PackedWrite) : Prop :=
  ∀ write, write ∈ writes → write.space ≠ .conflicts

theorem FieldPlan.two_sources_not_conflict_free
    (config : Config) (operation : OperationId) (plan : FieldPlan)
    (first second : FieldSource) (rest : List FieldSource)
    (sourcesExact : plan.sources = first :: second :: rest) :
    ¬ ConflictFree (plan.packedWrites config operation) := by
  intro conflictFree
  have member :
      (⟨.conflicts,
        { key := plan.conflictId config operation
          expected := none
          replacement := plan.conflictRecord operation }⟩ :
        Minidregg.Theory.HyperdocumentOperations.PackedWrite) ∈
        plan.packedWrites config operation := by
    simp [FieldPlan.packedWrites, sourcesExact]
  exact conflictFree _ member rfl

/-- The same tooth at declaration scope: embedding a two-or-more-source plan
in a larger merge cannot make its explicit conflict write disappear. -/
theorem Declaration.conflicting_plan_not_conflict_free
    (config : Config) (declaration : Declaration) (plan : FieldPlan)
    (planPresent : plan ∈ declaration.body.fields)
    (first second : FieldSource) (rest : List FieldSource)
    (sourcesExact : plan.sources = first :: second :: rest) :
    ¬ ConflictFree (declaration.packedWrites config) := by
  intro declarationConflictFree
  apply plan.two_sources_not_conflict_free config
    (declaration.operationId config) first second rest sourcesExact
  intro write writePresent
  apply declarationConflictFree write
  unfold Declaration.packedWrites
  apply List.mem_append_left
  exact List.mem_flatMap.2 ⟨plan, planPresent, writePresent⟩

/-- Positive offline-sibling shape: two canonically ordered sibling
contributions deterministically produce the exact conflict value containing
both provenance-bearing alternatives. -/
theorem concurrent_sibling_conflict_positive
    (config : Config) (operation : OperationId) (field : FieldKey)
    (expected : Option FieldRecord) (base : Option VersionEventId)
    (regime : MergeRegime) (left right : FieldSource) :
    let plan : FieldPlan :=
      { field := field, expected := expected, base := base, regime := regime,
        sources := [left, right] }
    plan.packedWrites config operation =
      [⟨.conflicts,
        { key := plan.conflictId config operation
          expected := none
          replacement := plan.conflictRecord operation }⟩] := by
  dsimp
  rfl

/-! ## Exact causal/version-event publication inputs -/

def recordOfAccepted
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration) :
    VersionEventRecord :=
  { historyDomain := declaration.intent.historyDomain
    document := declaration.intent.document
    schema := declaration.intent.schema
    semanticVersion := declaration.intent.semanticVersion
    operation := declaration.operationId config
    parents := declaration.intent.parents
    preStateRoot := documentPre.root
    postStateRoot := accepted.accepted.prepared.post.root
    requestId := declaration.requestId config
    effectId := declaration.effectDigest config
    author := declaration.intent.author }

def eventDeclaration
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration)
    (expectedLogRoot : Digest) :
    Minidregg.Kernel.HyperdocumentVersionEffects.Declaration where
  expectedLogRoot := expectedLogRoot
  request := declaration.request
  record := recordOfAccepted accepted

/-- Everything a publication adapter must additionally prove before creating
the event-log incidence.  In particular, multi-parent semantic compatibility
is not inferred from matching ids or roots. -/
structure PublicationInputs
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration)
    (eventConfig : Minidregg.Kernel.HyperdocumentVersionEffects.Config)
    (expectedLogRoot : Digest) : Type _ where
  addressingExact : scheme = eventConfig.scheme
  parentCompatibility : causalFamily.ParentCompatible
    (accepted.parents.resolved.map CausalVersionDag.VerifiedEvent.preimage)
    (recordOfAccepted accepted).toCausalPreimage
  eventWellFormed : (recordOfAccepted accepted).CausallyWellFormed

@[simp] theorem recordOfAccepted_parents_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration) :
    (recordOfAccepted accepted).parents = declaration.body.parents.map Parent.key := by
  exact accepted.semantic.parentFrontierExact

@[simp] theorem recordOfAccepted_pre_root_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration) :
    (recordOfAccepted accepted).preStateRoot = documentPre.root :=
  rfl

@[simp] theorem recordOfAccepted_post_root_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration) :
    (recordOfAccepted accepted).postStateRoot =
      accepted.accepted.prepared.post.root :=
  rfl

@[simp] theorem eventDeclaration_record_exact
    {MDoc : Hyperdocument.Materializer Digest}
    {MAuth : CredentialAuthorityState.Materializer}
    {history : CausalVersionDag.History (scheme := scheme)
      (family := causalFamily) anchor}
    {config : Config}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {authorityPre : CredentialAuthorityState.Cell MAuth}
    {documentPre : Hyperdocument.Cell MDoc}
    {portal : Portal} {declaration : Declaration}
    (accepted : Accepted history config projection authorityPre documentPre portal declaration)
    (expectedLogRoot : Digest) :
    (eventDeclaration accepted expectedLogRoot).record = recordOfAccepted accepted :=
  rfl

#print axioms canonicalPair_swap
#print axioms Accepted.post_contains_write
#print axioms Accepted.field_frame
#print axioms Accepted.changed_only_declared
#print axioms Accepted.post_contains_mark
#print axioms Accepted.post_contains_annotation
#print axioms FieldPlan.two_sources_not_conflict_free
#print axioms Declaration.conflicting_plan_not_conflict_free
#print axioms concurrent_sibling_conflict_positive
#print axioms LowestCommonBase.selected_unique
#print axioms AmbiguousCommonBases.excludes_lowest
#print axioms BaseDecision.unavailableOfAbsent
#print axioms recordOfAccepted_parents_exact
#print axioms eventDeclaration_record_exact

end CausalParents

end Minidregg.Kernel.HyperdocumentMerge
