/-
# Theory.ResourceBirthAuthority -- one authority effect for one birth batch

Every root-capability issue is checked against the same original canonical
authority cell using the existing IssueEvidence. The batch installs the exact
declared stored capabilities and consumes one shared nullifier. It never uses
one newborn grant as authority for a later grant.

The physical domain receiver computes its routed shard updates independently
of authorization, then proves their folded logical post equals this patch's
actual post. This module is the canonical sparse authority semantics, not a
second page or directory model.
-/
import Theory.ResourceBirth
import Theory.CredentialAuthorityEffects

namespace Minidregg.Theory.ResourceBirthAuthority

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.ResourceBirth

set_option autoImplicit false

def grantField (grant : AuthorityGrant) : AuthorityField :=
  .capability grant.kind grant.capability.head.id

def grantWrite (grant : AuthorityGrant) : FieldWrite CredentialAuthorityState.schema.{0, 0} :=
  { field := grantField grant, value := some grant.capability }

def nullifierWrite (identifier : Nat) : FieldWrite CredentialAuthorityState.schema.{0, 0} :=
  { field := .nullifier identifier, value := some true }

def issueDeclaration (preRoot : Digest) (nullifier : Nat) (grant : AuthorityGrant) :
    IssueDeclaration grant.kind where
  capability := grant.capability.head
  expectedPreRoot := preRoot
  operationNullifier := nullifier

def fieldWrites {registry : TypeRegistry Digest} (descriptor : Descriptor registry) :
    List (FieldWrite CredentialAuthorityState.schema.{0, 0}) :=
  descriptor.grants.map grantWrite ++ [nullifierWrite descriptor.authorityNullifier]

def patch {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) :
    Patch CredentialAuthorityState.schema.{0, 0} Digest where
  expectedPreRoot := pre.root
  fieldWrites := fieldWrites descriptor
  resourceWrites := []
  fieldFootprint := ((fieldWrites descriptor).map FieldWrite.field).toFinset
  resourceFootprint := ∅

/-- Evidence is structural/semantic preparation, preceding authorization.
Stored ancestry is checked separately because existing root-only IssueEvidence
describes the head and its canonical issue patch would install empty ancestry.
Freshness and live/epoch checks are all relative to the original pre-cell. -/
structure BatchEvidence {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest} (domain : ProjectionUniverse)
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) where
  slotsDistinct : (descriptor.grants.map grantField).Nodup
  nullifierFresh : isNullified pre descriptor.authorityNullifier = false
  ancestryEmpty : ∀ grant ∈ descriptor.grants, grant.capability.ancestry = []
  issue : ∀ grant ∈ descriptor.grants,
    IssueEvidence domain pre (issueDeclaration pre.root descriptor.authorityNullifier grant)

theorem validated {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) :
    ValidatedPatch M pre (patch pre descriptor) := by
  exact (validated_of_exact (patch pre descriptor) rfl rfl rfl).some

def post {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) :
    CredentialAuthorityState.Cell M :=
  (validated pre descriptor).apply

theorem post_fields {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) :
    (post pre descriptor).logical.fields =
      applyFieldWrites (fieldWrites descriptor) pre.logical.fields := rfl

private theorem applyFieldWrites_member
    {S : Schema} [DecidableEq S.Field]
    (writes : List (FieldWrite S)) (unique : (writes.map FieldWrite.field).Nodup)
    (fields : FieldStore S) (write : FieldWrite S) (member : write ∈ writes) :
    applyFieldWrites writes fields write.field = write.value := by
  induction writes generalizing fields with
  | nil => simp at member
  | cons first rest induction =>
      have pieces := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with same | inRest
      · cases same
        rw [applyFieldWrites, applyFieldWrites_frame rest
          (fields.assign write.field write.value) write.field (by simpa using pieces.1)]
        simp [FieldStore.assign]
      · exact induction pieces.2 _ inRest

theorem BatchEvidence.writes_distinct {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence domain pre descriptor) :
    ((fieldWrites descriptor).map FieldWrite.field).Nodup := by
  have outside : AuthorityField.nullifier descriptor.authorityNullifier ∉
      descriptor.grants.map grantField := by
    intro member
    obtain ⟨grant, _, same⟩ := List.mem_map.mp member
    cases grant
    simp [grantField] at same
  simp only [fieldWrites, List.map_append, List.map_map, List.map_singleton,
    grantWrite, nullifierWrite, Function.comp_def, List.nodup_append]
  refine ⟨evidence.slotsDistinct, by simp, ?_⟩
  intro field inGrants other inNullifier equal
  have same : other = AuthorityField.nullifier descriptor.authorityNullifier := by
    simpa using inNullifier
  apply outside
  simpa [equal, same] using inGrants

theorem BatchEvidence.installs_grant {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence domain pre descriptor)
    (grant : AuthorityGrant) (member : grant ∈ descriptor.grants) :
    (post pre descriptor).logical.fields (grantField grant) = some grant.capability := by
  rw [post_fields]
  exact applyFieldWrites_member (fieldWrites descriptor) evidence.writes_distinct
    pre.logical.fields (grantWrite grant)
      (List.mem_append_left _ (List.mem_map.mpr ⟨grant, member, rfl⟩))

theorem BatchEvidence.consumes_nullifier {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence domain pre descriptor) :
    (post pre descriptor).logical.fields (.nullifier descriptor.authorityNullifier) = some true := by
  rw [post_fields]
  exact applyFieldWrites_member (fieldWrites descriptor) evidence.writes_distinct
    pre.logical.fields (nullifierWrite descriptor.authorityNullifier) (by simp [fieldWrites])

theorem post_frame {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry)
    (field : AuthorityField) (outside : field ∉ (patch pre descriptor).fieldFootprint) :
    (post pre descriptor).logical.fields field = pre.logical.fields field :=
  (validated pre descriptor).field_frame field outside

theorem no_batch_of_used_nullifier {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (used : isNullified pre descriptor.authorityNullifier = true) :
    IsEmpty (BatchEvidence domain pre descriptor) :=
  ⟨fun evidence => Bool.noConfusion (used.symm.trans evidence.nullifierFresh)⟩

theorem no_batch_of_nonroot_lineage {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    {grant : AuthorityGrant} (member : grant ∈ descriptor.grants)
    (nonempty : grant.capability.ancestry ≠ []) :
    IsEmpty (BatchEvidence domain pre descriptor) :=
  ⟨fun evidence => nonempty (evidence.ancestryEmpty grant member)⟩

/-- These exact semantic outcomes must survive the final composed post:
every complete stored grant, and the batch's consumed nullifier. -/
def Postcondition {registry : TypeRegistry Digest} (descriptor : Descriptor registry)
    (state : LogicalState CredentialAuthorityState.schema.{0, 0}) : Prop :=
  (∀ grant ∈ descriptor.grants, state.fields (grantField grant) = some grant.capability) ∧
    state.fields (.nullifier descriptor.authorityNullifier) = some true

theorem BatchEvidence.postcondition {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence domain pre descriptor) :
    Postcondition descriptor (post pre descriptor).logical :=
  ⟨fun grant member => evidence.installs_grant grant member, evidence.consumes_nullifier⟩

theorem no_final_grant_erasure {registry : TypeRegistry Digest}
    {descriptor : Descriptor registry} {state : LogicalState CredentialAuthorityState.schema.{0, 0}}
    {grant : AuthorityGrant} (member : grant ∈ descriptor.grants)
    (missing : state.fields (grantField grant) ≠ some grant.capability) :
    ¬Postcondition descriptor state := fun final => missing (final.1 grant member)

theorem no_final_nullifier_erasure {registry : TypeRegistry Digest}
    {descriptor : Descriptor registry} {state : LogicalState CredentialAuthorityState.schema.{0, 0}}
    (missing : state.fields (.nullifier descriptor.authorityNullifier) ≠ some true) :
    ¬Postcondition descriptor state := fun final => missing final.2

/-- The authority incidence has its own actual domain pre-root. Its source
target is the pinned factory and it commits the whole same descriptor, but
it requires separate checked authorization for this exact request. -/
def request {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry) (domain : ProjectionUniverse)
    (pre : CredentialAuthorityState.Cell M) (height : Height) (descriptor : Descriptor registry) :
    Request .object :=
  factoryRequest pins encoding (authState domain pre) pre.root height descriptor

theorem factory_root_request_distinct {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry) (domain : ProjectionUniverse)
    (pre : CredentialAuthorityState.Cell M) (height : Height) (descriptor : Descriptor registry)
    (factoryRoot : Digest) (different : factoryRoot ≠ pre.root) :
    factoryRequest pins encoding (authState domain pre) factoryRoot height descriptor ≠
      request pins encoding domain pre height descriptor := by
  intro same
  exact different (congrArg Request.preStateRoot same)

def family {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry) (domain : ProjectionUniverse)
    (pre : CredentialAuthorityState.Cell M) (height : Height) :
    SemanticEffectFamily CredentialAuthorityState.schema.{0, 0} M Nat where
  pre := pre
  Declaration := Descriptor registry
  declarationCodec := encoding.codec
  request descriptor := ⟨.object, request pins encoding domain pre height descriptor⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => CredentialAuthorityEffects.unitCodec
  ModeEvidence := fun descriptor _ => BatchEvidence domain pre descriptor
  Postcondition := fun descriptor _ state => Postcondition descriptor state
  effectDigest := encoding.effectsDigest
  patch := fun descriptor _ => patch pre descriptor
  nullifier := fun descriptor _ => some descriptor.authorityNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => CredentialAuthorityEffects.sealedOnly

/-- Factory-root authorization is not accepted at this boundary. The token
must verify this authority-domain-rooted request against the same old state. -/
def accept {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.schema.{0, 0} Digest}
    {pins : FactoryPins} {encoding : SourceEncoding registry} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {height : Height} {descriptor : Descriptor registry}
    {portal : Portal} (evidence : BatchEvidence domain pre descriptor)
    (authorization : Authorized portal (authState domain pre)
      (request pins encoding domain pre height descriptor)) :
    AcceptedCellEffect (portal := portal) (authState := authState domain pre)
      (family pins encoding domain pre height) (request pins encoding domain pre height descriptor)
      pre descriptor () where
  authorization := authorization
  preStateBound := rfl
  requestBound := rfl
  effectsDigestBound := rfl
  preRootBound := rfl
  modeEvidence := evidence
  validated := validated pre descriptor
  postcondition := evidence.postcondition
  disclosure := .sealed
  disclosureAllowed := trivial

end Minidregg.Theory.ResourceBirthAuthority
