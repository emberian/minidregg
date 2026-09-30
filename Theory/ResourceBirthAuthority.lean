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
open Minidregg.Theory.Store

set_option autoImplicit false

def grantField (grant : AuthorityGrant) : Address CredentialAuthorityState.layout :=
  ⟨.capability grant.kind, grant.capability.head.id⟩

def grantEntry (grant : AuthorityGrant) : Entry :=
  ⟨grantField grant, grant.capability⟩

def policyEpochEntry (policy : InitialPolicy) : Entry :=
  ⟨⟨.policyEpoch, policy.policyId⟩, (0 : Epoch)⟩

def policyRevisionEntry (policy : InitialPolicy) : Entry :=
  ⟨⟨.policyRevision, policy.policyId⟩, (0 : PolicyRevision)⟩

def policyAddressEntry (policy : InitialPolicy) : Entry :=
  ⟨⟨.policyAddress, (policy.policyId, 0)⟩, policy.address⟩

def policyEntries (policy : InitialPolicy) : List Entry :=
  [policyEpochEntry policy, policyRevisionEntry policy, policyAddressEntry policy]

def issueDeclaration (preRoot : Digest) (nullifier : Nat) (grant : AuthorityGrant) :
    IssueDeclaration grant.kind where
  capability := grant.capability.head
  expectedPreRoot := preRoot
  operationNullifier := nullifier

def entries {registry : TypeRegistry Digest} (descriptor : Descriptor registry) :
    List Entry :=
  descriptor.initialPolicies.flatMap policyEntries ++
    descriptor.grants.map grantEntry ++ [nullifierEntry descriptor.authorityNullifier]

/-- The batch patch: every entry a guarded assignment at the canonical pre-cell. -/
def patch {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) :
    Patch CredentialAuthorityState.layout :=
  assignAll pre.logical (entries descriptor)

theorem patch_writeFootprint {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) :
    Patch.writeFootprint (patch pre descriptor) = ((entries descriptor).map Sigma.fst).toFinset :=
  assignAll_writeFootprint _ _

/-- Evidence is structural/semantic preparation, preceding authorization.
Stored ancestry is checked separately because existing root-only IssueEvidence
describes the head and its canonical issue patch would install empty ancestry.
Freshness and live/epoch checks are all relative to the original pre-cell. -/
structure BatchEvidence {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} (domain : ProjectionUniverse)
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) where
  slotsDistinct : ((entries descriptor).map Sigma.fst).Nodup
  grantIdsDistinct : descriptor.GrantIdsDistinct
  policiesFresh : ∀ policy ∈ descriptor.initialPolicies,
    pre.logical ⟨.policyEpoch, policy.policyId⟩ = none ∧
      pre.logical ⟨.policyRevision, policy.policyId⟩ = none ∧
      pre.logical ⟨.policyAddress, (policy.policyId, 0)⟩ = none
  nullifierFresh : isNullified pre descriptor.authorityNullifier = false
  ancestryEmpty : ∀ grant ∈ descriptor.grants, grant.capability.ancestry = []
  issue : ∀ grant ∈ descriptor.grants,
    IssueEvidence domain pre (issueDeclaration pre.root descriptor.authorityNullifier grant)

theorem validated {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) :
    ValidatedPatch M pre pre.root (patch pre descriptor) :=
  validated_of_assign (entries descriptor) rfl

def post {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) :
    CredentialAuthorityState.Cell M :=
  (validated pre descriptor).apply

theorem post_logical {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) :
    (post pre descriptor).logical = setAll pre.logical (entries descriptor) :=
  run_assignAll _ _

theorem BatchEvidence.writes_distinct {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence domain pre descriptor) :
    ((entries descriptor).map Sigma.fst).Nodup := evidence.slotsDistinct

theorem BatchEvidence.installs_grant {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence domain pre descriptor)
    (grant : AuthorityGrant) (member : grant ∈ descriptor.grants) :
    (post pre descriptor).logical (grantField grant) = some grant.capability := by
  rw [post_logical]
  exact setAll_member _ (entries descriptor) evidence.writes_distinct (grantEntry grant)
      (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨grant, member, rfl⟩)))

theorem BatchEvidence.installs_policy {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence domain pre descriptor)
    (policy : InitialPolicy) (member : policy ∈ descriptor.initialPolicies) :
    (post pre descriptor).logical ⟨.policyEpoch, policy.policyId⟩ = some (0 : Epoch) ∧
      (post pre descriptor).logical ⟨.policyRevision, policy.policyId⟩ =
        some (0 : PolicyRevision) ∧
      (post pre descriptor).logical ⟨.policyAddress, (policy.policyId, 0)⟩ =
        some policy.address := by
  refine ⟨?_, ?_, ?_⟩
  · rw [post_logical]
    exact setAll_member _ (entries descriptor) evidence.writes_distinct
      (policyEpochEntry policy)
      (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨policy, member, by simp [policyEntries]⟩)))
  · rw [post_logical]
    exact setAll_member _ (entries descriptor) evidence.writes_distinct
      (policyRevisionEntry policy)
      (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨policy, member, by simp [policyEntries]⟩)))
  · rw [post_logical]
    exact setAll_member _ (entries descriptor) evidence.writes_distinct
      (policyAddressEntry policy)
      (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.mpr ⟨policy, member, by simp [policyEntries]⟩)))

theorem BatchEvidence.consumes_nullifier {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence domain pre descriptor) :
    (post pre descriptor).logical ⟨.nullifier, descriptor.authorityNullifier⟩ = some true := by
  rw [post_logical]
  exact setAll_member _ (entries descriptor) evidence.writes_distinct
    (nullifierEntry descriptor.authorityNullifier) (by simp [entries])

theorem post_frame {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry)
    (address : Address CredentialAuthorityState.layout)
    (outside : address ∉ Patch.writeFootprint (patch pre descriptor)) :
    (post pre descriptor).logical address = pre.logical address :=
  Patch.run_frame pre.logical _ address outside

theorem no_batch_of_used_nullifier {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (used : isNullified pre descriptor.authorityNullifier = true) :
    IsEmpty (BatchEvidence domain pre descriptor) :=
  ⟨fun evidence => Bool.noConfusion (used.symm.trans evidence.nullifierFresh)⟩

theorem no_batch_of_nonroot_lineage {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    {grant : AuthorityGrant} (member : grant ∈ descriptor.grants)
    (nonempty : grant.capability.ancestry ≠ []) :
    IsEmpty (BatchEvidence domain pre descriptor) :=
  ⟨fun evidence => nonempty (evidence.ancestryEmpty grant member)⟩

/-- These exact semantic outcomes must survive the final composed post:
every complete stored grant, every initial policy head, and the consumed
nullifier. Source bytes are checked and retained by the physical compiler. -/
def Postcondition {registry : TypeRegistry Digest} (descriptor : Descriptor registry)
    (state : Store CredentialAuthorityState.layout) : Prop :=
  (∀ grant ∈ descriptor.grants, state (grantField grant) = some grant.capability) ∧
    (∀ policy ∈ descriptor.initialPolicies,
      state ⟨.policyEpoch, policy.policyId⟩ = some (0 : Epoch) ∧
        state ⟨.policyRevision, policy.policyId⟩ = some (0 : PolicyRevision) ∧
        state ⟨.policyAddress, (policy.policyId, 0)⟩ = some policy.address) ∧
    state ⟨.nullifier, descriptor.authorityNullifier⟩ = some true

theorem BatchEvidence.postcondition {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence domain pre descriptor) :
    Postcondition descriptor (post pre descriptor).logical :=
  ⟨fun grant member => evidence.installs_grant grant member,
    fun policy member => evidence.installs_policy policy member, evidence.consumes_nullifier⟩

theorem no_final_grant_erasure {registry : TypeRegistry Digest}
    {descriptor : Descriptor registry} {state : Store CredentialAuthorityState.layout}
    {grant : AuthorityGrant} (member : grant ∈ descriptor.grants)
    (missing : state (grantField grant) ≠ some grant.capability) :
    ¬Postcondition descriptor state := fun final => missing (final.1 grant member)

theorem no_final_nullifier_erasure {registry : TypeRegistry Digest}
    {descriptor : Descriptor registry} {state : Store CredentialAuthorityState.layout}
    (missing : state ⟨.nullifier, descriptor.authorityNullifier⟩ ≠ some true) :
    ¬Postcondition descriptor state := fun final => missing final.2.2

theorem no_final_policy_erasure {registry : TypeRegistry Digest}
    {descriptor : Descriptor registry} {state : Store CredentialAuthorityState.layout}
    {policy : InitialPolicy} (member : policy ∈ descriptor.initialPolicies)
    (missing : state ⟨.policyAddress, (policy.policyId, 0)⟩ ≠ some policy.address) :
    ¬Postcondition descriptor state := fun final => missing (final.2.1 policy member).2.2

theorem no_initial_policy_overwrite {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    {policy : InitialPolicy} (member : policy ∈ descriptor.initialPolicies)
    (occupied : pre.logical ⟨.policyEpoch, policy.policyId⟩ ≠ none) :
    IsEmpty (BatchEvidence domain pre descriptor) :=
  ⟨fun evidence => occupied (evidence.policiesFresh policy member).1⟩

/-- Existing source revision state cannot be overwritten by claiming its
separate generation slot was absent. Birth requires all three policy cells fresh. -/
theorem no_initial_revision_overwrite {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    {policy : InitialPolicy} (member : policy ∈ descriptor.initialPolicies)
    (occupied : pre.logical ⟨.policyRevision, policy.policyId⟩ ≠ none) :
    IsEmpty (BatchEvidence domain pre descriptor) :=
  ⟨fun evidence => occupied (evidence.policiesFresh policy member).2.1⟩

/-- A capability identifier has one revocation identity across resource kinds.
A birth cannot overwrite or shadow an existing grant of a different kind. -/
theorem no_batch_of_existing_grant_id {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    {grant : AuthorityGrant} (member : grant ∈ descriptor.grants)
    (otherKind : ResourceKind) (stored : StoredCapability otherKind)
    (occupied : readCapability pre otherKind grant.capability.head.id = some stored) :
    IsEmpty (BatchEvidence domain pre descriptor) :=
  ⟨fun evidence => (evidence.issue grant member).reject_existing_id otherKind stored occupied⟩

/-- The final joint post must retain revision zero independently of the grant
generation. An initial source address alone cannot discharge the postcondition. -/
theorem no_final_revision_erasure {registry : TypeRegistry Digest}
    {descriptor : Descriptor registry} {state : Store CredentialAuthorityState.layout}
    {policy : InitialPolicy} (member : policy ∈ descriptor.initialPolicies)
    (missing : state ⟨.policyRevision, policy.policyId⟩ ≠ some (0 : PolicyRevision)) :
    ¬Postcondition descriptor state := fun final => missing (final.2.1 policy member).2.1

/-- Distinct typed capability slots cannot excuse a shared revocation ID inside
the same batch. This is enforced by the family mode, not only by the receiver. -/
theorem no_batch_of_repeated_grant_id {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest} {domain : ProjectionUniverse}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (first second : AuthorityGrant) (grants : descriptor.grants = [first, second])
    (same : first.capability.head.id = second.capability.head.id) :
    IsEmpty (BatchEvidence domain pre descriptor) := by
  refine ⟨fun evidence => ?_⟩
  have distinct := evidence.grantIdsDistinct
  simp [Descriptor.GrantIdsDistinct, grants, same] at distinct

namespace CrossKindCollisionWitness

/-- Two closed grants with distinct typed slots but one global revocation ID. -/
def objectGrant : AuthorityGrant := ⟨.object, ⟨TypedAuthorization.demoCapability, []⟩⟩

def programGrant : AuthorityGrant :=
  ⟨.program, ⟨
    { id := TypedAuthorization.demoCapability.id
      root := TypedAuthorization.demoCapability.id
      parent := none
      issuer := ⟨1⟩
      holder := .subject ⟨4⟩
      scope := ⟨{⟨10⟩}, {.installPolicy, .revokeCapability}, 100⟩
      notBefore := 0
      notAfter := 100
      issuerEpoch := 0
      policyId := ⟨10⟩
      policyEpoch := 0
      ancestors := ∅
      channels := ∅ }, []⟩⟩

def descriptor (registry : TypeRegistry Digest) : Descriptor registry where
  factory := ⟨1⟩
  creator := ⟨4⟩
  transactionId := ⟨1⟩
  nonce := 1
  births := []
  auxiliaryCreates := []
  grants := [objectGrant, programGrant]
  initialPolicies := []
  authorityNullifier := 1
  funding := []
  fee := ⟨0, 1, 0, 0⟩

/-- The old typed-field distinctness condition alone accepts this shape. -/
theorem typed_fields_distinct (registry : TypeRegistry Digest) :
    ((entries (descriptor registry)).map Sigma.fst).Nodup := by
  change ([⟨.capability .object, TypedAuthorization.demoCapability.id⟩,
    ⟨.capability .program, TypedAuthorization.demoCapability.id⟩, ⟨.nullifier, (1 : Nat)⟩] :
      List (Address CredentialAuthorityState.layout)).Nodup
  decide

/-- The mandatory source-family evidence now rejects this same concrete
cross-kind collision for every old authority cell and revocation universe. -/
theorem refused (registry : TypeRegistry Digest)
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (domain : ProjectionUniverse) (pre : CredentialAuthorityState.Cell M) :
    IsEmpty (BatchEvidence domain pre (descriptor registry)) :=
  no_batch_of_repeated_grant_id objectGrant programGrant rfl rfl

end CrossKindCollisionWitness

/-- The authority incidence has its own actual domain pre-root. Its source
target is the pinned factory and it commits the whole same descriptor, but
it requires separate checked authorization for this exact request. -/
def request {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry) (domain : ProjectionUniverse)
    (pre : CredentialAuthorityState.Cell M) (height : Height) (descriptor : Descriptor registry) :
    Request .object :=
  factoryRequest pins encoding (authState domain pre) pre.root height descriptor

theorem factory_root_request_distinct {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry) (domain : ProjectionUniverse)
    (pre : CredentialAuthorityState.Cell M) (height : Height) (descriptor : Descriptor registry)
    (factoryRoot : Digest) (different : factoryRoot ≠ pre.root) :
    factoryRequest pins encoding (authState domain pre) factoryRoot height descriptor ≠
      request pins encoding domain pre height descriptor := by
  intro same
  exact different (congrArg Request.preStateRoot same)

def family {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry) (domain : ProjectionUniverse)
    (pre : CredentialAuthorityState.Cell M) (height : Height) :
    SemanticEffectFamily CredentialAuthorityState.layout M Nat where
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
def accept {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
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
  modeEvidence := evidence
  validated := validated pre descriptor
  postcondition := evidence.postcondition
  disclosure := .sealed
  disclosureAllowed := trivial

/-! ## Axiom accounting for the source and receiving laws -/

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.installs_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.installs_grant

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.consumes_nullifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.consumes_nullifier

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.postcondition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.postcondition

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.no_batch_of_used_nullifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.no_batch_of_used_nullifier

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.no_final_grant_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.no_final_grant_erasure

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.factory_root_request_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.factory_root_request_distinct

end Minidregg.Theory.ResourceBirthAuthority
