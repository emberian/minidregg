/-
# Theory.ResourceBirthAuthority -- one authority effect for one birth batch

Every root-capability issue is checked against the same original canonical
authority cell using the existing IssueEvidence. The batch installs the exact
declared stored capabilities, registers each grant's own revocation key in the
append-only `registered` plane. Its one shared nullifier (`authorityNullifier`)
is consumed in the durable nullifier set by the receiver, not written to the
authority cell. It never uses one newborn grant as authority for a later grant.

The physical receiver computes its routed shard updates independently
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

def grantEntry (grant : AuthorityGrant) : Entry CredentialAuthorityState.layout :=
  ⟨grantField grant, grant.capability⟩

/-- The registration of a grant's own revocation key, allocated by the birth. -/
def grantRegistrationEntry (grant : AuthorityGrant) : Entry CredentialAuthorityState.layout :=
  registrationEntry (.capability grant.capability.head.id)

def policyEpochEntry (policy : InitialPolicy) : Entry CredentialAuthorityState.layout :=
  ⟨⟨.policyEpoch, policy.policyId⟩, (0 : Epoch)⟩

def policyRevisionEntry (policy : InitialPolicy) : Entry CredentialAuthorityState.layout :=
  ⟨⟨.policyRevision, policy.policyId⟩, (0 : PolicyRevision)⟩

def policyAddressEntry (policy : InitialPolicy) : Entry CredentialAuthorityState.layout :=
  ⟨⟨.policyAddress, (policy.policyId, 0)⟩, policy.address⟩

def policyEntries (policy : InitialPolicy) : List (Entry CredentialAuthorityState.layout) :=
  [policyEpochEntry policy, policyRevisionEntry policy, policyAddressEntry policy]

def issueDeclaration (preRoot : Digest) (nullifier : Nat) (grant : AuthorityGrant) :
    IssueDeclaration grant.kind where
  capability := grant.capability.head
  expectedPreRoot := preRoot
  operationNullifier := nullifier

def entries {registry : TypeRegistry Digest} (descriptor : Descriptor registry) :
    List (Entry CredentialAuthorityState.layout) :=
  descriptor.initialPolicies.flatMap policyEntries ++
    descriptor.grants.map grantEntry ++ descriptor.grants.map grantRegistrationEntry

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
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry) where
  slotsDistinct : ((entries descriptor).map Sigma.fst).Nodup
  grantIdsDistinct : descriptor.GrantIdsDistinct
  policiesFresh : ∀ policy ∈ descriptor.initialPolicies,
    pre.logical ⟨.policyEpoch, policy.policyId⟩ = none ∧
      pre.logical ⟨.policyRevision, policy.policyId⟩ = none ∧
      pre.logical ⟨.policyAddress, (policy.policyId, 0)⟩ = none
  ancestryEmpty : ∀ grant ∈ descriptor.grants, grant.capability.ancestry = []
  issue : ∀ grant ∈ descriptor.grants,
    IssueEvidence pre (issueDeclaration pre.root descriptor.authorityNullifier grant)

/-- Every entry of an evidenced batch is assignable at the pre-cell: policy and
grant records are RAM and each grant's key is not yet registered. -/
theorem BatchEvidence.entries_assignable {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence pre descriptor) :
    ∀ entry ∈ entries descriptor, Assignable pre.logical entry.1 := by
  intro entry member
  simp only [entries, List.mem_append, List.mem_flatMap, List.mem_map] at member
  rcases member with (⟨policy, _, inPolicy⟩ | ⟨grant, _, rfl⟩) | ⟨grant, grantMember, rfl⟩
  · simp only [policyEntries, List.mem_cons, List.not_mem_nil, or_false] at inPolicy
    rcases inPolicy with rfl | rfl | rfl <;> exact assignable_of_ram _ _ rfl
  · exact assignable_of_ram _ _ rfl
  · exact assignable_of_absent _ _ (evidence.issue grant grantMember).selfUnregistered

/-- Satisfiable pole: an evidenced batch patch is valid at its own pre. -/
theorem BatchEvidence.valid {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence pre descriptor) :
    Patch.ValidFrom pre.logical (patch pre descriptor) :=
  assignAll_valid _ _ (assignableAll_of_nodup _ _ evidence.slotsDistinct evidence.entries_assignable)

theorem validated {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry)
    (evidence : BatchEvidence pre descriptor) :
    ValidatedPatch M pre pre.root (patch pre descriptor) := by
  obtain ⟨validated, _⟩ := CellState.validate_accepts M pre pre.root
    (patch pre descriptor) rfl evidence.valid
  exact validated

def post {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry)
    (evidence : BatchEvidence pre descriptor) :
    CredentialAuthorityState.Cell M :=
  (validated pre descriptor evidence).apply

theorem post_logical {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry)
    (evidence : BatchEvidence pre descriptor) :
    (post pre descriptor evidence).logical = setAll pre.logical (entries descriptor) :=
  run_assignAll _ _

theorem BatchEvidence.writes_distinct {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence pre descriptor) :
    ((entries descriptor).map Sigma.fst).Nodup := evidence.slotsDistinct

theorem BatchEvidence.installs_grant {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence pre descriptor)
    (grant : AuthorityGrant) (member : grant ∈ descriptor.grants) :
    (post pre descriptor evidence).logical (grantField grant) = some grant.capability := by
  rw [post_logical]
  exact setAll_member _ (entries descriptor) evidence.writes_distinct (grantEntry grant)
      (by simp only [entries, List.mem_append, List.mem_map]; exact Or.inl (Or.inr ⟨grant, member, rfl⟩))

/-- **Birth registers.**  Each grant's own revocation key is in the post-cell's
`registered` plane, allocated by the batch patch itself. -/
theorem BatchEvidence.registers_grant {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence pre descriptor)
    (grant : AuthorityGrant) (member : grant ∈ descriptor.grants) :
    (post pre descriptor evidence).logical ⟨.registered, .capability grant.capability.head.id⟩ =
      some () := by
  rw [post_logical]
  exact setAll_member _ (entries descriptor) evidence.writes_distinct (grantRegistrationEntry grant)
      (by simp only [entries, List.mem_append, List.mem_map]; exact Or.inr ⟨grant, member, rfl⟩)

/-- Refuting pole: a birth whose grant key is already registered has no
evidence; a capability identifier is registered once, ever. -/
theorem no_batch_of_registered_grant {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    {grant : AuthorityGrant} (member : grant ∈ descriptor.grants)
    (registered : isRegistered pre (.capability grant.capability.head.id) = true) :
    IsEmpty (BatchEvidence pre descriptor) :=
  ⟨fun evidence => Bool.noConfusion
    (registered.symm.trans (evidence.issue grant member).selfUnregistered)⟩

theorem BatchEvidence.installs_policy {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence pre descriptor)
    (policy : InitialPolicy) (member : policy ∈ descriptor.initialPolicies) :
    (post pre descriptor evidence).logical ⟨.policyEpoch, policy.policyId⟩ = some (0 : Epoch) ∧
      (post pre descriptor evidence).logical ⟨.policyRevision, policy.policyId⟩ =
        some (0 : PolicyRevision) ∧
      (post pre descriptor evidence).logical ⟨.policyAddress, (policy.policyId, 0)⟩ =
        some policy.address := by
  refine ⟨?_, ?_, ?_⟩
  · rw [post_logical]
    exact setAll_member _ (entries descriptor) evidence.writes_distinct
      (policyEpochEntry policy)
      (by
        simp only [entries, List.mem_append]
        exact Or.inl (Or.inl (List.mem_flatMap.mpr ⟨policy, member, by simp [policyEntries]⟩)))
  · rw [post_logical]
    exact setAll_member _ (entries descriptor) evidence.writes_distinct
      (policyRevisionEntry policy)
      (by
        simp only [entries, List.mem_append]
        exact Or.inl (Or.inl (List.mem_flatMap.mpr ⟨policy, member, by simp [policyEntries]⟩)))
  · rw [post_logical]
    exact setAll_member _ (entries descriptor) evidence.writes_distinct
      (policyAddressEntry policy)
      (by
        simp only [entries, List.mem_append]
        exact Or.inl (Or.inl (List.mem_flatMap.mpr ⟨policy, member, by simp [policyEntries]⟩)))

theorem post_frame {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) (descriptor : Descriptor registry)
    (evidence : BatchEvidence pre descriptor)
    (address : Address CredentialAuthorityState.layout)
    (outside : address ∉ Patch.writeFootprint (patch pre descriptor)) :
    (post pre descriptor evidence).logical address = pre.logical address :=
  Patch.run_frame pre.logical _ address outside

theorem no_batch_of_nonroot_lineage {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    {grant : AuthorityGrant} (member : grant ∈ descriptor.grants)
    (nonempty : grant.capability.ancestry ≠ []) :
    IsEmpty (BatchEvidence pre descriptor) :=
  ⟨fun evidence => nonempty (evidence.ancestryEmpty grant member)⟩

/-- These exact semantic outcomes must survive the final composed post:
every complete stored grant, every initial policy head, and every grant's
registration. Source bytes are checked and retained by the physical compiler. -/
def Postcondition {registry : TypeRegistry Digest} (descriptor : Descriptor registry)
    (state : Store CredentialAuthorityState.layout) : Prop :=
  (∀ grant ∈ descriptor.grants, state (grantField grant) = some grant.capability) ∧
    (∀ policy ∈ descriptor.initialPolicies,
      state ⟨.policyEpoch, policy.policyId⟩ = some (0 : Epoch) ∧
        state ⟨.policyRevision, policy.policyId⟩ = some (0 : PolicyRevision) ∧
        state ⟨.policyAddress, (policy.policyId, 0)⟩ = some policy.address) ∧
    (∀ grant ∈ descriptor.grants,
      state ⟨.registered, .capability grant.capability.head.id⟩ = some ())

theorem BatchEvidence.postcondition {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (evidence : BatchEvidence pre descriptor) :
    Postcondition descriptor (post pre descriptor evidence).logical :=
  ⟨fun grant member => evidence.installs_grant grant member,
    fun policy member => evidence.installs_policy policy member,
    fun grant member => evidence.registers_grant grant member⟩

theorem no_final_grant_erasure {registry : TypeRegistry Digest}
    {descriptor : Descriptor registry} {state : Store CredentialAuthorityState.layout}
    {grant : AuthorityGrant} (member : grant ∈ descriptor.grants)
    (missing : state (grantField grant) ≠ some grant.capability) :
    ¬Postcondition descriptor state := fun final => missing (final.1 grant member)

/-- The final joint post must retain every grant's registration. -/
theorem no_final_registration_erasure {registry : TypeRegistry Digest}
    {descriptor : Descriptor registry} {state : Store CredentialAuthorityState.layout}
    {grant : AuthorityGrant} (member : grant ∈ descriptor.grants)
    (missing : state ⟨.registered, .capability grant.capability.head.id⟩ ≠ some ()) :
    ¬Postcondition descriptor state := fun final => missing (final.2.2 grant member)

theorem no_final_policy_erasure {registry : TypeRegistry Digest}
    {descriptor : Descriptor registry} {state : Store CredentialAuthorityState.layout}
    {policy : InitialPolicy} (member : policy ∈ descriptor.initialPolicies)
    (missing : state ⟨.policyAddress, (policy.policyId, 0)⟩ ≠ some policy.address) :
    ¬Postcondition descriptor state := fun final => missing (final.2.1 policy member).2.2

theorem no_initial_policy_overwrite {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    {policy : InitialPolicy} (member : policy ∈ descriptor.initialPolicies)
    (occupied : pre.logical ⟨.policyEpoch, policy.policyId⟩ ≠ none) :
    IsEmpty (BatchEvidence pre descriptor) :=
  ⟨fun evidence => occupied (evidence.policiesFresh policy member).1⟩

/-- Existing source revision state cannot be overwritten by claiming its
separate generation slot was absent. Birth requires all three policy cells fresh. -/
theorem no_initial_revision_overwrite {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    {policy : InitialPolicy} (member : policy ∈ descriptor.initialPolicies)
    (occupied : pre.logical ⟨.policyRevision, policy.policyId⟩ ≠ none) :
    IsEmpty (BatchEvidence pre descriptor) :=
  ⟨fun evidence => occupied (evidence.policiesFresh policy member).2.1⟩

/-- A capability identifier has one revocation identity across resource kinds.
A birth cannot overwrite or shadow an existing grant of a different kind. -/
theorem no_batch_of_existing_grant_id {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    {grant : AuthorityGrant} (member : grant ∈ descriptor.grants)
    (otherKind : ResourceKind) (stored : StoredCapability otherKind)
    (occupied : readCapability pre otherKind grant.capability.head.id = some stored) :
    IsEmpty (BatchEvidence pre descriptor) :=
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
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    {pre : CredentialAuthorityState.Cell M} {descriptor : Descriptor registry}
    (first second : AuthorityGrant) (grants : descriptor.grants = [first, second])
    (same : first.capability.head.id = second.capability.head.id) :
    IsEmpty (BatchEvidence pre descriptor) := by
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
      scope := ⟨.explicit {⟨10⟩}, {.installPolicy, .revokeCapability}, 100⟩
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

/-- The typed capability slots are distinct, but the batch's own registration
entries name ONE `registered` address twice: a revocation ID shared across kinds
already fails slot distinctness, because registration is keyed by the ID alone. -/
theorem registration_slots_collide (registry : TypeRegistry Digest) :
    ¬ ((entries (descriptor registry)).map Sigma.fst).Nodup := by
  change ¬ ([⟨.capability .object, TypedAuthorization.demoCapability.id⟩,
    ⟨.capability .program, TypedAuthorization.demoCapability.id⟩,
    ⟨.registered, .capability TypedAuthorization.demoCapability.id⟩,
    ⟨.registered, .capability TypedAuthorization.demoCapability.id⟩] :
      List (Address CredentialAuthorityState.layout)).Nodup
  decide

/-- The mandatory source-family evidence now rejects this same concrete
cross-kind collision for every authority cell. -/
theorem refused (registry : TypeRegistry Digest)
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pre : CredentialAuthorityState.Cell M) :
    IsEmpty (BatchEvidence pre (descriptor registry)) :=
  no_batch_of_repeated_grant_id objectGrant programGrant rfl rfl

end CrossKindCollisionWitness

/-- The authority incidence has its own actual pre-root. Its source
target is the pinned factory and it commits the whole same descriptor, but
it requires separate checked authorization for this exact request. -/
def request {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (pre : CredentialAuthorityState.Cell M) (height : Height) (descriptor : Descriptor registry) :
    Request .object :=
  factoryRequest pins encoding (authState pre) pre.root height descriptor

theorem factory_root_request_distinct {registry : TypeRegistry Digest}
    {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (pre : CredentialAuthorityState.Cell M) (height : Height) (descriptor : Descriptor registry)
    (factoryRoot : Digest) (different : factoryRoot ≠ pre.root) :
    factoryRequest pins encoding (authState pre) factoryRoot height descriptor ≠
      request pins encoding pre height descriptor := by
  intro same
  exact different (congrArg Request.preStateRoot same)

def family {registry : TypeRegistry Digest} {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (pre : CredentialAuthorityState.Cell M) (height : Height) :
    SemanticEffectFamily CredentialAuthorityState.layout M Nat where
  pre := pre
  Declaration := Descriptor registry
  declarationCodec := encoding.codec
  request descriptor := ⟨.object, request pins encoding pre height descriptor⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => CredentialAuthorityEffects.unitCodec
  ModeEvidence := fun descriptor _ => BatchEvidence pre descriptor
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
    {pins : FactoryPins} {encoding : SourceEncoding registry}
    {pre : CredentialAuthorityState.Cell M} {height : Height} {descriptor : Descriptor registry}
    {portal : Portal} (evidence : BatchEvidence pre descriptor)
    (authorization : Authorized portal (authState pre)
      (request pins encoding pre height descriptor)) :
    AcceptedCellEffect (portal := portal) (authState := authState pre)
      (family pins encoding pre height) (request pins encoding pre height descriptor)
      pre descriptor () where
  authorization := authorization
  preStateBound := rfl
  requestBound := rfl
  effectsDigestBound := rfl
  modeEvidence := evidence
  validated := validated pre descriptor evidence
  postcondition := evidence.postcondition
  disclosure := .sealed
  disclosureAllowed := trivial

/-! ## Axiom accounting for the source and receiving laws -/

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.installs_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.installs_grant

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.postcondition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.postcondition

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.no_final_grant_erasure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.no_final_grant_erasure

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.factory_root_request_distinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.factory_root_request_distinct

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.valid

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.registers_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.BatchEvidence.registers_grant

/-- info: 'Minidregg.Theory.ResourceBirthAuthority.no_batch_of_registered_grant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Theory.ResourceBirthAuthority.no_batch_of_registered_grant

end Minidregg.Theory.ResourceBirthAuthority
