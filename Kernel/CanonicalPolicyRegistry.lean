/-
# Kernel.CanonicalPolicyRegistry -- durable committed policy selection

`CredentialAuthorityState` already makes the policy registry canonical: its
typed `(PolicyId, Epoch)` field stores the selected content address and the
cell root is projected as `AuthState.policyRoot`.  `CanonicalPolicyAdmission`
then resolves the same key to a versioned `Pred` record and accepts only the
compiler-emitted verifier for that addressed record.

This module closes the remaining physical-selection seams without introducing
a second policy state model:

* an actual `Authorized` determines one exact resolved policy payload;
* the canonical registry-cell address, compiler registry result, record digest,
  authenticated membership, canonical source bytes, and content-store fetch
  are joined in one proof-relevant payload;
* a durable data intent adds the exact registry cell as a read-only guard;
* registry mutation or epoch/address rotation between admission and install
  rejects the old intent before any post bytes are exposed.

Membership soundness and payload availability are explicit deployment
premises.  Digest collision resistance, signature soundness, and physical
snapshot isolation are not manufactured here; the last remains the existing
`DurableDataIntent.ImplementationRefinement` obligation.
-/
import Compiler.CanonicalPolicyAdmission
import Kernel.DurableDataIntent
import Theory.CredentialAuthorityState

namespace Minidregg.Kernel.CanonicalPolicyRegistry

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

/-! ## Canonical registry cell and content payload boundary -/

/-- The registry cell is the existing canonical authority cell.  In
particular, `policyRoot` is not a host-map digest supplied beside it. -/
abbrev RegistryCell (M : CredentialAuthorityState.Materializer) :=
  CredentialAuthorityState.Cell M

/-- Exact sparse lookup for one versioned policy address. -/
def addressAt {M : CredentialAuthorityState.Materializer} (cell : RegistryCell M)
    (policyId : PolicyId) (epoch : Epoch) : Digest :=
  CredentialAuthorityState.policyAddressAt cell policyId epoch

@[simp] theorem projected_policy_root {M : CredentialAuthorityState.Materializer}
    (projection : CredentialAuthorityState.ProjectionUniverse)
    (cell : RegistryCell M) :
    (CredentialAuthorityState.authState projection cell).policyRoot = cell.root :=
  rfl

@[simp] theorem projected_policy_address {M : CredentialAuthorityState.Materializer}
    (projection : CredentialAuthorityState.ProjectionUniverse)
    (cell : RegistryCell M)
    (policyId : PolicyId) (epoch : Epoch) :
    (CredentialAuthorityState.authState projection cell).policyAddress policyId epoch =
      addressAt cell policyId epoch :=
  rfl

/-- Canonical source encoding and the deployment digest used by
`CanonicalPolicyConfig.recordDigest`.  This is an exact representation bridge,
not a collision-resistance assumption. -/
structure ContentAddressing {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) where
  codec : LawfulCodec PolicyRecord
  hashBytes : List UInt8 -> Digest
  recordDigest_exact : forall record,
    config.recordDigest record = hashBytes (codec.encode record)

/-- Physical or replicated content storage is an explicit read interface. -/
structure PayloadStore where
  fetch : Digest -> Option (List UInt8)

/-- Availability is a deployment premise: every registry result used by this
configuration is fetchable at its canonical encoded bytes.  No filesystem,
database, or replication theorem is inferred from a lookup function. -/
structure PayloadAvailability {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F)
    (addressing : ContentAddressing config) (store : PayloadStore) : Prop where
  fetch_resolved : forall {policyId epoch committed},
    config.registry.resolve policyId epoch = some committed ->
      store.fetch committed.address = some (addressing.codec.encode committed.record)

/-- Cryptographic membership is interpreted by a deployment relation.  The
Boolean verifier is sound only through this premise; the logical kernel does
not call `true` a Merkle proof. -/
structure MembershipSemantics (portal : Portal) where
  Member : Digest -> Digest -> Prop
  verifier_sound : forall root address witness,
    portal.verifyMembership root address witness = true -> Member root address

/-! ## Exact selection extracted from `Authorized` -/

/-- The canonical compiler gate necessarily accepted whenever the specialized
`Authorized` exists. -/
theorem authorized_verifies
    {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F}
    {state : AuthState} {kind : ResourceKind} {request : Request kind}
    (authorized : CanonicalAuthorized config state request) :
    config.verifies request authorized.policyWitness = true := by
  have accepted := authorized.policyVerified
  rw [portal_verifyCommittedPolicy] at accepted
  simp only [Bool.and_eq_true] at accepted
  exact accepted.2

/-- All exact facts obtained when one already named registry result is the
result selected by the accepted compiler gate.  This proposition contains no
new data choice, so it can safely feed the data-bearing payload constructor. -/
structure ResolvedExact
    {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F) {kind : ResourceKind}
    (request : Request kind) (witness : CompiledPolicyWitness F)
    (committed : CommittedPolicy) : Prop where
  recordPolicyExact : committed.record.policyId = request.policyId
  recordEpochExact : committed.record.version = request.policyEpoch
  recordDomainExact : committed.record.domain = request.domain
  recordSemanticsExact : committed.record.semantics = request.semantics
  recordAddressExact : config.recordDigest committed.record = committed.address
  witnessAddressExact : witness.address = committed.address
  sourcePredicateAccepted :
    Minidregg.Pred.eval committed.record.predicate
      witness.oldState witness.newState = true

theorem authorized_resolved_exact
    {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F}
    {state : AuthState} {kind : ResourceKind} {request : Request kind}
    (authorized : CanonicalAuthorized config state request)
    {committed : CommittedPolicy}
    (resolved : config.registry.resolve request.policyId request.policyEpoch =
      some committed) :
    ResolvedExact config request authorized.policyWitness committed := by
  have policyAccepted := authorized_verifies authorized
  rcases (verifies_iff_verified config request authorized.policyWitness).mp
      policyAccepted with
    ⟨selected, selectedResolved, policyIdExact, epochExact, domainExact,
      semanticsExact, recordAddress, witnessAddress, _, _, _, _, _⟩
  rw [resolved] at selectedResolved
  cases selectedResolved
  have predicateAccepted : Minidregg.Pred.eval committed.record.predicate
      authorized.policyWitness.oldState authorized.policyWitness.newState = true := by
    rcases verifies_sound policyAccepted with
      ⟨selected, selectedResolved, evaluated⟩
    rw [resolved] at selectedResolved
    cases selectedResolved
    exact evaluated
  exact
    { recordPolicyExact := policyIdExact
      recordEpochExact := epochExact
      recordDomainExact := domainExact
      recordSemanticsExact := semanticsExact
      recordAddressExact := recordAddress
      witnessAddressExact := witnessAddress
      sourcePredicateAccepted := predicateAccepted }

/-- If the compiler registry resolves the selected key to `committed`, the
canonical authority cell must name exactly that address.  A host registry and
the authenticated cell cannot silently select different policy content. -/
theorem authorized_address_exact_of_resolved
    {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F}
    {M : CredentialAuthorityState.Materializer}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {cell : RegistryCell M} {kind : ResourceKind} {request : Request kind}
    (authorized : CanonicalAuthorized config
      (CredentialAuthorityState.authState projection cell) request)
    {committed : CommittedPolicy}
    (resolved : config.registry.resolve request.policyId request.policyEpoch =
      some committed) :
    addressAt cell request.policyId request.policyEpoch = committed.address := by
  have verified := authorized_resolved_exact authorized resolved
  have selectedByCell : authorized.policyWitness.address =
      addressAt cell request.policyId request.policyEpoch := by
    simpa [CanonicalPolicyConfig.portal] using
      authorized.policyAddressExact
  exact selectedByCell.symm.trans verified.witnessAddressExact

/-- One proof-relevant, canonical policy selection.  Its source bytes and
physical fetch are data; its authenticated membership and all semantic
equalities remain indexed by the exact `Authorized` and exact registry cell. -/
structure SelectionPayload
    {F : Type} [Field F] [DecidableEq F]
    (config : CanonicalPolicyConfig F)
    (addressing : ContentAddressing config) (store : PayloadStore)
    (membership : MembershipSemantics config.portal)
    {M : CredentialAuthorityState.Materializer}
    (projection : CredentialAuthorityState.ProjectionUniverse)
    (cell : RegistryCell M)
    {kind : ResourceKind} (request : Request kind)
    (authorized : CanonicalAuthorized config
      (CredentialAuthorityState.authState projection cell) request) where
  committed : CommittedPolicy
  registryResolved :
    config.registry.resolve request.policyId request.policyEpoch = some committed
  recordPolicyExact : committed.record.policyId = request.policyId
  recordEpochExact : committed.record.version = request.policyEpoch
  recordDomainExact : committed.record.domain = request.domain
  recordSemanticsExact : committed.record.semantics = request.semantics
  registryAddressExact :
    addressAt cell request.policyId request.policyEpoch = committed.address
  recordAddressExact : config.recordDigest committed.record = committed.address
  canonicalBytes : List UInt8
  canonicalBytesExact : canonicalBytes = addressing.codec.encode committed.record
  canonicalAddressExact : addressing.hashBytes canonicalBytes = committed.address
  payloadFetched : store.fetch committed.address = some canonicalBytes
  authenticatedMember : membership.Member cell.root committed.address
  sourcePredicateAccepted :
    Minidregg.Pred.eval committed.record.predicate
      authorized.policyWitness.oldState authorized.policyWitness.newState = true

/-- Extract the joined payload.  The only non-semantic inputs are the explicit
membership-soundness and payload-availability premises above. -/
def SelectionPayload.ofAuthorized
    {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F}
    {addressing : ContentAddressing config} {store : PayloadStore}
    {membership : MembershipSemantics config.portal}
    {availability : PayloadAvailability config addressing store}
    {M : CredentialAuthorityState.Materializer}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {cell : RegistryCell M}
    {kind : ResourceKind} {request : Request kind}
    (authorized : CanonicalAuthorized config
      (CredentialAuthorityState.authState projection cell) request)
    (committed : CommittedPolicy)
    (resolved : config.registry.resolve request.policyId request.policyEpoch =
      some committed) :
    SelectionPayload config addressing store membership projection cell request
      authorized := by
  have exact := authorized_resolved_exact authorized resolved
  have registryAddress := authorized_address_exact_of_resolved authorized resolved
  have membershipVerified : config.portal.verifyMembership cell.root
      committed.address authorized.policyMembershipWitness = true := by
    have verified := authorized.policyMembershipVerified
    change config.portal.verifyMembership cell.root
      (addressAt cell request.policyId request.policyEpoch)
      authorized.policyMembershipWitness = true at verified
    rw [registryAddress] at verified
    exact verified
  refine
    { committed := committed
      registryResolved := resolved
      recordPolicyExact := exact.recordPolicyExact
      recordEpochExact := exact.recordEpochExact
      recordDomainExact := exact.recordDomainExact
      recordSemanticsExact := exact.recordSemanticsExact
      registryAddressExact := registryAddress
      recordAddressExact := exact.recordAddressExact
      canonicalBytes := addressing.codec.encode committed.record
      canonicalBytesExact := rfl
      canonicalAddressExact := ?_
      payloadFetched := availability.fetch_resolved resolved
      authenticatedMember := membership.verifier_sound _ _ _ membershipVerified
      sourcePredicateAccepted := exact.sourcePredicateAccepted }
  exact (addressing.recordDigest_exact committed.record).symm.trans
    exact.recordAddressExact

/-! ## Wrong-address tooth -/

/-- A resolved compiler record at any address other than the canonical cell's
selected address is incompatible with `Authorized`. -/
theorem wrong_address_precludes_authorized
    {F : Type} [Field F] [DecidableEq F]
    {config : CanonicalPolicyConfig F}
    {M : CredentialAuthorityState.Materializer}
    {projection : CredentialAuthorityState.ProjectionUniverse}
    {cell : RegistryCell M} {kind : ResourceKind} {request : Request kind}
    {committed : CommittedPolicy}
    (resolved : config.registry.resolve request.policyId request.policyEpoch =
      some committed)
    (wrong : addressAt cell request.policyId request.policyEpoch ≠ committed.address) :
    IsEmpty (CanonicalAuthorized config
      (CredentialAuthorityState.authState projection cell) request) :=
  ⟨fun authorized =>
    wrong (authorized_address_exact_of_resolved authorized resolved)⟩

/-! ## Durable read guard -/

/-- The authority/registry materializer and the durable data snapshot use the
same deployment digest function.  This is representation agreement, not CR. -/
structure SharedDigest
    (M : CredentialAuthorityState.Materializer)
    (rootBytes : List UInt8 -> Digest) : Prop where
  exact : M.rootBytes = rootBytes

/-- Add the canonical registry root as a read-only durable guard.  The base
intent's writes, payload bytes, nullifiers, charge, semantic event, and prior
guards are preserved exactly; the new guard is retained in replay identity. -/
def guardPolicyRegistry
    {rootBytes : List UInt8 -> Digest} {M : CredentialAuthorityState.Materializer}
    (cell : RegistryCell M) (cellId : CellId)
    (_digest : SharedDigest M rootBytes)
    (intent : DataIntent rootBytes)
    (readOnly : cellId ∉ intent.writes.map DataWrite.cellId) :
    DataIntent rootBytes where
  transactionId := intent.transactionId
  writes := intent.writes
  readGuards :=
    { cellId := cellId, expectedRoot := rootBytes cell.bytes } :: intent.readGuards
  nullifiers := intent.nullifiers
  exactCharge := intent.exactCharge
  event := intent.event
  postRootsBound := intent.postRootsBound
  guardsReadOnly := by
    intro guard member
    rcases List.mem_cons.mp member with rfl | oldMember
    · exact readOnly
    · exact intent.guardsReadOnly guard oldMember

@[simp] theorem guardPolicyRegistry_readGuards
    {rootBytes : List UInt8 -> Digest} {M : CredentialAuthorityState.Materializer}
    (cell : RegistryCell M) (cellId : CellId)
    (digest : SharedDigest M rootBytes)
    (intent : DataIntent rootBytes)
    (readOnly : cellId ∉ intent.writes.map DataWrite.cellId) :
    (guardPolicyRegistry cell cellId digest intent readOnly).readGuards =
      { cellId := cellId, expectedRoot := cell.root } :: intent.readGuards := by
  have rootExact : rootBytes cell.bytes = cell.root :=
    congrFun digest.exact cell.bytes |>.symm
  simp [guardPolicyRegistry, rootExact]

/-- Adding the read guard does not alter ordinary durable preflight: root
writes, nullifiers, and charge are byte-for-byte the base intent's values. -/
theorem guardPolicyRegistry_erased_preflight
    {rootBytes : List UInt8 -> Digest} {M : CredentialAuthorityState.Materializer}
    (cell : RegistryCell M) (cellId : CellId)
    (_digest : SharedDigest M rootBytes)
    (intent : DataIntent rootBytes)
    (readOnly : cellId ∉ intent.writes.map DataWrite.cellId)
    (before : Snapshot TransactionId CellId StableNullifier ReplayEnvelope) :
    (guardPolicyRegistry cell cellId _digest intent readOnly).erase.preflight before =
      intent.erase.preflight before := by
  rfl

/-- Positive tooth: if the base intent is ready and the exact registry root is
still current, adding policy settlement keeps it ready. -/
theorem guardPolicyRegistry_preflight_ready
    {rootBytes : List UInt8 -> Digest} {M : CredentialAuthorityState.Materializer}
    (cell : RegistryCell M) (cellId : CellId)
    (digest : SharedDigest M rootBytes)
    (intent : DataIntent rootBytes)
    (readOnly : cellId ∉ intent.writes.map DataWrite.cellId)
    (before : DataSnapshot rootBytes)
    (rootCurrent : before.model.roots cellId = cell.root)
    (baseReady : intent.preflight before = .ok ()) :
    (guardPolicyRegistry cell cellId digest intent readOnly).preflight before =
      .ok () := by
  have rootExact : rootBytes cell.bytes = cell.root :=
    congrFun digest.exact cell.bytes |>.symm
  have baseGuardReady : intent.readGuardsMatchCheck before = true := by
    by_cases ready : intent.readGuardsMatchCheck before = true
    · exact ready
    · have falseCheck : intent.readGuardsMatchCheck before = false :=
        Bool.eq_false_of_not_eq_true ready
      simp [DataIntent.preflight, falseCheck] at baseReady
  have durableReady : intent.erase.preflight before.model = .ok () := by
    cases durable : intent.erase.preflight before.model with
    | error reason =>
        simp [DataIntent.preflight, baseGuardReady, durable] at baseReady
    | ok result =>
        cases result
        rfl
  have guardedReady :
      (guardPolicyRegistry cell cellId digest intent readOnly).readGuardsMatchCheck
        before = true := by
    apply (DataIntent.readGuardsMatchCheck_eq_true_iff before _).mpr
    intro guard member
    rcases List.mem_cons.mp member with rfl | oldMember
    · exact rootCurrent.trans rootExact.symm
    · exact (DataIntent.readGuardsMatchCheck_eq_true_iff before intent).mp
        baseGuardReady guard oldMember
  simp only [DataIntent.preflight, guardedReady, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  rw [guardPolicyRegistry_erased_preflight, durableReady]

/-- Stale-root tooth: policy mutation, address replacement, or epoch rotation
which changes the canonical registry root rejects the old admitted intent. -/
theorem policy_registry_rotation_rejects_old_intent
    {rootBytes : List UInt8 -> Digest} {M : CredentialAuthorityState.Materializer}
    (cell : RegistryCell M) (cellId : CellId)
    (digest : SharedDigest M rootBytes)
    (intent : DataIntent rootBytes)
    (readOnly : cellId ∉ intent.writes.map DataWrite.cellId)
    (current : DataSnapshot rootBytes)
    (moved : current.model.roots cellId ≠ cell.root) :
    (guardPolicyRegistry cell cellId digest intent readOnly).preflight current =
      .error .staleReadGuard := by
  apply stale_read_guard_rejected
  let guard : ReadGuard :=
    { cellId := cellId, expectedRoot := rootBytes cell.bytes }
  have rootExact : guard.expectedRoot = cell.root :=
    congrFun digest.exact cell.bytes |>.symm
  refine ⟨guard, ?_, ?_⟩
  · simp [guard, guardPolicyRegistry]
  · have notEqual : current.model.roots guard.cellId ≠ guard.expectedRoot := by
      intro equal
      exact moved (equal.trans rootExact)
    simpa using notEqual

end Minidregg.Kernel.CanonicalPolicyRegistry

/-! Kernel-facing theorem audit. -/

/-- info: 'Minidregg.Kernel.CanonicalPolicyRegistry.authorized_address_exact_of_resolved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Kernel.CanonicalPolicyRegistry.authorized_address_exact_of_resolved
/-- info: 'Minidregg.Kernel.CanonicalPolicyRegistry.SelectionPayload.ofAuthorized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Kernel.CanonicalPolicyRegistry.SelectionPayload.ofAuthorized
/-- info: 'Minidregg.Kernel.CanonicalPolicyRegistry.guardPolicyRegistry_preflight_ready' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Kernel.CanonicalPolicyRegistry.guardPolicyRegistry_preflight_ready
/-- info: 'Minidregg.Kernel.CanonicalPolicyRegistry.policy_registry_rotation_rejects_old_intent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms Minidregg.Kernel.CanonicalPolicyRegistry.policy_registry_rotation_rejects_old_intent
