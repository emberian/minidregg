/-
# Kernel.ResourceBirthReceiver -- accepted birth to one durable data intent

The policy controller owns signed ingress admission. This module connects its
complete accepted heterogeneous turn to the exact source-prepared physical
writes, without executing a second allocator, authority updater or resource
program. Policy-source read dependencies join the existing complete authority
guards. The native receiver remains the existing exact-byte journal/CAS loop.

Stable replay identity retains exact ingress bytes and the complete descriptor;
matching a recorded ingress precedes any new nullifier or state-root admission.
A replay returns the recorded receipt and performs no new semantic execution.
-/
module

public import Kernel.ResourceBirthPolicyController
public import Compiler.DurableReceiverIO
public import Compiler.CredentialAuthorityReplay
public import Kernel.PlatformCellDomain
public import Compiler.ServedBasis

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Kernel.ResourceBirthReceiver

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ResourceBirthPolicyController.Concrete
open Minidregg.Compiler.ServedBasis (Ground)

set_option autoImplicit false

-- Keep typeclass inference from trying to invert the concrete cSHAKE profile.
-- Runtime computation and the source identity equations remain unchanged.
attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

variable {F : Type} [Field F] {profile : CanonicalRuntimeProfile.Profile F}
variable {deployment : CanonicalCellRegistry.Deployment} {pins : FactoryPins}
variable {ground : Ground deployment}
variable {descriptor : Descriptor CanonicalCellRegistry.registry}

/-! ## Exact semantic and physical post correspondence -/

theorem tuple_source_exact
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins ground descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height)) :
    tuple.source = ⟨descriptor, rfl⟩ :=
  Subtype.ext tuple.source.property

/-- Every tuple under this concrete plan has the same source-computed final
cells. Validation proofs do not choose values or supply independent readouts. -/
theorem tuple_post_exact
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins ground descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (incidence : Legs descriptor) :
    tuple.post incidence = (validated prepared height incidence).apply := by
  apply CellState.Materialized.ext
  simp only [PreparedTuple.post, CellState.ValidatedPatch.apply]
  rw [tuple_source_exact prepared height tuple]
  rfl

/-- All deferred mode evidence and authorizations are required here. The
accepted post is exactly the source result already used by policy evaluation. -/
theorem accepted_post_exact
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins ground descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (portals : Legs descriptor → Portal)
    (evidence : tuple.AdmissionEvidence portals) (incidence : Legs descriptor) :
    (tuple.toDeclaration portals
      (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor)).post
      (tuple.accept portals (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor) evidence)
      incidence = (validated prepared height incidence).apply :=
  (tuple.accepted_posts_exact portals _ evidence incidence).trans
    (tuple_post_exact prepared height tuple incidence)

theorem accepted_book_post
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins ground descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (portals : Legs descriptor → Portal) (evidence : tuple.AdmissionEvidence portals) :
    (tuple.toDeclaration portals
      (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor)).post
      (tuple.accept portals (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor) evidence)
      .book = prepared.resources.post :=
  accepted_post_exact prepared height tuple portals evidence .book

/-- The authority incidence is the one pinned authority cell. Its accepted post
is exactly the cell the grant batch writes. -/
theorem accepted_authority_post
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins ground descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (portals : Legs descriptor → Portal) (evidence : tuple.AdmissionEvidence portals) :
    (tuple.toDeclaration portals
      (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor)).post
      (tuple.accept portals (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor) evidence)
      .authority = prepared.grants.post :=
  accepted_post_exact prepared height tuple portals evidence .authority

/-- Allocation posts are already physical lifecycle envelopes. The equality
prevents double wrapping and preserves the exact signed typed payload. -/
theorem accepted_allocation_bytes
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins ground descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (portals : Legs descriptor → Portal) (evidence : tuple.AdmissionEvidence portals)
    (index : Fin descriptor.createRequests.length) :
    ((tuple.toDeclaration portals
      (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor)).post
      (tuple.accept portals (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor) evidence)
      (.allocation index)).bytes =
      (ResourceBirthController.birthWrite (creation descriptor index)).canonicalPostBytes := by
  rw [accepted_post_exact prepared height tuple portals evidence (.allocation index)]
  change (LifecycleSlot.materializer CanonicalCellRegistry.registry).codec.encode
    (ResourceBirthController.allocationValidated ground.directory
      (creation descriptor index) (allocationFresh prepared index)).apply.logical = _
  rw [ResourceBirthController.allocation_post_exact _ _ (allocationFresh prepared index)]
  simpa only [LifecycleSlot.cell, CellState.materialize, CellState.Materialized.bytes,
    ResourceBirthController.birthWrite] using
    LifecycleSlot.bytes_exact CanonicalCellRegistry.registry (.live (creation descriptor index).cell)

theorem accepted_book_conserves
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment pins ground descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height))
    (portals : Legs descriptor → Portal) (evidence : tuple.AdmissionEvidence portals)
    (asset : Nat) :
    (CanonicalResourceKernel.logicalBook
      ((tuple.toDeclaration portals
        (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor)).post
        (tuple.accept portals (CanonicalCellRegistry.sourceEncoding.effectsDigest descriptor) evidence)
        .book).logical).totalAsset asset =
      (CanonicalResourceKernel.logicalBook prepared.book.payload.logical).totalAsset asset := by
  rw [accepted_book_post prepared height tuple portals evidence]
  exact prepared.conserves asset

/-! ## Stable identity and one source-owned accounting vector -/

/-- Birth consumes the same domain/marker key as every other operation over
the canonical authority nullifier map. -/
def birthNullifier (domain : Digest) (identifier : Nat) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain identifier

theorem birthNullifier_eq_iff (domainLeft domainRight : Digest) (left right : Nat) :
    birthNullifier domainLeft left = birthNullifier domainRight right ↔
      domainLeft = domainRight ∧ left = right :=
  CredentialAuthorityReplay.nullifier_eq_iff domainLeft domainRight left right

variable [DecidableEq F]

private def guardOfPair (guard : Nat × Digest) : ReadGuard :=
  ⟨⟨guard.1⟩, guard.2⟩

def sourceReadGuards {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) : List ReadGuard :=
  accepted.sourceReadGuards.map guardOfPair

/-- The platform cell as a read dependency of every ordinary birth: the birth is priced from
the platform record of the image it commits against (`Pending.priced`), so an install landing in
between makes the birth's commit stale instead of letting it land at the old price. -/
def platformGuards (deployment : CanonicalCellRegistry.Deployment)
    (ground : Ground deployment) : List ReadGuard :=
  match PlatformCellDomain.load deployment ground.view with
  | none => []
  | some loaded => [loaded.readGuard]

theorem platformGuards_exact (deployment : CanonicalCellRegistry.Deployment)
    (ground : Ground deployment) (guard : ReadGuard)
    (member : guard ∈ platformGuards deployment ground) :
    guard.expectedRoot = ground.view.model.roots guard.cellId := by
  unfold platformGuards at member
  split at member
  · simp at member
  · rw [List.mem_singleton] at member
    subst member
    rfl

/-- Duplicate observations retain their exact source roots. If a dependency
is already a guarded write, it does not become a second read-only participant. -/
def readGuards {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) : List ReadGuard :=
  let written := accepted.prepared.writes.map DataWrite.cellId
  accepted.prepared.readGuards ++
    (sourceReadGuards accepted ++ platformGuards deployment ground).filter fun guard =>
      guard.cellId ∉ written

set_option backward.isDefEq.respectTransparency false in
private theorem branch_read_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height)
    (branch : Branch accepted.descriptor) :
    (accepted.branches branch).readGuard.2 =
      ground.view.model.roots ⟨(accepted.branches branch).readGuard.1⟩ := by
  rw [BranchAccepted.readGuard_eq_source]
  exact (accepted.branches branch).source.readGuard_exact.trans
    ((congrArg rootBytes (ground.bytes_exact _)).trans
      (ground.view.coherent _))

theorem sourceReadGuards_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height)
    (guard : ReadGuard) (member : guard ∈ sourceReadGuards accepted) :
    guard.expectedRoot = ground.view.model.roots guard.cellId := by
  change guard ∈
    (ResourceBirthPolicyController.Concrete.AcceptedBirth.sourceReadGuards accepted).map guardOfPair
    at member
  obtain ⟨pair, inPairs, rfl⟩ := List.mem_map.mp member
  unfold ResourceBirthPolicyController.Concrete.AcceptedBirth.sourceReadGuards at inPairs
  obtain ⟨branch, _, inBranch⟩ := List.mem_flatMap.mp inPairs
  exact (accepted.branches branch).lawGuardsBound pair inBranch

theorem readGuards_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.expectedRoot = ground.view.model.roots guard.cellId := by
  rcases List.mem_append.mp member with authority | source
  · exact accepted.prepared.readGuards_exact guard authority
  · rcases List.mem_append.mp (List.mem_filter.mp source).1 with fromSource | fromPlatform
    · exact sourceReadGuards_exact accepted guard fromSource
    · exact platformGuards_exact deployment ground guard fromPlatform

theorem readGuards_readonly {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height)
    (guard : ReadGuard) (member : guard ∈ readGuards accepted) :
    guard.cellId ∉ accepted.prepared.writes.map DataWrite.cellId := by
  rcases List.mem_append.mp member with authority | source
  · exact accepted.prepared.readGuards_readonly guard authority
  · simpa using (List.mem_filter.mp source).2

theorem source_reads_covered {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height)
    (guard : ReadGuard) (member : guard ∈ sourceReadGuards accepted) :
    guard.cellId ∈ accepted.prepared.writes.map DataWrite.cellId ∨ guard ∈ readGuards accepted := by
  by_cases written : guard.cellId ∈ accepted.prepared.writes.map DataWrite.cellId
  · exact Or.inl written
  · exact Or.inr (List.mem_append_right _ (List.mem_filter.mpr
      ⟨List.mem_append_left _ member, by simpa using written⟩))

/-- The directory slot at an identifier is the live cell the image holds there. -/
private theorem slot_of_live (ground : Ground deployment) (identifier : Nat)
    (packed : CellRegistry.PackedCell CanonicalCellRegistry.registry)
    (holds : ground.view.canonicalBytes ⟨identifier⟩ =
      LifecycleImage.bytes CanonicalCellRegistry.registry (.live packed)) :
    ground.directory.slots identifier = .present packed := by
  have decoded := congrArg (LifecycleImage.rawDecode CanonicalCellRegistry.registry)
    ((ground.bytes_exact identifier).trans holds)
  rw [LifecycleImage.rawDecode_bytes, LifecycleImage.rawDecode_bytes] at decoded
  rw [← LifecycleImage.view_slot CanonicalCellRegistry.registry ground.directory identifier]
  rw [Option.some.inj decoded]
  try rfl

omit [DecidableEq F] in
set_option backward.isDefEq.respectTransparency false in
/-- **No birth writes the platform cell.** Every write a birth commits is a fresh allocation
(its identifier unused in the loaded directory), the factory cell, the resource book or the
credential-authority cell; the platform cell is live in the same directory with kind
`.platform`, which none of them has. No identifier arithmetic or digest premise is used. -/
theorem platform_unwritten
    (prepared : ResourceBirthController.Concrete.PreparedBirth profile.compilerProfile deployment
      pins ground descriptor)
    (loaded : PlatformCellDomain.Loaded deployment ground.view) :
    PlatformCellDomain.cellIdOf deployment ∉ prepared.writes.map DataWrite.cellId := by
  have platform := slot_of_live ground (PlatformCellDomain.cellIdOf deployment).value
    (PlatformCellDomain.packedCell loaded.cell) loaded.observed
  intro written
  obtain ⟨write, member, same⟩ := List.mem_map.mp written
  have ids := congrArg (fun cell => cell.value) same
  simp only [ResourceBirthController.Concrete.PreparedBirth.writes,
    ResourceBirthController.Concrete.planWrites, ResourceBirthController.allocationWrites,
    List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with (born | factory | book) | authority
  · obtain ⟨request, inRequests, rfl⟩ := List.mem_map.mp born
    have fresh := allocate_success_fresh CanonicalCellRegistry.registry _ _ _
      prepared.allocated.accepted request inRequests
    change request.cellId = (PlatformCellDomain.cellIdOf deployment).value at ids
    rw [← ids] at platform
    exact fresh (ground.directory.present_used platform)
  · subst factory
    have present := prepared.factory.present
    change deployment.factoryId = (PlatformCellDomain.cellIdOf deployment).value at ids
    rw [← ids] at platform
    rw [platform] at present
    simp [PlatformCellDomain.packedCell] at present
  · subst book
    have present := prepared.book.present
    change deployment.resourceBookId = (PlatformCellDomain.cellIdOf deployment).value at ids
    rw [← ids] at platform
    rw [platform] at present
    simp [PlatformCellDomain.packedCell] at present
  · simp only [Minidregg.Compiler.ServedBasis.Ground.authorityWrites, List.mem_singleton] at authority
    subst authority
    have present := slot_of_live ground deployment.authorityCellId
      (CredentialAuthorityDomainReceiver.packedCell ground.authority.cell)
      ground.authorityObserved
    change deployment.authorityCellId = (PlatformCellDomain.cellIdOf deployment).value at ids
    rw [← ids] at platform
    rw [platform] at present
    simp [PlatformCellDomain.packedCell, CredentialAuthorityDomainReceiver.packedCell] at present

/-- **The platform cell guards every ordinary birth**: a birth committed against an image
holding the platform cell carries that cell's exact root as a read guard. No birth writes
the platform cell (`platform_unwritten`), so the guard is never filtered out. -/
theorem readGuards_platform {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height)
    (loaded : PlatformCellDomain.Loaded deployment ground.view)
    (found : PlatformCellDomain.load deployment ground.view = some loaded) :
    loaded.readGuard ∈ readGuards accepted := by
  have inPlatform : loaded.readGuard ∈ platformGuards deployment ground := by
    unfold platformGuards
    rw [found]
    exact List.mem_singleton_self _
  exact List.mem_append_right _ (List.mem_filter.mpr
    ⟨List.mem_append_right _ inPlatform, by
      simpa [PlatformCellDomain.Loaded.readGuard] using
        platform_unwritten accepted.prepared loaded⟩)

/-- The strict signed ingress contains the complete frame-two descriptor and
all exact native envelopes in source order. It is retained privately for replay,
not returned as a receipt. Historical equality needs no new authorization. -/
def event (domain : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 2
  domain := domain
  eventId := commitmentBytes
    ("DREGG.RESOURCE.BIRTH.EVENT/v3".toUTF8.toList ++
      digestStream.encode domain ++ ingress.bytes)
  canonicalBytes := ingress.bytes

theorem event_retains_descriptor (domain : Digest) (ingress : DecodedIngress) :
    (event domain ingress).canonicalBytes = ingress.bytes ∧
      ingress.ingress.descriptorBytes =
        CanonicalCellRegistry.sourceEncoding.codec.encode ingress.descriptor :=
  ⟨rfl, ingress.descriptorCanonical.symm⟩

/-- Source-defined admission units: verification work counts source-selected
policy checks, bytes count canonical committed inputs/posts, and the fee lane
is the actual Book transfer amount. This one vector is checked and debited by
the durable preflight; no caller supplies a competing charge projection. -/
def charge {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) : Charge
  | .incidences => 3 + accepted.descriptor.createRequests.length
  | .turnBytes => accepted.ingress.bytes.length
  | .memoryTouches => accepted.prepared.writes.length + (readGuards accepted).length
  | .witnessBytes => (credentialBundleStream.encode accepted.ingress.ingress.credentials).length +
      (match accepted.ingress.ownerConsentEnvelopes with
       | none => 0
       | some owners => ((StreamCodec.list bytesStream).encode owners).length)
  | .proofWork => 2 + accepted.descriptor.createRequests.length +
      accepted.descriptor.resourceBatch.operations.length +
      (match accepted.ingress.ownerConsentEnvelopes with | none => 0 | some owners => owners.length)
  | .storageBytes => DeployedCharge.storageCharge ground.view accepted.prepared.writes (event deployment.domain accepted.ingress)
  | .sideEffectCount => 1
  | .feeDebit => accepted.descriptor.fee.amount
  | .networkBytes | .leaseByteBlocks => 0

/-- `charge` over writes and read guards the caller has already computed: the
admitted constructor evaluates the birth's writes and guards once and every
lane reads them (`chargeWith_self`). It carries no premise that its arguments
ARE the birth's own writes and guards: its one caller, `materializedIntent`,
passes exactly `accepted.prepared.writes` and `readGuards accepted`, and any
other caller must prove the same (`chargeWith_self`) before its charge counts. -/
def chargeWith {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height)
    (writes : List DataWrite) (guards : List ReadGuard) : Charge
  | .incidences => 3 + accepted.descriptor.createRequests.length
  | .turnBytes => accepted.ingress.bytes.length
  | .memoryTouches => writes.length + guards.length
  | .witnessBytes => (credentialBundleStream.encode accepted.ingress.ingress.credentials).length +
      (match accepted.ingress.ownerConsentEnvelopes with
       | none => 0
       | some owners => ((StreamCodec.list bytesStream).encode owners).length)
  | .proofWork => 2 + accepted.descriptor.createRequests.length +
      accepted.descriptor.resourceBatch.operations.length +
      (match accepted.ingress.ownerConsentEnvelopes with | none => 0 | some owners => owners.length)
  | .storageBytes => DeployedCharge.storageCharge ground.view writes (event deployment.domain accepted.ingress)
  | .sideEffectCount => 1
  | .feeDebit => accepted.descriptor.fee.amount
  | .networkBytes | .leaseByteBlocks => 0

theorem chargeWith_self {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) :
    chargeWith accepted accepted.prepared.writes (readGuards accepted) = charge accepted := by
  funext lane
  cases lane <;> rfl

theorem charge_fee {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) :
    charge accepted .feeDebit = accepted.descriptor.fee.amount := rfl

/-- Only the concrete private native-admitted carrier reaches this emitter.
There is no decoded DataIntent, arbitrary portal or freely chosen write list. -/
def intent {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) : DataIntent rootBytes where
  transactionId := accepted.descriptor.transactionId
  writes := accepted.prepared.writes
  readGuards := readGuards accepted
  nullifiers := [birthNullifier deployment.domain accepted.descriptor.authorityNullifier]
  exactCharge := charge accepted
  event := event deployment.domain accepted.ingress
  subject := some accepted.descriptor.creator
  postRootsBound := accepted.prepared.write_roots_bound
  guardsReadOnly := readGuards_readonly accepted

/-- The admitted constructor with its finite charge evaluated once. No
receiver or encoder needs to retain and rerun charge-producing source work. -/
def materializedIntent {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) : DataIntent rootBytes :=
  let writes := accepted.prepared.writes
  let guards := readGuards accepted
  { transactionId := accepted.descriptor.transactionId
    writes := writes
    readGuards := guards
    nullifiers := [birthNullifier deployment.domain accepted.descriptor.authorityNullifier]
    exactCharge := (Charge.materialize (chargeWith accepted writes guards)).toCharge
    event := event deployment.domain accepted.ingress
    subject := some accepted.descriptor.creator
    postRootsBound := accepted.prepared.write_roots_bound
    guardsReadOnly := readGuards_readonly accepted }

/-- Exact complete intent equality, including all roots, guards and charges. -/
theorem materializedIntent_eq {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) :
    materializedIntent accepted = intent accepted := by
  simp only [materializedIntent, intent, Charge.materialize_eq, chargeWith_self]

/-- The actual receiving and semantic-replay constructor uses finite values;
the source definition remains the specification for all existing consumers. -/
@[csimp] theorem intent_eq_materializedIntent : @intent = @materializedIntent := by
  funext F instF profile deployment pins ground instEq height accepted
  exact (materializedIntent_eq accepted).symm

theorem materializedIntent_record_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) :
    DurableReceiver.IntentRecord.ofIntent (materializedIntent accepted) =
      DurableReceiver.IntentRecord.ofIntent (intent accepted) := by
  rw [materializedIntent_eq]

/-- The original canonical record codec emits exactly the same bytes. -/
theorem materializedIntent_record_bytes_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) :
    DurableReceiverCodec.intentStream.encode
        (DurableReceiver.IntentRecord.ofIntent (materializedIntent accepted)) =
      DurableReceiverCodec.intentStream.encode
        (DurableReceiver.IntentRecord.ofIntent (intent accepted)) := by
  rw [materializedIntent_record_exact]

/-- info: 'Minidregg.Kernel.ResourceBirthReceiver.intent_eq_materializedIntent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intent_eq_materializedIntent

/-- info: 'Minidregg.Kernel.ResourceBirthReceiver.materializedIntent_record_bytes_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms materializedIntent_record_bytes_exact

theorem intent_exact_source {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) :
    (intent accepted).writes = accepted.prepared.writes ∧
      (intent accepted).exactCharge = charge accepted ∧
      (intent accepted).event.canonicalBytes = accepted.ingress.bytes ∧
      (intent accepted).transactionId = accepted.descriptor.transactionId :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The committed births are the named ones.**  Every write of the durable
intent that creates its cell is named by the step the factory law admitted
(`AcceptedBirth.births_named`): the intent commits exactly the writes the
naming check ran over, so no birth reaches the journal unjudged. -/
theorem intent_births_named {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) :
    ∀ write ∈ (intent accepted).writes, ResourceBirthController.Concrete.bornIn write = true →
      ReceivingLaw.namesBirth accepted.factoryStep write = true :=
  accepted.births_named.1

#assert_axioms intent_births_named

/-- Both global durable coordinates come from the receiving source's same
creator-scoped birth identity; neither can be chosen independently by ingress. -/
theorem intent_derived_identity {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) :
    (intent accepted).transactionId = ResourceBirthController.Concrete.sourceIdentity
        profile.compilerProfile deployment accepted.descriptor.creator accepted.descriptor.nonce ∧
      (intent accepted).nullifiers =
        [birthNullifier deployment.domain
          (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile deployment
            accepted.descriptor.creator accepted.descriptor.nonce).value] := by
  constructor
  · exact accepted.prepared.transaction_identity
  · change [birthNullifier deployment.domain accepted.ingress.descriptor.authorityNullifier] = _
    rw [accepted.prepared.authority_marker_identity]
    rfl

/-- Every exact planned post is installed by the existing data installer.
Uniqueness comes from actual receiving preparation, not a pick-last rule. -/
theorem installed_write_bytes {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height)
    (write : DataWrite) (member : write ∈ accepted.prepared.writes) :
    (DataSnapshot.install ground.view (intent accepted)).canonicalBytes write.cellId =
      write.canonicalPostBytes :=
  DataSnapshot.install_canonicalBytes_of_member ground.view (intent accepted)
    accepted.prepared.writesUnique write member

/-- Initial source bytes are in the same atomic installed image as their new
heads and owner grants. There is no external source-staging success premise. -/
theorem installed_policy_source_bytes {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height)
    (record : PolicyRecord)
    (member : record ∈ accepted.prepared.grants.initialSources.records) :
    (DataSnapshot.install ground.view (intent accepted)).canonicalBytes
        ⟨(CanonicalCellRegistry.policySourceCreate deployment.domain record).cellId⟩ =
      LifecycleImage.bytes CanonicalCellRegistry.registry
        (.live (CanonicalCellRegistry.policySourceCell record)) :=
  installed_write_bytes accepted
    (ResourceBirthController.birthWrite (CanonicalCellRegistry.policySourceCreate deployment.domain record))
    (accepted.prepared.initial_source_write record member)

theorem installed_initial_policy_source {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height)
    (initial : InitialPolicy) (member : initial ∈ accepted.descriptor.initialPolicies) :
    ∃ record,
      PolicyRecordCodec.decode initial.canonicalBytes = some record ∧
      PolicySourceCell.InitialFacts deployment.domain profile.compilerProfile initial record ∧
      (DataSnapshot.install ground.view (intent accepted)).canonicalBytes
          ⟨PolicySourceCell.physicalId deployment.domain initial.address⟩ =
        LifecycleImage.bytes CanonicalCellRegistry.registry
          (.live (CanonicalCellRegistry.policySourceCell record)) := by
  obtain ⟨record, inRecords, decoded, facts⟩ :=
    accepted.prepared.grants.initialSources.record_of_member initial member
  have installed := installed_policy_source_bytes accepted record inRecords
  change (DataSnapshot.install ground.view (intent accepted)).canonicalBytes
      ⟨PolicySourceCell.physicalId deployment.domain (PolicyRecordCodec.digest record)⟩ = _ at installed
  rw [facts.2.2.1] at installed
  exact ⟨record, decoded, facts, installed⟩

/-! ## The authority cell in the installed image -/

/-- The installed image holds exactly the grant batch's post authority cell at
the pinned identifier. There is one authority write; no page, shard or catalogue
correspondence remains to be established. -/
theorem installed_authority_cell {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) :
    (DataSnapshot.install ground.view (intent accepted)).canonicalBytes
        (CredentialAuthorityDomainReceiver.cellIdOf deployment) =
      CredentialAuthorityDomainReceiver.cellBytes accepted.prepared.grants.post :=
  installed_write_bytes accepted _ accepted.prepared.authority_write_member

theorem refusal_no_mutation {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height)
    (reason : DurableDataIntent.RejectReason)
    (refused : DurableDataIntent.execute .complete ground.view (intent accepted) =
      .rejected reason) :
    (DurableDataIntent.execute .complete ground.view (intent accepted)).storeAfter ground.view =
      ground.view := by rw [refused]; rfl

theorem no_partial_commit {height : Height}
    (accepted : AcceptedBirth profile deployment pins ground height) (schedule : Schedule) :
    (DurableDataIntent.execute schedule ground.view (intent accepted)).storeAfter ground.view =
        ground.view ∨
      (DurableDataIntent.execute schedule ground.view (intent accepted)).storeAfter ground.view =
        DataSnapshot.install ground.view (intent accepted) :=
  execute_no_partial_data_commit schedule ground.view (intent accepted)

/-! ## Replay before fresh admission, with sealed receipts -/

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

inductive Reject where
  | malformedIngress
  | transactionConflict
  | admission (reason : ResourceBirthPolicyController.Reject)
  | durable (reason : DurableDataIntent.RejectReason)
  /-- The ground does not answer the birth's transaction id (a light basis that
  did not declare it): refused by name, never read as "not recorded". -/
  | undeclaredTransaction

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receipt (domain : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨ingress.descriptor.transactionId, (event domain ingress).eventId⟩

/-- The keys a birth consults beyond the state: its transaction id (replay
detection, `replay`) and its replay marker's nullifier (`BatchReady` reads its
spent bit, `ResourceBirthController.Concrete.MarkerDeclared`). A light basis for a
birth declares at least these. -/
def birthKeys (domain : Digest) (ingress : DecodedIngress) : DurableView.Keys :=
  ⟨[ingress.descriptor.transactionId],
    [birthNullifier domain ingress.descriptor.authorityNullifier]⟩

/-- A recorded intent is this ingress's own: the same transaction id, the exact
original canonical signed ingress as its event, and the same semantic marker. -/
def recordedExact (domain : Digest) (ingress : DecodedIngress)
    (recorded : DurableCommitProtocol.Intent TransactionId DurableDataIntent.CellId StableNullifier
      ReplayEnvelope) : Bool :=
  decide (recorded.transactionId = ingress.descriptor.transactionId ∧
    recorded.event.event = event domain ingress ∧
    recorded.nullifiers = [birthNullifier domain ingress.descriptor.authorityNullifier])

/-- Return a historical receipt only for the exact original canonical signed
ingress and the same semantic marker. Roots, nullifier freshness, policy epoch
and time are deliberately not re-admitted after this historical match. The one
journal read goes through `Ground.replayOf`: a ground that does not answer the
transaction id (a light basis that did not declare it) gives `undeclared`, never
`fresh`. -/
def replay (domain : Digest) (ground : Ground deployment) (ingress : DecodedIngress) :
    Minidregg.Compiler.ServedBasis.Ground.Replay Receipt :=
  ground.replayOf ingress.descriptor.transactionId (recordedExact domain ingress) (receipt domain ingress)

/-- Historical success retains the original canonical signed ingress and
the exact shared authority marker. An occupied transaction identifier alone
cannot authorize a replay or substitute a different event. -/
theorem replay_only_exact (domain : Digest)
    (ground : Ground deployment) (ingress : DecodedIngress)
    (result : Receipt) (accepted : replay domain ground ingress = .original result) :
    result = receipt domain ingress ∧
      ∃ recorded,
        Snapshot.lookupRecorded ingress.descriptor.transactionId ground.view.model.journal =
            some recorded ∧
        recorded.transactionId = ingress.descriptor.transactionId ∧
        recorded.event.event = event domain ingress ∧
        recorded.nullifiers = [birthNullifier domain ingress.descriptor.authorityNullifier] := by
  obtain ⟨same, recorded, found, isExact⟩ :=
    Minidregg.Compiler.ServedBasis.Ground.replayOf_original ground _ _ _ _ accepted
  exact ⟨same, recorded, found, of_decide_eq_true isExact⟩

/-- A recorded transaction with a different source event refuses without
running any new authority or state transition (on any ground that answers the
transaction id; the full shape answers every one). -/
theorem replay_wrong_event_refused (domain : Digest)
    (ground : Ground deployment) (ingress : DecodedIngress)
    (recorded : DurableCommitProtocol.Intent TransactionId
      DurableDataIntent.CellId StableNullifier ReplayEnvelope)
    (declared : ground.declaresTransaction ingress.descriptor.transactionId = true)
    (found : Snapshot.lookupRecorded ingress.descriptor.transactionId
      ground.view.model.journal = some recorded)
    (different : recorded.event.event ≠ event domain ingress) :
    replay domain ground ingress = .conflict := by
  apply Minidregg.Compiler.ServedBasis.Ground.replayOf_conflict (recorded := recorded)
  · simp [Minidregg.Compiler.ServedBasis.Ground.recorded, declared, found]
  · simp [recordedExact, different]

/-- **An undeclared transaction id is refused by name**: on a light basis that did
not declare the birth's transaction id, the verdict is `undeclared`, never `fresh`. -/
theorem replay_undeclared (domain : Digest) {store : Minidregg.Compiler.DurableHistory.StoreIdentity}
    (basis : Minidregg.Compiler.ServedBasis.Basis deployment store) (ingress : DecodedIngress)
    (undeclared : ingress.descriptor.transactionId ∉ basis.keys.transactions) :
    replay domain (Ground.ofBasis basis) ingress = .undeclared :=
  Minidregg.Compiler.ServedBasis.Ground.replayOf_undeclared basis _ _ _ undeclared

#assert_axioms replay_only_exact replay_wrong_event_refused replay_undeclared

#assert_axioms platformGuards_exact platform_unwritten readGuards_platform

/-! ## Births read the current platform record (deployed keystone)

Scope: births admitted by this receiver (ordinary, reserve and lifetime-grant methods). The
share issue, lifetime-grant source, grain births, provisioning, PayEnrolV2 and the completion
keys are owed families (`scripts/platform-field-readers.json`). -/

/-- **Births through the resource-birth receiver read the current platform record**: every
admitted birth is priced from the record of the image it commits against (the factory pins
carry its creation tariff and the fee is bounded by it), is bound by that record's owner
budget and lifetime (`templateAt`, enforced through `RootGrantShape`/`BirthWindow`), and
read-guards the platform cell at that image's exact root. -/
def ReceiverReadsCurrent (profile : CanonicalRuntimeProfile.Profile F)
    (deployment : CanonicalCellRegistry.Deployment) : Prop :=
  ∀ (pins : FactoryPins) (ground : Ground deployment) (height : Height)
    (accepted : AcceptedBirth profile deployment pins ground height),
    ∃ record, platformRecordAt deployment ground.view = some record ∧
      pins.tariff = record.creation ∧
      accepted.descriptor.FeeBound record.creation ∧
      accepted.pending.template = templateAt profile.template record ∧
      ({ cellId := PlatformCellDomain.cellIdOf deployment
         expectedRoot := ground.view.model.roots (PlatformCellDomain.cellIdOf deployment) } :
          ReadGuard) ∈ (intent accepted).readGuards

theorem receiverReadsCurrent : ReceiverReadsCurrent profile deployment := by
  intro pins ground height accepted
  cases found : PlatformCellDomain.load deployment ground.view with
  | none =>
      have recorded := accepted.pending.recordExact
      simp [platformRecordAt, PlatformCellDomain.recordOn_load, found] at recorded
  | some loaded =>
      refine ⟨accepted.pending.record, accepted.pending.recordExact, accepted.pending.priced,
        ?_, rfl, readGuards_platform accepted loaded found⟩
      rw [← accepted.pending.priced]
      exact accepted.pending.checked.feeBound

/-- No record, no birth: an image whose platform cell or record is missing admits none. -/
theorem unpriced_empty {height : Height}
    (missing : platformRecordAt deployment ground.view = none) :
    IsEmpty (AcceptedBirth profile deployment pins ground height) :=
  ⟨fun accepted => by
    have recorded := accepted.pending.recordExact
    rw [missing] at recorded
    cases recorded⟩

/-- Teeth: pins carrying any tariff other than the record's admit no birth. In particular,
pins built from the genesis `config.tariff` admit nothing once an install changed the
creation tariff. -/
theorem stale_unadmitted {height : Height} (record : PlatformCellLayout.Platform)
    (recorded : platformRecordAt deployment ground.view = some record)
    (stale : pins.tariff ≠ record.creation) :
    IsEmpty (AcceptedBirth profile deployment pins ground height) :=
  ⟨fun accepted => (pending_stale_empty accepted.prepared height record recorded stale).false
    accepted.pending⟩

#assert_axioms receiverReadsCurrent unpriced_empty stale_unadmitted

/-- Admit against the exact full snapshot already validated by the host (the
ratchet-listed full-shape callers). The native receiver performs one
compare-and-swap against this image and returns contention if it changed; it
never silently rebases an accepted birth onto a later image. -/
def receiveLoaded
    (profile : CanonicalRuntimeProfile.Profile F)
    (deployment : CanonicalCellRegistry.Deployment) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (durable : ResourceBirthController.Concrete.Durable)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable)
    (authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot)
    (height : Height) (bytes : List UInt8) : IO Result := do
  let ground : Ground deployment := .ofLoaded durable directory authority
  match decodeIngress bytes with
  | none => return .rejected .malformedIngress
  | some ingress =>
      match replay deployment.domain ground ingress with
      | .original recorded => return .confirmed .replayed recorded
      | .conflict => return .rejected .transactionConflict
      | .undeclared => return .rejected .undeclaredTransaction
      | .fresh =>
          match ← admitDecodedNative profile deployment pins native ground height ingress with
          | .error reason => return .rejected (.admission reason)
          | .ok accepted =>
              match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
              | .confirmed kind _ => return .confirmed kind (receipt deployment.domain ingress)
              | .rejected reason => return .rejected (.durable reason)
              | .contention => return .contention
              | .unavailable detail => return .unavailable detail
              | .uncertain detail => return .uncertain detail

/-- **The light birth receive.** The birth's keys (`birthKeys`: its transaction id
and its replay marker's nullifier) are read from the authenticated history into a
basis (`basisOf`, the light opening's `Light.basisVia`); the replay check, the
preparation and the admission run on `Ground.ofBasis`; the commit is
`DurableServed.receiveServed` on the light opening. Nothing opens the full
materialization. The admission height is `genesisHeight + basis.height`. -/
def receiveServed
    (profile : CanonicalRuntimeProfile.Profile F)
    (deployment : CanonicalCellRegistry.Deployment) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (genesisHeight : Nat) (opening : DurableServed.Opening rootBytes)
    (basisOf : DurableView.Keys →
      IO (Except String (Minidregg.Compiler.ServedBasis.Basis deployment opening.store)))
    (bytes : List UInt8) : IO Result := do
  match decodeIngress bytes with
  | none => return .rejected .malformedIngress
  | some ingress =>
      match ← basisOf (birthKeys deployment.domain ingress) with
      | .error detail => return .unavailable detail
      | .ok basis =>
          let ground : Ground deployment := .ofBasis basis
          match replay deployment.domain ground ingress with
          | .original recorded => return .confirmed .replayed recorded
          | .conflict => return .rejected .transactionConflict
          | .undeclared => return .rejected .undeclaredTransaction
          | .fresh =>
              match ← admitDecodedNative profile deployment pins native ground
                  (genesisHeight + basis.height) ingress with
              | .error reason => return .rejected (.admission reason)
              | .ok accepted =>
                  let issued := receipt deployment.domain ingress
                  match ← DurableServed.receiveServed transport rootBytes opening (intent accepted) with
                  | .appended kind .. => return .confirmed kind issued
                  | .replayed _ => return .confirmed .replayed issued
                  | .rejected reason => return .rejected (.durable reason)
                  | .contention => return .contention
                  | .unavailable detail => return .unavailable detail
                  | .uncertain detail => return .uncertain detail

/-- This is the concrete external input boundary on the full shape. It accepts
only strict signed ingress, never an intent or an authority verdict. Storage
readback is the existing native receiver's success criterion; only receipt IDs
escape. The image's directory and authority are loaded once here; an image
without them refuses `directory` / `authorityDomain` (the preparation's own names). -/
def receive
    (profile : CanonicalRuntimeProfile.Profile F)
    (deployment : CanonicalCellRegistry.Deployment) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (height : Height) (bytes : List UInt8) (attempts : Nat := 4) : IO Result := do
  let _ := attempts
  match decodeIngress bytes with
  | none => return .rejected .malformedIngress
  | some _ =>
      match ← DurableReceiverIO.load transport rootBytes with
      | .error detail => return .unavailable detail
      | .ok durable =>
          match CredentialAuthorityDomainReceiver.loadDirectory durable with
          | none => return .rejected (.admission (.preparation .directory))
          | some directory =>
              match CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot with
              | none => return .rejected (.admission (.preparation .authorityDomain))
              | some authority =>
                  receiveLoaded profile deployment pins native transport durable directory authority
                    height bytes

end Minidregg.Kernel.ResourceBirthReceiver
