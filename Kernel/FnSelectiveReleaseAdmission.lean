/-
Capability evidence for the special selective-release ingress. The current
recipient authority and committed Pred still perform ordinary typed capability
lineage, revocation and policy checks; invocation authentication is the private
native-checked owner packet, not a forged DRC signed envelope or an fn claim.
This module does not install a durable effect until the accepted multi-cell
transition and physical receiver are connected.
-/
import Kernel.FnSelectiveReleaseIngress
import Compiler.CredentialAuthorityPolicyRegistry

namespace Minidregg.Kernel.FnSelectiveReleaseAdmission

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Compiler
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Kernel.FnSelectiveReleaseSignature
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Theory.ResourceCost

set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local irreducible] NativeHost.Config.profile CanonicalRuntimeProfile.Profile.compilerProfile

/-- Fresh preparation is performed against exactly the durable image that
was replay-verified into `opened`. Both authority views are loads of the one
pinned cell from that image, so they are the same snapshot
(`Loaded.snapshot_unique`); no runtime comparison is needed. -/
structure Prepared (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : FnSelectiveReleaseIngress.Ingress) where
  operation : DeclaredResourceController.PreparedInvocation config.deployment
    config.profile ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩
    opened.durable (FnSelectiveReleaseIngress.command ingress)

inductive PrepareReject where
  | ordinary (reason : DeclaredResourceController.Reject)

def prepare (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : FnSelectiveReleaseIngress.Ingress) :
    Except PrepareReject (Prepared config opened ingress) := do
  let operation ← (DeclaredResourceController.prepare config.deployment config.profile
      ⟨config.federation, NativeHost.logicalHeight config opened.durable⟩ opened.durable
      (FnSelectiveReleaseIngress.command ingress)).mapError .ordinary
  .ok ⟨operation⟩

theorem Prepared.snapshotExact (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (ingress : FnSelectiveReleaseIngress.Ingress)
    (prepared : Prepared config opened ingress) :
    prepared.operation.authority.snapshot = opened.authority.snapshot :=
  CredentialAuthorityDomainReceiver.Loaded.snapshot_unique _ _

theorem Prepared.logicalExact (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (ingress : FnSelectiveReleaseIngress.Ingress)
    (prepared : Prepared config opened ingress) :
    prepared.operation.authority.snapshot.logical =
      opened.authority.snapshot.logical := by
  rw [prepared.snapshotExact]

/-- The expected request must be the actual source-derived incidence request
of the owner packet's content command. The outer capability/root selectors
may choose a current witness, but cannot change this packet or the request.
The source portal retains the complete authority's capability membership,
issuer lineage and every revocation channel check. -/
def ownerPortal (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (packet : Packet) (marker : Nat) (expected : SomeRequest) : Portal :=
  { sourcePortal opened.authority.snapshot marker with
    SignatureWitness := PEmpty
    verifySignature := fun _ witness => nomatch witness
    CapabilityUseWitness := Checked config opened
    verifyCapabilityUse := fun request capability commitment checked =>
      capabilityCheck opened.authority.snapshot capability commitment &&
      match capability.holder with
      | .bearer => false
      | .subject holder =>
          decide (holder = request.subject ∧
            request.subject = ⟨checked.packet.release.owner.subject⟩ ∧
            request.subjectKeyEpoch =
              opened.authority.snapshot.authState.subjectKeyEpoch request.subject ∧
            CredentialSignatureAdmission.requestBytes ⟨_, request⟩ =
              CredentialSignatureAdmission.requestBytes expected ∧
            checked.packet = packet) }

/-- A successful capability-use projection cannot be made from a different
portable packet or from a different typed request. The signature was checked
over the exact release preimage by the private constructor. -/
theorem ownerPortal_use_exact (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (packet : Packet) (marker : Nat) (expected : SomeRequest)
    {kind : ResourceKind} (request : Request kind) (capability : Capability kind)
    (commitment : Digest) (checked : Checked config opened)
    (accepted : (ownerPortal config opened packet marker expected).verifyCapabilityUse
      request capability commitment checked = true) :
    checked.packet = packet ∧
      CredentialSignatureAdmission.requestBytes ⟨kind, request⟩ =
        CredentialSignatureAdmission.requestBytes expected := by
  unfold ownerPortal at accepted
  simp only [Bool.and_eq_true] at accepted
  obtain ⟨_, use⟩ := accepted
  cases holder : capability.holder with
  | bearer => simp [holder] at use
  | subject subject =>
      simp only [holder] at use
      have all := of_decide_eq_true use
      exact ⟨all.2.2.2.2, all.2.2.2.1⟩

/-- Construct the existing typed capability evidence from the complete
recipient authority. `capabilityEvidence` checks the stored parent, full
lineage, current epochs, every revocation channel and the exact request.
Only the signature-use witness differs from ordinary DRC admission. -/
def capabilityAt (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : FnSelectiveReleaseIngress.Ingress)
    (prepared : Prepared config opened ingress)
    (tuple : PreparedTuple (DeclaredResourceController.plan prepared.operation))
    (incidence : DeclaredResourceController.Incidence
      (FnSelectiveReleaseIngress.command ingress))
    (checked : Checked config opened) :=
  let request := tuple.request incidence
  let marker := DeclaredResourceController.operationMarker
    config.deployment.domain config.profile.semantics
    (FnSelectiveReleaseIngress.command ingress)
  CredentialAuthorityPolicyRegistry.capabilityEvidence
    config.profile.compilerProfile opened.authority.snapshot
    (DeclaredResourceController.sourceStore config.deployment.domain
      opened.directory.directory)
    (ownerPortal config opened ingress.packet marker request)
    (DeclaredResourceController.step prepared.operation tuple incidence)
    request.2
    (DeclaredResourceController.incidenceTarget
      (FnSelectiveReleaseIngress.command ingress) incidence).capability
    () checked () (fun _ => ())

/-- The same canonical policy compiler used by DRC admits each special
incidence. This is intentionally an `Option` of the *typed* authorized result,
not a Boolean assertion supplied by the relay. -/
def authorizeAt (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : FnSelectiveReleaseIngress.Ingress)
    (prepared : Prepared config opened ingress)
    (tuple : PreparedTuple (DeclaredResourceController.plan prepared.operation))
    (incidence : DeclaredResourceController.Incidence
      (FnSelectiveReleaseIngress.command ingress))
    (checked : Checked config opened) :=
  let request := (tuple.request incidence).2
  let context := DeclaredResourceController.step prepared.operation tuple incidence
  let policyConfig := CredentialAuthorityPolicyRegistry.config
    config.profile.compilerProfile opened.authority.snapshot
    (DeclaredResourceController.sourceStore config.deployment.domain
      opened.directory.directory)
    (ownerPortal config opened ingress.packet
      (DeclaredResourceController.operationMarker config.deployment.domain
        config.profile.semantics (FnSelectiveReleaseIngress.command ingress))
      (tuple.request incidence))
    context
  (capabilityAt config opened ingress prepared tuple incidence checked).bind fun evidence =>
    (policyConfig.registry.resolve request.policyId request.policyRevision).bind fun committed =>
      let witness := CanonicalPolicyAdmission.canonicalWitness
        config.profile.compilerProfile.compiler committed
        context.oldState context.newState
      if inputsInRange config.profile.compilerProfile.compiler
          committed.record.predicate witness.oldState witness.newState then
        if decide (castInjOn NativeHostProfile.Field
            (intsOf committed.record.predicate witness.oldState witness.newState)) then
          if epoch : request.policyEpoch =
              opened.authority.snapshot.authState.policyEpoch request.policyId then
            if revision : request.policyRevision =
                opened.authority.snapshot.authState.policyRevision request.policyId then
              CanonicalPolicyAdmission.admit policyConfig
                opened.authority.snapshot.authState request evidence witness
                (.policy request.policyId request.policyRevision) epoch revision
            else none
          else none
        else none
      else none

def targetIndex (ingress : FnSelectiveReleaseIngress.Ingress) :
    DeclaredResourceController.TargetIndex (FnSelectiveReleaseIngress.command ingress) :=
  ⟨0, by simp [FnSelectiveReleaseIngress.command]⟩

attribute [local irreducible] authorizeAt capabilityAt ownerPortal

/-- Only an actual pair of canonical typed policy/capability authorizations
can make this check true. It is computed here from the exact prepared tuple. -/
def bothAuthorized (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : FnSelectiveReleaseIngress.Ingress)
    (prepared : Prepared config opened ingress)
    (tuple : PreparedTuple (DeclaredResourceController.plan prepared.operation))
    (checked : Checked config opened) : Bool :=
  (authorizeAt config opened ingress prepared tuple
    (some (targetIndex ingress)) checked).isSome &&
  (authorizeAt config opened ingress prepared tuple none checked).isSome

theorem bothAuthorized_sound (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (ingress : FnSelectiveReleaseIngress.Ingress)
    (prepared : Prepared config opened ingress)
    (tuple : PreparedTuple (DeclaredResourceController.plan prepared.operation))
    (checked : Checked config opened)
    (accepted : bothAuthorized config opened ingress prepared tuple checked = true) :
    (authorizeAt config opened ingress prepared tuple
      (some (targetIndex ingress)) checked).isSome = true ∧
    (authorizeAt config opened ingress prepared tuple none checked).isSome = true := by
  simpa only [bothAuthorized, Bool.and_eq_true] using accepted

attribute [local irreducible] bothAuthorized

def Validated (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : FnSelectiveReleaseIngress.Ingress)
    (checked : Checked config opened) (prepared : Prepared config opened ingress) : Prop :=
  ∃ _shape : DeclaredResourceController.PhysicalShape prepared.operation,
    ∃ tuple : PreparedTuple (DeclaredResourceController.plan prepared.operation),
      bothAuthorized config opened ingress prepared tuple checked = true

attribute [local irreducible] Validated

/-- A native checked owner packet plus BOTH current typed incidence decisions
for the very same source-derived prepared command. No generic DRC signed
envelope can construct this value. -/
structure Accepted (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : FnSelectiveReleaseIngress.Ingress) where
  private mk ::
  checked : Checked config opened
  prepared : Prepared config opened ingress
  validated : Validated config opened ingress checked prepared

inductive Reject where
  | signature (reason : FnSelectiveReleaseSignature.Reject)
  | preparation (reason : PrepareReject)
  | collision
  | invalidPhysicalShape
  | targetAuthority

def admit (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : FnSelectiveReleaseIngress.Ingress) :
    IO (Except Reject (Accepted config opened ingress)) := do
  match ← FnSelectiveReleaseSignature.verifyNative config opened ingress.packet with
  | .error reason => return .error (.signature reason)
  | .ok checked =>
      match prepare config opened ingress with
      | .error reason => return .error (.preparation reason)
      | .ok prepared =>
          if shape : DeclaredResourceController.PhysicalShape prepared.operation then
            match DeclaredResourceController.prepareTuple prepared.operation with
            | none => return .error .collision
            | some tuple =>
                if authorized : bothAuthorized config opened ingress prepared tuple checked = true then
                  let validated : Validated config opened ingress checked prepared := by
                    unfold Validated
                    exact ⟨shape, tuple, authorized⟩
                  return .ok ⟨checked, prepared, validated⟩
                else return .error .targetAuthority
          else return .error .invalidPhysicalShape

/-- A special event and a second, release-key-specific nullifier are settled
with the exact content and authority writes in the same durable CAS. The
ordinary marker remains the prepared authority edit; the second marker is
durable-journal state, not an invented authority-page post. -/
def charge (ingress : FnSelectiveReleaseIngress.Ingress)
    (writes : List DataWrite) (guards : List ReadGuard) : Charge
  | .incidences => 2
  | .turnBytes => (FnSelectiveReleaseIngress.ingressCodec.encode ingress).length
  | .memoryTouches => writes.length + guards.length
  | .storageBytes =>
      (writes.map fun write => write.canonicalPostBytes.length).sum +
        (FnSelectiveReleaseIngress.ingressCodec.encode ingress).length
  | .witnessBytes => (FnSelectiveReleaseIngress.ingressCodec.encode ingress).length
  | .proofWork => 2
  | .sideEffectCount => 1
  | .feeDebit | .networkBytes | .leaseByteBlocks => 0

def Accepted.intent (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : FnSelectiveReleaseIngress.Ingress)
    (accepted : Accepted config opened ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  let operation := accepted.prepared.operation
  let shape : DeclaredResourceController.PhysicalShape operation := by
    have valid := accepted.validated
    unfold Validated at valid
    obtain ⟨shape, _, _⟩ := valid
    exact shape
  let writes := DeclaredResourceController.writes operation
  let guards := DeclaredResourceController.readGuards operation
  { transactionId := FnSelectiveReleaseIngress.transactionId ingress
    writes := writes
    readGuards := guards
    nullifiers :=
      [CredentialAuthorityReplay.nullifier config.deployment.domain
          (DeclaredResourceController.operationMarker config.deployment.domain
            config.profile.semantics (FnSelectiveReleaseIngress.command ingress)),
        FnSelectiveReleaseIngress.releaseNullifier ingress.packet.release]
    exactCharge := charge ingress writes guards
    event := FnSelectiveReleaseIngress.event ingress
    postRootsBound := DeclaredResourceController.writes_roots_bound operation
    guardsReadOnly := DeclaredResourceController.readGuards_readonly operation shape }

theorem Accepted.intent_special_event (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (ingress : FnSelectiveReleaseIngress.Ingress)
    (accepted : Accepted config opened ingress) :
    (accepted.intent config opened ingress).event = FnSelectiveReleaseIngress.event ingress := rfl

theorem Accepted.intent_release_nullifier (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (ingress : FnSelectiveReleaseIngress.Ingress)
    (accepted : Accepted config opened ingress) :
    FnSelectiveReleaseIngress.releaseNullifier ingress.packet.release ∈
      (accepted.intent config opened ingress).nullifiers := by simp [Accepted.intent]

end Minidregg.Kernel.FnSelectiveReleaseAdmission
