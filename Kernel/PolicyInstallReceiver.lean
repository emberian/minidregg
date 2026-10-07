/-
# Kernel.PolicyInstallReceiver -- one durable, capability-authorized policy installation

The existing installer determines and admits the semantic authority transition.
This receiver refines that same declaration into immutable source allocation and
the one write of the authority cell. The only internal create is the installed
source's cell; no caller supplies auxiliary payloads, an alternate policy store,
or a raw durable intent.

The original canonical signed ingress is retained for receipt-only replay before
fresh-state admission. A replay never resigns an old request or derives a new
marker from the current height or authority state.

Source replacement advances the selected revision while preserving the grant
generation. Every later use checks the newly selected source. The current source
still governs its own replacement, so a deliberately restrictive new law may
refuse future installations even though the control grant remains current.
-/
import Compiler.NativeProtocolFrames
import Kernel.ObjectAudienceInstall
import Kernel.PolicyInstallController
import Kernel.ResourceBirthController
import Compiler.DurableReceiverIO
import Compiler.CredentialAuthorityReplay
import Compiler.WorldKindLawDependencies

namespace Minidregg.Kernel.PolicyInstallReceiver

open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableCommitProtocol

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Ground := ServedBasis.Ground

attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

/-! ## Strict original command and signature bytes -/

structure Ingress where
  subject : SubjectId
  controlCapability : CapabilityId
  declarationBytes : List UInt8
  envelopeBytes : List UInt8
  rosterBytes : Option (List UInt8) := none
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
        (StreamCodec.product bytesStream (StreamCodec.product bytesStream (StreamCodec.option bytesStream)))))
    (fun ingress => (ingress.subject, ingress.controlCapability,
      ingress.declarationBytes, ingress.envelopeBytes, ingress.rosterBytes))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2.1, tuple.2.2.2.2⟩)
    (by intro ingress; cases ingress; rfl)

def ingressRawCodec : LawfulCodec Ingress where
  encode ingress := ingressFrame ++ ingressStream.encode ingress
  decode bytes := if bytes.take ingressFrame.length = ingressFrame then
    ingressStream.toLawful.decode (bytes.drop ingressFrame.length) else none
  decode_encode := by
    intro ingress
    have decoded := ingressStream.toLawful.decode_encode ingress
    change ingressStream.toLawful.decode (ingressStream.encode ingress) = some ingress at decoded
    simp [decoded]

def ingressCodec : LawfulCodec Ingress := strictCodec ingressRawCodec

def retiredIngressFrame : List UInt8 := "DREGG/POLICY/INSTALL/SIGNED-INGRESS".toUTF8.toList ++ [1]

theorem retired_ingress_refused (payload : List UInt8) :
    ingressCodec.decode (retiredIngressFrame ++ payload) = none := by
  have lengthExact : ingressFrame.length = retiredIngressFrame.length := by decide +kernel
  have different : retiredIngressFrame ≠ ingressFrame := by decide +kernel
  simp [ingressCodec, strictCodec, ingressRawCodec, lengthExact, different]

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  declaration : PolicyInstallController.Declaration
  declarationExact : PolicyInstallController.decodeDeclaration ingress.declarationBytes = some declaration
  envelope : CredentialSignedEnvelopeController.SignedEnvelope
  envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode
    ingress.envelopeBytes = some envelope

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match declarationExact : PolicyInstallController.decodeDeclaration ingress.declarationBytes with
  | none => none
  | some declaration =>
      match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode
          ingress.envelopeBytes with
      | none => none
      | some envelope => some ⟨ingress, declaration, declarationExact, envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def DecodedIngress.marker (ingress : DecodedIngress) : Nat := ingress.envelope.header.nullifier

theorem decodeIngress_canonical {bytes : List UInt8} {ingress : DecodedIngress}
    (decoded : decodeIngress bytes = some ingress) : ingress.bytes = bytes := by
  unfold decodeIngress at decoded
  cases parsed : ingressCodec.decode bytes with
  | none => simp [parsed] at decoded
  | some raw =>
      simp only [parsed, bind, Option.bind] at decoded
      split at decoded
      · contradiction
      · split at decoded
        · contradiction
        · cases Option.some.inj decoded
          exact strictCodec_canonical ingressRawCodec parsed

/-- Subject, target and nonce scope transaction identity. Changing a payload,
root, control-capability choice or signature at the same identity conflicts
with a recorded original ingress; it cannot become a second execution. -/
def transactionId (domain : Digest) (ingress : DecodedIngress) : Digest :=
  (Sp800185Cshake256.hash "DREGG.POLICY.INSTALL.TRANSACTION/v1".toUTF8.toList
    ((StreamCodec.product digestStream
      (StreamCodec.product digestStream
        (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
          (StreamCodec.product StreamCodec.nat StreamCodec.nat)))).encode
      (domain, ingress.declaration.source.semantics, ingress.ingress.subject,
        ingress.declaration.source.policyId.value, ingress.declaration.nonce))).digest

def operationNullifier (domain : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain ingress.marker

/-! ## Source-derived candidate and deterministic physical representation -/

variable {F : Type} [Field F]

def context (federation : FederationId) (height : Height)
    (snapshot : CredentialAuthorityDomain.Snapshot) (ingress : DecodedIngress) : PolicyInstallController.RequestContext where
  federation := federation
  subject := ingress.ingress.subject
  subjectKeyEpoch := snapshot.authState.subjectKeyEpoch ingress.ingress.subject
  height := height
  policyEpoch := snapshot.authState.policyEpoch ingress.declaration.source.policyId
  policyRevision := snapshot.authState.policyRevision ingress.declaration.source.policyId

def payloadStore {deployment : Deployment} (ground : Ground deployment) : CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource deployment.domain ground.directory⟩

def successorCreate (deployment : Deployment) (declaration : PolicyInstallController.Declaration) :
    CreateRequest (CellId := Nat) Registry :=
  CanonicalCellRegistry.policySourceCreate deployment.domain declaration.source

def representationCreates (deployment : Deployment) (declaration : PolicyInstallController.Declaration) :
    List (CreateRequest (CellId := Nat) Registry) :=
  [successorCreate deployment declaration]

def planWrites (creates : List (CreateRequest (CellId := Nat) Registry))
    (authorityWrites : List DataWrite) : List DataWrite :=
  creates.map ResourceBirthController.birthWrite ++ authorityWrites

def PhysicalShape (deployment : Deployment) (ground : Ground deployment) (writes : List DataWrite) : Prop :=
  (writes.map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes, write.expectedPre = ground.view.model.roots write.cellId) ∧
    ∀ write ∈ writes, ResourceBirthController.Concrete.PhysicalPostLaw deployment write

instance physicalShapeDecidable (deployment : Deployment) (ground : Ground deployment)
    (writes : List DataWrite) : Decidable (PhysicalShape deployment ground writes) := by
  unfold PhysicalShape
  infer_instance

inductive Reject where
  | malformedIngress
  | semantic (reason : PolicyInstallController.Reject)
  | sourceMismatch
  | markerMismatch
  | structuralDependencies
  | lawDependencies
  | audience (reason : ObjectAudienceInstall.Reject)
  | oldSourceUnavailable
  | physicalLowering
  | allocation (reason : CellRegistry.RejectReason)
  | physicalShape
  | nativeSignature (reason : CredentialSignatureAdmission.Reject)
  | envelopeMismatch
  | transactionConflict
  /-- The ground has no journal answer for this install's transaction id (a light
  basis that did not declare it): refused, never read as "not recorded". -/
  | undeclaredTransaction
  /-- The ground has no answer for the operation marker's replay nullifier (a light
  basis that did not declare it): refused before any state is read, never "unspent". -/
  | undeclaredMarker
  deriving DecidableEq, Repr

private def require (condition : Prop) [Decidable condition] (reason : Reject) :
    Except Reject (PLift condition) :=
  if accepted : condition then .ok ⟨accepted⟩ else .error reason

private def fromOption {A : Type} (value : Option A) (reason : Reject) : Except Reject A :=
  match value with | none => .error reason | some value => .ok value

structure Prepared (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (ground : Ground deployment) (federation : FederationId) (height : Height)
    (ingress : DecodedIngress) : Type where
  private mk ::
  structural : WorldKindLawDependencies.Dependencies
  structuralExact : WorldKindLawDependencies.loadTarget deployment ground.directory
    ingress.declaration.source.policyId.value = some structural
  storageKind : Nat
  storageKindExact : (match ground.directory.slots ingress.declaration.source.policyId.value with
    | .present cell => some cell.1.tag.toNat
    | _ => none) = some storageKind
  /-- The installer prepared on this ground: its marker read only through the
  ground's answer (`Ground.markerSpent`). -/
  semantic : PolicyInstallController.Prepared profile ground.authority ground.markerSpent
    (context federation height ground.authority ingress)
  additionalExact : semantic.additional = structural.additional
  storageKindBound : semantic.storageKind = storageKind
  declarationExact : semantic.declaration = ingress.declaration
  markerExact : ingress.marker = (PolicyInstallController.requestDigest profile ground.authority
    (context federation height ground.authority ingress) semantic.declaration).value
  source : CanonicalCellRegistry.LoadedPolicySource deployment.domain ground.directory
    (ground.authority.authState.policyAddress ingress.declaration.source.policyId
      (context federation height ground.authority ingress).policyRevision)
  audience : ObjectAudienceInstall.Prepared deployment ground ingress.declaration.source.policyId.value
    source.record.audience semantic.declaration.source.audience
    (ObjectAudienceInstall.objectMetadataRequired source.record semantic.declaration.source)
  allocated : Directory Nat Registry
  allocationExact : ResourceBirth.allocate Registry ground.directory
    (representationCreates deployment semantic.declaration) = .ok allocated
  physicalShape : PhysicalShape deployment ground
    (planWrites (representationCreates deployment semantic.declaration)
      (ground.authorityWrites semantic.update.validated.apply))

def prepare (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (ground : Ground deployment) (federation : FederationId) (height : Height)
    (ingress : DecodedIngress) : Except Reject (Prepared profile deployment ground federation height ingress) := do
  if ground.markerSpent ingress.marker = none then throw .undeclaredMarker
  let structuralChecked ← fromOption (show Option { dependencies //
      WorldKindLawDependencies.loadTarget deployment ground.directory
        ingress.declaration.source.policyId.value = some dependencies } from
    match exact : WorldKindLawDependencies.loadTarget deployment ground.directory
        ingress.declaration.source.policyId.value with
    | none => none
    | some dependencies => some ⟨dependencies, rfl⟩) .structuralDependencies
  let structural := structuralChecked.val
  let kindValue := match ground.directory.slots ingress.declaration.source.policyId.value with
    | .present cell => some cell.1.tag.toNat
    | _ => none
  let storageKind ← fromOption kindValue .structuralDependencies
  let storageKindExact ← require (kindValue = some storageKind) .structuralDependencies
  let requestContext := context federation height ground.authority ingress
  let semantic ← match PolicyInstallController.prepare profile ground.authority ground.markerSpent requestContext ingress.ingress.declarationBytes structural.additional storageKind with
    | .error reason => .error (.semantic reason)
    | .ok prepared => .ok prepared
  let additionalExact ← require (semantic.additional = structural.additional) .structuralDependencies
  let storageKindBound ← require (semantic.storageKind = storageKind) .structuralDependencies
  let declarationExact ← require (semantic.declaration = ingress.declaration) .sourceMismatch
  let markerExact ← require (ingress.marker =
    (PolicyInstallController.requestDigest profile ground.authority requestContext semantic.declaration).value) .markerMismatch
  let source ← fromOption (CanonicalCellRegistry.loadPolicySource deployment.domain ground.directory
    (ground.authority.authState.policyAddress ingress.declaration.source.policyId requestContext.policyRevision))
    .oldSourceUnavailable
  let audience ← (ObjectAudienceInstall.prepare deployment ground
    ingress.declaration.source.policyId.value source.record.audience semantic.declaration.source.audience
    ingress.ingress.rosterBytes
    (ObjectAudienceInstall.objectMetadataRequired source.record semantic.declaration.source)).mapError Reject.audience
  let creates := representationCreates deployment semantic.declaration
  match allocationExact : ResourceBirth.allocate Registry ground.directory creates with
  | .error reason => .error (.allocation reason)
  | .ok allocated => do
      let shape ← require (PhysicalShape deployment ground
        (planWrites creates (ground.authorityWrites semantic.update.validated.apply))) .physicalShape
      .ok ⟨structural, structuralChecked.property,
        storageKind, storageKindExact.down, semantic, additionalExact.down, storageKindBound.down, declarationExact.down,
        markerExact.down, source, audience, allocated, allocationExact, shape.down⟩

variable {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment} {ground : Ground deployment}
    {federation : FederationId} {height : Height} {ingress : DecodedIngress}

def Prepared.creates (prepared : Prepared profile deployment ground federation height ingress) :=
  representationCreates deployment prepared.semantic.declaration

/-- The authority cell after the installation: the one validated install patch
applied to the loaded cell. -/
def Prepared.authorityPost (prepared : Prepared profile deployment ground federation height ingress) :
    CredentialAuthorityDomain.Cell :=
  prepared.semantic.update.validated.apply

def Prepared.writes (prepared : Prepared profile deployment ground federation height ingress) :=
  planWrites prepared.creates (ground.authorityWrites prepared.authorityPost)

def Prepared.readGuards (prepared : Prepared profile deployment ground federation height ingress) : List ReadGuard :=
  (ground.authorityReadGuards ++
      (([⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩] : List ReadGuard) ++ prepared.audience.readGuards)).filter
    fun guard => guard.cellId ∉ prepared.writes.map DataWrite.cellId

theorem Prepared.creates_source_owned
    (prepared : Prepared profile deployment ground federation height ingress) :
    prepared.creates = [successorCreate deployment ingress.declaration] := by
  simp only [Prepared.creates, representationCreates, prepared.declarationExact]

theorem Prepared.fresh_pre (prepared : Prepared profile deployment ground federation height ingress)
    (request : CreateRequest (CellId := Nat) Registry) (member : request ∈ prepared.creates) :
    LifecycleImage.view Registry ground.directory request.cellId = .fresh :=
  LifecycleImage.accepted_fresh_before Registry ground.directory prepared.allocated
    prepared.creates prepared.allocationExact request member

theorem Prepared.exact_created (prepared : Prepared profile deployment ground federation height ingress)
    (request : CreateRequest (CellId := Nat) Registry) (member : request ∈ prepared.creates) :
    prepared.allocated.slots request.cellId = .present request.cell :=
  ResourceBirth.allocate_success_created Registry ground.directory prepared.allocated
    prepared.creates prepared.allocationExact request member

theorem Prepared.write_roots_bound (prepared : Prepared profile deployment ground federation height ingress)
    (write : DataWrite) (member : write ∈ prepared.writes) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  rcases List.mem_append.mp member with created | changed
  · obtain ⟨request, _, rfl⟩ := List.mem_map.mp created
    exact ResourceBirthController.birthWrite_root_bound request
  · simp only [ServedBasis.Ground.authorityWrites, List.mem_singleton] at changed
    subst write
    exact ground.authorityWrite_root_bound _

theorem Prepared.readGuards_exact (prepared : Prepared profile deployment ground federation height ingress)
    (guard : ReadGuard) (member : guard ∈ prepared.readGuards) :
    guard.expectedRoot = ground.view.model.roots guard.cellId := by
  have present := (List.mem_filter.mp member).1
  rcases List.mem_append.mp present with authority | source
  · exact ground.authorityReadGuards_exact guard authority
  · rcases List.mem_append.mp source with source | audience
    · simp only [List.mem_singleton] at source
      subst guard
      exact prepared.source.readGuard_exact.trans
        ((congrArg rootBytes (ground.bytes_exact _)).trans (ground.view.coherent _))
    · exact prepared.audience.readGuardsExact guard audience

theorem Prepared.readGuards_readonly (prepared : Prepared profile deployment ground federation height ingress)
    (guard : ReadGuard) (member : guard ∈ prepared.readGuards) :
    guard.cellId ∉ prepared.writes.map DataWrite.cellId :=
  by simpa using (List.mem_filter.mp member).2

theorem Prepared.authority_reads_covered (prepared : Prepared profile deployment ground federation height ingress)
    (guard : ReadGuard) (member : guard ∈ ground.authorityReadGuards) :
    guard.cellId ∈ prepared.writes.map DataWrite.cellId ∨ guard ∈ prepared.readGuards := by
  by_cases written : guard.cellId ∈ prepared.writes.map DataWrite.cellId
  · exact Or.inl written
  · exact Or.inr (List.mem_filter.mpr ⟨List.mem_append_left _ member, by simpa using written⟩)

/-! ## The same actual native receipt and capability enter the existing installer -/

variable [DecidableEq F]

/-- Every selected old source and predecessor, and every external source used
by the candidate graph, is read under the old physical snapshot. Only the exact
new immutable source staged by this operation is exempt from an old-cell guard. -/
def dependencyGuards (prepared : Prepared profile deployment ground federation height ingress)
    (semantic : prepared.semantic.Accepted (payloadStore ground)) :
    Option (List (Nat × Digest)) := do
  let old ← (prepared.semantic.policyConfig (payloadStore ground)).resolve?
  let oldGuards ← PhysicalLawResolution.loadGuards ground.authority
    ground.directory (PhysicalLawResolution.addresses old.graph)
  let external := (PhysicalLawResolution.addresses semantic.candidateGraph).filter
    fun address => address != PolicyRecordCodec.digest prepared.semantic.declaration.source
  let candidateGuards ← PhysicalLawResolution.loadGuards ground.authority
    ground.directory external
  pure (prepared.structural.readGuards ++ oldGuards ++ candidateGuards).eraseDups

structure AcceptedInstall (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (ground : Ground deployment) (federation : FederationId) (height : Height) : Type where
  private mk ::
  ingress : DecodedIngress
  prepared : Prepared profile deployment ground federation height ingress
  receipt : CredentialSignatureAdmission.CheckedSignature ground.authority
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelopeBytes
  semantic : prepared.semantic.Accepted (payloadStore ground)
  admitted : prepared.semantic.admit (payloadStore ground)
    ingress.ingress.controlCapability receipt = .ok semantic
  lawGuards : List (Nat × Digest)
  lawGuardsExact : dependencyGuards prepared semantic = some lawGuards
  lawGuardsBound : lawGuards.all (fun guard =>
    decide (guard.2 = ground.view.model.roots ⟨guard.1⟩)) = true

/-- Admission on a ground. The marker's spent bit is answered declared and
unspent by `prepare` before the native verifier reads the authority's spent set
for it (`CredentialSignatureAdmission.controllerState`), so that read is the
ground's verified answer, never a light basis's silent default. -/
def admitDecodedNative (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (native : CredentialSignatureIO.NativeConfig) (ground : Ground deployment)
    (federation : FederationId) (height : Height) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedInstall profile deployment ground federation height)) := do
  match prepare profile deployment ground federation height ingress with
  | .error reason => return .error reason
  | .ok prepared =>
      let wanted := PolicyInstallController.request profile ground.authority
        (context federation height ground.authority ingress) prepared.semantic.declaration
      match ← CredentialSignatureAdmission.verifyNative native ground.authority
          (PolicyInstallController.requestDigest profile ground.authority
            (context federation height ground.authority ingress) prepared.semantic.declaration).value
          wanted ingress.ingress.envelopeBytes with
      | .error reason => return .error (.nativeSignature reason)
      | .ok receipt =>
          if envelopeExact : receipt.envelopeBytes = ingress.ingress.envelopeBytes then
            match admitted : prepared.semantic.admit (payloadStore ground)
                ingress.ingress.controlCapability receipt with
            | .error reason => return .error (.semantic reason)
            | .ok semantic =>
                match guardsExact : dependencyGuards prepared semantic with
                | none => return .error .lawDependencies
                | some guards =>
                    if bound : guards.all (fun guard =>
                        decide (guard.2 = ground.view.model.roots ⟨guard.1⟩)) = true then
                      return .ok ⟨ingress, prepared, receipt, envelopeExact, semantic, admitted,
                        guards, guardsExact, bound⟩
                    else return .error .lawDependencies
          else return .error .envelopeMismatch

def AcceptedInstall.installed (accepted : AcceptedInstall profile deployment ground federation height) :
    PolicyInstallController.Installed profile ground.authority ground.markerSpent
      (context federation height ground.authority accepted.ingress)
      (payloadStore ground) :=
  ⟨accepted.prepared.semantic, accepted.semantic⟩

/-- The written authority cell is the accepted installer's own post. -/
theorem AcceptedInstall.actual_authority_post
    (accepted : AcceptedInstall profile deployment ground federation height) :
    accepted.prepared.authorityPost.logical = accepted.installed.post.logical := rfl

theorem AcceptedInstall.actual_post_head
    (accepted : AcceptedInstall profile deployment ground federation height) :
    CredentialAuthorityDomain.headAt accepted.prepared.authorityPost.logical accepted.ingress.declaration.source.policyId =
      some ⟨accepted.ingress.declaration.source.version,
        PolicyRecordCodec.digest accepted.ingress.declaration.source⟩ := by
  rw [accepted.actual_authority_post, ← accepted.prepared.declarationExact]
  exact accepted.installed.source_selected_in_post

theorem AcceptedInstall.generation_preserved
    (accepted : AcceptedInstall profile deployment ground federation height) :
    accepted.prepared.authorityPost.logical
        ⟨.policyEpoch, accepted.ingress.declaration.source.policyId⟩ =
      ground.authority.logical
        ⟨.policyEpoch, accepted.ingress.declaration.source.policyId⟩ := by
  rw [accepted.actual_authority_post, ← accepted.prepared.declarationExact]
  exact accepted.installed.generation_preserved

theorem AcceptedInstall.capability_preserved
    (accepted : AcceptedInstall profile deployment ground federation height)
    (kind : ResourceKind) (id : CapabilityId) :
    accepted.prepared.authorityPost.logical ⟨.capability kind, id⟩ =
      ground.authority.logical ⟨.capability kind, id⟩ := by
  rw [accepted.actual_authority_post]
  exact accepted.installed.capability_preserved kind id

/-- The operation marker was unspent in the nullifier set of the ground this
install was prepared on; the intent below consumes it there. On a light ground
the answer is the spent map's, verified at use for the declared nullifier. -/
theorem AcceptedInstall.marker_was_unspent
    (accepted : AcceptedInstall profile deployment ground federation height) :
    CredentialAuthorityDomainReceiver.spentOf deployment.domain ground.view
      accepted.ingress.marker = false := by
  have answered : ground.markerSpent (PolicyInstallController.requestDigest profile ground.authority
      (context federation height ground.authority accepted.ingress)
      accepted.prepared.semantic.declaration).value = some false :=
    accepted.installed.marker_answered
  rw [← accepted.prepared.markerExact] at answered
  rw [← ground.authoritySpent]
  exact (ServedBasis.Ground.markerSpent_some ground answered).symm

/-! ## Exact source-owned intent, storage bytes and accounting -/

def event (domain : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := commitmentBytes ("DREGG.POLICY.INSTALL.EVENT/v1".toUTF8.toList ++
    digestStream.encode domain ++ ingress.bytes)
  canonicalBytes := ingress.bytes

/-- Admission units count the one semantic installation, its actual physical
touches and bytes, one native signature, capability admission and compiled
policy check. There is no invented monetary transfer for internal source or
authority representation; monetary operations require their conserved Book leg. -/
def AcceptedInstall.readGuards (accepted : AcceptedInstall profile deployment ground federation height) :
    List ReadGuard :=
  (accepted.prepared.readGuards ++ accepted.lawGuards.map (fun guard =>
    (⟨⟨guard.1⟩, guard.2⟩ : ReadGuard))).filter
      fun guard => guard.cellId ∉ accepted.prepared.writes.map DataWrite.cellId

theorem AcceptedInstall.readGuards_readonly
    (accepted : AcceptedInstall profile deployment ground federation height)
    (guard : ReadGuard) (member : guard ∈ accepted.readGuards) :
    guard.cellId ∉ accepted.prepared.writes.map DataWrite.cellId := by
  simpa using (List.mem_filter.mp member).2

theorem AcceptedInstall.readGuards_exact
    (accepted : AcceptedInstall profile deployment ground federation height)
    (guard : ReadGuard) (member : guard ∈ accepted.readGuards) :
    guard.expectedRoot = ground.view.model.roots guard.cellId := by
  have present := (List.mem_filter.mp member).1
  rcases List.mem_append.mp present with prepared | law
  · exact accepted.prepared.readGuards_exact guard prepared
  · obtain ⟨pair, inLaw, pairExact⟩ := List.mem_map.mp law
    cases pairExact
    exact of_decide_eq_true ((List.all_eq_true.mp accepted.lawGuardsBound) pair inLaw)

/-- Every dependency survives either as a read guard or as the same cell's
pre-state-checked write leg. No inherited source read is silently dropped. -/
theorem AcceptedInstall.law_reads_covered
    (accepted : AcceptedInstall profile deployment ground federation height)
    (pair : Nat × Digest) (member : pair ∈ accepted.lawGuards) :
    (⟨pair.1⟩ : CellId) ∈ accepted.prepared.writes.map DataWrite.cellId ∨
      (⟨⟨pair.1⟩, pair.2⟩ : ReadGuard) ∈ accepted.readGuards := by
  by_cases written : (⟨pair.1⟩ : CellId) ∈ accepted.prepared.writes.map DataWrite.cellId
  · exact Or.inl written
  · exact Or.inr (List.mem_filter.mpr ⟨List.mem_append_right _
      (List.mem_map.mpr ⟨pair, member, rfl⟩), by simpa using written⟩)

def charge (accepted : AcceptedInstall profile deployment ground federation height) : Charge
  | .incidences => 1
  | .turnBytes => accepted.ingress.bytes.length
  | .memoryTouches => accepted.prepared.writes.length + accepted.readGuards.length
  | .witnessBytes => accepted.ingress.ingress.envelopeBytes.length
  | .proofWork => 3
  | .storageBytes =>
      (accepted.prepared.writes.map fun write => write.canonicalPostBytes.length).sum +
        accepted.ingress.bytes.length
  | .sideEffectCount => 1
  | .feeDebit | .networkBytes | .leaseByteBlocks => 0

def intent (accepted : AcceptedInstall profile deployment ground federation height) : DataIntent rootBytes where
  transactionId := transactionId deployment.domain accepted.ingress
  writes := accepted.prepared.writes
  readGuards := accepted.readGuards
  nullifiers := [operationNullifier deployment.domain accepted.ingress]
  exactCharge := charge accepted
  event := event deployment.domain accepted.ingress
  subject := some accepted.ingress.ingress.subject
  postRootsBound := accepted.prepared.write_roots_bound
  guardsReadOnly := accepted.readGuards_readonly

theorem intent_exact_source (accepted : AcceptedInstall profile deployment ground federation height) :
    (intent accepted).writes = accepted.prepared.writes ∧
      (intent accepted).exactCharge = charge accepted ∧
      (intent accepted).event.canonicalBytes = accepted.ingress.bytes ∧
      (intent accepted).nullifiers = [CredentialAuthorityReplay.nullifier deployment.domain
        (PolicyInstallController.requestDigest profile ground.authority
          (context federation height ground.authority accepted.ingress)
          accepted.prepared.semantic.declaration).value] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  change [CredentialAuthorityReplay.nullifier deployment.domain accepted.ingress.marker] = _
  rw [accepted.prepared.markerExact]

theorem installed_write_bytes (accepted : AcceptedInstall profile deployment ground federation height)
    (write : DataWrite) (member : write ∈ accepted.prepared.writes) :
    (DataSnapshot.install ground.view (intent accepted)).canonicalBytes write.cellId =
      write.canonicalPostBytes :=
  DataSnapshot.install_canonicalBytes_of_member ground.view (intent accepted)
    accepted.prepared.physicalShape.1 write member

theorem installed_source_bytes (accepted : AcceptedInstall profile deployment ground federation height) :
    (DataSnapshot.install ground.view (intent accepted)).canonicalBytes
        ⟨PolicySourceCell.physicalId deployment.domain
          (PolicyRecordCodec.digest accepted.ingress.declaration.source)⟩ =
      LifecycleImage.bytes Registry
        (.live (CanonicalCellRegistry.policySourceCell accepted.ingress.declaration.source)) := by
  let request := successorCreate deployment accepted.prepared.semantic.declaration
  have member : ResourceBirthController.birthWrite request ∈ accepted.prepared.writes :=
    List.mem_append_left _ (List.mem_map.mpr ⟨request, List.mem_cons_self, rfl⟩)
  have installed := installed_write_bytes accepted _ member
  change (DataSnapshot.install ground.view (intent accepted)).canonicalBytes
      ⟨PolicySourceCell.physicalId deployment.domain
        (PolicyRecordCodec.digest accepted.prepared.semantic.declaration.source)⟩ =
    LifecycleImage.bytes Registry
      (.live (CanonicalCellRegistry.policySourceCell accepted.prepared.semantic.declaration.source)) at installed
  simpa only [accepted.prepared.declarationExact] using installed

/-- The actual installed row decodes to the exact source selected by the new
canonical head. This is a byte statement, not equality of cryptographic roots. -/
theorem installed_head_and_source (accepted : AcceptedInstall profile deployment ground federation height) :
    CredentialAuthorityDomain.headAt accepted.prepared.authorityPost.logical
        accepted.ingress.declaration.source.policyId =
      some ⟨accepted.ingress.declaration.source.version,
        PolicyRecordCodec.digest accepted.ingress.declaration.source⟩ ∧
    (LifecycleImage.codec Registry).decode
      ((DataSnapshot.install ground.view (intent accepted)).canonicalBytes
        ⟨PolicySourceCell.physicalId deployment.domain
          (PolicyRecordCodec.digest accepted.ingress.declaration.source)⟩) =
      some (.live (CanonicalCellRegistry.policySourceCell accepted.ingress.declaration.source)) := by
  refine ⟨accepted.actual_post_head, ?_⟩
  rw [installed_source_bytes]
  simpa only [LifecycleImage.codec, strictCodec, LifecycleImage.rawCodec] using
    (LifecycleImage.codec Registry).decode_encode
      (.live (CanonicalCellRegistry.policySourceCell accepted.ingress.declaration.source))

/-- The existing source loader selects a genuinely present canonical source.
This generic completeness lemma applies to every actual directory readback;
it adds no host source map or digest-injectivity assumption. -/
theorem source_loader_of_present (domain : Digest) (directory : Directory Nat Registry)
    (record : PolicyRecord)
    (present : directory.slots (PolicySourceCell.physicalId domain (PolicyRecordCodec.digest record)) =
      .present (CanonicalCellRegistry.policySourceCell record))
    (domainExact : record.domain = domain) :
    ∃ loaded, CanonicalCellRegistry.loadPolicySource domain directory (PolicyRecordCodec.digest record) =
      some loaded ∧ loaded.record = record := by
  have fetched := CanonicalCellRegistry.fetchPolicySource_exact domain directory
    (PolicyRecordCodec.digest record) record present domainExact rfl
  change (CanonicalCellRegistry.loadPolicySource domain directory (PolicyRecordCodec.digest record)).map
    CanonicalCellRegistry.LoadedPolicySource.canonicalBytes = some _ at fetched
  obtain ⟨loaded, loadedAt, _⟩ := Option.map_eq_some_iff.mp fetched
  exact ⟨loaded, loadedAt, loaded.record_of_present record present⟩

omit [DecidableEq F] in
theorem Prepared.fresh_before (prepared : Prepared profile deployment ground federation height ingress)
    (request : CreateRequest (CellId := Nat) Registry) (member : request ∈ prepared.creates) :
    ground.view.canonicalBytes ⟨request.cellId⟩ = [] := by
  rw [← ground.bytes_exact, prepared.fresh_pre request member]
  rfl

/-- The installed image holds exactly the post authority cell at the pinned
identifier: one write, carrying the accepted installer's post. -/
theorem installed_authority_cell (accepted : AcceptedInstall profile deployment ground federation height) :
    (DataSnapshot.install ground.view (intent accepted)).canonicalBytes
        (CredentialAuthorityDomainReceiver.cellIdOf deployment) =
      CredentialAuthorityDomainReceiver.cellBytes accepted.prepared.authorityPost := by
  have member : ground.authorityWrite accepted.prepared.authorityPost ∈
      accepted.prepared.writes := by
    unfold Prepared.writes planWrites ServedBasis.Ground.authorityWrites
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  exact installed_write_bytes accepted
    (ground.authorityWrite accepted.prepared.authorityPost) member

theorem no_partial_commit (accepted : AcceptedInstall profile deployment ground federation height)
    (schedule : Schedule) :
    (DurableDataIntent.execute schedule ground.view (intent accepted)).storeAfter ground.view =
        ground.view ∨
      (DurableDataIntent.execute schedule ground.view (intent accepted)).storeAfter ground.view =
        DataSnapshot.install ground.view (intent accepted) :=
  execute_no_partial_data_commit schedule ground.view (intent accepted)

/-! ## Receipt-only replay precedes all new admission -/

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain ingress, (event domain ingress).eventId⟩

/-- The keys an install reads of the history: its transaction id (replay) and its
operation marker's replay nullifier (the installer's spent check). Both are in
the signed ingress, so they are known before any state is read. -/
def keys (domain : Digest) (ingress : DecodedIngress) : DurableView.Keys :=
  ⟨[transactionId domain ingress], [operationNullifier domain ingress]⟩

/-- The recorded intent under this install's transaction id is exactly its own. -/
def exactRecord (domain : Digest) (ingress : DecodedIngress)
    (recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope) : Bool :=
  decide (recorded.transactionId = transactionId domain ingress ∧
    recorded.event.event = event domain ingress ∧
    recorded.nullifiers = [operationNullifier domain ingress])

/-- The replay verdict on a ground, read only through its answer for the
transaction id (`ServedBasis.Ground.replayOf`): an undeclared id is `undeclared`. -/
def replay (domain : Digest) (ground : Ground deployment) (ingress : DecodedIngress) :
    ServedBasis.Ground.Replay Receipt :=
  ground.replayOf (transactionId domain ingress) (exactRecord domain ingress) (receipt domain ingress)

theorem replay_only_original (domain : Digest) (ground : Ground deployment) (ingress : DecodedIngress)
    (result : Receipt) (accepted : replay domain ground ingress = .original result) :
    result = receipt domain ingress ∧
      ∃ recorded,
        Snapshot.lookupRecorded (transactionId domain ingress) ground.view.model.journal = some recorded ∧
        recorded.event.event = event domain ingress ∧
        recorded.nullifiers = [operationNullifier domain ingress] := by
  obtain ⟨same, recorded, found, isExact⟩ := ServedBasis.Ground.replayOf_original ground _ _ _ result accepted
  simp only [exactRecord, decide_eq_true_eq] at isExact
  exact ⟨same, recorded, found, isExact.2⟩

/-- **A changed ingress under a recorded transaction id is refused as a conflict**:
the ground's journal answer for this ingress's transaction id is an intent whose
event differs from this ingress's event, so the verdict is `conflict` — never
`fresh` (a second admission) and never `original` (a receipt). -/
theorem replay_changed_ingress_refused (domain : Digest) (ground : Ground deployment) (ingress : DecodedIngress)
    {recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope}
    (found : ground.recorded (transactionId domain ingress) = some (some recorded))
    (different : recorded.event.event ≠ event domain ingress) :
    replay domain ground ingress = .conflict :=
  ServedBasis.Ground.replayOf_conflict ground _ _ _ found (by simp [exactRecord, different])

#assert_axioms replay_changed_ingress_refused

/-- **An undeclared transaction id is refused by name** (the plant's pole): on a
light basis that did not declare it, the verdict is `undeclared`, never "not
recorded". -/
theorem replay_undeclared (domain : Digest) {store : DurableHistory.StoreIdentity}
    (basis : ServedBasis.Basis deployment store) (ingress : DecodedIngress)
    (undeclared : transactionId domain ingress ∉ basis.keys.transactions) :
    replay domain (ServedBasis.Ground.ofBasis basis) ingress = .undeclared :=
  ServedBasis.Ground.replayOf_undeclared basis _ _ _ undeclared

/-- **An undeclared operation marker is refused by name, first** (the plant's
pole): on a light basis that did not declare the marker's replay nullifier,
`prepare` is `undeclaredMarker` whatever the state — never read as unspent. -/
theorem prepare_undeclaredMarker (profile : CanonicalRuntimeProfile.Profile F) {store : DurableHistory.StoreIdentity}
    (basis : ServedBasis.Basis deployment store) (federation : FederationId) (height : Height)
    (ingress : DecodedIngress)
    (undeclared : operationNullifier deployment.domain ingress ∉ basis.keys.nullifiers) :
    (prepare profile deployment (ServedBasis.Ground.ofBasis basis) federation height ingress).map (fun _ => ()) =
      .error .undeclaredMarker := by
  have unanswered := ServedBasis.Ground.markerSpent_undeclared basis ingress.marker undeclared
  unfold prepare
  simp only [unanswered]
  rfl

#assert_axioms prepare_undeclaredMarker
#assert_axioms replay_only_original
#assert_axioms replay_undeclared

end Minidregg.Kernel.PolicyInstallReceiver
