/-
# Kernel.PolicyInstallReceiver -- one durable, capability-authorized policy installation

The existing installer determines and admits the semantic authority transition.
This receiver refines that same declaration into immutable source allocation and
the existing routed shard/catalogue writes. The internal creates are determined
by the installed source and page materializer; no caller supplies auxiliary
payloads, an alternate policy store, or a raw durable intent.

The original canonical signed ingress is retained for receipt-only replay before
fresh-state admission. A replay never resigns an old request or derives a new
marker from the current height or authority state.

Source replacement advances the selected revision while preserving the grant
generation. Every later use checks the newly selected source. The current source
still governs its own replacement, so a deliberately restrictive new law may
refuse future installations even though the control grant remains current.
-/
import Kernel.PolicyInstallController
import Kernel.ResourceBirthController
import Compiler.DurableReceiverIO
import Compiler.CredentialAuthorityReplay

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
abbrev Durable := DurableReceiverIO.Loaded rootBytes

attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

/-! ## Strict original command and signature bytes -/

structure Ingress where
  subject : SubjectId
  controlCapability : CapabilityId
  declarationBytes : List UInt8
  envelopeBytes : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
        (StreamCodec.product bytesStream bytesStream)))
    (fun ingress => (ingress.subject, ingress.controlCapability,
      ingress.declarationBytes, ingress.envelopeBytes))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro ingress; cases ingress; rfl)

def ingressFrame : List UInt8 := "DREGG/POLICY/INSTALL/SIGNED-INGRESS".toUTF8.toList ++ [1]

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

def payloadStore {durable : Durable} (deployment : Deployment)
    (directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable) : CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource deployment.domain directory.directory⟩

def successorCreate (deployment : Deployment) (declaration : PolicyInstallController.Declaration) :
    CreateRequest (CellId := Nat) Registry :=
  CanonicalCellRegistry.policySourceCreate deployment.domain declaration.source

def representationCreates (deployment : Deployment) (declaration : PolicyInstallController.Declaration)
    (placement : CredentialAuthorityDomainReceiver.Placement) : List (CreateRequest (CellId := Nat) Registry) :=
  successorCreate deployment declaration :: placement.auxiliaryCreates

def planWrites (creates : List (CreateRequest (CellId := Nat) Registry))
    (authorityWrites : List DataWrite) : List DataWrite :=
  creates.map ResourceBirthController.birthWrite ++ authorityWrites

def PhysicalShape (deployment : Deployment) (durable : Durable) (writes : List DataWrite) : Prop :=
  (writes.map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    ∀ write ∈ writes, ResourceBirthController.Concrete.PhysicalPostLaw deployment write

instance physicalShapeDecidable (deployment : Deployment) (durable : Durable)
    (writes : List DataWrite) : Decidable (PhysicalShape deployment durable writes) := by
  unfold PhysicalShape
  infer_instance

inductive Reject where
  | malformedIngress
  | deployment
  | directory
  | authority
  | semantic (reason : PolicyInstallController.Reject)
  | sourceMismatch
  | markerMismatch
  | oldSourceUnavailable
  | physicalLowering
  | allocation (reason : CellRegistry.RejectReason)
  | physicalShape
  | nativeSignature (reason : CredentialSignatureAdmission.Reject)
  | envelopeMismatch
  | transactionConflict
  deriving DecidableEq, Repr

private def require (condition : Prop) [Decidable condition] (reason : Reject) :
    Except Reject (PLift condition) :=
  if accepted : condition then .ok ⟨accepted⟩ else .error reason

private def fromOption {A : Type} (value : Option A) (reason : Reject) : Except Reject A :=
  match value with | none => .error reason | some value => .ok value

structure Prepared (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (durable : Durable) (federation : FederationId) (height : Height)
    (ingress : DecodedIngress) : Type where
  private mk ::
  deploymentValid : deployment.Valid
  directory : CredentialAuthorityDomainReceiver.LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment.authorityAnchor durable.snapshot
  semantic : PolicyInstallController.Prepared profile authority.snapshot (context federation height authority.snapshot ingress)
  declarationExact : semantic.declaration = ingress.declaration
  markerExact : ingress.marker = (PolicyInstallController.requestDigest profile authority.snapshot
    (context federation height authority.snapshot ingress) semantic.declaration).value
  source : CanonicalCellRegistry.LoadedPolicySource deployment.domain directory.directory
    (authority.snapshot.authState.policyAddress ingress.declaration.source.policyId
      (context federation height authority.snapshot ingress).policyRevision)
  lowered : CredentialAuthorityDomainReceiver.Lowered directory authority
    (PolicyInstallController.edits profile authority.snapshot (context federation height authority.snapshot ingress)
      semantic.declaration) semantic.update [(successorCreate deployment semantic.declaration).cellId]
  allocated : Directory Nat Registry
  allocationExact : ResourceBirth.allocate Registry directory.directory
    (representationCreates deployment semantic.declaration lowered.placement) = .ok allocated
  physicalShape : PhysicalShape deployment durable
    (planWrites (representationCreates deployment semantic.declaration lowered.placement) lowered.writes)

def prepare (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (durable : Durable) (federation : FederationId) (height : Height)
    (ingress : DecodedIngress) : Except Reject (Prepared profile deployment durable federation height ingress) := do
  let deploymentValid ← require deployment.Valid .deployment
  let directory ← fromOption (CredentialAuthorityDomainReceiver.loadDirectory durable) .directory
  let authority ← fromOption (CredentialAuthorityDomainReceiver.loadDeployment deployment durable.snapshot) .authority
  let requestContext := context federation height authority.snapshot ingress
  let semantic ← match PolicyInstallController.prepare profile authority.snapshot requestContext ingress.ingress.declarationBytes with
    | .error reason => .error (.semantic reason)
    | .ok prepared => .ok prepared
  let declarationExact ← require (semantic.declaration = ingress.declaration) .sourceMismatch
  let markerExact ← require (ingress.marker =
    (PolicyInstallController.requestDigest profile authority.snapshot requestContext semantic.declaration).value) .markerMismatch
  let source ← fromOption (CanonicalCellRegistry.loadPolicySource deployment.domain directory.directory
    (authority.snapshot.authState.policyAddress ingress.declaration.source.policyId requestContext.policyRevision))
    .oldSourceUnavailable
  let lowered ← fromOption (CredentialAuthorityDomainReceiver.lower directory authority semantic.update
    [(successorCreate deployment semantic.declaration).cellId]) .physicalLowering
  let creates := representationCreates deployment semantic.declaration lowered.placement
  match allocationExact : ResourceBirth.allocate Registry directory.directory creates with
  | .error reason => .error (.allocation reason)
  | .ok allocated => do
      let shape ← require (PhysicalShape deployment durable (planWrites creates lowered.writes)) .physicalShape
      .ok ⟨deploymentValid.down, directory, authority, semantic, declarationExact.down,
        markerExact.down, source, lowered, allocated, allocationExact, shape.down⟩

variable {profile : CanonicalRuntimeProfile.Profile F} {deployment : Deployment} {durable : Durable}
    {federation : FederationId} {height : Height} {ingress : DecodedIngress}

def Prepared.creates (prepared : Prepared profile deployment durable federation height ingress) :=
  representationCreates deployment prepared.semantic.declaration prepared.lowered.placement

def Prepared.writes (prepared : Prepared profile deployment durable federation height ingress) :=
  planWrites prepared.creates prepared.lowered.writes

def Prepared.readGuards (prepared : Prepared profile deployment durable federation height ingress) : List ReadGuard :=
  CredentialAuthorityDomainReceiver.readonlyGuards
    (prepared.authority.readGuards ++ [⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩])
    prepared.writes

theorem Prepared.creates_source_owned
    (prepared : Prepared profile deployment durable federation height ingress) :
    prepared.creates = successorCreate deployment ingress.declaration ::
      prepared.lowered.placement.auxiliaryCreates := by
  simp only [Prepared.creates, representationCreates, prepared.declarationExact]

theorem Prepared.fresh_pre (prepared : Prepared profile deployment durable federation height ingress)
    (request : CreateRequest (CellId := Nat) Registry) (member : request ∈ prepared.creates) :
    LifecycleImage.view Registry prepared.directory.directory request.cellId = .fresh :=
  LifecycleImage.accepted_fresh_before Registry prepared.directory.directory prepared.allocated
    prepared.creates prepared.allocationExact request member

theorem Prepared.exact_created (prepared : Prepared profile deployment durable federation height ingress)
    (request : CreateRequest (CellId := Nat) Registry) (member : request ∈ prepared.creates) :
    prepared.allocated.slots request.cellId = .present request.cell :=
  ResourceBirth.allocate_success_created Registry prepared.directory.directory prepared.allocated
    prepared.creates prepared.allocationExact request member

theorem Prepared.source_reserved (prepared : Prepared profile deployment durable federation height ingress)
    (request : CreateRequest (CellId := Nat) Registry)
    (member : request ∈ prepared.lowered.placement.auxiliaryCreates) :
    request.cellId ≠ (successorCreate deployment prepared.semantic.declaration).cellId := by
  have fresh := prepared.lowered.fresh.2 request member
  simpa using fresh.2

theorem Prepared.write_roots_bound (prepared : Prepared profile deployment durable federation height ingress)
    (write : DataWrite) (member : write ∈ prepared.writes) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  rcases List.mem_append.mp member with created | changed
  · obtain ⟨request, _, rfl⟩ := List.mem_map.mp created
    exact ResourceBirthController.birthWrite_root_bound request
  · exact CredentialAuthorityDomainReceiver.planWrites_roots_bound deployment.authorityAnchor durable.snapshot
      prepared.authority.snapshot.catalogue prepared.semantic.update.postPages
      prepared.lowered.placement write changed

theorem Prepared.readGuards_exact (prepared : Prepared profile deployment durable federation height ingress)
    (guard : ReadGuard) (member : guard ∈ prepared.readGuards) :
    guard.expectedRoot = durable.snapshot.model.roots guard.cellId := by
  have present := (List.mem_filter.mp member).1
  rcases List.mem_append.mp present with authority | source
  · exact prepared.authority.readGuards_exact guard authority
  · simp only [List.mem_singleton] at source
    subst guard
    exact prepared.source.readGuard_exact.trans
      ((congrArg rootBytes (prepared.directory.bytes_exact _)).trans (durable.snapshot.coherent _))

theorem Prepared.readGuards_readonly (prepared : Prepared profile deployment durable federation height ingress)
    (guard : ReadGuard) (member : guard ∈ prepared.readGuards) :
    guard.cellId ∉ prepared.writes.map DataWrite.cellId :=
  of_decide_eq_true (List.mem_filter.mp member).2

theorem Prepared.authority_reads_covered (prepared : Prepared profile deployment durable federation height ingress)
    (guard : ReadGuard) (member : guard ∈ prepared.authority.readGuards) :
    guard.cellId ∈ prepared.writes.map DataWrite.cellId ∨ guard ∈ prepared.readGuards := by
  by_cases written : guard.cellId ∈ prepared.writes.map DataWrite.cellId
  · exact Or.inl written
  · exact Or.inr (List.mem_filter.mpr ⟨List.mem_append_left _ member, by simpa using written⟩)

/-! ## The same actual native receipt and capability enter the existing installer -/

variable [DecidableEq F]

structure AcceptedInstall (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (durable : Durable) (federation : FederationId) (height : Height) : Type where
  private mk ::
  ingress : DecodedIngress
  prepared : Prepared profile deployment durable federation height ingress
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelopeBytes
  semantic : prepared.semantic.Accepted (payloadStore deployment prepared.directory)
  admitted : prepared.semantic.admit (payloadStore deployment prepared.directory)
    ingress.ingress.controlCapability receipt = .ok semantic

def admitDecodedNative (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (native : CredentialSignatureIO.NativeConfig) (durable : Durable)
    (federation : FederationId) (height : Height) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedInstall profile deployment durable federation height)) := do
  match prepare profile deployment durable federation height ingress with
  | .error reason => return .error reason
  | .ok prepared =>
      let wanted := PolicyInstallController.request profile prepared.authority.snapshot
        (context federation height prepared.authority.snapshot ingress) prepared.semantic.declaration
      match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
          (PolicyInstallController.requestDigest profile prepared.authority.snapshot
            (context federation height prepared.authority.snapshot ingress) prepared.semantic.declaration).value
          wanted ingress.ingress.envelopeBytes with
      | .error reason => return .error (.nativeSignature reason)
      | .ok receipt =>
          if envelopeExact : receipt.envelopeBytes = ingress.ingress.envelopeBytes then
            match admitted : prepared.semantic.admit (payloadStore deployment prepared.directory)
                ingress.ingress.controlCapability receipt with
            | .error reason => return .error (.semantic reason)
            | .ok semantic => return .ok ⟨ingress, prepared, receipt, envelopeExact, semantic, admitted⟩
          else return .error .envelopeMismatch

def AcceptedInstall.installed (accepted : AcceptedInstall profile deployment durable federation height) :
    PolicyInstallController.Installed profile accepted.prepared.authority.snapshot
      (context federation height accepted.prepared.authority.snapshot accepted.ingress)
      (payloadStore deployment accepted.prepared.directory) :=
  ⟨accepted.prepared.semantic, accepted.semantic⟩

theorem AcceptedInstall.actual_authority_post
    (accepted : AcceptedInstall profile deployment durable federation height) :
    accepted.prepared.lowered.post.logical = accepted.installed.post.logical := by
  rw [accepted.installed.post_pages_exact]
  change accepted.prepared.lowered.post.logical =
    CredentialAuthorityDomain.logicalOfPages accepted.prepared.semantic.update.postPages
  change CredentialAuthorityDomain.logicalOfPages accepted.prepared.lowered.post.pages = _
  rw [accepted.prepared.lowered.postPages]

theorem AcceptedInstall.actual_post_head
    (accepted : AcceptedInstall profile deployment durable federation height) :
    CredentialAuthorityDomain.headAt accepted.prepared.lowered.post.logical accepted.ingress.declaration.source.policyId =
      some ⟨accepted.ingress.declaration.source.version,
        PolicyRecordCodec.digest accepted.ingress.declaration.source⟩ := by
  rw [accepted.actual_authority_post, ← accepted.prepared.declarationExact]
  exact accepted.installed.source_selected_in_post

theorem AcceptedInstall.generation_preserved
    (accepted : AcceptedInstall profile deployment durable federation height) :
    accepted.prepared.lowered.post.logical.fields
        (.policyEpoch accepted.ingress.declaration.source.policyId) =
      accepted.prepared.authority.snapshot.logical.fields
        (.policyEpoch accepted.ingress.declaration.source.policyId) := by
  rw [accepted.actual_authority_post, ← accepted.prepared.declarationExact]
  exact accepted.installed.generation_preserved

theorem AcceptedInstall.capability_preserved
    (accepted : AcceptedInstall profile deployment durable federation height)
    (kind : ResourceKind) (id : CapabilityId) :
    accepted.prepared.lowered.post.logical.fields (.capability kind id) =
      accepted.prepared.authority.snapshot.logical.fields (.capability kind id) := by
  rw [accepted.actual_authority_post]
  exact accepted.installed.capability_preserved kind id

theorem AcceptedInstall.marker_consumed
    (accepted : AcceptedInstall profile deployment durable federation height) :
    accepted.prepared.lowered.post.logical.fields (.nullifier accepted.ingress.marker) = some true := by
  rw [accepted.actual_authority_post, accepted.prepared.markerExact]
  exact accepted.installed.nullifier_consumed

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
shard representation; monetary operations require their conserved Book leg. -/
def charge (accepted : AcceptedInstall profile deployment durable federation height) : Charge
  | .incidences => 1
  | .turnBytes => accepted.ingress.bytes.length
  | .memoryTouches => accepted.prepared.writes.length + accepted.prepared.readGuards.length
  | .witnessBytes => accepted.ingress.ingress.envelopeBytes.length
  | .proofWork => 3
  | .storageBytes =>
      (accepted.prepared.writes.map fun write => write.canonicalPostBytes.length).sum +
        accepted.ingress.bytes.length
  | .sideEffectCount => 1
  | .feeDebit | .networkBytes | .leaseByteBlocks => 0

def intent (accepted : AcceptedInstall profile deployment durable federation height) : DataIntent rootBytes where
  transactionId := transactionId deployment.domain accepted.ingress
  writes := accepted.prepared.writes
  readGuards := accepted.prepared.readGuards
  nullifiers := [operationNullifier deployment.domain accepted.ingress]
  exactCharge := charge accepted
  event := event deployment.domain accepted.ingress
  postRootsBound := accepted.prepared.write_roots_bound
  guardsReadOnly := accepted.prepared.readGuards_readonly

theorem intent_exact_source (accepted : AcceptedInstall profile deployment durable federation height) :
    (intent accepted).writes = accepted.prepared.writes ∧
      (intent accepted).exactCharge = charge accepted ∧
      (intent accepted).event.canonicalBytes = accepted.ingress.bytes ∧
      (intent accepted).nullifiers = [CredentialAuthorityReplay.nullifier deployment.domain
        (PolicyInstallController.requestDigest profile accepted.prepared.authority.snapshot
          (context federation height accepted.prepared.authority.snapshot accepted.ingress)
          accepted.prepared.semantic.declaration).value] := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  change [CredentialAuthorityReplay.nullifier deployment.domain accepted.ingress.marker] = _
  rw [accepted.prepared.markerExact]

theorem installed_write_bytes (accepted : AcceptedInstall profile deployment durable federation height)
    (write : DataWrite) (member : write ∈ accepted.prepared.writes) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes write.cellId =
      write.canonicalPostBytes :=
  DataSnapshot.install_canonicalBytes_of_member durable.snapshot (intent accepted)
    accepted.prepared.physicalShape.1 write member

theorem installed_source_bytes (accepted : AcceptedInstall profile deployment durable federation height) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
        ⟨PolicySourceCell.physicalId deployment.domain
          (PolicyRecordCodec.digest accepted.ingress.declaration.source)⟩ =
      LifecycleImage.bytes Registry
        (.live (CanonicalCellRegistry.policySourceCell accepted.ingress.declaration.source)) := by
  let request := successorCreate deployment accepted.prepared.semantic.declaration
  have member : ResourceBirthController.birthWrite request ∈ accepted.prepared.writes :=
    List.mem_append_left _ (List.mem_map.mpr ⟨request, List.mem_cons_self, rfl⟩)
  have installed := installed_write_bytes accepted _ member
  change (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
      ⟨PolicySourceCell.physicalId deployment.domain
        (PolicyRecordCodec.digest accepted.prepared.semantic.declaration.source)⟩ =
    LifecycleImage.bytes Registry
      (.live (CanonicalCellRegistry.policySourceCell accepted.prepared.semantic.declaration.source)) at installed
  simpa only [accepted.prepared.declarationExact] using installed

/-- The actual installed row decodes to the exact source selected by the new
canonical head. This is a byte statement, not equality of cryptographic roots. -/
theorem installed_head_and_source (accepted : AcceptedInstall profile deployment durable federation height) :
    CredentialAuthorityDomain.headAt accepted.prepared.lowered.post.logical
        accepted.ingress.declaration.source.policyId =
      some ⟨accepted.ingress.declaration.source.version,
        PolicyRecordCodec.digest accepted.ingress.declaration.source⟩ ∧
    (LifecycleImage.codec Registry).decode
      ((DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
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
theorem Prepared.fresh_before (prepared : Prepared profile deployment durable federation height ingress)
    (request : CreateRequest (CellId := Nat) Registry) (member : request ∈ prepared.creates) :
    durable.snapshot.canonicalBytes ⟨request.cellId⟩ = [] := by
  rw [← prepared.directory.bytes_exact, prepared.fresh_pre request member]
  rfl

/-- Source and internal shard allocations cannot overwrite an old live shard
that the semantic materializer leaves unchanged. Permanent freshness is checked
against the whole old directory, including tombstones. -/
theorem unchanged_authority_shard_unwritten
    (accepted : AcceptedInstall profile deployment durable federation height)
    (cellId : DurableDataIntent.CellId) (page : CredentialAuthorityPageMaterializer.Page)
    (physical : durable.snapshot.canonicalBytes cellId =
      CredentialAuthorityDomainReceiver.shardBytes page)
    (authorityUnwritten : cellId ∉ accepted.prepared.lowered.writes.map DataWrite.cellId) :
    cellId ∉ accepted.prepared.writes.map DataWrite.cellId := by
  intro member
  obtain ⟨write, member, same⟩ := List.mem_map.mp member
  rcases List.mem_append.mp member with allocation | authority
  · obtain ⟨request, inRequests, rfl⟩ := List.mem_map.mp allocation
    have fresh := accepted.prepared.fresh_before request inRequests
    change (⟨request.cellId⟩ : DurableDataIntent.CellId) = cellId at same
    rw [same] at fresh
    have impossible := fresh.symm.trans physical
    cases impossible
  · exact authorityUnwritten (List.mem_map.mpr ⟨write, authority, same⟩)

private theorem installed_authority_page
    (accepted : AcceptedInstall profile deployment durable federation height)
    (reference : CredentialAuthorityDomain.Ref) (page : CredentialAuthorityPageMaterializer.Page)
    (represented : CredentialAuthorityDomainReceiver.PostPageRepresented durable.snapshot
      accepted.prepared.lowered.writes accepted.prepared.lowered.readGuards
      accepted.prepared.lowered.placement.auxiliaryCreates reference page) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes reference.cellId =
      CredentialAuthorityDomainReceiver.shardBytes page := by
  rcases represented.2 with written | created | unchanged
  · obtain ⟨write, member, same, bytes⟩ := written
    have installed := installed_write_bytes accepted write (List.mem_append_right _ member)
    rw [same, bytes] at installed
    exact installed
  · obtain ⟨request, member, same, bytes⟩ := created
    have inRequests : request ∈ accepted.prepared.creates := List.mem_cons_of_mem _ member
    have inWrites : ResourceBirthController.birthWrite request ∈ accepted.prepared.writes :=
      List.mem_append_left _ (List.mem_map.mpr ⟨request, inRequests, rfl⟩)
    have installed := installed_write_bytes accepted _ inWrites
    change (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
      ⟨request.cellId⟩ = LifecycleImage.bytes Registry (.live request.cell) at installed
    rw [same, bytes] at installed
    exact installed
  · obtain ⟨bytes, guard, member, same⟩ := unchanged
    have localFrame := accepted.prepared.lowered.readGuards_readonly guard member
    rw [same] at localFrame
    have frame := unchanged_authority_shard_unwritten accepted reference.cellId page bytes localFrame
    rw [DataSnapshot.install_canonicalBytes]
    simp only [intent]
    rw [DurableReceiver.lookupPostBytes_missing _ _ frame]
    exact bytes

theorem installed_authority_pages (accepted : AcceptedInstall profile deployment durable federation height) :
    List.Forall₂
      (fun (reference : CredentialAuthorityDomain.Ref) (page : CredentialAuthorityPageMaterializer.Page) =>
        (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes reference.cellId =
          CredentialAuthorityDomainReceiver.shardBytes page)
      accepted.prepared.lowered.post.catalogue.pages accepted.prepared.lowered.post.pages :=
  accepted.prepared.lowered.represented.imp
    (fun reference page represented => installed_authority_page accepted reference page represented)

theorem installed_authority_catalogue (accepted : AcceptedInstall profile deployment durable federation height) :
    (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
        deployment.authorityAnchor.catalogueCellId =
      CredentialAuthorityDomainReceiver.catalogueBytes accepted.prepared.lowered.post.catalogue := by
  let write := CredentialAuthorityDomainReceiver.catalogueWrite deployment.authorityAnchor durable.snapshot
    (CredentialAuthorityDomainReceiver.placedCatalogue
      accepted.prepared.authority.snapshot.catalogue accepted.prepared.lowered.placement)
  have member : write ∈ accepted.prepared.writes :=
    List.mem_append_right _ (by
      simp [write, CredentialAuthorityDomainReceiver.Lowered.writes,
        CredentialAuthorityDomainReceiver.planWrites])
  have installed := installed_write_bytes accepted write member
  change (DataSnapshot.install durable.snapshot (intent accepted)).canonicalBytes
    deployment.authorityAnchor.catalogueCellId = _ at installed
  rw [accepted.prepared.lowered.postCatalogue]
  exact installed

theorem no_partial_commit (accepted : AcceptedInstall profile deployment durable federation height)
    (schedule : Schedule) :
    (DurableDataIntent.execute schedule durable.snapshot (intent accepted)).storeAfter durable.snapshot =
        durable.snapshot ∨
      (DurableDataIntent.execute schedule durable.snapshot (intent accepted)).storeAfter durable.snapshot =
        DataSnapshot.install durable.snapshot (intent accepted) :=
  execute_no_partial_data_commit schedule durable.snapshot (intent accepted)

/-! ## Receipt-only replay precedes all new admission -/

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain ingress, (event domain ingress).eventId⟩

def replay (domain : Digest) (durable : Durable) (ingress : DecodedIngress) :
    Option (Except Reject Receipt) :=
  match Snapshot.lookupRecorded (transactionId domain ingress) durable.snapshot.model.journal with
  | none => none
  | some recorded =>
      if recorded.transactionId = transactionId domain ingress ∧
          recorded.event.event = event domain ingress ∧
          recorded.nullifiers = [operationNullifier domain ingress] then
        some (.ok (receipt domain ingress))
      else some (.error .transactionConflict)

theorem replay_only_original (domain : Digest) (durable : Durable) (ingress : DecodedIngress)
    (result : Receipt) (accepted : replay domain durable ingress = some (.ok result)) :
    result = receipt domain ingress ∧
      ∃ recorded,
        Snapshot.lookupRecorded (transactionId domain ingress) durable.snapshot.model.journal = some recorded ∧
        recorded.event.event = event domain ingress ∧
        recorded.nullifiers = [operationNullifier domain ingress] := by
  unfold replay at accepted
  split at accepted
  · cases accepted
  · rename_i recorded found
    split at accepted
    · rename_i exactRecord
      have same : receipt domain ingress = result := by simpa using accepted
      exact ⟨same.symm, recorded, found, exactRecord.2⟩
    · cases accepted

theorem replay_changed_ingress_refused (domain : Digest) (durable : Durable) (ingress : DecodedIngress)
    (recorded : DurableCommitProtocol.Intent TransactionId DurableDataIntent.CellId StableNullifier ReplayEnvelope)
    (found : Snapshot.lookupRecorded (transactionId domain ingress) durable.snapshot.model.journal = some recorded)
    (different : recorded.event.event ≠ event domain ingress) :
    replay domain durable ingress = some (.error .transactionConflict) := by
  simp [replay, found, different]

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- Admission and publication share the exact loaded image. In particular a
host-derived logical height cannot be transplanted onto a newer journal after a
CAS race; the caller must reopen, reconstruct and reauthorize after contention. -/
def receiveLoaded (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (durable : Durable) (federation : FederationId) (height : Height)
    (bytes : List UInt8) : IO Result := do
  match decodeIngress bytes with
  | none => return .rejected .malformedIngress
  | some ingress =>
      match replay deployment.domain durable ingress with
      | some (.ok receipt) => return .confirmed .replayed receipt
      | some (.error reason) => return .rejected reason
      | none =>
          match ← admitDecodedNative profile deployment native durable federation height ingress with
          | .error reason => return .rejected reason
          | .ok accepted =>
              match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
              | .confirmed kind _ => return .confirmed kind (receipt deployment.domain ingress)
              | .rejected reason => return .durableRejected reason
              | .contention => return .contention
              | .unavailable detail => return .unavailable detail
              | .uncertain detail => return .uncertain detail

/-- The public boundary accepts only the strict original command and native
signature. Ambient federation and height are service inputs. Historic success
returns the original IDs without reauthorizing, resigning or releasing state.
Publication never silently rebases a checked installation onto a newer image. -/
def receive (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment)
    (native : CredentialSignatureIO.NativeConfig) (transport : DurableReceiverIO.Transport)
    (federation : FederationId) (height : Height) (bytes : List UInt8) : IO Result := do
  match ← DurableReceiverIO.load transport rootBytes with
  | .error detail => return .unavailable detail
  | .ok durable => receiveLoaded profile deployment native transport durable federation height bytes

end Minidregg.Kernel.PolicyInstallReceiver
