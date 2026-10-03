/- Independent current release of an exact governed opaque result. This uses
the native delegation verb and current capability/law, then an event-only CAS
with a physical source guard. It establishes release authority, not plaintext
validity or cryptographic confidentiality. A physical key holder must verify
the actual journal receipt before decoding the exact retained ciphertext. -/
import Kernel.BendOpaqueResultReceiver
import Kernel.FnSelectiveReleaseSourceAuthority
import Kernel.NativeHostContext

namespace Minidregg.Kernel.BendReturnRelease
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

structure Handle where
  resource : Nat
  root : Digest
  result : Digest
  deriving DecidableEq, Repr
structure Destination where
  recipient : SubjectId
  keyEpoch : Digest
  audience : Digest
  generation : Nat
  purpose : String
  deriving DecidableEq, Repr
structure Spec where
  domain : Digest
  semantics : Digest
  subject : SubjectId
  nonce : Nat
  source : Handle
  destination : Destination
  capability : CapabilityId
  deriving DecidableEq, Repr

def handleStream : StreamCodec Handle :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product digestStream digestStream))
    (fun h => (h.resource, h.root, h.result))
    (fun h => ⟨h.1, h.2.1, h.2.2⟩) (by intro h; cases h; rfl)
def destinationStream : StreamCodec Destination :=
  StreamCodec.xmap (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
    (StreamCodec.product digestStream (StreamCodec.product digestStream
    (StreamCodec.product StreamCodec.nat PolicyRecordCodec.stringStream))))
    (fun d => (d.recipient, d.keyEpoch, d.audience, d.generation, d.purpose))
    (fun d => ⟨d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2⟩)
    (by intro d; cases d; rfl)
def specStream : StreamCodec Spec :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
    (StreamCodec.product StreamCodec.nat
    (StreamCodec.product handleStream
    (StreamCodec.product destinationStream CredentialAuthorityEntryCodec.capabilityIdStream))))))
    (fun s => (s.domain, s.semantics, s.subject, s.nonce, s.source, s.destination, s.capability))
    (fun s => ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1,
      s.2.2.2.2.2.1, s.2.2.2.2.2.2⟩) (by intro s; cases s; rfl)
def specCodec : LawfulCodec Spec :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/BEND/RETURN-RELEASE-SPEC/v1".toUTF8.toList specStream)

structure Ingress where
  spec : Spec
  envelope : List UInt8
  deriving DecidableEq, Repr
def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product specStream bytesStream)
    (fun i => (i.spec, i.envelope)) (fun i => ⟨i.1, i.2⟩)
    (by intro i; cases i; rfl)
def ingressCodec : LawfulCodec Ingress :=
  ResourceBirthCodec.strictCodec
    (NativeHostCodec.framed "DREGG/BEND/RETURN-RELEASE-INGRESS/v1".toUTF8.toList ingressStream)
def marker (spec : Spec) : Nat :=
  (Sp800185Cshake256.hash "DREGG.BEND.RETURN-RELEASE-MARKER/v1".toUTF8.toList
    (specCodec.encode spec)).digest.value
def keyBytes (spec : Spec) : List UInt8 :=
  (StreamCodec.product digestStream
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product StreamCodec.nat StreamCodec.nat))).encode
    (spec.domain, spec.subject, spec.source.resource, spec.nonce)
def transactionId (spec : Spec) : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.RETURN-RELEASE-KEY/v1".toUTF8.toList
    (keyBytes spec)).digest
def nullifier (spec : Spec) : StableNullifier :=
  { codecVersion := 15, domain := spec.domain, nullifierId := transactionId spec
    canonicalBytes := keyBytes spec }
def event (ingress : Ingress) : StableEvent :=
  { codecVersion := 15, domain := ingress.spec.domain
    eventId := (Sp800185Cshake256.hash "DREGG.BEND.RETURN-RELEASE-EVENT/v1".toUTF8.toList
      (ingressCodec.encode ingress)).digest
    canonicalBytes := ingressCodec.encode ingress }

def request (federation : FederationId) (authority : AuthState)
    (height : Nat) (spec : Spec) : Request .object :=
  { domain := spec.domain, semantics := spec.semantics, federation := federation
    subject := spec.subject, subjectKeyEpoch := authority.subjectKeyEpoch spec.subject
    target := ⟨spec.source.resource⟩, verb := .delegateObject
    argsDigest := ⟨marker spec⟩, effectsDigest := ⟨marker spec⟩
    nonce := spec.nonce, height := height, preStateRoot := spec.source.root
    policyId := ⟨spec.source.resource⟩
    policyEpoch := authority.policyEpoch ⟨spec.source.resource⟩
    policyRevision := authority.policyRevision ⟨spec.source.resource⟩
    cost := (specCodec.encode spec).length }

def currentResult {deployment : DeclaredResourceController.Deployment}
    {durable : DeclaredResourceController.Durable}
    (context : ResourceObservationAdmission.Context deployment durable)
    (spec : Spec) : Option (Digest × BendInvocation.Result) := do
  let .present packed := context.directory.directory.slots spec.source.resource | none
  match packed with
  | ⟨.content, materialized⟩ => do
      let result ← BendOpaqueResultReceiver.lookup materialized.logical ⟨spec.source.result⟩
      if decide (result.result.recipient = spec.destination.recipient ∧
          result.result.keyEpoch = spec.destination.keyEpoch ∧
          result.result.audience = spec.destination.audience ∧
          result.result.generation = spec.destination.generation) then
        some (materialized.root, result)
      else none
  | _ => none

variable {F : Type} [Field F] [DecidableEq F]
  {deployment : DeclaredResourceController.Deployment}
  {durable : DeclaredResourceController.Durable}

structure Prepared (context : ResourceObservationAdmission.Context deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (spec : Spec) where
  private mk ::
  selected : BendInvocation.Result
  observed : ResourceTargetAdmission.Observed deployment context.directory.directory
    .object spec.source.resource spec.source.root
  current : currentResult context spec = some (spec.source.root, selected)
  physicalCurrent : ResourceBirthCodec.physicalRoot (.live observed.before) =
    durable.snapshot.model.roots ⟨spec.source.resource⟩
  domainExact : spec.domain = deployment.domain
  semanticsExact : spec.semantics = profile.semantics

def prepare (context : ResourceObservationAdmission.Context deployment durable)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (spec : Spec) : Option (Prepared context profile federation height spec) := do
  if !BendWorldSource.nameValid spec.destination.purpose then none else do
    let selectedPair ← currentResult context spec
    if current : currentResult context spec = some (spec.source.root, selectedPair.2) then
      let observed ← ResourceTargetAdmission.observe deployment context.directory.directory
        .object spec.source.resource spec.source.root
      let physicalCurrent := PhysicalResourceReadGuard.current context.directory
        spec.source.resource observed.before observed.present
      if domainExact : spec.domain = deployment.domain then
        if semanticsExact : spec.semantics = profile.semantics then
          some ⟨selectedPair.2, observed, current, physicalCurrent, domainExact, semanticsExact⟩
        else none
      else none
    else none

variable {context : ResourceObservationAdmission.Context deployment durable}
  {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
  {height : Nat} {spec : Spec}

def Prepared.wanted (_prepared : Prepared context profile federation height spec) : Request .object :=
  request federation context.authority.snapshot.authState height spec
def project (prepared : Prepared context profile federation height spec)
    (logical : Store.Store (CanonicalCellRegistry.layout prepared.observed.before.kind)) :
    Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots context.directory.directory spec.source.resource ++
    CanonicalRuntimeProfile.requestSlots prepared.wanted ++
    ResourceAuthorityProjection.bytesSlots "context/bytes" 0 (specCodec.encode spec) ++
    ResourceAuthorityProjection.bytesSlots "resource/bytes" 0
      ((CanonicalCellRegistry.materializer prepared.observed.before.kind).codec.encode logical) ++
    ResourceObservationAdmission.resourceSlots prepared.wanted.subject spec.source.resource
      prepared.observed.before.kind logical⟩
def step (prepared : Prepared context profile federation height spec) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics
    (ResourceObservationAdmission.readCandidate prepared.wanted prepared.observed.before.kind
      prepared.observed.before.payload (by
        simpa [Prepared.wanted, request] using prepared.observed.rootExact))
def kindDependencies (prepared : Prepared context profile federation height spec) :
    Option WorldKindLawDependencies.Dependencies :=
  WorldKindLawDependencies.loadTarget deployment context.directory.directory spec.source.resource
def lawReadGuards (prepared : Prepared context profile federation height spec) :
    Option (List (Nat × Digest)) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards context.authority.snapshot
    context.directory.directory profile.semantics spec.source.resource structural.additional
  pure (sources ++ structural.readGuards)
def policyConfig (prepared : Prepared context profile federation height spec) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile context.authority.snapshot
    context.directory.directory (sourceCapabilityPortal context.authority.snapshot (marker spec))
    (step prepared) spec.source.resource ((kindDependencies prepared).map (·.additional) |>.getD [])
def portal (prepared : Prepared context profile federation height spec) : Portal :=
  (policyConfig prepared).portal
def authorize (prepared : Prepared context profile federation height spec)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot) :
    Option (Authorized (portal prepared) context.authority.snapshot.authState prepared.wanted) := do
  let config := policyConfig prepared
  let _ ← lawReadGuards prepared
  let evidence ← (config.capabilityEvidenceChecked prepared.wanted
    spec.capability () signature () (fun _ => ())).toOption
  let law ← config.resolve?
  ComposedPolicyAdmission.admit config prepared.wanted evidence law.witness
    (.policy prepared.wanted.policyId prepared.wanted.policyRevision) (by rfl) (by rfl)

attribute [irreducible] portal
structure Checked (prepared : Prepared context profile federation height spec)
    (envelope : List UInt8) where
  private mk ::
  signature : CredentialSignatureAdmission.CheckedSignature context.authority.snapshot
  envelopeExact : signature.envelopeBytes = envelope
  authorization : Authorized (portal prepared) context.authority.snapshot.authState prepared.wanted
  authorized : authorize prepared signature = some authorization
def check (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared context profile federation height spec) (envelope : List UInt8) :
    IO (Option (Checked prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native context.authority.snapshot
      (marker spec) prepared.wanted envelope with
  | .error _ => return none
  | .ok signature =>
      if exactEnvelope : signature.envelopeBytes = envelope then
        match authorized : authorize prepared signature with
        | none => return none
        | some authorization => return some ⟨signature, exactEnvelope, authorization, authorized⟩
      else return none

def sourceContext (config : NativeHost.Config) (opened : NativeHost.Opened config) :
    ResourceObservationAdmission.Context config.deployment opened.durable :=
  ⟨opened.directory, opened.authority⟩
structure Accepted (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : Ingress) where
  private mk ::
  prepared : Prepared (sourceContext config opened) config.profile config.federation
    (NativeHost.logicalHeight config opened.durable) ingress.spec
  checked : Checked prepared ingress.envelope

/-- Shared ingress admission for live receiving and original-prefix semantic
history replay. It does not call CAS or a historical-success shortcut. -/
def admitLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : Ingress) : IO (Option (Accepted config opened ingress)) := do
  let context := sourceContext config opened
  let some prepared := prepare context config.profile config.federation
      (NativeHost.logicalHeight config opened.durable) ingress.spec | return none
  let some checked ← check config.signature prepared ingress.envelope | return none
  return some ⟨prepared, checked⟩

def charge (ingress : Ingress) : ResourceCost.Charge
  | .incidences | .memoryTouches | .proofWork | .sideEffectCount => 1
  | .turnBytes | .witnessBytes | .storageBytes => (ingressCodec.encode ingress).length
  | .networkBytes | .feeDebit | .leaseByteBlocks => 0
def Accepted.intent (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : Ingress) (accepted : Accepted config opened ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  { transactionId := transactionId ingress.spec, writes := []
    readGuards :=
      [⟨⟨ingress.spec.source.resource⟩,
        ResourceBirthCodec.physicalRoot (.live accepted.prepared.observed.before)⟩] ++
      ((lawReadGuards accepted.prepared).getD []).map (fun g => ⟨⟨g.1⟩, g.2⟩) ++
      (sourceContext config opened).authority.readGuards
    nullifiers := [nullifier ingress.spec], exactCharge := charge ingress
    event := event ingress, subject := some ingress.spec.subject
    postRootsBound := by intro write member; cases member
    guardsReadOnly := by intro guard _; simp }

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr
def receipt (ingress : Ingress) : Receipt :=
  ⟨transactionId ingress.spec, (event ingress).eventId⟩
def replay {config : NativeHost.Config} (opened : NativeHost.Opened config)
    (ingress : Ingress) : Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded (transactionId ingress.spec)
      opened.durable.snapshot.model.journal with
  | none => none
  | some recorded =>
      if recorded.transactionId = transactionId ingress.spec ∧
          recorded.event.event = event ingress ∧ recorded.nullifiers = [nullifier ingress.spec] then
        some (.ok (receipt ingress))
      else some (.error ())

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | transactionConflict
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)
def receiveLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (bytes : List UInt8) : IO Result := do
  let some ingress := ingressCodec.decode bytes | return .rejected
  match replay opened ingress with
  | some (.ok retained) => return .confirmed .replayed retained
  | some (.error _) => return .transactionConflict
  | none =>
      let some accepted ← admitLoaded config opened ingress | return .rejected
      match ← DurableReceiverIO.receiveLoaded config.transport ResourceBirthCodec.rootBytes
          opened.durable (accepted.intent config opened ingress) with
      | .confirmed kind _ => return .confirmed kind (receipt ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

theorem exact_current_result (prepared : Prepared context profile federation height spec) :
    currentResult context spec = some (spec.source.root, prepared.selected) := prepared.current
theorem source_guard_current (prepared : Prepared context profile federation height spec) :
    ResourceBirthCodec.physicalRoot (.live prepared.observed.before) =
      durable.snapshot.model.roots ⟨spec.source.resource⟩ := prepared.physicalCurrent

end Minidregg.Kernel.BendReturnRelease
