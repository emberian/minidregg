/- Source-current private-party authority. Canonical packet parsing does not
create authority. The only Checked producer verifies the deployment-pinned
native credential and the selected manifest resource's complete current law.
This module does not dispatch a worker or claim physical/qualified custody. -/
import Compiler.JointBackendPartyCodec
import Kernel.NativeHostContext
import Kernel.JointReserveIngress
import Kernel.ResourceObservationAdmission
import Kernel.PhysicalResourceReadGuard
namespace Minidregg.Kernel.JointBackendPartyAdmission
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.JointBackendPartyCodec
open Minidregg.Compiler.PrivateSuccessorCustodyCodec
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost
set_option autoImplicit false


variable {config : Config} {opened : Opened config}
def sourceContext (opened : Opened config) :
    ResourceObservationAdmission.Context config.deployment opened.durable :=
  ⟨opened.directory,opened.authority⟩

def selectedManifest (pin : EndpointPin) (opened : Opened config) : Option (List Enrollment) := do
  let payload ← ContentControlFrame.readPayload pin.manifest
    (opened.durable.snapshot.canonicalBytes pin.manifest.cell)
  let entries ← manifestStream.toLawful.decode payload
  if manifestStream.encode entries != payload then none else some entries

/-- Credential randomness is excluded from semantic dispatch identity. Exact
candidate, manifest root, participant, Generation and signed backend preimage
remain present. A newly randomized valid credential replays the same work. -/
def semanticBytes (pin : EndpointPin) (request : JointBackendPartyCodec.Request)
    (row : Enrollment) (packet : PacketClaim) : List UInt8 :=
  "DREGG.JOINT.PRIVATE.SOURCE.DISPATCH".toUTF8.toList ++ [1] ++
  endpointPinStream.encode pin ++
  enrollmentStream.encode row ++ bytesStream.encode request.candidateBytes ++
  StreamCodec.nat.encode request.participant ++ bytesStream.encode request.fullGenerationBytes ++
  digestStream.encode request.manifestRoot ++ bytesStream.encode packet.signingBytes

def marker (pin : EndpointPin) (request : JointBackendPartyCodec.Request)
    (row : Enrollment) (packet : PacketClaim) : Nat :=
  (Sp800185Cshake256.hash "DREGG.JOINT.PRIVATE.MARKER".toUTF8.toList
    (semanticBytes pin request row packet)).digest.value

def wanted (config : Config) (opened : Opened config) (pin : EndpointPin)
    (request : JointBackendPartyCodec.Request) (row : Enrollment) (packet : PacketClaim) :
    Request .object where
  domain := config.deployment.domain
  semantics := config.profile.semantics
  federation := config.federation
  subject := row.party.subject
  subjectKeyEpoch := opened.authority.snapshot.authState.subjectKeyEpoch row.party.subject
  target := ⟨pin.manifest.cell.value⟩
  verb := .delegateObject
  argsDigest := (Sp800185Cshake256.hash "DREGG.JOINT.PRIVATE.ARGS".toUTF8.toList
    (semanticBytes pin request row packet)).digest
  effectsDigest := (Sp800185Cshake256.hash "DREGG.JOINT.PRIVATE.EFFECTS".toUTF8.toList
    (semanticBytes pin request row packet)).digest
  nonce := marker pin request row packet
  height := logicalHeight config opened.durable
  preStateRoot := request.manifestRoot
  policyId := ⟨pin.manifest.cell.value⟩
  policyEpoch := opened.authority.snapshot.authState.policyEpoch ⟨pin.manifest.cell.value⟩
  policyRevision := opened.authority.snapshot.authState.policyRevision ⟨pin.manifest.cell.value⟩
  cost := (semanticBytes pin request row packet).length + pin.dispatchCapacity .feeDebit

/-- Exact candidate/slot/descriptor reconstruction; merely naming a held
Generation cannot authorize a different command, attempt or successor. -/
def matchesPending (config : Config) (request : JointBackendPartyCodec.Request)
    (row : Enrollment) (held : JointReservation.Reservation) : Bool := Id.run do
  let some plan := JointReserveIngress.decodePlan request.candidateBytes | return false
  if index : request.participant < plan.candidate.participants.length then
    let projection := plan.candidate.participants[request.participant]
    return JointReserveIngress.descriptorMatches plan.candidate projection &&
      decide (projection.domain = config.deployment.domain) &&
      decide (row.party.authorityEpoch = projection.epoch) &&
      decide ((config.jointConsensus.map (·.epoch)) = some projection.epoch) &&
      decide (descriptorStream.encode projection.custody = row.descriptorBytes) &&
      decide (generationStream.encode projection.custody.key = request.fullGenerationBytes) &&
      decide (row.party.generation = projection.custody.key) &&
      decide (held.domain = projection.domain) && decide (held.candidateBytes = request.candidateBytes) &&
      decide (held.lineage = plan.candidate.lineage) && decide (held.generation = projection.generation) &&
      decide (held.intent.transactionId = projection.intent.transactionId) &&
      decide (held.intent.writes = projection.intent.writes) &&
      decide (held.intent.nullifiers = projection.intent.nullifiers) &&
      decide (held.intent.event = projection.intent.event) &&
      decide (held.intent.exactCharge = projection.intent.exactCharge)
  else return false

structure Prepared (config : Config) (opened : Opened config) (pin : EndpointPin)
    (request : JointBackendPartyCodec.Request) where
  private mk ::
  endpointExact : config.privatePartyEndpoint.map endpointPinStream.encode = some (endpointPinStream.encode pin)
  row : Enrollment
  packet : PacketClaim
  packetExact : decodeCarrier request.rawCarrier = some packet
  manifest : List Enrollment
  manifestExact : selectedManifest pin opened = some manifest
  rowExact : row ∈ manifest
  recordExact : packet.recordBytes = partyWire row.party
  routeExact : row.party.protocol = pin.protocol ∧ row.party.recipient = pin.recipient ∧
    row.party.recipientRole = pin.recipientRole
  identityExact : row.candidateBytes = request.candidateBytes ∧ row.participant = request.participant
  bounded : row.party.bounded = true
  controlPin : JointControlFrame.Pin
  configuredControl : config.jointControl = some controlPin
  control : JointControlCell.Control
  controlExact : JointControlFrame.readControl controlPin
    (opened.durable.snapshot.canonicalBytes controlPin.cell) = some control
  held : JointReservation.Reservation
  heldExact : held ∈ control.reservations
  pendingExact : matchesPending config request row held = true
  key : KeyRecord
  keyCurrent : CredentialAuthorityState.currentSigningKey opened.authority.snapshot.logical row.party.subject = some key
  keyExact : key.keyEpoch = row.party.keyEpoch ∧ key.publicKey = row.party.keyBinding
  observed : ResourceTargetAdmission.Observed config.deployment opened.directory.directory .object
    pin.manifest.cell.value request.manifestRoot
  clock : ClockCellDomain.Loaded config.deployment opened.durable.snapshot
  clockExact : ClockCellDomain.load config.deployment opened.durable.snapshot = some clock
  dependencies : WorldKindLawDependencies.Dependencies
  dependenciesExact : WorldKindLawDependencies.loadTarget config.deployment opened.directory.directory
    pin.manifest.cell.value = some dependencies

/-- Current source is read once. A manifest row is neither a grant nor an
installation promise; the independent native request below still must pass
capability revocation, current-key and complete predicate admission. -/
def prepare (config : Config) (opened : Opened config) (pin : EndpointPin)
    (request : JointBackendPartyCodec.Request) : Except String (Prepared config opened pin request) :=
  if configured : config.privatePartyEndpoint.map endpointPinStream.encode = some (endpointPinStream.encode pin) then
    match packetExact : decodeCarrier request.rawCarrier with
    | none => .error "invalid private carrier"
    | some packet =>
    match manifestExact : selectedManifest pin opened with
    | none => .error "no current enrolled manifest"
    | some entries =>
    match entries.find? (fun row => partyWire row.party == packet.recordBytes) with
    | none => .error "party is not currently enrolled"
    | some row =>
    if rowMember : row ∈ entries then
      if recordExact : packet.recordBytes = partyWire row.party then
        if routeExact : row.party.protocol = pin.protocol ∧ row.party.recipient = pin.recipient ∧
            row.party.recipientRole = pin.recipientRole then
          if identityExact : row.candidateBytes = request.candidateBytes ∧ row.participant = request.participant then
            if bounded : row.party.bounded = true then
              match configuredControl : config.jointControl with
              | none => .error "joint control disabled"
              | some cp =>
              match controlExact : JointControlFrame.readControl cp
                  (opened.durable.snapshot.canonicalBytes cp.cell) with
              | none => .error "no current joint control"
              | some control =>
              match foundHeld : control.reservations.find? (matchesPending config request row) with
              | none => .error "exact source PENDING reservation missing"
              | some held =>
                if pending : matchesPending config request row held = true then
                  match keyCurrent : CredentialAuthorityState.currentSigningKey
                      opened.authority.snapshot.logical row.party.subject with
                  | none => .error "no current party key"
                  | some key =>
                  if keyExact : key.keyEpoch = row.party.keyEpoch ∧ key.publicKey = row.party.keyBinding then
                    match ResourceTargetAdmission.observe config.deployment opened.directory.directory
                        .object pin.manifest.cell.value request.manifestRoot with
                    | none => .error "stale manifest root"
                    | some observed =>
                    match clockExact : ClockCellDomain.load config.deployment opened.durable.snapshot with
                    | none => .error "clock unavailable"
                    | some clock =>
                    match dependenciesExact : WorldKindLawDependencies.loadTarget config.deployment
                        opened.directory.directory pin.manifest.cell.value with
                    | none => .error "complete law dependencies unavailable"
                    | some deps => .ok ⟨configured,row,packet,packetExact,entries,manifestExact,rowMember,recordExact,
                      routeExact,identityExact,bounded,cp,configuredControl,control,controlExact,
                      held,List.mem_of_find?_eq_some foundHeld,pending,key,keyCurrent,keyExact,observed,clock,clockExact,deps,dependenciesExact⟩
                  else .error "enrolled key moved"
                else .error "reservation identity changed"
            else .error "unbounded party context"
          else .error "wrong candidate or participant"
        else .error "wrong designated worker route"
      else .error "noncanonical party record"
    else .error "manifest selection failed"
  else .error "private-party endpoint is not source configured"

variable {pin : EndpointPin} {request : JointBackendPartyCodec.Request}
def Prepared.wanted (p : Prepared config opened pin request) : Request .object :=
  wanted config opened pin request p.row p.packet

def project (p : Prepared config opened pin request)
    (logical : Store.Store (CanonicalCellRegistry.layout p.observed.before.kind)) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots opened.directory.directory pin.manifest.cell.value ++
    (ResourceObservationAdmission.projectWith p.clock.clock p.wanted
      (semanticBytes pin request p.row p.packet) p.observed.before.kind [] logical ).slots⟩

def step (p : Prepared config opened pin request) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project p) config.profile.semantics
    (ResourceObservationAdmission.readCandidate p.wanted p.observed.before.kind
      p.observed.before.payload (by simpa [Prepared.wanted,wanted] using p.observed.rootExact))

def policyConfig (p : Prepared config opened pin request) :
    ComposedPolicyAdmission.Config NativeHostProfile.Field :=
  PhysicalLawResolution.config config.profile.compilerProfile opened.authority.snapshot
    opened.directory.directory (sourceCapabilityPortal opened.authority.snapshot
      (marker pin request p.row p.packet)) (step p) pin.manifest.cell.value p.dependencies.additional

def portal (p : Prepared config opened pin request) : Portal := (policyConfig p).portal

def lawReadGuards (p : Prepared config opened pin request) : Option (List (Nat × Digest)) :=
  (PhysicalLawResolution.readGuards opened.authority.snapshot opened.directory.directory
    config.profile.semantics pin.manifest.cell.value p.dependencies.additional).map
      (· ++ p.dependencies.readGuards)

def authorize (p : Prepared config opened pin request)
    (signature : CredentialSignatureAdmission.CheckedSignature opened.authority.snapshot) :
    Option (Authorized (portal p) opened.authority.snapshot.authState p.wanted) := do
  let _ ← lawReadGuards p
  let c := policyConfig p
  let evidence ← (c.capabilityEvidenceChecked p.wanted p.row.delegateCapability () signature () (fun _ => ())).toOption
  let law ← c.resolve?
  ComposedPolicyAdmission.admit c p.wanted evidence law.witness
    (.policy p.wanted.policyId p.wanted.policyRevision) (by rfl) (by rfl)

attribute [irreducible] portal
structure Checked (p : Prepared config opened pin request) where
  private mk ::
  signature : CredentialSignatureAdmission.CheckedSignature opened.authority.snapshot
  envelopeExact : signature.envelopeBytes = p.packet.credential
  authorization : Authorized (portal p) opened.authority.snapshot.authState p.wanted
  authorized : authorize p signature = some authorization

/-- The only authority producer uses config.signature; neither packets nor
worker requests supply a verifier implementation or a positive-result bit. -/
def check (p : Prepared config opened pin request) : IO (Except String (Checked p)) := do
  match ← CredentialSignatureAdmission.verifyNative config.signature opened.authority.snapshot
      (marker pin request p.row p.packet) p.wanted p.packet.credential with
  | .error _ => return .error "native party credential refused"
  | .ok signature =>
    if exact : signature.envelopeBytes = p.packet.credential then
      match accepted : authorize p signature with
      | none => return .error "current party capability or law refused"
      | some permission => return .ok ⟨signature,exact,permission,accepted⟩
    else return .error "native envelope binding refused"

/-- Every source dispatch must carry all these retained dependencies into the
one actual source record; this list includes clock, authority, control, manifest
and complete structural/negative-predicate law sources. -/
def readGuards (p : Prepared config opened pin request) : List ReadGuard :=
  [opened.authority.readGuard,p.clock.readGuard,
   ⟨pin.manifest.cell,opened.durable.snapshot.model.roots pin.manifest.cell⟩,
   ⟨p.controlPin.cell,opened.durable.snapshot.model.roots p.controlPin.cell⟩] ++
  ((lawReadGuards p).getD []).map (fun pair => ⟨⟨pair.1⟩,pair.2⟩)

theorem checked_requires_complete_sources (p : Prepared config opened pin request)
    (checked : Checked p) : (lawReadGuards p).isSome = true := by
  cases found : lawReadGuards p with
  | none => simp [authorize,found] at checked.authorized
  | some guards => simp [found]
#assert_axioms checked_requires_complete_sources
end Minidregg.Kernel.JointBackendPartyAdmission
