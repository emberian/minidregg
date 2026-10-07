/-
Current-law gateway authorization for a local fn frontier testimony. This
does not decide which article the fn server offered. A Host route must form
the canonical selected or empty spec from an authenticated pinned poll, and
Replay must match the event to an admitted predecessor and release receipt.
-/
import Kernel.FnGatewayPolicy
import Kernel.ResourceObservationAdmission
import Kernel.PhysicalResourceReadGuard

namespace Minidregg.Kernel.FnConsumerFrontierGateway

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

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := ResourceObservationAdmission.Durable
abbrev Context := ResourceObservationAdmission.Context

/-- This source-only request shape is built from a decoded event17 or event19
spec and current witness roots. Its fields are checked against the configured
gateway pin before native signature verification. -/
structure Proposal where
  domain : Digest
  semantics : Digest
  application : List UInt8
  subject : SubjectId
  target : Nat
  capability : CapabilityId
  canonicalSpec : List UInt8
  expectedAuthorityRoot : Digest
  expectedTargetRoot : Digest
  deriving DecidableEq, Repr

def Proposal.matchesPin (proposal : Proposal) (pin : FnGatewayPolicy.Pin) : Bool :=
  proposal.application == pin.application && proposal.subject == pin.subject &&
  proposal.target == pin.target && proposal.capability == pin.capability

def signingBytes (proposal : Proposal) : List UInt8 :=
  (StreamCodec.product bytesStream
    (StreamCodec.product digestStream digestStream)).encode
    (proposal.canonicalSpec, proposal.expectedAuthorityRoot,
      proposal.expectedTargetRoot)

def marker (proposal : Proposal) : Nat :=
  (Sp800185Cshake256.hash
    "DREGG/FN/CONSUMER-FRONTIER-GATEWAY-MARKER/v2".toUTF8.toList
    (signingBytes proposal)).digest.value

def gatewayRequest (federation : FederationId) (authority : AuthState)
    (height : Nat) (proposal : Proposal) : Request .object where
  domain := proposal.domain
  semantics := proposal.semantics
  federation := federation
  subject := proposal.subject
  subjectKeyEpoch := authority.subjectKeyEpoch proposal.subject
  target := ⟨proposal.target⟩
  verb := .mutateObject
  argsDigest := (Sp800185Cshake256.hash
    "DREGG/FN/CONSUMER-FRONTIER-GATEWAY-ARGS/v2".toUTF8.toList
    (signingBytes proposal)).digest
  effectsDigest := (Sp800185Cshake256.hash
    "DREGG/FN/CONSUMER-FRONTIER-GATEWAY-EFFECTS/v2".toUTF8.toList
    (signingBytes proposal)).digest
  nonce := marker proposal
  height := height
  preStateRoot := proposal.expectedTargetRoot
  policyId := ⟨proposal.target⟩
  policyEpoch := authority.policyEpoch ⟨proposal.target⟩
  policyRevision := authority.policyRevision ⟨proposal.target⟩
  cost := (signingBytes proposal).length

theorem gatewayRequest_mutate (federation : FederationId) (authority : AuthState)
    (height : Nat) (proposal : Proposal) :
    (gatewayRequest federation authority height proposal).verb = .mutateObject := rfl

theorem gatewayRequest_subject (federation : FederationId) (authority : AuthState)
    (height : Nat) (proposal : Proposal) :
    (gatewayRequest federation authority height proposal).subject = proposal.subject := rfl

variable {deployment : Deployment} {durable : Durable}
variable {F : Type} [Field F] [DecidableEq F]

structure Prepared (context : Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (pin : FnGatewayPolicy.Pin) (proposal : Proposal) where
  private mk ::
  observed : ResourceTargetAdmission.Observed deployment context.directory
    .object proposal.target proposal.expectedTargetRoot
  contentKind : observed.before.kind = .content
  physicalCurrent : ResourceBirthCodec.physicalRoot (.live observed.before) =
    durable.snapshot.model.roots ⟨proposal.target⟩
  domainExact : proposal.domain = deployment.domain
  semanticsExact : proposal.semantics = profile.semantics
  pinExact : proposal.matchesPin pin = true

def prepare (context : Context deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (federation : FederationId)
    (height : Nat) (pin : FnGatewayPolicy.Pin) (proposal : Proposal) :
    Except String (Prepared context profile federation height pin proposal) :=
  if proposal.canonicalSpec.isEmpty || proposal.canonicalSpec.length > 8192 then
    .error "fn consumer gateway testimony refused"
  else match context.directory.slots proposal.target with
  | .absent => .error "fn consumer gateway testimony refused"
  | .present _ =>
      match ResourceTargetAdmission.observe deployment context.directory
          .object proposal.target proposal.expectedTargetRoot with
      | none => .error "fn consumer gateway testimony refused"
      | some observed =>
          if contentKind : observed.before.kind = .content then
            let physicalCurrent := PhysicalResourceReadGuard.current context.directory
              proposal.target observed.before observed.present
            if domainExact : proposal.domain = deployment.domain then
              if semanticsExact : proposal.semantics = profile.semantics then
                if pinExact : proposal.matchesPin pin = true then
                  .ok ⟨observed, contentKind, physicalCurrent, domainExact,
                    semanticsExact, pinExact⟩
                else .error "fn consumer gateway testimony refused"
              else .error "fn consumer gateway testimony refused"
            else .error "fn consumer gateway testimony refused"
          else .error "fn consumer gateway testimony refused"

variable {context : Context deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {federation : FederationId}
  {height : Nat} {pin : FnGatewayPolicy.Pin} {proposal : Proposal}

def Prepared.wanted (_prepared : Prepared context profile federation height pin proposal) :
    Request .object :=
  gatewayRequest federation context.authority.authState height proposal

def project (prepared : Prepared context profile federation height pin proposal)
    (logical : Store.Store (CanonicalCellRegistry.layout prepared.observed.before.kind)) :
    Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots context.directory proposal.target ++
    CanonicalRuntimeProfile.requestSlots prepared.wanted ++
    ResourceAuthorityProjection.bytesSlots "context/bytes" 0 (signingBytes proposal) ++
    ResourceAuthorityProjection.bytesSlots "resource/bytes" 0
      ((CanonicalCellRegistry.materializer prepared.observed.before.kind).codec.encode logical) ++
    ResourceObservationAdmission.resourceSlots prepared.wanted.subject proposal.target
      prepared.observed.before.kind logical⟩

def step (prepared : Prepared context profile federation height pin proposal) :
    PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics
    (ResourceObservationAdmission.readCandidate prepared.wanted
      prepared.observed.before.kind prepared.observed.before.payload
      prepared.observed.rootExact)

def kindDependencies (prepared : Prepared context profile federation height pin proposal) :
    Option WorldKindLawDependencies.Dependencies :=
  WorldKindLawDependencies.loadTarget deployment context.directory proposal.target

def lawReadGuards (prepared : Prepared context profile federation height pin proposal) :
    Option (List (Nat × Digest)) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards context.authority
    context.directory profile.semantics proposal.target structural.additional
  pure (sources ++ structural.readGuards)

def policyConfig (prepared : Prepared context profile federation height pin proposal) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile context.authority
    context.directory (sourceCapabilityPortal context.authority (marker proposal))
    (step prepared) proposal.target
    ((kindDependencies prepared).map (·.additional) |>.getD [])

def portal (prepared : Prepared context profile federation height pin proposal) : Portal :=
  (policyConfig prepared).portal

def authorize (prepared : Prepared context profile federation height pin proposal)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority) :
    Option (Authorized (portal prepared) context.authority.authState
      prepared.wanted) := do
  let config := policyConfig prepared
  let _ ← lawReadGuards prepared
  let evidence ← (config.capabilityEvidenceChecked prepared.wanted
    proposal.capability () signature () (fun _ => ())).toOption
  let law ← config.resolve?
  ComposedPolicyAdmission.admit config prepared.wanted evidence law.witness
    (.policy prepared.wanted.policyId prepared.wanted.policyRevision)
    (by rfl) (by rfl)

/-- A public success cannot be obtained with missing source custody. -/
theorem authorize_requires_sources (prepared : Prepared context profile federation height pin proposal)
    (signature : CredentialSignatureAdmission.CheckedSignature context.authority)
    (accepted : (authorize prepared signature).isSome = true) :
    (lawReadGuards prepared).isSome = true := by
  cases resolved : lawReadGuards prepared with
  | none => simp [authorize, resolved] at accepted
  | some guards => simp [resolved]

attribute [irreducible] portal

structure Checked (prepared : Prepared context profile federation height pin proposal)
    (envelope : List UInt8) where
  private mk ::
  signature : CredentialSignatureAdmission.CheckedSignature context.authority
  envelopeExact : signature.envelopeBytes = envelope
  authorization : Authorized (portal prepared) context.authority.authState
    prepared.wanted
  authorized : authorize prepared signature = some authorization

def check (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared context profile federation height pin proposal)
    (envelope : List UInt8) : IO (Except String (Checked prepared envelope)) := do
  match ← CredentialSignatureAdmission.verifyNative native context.authority
      (marker proposal) prepared.wanted envelope with
  | .error _ => return .error "fn consumer gateway testimony refused"
  | .ok signature =>
      if exact : signature.envelopeBytes = envelope then
        match authorized : authorize prepared signature with
        | none => return .error "fn consumer gateway testimony refused"
        | some authorization => return .ok ⟨signature, exact, authorization, authorized⟩
      else return .error "fn consumer gateway testimony refused"

/-- Complete source and structural custody. Authorization requires this exact
resolver result to exist before a Checked value can be constructed. -/
def readGuards (prepared : Prepared context profile federation height pin proposal) :
    List DurableDataIntent.ReadGuard :=
  ((lawReadGuards prepared).getD []).map fun guard => ⟨⟨guard.1⟩, guard.2⟩

def readGuard (prepared : Prepared context profile federation height pin proposal) :
    DurableDataIntent.ReadGuard :=
  ⟨⟨proposal.target⟩,
    ResourceBirthCodec.physicalRoot (.live prepared.observed.before)⟩

omit [DecidableEq F] in
theorem readGuard_current
    (prepared : Prepared context profile federation height pin proposal) :
    (readGuard prepared).expectedRoot =
      durable.snapshot.model.roots (readGuard prepared).cellId :=
  prepared.physicalCurrent

/-- Shared lower current-law check used by historical Replay and live verified
admission. It has no durable intent and no caller-supplied frontier authority. -/
def contextOf {config : NativeHost.Config} (opened : NativeHost.Opened config) :
    Context config.deployment :=
  (Minidregg.Compiler.ServedBasis.Ground.full _ opened.directory opened.authority)

structure CheckedOpened (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (proposal : Proposal)
    (envelope : List UInt8) where
  private mk ::
  pin : NativeHost.FnGatewayPin
  pinExact : config.fnGateway = some pin
  current : FnGatewayPolicy.checkCurrent config opened pin = .ok ()
  prepared : Prepared (contextOf opened) config.profile config.federation
    (NativeHost.logicalHeight config opened.durable) pin proposal
  signature : Checked prepared envelope

def checkOpened (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (proposal : Proposal) (envelope : List UInt8) :
    IO (Except String (CheckedOpened config opened proposal envelope)) := do
  unless proposal.domain == config.deployment.domain &&
      proposal.semantics == config.profile.semantics &&
      envelope.length ≤ 4096 &&
      proposal.expectedAuthorityRoot ==
        opened.durable.snapshot.model.roots
          (CredentialAuthorityDomainReceiver.cellIdOf config.deployment) do
    return .error "fn consumer gateway testimony refused"
  let some pin := config.fnGateway
    | return .error "fn consumer gateway testimony refused"
  if pinExact : config.fnGateway = some pin then
    if current : FnGatewayPolicy.checkCurrent config opened pin = .ok () then
      match prepare (contextOf opened) config.profile config.federation
          (NativeHost.logicalHeight config opened.durable) pin proposal with
      | .error _ => return .error "fn consumer gateway testimony refused"
      | .ok prepared =>
          match ← check config.signature prepared envelope with
          | .error _ => return .error "fn consumer gateway testimony refused"
          | .ok signature => return .ok ⟨pin, pinExact, current, prepared, signature⟩
    else return .error "fn consumer gateway testimony refused"
  else return .error "fn consumer gateway testimony refused"

end Minidregg.Kernel.FnConsumerFrontierGateway
