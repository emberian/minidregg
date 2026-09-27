/-
Source-owned issuance request for the distinct event27 lifetime grant. The
ordinary birth leg creates a content resource; only the later special
receiver may join that exact birth with current app delegation and install
the first canonical grant atom in one durable transaction. This source alone
neither admits a grant nor extends event21's generation-bound ticket.
-/
import Kernel.ApplicationAgentLifetimeGrant
import Kernel.ApplicationShareIssueSource

namespace Minidregg.Kernel.ApplicationAgentLifetimeGrantSource

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.HyperdocumentContentPageMaterializer
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Pred

set_option autoImplicit false

/-- The current app delegate must sign the source-derived descriptor for the
one grant resource. Owner/control selectors do not grant app authority. -/
structure Spec where
  grant : ApplicationAgentLifetimeGrant.Grant
  grantOwnerCapability : CapabilityId
  grantControlCapability : CapabilityId
  deriving DecidableEq

def Spec.valid (spec : Spec) : Prop :=
  spec.grant.source.resource ≠ spec.grant.source.ticketResource ∧
  spec.grant.source.resource ≠ spec.grant.participant.app ∧
  spec.grant.source.resource ≠ spec.grant.participant.session ∧
  spec.grant.source.resource ≠ spec.grant.participant.parentTask ∧
  spec.grant.participant.originalGeneration ≥ 0 ∧
  spec.grant.source.issueReceipt.acceptedCount > 0 ∧
  spec.grantOwnerCapability ≠ spec.grantControlCapability ∧
  spec.grantOwnerCapability ≠ spec.grant.approval.delegateCapability ∧
  spec.grantControlCapability ≠ spec.grant.approval.delegateCapability ∧
  spec.grant.approval.ceiling.valid = true

instance (spec : Spec) : Decidable spec.valid := by
  unfold Spec.valid
  infer_instance

def specStream : StreamCodec Spec :=
  StreamCodec.xmap
    (StreamCodec.product ApplicationAgentLifetimeGrant.grantStream
      (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
        CredentialAuthorityEntryCodec.capabilityIdStream))
    (fun spec => (spec.grant, spec.grantOwnerCapability,
      spec.grantControlCapability))
    (fun (grant, grantOwnerCapability, grantControlCapability) =>
      ⟨grant, grantOwnerCapability, grantControlCapability⟩)
    (by intro spec; cases spec; rfl)

def specCodec : LawfulCodec Spec := ResourceBirthCodec.strictCodec
  (NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-LIFETIME-ISSUE-SPEC/v1".toUTF8.toList specStream)

theorem spec_decode_encode (spec : Spec) :
    specCodec.decode (specCodec.encode spec) = some spec :=
  specCodec.decode_encode spec

structure Ingress where
  spec : Spec
  birthIngress : List UInt8
  appEnvelope : List UInt8
  deriving DecidableEq

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product specStream
      (StreamCodec.product bytesStream bytesStream))
    (fun ingress => (ingress.spec, ingress.birthIngress, ingress.appEnvelope))
    (fun (spec, birthIngress, appEnvelope) =>
      ⟨spec, birthIngress, appEnvelope⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress := ResourceBirthCodec.strictCodec
  (NativeHostCodec.framed
    "DREGG/APPLICATION/AGENT-LIFETIME-ISSUE-INGRESS/v1".toUTF8.toList
    ingressStream)

def Ingress.canonicalBytes (ingress : Ingress) : List UInt8 :=
  ingressCodec.encode ingress

theorem ingress_decode_encode (ingress : Ingress) :
    ingressCodec.decode ingress.canonicalBytes = some ingress :=
  ingressCodec.decode_encode ingress

theorem ingress_bytes_injective : Function.Injective Ingress.canonicalBytes := by
  intro left right same
  have decoded := congrArg ingressCodec.decode same
  exact Option.some.inj (by simpa only [ingress_decode_encode] using decoded)

/-- Event27 is distinct from event21 dispatch and event22 share issue. A
decoded ingress is still only bytes until native issue admission succeeds. -/
def event (domain : Digest) (ingress : Ingress) : StableEvent where
  codecVersion := 27
  domain := domain
  eventId := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-LIFETIME-ISSUE-EVENT/v1".toUTF8.toList
    ingress.canonicalBytes).digest
  canonicalBytes := ingress.canonicalBytes

theorem event_retains_ingress (domain : Digest) (ingress : Ingress) :
    (event domain ingress).canonicalBytes = ingress.canonicalBytes := rfl

/-- The app request signs both the complete canonical grant and the ordinary
birth descriptor, so a grant payload cannot be spliced into another birth. -/
def sourceBytes (spec : Spec)
    (descriptor : Descriptor CanonicalCellRegistry.registry) : List UInt8 :=
  "DREGG/APPLICATION/AGENT-LIFETIME-ISSUE-SOURCE/v1".toUTF8.toList ++
    (StreamCodec.product bytesStream bytesStream).encode
      (specCodec.encode spec,
        (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode descriptor)

def issueMarker (spec : Spec)
    (descriptor : Descriptor CanonicalCellRegistry.registry) : Nat :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-LIFETIME-ISSUE-MARKER/v1".toUTF8.toList
    (sourceBytes spec descriptor)).digest.value

def appRequest (domain semantics : Digest) (federation : FederationId)
    (authority : AuthState) (height : Nat) (appRoot : Digest)
    (spec : Spec) (descriptor : Descriptor CanonicalCellRegistry.registry) :
    Request .object where
  domain := domain
  semantics := semantics
  federation := federation
  subject := spec.grant.approval.issuer
  subjectKeyEpoch := authority.subjectKeyEpoch spec.grant.approval.issuer
  target := ⟨spec.grant.participant.app⟩
  verb := .delegateObject
  argsDigest := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-LIFETIME-ISSUE-ARGS/v1".toUTF8.toList
    (sourceBytes spec descriptor)).digest
  effectsDigest := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/AGENT-LIFETIME-ISSUE-EFFECTS/v1".toUTF8.toList
    (sourceBytes spec descriptor)).digest
  nonce := spec.grant.approval.nonce
  height := height
  preStateRoot := appRoot
  policyId := ⟨spec.grant.participant.app⟩
  policyEpoch := authority.policyEpoch ⟨spec.grant.participant.app⟩
  policyRevision := authority.policyRevision ⟨spec.grant.participant.app⟩
  cost := (sourceBytes spec descriptor).length

theorem appRequest_exact_target (domain semantics : Digest)
    (federation : FederationId) (authority : AuthState) (height : Nat)
    (appRoot : Digest) (spec : Spec)
    (descriptor : Descriptor CanonicalCellRegistry.registry) :
    (appRequest domain semantics federation authority height appRoot
      spec descriptor).target.value = spec.grant.participant.app := rfl

theorem appRequest_delegate (domain semantics : Digest)
    (federation : FederationId) (authority : AuthState) (height : Nat)
    (appRoot : Digest) (spec : Spec)
    (descriptor : Descriptor CanonicalCellRegistry.registry) :
    (appRequest domain semantics federation authority height appRoot
      spec descriptor).verb = .delegateObject := rfl

/-- The special event27 finalizes this one atom in the same physical write
as an otherwise ordinary empty content-resource birth. The issuer's content
capability alone cannot authorize lifetime app delegation. -/
def grantPage (domain : Digest) (spec : Spec) (operation : Nat) :
    Except String HyperdocumentContentPageMaterializer.Page := do
  match ContentResource.step
      ⟨spec.grant.approval.issuer, .object, spec.grantOwnerCapability⟩
      ⟨⟨operation⟩⟩
      (ContentResource.initialPage domain spec.grant.source.resource)
      (ApplicationAgentLifetimeGrant.initialAction domain spec.grant) with
  | .ok page => pure page
  | .error _ => throw "lifetime grant initial atom refused"

private def bornCell (page : HyperdocumentContentPageMaterializer.Page) :
    PackedCell CanonicalCellRegistry.registry :=
  ⟨.content, materialize HyperdocumentContentPageMaterializer.materializer
    (HyperdocumentContentPageMaterializer.stateOfOption (some page))⟩

structure Ready (domain : Digest) (spec : Spec) (operation : Nat) where
  private mk ::
  valid : spec.valid
  page : HyperdocumentContentPageMaterializer.Page
  pageExact : grantPage domain spec operation = .ok page
  payloadAtLeast :
    (PackedCell.bytes CanonicalCellRegistry.registry
      (bornCell (ContentResource.initialPage domain spec.grant.source.resource))).length ≤
    (PackedCell.bytes CanonicalCellRegistry.registry (bornCell page)).length

def prepare {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) (spec : Spec) :
    Except String (Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.grant.approval.issuer spec.grant.approval.nonce).value) := do
  let operation := (ResourceBirthController.Concrete.sourceIdentity
    profile.compilerProfile config.deployment spec.grant.approval.issuer
    spec.grant.approval.nonce).value
  if valid : spec.valid then
    match exact : grantPage config.deployment.domain spec operation with
    | .error detail => .error detail
    | .ok page =>
      if size : (PackedCell.bytes CanonicalCellRegistry.registry
          (bornCell (ContentResource.initialPage config.deployment.domain
            spec.grant.source.resource))).length ≤
          (PackedCell.bytes CanonicalCellRegistry.registry (bornCell page)).length then
        .ok ⟨valid, page, exact, size⟩
      else .error "lifetime grant final payload shorter than empty birth"
  else .error "lifetime grant issuance selectors invalid"

variable {domain : Digest} {spec : Spec} {operation : Nat}

def Ready.birth (_ready : Ready domain spec operation) :
    BirthItem CanonicalCellRegistry.registry :=
  ⟨⟨spec.grant.source.resource, CellSlot.root CanonicalCellRegistry.registry .absent,
      bornCell (ContentResource.initialPage domain spec.grant.source.resource)⟩,
    .object, spec.grant.approval.issuer⟩

def Ready.initializedCell (ready : Ready domain spec operation) :
    PackedCell CanonicalCellRegistry.registry := bornCell ready.page

def Ready.emptyPayloadBytes (ready : Ready domain spec operation) : Nat :=
  (PackedCell.bytes CanonicalCellRegistry.registry ready.birth.create.cell).length

def Ready.finalPayloadBytes (ready : Ready domain spec operation) : Nat :=
  (PackedCell.bytes CanonicalCellRegistry.registry ready.initializedCell).length

theorem Ready.empty_le_final (ready : Ready domain spec operation) :
    ready.emptyPayloadBytes ≤ ready.finalPayloadBytes := ready.payloadAtLeast

def Ready.effectiveTariff (ready : Ready domain spec operation)
    (tariff : CreationTariff) : CreationTariff :=
  { tariff with base := tariff.base + tariff.perInitialPayloadByte *
      (ready.finalPayloadBytes - ready.emptyPayloadBytes) }

theorem Ready.effective_payload_quote (ready : Ready domain spec operation)
    (tariff : CreationTariff) :
    (ready.effectiveTariff tariff).base +
      tariff.perInitialPayloadByte * ready.emptyPayloadBytes =
      tariff.base + tariff.perInitialPayloadByte * ready.finalPayloadBytes := by
  simp only [Ready.effectiveTariff]
  rw [Nat.add_assoc, ← Nat.mul_add]
  rw [Nat.sub_add_cancel ready.empty_le_final]

def Ready.effectivePins (ready : Ready domain spec operation)
    (pins : FactoryPins) : FactoryPins :=
  { pins with tariff := ready.effectiveTariff pins.tariff }

def Ready.births (ready : Ready domain spec operation) :
    List (BirthItem CanonicalCellRegistry.registry) := [ready.birth]

theorem Ready.one_birth (ready : Ready domain spec operation) :
    ready.births.length = 1 := rfl

private def rootCapability {F : Type} [Field F] (kind : ResourceKind)
    (profile : CanonicalRuntimeProfile.Profile F) (authority : AuthState)
    (height : Nat) (identifier : CapabilityId) (subject : SubjectId)
    (target : Nat) (verbs : Finset (Verb kind)) : Capability kind where
  id := identifier
  root := identifier
  parent := none
  issuer := profile.template.issuer
  holder := .subject subject
  scope := ⟨{⟨target⟩}, verbs, profile.template.ownerBudget⟩
  notBefore := height
  notAfter := height + profile.template.lifetime
  issuerEpoch := authority.issuerEpoch profile.template.issuer
  policyId := ⟨target⟩
  policyEpoch := authority.policyEpoch ⟨target⟩
  ancestors := ∅
  channels := ∅

private def ownerGrant {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (authority : AuthState)
    (height : Nat) (spec : Spec) : AuthorityGrant :=
  ⟨.object, ⟨rootCapability .object profile authority height
      spec.grantOwnerCapability spec.grant.approval.issuer spec.grant.source.resource
      (ResourceBirthPolicyController.Concrete.ownerVerbs .object), []⟩⟩

private def controlGrant {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (authority : AuthState)
    (height : Nat) (spec : Spec) : AuthorityGrant :=
  ⟨.program, ⟨rootCapability .program profile authority height
      spec.grantControlCapability spec.grant.approval.issuer spec.grant.source.resource
      {.installPolicy, .revokeCapability}, []⟩⟩

def Ready.grants {F : Type} [Field F]
    (_ready : Ready domain spec operation) (profile : CanonicalRuntimeProfile.Profile F)
    (authority : AuthState) (height : Nat) : List AuthorityGrant :=
  [ownerGrant profile authority height spec, controlGrant profile authority height spec]

theorem Ready.two_grants {F : Type} [Field F]
    (ready : Ready domain spec operation) (profile : CanonicalRuntimeProfile.Profile F)
    (authority : AuthState) (height : Nat) :
    (ready.grants profile authority height).length = 2 := rfl

/-- The initial policy permits observation but locks ordinary mutation of the
signed grant atom. Future policy changes are not intrinsically revocations:
event26 must inspect and admit the *current* law rather than requiring this
original policy root forever. A changed payload or tombstone still fails its
exact current certificate check. -/
def initialGrantPolicy (owner : SubjectId) : Pred := .any [
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5], .eq "request/subject" owner.value]]

def Ready.policyRecord {F : Type} [Field F]
    (_ready : Ready domain spec operation) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) : PolicyRecord :=
  ⟨⟨spec.grant.source.resource⟩, 0, config.deployment.domain, profile.semantics,
    none, initialGrantPolicy spec.grant.approval.issuer⟩

def Ready.initialPolicies {F : Type} [Field F]
    (ready : Ready domain spec operation) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) : List InitialPolicy :=
  let record := ready.policyRecord profile config
  [⟨record.policyId, PolicyRecordCodec.digest record,
    PolicyRecordCodec.encode record⟩]

/-- The factory/Book descriptor is fixed by issuer, nonce, one empty content
birth, two source-derived capabilities and the pinned final-payload tariff.
The later event27 admission must compare the complete decoded descriptor and
install `initializedCell` only after the current app delegation check. -/
def Ready.descriptor {F : Type} [Field F]
    (ready : Ready domain spec operation)
    (profile : CanonicalRuntimeProfile.Profile F) (config : NativeHost.Config)
    (authority : AuthState) (height : Nat)
    (_domainBound : domain = config.deployment.domain)
    (_operationBound : operation =
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.grant.approval.issuer spec.grant.approval.nonce).value)
    (payer : Nat) (funding : List InitialFunding := []) :
    Descriptor CanonicalCellRegistry.registry :=
  let identity := ResourceBirthController.Concrete.sourceIdentity
    profile.compilerProfile config.deployment spec.grant.approval.issuer
    spec.grant.approval.nonce
  let draft : Descriptor CanonicalCellRegistry.registry :=
    { factory := ⟨config.deployment.factoryId⟩,
      creator := spec.grant.approval.issuer,
      transactionId := identity,
      nonce := spec.grant.approval.nonce,
      births := ready.births,
      auxiliaryCreates := [],
      grants := ready.grants profile authority height,
      initialPolicies := ready.initialPolicies profile config,
      authorityNullifier := identity.value,
      funding := funding,
      fee := ⟨payer, config.tariff.collector, config.tariff.asset, 0⟩ }
  { draft with fee := { draft.fee with amount :=
      (draft.quotedFee (ready.effectiveTariff config.tariff)) } }

def Ready.expectedDescriptor {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config)
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.grant.approval.issuer spec.grant.approval.nonce).value)
    (authority : AuthState) (height payer : Nat)
    (funding : List InitialFunding := []) :
    Descriptor CanonicalCellRegistry.registry :=
  ready.descriptor profile config authority height rfl rfl payer funding

end Minidregg.Kernel.ApplicationAgentLifetimeGrantSource
