/-
Source construction for a special app-authorized share issue. This is not a
receiving endpoint: the issue receiver must admit the ordinary factory/Book/
allocation/authority birth branches and a current app `.delegateObject`
signature/capability/law at the same loaded image, then emit one distinct
durable issue event. A bare resource birth or this generated draft alone is
never a dispatch share.
-/
import Kernel.ApplicationDispatchAuthority
import Kernel.ApplicationGrain
import Kernel.NativeHostContext
import Kernel.ResourceBirthController

namespace Minidregg.Kernel.ApplicationShareIssueSource
open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.HyperdocumentContentPageMaterializer
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Pred
open Minidregg.Kernel.ApplicationDispatchAuthority
set_option autoImplicit false

/-- The issuer may be app-owner-delegated, but its selected current capability
must authorize `.delegateObject` on this app. There is no caller-supplied
original-owner assertion. The born ticket is issuer-owned and immutable under
its content law; dispatch rechecks the issuer's app delegation lineage and
revocation before using the accepted issue event. -/
structure Spec where
  ticket : Ticket
  issuer : SubjectId
  appDelegateCapability : CapabilityId
  ticketOwnerCapability : CapabilityId
  ticketControlCapability : CapabilityId
  deriving DecidableEq, Repr

def specStream : StreamCodec Spec :=
  StreamCodec.xmap
    (StreamCodec.product ticketStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
          (StreamCodec.product CredentialAuthorityEntryCodec.capabilityIdStream
            CredentialAuthorityEntryCodec.capabilityIdStream))))
    (fun spec => (spec.ticket, spec.issuer,
      spec.appDelegateCapability, spec.ticketOwnerCapability,
      spec.ticketControlCapability))
    (fun (ticket, issuer, appDelegateCapability,
          ticketOwnerCapability, ticketControlCapability) =>
      ⟨ticket, issuer, appDelegateCapability,
        ticketOwnerCapability, ticketControlCapability⟩)
    (by intro spec; cases spec; rfl)

private def specFrame : List UInt8 :=
  "DREGG/APPLICATION/SHARE-ISSUE-SPEC/v2".toUTF8.toList

private def rawSpecCodec : LawfulCodec Spec where
  encode spec := specFrame ++ specStream.encode spec
  decode bytes := if bytes.take specFrame.length = specFrame then
    specStream.toLawful.decode (bytes.drop specFrame.length) else none
  decode_encode := by
    intro spec
    have decoded := specStream.toLawful.decode_encode spec
    change specStream.toLawful.decode (specStream.encode spec) = some spec at decoded
    simp [decoded]

def specCodec : LawfulCodec Spec := ResourceBirthCodec.strictCodec rawSpecCodec

theorem spec_decode_encode (spec : Spec) :
    specCodec.decode (specCodec.encode spec) = some spec := specCodec.decode_encode spec

theorem spec_bytes_injective : Function.Injective specCodec.encode := by
  intro left right same
  have decoded := congrArg specCodec.decode same
  exact Option.some.inj (by simpa only [specCodec.decode_encode] using decoded)

/-- Distinct outer ingress. The bare birth decoder cannot consume these
bytes, and replay must re-run both native branches from the retained exact
envelopes. A participant cannot turn a plain birth receipt into share issue
provenance by merely presenting the ticket payload. -/
structure Ingress where
  spec : Spec
  birthIngress : List UInt8
  appEnvelope : List UInt8
  deriving DecidableEq, Repr

private def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap
    (StreamCodec.product specStream
      (StreamCodec.product bytesStream bytesStream))
    (fun ingress => (ingress.spec, ingress.birthIngress, ingress.appEnvelope))
    (fun (spec, birthIngress, appEnvelope) =>
      ⟨spec, birthIngress, appEnvelope⟩)
    (by intro ingress; cases ingress; rfl)

private def ingressFrame : List UInt8 :=
  "DREGG/APPLICATION/SHARE-ISSUE-INGRESS/v2".toUTF8.toList

private def rawIngressCodec : LawfulCodec Ingress where
  encode ingress := ingressFrame ++ ingressStream.encode ingress
  decode bytes := if bytes.take ingressFrame.length = ingressFrame then
    ingressStream.toLawful.decode (bytes.drop ingressFrame.length) else none
  decode_encode := by
    intro ingress
    have decoded := ingressStream.toLawful.decode_encode ingress
    change ingressStream.toLawful.decode (ingressStream.encode ingress) = some ingress at decoded
    simp [decoded]

def ingressCodec : LawfulCodec Ingress := ResourceBirthCodec.strictCodec rawIngressCodec

theorem ingress_decode_encode (ingress : Ingress) :
    ingressCodec.decode (ingressCodec.encode ingress) = some ingress :=
  ingressCodec.decode_encode ingress

theorem ingress_bytes_injective : Function.Injective ingressCodec.encode := by
  intro left right same
  have decoded := congrArg ingressCodec.decode same
  exact Option.some.inj (by simpa only [ingressCodec.decode_encode] using decoded)

def Spec.valid (spec : Spec) : Prop :=
  spec.ticket.resource ≠ spec.ticket.scope.app ∧
  spec.ticket.participant.session ≠ spec.ticket.resource ∧
  spec.ticket.participant.descriptorResource ≠ spec.ticket.resource ∧
  spec.ticketOwnerCapability ≠ spec.ticketControlCapability ∧
  spec.ticket.participant.ticketObserveCapability ≠ spec.ticketOwnerCapability ∧
  spec.ticket.participant.ticketObserveCapability ≠ spec.ticketControlCapability ∧
  spec.ticket.scope.schemaRoot = spec.ticket.ceiling.roleSchemaRoot ∧
  spec.ticket.scope.schemaVersion = spec.ticket.ceiling.roleVersion ∧
  spec.ticket.ceiling.valid = true

instance validDecidable (spec : Spec) : Decidable spec.valid := by
  unfold Spec.valid
  infer_instance

/-- The source-owned initial page has exactly one canonical share-ticket
atom, with the born resource as document. No arbitrary initial content page is
accepted from a caller. -/
def ticketPage (domain : Digest) (spec : Spec) (operation : Nat) :
    Except ContentResource.Reject HyperdocumentContentPageMaterializer.Page :=
  ContentResource.step ⟨spec.issuer, .object, spec.ticketOwnerCapability⟩ ⟨⟨operation⟩⟩
    (ContentResource.initialPage domain spec.ticket.resource)
    (ApplicationDispatchAuthority.initialAction domain spec.ticket)

structure Ready (domain : Digest) (spec : Spec) (operation : Nat) where
  private mk ::
  valid : spec.valid
  page : HyperdocumentContentPageMaterializer.Page
  pageExact : ticketPage domain spec operation = .ok page

def prepare {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) (spec : Spec) :
    Except String (Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value) := do
  let operation :=
    (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
      config.deployment spec.issuer spec.ticket.issueNonce).value
  if valid : spec.valid then
    match exact : ticketPage config.deployment.domain spec operation with
    | .error _ => .error "share ticket initial page refused"
    | .ok page => .ok ⟨valid, page, exact⟩
  else .error "invalid share ticket selectors"

private def bornCell (page : HyperdocumentContentPageMaterializer.Page) :
    PackedCell CanonicalCellRegistry.registry :=
  ⟨.content, materialize HyperdocumentContentPageMaterializer.materializer
    (HyperdocumentContentPageMaterializer.stateOfOption (some page))⟩

variable {domain : Digest} {spec : Spec} {operation : Nat}

def Ready.birth (ready : Ready domain spec operation) :
    BirthItem CanonicalCellRegistry.registry :=
  ⟨⟨spec.ticket.resource, CellSlot.root CanonicalCellRegistry.registry .absent,
      bornCell ready.page⟩, .object, spec.issuer⟩

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
      spec.ticketOwnerCapability spec.issuer spec.ticket.resource
      (ResourceBirthPolicyController.Concrete.ownerVerbs .object), []⟩⟩

private def controlGrant {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F) (authority : AuthState)
    (height : Nat) (spec : Spec) : AuthorityGrant :=
  ⟨.program, ⟨rootCapability .program profile authority height
      spec.ticketControlCapability spec.issuer spec.ticket.resource
      {.installPolicy, .revokeCapability}, []⟩⟩

def Ready.grants {F : Type} [Field F]
    (_ready : Ready domain spec operation) (profile : CanonicalRuntimeProfile.Profile F)
    (authority : AuthState) (height : Nat) : List AuthorityGrant :=
  [ownerGrant profile authority height spec, controlGrant profile authority height spec]

theorem Ready.two_grants {F : Type} [Field F]
    (ready : Ready domain spec operation) (profile : CanonicalRuntimeProfile.Profile F)
    (authority : AuthState) (height : Nat) :
    (ready.grants profile authority height).length = 2 := rfl

/-- A v2 share ticket is immutable as content. Even if a factory caller names
its own subject as the born resource owner, a later ordinary content edit
cannot broaden this accepted grant under this law. The dispatch receiver must
also require this exact current policy source and compare the current ticket
bytes with the special issue event; changing the law or ticket refuses. A
native current capability still governs observation and revocation. -/
def ticketPolicy (owner : SubjectId) : Pred := .any [
  .memberOf "request/verb" [1,3],
  .all [.memberOf "request/verb" [4,5], .eq "request/subject" owner.value]]

def Ready.policyRecord {F : Type} [Field F]
    (_ready : Ready domain spec operation) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) : PolicyRecord :=
  ⟨⟨spec.ticket.resource⟩, 0, config.deployment.domain, profile.semantics,
    none, ticketPolicy spec.issuer⟩

def Ready.initialPolicies {F : Type} [Field F]
    (ready : Ready domain spec operation) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) : List InitialPolicy :=
  let record := ready.policyRecord profile config
  [⟨record.policyId, PolicyRecordCodec.digest record, PolicyRecordCodec.encode record⟩]

/-- The ordinary birth descriptor is source-authored from the exact ticket
page and owner-locked policy. A later receiving step must additionally check
the app delegation branch; this descriptor can never prove that by itself. -/
def Ready.descriptor {F : Type} [Field F]
    (ready : Ready domain spec operation) (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config) (authority : AuthState) (height : Nat)
    (domainBound : domain = config.deployment.domain)
    (operationBound : operation =
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (payer : Nat) (funding : List InitialFunding := []) :
    Descriptor CanonicalCellRegistry.registry :=
  let identity := ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
    config.deployment spec.issuer spec.ticket.issueNonce
  let draft : Descriptor CanonicalCellRegistry.registry :=
    { factory := ⟨config.deployment.factoryId⟩, creator := spec.issuer,
      transactionId := identity, nonce := spec.ticket.issueNonce,
      births := ready.births, auxiliaryCreates := [],
      grants := ready.grants profile authority height,
      initialPolicies := ready.initialPolicies profile config,
      authorityNullifier := identity.value,
      funding := funding,
      fee := ⟨payer, config.tariff.collector, config.tariff.asset, 0⟩ }
  { draft with fee := { draft.fee with amount := draft.quotedFee config.tariff } }

/-- Rebuild the one permissible birth descriptor from the selected issuer and
exact ticket, retaining only the caller's payer/funding choices. The special
receiver compares this whole value with the decoded, natively admitted birth;
the source builder alone is not issue authority. -/
def Ready.expectedDescriptor {F : Type} [Field F]
    (profile : CanonicalRuntimeProfile.Profile F)
    (config : NativeHost.Config)
    (ready : Ready config.deployment.domain spec
      (ResourceBirthController.Concrete.sourceIdentity profile.compilerProfile
        config.deployment spec.issuer spec.ticket.issueNonce).value)
    (authority : AuthState) (height payer : Nat)
    (funding : List InitialFunding := []) :
    Descriptor CanonicalCellRegistry.registry :=
  ready.descriptor profile config authority height rfl rfl payer funding

/-- The app delegation request commits to the exact complete source draft
under an independent domain. Hash collision resistance is an external crypto
assumption; no theorem treats digest equality as byte equality. -/
def sourceBytes (spec : Spec) (descriptor : Descriptor CanonicalCellRegistry.registry) :
    List UInt8 :=
  "DREGG/APPLICATION/SHARE-ISSUE-SOURCE/v2".toUTF8.toList ++
    (StreamCodec.product bytesStream bytesStream).encode
      (specCodec.encode spec,
        (ResourceBirthCodec.descriptorCodec CanonicalCellRegistry.registry).encode descriptor)

def issueMarker (spec : Spec) (descriptor : Descriptor CanonicalCellRegistry.registry) : Nat :=
  (Sp800185Cshake256.hash
    "DREGG/APPLICATION/SHARE-ISSUE-MARKER/v2".toUTF8.toList
    (sourceBytes spec descriptor)).digest.value

def appRequest (domain semantics : Digest) (federation : FederationId)
    (authority : AuthState) (height : Nat) (appRoot : Digest)
    (spec : Spec) (descriptor : Descriptor CanonicalCellRegistry.registry) :
    Request .object where
  domain := domain
  semantics := semantics
  federation := federation
  subject := spec.issuer
  subjectKeyEpoch := authority.subjectKeyEpoch spec.issuer
  target := ⟨spec.ticket.scope.app⟩
  verb := .delegateObject
  argsDigest := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/SHARE-ISSUE-ARGS/v2".toUTF8.toList
    (sourceBytes spec descriptor)).digest
  effectsDigest := (Sp800185Cshake256.hash
    "DREGG/APPLICATION/SHARE-ISSUE-EFFECTS/v2".toUTF8.toList
    (sourceBytes spec descriptor)).digest
  nonce := spec.ticket.issueNonce
  height := height
  preStateRoot := appRoot
  policyId := ⟨spec.ticket.scope.app⟩
  policyEpoch := authority.policyEpoch ⟨spec.ticket.scope.app⟩
  policyRevision := authority.policyRevision ⟨spec.ticket.scope.app⟩
  cost := (sourceBytes spec descriptor).length

theorem appRequest_issuer (domain semantics : Digest) (federation : FederationId)
    (authority : AuthState) (height : Nat) (appRoot : Digest)
    (spec : Spec) (descriptor : Descriptor CanonicalCellRegistry.registry) :
    (appRequest domain semantics federation authority height appRoot spec descriptor).subject =
      spec.issuer := rfl

theorem appRequest_app (domain semantics : Digest) (federation : FederationId)
    (authority : AuthState) (height : Nat) (appRoot : Digest)
    (spec : Spec) (descriptor : Descriptor CanonicalCellRegistry.registry) :
    (appRequest domain semantics federation authority height appRoot spec descriptor).target.value =
      spec.ticket.scope.app := rfl

theorem appRequest_delegate (domain semantics : Digest) (federation : FederationId)
    (authority : AuthState) (height : Nat) (appRoot : Digest)
    (spec : Spec) (descriptor : Descriptor CanonicalCellRegistry.registry) :
    (appRequest domain semantics federation authority height appRoot spec descriptor).verb =
      .delegateObject := rfl

end Minidregg.Kernel.ApplicationShareIssueSource
