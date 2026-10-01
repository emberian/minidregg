/-
Runtime provisioning of factory observation for an already enrolled signing
principal. A current factory-management capability, presented by its holder
under the factory's current law, issues one fresh root object capability that
permits exactly `observeObject` on the deployed factory. The effect is the
existing root-issuance family: fresh identifier, current issuer and policy
epochs, registered for revocation, single-use operation marker.

Key enrollment conveys no grant. Paying for a birth needs an account the new
subject can debit; that is an ordinary resource birth of an account owned by
the new subject, which the birth controller already admits. This operation
supplies the remaining permission: reading the factory, which current resource
birth authoring requires as a signed observation.
-/
import Kernel.CapabilityRevocationController

namespace Minidregg.Kernel.ParticipantFactoryProvisioning

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.CredentialLineageAdmission
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev AuthorityMaterializer := CredentialAuthorityCell.materializer

/-- The caller names the sponsor's control capability, the enrolled holder and
a fresh capability identifier. Every other capability field is derived by the
receiving source from the deployment, the runtime profile, the current height
and the current authority epochs. -/
structure Command where
  sponsor : SubjectId
  control : CapabilityId
  nonce : Nat
  expectedFactoryRoot : Digest
  expectedAuthorityRoot : Digest
  holder : SubjectId
  capability : CapabilityId
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
                capabilityIdStream))))))
    (fun command => (command.sponsor, command.control, command.nonce,
      command.expectedFactoryRoot, command.expectedAuthorityRoot, command.holder,
      command.capability))
    (fun (sponsor, control, nonce, factoryRoot, authorityRoot, holder, capability) =>
      ⟨sponsor, control, nonce, factoryRoot, authorityRoot, holder, capability⟩)
    (by intro command; cases command; rfl)

def framedRaw {α : Type} (frame : List UInt8) (stream : StreamCodec α) : LawfulCodec α :=
  { encode := fun value => frame ++ stream.encode value
    decode := fun bytes => if bytes.take frame.length = frame then
        stream.toLawful.decode (bytes.drop frame.length) else none
    decode_encode := by
      intro value
      have exact := stream.toLawful.decode_encode value
      change stream.toLawful.decode (stream.encode value) = some value at exact
      simp [exact] }

def framed {α : Type} (frame : List UInt8) (stream : StreamCodec α) : LawfulCodec α :=
  ResourceBirthCodec.strictCodec (framedRaw frame stream)

def commandFrame : List UInt8 := "DREGG/PARTICIPANT/FACTORY-OBSERVE/v1".toUTF8.toList

def commandCodec : LawfulCodec Command := framed commandFrame commandStream

structure Ingress where
  commandBytes : List UInt8
  sponsorEnvelope : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun ingress => (ingress.commandBytes, ingress.sponsorEnvelope))
    (fun (command, sponsor) => ⟨command, sponsor⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  framed "DREGG/PARTICIPANT/FACTORY-OBSERVE/SIGNED/v1".toUTF8.toList ingressStream

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes
  envelope : CredentialSignedEnvelopeController.SignedEnvelope
  envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.sponsorEnvelope =
    some envelope

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command =>
    match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.sponsorEnvelope with
    | none => none
    | some envelope =>
      some ⟨ingress, command,
        ResourceBirthCodec.strictCodec_canonical (framedRaw commandFrame commandStream)
          commandExact, envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.PARTICIPANT.FACTORY-OBSERVE.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.sponsor, command.nonce))).digest.value

structure Ambient where
  federation : FederationId
  height : Height

/-- The one grant this operation can produce: root, observation only, on the
deployed factory, for the named holder. Window and budget follow the same
factory template as grants issued by a resource birth at this height. -/
def observeCapability (deployment : Deployment) (template : CanonicalRuntimeProfile.FactoryTemplate)
    (pre : Cell AuthorityMaterializer) (ambient : Ambient) (command : Command) :
    Capability .object where
  id := command.capability
  root := command.capability
  parent := none
  issuer := template.issuer
  holder := .subject command.holder
  scope := ⟨.explicit {⟨deployment.factoryId⟩}, {.observeObject}, template.ownerBudget⟩
  notBefore := ambient.height
  notAfter := ambient.height + template.lifetime
  issuerEpoch := issuerEpochAt pre template.issuer
  policyId := ⟨deployment.factoryId⟩
  policyEpoch := policyEpochAt pre ⟨deployment.factoryId⟩
  ancestors := ∅
  channels := ∅

def declaration (deployment : Deployment) (template : CanonicalRuntimeProfile.FactoryTemplate)
    (domain semantics : Digest) (pre : Cell AuthorityMaterializer) (ambient : Ambient)
    (command : Command) : IssueDeclaration .object :=
  ⟨observeCapability deployment template pre ambient command, command.expectedAuthorityRoot,
    marker domain semantics command⟩

def declarationStream : StreamCodec (IssueDeclaration .object) :=
  StreamCodec.xmap
    (StreamCodec.product (capabilityStream .object)
      (StreamCodec.product digestStream StreamCodec.nat))
    (fun d => (d.capability, d.expectedPreRoot, d.operationNullifier))
    (fun (capability, root, nullifier) => ⟨capability, root, nullifier⟩)
    (by intro d; cases d; rfl)

def declarationCodec : LawfulCodec (IssueDeclaration .object) :=
  ResourceBirthCodec.strictCodec declarationStream.toLawful

def effectDigest (domain semantics : Digest) (command : Command)
    (d : IssueDeclaration .object) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PARTICIPANT.FACTORY-OBSERVE.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream bytesStream))).encode
      (domain, semantics, commandCodec.encode command, declarationCodec.encode d))).digest

/-- The same factory-management request shape as key enrollment: the sponsor's
program capability over the factory, checked against the factory's current law. -/
def context (deployment : Deployment) (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) : RequestContext where
  authority :=
    { kind := .program
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.sponsor
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.sponsor
      target := ⟨deployment.factoryId⟩
      verb := .installPolicy
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨deployment.factoryId⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨deployment.factoryId⟩
      policyRevision := snapshot.authState.policyRevision ⟨deployment.factoryId⟩
      cost := (commandCodec.encode command).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.PARTICIPANT.FACTORY-OBSERVE.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

abbrev family (deployment : Deployment)
    (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command) :
    SemanticEffectFamily CredentialAuthorityState.layout AuthorityMaterializer Nat :=
  issueFamily snapshot.cell declarationCodec
    (effectDigest snapshot.domain semantics command)
    (context deployment snapshot semantics ambient command)

def request (deployment : Deployment) (template : CanonicalRuntimeProfile.FactoryTemplate)
    (snapshot : Snapshot) (semantics : Digest) (ambient : Ambient) (command : Command) :
    Request .program :=
  ((context deployment snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) snapshot.cell.root
    (marker snapshot.domain semantics command)
    (declaration deployment template snapshot.domain semantics snapshot.cell ambient command)).2

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | factoryUnavailable
  | staleAuthority | holderNotEnrolled | capabilityExists | capabilityRevoked | replayedMarker
  | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  authority : Loaded deployment durable.snapshot
  factory : ResourceTargetAdmission.Observed deployment directory.directory .object
    deployment.factoryId command.expectedFactoryRoot
  holderEnrolled :
    (show Option Epoch from authority.snapshot.logical ⟨.subjectKeyEpoch, command.holder⟩).isSome = true
  candidate : Candidate
    (family deployment authority.snapshot profile.semantics ambient command)
    authority.snapshot.cell
    (declaration deployment profile.template authority.snapshot.domain profile.semantics
      authority.snapshot.cell ambient command) ()
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨deployment.factoryId⟩
      (authority.snapshot.authState.policyRevision ⟨deployment.factoryId⟩))

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let factory ← requireSome .factoryUnavailable
    (ResourceTargetAdmission.observe deployment directory.directory .object
      deployment.factoryId command.expectedFactoryRoot)
  let snapshot := authority.snapshot
  let template := profile.template
  let d := declaration deployment template snapshot.domain profile.semantics snapshot.cell
    ambient command
  if rootExact : command.expectedAuthorityRoot = snapshot.cell.root then
    if holderEnrolled :
        (show Option Epoch from snapshot.logical ⟨.subjectKeyEpoch, command.holder⟩).isSome = true then
      if fresh : capabilityIdFreshCheck snapshot.cell command.capability = true then
        if live : isRevoked snapshot.cell (.capability command.capability) = false then
         if unregistered : isRegistered snapshot.cell (.capability command.capability) = false then
          if snapshot.spent (marker snapshot.domain profile.semantics command) = false then
            match validate AuthorityMaterializer snapshot.cell snapshot.cell.root (d.patch snapshot.cell.logical) with
            | .rejected _ => throw .validation
            | .accepted validated =>
                let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                  snapshot.domain directory.directory
                  (snapshot.authState.policyAddress ⟨deployment.factoryId⟩
                    (snapshot.authState.policyRevision ⟨deployment.factoryId⟩)))
                let evidence : IssueEvidence snapshot.cell d :=
                  { preRootExact := rootExact
                    slotFresh := (capabilityIdFreshCheck_iff snapshot.cell command.capability).mp fresh
                    rootParent := rfl
                    rootSelf := rfl
                    rootAncestors := rfl
                    issuerCurrent := rfl
                    policyCurrent := rfl
                    selfUnregistered := unregistered
                    channelsRegistered := fun _ member => absurd member (Finset.notMem_empty _)
                    selfLive := live
                    channelsLive := fun _ member => absurd member (Finset.notMem_empty _) }
                let candidate : Candidate
                    (family deployment snapshot profile.semantics ambient command)
                    snapshot.cell d () :=
                  { preStateBound := rfl
                    modeEvidence := evidence
                    validated := validated
                    postcondition := validated.resultAt }
                pure ⟨directory, authority, factory, holderEnrolled, candidate, source⟩
          else throw .replayedMarker
         else throw .capabilityExists
        else throw .capabilityRevoked
      else throw .capabilityExists
    else throw .holderNotEnrolled
  else throw .staleAuthority

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

/-- The authority cell after provisioning: the validated issuance patch applied
to the loaded cell. It is the one authority write; the operation marker is the
intent's durable nullifier. -/
def Prepared.authorityPost (prepared : Prepared deployment profile ambient durable command) :
    CredentialAuthorityDomain.Cell :=
  prepared.candidate.validated.apply

/-- The factory law sees the operation label, the exact command, the factory
cell it will govern and the presented control grant. Unrelated authority
records are not projected. -/
def project (prepared : Prepared deployment profile ambient durable command)
    (logical : Store CredentialAuthorityState.layout) : Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots
      (request deployment profile.template prepared.authority.snapshot profile.semantics
        ambient command) ++
    [("authority/operation/provision-factory-observe", 1)] ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode command) ++
    DeclaredResourceController.bytesSlots "resource/bytes" 0
      (PackedCell.bytes Registry prepared.factory.before) ++
    ResourceAuthorityProjection.grantSlots "authority/control" .program command.control logical⟩

def step (prepared : Prepared deployment profile ambient durable command) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics prepared.candidate

def sourceStore (prepared : Prepared deployment profile ambient durable command) :
    CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource prepared.authority.snapshot.domain
    prepared.directory.directory⟩

def policyConfig [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) : CanonicalPolicyConfig F :=
  CredentialAuthorityPolicyRegistry.config profile.compilerProfile prepared.authority.snapshot
    (sourceStore prepared)
    (sourceCapabilityPortal prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared)

abbrev Prepared.SemanticAccepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family deployment prepared.authority.snapshot profile.semantics ambient command)
    (request deployment profile.template prepared.authority.snapshot profile.semantics ambient command)
    prepared.authority.snapshot.cell
    (declaration deployment profile.template prepared.authority.snapshot.domain profile.semantics
      prepared.authority.snapshot.cell ambient command) ()

/-- Capability-mode authorization only: the presented factory control grant
must be held by the signing sponsor and admitted by the current factory law. -/
def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request deployment profile.template prepared.authority.snapshot
    profile.semantics ambient command
  let config := policyConfig prepared
  let evidence ← requireSome .capabilityRejected
    (sourceCapabilityOnlyEvidence profile.compilerProfile prepared.authority.snapshot
      (sourceStore prepared)
      (marker prepared.authority.snapshot.domain profile.semantics command) (step prepared)
      wanted command.control receipt)
  let committed ← requireSome .policyUnavailable
    (config.registry.resolve wanted.policyId wanted.policyRevision)
  let witness := canonicalWitness profile.compilerProfile.compiler committed
    (step prepared).oldState (step prepared).newState
  if inputsInRange profile.compilerProfile.compiler committed.record.predicate
      witness.oldState witness.newState != true then
    throw .policyInputRange
  if !decide (castInjOn F
      (intsOf committed.record.predicate witness.oldState witness.newState)) then
    throw .policyCastAlias
  match CanonicalPolicyAdmission.admit config prepared.authority.snapshot.authState wanted
      evidence witness (.policy wanted.policyId wanted.policyRevision) rfl rfl with
  | none => .error .policyRejected
  | some authorization =>
      .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)

structure Accepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope
  semantic : prepared.SemanticAccepted

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request deployment profile.template prepared.authority.snapshot profile.semantics
        ambient command)
      ingress.ingress.sponsorEnvelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .capabilityRejected

/-- The sponsor signs one source-selected header. -/
structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  sponsorHeader : List UInt8
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream
      (StreamCodec.product bytesStream bytesStream)))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes, plan.sponsorHeader))
    (fun (domain, semantics, command, sponsor) => ⟨domain, semantics, command, sponsor⟩)
    (by intro plan; cases plan; rfl)

def signingPlanCodec : LawfulCodec SigningPlan :=
  framed "DREGG/PARTICIPANT/FACTORY-OBSERVE/PLAN/v1".toUTF8.toList signingPlanStream

/-! ## Named facts about the admitted grant -/

/-- Whatever the caller names, the issued grant observes and nothing else. -/
theorem observeCapability_verbs (deployment : Deployment)
    (template : CanonicalRuntimeProfile.FactoryTemplate) (pre : Cell AuthorityMaterializer)
    (ambient : Ambient) (command : Command) :
    (observeCapability deployment template pre ambient command).scope.verbs = {.observeObject} :=
  rfl

theorem observeCapability_cannot_delegate (deployment : Deployment)
    (template : CanonicalRuntimeProfile.FactoryTemplate) (pre : Cell AuthorityMaterializer)
    (ambient : Ambient) (command : Command) :
    Verb.delegateObject ∉ (observeCapability deployment template pre ambient command).scope.verbs := by
  simp [observeCapability]

theorem observeCapability_targets_factory (deployment : Deployment)
    (template : CanonicalRuntimeProfile.FactoryTemplate) (pre : Cell AuthorityMaterializer)
    (ambient : Ambient) (command : Command) :
    (observeCapability deployment template pre ambient command).scope.targets =
      .explicit {⟨deployment.factoryId⟩} := rfl

/-- A prepared provisioning always names an enrolled holder. -/
theorem Prepared.holder_enrolled (prepared : Prepared deployment profile ambient durable command) :
    (show Option Epoch from
      prepared.authority.snapshot.logical ⟨.subjectKeyEpoch, command.holder⟩).isSome = true :=
  prepared.holderEnrolled

/-- An accepted provisioning was authorized through capability mode naming the
sponsor's presented control record, never through signature mode alone. -/
theorem Accepted.capability_mode [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {ingress : DecodedIngress}
    (accepted : Accepted prepared ingress) :
    ∃ capability commitment,
      accepted.semantic.authorization.evidence.capabilityValue = some (capability, commitment) :=
  source_capability_only_mode _ _ _ _ _ accepted.semantic.authorization.evidence

end Minidregg.Kernel.ParticipantFactoryProvisioning
