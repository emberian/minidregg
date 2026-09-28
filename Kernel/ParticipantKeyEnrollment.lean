/-
Runtime enrollment of a fresh signing principal. The new key is installed in
the same canonical authority cell used by every signed receiver. Enrollment
does not issue a capability or create an account: a current factory-management
capability, its current law, and the new key holder's proof of possession are
all required before the authority and nullifier update can commit.
-/
import Kernel.CapabilityRevocationController

namespace Minidregg.Kernel.ParticipantKeyEnrollment

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
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev AuthorityMaterializer := CredentialAuthorityStateCodec.materializer

structure Command where
  sponsor : SubjectId
  control : CapabilityId
  nonce : Nat
  expectedFactoryRoot : Digest
  expectedAuthorityRoot : Digest
  key : KeyRecord
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream CredentialSigningKeyCodec.keyRecordStream)))))
    (fun command => (command.sponsor, command.control, command.nonce,
      command.expectedFactoryRoot, command.expectedAuthorityRoot, command.key))
    (fun (sponsor, control, nonce, factoryRoot, authorityRoot, key) =>
      ⟨sponsor, control, nonce, factoryRoot, authorityRoot, key⟩)
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

def commandCodec : LawfulCodec Command :=
  framed "DREGG/PARTICIPANT/KEY-ENROLL/v1".toUTF8.toList commandStream

structure Ingress where
  commandBytes : List UInt8
  sponsorEnvelope : List UInt8
  possessionSignature : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream
    (StreamCodec.product bytesStream bytesStream))
    (fun ingress => (ingress.commandBytes, ingress.sponsorEnvelope, ingress.possessionSignature))
    (fun (command, sponsor, possession) => ⟨command, sponsor, possession⟩)
    (by intro ingress; cases ingress; rfl)

def ingressCodec : LawfulCodec Ingress :=
  framed "DREGG/PARTICIPANT/KEY-ENROLL/SIGNED/v1".toUTF8.toList ingressStream

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
        ResourceBirthCodec.strictCodec_canonical
          (framedRaw "DREGG/PARTICIPANT/KEY-ENROLL/v1".toUTF8.toList commandStream)
          commandExact, envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.PARTICIPANT.KEY-ENROLL.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.sponsor, command.nonce))).digest.value

def possessionFrame (domain semantics : Digest) (command : Command) : List UInt8 :=
  "DREGG/PARTICIPANT/KEY-ENROLL/POSSESSION/v1".toUTF8.toList ++
    (StreamCodec.product digestStream (StreamCodec.product digestStream bytesStream)).encode
      (domain, semantics, commandCodec.encode command)

structure Declaration where
  key : KeyRecord
  expectedPreRoot : Digest
  operationNullifier : Nat

def declarationStream : StreamCodec Declaration :=
  StreamCodec.xmap
    (StreamCodec.product CredentialSigningKeyCodec.keyRecordStream
      (StreamCodec.product digestStream StreamCodec.nat))
    (fun d => (d.key, d.expectedPreRoot, d.operationNullifier))
    (fun (key, root, nullifier) => ⟨key, root, nullifier⟩)
    (by intro d; cases d; rfl)

def declarationCodec : LawfulCodec Declaration :=
  ResourceBirthCodec.strictCodec declarationStream.toLawful

def declaration (domain semantics : Digest) (command : Command) : Declaration :=
  ⟨command.key, command.expectedAuthorityRoot, marker domain semantics command⟩

def Declaration.patch (d : Declaration) : Patch CredentialAuthorityState.schema Digest where
  expectedPreRoot := d.expectedPreRoot
  fieldFootprint := {
    .subjectKeyEpoch ⟨d.key.subject⟩,
    .subjectKey ⟨d.key.subject⟩ d.key.keyEpoch,
    .nullifier d.operationNullifier }
  resourceFootprint := ∅
  fieldWrites :=
    [⟨.subjectKeyEpoch ⟨d.key.subject⟩, some d.key.keyEpoch⟩,
     ⟨.subjectKey ⟨d.key.subject⟩ d.key.keyEpoch, some d.key⟩,
     ⟨.nullifier d.operationNullifier, some true⟩]
  resourceWrites := []

theorem Declaration.patch_namedFields (d : Declaration) :
    d.patch.namedFields = d.patch.fieldFootprint := by
  simp [Declaration.patch, Patch.namedFields]

theorem Declaration.patch_namedResources (d : Declaration) :
    d.patch.namedResources = d.patch.resourceFootprint := by
  simp [Declaration.patch, Patch.namedResources]

structure Mode {M : Materializer} (pre : Cell M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root
  subjectAbsent : pre.logical.fields (.subjectKeyEpoch ⟨d.key.subject⟩) = none
  keyAbsent : pre.logical.fields (.subjectKey ⟨d.key.subject⟩ d.key.keyEpoch) = none
  fresh : isNullified pre d.operationNullifier = false

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PARTICIPANT.KEY-ENROLL.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream bytesStream))).encode
      (domain, semantics, commandCodec.encode command, declarationCodec.encode d))).digest

structure Ambient where
  federation : FederationId
  height : Height

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
    (Sp800185Cshake256.hash "DREGG.PARTICIPANT.KEY-ENROLL.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

def request (deployment : Deployment) (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) : Request .program :=
  ((context deployment snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) snapshot.cell.root
    (marker snapshot.domain semantics command) (declaration snapshot.domain semantics command)).2

def family (deployment : Deployment) (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) :
    SemanticEffectFamily CredentialAuthorityState.schema AuthorityMaterializer Nat where
  Declaration := Declaration
  declarationCodec := declarationCodec
  pre := snapshot.cell
  request := fun d => (context deployment snapshot semantics ambient command).request
    declarationCodec (effectDigest snapshot.domain semantics command) snapshot.cell.root
    d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun d _ => Mode snapshot.cell d
  Postcondition := fun d _ post => d.patch.ResultAt snapshot.logical post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun d _ => d.patch
  nullifier := fun d _ => some d.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

def edits (snapshot : Snapshot) (d : Declaration) : List CredentialAuthorityDomain.Edit :=
  [CredentialAuthorityDomain.signingKeyEdit snapshot d.key,
   CredentialAuthorityDomain.nullifierEdit snapshot d.operationNullifier]

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | factoryUnavailable | staleAuthority
  | subjectExists | keyIdExists | publicKeyExists | malformedKey | replayedMarker
  | authorityPreparation | validation | refinement | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  | possession (reason : CredentialSignatureIO.Error) | invalidPossession
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  authority : Loaded deployment.authorityAnchor durable.snapshot
  factory : ResourceTargetAdmission.Observed deployment directory.directory .object
    deployment.factoryId command.expectedFactoryRoot
  candidate : Candidate (family deployment authority.snapshot profile.semantics ambient command)
    authority.snapshot.cell (declaration authority.snapshot.domain profile.semantics command) ()
  update : CredentialAuthorityDomain.Prepared authority.snapshot
    (edits authority.snapshot (declaration authority.snapshot.domain profile.semantics command))
  postExact : update.postLogical = candidate.validated.apply.logical
  physical : Lowered directory authority
    (edits authority.snapshot (declaration authority.snapshot.domain profile.semantics command)) update []
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨deployment.factoryId⟩
      (authority.snapshot.authState.policyRevision ⟨deployment.factoryId⟩))
  keyIdFresh : authority.snapshot.entries.all (fun entry => match entry with
    | .subjectKey key => key.keyId != command.key.keyId
    | _ => true) = true
  publicKeyFresh : authority.snapshot.entries.all (fun entry => match entry with
    | .subjectKey key => key.publicKey != command.key.publicKey
    | _ => true) = true
  keyShape : command.key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
    command.key.publicKey.length = 32 ∧ command.key.revoked = false ∧
    command.key.activeFrom ≤ authority.snapshot.catalogue.revision + 1 ∧
    authority.snapshot.catalogue.revision + 1 ≤ command.key.activeUntil ∧
    command.key.subject ≠ command.sponsor.value

def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let factory ← requireSome .factoryUnavailable
    (ResourceTargetAdmission.observe deployment directory.directory .object
      deployment.factoryId command.expectedFactoryRoot)
  let snapshot := authority.snapshot
  let d := declaration snapshot.domain profile.semantics command
  if rootExact : command.expectedAuthorityRoot = snapshot.cell.root then
    if subjectAbsent : snapshot.logical.fields (.subjectKeyEpoch ⟨command.key.subject⟩) = none then
      if keyAbsent : snapshot.logical.fields (.subjectKey ⟨command.key.subject⟩ command.key.keyEpoch) = none then
        if keyIdFresh : snapshot.entries.all (fun entry => match entry with
            | .subjectKey key => key.keyId != command.key.keyId
            | _ => true) then
          if publicKeyFresh : snapshot.entries.all (fun entry => match entry with
              | .subjectKey key => key.publicKey != command.key.publicKey
              | _ => true) then
            if keyShape : command.key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
                command.key.publicKey.length = 32 ∧
                command.key.revoked = false ∧
                command.key.activeFrom ≤ snapshot.catalogue.revision + 1 ∧
                snapshot.catalogue.revision + 1 ≤ command.key.activeUntil ∧
                command.key.subject ≠ command.sponsor.value then
              if fresh : isNullified snapshot.cell d.operationNullifier = false then
                let update ← requireSome .authorityPreparation
                  (CredentialAuthorityDomain.prepare snapshot (edits snapshot d))
                match validate AuthorityMaterializer snapshot.cell d.patch with
                | .rejected _ => throw .validation
                | .accepted validated =>
                  if same : CredentialAuthorityStateCodec.encode update.postLogical =
                      CredentialAuthorityStateCodec.encode validated.apply.logical then
                    let physical ← requireSome .physicalPreparation (lower directory authority update [])
                    let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                      snapshot.domain directory.directory
                      (snapshot.authState.policyAddress ⟨deployment.factoryId⟩
                        (snapshot.authState.policyRevision ⟨deployment.factoryId⟩)))
                    let candidate : Candidate (family deployment snapshot profile.semantics ambient command)
                        snapshot.cell d () :=
                      { preStateBound := rfl
                        modeEvidence := ⟨rootExact, subjectAbsent, keyAbsent, fresh⟩
                        validated := validated
                        postcondition := validated.resultAt }
                    pure ⟨directory, authority, factory, candidate, update,
                      CredentialAuthorityStateCodec.encode_injective same, physical, source,
                      keyIdFresh, publicKeyFresh, keyShape⟩
                  else throw .refinement
              else throw .replayedMarker
            else throw .malformedKey
          else throw .publicKeyExists
        else throw .keyIdExists
      else throw .subjectExists
    else throw .subjectExists
  else throw .staleAuthority

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

def project (prepared : Prepared deployment profile ambient durable command)
    (logical : LogicalState CredentialAuthorityState.schema.{0, 0}) : Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots
      (request deployment prepared.authority.snapshot profile.semantics ambient command) ++
    [("authority/operation/enroll-key", 1)] ++
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
    (request deployment prepared.authority.snapshot profile.semantics ambient command)
    prepared.authority.snapshot.cell
    (declaration prepared.authority.snapshot.domain profile.semantics command) ()

def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request deployment prepared.authority.snapshot profile.semantics ambient command
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
  possessionVerified : Bool
  possessionTrue : possessionVerified = true

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request deployment prepared.authority.snapshot profile.semantics ambient command)
      ingress.ingress.sponsorEnvelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic =>
          match ← CredentialSignatureIO.verify native command.key.publicKey
              (possessionFrame prepared.authority.snapshot.domain profile.semantics command)
              ingress.ingress.possessionSignature with
          | .error reason => return .error (.possession reason)
          | .ok verified =>
              if yes : verified = true then return .ok ⟨receipt, same, semantic, verified, yes⟩
              else return .error .invalidPossession
      else return .error .capabilityRejected

/-- The caller signs the sponsor's exact request header and the new key's
independent possession frame. The two raw signatures have distinct meanings. -/
structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  sponsorHeader : List UInt8
  possessionHeader : List UInt8
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream
      (StreamCodec.product bytesStream
        (StreamCodec.product bytesStream bytesStream))))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes,
      plan.sponsorHeader, plan.possessionHeader))
    (fun (domain, semantics, command, sponsor, possession) =>
      ⟨domain, semantics, command, sponsor, possession⟩)
    (by intro plan; cases plan; rfl)

def signingPlanCodec : LawfulCodec SigningPlan :=
  framed "DREGG/PARTICIPANT/KEY-ENROLL/PLAN/v1".toUTF8.toList signingPlanStream

end Minidregg.Kernel.ParticipantKeyEnrollment
