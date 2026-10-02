/-
Runtime enrollment of a fresh signing principal. The new key is installed in
the same canonical authority cell used by every signed receiver. Enrollment
does not issue a capability or create an account: a current factory-management
capability, its current law, and the new key holder's proof of possession are
all required before the authority update and its durable nullifier commit.

A record that commits to a next key (pre-rotation) also needs POSSESSION of
that next key: the ingress carries the next public key and its signature over
`nextPossessionFrame` (the enrolled public key and the next public key), and
admission runs `Theory.KeyPreRotation.enrollGate` -- the same possession rule a
rotation has (`Accepted.nextPossession`).  A sponsor therefore cannot commit a
next key it merely names.  It CAN commit a keypair of its own; only the
subject's client, comparing the commitment with the digest of its own next
key, refuses that (`workspace init`).
-/
import Kernel.CapabilityRevocationController
import Theory.KeyPreRotation

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
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot
abbrev AuthorityMaterializer := CredentialAuthorityCell.materializer

/-! ## The next-key digest -/

def nextKeyDigestTag : List UInt8 := "DREGG.SIGNING-KEY.NEXT/v1".toUTF8.toList

/-- The pre-rotation commitment to a public key: cSHAKE256 under its own tag,
projected to the authority `Digest`.  The client never computes it; it asks the
host (`Host.Json` kind `signing-key-next-digest`). -/
def nextKeyDigest (publicKey : List UInt8) : Digest :=
  (Sp800185Cshake256.hash nextKeyDigestTag publicKey).digest

/-- The exact bytes the committed NEXT key signs at enrollment: its consent to
succeed the enrolled key.  Fixed layout (tag, the enrolled public key, the next
public key; both 32 bytes for Ed25519) so a key made offline by `mini keygen`
can co-sign before any Host is reachable.  No domain and no command: the
co-signature is made once, at keygen, and binds the pair only. -/
def nextPossessionTag : List UInt8 :=
  "DREGG/PARTICIPANT/KEY-ENROLL/NEXT-POSSESSION/v1".toUTF8.toList

def nextPossessionFrame (publicKey nextPublicKey : List UInt8) : List UInt8 :=
  nextPossessionTag ++ publicKey ++ nextPublicKey

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

/-- `nextPublicKey` / `nextPossessionSignature` are empty exactly when the
record commits to no next key (`enrollGate` refuses any other combination). -/
structure Ingress where
  commandBytes : List UInt8
  sponsorEnvelope : List UInt8
  possessionSignature : List UInt8
  nextPublicKey : List UInt8
  nextPossessionSignature : List UInt8
  deriving DecidableEq, Repr

def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream
    (StreamCodec.product bytesStream (StreamCodec.product bytesStream
      (StreamCodec.product bytesStream bytesStream))))
    (fun ingress => (ingress.commandBytes, ingress.sponsorEnvelope, ingress.possessionSignature,
      ingress.nextPublicKey, ingress.nextPossessionSignature))
    (fun (command, sponsor, possession, next, nextPossession) =>
      ⟨command, sponsor, possession, next, nextPossession⟩)
    (by intro ingress; cases ingress; rfl)

/-- v2: v1 plus the next key and its co-signature.  A v1 ingress refuses to
decode (its frame differs). -/
def ingressCodec : LawfulCodec Ingress :=
  framed "DREGG/PARTICIPANT/KEY-ENROLL/SIGNED/v2".toUTF8.toList ingressStream

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

/-- Enrollment allocates a fresh subject's key epoch and key record, and
registers the key version's revocation key in the append-only `registered`
plane: three allocations, each enabled only at an absent address.  The
registration is what makes the key a live signer
(`CredentialAuthorityState.keyStanding`).  The operation marker is the
intent's durable nullifier. -/
def Declaration.patch (d : Declaration) : Patch CredentialAuthorityState.layout :=
  [.allocate .subjectKeyEpoch ⟨d.key.subject⟩ d.key.keyEpoch,
   .allocate .subjectKey (⟨d.key.subject⟩, d.key.keyEpoch) d.key,
   .allocate .registered (CredentialAuthorityState.signingKeyRevocation d.key) ()]

structure Mode {M : Materializer} (pre : Cell M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root
  subjectAbsent : (show Option Epoch from pre.logical ⟨.subjectKeyEpoch, ⟨d.key.subject⟩⟩) = none
  keyAbsent : (show Option KeyRecord from
    pre.logical ⟨.subjectKey, (⟨d.key.subject⟩, d.key.keyEpoch)⟩) = none
  keyUnregistered : isRegistered pre (CredentialAuthorityState.signingKeyRevocation d.key) = false

/-- The key record stored at one authority address satisfies `check`; every
other address passes. -/
def keyAt (logical : Store CredentialAuthorityState.layout) (check : KeyRecord → Bool) :
    Address CredentialAuthorityState.layout → Bool
  | ⟨.subjectKey, key⟩ =>
      match logical ⟨.subjectKey, key⟩ with
      | some record => check (show KeyRecord from record)
      | none => true
  | _ => true

/-- Every stored key record satisfies `check`: a scan of the one cell's support. -/
def allKeys (logical : Store CredentialAuthorityState.layout) (check : KeyRecord → Bool) : Bool :=
  decide (∀ address ∈ logical.support, keyAt logical check address = true)

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
    SemanticEffectFamily CredentialAuthorityState.layout AuthorityMaterializer Nat where
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

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | factoryUnavailable | staleAuthority
  | subjectExists | keyIdExists | publicKeyExists | keyVersionRegistered | malformedKey | replayedMarker
  | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  | possession (reason : CredentialSignatureIO.Error) | invalidPossession
  | nextPossession (reason : CredentialSignatureIO.Error)
  | nextKey (reason : KeyPreRotation.EnrollReject)
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
  candidate : Candidate (family deployment authority.snapshot profile.semantics ambient command)
    authority.snapshot.cell (declaration authority.snapshot.domain profile.semantics command) ()
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨deployment.factoryId⟩
      (authority.snapshot.authState.policyRevision ⟨deployment.factoryId⟩))
  subjectFresh : allKeys authority.snapshot.logical (fun key => key.subject != command.key.subject) = true
  keyIdFresh : allKeys authority.snapshot.logical (fun key => key.keyId != command.key.keyId) = true
  publicKeyFresh : allKeys authority.snapshot.logical
    (fun key => key.publicKey != command.key.publicKey) = true
  keyShape : command.key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
    command.key.publicKey.length = 32 ∧
    command.key.activeFrom ≤ authority.snapshot.revision + 1 ∧
    authority.snapshot.revision + 1 ≤ command.key.activeUntil ∧
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
    if subjectAbsent : (show Option Epoch from
        snapshot.logical ⟨.subjectKeyEpoch, ⟨command.key.subject⟩⟩) = none then
      if keyAbsent : (show Option KeyRecord from
          snapshot.logical ⟨.subjectKey, (⟨command.key.subject⟩, command.key.keyEpoch)⟩) = none then
        if subjectFresh : allKeys snapshot.logical (fun key => key.subject != command.key.subject) then
          if keyIdFresh : allKeys snapshot.logical (fun key => key.keyId != command.key.keyId) then
            if publicKeyFresh : allKeys snapshot.logical
                (fun key => key.publicKey != command.key.publicKey) then
              if keyShape : command.key.algorithm = CredentialSignatureAdmission.ed25519Algorithm ∧
                  command.key.publicKey.length = 32 ∧
                  command.key.activeFrom ≤ snapshot.revision + 1 ∧
                  snapshot.revision + 1 ≤ command.key.activeUntil ∧
                  command.key.subject ≠ command.sponsor.value then
               if keyUnregistered : isRegistered snapshot.cell
                   (CredentialAuthorityState.signingKeyRevocation command.key) = false then
                if snapshot.spent d.operationNullifier = false then
                  match validate AuthorityMaterializer snapshot.cell snapshot.cell.root d.patch with
                  | .rejected _ => throw .validation
                  | .accepted validated =>
                      let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                        snapshot.domain directory.directory
                        (snapshot.authState.policyAddress ⟨deployment.factoryId⟩
                          (snapshot.authState.policyRevision ⟨deployment.factoryId⟩)))
                      let candidate : Candidate (family deployment snapshot profile.semantics ambient command)
                          snapshot.cell d () :=
                        { preStateBound := rfl
                          modeEvidence := ⟨rootExact, subjectAbsent, keyAbsent, keyUnregistered⟩
                          validated := validated
                          postcondition := validated.resultAt }
                      pure ⟨directory, authority, factory, candidate, source,
                        subjectFresh, keyIdFresh, publicKeyFresh, keyShape⟩
                else throw .replayedMarker
               else throw .keyVersionRegistered
              else throw .malformedKey
            else throw .publicKeyExists
          else throw .keyIdExists
        else throw .subjectExists
      else throw .subjectExists
    else throw .subjectExists
  else throw .staleAuthority

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

/-- The authority cell after enrollment: the validated patch applied to the
loaded cell. It is the one authority write. -/
def Prepared.authorityPost (prepared : Prepared deployment profile ambient durable command) :
    CredentialAuthorityDomain.Cell :=
  prepared.candidate.validated.apply

def project (prepared : Prepared deployment profile ambient durable command)
    (logical : Store CredentialAuthorityState.layout) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory deployment.factoryId ++
    CanonicalRuntimeProfile.requestSlots
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

/-- The actual management target supplies current ambient and kind restrictions. -/
def kindDependencies (prepared : Prepared deployment profile ambient durable command) :
    Option WorldKindLawDependencies.Dependencies :=
  WorldKindLawDependencies.loadTarget deployment prepared.directory.directory deployment.factoryId

def policyConfig [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command) : ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile prepared.authority.snapshot
    prepared.directory.directory
    (sourceCapabilityPortal prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared) deployment.factoryId
    ((kindDependencies prepared).map (·.additional) |>.getD [])

def lawReadGuards (prepared : Prepared deployment profile ambient durable command) :
    Option (List (Nat × Digest)) := do
  let structural ← kindDependencies prepared
  let sources ← PhysicalLawResolution.readGuards prepared.authority.snapshot
    prepared.directory.directory profile.semantics deployment.factoryId structural.additional
  pure (sources ++ structural.readGuards)

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
  let _ ← requireSome .policyUnavailable (kindDependencies prepared)
  let evidence ← requireSome .capabilityRejected
    (config.capabilityEvidenceChecked wanted command.control () receipt () (fun _ => ())).toOption
  let law ← requireSome .policyUnavailable config.resolve?
  let witness := law.witness
  if inputsInRange profile.compilerProfile.compiler law.predicate
      (step prepared).oldState (step prepared).newState != true then
    throw .policyInputRange
  if !decide (castInjOn F
      (intsOf law.predicate (step prepared).oldState (step prepared).newState)) then
    throw .policyCastAlias
  match ComposedPolicyAdmission.admit config wanted
      evidence witness (.policy wanted.policyId wanted.policyRevision) rfl rfl with
  | none => .error .policyRejected
  | some authorization =>
      .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)

/-- The signature oracle of the one presented next-possession signature: it
vouches for the presented next key exactly when the native verifier accepted
it there, and for no other key. -/
def presentedNext (nextPublicKey : List UInt8) (verified : Bool) : List UInt8 → Bool :=
  fun publicKey => decide (publicKey = nextPublicKey) && verified

structure Accepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope
  semantic : prepared.SemanticAccepted
  possessionVerified : Bool
  possessionTrue : possessionVerified = true
  nextVerified : Bool
  nextGated : KeyPreRotation.enrollGate nextKeyDigest command.key ingress.ingress.nextPublicKey
    (presentedNext ingress.ingress.nextPublicKey nextVerified) = .ok ()

/-- The native verdict on the next-possession signature: `false` (and no call)
when no next key is presented. -/
def verifyNext (native : CredentialSignatureIO.NativeConfig) (command : Command)
    (ingress : DecodedIngress) : IO (Except CredentialSignatureIO.Error Bool) :=
  if ingress.ingress.nextPublicKey = [] then pure (.ok false)
  else CredentialSignatureIO.verify native ingress.ingress.nextPublicKey
    (nextPossessionFrame command.key.publicKey ingress.ingress.nextPublicKey)
    ingress.ingress.nextPossessionSignature

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
              if yes : verified = true then
                match ← verifyNext native command ingress with
                | .error reason => return .error (.nextPossession reason)
                | .ok nextVerified =>
                  match gated : KeyPreRotation.enrollGate nextKeyDigest command.key
                      ingress.ingress.nextPublicKey
                      (presentedNext ingress.ingress.nextPublicKey nextVerified) with
                  | .error reason => return .error (.nextKey reason)
                  | .ok () => return .ok ⟨receipt, same, semantic, verified, yes, nextVerified, gated⟩
              else return .error .invalidPossession
      else return .error .capabilityRejected

/-- **An admitted enrollment that commits to a next key carried that key,
and that key signed** (`enroll_requires_next_key_possession`, at the host's
own oracle). -/
theorem Accepted.nextPossession [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command}
    {ingress : DecodedIngress} (accepted : Accepted prepared ingress) {committed : Digest}
    (precommitted : command.key.nextKeyDigest = some committed) :
    nextKeyDigest ingress.ingress.nextPublicKey = committed ∧ accepted.nextVerified = true := by
  have facts := KeyPreRotation.enroll_requires_next_key_possession accepted.nextGated precommitted
  refine ⟨facts.1, ?_⟩
  simpa [presentedNext] using facts.2

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
