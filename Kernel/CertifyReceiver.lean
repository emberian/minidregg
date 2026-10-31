/-
# Kernel.CertifyReceiver — the operator certifies the head: the checkpoint path

A certify record asserts that the head at height `n` (the record count before
it) with log-chain value `c` is vouched for, and writes the system cell's
`certified := (n, c)` (`SystemCell.certifyNext`).  It is admitted exactly when:
* the sponsor presents the deployment's factory control capability (verb
  `installPolicy`), admitted in capability mode under the factory's current law
  with the operation slot `authority/operation/certify` — the authority shape of
  the clock tick and PAY's book receiver, so the factory law decides WHICH
  certifiers may certify (today the operator; a witness
  quorum's certificate is not built);
* the command pins the current factory, authority and system roots;
* the command names a prefix of the log that the durable chain log holds
  (`heightUnavailable`) at that prefix's chain value (`chainMismatch`), past the
  certified height (`notAdvancing`) — `Kernel.ChainHistory.certifiable`, the one
  rule the tail gate also calls; `certified_advances`, `certified_true`. A
  certifier names the head it observed; records landing before its submission
  no longer refuse it;
* its single-use marker (sponsor, nonce) is unspent.

The kernel's tail rule (`Kernel.TailBound.gate`) judges the same write again at
the durable boundary: whatever produced it, a write to the system cell must be
exactly `certifyNext` of a held prefix and its chain.  A certify record is the
one record the tail bound exempts, so certification can always follow a full
tail.

The patch is one guarded write of the system value from the exact loaded value;
the record writes only the system cell (`intent_writes_system_cell`).
-/
module

public import Compiler.DurableReceiverIO
public import Kernel.CapabilityRevocationController
public import Kernel.SystemCellDomain

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Kernel.CertifyReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.SystemCell
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.CredentialAuthorityEffects
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := DurableReceiverIO.Loaded ResourceBirthCodec.rootBytes
abbrev Snapshot := CredentialAuthorityDomain.Snapshot

/-! ## The pure decision -/

/-- A decided certify: the system value it replaces and the value it installs. -/
structure Plan where
  current : System
  next : System
  deriving DecidableEq, Repr

def Plan.patch (plan : Plan) : Patch SystemCell.layout := certifyPatch plan.current plan.next

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | factoryUnavailable
  | systemUnavailable | staleAuthority | staleSystem | heightUnavailable | chainMismatch | notAdvancing
  | replayedMarker | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving DecidableEq, Repr

/-- The whole rule of certification, on the loaded system value and the log's chain
history: `Kernel.ChainHistory.certifiable`, its refusals named as the receiver's. -/
def decideCertify {H : Type} [ChainHistory H] (current : System) (history : H) (height : Nat)
    (digest : Digest) : Except Reject Plan :=
  match ChainHistory.certifiable current.certifiedHeight history height digest with
  | .ok () => .ok ⟨current, certifyNext current height digest⟩
  | .error .notAdvancing => .error .notAdvancing
  | .error .heightUnavailable => .error .heightUnavailable
  | .error .chainMismatch => .error .chainMismatch

theorem decideCertify_ok {H : Type} [ChainHistory H] {current : System} {history : H}
    {height : Nat} {digest : Digest} {plan : Plan}
    (decided : decideCertify current history height digest = .ok plan) :
    plan = ⟨current, certifyNext current height digest⟩ ∧ current.certifiedHeight < height ∧
      ChainHistory.chainAt history height = some digest := by
  unfold decideCertify at decided
  split at decided
  · rename_i certified
    cases decided
    exact ⟨rfl, (ChainHistory.certifiable_ok_iff _ _ _ _).mp certified⟩
  all_goals cases decided

/-- Refuting pole: a certify at or below the certified height is refused. -/
theorem certify_not_advancing_refused {H : Type} [ChainHistory H] (current : System) (history : H)
    (height : Nat) (digest : Digest) (behind : height ≤ current.certifiedHeight) :
    decideCertify current history height digest = .error .notAdvancing := by
  unfold decideCertify
  rw [ChainHistory.at_or_below_certified_refused _ _ _ _ behind]

/-- Refuting pole: a certify of a height the history does not hold (past the head) is refused. -/
theorem certify_unheld_refused {H : Type} [ChainHistory H] (current : System) (history : H)
    (height : Nat) (digest : Digest) (advancing : current.certifiedHeight < height)
    (unheld : ChainHistory.chainAt history height = none) :
    decideCertify current history height digest = .error .heightUnavailable := by
  unfold decideCertify
  rw [ChainHistory.unheld_refused _ _ _ _ advancing unheld]

/-- Refuting pole: a certify naming another chain value than the held one is refused. -/
theorem certify_other_chain_refused {H : Type} [ChainHistory H] (current : System) (history : H)
    (height : Nat) (digest chain : Digest) (advancing : current.certifiedHeight < height)
    (held : ChainHistory.chainAt history height = some chain) (other : digest ≠ chain) :
    decideCertify current history height digest = .error .chainMismatch := by
  unfold decideCertify
  rw [ChainHistory.other_chain_refused _ _ _ _ _ advancing held other]

/-- The certify patch installs exactly the next value. -/
theorem certify_installs (store : SystemStore) (plan : Plan) :
    SystemCell.systemOf (Patch.run store plan.patch) = some plan.next := by
  simp [Plan.patch, certifyPatch, Patch.run, Op.apply, SystemCell.systemOf, SystemCell.systemAddress,
    Store.set]

/-! ## Command and ingress -/

structure Command where
  sponsor : SubjectId
  control : CapabilityId
  nonce : Nat
  expectedFactoryRoot : Digest
  expectedAuthorityRoot : Digest
  expectedSystemRoot : Digest
  height : Nat
  digest : Digest
  deriving DecidableEq, Repr

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product digestStream
                (StreamCodec.product StreamCodec.nat digestStream)))))))
    (fun c => (c.sponsor, c.control, c.nonce, c.expectedFactoryRoot, c.expectedAuthorityRoot,
      c.expectedSystemRoot, c.height, c.digest))
    (fun (sponsor, control, nonce, factoryRoot, authorityRoot, systemRoot, height, digest) =>
      ⟨sponsor, control, nonce, factoryRoot, authorityRoot, systemRoot, height, digest⟩)
    (by intro c; cases c; rfl)

/-- `frame`, checked, then one value: the top-level codec of `StreamCodec.framed`,
canonical by construction (`framed_canonical`), so decoding never re-encodes. -/
def framed {A : Type} (frame : List UInt8) (stream : StreamCodec A) : LawfulCodec A :=
  (StreamCodec.framed frame stream).toLawful

theorem framed_canonical {A : Type} (frame : List UInt8) (stream : StreamCodec A)
    {bytes : List UInt8} {value : A}
    (decoded : (framed frame stream).decode bytes = some value) :
    (framed frame stream).encode value = bytes :=
  (StreamCodec.framed frame stream).toLawful_canonical bytes value decoded

def commandFrame : List UInt8 := "DREGG/CERTIFY/v1".toUTF8.toList

def commandCodec : LawfulCodec Command := framed commandFrame commandStream

theorem command_roundtrip (command : Command) :
    commandCodec.decode (commandCodec.encode command) = some command :=
  commandCodec.decode_encode command

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
  framed "DREGG/CERTIFY/SIGNED/v2".toUTF8.toList ingressStream

structure DecodedIngress where
  mk ::
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
    match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode
        ingress.sponsorEnvelope with
    | none => none
    | some envelope =>
      some ⟨ingress, command, framed_canonical commandFrame commandStream commandExact,
        envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.CERTIFY.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.sponsor, command.nonce))).digest.value

/-! ## The effect family over the system cell -/

def planStream : StreamCodec Plan :=
  StreamCodec.xmap (StreamCodec.product systemStream systemStream)
    (fun plan => (plan.current, plan.next))
    (fun (current, next) => ⟨current, next⟩)
    (by intro plan; cases plan; rfl)

structure Declaration where
  plan : Plan
  expectedPreRoot : Digest
  operationNullifier : Nat

def declarationStream : StreamCodec Declaration :=
  StreamCodec.xmap (StreamCodec.product planStream (StreamCodec.product digestStream StreamCodec.nat))
    (fun d => (d.plan, d.expectedPreRoot, d.operationNullifier))
    (fun (plan, root, nullifier) => ⟨plan, root, nullifier⟩)
    (by intro d; cases d; rfl)

def declarationCodec : LawfulCodec Declaration :=
  declarationStream.toLawful

def declaration (domain semantics : Digest) (command : Command) (plan : Plan) : Declaration :=
  ⟨plan, command.expectedSystemRoot, marker domain semantics command⟩

structure Mode {M : Materializer SystemCell.layout Digest} (pre : Materialized M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.CERTIFY.EFFECT/v1".toUTF8.toList
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
    (Sp800185Cshake256.hash "DREGG.CERTIFY.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

def request (deployment : Deployment) (snapshot : Snapshot) (system : SystemCell.Cell) (semantics : Digest)
    (ambient : Ambient) (command : Command) (plan : Plan) : Request .program :=
  ((context deployment snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) system.root
    (marker snapshot.domain semantics command)
    (declaration snapshot.domain semantics command plan)).2

def family (deployment : Deployment) (snapshot : Snapshot) (system : SystemCell.Cell) (semantics : Digest)
    (ambient : Ambient) (command : Command) :
    SemanticEffectFamily SystemCell.layout SystemCell.materializer Nat where
  Declaration := Declaration
  declarationCodec := declarationCodec
  pre := system
  request := fun d => (context deployment snapshot semantics ambient command).request
    declarationCodec (effectDigest snapshot.domain semantics command) system.root
    d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun d _ => Mode system d
  Postcondition := fun d _ post => d.plan.patch.ResultAt system.logical post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun d _ => d.plan.patch
  nullifier := fun d _ => some d.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

/-! ## Preparation -/

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  factory : ResourceTargetAdmission.Observed deployment directory.directory .object
    deployment.factoryId command.expectedFactoryRoot
  system : SystemCellDomain.Loaded deployment durable.snapshot
  plan : Plan
  decided : decideCertify system.system durable command.height command.digest = .ok plan
  candidate : Candidate (family deployment authority.snapshot system.cell profile.semantics ambient command)
    system.cell (declaration authority.snapshot.domain profile.semantics command plan) ()
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
  let system ← requireSome .systemUnavailable (SystemCellDomain.load deployment durable.snapshot)
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot = snapshot.cell.root then
    if rootExact : command.expectedSystemRoot = system.cell.root then
      match decided : decideCertify system.system durable command.height command.digest with
      | .error reason => throw reason
      | .ok plan =>
        let d := declaration snapshot.domain profile.semantics command plan
        if snapshot.spent d.operationNullifier = false then
          match validate SystemCell.materializer system.cell system.cell.root d.plan.patch with
          | .rejected _ => throw .validation
          | .accepted validated =>
              let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                snapshot.domain directory.directory
                (snapshot.authState.policyAddress ⟨deployment.factoryId⟩
                  (snapshot.authState.policyRevision ⟨deployment.factoryId⟩)))
              let candidate : Candidate (family deployment snapshot system.cell profile.semantics ambient command)
                  system.cell d () :=
                { preStateBound := rfl
                  modeEvidence := ⟨rootExact⟩
                  validated := validated
                  postcondition := validated.resultAt }
              pure ⟨directory, authority, factory, system, plan, decided, candidate, source⟩
        else throw .replayedMarker
    else throw .staleSystem
  else throw .staleAuthority

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

/-- The system cell after the certify: the validated patch applied to the loaded cell. -/
def Prepared.systemPost (prepared : Prepared deployment profile ambient durable command) : SystemCell.Cell :=
  prepared.candidate.validated.apply

/-- **`certified_advances`.**  A prepared certify installs exactly the
certification of the prefix it names at the chain value it names, that prefix is
past the certified height the snapshot holds, and the durable chain log holds it
at that value. -/
theorem certified_advances (prepared : Prepared deployment profile ambient durable command) :
    systemOf prepared.systemPost.logical =
        some (certifyNext prepared.system.system command.height command.digest) ∧
      prepared.system.system.certifiedHeight < command.height ∧
      ChainHistory.chainAt durable command.height = some command.digest := by
  obtain ⟨planExact, advancing, held⟩ := decideCertify_ok prepared.decided
  refine ⟨?_, advancing, held⟩
  have installs := certify_installs prepared.system.cell.logical prepared.plan
  simp only [Prepared.systemPost, ValidatedPatch.apply_logical]
  show SystemCell.systemOf (Patch.run prepared.system.cell.logical prepared.plan.patch) = _
  rw [installs, planExact]

/-- **`certified_true`.**  What a prepared certify vouches for is true of the log: its
height is at or below the head, and its digest is the chain after exactly that many
accepted records (`Loaded.faithful`). -/
theorem certified_true (prepared : Prepared deployment profile ambient durable command) :
    command.height ≤ durable.height ∧
      command.digest = DurableCheckpointCodec.chainAfter durable.logStart (durable.image.accepted.take command.height) := by
  have held := (certified_advances prepared).2.2
  exact ⟨ChainHistory.chainAt_le_head durable command.height command.digest held,
    (DurableReceiverIO.Loaded.faithful durable).sound command.height command.digest held⟩

def project (prepared : Prepared deployment profile ambient durable command)
    (logical : SystemStore) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory deployment.factoryId ++
    CanonicalRuntimeProfile.requestSlots
      (request deployment prepared.authority.snapshot prepared.system.cell profile.semantics ambient command
        prepared.plan) ++
    [("authority/operation/certify", 1)] ++
    SystemCell.slots ((SystemCell.systemOf logical).getD prepared.system.system) (durable.height + 1) ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode command) ++
    DeclaredResourceController.bytesSlots "resource/bytes" 0
      (PackedCell.bytes Registry prepared.factory.before) ++
    ResourceAuthorityProjection.grantSlots "authority/control" .program command.control
      prepared.authority.snapshot.logical⟩

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
    (family deployment prepared.authority.snapshot prepared.system.cell profile.semantics ambient command)
    (request deployment prepared.authority.snapshot prepared.system.cell profile.semantics ambient command
      prepared.plan)
    prepared.system.cell
    (declaration prepared.authority.snapshot.domain profile.semantics command prepared.plan) ()

/-- The capability evidence a certify needs: the sponsor's control capability on
the factory, checked in capability mode against the checked signature. -/
def capabilityEvidence [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :=
  ((policyConfig prepared).capabilityEvidenceChecked (request deployment prepared.authority.snapshot prepared.system.cell profile.semantics
      ambient command prepared.plan)
    command.control () receipt () (fun _ => ())).toOption

def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request deployment prepared.authority.snapshot prepared.system.cell profile.semantics
    ambient command prepared.plan
  let config := policyConfig prepared
  let evidence ← requireSome .capabilityRejected (capabilityEvidence prepared receipt)
  let _ ← requireSome .policyUnavailable (kindDependencies prepared)
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

/-- **`certify_requires_capability`** (refuting pole).  A sponsor whose signed
request carries no admissible control capability on the factory is refused,
whatever head it certifies. -/
theorem certify_requires_capability [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot)
    (none_ : capabilityEvidence prepared receipt = none) :
    authorize prepared receipt = .error .capabilityRejected := by
  unfold authorize
  simp [none_, requireSome, bind, Except.bind]

structure Accepted [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope
  semantic : prepared.SemanticAccepted
theorem Accepted.sound [DecidableEq F]
    {prepared : Prepared deployment profile ambient durable command} {ingress : DecodedIngress}
    (accepted : Accepted prepared ingress) :
    accepted.receipt.envelopeBytes = ingress.ingress.sponsorEnvelope ∧
    ∃ graph : PolicyComponentResolution.LoadedGraph
        (policyConfig prepared).snapshot (policyConfig prepared).store
        (policyConfig prepared).profile.semantics (policyConfig prepared).target
        (policyConfig prepared).additional,
      PolicyComponentResolution.loadTarget (policyConfig prepared).snapshot
        (policyConfig prepared).store (policyConfig prepared).profile.semantics
        (policyConfig prepared).target (policyConfig prepared).resolutionBudget
        (policyConfig prepared).additional = .ok graph ∧
      Minidregg.Pred.eval (ResolvedLawCompilation.predicate graph.resolved)
        (step prepared).oldState (step prepared).newState = true :=
  ⟨accepted.envelopeExact, ComposedPolicyAdmission.authorized_effective_law (policyConfig prepared)
    (request deployment prepared.authority.snapshot prepared.system.cell profile.semantics ambient
      command prepared.plan)
    accepted.semantic.authorization⟩

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request deployment prepared.authority.snapshot prepared.system.cell profile.semantics ambient
        command prepared.plan)
      ingress.ingress.sponsorEnvelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .capabilityRejected

/-- The exact header the sponsor signs, derived from the current system value,
head and authority.  It discloses no decision beyond the current head. -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let some system := SystemCellDomain.load deployment durable.snapshot
    | .error "system cell unavailable"
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    ⟨.program, request deployment authority.snapshot system.cell profile.semantics ambient command
      ⟨system.system, certifyNext system.system command.height command.digest⟩⟩).mapError
      (fun reason => s!"certify signer key: {repr reason}")

/-! ## The receiver -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.CERTIFY.EVENT/v2".toUTF8.toList ingress.bytes).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

def writes (prepared : Prepared deployment profile ambient durable command) : List DataWrite :=
  [prepared.system.write prepared.systemPost]

def resourceGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨deployment.factoryId⟩,
    rootBytes (LifecycleImage.bytes Registry (.live prepared.factory.before))⟩

def policyGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  resourceGuard prepared :: policyGuard prepared ::
    (prepared.authority.readGuards ++
      ((lawReadGuards prepared).getD []).map (fun (cellIdValue, root) => (⟨⟨cellIdValue⟩, root⟩ : Minidregg.Kernel.DurableDataIntent.ReadGuard))).filter fun guard => guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (resourceGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId) ∧
    (lawReadGuards prepared).isSome = true

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound (prepared : Prepared deployment profile ambient durable command)
    (write : DataWrite) (member : write ∈ writes prepared) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, List.mem_singleton] at member
  subst write
  exact prepared.system.write_root_bound _

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_cons.mp member with rfl | rest
  · exact shape.2.2.2.1
  · rcases List.mem_cons.mp rest with rfl | authority
    · exact shape.2.2.2.2.1
    · simpa using (List.mem_filter.mp authority).2

structure AcceptedCertify [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  accepted : CertifyReceiver.Accepted prepared ingress
  physical : PhysicalShape prepared
theorem AcceptedCertify.sound [DecidableEq F] {ingress : DecodedIngress}
    (accepted : AcceptedCertify deployment profile ambient durable ingress) :
    accepted.accepted.receipt.envelopeBytes = ingress.ingress.sponsorEnvelope ∧
    systemOf accepted.prepared.systemPost.logical =
      some (certifyNext accepted.prepared.system.system ingress.command.height ingress.command.digest) ∧
    ingress.command.height ≤ durable.height ∧
    ingress.command.digest =
      DurableCheckpointCodec.chainAfter durable.logStart (durable.image.accepted.take ingress.command.height) ∧
    PhysicalShape accepted.prepared :=
  ⟨accepted.accepted.envelopeExact, (certified_advances accepted.prepared).1,
    (certified_true accepted.prepared).1, (certified_true accepted.prepared).2,
    accepted.physical⟩

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedCertify deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def charge (accepted : AcceptedCertify deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => DeployedCharge.storageCharge durable.snapshot
      (writes accepted.prepared)
      (event deployment.domain profile.semantics ingress)
  | .witnessBytes => ingress.ingress.sponsorEnvelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedCertify deployment profile ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some ingress.command.sponsor
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain profile.semantics ingress]
  exactCharge := (Minidregg.Theory.ResourceCost.Charge.materialize (charge accepted)).toCharge
  event := event deployment.domain profile.semantics ingress
  postRootsBound := writes_roots_bound accepted.prepared
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

/-- The one cell an accepted certify writes is the system cell. -/
theorem intent_writes_system_cell (accepted : AcceptedCertify deployment profile ambient durable ingress) :
    (intent accepted).writes.map DataWrite.cellId = [SystemCellDomain.cellIdOf deployment] := rfl

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (domain semantics : Digest) (ingress : DecodedIngress) : Receipt :=
  ⟨transactionId domain semantics ingress, (event domain semantics ingress).eventId⟩

def replay (domain semantics : Digest) (durable : Durable) (ingress : DecodedIngress) :
    Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics ingress) durable.snapshot.model.journal with
  | none => none
  | some recorded =>
    if recorded.transactionId = transactionId domain semantics ingress ∧
        recorded.event.event = event domain semantics ingress ∧
        recorded.nullifiers = [nullifier domain semantics ingress] then
      some (.ok (receipt domain semantics ingress))
    else some (.error ())

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | transactionConflict
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveLoaded (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable)
    (bytes : List UInt8) : IO Result := do
  let some ingress := decodeIngress bytes
    | return .rejected .malformedIngress
  match replay deployment.domain profile.semantics durable ingress with
  | some (.ok prior) => return .confirmed .replayed prior
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment profile ambient durable native ingress with
    | .error reason => return .rejected reason
    | .ok accepted =>
      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
      | .confirmed kind _ =>
          return .confirmed kind (receipt deployment.domain profile.semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

/-! ## Signing plan and public view -/

/-- What the signer signs: the exact source-derived header over the command. -/
structure SigningPlan where
  domain : Digest
  semantics : Digest
  commandBytes : List UInt8
  header : List UInt8
  deriving DecidableEq, Repr

def signingPlanStream : StreamCodec SigningPlan :=
  StreamCodec.xmap (StreamCodec.product digestStream
    (StreamCodec.product digestStream (StreamCodec.product bytesStream bytesStream)))
    (fun plan => (plan.domain, plan.semantics, plan.commandBytes, plan.header))
    (fun (domain, semantics, command, header) => ⟨domain, semantics, command, header⟩)
    (by intro plan; cases plan; rfl)

def signingPlanCodec : LawfulCodec SigningPlan :=
  framed "DREGG/CERTIFY/PLAN/v1".toUTF8.toList signingPlanStream

def viewStream : StreamCodec SystemCellDomain.View :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream (StreamCodec.product systemStream
        (StreamCodec.product StreamCodec.nat digestStream)))))
    (fun view => (view.systemRoot, view.authorityRoot, view.factoryRoot, view.system, view.head,
      view.chain))
    (fun (systemRoot, authorityRoot, factoryRoot, system, head, chain) =>
      ⟨systemRoot, authorityRoot, factoryRoot, system, head, chain⟩)
    (by intro view; cases view; rfl)

def viewCodec : LawfulCodec SystemCellDomain.View :=
  framed "DREGG/CERTIFY/VIEW/v1".toUTF8.toList viewStream

#assert_axioms certified_advances certified_true certify_not_advancing_refused
  certify_unheld_refused certify_other_chain_refused certify_installs certify_requires_capability
  command_roundtrip decideCertify_ok AcceptedCertify.sound

end Minidregg.Kernel.CertifyReceiver
