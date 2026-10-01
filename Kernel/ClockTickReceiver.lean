/-
# Kernel.ClockTickReceiver — an authorised observer advances the one clock

A tick asserts a new clock value `{now, slot}`.  It is admitted exactly when:
* the sponsor presents the deployment's factory control capability (verb
  `installPolicy`), admitted in capability mode under the factory's current law
  with the operation slot `authority/operation/clock-tick` — the same authority
  shape as key enrollment and PAY's book receiver, so the factory law decides
  WHICH observers may tick (the operator's wall-clock ticker, PAY's chain
  observer);
* the command pins the current factory, authority and clock roots;
* the tick `advances` the loaded clock: `now` strictly increases and `slot`
  does not decrease (`clock_monotone`; a tick behind or at the current time is
  refused, `tick_behind_refused`);
* its single-use marker (sponsor, nonce) is unspent; it is the intent's durable
  nullifier.

The patch is one guarded write of the clock value from the exact loaded value;
the record writes only the clock cell (`intent_writes_clock_cell`).
-/
import Kernel.CapabilityRevocationController
import Kernel.ClockCellDomain

namespace Minidregg.Kernel.ClockTickReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ClockCell
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

/-- A decided tick: the clock it replaces and the clock it installs. -/
structure Plan where
  current : Clock
  next : Clock
  deriving DecidableEq, Repr

def Plan.patch (plan : Plan) : Patch ClockCell.layout := tickPatch plan.current plan.next

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | factoryUnavailable
  | clockUnavailable | staleAuthority | staleClock | clockNotAdvancing
  | replayedMarker | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving DecidableEq, Repr

/-- The whole rule of time, on the loaded clock. -/
def decideTick (current next : Clock) : Except Reject Plan :=
  if advances current next then .ok ⟨current, next⟩ else .error .clockNotAdvancing

theorem decideTick_ok {current next : Clock} {plan : Plan}
    (decided : decideTick current next = .ok plan) :
    plan = ⟨current, next⟩ ∧ current.now < next.now ∧ current.slot ≤ next.slot := by
  unfold decideTick at decided
  split at decided
  · rename_i advancing
    cases decided
    exact ⟨rfl, (advances_iff current next).mp advancing⟩
  · cases decided

/-- Refuting pole of time: a tick at or behind the current `now` is refused. -/
theorem tick_behind_refused (current next : Clock) (behind : next.now ≤ current.now) :
    decideTick current next = .error .clockNotAdvancing := by
  unfold decideTick
  have : advances current next = false := by
    cases h : advances current next
    · rfl
    · exact absurd ((advances_iff current next).mp h).1 (Nat.not_lt.mpr behind)
  simp [this]

/-- Refuting pole of the slot: a tick taking the chain slot back is refused. -/
theorem slot_back_refused (current next : Clock) (back : next.slot < current.slot) :
    decideTick current next = .error .clockNotAdvancing := by
  unfold decideTick
  have : advances current next = false := by
    cases h : advances current next
    · rfl
    · exact absurd ((advances_iff current next).mp h).2 (Nat.not_le.mpr back)
  simp [this]

/-- The tick's patch installs exactly the next clock. -/
theorem tick_installs (store : ClockStore) (plan : Plan) :
    ClockCell.clockOf (Patch.run store plan.patch) = some plan.next := by
  simp [Plan.patch, tickPatch, Patch.run, Op.apply, ClockCell.clockOf, ClockCell.clockAddress,
    Store.set] <;> rfl

/-! ## Command and ingress -/

structure Command where
  sponsor : SubjectId
  control : CapabilityId
  nonce : Nat
  expectedFactoryRoot : Digest
  expectedAuthorityRoot : Digest
  expectedClockRoot : Digest
  now : Nat
  slot : Nat
  deriving DecidableEq, Repr

def Command.tick (command : Command) : Clock := ⟨command.now, command.slot⟩

def commandStream : StreamCodec Command :=
  StreamCodec.xmap
    (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
      (StreamCodec.product capabilityIdStream
        (StreamCodec.product StreamCodec.nat
          (StreamCodec.product digestStream
            (StreamCodec.product digestStream
              (StreamCodec.product digestStream
                (StreamCodec.product StreamCodec.nat StreamCodec.nat)))))))
    (fun c => (c.sponsor, c.control, c.nonce, c.expectedFactoryRoot, c.expectedAuthorityRoot,
      c.expectedClockRoot, c.now, c.slot))
    (fun (sponsor, control, nonce, factoryRoot, authorityRoot, clockRoot, now, slot) =>
      ⟨sponsor, control, nonce, factoryRoot, authorityRoot, clockRoot, now, slot⟩)
    (by intro c; cases c; rfl)

def framedRaw {A : Type} (frame : List UInt8) (stream : StreamCodec A) : LawfulCodec A :=
    { encode value := frame ++ stream.encode value
      decode bytes := if bytes.take frame.length = frame then
        stream.toLawful.decode (bytes.drop frame.length) else none
      decode_encode := by
        intro value
        have exact := stream.toLawful.decode_encode value
        change stream.toLawful.decode (stream.encode value) = some value at exact
        simp [exact] }

def framed {A : Type} (frame : List UInt8) (stream : StreamCodec A) : LawfulCodec A :=
  ResourceBirthCodec.strictCodec (framedRaw frame stream)

theorem framed_canonical {A : Type} (frame : List UInt8) (stream : StreamCodec A)
    {bytes : List UInt8} {value : A}
    (decoded : (framed frame stream).decode bytes = some value) :
    (framed frame stream).encode value = bytes :=
  ResourceBirthCodec.strictCodec_canonical (framedRaw frame stream) decoded

def commandFrame : List UInt8 := "DREGG/CLOCK/TICK/v1".toUTF8.toList

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
  framed "DREGG/CLOCK/TICK/SIGNED/v1".toUTF8.toList ingressStream

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
    match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode
        ingress.sponsorEnvelope with
    | none => none
    | some envelope =>
      some ⟨ingress, command, framed_canonical commandFrame commandStream commandExact,
        envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.CLOCK.TICK.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.sponsor, command.nonce))).digest.value

/-! ## The effect family over the clock cell -/

def planStream : StreamCodec Plan :=
  StreamCodec.xmap (StreamCodec.product clockStream clockStream)
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
  ResourceBirthCodec.strictCodec declarationStream.toLawful

def declaration (domain semantics : Digest) (command : Command) (plan : Plan) : Declaration :=
  ⟨plan, command.expectedClockRoot, marker domain semantics command⟩

structure Mode {M : Materializer ClockCell.layout Digest} (pre : Materialized M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.CLOCK.TICK.EFFECT/v1".toUTF8.toList
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
    (Sp800185Cshake256.hash "DREGG.CLOCK.TICK.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

def request (deployment : Deployment) (snapshot : Snapshot) (clock : ClockCell.Cell) (semantics : Digest)
    (ambient : Ambient) (command : Command) (plan : Plan) : Request .program :=
  ((context deployment snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) clock.root
    (marker snapshot.domain semantics command)
    (declaration snapshot.domain semantics command plan)).2

def family (deployment : Deployment) (snapshot : Snapshot) (clock : ClockCell.Cell) (semantics : Digest)
    (ambient : Ambient) (command : Command) :
    SemanticEffectFamily ClockCell.layout ClockCell.materializer Nat where
  Declaration := Declaration
  declarationCodec := declarationCodec
  pre := clock
  request := fun d => (context deployment snapshot semantics ambient command).request
    declarationCodec (effectDigest snapshot.domain semantics command) clock.root
    d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun d _ => Mode clock d
  Postcondition := fun d _ post => d.plan.patch.ResultAt clock.logical post
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
  clock : ClockCellDomain.Loaded deployment durable.snapshot
  plan : Plan
  decided : decideTick clock.clock command.tick = .ok plan
  candidate : Candidate (family deployment authority.snapshot clock.cell profile.semantics ambient command)
    clock.cell (declaration authority.snapshot.domain profile.semantics command plan) ()
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
  let clock ← requireSome .clockUnavailable (ClockCellDomain.load deployment durable.snapshot)
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot = snapshot.cell.root then
    if rootExact : command.expectedClockRoot = clock.cell.root then
      match decided : decideTick clock.clock command.tick with
      | .error reason => throw reason
      | .ok plan =>
        let d := declaration snapshot.domain profile.semantics command plan
        if snapshot.spent d.operationNullifier = false then
          match validate ClockCell.materializer clock.cell clock.cell.root d.plan.patch with
          | .rejected _ => throw .validation
          | .accepted validated =>
              let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                snapshot.domain directory.directory
                (snapshot.authState.policyAddress ⟨deployment.factoryId⟩
                  (snapshot.authState.policyRevision ⟨deployment.factoryId⟩)))
              let candidate : Candidate (family deployment snapshot clock.cell profile.semantics ambient command)
                  clock.cell d () :=
                { preStateBound := rfl
                  modeEvidence := ⟨rootExact⟩
                  validated := validated
                  postcondition := validated.resultAt }
              pure ⟨directory, authority, factory, clock, plan, decided, candidate, source⟩
        else throw .replayedMarker
    else throw .staleClock
  else throw .staleAuthority

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

/-- The clock cell after the tick: the validated patch applied to the loaded cell. -/
def Prepared.clockPost (prepared : Prepared deployment profile ambient durable command) : ClockCell.Cell :=
  prepared.candidate.validated.apply

/-- **`clock_monotone`.**  A prepared tick installs exactly the command's clock,
and that clock is strictly later than, and at no earlier slot than, the clock
the snapshot holds. -/
theorem clock_monotone (prepared : Prepared deployment profile ambient durable command) :
    clockOf prepared.clockPost.logical = some command.tick ∧
      prepared.clock.clock.now < command.now ∧ prepared.clock.clock.slot ≤ command.slot := by
  obtain ⟨planExact, later, notBack⟩ := decideTick_ok prepared.decided
  refine ⟨?_, later, notBack⟩
  have installs := tick_installs prepared.clock.cell.logical prepared.plan
  simp only [Prepared.clockPost, ValidatedPatch.apply_logical]
  show ClockCell.clockOf (Patch.run prepared.clock.cell.logical prepared.plan.patch) = some command.tick
  rw [installs, planExact]

/-- Refuting pole at preparation: no tick at or behind the snapshot's clock
prepares. -/
theorem prepare_behind_refused (prepared : Prepared deployment profile ambient durable command)
    (behind : command.now ≤ prepared.clock.clock.now) : False :=
  absurd (clock_monotone prepared).2.1 (Nat.not_lt.mpr behind)

def project (prepared : Prepared deployment profile ambient durable command)
    (logical : ClockStore) : Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots
      (request deployment prepared.authority.snapshot prepared.clock.cell profile.semantics ambient command
        prepared.plan) ++
    [("authority/operation/clock-tick", 1)] ++
    ClockCell.slots ((ClockCell.clockOf logical).getD prepared.clock.clock) ++
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
    (family deployment prepared.authority.snapshot prepared.clock.cell profile.semantics ambient command)
    (request deployment prepared.authority.snapshot prepared.clock.cell profile.semantics ambient command
      prepared.plan)
    prepared.clock.cell
    (declaration prepared.authority.snapshot.domain profile.semantics command prepared.plan) ()

/-- The capability evidence a tick needs: the sponsor's control capability on
the factory, checked in capability mode against the checked signature. -/
def capabilityEvidence [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :=
  sourceCapabilityOnlyEvidence profile.compilerProfile prepared.authority.snapshot
    (sourceStore prepared)
    (marker prepared.authority.snapshot.domain profile.semantics command) (step prepared)
    (request deployment prepared.authority.snapshot prepared.clock.cell profile.semantics
      ambient command prepared.plan) command.control receipt

def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request deployment prepared.authority.snapshot prepared.clock.cell profile.semantics
    ambient command prepared.plan
  let config := policyConfig prepared
  let evidence ← requireSome .capabilityRejected (capabilityEvidence prepared receipt)
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

/-- **`tick_requires_capability`** (refuting pole).  A sponsor whose signed
request carries no admissible control capability on the factory is refused,
whatever clock it asserts. -/
theorem tick_requires_capability [DecidableEq F]
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

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request deployment prepared.authority.snapshot prepared.clock.cell profile.semantics ambient
        command prepared.plan)
      ingress.ingress.sponsorEnvelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.sponsorEnvelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .capabilityRejected

/-- The exact header the sponsor signs, derived from the current clock and
authority.  It discloses no decision beyond the current clock value. -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let some clock := ClockCellDomain.load deployment durable.snapshot
    | .error "clock cell unavailable"
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    ⟨.program, request deployment authority.snapshot clock.cell profile.semantics ambient command
      ⟨clock.clock, command.tick⟩⟩).mapError
      (fun reason => s!"clock-tick signer key: {repr reason}")

/-! ## The receiver -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.CLOCK.TICK.EVENT/v1".toUTF8.toList ingress.bytes).digest
  canonicalBytes := ingress.bytes

def nullifier (domain semantics : Digest) (ingress : DecodedIngress) : StableNullifier :=
  CredentialAuthorityReplay.nullifier domain (marker domain semantics ingress.command)

def writes (prepared : Prepared deployment profile ambient durable command) : List DataWrite :=
  [prepared.clock.write prepared.clockPost]

def resourceGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨deployment.factoryId⟩,
    rootBytes (LifecycleImage.bytes Registry (.live prepared.factory.before))⟩

def policyGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  resourceGuard prepared :: policyGuard prepared ::
    prepared.authority.readGuards.filter fun guard => guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (resourceGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem writes_roots_bound (prepared : Prepared deployment profile ambient durable command)
    (write : DataWrite) (member : write ∈ writes prepared) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, List.mem_singleton] at member
  subst write
  exact prepared.clock.write_root_bound _

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_cons.mp member with rfl | rest
  · exact shape.2.2.2.1
  · rcases List.mem_cons.mp rest with rfl | authority
    · exact shape.2.2.2.2.1
    · simpa using (List.mem_filter.mp authority).2

structure AcceptedTick [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  accepted : ClockTickReceiver.Accepted prepared ingress
  physical : PhysicalShape prepared

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedTick deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def charge (accepted : AcceptedTick deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.sponsorEnvelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedTick deployment profile ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some ingress.command.sponsor
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := [nullifier deployment.domain profile.semantics ingress]
  exactCharge := charge accepted
  event := event deployment.domain profile.semantics ingress
  postRootsBound := writes_roots_bound accepted.prepared
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

/-- The one cell an accepted tick writes is the clock cell. -/
theorem intent_writes_clock_cell (accepted : AcceptedTick deployment profile ambient durable ingress) :
    (intent accepted).writes.map DataWrite.cellId = [ClockCellDomain.cellIdOf deployment] := rfl

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
  framed "DREGG/CLOCK/PLAN/v1".toUTF8.toList signingPlanStream

def viewStream : StreamCodec ClockCellDomain.View :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product digestStream clockStream)))
    (fun view => (view.clockRoot, view.authorityRoot, view.factoryRoot, view.clock))
    (fun (clockRoot, authorityRoot, factoryRoot, clock) =>
      ⟨clockRoot, authorityRoot, factoryRoot, clock⟩)
    (by intro view; cases view; rfl)

def viewCodec : LawfulCodec ClockCellDomain.View :=
  framed "DREGG/CLOCK/VIEW/v1".toUTF8.toList viewStream

/-- info: 'Minidregg.Kernel.ClockTickReceiver.clock_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms clock_monotone
/-- info: 'Minidregg.Kernel.ClockTickReceiver.tick_behind_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms tick_behind_refused
/-- info: 'Minidregg.Kernel.ClockTickReceiver.slot_back_refused' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms slot_back_refused
/-- info: 'Minidregg.Kernel.ClockTickReceiver.tick_installs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tick_installs
/-- info: 'Minidregg.Kernel.ClockTickReceiver.prepare_behind_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms prepare_behind_refused
/-- info: 'Minidregg.Kernel.ClockTickReceiver.tick_requires_capability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tick_requires_capability
/-- info: 'Minidregg.Kernel.ClockTickReceiver.command_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms command_roundtrip

end Minidregg.Kernel.ClockTickReceiver
