/-
# Kernel.PayObservationReceiver — observed payments become Book credit

One signed report of the enrolled observer (`PayObservation.Command`) is one
turn over two cells:

* the **clock cell** (`Kernel.ClockCell`, the deployment's one clock): its
  `slot` becomes the tip's and its `now` the tip's block time when that is
  later (`Plan.nextClock`, a guarded write at the clock's exact pre-root);
* the **pay cell** is read, not written: tariff, book and assignment, pinned
  at its exact pre-root `expectedPayRoot` (a read guard);
* the **Book**: one issuer mint `.mint tariff.asset payer (creditFor amount)`
  per observation, as a `Batch` decided by `Batch.Admission` at the Book's
  loaded state (`AcceptedBatch.ofAdmission`, as resource birth does).

Authorization: the observer signs a capability-mode request of kind `program`,
target and policy the pay cell (`PayCell.physicalId`), verb `observePayment`,
presenting its capability; it is admitted under the pay cell's current law
(genesis installs `eq request/subject observer`, `NativeHostGenesis`), with the
operation slot `authority/operation/pay-observe`.  The effect digest commits
to the command bytes and to the decided plan, so the authorized request binds
every credit.

The intent's nullifiers are the observations' `"soltx:" ‖ signature ‖ address`
nullifiers followed by the tip's tick nullifier: the durable preflight refuses a
second credit for the same transfer and a second report at the same tip slot
(`PayObservationProofs.second_credit_refused`).  A duplicate transfer inside
one report is refused before that (`duplicateInBatch`).
-/
import Kernel.CapabilityRevocationController
import Kernel.ResourceBirthController
import Kernel.PayObservation
import Kernel.ClockCellDomain

namespace Minidregg.Kernel.PayObservationReceiver

open Minidregg.Compiler
open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityDomainReceiver
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.CredentialAuthorityEntryCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.PayObservation
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
abbrev BookCell (deployment : Deployment) (directory : Directory Nat Registry) :=
  ResourceBirthController.Concrete.ObservedCell deployment directory deployment.resourceBookId
    .resourceBook

/-! ## Decoded ingress -/

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  command : Command
  canonical : commandCodec.encode command = ingress.commandBytes
  envelope : CredentialSignedEnvelopeController.SignedEnvelope
  envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode ingress.envelope =
    some envelope

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match commandExact : commandCodec.decode ingress.commandBytes with
  | none => none
  | some command =>
    match envelopeExact : CredentialSignatureAdmission.canonicalEnvelopeCodec.decode
        ingress.envelope with
    | none => none
    | some envelope =>
      some ⟨ingress, command, command_canonical commandExact, envelope, envelopeExact⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

def marker (domain semantics : Digest) (command : Command) : Nat :=
  (Sp800185Cshake256.hash "DREGG.PAY.OBSERVATION.IDENTITY/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product TypedAuthorizationRequestCodec.subjectIdStream
        StreamCodec.nat))).encode
      (domain, semantics, command.observer, command.nonce))).digest.value

/-! ## The effect family over the pay cell -/

def creditStream : StreamCodec Credit :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    (fun c => (c.index, c.payer, c.amount, c.credit))
    (fun (index, payer, amount, credit) => ⟨index, payer, amount, credit⟩)
    (by intro c; cases c; rfl)

def planStream : StreamCodec Plan :=
  StreamCodec.xmap
    (StreamCodec.product tariffStream
      (StreamCodec.product ClockCell.clockStream
        (StreamCodec.product chainTipStream (StreamCodec.list creditStream))))
    (fun plan => (plan.tariff, plan.clock, plan.tip, plan.credits))
    (fun (tariff, clock, tip, credits) => ⟨tariff, clock, tip, credits⟩)
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
  ⟨plan, command.expectedPayRoot, marker domain semantics command⟩

structure Mode {M : Materializer PayCell.layout Digest} (pre : Materialized M) (d : Declaration) : Type where
  rootExact : d.expectedPreRoot = pre.root

def effectDigest (domain semantics : Digest) (command : Command) (d : Declaration) : Digest :=
  (Sp800185Cshake256.hash "DREGG.PAY.OBSERVATION.EFFECT/v1".toUTF8.toList
    ((StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product bytesStream bytesStream))).encode
      (domain, semantics, commandCodec.encode command, declarationCodec.encode d))).digest

structure Ambient where
  federation : FederationId
  height : Height

/-- The pay cell as a program resource: its identifier is its policy. -/
def payTarget (deployment : Deployment) : Nat := PayCell.physicalId deployment.domain

def context (deployment : Deployment) (snapshot : Snapshot) (semantics : Digest)
    (ambient : Ambient) (command : Command) : RequestContext where
  authority :=
    { kind := .program
      domain := snapshot.domain
      semantics := semantics
      federation := ambient.federation
      subject := command.observer
      subjectKeyEpoch := snapshot.authState.subjectKeyEpoch command.observer
      target := ⟨payTarget deployment⟩
      verb := .observePayment
      nonce := marker snapshot.domain semantics command
      height := ambient.height
      policyId := ⟨payTarget deployment⟩
      policyEpoch := snapshot.authState.policyEpoch ⟨payTarget deployment⟩
      policyRevision := snapshot.authState.policyRevision ⟨payTarget deployment⟩
      cost := (commandCodec.encode command).length }
  argsDigestBytes := fun bytes =>
    (Sp800185Cshake256.hash "DREGG.PAY.OBSERVATION.ARGS/v1".toUTF8.toList
      (commandCodec.encode command ++ bytes)).digest

def request (deployment : Deployment) (snapshot : Snapshot) (pay : PayCell.Cell) (semantics : Digest)
    (ambient : Ambient) (command : Command) (plan : Plan) : Request .program :=
  ((context deployment snapshot semantics ambient command).request declarationCodec
    (effectDigest snapshot.domain semantics command) pay.root
    (marker snapshot.domain semantics command)
    (declaration snapshot.domain semantics command plan)).2

def family (deployment : Deployment) (snapshot : Snapshot) (pay : PayCell.Cell) (semantics : Digest)
    (ambient : Ambient) (command : Command) :
    SemanticEffectFamily PayCell.layout PayCell.materializer Nat where
  Declaration := Declaration
  declarationCodec := declarationCodec
  pre := pay
  request := fun d => (context deployment snapshot semantics ambient command).request
    declarationCodec (effectDigest snapshot.domain semantics command) pay.root
    d.operationNullifier d
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun d _ => Mode pay d
  -- The report writes the clock cell, not the pay cell: the family's own
  -- patch on the pay cell is empty (the pay cell's root is pinned by the mode).
  Postcondition := fun _ _ post => Patch.ResultAt pay.logical ([] : Patch PayCell.layout) post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun _ _ => []
  nullifier := fun d _ => some d.operationNullifier
  Release := fun _ _ => Unit
  DeclassificationAuthority := fun _ _ => Unit
  ReleaseAuthorization := fun _ _ _ => Unit
  DisclosureAllowed := fun _ _ => sealedOnly

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason
  | some value => .ok value

/-- The Book the observed cell holds. -/
def bookOf {deployment : Deployment} {directory : Directory Nat Registry}
    (book : BookCell deployment directory) : CanonicalResourceKernel.Book :=
  CanonicalResourceKernel.logicalBook book.payload.logical

/-! ## Preparation -/

structure Prepared {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  pay : PayCellDomain.Loaded deployment durable.snapshot
  clock : ClockCellDomain.Loaded deployment durable.snapshot
  book : BookCell deployment directory.directory
  plan : Plan
  decided : decideObservations pay.cell.logical clock.clock (bookOf book) command.tip
    command.observations = .ok plan
  clockValid : ValidatedPatch ClockCell.materializer clock.cell clock.cell.root plan.patch
  resources : CanonicalResourceKernel.AcceptedBatch book.payload plan.batch
  candidate : Candidate (family deployment authority.snapshot pay.cell profile.semantics ambient command)
    pay.cell (declaration authority.snapshot.domain profile.semantics command plan) ()
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨payTarget deployment⟩
      (authority.snapshot.authState.policyRevision ⟨payTarget deployment⟩))

/-- The decision, in order: the loaded cells, the two pinned roots, the pure
`decideObservations` (which includes the Book admission), the pay patch's
validation and the pay law's source.  Refusal reasons before the signature
check are named (the enrollment pattern of this branch). -/
def prepare {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) : Except Reject (Prepared deployment profile ambient durable command) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let pay ← requireSome .payUnavailable (PayCellDomain.load deployment durable.snapshot)
  let clock ← requireSome .clockUnavailable (ClockCellDomain.load deployment durable.snapshot)
  let book ← requireSome .bookUnavailable
    (ResourceBirthController.Concrete.observeCell deployment directory.directory
      deployment.resourceBookId .resourceBook)
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot = snapshot.cell.root then
    if rootExact : command.expectedPayRoot = pay.cell.root then
      match decided : decideObservations pay.cell.logical clock.clock (bookOf book) command.tip
          command.observations with
      | .error reason => throw reason
      | .ok plan =>
        let d := declaration snapshot.domain profile.semantics command plan
        match validate ClockCell.materializer clock.cell clock.cell.root plan.patch with
        | .rejected _ => throw .validation
        | .accepted clockValid =>
        match validate PayCell.materializer pay.cell pay.cell.root ([] : Patch PayCell.layout) with
        | .rejected _ => throw .validation
        | .accepted validated =>
            let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
              snapshot.domain directory.directory
              (snapshot.authState.policyAddress ⟨payTarget deployment⟩
                (snapshot.authState.policyRevision ⟨payTarget deployment⟩)))
            let candidate : Candidate (family deployment snapshot pay.cell profile.semantics
                ambient command) pay.cell d () :=
              { preStateBound := rfl
                modeEvidence := ⟨rootExact⟩
                validated := validated
                postcondition := validated.resultAt }
            pure ⟨directory, authority, pay, clock, book, plan, decided, clockValid,
              CanonicalResourceKernel.AcceptedBatch.ofAdmission
                (decideObservations_admitted decided), candidate, source⟩
    else throw .stalePay
  else throw .staleAuthority

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

/-- The clock cell after the report: the validated clock write applied. -/
def Prepared.clockPost (prepared : Prepared deployment profile ambient durable command) : ClockCell.Cell :=
  prepared.clockValid.apply

/-- The Book after the report: the admitted batch applied. -/
def Prepared.bookPost (prepared : Prepared deployment profile ambient durable command) :
    Materialized (CanonicalCellRegistry.materializer .resourceBook) :=
  prepared.resources.post

/-- The prepared Book is exactly the batch applied to the loaded Book. -/
theorem Prepared.bookPost_exact (prepared : Prepared deployment profile ambient durable command) :
    CanonicalResourceKernel.logicalBook prepared.bookPost.logical =
      prepared.plan.batch.apply (bookOf prepared.book) :=
  prepared.resources.post_logicalBook

/-- The prepared clock cell holds the report's next clock: the tip's slot, and
`now` advanced to the tip's block time when that is later. -/
theorem Prepared.clock_post (prepared : Prepared deployment profile ambient durable command) :
    ClockCell.clockOf prepared.clockPost.logical = some prepared.plan.nextClock := by
  change Minidregg.Theory.Store.Patch.run prepared.clock.cell.logical prepared.plan.patch
    ClockCell.clockAddress = some prepared.plan.nextClock
  exact Minidregg.Theory.Store.Store.set_eq _ _ _

/-- The next clock's slot is the report's tip slot. -/
theorem Prepared.clock_post_slot (prepared : Prepared deployment profile ambient durable command) :
    prepared.plan.nextClock.slot = command.tip.slot := by
  show prepared.plan.tip.slot = command.tip.slot
  rw [decideObservations_tip prepared.decided]

def project (prepared : Prepared deployment profile ambient durable command)
    (logical : PayStore) : Minidregg.Pred.State :=
  ⟨CanonicalRuntimeProfile.requestSlots
      (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient
        command prepared.plan) ++
    [("authority/operation/pay-observe", 1),
     ("pay/observations", Int.ofNat command.observations.length),
     ("pay/tip/slot", Int.ofNat command.tip.slot),
     ("pay/clock/slot", Int.ofNat prepared.clock.clock.slot)] ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode command) ++
    ResourceAuthorityProjection.grantSlots "authority/observer" .program command.capability
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
    (family deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command)
    (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command
      prepared.plan)
    prepared.pay.cell
    (declaration prepared.authority.snapshot.domain profile.semantics command prepared.plan) ()

def authorize [DecidableEq F]
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics
    ambient command prepared.plan
  let config := policyConfig prepared
  let evidence ← requireSome .capabilityRejected
    (sourceCapabilityOnlyEvidence profile.compilerProfile prepared.authority.snapshot
      (sourceStore prepared)
      (marker prepared.authority.snapshot.domain profile.semantics command) (step prepared)
      wanted command.capability receipt)
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
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  semantic : prepared.SemanticAccepted

def admitNative [DecidableEq F] (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient
        command prepared.plan)
      ingress.ingress.envelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.envelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .capabilityRejected

/-- The exact header the observer signs.  It is derived from the current pay
cell, Book and authority, and discloses no decision: when the report does not
decide, the header is built over an empty plan at the current tariff and clock
(and submission then refuses with the named reason). -/
def signingHeader (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) :
    Except String CredentialSignedEnvelopeController.SignedHeader := do
  let some authority := loadDeployment deployment durable.snapshot
    | .error "authority unavailable"
  let some pay := PayCellDomain.load deployment durable.snapshot
    | .error "pay cell unavailable"
  let some clock := ClockCellDomain.load deployment durable.snapshot
    | .error "clock cell unavailable"
  let some directory := loadDirectory durable
    | .error "directory unavailable"
  let some book := ResourceBirthController.Concrete.observeCell deployment directory.directory
      deployment.resourceBookId .resourceBook
    | .error "book unavailable"
  let plan : Plan :=
    match decideObservations pay.cell.logical clock.clock (bookOf book) command.tip
        command.observations with
    | .ok plan => plan
    | .error _ =>
        ⟨(tariffOf pay.cell.logical).getD genesisDefault, clock.clock, command.tip, []⟩
  (CredentialSignatureAdmission.signingHeader authority.snapshot
    (marker deployment.domain profile.semantics command)
    ⟨.program, request deployment authority.snapshot pay.cell profile.semantics ambient command
      plan⟩).mapError
      (fun reason => s!"pay-observation signer key: {repr reason}")

/-! ## The receiver -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.PAY.OBSERVATION.EVENT/v1".toUTF8.toList
    ingress.bytes).digest
  canonicalBytes := ingress.bytes

def clockWrite (prepared : Prepared deployment profile ambient durable command) : DataWrite :=
  prepared.clock.write prepared.clockPost

def bookWrite (prepared : Prepared deployment profile ambient durable command) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite deployment.resourceBookId
    ⟨.resourceBook, prepared.book.payload⟩ ⟨.resourceBook, prepared.bookPost⟩

def writes (prepared : Prepared deployment profile ambient durable command) : List DataWrite :=
  [clockWrite prepared, bookWrite prepared]

def policyGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

/-- The pay cell is read (tariff, book, assignment), not written. -/
def payGuard (prepared : Prepared deployment profile ambient durable command) : ReadGuard :=
  prepared.pay.readGuard

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  policyGuard prepared :: payGuard prepared ::
    prepared.authority.readGuards.filter fun guard => guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ writes prepared, rootBytes write.canonicalPostBytes = write.exactPost) ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (payGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_cons.mp member with rfl | rest
  · exact shape.2.2.2.2.1
  rcases List.mem_cons.mp rest with rfl | authority
  · exact shape.2.2.2.2.2.1
  · simpa using (List.mem_filter.mp authority).2

structure AcceptedObservation [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  accepted : PayObservationReceiver.Accepted prepared ingress
  physical : PhysicalShape prepared

def admitDecodedNative [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (native : CredentialSignatureIO.NativeConfig) (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedObservation deployment profile ambient durable ingress)) := do
  match prepare deployment profile ambient durable ingress.command with
  | .error reason => return .error reason
  | .ok prepared =>
    if physical : PhysicalShape prepared then
      match ← admitNative native prepared ingress with
      | .error reason => return .error reason
      | .ok accepted => return .ok ⟨prepared, accepted, physical⟩
    else return .error .physicalPreparation

variable [DecidableEq F] {ingress : DecodedIngress}

def charge (accepted : AcceptedObservation deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 2
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.envelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedObservation deployment profile ambient durable ingress) :
    DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some ingress.command.observer
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := nullifiers deployment.domain ingress.command
  exactCharge := charge accepted
  event := event deployment.domain profile.semantics ingress
  postRootsBound := accepted.physical.2.2.2.1
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

/-- An accepted report writes exactly the clock cell and the Book. -/
theorem intent_writes (accepted : AcceptedObservation deployment profile ambient durable ingress) :
    (intent accepted).writes.map DataWrite.cellId =
      [ClockCellDomain.cellIdOf deployment, ⟨deployment.resourceBookId⟩] := rfl

/-- An accepted report spends each observation's transfer nullifier. -/
theorem intent_spends (accepted : AcceptedObservation deployment profile ambient durable ingress)
    (o : Observation) (member : o ∈ ingress.command.observations) :
    nullifier deployment.domain o ∈ (intent accepted).nullifiers :=
  List.mem_append_left _ (List.mem_map_of_mem member)

/-- An accepted report spends its tip's tick nullifier. -/
theorem intent_spends_tick (accepted : AcceptedObservation deployment profile ambient durable ingress) :
    tickNullifier deployment.domain ingress.command.tip ∈ (intent accepted).nullifiers :=
  List.mem_append_right _ (List.mem_singleton_self _)

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
        recorded.nullifiers = nullifiers domain ingress.command then
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

#assert_axioms Prepared.bookPost_exact
#assert_axioms Prepared.clock_post
#assert_axioms readGuards_readonly
#assert_axioms intent_writes
#assert_axioms intent_spends
#assert_axioms intent_spends_tick

end Minidregg.Kernel.PayObservationReceiver
