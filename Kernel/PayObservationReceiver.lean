/-
# Kernel.PayObservationReceiver — observed payments become Book credit

One signed report of the enrolled observer (`PayObservation.Command`) is one
turn over three cells, as a `Kernel.Receiving.Family` (`family`): the Receiver
verifies the observer's signature before anything is decided, the family
decides and binds the report, and the Receiver judges every written cell's law.

* the **pay cell**: the finalized tip is retained (`PayChainTip.patch`).  The
  pay cell is `lawBearing`; its committed law (genesis: `eq request/subject
  observer`) is judged by the Receiver on the report's step (`step`: the pay
  target's selector slots, the observer's signed request, operation
  `pay-observe`, the report's counts, the command bytes, the observer's grant);
* the **clock cell** (`Kernel.ClockCell`, the deployment's one clock): its
  `slot` becomes the tip's and its `now` the tip's block time when that is
  later (`Plan.nextClock`).  The clock is `lawBearing`; its OWN committed law is
  judged by the Receiver on `ClockLaw.step` (the observer's request under
  operation `pay-observe`, the clock before and after);
* the **Book**: one issuer mint `.mint tariff.asset payer (creditFor amount)`
  per observation, as a `Batch` decided by `Batch.Admission` at the Book's
  loaded state.  The Book is `kernelOnly` and names this family.

The family projects both law steps (`lawStep`); it judges no law.  One judge:
the Receiver's (`Kernel.ReceivingLaw`).  `Minidregg.Kernel.Receiving.Family.receive_committed_lawful`
is the per-write statement for every committed report.

**Signature first.**  The one claim (`claims`) is the observer's current key over
the envelope's own signed header (`CredentialSignatureAdmission.envelopeClaim`):
a key lookup and a decode, no decision.  `prepare` receives the Receiver's
verdict and builds the capability-mode receipt from it
(`CheckedSignature.ofReceiverClaim`, `Source.receiver`); without the voucher it
refuses `signature unvouched`.

**Authorization** is binding only (`ComposedPolicyAdmission.Bound`): the
observer's capability evidence under the receipt, and the signed request bound to
the pay cell's committed head (policy, revision, domain, semantics, the step),
its address and membership.  The law's verdict on the step is the Receiver's;
`ComposedPolicyAdmission.Bound.admit_of_verifies` shows the binding plus that
verdict is the former `admit` exactly.  The effect digest commits to the command
bytes and the decided plan, so the authorized request binds every credit.

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
import Compiler.PhysicalLawResolution
import Compiler.WorldKindLawDependencies
import Kernel.ClockLaw
import Kernel.ReceivingLaw
import Kernel.Receiving

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
open Minidregg.Theory.Receiving (SigQuery)

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

def effectFamily (deployment : Deployment) (snapshot : Snapshot) (pay : PayCell.Cell) (semantics : Digest)
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
  -- The signed semantic effect retains exact finalized evidence in the pay
  -- cell. The clock and Book writes join this same durable intent.
  Postcondition := fun d _ post => Patch.ResultAt pay.logical
    (PayChainTip.patch (chainTipOf pay.logical) d.plan.tip) post
  effectDigest := effectDigest snapshot.domain semantics command
  patch := fun d _ => PayChainTip.patch (chainTipOf pay.logical) d.plan.tip
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

/-! ## The laws -/

/-- The deployed law source (`ReceivingLaw.Laws.physical`) under a runtime
profile: what the Receiver judges every `Minidregg.Kernel.Receiving.Family` by on a Host
(`Minidregg.Kernel.Receiving.Family.receiveLoaded`). -/
def laws {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) : ReceivingLaw.Laws Durable :=
  ReceivingLaw.Laws.physical profile.compilerProfile deployment

/-- The clock write's law step (`ClockLaw.step`): the clock target's selector
slots, the observer's signed request, operation `pay-observe`, and the clock
before and after the validated advance. -/
def clockStepOf {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (command : Command)
    (directory : Directory Nat Registry) (snapshot : Snapshot) (pay : PayCell.Cell)
    (clock : ClockCell.Cell) (current : ClockCell.Clock) (plan : Plan)
    (clockValid : ValidatedPatch ClockCell.materializer clock clock.root plan.patch) :
    PolicyStepContext :=
  ClockLaw.step (WorldKindLawDependencies.targetSelectorSlots directory
      (ClockCell.physicalId deployment.domain))
    (request deployment snapshot pay profile.semantics ambient command plan)
    ClockLaw.payObserveSlot current profile.semantics
    (effectDigest snapshot.domain profile.semantics command
      (declaration snapshot.domain profile.semantics command plan))
    clockValid

/-! ## The decision -/

/-- A report decided on the loaded state: the loaded cells, the plan, the
validated clock and pay patches, the admitted Book batch and the pay target's
structural dependencies.  No law is judged here (the Receiver judges every
written cell) and no signature is read (that is `Prepared`'s). -/
structure Planned {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) where
  private mk ::
  directory : LoadedDirectory durable
  directoryExact : loadDirectory durable = some directory
  authority : CredentialAuthorityDomainReceiver.Loaded deployment durable.snapshot
  authorityExact : loadDeployment deployment durable.snapshot = some authority
  pay : PayCellDomain.Loaded deployment durable.snapshot
  clock : ClockCellDomain.Loaded deployment durable.snapshot
  book : BookCell deployment directory.directory
  plan : Plan
  decided : decideObservations pay.cell.logical clock.clock (bookOf book) command.tip
    command.observations = .ok plan
  clockValid : ValidatedPatch ClockCell.materializer clock.cell clock.cell.root plan.patch
  resources : CanonicalResourceKernel.AcceptedBatch book.payload plan.batch
  candidate : Candidate (effectFamily deployment authority.snapshot pay.cell profile.semantics ambient
    command) pay.cell (declaration authority.snapshot.domain profile.semantics command plan) ()
  /-- Structural selector roots are mandatory, not a default empty list. -/
  dependencies : WorldKindLawDependencies.Dependencies
  dependenciesExact : WorldKindLawDependencies.loadTarget deployment directory.directory
    (payTarget deployment) = some dependencies

/-- The decision, in order: the loaded cells, the two pinned roots, the pure
`decideObservations` (which includes the Book admission), the clock and pay
patches' validation and the pay target's structural dependencies. -/
def planReport {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (command : Command) : Except Reject (Planned deployment profile ambient durable command) := do
  match directoryExact : loadDirectory durable with
  | none => throw .directoryUnavailable
  | some directory =>
  match authorityExact : loadDeployment deployment durable.snapshot with
  | none => throw .authorityUnavailable
  | some authority =>
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
        match validate PayCell.materializer pay.cell pay.cell.root
            (PayChainTip.patch (chainTipOf pay.cell.logical) plan.tip) with
        | .rejected _ => throw .validation
        | .accepted validated =>
            let candidate : Candidate (effectFamily deployment snapshot pay.cell profile.semantics
                ambient command) pay.cell d () :=
              { preStateBound := rfl
                modeEvidence := ⟨rootExact⟩
                validated := validated
                postcondition := validated.resultAt }
            match dependenciesExact : WorldKindLawDependencies.loadTarget deployment
                directory.directory (payTarget deployment) with
            | none => throw .policyUnavailable
            | some dependencies =>
                pure ⟨directory, directoryExact, authority, authorityExact, pay, clock, book, plan,
                  decided, clockValid,
                  CanonicalResourceKernel.AcceptedBatch.ofAdmission
                    (decideObservations_admitted decided), candidate,
                  dependencies, dependenciesExact⟩
    else throw .stalePay
  else throw .staleAuthority

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

/-- The clock cell after the report: the validated clock write applied. -/
def Planned.clockPost (planned : Planned deployment profile ambient durable command) : ClockCell.Cell :=
  planned.clockValid.apply

/-- The clock write's law step. -/
def Planned.clockStep (planned : Planned deployment profile ambient durable command) :
    PolicyStepContext :=
  clockStepOf deployment profile ambient command planned.directory.directory
    planned.authority.snapshot planned.pay.cell planned.clock.cell planned.clock.clock
    planned.plan planned.clockValid

/-- The validated semantic family's exact pay post, including chain evidence. -/
def Planned.payPost (planned : Planned deployment profile ambient durable command) : PayCell.Cell :=
  planned.candidate.validated.apply

/-- A checked observation, including a heartbeat, actually retains its tip in
the pay post committed by this receiver. -/
theorem Planned.pay_post (planned : Planned deployment profile ambient durable command) :
    chainTipOf planned.payPost.logical = some planned.plan.tip := by
  change chainTipOf (Minidregg.Theory.Store.Patch.run planned.pay.cell.logical
    (PayChainTip.patch (chainTipOf planned.pay.cell.logical) planned.plan.tip)) =
      some planned.plan.tip
  exact PayChainTip.patch_tip _ _ _

/-- The committed evidence is exactly the ingress tip, not a wall-clock
substitute or an unchecked declaration-only value. -/
theorem Planned.pay_post_exact (planned : Planned deployment profile ambient durable command) :
    chainTipOf planned.payPost.logical = some command.tip := by
  rw [planned.pay_post, decideObservations_tip planned.decided]

theorem Planned.chain_tip_advances (planned : Planned deployment profile ambient durable command) :
    PayChainTip.advances (chainTipOf planned.pay.cell.logical) command.tip :=
  decideObservations_chainTip planned.decided

/-- The Book after the report: the admitted batch applied. -/
def Planned.bookPost (planned : Planned deployment profile ambient durable command) :
    Materialized (CanonicalCellRegistry.materializer .resourceBook) :=
  planned.resources.post

/-- The prepared Book is exactly the batch applied to the loaded Book. -/
theorem Planned.bookPost_exact (planned : Planned deployment profile ambient durable command) :
    CanonicalResourceKernel.logicalBook planned.bookPost.logical =
      planned.plan.batch.apply (bookOf planned.book) :=
  planned.resources.post_logicalBook

/-- The prepared clock cell holds the report's next clock: the tip's slot, and
`now` advanced to the tip's block time when that is later. -/
theorem Planned.clock_post (planned : Planned deployment profile ambient durable command) :
    ClockCell.clockOf planned.clockPost.logical = some planned.plan.nextClock := by
  change Minidregg.Theory.Store.Patch.run planned.clock.cell.logical planned.plan.patch
    ClockCell.clockAddress = some planned.plan.nextClock
  exact Minidregg.Theory.Store.Store.set_eq _ _ _

/-- The next clock's slot is the report's tip slot. -/
theorem Planned.clock_post_slot (planned : Planned deployment profile ambient durable command) :
    planned.plan.nextClock.slot = command.tip.slot := by
  show planned.plan.tip.slot = command.tip.slot
  rw [decideObservations_tip planned.decided]

theorem Planned.dependencies_available (planned : Planned deployment profile ambient durable command) :
    (WorldKindLawDependencies.loadTarget deployment planned.directory.directory
      (payTarget deployment)).isSome = true := by
  rw [planned.dependenciesExact]
  rfl

/-- **What every `Planned` report means** (the census's layer-1 theorem): its
cells are the ones the durable state loads, the pay post retains exactly the
report's tip, the clock post holds the next clock at the tip's slot, and the Book
post is the decided batch applied to the loaded Book.  A value built any way at
all carries all of it. -/
theorem Planned.sound (planned : Planned deployment profile ambient durable command) :
    loadDirectory durable = some planned.directory ∧
      loadDeployment deployment durable.snapshot = some planned.authority ∧
      decideObservations planned.pay.cell.logical planned.clock.clock (bookOf planned.book)
        command.tip command.observations = .ok planned.plan ∧
      chainTipOf planned.payPost.logical = some command.tip ∧
      ClockCell.clockOf planned.clockPost.logical = some planned.plan.nextClock ∧
      planned.plan.nextClock.slot = command.tip.slot ∧
      CanonicalResourceKernel.logicalBook planned.bookPost.logical =
        planned.plan.batch.apply (bookOf planned.book) :=
  ⟨planned.directoryExact, planned.authorityExact, planned.decided, planned.pay_post_exact,
    planned.clock_post, planned.clock_post_slot, planned.bookPost_exact⟩

/-- The pay law's projected state of a pay store. -/
def project (planned : Planned deployment profile ambient durable command)
    (logical : PayStore) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots planned.directory.directory
      (payTarget deployment) ++
    CanonicalRuntimeProfile.requestSlots
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
        command planned.plan) ++
    [(ClockLaw.payObserveSlot, 1),
     ("pay/observations", Int.ofNat command.observations.length),
     ("pay/tip/slot", Int.ofNat command.tip.slot),
     ("pay/clock/slot", Int.ofNat planned.clock.clock.slot)] ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode command) ++
    ResourceAuthorityProjection.grantSlots "authority/observer" .program command.capability
      planned.authority.snapshot.logical⟩

/-- The pay write's law step: the pay law's projection of the pay cell before
and after the retained tip. -/
def step (planned : Planned deployment profile ambient durable command) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project planned) profile.semantics planned.candidate

/-- The configuration the observer's request is bound under: the pay target's
committed law on the pay step, its structural restrictions, the observer's
capability portal. -/
def policyConfig
    (planned : Planned deployment profile ambient durable command) : ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile planned.authority.snapshot
    planned.directory.directory
    (sourceCapabilityPortal planned.authority.snapshot
      (marker planned.authority.snapshot.domain profile.semantics command))
    (step planned) (payTarget deployment) planned.dependencies.additional

/-! ## The signature claim, the receipt and the binding -/

/-- **The one claim**: the observer's current key over the envelope's own signed
header.  A key lookup and a decode; no decision is made before the Receiver has
verified it. -/
def claims (deployment : Deployment) (durable : Durable) (ingress : DecodedIngress) :
    Except Reject (List SigQuery) :=
  match loadDeployment deployment durable.snapshot with
  | none => .error .authorityUnavailable
  | some authority =>
      match CredentialSignatureAdmission.envelopeClaim authority.snapshot ingress.command.observer
          ingress.ingress.envelope with
      | .error reason => .error (.signature reason)
      | .ok claim => .ok [claim]

/-- The observer's request bound to the pay cell's committed head on the pay
step (`ComposedPolicyAdmission.Bound`). -/
@[irreducible] def Authorization (planned : Planned deployment profile ambient durable command) : Type :=
  ComposedPolicyAdmission.Bound (policyConfig planned)
    (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
      command planned.plan)

/-- A bound request as the report's authorization (the definition is
irreducible: the structure holding it would otherwise unfold the whole binding
while it is declared). -/
def Authorization.of {planned : Planned deployment profile ambient durable command}
    (bound : ComposedPolicyAdmission.Bound (policyConfig planned)
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
        command planned.plan)) : Authorization planned := by
  unfold Authorization
  exact bound

/-- The binding an authorization holds. -/
def Authorization.bound {planned : Planned deployment profile ambient durable command}
    (authorization : Authorization planned) :
    ComposedPolicyAdmission.Bound (policyConfig planned)
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
        command planned.plan) := by
  unfold Authorization at authorization
  exact authorization

/-- A prepared report: the decision, the capability-mode receipt built from the
Receiver's voucher, and the observer's request bound to the pay cell's committed
head on the pay step.  The pay and clock laws' verdicts are the Receiver's. -/
structure Prepared {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  planned : Planned deployment profile ambient durable ingress.command
  receipt : CredentialSignatureAdmission.CheckedSignature planned.authority.snapshot
  /-- The receipt is the Receiver's: its oracle answered the claim the envelope
  admission checked, before `prepare` ran. -/
  receiptVouched : ∃ oracle, receipt.source = .receiver oracle
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  authorized : Authorization planned

/-- **What every `Prepared` report means** (the census's layer-1 theorem, over
layer-2 parts): its decision is sound (`Planned.sound`), its receipt is the
Receiver's (`Source.receiver`) for the envelope the ingress carries, and the
observer's request is bound to the pay cell's committed head on the pay step.
The receipt's signature verdict itself is the oracle's (layer 2). -/
theorem Prepared.sound {ingress : DecodedIngress}
    (prepared : Prepared deployment profile ambient durable ingress) :
    (∃ oracle, prepared.receipt.source = .receiver oracle) ∧
      prepared.receipt.envelopeBytes = ingress.ingress.envelope ∧
      prepared.authorized.bound.law.binding
        (request deployment prepared.planned.authority.snapshot prepared.planned.pay.cell
          profile.semantics ambient ingress.command prepared.planned.plan) = true :=
  ⟨prepared.receiptVouched, prepared.envelopeExact, prepared.authorized.bound.bound⟩

/-- The gate: decide the report, build the receipt from the Receiver's voucher,
check the observer's capability evidence under it, bind the request to the pay
cell's committed head.  It judges no law. -/
def prepare {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (received : CredentialSignatureAdmission.Received)
    (ambient : Ambient) (durable : Durable) (ingress : DecodedIngress) :
    Except Reject (Prepared deployment profile ambient durable ingress) :=
  match planReport deployment profile ambient durable ingress.command with
  | .error reason => .error reason
  | .ok planned =>
    let wanted := request deployment planned.authority.snapshot planned.pay.cell profile.semantics
      ambient ingress.command planned.plan
    match checked : CredentialSignatureAdmission.CheckedSignature.ofReceiverClaim received
        planned.authority.snapshot
        (marker planned.authority.snapshot.domain profile.semantics ingress.command) wanted
        ingress.ingress.envelope with
    | .error reason => .error (.signature reason)
    | .ok receipt =>
      let config := policyConfig planned
      match (config.capabilityEvidenceChecked wanted ingress.command.capability () receipt ()
          (fun _ => ())).toOption with
      | none => .error .capabilityRejected
      | some evidence =>
        match config.resolve? with
        | none => .error .policyUnavailable
        | some law =>
          match ComposedPolicyAdmission.bind config wanted evidence law
              (.policy wanted.policyId wanted.policyRevision) rfl rfl with
          | none => .error .policyRejected
          | some authorized =>
            have vouched := CredentialSignatureAdmission.CheckedSignature.ofReceiverClaim_vouched checked
            .ok ⟨planned, receipt, ⟨_, vouched.2.1⟩, vouched.2.2.2.2, Authorization.of authorized⟩

/-! ## The patch -/

def payWrite (planned : Planned deployment profile ambient durable command) : DataWrite :=
  planned.pay.write planned.payPost

def clockWrite (planned : Planned deployment profile ambient durable command) : DataWrite :=
  planned.clock.write planned.clockPost

def bookWrite (planned : Planned deployment profile ambient durable command) : DataWrite :=
  ResourceBirthController.Concrete.packedWrite deployment.resourceBookId
    ⟨.resourceBook, planned.book.payload⟩ ⟨.resourceBook, planned.bookPost⟩

/-- Retained chain evidence, the clock, the Book. -/
def writes (planned : Planned deployment profile ambient durable command) : List DataWrite :=
  [payWrite planned, clockWrite planned, bookWrite planned]

theorem writes_bound (planned : Planned deployment profile ambient durable command)
    (write : DataWrite) (member : write ∈ writes planned) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

/-- **The family projects; the Receiver judges.**  The pay write carries the pay
law's step, the clock write the clock law's step; the Book (kernel-only) none. -/
def lawStepOf (planned : Planned deployment profile ambient durable command) (write : DataWrite) :
    Option PolicyStepContext :=
  if write.cellId = PayCellDomain.cellIdOf deployment then some (step planned)
  else if write.cellId = ClockCellDomain.cellIdOf deployment then some planned.clockStep
  else none

theorem lawStepOf_pay (planned : Planned deployment profile ambient durable command) :
    lawStepOf planned (payWrite planned) = some (step planned) := by
  unfold lawStepOf
  split
  · rfl
  · rename_i differs
    exact absurd rfl differs

theorem lawStepOf_clock (planned : Planned deployment profile ambient durable command)
    (distinct : (clockWrite planned).cellId ≠ (payWrite planned).cellId) :
    lawStepOf planned (clockWrite planned) = some planned.clockStep := by
  unfold lawStepOf
  split
  · rename_i same
    exact absurd same distinct
  · split
    · rfl
    · rename_i differs
      exact absurd rfl differs

theorem lawStepOf_book (planned : Planned deployment profile ambient durable command)
    (notPay : (bookWrite planned).cellId ≠ (payWrite planned).cellId)
    (notClock : (bookWrite planned).cellId ≠ (clockWrite planned).cellId) :
    lawStepOf planned (bookWrite planned) = none := by
  unfold lawStepOf
  split
  · rename_i same
    exact absurd same notPay
  · split
    · rename_i same
      exact absurd same notClock
    · rfl

theorem distinct_of_nodup {α : Type} {a b c : α} (nodup : [a, b, c].Nodup) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨notA, rest⟩ := List.nodup_cons.1 nodup
  obtain ⟨notB, -⟩ := List.nodup_cons.1 rest
  exact ⟨fun same => notA (by simp [same]), fun same => notA (by simp [same]),
    fun same => notB (by simp [same])⟩

def physicalPostLaw (planned : Planned deployment profile ambient durable command) : Bool :=
  (writes planned).all fun write =>
    decide (ResourceBirthController.Concrete.PhysicalPostLaw deployment write)

/-! ## The receiver -/

def transactionId (domain semantics : Digest) (ingress : DecodedIngress) : Digest :=
  ⟨marker domain semantics ingress.command⟩

def event (domain _semantics : Digest) (ingress : DecodedIngress) : StableEvent where
  codecVersion := 1
  domain := domain
  eventId := (Sp800185Cshake256.hash "DREGG.PAY.OBSERVATION.EVENT/v1".toUTF8.toList
    ingress.bytes).digest
  canonicalBytes := ingress.bytes

/-- **The payment observation family.** -/
def family {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) : Minidregg.Kernel.Receiving.Family where
  id := .payObservation
  Env := Ambient
  Ingress := DecodedIngress
  Command := DecodedIngress
  Reject := Reject
  rejectRepr := inferInstance
  Prepared := fun ambient durable ingress => Prepared deployment profile ambient durable ingress
  decode := decodeIngress
  bytes := DecodedIngress.bytes
  command := id
  claims := fun _ durable ingress => claims deployment durable ingress
  prepare := fun received ambient durable ingress =>
    prepare deployment profile received ambient durable ingress
  writes := fun prepared => writes prepared.planned
  writes_bound := fun prepared => writes_bound prepared.planned
  lawStep := fun prepared write _ => lawStepOf prepared.planned write
  observed := fun prepared => prepared.planned.authority.readGuards
  physicalPostLaw := fun prepared => physicalPostLaw prepared.planned
  txId := fun _ ingress => transactionId deployment.domain profile.semantics ingress
  event := fun _ ingress => event deployment.domain profile.semantics ingress
  nullifiers := fun _ ingress => nullifiers deployment.domain ingress.command
  subject := fun ingress => some ingress.command.observer
  witnessBytes := fun ingress => ingress.ingress.envelope.length

/-! ## What a committed report means -/

variable {ingress : DecodedIngress}

/-- **Every committed report's pay and clock writes were judged by their own
committed laws, on the family's steps**, and its Book write by the registry row
that names this family.  `Minidregg.Kernel.Receiving.Family.receive_committed_lawful`,
instantiated: the pay cell's law on the pay step and the clock's law on the
clock step both resolved at the loaded state with the three compiler verdicts
true and `Pred.eval` accepting.  The planted fault for this theorem is the
Receiver's judgement removed (`lawFault := fun _ => none` in
`Minidregg.Kernel.Receiving.Family.receiver`). -/
theorem committed_lawful {laws : ReceivingLaw.Laws Durable}
    {oracle : CredentialSignatureIO.Oracle Id}
    {Exact : Durable → DataIntent rootBytes → Type} {Other : Type}
    {append : (state : Durable) → (intent : DataIntent rootBytes) →
      Id (Minidregg.Theory.Receiving.Receiver.Commit (Exact state intent) Other)}
    {bytes : List UInt8}
    {admission : ((family deployment profile).receiver laws oracle).Admitted ambient durable ingress}
    {witness : Exact durable (((family deployment profile).receiver laws oracle).intent admission.accepted)}
    (committed : ((family deployment profile).receiver laws oracle).receive append ambient durable bytes =
      pure (.committed ingress admission witness)) :
    let planned := admission.accepted.prepared.planned
    ReceivingLaw.Lawful laws .payObservation durable (payWrite planned) (some (step planned)) ∧
      ReceivingLaw.Lawful laws .payObservation durable (clockWrite planned)
        (some planned.clockStep) ∧
      ReceivingLaw.Lawful laws .payObservation durable (bookWrite planned) none := by
  intro planned
  have judged := Minidregg.Kernel.Receiving.Family.receive_committed_lawful (family deployment profile) committed
  have nodup : ((writes planned).map DataWrite.cellId).Nodup :=
    (Minidregg.Kernel.Receiving.Family.receive_committed_shape (family deployment profile)
      committed).1
  simp only [writes, List.map_cons, List.map_nil] at nodup
  obtain ⟨payClock, payBook, clockBook⟩ := distinct_of_nodup nodup
  have payMem : payWrite planned ∈ writes planned := List.Mem.head _
  have clockMem : clockWrite planned ∈ writes planned := List.Mem.tail _ (List.Mem.head _)
  have bookMem : bookWrite planned ∈ writes planned :=
    List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  refine ⟨?_, ?_, ?_⟩
  · have lawful := judged (payWrite planned) payMem
    have stepEq : (family deployment profile).lawStep admission.accepted.prepared (payWrite planned)
        payMem = some (step planned) := by
      dsimp only [family]
      exact lawStepOf_pay planned
    rwa [stepEq] at lawful
  · have lawful := judged (clockWrite planned) clockMem
    have stepEq : (family deployment profile).lawStep admission.accepted.prepared (clockWrite planned)
        clockMem = some planned.clockStep := by
      dsimp only [family]
      exact lawStepOf_clock planned (Ne.symm payClock)
    rwa [stepEq] at lawful
  · have lawful := judged (bookWrite planned) bookMem
    have stepEq : (family deployment profile).lawStep admission.accepted.prepared (bookWrite planned)
        bookMem = none := by
      dsimp only [family]
      exact lawStepOf_book planned (Ne.symm payBook) (Ne.symm clockBook)
    rwa [stepEq] at lawful

/-- **One judge, nothing weakened.**  Under the deployed laws, every committed
report satisfies the full compiled admission the family's `prepare` no longer
runs itself: the observer's bound request (`Prepared.authorized`), with the pay
law's compiled verdict on the pay step, is `ComposedPolicyAdmission.admit`
exactly.  The verdict comes from the Receiver's judgement of the pay write
(`committed_lawful`): the law it resolved is the bound law
(`PhysicalLawResolution.predicate_portal_irrelevant`), and its three compiler
verdicts are `verifies_iff_eval`'s premises. -/
theorem committed_admitted {oracle : CredentialSignatureIO.Oracle Id}
    {Exact : Durable → DataIntent rootBytes → Type} {Other : Type}
    {append : (state : Durable) → (intent : DataIntent rootBytes) →
      Id (Minidregg.Theory.Receiving.Receiver.Commit (Exact state intent) Other)}
    {bytes : List UInt8}
    {admission : ((family deployment profile).receiver (laws deployment profile) oracle).Admitted
      ambient durable ingress}
    {witness : Exact durable
      (((family deployment profile).receiver (laws deployment profile) oracle).intent
        admission.accepted)}
    (committed : ((family deployment profile).receiver (laws deployment profile) oracle).receive
      append ambient durable bytes = pure (.committed ingress admission witness)) :
    let planned := admission.accepted.prepared.planned
    let bound := admission.accepted.prepared.authorized.bound
    ∃ authorized, ComposedPolicyAdmission.admit (policyConfig planned)
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
        ingress.command planned.plan)
      bound.evidence bound.law.witness bound.membership bound.epochExact bound.revisionExact =
        some authorized := by
  intro planned bound
  apply bound.admit_of_verifies
  obtain ⟨payLawful, -, -⟩ := committed_lawful committed
  obtain ⟨kind, -, judgedPay⟩ := payLawful
  rcases judgedPay with ⟨-, -, judgedStep, law, stepEq, resolved, lowerable, inRange, casts, evaluated⟩ |
      ⟨-, -, -, noStep⟩
  · cases stepEq
    obtain ⟨directory, authority, structural, sources, judged, directoryEq, authorityEq, -, -,
        judgedEq, rfl⟩ :=
      (ReceivingLaw.physical_resolve_some_iff _ _ _ _ _ _).1 resolved
    rw [planned.directoryExact] at directoryEq
    rw [planned.authorityExact] at authorityEq
    cases directoryEq
    cases authorityEq
    have restrictions : ((WorldKindLawDependencies.loadTarget deployment planned.directory.directory
        (payTarget deployment)).map (·.additional) |>.getD []) = planned.dependencies.additional := by
      rw [planned.dependenciesExact]
      rfl
    simp only at lowerable inRange casts evaluated
    exact PhysicalLawResolution.bound_verifies_of_target_judged deployment profile.compilerProfile
      planned.authority.snapshot planned.directory.directory _ _ (step planned) (payTarget deployment)
      planned.dependencies.additional restrictions judged judgedEq lowerable inRange casts evaluated
      bound
  · cases noStep

/-- **The receipt behind every admitted report is the Receiver's**: it was built
from a voucher of the receiver's own oracle (`Source.receiver`), for the envelope
the ingress carries. -/
theorem admitted_receipt_vouched {laws : ReceivingLaw.Laws Durable} {m : Type → Type}
    {oracle : CredentialSignatureIO.Oracle m}
    (admission : ((family deployment profile).receiver laws oracle).Admitted ambient durable ingress) :
    (∃ source, admission.accepted.prepared.receipt.source = .receiver source) ∧
      admission.accepted.prepared.receipt.envelopeBytes = ingress.ingress.envelope :=
  ⟨admission.accepted.prepared.receiptVouched, admission.accepted.prepared.envelopeExact⟩

/-- An admitted report spends each observation's transfer nullifier. -/
theorem intent_spends {laws : ReceivingLaw.Laws Durable} {m : Type → Type}
    {oracle : CredentialSignatureIO.Oracle m}
    (accepted : ((family deployment profile).receiver laws oracle).Accepted ambient durable ingress)
    (o : Observation) (member : o ∈ ingress.command.observations) :
    nullifier deployment.domain o ∈
      (((family deployment profile).receiver laws oracle).intent accepted).nullifiers :=
  List.mem_append_left _ (List.mem_map_of_mem member)

/-- An admitted report spends its tip's tick nullifier. -/
theorem intent_spends_tick {laws : ReceivingLaw.Laws Durable} {m : Type → Type}
    {oracle : CredentialSignatureIO.Oracle m}
    (accepted : ((family deployment profile).receiver laws oracle).Accepted ambient durable ingress) :
    tickNullifier deployment.domain ingress.command.tip ∈
      (((family deployment profile).receiver laws oracle).intent accepted).nullifiers :=
  List.mem_append_right _ (List.mem_singleton_self _)

/-- An admitted report writes retained chain evidence, the clock and the Book. -/
theorem intent_writes {laws : ReceivingLaw.Laws Durable} {m : Type → Type}
    {oracle : CredentialSignatureIO.Oracle m}
    (accepted : ((family deployment profile).receiver laws oracle).Accepted ambient durable ingress) :
    (((family deployment profile).receiver laws oracle).intent accepted).writes.map DataWrite.cellId =
      [PayCellDomain.cellIdOf deployment, ClockCellDomain.cellIdOf deployment,
        ⟨deployment.resourceBookId⟩] := rfl

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

#assert_axioms Planned.sound
#assert_axioms Prepared.sound
#assert_axioms Planned.pay_post
#assert_axioms Planned.pay_post_exact
#assert_axioms Planned.chain_tip_advances
#assert_axioms Planned.bookPost_exact
#assert_axioms Planned.clock_post
#assert_axioms Planned.clock_post_slot
#assert_axioms Planned.dependencies_available
#assert_axioms writes_bound
#assert_axioms lawStepOf_pay
#assert_axioms lawStepOf_clock
#assert_axioms lawStepOf_book
#assert_axioms distinct_of_nodup
#assert_axioms committed_lawful
#assert_axioms committed_admitted
#assert_axioms admitted_receipt_vouched
#assert_axioms intent_spends
#assert_axioms intent_spends_tick
#assert_axioms intent_writes

end Minidregg.Kernel.PayObservationReceiver
