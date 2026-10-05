/-
# Kernel.PayObservationReceiver — observed payments become Book credit

One signed report of the enrolled observer (`PayObservation.Command`) is one
turn over two cells:

* the **clock cell** (`Kernel.ClockCell`, the deployment's one clock): its
  `slot` becomes the tip's and its `now` the tip's block time when that is
  later (`Plan.nextClock`, a guarded write at the clock's exact pre-root).
  The clock is `lawBearing`: its OWN committed law judges this write
  (`ReceivingLaw.judgeWrite` on `Laws.physical`, the Receiver's one judgement,
  on `ClockLaw.step` -- the observer's request under operation `pay-observe`,
  the clock before and after), and a refusal names the failing clause
  (`Reject.law`, `Prepared.clock_lawful`); the law's source cells join the
  read guards;
* the **pay cell** is read, not written: tariff, book and assignment, pinned
  at its exact pre-root `expectedPayRoot` and writes the finalized tip there;
* the **Book**: one issuer mint `.mint tariff.asset payer (creditFor amount)`
  per observation, as a `Batch` decided by `Batch.Admission` at the Book's
  loaded state (`AcceptedBatch.ofAdmission`, as resource birth does).

Authorization: the observer signs a capability-mode request of kind `program`,
target and policy the pay cell (`PayCell.physicalId`), verb `observePayment`,
presenting its capability; it is admitted under the pay cell's complete current law closure
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
import Compiler.PhysicalLawResolution
import Compiler.WorldKindLawDependencies
import Kernel.ClockLaw
import Kernel.ReceivingLaw

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

/-! ## The clock write's law -/

/-- The laws the clock write is judged by: the deployed law source
(`ReceivingLaw.Laws.physical`), the one every `Receiving.Family` is judged by. -/
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

/-! ## Preparation -/

structure Prepared {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
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
  /-- The clock's own committed law admits the advance (no fault). -/
  clockJudged : ReceivingLaw.judgeWrite (laws deployment profile) .payObservation durable
    (clock.write clockValid.apply)
    (some (clockStepOf deployment profile ambient command directory.directory authority.snapshot
      pay.cell clock.cell clock.clock plan clockValid)) = none
  resources : CanonicalResourceKernel.AcceptedBatch book.payload plan.batch
  candidate : Candidate (family deployment authority.snapshot pay.cell profile.semantics ambient command)
    pay.cell (declaration authority.snapshot.domain profile.semantics command plan) ()
  /-- Structural selector roots are mandatory, not a default empty list. -/
  dependencies : WorldKindLawDependencies.Dependencies
  dependenciesExact : WorldKindLawDependencies.loadTarget deployment directory.directory
    (payTarget deployment) = some dependencies
  /-- Every resolved component and historical predecessor is guarded at CAS. -/
  sourceGuards : List (Nat × Digest)
  sourceGuardsExact : PhysicalLawResolution.readGuards authority.snapshot directory.directory
    profile.semantics (payTarget deployment) dependencies.additional = some sourceGuards

/-- The decision, in order: the loaded cells, the two pinned roots, the pure
`decideObservations` (which includes the Book admission), the pay patch's
validation and the complete current law dependency closure.  Refusal reasons before the signature
check are named (the enrollment pattern of this branch). -/
def prepare {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
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
        match clockJudged : ReceivingLaw.judgeWrite (laws deployment profile) .payObservation durable
            (clock.write clockValid.apply)
            (some (clockStepOf deployment profile ambient command directory.directory snapshot
              pay.cell clock.cell clock.clock plan clockValid)) with
        | some fault => throw (.law fault)
        | none =>
        match validate PayCell.materializer pay.cell pay.cell.root
            (PayChainTip.patch (chainTipOf pay.cell.logical) plan.tip) with
        | .rejected _ => throw .validation
        | .accepted validated =>
            let candidate : Candidate (family deployment snapshot pay.cell profile.semantics
                ambient command) pay.cell d () :=
              { preStateBound := rfl
                modeEvidence := ⟨rootExact⟩
                validated := validated
                postcondition := validated.resultAt }
            match dependenciesExact : WorldKindLawDependencies.loadTarget deployment
                directory.directory (payTarget deployment) with
            | none => throw .policyUnavailable
            | some dependencies =>
              match sourceGuardsExact : PhysicalLawResolution.readGuards snapshot
                  directory.directory profile.semantics (payTarget deployment) dependencies.additional with
              | none => throw .policyUnavailable
              | some sourceGuards =>
                pure ⟨directory, authority, pay, clock, book, plan, decided, clockValid, clockJudged,
                  CanonicalResourceKernel.AcceptedBatch.ofAdmission
                    (decideObservations_admitted decided), candidate,
                  dependencies, dependenciesExact, sourceGuards, sourceGuardsExact⟩
    else throw .stalePay
  else throw .staleAuthority

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {durable : Durable}
  {command : Command}

/-- The clock cell after the report: the validated clock write applied. -/
def Prepared.clockPost (prepared : Prepared deployment profile ambient durable command) : ClockCell.Cell :=
  prepared.clockValid.apply

/-- The clock write's law step. -/
def Prepared.clockStep (prepared : Prepared deployment profile ambient durable command) :
    PolicyStepContext :=
  clockStepOf deployment profile ambient command prepared.directory.directory
    prepared.authority.snapshot prepared.pay.cell prepared.clock.cell prepared.clock.clock
    prepared.plan prepared.clockValid

/-- **The clock's own law admitted the advance.**  A prepared report's clock
write is lawful under the deployed laws: the clock is a `lawBearing` cell (not
a birth) whose committed law resolved at the loaded state on the report's step
with both compiler verdicts true and `Pred.eval` accepting it -- or, were the
registry to make the clock kernel-only, a write by a family its row names.
Exactly `Receiving.Family.shape_lawful`'s per-write conclusion. -/
theorem Prepared.clock_lawful (prepared : Prepared deployment profile ambient durable command) :
    ReceivingLaw.Lawful (laws deployment profile) .payObservation durable
      (prepared.clock.write prepared.clockPost) (some prepared.clockStep) :=
  (ReceivingLaw.judgeWrite_none_iff _ _ _ _ _).1 prepared.clockJudged

/-- The validated semantic family's exact pay post, including chain evidence. -/
def Prepared.payPost (prepared : Prepared deployment profile ambient durable command) : PayCell.Cell :=
  prepared.candidate.validated.apply

/-- A checked observation, including a heartbeat, actually retains its tip in
the pay post committed by this receiver. -/
theorem Prepared.pay_post (prepared : Prepared deployment profile ambient durable command) :
    chainTipOf prepared.payPost.logical = some prepared.plan.tip := by
  change chainTipOf (Minidregg.Theory.Store.Patch.run prepared.pay.cell.logical
    (PayChainTip.patch (chainTipOf prepared.pay.cell.logical) prepared.plan.tip)) =
      some prepared.plan.tip
  exact PayChainTip.patch_tip _ _ _

/-- The committed evidence is exactly the ingress tip, not a wall-clock
substitute or an unchecked declaration-only value. -/
theorem Prepared.pay_post_exact (prepared : Prepared deployment profile ambient durable command) :
    chainTipOf prepared.payPost.logical = some command.tip := by
  rw [prepared.pay_post, decideObservations_tip prepared.decided]

theorem Prepared.chain_tip_advances (prepared : Prepared deployment profile ambient durable command) :
    PayChainTip.advances (chainTipOf prepared.pay.cell.logical) command.tip :=
  decideObservations_chainTip prepared.decided

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
  ⟨WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory
      (payTarget deployment) ++
    CanonicalRuntimeProfile.requestSlots
      (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient
        command prepared.plan) ++
    [(ClockLaw.payObserveSlot, 1),
     ("pay/observations", Int.ofNat command.observations.length),
     ("pay/tip/slot", Int.ofNat command.tip.slot),
     ("pay/clock/slot", Int.ofNat prepared.clock.clock.slot)] ++
    DeclaredResourceController.bytesSlots "command/bytes" 0 (commandCodec.encode command) ++
    ResourceAuthorityProjection.grantSlots "authority/observer" .program command.capability
      prepared.authority.snapshot.logical⟩

def step (prepared : Prepared deployment profile ambient durable command) : PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics prepared.candidate

def policyConfig
    (prepared : Prepared deployment profile ambient durable command) : ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile prepared.authority.snapshot
    prepared.directory.directory
    (sourceCapabilityPortal prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared) (payTarget deployment) prepared.dependencies.additional

abbrev Prepared.SemanticAccepted
    (prepared : Prepared deployment profile ambient durable command) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command)
    (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command
      prepared.plan)
    prepared.pay.cell
    (declaration prepared.authority.snapshot.domain profile.semantics command prepared.plan) ()

def authorize
    (prepared : Prepared deployment profile ambient durable command)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics
    ambient command prepared.plan
  let config := policyConfig prepared
  let evidence ← requireSome .capabilityRejected
    (config.capabilityEvidenceChecked wanted command.capability () receipt () (fun _ => ())).toOption
  let law ← requireSome .policyUnavailable config.resolve?
  let witness := law.witness
  if inputsInRange profile.compilerProfile.compiler law.predicate
      (step prepared).oldState (step prepared).newState != true then
    throw .policyInputRange
  if !decide (castInjOn F
      (intsOf law.predicate (step prepared).oldState (step prepared).newState)) then
    throw .policyCastAlias
  match ComposedPolicyAdmission.admit config wanted evidence witness
      (.policy wanted.policyId wanted.policyRevision) rfl rfl with
  | none => .error .policyRejected
  | some authorization =>
      .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)

structure Accepted
    (prepared : Prepared deployment profile ambient durable command)
    (ingress : DecodedIngress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  semantic : prepared.SemanticAccepted

/-- Acceptance evaluates the full source-resolved current restriction
closure on the observer's actual scoped step, including selector coordinates. -/
theorem Accepted.policy_evaluated_actual_post
    {prepared : Prepared deployment profile ambient durable command} {ingress : DecodedIngress}
    (accepted : Accepted prepared ingress) :
    ∃ graph : PolicyComponentResolution.LoadedGraph
        (policyConfig prepared).snapshot (policyConfig prepared).store
        (policyConfig prepared).profile.semantics (policyConfig prepared).target
        (policyConfig prepared).additional,
      PolicyComponentResolution.loadTarget (policyConfig prepared).snapshot
        (policyConfig prepared).store (policyConfig prepared).profile.semantics
        (policyConfig prepared).target (policyConfig prepared).resolutionBudget
        (policyConfig prepared).additional = .ok graph ∧
      Minidregg.Pred.eval (ResolvedLawCompilation.predicate graph.resolved)
        (step prepared).oldState (step prepared).newState = true := by
  exact ComposedPolicyAdmission.authorized_effective_law (policyConfig prepared)
    (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient
      command prepared.plan) accepted.semantic.authorization

def admitNative (native : CredentialSignatureIO.NativeConfig)
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

def payWrite (prepared : Prepared deployment profile ambient durable command) : DataWrite :=
  prepared.pay.write prepared.payPost

def writes (prepared : Prepared deployment profile ambient durable command) : List DataWrite :=
  [payWrite prepared, clockWrite prepared, bookWrite prepared]

/-- The successful physical resolver's complete source/history closure plus
the actual target and structural kind roots. Prepared retains both load proofs. -/
def lawReadGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  (prepared.sourceGuards ++ prepared.dependencies.readGuards).map
    fun (cellIdentifier, expectedRoot) => ⟨⟨cellIdentifier⟩, expectedRoot⟩

/-- The cells the clock law's resolution read (`ReceivingLaw.writeGuards`): a
concurrent change of the clock's law conflicts with the report. -/
def clockLawGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  ReceivingLaw.writeGuards (laws deployment profile) durable (clockWrite prepared)
    (some prepared.clockStep)

def readGuards (prepared : Prepared deployment profile ambient durable command) : List ReadGuard :=
  (prepared.authority.readGuards ++ lawReadGuards prepared ++ clockLawGuards prepared).filter
      fun guard => guard.cellId ∉ (writes prepared).map DataWrite.cellId

/-- No resolved dependency can disappear between admission and commit:
an existing write guards its pre-root, otherwise the intent reads its root. -/
theorem lawGuard_read_or_written (prepared : Prepared deployment profile ambient durable command)
    (guard : ReadGuard) (member : guard ∈ lawReadGuards prepared) :
    guard ∈ readGuards prepared ∨ guard.cellId ∈ (writes prepared).map DataWrite.cellId := by
  by_cases written : guard.cellId ∈ (writes prepared).map DataWrite.cellId
  · exact Or.inr written
  · apply Or.inl
    apply List.mem_filter.mpr
    exact ⟨List.mem_append_left _ (List.mem_append_right _ member), by simpa using written⟩

/-- The same for the clock law's source cells. -/
theorem clockLawGuard_read_or_written (prepared : Prepared deployment profile ambient durable command)
    (guard : ReadGuard) (member : guard ∈ clockLawGuards prepared) :
    guard ∈ readGuards prepared ∨ guard.cellId ∈ (writes prepared).map DataWrite.cellId := by
  by_cases written : guard.cellId ∈ (writes prepared).map DataWrite.cellId
  · exact Or.inr written
  · apply Or.inl
    apply List.mem_filter.mpr
    exact ⟨List.mem_append_right _ member, by simpa using written⟩

theorem Prepared.dependencies_available (prepared : Prepared deployment profile ambient durable command) :
    (WorldKindLawDependencies.loadTarget deployment prepared.directory.directory
      (payTarget deployment)).isSome = true := by
  rw [prepared.dependenciesExact]
  rfl

theorem Prepared.source_guards_available (prepared : Prepared deployment profile ambient durable command) :
    (PhysicalLawResolution.readGuards prepared.authority.snapshot prepared.directory.directory
      profile.semantics (payTarget deployment) prepared.dependencies.additional).isSome = true := by
  rw [prepared.sourceGuardsExact]
  rfl

def PhysicalShape (prepared : Prepared deployment profile ambient durable command) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ writes prepared, rootBytes write.canonicalPostBytes = write.exactPost) ∧

    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable (prepared : Prepared deployment profile ambient durable command) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  simpa [readGuards] using (List.mem_filter.mp member).2

structure AcceptedObservation (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  prepared : Prepared deployment profile ambient durable ingress.command
  accepted : PayObservationReceiver.Accepted prepared ingress
  physical : PhysicalShape prepared

def admitDecodedNative (deployment : Deployment)
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

variable {ingress : DecodedIngress}

def charge (accepted : AcceptedObservation deployment profile ambient durable ingress) :
    ResourceCost.Charge
  | .incidences => 3
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

/-- An accepted report writes retained chain evidence, the clock and the Book. -/
theorem intent_writes (accepted : AcceptedObservation deployment profile ambient durable ingress) :
    (intent accepted).writes.map DataWrite.cellId =
      [PayCellDomain.cellIdOf deployment, ClockCellDomain.cellIdOf deployment, ⟨deployment.resourceBookId⟩] := rfl

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

#assert_axioms Accepted.policy_evaluated_actual_post
#assert_axioms Prepared.pay_post
#assert_axioms Prepared.pay_post_exact
#assert_axioms Prepared.chain_tip_advances
#assert_axioms Prepared.bookPost_exact
#assert_axioms Prepared.clock_post
#assert_axioms lawGuard_read_or_written
#assert_axioms clockLawGuard_read_or_written
#assert_axioms Prepared.clock_lawful
#assert_axioms Prepared.dependencies_available
#assert_axioms Prepared.source_guards_available
#assert_axioms readGuards_readonly
#assert_axioms intent_writes
#assert_axioms intent_spends
#assert_axioms intent_spends_tick

end Minidregg.Kernel.PayObservationReceiver
