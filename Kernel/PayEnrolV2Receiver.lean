/-
Quote-bound v2 observation receiver. The existing observer command and capability
request remain the authenticated ingress; canonical v2 memo bytes select this
receiver and its native possession checks. Original v1 receiving stays explicit.

One DataIntent commits source origin, optional consumption, Book/birth/member
and clock/tip effects. Pending value has zero Book writes. Exact replay precedes
current expiry, freshness, pricing and authority decisions.
-/
import Kernel.PayEnrolReceiver
import Kernel.PayEnrolV2Legs
import Compiler.PhysicalLawResolution
import Compiler.ComposedPolicyAdmission
import Compiler.WorldKindLawDependencies
import Kernel.ClockLaw

namespace Minidregg.Kernel.PayEnrolV2Receiver

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
open Minidregg.Kernel.PayEnrolReceiver (Registry Deployment Durable Ambient Command DecodedIngress
  BookCell FactoryCell Declaration Mode family request marker decodeIngress
  context)
open Minidregg.Kernel.PayEnrolV2Decision (Memo Decision EnrolPlan RenewPlan PendingPlan)
open Minidregg.Kernel.PayObservation (Observation nullifier tickNullifier nullifierBytes)
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.PolicyInstall
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.Store (Store Patch Op Address)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

inductive Reject where
  | malformedIngress | malformedMemo | directoryUnavailable | authorityUnavailable | payUnavailable
  | bookUnavailable | factoryUnavailable | staleAuthority | stalePay
  | clockUnavailable | tipBehindClock | chainTipRegressed
  | chainFreshness (reason : PayChainTip.FreshnessReject)
  | decision (reason : PayEnrolV2Decision.Reject)
  | legs (reason : PayEnrolV2Legs.Reject)
  | verifier (error : CredentialSignatureIO.Error)
  | validation | physicalPreparation | policyUnavailable | capabilityRejected
  | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  /-- The committed law of a written cell refused the write (`Kernel.ReceivingLaw`):
  the clock's own law, judged on the enrollment's clock advance. -/
  | law (fault : ReceivingLaw.LawFault)
  deriving Repr

def requireSome {A : Type} (reason : Reject) : Option A → Except Reject A
  | none => .error reason | some value => .ok value

def parsedMemo (observation : Observation) : Option Memo :=
  match observation.memo with
  | .present bytes => (PayEnrolMemoV2.parse bytes).toOption
  | _ => none

/-- The loaded Host passes the authenticated original expectedSeed, not a
request field. Ordinary birth pricing is reused unchanged. -/
def pricingAt {F : Type} [Field F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (seed : Digest)
    (authority : CredentialAuthorityDomain.Snapshot) (memo : Memo) : PayEnrolV2Decision.Pricing :=
  ⟨deployment.domain, seed, profile.semantics, ambient.tariff, profile.template,
    PayEnrolReceiver.birthFee deployment profile.semantics profile.template ambient.tariff
      authority.cell ambient.height
      (PayEnrolReceiver.ids deployment.domain memo.unsigned.enrollmentIdentityKey) 0⟩

/-- Commit exact economic origin and consumption, plus all source allocation
choices. No detached acceptance command or v1 possession is synthesized. -/
def decisionBytes : Decision → List UInt8
  | .enrol plan => [1] ++ PayEnrolClaim.claimCodec.encode plan.origin ++
      PayEnrolClaim.consumptionCodec.encode plan.consumption ++
      StreamCodec.nat.encode plan.float ++
      (StreamCodec.option StreamCodec.nat).encode plan.index ++
      StreamCodec.nat.encode plan.leaseUntil
  | .renew plan => [2] ++ PayEnrolClaim.claimCodec.encode plan.origin ++
      PayEnrolClaim.consumptionCodec.encode plan.consumption ++
      StreamCodec.nat.encode plan.float ++ StreamCodec.nat.encode plan.account ++
      enrolRecordStream.encode plan.before ++ StreamCodec.nat.encode plan.leaseFrom ++
      StreamCodec.nat.encode plan.leaseUntil
  | .pending plan => [4] ++ PayEnrolClaim.claimCodec.encode plan.claim ++
      (StreamCodec.option PayEnrolClaim.pendingOwnerStream).encode plan.ownerAllocation
  | .journal reason => [3] ++ StreamCodec.nat.encode reason.code

def decisionTag : Decision → Nat
  | .enrol _ => 1 | .renew _ => 2 | .journal _ => 3 | .pending _ => 4


def economicInput (pay : PayStore) (authority : CredentialAuthorityDomain.Snapshot) :
    Decision → Except Reject PayEnrolV2Legs.Input
  | .enrol plan => do
      let custody ← (PayEnrolV2Decision.resolveCustody pay authority plan.memo.unsigned).mapError Reject.decision
      let next ← requireSome (.decision .malformedCustody) custody.owner.nextKeyDigest
      let owner : PayEnrolClaim.PendingOwner :=
        ⟨custody.owner.identityKey, custody.owner.currentKey, custody.owner.epoch, next⟩
      pure (.enrol (PayEnrolV2Legs.ofDirectEnrol plan owner))
  | .renew plan => .ok (.renew (PayEnrolV2Legs.ofDirectRenew plan))
  | .pending _ | .journal _ => .ok .noCredit

def payPatch (observation : Observation) (decision : Decision) (account : Nat) : Patch PayCell.layout :=
  match decision with
  | .enrol plan => plan.patch account observation.slot
  | .renew plan => plan.patch
  | .pending plan => plan.patch
  | .journal reason => PayEnrolDecision.journalPatch observation reason

section Preparation
variable {F : Type} [Field F] [DecidableEq F]

/-- The clock write's law step (`ClockLaw.step`): the clock target's selector
slots, the observer's signed self-enrollment request, operation
`pay-self-enrol`, and the clock before and after the validated advance. -/
def clockStepOf (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (command : Command) (directory : Directory Nat Registry)
    (snapshot : PayEnrolReceiver.Snapshot) (pay : PayCell.Cell) (clock : ClockCell.Cell)
    (current : ClockCell.Clock) (d : Declaration) {patch : Patch ClockCell.layout}
    (clockValid : ValidatedPatch ClockCell.materializer clock clock.root patch) : PolicyStepContext :=
  ClockLaw.step (WorldKindLawDependencies.targetSelectorSlots directory
      (ClockCell.physicalId deployment.domain))
    (request deployment snapshot pay profile.semantics ambient command d)
    ClockLaw.paySelfEnrolSlot current profile.semantics
    (PayEnrolReceiver.effectDigest snapshot.domain profile.semantics command d) clockValid

def declarationOf {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot}
    {pay : PayCellDomain.Loaded deployment durable.snapshot}
    {book : BookCell deployment directory.directory} {tariff : Tariff}
    (command : Command) (decision : Decision) {input : PayEnrolV2Legs.Input}
    (legs : PayEnrolV2Legs.Legs deployment profile ambient directory authority pay book tariff input) :
    Declaration :=
  ⟨decisionBytes decision, legs.birthBytes, command.expectedPayRoot,
    marker authority.snapshot.domain profile.semantics command⟩

def patchOf {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {durable : Durable} {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot}
    {pay : PayCellDomain.Loaded deployment durable.snapshot}
    {book : BookCell deployment directory.directory} {tariff : Tariff}
    (command : Command) (decision : Decision) {input : PayEnrolV2Legs.Input}
    (legs : PayEnrolV2Legs.Legs deployment profile ambient directory authority pay book tariff input) :
    Patch PayCell.layout :=
  payPatch command.observation decision legs.account ++
    PayChainTip.patch (chainTipOf pay.cell.logical) command.tip

structure Prepared (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (command : Command) (memo : Memo)
    (verified : PayEnrolSignatureV2IO.Checked (PayEnrolV2Decision.observationContext command.observation) memo) where
  private mk ::
  expectedSeed : Digest
  directory : LoadedDirectory durable
  authority : Loaded deployment durable.snapshot
  pay : PayCellDomain.Loaded deployment durable.snapshot
  book : BookCell deployment directory.directory
  factory : FactoryCell deployment directory.directory
  tariff : Tariff
  tariffExact : tariffOf pay.cell.logical = some tariff
  clock : ClockCellDomain.Loaded deployment durable.snapshot
  tipAhead : clock.clock.slot ≤ command.tip.slot
  chainTipAhead : PayChainTip.advances (chainTipOf pay.cell.logical) command.tip
  tipFresh : PayChainTip.fresh (PayObservation.advanceClock clock.clock command.tip)
    (some command.tip) = .ok command.tip
  clockValid : ValidatedPatch ClockCell.materializer clock.cell clock.cell.root
    (ClockCell.tickPatch clock.clock (PayObservation.advanceClock clock.clock command.tip))
  decision : Decision
  decided : PayEnrolV2Decision.decide pay.cell.logical authority.snapshot
    (pricingAt deployment profile ambient expectedSeed authority.snapshot memo)
    command.tip command.observation memo verified = .ok decision
  input : PayEnrolV2Legs.Input
  inputExact : economicInput pay.cell.logical authority.snapshot decision = .ok input
  legs : PayEnrolV2Legs.Legs deployment profile ambient directory authority pay book tariff input
  candidate : Candidate (family deployment authority.snapshot pay.cell profile.semantics ambient command
      (patchOf command decision legs)) pay.cell (declarationOf command decision legs) ()
  /-- The clock's own committed law admits the advance (no fault). -/
  clockJudged : ReceivingLaw.judgeWrite (PayObservationReceiver.laws deployment profile) .payEnrolV2
    durable [] (clock.write clockValid.apply)
    (some (clockStepOf deployment profile ambient command directory.directory authority.snapshot
      pay.cell clock.cell clock.clock (declarationOf command decision legs) clockValid)) = none
  source : CanonicalCellRegistry.LoadedPolicySource authority.snapshot.domain directory.directory
    (authority.snapshot.authState.policyAddress ⟨deployment.factoryId⟩
      (authority.snapshot.authState.policyRevision ⟨deployment.factoryId⟩))
  dependencies : WorldKindLawDependencies.Dependencies
  dependenciesExact : WorldKindLawDependencies.loadTarget deployment directory.directory
    deployment.factoryId = some dependencies
  lawGuards : List (Nat × Digest)
  lawGuardsExact : PhysicalLawResolution.readGuards authority.snapshot directory.directory
    profile.semantics deployment.factoryId dependencies.additional = some lawGuards

/-- Every semantic input is read from this loaded image; none of the legs can
be supplied by the transport. Freshness measures observer lag against the
monotone deployment clock, while the expiry hour still comes from the chain.
The verified observer may advance that clock; this rejects evidence lagging the
prior clock, not a timestamp independently known to be in the future. -/
def prepare (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (seed : Digest) (durable : Durable) (command : Command) (memo : Memo)
    (verified : PayEnrolSignatureV2IO.Checked (PayEnrolV2Decision.observationContext command.observation) memo) :
    Except Reject (Prepared deployment profile ambient durable command memo verified) := do
  let directory ← requireSome .directoryUnavailable (loadDirectory durable)
  let authority ← requireSome .authorityUnavailable (loadDeployment deployment durable.snapshot)
  let pay ← requireSome .payUnavailable (PayCellDomain.load deployment durable.snapshot)
  let clock ← requireSome .clockUnavailable (ClockCellDomain.load deployment durable.snapshot)
  let book ← requireSome .bookUnavailable
    (ResourceBirthController.Concrete.observeCell deployment directory.directory deployment.resourceBookId .resourceBook)
  let factory ← requireSome .factoryUnavailable
    (ResourceBirthController.Concrete.observeCell deployment directory.directory deployment.factoryId .declaredObject)
  let snapshot := authority.snapshot
  if command.expectedAuthorityRoot ≠ snapshot.cell.root then throw .staleAuthority
  if rootExact : command.expectedPayRoot = pay.cell.root then
    match tariffExact : tariffOf pay.cell.logical with
    | none => throw (.decision .tariffInvalid)
    | some tariff =>
      if tipAhead : clock.clock.slot ≤ command.tip.slot then
        if chainTipAhead : PayChainTip.advances (chainTipOf pay.cell.logical) command.tip then
          match tipFresh : PayChainTip.fresh (PayObservation.advanceClock clock.clock command.tip) (some command.tip) with
          | .error reason => throw (.chainFreshness reason)
          | .ok freshTip =>
            -- Fresh returns its exact evidence; retain the equality for the receiver boundary.
            if exactTip : freshTip = command.tip then
              match validate ClockCell.materializer clock.cell clock.cell.root
                  (ClockCell.tickPatch clock.clock (PayObservation.advanceClock clock.clock command.tip)) with
              | .rejected _ => throw .validation
              | .accepted clockValid =>
                match decided : PayEnrolV2Decision.decide pay.cell.logical authority.snapshot
                    (pricingAt deployment profile ambient seed authority.snapshot memo)
                    command.tip command.observation memo verified with
                | .error reason => throw (.decision reason)
                | .ok decision =>
                  match inputExact : economicInput pay.cell.logical authority.snapshot decision with
                  | .error reason => throw reason
                  | .ok input =>
                    let legs ← (PayEnrolV2Legs.prepare deployment profile ambient directory authority pay book tariff input).mapError Reject.legs
                    match validate PayCell.materializer pay.cell pay.cell.root (patchOf command decision legs) with
                    | .rejected _ => throw .validation
                    | .accepted validated =>
                     match clockJudged : ReceivingLaw.judgeWrite
                         (PayObservationReceiver.laws deployment profile) .payEnrolV2 durable []
                         (clock.write clockValid.apply)
                         (some (clockStepOf deployment profile ambient command directory.directory
                           snapshot pay.cell clock.cell clock.clock (declarationOf command decision legs)
                           clockValid)) with
                     | some fault => throw (.law fault)
                     | none =>
                      let source ← requireSome .policyUnavailable (CanonicalCellRegistry.loadPolicySource
                        snapshot.domain directory.directory
                        (snapshot.authState.policyAddress ⟨deployment.factoryId⟩
                          (snapshot.authState.policyRevision ⟨deployment.factoryId⟩)))
                      let candidate : Candidate (family deployment snapshot pay.cell profile.semantics
                          ambient command (patchOf command decision legs)) pay.cell
                          (declarationOf command decision legs) () :=
                        { preStateBound := rfl
                          modeEvidence := ⟨rootExact⟩
                          validated := validated
                          postcondition := validated.resultAt }
                      match dependenciesExact : WorldKindLawDependencies.loadTarget deployment directory.directory deployment.factoryId with
                      | none => throw .policyUnavailable
                      | some dependencies =>
                        match lawGuardsExact : PhysicalLawResolution.readGuards snapshot directory.directory
                            profile.semantics deployment.factoryId dependencies.additional with
                        | none => throw .policyUnavailable
                        | some lawGuards =>
                          pure ⟨seed, directory, authority, pay, book, factory, tariff, tariffExact,
                            clock, tipAhead, chainTipAhead, by simpa [exactTip] using tipFresh,
                            clockValid, decision, decided, input, inputExact, legs, candidate,
                            clockJudged, source, dependencies, dependenciesExact, lawGuards, lawGuardsExact⟩
            else throw .chainTipRegressed
        else throw .chainTipRegressed
      else throw .tipBehindClock
  else throw .stalePay

variable {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {durable : Durable} {command : Command} {memo : Memo}
  {verified : PayEnrolSignatureV2IO.Checked (PayEnrolV2Decision.observationContext command.observation) memo}

def Prepared.payPost (prepared : Prepared deployment profile ambient durable command memo verified) :
    PayCell.Cell :=
  prepared.candidate.validated.apply

def Prepared.declaration (prepared : Prepared deployment profile ambient durable command memo verified) :
    Declaration :=
  declarationOf command prepared.decision prepared.legs

def project (prepared : Prepared deployment profile ambient durable command memo verified)
    (_logical : PayStore) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory deployment.factoryId ++
    CanonicalRuntimeProfile.requestSlots
      (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient
        command prepared.declaration) ++
    [(ClockLaw.paySelfEnrolSlot, 1),
     ("pay/decision", Int.ofNat (decisionTag prepared.decision)),
     ("pay/amount", Int.ofNat command.observation.amount),
     ("pay/price", Int.ofNat (match prepared.decision.consumption with
        | some consumed => consumed.birthFee + consumed.membershipCredit
        | none => 0))] ++
    ResourceAuthorityProjection.grantSlots "authority/enrol" .program command.capability
      prepared.authority.snapshot.logical⟩

def step (prepared : Prepared deployment profile ambient durable command memo verified) :
    PolicyStepContext :=
  PolicyStepContext.ofCandidate (project prepared) profile.semantics prepared.candidate

def sourceStore (prepared : Prepared deployment profile ambient durable command memo verified) :
    CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource prepared.authority.snapshot.domain
    prepared.directory.directory⟩

/-- The factory is the request's actual target. Preparation retains the exact
structural dependencies and complete current/pinned law-source read set. -/
def policyConfig
    (prepared : Prepared deployment profile ambient durable command memo verified) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile prepared.authority.snapshot
    prepared.directory.directory
    (sourceCapabilityPortal prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command))
    (step prepared) deployment.factoryId prepared.dependencies.additional

def lawReadGuards (prepared : Prepared deployment profile ambient durable command memo verified) :
    List (Nat × Digest) := prepared.lawGuards ++ prepared.dependencies.readGuards

/-- No absent resolver can be interpreted as an empty dependency list. -/
theorem Prepared.complete_law_dependencies
    (prepared : Prepared deployment profile ambient durable command memo verified) :
    WorldKindLawDependencies.loadTarget deployment prepared.directory.directory deployment.factoryId =
      some prepared.dependencies ∧
    PhysicalLawResolution.readGuards prepared.authority.snapshot prepared.directory.directory
      profile.semantics deployment.factoryId prepared.dependencies.additional = some prepared.lawGuards :=
  ⟨prepared.dependenciesExact, prepared.lawGuardsExact⟩

abbrev Prepared.SemanticAccepted
    (prepared : Prepared deployment profile ambient durable command memo verified) :=
  AcceptedCellEffect (portal := (policyConfig prepared).portal)
    (authState := prepared.authority.snapshot.authState)
    (family deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient command
      (patchOf command prepared.decision prepared.legs))
    (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient
      command prepared.declaration)
    prepared.pay.cell prepared.declaration ()

/-- The observer's request under the factory's CURRENT law: capability mode
with `C_enrol`, the slot `authority/operation/pay-self-enrol = 1`. -/
def authorize
    (prepared : Prepared deployment profile ambient durable command memo verified)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject prepared.SemanticAccepted := do
  let wanted := request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics
    ambient command prepared.declaration
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
  match ComposedPolicyAdmission.admit config wanted
      evidence witness (.policy wanted.policyId wanted.policyRevision) rfl rfl with
  | none => .error .policyRejected
  | some authorization =>
      .ok (prepared.candidate.accept authorization rfl rfl rfl .sealed trivial)

structure Accepted
    (prepared : Prepared deployment profile ambient durable command memo verified)
    (ingress : DecodedIngress) where
  private mk ::
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  semantic : prepared.SemanticAccepted

/-- An accepted observer submission satisfies the resolved current law, including
inherited/ambient/kind components, on this exact source-prepared effect. -/
theorem Accepted.composed_law_evaluated
    {prepared : Prepared deployment profile ambient durable command memo verified}
    {ingress : DecodedIngress} (accepted : Accepted prepared ingress) :
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
    (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics
      ambient command prepared.declaration) accepted.semantic.authorization

def admitNative (native : CredentialSignatureIO.NativeConfig)
    (prepared : Prepared deployment profile ambient durable command memo verified)
    (ingress : DecodedIngress) : IO (Except Reject (Accepted prepared ingress)) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      (marker prepared.authority.snapshot.domain profile.semantics command)
      (request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics ambient
        command prepared.declaration)
      ingress.ingress.envelope with
  | .error reason => return .error (.signature reason)
  | .ok receipt =>
      if same : receipt.envelopeBytes = ingress.ingress.envelope then
        match authorize prepared receipt with
        | .error reason => return .error reason
        | .ok semantic => return .ok ⟨receipt, same, semantic⟩
      else return .error .capabilityRejected

/-! ## The physical intent -/

def payWrite (prepared : Prepared deployment profile ambient durable command memo verified) : DataWrite :=
  prepared.pay.write prepared.payPost

/-- The clock cell after the payment: `PayObservation.advanceClock` at the tip. -/
def Prepared.clockPost (prepared : Prepared deployment profile ambient durable command memo verified) :
    ClockCell.Cell :=
  prepared.clockValid.apply

def clockWrite (prepared : Prepared deployment profile ambient durable command memo verified) : DataWrite :=
  prepared.clock.write prepared.clockPost

/-- The clock write's law step. -/
def Prepared.clockStep (prepared : Prepared deployment profile ambient durable command memo verified) :
    PolicyStepContext :=
  clockStepOf deployment profile ambient command prepared.directory.directory
    prepared.authority.snapshot prepared.pay.cell prepared.clock.cell prepared.clock.clock
    prepared.declaration prepared.clockValid

/-- **The clock's own law admitted the advance** (`ReceivingLaw.Lawful` under the
deployed laws, the conclusion `Receiving.Family.shape_lawful` gives a migrated
family per write). -/
theorem Prepared.clock_lawful
    (prepared : Prepared deployment profile ambient durable command memo verified) :
    ReceivingLaw.Lawful (PayObservationReceiver.laws deployment profile) .payEnrolV2 durable []
      (clockWrite prepared) (some prepared.clockStep) :=
  (ReceivingLaw.judgeWrite_none_iff _ _ _ _ _ _).1 prepared.clockJudged

/-- The cells the clock law's resolution read: a concurrent change of the
clock's law conflicts with the enrollment. -/
def clockLawGuards (prepared : Prepared deployment profile ambient durable command memo verified) :
    List ReadGuard :=
  ReceivingLaw.writeGuards (PayObservationReceiver.laws deployment profile) durable []
    (clockWrite prepared) (some prepared.clockStep)

/-- The pay cell, the clock cell, then the decision's other cells. -/
def writes (prepared : Prepared deployment profile ambient durable command memo verified) :
    List DataWrite :=
  payWrite prepared :: clockWrite prepared :: prepared.legs.writes prepared.factory

def policyGuard (prepared : Prepared deployment profile ambient durable command memo verified) :
    ReadGuard :=
  ⟨⟨prepared.source.readGuard.1⟩, prepared.source.readGuard.2⟩

def readGuards (prepared : Prepared deployment profile ambient durable command memo verified) :
    List ReadGuard :=
  policyGuard prepared ::
    (prepared.authority.readGuards ++
      (lawReadGuards prepared).map (fun (cellIdentifier, expectedRoot) => (⟨⟨cellIdentifier⟩, expectedRoot⟩ : ReadGuard)) ++
      clockLawGuards prepared).filter fun guard =>
      guard.cellId ∉ (writes prepared).map DataWrite.cellId

def PhysicalShape (prepared : Prepared deployment profile ambient durable command memo verified) : Prop :=
  ((writes prepared).map DataWrite.cellId).Nodup ∧
    (∀ write ∈ writes prepared, write.expectedPre = durable.snapshot.model.roots write.cellId) ∧
    (∀ write ∈ writes prepared, ResourceBirthController.Concrete.PhysicalPostLaw deployment write) ∧
    (∀ write ∈ writes prepared, rootBytes write.canonicalPostBytes = write.exactPost) ∧
    (policyGuard prepared).cellId ∉ (writes prepared).map DataWrite.cellId ∧
    (∀ guard ∈ readGuards prepared, guard.expectedRoot = durable.snapshot.model.roots guard.cellId)

instance physicalShapeDecidable
    (prepared : Prepared deployment profile ambient durable command memo verified) :
    Decidable (PhysicalShape prepared) := by
  unfold PhysicalShape
  infer_instance

theorem readGuards_readonly (prepared : Prepared deployment profile ambient durable command memo verified)
    (shape : PhysicalShape prepared) (guard : ReadGuard) (member : guard ∈ readGuards prepared) :
    guard.cellId ∉ (writes prepared).map DataWrite.cellId := by
  rcases List.mem_cons.mp member with rfl | authority
  · exact shape.2.2.2.2.1
  · simpa using (List.mem_filter.mp authority).2

def nullifiers (prepared : Prepared deployment profile ambient durable command memo verified) :
    List StableNullifier :=
  [nullifier deployment.domain command.observation, tickNullifier deployment.domain command.tip] ++
    prepared.legs.nullifiers

end Preparation

/-- A v2 signature check cannot be replaced by a fabricated v1 Verified pair. -/
structure VerifiedMemo (observation : Observation) where
  memo : Memo
  checked : PayEnrolSignatureV2IO.Checked (PayEnrolV2Decision.observationContext observation) memo

def verifyFor (native : CredentialSignatureIO.NativeConfig) (observation : Observation) :
    IO (Except Reject (VerifiedMemo observation)) := do
  let some memo := parsedMemo observation | return .error .malformedMemo
  match ← PayEnrolSignatureV2IO.verifyNative native (PayEnrolV2Decision.observationContext observation) memo with
  | .error error => return .error (.verifier error)
  | .ok checked => return .ok ⟨memo, checked⟩

section Receiver
variable {F : Type} [Field F] [DecidableEq F]

structure AcceptedEnrol (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) (ingress : DecodedIngress) where
  private mk ::
  verified : VerifiedMemo ingress.command.observation
  prepared : Prepared deployment profile ambient durable ingress.command verified.memo verified.checked
  accepted : Accepted prepared ingress
  physical : PhysicalShape prepared

def admitDecodedNative (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (seed : Digest) (durable : Durable) (native : CredentialSignatureIO.NativeConfig)
    (ingress : DecodedIngress) :
    IO (Except Reject (AcceptedEnrol deployment profile ambient durable ingress)) := do
  match ← verifyFor native ingress.command.observation with
  | .error reason => return .error reason
  | .ok verified =>
    match prepare deployment profile ambient seed durable ingress.command verified.memo verified.checked with
    | .error reason => return .error reason
    | .ok prepared =>
      if physical : PhysicalShape prepared then
        match ← admitNative native prepared ingress with
        | .error reason => return .error reason
        | .ok accepted => return .ok ⟨verified, prepared, accepted, physical⟩
      else return .error .physicalPreparation

variable {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {durable : Durable} {ingress : DecodedIngress}

/-- Event/transaction identity stays the existing exact observer ingress. The
v2 memo and full declaration are committed inside it; old receipts remain exact. -/
abbrev transactionId := PayEnrolReceiver.transactionId
abbrev event := PayEnrolReceiver.event
abbrev Receipt := PayEnrolReceiver.Receipt
abbrev receipt := PayEnrolReceiver.receipt
abbrev replay := PayEnrolReceiver.replay

def charge (accepted : AcceptedEnrol deployment profile ambient durable ingress) : ResourceCost.Charge
  | .incidences => (writes accepted.prepared).length
  | .turnBytes => ingress.bytes.length
  | .memoryTouches => (writes accepted.prepared).length + (readGuards accepted.prepared).length
  | .storageBytes => ((writes accepted.prepared).map fun write => write.canonicalPostBytes.length).sum
  | .witnessBytes => ingress.ingress.envelope.length
  | .proofWork => 2
  | .feeDebit | .networkBytes | .sideEffectCount | .leaseByteBlocks => 0

def intent (accepted : AcceptedEnrol deployment profile ambient durable ingress) : DataIntent rootBytes where
  transactionId := transactionId deployment.domain profile.semantics ingress
  subject := some ingress.command.observer
  writes := writes accepted.prepared
  readGuards := readGuards accepted.prepared
  nullifiers := nullifiers accepted.prepared
  exactCharge := charge accepted
  event := event deployment.domain ingress
  postRootsBound := accepted.physical.2.2.2.1
  guardsReadOnly := readGuards_readonly accepted.prepared accepted.physical

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | transactionConflict
  | durableRejected (reason : DurableDataIntent.RejectReason)
  | contention | unavailable (detail : String) | uncertain (detail : String)

/-- Recorded receipts win before any new quote or authority decision. A new
submission crosses one durable intent for all value and source-index writes. -/
def receiveLoaded (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (seed : Digest) (native : CredentialSignatureIO.NativeConfig)
    (transport : DurableReceiverIO.Transport) (durable : Durable) (bytes : List UInt8) : IO Result := do
  let some ingress := decodeIngress bytes | return .rejected .malformedIngress
  match replay deployment.domain profile.semantics durable ingress with
  | some (.ok prior) => return .confirmed .replayed prior
  | some (.error _) => return .transactionConflict
  | none =>
    match ← admitDecodedNative deployment profile ambient seed durable native ingress with
    | .error reason => return .rejected reason
    | .ok accepted =>
      match ← DurableReceiverIO.receiveLoaded transport rootBytes durable (intent accepted) with
      | .confirmed kind _ => return .confirmed kind (receipt deployment.domain profile.semantics ingress)
      | .rejected reason => return .durableRejected reason
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

/-- Atomicity is the existing durable transaction, including BOTH source-index
rows and the same birth/Book writes. There is no out-of-band credit operation. -/
theorem intent_writes_exact (accepted : AcceptedEnrol deployment profile ambient durable ingress) :
    (intent accepted).writes = payWrite accepted.prepared :: clockWrite accepted.prepared ::
      accepted.prepared.legs.writes accepted.prepared.factory := rfl

end Receiver

/-- The observer signs the actual source-prepared v2 decision. Failure is
returned before a signing plan is handed to the watcher. -/
def signingHeader {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (seed : Digest)
    (durable : Durable) (native : CredentialSignatureIO.NativeConfig) (command : Command) :
    IO (Except String CredentialSignedEnvelopeController.SignedHeader) := do
  match ← verifyFor native command.observation with
  | .error reason => return .error s!"v2 payment possession: {repr reason}"
  | .ok verified =>
    match prepare deployment profile ambient seed durable command verified.memo verified.checked with
    | .error reason => return .error s!"v2 payment preparation: {repr reason}"
    | .ok prepared =>
      return (CredentialSignatureAdmission.signingHeader prepared.authority.snapshot
        (marker deployment.domain profile.semantics command)
        ⟨.program, request deployment prepared.authority.snapshot prepared.pay.cell profile.semantics
          ambient command prepared.declaration⟩).mapError
        (fun reason => s!"v2 payment observer key: {repr reason}")

#assert_axioms Prepared.clock_lawful

end Minidregg.Kernel.PayEnrolV2Receiver
