/-
Quote-bound v2 observation family (`Kernel.Receiving.Family`). The existing
observer command and capability request remain the authenticated ingress;
canonical v2 memo bytes select this family. The memo's two possession signatures
are OBSERVED by the Receiver's verifier before `prepare` (`observations`,
`committed_verified`); every written cell's law is the Receiver's to judge
(`committed_lawful`, `committed_admitted`). Original v1 receiving stays explicit.

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
open Minidregg.Theory.Receiving (SigQuery Vouchers)

set_option autoImplicit false
attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

inductive Reject where
  | malformedMemo | directoryUnavailable | authorityUnavailable | payUnavailable
  | bookUnavailable | factoryUnavailable | staleAuthority | stalePay
  | clockUnavailable | tipBehindClock | chainTipRegressed
  | chainFreshness (reason : PayChainTip.FreshnessReject)
  | decision (reason : PayEnrolV2Decision.Reject)
  | legs (reason : PayEnrolV2Legs.Reject)
  /-- The Receiver did not answer one of the memo's observed signatures (it always
  does: `admitVia` answers every observation or refuses `.verifier`). -/
  | unobserved
  | validation | policyUnavailable | capabilityRejected | policyRejected
  | signature (reason : CredentialSignatureAdmission.Reject)
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

/-- **The v2 payment, decided and planned before any authorization**: the
loaded cells, the two pinned roots, the fresh tip and clock advance, the decision
under the Receiver's answers on the memo's possession signatures (`verified`),
its economic input, the legs, the pay patch and the factory law's dependencies.
No law is judged here: the Receiver judges every written cell. -/
structure Planned (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (seed : Digest) (durable : Durable) (command : Command) (memo : Memo)
    (verified : PayEnrolDecision.Verified) where
  private mk ::
  directory : LoadedDirectory durable
  directoryExact : loadDirectory durable = some directory
  authority : Loaded deployment durable.snapshot
  authorityExact : loadDeployment deployment durable.snapshot = some authority
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
    (pricingAt deployment profile ambient seed authority.snapshot memo)
    command.tip command.observation memo verified.mini verified.ssh = .ok decision
  input : PayEnrolV2Legs.Input
  inputExact : economicInput pay.cell.logical authority.snapshot decision = .ok input
  legs : PayEnrolV2Legs.Legs deployment profile ambient directory authority pay book tariff input
  candidate : Candidate (family deployment authority.snapshot pay.cell profile.semantics ambient command
      (patchOf command decision legs)) pay.cell (declarationOf command decision legs) ()
  dependencies : WorldKindLawDependencies.Dependencies
  dependenciesExact : WorldKindLawDependencies.loadTarget deployment directory.directory
    deployment.factoryId = some dependencies

/-- **What every `Planned` v2 payment means** (layer 1): the decision is
`PayEnrolV2Decision.decide`'s on the loaded pay and authority cells under exactly
the bits `verified`, its economic input is the decision's, the tip is fresh and
ahead of the clock, and the factory law's dependencies are the loaded ones. -/
theorem Planned.sound {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
    {ambient : Ambient} {seed : Digest} {durable : Durable} {command : Command} {memo : Memo}
    {verified : PayEnrolDecision.Verified}
    (planned : Planned deployment profile ambient seed durable command memo verified) :
    PayEnrolV2Decision.decide planned.pay.cell.logical planned.authority.snapshot
        (pricingAt deployment profile ambient seed planned.authority.snapshot memo)
        command.tip command.observation memo verified.mini verified.ssh = .ok planned.decision ∧
      economicInput planned.pay.cell.logical planned.authority.snapshot planned.decision =
        .ok planned.input ∧
      planned.clock.clock.slot ≤ command.tip.slot ∧
      PayChainTip.fresh (PayObservation.advanceClock planned.clock.clock command.tip)
        (some command.tip) = .ok command.tip ∧
      WorldKindLawDependencies.loadTarget deployment planned.directory.directory
        deployment.factoryId = some planned.dependencies :=
  ⟨planned.decided, planned.inputExact, planned.tipAhead, planned.tipFresh, planned.dependenciesExact⟩

/-- Plan the payment under the verifier's answers `verified`.  Freshness
measures observer lag against the monotone deployment clock, while the expiry
hour still comes from the chain. -/
def plan (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (seed : Digest) (durable : Durable) (command : Command) (memo : Memo)
    (verified : PayEnrolDecision.Verified) :
    Except Reject (Planned deployment profile ambient seed durable command memo verified) := do
  match directoryExact : loadDirectory durable with
  | none => throw .directoryUnavailable
  | some directory =>
  match authorityExact : loadDeployment deployment durable.snapshot with
  | none => throw .authorityUnavailable
  | some authority =>
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
            if exactTip : freshTip = command.tip then
              match validate ClockCell.materializer clock.cell clock.cell.root
                  (ClockCell.tickPatch clock.clock (PayObservation.advanceClock clock.clock command.tip)) with
              | .rejected _ => throw .validation
              | .accepted clockValid =>
                match decided : PayEnrolV2Decision.decide pay.cell.logical authority.snapshot
                    (pricingAt deployment profile ambient seed authority.snapshot memo)
                    command.tip command.observation memo verified.mini verified.ssh with
                | .error reason => throw (.decision reason)
                | .ok decision =>
                  match inputExact : economicInput pay.cell.logical authority.snapshot decision with
                  | .error reason => throw reason
                  | .ok input =>
                    let legs ← (PayEnrolV2Legs.prepare deployment profile ambient directory authority pay book tariff input).mapError Reject.legs
                    match validate PayCell.materializer pay.cell pay.cell.root (patchOf command decision legs) with
                    | .rejected _ => throw .validation
                    | .accepted validated =>
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
                        pure ⟨directory, directoryExact, authority, authorityExact, pay, book, factory,
                          tariff, tariffExact, clock, tipAhead, chainTipAhead,
                          by simpa [exactTip] using tipFresh, clockValid, decision, decided, input,
                          inputExact, legs, candidate, dependencies, dependenciesExact⟩
            else throw .chainTipRegressed
        else throw .chainTipRegressed
      else throw .tipBehindClock
  else throw .stalePay

variable {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {seed : Digest} {durable : Durable} {command : Command} {memo : Memo}
  {verified : PayEnrolDecision.Verified}

def Planned.payPost (planned : Planned deployment profile ambient seed durable command memo verified) :
    PayCell.Cell :=
  planned.candidate.validated.apply

def Planned.declaration (planned : Planned deployment profile ambient seed durable command memo verified) :
    Declaration :=
  declarationOf command planned.decision planned.legs

def project (planned : Planned deployment profile ambient seed durable command memo verified)
    (_logical : PayStore) : Minidregg.Pred.State :=
  ⟨WorldKindLawDependencies.targetSelectorSlots planned.directory.directory deployment.factoryId ++
    CanonicalRuntimeProfile.requestSlots
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
        command planned.declaration) ++
    [(ClockLaw.paySelfEnrolSlot, 1),
     ("pay/decision", Int.ofNat (decisionTag planned.decision)),
     ("pay/amount", Int.ofNat command.observation.amount),
     ("pay/price", Int.ofNat (match planned.decision.consumption with
        | some consumed => consumed.birthFee + consumed.membershipCredit
        | none => 0))] ++
    ResourceAuthorityProjection.grantSlots "authority/enrol" .program command.capability
      planned.authority.snapshot.logical⟩

/-- The payment's law step: the factory's selector slots, the observer's
self-enrollment request (the self-enrol slot 1), the decision, the amount and
the price.  The factory's law, the pay law and a newborn's export law judge it. -/
def step (planned : Planned deployment profile ambient seed durable command memo verified) :
    PolicyStepContext :=
  PolicyStepContext.ofCandidate (project planned) profile.semantics planned.candidate

def policyConfig
    (planned : Planned deployment profile ambient seed durable command memo verified) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile planned.authority.snapshot
    planned.directory.directory
    (sourceCapabilityPortal planned.authority.snapshot
      (marker planned.authority.snapshot.domain profile.semantics command))
    (step planned) deployment.factoryId planned.dependencies.additional

def Planned.clockStep (planned : Planned deployment profile ambient seed durable command memo verified) :
    PolicyStepContext :=
  clockStepOf deployment profile ambient command planned.directory.directory
    planned.authority.snapshot planned.pay.cell planned.clock.cell planned.clock.clock
    planned.declaration planned.clockValid

end Preparation

/-! ## The patch -/

section Patch

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {seed : Digest} {durable : Durable}
  {command : Command} {memo : Memo} {verified : PayEnrolDecision.Verified}

/-- The factory at its loaded payload: the write that puts the payment under the
factory's law.  An enrollment writes it through the birth plan; every other
branch writes it here. -/
def factoryPacked {directory : Directory Nat Registry} (factory : FactoryCell deployment directory) :
    DataWrite :=
  ResourceBirthController.Concrete.packedWrite deployment.factoryId
    ⟨.declaredObject, factory.payload⟩ ⟨.declaredObject, factory.payload⟩

/-- The factory write a branch adds beyond its legs: none for an enrollment (its
birth plan writes the factory), the factory otherwise. -/
def factoryExtra {durable : Durable} {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot}
    {pay : PayCellDomain.Loaded deployment durable.snapshot}
    {book : BookCell deployment directory.directory} {tariff : Tariff}
    (factory : FactoryCell deployment directory.directory) : {input : PayEnrolV2Legs.Input} →
    PayEnrolV2Legs.Legs deployment profile ambient directory authority pay book tariff input →
      List DataWrite
  | _, .enrol _ _ => []
  | _, .renew _ _ => [factoryPacked factory]
  | _, .noCredit => [factoryPacked factory]

def payWrite (planned : Planned deployment profile ambient seed durable command memo verified) : DataWrite :=
  planned.pay.write planned.payPost

def clockWrite (planned : Planned deployment profile ambient seed durable command memo verified) : DataWrite :=
  planned.clock.write planned.clockValid.apply

/-- The pay cell, the clock cell, the legs' cells, then the factory when the legs
do not write it. -/
def writes (planned : Planned deployment profile ambient seed durable command memo verified) :
    List DataWrite :=
  payWrite planned :: clockWrite planned ::
    (planned.legs.writes planned.factory ++ factoryExtra planned.factory planned.legs)

theorem legs_writes_bound {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot}
    {pay : PayCellDomain.Loaded deployment durable.snapshot}
    {book : BookCell deployment directory.directory} {tariff : Tariff}
    (factory : FactoryCell deployment directory.directory) :
    {input : PayEnrolV2Legs.Input} →
    (legs : PayEnrolV2Legs.Legs deployment profile ambient directory authority pay book tariff input) →
    ∀ write ∈ legs.writes factory ++ factoryExtra factory legs,
      rootBytes write.canonicalPostBytes = write.exactPost
  | _, .enrol _ legs, write, member => by
      simp only [PayEnrolV2Legs.Legs.writes, factoryExtra, List.append_nil,
        ResourceBirthController.Concrete.planWrites, ResourceBirthController.allocationWrites,
        CredentialAuthorityDomainReceiver.Loaded.writes,
        List.mem_append, List.mem_map, List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with ((⟨request, -, rfl⟩ | rfl | rfl) | rfl) <;> rfl
  | _, .renew _ _, write, member => by
      simp only [PayEnrolV2Legs.Legs.writes, factoryExtra, List.cons_append, List.nil_append,
        List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl <;> rfl
  | _, .noCredit, write, member => by
      simp only [PayEnrolV2Legs.Legs.writes, factoryExtra, List.nil_append, List.mem_cons,
        List.mem_nil_iff, or_false] at member
      subst member; rfl

theorem legs_factory_mem {directory : LoadedDirectory durable}
    {authority : Loaded deployment durable.snapshot}
    {pay : PayCellDomain.Loaded deployment durable.snapshot}
    {book : BookCell deployment directory.directory} {tariff : Tariff}
    (factory : FactoryCell deployment directory.directory) :
    {input : PayEnrolV2Legs.Input} →
    (legs : PayEnrolV2Legs.Legs deployment profile ambient directory authority pay book tariff input) →
    factoryPacked factory ∈ legs.writes factory ++ factoryExtra factory legs
  | _, .enrol _ _ => by
      simp [PayEnrolV2Legs.Legs.writes, factoryExtra, factoryPacked,
        ResourceBirthController.Concrete.planWrites]
  | _, .renew _ _ => by simp [factoryExtra]
  | _, .noCredit => by simp [factoryExtra]

theorem writes_bound (planned : Planned deployment profile ambient seed durable command memo verified)
    (write : DataWrite) (member : write ∈ writes planned) :
    rootBytes write.canonicalPostBytes = write.exactPost := by
  simp only [writes, List.mem_cons] at member
  rcases member with rfl | rfl | legs
  · rfl
  · rfl
  · exact legs_writes_bound planned.factory planned.legs write legs

/-- **The family projects; the Receiver judges** (as v1's): the clock carries the
clock law's step, a kernel-only cell none, every other write the payment step. -/
def lawStepOf (planned : Planned deployment profile ambient seed durable command memo verified)
    (write : DataWrite) : Option PolicyStepContext :=
  match ReceivingLaw.livePost write with
  | some ⟨.clock, _⟩ => some planned.clockStep
  | some ⟨kind, _⟩ =>
      match kind.lawClass with
      | .kernelOnly _ => none
      | _ => some (step planned)
  | none => some (step planned)

theorem lawStepOf_pay (planned : Planned deployment profile ambient seed durable command memo verified) :
    lawStepOf planned (payWrite planned) = some (step planned) := by
  unfold lawStepOf
  rw [ReceivingLaw.livePost_live (cell := PayCellDomain.packedCell planned.payPost) rfl]
  rfl

theorem lawStepOf_clock (planned : Planned deployment profile ambient seed durable command memo verified) :
    lawStepOf planned (clockWrite planned) = some planned.clockStep := by
  unfold lawStepOf
  rw [ReceivingLaw.livePost_live (cell := ClockCellDomain.packedCell planned.clockValid.apply) rfl]
  rfl

theorem lawStepOf_factory (planned : Planned deployment profile ambient seed durable command memo verified) :
    lawStepOf planned (factoryPacked planned.factory) = some (step planned) := by
  unfold lawStepOf
  rw [ReceivingLaw.livePost_live (cell := ⟨.declaredObject, planned.factory.payload⟩) rfl]
  rfl

def physicalPostLaw (planned : Planned deployment profile ambient seed durable command memo verified) :
    Bool :=
  (writes planned).all fun write =>
    decide (ResourceBirthController.Concrete.PhysicalPostLaw deployment write)

end Patch

/-! ## The signatures: one claim, two observations -/

/-- The memo's authorizing-key possession query: Ed25519 over the v2 frame. -/
def miniQuery (observation : Observation) (memo : Memo) : SigQuery :=
  ⟨.ed25519, memo.unsigned.authorizingKey,
    PayEnrolMemoV2.miniFrame (PayEnrolV2Decision.observationContext observation) memo,
    memo.miniSignature⟩

/-- The memo's ssh-key possession query: `SSHSIG` under the v2 namespace. -/
def sshQuery (observation : Observation) (memo : Memo) : SigQuery :=
  ⟨.sshsig PayEnrolMemoV2.sshsigNamespace, memo.unsigned.sshKey,
    PayEnrolMemoV2.sshsigMessage (PayEnrolV2Decision.observationContext observation) memo,
    memo.sshSignature⟩

/-- **The OBSERVED signatures**: the v2 memo's two possession signatures over
the observed asset and recipient.  A `false` journals the payment; only a
verifier error refuses. -/
def observations (observation : Observation) : Except Reject (List SigQuery) :=
  match parsedMemo observation with
  | none => .error .malformedMemo
  | some memo => .ok [miniQuery observation memo, sshQuery observation memo]

/-- The two bits the decision reads, from the verifier's `answer`s on exactly the
observed queries. -/
def verifiedOf (answer : SigQuery → Option Bool) (observation : Observation) (memo : Memo) :
    Except Reject PayEnrolDecision.Verified :=
  match answer (miniQuery observation memo), answer (sshQuery observation memo) with
  | some mini, some ssh => .ok ⟨mini, ssh⟩
  | _, _ => .error .unobserved

theorem verifiedOf_answers {answer : SigQuery → Option Bool} {observation : Observation}
    {memo : Memo} {verified : PayEnrolDecision.Verified}
    (decided : verifiedOf answer observation memo = .ok verified) :
    answer (miniQuery observation memo) = some verified.mini ∧
      answer (sshQuery observation memo) = some verified.ssh := by
  unfold verifiedOf at decided
  split at decided
  · rename_i mini ssh miniEq sshEq
    cases decided
    exact ⟨miniEq, sshEq⟩
  · cases decided

/-! ## The gate -/

section Gate

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {ambient : Ambient} {seed : Digest} {durable : Durable}
  {command : Command} {memo : Memo} {verified : PayEnrolDecision.Verified}

@[irreducible] def Authorization
    (planned : Planned deployment profile ambient seed durable command memo verified) : Type :=
  ComposedPolicyAdmission.Bound (policyConfig planned)
    (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
      command planned.declaration)

def Authorization.of {planned : Planned deployment profile ambient seed durable command memo verified}
    (bound : ComposedPolicyAdmission.Bound (policyConfig planned)
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
        command planned.declaration)) : Authorization planned := by
  unfold Authorization
  exact bound

def Authorization.bound {planned : Planned deployment profile ambient seed durable command memo verified}
    (authorization : Authorization planned) :
    ComposedPolicyAdmission.Bound (policyConfig planned)
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics ambient
        command planned.declaration) := by
  unfold Authorization at authorization
  exact authorization

end Gate

/-- The v2 family's environment: the ambient and the Host's authenticated
original expected seed (never a request field). -/
structure Env where
  ambient : Ambient
  seed : Digest

/-- A prepared v2 payment: the memo, the Receiver's answers as bits, the plan
under them, the receipt from the Receiver's voucher, and the observer's request
bound to the factory's committed head.  Every law verdict is the Receiver's. -/
structure Prepared {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (env : Env) (durable : Durable)
    (ingress : DecodedIngress) where
  private mk ::
  memo : Memo
  memoExact : parsedMemo ingress.command.observation = some memo
  verified : PayEnrolDecision.Verified
  planned : Planned deployment profile env.ambient env.seed durable ingress.command memo verified
  receipt : CredentialSignatureAdmission.CheckedSignature planned.authority.snapshot
  receiptVouched : ∃ oracle, receipt.source = .receiver oracle
  envelopeExact : receipt.envelopeBytes = ingress.ingress.envelope
  authorized : Authorization planned

theorem Prepared.sound {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {env : Env} {durable : Durable}
    {ingress : DecodedIngress} (prepared : Prepared deployment profile env durable ingress) :
    parsedMemo ingress.command.observation = some prepared.memo ∧
      (∃ oracle, prepared.receipt.source = .receiver oracle) ∧
      prepared.receipt.envelopeBytes = ingress.ingress.envelope ∧
      prepared.authorized.bound.law.binding
        (request deployment prepared.planned.authority.snapshot prepared.planned.pay.cell
          profile.semantics env.ambient ingress.command prepared.planned.declaration) = true :=
  ⟨prepared.memoExact, prepared.receiptVouched, prepared.envelopeExact, prepared.authorized.bound.bound⟩

def prepare {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (received : CredentialSignatureAdmission.Received)
    (env : Env) (durable : Durable) (ingress : DecodedIngress) :
    Except Reject (Prepared deployment profile env durable ingress) :=
  match memoExact : parsedMemo ingress.command.observation with
  | none => .error .malformedMemo
  | some memo =>
  match verifiedOf received.vouchers.answer? ingress.command.observation memo with
  | .error reason => .error reason
  | .ok verified =>
  match plan deployment profile env.ambient env.seed durable ingress.command memo verified with
  | .error reason => .error reason
  | .ok planned =>
    let wanted := request deployment planned.authority.snapshot planned.pay.cell profile.semantics
      env.ambient ingress.command planned.declaration
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
            .ok ⟨memo, memoExact, verified, planned, receipt, ⟨_, vouched.2.1⟩, vouched.2.2.2.2,
              Authorization.of authorized⟩

theorem prepare_verified {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
    {profile : CanonicalRuntimeProfile.Profile F} {received : CredentialSignatureAdmission.Received}
    {env : Env} {durable : Durable} {ingress : DecodedIngress}
    {prepared : Prepared deployment profile env durable ingress}
    (ran : prepare deployment profile received env durable ingress = .ok prepared) :
    verifiedOf received.vouchers.answer? ingress.command.observation prepared.memo =
      .ok prepared.verified := by
  unfold prepare at ran
  split at ran
  · cases ran
  · split at ran
    · cases ran
    · rename_i verified decided
      split at ran
      · cases ran
      · dsimp only at ran
        split at ran
        · cases ran
        · split at ran
          · cases ran
          · split at ran
            · cases ran
            · split at ran
              · cases ran
              · cases ran
                exact decided

/-! ## The family -/

def payEnrolV2Family {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) : Minidregg.Kernel.Receiving.Family where
  id := .payEnrolV2
  Env := Env
  Ingress := DecodedIngress
  Command := DecodedIngress
  Reject := Reject
  rejectRepr := inferInstance
  Prepared := fun env durable ingress => Prepared deployment profile env durable ingress
  decode := decodeIngress
  bytes := DecodedIngress.bytes
  command := id
  claims := fun _ durable ingress =>
    PayEnrolReceiver.envelopeClaims .authorityUnavailable .signature deployment durable ingress
  observations := fun _ _ ingress => observations ingress.command.observation
  prepare := fun received env durable ingress => prepare deployment profile received env durable ingress
  writes := fun prepared => writes prepared.planned
  writes_bound := fun prepared => writes_bound prepared.planned
  lawStep := fun prepared write _ => lawStepOf prepared.planned write
  observed := fun prepared => prepared.planned.authority.readGuards
  physicalPostLaw := fun prepared => physicalPostLaw prepared.planned
  txId := fun _ ingress => PayEnrolReceiver.transactionId deployment.domain profile.semantics ingress
  event := fun _ ingress => PayEnrolReceiver.event deployment.domain ingress
  nullifiers := fun _ ingress =>
    [nullifier deployment.domain ingress.command.observation,
      tickNullifier deployment.domain ingress.command.tip]
  spent := fun prepared => prepared.planned.legs.nullifiers
  subject := fun ingress => some ingress.command.observer
  witnessBytes := fun ingress => ingress.ingress.envelope.length

/-! ## What a committed v2 payment means -/

section Committed

variable {F : Type} [Field F] [DecidableEq F] {deployment : Deployment}
  {profile : CanonicalRuntimeProfile.Profile F} {env : Env} {durable : Durable}
  {ingress : DecodedIngress}

theorem factoryPacked_mem {ambient : Ambient} {seed : Digest} {command : Command} {memo : Memo}
    {verified : PayEnrolDecision.Verified}
    (planned : Planned deployment profile ambient seed durable command memo verified) :
    factoryPacked planned.factory ∈ writes planned :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (legs_factory_mem planned.factory planned.legs))

theorem factoryPacked_not_birth {ambient : Ambient} {seed : Digest} {command : Command}
    {memo : Memo} {verified : PayEnrolDecision.Verified}
    (planned : Planned deployment profile ambient seed durable command memo verified) :
    ReceivingLaw.physicalBirth durable (factoryPacked planned.factory) = false :=
  ReceivingLaw.physicalBirth_false_of_present planned.directory planned.factory.present

/-- **Every committed v2 payment's pay, clock and factory writes were judged by
their own committed laws on the family's steps.** -/
theorem committed_lawful {laws : ReceivingLaw.Laws Durable}
    {oracle : CredentialSignatureIO.Oracle Id}
    {Exact : Durable → DataIntent rootBytes → Type} {Other : Type}
    {append : (state : Durable) → (intent : DataIntent rootBytes) →
      Id (Minidregg.Theory.Receiving.Receiver.Commit (Exact state intent) Other)}
    {bytes : List UInt8}
    {admission : ((payEnrolV2Family deployment profile).receiver laws oracle).Admitted env durable ingress}
    {witness : Exact durable (((payEnrolV2Family deployment profile).receiver laws oracle).intent
      admission.accepted)}
    (committed : ((payEnrolV2Family deployment profile).receiver laws oracle).receive append env
      durable bytes = pure (.committed ingress admission witness)) :
    let planned := admission.accepted.prepared.planned
    ReceivingLaw.Lawful laws .payEnrolV2 durable (writes planned) (payWrite planned)
        (some (step planned)) ∧
      ReceivingLaw.Lawful laws .payEnrolV2 durable (writes planned) (clockWrite planned)
        (some planned.clockStep) ∧
      ReceivingLaw.Lawful laws .payEnrolV2 durable (writes planned) (factoryPacked planned.factory)
        (some (step planned)) := by
  intro planned
  have judged := Minidregg.Kernel.Receiving.Family.receive_committed_lawful
    (payEnrolV2Family deployment profile) committed
  have payMem : payWrite planned ∈ writes planned := List.Mem.head _
  have clockMem : clockWrite planned ∈ writes planned := List.Mem.tail _ (List.Mem.head _)
  have factoryMem := factoryPacked_mem planned
  refine ⟨?_, ?_, ?_⟩
  · have lawful := judged (payWrite planned) payMem
    have stepEq : (payEnrolV2Family deployment profile).lawStep admission.accepted.prepared
        (payWrite planned) payMem = some (step planned) := by
      dsimp only [payEnrolV2Family]
      exact lawStepOf_pay planned
    rwa [stepEq] at lawful
  · have lawful := judged (clockWrite planned) clockMem
    have stepEq : (payEnrolV2Family deployment profile).lawStep admission.accepted.prepared
        (clockWrite planned) clockMem = some planned.clockStep := by
      dsimp only [payEnrolV2Family]
      exact lawStepOf_clock planned
    rwa [stepEq] at lawful
  · have lawful := judged (factoryPacked planned.factory) factoryMem
    have stepEq : (payEnrolV2Family deployment profile).lawStep admission.accepted.prepared
        (factoryPacked planned.factory) factoryMem = some (step planned) := by
      dsimp only [payEnrolV2Family]
      exact lawStepOf_factory planned
    rwa [stepEq] at lawful

/-- **One judge, nothing weakened** (as v1's `committed_admitted`): every
committed v2 payment satisfies the full compiled admission of the observer's
request under the factory's law, whose verdict the Receiver gave on the factory
write. -/
theorem committed_admitted {oracle : CredentialSignatureIO.Oracle Id}
    {Exact : Durable → DataIntent rootBytes → Type} {Other : Type}
    {append : (state : Durable) → (intent : DataIntent rootBytes) →
      Id (Minidregg.Theory.Receiving.Receiver.Commit (Exact state intent) Other)}
    {bytes : List UInt8}
    {admission : ((payEnrolV2Family deployment profile).receiver
      (PayEnrolReceiver.laws deployment profile) oracle).Admitted env durable ingress}
    {witness : Exact durable
      (((payEnrolV2Family deployment profile).receiver (PayEnrolReceiver.laws deployment profile)
        oracle).intent admission.accepted)}
    (committed : ((payEnrolV2Family deployment profile).receiver
      (PayEnrolReceiver.laws deployment profile) oracle).receive append env durable bytes =
        pure (.committed ingress admission witness)) :
    let planned := admission.accepted.prepared.planned
    let bound := admission.accepted.prepared.authorized.bound
    ∃ authorized, ComposedPolicyAdmission.admit (policyConfig planned)
      (request deployment planned.authority.snapshot planned.pay.cell profile.semantics env.ambient
        ingress.command planned.declaration)
      bound.evidence bound.law.witness bound.membership bound.epochExact bound.revisionExact =
        some authorized := by
  intro planned bound
  apply bound.admit_of_verifies
  obtain ⟨-, -, factoryLawful⟩ := committed_lawful committed
  obtain ⟨kind, -, judgedFactory⟩ := factoryLawful
  have notBirth := factoryPacked_not_birth planned
  rcases judgedFactory with ⟨-, judgedStep, law, stepEq, resolvedOf, lowerable, inRange, casts,
      evaluated⟩ | ⟨-, -, -, noStep⟩ | ⟨-, -, (⟨birth, -⟩ | ⟨-, -, noStep⟩)⟩
  · cases stepEq
    have resolved : (PayEnrolReceiver.laws deployment profile).resolve durable
        (factoryPacked planned.factory).cellId.value (step planned) = some law := by
      unfold ReceivingLaw.lawOf at resolvedOf
      rw [if_neg (by
        show ¬ (ReceivingLaw.physicalBirth durable (factoryPacked planned.factory) = true)
        rw [notBirth]; simp)] at resolvedOf
      exact resolvedOf
    obtain ⟨directory, authority, structural, sources, judged, directoryEq, authorityEq, -, -,
        judgedEq, rfl⟩ :=
      (ReceivingLaw.physical_resolve_some_iff _ _ _ _ _ _).1 resolved
    rw [planned.directoryExact] at directoryEq
    rw [planned.authorityExact] at authorityEq
    cases directoryEq
    cases authorityEq
    have restrictions : ((WorldKindLawDependencies.loadTarget deployment planned.directory.directory
        deployment.factoryId).map (·.additional) |>.getD []) = planned.dependencies.additional := by
      rw [planned.dependenciesExact]
      rfl
    simp only at lowerable inRange casts evaluated
    exact PhysicalLawResolution.bound_verifies_of_target_judged deployment profile.compilerProfile
      planned.authority.snapshot planned.directory.directory _ _ (step planned) deployment.factoryId
      planned.dependencies.additional restrictions judged judgedEq lowerable inRange casts evaluated
      bound
  · cases noStep
  · exact absurd (notBirth.symm.trans birth) (by simp)
  · cases noStep

/-- **The v2 memo's bits are the verifier's answers**: in every committed v2
payment, under any `Id` oracle, `verified.mini` and `verified.ssh` are the
verifier's answers on exactly the memo's two possession queries (Ed25519 over
the v2 frame, `SSHSIG` under the v2 namespace). -/
theorem committed_verified {laws : ReceivingLaw.Laws Durable}
    {oracle : CredentialSignatureIO.Oracle Id}
    {Exact : Durable → DataIntent rootBytes → Type} {Other : Type}
    {append : (state : Durable) → (intent : DataIntent rootBytes) →
      Id (Minidregg.Theory.Receiving.Receiver.Commit (Exact state intent) Other)}
    {bytes : List UInt8}
    {admission : ((payEnrolV2Family deployment profile).receiver laws oracle).Admitted env durable ingress}
    {witness : Exact durable (((payEnrolV2Family deployment profile).receiver laws oracle).intent
      admission.accepted)}
    (committed : ((payEnrolV2Family deployment profile).receiver laws oracle).receive append env
      durable bytes = pure (.committed ingress admission witness)) :
    CredentialSignatureAdmission.receiverVerify oracle
        (miniQuery ingress.command.observation admission.accepted.prepared.memo) =
      pure (.ok admission.accepted.prepared.verified.mini) ∧
    CredentialSignatureAdmission.receiverVerify oracle
        (sshQuery ingress.command.observation admission.accepted.prepared.memo) =
      pure (.ok admission.accepted.prepared.verified.ssh) := by
  have admitted := (((payEnrolV2Family deployment profile).receiver laws oracle).receive_committed
    committed).2.2.1
  obtain ⟨queries, observing, keys, answers⟩ :=
    ((payEnrolV2Family deployment profile).receiver laws oracle).admitVia_observed admitted
  have decided := prepare_verified (received := ⟨oracle, admission.vouchers⟩) admission.prepared.1
  obtain ⟨miniAnswer, sshAnswer⟩ := verifiedOf_answers decided
  exact ⟨answers _ (Vouchers.answer?_some miniAnswer), answers _ (Vouchers.answer?_some sshAnswer)⟩

end Committed

/-- The observer signs the actual source-prepared v2 decision.  The memo's bits
are asked of the same verifier on the same observed queries the Receiver asks.
Failure is returned before a signing plan is handed to the watcher. -/
def signingHeader {F : Type} [Field F] [DecidableEq F] (deployment : Deployment)
    (profile : CanonicalRuntimeProfile.Profile F) (ambient : Ambient) (seed : Digest)
    (durable : Durable) (native : CredentialSignatureIO.NativeConfig) (command : Command) :
    IO (Except String CredentialSignedEnvelopeController.SignedHeader) := do
  let some memo := parsedMemo command.observation | return .error "v2 payment memo malformed"
  match ← Minidregg.Theory.Receiving.Receiver.observeAll
      (CredentialSignatureAdmission.receiverVerify (.live native))
      [miniQuery command.observation memo, sshQuery command.observation memo] with
  | .error detail => return .error s!"v2 payment possession: {detail}"
  | .ok answered =>
    let answer := fun query => (answered.find? fun given => given.1 == query).map Prod.snd
    match verifiedOf answer command.observation memo with
    | .error reason => return .error s!"v2 payment possession: {repr reason}"
    | .ok verified =>
      match plan deployment profile ambient seed durable command memo verified with
      | .error reason => return .error s!"v2 payment preparation: {repr reason}"
      | .ok planned =>
        return (CredentialSignatureAdmission.signingHeader planned.authority.snapshot
          (marker deployment.domain profile.semantics command)
          ⟨.program, request deployment planned.authority.snapshot planned.pay.cell profile.semantics
            ambient command planned.declaration⟩).mapError
          (fun reason => s!"v2 payment observer key: {repr reason}")

#assert_axioms Planned.sound
#assert_axioms Prepared.sound
#assert_axioms verifiedOf_answers
#assert_axioms prepare_verified
#assert_axioms legs_writes_bound
#assert_axioms legs_factory_mem
#assert_axioms writes_bound
#assert_axioms lawStepOf_pay
#assert_axioms lawStepOf_clock
#assert_axioms lawStepOf_factory
#assert_axioms factoryPacked_mem
#assert_axioms factoryPacked_not_birth
#assert_axioms committed_lawful
#assert_axioms committed_admitted
#assert_axioms committed_verified

end Minidregg.Kernel.PayEnrolV2Receiver
