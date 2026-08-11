/-
# Kernel.ProviderExecutionLease -- prepaid proof-carrying provider execution

This module is a concrete consumer kernel for a cloud/provider execution lease.
It composes four existing semantic joints instead of inventing a second runtime
state machine:

* `CanonicalResourceKernel.Operation.lease` moves the exact prepaid value and
  installs the lease record;
* `AuthorizedResourceCharge` binds its complete ten-lane charge to authority
  and the payload-bearing durable write;
* `IrreversibleEffectSettlement` treats provider start and compensation as
  evidence-backed, fail-closed external commands;
* `ReactiveTerminalCell` makes completion, cancellation, expiry, compensation,
  and quarantine contend for one durable terminal/outbox/nullifier.

Provider evidence is not proof that a machine executed correctly.  Completion
evidence, physical handler refinement, eventual scheduling, availability, and
the separately authorized refund transition remain explicit boundaries below.
-/
import Kernel.AuthorizedResourceCharge
import Kernel.IrreversibleEffectSettlement
import Kernel.ReactiveTerminalCell

namespace Minidregg.Kernel.ProviderExecutionLease

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

/-! ## Canonical prepaid lease -/

structure Terms where
  leaseId : LeaseId
  holder : AccountId
  provider : AccountId
  asset : AssetId
  rate : Nat
  epochs : Nat
  startsAt : CanonicalResourceKernel.Epoch
  deriving DecidableEq, Repr

def Terms.prepaid (terms : Terms) : Nat := terms.rate * terms.epochs

def Terms.operation (terms : Terms) : Operation :=
  .lease terms.leaseId terms.holder terms.provider terms.asset
    terms.rate terms.epochs terms.startsAt

def Terms.refundOperation (terms : Terms) : Operation :=
  .transfer terms.provider terms.holder terms.asset terms.prepaid

/-- Stable identities and canonical open images for the provider lifecycle.
The start cell is a trigger/read-guard cell distinct from the terminal and
outbox pair. -/
structure Runtime where
  providerEndpoint : Digest
  imageRoot : Digest
  inputRoot : Digest
  prepayTransaction : TransactionId
  resourceCell : CellId
  startTransaction : Digest
  startCell : CellId
  terminalTransaction : TransactionId
  terminalNullifier : Digest
  terminalEvent : Digest
  terminalCell : CellId
  outboxCell : CellId
  clockCell : CellId
  openStartBytes : List UInt8
  openTerminalBytes : List UInt8
  openOutboxBytes : List UInt8
  prepayTerminalDistinct : prepayTransaction ≠ terminalTransaction
  terminalOutboxDistinct : terminalCell ≠ outboxCell
  terminalClockDistinct : terminalCell ≠ clockCell
  outboxClockDistinct : outboxCell ≠ clockCell
  terminalStartDistinct : terminalCell ≠ startCell
  outboxStartDistinct : outboxCell ≠ startCell

/-- An opened lease is indexed by the exact canonical pre-book.  Acceptance,
the tariff-derived request, and authority are all fields; neither a post-book
nor an executor charge is caller data. -/
structure OpenedLease
    (M : Materializer CanonicalResourceKernel.schema Digest)
    (portal : Portal) (authState : AuthState) (pre : Materialized M) where
  terms : Terms
  runtime : Runtime
  manifest : AuthorizedResourceCharge.DeploymentManifest
  requestContext : AuthorizedResourceCharge.RequestContext
  accepted : Accepted pre terms.operation
  authorization : Authorized portal authState
    (requestContext.request manifest accepted)

namespace OpenedLease

variable
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}

def prepaid
    (lease : OpenedLease M portal authState pre) : Nat :=
  lease.terms.prepaid

noncomputable def acceptedEffect
    (lease : OpenedLease M portal authState pre) :=
  AuthorizedResourceCharge.toCellEffect lease.manifest lease.accepted lease.requestContext
    lease.authorization

/-- Provider-specific replay nullifier.  Unlike the generic resource adapter,
this consumer consumes the authorization nonce durably, so changing the
transaction id cannot charge the same lease again. -/
def prepayNullifier
    (lease : OpenedLease M portal authState pre) : StableNullifier where
  codecVersion := lease.manifest.version
  domain := lease.manifest.semanticDigest
  nullifierId :=
    ⟨Nat.pair lease.requestContext.nonce lease.runtime.prepayTransaction.value⟩
  canonicalBytes := ReactiveTerminalCell.frame 180
    [ReactiveTerminalCell.encodeNat lease.requestContext.nonce,
      ReactiveTerminalCell.encodeDigest lease.runtime.prepayTransaction]

/-- Exact prepay intent: canonical resource post bytes, authorized ten-lane
charge, and the provider-specific replay nullifier. -/
def prepayIntent
    (lease : OpenedLease M portal authState pre) : DataIntent M.rootBytes :=
  { AuthorizedResourceCharge.durableIntent lease.runtime.prepayTransaction lease.runtime.resourceCell
      lease.manifest lease.accepted with
      nullifiers := [lease.prepayNullifier] }

@[simp] theorem prepayIntent_exactCharge
    (lease : OpenedLease M portal authState pre) :
    lease.prepayIntent.exactCharge = AuthorizedResourceCharge.exactCharge lease.manifest lease.accepted :=
  rfl

@[simp] theorem authorized_cost_is_prepay_fee
    (lease : OpenedLease M portal authState pre) :
    (lease.requestContext.request lease.manifest lease.accepted).cost =
      lease.prepayIntent.exactCharge .feeDebit :=
  rfl

@[simp] theorem prepay_retry_replays
    (lease : OpenedLease M portal authState pre)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before lease.prepayIntent) lease.prepayIntent =
      .replayed lease.prepayIntent.erase := by
  simp [DurableDataIntent.execute, DataSnapshot.install, Snapshot.install,
    Snapshot.lookupRecorded, Intent.sameCheck_self]

/-- An exact retry is observationally budget-idempotent; it cannot debit any
of the ten lanes twice. -/
theorem prepay_retry_preserves_budget
    (lease : OpenedLease M portal authState pre)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    ((DurableDataIntent.execute schedule
        (DataSnapshot.install before lease.prepayIntent) lease.prepayIntent).storeAfter
      (DataSnapshot.install before lease.prepayIntent)).model.available =
      (DataSnapshot.install before lease.prepayIntent).model.available := by
  rw [prepay_retry_replays]
  rfl

/-- Same payload under a new transaction id.  It is useful only for the
negative replay tooth below; no API returns it as an accepted plan. -/
def rekeyPrepay (lease : OpenedLease M portal authState pre)
    (newTransaction : TransactionId) : DataIntent M.rootBytes :=
  { lease.prepayIntent with transactionId := newTransaction }

@[simp] theorem rekeyPrepay_transactionId
    (lease : OpenedLease M portal authState pre)
    (newTransaction : TransactionId) :
    (rekeyPrepay lease newTransaction).transactionId = newTransaction :=
  rfl

/-- After one installation, the provider prepay nullifier is definitively not
fresh for a re-keyed transaction.  Exact same-id retry is handled by the
journal theorem above; changing the id therefore cannot bypass the replay
gate and debit again. -/
@[simp] theorem installed_rekey_nullifier_not_fresh
    (lease : OpenedLease M portal authState pre)
    (newTransaction : TransactionId) (before : DataSnapshot M.rootBytes) :
    (rekeyPrepay lease newTransaction).erase.nullifiersFreshCheck
        (DataSnapshot.install before lease.prepayIntent).model = false := by
  simp [rekeyPrepay, prepayIntent, prepayNullifier,
    DurableCommitProtocol.Intent.nullifiersFreshCheck,
    DataSnapshot.install, Snapshot.install]

theorem installed_rekey_preflight_rejects
    (lease : OpenedLease M portal authState pre)
    (newTransaction : TransactionId) (before : DataSnapshot M.rootBytes) :
    (rekeyPrepay lease newTransaction).preflight
        (DataSnapshot.install before lease.prepayIntent) ≠ .ok () := by
  simp [DataIntent.preflight, DurableCommitProtocol.Intent.preflight,
    rekeyPrepay, prepayIntent, prepayNullifier,
    DurableCommitProtocol.Intent.rootsMatchCheck,
    DurableCommitProtocol.Intent.nullifiersFreshCheck,
    DataSnapshot.install, Snapshot.install]
  split <;> simp_all
  all_goals aesop

theorem rekeyed_prepay_cannot_accept_twice
    (lease : OpenedLease M portal authState pre)
    (newTransaction : TransactionId)
    (different : newTransaction ≠ lease.runtime.prepayTransaction)
    (before : DataSnapshot M.rootBytes)
    (newUnrecorded : Snapshot.lookupRecorded newTransaction
      before.model.journal = none)
    (schedule : Schedule) (next : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before lease.prepayIntent)
        (rekeyPrepay lease newTransaction) ≠ .accepted next := by
  have lookup : Snapshot.lookupRecorded newTransaction
      (DataSnapshot.install before lease.prepayIntent).model.journal = none := by
    have oldNe : lease.prepayIntent.transactionId ≠ newTransaction := by
      simpa [prepayIntent] using different.symm
    simp [DataSnapshot.install, Snapshot.install, Snapshot.lookupRecorded,
      oldNe, newUnrecorded]
  unfold DurableDataIntent.execute
  simp only [rekeyPrepay_transactionId]
  rw [lookup]
  cases preflightEq : (rekeyPrepay lease newTransaction).preflight
      (DataSnapshot.install before lease.prepayIntent) with
  | error reason => simp
  | ok _ =>
      exact (installed_rekey_preflight_rejects lease newTransaction before
        preflightEq).elim

@[simp] theorem post_installs_exact_lease_record
    (lease : OpenedLease M portal authState pre) :
    (logicalBook lease.accepted.post.logical).leases lease.terms.leaseId =
      some
        { holder := lease.terms.holder
          lessor := lease.terms.provider
          asset := lease.terms.asset
          prepaid := lease.terms.prepaid
          startsAt := lease.terms.startsAt
          expiresAt := lease.terms.startsAt + lease.terms.epochs } := by
  rw [lease.accepted.post_logicalBook]
  exact lease_installs_exact_record _ _ _ _ _ _ _ _

/-- Conditional adapter to fee-first admission.  It does not manufacture a
fee-account payload; an actual well-formed prologue must be supplied and shown
to carry exactly the tariff-derived fee projection. -/
structure FeeFirstEnvelope (lease : OpenedLease M portal authState pre) where
  request : AdmissionPrologue.Request M.rootBytes
  wellFormed : request.WellFormed
  prologueExact : request.prologue.exactCharge =
    AuthorizedResourceCharge.admissionCharge lease.manifest lease.accepted
  bodyExact : request.body =
    AuthorizedResourceCharge.admissionBodyIntent lease.runtime.prepayTransaction
      lease.runtime.resourceCell lease.manifest lease.accepted

theorem FeeFirstEnvelope.exact_split
    {lease : OpenedLease M portal authState pre}
    (envelope : FeeFirstEnvelope lease) :
    (lease.requestContext.request lease.manifest lease.accepted).cost =
        envelope.request.prologue.exactCharge .feeDebit /\
      envelope.request.body.exactCharge .feeDebit = 0 /\
      envelope.request.prologue.exactCharge + envelope.request.body.exactCharge =
        AuthorizedResourceCharge.exactCharge lease.manifest lease.accepted :=
  AuthorizedResourceCharge.admissionPrologue_exact_split lease.runtime.prepayTransaction
    lease.runtime.resourceCell lease.requestContext lease.manifest lease.accepted
    envelope.request envelope.wellFormed envelope.prologueExact envelope.bodyExact

end OpenedLease

/-! ## Exact external provider start -/

inductive EffectClass
  | providerExecution
  deriving DecidableEq, Repr

structure StartAction where
  leaseId : LeaseId
  endpoint : Digest
  imageRoot : Digest
  inputRoot : Digest
  prepaid : Nat
  deriving DecidableEq, Repr

structure Compensation where
  leaseId : LeaseId
  endpoint : Digest
  refundTo : AccountId
  asset : AssetId
  amount : Nat
  deriving DecidableEq, Repr

structure StartReceipt where
  runId : Digest
  providerEvidenceRoot : Digest
  deriving DecidableEq, Repr

inductive StartFailure
  | refused
  | unavailable
  | imageRejected
  deriving DecidableEq, Repr

abbrev StartIntent :=
  IrreversibleEffectSettlement.Intent Digest Digest EffectClass Digest StartAction Compensation Digest

abbrev StartGrant :=
  IrreversibleEffectSettlement.Grant Digest Digest EffectClass Digest StartAction Compensation

abbrev StartBoundary :=
  IrreversibleEffectSettlement.HandlerBoundary Digest Digest EffectClass Digest StartAction Compensation
    Digest StartReceipt StartFailure Digest

abbrev StartObserved (boundary : StartBoundary) (intent : StartIntent) :=
  IrreversibleEffectSettlement.Observed boundary (.forward intent)

def startAction
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (lease : OpenedLease M portal authState pre) : StartAction where
  leaseId := lease.terms.leaseId
  endpoint := lease.runtime.providerEndpoint
  imageRoot := lease.runtime.imageRoot
  inputRoot := lease.runtime.inputRoot
  prepaid := lease.prepaid

def compensation
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (lease : OpenedLease M portal authState pre) : Compensation where
  leaseId := lease.terms.leaseId
  endpoint := lease.runtime.providerEndpoint
  refundTo := lease.terms.holder
  asset := lease.terms.asset
  amount := lease.prepaid

def runningBytes
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (lease : OpenedLease M portal authState pre) : List UInt8 :=
  ReactiveTerminalCell.frame 181 [ReactiveTerminalCell.encodeNat lease.manifest.version,
    ReactiveTerminalCell.encodeNat lease.terms.leaseId,
    ReactiveTerminalCell.encodeDigest lease.runtime.providerEndpoint,
    ReactiveTerminalCell.encodeDigest lease.runtime.imageRoot,
    ReactiveTerminalCell.encodeDigest lease.runtime.inputRoot,
    ReactiveTerminalCell.encodeNat lease.prepaid]

def startIntent
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (lease : OpenedLease M portal authState pre)
    (height attempt : Nat) : StartIntent where
  transactionId := lease.runtime.startTransaction
  principal := ⟨lease.terms.holder⟩
  effectClass := .providerExecution
  target := lease.runtime.providerEndpoint
  action := startAction lease
  compensation := some (compensation lease)
  height := height
  attempt := attempt
  expectedPreRoot := M.rootBytes lease.runtime.openStartBytes
  exactPostRoot := M.rootBytes (runningBytes lease)

/-- One fully authorized observed provider-start attempt.  `currentRoot` is
read at settlement time, so a provider success racing a logical change is
quarantined by `IrreversibleEffectSettlement`. -/
structure StartAttempt
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (lease : OpenedLease M portal authState pre) (boundary : StartBoundary) where
  height : Nat
  attempt : Nat
  grant : StartGrant
  authorized : grant.Authorizes (startIntent lease height attempt)
  currentRoot : Digest
  forward : StartObserved boundary (startIntent lease height attempt)
  plan : IrreversibleEffectSettlement.Plan boundary (startIntent lease height attempt)

namespace StartAttempt

variable
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}

def settlement (attempt : StartAttempt lease boundary) :=
  IrreversibleEffectSettlement.settle boundary attempt.grant
    (startIntent lease attempt.height attempt.attempt) attempt.authorized
    attempt.currentRoot attempt.forward attempt.plan

end StartAttempt

/-! ## Completion, cancel, expiry, compensation, and quarantine -/

structure CompletionClaim where
  runId : Digest
  outputRoot : Digest
  usageRoot : Digest
  providerEvidenceRoot : Digest
  deriving DecidableEq, Repr

/-- Completion evidence is indexed by the exact start attempt.  The boundary
is intentionally abstract: a production provider must refine it below. -/
structure CompletionBoundary
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {startBoundary : StartBoundary}
    (attempt : StartAttempt lease startBoundary) where
  Evidence : CompletionClaim → Prop
  rootBound : ∀ claim, Evidence claim →
    claim.providerEvidenceRoot =
      ⟨Nat.pair claim.runId.value
        (Nat.pair claim.outputRoot.value claim.usageRoot.value)⟩

def statusTag : IrreversibleEffectSettlement.Status → Nat
  | .committed => 0
  | .refused => 1
  | .compensated => 2
  | .quarantinedForward => 3
  | .quarantinedStale => 4
  | .quarantinedCompensation => 5

/-- Receipt digest used by cancellation/expiry/quarantine terminal records.
It commits the exact external transaction, before/after roots, intended root,
and status. -/
def startSettlementDigest
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    (attempt : StartAttempt lease boundary) : Digest :=
  let receipt := attempt.settlement.toReceipt
  ⟨Nat.pair receipt.transactionId.value
    (Nat.pair receipt.logicalBefore.value
      (Nat.pair receipt.logicalAfter.value
        (Nat.pair receipt.intendedPost.value (statusTag receipt.status))))⟩

def QuarantinedStatus : IrreversibleEffectSettlement.Status → Prop
  | .quarantinedForward | .quarantinedStale | .quarantinedCompensation => True
  | _ => False

/-- Exactly one provider lifecycle reason selects a terminal kind.  Completion
requires both a committed start and completion evidence.  Cancellation is
allowed only after a definitely refused start; compensation requires the exact
compensated status.  Uncertain/stale provider outcomes become `broken`, never
successful or automatically refundable. -/
inductive Outcome
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    (attempt : StartAttempt lease boundary)
    (completion : CompletionBoundary attempt)
    (deadline settledAt : Nat) where
  | completed (claim : CompletionClaim)
      (evidence : completion.Evidence claim)
      (startCommitted : attempt.settlement.status = .committed)
      (within : settledAt ≤ deadline)
  | cancelled
      (startRefused : attempt.settlement.status = .refused)
      (within : settledAt ≤ deadline)
  | compensated
      (compensationPerformed : attempt.settlement.status = .compensated)
      (within : settledAt ≤ deadline)
  | expired (after : deadline < settledAt)
  | quarantined
      (quarantineProof : QuarantinedStatus attempt.settlement.status)
      (within : settledAt ≤ deadline)

namespace Outcome

variable
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline settledAt : Nat}

def terminalKind : Outcome attempt completion deadline settledAt → ReactiveTerminalCell.TerminalKind
  | .completed .. => .finalized
  | .cancelled .. => .cancelled
  | .compensated .. => .cancelled
  | .expired .. => .expired
  | .quarantined .. => .broken

def decision : (outcome : Outcome attempt completion deadline settledAt) →
    ReactiveTerminalCell.Decision deadline settledAt
  | .completed _ _ _ within => .finalize within
  | .cancelled _ within => .cancel within
  | .compensated _ within => .cancel within
  | .expired after => .expire after
  | .quarantined _ within => .broken within

def evidenceRoot : Outcome attempt completion deadline settledAt → Digest
  | .completed claim .. => claim.providerEvidenceRoot
  | .cancelled .. => startSettlementDigest attempt
  | .compensated .. => startSettlementDigest attempt
  | .expired .. => startSettlementDigest attempt
  | .quarantined .. => startSettlementDigest attempt

/-- Refund is a separate authorized semantic turn for cancel, compensation,
or expiry.  Quarantine does not automatically refund because provider action
is uncertain; completion consumes the prepaid lease normally. -/
def RefundDue : Outcome attempt completion deadline settledAt → Prop
  | .cancelled .. | .compensated .. | .expired .. => True
  | .completed .. | .quarantined .. => False

@[simp] theorem completed_not_refundable
    (claim : CompletionClaim) (evidence : completion.Evidence claim)
    (committed : attempt.settlement.status = .committed)
    (within : settledAt ≤ deadline) :
    ¬ RefundDue (.completed claim evidence committed within) := by
  simp [RefundDue]

@[simp] theorem quarantined_not_automatic_refund
    (quarantineProof : QuarantinedStatus attempt.settlement.status)
    (within : settledAt ≤ deadline) :
    ¬ RefundDue
      (.quarantined quarantineProof within :
        Outcome attempt completion deadline settledAt) := by
  simp [RefundDue]

end Outcome

/-! ## Exact terminal/outbox settlement -/

def promiseId
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (lease : OpenedLease M portal authState pre) : Digest :=
  ⟨Nat.pair lease.terms.leaseId lease.runtime.providerEndpoint.value⟩

/-- Terminal settlement is bookkeeping for already prepaid work.  Its charge
is zero: the authorized ten-lane debit occurs exactly once in `prepayIntent`.
A deployment wanting a separately priced terminal operation must authorize a
second charged request rather than smuggling cost here. -/
def terminalOpenCell
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (lease : OpenedLease M portal authState pre) (deadline : Nat) : ReactiveTerminalCell.OpenCell where
  codecVersion := lease.manifest.version
  domain := lease.manifest.eventCodecId
  promiseId := promiseId lease
  deadline := deadline
  transactionId := lease.runtime.terminalTransaction
  nullifierId := lease.runtime.terminalNullifier
  eventId := lease.runtime.terminalEvent
  terminalCell := lease.runtime.terminalCell
  outboxCell := lease.runtime.outboxCell
  clockCell := lease.runtime.clockCell
  triggerCell := lease.runtime.startCell
  openTerminalBytes := lease.runtime.openTerminalBytes
  openOutboxBytes := lease.runtime.openOutboxBytes
  exactCharge := 0
  terminalOutboxDistinct := lease.runtime.terminalOutboxDistinct
  terminalClockDistinct := lease.runtime.terminalClockDistinct
  outboxClockDistinct := lease.runtime.outboxClockDistinct
  terminalTriggerDistinct := lease.runtime.terminalStartDistinct
  outboxTriggerDistinct := lease.runtime.outboxStartDistinct

@[simp] theorem prepay_and_terminal_transactions_distinct
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    (lease : OpenedLease M portal authState pre) (deadline : Nat) :
    lease.prepayIntent.transactionId ≠
      (terminalOpenCell lease deadline).transactionId :=
  lease.runtime.prepayTerminalDistinct

def terminalPlan
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline settledAt : Nat}
    (outcome : Outcome attempt completion deadline settledAt) :
    ReactiveTerminalCell.Plan M.rootBytes (terminalOpenCell lease deadline) where
  settledAt := settledAt
  decision := outcome.decision
  evidenceRoot := outcome.evidenceRoot
  triggerRoot := attempt.settlement.logicalRoot

@[simp] theorem terminalPlan_kind
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline settledAt : Nat}
    (outcome : Outcome attempt completion deadline settledAt) :
    (terminalPlan outcome).kind = outcome.terminalKind := by
  cases outcome <;> rfl

theorem terminal_and_outbox_atomic
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline settledAt : Nat}
    (outcome : Outcome attempt completion deadline settledAt)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    (DurableDataIntent.execute schedule before (terminalPlan outcome).intent).storeAfter
        before = before \/
      (DurableDataIntent.execute schedule before (terminalPlan outcome).intent).storeAfter
        before = DataSnapshot.install before (terminalPlan outcome).intent :=
  ReactiveTerminalCell.Plan.terminal_and_outbox_atomic (terminalPlan outcome) schedule before

@[simp] theorem terminal_retry_replays
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline settledAt : Nat}
    (outcome : Outcome attempt completion deadline settledAt)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before (terminalPlan outcome).intent)
        (terminalPlan outcome).intent =
      .replayed (terminalPlan outcome).intent.erase :=
  ReactiveTerminalCell.Plan.retry_after_install (terminalPlan outcome) schedule before

theorem distinct_provider_terminals_conflict
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline leftAt rightAt : Nat}
    (left : Outcome attempt completion deadline leftAt)
    (right : Outcome attempt completion deadline rightAt)
    (different : left.terminalKind ≠ right.terminalKind)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before (terminalPlan left).intent)
        (terminalPlan right).intent =
      .rejected (.durable .transactionConflict) := by
  exact ReactiveTerminalCell.competing_decision_conflicts (terminalPlan left) (terminalPlan right)
    (by simpa [terminalPlan_kind] using different) schedule before

@[simp] theorem terminal_settlement_has_no_second_charge
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline settledAt : Nat}
    (outcome : Outcome attempt completion deadline settledAt) :
    (terminalPlan outcome).intent.exactCharge = 0 :=
  rfl

@[simp] theorem terminal_exact_writes_and_nullifier
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline settledAt : Nat}
    (outcome : Outcome attempt completion deadline settledAt) :
    (terminalPlan outcome).intent.writes =
        [(terminalPlan outcome).terminalWrite, (terminalPlan outcome).outboxWrite] /\
      (terminalPlan outcome).intent.nullifiers =
        [(terminalPlan outcome).nullifier] :=
  ⟨rfl, rfl⟩

/-! ## Separately authorized canonical refund -/

theorem refundOperation_ne_operation (terms : Terms) :
    terms.refundOperation ≠ terms.operation := by
  cases terms
  simp [Terms.refundOperation, Terms.operation]

/-- A refund is not implied by a terminal tag.  A refundable outcome must be
joined to a second canonical accepted resource operation and fresh authority.
This also means a quarantined/uncertain provider action cannot silently mint
or transfer value. -/
structure RefundPlan
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline settledAt : Nat}
    (outcome : Outcome attempt completion deadline settledAt)
    (_due : outcome.RefundDue) where
  transactionId : TransactionId
  resourceCell : CellId
  requestContext : AuthorizedResourceCharge.RequestContext
  accepted : Accepted lease.accepted.post lease.terms.refundOperation
  authorization : Authorized portal authState
    (requestContext.request lease.manifest accepted)

namespace RefundPlan

variable
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline settledAt : Nat}
    {outcome : Outcome attempt completion deadline settledAt}
    {due : outcome.RefundDue}

noncomputable def acceptedEffect (refund : RefundPlan outcome due) :=
  AuthorizedResourceCharge.toCellEffect lease.manifest refund.accepted
    refund.requestContext refund.authorization

def nullifier (refund : RefundPlan outcome due) : StableNullifier where
  codecVersion := lease.manifest.version
  domain := lease.manifest.semanticDigest
  nullifierId :=
    ⟨Nat.pair refund.requestContext.nonce refund.transactionId.value⟩
  canonicalBytes := ReactiveTerminalCell.frame 182
    [ReactiveTerminalCell.encodeNat refund.requestContext.nonce,
      ReactiveTerminalCell.encodeDigest refund.transactionId]

def intent (refund : RefundPlan outcome due) : DataIntent M.rootBytes :=
  { AuthorizedResourceCharge.durableIntent refund.transactionId refund.resourceCell
      lease.manifest refund.accepted with
      nullifiers := [refund.nullifier] }

@[simp] theorem exact_charge (refund : RefundPlan outcome due) :
    refund.intent.exactCharge =
      AuthorizedResourceCharge.exactCharge lease.manifest refund.accepted :=
  rfl

/-- The refund cannot reuse the prepay authorization request: their argument
commitments decode to disjoint resource-operation constructors. -/
theorem request_ne_prepay (refund : RefundPlan outcome due) :
    refund.requestContext.request lease.manifest refund.accepted ≠
      lease.requestContext.request lease.manifest lease.accepted := by
  intro same
  have args := congrArg (fun request : Request .account => request.argsDigest) same
  have operations := CanonicalResourceEffect.argsDigest_injective args
  exact refundOperation_ne_operation lease.terms operations

theorem conserves_asset (refund : RefundPlan outcome due) (asset : AssetId) :
    (logicalBook refund.accepted.post.logical).totalAsset asset =
      (logicalBook lease.accepted.post.logical).totalAsset asset :=
  refund.accepted.conserves asset

@[simp] theorem exact_retry_replays (refund : RefundPlan outcome due)
    (schedule : Schedule) (before : DataSnapshot M.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before refund.intent) refund.intent =
      .replayed refund.intent.erase := by
  simp [DurableDataIntent.execute, DataSnapshot.install, Snapshot.install,
    Snapshot.lookupRecorded, Intent.sameCheck_self]

end RefundPlan

/-! ## Explicit evidence, physical, liveness, and refund ceilings -/

/-- The application decides what physical run a completion claim represents.
No `CompletionBoundary.Evidence` is sound without this separately supplied
relation and refinement. -/
structure CompletionRefinement
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    (completion : CompletionBoundary attempt)
    (PhysicalRun : Type)
    (Represents : PhysicalRun → CompletionClaim → Prop) : Prop where
  evidenceSound : ∀ claim, completion.Evidence claim →
    ∃ run, Represents run claim

/-- Safety and retry theorems do not imply provider progress. -/
structure LivenessRefinement
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    (Enabled : StartAttempt lease boundary → Prop)
    (EventuallyTerminal : StartAttempt lease boundary → Prop) : Prop where
  progresses : ∀ attempt, Enabled attempt → EventuallyTerminal attempt

/-- Physical atomicity is conditional on the existing payload-bearing durable
simulation.  This wrapper covers the exact provider terminal/outbox intent. -/
theorem physical_terminal_step_atomic
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline settledAt : Nat}
    (outcome : Outcome attempt completion deadline settledAt)
    {PhysicalState : Type} {PhysicalStep : PhysicalState →
      DataIntent M.rootBytes → PhysicalState → Type}
    {Represents : PhysicalState → DataSnapshot M.rootBytes → Prop}
    (refinement : DurableDataIntent.ImplementationRefinement
      M.rootBytes PhysicalState PhysicalStep Represents)
    {physicalBefore physicalAfter : PhysicalState}
    {modelBefore : DataSnapshot M.rootBytes}
    (represented : Represents physicalBefore modelBefore)
    (stepped : PhysicalStep physicalBefore (terminalPlan outcome).intent physicalAfter) :
    ∃ modelAfter,
      Represents physicalAfter modelAfter /\
      (modelAfter = modelBefore \/
        modelAfter = DataSnapshot.install modelBefore (terminalPlan outcome).intent) /\
      (∀ cellId, M.rootBytes (modelAfter.canonicalBytes cellId) =
        modelAfter.model.roots cellId) :=
  ReactiveTerminalCell.physical_step_terminal_atomic
    (terminalPlan outcome) refinement represented stepped

/-! ## Closed positive and failure witnesses -/

namespace Witness

def terms : Terms where
  leaseId := 0
  holder := 1
  provider := 2
  asset := 0
  rate := 1
  epochs := 2
  startsAt := 0

def runtime : Runtime where
  providerEndpoint := ⟨40⟩
  imageRoot := ⟨41⟩
  inputRoot := ⟨42⟩
  prepayTransaction := ⟨50⟩
  resourceCell := ⟨51⟩
  startTransaction := ⟨52⟩
  startCell := ⟨53⟩
  terminalTransaction := ⟨54⟩
  terminalNullifier := ⟨55⟩
  terminalEvent := ⟨56⟩
  terminalCell := ⟨57⟩
  outboxCell := ⟨58⟩
  clockCell := ⟨59⟩
  openStartBytes := [0]
  openTerminalBytes := [0, 0]
  openOutboxBytes := [0, 0, 0]
  prepayTerminalDistinct := by decide
  terminalOutboxDistinct := by decide
  terminalClockDistinct := by decide
  outboxClockDistinct := by decide
  terminalStartDistinct := by decide
  outboxStartDistinct := by decide

def leaseAdmission : Admission witnessBook terms.operation where
  sourcePresent := by decide
  destinationPresent := by decide
  sourceSolvent := Or.inr (by decide)
  leaseWellFormed := by
    change 0 < terms.epochs /\ witnessBook.leases terms.leaseId = none
    decide

noncomputable def accepted :
    Accepted witnessCell terms.operation :=
  Accepted.ofAdmission (by simpa using leaseAdmission)

def requestContext : AuthorizedResourceCharge.RequestContext where
  domain := ⟨1⟩
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 2
  nonce := 61
  height := 10
  policyId := ⟨9⟩
  policyEpoch := 5

noncomputable def authorization :
    Authorized demoPortal demoState
      (requestContext.request AuthorizedResourceCharge.witnessManifest accepted) where
  evidence := .signature () rfl rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

noncomputable def lease :
    OpenedLease CanonicalResourceKernel.materializer demoPortal demoState witnessCell where
  terms := terms
  runtime := runtime
  manifest := AuthorizedResourceCharge.witnessManifest
  requestContext := requestContext
  accepted := accepted
  authorization := authorization

noncomputable def chargedLeaseEffect := lease.acceptedEffect

example : lease.prepayIntent.nullifiers = [lease.prepayNullifier] :=
  rfl

example :
    (logicalBook lease.accepted.post.logical).leases lease.terms.leaseId =
      some
        { holder := lease.terms.holder
          lessor := lease.terms.provider
          asset := lease.terms.asset
          prepaid := lease.terms.prepaid
          startsAt := lease.terms.startsAt
          expiresAt := lease.terms.startsAt + lease.terms.epochs } :=
  lease.post_installs_exact_lease_record

noncomputable def startGrant : StartGrant where
  grantId := ⟨70⟩
  principal := ⟨terms.holder⟩
  effectClass := .providerExecution
  target := runtime.providerEndpoint
  actions := {startAction lease}
  compensations := {compensation lease}
  notBefore := 10
  notAfter := 20
  maxAttempt := 2

def startBoundary : StartBoundary where
  Evidence := fun _ _ => Unit

noncomputable def startAuthorized :
    startGrant.Authorizes (startIntent lease 12 1) where
  principal := rfl
  effectClass := rfl
  target := rfl
  action := by
    change startAction lease ∈ ({startAction lease} : Finset StartAction)
    simp
  validFrom := by decide
  validUntil := by decide
  attempt := by decide
  compensation := by
    intro request exact
    simp [startIntent] at exact
    subst request
    simp [startGrant]

def forwardPerformed :
    StartObserved startBoundary (startIntent lease 12 1) :=
  ⟨.performed { runId := ⟨80⟩, providerEvidenceRoot := ⟨81⟩ }, ()⟩

noncomputable def completedAttempt : StartAttempt lease startBoundary where
  height := 12
  attempt := 1
  grant := startGrant
  authorized := startAuthorized
  currentRoot := (startIntent lease 12 1).expectedPreRoot
  forward := forwardPerformed
  plan := .commit

def completionBoundary : CompletionBoundary completedAttempt where
  Evidence := fun claim => claim.providerEvidenceRoot =
    ⟨Nat.pair claim.runId.value
      (Nat.pair claim.outputRoot.value claim.usageRoot.value)⟩
  rootBound := fun _ evidence => evidence

def completionClaim : CompletionClaim where
  runId := ⟨0⟩
  outputRoot := ⟨0⟩
  usageRoot := ⟨0⟩
  providerEvidenceRoot := ⟨0⟩

noncomputable def completedOutcome :
  Outcome completedAttempt completionBoundary 20 19 :=
  .completed completionClaim rfl rfl (by decide)

noncomputable def completedPlan := terminalPlan completedOutcome

noncomputable def terminalBeforeBytes (cellId : CellId) : List UInt8 :=
  if cellId = runtime.terminalCell then runtime.openTerminalBytes
  else if cellId = runtime.outboxCell then runtime.openOutboxBytes
  else if cellId = runtime.clockCell then completedPlan.clockBytes
  else if cellId = runtime.startCell then
    List.replicate completedPlan.triggerRoot.value 0
  else []

noncomputable def terminalBeforeModel :
    Snapshot TransactionId CellId StableNullifier ReplayEnvelope where
  roots := fun cellId => CanonicalResourceKernel.materializer.rootBytes
    (terminalBeforeBytes cellId)
  consumed := fun _ => false
  available := 0
  history := []
  journal := []

noncomputable def terminalBefore :
    DataSnapshot CanonicalResourceKernel.materializer.rootBytes where
  model := terminalBeforeModel
  canonicalBytes := terminalBeforeBytes
  coherent := fun _ => rfl

@[simp] theorem completed_status_committed :
    completedAttempt.settlement.status = .committed :=
  rfl

@[simp] theorem completed_maps_finalized :
    completedPlan.kind = .finalized :=
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
@[simp] theorem completed_ready :
    completedPlan.intent.preflight terminalBefore = .ok () := by
  decide

@[simp] theorem completed_commits_terminal_and_outbox :
    DurableDataIntent.execute .complete terminalBefore completedPlan.intent =
      .accepted (DataSnapshot.install terminalBefore completedPlan.intent) :=
  ReactiveTerminalCell.Plan.complete_ready completedPlan terminalBefore
    (by decide) completed_ready

@[simp] theorem completed_retry_does_not_charge_again :
    DurableDataIntent.execute .complete
        (DataSnapshot.install terminalBefore completedPlan.intent)
        completedPlan.intent = .replayed completedPlan.intent.erase :=
  terminal_retry_replays completedOutcome .complete terminalBefore

noncomputable def expiredOutcome :
    Outcome completedAttempt completionBoundary 20 21 :=
  .expired (by decide)

noncomputable def expiredPlan := terminalPlan expiredOutcome

@[simp] theorem expiry_loses_completed_race :
    DurableDataIntent.execute .complete
        (DataSnapshot.install terminalBefore completedPlan.intent)
        expiredPlan.intent = .rejected (.durable .transactionConflict) := by
  exact distinct_provider_terminals_conflict completedOutcome expiredOutcome
    (by decide) .complete terminalBefore

def forwardRefused :
    StartObserved startBoundary (startIntent lease 12 1) :=
  ⟨.notPerformed .refused, ()⟩

noncomputable def refusedAttempt : StartAttempt lease startBoundary where
  height := 12
  attempt := 1
  grant := startGrant
  authorized := startAuthorized
  currentRoot := (startIntent lease 12 1).expectedPreRoot
  forward := forwardRefused
  plan := .commit

def refusedCompletionBoundary : CompletionBoundary refusedAttempt where
  Evidence := fun claim => claim.providerEvidenceRoot =
    ⟨Nat.pair claim.runId.value
      (Nat.pair claim.outputRoot.value claim.usageRoot.value)⟩
  rootBound := fun _ evidence => evidence

noncomputable def cancelledOutcome :
    Outcome refusedAttempt refusedCompletionBoundary 20 13 :=
  .cancelled rfl (by decide)

@[simp] theorem refused_cannot_report_committed :
    refusedAttempt.settlement.status ≠ .committed := by
  decide

@[simp] theorem refused_maps_cancelled :
    (terminalPlan cancelledOutcome).kind = .cancelled :=
  rfl

def compensationObserved :
    IrreversibleEffectSettlement.Observed startBoundary
      (.compensate (startIntent lease 12 1) (compensation lease)) :=
  ⟨.performed { runId := ⟨85⟩, providerEvidenceRoot := ⟨86⟩ }, ()⟩

noncomputable def compensatedAttempt : StartAttempt lease startBoundary where
  height := 12
  attempt := 1
  grant := startGrant
  authorized := startAuthorized
  currentRoot := (startIntent lease 12 1).expectedPreRoot
  forward := forwardPerformed
  plan := .compensate (compensation lease) rfl compensationObserved

def compensatedCompletionBoundary : CompletionBoundary compensatedAttempt where
  Evidence := fun claim => claim.providerEvidenceRoot =
    ⟨Nat.pair claim.runId.value
      (Nat.pair claim.outputRoot.value claim.usageRoot.value)⟩
  rootBound := fun _ evidence => evidence

noncomputable def compensatedOutcome :
    Outcome compensatedAttempt compensatedCompletionBoundary 20 14 :=
  .compensated rfl (by decide)

@[simp] theorem compensated_preserves_start_root :
    compensatedAttempt.settlement.logicalRoot =
      (startIntent lease 12 1).expectedPreRoot :=
  rfl

@[simp] theorem compensated_maps_cancelled :
    (terminalPlan compensatedOutcome).kind = .cancelled :=
  rfl

def forwardUncertain :
    StartObserved startBoundary (startIntent lease 12 1) :=
  ⟨.indeterminate ⟨404⟩, ()⟩

noncomputable def uncertainAttempt : StartAttempt lease startBoundary where
  height := 12
  attempt := 1
  grant := startGrant
  authorized := startAuthorized
  currentRoot := (startIntent lease 12 1).expectedPreRoot
  forward := forwardUncertain
  plan := .commit

def uncertainCompletionBoundary : CompletionBoundary uncertainAttempt where
  Evidence := fun claim => claim.providerEvidenceRoot =
    ⟨Nat.pair claim.runId.value
      (Nat.pair claim.outputRoot.value claim.usageRoot.value)⟩
  rootBound := fun _ evidence => evidence

noncomputable def quarantinedOutcome :
    Outcome uncertainAttempt uncertainCompletionBoundary 20 15 :=
  .quarantined trivial (by decide)

@[simp] theorem uncertainty_maps_broken_not_refund :
    (terminalPlan quarantinedOutcome).kind = .broken /\
      ¬ quarantinedOutcome.RefundDue := by
  constructor
  · rfl
  · unfold quarantinedOutcome Outcome.RefundDue
    simp

theorem expired_refund_due : expiredOutcome.RefundDue := by
  unfold expiredOutcome Outcome.RefundDue
  trivial

def refundAdmission :
    Admission (logicalBook accepted.post.logical) terms.refundOperation where
  sourcePresent := by
    rw [accepted.post_logicalBook]
    decide
  destinationPresent := by
    rw [accepted.post_logicalBook]
    decide
  sourceSolvent := Or.inr (by
    rw [accepted.post_logicalBook]
    decide)
  leaseWellFormed := trivial

noncomputable def refundAccepted :
    Accepted accepted.post terms.refundOperation :=
  Accepted.ofAdmission refundAdmission

def refundContext : AuthorizedResourceCharge.RequestContext where
  domain := ⟨1⟩
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 2
  nonce := 87
  height := 21
  policyId := ⟨9⟩
  policyEpoch := 5

noncomputable def refundAuthorization :
    Authorized demoPortal demoState
      (refundContext.request AuthorizedResourceCharge.witnessManifest
        refundAccepted) where
  evidence := .signature () rfl rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

noncomputable def refundPlan :
    RefundPlan expiredOutcome expired_refund_due where
  transactionId := ⟨88⟩
  resourceCell := runtime.resourceCell
  requestContext := refundContext
  accepted := refundAccepted
  authorization := refundAuthorization

@[simp] theorem refund_requires_distinct_authority :
    refundPlan.requestContext.request lease.manifest refundPlan.accepted ≠
      lease.requestContext.request lease.manifest lease.accepted :=
  refundPlan.request_ne_prepay

@[simp] theorem exact_prepay_retry_replays
    (schedule : Schedule)
    (before : DataSnapshot CanonicalResourceKernel.materializer.rootBytes) :
    DurableDataIntent.execute schedule
        (DataSnapshot.install before lease.prepayIntent) lease.prepayIntent =
      .replayed lease.prepayIntent.erase :=
  lease.prepay_retry_replays schedule before

end Witness

/-- info: 'Minidregg.Kernel.ProviderExecutionLease.OpenedLease.installed_rekey_nullifier_not_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OpenedLease.installed_rekey_nullifier_not_fresh
/-- info: 'Minidregg.Kernel.ProviderExecutionLease.OpenedLease.rekeyed_prepay_cannot_accept_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OpenedLease.rekeyed_prepay_cannot_accept_twice
/-- info: 'Minidregg.Kernel.ProviderExecutionLease.terminal_and_outbox_atomic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms terminal_and_outbox_atomic
/-- info: 'Minidregg.Kernel.ProviderExecutionLease.distinct_provider_terminals_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms distinct_provider_terminals_conflict
/-- info: 'Minidregg.Kernel.ProviderExecutionLease.RefundPlan.request_ne_prepay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RefundPlan.request_ne_prepay
/-- info: 'Minidregg.Kernel.ProviderExecutionLease.Witness.completed_commits_terminal_and_outbox' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.completed_commits_terminal_and_outbox
/-- info: 'Minidregg.Kernel.ProviderExecutionLease.Witness.expiry_loses_completed_race' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.expiry_loses_completed_race
/-- info: 'Minidregg.Kernel.ProviderExecutionLease.Witness.refund_requires_distinct_authority' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Witness.refund_requires_distinct_authority

end Minidregg.Kernel.ProviderExecutionLease
