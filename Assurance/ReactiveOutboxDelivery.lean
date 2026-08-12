/-
# Assurance.ReactiveOutboxDelivery -- durable reactive outbox delivery seam

This module connects `Kernel.OutboxDelivery` to the existing terminal plan,
reactive durable settlement, provider lease, and concrete hyperdocument agent
scheduler.  It does not add a native transport.  The durable source bytes and
root are projected exactly; attempts retain one stable message id; duplicate
delivery is a receiver replay; and only an externally authenticated ack for the
current attempt and exact source bytes/root is accepted.

Scheduler, network, acknowledgement, and eventual-delivery ceilings remain the
uninhabited deployment boundary `AgentRuntimeProgress` below.
-/
import Assurance.HyperdocumentAgentRuntimeScheduler
import Kernel.OutboxDelivery

namespace Minidregg.Assurance.ReactiveOutboxDelivery

open Minidregg.Assurance.ReactiveDurableSettlement
open Minidregg.Assurance.ReactiveLifecycleHistory
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Kernel
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.OutboxDelivery
open Minidregg.Kernel.ReactiveTerminalCell
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## Every terminal plan has one stable exact message -/

/-- Exact delivery message projected from the atomic terminal plan.  Its stable
id comes from open-cell identities, while its bytes/root come from the outbox
write installed by that same plan. -/
def planMessage {rootBytes : List UInt8 → Digest} {openCell : OpenCell}
    (plan : Plan rootBytes openCell) : Message rootBytes where
  messageId := {
    codecVersion := openCell.codecVersion
    domain := openCell.domain
    promiseId := openCell.promiseId
    eventId := openCell.eventId
    transactionId := openCell.transactionId }
  outboxBytes := plan.outboxBytes
  outboxRoot := plan.outboxRoot
  rootExact := rfl

def planAttempt {rootBytes : List UInt8 → Digest} {openCell : OpenCell}
    (plan : Plan rootBytes openCell) (attempt : Nat) : Attempt where
  messageId := (planMessage plan).messageId
  number := attempt
  outboxBytes := (planMessage plan).outboxBytes
  outboxRoot := (planMessage plan).outboxRoot

@[simp] theorem planAttempt_exact
    {rootBytes : List UInt8 → Digest} {openCell : OpenCell}
    (plan : Plan rootBytes openCell) (attempt : Nat) :
    (planAttempt plan attempt).ExactFor (planMessage plan) :=
  ⟨rfl, rfl, rfl⟩

/-- All terminal alternatives for one open cell share the same delivery id.
Payload differences remain protected by the terminal race and receiver
conflict checks rather than being hidden in retry identity. -/
theorem plan_message_id_stable
    {rootBytes : List UInt8 → Digest} {openCell : OpenCell}
    (left right : Plan rootBytes openCell) :
    (planMessage left).messageId = (planMessage right).messageId :=
  rfl

theorem plan_retry_preserves_exact
    {rootBytes : List UInt8 → Digest} {openCell : OpenCell}
    (plan : Plan rootBytes openCell) (attempt : Nat) :
    (planAttempt plan attempt).retry.ExactFor (planMessage plan) :=
  Attempt.retry_preserves_exact (planAttempt_exact plan attempt)

/-- Logical installation exposes exactly the bytes and root delivered by this
message.  The root statement follows from the data snapshot's canonical-byte
coherence, not from root injectivity. -/
theorem installed_plan_message_exact
    {rootBytes : List UInt8 → Digest} {openCell : OpenCell}
    (plan : Plan rootBytes openCell) (before : DataSnapshot rootBytes) :
    (DataSnapshot.install before plan.intent).canonicalBytes openCell.outboxCell =
        (planMessage plan).outboxBytes ∧
      (DataSnapshot.install before plan.intent).model.roots openCell.outboxCell =
        (planMessage plan).outboxRoot := by
  have bytes := (Plan.installed_exact plan before).2
  refine ⟨bytes, ?_⟩
  rw [← (DataSnapshot.install before plan.intent).coherent openCell.outboxCell,
    bytes]
  exact (planMessage plan).rootExact

/-! ## Reactive durable settlement adapter -/

universe u v w x y z q r
  uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome
  uClauseEvidence

section ReactiveSettlement

variable
    {U : FirstOrderUniverse.{q, r}}
    {S : CellState.Schema.{u, v, w, x}}
    [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest} {Nullifier : Type y}
    {family : SemanticEffectFamily.{u, v, w, x, y, z} S M Nullifier}
    {Condition Continuation BreakReason : Type}
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {entryFamily : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext → BindingIx → F}
    {C : Submodule F (BoundReceiptIx n → F)}
    {rules : HistoryRules n F Nat Condition BreakReason}
    {spec : PromiseSpec U family Nat Condition Continuation}
    {portal : Portal} {authState : AuthState}
    {binding : ReactiveDurableSettlement.Binding spec}
    {finalized : Finalized (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (entryFamily := entryFamily)
      (headerCells := headerCells) (C := C)
      (portal := portal) (authState := authState) rules spec}

/-- The assurance settlement's delivery source is exactly its terminal plan,
not a separately serialized event. -/
def finalizeMessage
    (settlement : ReactiveDurableSettlement.FinalizeSettlement
      binding finalized) : Message M.rootBytes :=
  planMessage settlement.terminalPlan

theorem installed_finalize_message_exact
    (settlement : ReactiveDurableSettlement.FinalizeSettlement binding finalized)
    (before : DataSnapshot M.rootBytes) :
    (DataSnapshot.install before settlement.intent).canonicalBytes
        binding.openCell.outboxCell = (finalizeMessage settlement).outboxBytes ∧
      (DataSnapshot.install before settlement.intent).model.roots
        binding.openCell.outboxCell = (finalizeMessage settlement).outboxRoot := by
  have bytes := (settlement.installed_exact before).2.2
  refine ⟨bytes, ?_⟩
  rw [← (DataSnapshot.install before settlement.intent).coherent
    binding.openCell.outboxCell, bytes]
  exact (finalizeMessage settlement).rootExact

end ReactiveSettlement

/-! ## Provider execution lease adapter -/

namespace ProviderLease

open Minidregg.Kernel.ProviderExecutionLease
open Minidregg.Theory.CanonicalResourceKernel

variable
    {M : Materializer CanonicalResourceKernel.schema Digest}
    {portal : Portal} {authState : AuthState} {pre : Materialized M}
    {lease : OpenedLease M portal authState pre} {boundary : StartBoundary}
    {attempt : StartAttempt lease boundary}
    {completion : CompletionBoundary attempt}
    {deadline settledAt : Nat}

def message (outcome : Outcome attempt completion deadline settledAt) :
    Message M.rootBytes :=
  planMessage (terminalPlan outcome)

def deliveryAttempt (outcome : Outcome attempt completion deadline settledAt)
    (number : Nat) : Attempt :=
  planAttempt (terminalPlan outcome) number

@[simp] theorem deliveryAttempt_exact
    (outcome : Outcome attempt completion deadline settledAt) (number : Nat) :
    (deliveryAttempt outcome number).ExactFor (message outcome) :=
  planAttempt_exact (terminalPlan outcome) number

/-- Completion, cancellation, expiry, compensation, and quarantine for one
lease/deadline retain one message id.  The existing terminal-cell race decides
which distinct payload can be installed. -/
theorem message_id_stable
    {leftAt rightAt : Nat}
    (left : Outcome attempt completion deadline leftAt)
    (right : Outcome attempt completion deadline rightAt) :
    (message left).messageId = (message right).messageId :=
  plan_message_id_stable (terminalPlan left) (terminalPlan right)

end ProviderLease

/-! ## Concrete agent runtime seam and safety teeth -/

namespace AgentRuntime

namespace Scheduler :=
  Minidregg.Assurance.HyperdocumentAgentRuntimeScheduler

def message : Message Scheduler.Link.materializer.rootBytes :=
  planMessage Scheduler.settlement.terminalPlan

def attempt (number : Nat) : Attempt :=
  planAttempt Scheduler.settlement.terminalPlan number

@[simp] theorem attempt_exact (number : Nat) :
    (attempt number).ExactFor message :=
  planAttempt_exact Scheduler.settlement.terminalPlan number

/-- The queue item whose outbox is delivered retains the exact accepted
provider lease and start grant; delivery does not manufacture provider
authority or execution evidence. -/
@[simp] theorem job_retains_exact_provider_lease :
    Scheduler.agentJob.leased.lease = Scheduler.ProviderWitness.lease ∧
      Scheduler.agentJob.leased.grant = Scheduler.ProviderWitness.grant :=
  ⟨Scheduler.agentJob.leased.leaseExact,
    Scheduler.agentJob.leased.grantExact⟩

theorem installed_message_exact (before : Scheduler.Store) :
    (DataSnapshot.install before Scheduler.intent).canonicalBytes
        Scheduler.openCell.outboxCell = message.outboxBytes ∧
      (DataSnapshot.install before Scheduler.intent).model.roots
        Scheduler.openCell.outboxCell = message.outboxRoot := by
  have bytes := (Scheduler.installed_semantic_terminal_outbox_exact before).2.2
  refine ⟨bytes, ?_⟩
  rw [← (DataSnapshot.install before Scheduler.intent).coherent
    Scheduler.openCell.outboxCell, bytes]
  exact message.rootExact

def emptyReceiver : ReceiverState where
  delivered := fun _ => none

@[simp] theorem first_delivery_applies :
    receive emptyReceiver message (attempt 0) =
      .applied (emptyReceiver.install message) := by
  exact receive_first_applies emptyReceiver message rfl

/-- Retrying the exact agent outbox after its first delivery is a receiver
replay, even though the attempt number changed. -/
@[simp] theorem duplicate_delivery_replays (number : Nat) :
    receive (emptyReceiver.install message) message (attempt number).retry =
      .replayed :=
  duplicate_retry_replays emptyReceiver message (attempt number)
    (attempt_exact number)

/-- Any accepted agent acknowledgement is externally authenticated and binds
the literal installed outbox bytes and root. -/
theorem accepted_ack_binds_installed_outbox
    {AuthTag : Type} (verifier : AckVerifier AuthTag)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (accepted : checkAck verifier message currentAttempt ack = .accepted) :
    verifier.Authenticated ack ∧
      ack.outboxBytes = Scheduler.settlement.terminalPlan.outboxBytes ∧
      ack.outboxRoot = Scheduler.settlement.terminalPlan.outboxRoot ∧
      Scheduler.Link.materializer.rootBytes ack.outboxBytes = ack.outboxRoot :=
  accepted_ack_binds_exact_outbox verifier message currentAttempt ack accepted

theorem stale_ack_rejected
    {AuthTag : Type} (verifier : AckVerifier AuthTag)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (authenticated : verifier.verify ack = true)
    (id : ack.messageId = message.messageId)
    (stale : ack.attempt < currentAttempt) :
    checkAck verifier message currentAttempt ack =
      .rejected .staleAttempt :=
  OutboxDelivery.stale_ack_rejected verifier message currentAttempt ack
    authenticated id stale

theorem wrong_ack_message_rejected
    {AuthTag : Type} (verifier : AckVerifier AuthTag)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (authenticated : verifier.verify ack = true)
    (wrong : ack.messageId ≠ message.messageId) :
    checkAck verifier message currentAttempt ack =
      .rejected .wrongMessageId :=
  OutboxDelivery.wrong_ack_message_rejected verifier message currentAttempt ack
    authenticated wrong

theorem future_ack_rejected
    {AuthTag : Type} (verifier : AckVerifier AuthTag)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (authenticated : verifier.verify ack = true)
    (id : ack.messageId = message.messageId)
    (future : currentAttempt < ack.attempt) :
    checkAck verifier message currentAttempt ack =
      .rejected .futureAttempt :=
  OutboxDelivery.future_ack_rejected verifier message currentAttempt ack
    authenticated id future

theorem wrong_ack_root_rejected
    {AuthTag : Type} (verifier : AckVerifier AuthTag)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (authenticated : verifier.verify ack = true)
    (id : ack.messageId = message.messageId)
    (attemptExact : ack.attempt = currentAttempt)
    (wrong : ack.outboxRoot ≠ message.outboxRoot) :
    checkAck verifier message currentAttempt ack = .rejected .wrongRoot :=
  OutboxDelivery.wrong_ack_root_rejected verifier message currentAttempt ack
    authenticated id attemptExact wrong

theorem wrong_ack_bytes_rejected
    {AuthTag : Type} (verifier : AckVerifier AuthTag)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (authenticated : verifier.verify ack = true)
    (id : ack.messageId = message.messageId)
    (attemptExact : ack.attempt = currentAttempt)
    (rootExact : ack.outboxRoot = message.outboxRoot)
    (wrong : ack.outboxBytes ≠ message.outboxBytes) :
    checkAck verifier message currentAttempt ack = .rejected .wrongBytes :=
  OutboxDelivery.wrong_ack_bytes_rejected verifier message currentAttempt ack
    authenticated id attemptExact rootExact wrong

/-- Exact deployment ceiling for this agent message.  A runtime must provide
the scheduling, transport, ack-return, and end-to-end bounded-delivery
relations.  There is intentionally no inhabitant in this module. -/
abbrev AgentRuntimeProgress
    (Enabled : Attempt → Prop)
    (ScheduledWithin NetworkDeliveredWithin AckReturnedWithin :
      Attempt → Nat → Prop)
    (EventuallyDeliveredWithin EventuallyAcknowledgedWithin :
      Message Scheduler.Link.materializer.rootBytes → Nat → Prop) : Type :=
  ProgressRefinement message Enabled ScheduledWithin NetworkDeliveredWithin
    AckReturnedWithin EventuallyDeliveredWithin EventuallyAcknowledgedWithin

/-! ## Axiom audit -/

#print axioms installed_message_exact
#print axioms duplicate_delivery_replays
#print axioms accepted_ack_binds_installed_outbox

end AgentRuntime

end

end Minidregg.Assurance.ReactiveOutboxDelivery
