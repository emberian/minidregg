/-
# Kernel.OutboxDelivery -- exact outbox delivery and acknowledgement safety

An atomic outbox write is not yet a delivered message.  This module supplies
the narrow logical seam after installation.  It models stable message identity,
numbered delivery attempts, idempotent duplicate receipt, and acknowledgements
authenticated by an abstract deployment verifier and bound to the exact outbox
bytes and root.

All progress claims remain parameters of `ProgressRefinement`.  No scheduler,
network, authentication mechanism, native transport, or eventual-delivery fact
is constructed here.
-/
import Kernel.ReactiveTerminalCell

namespace Minidregg.Kernel.OutboxDelivery

open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ReactiveTerminalCell
open Minidregg.Theory

set_option autoImplicit false

/-! ## Stable message and attempt identity -/

/-- The stable identity of one installed outbox record.  Attempt numbers are
deliberately absent: every retry of one message keeps this identity. -/
structure MessageId where
  codecVersion : Nat
  domain : Digest
  promiseId : Digest
  eventId : Digest
  transactionId : TransactionId
  deriving DecidableEq, Repr

/-- Exact installed outbox content.  `rootExact` prevents a delivery adapter
from pairing arbitrary bytes with the durable outbox root. -/
structure Message (rootBytes : List UInt8 → Digest) where
  messageId : MessageId
  outboxBytes : List UInt8
  outboxRoot : Digest
  rootExact : rootBytes outboxBytes = outboxRoot

/-- A wire attempt repeats the stable identity and exact payload while adding
only a monotonically chosen attempt number.  Raw attempts can be malformed;
`ExactFor` is the admission relation checked by the receiver. -/
structure Attempt where
  messageId : MessageId
  number : Nat
  outboxBytes : List UInt8
  outboxRoot : Digest
  deriving DecidableEq, Repr

def Attempt.ExactFor {rootBytes : List UInt8 → Digest}
    (attempt : Attempt) (message : Message rootBytes) : Prop :=
  attempt.messageId = message.messageId ∧
    attempt.outboxBytes = message.outboxBytes ∧
    attempt.outboxRoot = message.outboxRoot

def firstAttempt {rootBytes : List UInt8 → Digest}
    (message : Message rootBytes) : Attempt where
  messageId := message.messageId
  number := 0
  outboxBytes := message.outboxBytes
  outboxRoot := message.outboxRoot

/-- Retrying changes only the attempt number. -/
def Attempt.retry (attempt : Attempt) : Attempt :=
  { attempt with number := attempt.number + 1 }

@[simp] theorem firstAttempt_exact {rootBytes : List UInt8 → Digest}
    (message : Message rootBytes) :
    (firstAttempt message).ExactFor message :=
  ⟨rfl, rfl, rfl⟩

@[simp] theorem Attempt.retry_number (attempt : Attempt) :
    attempt.retry.number = attempt.number + 1 := rfl

theorem Attempt.retry_preserves_exact
    {rootBytes : List UInt8 → Digest} {message : Message rootBytes}
    {attempt : Attempt} (exact : attempt.ExactFor message) :
    attempt.retry.ExactFor message :=
  exact

theorem Attempt.retry_preserves_message_id (attempt : Attempt) :
    attempt.retry.messageId = attempt.messageId := rfl

theorem Attempt.retry_preserves_payload (attempt : Attempt) :
    attempt.retry.outboxBytes = attempt.outboxBytes ∧
      attempt.retry.outboxRoot = attempt.outboxRoot :=
  ⟨rfl, rfl⟩

/-! ## Idempotent receiver journal -/

structure DeliveryBinding where
  outboxBytes : List UInt8
  outboxRoot : Digest
  deriving DecidableEq, Repr

def Message.binding {rootBytes : List UInt8 → Digest}
    (message : Message rootBytes) : DeliveryBinding where
  outboxBytes := message.outboxBytes
  outboxRoot := message.outboxRoot

/-- The receiver journal is keyed only by stable message identity. -/
structure ReceiverState where
  delivered : MessageId → Option DeliveryBinding

def ReceiverState.install {rootBytes : List UInt8 → Digest}
    (before : ReceiverState) (message : Message rootBytes) : ReceiverState where
  delivered := Function.update before.delivered message.messageId
    (some message.binding)

inductive ReceiveFailure where
  | wrongMessageId
  | wrongRoot
  | wrongBytes
  | recipientConflict
  deriving DecidableEq, Repr

inductive ReceiveOutcome where
  | applied (after : ReceiverState)
  | replayed
  | rejected (failure : ReceiveFailure)

/-- Delivery admission checks the full source message before consulting the
idempotence journal.  An unseen exact message is applied, the same stable
binding is replayed, and a prior different binding is a conflict. -/
noncomputable def receive {rootBytes : List UInt8 → Digest}
    (before : ReceiverState) (message : Message rootBytes)
    (attempt : Attempt) : ReceiveOutcome :=
  if attempt.messageId ≠ message.messageId then
    .rejected .wrongMessageId
  else if attempt.outboxRoot ≠ message.outboxRoot then
    .rejected .wrongRoot
  else if attempt.outboxBytes ≠ message.outboxBytes then
    .rejected .wrongBytes
  else
    match before.delivered message.messageId with
    | none => .applied (before.install message)
    | some binding =>
        if binding = message.binding then .replayed
        else .rejected .recipientConflict

@[simp] theorem ReceiverState.install_lookup_self
    {rootBytes : List UInt8 → Digest} (before : ReceiverState)
    (message : Message rootBytes) :
    (before.install message).delivered message.messageId =
      some message.binding := by
  simp [ReceiverState.install]

theorem receive_first_applies {rootBytes : List UInt8 → Digest}
    (before : ReceiverState) (message : Message rootBytes)
    (fresh : before.delivered message.messageId = none) :
    receive before message (firstAttempt message) =
      .applied (before.install message) := by
  simp [receive, firstAttempt, fresh]

/-- Duplicate delivery is idempotent even when it arrives under a new retry
number: no second receiver application is produced. -/
theorem duplicate_retry_replays {rootBytes : List UInt8 → Digest}
    (before : ReceiverState) (message : Message rootBytes)
    (attempt : Attempt) (exact : attempt.ExactFor message) :
    receive (before.install message) message attempt.retry = .replayed := by
  rcases exact with ⟨id, bytes, root⟩
  simp [receive, Attempt.retry, id, bytes, root]

theorem wrong_message_rejected {rootBytes : List UInt8 → Digest}
    (before : ReceiverState) (message : Message rootBytes) (attempt : Attempt)
    (wrong : attempt.messageId ≠ message.messageId) :
    receive before message attempt = .rejected .wrongMessageId := by
  simp [receive, wrong]

theorem wrong_root_rejected {rootBytes : List UInt8 → Digest}
    (before : ReceiverState) (message : Message rootBytes) (attempt : Attempt)
    (id : attempt.messageId = message.messageId)
    (wrong : attempt.outboxRoot ≠ message.outboxRoot) :
    receive before message attempt = .rejected .wrongRoot := by
  simp [receive, id, wrong]

theorem wrong_bytes_rejected {rootBytes : List UInt8 → Digest}
    (before : ReceiverState) (message : Message rootBytes) (attempt : Attempt)
    (id : attempt.messageId = message.messageId)
    (root : attempt.outboxRoot = message.outboxRoot)
    (wrong : attempt.outboxBytes ≠ message.outboxBytes) :
    receive before message attempt = .rejected .wrongBytes := by
  simp [receive, id, root, wrong]

/-! ## Authenticated acknowledgements -/

/-- Acknowledgement material repeats every delivery binding field.  The
authentication tag is opaque to the logical kernel. -/
structure Ack (AuthTag : Type) where
  messageId : MessageId
  attempt : Nat
  outboxBytes : List UInt8
  outboxRoot : Digest
  authTag : AuthTag

/-- Deployment authentication boundary.  `verify` is executable policy;
`sound` is the required refinement from acceptance to the external
authentication relation.  This module supplies no instance. -/
structure AckVerifier (AuthTag : Type) where
  Authenticated : Ack AuthTag → Prop
  verify : Ack AuthTag → Bool
  sound : ∀ ack, verify ack = true → Authenticated ack

inductive AckFailure where
  | unauthenticated
  | wrongMessageId
  | staleAttempt
  | futureAttempt
  | wrongRoot
  | wrongBytes
  deriving DecidableEq, Repr

inductive AckOutcome where
  | accepted
  | rejected (failure : AckFailure)
  deriving DecidableEq, Repr

/-- An accepted acknowledgement must match the currently outstanding attempt,
not merely the stable message.  This rejects late acknowledgements for an
attempt superseded by a retry. -/
def checkAck {rootBytes : List UInt8 → Digest} {AuthTag : Type}
    (verifier : AckVerifier AuthTag) (message : Message rootBytes)
    (currentAttempt : Nat) (ack : Ack AuthTag) : AckOutcome :=
  if verifier.verify ack ≠ true then
    .rejected .unauthenticated
  else if ack.messageId ≠ message.messageId then
    .rejected .wrongMessageId
  else if ack.attempt ≠ currentAttempt then
    if ack.attempt < currentAttempt then .rejected .staleAttempt
    else .rejected .futureAttempt
  else if ack.outboxRoot ≠ message.outboxRoot then
    .rejected .wrongRoot
  else if ack.outboxBytes ≠ message.outboxBytes then
    .rejected .wrongBytes
  else
    .accepted

def Ack.ExactFor {rootBytes : List UInt8 → Digest} {AuthTag : Type}
    (verifier : AckVerifier AuthTag) (message : Message rootBytes)
    (currentAttempt : Nat) (ack : Ack AuthTag) : Prop :=
  verifier.Authenticated ack ∧
    ack.messageId = message.messageId ∧
    ack.attempt = currentAttempt ∧
    ack.outboxRoot = message.outboxRoot ∧
    ack.outboxBytes = message.outboxBytes

theorem accepted_ack_exact
    {rootBytes : List UInt8 → Digest} {AuthTag : Type}
    (verifier : AckVerifier AuthTag) (message : Message rootBytes)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (accepted : checkAck verifier message currentAttempt ack = .accepted) :
    ack.ExactFor verifier message currentAttempt := by
  unfold checkAck at accepted
  split at accepted <;> rename_i auth
  · simp at accepted
  split at accepted <;> rename_i id
  · simp at accepted
  split at accepted <;> rename_i attempt
  · split at accepted <;> simp at accepted
  split at accepted <;> rename_i root
  · simp at accepted
  split at accepted <;> rename_i bytes
  · simp at accepted
  exact ⟨verifier.sound ack (by simpa using auth), by simpa using id,
    by simpa using attempt, by simpa using root, by simpa using bytes⟩

theorem accepted_ack_binds_exact_outbox
    {rootBytes : List UInt8 → Digest} {AuthTag : Type}
    (verifier : AckVerifier AuthTag) (message : Message rootBytes)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (accepted : checkAck verifier message currentAttempt ack = .accepted) :
    verifier.Authenticated ack ∧
      ack.outboxBytes = message.outboxBytes ∧
      ack.outboxRoot = message.outboxRoot ∧
      rootBytes ack.outboxBytes = ack.outboxRoot := by
  have exact := accepted_ack_exact verifier message currentAttempt ack accepted
  refine ⟨exact.1, exact.2.2.2.2, exact.2.2.2.1, ?_⟩
  rw [exact.2.2.2.2, exact.2.2.2.1]
  exact message.rootExact

theorem stale_ack_rejected
    {rootBytes : List UInt8 → Digest} {AuthTag : Type}
    (verifier : AckVerifier AuthTag) (message : Message rootBytes)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (authenticated : verifier.verify ack = true)
    (id : ack.messageId = message.messageId)
    (stale : ack.attempt < currentAttempt) :
    checkAck verifier message currentAttempt ack =
      .rejected .staleAttempt := by
  simp [checkAck, authenticated, id, Nat.ne_of_lt stale, stale]

theorem wrong_ack_message_rejected
    {rootBytes : List UInt8 → Digest} {AuthTag : Type}
    (verifier : AckVerifier AuthTag) (message : Message rootBytes)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (authenticated : verifier.verify ack = true)
    (wrong : ack.messageId ≠ message.messageId) :
    checkAck verifier message currentAttempt ack =
      .rejected .wrongMessageId := by
  simp [checkAck, authenticated, wrong]

theorem future_ack_rejected
    {rootBytes : List UInt8 → Digest} {AuthTag : Type}
    (verifier : AckVerifier AuthTag) (message : Message rootBytes)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (authenticated : verifier.verify ack = true)
    (id : ack.messageId = message.messageId)
    (future : currentAttempt < ack.attempt) :
    checkAck verifier message currentAttempt ack =
      .rejected .futureAttempt := by
  have ne : ack.attempt ≠ currentAttempt := Nat.ne_of_gt future
  have notStale : ¬ ack.attempt < currentAttempt := Nat.not_lt_of_ge future.le
  simp [checkAck, authenticated, id, ne, notStale]

theorem wrong_ack_root_rejected
    {rootBytes : List UInt8 → Digest} {AuthTag : Type}
    (verifier : AckVerifier AuthTag) (message : Message rootBytes)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (authenticated : verifier.verify ack = true)
    (id : ack.messageId = message.messageId)
    (attempt : ack.attempt = currentAttempt)
    (wrong : ack.outboxRoot ≠ message.outboxRoot) :
    checkAck verifier message currentAttempt ack = .rejected .wrongRoot := by
  simp [checkAck, authenticated, id, attempt, wrong]

theorem wrong_ack_bytes_rejected
    {rootBytes : List UInt8 → Digest} {AuthTag : Type}
    (verifier : AckVerifier AuthTag) (message : Message rootBytes)
    (currentAttempt : Nat) (ack : Ack AuthTag)
    (authenticated : verifier.verify ack = true)
    (id : ack.messageId = message.messageId)
    (attempt : ack.attempt = currentAttempt)
    (root : ack.outboxRoot = message.outboxRoot)
    (wrong : ack.outboxBytes ≠ message.outboxBytes) :
    checkAck verifier message currentAttempt ack = .rejected .wrongBytes := by
  simp [checkAck, authenticated, id, attempt, root, wrong]

/-! ## Explicit scheduler, network, and eventual-delivery ceilings -/

/-- A deployment claiming progress must refine all four relations and provide
finite scheduler/network/ack ceilings.  The final two fields are explicit
end-to-end obligations at the sum of those ceilings; they are not derived from
the safety model above. -/
structure ProgressRefinement
    {rootBytes : List UInt8 → Digest} (message : Message rootBytes)
    (Enabled : Attempt → Prop)
    (ScheduledWithin NetworkDeliveredWithin AckReturnedWithin :
      Attempt → Nat → Prop)
    (EventuallyDeliveredWithin EventuallyAcknowledgedWithin :
      Message rootBytes → Nat → Prop) : Prop where
  schedulerCeiling : Nat
  networkCeiling : Nat
  acknowledgementCeiling : Nat
  scheduled : ∀ attempt, attempt.ExactFor message → Enabled attempt →
    ScheduledWithin attempt schedulerCeiling
  networkDelivered : ∀ attempt, attempt.ExactFor message →
    ScheduledWithin attempt schedulerCeiling →
    NetworkDeliveredWithin attempt networkCeiling
  acknowledgementReturned : ∀ attempt, attempt.ExactFor message →
    NetworkDeliveredWithin attempt networkCeiling →
    AckReturnedWithin attempt acknowledgementCeiling
  eventuallyDelivered : EventuallyDeliveredWithin message
    (schedulerCeiling + networkCeiling)
  eventuallyAcknowledged : EventuallyAcknowledgedWithin message
    (schedulerCeiling + networkCeiling + acknowledgementCeiling)

/-! ## Axiom audit -/

#print axioms duplicate_retry_replays
#print axioms accepted_ack_binds_exact_outbox

end Minidregg.Kernel.OutboxDelivery
