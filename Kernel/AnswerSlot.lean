/- Answer slots: the cell an awaiting activity's reply arrives in.

A slot is named `H(turn, call site)`: the transaction of the yielding turn and
the yield's place in its activity (record cell and generation), so every
validator derives the same name and no submitter chooses it. It has exactly
one decider, fixed when the slot opens, and one terminal decision, written once.
The decider is a ROLE (`Decider`, BREAD review D-4):

* `subject s`: an activity's await names a subject; with a deadline height:

    open --s, at or before the deadline--> decided (reply | refused | unknown | broken)
    open --anyone, strictly after the deadline--> decided expired

* `delivery m`: the reply slot of a sent message `m` (`Kernel.ObjectiveSend`,
  named `m`, the message's own id). Only the kernel turn that delivers `m`
  decides it (`decideDelivery`): the turn that pops `m` from the head of the
  inbox holding it decides `reply` with the method's result, or `broken` when the
  delivery failed. No subject decides it (`decide_delivery_refused`) and it never
  expires (`expire_delivery_refused`): a queued message is always deliverable by
  anyone, so its slot needs no deadline. The role travels with the message: a
  message forwarded from a resolved slot keeps its id, so its slot (opened when
  it enters an inbox) names the same role.

A delivery slot also holds the sends queued ON it (`queued`, at most
`Inbox.bound`): sends addressed to the reply of a message not yet delivered. The
turn that decides the slot forwards them (when the reply names an object) or
refunds them, in that same turn.

The message's SENDER (a frame of the sending object, `ObjectiveCall`) controls the
slot two separate ways (GPT-6 row F: stop-waiting is not cancel-if-queued):
* `stopWaiting`: the sender stops waiting for the reply. The pipelined sends are
  refunded, nothing more may be pipelined on it (`watched = false`), and the message
  STAYS QUEUED: it is delivered as ever, and the delivery RETIRES the unwatched slot
  instead of writing a decision nobody reads. A decided slot it retires at once.
* `cancelDelivery`: the sender withdraws the message IF IT IS STILL QUEUED. Its slot is
  decided `cancelled` (by the cancelling turn, the only decider besides the
  delivery). A slot already decided is left as it is: the cancel is a no-op.

The rule below is pure. Its intents (in `Kernel.ObjectiveActivity`) write the
slot cell against its open root AND spend the slot's claim, so a second
decision is refused twice over: the cell CAS (`stalePreRoot`) and the claim
(`alreadyConsumed`). The decision a delivery reads is typed against the
awaiting activity's declared response type before it is ever written
(`ObjectiveActivity.resolve`); `expired` becomes the `timedOut` outcome and
`broken` the `broken` outcome of the activity. Upgrade-driven `upgraded` and
kernel-driven `conflict` are outcomes of the activity, never slot decisions. -/
import Kernel.ObjectiveActivityWire
import Kernel.ObjectiveActivityCell
import Kernel.Inbox

namespace Minidregg.Kernel.AnswerSlot
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
set_option autoImplicit false

/-- A terminal decision. A reply carries the exact data bytes of the value
(`ObjectiveActivityWire.dataBytes`), typed before it is written. -/
inductive Decision where
  | reply (value : Bytes)
  | refused (reason : String)
  | unknown
  | broken (reason : String)
  | expired
  /-- The message's sender withdrew it while it was still queued. Kernel-only: no
  subject's answer carries it (`ObjectiveActivityReceiver.AnswerWire`). -/
  | cancelled
  deriving DecidableEq, Repr

inductive Phase where
  | opened
  | decided (decision : Decision) (height : Nat)
  deriving DecidableEq, Repr

/-- Who decides a slot: a subject, or the delivery of one message. -/
inductive Decider where
  | subject (subject : SubjectId)
  | delivery (message : Digest)
  deriving DecidableEq, Repr

structure Slot where
  name : Digest
  /-- The cell this slot answers to: the record cell of the awaiting activity
  (a subject slot), or the inbox holding the message (a delivery slot; its
  purse holds the postage of the sends queued here). -/
  activity : CellId
  decider : Decider
  deadline : Nat
  phase : Phase
  /-- Sends queued on this slot's reply (delivery slots only). -/
  queued : List Inbox.Message
  /-- Someone waits for the reply: false once the message's sender stopped waiting
  (`stopWaiting`); an unwatched slot takes no pipelined send and is retired by the
  turn that would decide it. -/
  watched : Bool
  deriving DecidableEq, Repr

def decisionStream : StreamCodec Decision :=
  StreamCodec.xmap
    (StreamCodec.sum bytesStream (StreamCodec.sum stringStream
      (StreamCodec.sum unitStream (StreamCodec.sum stringStream (StreamCodec.sum unitStream unitStream)))))
    (fun decision => match decision with
      | .reply value => .inl value
      | .refused reason => .inr (.inl reason)
      | .unknown => .inr (.inr (.inl ()))
      | .broken reason => .inr (.inr (.inr (.inl reason)))
      | .expired => .inr (.inr (.inr (.inr (.inl ()))))
      | .cancelled => .inr (.inr (.inr (.inr (.inr ())))))
    (fun wire => match wire with
      | .inl value => .reply value
      | .inr (.inl reason) => .refused reason
      | .inr (.inr (.inl _)) => .unknown
      | .inr (.inr (.inr (.inl reason))) => .broken reason
      | .inr (.inr (.inr (.inr (.inl _)))) => .expired
      | .inr (.inr (.inr (.inr (.inr _)))) => .cancelled)
    (by intro decision; cases decision <;> rfl)

def phaseStream : StreamCodec Phase :=
  StreamCodec.xmap (StreamCodec.sum unitStream (StreamCodec.product decisionStream StreamCodec.nat))
    (fun phase => match phase with
      | .opened => .inl ()
      | .decided decision height => .inr (decision, height))
    (fun wire => match wire with
      | .inl _ => .opened
      | .inr (decision, height) => .decided decision height)
    (by intro phase; cases phase <;> rfl)

def deciderStream : StreamCodec Decider :=
  StreamCodec.xmap (StreamCodec.sum subjectStream digestStream)
    (fun decider => match decider with
      | .subject subject => .inl subject
      | .delivery message => .inr message)
    (fun wire => match wire with
      | .inl subject => .subject subject
      | .inr message => .delivery message)
    (by intro decider; cases decider <;> rfl)

def slotStream : StreamCodec Slot :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product deciderStream (StreamCodec.product StreamCodec.nat
        (StreamCodec.product phaseStream (StreamCodec.product (StreamCodec.list Inbox.messageStream)
          StreamCodec.bool))))))
    (fun slot => (slot.name, slot.activity, slot.decider, slot.deadline, slot.phase, slot.queued, slot.watched))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2.1, wire.2.2.2.2.2.1, wire.2.2.2.2.2.2⟩)
    (by intro slot; cases slot; rfl)

/-- v4: the messages a slot queues carry their continuation `allowance` and `depth` (the INBOX
v2 message, GPT-6 row F); v3 carried `watched` and `cancelled`. A v3 (or older) slot refuses
to decode (`v3_refuses`). -/
def frame : Bytes := "DREGG/OBJECTIVE/ANSWER-SLOT/v4".toUTF8.toList
def codec := framed frame slotStream
def encode (slot : Slot) : Bytes := codec.encode slot
def decode (bytes : Bytes) : Option Slot := codec.decode bytes

theorem roundTrip (slot : Slot) : decode (encode slot) = some slot := framed_roundTrip _ _ slot

/-- `H(turn, call site)`: the yielding turn's transaction and the yield's place
(the activity's record cell and the generation of the yield). -/
def name (turn : TransactionId) (activity : CellId) (generation : Nat) : Digest :=
  tagged "DREGG/OBJECTIVE/ANSWER-SLOT/NAME/v1"
    (digestStream.encode turn ++ digestStream.encode activity ++ StreamCodec.nat.encode generation)

/-- The coordinate preimage of a slot cell: its name. -/
def key (slotName : Digest) : Bytes := digestStream.encode slotName

/-- The slot's cell: a protected activity coordinate of the deployment
(`ObjectiveActivityCell.coordinate`, role `slot`). -/
def cell (domain : Digest) (slotName : Digest) : CellId :=
  ⟨ObjectiveActivityCell.coordinate domain .slot (key slotName)⟩

/-- The one claim every decision of this slot spends. -/
def decisionClaim (slotName : Digest) : StableNullifier :=
  claim "answer-slot-decision" (digestStream.encode slotName)

inductive Refusal where
  | notOpen
  | notDecider
  | pastDeadline (deadline height : Nat)
  | notYetExpired (deadline height : Nat)
  | expiryIsKernelOnly
  /-- A delivery slot is decided only by the delivery of its message. -/
  | deliveryDecides
  deriving DecidableEq, Repr

/-- The decider's decision, at or before the deadline, of an open slot. -/
def decide (slot : Slot) (subject : SubjectId) (height : Nat) (decision : Decision) :
    Except Refusal Slot :=
  match slot.phase with
  | .decided _ _ => .error .notOpen
  | .opened =>
    if decision = .expired then .error .expiryIsKernelOnly
    else if slot.decider ≠ .subject subject then .error .notDecider
    else if slot.deadline < height then .error (.pastDeadline slot.deadline height)
    else .ok {slot with phase := .decided decision height}

/-- Anyone's expiry, strictly after the deadline, of a subject slot still open.
A delivery slot never expires. -/
def expire (slot : Slot) (height : Nat) : Except Refusal Slot :=
  match slot.phase with
  | .decided _ _ => .error .notOpen
  | .opened =>
    match slot.decider with
    | .delivery _ => .error .deliveryDecides
    | .subject _ =>
      if slot.deadline < height then .ok {slot with phase := .decided .expired height}
      else .error (.notYetExpired slot.deadline height)

/-- The delivery of `message` decides its reply slot: only an open slot whose
decider is that delivery, and never `expired`. The decided slot keeps nothing
queued: the deciding turn forwards or refunds every queued send. -/
def decideDelivery (slot : Slot) (message : Digest) (height : Nat) (decision : Decision) :
    Except Refusal Slot :=
  match slot.phase with
  | .decided _ _ => .error .notOpen
  | .opened =>
    if decision = .expired then .error .expiryIsKernelOnly
    else if slot.decider ≠ .delivery message then .error .notDecider
    else .ok {slot with phase := .decided decision height, queued := []}

/-- **The sender stops waiting**: an open delivery slot keeps its message's place
(nothing about the inbox changes) but drops its pipelined sends (the caller refunds
them) and is unwatched from now on. -/
def stopWaiting (slot : Slot) : Except Refusal Slot :=
  match slot.phase with
  | .decided _ _ => .error .notOpen
  | .opened =>
    match slot.decider with
    | .subject _ => .error .notDecider
    | .delivery _ => .ok {slot with queued := [], watched := false}

/-- **The sender cancels a still-queued message**: its open delivery slot is decided
`cancelled` with nothing queued (the caller refunds the message and every pipelined send). -/
def cancelDelivery (slot : Slot) (height : Nat) : Except Refusal Slot :=
  match slot.phase with
  | .decided _ _ => .error .notOpen
  | .opened =>
    match slot.decider with
    | .subject _ => .error .notDecider
    | .delivery _ => .ok {slot with phase := .decided .cancelled height, queued := []}

/-- A cancel decides only an open delivery slot, `cancelled`, emptying its queue. -/
theorem cancelDelivery_spec {slot decided : Slot} {height : Nat} (ok : cancelDelivery slot height = .ok decided) :
    slot.phase = .opened ∧ (∃ message, slot.decider = .delivery message) ∧
      decided = {slot with phase := .decided .cancelled height, queued := []} := by
  unfold cancelDelivery at ok
  split at ok
  · cases ok
  · rename_i opened
    split at ok
    · cases ok
    · rename_i message role
      cases ok
      exact ⟨opened, ⟨message, role⟩, rfl⟩

/-- Stopping keeps the slot open and its decider; it only unwatches it and empties its queue. -/
theorem stopWaiting_spec {slot stopped : Slot} (ok : stopWaiting slot = .ok stopped) :
    slot.phase = .opened ∧ (∃ message, slot.decider = .delivery message) ∧
      stopped = {slot with queued := [], watched := false} := by
  unfold stopWaiting at ok
  split at ok
  · cases ok
  · rename_i opened
    split at ok
    · cases ok
    · rename_i message role
      cases ok
      exact ⟨opened, ⟨message, role⟩, rfl⟩

/-- Exactly one decider: a decided slot names the subject that decided it. -/
theorem decide_single_decider {slot decided : Slot} {subject : SubjectId} {height : Nat}
    {decision : Decision} (ok : decide slot subject height decision = .ok decided) :
    slot.decider = .subject subject ∧ slot.phase = .opened ∧ height ≤ slot.deadline ∧
      decided = {slot with phase := .decided decision height} ∧ decision ≠ .expired := by
  unfold decide at ok
  split at ok
  · cases ok
  · rename_i opened
    split at ok
    · cases ok
    · rename_i notExpired
      split at ok
      · cases ok
      · rename_i same
        split at ok
        · cases ok
        · rename_i timely
          cases ok
          exact ⟨Classical.not_not.mp same, opened, by omega, rfl, notExpired⟩

/-- Write-once at the rule: a decided slot accepts no decision and no expiry. -/
theorem decided_refuses (slot : Slot)
    (decided : ∃ prior when, slot.phase = .decided prior when) (subject : SubjectId) (other : Decision)
    (now : Nat) :
    decide slot subject now other = .error .notOpen ∧ expire slot now = .error .notOpen := by
  obtain ⟨prior, when, phase⟩ := decided
  simp [decide, expire, phase]

/-- Expiry is the only way past the deadline, and only past it. -/
theorem expire_after_deadline {slot expired : Slot} {height : Nat}
    (ok : expire slot height = .ok expired) :
    slot.deadline < height ∧ slot.phase = .opened ∧
      expired = {slot with phase := .decided .expired height} := by
  unfold expire at ok
  split at ok
  · cases ok
  · rename_i opened
    split at ok
    · cases ok
    · split at ok
      · rename_i late
        cases ok
        exact ⟨late, opened, rfl⟩
      · cases ok

/-! ### The delivery role (condition (c) of OB8, at the rule) -/

/-- **No subject decides a delivery slot**, whatever it decides. -/
theorem decide_delivery_refused (slot : Slot) (message : Digest) (subject : SubjectId) (height : Nat)
    (decision : Decision) (role : slot.decider = .delivery message) :
    ∃ reason, decide slot subject height decision = .error reason := by
  unfold decide
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · rw [if_pos (by rw [role]; exact fun same => by cases same)]
      exact ⟨_, rfl⟩

/-- **A delivery slot never expires.** -/
theorem expire_delivery_refused (slot : Slot) (message : Digest) (height : Nat)
    (role : slot.decider = .delivery message) (opened : slot.phase = .opened) :
    expire slot height = .error .deliveryDecides := by
  simp [expire, opened, role]

/-- **Only the delivery of its own message decides a delivery slot**: a decided
slot was open, its decider is that delivery, and its queue is emptied. -/
theorem decideDelivery_single {slot decided : Slot} {message : Digest} {height : Nat} {decision : Decision}
    (ok : decideDelivery slot message height decision = .ok decided) :
    slot.decider = .delivery message ∧ slot.phase = .opened ∧ decision ≠ .expired ∧
      decided = {slot with phase := .decided decision height, queued := []} := by
  unfold decideDelivery at ok
  split at ok
  · cases ok
  · rename_i opened
    split at ok
    · cases ok
    · rename_i notExpired
      split at ok
      · cases ok
      · rename_i same
        cases ok
        exact ⟨Classical.not_not.mp same, opened, notExpired, rfl⟩

/-- A subject's decision cannot take a delivery slot's role. -/
theorem decideDelivery_subject_refused (slot : Slot) (subject : SubjectId) (message : Digest) (height : Nat)
    (decision : Decision) (role : slot.decider = .subject subject) :
    ∃ reason, decideDelivery slot message height decision = .error reason := by
  unfold decideDelivery
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · rw [if_pos (by rw [role]; exact fun same => by cases same)]
      exact ⟨_, rfl⟩

/-- A non-decider is refused whatever it decides. -/
theorem stranger_refused (slot : Slot) (subject : SubjectId) (height : Nat) (decision : Decision)
    (opened : slot.phase = .opened) (stranger : slot.decider ≠ .subject subject) (notExpired : decision ≠ .expired) :
    decide slot subject height decision = .error .notDecider := by
  simp [decide, opened, notExpired, stranger]

/-! Inhabitants of the premises above (closed slots, no hashing). -/

def sampleSlot : Slot := ⟨⟨1⟩, ⟨2⟩, .subject ⟨7⟩, 10, .opened, [], true⟩

/-- A delivery slot: the reply of message 1. -/
def sampleSendSlot : Slot := ⟨⟨1⟩, ⟨2⟩, .delivery ⟨1⟩, 0, .opened, [], true⟩

theorem sample_cancelled :
    cancelDelivery sampleSendSlot 5 = .ok {sampleSendSlot with phase := .decided .cancelled 5, queued := []} := rfl

theorem sample_cancel_decided_refused :
    cancelDelivery {sampleSendSlot with phase := .decided (.reply [3]) 4} 5 = .error .notOpen := rfl

theorem sample_cancel_subject_refused : cancelDelivery sampleSlot 5 = .error .notDecider := rfl

theorem sample_stopped : stopWaiting sampleSendSlot = .ok {sampleSendSlot with watched := false} := rfl

/-- The v3 frame (queued messages without an allowance) refuses to decode as v4. -/
theorem v3_refuses (body : Bytes) :
    decode ("DREGG/OBJECTIVE/ANSWER-SLOT/v3".toUTF8.toList ++ body) = none := by
  cases found : decode ("DREGG/OBJECTIVE/ANSWER-SLOT/v3".toUTF8.toList ++ body) with
  | none => rfl
  | some slot =>
    have canon := framed_canonical found
    have cut := congrArg (List.take frame.length) canon
    change (frame ++ slotStream.encode slot).take frame.length =
      ("DREGG/OBJECTIVE/ANSWER-SLOT/v3".toUTF8.toList ++ body).take frame.length at cut
    rw [List.take_left' rfl, List.take_left' (by decide +kernel)] at cut
    exact absurd cut (by decide +kernel)

theorem sample_delivered :
    decideDelivery sampleSendSlot ⟨1⟩ 5 (.reply [3]) =
      .ok {sampleSendSlot with phase := .decided (.reply [3]) 5, queued := []} := rfl

theorem sample_other_message : decideDelivery sampleSendSlot ⟨2⟩ 5 (.reply [3]) = .error .notDecider := rfl

theorem sample_subject_on_send_slot : decide sampleSendSlot ⟨1⟩ 5 (.reply [3]) = .error .notDecider := rfl

theorem sample_send_slot_never_expires : expire sampleSendSlot 1000 = .error .deliveryDecides := rfl

theorem sample_decided :
    decide sampleSlot ⟨7⟩ 5 (.reply [3]) = .ok {sampleSlot with phase := .decided (.reply [3]) 5} := rfl

theorem sample_stranger :
    decide sampleSlot ⟨8⟩ 5 (.reply [3]) = .error .notDecider := rfl

theorem sample_late :
    decide sampleSlot ⟨7⟩ 11 (.reply [3]) = .error (.pastDeadline 10 11) := rfl

theorem sample_expired :
    expire sampleSlot 11 = .ok {sampleSlot with phase := .decided .expired 11} := rfl

theorem sample_not_yet_expired : expire sampleSlot 10 = .error (.notYetExpired 10 10) := rfl

#assert_axioms roundTrip
#assert_axioms decide_single_decider
#assert_axioms decided_refuses
#assert_axioms expire_after_deadline
#assert_axioms stranger_refused
#assert_axioms sample_decided
#assert_axioms sample_stranger
#assert_axioms sample_late
#assert_axioms sample_expired
#assert_axioms sample_not_yet_expired
#assert_axioms decide_delivery_refused
#assert_axioms expire_delivery_refused
#assert_axioms decideDelivery_single
#assert_axioms decideDelivery_subject_refused
#assert_axioms sample_delivered
#assert_axioms sample_other_message
#assert_axioms sample_subject_on_send_slot
#assert_axioms sample_send_slot_never_expires
#assert_axioms cancelDelivery_spec
#assert_axioms stopWaiting_spec
#assert_axioms sample_cancelled
#assert_axioms sample_cancel_decided_refused
#assert_axioms sample_cancel_subject_refused
#assert_axioms sample_stopped
#assert_axioms v3_refuses
end Minidregg.Kernel.AnswerSlot
