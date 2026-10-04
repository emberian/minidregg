/- Answer slots: the cell an awaiting activity's reply arrives in.

A slot is named `H(turn, call site)`: the transaction of the yielding turn and
the yield's place in its activity (record cell and generation), so every
validator derives the same name and no submitter chooses it. It has exactly
one decider (a subject, fixed when the slot opens), one deadline height, and
one terminal decision, written once:

  open --decider, at or before the deadline--> decided (reply | refused | unknown | broken)
  open --anyone, strictly after the deadline--> decided expired

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
  deriving DecidableEq, Repr

inductive Phase where
  | opened
  | decided (decision : Decision) (height : Nat)
  deriving DecidableEq, Repr

structure Slot where
  name : Digest
  /-- The record cell of the one activity this slot answers. -/
  activity : CellId
  decider : SubjectId
  deadline : Nat
  phase : Phase
  deriving DecidableEq, Repr

def decisionStream : StreamCodec Decision :=
  StreamCodec.xmap
    (StreamCodec.sum bytesStream (StreamCodec.sum stringStream
      (StreamCodec.sum unitStream (StreamCodec.sum stringStream unitStream))))
    (fun decision => match decision with
      | .reply value => .inl value
      | .refused reason => .inr (.inl reason)
      | .unknown => .inr (.inr (.inl ()))
      | .broken reason => .inr (.inr (.inr (.inl reason)))
      | .expired => .inr (.inr (.inr (.inr ()))))
    (fun wire => match wire with
      | .inl value => .reply value
      | .inr (.inl reason) => .refused reason
      | .inr (.inr (.inl _)) => .unknown
      | .inr (.inr (.inr (.inl reason))) => .broken reason
      | .inr (.inr (.inr (.inr _))) => .expired)
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

def slotStream : StreamCodec Slot :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      (StreamCodec.product subjectStream (StreamCodec.product StreamCodec.nat phaseStream))))
    (fun slot => (slot.name, slot.activity, slot.decider, slot.deadline, slot.phase))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2.1, wire.2.2.2.1, wire.2.2.2.2⟩)
    (by intro slot; cases slot; rfl)

def frame : Bytes := "DREGG/OBJECTIVE/ANSWER-SLOT/v1".toUTF8.toList
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
  deriving DecidableEq, Repr

/-- The decider's decision, at or before the deadline, of an open slot. -/
def decide (slot : Slot) (subject : SubjectId) (height : Nat) (decision : Decision) :
    Except Refusal Slot :=
  match slot.phase with
  | .decided _ _ => .error .notOpen
  | .opened =>
    if decision = .expired then .error .expiryIsKernelOnly
    else if subject ≠ slot.decider then .error .notDecider
    else if slot.deadline < height then .error (.pastDeadline slot.deadline height)
    else .ok {slot with phase := .decided decision height}

/-- Anyone's expiry, strictly after the deadline, of a slot still open. -/
def expire (slot : Slot) (height : Nat) : Except Refusal Slot :=
  match slot.phase with
  | .decided _ _ => .error .notOpen
  | .opened =>
    if slot.deadline < height then .ok {slot with phase := .decided .expired height}
    else .error (.notYetExpired slot.deadline height)

/-- Exactly one decider: a decided slot names the subject that decided it. -/
theorem decide_single_decider {slot decided : Slot} {subject : SubjectId} {height : Nat}
    {decision : Decision} (ok : decide slot subject height decision = .ok decided) :
    subject = slot.decider ∧ slot.phase = .opened ∧ height ≤ slot.deadline ∧
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
    · rename_i late
      cases ok
      exact ⟨late, opened, rfl⟩
    · cases ok

/-- A non-decider is refused whatever it decides. -/
theorem stranger_refused (slot : Slot) (subject : SubjectId) (height : Nat) (decision : Decision)
    (opened : slot.phase = .opened) (stranger : subject ≠ slot.decider) (notExpired : decision ≠ .expired) :
    decide slot subject height decision = .error .notDecider := by
  simp [decide, opened, notExpired, stranger]

/-! Inhabitants of the premises above (closed slots, no hashing). -/

def sampleSlot : Slot := ⟨⟨1⟩, ⟨2⟩, ⟨7⟩, 10, .opened⟩

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
end Minidregg.Kernel.AnswerSlot
