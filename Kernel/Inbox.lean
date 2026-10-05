/- Inboxes (OB8): the per-(sender, target) FIFO queue an asynchronous `send`
appends to and a `deliverMessage` turn pops (`Kernel.ObjectiveSend`).

**The cell.** One inbox per (sender object, target object), at the protected
activity coordinate of role `inbox` (`cell`, `cell_reserved`): every intent of
another facet that writes it is refused by name (`ObjectiveActivityGate`), so
only the object kernel's own turns write it.

**The law is the queue discipline** (`Step`, `Lawful`): a step appends one
message at the tail while the queue holds fewer than `bound` messages, or removes
the head and advances `head`. Nothing else: no reordering, no removal from the
middle, no rewrite of a queued message, no overflow. `lawful_fifo` states what
that means for a whole turn: what was queued before, followed by what the turn
pushed, is what it popped followed by what is queued after, and `head` advanced
by exactly the number popped. `reorder_unlawful` is the tooth.

**A message** carries its own escrow: the declared envelope its delivery runs
under, the postage (the public price of that envelope) the sending turn moved
into the purse of the queue holding it, and the account the postage returns to
if the message is never delivered. Its id is `H(sending turn, index of the send
in that turn)` (`sendId`), and it is also the name of its reply slot. -/
import Kernel.ObjectiveActivityWire
import Kernel.ObjectiveActivityCell
import Compiler.ObjectiveInvocationClaim

namespace Minidregg.Kernel.Inbox
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Compiler.ObjectiveInvocationClaim (Capacity capacityStream)
set_option autoImplicit false

/-- One queued message. -/
structure Message where
  /-- `sendId`: the sending turn and the send's index in it. Also its reply slot's name. -/
  id : Digest
  /-- The object whose frame sent it. -/
  sender : Nat
  method : String
  /-- The arguments, as data bytes. -/
  args : Bytes
  /-- The declared envelope its delivery runs under. -/
  envelope : Capacity
  /-- The escrowed price of `envelope`, held in the purse of the queue holding it. -/
  postage : Nat
  /-- The Book account the postage returns to if the message is never delivered. -/
  refund : Nat
  deriving DecidableEq, Repr

structure Inbox where
  sender : Nat
  target : Nat
  /-- The sequence number of the first queued message (the number ever popped). -/
  head : Nat
  messages : List Message
  deriving DecidableEq, Repr

/-- The most messages one inbox (and one slot's forwarding queue) holds. -/
def bound : Nat := 16

def Inbox.empty (sender target : Nat) : Inbox := ⟨sender, target, 0, []⟩

/-- The sequence number the next pushed message gets. -/
def Inbox.tail (inbox : Inbox) : Nat := inbox.head + inbox.messages.length

/-- Append at the tail: refused (`none`) when the queue is full. -/
def Inbox.push (inbox : Inbox) (message : Message) : Option Inbox :=
  if inbox.messages.length < bound then some { inbox with messages := inbox.messages ++ [message] } else none

/-- Remove the head. -/
def Inbox.pop (inbox : Inbox) : Option (Message × Inbox) :=
  match inbox.messages with
  | [] => none
  | message :: rest => some (message, { inbox with head := inbox.head + 1, messages := rest })

/-! ## The law -/

/-- One step of the queue discipline. -/
inductive Step : Inbox → Inbox → Prop
  | push (inbox : Inbox) (message : Message) (room : inbox.messages.length < bound) :
      Step inbox { inbox with messages := inbox.messages ++ [message] }
  | pop (inbox : Inbox) (message : Message) (rest : List Message) (front : inbox.messages = message :: rest) :
      Step inbox { inbox with head := inbox.head + 1, messages := rest }

/-- What a turn may do to an inbox: steps of the discipline, in order. -/
inductive Lawful : Inbox → Inbox → Prop
  | refl (inbox : Inbox) : Lawful inbox inbox
  | step {a b c : Inbox} : Step a b → Lawful b c → Lawful a c

theorem Lawful.snoc {a b c : Inbox} (lawful : Lawful a b) (step : Step b c) : Lawful a c := by
  induction lawful with
  | refl _ => exact .step step (.refl _)
  | step first _ ih => exact .step first (ih step)

theorem Lawful.trans {a b c : Inbox} (one : Lawful a b) (two : Lawful b c) : Lawful a c := by
  induction one with
  | refl _ => exact two
  | step first _ ih => exact .step first (ih two)

theorem push_step {inbox next : Inbox} {message : Message} (pushed : inbox.push message = some next) :
    Step inbox next := by
  unfold Inbox.push at pushed
  split at pushed
  · rename_i room; cases pushed; exact .push inbox message room
  · cases pushed

theorem pop_step {inbox next : Inbox} {message : Message} (popped : inbox.pop = some (message, next)) :
    Step inbox next ∧ ∃ rest, inbox.messages = message :: rest ∧ next.messages = rest ∧ next.head = inbox.head + 1 := by
  unfold Inbox.pop at popped
  cases front : inbox.messages with
  | nil => simp only [front] at popped; cases popped
  | cons first rest =>
    simp only [front, Option.some.injEq, Prod.mk.injEq] at popped
    obtain ⟨rfl, rfl⟩ := popped
    exact ⟨.pop inbox first rest front, rest, rfl, rfl, rfl⟩

/-- **A full queue refuses a push.** -/
theorem push_full (inbox : Inbox) (message : Message) (full : bound ≤ inbox.messages.length) :
    inbox.push message = none := by
  simp [Inbox.push, Nat.not_lt.mpr full]

/-- A step keeps the inbox's ends, never moves `head` back, and never overfills. -/
theorem Step.keeps {a b : Inbox} (step : Step a b) :
    b.sender = a.sender ∧ b.target = a.target ∧ a.head ≤ b.head ∧
      (a.messages.length ≤ bound → b.messages.length ≤ bound) := by
  cases step with
  | push message room => exact ⟨rfl, rfl, Nat.le_refl _, fun _ => by simp; omega⟩
  | pop message rest front => exact ⟨rfl, rfl, Nat.le_succ _, fun within => by simp [front] at within ⊢; omega⟩

theorem Lawful.keeps {a b : Inbox} (lawful : Lawful a b) :
    b.sender = a.sender ∧ b.target = a.target ∧ a.head ≤ b.head ∧
      (a.messages.length ≤ bound → b.messages.length ≤ bound) := by
  induction lawful with
  | refl _ => exact ⟨rfl, rfl, Nat.le_refl _, id⟩
  | step first _ ih =>
    obtain ⟨s1, t1, h1, b1⟩ := first.keeps
    obtain ⟨s2, t2, h2, b2⟩ := ih
    exact ⟨s2.trans s1, t2.trans t1, Nat.le_trans h1 h2, fun within => b2 (b1 within)⟩

/-- **First in, first out.** Over any lawful change, what was queued followed by
what was pushed is what was popped followed by what is queued now, and `head`
advanced by exactly the number popped: no message is reordered, dropped from the
middle, rewritten or duplicated. -/
theorem lawful_fifo {a b : Inbox} (lawful : Lawful a b) :
    ∃ popped pushed : List Message, a.messages ++ pushed = popped ++ b.messages ∧
      b.head = a.head + popped.length := by
  induction lawful with
  | refl inbox => exact ⟨[], [], by simp, by simp⟩
  | step first _ ih =>
    obtain ⟨popped, pushed, same, advanced⟩ := ih
    cases first with
    | push message _ =>
      exact ⟨popped, message :: pushed, by simpa using same, by simpa using advanced⟩
    | pop message rest front =>
      refine ⟨message :: popped, pushed, ?_, ?_⟩
      · simp only at same; rw [front]; simpa using same
      · simp only at advanced; rw [advanced]; simp; omega

/-! Inhabitants and teeth (closed values, no hashing). -/

def sampleMessage (n : Nat) : Message := ⟨⟨n⟩, 1, "m", [], ⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩, 1, 9⟩

def sampleInbox : Inbox := ⟨1, 2, 0, [sampleMessage 10, sampleMessage 11]⟩

theorem sample_push_pop :
    Lawful (Inbox.empty 1 2) { (Inbox.empty 1 2) with messages := [sampleMessage 10] } :=
  .step (.push _ (sampleMessage 10) (by decide)) (.refl _)

/-- **The tooth**: swapping two queued messages, keeping `head`, is not lawful. -/
theorem reorder_unlawful :
    ¬ Lawful sampleInbox { sampleInbox with messages := [sampleMessage 11, sampleMessage 10] } := by
  intro lawful
  obtain ⟨popped, pushed, same, advanced⟩ := lawful_fifo lawful
  have none : popped = [] := by
    simp [sampleInbox] at advanced
    exact List.length_eq_zero_iff.mp advanced.symm
  subst none
  simp [sampleInbox] at same
  exact absurd same.1 (by decide)

/-- A full inbox refuses, by the bound alone. -/
theorem sample_full :
    ({ sampleInbox with messages := List.replicate bound (sampleMessage 10) } : Inbox).push (sampleMessage 11) =
      none := push_full _ _ (by simp)

/-! ## Codec, key, cell -/

def messageStream : StreamCodec Message :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product StreamCodec.nat (StreamCodec.product stringStream
      (StreamCodec.product bytesStream (StreamCodec.product capacityStream
        (StreamCodec.product StreamCodec.nat StreamCodec.nat))))))
    (fun m => (m.id, m.sender, m.method, m.args, m.envelope, m.postage, m.refund))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2.1, w.2.2.2.2.2.1, w.2.2.2.2.2.2⟩)
    (by intro m; cases m; rfl)

def inboxStream : StreamCodec Inbox :=
  StreamCodec.xmap
    (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.list messageStream))))
    (fun i => (i.sender, i.target, i.head, i.messages))
    (fun w => ⟨w.1, w.2.1, w.2.2.1, w.2.2.2⟩)
    (by intro i; cases i; rfl)

def frame : Bytes := "DREGG/OBJECTIVE/INBOX/v1".toUTF8.toList
def codec := framed frame inboxStream
def encode (inbox : Inbox) : Bytes := codec.encode inbox
def decode (bytes : Bytes) : Option Inbox := codec.decode bytes

theorem roundTrip (inbox : Inbox) : decode (encode inbox) = some inbox := framed_roundTrip _ _ inbox

/-- The coordinate preimage of an inbox: (sender, target). -/
def key (sender target : Nat) : Bytes := StreamCodec.nat.encode sender ++ StreamCodec.nat.encode target

/-- The inbox of (sender, target): a protected activity coordinate of role `inbox`. -/
def cell (domain : Digest) (sender target : Nat) : CellId :=
  ⟨ObjectiveActivityCell.coordinate domain .inbox (key sender target)⟩

/-- **Condition (a): an inbox lives at a protected coordinate**, at or above
`reservedBase`, which the ordinary gate refuses to every other facet. -/
theorem cell_reserved (domain : Digest) (sender target : Nat) :
    ObjectiveActivityCell.reservedBase ≤ (cell domain sender target).value :=
  ObjectiveActivityCell.coordinate_reserved domain .inbox (key sender target)

/-- The id of the `index`-th send of the turn `turn`: the message's id and its reply slot's name. -/
def sendId (turn : TransactionId) (index : Nat) : Digest :=
  tagged "DREGG/OBJECTIVE/SEND/ID/v1" (digestStream.encode turn ++ StreamCodec.nat.encode index)

#assert_axioms Lawful.snoc
#assert_axioms Lawful.trans
#assert_axioms push_step
#assert_axioms pop_step
#assert_axioms push_full
#assert_axioms Step.keeps
#assert_axioms Lawful.keeps
#assert_axioms lawful_fifo
#assert_axioms sample_push_pop
#assert_axioms reorder_unlawful
#assert_axioms sample_full
#assert_axioms roundTrip
#assert_axioms cell_reserved

end Minidregg.Kernel.Inbox
