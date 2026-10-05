/- Message delivery (OB8): the turn that pops the head of an inbox and runs it.

A `send` (`Kernel.ObjectiveCall`, a call frame's yield) queues a message on the
inbox of (sender, target) and opens its reply slot, whose decider is the ROLE
`delivery m` (`AnswerSlot.Decider`). `deliverMessage` is that role's only turn:

* **Anyone may submit it**, naming the inbox and the id of its head message (a
  stale id refuses: the head moved). It reads the inbox and pops the head.
* **It runs the message** as a root frame of a call tree (`ObjectiveCall.exec`):
  `method` of the target object, with the message's arguments, under the
  message's own escrowed envelope, with `request/caller` the sender and NO
  subject (`request/subject` is absent: a message carries no signer's
  authority, so a law that reads it fails closed).
* **The delivery decides the reply slot** (`AnswerSlot.decideDelivery`):
  `reply result` when the call tree returned; otherwise `broken reason`. A
  failure of the delivered method (its law refused a write, it faulted, it ran
  out of the envelope, it is not callable, it tried to send: a delivery has no
  paying account) is NOT a refusal of the turn: it is a kernel decision, and the
  message is popped all the same (`MessageRefusal` has no member for any of
  them; `failed_delivery_pops`). A delivery that failed commits no write of its
  call tree.
* **Forwarding.** Sends queued on the slot (pipelined sends to this reply) are
  handled in the same turn: when the reply is a reference to an object
  (`ref n`), each is pushed onto the inbox (its sender, n) with its own reply
  slot opened, its postage moving from this inbox's purse to that inbox's purse
  (each forwarded send is paid from its own escrow, never by the resolver); a
  forward that cannot be queued (a full inbox, a taken slot), and every queued
  send when the reply is no reference or the delivery failed, is REFUNDED: its
  postage returns to the account that paid it (`broken NotAReference`).
* **Paid from the inbox purse only.** The delivery's fee is the message's own
  escrowed postage, paid from the inbox's purse to the collector; forwards and
  refunds are transfers out of the same purse (`debits_only_purse`). Nothing is
  charged to the submitter.

The turn is ONE intent: the inboxes and slots it read and writes (each a lawful
queue step of what it held), the decided slot, the delivered call tree's state
writes, and the Book, guarded on every object it read, spending the message's
claim (`messageClaim`): a message is delivered once. -/
import Kernel.ObjectiveCall

namespace Minidregg.Kernel.ObjectiveSend
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Kernel.ObjectiveCall
open Minidregg.Theory.CanonicalResourceKernel (Book Batch Operation AccountId AssetId logicalBook)
set_option autoImplicit false

structure MessageRequest where
  /-- Whoever submits; the kernel reads no authority from it. -/
  subject : SubjectId
  sender : Nat
  target : Nat
  /-- The id of the head message the submitter delivers. -/
  message : Digest

/-- Every delivery of one message shares one transaction id. -/
def messageTransaction (id : Digest) : TransactionId :=
  tagged "DREGG/OBJECTIVE/MESSAGE/TX/DELIVER/v1" (digestStream.encode id)

/-- Spent by the turn that delivers the message. -/
def messageClaim (id : Digest) : StableNullifier := claim "message" (digestStream.encode id)

/-- A reply that is a reference to an object: `ref n`. -/
def referenceOf : Data → Option Nat
  | .variant "ref" (.natural object) => some object
  | _ => none

/-- How a delivery went: its call tree returned (with its journal), or failed. -/
inductive Outcome where
  | replied (result : Data) (journal : Journal)
  | failed (reason : String)

/-- Run a message: `method` of `target` as a root frame, caller the sender, no
subject, under the message's envelope. A delivered call tree may not send. -/
def runMessage {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (target : Nat) (message : Inbox.Message) : Outcome :=
  match decodeDataBytes message.args with
  | none => .failed "the arguments do not decode"
  | some args =>
    match exec config snapshot height ⟨none, some message.sender⟩ (messageTransaction message.id)
        (callFuel message.envelope) [] (.enter ⟨⟨target⟩, message.method, args⟩) (Journal.start [])
        message.envelope.sourceTicks with
    | .error reason => .failed (reprStr reason)
    | .ok (result, journal, _) =>
      if journal.outbox.isEmpty then .replied result journal
      else .failed "a delivered message sends: its delivery has no paying account"

def Outcome.decision : Outcome → AnswerSlot.Decision
  | .replied result _ => .reply (dataBytes result)
  | .failed reason => .broken reason

def Outcome.reference : Outcome → Option Nat
  | .replied result _ => referenceOf result
  | .failed _ => none

/-- The state writes of a delivery that returned. -/
def Outcome.posts {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) : Outcome → List Post
  | .replied _ journal => journal.posts config snapshot
  | .failed _ => []

def Outcome.guards {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) : Outcome → List ReadGuard
  | .replied _ journal => journal.guards config snapshot
  | .failed _ => []

/-- **Forward the sends queued on a decided slot** to the object its reply
names: each is queued on (its sender, that object) with its reply slot opened;
any that cannot be (no reference, not an object, a full inbox, a taken slot) is
refunded. Never refuses. -/
def forward {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (reference : Option Nat) : Mail config snapshot → List Inbox.Message → Mail config snapshot × List Inbox.Message
  | mail, [] => (mail, [])
  | mail, message :: rest =>
    match reference.map fun target => mail.send message (.object target) with
    | some (.ok next) => forward reference next rest
    | _ =>
      let (mail, refunds) := forward reference mail rest
      (mail, message :: refunds)

/-- The delivery's Book batch, every operation out of the inbox's purse: the
message's postage to the collector, each forward's postage to its new inbox's
purse, each refund back to its payer. -/
def deliveryBatch {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} (config : Config) (book : Book)
    (purse : AccountId) (message : Inbox.Message) (mail : Mail config snapshot) (refunds : List Inbox.Message) : Batch :=
  ⟨mail.registrations book,
    (if message.postage = 0 then [] else [.fee purse config.collector config.asset message.postage]) ++
      creditTransfers config purse mail.credits ++
      refunds.filterMap (fun refunded => if refunded.postage = 0 ∨ refunded.refund = purse then none
        else some (.transfer purse refunded.refund config.asset refunded.postage)), []⟩

inductive MessageRefusal where
  /-- The inbox cell holds no inbox of (sender, target). -/
  | noInbox (sender target : Nat)
  | empty (sender target : Nat)
  /-- The head is not the message the command names (it was delivered). -/
  | staleHead (head : Digest)
  /-- The head's reply slot is missing, misnamed or not its delivery's to decide. -/
  | replySlot (reason : String)
  | kernel (reason : ObjectiveActivity.Refusal)
  deriving Repr

/-- An admitted delivery. -/
structure MessageDelivery {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : MessageRequest) where
  private mk ::
  inbox : Inbox.Inbox
  readExact : readInbox snapshot (Inbox.cell config.domain request.sender request.target) = some (some inbox)
  clean : bodyOf .package (snapshot.canonicalBytes (Inbox.cell config.domain request.sender request.target)) = none
  ends : inbox.sender = request.sender ∧ inbox.target = request.target
  message : Inbox.Message
  remaining : Inbox.Inbox
  popped : inbox.pop = some (message, remaining)
  named : message.id = request.message
  slot : AnswerSlot.Slot
  slotExact : readSlot config snapshot message.id = some slot
  slotNamed : slot.name = message.id
  outcome : Outcome
  outcomeExact : runMessage config snapshot height request.target message = outcome
  decided : AnswerSlot.Slot
  decidedExact : AnswerSlot.decideDelivery slot message.id height outcome.decision = .ok decided
  /-- The popped inbox, held by this turn. -/
  seed : Mail config snapshot
  seedExact : seed.inboxes.map (fun held => (held.sender, held.target, held.now)) =
    [(request.sender, request.target, remaining)] ∧ seed.slots = [] ∧ seed.credits = [] ∧ seed.targets = []
  mail : Mail config snapshot
  refunds : List Inbox.Message
  forwarded : forward outcome.reference seed slot.queued = (mail, refunds)
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  batchExact : posted.batch = deliveryBatch config (logicalBook book.logical)
    (Inbox.cell config.domain request.sender request.target).value message mail refunds
  posts : List Post
  postsExact : posts = outcome.posts config snapshot ++ mail.posts ++
    [slotPost config snapshot decided, posted.write config snapshot]

/-- The popped inbox, as a held inbox of this turn's mail. -/
def seedMail {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (sender target : Nat)
    (inbox remaining : Inbox.Inbox) (message : Inbox.Message)
    (readExact : readInbox snapshot (Inbox.cell config.domain sender target) = some (some inbox))
    (clean : bodyOf .package (snapshot.canonicalBytes (Inbox.cell config.domain sender target)) = none)
    (ends : inbox.sender = sender ∧ inbox.target = target)
    (popped : inbox.pop = some (message, remaining)) : Mail config snapshot :=
  have step := (Inbox.pop_step popped).1
  have keeps := step.keeps
  ⟨[⟨sender, target, some inbox, readExact, clean, remaining, .step step (.refl _),
      ⟨keeps.1.trans ends.1, keeps.2.1.trans ends.2⟩⟩], [], [], []⟩

def deliverMessage {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : MessageRequest) : Except MessageRefusal (MessageDelivery config snapshot height request) :=
  match readExact : readInbox snapshot (Inbox.cell config.domain request.sender request.target) with
  | none | some none => .error (.noInbox request.sender request.target)
  | some (some inbox) =>
  if clean : bodyOf .package (snapshot.canonicalBytes (Inbox.cell config.domain request.sender request.target)) = none then
  if ends : inbox.sender = request.sender ∧ inbox.target = request.target then
  match popped : inbox.pop with
  | none => .error (.empty request.sender request.target)
  | some (message, remaining) =>
  if named : message.id = request.message then
  match slotExact : readSlot config snapshot message.id with
  | none => .error (.replySlot "missing")
  | some slot =>
  if slotNamed : slot.name = message.id then
  match outcomeExact : runMessage config snapshot height request.target message with
  | outcome =>
  match decidedExact : AnswerSlot.decideDelivery slot message.id height outcome.decision with
  | .error reason => .error (.replySlot (reprStr reason))
  | .ok decided =>
  let seed := seedMail config snapshot request.sender request.target inbox remaining message readExact clean ends popped
  match forwarded : forward outcome.reference seed slot.queued with
  | (mail, refunds) =>
  match bookExact : loadBook config snapshot with
  | .error reason => .error (.kernel reason)
  | .ok book =>
  let batch := deliveryBatch config (logicalBook book.logical)
    (Inbox.cell config.domain request.sender request.target).value message mail refunds
  match postedExact : postings book batch with
  | .error reason => .error (.kernel reason)
  | .ok posted =>
    have batchExact : posted.batch = batch := by
      unfold postings at postedExact
      split at postedExact
      · cases postedExact; rfl
      · cases postedExact
    .ok ⟨inbox, readExact, clean, ends, message, remaining, popped, named, slot, slotExact, slotNamed, outcome,
      outcomeExact, decided, decidedExact, seed, ⟨rfl, rfl, rfl, rfl⟩, mail, refunds, forwarded, book, bookExact,
      posted, batchExact, _, rfl⟩
  else .error (.replySlot "misnamed")
  else .error (.staleHead message.id)
  else .error (.noInbox request.sender request.target)
  else .error (.kernel (.packageSource "an inbox coordinate holds a package"))

def MessageDelivery.guards {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : MessageRequest} (delivered : MessageDelivery config snapshot height request) :
    List ReadGuard :=
  delivered.outcome.guards config snapshot ++
    delivered.mail.targets.map fun target => guardAt snapshot (objectCell config.domain ⟨target⟩)

def MessageDelivery.claims {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : MessageRequest} (delivered : MessageDelivery config snapshot height request) :
    List StableNullifier :=
  [messageClaim delivered.message.id]

def MessageDelivery.intent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : MessageRequest} (delivered : MessageDelivery config snapshot height request)
    (sealing : Seal) : DataIntent rootBytes :=
  intentOf rootBytes (messageTransaction delivered.message.id) delivered.posts delivered.guards delivered.claims sealing

/-! ## The four conditions, at the delivery -/

/-- **A delivery conserves every asset.** -/
theorem MessageDelivery.conserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : MessageRequest} (delivered : MessageDelivery config snapshot height request)
    (asset : AssetId) :
    (logicalBook delivered.posted.post.logical).totalAsset asset = (logicalBook delivered.book.logical).totalAsset asset :=
  delivered.posted.conserves asset

/-- The account an operation debits. -/
def debited : Operation → Option AccountId
  | .transfer source _ _ _ => some source
  | .fee payer _ _ _ => some payer
  | .burn source _ _ => some source
  | .lease _ holder _ _ _ _ _ => some holder
  | .mint _ _ _ => none

theorem creditTransfers_debit (config : Config) (source : AccountId) (credits : List (AccountId × Nat)) :
    ∀ op ∈ creditTransfers config source credits, debited op = some source := by
  intro op member
  simp only [creditTransfers, List.mem_filterMap] at member
  obtain ⟨⟨purse, amount⟩, _, made⟩ := member
  split at made
  · cases made
  · cases made; rfl

/-- **Condition (d): a delivery is paid from the inbox's purse only.** Every
operation of its batch, delivered or failed, debits the purse of the popped
inbox: the fee is the message's own escrowed postage, forwards and refunds move
escrow out of the same purse. No submitter, sender or target account is debited. -/
theorem MessageDelivery.debits_only_purse {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) :
    ∀ op ∈ delivered.posted.batch.operations,
      debited op = some (Inbox.cell config.domain request.sender request.target).value := by
  rw [delivered.batchExact]
  intro op member
  simp only [deliveryBatch] at member
  rcases List.mem_append.mp member with front | refund
  · rcases List.mem_append.mp front with fee | credit
    · split at fee
      · cases fee
      · simp only [List.mem_singleton] at fee; subst fee; rfl
    · exact creditTransfers_debit config _ _ op credit
  · simp only [List.mem_filterMap] at refund
    obtain ⟨refunded, _, made⟩ := refund
    split at made
    · cases made
    · cases made; rfl

/-- **The delivery pops its message**: the head of the inbox it read is the
message it ran and decided, and the inbox it posts is a lawful change (FIFO,
`Inbox.Lawful`) of the inbox with that head removed and `head` advanced. -/
theorem MessageDelivery.pops {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : MessageRequest} (delivered : MessageDelivery config snapshot height request) :
    ∃ rest, delivered.inbox.messages = delivered.message :: rest ∧ delivered.remaining.messages = rest ∧
      delivered.remaining.head = delivered.inbox.head + 1 ∧ delivered.message.id = request.message :=
  let ⟨_, rest, front, after, advanced⟩ := Inbox.pop_step delivered.popped
  ⟨rest, front, after, advanced, delivered.named⟩

/-- **Condition (c): only the delivery of its own message decides a reply slot.**
The slot a delivery decides is the reply slot of the message it popped: read
at that message's id, named by it, its decider the role `delivery` of that very
message, open until now; and its decision is this delivery's outcome. -/
theorem MessageDelivery.decides_own_slot {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) :
    readSlot config snapshot delivered.message.id = some delivered.slot ∧
      delivered.slot.decider = .delivery delivered.message.id ∧ delivered.slot.phase = .opened ∧
      delivered.inbox.messages.head? = some delivered.message ∧
      delivered.decided = {delivered.slot with phase := .decided delivered.outcome.decision height, queued := []} := by
  obtain ⟨role, opened, _, decided⟩ := AnswerSlot.decideDelivery_single delivered.decidedExact
  obtain ⟨rest, front, _, _, _⟩ := delivered.pops
  exact ⟨delivered.slotExact, role, opened, by rw [front]; rfl, decided⟩

/-- **A failed delivery still pops, and decides `broken`** (condition (d)): when
the delivered call tree failed, for whatever reason the method gave, the turn
is admitted all the same; it removes the head, decides the reply slot `broken`
with the reason, commits no write of the failed call tree, and refunds every
send queued on the slot. -/
theorem MessageDelivery.failed_delivery_pops {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) {reason : String}
    (failed : delivered.outcome = .failed reason) :
    delivered.decided.phase = .decided (.broken reason) height ∧
      delivered.outcome.posts config snapshot = [] ∧ delivered.refunds = delivered.slot.queued ∧
      delivered.mail.inboxes.map (fun held => (held.sender, held.target, held.now)) =
        [(request.sender, request.target, delivered.remaining)] := by
  obtain ⟨_, _, _, decided⟩ := AnswerSlot.decideDelivery_single delivered.decidedExact
  have forwarded := delivered.forwarded
  rw [failed] at forwarded
  have none_forwarded : ∀ (mail : Mail config snapshot) (queued : List Inbox.Message),
      forward (rootBytes := rootBytes) none mail queued = (mail, queued) := by
    intro mail queued
    induction queued generalizing mail with
    | nil => rfl
    | cons message rest ih => simp [forward, ih]
  rw [show (Outcome.failed reason).reference = none from rfl, none_forwarded] at forwarded
  simp only [Prod.mk.injEq] at forwarded
  obtain ⟨sameMail, sameRefunds⟩ := forwarded
  refine ⟨by rw [decided, failed]; rfl, by rw [failed]; rfl, sameRefunds.symm, ?_⟩
  rw [← sameMail]
  exact delivered.seedExact.1

#assert_axioms MessageDelivery.conserves
#assert_axioms creditTransfers_debit
#assert_axioms MessageDelivery.debits_only_purse
#assert_axioms MessageDelivery.pops
#assert_axioms MessageDelivery.decides_own_slot
#assert_axioms MessageDelivery.failed_delivery_pops

end Minidregg.Kernel.ObjectiveSend
