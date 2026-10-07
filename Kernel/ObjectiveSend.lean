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
* **The reply slot is THIS inbox's** (its activity cell is the inbox popped, else
  `replySlot "not this inbox's"`), and an unwatched one (its sender stopped waiting,
  `ObjectiveCall.ControlKind.stop`) is RETIRED instead of written (`replyPost`).
* **The delivery decides the reply slot** (`AnswerSlot.decideDelivery`):
  `reply result` when the call tree returned; otherwise `broken reason`. A
  failure of the delivered method (its law refused a write, it faulted, it ran
  out of the envelope, it is not callable, its onward sends were refused: see below)
  is NOT a refusal of the turn: it is a kernel decision, and the
  message is popped all the same (`MessageRefusal` has no member for any of
  them; `failed_delivery_pops`). A delivery that failed commits no write of its
  call tree.
* **Onward sends, out of the prepaid allowance (GPT-6 row F).** The delivered call tree may
  send only out of its message's continuation allowance (`Inbox.Message.allowance`, escrowed
  in this purse by whoever paid the postage): at most `Inbox.fanOut` sends, from a message
  below `Inbox.continuationDepth`, escrowing in total at most the allowance, each onward
  message one hop deeper, delivered under the same envelope, refunded to the same payer
  (`continueMessage`). Any refusal (`fanOut`, `continuationDepth`, `allowanceExceeded`, or
  one of `Mail.send`'s, such as `notDeliverable` for an onward send to a sending method)
  decides the slot `broken` naming it and commits none of the call tree's writes. The split
  is deliberate: the POSTAGE bought the attempt (the method ran, the collector is paid), the
  ALLOWANCE buys only the continuation, so it is refunded in full; what a successful
  delivery does not spend of it returns to the payer too (`escrow_conservation`). A send to a
  sending method is refused at the send unless its message continues
  (`ObjectiveCall.Deliverable`), so these checks are where the actual count is decided.
* **Forwarding.** Sends queued on the slot (pipelined sends to this reply) are
  handled in the same turn: when the reply is a reference to an object
  (`ref n`), each is pushed onto the inbox (its sender, n) with its own reply
  slot opened, its postage moving from this inbox's purse to that inbox's purse
  (each forwarded send is paid from its own escrow, never by the resolver); a
  forward that cannot be queued (its method not `Deliverable` at the RESOLVED
  object, decided now by the same `Mail.send` an invocation's send passes; a full
  inbox; a taken slot), and every queued
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
subject, under the message's envelope. A delivered call tree may not stop or cancel; its
sends are judged against the message's allowance by `continueMessage`. -/
def runMessage {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (target : Nat) (message : Inbox.Message) : Outcome :=
  match decodeDataBytes message.args with
  | none => .failed "the arguments do not decode"
  | some args =>
    match exec config snapshot height ⟨none, some message.sender⟩ (messageTransaction message.id)
        (callFuel message.envelope) [] (.enter ⟨⟨target⟩, message.method, args⟩) (Journal.start [] message.envelope.extractTicks)
        message.envelope.sourceTicks with
    | .error reason => .failed (reprStr reason)
    | .ok (result, journal, _) =>
      if journal.controls.isEmpty && journal.drained then .replied result journal
      else .failed (if !journal.controls.isEmpty then
          "a delivered message stops or cancels: only an invocation's call tree controls its object's messages"
        else "the state it leaves on a draining object is one MIGRATE would refuse")

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

/-! ### The continuation: onward sends out of the allowance -/

/-- The message an onward send of the delivery of `message` queues: delivered under the same
envelope, refunded to the same payer, one hop deeper. -/
def onwardOf (config : Config) (message : Inbox.Message) (out : Outgoing) : Inbox.Message :=
  messageOf config message.envelope message.refund (message.depth + 1) out

/-- What a delivery's onward sends escrow, in total, out of its message's allowance. -/
def onwardEscrow (config : Config) (message : Inbox.Message) (outs : List Outgoing) : Nat :=
  (outs.map fun out => (onwardOf config message out).escrow).sum

/-- The bounds of a delivery's onward sends, in order: the depth (`Inbox.continuationDepth`),
the fan-out (`Inbox.fanOut`), the allowance. -/
def onwardRefusal (config : Config) (message : Inbox.Message) (outs : List Outgoing) : Option CallRefusal :=
  if Inbox.continuationDepth ≤ message.depth then some (.continuationDepth Inbox.continuationDepth)
  else if Inbox.fanOut < outs.length then some (.fanOut Inbox.fanOut)
  else if message.allowance < onwardEscrow config message outs then
    some (.allowanceExceeded (onwardEscrow config message outs) message.allowance)
  else none

/-- **Continue a delivered message**: the call tree's sends are queued (`postMail`, into the
delivery's own mail) and paid out of the message's allowance, within its bounds; the result
is the delivery's outcome, its mail, and what the onward sends spent of the allowance. A
refusal fails the delivery (nothing of the call tree commits, nothing is spent). -/
def continueMessage {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (message : Inbox.Message) (seed : Mail config snapshot) : Outcome → Outcome × Mail config snapshot × Nat
  | .failed reason => (.failed reason, seed, 0)
  | .replied result journal =>
    if journal.outbox = [] then (.replied result journal, seed, 0) else
    match onwardRefusal config message journal.outbox with
    | some refusal => (.failed (reprStr refusal), seed, 0)
    | none =>
      match postMail config snapshot message.envelope message.refund (message.depth + 1) seed journal.outbox with
      | .error reason => (.failed (reprStr reason), seed, 0)
      | .ok mail => (.replied result journal, mail, onwardEscrow config message journal.outbox)

/-- **What a continuation can be**: the run unchanged, nothing sent; or a failure, nothing
sent; or the run with its sends queued out of the allowance, within every bound. -/
theorem continueMessage_cases {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {message : Inbox.Message} {seed mail : Mail config snapshot} {run outcome : Outcome} {spent : Nat}
    (continued : continueMessage config snapshot message seed run = (outcome, mail, spent)) :
    (outcome = run ∧ mail = seed ∧ spent = 0) ∨ (∃ reason, outcome = .failed reason ∧ mail = seed ∧ spent = 0) ∨
    (∃ result journal, run = .replied result journal ∧ outcome = run ∧ journal.outbox ≠ [] ∧
      message.depth < Inbox.continuationDepth ∧ journal.outbox.length ≤ Inbox.fanOut ∧
      spent = onwardEscrow config message journal.outbox ∧ spent ≤ message.allowance ∧
      postMail config snapshot message.envelope message.refund (message.depth + 1) seed journal.outbox = .ok mail) := by
  cases run with
  | failed reason =>
    simp only [continueMessage, Prod.mk.injEq] at continued
    obtain ⟨rfl, rfl, rfl⟩ := continued
    exact .inl ⟨rfl, rfl, rfl⟩
  | replied result journal =>
    simp only [continueMessage] at continued
    split at continued
    · simp only [Prod.mk.injEq] at continued
      obtain ⟨rfl, rfl, rfl⟩ := continued
      exact .inl ⟨rfl, rfl, rfl⟩
    · rename_i sends
      split at continued
      · simp only [Prod.mk.injEq] at continued
        obtain ⟨rfl, rfl, rfl⟩ := continued
        exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
      · rename_i within
        unfold onwardRefusal at within
        split at within
        · cases within
        · rename_i shallow
          split at within
          · cases within
          · rename_i narrow
            split at within
            · cases within
            · rename_i covered
              split at continued
              · simp only [Prod.mk.injEq] at continued
                obtain ⟨rfl, rfl, rfl⟩ := continued
                exact .inr (.inl ⟨_, rfl, rfl, rfl⟩)
              · rename_i posted
                simp only [Prod.mk.injEq] at continued
                obtain ⟨rfl, rfl, rfl⟩ := continued
                exact .inr (.inr ⟨result, journal, rfl, rfl, sends, by omega, by omega, rfl, by omega, posted⟩)

/-- A continuation that failed sent nothing: its mail is the seed and it spent nothing. -/
theorem continueMessage_failed {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {message : Inbox.Message} {seed mail : Mail config snapshot} {run : Outcome} {reason : String} {spent : Nat}
    (continued : continueMessage config snapshot message seed run = (.failed reason, mail, spent)) :
    mail = seed ∧ spent = 0 := by
  rcases continueMessage_cases continued with ⟨_, m, s⟩ | ⟨_, _, m, s⟩ | ⟨_, _, hrun, hout, _⟩
  · exact ⟨m, s⟩
  · exact ⟨m, s⟩
  · cases hout.trans hrun

/-- A continuation's outcome that replied is the run's own. -/
theorem continueMessage_replied {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {message : Inbox.Message} {seed mail : Mail config snapshot} {run : Outcome} {result : Data} {journal : Journal}
    {spent : Nat}
    (continued : continueMessage config snapshot message seed run = (.replied result journal, mail, spent)) :
    run = .replied result journal := by
  rcases continueMessage_cases continued with ⟨same, _⟩ | ⟨_, bad, _⟩ | ⟨_, _, _, same, _⟩
  · exact same.symm
  · cases bad
  · exact same.symm

/-- **Forward the sends queued on a decided slot** to the object its reply
names: each is queued on (its sender, that object) with its reply slot opened;
any that cannot be (no reference, not an object, a method not `Deliverable` there, a
full inbox, a taken slot) is refunded. Never refuses. -/
def forward {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (reference : Option Nat) : Mail config snapshot → List Inbox.Message → Mail config snapshot × List Inbox.Message
  | mail, [] => (mail, [])
  | mail, message :: rest =>
    match reference.map fun target => mail.send message (.object target) with
    | some (.ok next) => forward reference next rest
    | _ =>
      let (mail, refunds) := forward reference mail rest
      (mail, message :: refunds)

/-- A payment out of `purse` (dropped when zero, or when it would land in `purse` itself: the
escrow then simply stays where it is). -/
def payOut (config : Config) (purse payee : AccountId) (amount : Nat) : List Operation :=
  if amount = 0 ∨ payee = purse then [] else [.transfer purse payee config.asset amount]

/-- The delivery's Book batch, every operation out of the inbox's purse: the
message's postage to the collector, each onward send's and each forward's escrow to its
new queue's purse, each refunded forward's escrow back to its payer, and what the onward
sends did not spend of the allowance (`spent`) back to the message's payer. -/
def deliveryBatch {rootBytes : Bytes → Digest} {snapshot : Snapshot rootBytes} (config : Config) (book : Book)
    (purse : AccountId) (message : Inbox.Message) (spent : Nat) (mail : Mail config snapshot)
    (refunds : List Inbox.Message) : Batch :=
  ⟨mail.registrations book,
    (if message.postage = 0 then [] else [.fee purse config.collector config.asset message.postage]) ++
      creditTransfers config purse mail.credits ++
      refunds.flatMap (fun refunded => payOut config purse refunded.refund refunded.escrow) ++
      payOut config purse message.refund (message.allowance - spent), []⟩

/-- What a delivery writes at the reply slot: the decided slot, when someone waits for it;
the retired image when its sender stopped waiting (`ObjectiveCall.ControlKind.stop`): a
decision nobody reads is not kept. -/
def replyPost {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (slot decided : AnswerSlot.Slot) : Post :=
  if slot.watched then slotPost config snapshot decided else slotRetire config snapshot slot.name

inductive MessageRefusal where
  /-- The inbox cell holds no inbox of (sender, target). -/
  | noInbox (sender target : Nat)
  | empty (sender target : Nat)
  /-- The head is not the message the command names (it was delivered). -/
  | staleHead (head : Digest)
  /-- The head's reply slot is missing, misnamed, not this inbox's (its activity cell is
  another), or not its delivery's to decide. -/
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
  /-- The slot answers to THIS inbox: its activity cell is the inbox the message was popped from. -/
  activityExact : slot.activity = Inbox.cell config.domain request.sender request.target
  /-- The call tree as it ran. -/
  run : Outcome
  runExact : runMessage config snapshot height request.target message = run
  /-- The popped inbox, held by this turn. -/
  seed : Mail config snapshot
  seedExact : seed.inboxes.map (fun held => (held.sender, held.target, held.now)) =
    [(request.sender, request.target, remaining)] ∧ seed.slots = [] ∧ seed.credits = [] ∧ seed.targets = [] ∧
      seed.closed = [] ∧ seed.refunds = []
  /-- The delivery as it is decided: the run with its onward sends queued out of the
  allowance (`sent`, spending `spent`), or failed. -/
  outcome : Outcome
  sent : Mail config snapshot
  spent : Nat
  continued : continueMessage config snapshot message seed run = (outcome, sent, spent)
  decided : AnswerSlot.Slot
  decidedExact : AnswerSlot.decideDelivery slot message.id height outcome.decision = .ok decided
  mail : Mail config snapshot
  refunds : List Inbox.Message
  forwarded : forward outcome.reference sent slot.queued = (mail, refunds)
  book : BookCell
  bookExact : loadBook config snapshot = .ok book
  posted : Postings book
  batchExact : posted.batch = deliveryBatch config (logicalBook book.logical)
    (Inbox.cell config.domain request.sender request.target).value message spent mail refunds
  posts : List Post
  postsExact : posts = outcome.posts config snapshot ++ mail.posts ++
    [replyPost config snapshot slot decided, posted.write config snapshot]

/-- **An unwatched slot's delivery retires it; a watched one's writes the decision.** -/
theorem replyPost_spec {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (slot decided : AnswerSlot.Slot) :
    (slot.watched = true → replyPost config snapshot slot decided = slotPost config snapshot decided) ∧
      (slot.watched = false → replyPost config snapshot slot decided = slotRetire config snapshot slot.name) := by
  constructor <;> intro watched <;> simp [replyPost, watched]

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
      ⟨keeps.1.trans ends.1, keeps.2.1.trans ends.2⟩⟩], [], [], [], [], []⟩

/-- **A message to a draining object waits.** The target object drains toward an
upgrade that admits no new frame (`ObjectRecord.admitsNew`): delivering now would
fail the message (`broken`) for a reason that ends at MIGRATE, so the turn is
refused instead and the message stays queued (back-pressure is the inbox bound). -/
def waitsForUpgrade {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (target : Nat) :
    Bool :=
  match readObject config snapshot ⟨target⟩ with
  | .ok (some record) => !record.admitsNew
  | _ => false

def deliverMessage {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (request : MessageRequest) : Except MessageRefusal (MessageDelivery config snapshot height request) :=
  if waitsForUpgrade config snapshot request.target then .error (.kernel .draining) else
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
  if activityExact : slot.activity = Inbox.cell config.domain request.sender request.target then
  match runExact : runMessage config snapshot height request.target message with
  | run =>
  let seed := seedMail config snapshot request.sender request.target inbox remaining message readExact clean ends popped
  match continued : continueMessage config snapshot message seed run with
  | (outcome, sent, spent) =>
  match decidedExact : AnswerSlot.decideDelivery slot message.id height outcome.decision with
  | .error reason => .error (.replySlot (reprStr reason))
  | .ok decided =>
  match forwarded : forward outcome.reference sent slot.queued with
  | (mail, refunds) =>
  match bookExact : loadBook config snapshot with
  | .error reason => .error (.kernel reason)
  | .ok book =>
  let batch := deliveryBatch config (logicalBook book.logical)
    (Inbox.cell config.domain request.sender request.target).value message spent mail refunds
  match postedExact : postings book batch with
  | .error reason => .error (.kernel reason)
  | .ok posted =>
    have batchExact : posted.batch = batch := by
      unfold postings at postedExact
      split at postedExact
      · cases postedExact; rfl
      · cases postedExact
    .ok ⟨inbox, readExact, clean, ends, message, remaining, popped, named, slot, slotExact, slotNamed, activityExact,
      run, runExact, seed, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, outcome, sent, spent, continued, decided, decidedExact, mail,
      refunds, forwarded, book, bookExact, posted, batchExact, _, rfl⟩
  else .error (.replySlot "not this inbox's")
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

theorem payOut_debit (config : Config) (purse payee : AccountId) (amount : Nat) :
    ∀ op ∈ payOut config purse payee amount, debited op = some purse := by
  intro op member
  unfold payOut at member
  split at member
  · cases member
  · simp only [List.mem_singleton] at member; subst member; rfl

/-- **Condition (d): a delivery is paid from the inbox's purse only.** Every
operation of its batch, delivered or failed, debits the purse of the popped
inbox: the fee is the message's own escrowed postage, onward sends, forwards and refunds
move escrow out of the same purse. No submitter, sender or target account is debited. -/
theorem MessageDelivery.debits_only_purse {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) :
    ∀ op ∈ delivered.posted.batch.operations,
      debited op = some (Inbox.cell config.domain request.sender request.target).value := by
  rw [delivered.batchExact]
  intro op member
  simp only [deliveryBatch] at member
  rcases List.mem_append.mp member with front | remainder
  · rcases List.mem_append.mp front with front | refund
    · rcases List.mem_append.mp front with fee | credit
      · split at fee
        · cases fee
        · simp only [List.mem_singleton] at fee; subst fee; rfl
      · exact creditTransfers_debit config _ _ op credit
    · obtain ⟨refunded, _, made⟩ := List.mem_flatMap.mp refund
      exact payOut_debit config _ _ _ op made
  · exact payOut_debit config _ _ _ op remainder

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
the delivered call tree failed, for whatever reason the method gave (or its onward sends
were refused), the turn is admitted all the same; it removes the head, decides the reply
slot `broken` with the reason, commits no write of the failed call tree, sends nothing
onward, spends none of the allowance, and refunds every send queued on the slot. -/
theorem MessageDelivery.failed_delivery_pops {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) {reason : String}
    (failed : delivered.outcome = .failed reason) :
    delivered.decided.phase = .decided (.broken reason) height ∧
      delivered.outcome.posts config snapshot = [] ∧ delivered.refunds = delivered.slot.queued ∧
      delivered.spent = 0 ∧
      delivered.mail.inboxes.map (fun held => (held.sender, held.target, held.now)) =
        [(request.sender, request.target, delivered.remaining)] := by
  obtain ⟨_, _, _, decided⟩ := AnswerSlot.decideDelivery_single delivered.decidedExact
  have continued := delivered.continued
  rw [failed] at continued
  obtain ⟨sentSeed, spentZero⟩ := continueMessage_failed continued
  have forwarded := delivered.forwarded
  rw [failed, sentSeed] at forwarded
  have none_forwarded : ∀ (mail : Mail config snapshot) (queued : List Inbox.Message),
      forward (rootBytes := rootBytes) none mail queued = (mail, queued) := by
    intro mail queued
    induction queued generalizing mail with
    | nil => rfl
    | cons message rest ih => simp [forward, ih]
  rw [show (Outcome.failed reason).reference = none from rfl, none_forwarded] at forwarded
  simp only [Prod.mk.injEq] at forwarded
  obtain ⟨sameMail, sameRefunds⟩ := forwarded
  refine ⟨by rw [decided, failed]; rfl, by rw [failed]; rfl, sameRefunds.symm, spentZero, ?_⟩
  rw [← sameMail]
  exact delivered.seedExact.1

/-- **Every frame write of a delivered message's call tree is made under the pin of its own
object**: the facts it was judged under name the package that object's record pins, so the
object's pin clause accepts it (`ObjectRecord.objectivePin_accepts_run`). -/
theorem runMessage_writes_pinned {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height target : Nat} {message : Inbox.Message} {result : Data} {journal : Journal}
    (ran : runMessage config snapshot height target message = .replied result journal) :
    ∀ w ∈ journal.writes, w.facts.artifact = some w.record.activePin.value := by
  unfold runMessage at ran
  split at ran
  · cases ran
  · split at ran
    · cases ran
    · rename_i execExact
      split at ran
      · cases ran
        obtain ⟨_, _, ⟨new, writes, fresh⟩, _⟩ :=
          exec_invariant config snapshot height _ _ _ [] _ _ _ _ _ _ execExact
            (by simp) (by intro _ _ h; cases h) (by intro _ h; cases h)
        intro w member
        rw [writes] at member
        simp only [Journal.start, List.nil_append] at member
        exact (fresh w member).2.2
      · cases ran

/-- **Active-frame view stability for a delivered message's call tree**: every frame write is
applied to exactly the state that frame was shown (`ObjectiveCall.active_frame_view_stability`). -/
theorem runMessage_writes_from_view {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height target : Nat} {message : Inbox.Message} {result : Data} {journal : Journal}
    (ran : runMessage config snapshot height target message = .replied result journal) :
    ∀ w ∈ journal.writes, w.before = w.viewed := by
  unfold runMessage at ran
  split at ran
  · cases ran
  · split at ran
    · cases ran
    · rename_i execExact
      split at ran
      · cases ran
        obtain ⟨_, ⟨new, writes, fresh⟩⟩ :=
          active_frame_view_stability config snapshot height _ _ execExact (by simp) (by intro _ h; cases h)
        intro w member
        rw [writes] at member
        simp only [Journal.start, List.nil_append] at member
        exact fresh w member
      · cases ran

/-- **A delivery that replied is the run of its message**: the outcome it decides, when it
replied, is exactly what `runMessage` returned (`continueMessage` only fails a run or keeps it). -/
theorem MessageDelivery.ran {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) {result : Data} {journal : Journal}
    (replied : delivered.outcome = .replied result journal) :
    runMessage config snapshot height request.target delivered.message = .replied result journal := by
  have continued := delivered.continued
  rw [replied] at continued
  rw [delivered.runExact]
  exact continueMessage_replied continued

/-- Every state write a delivery commits is one its run made. -/
theorem MessageDelivery.posts_of_run {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) :
    ∀ post ∈ delivered.outcome.posts config snapshot, post ∈ delivered.run.posts config snapshot := by
  intro post member
  cases hout : delivered.outcome with
  | failed _ => rw [hout] at member; cases member
  | replied result journal =>
    rw [hout] at member
    have continued := delivered.continued
    rw [hout] at continued
    rw [continueMessage_replied continued]
    exact member

/-- The admitted delivery's own outcome, read through `runMessage_writes_pinned`. -/
theorem MessageDelivery.writes_pinned {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) {result : Data} {journal : Journal}
    (replied : delivered.outcome = .replied result journal) :
    ∀ w ∈ journal.writes, w.facts.artifact = some w.record.activePin.value :=
  runMessage_writes_pinned (delivered.ran replied)

#assert_axioms runMessage_writes_pinned
#assert_axioms runMessage_writes_from_view
#assert_axioms MessageDelivery.writes_pinned
#assert_axioms MessageDelivery.ran
#assert_axioms MessageDelivery.posts_of_run
#assert_axioms continueMessage_cases
#assert_axioms continueMessage_failed
#assert_axioms continueMessage_replied
#assert_axioms payOut_debit

/-! ## Retention: what a send and a delivery pay, and what they leave behind (OB8)

The activity turns retain their cells against a payer (`Birth.retention_cells_have_payer`,
...) and reserve a storage deposit in the activity's purse. The send path retains
two kinds of cell, an INBOX (`Inbox.cell`, role `inbox`) and a DELIVERY SLOT (role
`slot`, decider `delivery m`), and prices them as follows. These theorems state
what the admitting functions do, no more:

* an invocation is paid from its signer's account only (`Invocation.debits_only_account`),
  and each send credits exactly one purse with exactly the public price of the
  declared postage envelope (`Invocation.escrows_every_send`);
* a delivery is paid from the popped inbox's purse only (`MessageDelivery.debits_only_purse`,
  `conserves`), the popped message leaves the inbox
  (`MessageDelivery.pop_frees_message`), and a FAILED delivery posts exactly the
  shortened inbox, the decided slot and the Book (`MessageDelivery.failed_delivery_posts`);
* an inbox never exceeds `Inbox.bound` messages (`Mail.inboxes_bounded`,
  `MessageDelivery.remaining_within_bound`);
* every live cell the turns write names a payer (`Invocation.retention_cells_have_payer`,
  `MessageDelivery.retention_cells_have_payer`), under premises stated at each.

What is NOT stated, because it is false of the existing semantics (STATUS: design
questions for the grounding round): no STORAGE DEPOSIT backs an inbox cell or a
delivery slot (an inbox purse holds postage, which is the price of the delivered
envelope, and nothing for the bytes of the queued messages); an emptied inbox cell
is never retired and its purse never deregistered; a decided delivery slot is
retired only by its sender's `stop` (`ObjectiveCall.Mail.control`), or by its delivery when
the sender had stopped waiting before it (`replyPost`). -/

/-- **An invocation pays from its signer's account, and moves escrow only as its controls
refund it**: every operation of its batch (the envelope's fee, each send's postage into its
queue's purse) debits `request.account`, except the refund transfers of its controls, each
exactly a `Refund` its mail recorded (out of the purse that held the escrow, back to the
account that paid it; `Mail.control_cancel_refunds`). (Restated for row F: before the
controls the second alternative did not occur; `Invocation.debits_only_account_of_silent`
is the old statement, for a turn that controls nothing.) -/
theorem Invocation.debits_only_account {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : InvokeRequest}
    (invoked : Invocation config snapshot height request) :
    ∀ op ∈ invoked.posted.batch.operations, debited op = some request.account ∨
      ∃ refund ∈ invoked.mail.refunds, op = .transfer refund.purse refund.payer config.asset refund.amount := by
  rw [invoked.batchExact]
  intro op member
  simp only [invokeBatch, List.mem_cons, List.mem_append] at member
  rcases member with fee | credit | refunded
  · subst fee; exact .inl rfl
  · exact .inl (creditTransfers_debit config _ _ op credit)
  · right
    simp only [refundTransfers, List.mem_filterMap] at refunded
    obtain ⟨refund, member, made⟩ := refunded
    split at made
    · cases made
    · cases made; exact ⟨refund, member, rfl⟩

/-- Sending touches neither the closed slots nor the refunds of a mail. -/
theorem Mail.send_keeps {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail next : Mail config snapshot} {message : Inbox.Message} {destination : Destination}
    (sent : mail.send message destination = .ok next) : next.closed = mail.closed ∧ next.refunds = mail.refunds := by
  cases destination with
  | object target =>
    simp only [Mail.send] at sent
    repeat' split at sent
    all_goals first | (cases sent; done) | (cases sent; exact ⟨rfl, rfl⟩)
  | slot name =>
    simp only [Mail.send] at sent
    repeat' split at sent
    all_goals first | (cases sent; done) | (cases sent; exact ⟨rfl, rfl⟩)

theorem postMail_keeps {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (postage : Minidregg.Compiler.ObjectiveInvocationClaim.Capacity) (refund : AccountId) (depth : Nat) :
    ∀ (outs : List Outgoing) (mail next : Mail config snapshot),
      postMail config snapshot postage refund depth mail outs = .ok next →
      next.closed = mail.closed ∧ next.refunds = mail.refunds
  | [], mail, next, ok => by simp only [postMail] at ok; cases ok; exact ⟨rfl, rfl⟩
  | out :: rest, mail, next, ok => by
    simp only [postMail] at ok
    split at ok
    · cases ok
    · rename_i mail' sent
      obtain ⟨c1, r1⟩ := Mail.send_keeps sent
      obtain ⟨c2, r2⟩ := postMail_keeps postage refund depth rest mail' next ok
      exact ⟨c2.trans c1, r2.trans r1⟩

/-- Controls touch neither the credits nor the targets of a mail. -/
theorem Mail.control_credits {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail next : Mail config snapshot} {height : Nat} {control : Control}
    (ok : mail.control height control = .ok next) : next.credits = mail.credits ∧ next.targets = mail.targets := by
  rcases Mail.control_cases ok with same | ⟨_, _, _, _, _, _, _, _, _, rfl⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  · rw [same]; exact ⟨rfl, rfl⟩
  all_goals exact ⟨rfl, rfl⟩

theorem postControls_credits {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (height : Nat) :
    ∀ (controls : List Control) (mail next : Mail config snapshot),
      postControls config snapshot height mail controls = .ok next →
      next.credits = mail.credits ∧ next.targets = mail.targets
  | [], mail, next, ok => by simp only [postControls] at ok; cases ok; exact ⟨rfl, rfl⟩
  | control :: rest, mail, next, ok => by
    simp only [postControls] at ok
    split at ok
    · cases ok
    · rename_i mail' controlled
      obtain ⟨c1, t1⟩ := Mail.control_credits controlled
      obtain ⟨c2, t2⟩ := postControls_credits height rest mail' next ok
      exact ⟨c2.trans c1, t2.trans t1⟩

/-- A turn that yields no control posts the mail of its sends. -/
theorem Invocation.mail_of_silent {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : InvokeRequest}
    (invoked : Invocation config snapshot height request) (silent : invoked.journal.controls = []) :
    invoked.mail = invoked.sent := by
  have ok := invoked.mailExact
  rw [silent] at ok
  simp only [postControls] at ok
  exact (Except.ok.inj ok).symm

/-- **The old statement, for a turn that controls nothing**: every operation of its batch
debits `request.account`. -/
theorem Invocation.debits_only_account_of_silent {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : InvokeRequest}
    (invoked : Invocation config snapshot height request) (silent : invoked.journal.controls = []) :
    ∀ op ∈ invoked.posted.batch.operations, debited op = some request.account := by
  intro op member
  rcases Invocation.debits_only_account invoked op member with paid | ⟨refund, member, _⟩
  · exact paid
  · have none_ : invoked.mail.refunds = [] := by
      rw [Invocation.mail_of_silent invoked silent,
        (postMail_keeps request.postage request.account 0 _ _ _ invoked.sentExact).2]
      rfl
    rw [none_] at member
    cases member

/-- **Every send credits exactly one purse, with the escrow of its message** (its postage
and its continuation allowance). -/
theorem Mail.send_credit {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail next : Mail config snapshot} {message : Inbox.Message} {destination : Destination}
    (sent : mail.send message destination = .ok next) :
    ∃ purse, next.credits = mail.credits ++ [(purse, message.escrow)] := by
  cases destination with
  | object target =>
    simp only [Mail.send] at sent
    repeat' split at sent
    all_goals first
      | (cases sent; done)
      | (cases sent; exact ⟨_, rfl⟩)
  | slot name =>
    simp only [Mail.send] at sent
    repeat' split at sent
    all_goals first
      | (cases sent; done)
      | (cases sent; exact ⟨_, rfl⟩)

/-- **Posting sends credits exactly their escrows**: one credit per send, and in total the
escrow of every message posted (postage and continuation allowance). -/
theorem postMail_credits {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (postage : Minidregg.Compiler.ObjectiveInvocationClaim.Capacity) (refund : AccountId) (depth : Nat) :
    ∀ (outs : List Outgoing) (mail next : Mail config snapshot),
      postMail config snapshot postage refund depth mail outs = .ok next →
      next.credits.length = mail.credits.length + outs.length ∧
        (next.credits.map Prod.snd).sum = (mail.credits.map Prod.snd).sum +
          (outs.map fun out => (messageOf config postage refund depth out).escrow).sum
  | [], mail, next, ok => by
    simp only [postMail] at ok
    cases ok
    exact ⟨by simp, by simp⟩
  | out :: rest, mail, next, ok => by
    simp only [postMail] at ok
    split at ok
    · cases ok
    · rename_i mail' sent
      obtain ⟨purse, credits⟩ := Mail.send_credit sent
      obtain ⟨len, sum⟩ := postMail_credits postage refund depth rest mail' next ok
      refine ⟨?_, ?_⟩
      · rw [len, credits]; simp; omega
      · rw [sum, credits]; simp; omega

/-- **An invocation escrows every send at the public price of its declared postage
envelope plus the allowance it carries, within the allowance its signer declared**: one
credit per send, in total `workOf request.postage` per send plus the sends' allowances, which
`request.allowance` bounds. (A credit is the message's escrow, not a storage deposit.) -/
theorem Invocation.escrows_every_send {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : InvokeRequest}
    (invoked : Invocation config snapshot height request) :
    invoked.mail.credits.length = invoked.journal.outbox.length ∧
      (invoked.mail.credits.map Prod.snd).sum =
        invoked.journal.outbox.length * config.tariff.workOf request.postage + outboxAllowance invoked.journal.outbox ∧
      outboxAllowance invoked.journal.outbox ≤ request.allowance := by
  obtain ⟨len, sum⟩ := postMail_credits request.postage request.account 0 invoked.journal.outbox Mail.empty
    invoked.sent invoked.sentExact
  rw [(postControls_credits height _ _ _ invoked.mailExact).1]
  have each : ∀ (outs : List Outgoing),
      (outs.map fun out => (messageOf config request.postage request.account 0 out).escrow).sum =
        outs.length * config.tariff.workOf request.postage + outboxAllowance outs := by
    intro outs
    induction outs with
    | nil => simp [outboxAllowance]
    | cons out rest ih =>
      simp only [List.map_cons, List.sum_cons, ih, outboxAllowance, List.length_cons] at ⊢
      simp only [messageOf, Inbox.Message.escrow, outboxAllowance] at ⊢ ih
      rw [Nat.succ_mul]; omega
  refine ⟨?_, ?_, invoked.allowanceCovered⟩
  · rw [len]; simp [Mail.empty]
  · rw [sum, each]; simp [Mail.empty]

/-- **An inbox the mail holds stays within `Inbox.bound`** when the inbox the turn read
was (a fresh inbox, read as nothing, always is). -/
theorem Mail.inboxes_bounded {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) :
    ∀ held ∈ mail.inboxes,
      (held.read.getD (Inbox.Inbox.empty held.sender held.target)).messages.length ≤ Inbox.bound →
        held.now.messages.length ≤ Inbox.bound :=
  fun held _ within => held.lawful.keeps.2.2.2 within

/-- **A pop frees the message**: the inbox the delivery posts holds exactly one message fewer. -/
theorem MessageDelivery.pop_frees_message {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) :
    delivered.remaining.messages.length + 1 = delivered.inbox.messages.length := by
  obtain ⟨rest, front, after, _, _⟩ := delivered.pops
  simp [front, after]

theorem MessageDelivery.remaining_within_bound {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request)
    (within : delivered.inbox.messages.length ≤ Inbox.bound) :
    delivered.remaining.messages.length ≤ Inbox.bound := by
  have := delivered.pop_frees_message
  omega

theorem forward_none {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) (queued : List Inbox.Message) :
    forward (rootBytes := rootBytes) none mail queued = (mail, queued) := by
  induction queued generalizing mail with
  | nil => rfl
  | cons message rest ih => simp [forward, ih]

/-- A failed delivery forwards nothing: its mail is the popped inbox alone and every
queued send is refunded. -/
theorem MessageDelivery.failed_mail {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) {reason : String}
    (failed : delivered.outcome = .failed reason) :
    delivered.mail = delivered.seed ∧ delivered.refunds = delivered.slot.queued := by
  have continued := delivered.continued
  rw [failed] at continued
  have forwarded := delivered.forwarded
  rw [failed, show (Outcome.failed reason).reference = none from rfl, forward_none,
    (continueMessage_failed continued).1] at forwarded
  simp only [Prod.mk.injEq] at forwarded
  exact ⟨forwarded.1.symm, forwarded.2.symm⟩

/-- **A failed delivery leaves behind exactly three posts**: the popped, shortened inbox,
its reply slot (decided `broken`, or retired when its sender had stopped waiting:
`replyPost`), and the Book. No cell is opened, no state cell written. -/
theorem MessageDelivery.failed_delivery_posts {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) {reason : String}
    (failed : delivered.outcome = .failed reason) :
    delivered.posts =
      [postAt snapshot (Inbox.cell config.domain request.sender request.target) (inboxImage delivered.remaining),
        replyPost config snapshot delivered.slot delivered.decided, delivered.posted.write config snapshot] := by
  obtain ⟨sameMail, _⟩ := delivered.failed_mail failed
  have noPosts : delivered.outcome.posts config snapshot = [] := by rw [failed]; rfl
  obtain ⟨inboxes, slots, _, _, closed, _⟩ := delivered.seedExact
  have seedPosts : delivered.seed.posts =
      [postAt snapshot (Inbox.cell config.domain request.sender request.target) (inboxImage delivered.remaining)] := by
    cases hl : delivered.seed.inboxes with
    | nil => rw [hl] at inboxes; cases inboxes
    | cons first rest =>
      rw [hl] at inboxes
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, List.map_eq_nil_iff] at inboxes
      obtain ⟨⟨hs, ht, hn⟩, restNil⟩ := inboxes
      unfold Mail.posts
      rw [hl, slots, restNil, closed]
      simp [HeldInbox.cell, hs, ht, hn]
  rw [delivered.postsExact, noPosts, sameMail, seedPosts]
  simp

/-! ## Escrow conservation (GPT-6 row F): postage + allowance in = delivered spend + refunds

A message's ESCROW (`Inbox.Message.escrow`: its postage and its continuation allowance) is
credited into its queue's purse by the turn that sends it, and leaves that purse by exactly
one of three exits: its delivery (the postage to the collector, the onward sends' escrows to
their queues, the unspent allowance back to its payer; the sends pipelined on its slot
forwarded or refunded), or a cancel (all of it, with the pipelined sends', back to the
payer), and a failed delivery is the first exit with nothing spent. `escrow_conservation`
states all three over the REAL ledger: the amounts of the postings of the batch the turn
commits (`Operation.posting`), plus whatever lands back in the same purse (a payment the
batch drops because it would move escrow from a purse to itself, e.g. an onward send that
re-queues on the inbox it was popped from). -/

/-- The amounts the postings of `ops` move. -/
def postedAmount (ops : List Operation) : Nat := (ops.map fun op => op.posting.amount).sum

/-- What of `flows` (payee, amount) lands back in `purse` itself. -/
def retained (purse : AccountId) (flows : List (AccountId × Nat)) : Nat :=
  ((flows.filter fun flow => decide (flow.1 = purse)).map Prod.snd).sum

theorem postedAmount_append (a b : List Operation) : postedAmount (a ++ b) = postedAmount a + postedAmount b := by
  simp [postedAmount]

theorem retained_append (purse : AccountId) (a b : List (AccountId × Nat)) :
    retained purse (a ++ b) = retained purse a + retained purse b := by
  simp [retained, List.filter_append]

theorem payOut_posted (config : Config) (purse payee : AccountId) (amount : Nat) :
    postedAmount (payOut config purse payee amount) + retained purse [(payee, amount)] = amount := by
  unfold payOut retained postedAmount
  by_cases zero : amount = 0
  · subst zero; by_cases same : payee = purse <;> simp [same]
  · by_cases same : payee = purse
    · simp [same]
    · simp [zero, same, Operation.posting]

theorem creditTransfers_posted (config : Config) (purse : AccountId) :
    ∀ credits : List (AccountId × Nat),
      postedAmount (creditTransfers config purse credits) + retained purse credits = (credits.map Prod.snd).sum
  | [] => by simp [creditTransfers, postedAmount, retained]
  | (payee, amount) :: rest => by
    have ih := creditTransfers_posted config purse rest
    have one := payOut_posted config purse payee amount
    have split : creditTransfers config purse ((payee, amount) :: rest) =
        payOut config purse payee amount ++ creditTransfers config purse rest := by
      unfold payOut
      simp only [creditTransfers, List.filterMap_cons]
      split <;> simp_all
    rw [split, postedAmount_append, show (payee, amount) :: rest = [(payee, amount)] ++ rest from rfl,
      retained_append]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at ih one ⊢
    omega

theorem refunds_posted (config : Config) (purse : AccountId) :
    ∀ refunds : List Inbox.Message,
      postedAmount (refunds.flatMap fun refunded => payOut config purse refunded.refund refunded.escrow) +
        retained purse (refunds.map fun refunded => (refunded.refund, refunded.escrow)) =
      (refunds.map Inbox.Message.escrow).sum
  | [] => by simp [postedAmount, retained]
  | refunded :: rest => by
    have ih := refunds_posted config purse rest
    have one := payOut_posted config purse refunded.refund refunded.escrow
    rw [List.flatMap_cons, postedAmount_append, List.map_cons,
      show (refunded.refund, refunded.escrow) :: rest.map (fun r => (r.refund, r.escrow)) =
        [(refunded.refund, refunded.escrow)] ++ rest.map (fun r => (r.refund, r.escrow)) from rfl, retained_append]
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- **Forwarding conserves the pipelined escrow**: every send queued on the slot is either
credited, its whole escrow, to the queue it is forwarded into, or refunded. -/
theorem forward_escrow {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (reference : Option Nat) :
    ∀ (queued : List Inbox.Message) (mail next : Mail config snapshot) (refunds : List Inbox.Message),
      forward reference mail queued = (next, refunds) →
      (next.credits.map Prod.snd).sum + (refunds.map Inbox.Message.escrow).sum =
        (mail.credits.map Prod.snd).sum + (queued.map Inbox.Message.escrow).sum
  | [], mail, next, refunds, ok => by
    simp only [forward, Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    simp
  | message :: rest, mail, next, refunds, ok => by
    simp only [forward] at ok
    split at ok
    · rename_i mail' hmatch
      cases reference with
      | none => simp at hmatch
      | some target =>
        have sent : mail.send message (.object target) = .ok mail' := by simpa using hmatch
        obtain ⟨purse, credits⟩ := Mail.send_credit sent
        have ih := forward_escrow (some target) rest mail' next refunds ok
        rw [credits] at ih
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at ih ⊢
        omega
    · cases inner : forward reference mail rest with
      | mk next' refunds' =>
        rw [inner] at ok
        simp only [Prod.mk.injEq] at ok
        obtain ⟨rfl, rfl⟩ := ok
        have ih := forward_escrow reference rest mail next' refunds' inner
        simp only [List.map_cons, List.sum_cons] at ih ⊢
        omega

/-- **A continuation credits exactly what it spends of the allowance**, and spends at most it. -/
theorem continueMessage_credits {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {message : Inbox.Message} {seed mail : Mail config snapshot} {run outcome : Outcome} {spent : Nat}
    (continued : continueMessage config snapshot message seed run = (outcome, mail, spent)) :
    (mail.credits.map Prod.snd).sum = (seed.credits.map Prod.snd).sum + spent ∧ spent ≤ message.allowance ∧
      mail.credits.length ≤ seed.credits.length + Inbox.fanOut ∧
      (mail.credits.length ≠ seed.credits.length → message.depth < Inbox.continuationDepth) := by
  rcases continueMessage_cases continued with ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ |
    ⟨_, journal, _, _, _, shallow, narrow, rfl, within, posted⟩
  · exact ⟨by simp, Nat.zero_le _, by omega, fun same => absurd rfl same⟩
  · exact ⟨by simp, Nat.zero_le _, by omega, fun same => absurd rfl same⟩
  · obtain ⟨len, sum⟩ := postMail_credits _ _ _ _ _ _ posted
    exact ⟨by rw [sum]; rfl, within, by omega, fun _ => shallow⟩

/-- The flows of a delivery out of its purse, payee and amount: the onward sends' and the
forwards' credits, the refunded forwards, and the unspent allowance (the fee aside). -/
def MessageDelivery.flows {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : MessageRequest} (delivered : MessageDelivery config snapshot height request) :
    List (AccountId × Nat) :=
  delivered.mail.credits ++ delivered.refunds.map (fun refunded => (refunded.refund, refunded.escrow)) ++
    [(delivered.message.refund, delivered.message.allowance - delivered.spent)]

/-- **The delivery leg, over its real postings**: the amounts its batch posts out of the
purse, plus what of its flows lands back in that purse, are EXACTLY the popped message's
escrow (postage + allowance) plus the escrow of every send pipelined on its slot; and the
onward sends spent at most the allowance. -/
theorem MessageDelivery.escrow_conserves {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) :
    postedAmount delivered.posted.batch.operations +
        retained (Inbox.cell config.domain request.sender request.target).value delivered.flows =
      delivered.message.escrow + (delivered.slot.queued.map Inbox.Message.escrow).sum ∧
    delivered.spent ≤ delivered.message.allowance := by
  rw [delivered.batchExact]
  simp only [deliveryBatch, MessageDelivery.flows, postedAmount_append, retained_append]
  set purse := (Inbox.cell config.domain request.sender request.target).value
  obtain ⟨sentSum, within, _, _⟩ := continueMessage_credits delivered.continued
  have seedNil : delivered.seed.credits = [] := delivered.seedExact.2.2.1
  rw [seedNil] at sentSum
  have fwd := forward_escrow delivered.outcome.reference delivered.slot.queued delivered.sent delivered.mail
    delivered.refunds delivered.forwarded
  have credits := creditTransfers_posted config purse delivered.mail.credits
  have refunded := refunds_posted config purse delivered.refunds
  have remainder := payOut_posted config purse delivered.message.refund (delivered.message.allowance - delivered.spent)
  have fee : postedAmount (if delivered.message.postage = 0 then []
      else [.fee purse config.collector config.asset delivered.message.postage]) = delivered.message.postage := by
    by_cases zero : delivered.message.postage = 0
    · simp [zero, postedAmount]
    · simp [zero, postedAmount, Operation.posting]
  refine ⟨?_, within⟩
  simp only [List.map_nil, List.sum_nil] at sentSum
  have escrow : delivered.message.escrow = delivered.message.postage + delivered.message.allowance := rfl
  omega

/-- **The bounds bound the work, per delivery**: a delivery queues at most `Inbox.fanOut`
onward messages, only from a message below `Inbox.continuationDepth`, each one hop deeper
(`onwardOf`). So the messages a chain rooted at one message posts are bounded generation by
generation (`chain_total`). -/
theorem MessageDelivery.onward_bounded {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) :
    delivered.sent.credits.length ≤ Inbox.fanOut ∧
      (delivered.sent.credits ≠ [] → delivered.message.depth < Inbox.continuationDepth) := by
  obtain ⟨_, _, wide, deep⟩ := continueMessage_credits delivered.continued
  have seedNil : delivered.seed.credits = [] := delivered.seedExact.2.2.1
  rw [seedNil] at wide deep
  refine ⟨by simpa using wide, fun some => deep (by simpa using some)⟩

theorem onwardOf_depth (config : Config) (message : Inbox.Message) (out : Outgoing) :
    (onwardOf config message out).depth = message.depth + 1 := rfl

/-- **Generation counting**: if a chain has at most one message at relative depth 0, each
generation at most `fanOut` times the one before, and none past `depth`, then it holds at
most `Σ_{k ≤ depth} fanOut^k` messages. With `Inbox.fanOut` = 4 and the relative depth
`Inbox.continuationDepth` = 3 below an invocation's send: at most 1 + 4 + 16 + 64 = 85. -/
theorem chain_total (fanOut depth : Nat) (count : Nat → Nat) (root : count 0 ≤ 1)
    (fans : ∀ k, count (k + 1) ≤ fanOut * count k) :
    (∀ n, count n ≤ fanOut ^ n) ∧
      ((List.range (depth + 1)).map count).sum ≤ ((List.range (depth + 1)).map (fanOut ^ ·)).sum := by
  have each : ∀ n, count n ≤ fanOut ^ n := by
    intro n
    induction n with
    | zero => simpa using root
    | succ n ih =>
      calc count (n + 1) ≤ fanOut * count n := fans n
        _ ≤ fanOut * fanOut ^ n := Nat.mul_le_mul_left _ ih
        _ = fanOut ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  refine ⟨each, ?_⟩
  clear root fans
  induction depth with
  | zero => simpa using each 0
  | succ d ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := each (d + 1)
    omega

/-- **`escrow_conservation`: ONE statement, three exits, over the real ledger.**
* A SEND credits its queue's purse with exactly the message's escrow (postage + allowance).
* A DELIVERY (succeeded, failed, or refused at its continuation) posts out of the purse,
  plus what lands back in it, exactly the popped escrow plus the escrow pipelined on its
  slot: postage to the collector, onward escrows (at most the allowance), forwards, refunds
  and the unspent allowance.
* A CANCEL either refunds nothing (the message was delivered first, or its slot is gone) or
  its refund transfers post, plus what lands back in the purse, exactly the withdrawn
  message's escrow plus the escrow of every send pipelined on its slot. -/
theorem escrow_conservation {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} :
    (∀ (mail next : Mail config snapshot) (message : Inbox.Message) (destination : Destination),
      mail.send message destination = .ok next →
      ∃ purse, next.credits = mail.credits ++ [(purse, message.escrow)]) ∧
    (∀ (height : Nat) (request : MessageRequest) (delivered : MessageDelivery config snapshot height request),
      postedAmount delivered.posted.batch.operations +
          retained (Inbox.cell config.domain request.sender request.target).value delivered.flows =
        delivered.message.escrow + (delivered.slot.queued.map Inbox.Message.escrow).sum ∧
      delivered.spent ≤ delivered.message.allowance) ∧
    (∀ (mail next : Mail config snapshot) (height : Nat) (control : Control),
      mail.control height control = .ok next → control.kind = .cancel →
      next.refunds = mail.refunds ∨
      ∃ (purse : AccountId) (message : Inbox.Message) (queued : List Inbox.Message),
        next.refunds = mail.refunds ++ cancelRefunds purse message queued ∧
        postedAmount (refundTransfers config (cancelRefunds purse message queued)) +
            retained purse ((cancelRefunds purse message queued).map fun refund => (refund.payer, refund.amount)) =
          message.escrow + (queued.map Inbox.Message.escrow).sum) := by
  refine ⟨fun _ _ _ _ sent => Mail.send_credit sent, fun _ _ delivered => delivered.escrow_conserves, ?_⟩
  intro mail next height control ok cancel
  rcases Mail.control_cancel_refunds ok cancel with same | ⟨held, _, message, _, _, _, _, _, _, refunds, sum, _⟩
  · exact .inl same
  · refine .inr ⟨held.now.activity.value, message, held.now.queued, refunds, ?_⟩
    rw [← sum]
    have general : ∀ (rs : List Refund), (∀ r ∈ rs, r.purse = held.now.activity.value) →
        postedAmount (refundTransfers config rs) +
          retained held.now.activity.value (rs.map fun refund => (refund.payer, refund.amount)) =
        (rs.map Refund.amount).sum := by
      intro rs fromPurse
      induction rs with
      | nil => simp [refundTransfers, postedAmount, retained]
      | cons r rest ih =>
        have ih := ih (fun r' member => fromPurse r' (List.mem_cons_of_mem _ member))
        have rp := fromPurse r (List.mem_cons_self ..)
        have one := payOut_posted config held.now.activity.value r.payer r.amount
        have split : refundTransfers config (r :: rest) =
            payOut config held.now.activity.value r.payer r.amount ++ refundTransfers config rest := by
          unfold payOut
          simp only [refundTransfers, List.filterMap_cons, rp]
          by_cases zero : r.amount = 0
          · simp [zero]
          · by_cases self : r.payer = held.now.activity.value
            · simp [zero, self]
            · simp [zero, self, Ne.symm self]
        rw [split, postedAmount_append, List.map_cons,
          show (r.payer, r.amount) :: rest.map (fun refund => (refund.payer, refund.amount)) =
            [(r.payer, r.amount)] ++ rest.map (fun refund => (refund.payer, refund.amount)) from rfl,
          retained_append]
        simp only [List.map_cons, List.sum_cons] at ih ⊢
        omega
    exact general _ (cancelRefunds_escrow held.now.activity.value message held.now.queued).2

#assert_axioms postedAmount_append
#assert_axioms retained_append
#assert_axioms payOut_posted
#assert_axioms creditTransfers_posted
#assert_axioms refunds_posted
#assert_axioms forward_escrow
#assert_axioms continueMessage_credits
#assert_axioms MessageDelivery.escrow_conserves
#assert_axioms MessageDelivery.onward_bounded
#assert_axioms chain_total
#assert_axioms escrow_conservation

/-! ### Every live cell a send or a delivery writes names a payer -/

open Minidregg.Kernel.ObjectRecord (ObjectRecord)

theorem option_isSome_of_eq {α : Type} {o : Option α} {a : α} (h : o = some a) : o.isSome = true := by
  subst h; rfl

theorem HeldInbox.cell_eq {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {a b : HeldInbox config snapshot} (sender : a.sender = b.sender) (target : a.target = b.target) :
    a.cell = b.cell := by
  unfold HeldInbox.cell
  rw [sender, target]

/-- The payer of an inbox image: its sender object's. -/
theorem payer_inbox_image (config : Config) (bytesAt : CellId → Bytes) (inbox : Inbox.Inbox)
    (record : ObjectRecord) (held : objectAt config bytesAt ⟨inbox.sender⟩ = some record) :
    payerOfBytes config bytesAt (inboxImage inbox) = some record.payer := by
  simp [payerOfBytes, inboxImage, payloadOf_image, payerRoute, routePayer, Inbox.roundTrip, held]

/-- The payer of a slot image whose activity cell holds an inbox (or a record): the
sender object's. -/
theorem payer_slot_image_inbox (config : Config) (bytesAt : CellId → Bytes) (slot : AnswerSlot.Slot)
    (inbox : Inbox.Inbox) (record : ObjectRecord) (held : inboxAt bytesAt slot.activity = some inbox)
    (owner : objectAt config bytesAt ⟨inbox.sender⟩ = some record) :
    (payerOfBytes config bytesAt (image .slot (AnswerSlot.key slot.name) (AnswerSlot.encode slot))).isSome = true := by
  cases hr : recordAt bytesAt slot.activity <;>
    simp [payerOfBytes, payloadOf_image, payerRoute, routePayer, AnswerSlot.roundTrip, hr, held, owner]

theorem afterPosts_of_nodup {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) :
    ∀ (posts : List Post), (posts.map Post.cell).Nodup → ∀ post ∈ posts,
      afterPosts snapshot posts post.cell = post.bytes
  | [], _, post, member => by cases member
  | first :: rest, nodup, post, member => by
    rw [List.map_cons, List.nodup_cons] at nodup
    by_cases same : first.cell = post.cell
    · have isFirst : post = first := by
        rcases List.mem_cons.mp member with h | inRest
        · exact h
        · exact absurd (by rw [same]; exact List.mem_map.mpr ⟨post, inRest, rfl⟩) nodup.1
      subst isFirst
      exact afterPosts_first snapshot post rest
    · have tail := afterPosts_of_nodup snapshot rest nodup.2 post (by
        rcases List.mem_cons.mp member with h | inRest
        · exact absurd (by rw [h]) same
        · exact inRest)
      have skip : afterPosts snapshot (first :: rest) post.cell = afterPosts snapshot rest post.cell := by
        simp [afterPosts, List.find?_cons, same]
      rw [skip, tail]

theorem objectAt_afterPosts {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (posts : List Post) (object : CellId)
    (unwritten : ∀ post ∈ posts, post.cell ≠ objectCell config.domain object) :
    objectAt config (afterPosts snapshot posts) object = objectAt config snapshot.canonicalBytes object := by
  unfold objectAt
  rw [afterPosts_unwritten snapshot posts _ unwritten]

theorem inboxAt_posted {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (posts : List Post)
    (nodup : (posts.map Post.cell).Nodup) (post : Post) (member : post ∈ posts) (inbox : Inbox.Inbox)
    (isImage : post.bytes = inboxImage inbox) :
    inboxAt (afterPosts snapshot posts) post.cell = some inbox := by
  unfold inboxAt
  rw [afterPosts_of_nodup snapshot posts nodup post member, isImage]
  simp [inboxImage, bodyOf_image, Inbox.roundTrip]

/-- **Anchored**: every reply slot a mail opens (one it did not read), and every slot a
cancel decides, answers to an inbox cell the mail holds. -/
def Mail.Anchored {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) : Prop :=
  (∀ slot ∈ mail.slots, slot.read = none → ∃ held ∈ mail.inboxes, held.cell = slot.now.activity) ∧
    ∀ closed ∈ mail.closed, ∀ slot, closed.decided = some slot → ∃ held ∈ mail.inboxes, held.cell = slot.activity

theorem Mail.empty_anchored {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} :
    Mail.Anchored (Mail.empty : Mail config snapshot) := by
  constructor <;> intro _ member <;> cases member

theorem holdInbox_cover {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail : Mail config snapshot} {sender target : Nat} {held : HeldInbox config snapshot}
    {others : List (HeldInbox config snapshot)}
    (ok : holdInbox config snapshot mail sender target = .ok (held, others)) :
    held.sender = sender ∧ held.target = target ∧
      ∀ other ∈ mail.inboxes, other ∈ others ∨ (other.sender = sender ∧ other.target = target) := by
  unfold holdInbox at ok
  split at ok
  · rename_i found hit
    cases ok
    have hits := List.find?_some hit
    simp only [Bool.and_eq_true, beq_iff_eq] at hits
    refine ⟨hits.1, hits.2, fun other member => ?_⟩
    by_cases same : (other.sender == sender && other.target == target) = true
    · simp only [Bool.and_eq_true, beq_iff_eq] at same
      exact .inr same
    · exact .inl (List.mem_filter.mpr ⟨member, by
      cases h : (other.sender == sender && other.target == target) with
      | true => exact absurd h same
      | false => simp [h]⟩)
  · split at ok
    · cases ok
    · split at ok
      · split at ok
        · cases ok
          exact ⟨rfl, rfl, fun other member => .inl member⟩
        · cases ok
      · cases ok

theorem holdSlot_cover {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail : Mail config snapshot} {name : Digest} {held : HeldSlot config snapshot}
    {others : List (HeldSlot config snapshot)}
    (ok : holdSlot config snapshot mail name = .ok (held, others)) :
    (∀ other ∈ others, other ∈ mail.slots) ∧ (held ∈ mail.slots ∨ held.read ≠ none) := by
  unfold holdSlot at ok
  split at ok
  · rename_i found hit
    cases ok
    exact ⟨fun other member => (List.mem_filter.mp member).1, .inl (List.mem_of_find?_eq_some hit)⟩
  · split at ok
    · cases ok
    · repeat' split at ok
      all_goals first
        | (cases ok; done)
        | (cases ok; exact ⟨fun other member => member, Or.inr (by simp)⟩)

theorem openSlot_fresh {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail : Mail config snapshot} {name : Digest} {inbox : CellId} {slot : HeldSlot config snapshot}
    (ok : openSlot config snapshot mail name inbox = .ok slot) :
    slot.read = none ∧ slot.now.activity = inbox := by
  simp only [openSlot] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; done)
    | (cases ok; exact ⟨rfl, rfl⟩)

/-- Sending keeps every inbox cell the mail holds. -/
theorem Mail.send_inboxes_persist {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail next : Mail config snapshot} {message : Inbox.Message} {destination : Destination}
    (sent : mail.send message destination = .ok next) :
    ∀ held ∈ mail.inboxes, ∃ held' ∈ next.inboxes, held'.cell = held.cell := by
  cases destination with
  | object target =>
    simp only [Mail.send] at sent
    repeat' split at sent
    all_goals try (cases sent; done)
    have holdOk := ‹holdInbox config snapshot mail message.sender target = .ok (_, _)›
    obtain ⟨hs, ht, cover⟩ := holdInbox_cover holdOk
    cases sent
    intro held member
    rcases cover held member with inOthers | same
    · exact ⟨held, List.mem_append.mpr (.inl inOthers), rfl⟩
    · exact ⟨_, List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl)),
        HeldInbox.cell_eq (hs.trans same.1.symm) (ht.trans same.2.symm)⟩
  | slot name =>
    simp only [Mail.send] at sent
    repeat' split at sent
    all_goals try (cases sent; done)
    cases sent
    intro held member
    exact ⟨held, member, rfl⟩

/-- **Sending keeps a mail anchored.** -/
theorem Mail.send_anchored {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail next : Mail config snapshot} {message : Inbox.Message} {destination : Destination}
    (anchored : Mail.Anchored mail) (sent : mail.send message destination = .ok next) :
    Mail.Anchored next := by
  have persist := Mail.send_inboxes_persist sent
  refine ⟨?_, ?_⟩
  swap
  · intro closed member slot decided
    rw [(Mail.send_keeps sent).1] at member
    obtain ⟨held, hm, hc⟩ := anchored.2 closed member slot decided
    obtain ⟨held', hm', hc'⟩ := persist held hm
    exact ⟨held', hm', hc'.trans hc⟩
  cases destination with
  | object target =>
    simp only [Mail.send] at sent
    repeat' split at sent
    all_goals try (cases sent; done)
    have openOk := ‹openSlot config snapshot mail message.id _ = .ok _›
    obtain ⟨_, activity⟩ := openSlot_fresh openOk
    cases sent
    intro slot member opened
    rcases List.mem_append.mp member with old | fresh
    · obtain ⟨held, hm, hc⟩ := anchored.1 slot old opened
      obtain ⟨held', hm', hc'⟩ := persist held hm
      exact ⟨held', hm', hc'.trans hc⟩
    · have same := List.mem_singleton.mp fresh
      subst same
      rw [activity]
      exact ⟨_, List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl)), rfl⟩
  | slot name =>
    simp only [Mail.send] at sent
    repeat' split at sent
    all_goals try (cases sent; done)
    have holdOk := ‹holdSlot config snapshot mail name = .ok (_, _)›
    obtain ⟨others, heldCover⟩ := holdSlot_cover holdOk
    cases sent
    intro slot member opened
    rcases List.mem_append.mp member with old | updated
    · exact anchored.1 slot (others slot old) opened
    · have same := List.mem_singleton.mp updated
      subst same
      rcases heldCover with inMail | read
      · have a := anchored.1 _ inMail opened
        exact a
      · exact absurd opened read

theorem postMail_anchored {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (postage : Minidregg.Compiler.ObjectiveInvocationClaim.Capacity) (refund : AccountId) (depth : Nat) :
    ∀ (outs : List Outgoing) (mail next : Mail config snapshot),
      postMail config snapshot postage refund depth mail outs = .ok next → Mail.Anchored mail → Mail.Anchored next
  | [], mail, next, ok, anchored => by
    simp only [postMail] at ok
    cases ok
    exact anchored
  | out :: rest, mail, next, ok, anchored => by
    simp only [postMail] at ok
    split at ok
    · cases ok
    · rename_i mail' sent
      exact postMail_anchored postage refund depth rest mail' next ok (Mail.send_anchored anchored sent)

theorem postMail_inboxes_persist {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (postage : Minidregg.Compiler.ObjectiveInvocationClaim.Capacity) (refund : AccountId) (depth : Nat) :
    ∀ (outs : List Outgoing) (mail next : Mail config snapshot),
      postMail config snapshot postage refund depth mail outs = .ok next →
      ∀ held ∈ mail.inboxes, ∃ held' ∈ next.inboxes, held'.cell = held.cell
  | [], mail, next, ok, held, member => by
    simp only [postMail] at ok; cases ok; exact ⟨held, member, rfl⟩
  | out :: rest, mail, next, ok, held, member => by
    simp only [postMail] at ok
    split at ok
    · cases ok
    · rename_i mail' sent
      obtain ⟨h1, m1, c1⟩ := Mail.send_inboxes_persist sent held member
      obtain ⟨h2, m2, c2⟩ := postMail_inboxes_persist postage refund depth rest mail' next ok h1 m1
      exact ⟨h2, m2, c2.trans c1⟩

/-- The mail a continuation leaves is anchored and keeps every inbox of the seed. -/
theorem continueMessage_mail {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {message : Inbox.Message} {seed mail : Mail config snapshot} {run outcome : Outcome} {spent : Nat}
    (continued : continueMessage config snapshot message seed run = (outcome, mail, spent))
    (anchored : Mail.Anchored seed) :
    Mail.Anchored mail ∧ (∀ held ∈ seed.inboxes, ∃ held' ∈ mail.inboxes, held'.cell = held.cell) ∧
      mail.closed = seed.closed ∧ mail.refunds = seed.refunds := by
  rcases continueMessage_cases continued with ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨_, _, _, _, _, _, _, _, _, posted⟩
  · exact ⟨anchored, fun held member => ⟨held, member, rfl⟩, rfl, rfl⟩
  · exact ⟨anchored, fun held member => ⟨held, member, rfl⟩, rfl, rfl⟩
  · obtain ⟨c, r⟩ := postMail_keeps _ _ _ _ _ _ posted
    exact ⟨postMail_anchored _ _ _ _ _ _ posted anchored, postMail_inboxes_persist _ _ _ _ _ _ posted, c, r⟩

theorem forward_anchored {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} :
    ∀ (reference : Option Nat) (queued : List Inbox.Message) (mail : Mail config snapshot),
      Mail.Anchored mail → Mail.Anchored (forward reference mail queued).1
  | reference, [], mail, anchored => anchored
  | reference, message :: rest, mail, anchored => by
    simp only [forward]
    split
    · rename_i next hmatch
      cases reference with
      | none => simp at hmatch
      | some target =>
        have sent : mail.send message (.object target) = .ok next := by simpa using hmatch
        exact forward_anchored (some target) rest next (Mail.send_anchored anchored sent)
    · exact forward_anchored reference rest mail anchored

theorem forward_inboxes_persist {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} :
    ∀ (reference : Option Nat) (queued : List Inbox.Message) (mail : Mail config snapshot),
      ∀ held ∈ mail.inboxes, ∃ held' ∈ (forward reference mail queued).1.inboxes, held'.cell = held.cell
  | reference, [], mail, held, member => ⟨held, member, rfl⟩
  | reference, message :: rest, mail, held, member => by
    simp only [forward]
    split
    · rename_i next hmatch
      cases reference with
      | none => simp at hmatch
      | some target =>
        have sent : mail.send message (.object target) = .ok next := by simpa using hmatch
        obtain ⟨h1, m1, c1⟩ := Mail.send_inboxes_persist sent held member
        obtain ⟨h2, m2, c2⟩ := forward_inboxes_persist (some target) rest next h1 m1
        exact ⟨h2, m2, c2.trans c1⟩
    · exact forward_inboxes_persist reference rest mail held member

theorem controlSlot_held_cover {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail : Mail config snapshot} {name : Digest} {held : HeldSlot config snapshot}
    {others : List (HeldSlot config snapshot)}
    (ok : controlSlot config snapshot mail name = .ok (.held held others)) :
    (∀ other ∈ others, other ∈ mail.slots) ∧ (held ∈ mail.slots ∨ held.read ≠ none) := by
  unfold controlSlot at ok
  split at ok
  · cases ok
  · split at ok
    · rename_i found hit
      split at ok
      · cases ok
      · cases ok
        exact ⟨fun other member => (List.mem_filter.mp member).1, .inl (List.mem_of_find?_eq_some hit)⟩
    · repeat' split at ok
      all_goals first
        | (cases ok; done)
        | (cases ok; exact ⟨fun other member => member, Or.inr (by simp)⟩)

/-- A control keeps every inbox cell the mail holds. -/
theorem Mail.control_inboxes_persist {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail next : Mail config snapshot} {height : Nat} {control : Control}
    (ok : mail.control height control = .ok next) :
    ∀ held ∈ mail.inboxes, ∃ held' ∈ next.inboxes, held'.cell = held.cell := by
  rcases Mail.control_cases ok with same | ⟨_, _, _, _, _, _, _, _, _, rfl⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ |
    ⟨_, held, others, inbox, updated, inboxes, message, closing, found, heldOk, _, _, _, _, us, ut, _, _, _, rfl⟩
  · rw [same]; exact fun held member => ⟨held, member, rfl⟩
  · exact fun held member => ⟨held, member, rfl⟩
  · exact fun held member => ⟨held, member, rfl⟩
  · obtain ⟨_, hold⟩ := controlInbox_spec heldOk
    obtain ⟨_, _, cover⟩ := holdInbox_cover hold
    intro other member
    rcases cover other member with kept | same
    · exact ⟨other, List.mem_append.mpr (.inl kept), rfl⟩
    · exact ⟨updated, List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl)),
        HeldInbox.cell_eq (us.trans same.1.symm) (ut.trans same.2.symm)⟩

/-- **A control keeps a mail anchored**: the slot a cancel decides answers to the inbox it
withdrew the message from, which the mail now holds. -/
theorem Mail.control_anchored {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail next : Mail config snapshot} {height : Nat} {control : Control}
    (anchored : Mail.Anchored mail) (ok : mail.control height control = .ok next) : Mail.Anchored next := by
  have persist := Mail.control_inboxes_persist ok
  have lift : ∀ (slot : AnswerSlot.Slot), (∃ held ∈ mail.inboxes, held.cell = slot.activity) →
      ∃ held ∈ next.inboxes, held.cell = slot.activity := by
    intro slot ⟨held, hm, hc⟩
    obtain ⟨held', hm', hc'⟩ := persist held hm
    exact ⟨held', hm', hc'.trans hc⟩
  rcases Mail.control_cases ok with same | ⟨_, _, closing, _, _, _, none_, _, _, rfl⟩ |
    ⟨_, held, updated, others, _, _, found, _, _, read, now, rfl⟩ |
    ⟨_, held, others, inbox, updated, inboxes, message, closing, found, heldOk, _, cell, _, _, us, ut, _, decided, _,
      rfl⟩
  · rw [same]; exact anchored
  · refine ⟨anchored.1, ?_⟩
    intro closed member slot isSome
    rcases List.mem_append.mp member with old | fresh
    · exact anchored.2 closed old slot isSome
    · rw [List.mem_singleton.mp fresh, none_] at isSome; cases isSome
  · obtain ⟨others', heldCover⟩ := controlSlot_held_cover found
    refine ⟨?_, anchored.2⟩
    intro slot member opened
    rcases List.mem_append.mp member with old | fresh
    · exact anchored.1 slot (others' slot old) opened
    · rw [List.mem_singleton.mp fresh] at opened ⊢
      rw [read] at opened
      rw [now]
      rcases heldCover with inMail | wasRead
      · exact anchored.1 held inMail opened
      · exact absurd opened wasRead
  · obtain ⟨others', _⟩ := controlSlot_held_cover found
    refine ⟨fun slot member opened => lift slot.now (anchored.1 slot (others' slot member) opened), ?_⟩
    intro closed member slot isSome
    rcases List.mem_append.mp member with old | fresh
    · exact lift slot (anchored.2 closed old slot isSome)
    · rw [List.mem_singleton.mp fresh] at isSome
      obtain ⟨_, rfl⟩ := decided slot isSome
      refine ⟨updated, List.mem_append.mpr (.inr (List.mem_singleton.mpr rfl)), ?_⟩
      rw [← cell]
      exact HeldInbox.cell_eq us ut

theorem postControls_anchored {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (height : Nat) :
    ∀ (controls : List Control) (mail next : Mail config snapshot),
      postControls config snapshot height mail controls = .ok next → Mail.Anchored mail → Mail.Anchored next
  | [], mail, next, ok, anchored => by simp only [postControls] at ok; cases ok; exact anchored
  | control :: rest, mail, next, ok, anchored => by
    simp only [postControls] at ok
    split at ok
    · cases ok
    · rename_i mail' controlled
      exact postControls_anchored height rest mail' next ok (Mail.control_anchored anchored controlled)

/-- **Controls that cancel nothing write no inbox and decide no slot**: with no `cancel`
among them, the inboxes of the mail are untouched and every slot they close is retired. -/
theorem postControls_stops {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (height : Nat) :
    ∀ (controls : List Control) (mail next : Mail config snapshot),
      postControls config snapshot height mail controls = .ok next →
      (∀ control ∈ controls, control.kind ≠ .cancel) →
      (∀ closed ∈ mail.closed, closed.decided = none) →
      next.inboxes = mail.inboxes ∧ ∀ closed ∈ next.closed, closed.decided = none
  | [], mail, next, ok, _, retired => by
    simp only [postControls] at ok; cases ok; exact ⟨rfl, retired⟩
  | control :: rest, mail, next, ok, stops, retired => by
    simp only [postControls] at ok
    split at ok
    · cases ok
    · rename_i mail' controlled
      have one : mail'.inboxes = mail.inboxes ∧ ∀ closed ∈ mail'.closed, closed.decided = none := by
        rcases Mail.control_cases controlled with same | ⟨_, _, closing, _, _, _, none_, _, _, rfl⟩ |
          ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ | ⟨cancel, _⟩
        · rw [same]; exact ⟨rfl, retired⟩
        · refine ⟨rfl, fun closed member => ?_⟩
          rcases List.mem_append.mp member with old | fresh
          · exact retired closed old
          · rw [List.mem_singleton.mp fresh]; exact none_
        · exact ⟨rfl, retired⟩
        · exact absurd cancel (stops control (List.mem_cons_self ..))
      obtain ⟨two, rest'⟩ := postControls_stops height rest mail' next ok
        (fun c member => stops c (List.mem_cons_of_mem _ member)) one.2
      exact ⟨two.trans one.1, rest'⟩

/-- **Every post of a mail names a payer**, in the state the turn installs. Premises (the
census's, as `Birth.retention_cells_have_payer`'s): the posts' cells are pairwise
distinct and none lands on an object record (a coordinate collision); the objects
sending into the mail's inboxes have records; and a slot the mail queues on (read, not
opened by it) still answers to an inbox cell. -/
theorem Mail.cells_have_payer {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) (posts : List Post)
    (included : ∀ post ∈ mail.posts, post ∈ posts)
    (distinct : (posts.map Post.cell).Nodup)
    (objectsUnwritten : ∀ post ∈ posts, ∀ object, post.cell ≠ objectCell config.domain object)
    (anchored : Mail.Anchored mail)
    (owned : ∀ held ∈ mail.inboxes, (objectAt config snapshot.canonicalBytes ⟨held.sender⟩).isSome = true)
    (pipelined : ∀ held ∈ mail.slots, held.read ≠ none → ∃ inbox,
      inboxAt (afterPosts snapshot posts) held.now.activity = some inbox ∧
        (objectAt config snapshot.canonicalBytes ⟨inbox.sender⟩).isSome = true) :
    ∀ post ∈ mail.posts, (payloadOf post.bytes).isSome = true →
      (payerOfBytes config (afterPosts snapshot posts) post.bytes).isSome = true := by
  have ownedAfter : ∀ (sender : Nat), (objectAt config snapshot.canonicalBytes ⟨sender⟩).isSome = true →
      ∃ record, objectAt config (afterPosts snapshot posts) ⟨sender⟩ = some record := by
    intro sender isSome
    rw [objectAt_afterPosts config snapshot posts ⟨sender⟩ (fun post member => objectsUnwritten post member _)]
    exact Option.isSome_iff_exists.mp isSome
  intro post member live
  have inboxOf : ∀ (cell : CellId), (∃ held ∈ mail.inboxes, held.cell = cell) → ∃ inbox,
      inboxAt (afterPosts snapshot posts) cell = some inbox ∧
        (objectAt config snapshot.canonicalBytes ⟨inbox.sender⟩).isSome = true := by
    intro cell ⟨h, hm, hcell⟩
    have inPosts := included _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (List.mem_map.mpr ⟨h, hm, rfl⟩)))))
    refine ⟨h.now, ?_, ?_⟩
    · rw [← hcell]
      exact inboxAt_posted snapshot posts distinct _ inPosts h.now rfl
    · rw [h.ends.1]; exact owned h hm
  rcases List.mem_append.mp member with front | inClosed
  swap
  · obtain ⟨closed, hmem, rfl⟩ := List.mem_map.mp inClosed
    unfold ClosedSlot.post at live ⊢
    cases decided : closed.decided with
    | none =>
      rw [decided] at live
      simp [slotRetire, postAt, payloadOf_retired] at live
    | some slot =>
      obtain ⟨inbox, hin, hown⟩ := inboxOf slot.activity (anchored.2 closed hmem slot decided)
      obtain ⟨record, hrec⟩ := ownedAfter inbox.sender hown
      exact payer_slot_image_inbox config _ slot inbox record hin hrec
  rcases List.mem_append.mp front with inInbox | inSlot
  · obtain ⟨held, hmem, rfl⟩ := List.mem_map.mp inInbox
    obtain ⟨record, hrec⟩ := ownedAfter held.sender (owned held hmem)
    have ends := held.ends.1
    exact option_isSome_of_eq (payer_inbox_image config _ held.now record (by rw [ends]; exact hrec))
  · obtain ⟨held, hmem, rfl⟩ := List.mem_map.mp inSlot
    have found : ∃ inbox, inboxAt (afterPosts snapshot posts) held.now.activity = some inbox ∧
        (objectAt config snapshot.canonicalBytes ⟨inbox.sender⟩).isSome = true := by
      by_cases fresh : held.read = none
      · exact inboxOf _ (anchored.1 held hmem fresh)
      · exact pipelined held hmem fresh
    obtain ⟨inbox, hin, hown⟩ := found
    obtain ⟨record, hrec⟩ := ownedAfter inbox.sender hown
    exact payer_slot_image_inbox config _ held.now inbox record hin hrec

/-- **`retention_cells_have_payer`, an invocation.** Every cell an admitted invocation
leaves holding an activity payload names its payer in the installed state: a state
cell its object's `ObjectRecord.payer`, an inbox its sender object's, a reply slot the
payer of the inbox it answers to. Premises: as `Mail.cells_have_payer`. The inhabitants
are the invocations of the send journeys (RECORD: journey-send S1-S6); no closed
invocation is constructible in Lean (the call tree runs a program). -/
theorem Invocation.retention_cells_have_payer {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : InvokeRequest}
    (invoked : Invocation config snapshot height request)
    (distinct : (invoked.posts.map Post.cell).Nodup)
    (objectsUnwritten : ∀ post ∈ invoked.posts, ∀ object, post.cell ≠ objectCell config.domain object)
    (owned : ∀ held ∈ invoked.mail.inboxes,
      (objectAt config snapshot.canonicalBytes ⟨held.sender⟩).isSome = true)
    (pipelined : ∀ held ∈ invoked.mail.slots, held.read ≠ none → ∃ inbox,
      inboxAt (afterPosts snapshot invoked.posts) held.now.activity = some inbox ∧
        (objectAt config snapshot.canonicalBytes ⟨inbox.sender⟩).isSome = true) :
    CellsPaid config (afterPosts snapshot invoked.posts) (invoked.posts.map Post.cell) := by
  obtain ⟨read, _⟩ :=
    exec_invariant config snapshot height request.authority (invokeTransaction request) _ [] _ _ _ _ _ _
      invoked.execExact (by simp) (by intro _ _ h; cases h) (by intro _ h; cases h)
  have anchored : Mail.Anchored invoked.mail :=
    postControls_anchored height _ _ _ invoked.mailExact
      (postMail_anchored request.postage request.account 0 _ _ _ invoked.sentExact Mail.empty_anchored)
  apply cellsPaid_of_posts
  intro post member live
  have inPosts := member
  rw [invoked.postsExact] at member
  rcases List.mem_append.mp member with inFront | isBook
  · rcases List.mem_append.mp inFront with inJournal | inMail
    · obtain ⟨entry, entryIn, state, shape⟩ := Journal.posts_state invoked.journal config snapshot post inJournal
      have held : objectAt config (afterPosts snapshot invoked.posts) entry.object = some entry.record := by
        rw [objectAt_afterPosts config snapshot invoked.posts entry.object
          (fun post member => objectsUnwritten post member _)]
        exact objectAt_of_read (read entry entryIn).2
      rw [shape]
      exact option_isSome_of_eq (payer_state_image config _ entry.object state entry.record held)
    · exact Mail.cells_have_payer invoked.mail invoked.posts
        (fun post member => by
          rw [invoked.postsExact]
          exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr member))))
        distinct objectsUnwritten anchored owned pipelined post inMail live
  · simp only [List.mem_singleton] at isBook
    subst isBook
    rw [Postings.write_payload] at live
    cases live

theorem runMessage_read {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height target : Nat} {message : Inbox.Message} {result : Data} {journal : Journal}
    (ran : runMessage config snapshot height target message = .replied result journal) :
    ObjectsRead config snapshot journal := by
  unfold runMessage at ran
  split at ran
  · cases ran
  · split at ran
    · cases ran
    · rename_i execExact
      split at ran
      · cases ran
        obtain ⟨read, _⟩ := exec_invariant config snapshot height _ _ _ [] _ _ _ _ _ _ execExact
          (by simp) (by intro _ _ h; cases h) (by intro _ h; cases h)
        exact read
      · cases ran

/-- **`retention_cells_have_payer`, a delivery** (failed or not). Every cell an admitted
delivery leaves holding an activity payload names its payer in the installed state: the
state cells its call tree wrote their object's, the inboxes (the popped one and the
forwarded ones) their sender object's, the slots it opens and the slot it decides the
payer of the inbox they answer to (a slot whose sender stopped waiting is retired and
holds nothing). Premises: as `Mail.cells_have_payer`. (The former premise that the slot
answers to the inbox that held its message is now checked by `deliverMessage` itself,
`MessageDelivery.activityExact`, cv 01a113fe-140a.) -/
theorem MessageDelivery.retention_cells_have_payer {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request)
    (distinct : (delivered.posts.map Post.cell).Nodup)
    (objectsUnwritten : ∀ post ∈ delivered.posts, ∀ object, post.cell ≠ objectCell config.domain object)
    (owned : ∀ held ∈ delivered.mail.inboxes,
      (objectAt config snapshot.canonicalBytes ⟨held.sender⟩).isSome = true)
    (pipelined : ∀ held ∈ delivered.mail.slots, held.read ≠ none → ∃ inbox,
      inboxAt (afterPosts snapshot delivered.posts) held.now.activity = some inbox ∧
        (objectAt config snapshot.canonicalBytes ⟨inbox.sender⟩).isSome = true) :
    CellsPaid config (afterPosts snapshot delivered.posts) (delivered.posts.map Post.cell) := by
  have seedAnchored : Mail.Anchored delivered.seed := by
    refine ⟨fun slot member => ?_, fun closed member => ?_⟩
    · rw [delivered.seedExact.2.1] at member
      cases member
    · rw [delivered.seedExact.2.2.2.2.1] at member
      cases member
  obtain ⟨sentAnchored, sentPersist, _, _⟩ := continueMessage_mail delivered.continued seedAnchored
  have anchored : Mail.Anchored delivered.mail := by
    have := forward_anchored delivered.outcome.reference delivered.slot.queued delivered.sent sentAnchored
    rw [delivered.forwarded] at this
    exact this
  have mailIn : ∀ post ∈ delivered.mail.posts, post ∈ delivered.posts := by
    intro post member
    rw [delivered.postsExact]
    exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr member)))
  apply cellsPaid_of_posts
  intro post member live
  rw [delivered.postsExact] at member
  rcases List.mem_append.mp member with inFront | last
  · rcases List.mem_append.mp inFront with inOutcome | inMail
    · rcases hout : delivered.outcome with ⟨result, journal⟩ | reason
      · rw [hout] at inOutcome
        have read := runMessage_read (delivered.ran hout)
        obtain ⟨entry, entryIn, state, shape⟩ := Journal.posts_state journal config snapshot post inOutcome
        have held : objectAt config (afterPosts snapshot delivered.posts) entry.object = some entry.record := by
          rw [objectAt_afterPosts config snapshot delivered.posts entry.object
            (fun post member => objectsUnwritten post member _)]
          exact objectAt_of_read (read entry entryIn).2
        rw [shape]
        exact option_isSome_of_eq (payer_state_image config _ entry.object state entry.record held)
      · rw [hout] at inOutcome
        simp [Outcome.posts] at inOutcome
    · exact Mail.cells_have_payer delivered.mail delivered.posts mailIn distinct objectsUnwritten anchored owned
        pipelined post inMail live
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at last
    rcases last with isSlot | isBook
    · subst isSlot
      unfold replyPost at live ⊢
      split
      swap
      · rename_i unwatched
        rw [if_neg unwatched] at live
        simp [slotRetire, postAt, payloadOf_retired] at live
      obtain ⟨_, _, _, decided⟩ := AnswerSlot.decideDelivery_single delivered.decidedExact
      have decidedActivity : delivered.decided.activity = delivered.slot.activity := by rw [decided]
      have inboxCell : ∃ held ∈ delivered.mail.inboxes,
          held.cell = Inbox.cell config.domain request.sender request.target := by
        have seeded := delivered.seedExact.1
        cases hl : delivered.seed.inboxes with
        | nil => rw [hl] at seeded; cases seeded
        | cons first rest =>
          rw [hl] at seeded
          simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at seeded
          obtain ⟨⟨hs, ht, _⟩, _⟩ := seeded
          have firstIn : first ∈ delivered.seed.inboxes := by rw [hl]; exact List.mem_cons_self ..
          obtain ⟨kept, keptIn, keptCell⟩ := sentPersist first firstIn
          have persisted := forward_inboxes_persist delivered.outcome.reference delivered.slot.queued
            delivered.sent kept keptIn
          rw [delivered.forwarded] at persisted
          obtain ⟨held, hm, hc⟩ := persisted
          refine ⟨held, hm, (hc.trans keptCell).trans ?_⟩
          unfold HeldInbox.cell
          rw [hs, ht]
      obtain ⟨held, hm, hcell⟩ := inboxCell
      have inPosts := mailIn _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (List.mem_map.mpr ⟨held, hm, rfl⟩)))))
      have inboxHeld : inboxAt (afterPosts snapshot delivered.posts) delivered.decided.activity = some held.now := by
        rw [decidedActivity, delivered.activityExact, ← hcell]
        exact inboxAt_posted snapshot delivered.posts distinct _ inPosts held.now rfl
      obtain ⟨record, hrec⟩ : ∃ record, objectAt config (afterPosts snapshot delivered.posts) ⟨held.now.sender⟩ =
          some record := by
        rw [objectAt_afterPosts config snapshot delivered.posts ⟨held.now.sender⟩
          (fun post member => objectsUnwritten post member _), held.ends.1]
        exact Option.isSome_iff_exists.mp (owned held hm)
      exact payer_slot_image_inbox config _ delivered.decided held.now record inboxHeld hrec
    · subst isBook
      rw [Postings.write_payload] at live
      cases live

#assert_axioms MessageDelivery.conserves
#assert_axioms creditTransfers_debit
#assert_axioms MessageDelivery.debits_only_purse
#assert_axioms MessageDelivery.pops
#assert_axioms MessageDelivery.decides_own_slot
#assert_axioms MessageDelivery.failed_delivery_pops
#assert_axioms runMessage_read
#assert_axioms MessageDelivery.retention_cells_have_payer
#assert_axioms option_isSome_of_eq
#assert_axioms HeldInbox.cell_eq
#assert_axioms payer_inbox_image
#assert_axioms payer_slot_image_inbox
#assert_axioms afterPosts_of_nodup
#assert_axioms objectAt_afterPosts
#assert_axioms inboxAt_posted
#assert_axioms Mail.empty_anchored
#assert_axioms holdInbox_cover
#assert_axioms holdSlot_cover
#assert_axioms openSlot_fresh
#assert_axioms Mail.send_inboxes_persist
#assert_axioms Mail.send_anchored
#assert_axioms postMail_anchored
#assert_axioms forward_anchored
#assert_axioms postMail_inboxes_persist
#assert_axioms continueMessage_mail
#assert_axioms forward_inboxes_persist
#assert_axioms Mail.cells_have_payer
#assert_axioms Mail.send_keeps
#assert_axioms postMail_keeps
#assert_axioms Mail.control_credits
#assert_axioms postControls_credits
#assert_axioms Invocation.mail_of_silent
#assert_axioms Invocation.debits_only_account_of_silent
#assert_axioms controlSlot_held_cover
#assert_axioms Mail.control_inboxes_persist
#assert_axioms Mail.control_anchored
#assert_axioms postControls_anchored
#assert_axioms postControls_stops
#assert_axioms replyPost_spec
#assert_axioms Invocation.retention_cells_have_payer
#assert_axioms Invocation.debits_only_account
#assert_axioms Mail.send_credit
#assert_axioms postMail_credits
#assert_axioms Invocation.escrows_every_send
#assert_axioms Mail.inboxes_bounded
#assert_axioms MessageDelivery.pop_frees_message
#assert_axioms MessageDelivery.remaining_within_bound
#assert_axioms forward_none
#assert_axioms MessageDelivery.failed_mail
#assert_axioms MessageDelivery.failed_delivery_posts

/-- **A message waits while its target drains**: the delivery is refused (the
message stays at the head of its inbox) when the target's upgrade admits no new
frame. -/
theorem message_waits_while_draining {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : MessageRequest} {record : ObjectRecord.ObjectRecord}
    (found : readObject config snapshot ⟨request.target⟩ = .ok (some record)) (closed : record.admitsNew = false) :
    deliverMessage config snapshot height request = .error (.kernel .draining) := by
  have waits : waitsForUpgrade config snapshot request.target = true := by
    simp [waitsForUpgrade, found, closed]
  simp [deliverMessage, waits]

#assert_axioms message_waits_while_draining

end Minidregg.Kernel.ObjectiveSend
