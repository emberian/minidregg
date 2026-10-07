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
never retired. -/

/-- **An invocation is paid from its signer's account only**: every operation of its
batch (the envelope's fee and each send's postage into its queue's purse) debits
`request.account`. -/
theorem Invocation.debits_only_account {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : InvokeRequest}
    (invoked : Invocation config snapshot height request) :
    ∀ op ∈ invoked.posted.batch.operations, debited op = some request.account := by
  rw [invoked.batchExact]
  intro op member
  simp only [invokeBatch, List.mem_cons] at member
  rcases member with fee | credit
  · subst fee; rfl
  · exact creditTransfers_debit config _ _ op credit

/-- **Every send credits exactly one purse, with the postage of its message.** -/
theorem Mail.send_credit {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {mail next : Mail config snapshot} {message : Inbox.Message} {destination : Destination}
    (sent : mail.send message destination = .ok next) :
    ∃ purse, next.credits = mail.credits ++ [(purse, message.postage)] := by
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

theorem postMail_credits {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (postage : Minidregg.Compiler.ObjectiveInvocationClaim.Capacity) (refund : AccountId) :
    ∀ (outs : List Outgoing) (mail next : Mail config snapshot),
      postMail config snapshot postage refund mail outs = .ok next →
      next.credits.length = mail.credits.length + outs.length ∧
        ∀ credit ∈ next.credits, credit ∈ mail.credits ∨ credit.2 = config.tariff.workOf postage
  | [], mail, next, ok => by
    simp only [postMail] at ok
    cases ok
    exact ⟨by simp, fun credit member => .inl member⟩
  | out :: rest, mail, next, ok => by
    simp only [postMail] at ok
    split at ok
    · cases ok
    · rename_i mail' sent
      obtain ⟨purse, credits⟩ := Mail.send_credit sent
      obtain ⟨len, each⟩ := postMail_credits postage refund rest mail' next ok
      refine ⟨?_, ?_⟩
      · rw [len, credits]; simp; omega
      · intro credit member
        rcases each credit member with old | fresh
        · rw [credits] at old
          rcases List.mem_append.mp old with first | added
          · exact .inl first
          · simp only [List.mem_singleton] at added
            exact .inr (congrArg Prod.snd added)
        · exact .inr fresh

/-- **An invocation escrows every send at the public price of its declared postage
envelope**: one credit per send, each of `workOf request.postage`, and nothing else.
(A credit is the message's postage, not a storage deposit.) -/
theorem Invocation.escrows_every_send {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : InvokeRequest}
    (invoked : Invocation config snapshot height request) :
    invoked.mail.credits.length = invoked.journal.outbox.length ∧
      ∀ credit ∈ invoked.mail.credits, credit.2 = config.tariff.workOf request.postage := by
  obtain ⟨len, each⟩ := postMail_credits request.postage request.account invoked.journal.outbox Mail.empty
    invoked.mail invoked.mailExact
  refine ⟨?_, ?_⟩
  · rw [len]; simp [Mail.empty]
  · intro credit member
    rcases each credit member with old | fresh
    · exact absurd old (by simp [Mail.empty])
    · exact fresh

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
  have forwarded := delivered.forwarded
  rw [failed, show (Outcome.failed reason).reference = none from rfl, forward_none] at forwarded
  simp only [Prod.mk.injEq] at forwarded
  exact ⟨forwarded.1.symm, forwarded.2.symm⟩

/-- **A failed delivery leaves behind exactly three posts**: the popped, shortened inbox,
the slot it decided `broken`, and the Book. No cell is opened, no state cell written. -/
theorem MessageDelivery.failed_delivery_posts {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request) {reason : String}
    (failed : delivered.outcome = .failed reason) :
    delivered.posts =
      [postAt snapshot (Inbox.cell config.domain request.sender request.target) (inboxImage delivered.remaining),
        slotPost config snapshot delivered.decided, delivered.posted.write config snapshot] := by
  obtain ⟨sameMail, _⟩ := delivered.failed_mail failed
  have noPosts : delivered.outcome.posts config snapshot = [] := by rw [failed]; rfl
  obtain ⟨inboxes, slots, _, _⟩ := delivered.seedExact
  have seedPosts : delivered.seed.posts =
      [postAt snapshot (Inbox.cell config.domain request.sender request.target) (inboxImage delivered.remaining)] := by
    cases hl : delivered.seed.inboxes with
    | nil => rw [hl] at inboxes; cases inboxes
    | cons first rest =>
      rw [hl] at inboxes
      simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, List.map_eq_nil_iff] at inboxes
      obtain ⟨⟨hs, ht, hn⟩, restNil⟩ := inboxes
      unfold Mail.posts
      rw [hl, slots, restNil]
      simp [HeldInbox.cell, hs, ht, hn]
  rw [delivered.postsExact, noPosts, sameMail, seedPosts]
  simp

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

/-- **Anchored**: every reply slot a mail opens (one it did not read) answers to an inbox cell the mail holds. -/
def Mail.Anchored {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (mail : Mail config snapshot) : Prop :=
  ∀ slot ∈ mail.slots, slot.read = none → ∃ held ∈ mail.inboxes, held.cell = slot.now.activity

theorem Mail.empty_anchored {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} :
    Mail.Anchored (Mail.empty : Mail config snapshot) := by
  intro slot member
  cases member

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
    · obtain ⟨held, hm, hc⟩ := anchored slot old opened
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
    · exact anchored slot (others slot old) opened
    · have same := List.mem_singleton.mp updated
      subst same
      rcases heldCover with inMail | read
      · have a := anchored _ inMail opened
        exact a
      · exact absurd opened read

theorem postMail_anchored {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    (postage : Minidregg.Compiler.ObjectiveInvocationClaim.Capacity) (refund : AccountId) :
    ∀ (outs : List Outgoing) (mail next : Mail config snapshot),
      postMail config snapshot postage refund mail outs = .ok next → Mail.Anchored mail → Mail.Anchored next
  | [], mail, next, ok, anchored => by
    simp only [postMail] at ok
    cases ok
    exact anchored
  | out :: rest, mail, next, ok, anchored => by
    simp only [postMail] at ok
    split at ok
    · cases ok
    · rename_i mail' sent
      exact postMail_anchored postage refund rest mail' next ok (Mail.send_anchored anchored sent)

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
    ∀ post ∈ mail.posts, (payerOfBytes config (afterPosts snapshot posts) post.bytes).isSome = true := by
  have ownedAfter : ∀ (sender : Nat), (objectAt config snapshot.canonicalBytes ⟨sender⟩).isSome = true →
      ∃ record, objectAt config (afterPosts snapshot posts) ⟨sender⟩ = some record := by
    intro sender isSome
    rw [objectAt_afterPosts config snapshot posts ⟨sender⟩ (fun post member => objectsUnwritten post member _)]
    exact Option.isSome_iff_exists.mp isSome
  intro post member
  rcases List.mem_append.mp member with inInbox | inSlot
  · obtain ⟨held, hmem, rfl⟩ := List.mem_map.mp inInbox
    obtain ⟨record, hrec⟩ := ownedAfter held.sender (owned held hmem)
    have ends := held.ends.1
    exact option_isSome_of_eq (payer_inbox_image config _ held.now record (by rw [ends]; exact hrec))
  · obtain ⟨held, hmem, rfl⟩ := List.mem_map.mp inSlot
    have inboxOf : ∃ inbox, inboxAt (afterPosts snapshot posts) held.now.activity = some inbox ∧
        (objectAt config snapshot.canonicalBytes ⟨inbox.sender⟩).isSome = true := by
      by_cases fresh : held.read = none
      · obtain ⟨h, hm, hcell⟩ := anchored held hmem fresh
        have inPosts := included _ (List.mem_append.mpr (.inl (List.mem_map.mpr ⟨h, hm, rfl⟩)))
        refine ⟨h.now, ?_, ?_⟩
        · rw [← hcell]
          exact inboxAt_posted snapshot posts distinct _ inPosts h.now rfl
        · rw [h.ends.1]; exact owned h hm
      · exact pipelined held hmem fresh
    obtain ⟨inbox, hin, hown⟩ := inboxOf
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
    postMail_anchored request.postage request.account _ _ _ invoked.mailExact Mail.empty_anchored
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
        distinct objectsUnwritten anchored owned pipelined post inMail
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
payer of the inbox they answer to. Premises: as `Mail.cells_have_payer`, and that the
slot the message answers to is the reply slot of the inbox that held it
(`activity`: established by `openSlot`, which `deliverMessage` does not recheck). -/
theorem MessageDelivery.retention_cells_have_payer {rootBytes : Bytes → Digest} {config : Config}
    {snapshot : Snapshot rootBytes} {height : Nat} {request : MessageRequest}
    (delivered : MessageDelivery config snapshot height request)
    (distinct : (delivered.posts.map Post.cell).Nodup)
    (objectsUnwritten : ∀ post ∈ delivered.posts, ∀ object, post.cell ≠ objectCell config.domain object)
    (owned : ∀ held ∈ delivered.mail.inboxes,
      (objectAt config snapshot.canonicalBytes ⟨held.sender⟩).isSome = true)
    (pipelined : ∀ held ∈ delivered.mail.slots, held.read ≠ none → ∃ inbox,
      inboxAt (afterPosts snapshot delivered.posts) held.now.activity = some inbox ∧
        (objectAt config snapshot.canonicalBytes ⟨inbox.sender⟩).isSome = true)
    (activity : delivered.slot.activity = Inbox.cell config.domain request.sender request.target) :
    CellsPaid config (afterPosts snapshot delivered.posts) (delivered.posts.map Post.cell) := by
  have seedAnchored : Mail.Anchored delivered.seed := by
    intro slot member
    rw [delivered.seedExact.2.1] at member
    cases member
  have anchored : Mail.Anchored delivered.mail := by
    have := forward_anchored delivered.outcome.reference delivered.slot.queued delivered.seed seedAnchored
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
        have ran := delivered.outcomeExact
        rw [hout] at ran
        have read := runMessage_read ran
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
        pipelined post inMail
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at last
    rcases last with isSlot | isBook
    · subst isSlot
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
          have persisted := forward_inboxes_persist delivered.outcome.reference delivered.slot.queued
            delivered.seed first firstIn
          rw [delivered.forwarded] at persisted
          obtain ⟨held, hm, hc⟩ := persisted
          refine ⟨held, hm, hc.trans ?_⟩
          unfold HeldInbox.cell
          rw [hs, ht]
      obtain ⟨held, hm, hcell⟩ := inboxCell
      have inPosts := mailIn _ (List.mem_append.mpr (.inl (List.mem_map.mpr ⟨held, hm, rfl⟩)))
      have inboxHeld : inboxAt (afterPosts snapshot delivered.posts) delivered.decided.activity = some held.now := by
        rw [decidedActivity, activity, ← hcell]
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
#assert_axioms forward_inboxes_persist
#assert_axioms Mail.cells_have_payer
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

end Minidregg.Kernel.ObjectiveSend
