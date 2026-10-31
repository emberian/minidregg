/- The effect Plan's keystone (statement first: docs/evidence/2026-10-27-world-native/DOMAINS.md,
"The effect Plan: statement first").

An activity's Plan may ask the kernel to perform an effect at its yield (`decodePlan`:
`transfer {to, amount, write}` and `commit {write}`, each a `PlanAwait` whose source is
`PlanSource.performed`). The yield's await is decided by the kernel at the yield itself
(`commitYield`): `settled` when performed, `refused` with its reason when not, and the next
delivery resumes with exactly that outcome (`settle`). A performed transfer is ONE posting in the
turn's own batch (`effectOps`, `withEffect`); a refused one posts and writes nothing.

This file states the keystone (Performed, Refused, Resumed, and the law's teeth on a commit) and
its poles (satisfiable, teeth, premise inhabitation) as propositions. -/
import Kernel.ObjectiveActivity

namespace Minidregg.Kernel.ObjectiveActivityEffect
open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Theory.ObjectiveBendDemandMachine (State resume)
open Minidregg.Theory.CanonicalResourceKernel (Book Batch Operation AccountId AssetId logicalBook
  applyOperations registerAccounts deregisterAccounts deregisterAccounts_accounts)
open Minidregg.Kernel.ObjectiveTariff (addCapacity)
open Minidregg.Kernel.ObjectRecord (ObjectRecord admitWrite)
set_option autoImplicit false

/-! ## Vocabulary -/

/-- The await a yield at `height` records for an effect the kernel decided `verdict`: an effect
Plan's patience is 1. -/
def decidedAwait (cell : CellId) (generation : Nat) (checkpoint : Digest) (height : Nat) (verdict : Verdict) :
    Await :=
  ⟨awaitId cell generation checkpoint, .performed verdict, height + 1, height⟩

/-- The Plan `transfer {to, amount, write}` decodes to. -/
def transferPlan (write : Data) (recipient : AccountId) (amount : Nat) : PlanAwait :=
  ⟨write, .performed (.transfer recipient amount), 1⟩

/-- The Plan `commit {write}` decodes to. -/
def commitPlan (write : Data) : PlanAwait := ⟨write, .performed .commit, 1⟩

/-- A recipient the kernel transfers to: an open account of the Book (after the turn's own
postings) other than the purse, the collector and the issuer well. -/
def Admissible (config : Config) (funds : Funds) (written : Option StateWritten) (recipient : AccountId) : Prop :=
  recipient ≠ funds.purse ∧ recipient ≠ config.collector ∧ recipient ≠ config.asset ∧
    recipient ∈ (funds.book written).accounts

/-- The purse covers the transfer and still reserves `reserve` of the settled await after it. -/
def Covered (config : Config) (funds : Funds) (reserve : Await → Nat) (written : Option StateWritten)
    (settledAwait : Await) (amount : Nat) : Prop :=
  amount + reserve settledAwait ≤ purse (funds.book written) config.asset funds.purse

/-! ## The keystone -/

/-- **1. Performed.** A yield whose Plan is `transfer {to, amount, write}`, on a program that types
the effect outcomes, whose write builds, whose recipient is admissible and whose purse covers the
amount and the await's reserve after it, commits exactly: the await decided `settled`, the write
built, the write's post, and the transfer as the yield's effect; the turn's batch gets exactly the
one posting `purse → to` of `amount` in the credit asset. -/
def PerformedStatement : Prop :=
  ∀ {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (transaction : TransactionId) (cell object : CellId) (generation : Nat) (checkpoint : Digest)
    (current : Option ObjectState) (viewed : Bool) (write : Data) (recipient : AccountId) (amount : Nat)
    (funds : Funds) (reserve : Await → Nat) (written : Option StateWritten),
    1 ≤ config.maxPatience → height + 1 < 256 ^ 8 → funds.effects = true →
    stateWrite config snapshot object current viewed write = .ok written →
    Admissible config funds written recipient →
    Covered config funds reserve written (decidedAwait cell generation checkpoint height .settled) amount →
    ∃ committed,
      commitYield config snapshot height transaction cell object generation checkpoint current viewed
        (transferPlan write recipient amount) funds reserve = .ok committed ∧
      committed.await = decidedAwait cell generation checkpoint height .settled ∧
      committed.written = written ∧
      committed.posts = (written.map StateWritten.post).toList ∧
      effectOps config funds.purse (some committed) = [.transfer funds.purse recipient config.asset amount]

/-- **1'. Performed, in the turn.** An admitted delivery whose yield performed a transfer posts,
in its one batch, exactly its own charges followed by the transfer out of the purse, and the batch
conserves every asset on the Book. -/
def DeliveryPerformedStatement : Prop :=
  ∀ {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} {height : Nat}
    {request : DeliverRequest} (delivery : Delivery config snapshot height request) (committed : YieldCommit)
    (recipient : AccountId) (amount : Nat),
    delivery.yielded = some committed → committed.effect = some (recipient, amount) →
    delivery.posted.batch = withEffect
        (deliveryCharges config delivery.record request.record delivery.settlement.path request
          (drainFee config delivery.object (delivery.yielded.bind YieldCommit.written)))
        [.transfer (heldAccount request.record) recipient config.asset amount] ∧
    ∀ asset, (logicalBook delivery.posted.post.logical).totalAsset asset =
      (logicalBook delivery.book.logical).totalAsset asset

/-- **1''. The transfer moves exactly `amount`** from the purse to the recipient (two distinct
accounts) and nothing else of either balance. -/
def TransferMovesStatement : Prop :=
  ∀ (book : Book) (source recipient : AccountId) (asset : AssetId) (amount : Nat), source ≠ recipient →
    ((Operation.transfer source recipient asset amount).apply book).balance source asset =
        book.balance source asset - amount ∧
      ((Operation.transfer source recipient asset amount).apply book).balance recipient asset =
        book.balance recipient asset + amount

/-- **2. Refused (teeth).** A transfer whose verdict is a refusal commits the await decided
`refused` by that reason, with NO write, NO post and NO effect. -/
def RefusedStatement : Prop :=
  ∀ {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (transaction : TransactionId) (cell object : CellId) (generation : Nat) (checkpoint : Digest)
    (current : Option ObjectState) (viewed : Bool) (write : Data) (recipient : AccountId) (amount : Nat)
    (funds : Funds) (reserve : Await → Nat) (written : Option StateWritten) (reason : EffectRefusal),
    1 ≤ config.maxPatience → height + 1 < 256 ^ 8 → funds.effects = true →
    stateWrite config snapshot object current viewed write = .ok written →
    transferVerdict config funds (reserve (decidedAwait cell generation checkpoint height .settled)) written
      recipient amount = .refused reason →
    commitYield config snapshot height transaction cell object generation checkpoint current viewed
      (transferPlan write recipient amount) funds reserve =
      .ok ⟨decidedAwait cell generation checkpoint height (.refused reason), none, [], none⟩

/-- **2'. The refusals, by name.** An uncovered transfer to an admissible recipient is refused
`unfunded`; a transfer to the purse, the collector or the issuer well is refused `reserved`; one
to an account the Book does not hold open is refused `closed`. Exactly the covered transfer to an
admissible recipient is performed. -/
def VerdictStatement : Prop :=
  ∀ (config : Config) (funds : Funds) (reserve : Nat) (written : Option StateWritten)
    (recipient : AccountId) (amount : Nat),
    (Admissible config funds written recipient → purse (funds.book written) config.asset funds.purse < amount + reserve →
      transferVerdict config funds reserve written recipient amount = .refused .unfunded) ∧
    ((recipient = funds.purse ∨ recipient = config.collector ∨ recipient = config.asset) →
      transferVerdict config funds reserve written recipient amount = .refused .reserved) ∧
    ((recipient ≠ funds.purse ∧ recipient ≠ config.collector ∧ recipient ≠ config.asset) →
      recipient ∉ (funds.book written).accounts →
      transferVerdict config funds reserve written recipient amount = .refused .closed) ∧
    (transferVerdict config funds reserve written recipient amount = .settled ↔
      Admissible config funds written recipient ∧ amount + reserve ≤ purse (funds.book written) config.asset funds.purse)

/-- **2''. Refused, in the turn.** An admitted delivery whose yield's effect was refused posts
only its own charges (nothing from the purse to the recipient) and its yield writes no state. -/
def DeliveryRefusedStatement : Prop :=
  ∀ {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} {height : Nat}
    {request : DeliverRequest} (delivery : Delivery config snapshot height request) (committed : YieldCommit)
    (reason : EffectRefusal),
    delivery.yielded = some committed → committed.await.source = .performed (.refused reason) →
    delivery.posted.batch = withEffect
        (deliveryCharges config delivery.record request.record delivery.settlement.path request
          (drainFee config delivery.object none)) [] ∧
    committed.written = none ∧ committed.posts = []

/-- **2'''. The law's teeth on a commit.** A `commit` writes only through the object's law: every
admitted delivery whose segment yields a `commit` and writes, wrote a state the object's law
admitted under the activity's principal. So a law-refused commit refuses the turn: no delivery is
admitted, nothing is written. -/
def CommitJudgedStatement : Prop :=
  ∀ {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} {height : Nat}
    {request : DeliverRequest} (delivery : Delivery config snapshot height request) (state : State)
    (write : Data) (committed : YieldCommit) (written : StateWritten),
    delivery.segment = .yielded state (commitPlan write) → delivery.yielded = some committed →
    committed.written = some written →
    admitWrite delivery.object (factsOf delivery.record.escrow.payer height delivery.record.object 2
      (some delivery.record.pin)) (written.before.map ObjectState.value) written.after.value = .ok ()

/-- **3. Resumed.** A performed await is settled by any delivery at any height with exactly the
outcome the yield recorded (no decider, no due height, no deadline, no slot), and the delivery
resumes the stored checkpoint with `responseData outcome view`. -/
def ResumedStatement : Prop :=
  (∀ {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (cell : CellId) (await : Await) (verdict : Verdict),
    await.source = .performed verdict →
    settle config snapshot height cell await = .ok ⟨.resumed, verdict.outcome, [], [], []⟩) ∧
  (∀ {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} {height : Nat}
    {request : DeliverRequest} (delivery : Delivery config snapshot height request) (verdict : Verdict),
    delivery.await.source = .performed verdict →
    delivery.settlement.decided = verdict.outcome ∧
      resume (responseData verdict.outcome delivery.view).term delivery.state = some delivery.resumed)

/-- **The funds agree with the batch.** A delivery's yield judges its effect against the purse
after the purse's own charges (`deliveryFunds`, `purseCharges`) while its batch applies all of the
delivery's charges (`deliveryCharges`, the submitter's added envelope included): for an admitted
delivery the two leave the purse the same balance and the Book the same open accounts, whatever the
yield writes. So a settled verdict is never refused at `settlePurse` (`awaitsFunding`) under the
wrong name, and a covered transfer is never recorded `unfunded`. A birth's funds ARE the Book its
`settlePurse` reads before the effect (`birthBefore` over the registered purse). -/
def FundsAgreeStatement : Prop :=
  (∀ {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} {height : Nat}
    {request : DeliverRequest} (delivery : Delivery config snapshot height request) (written : Option StateWritten),
    (deliveryFunds config snapshot delivery.input (logicalBook delivery.book.logical) delivery.object
      delivery.record request.record delivery.settlement.path).purse = heldAccount request.record ∧
    purse ((deliveryFunds config snapshot delivery.input (logicalBook delivery.book.logical) delivery.object
        delivery.record request.record delivery.settlement.path).book written) config.asset (heldAccount request.record) =
      purse ((deliveryCharges config delivery.record request.record delivery.settlement.path request
        (drainFee config delivery.object written)).apply (logicalBook delivery.book.logical)) config.asset
        (heldAccount request.record) ∧
    ((deliveryFunds config snapshot delivery.input (logicalBook delivery.book.logical) delivery.object
        delivery.record request.record delivery.settlement.path).book written).accounts =
      ((deliveryCharges config delivery.record request.record delivery.settlement.path request
        (drainFee config delivery.object written)).apply (logicalBook delivery.book.logical)).accounts) ∧
  (∀ {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (request : BirthRequest)
    (book : Book) (cell : CellId) (written : Option StateWritten),
    (birthFunds config snapshot request book cell).purse = heldAccount cell ∧
      (birthFunds config snapshot request book cell).book written =
        (birthBefore config book (heldAccount cell) request).apply (Batch.apply ⟨[heldAccount cell], [], []⟩ book))

/-- **The deposit does not depend on the verdict.** The storage deposit of the record a yield
stores is the same whether its effect was performed or refused (the verdict's wire is two octets
for every verdict), so the reserve a transfer is judged against (`yieldReserve`, at the settled
await) is the reserve of the record that is stored, whichever way it is decided. -/
def DepositIndependentStatement : Prop :=
  ∀ (config : Config) (base : Record) (generation : Nat) (state : State) (plan : PlanAwait)
    (id : Digest) (deadline yieldedAt : Nat) (verdict verdict' : Verdict)
    (written written' : Option StateWritten) (posts posts' : List Post) (effect effect' : Option (AccountId × Nat)),
    storageDeposit config (nextRecord base generation (.yielded state plan)
        (some ⟨⟨id, .performed verdict, deadline, yieldedAt⟩, written, posts, effect⟩)) =
      storageDeposit config (nextRecord base generation (.yielded state plan)
        (some ⟨⟨id, .performed verdict', deadline, yieldedAt⟩, written', posts', effect'⟩))

/-- **The law's teeth on a commit, at birth.** A birth whose first segment yields a `commit` that
writes wrote a state the object's law admitted under the birth's subject. -/
def BirthCommitJudgedStatement : Prop :=
  ∀ {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} {height : Nat}
    {request : BirthRequest} (born : Birth config snapshot height request) (state : State)
    (write : Data) (committed : YieldCommit) (written : StateWritten),
    born.segment = .yielded state (commitPlan write) → born.yielded = some committed →
    committed.written = some written →
    admitWrite born.object (factsOf request.subject height request.object request.factsTurn (some request.pin))
      (written.before.map ObjectState.value) written.after.value = .ok ()

/-- **The law refuses the turn, by name.** A delivery that reaches its judgment (every earlier step
admitted) with a yield whose write the object's law refuses is refused `objectWrite` with the law's
reason: nothing is committed. -/
def DeliverLawRefusesStatement : Prop :=
  ∀ {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes} {height : Nat}
    {request : DeliverRequest} (head : ResumeHead config snapshot request.record) (object : ObjectRecord)
    (tail : ResumeTail config snapshot height request.record head) (book : BookCell)
    (segment : Segment) (yielded : Option YieldCommit) (reason : ObjectRecord.WriteRefusal),
    resumeHead config snapshot request.record = .ok head →
    readObject config snapshot head.record.object = .ok (some object) →
    object.runs head.record.pin = true →
    resumeTail config snapshot height request.record head = .ok tail →
    config.covers (addCapacity (head.record.escrow.capacity tail.settlement.path) request.extra) = true →
    tail.needed config ≤ (addCapacity (head.record.escrow.capacity tail.settlement.path) request.extra).heap →
    config.planBudget.ticks ≤ (addCapacity (head.record.escrow.capacity tail.settlement.path) request.extra).extractTicks →
    ¬ (0 < head.record.tried ∧
      (addCapacity (head.record.escrow.capacity tail.settlement.path) request.extra).sourceTicks ≤ head.record.tried) →
    loadBook config snapshot = .ok book →
    (request.account ≠ heldAccount request.record ∧ config.collector ≠ heldAccount request.record) →
    resumedSegment config snapshot height (deliveryTransaction head.await.id) request.record head.record.object
      (head.record.generation + 1)
      (addCapacity (head.record.escrow.capacity tail.settlement.path) request.extra).sourceTicks tail.view tail.resumed
      (deliveryFunds config snapshot head.input (logicalBook book.logical) object head.record request.record
        tail.settlement.path) = .ok (segment, yielded) →
    judgeWritten object (factsOf head.record.escrow.payer height head.record.object 2 (some head.record.pin))
      (yielded.bind YieldCommit.written) = .error (.objectWrite reason) →
    deliver config snapshot height request = .error (.objectWrite reason)

/-! ## The poles -/

/-- The pole's purse, payer (recipient) and asset. -/
def polePurse : AccountId := 1001
def polePayer : AccountId := 7
def poleAsset : AssetId := 0

/-- The pole's Book: the purse holds 10 of the credit asset; the purse and the payer are open. -/
def poleBook : Book :=
  { Book.empty with accounts := {polePurse, polePayer}, balances := DFinsupp.single (polePurse, poleAsset) 10 }

/-- The pole's funds: a program typing the effect outcomes, the pole's purse and Book. -/
def poleFunds (base : Record) : Funds := ⟨true, polePurse, fun _ => poleBook, base⟩

/-- The pole's reserve: 3 (the await's fee pair plus its storage deposit). -/
def poleReserve : Await → Nat := fun _ => 3

/-- The deployments the poles run in: the credit asset is `poleAsset`, the collector is neither the
purse nor the payer, and a patience of 1 is admitted. -/
def PoleConfig (config : Config) : Prop :=
  config.asset = poleAsset ∧ config.collector ≠ polePurse ∧ config.collector ≠ polePayer ∧ 1 ≤ config.maxPatience

/-- **Satisfiable.** In a pole deployment, a yield `commit {write: {}}` (keep every field of present
state) is performed `settled`; a yield `transfer {to: payer, amount: 1}` is performed `settled` with
the one posting; and the delivery's response for the recorded await is
`resumed {outcome: settled {}, view}`. -/
def SatisfiablePole : Prop :=
  ∀ {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (transaction : TransactionId) (cell object : CellId) (generation : Nat) (checkpoint : Digest)
    (state : ObjectState) (base : Record) (view : ObjectState),
    PoleConfig config → height + 1 < 256 ^ 8 →
    (∃ committed, commitYield config snapshot height transaction cell object generation checkpoint (some state) true
        (commitPlan (.record [])) (poleFunds base) poleReserve = .ok committed ∧
      committed.await = decidedAwait cell generation checkpoint height .settled ∧ committed.effect = none) ∧
    (∃ committed, commitYield config snapshot height transaction cell object generation checkpoint (some state) true
        (transferPlan (.record []) polePayer 1) (poleFunds base) poleReserve = .ok committed ∧
      committed.await = decidedAwait cell generation checkpoint height .settled ∧
      effectOps config polePurse (some committed) = [.transfer polePurse polePayer poleAsset 1] ∧
      ∃ settlement, settle config snapshot height cell committed.await = .ok settlement ∧
        responseData settlement.decided view =
          .variant "resumed" (.record [("outcome", .variant "settled" (.record [])), ("view", viewData view)]))

/-- **Teeth.** In the same deployment, `transfer {to: payer, amount: 8}` (one above
purse − reserve = 10 − 3) is refused `unfunded` and `transfer {to: purse, amount: 1}` is refused
`reserved`; each writes nothing, posts nothing and moves nothing (no effect posting). That the
purse, the recipient and the state are then untouched by the whole turn is
`DeliveryRefusedStatement` (the batch is the turn's own charges only, the yield writes no state). -/
def TeethPole : Prop :=
  ∀ {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (transaction : TransactionId) (cell object : CellId) (generation : Nat) (checkpoint : Digest)
    (state : ObjectState) (base : Record),
    PoleConfig config → height + 1 < 256 ^ 8 →
    commitYield config snapshot height transaction cell object generation checkpoint (some state) true
        (transferPlan (.record []) polePayer 8) (poleFunds base) poleReserve =
      .ok ⟨decidedAwait cell generation checkpoint height (.refused .unfunded), none, [], none⟩ ∧
    commitYield config snapshot height transaction cell object generation checkpoint (some state) true
        (transferPlan (.record []) polePurse 1) (poleFunds base) poleReserve =
      .ok ⟨decidedAwait cell generation checkpoint height (.refused .reserved), none, [], none⟩ ∧
    effectOps config polePurse
      (some ⟨decidedAwait cell generation checkpoint height (.refused .unfunded), none, [], none⟩) = []

/-- **A commit writes.** In a pole deployment, `commit {write: {n: add 1}}` on present state
`{n: 0}` is performed `settled` and writes `{n: 1}` (the satisfiable pole's `commit {write: {}}`
writes nothing). -/
def CommitWritesPole : Prop :=
  ∀ {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height : Nat)
    (transaction : TransactionId) (cell object : CellId) (generation : Nat) (checkpoint : Digest)
    (version : Nat) (base : Record),
    PoleConfig config → height + 1 < 256 ^ 8 →
    ∃ committed written,
      commitYield config snapshot height transaction cell object generation checkpoint
          (some ⟨version, .record [("n", .natural 0)]⟩) true
          (commitPlan (.record [("n", .variant "add" (.natural 1))])) (poleFunds base) poleReserve = .ok committed ∧
        committed.await = decidedAwait cell generation checkpoint height .settled ∧
        committed.written = some written ∧ written.after.value = .record [("n", .natural 1)]

/-- **A law that refuses a commit.** The object `teethSeedRecord` (pinned to package 7, creator's
law `state = 5`) refuses, by name, the write of state 6 that a delivery of its own package makes
(turn 2, artifact 7): the judgment a delivery runs (`judgeWritten`) is `objectWrite`, so by
`DeliverLawRefusesStatement` the delivery is refused and nothing is written. -/
def CommitLawRefusedPole : Prop :=
  ∀ (post : Post),
    ∃ reason, judgeWritten ObjectRecord.teethSeedRecord (factsOf ⟨40⟩ 5 ⟨1⟩ 2 (some ⟨7⟩))
      (some ⟨none, ⟨1, .natural 6⟩, post⟩) = .error (.objectWrite reason)

/-- **Premise inhabitation.** The performed premises hold together: a pole deployment's funds have
an admissible recipient (the payer's own open account) and a purse covering amount 1 plus the
reserve. -/
def PremiseInhabitedPole : Prop :=
  ∀ (config : Config) (base : Record) (written : Option StateWritten) (settledAwait : Await),
    PoleConfig config →
    Admissible config (poleFunds base) written polePayer ∧
      Covered config (poleFunds base) poleReserve written settledAwait 1

/-! ## Proofs -/

theorem transferVerdict_settled_iff {config : Config} {funds : Funds} {reserve : Nat} {written : Option StateWritten}
    {recipient : AccountId} {amount : Nat} :
    transferVerdict config funds reserve written recipient amount = .settled ↔
      Admissible config funds written recipient ∧
        amount + reserve ≤ purse (funds.book written) config.asset funds.purse := by
  unfold transferVerdict Admissible
  by_cases r : recipient = funds.purse ∨ recipient = config.collector ∨ recipient = config.asset
  · rw [if_pos r]
    constructor
    · intro h; cases h
    · rintro ⟨⟨a, b, c, _⟩, _⟩; rcases r with r | r | r <;> contradiction
  · rw [if_neg r]
    simp only [not_or] at r
    by_cases o : recipient ∈ (funds.book written).accounts
    · rw [if_neg (not_not.mpr o)]
      by_cases c : amount + reserve ≤ purse (funds.book written) config.asset funds.purse
      · rw [if_pos c]; exact ⟨fun _ => ⟨⟨r.1, r.2.1, r.2.2, o⟩, c⟩, fun _ => rfl⟩
      · rw [if_neg c]
        constructor
        · intro h; cases h
        · rintro ⟨_, h⟩; exact absurd h c
    · rw [if_pos o]
      constructor
      · intro h; cases h
      · rintro ⟨⟨_, _, _, h⟩, _⟩; exact absurd h o

theorem verdict : VerdictStatement := by
  intro config funds reserve written recipient amount
  refine ⟨?_, ?_, ?_, transferVerdict_settled_iff⟩
  · rintro ⟨a, b, c, o⟩ short
    unfold transferVerdict
    rw [if_neg (by rintro (h | h | h) <;> contradiction), if_neg (not_not.mpr o), if_neg (by omega)]
  · intro r
    unfold transferVerdict
    rw [if_pos r]
  · intro r closed
    unfold transferVerdict
    rw [if_neg (by rintro (h | h | h) <;> simp_all), if_pos closed]

set_option backward.isDefEq.respectTransparency false in
/-- How a yield commits a transfer Plan: by the verdict, at the settled await's reserve. -/
theorem commitYield_transfer {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat} {checkpoint : Digest}
    {current : Option ObjectState} {viewed : Bool} {write : Data} {recipient : AccountId} {amount : Nat}
    {funds : Funds} {reserve : Await → Nat} {written : Option StateWritten}
    (patient : 1 ≤ config.maxPatience) (narrow : height + 1 < 256 ^ 8) (effects : funds.effects = true)
    (wrote : stateWrite config snapshot object current viewed write = .ok written) :
    commitYield config snapshot height transaction cell object generation checkpoint current viewed
        (transferPlan write recipient amount) funds reserve =
      match transferVerdict config funds (reserve (decidedAwait cell generation checkpoint height .settled)) written
          recipient amount with
      | .settled => .ok ⟨decidedAwait cell generation checkpoint height .settled, written,
          (written.map StateWritten.post).toList, some (recipient, amount)⟩
      | .refused reason => .ok ⟨decidedAwait cell generation checkpoint height (.refused reason), none, [], none⟩ := by
  unfold commitYield
  simp only [transferPlan]
  rw [if_neg (by omega), if_neg (by omega), wrote]
  simp only [effects, Bool.not_true, Bool.false_eq_true, if_false]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- How a yield commits a commit Plan: settled, with its write. -/
theorem commitYield_commit {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat} {checkpoint : Digest}
    {current : Option ObjectState} {viewed : Bool} {write : Data}
    {funds : Funds} {reserve : Await → Nat} {written : Option StateWritten}
    (patient : 1 ≤ config.maxPatience) (narrow : height + 1 < 256 ^ 8) (effects : funds.effects = true)
    (wrote : stateWrite config snapshot object current viewed write = .ok written) :
    commitYield config snapshot height transaction cell object generation checkpoint current viewed
        (commitPlan write) funds reserve =
      .ok ⟨decidedAwait cell generation checkpoint height .settled, written, (written.map StateWritten.post).toList,
        none⟩ := by
  unfold commitYield
  simp only [commitPlan]
  rw [if_neg (by omega), if_neg (by omega), wrote]
  simp only [effects, Bool.not_true, Bool.false_eq_true, if_false]
  rfl

theorem performed : PerformedStatement := by
  intro rootBytes config snapshot height transaction cell object generation checkpoint current viewed write
    recipient amount funds reserve written patient narrow effects wrote admissible covered
  have settled := transferVerdict_settled_iff.mpr ⟨admissible, covered⟩
  rw [commitYield_transfer patient narrow effects wrote, settled]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem refused : RefusedStatement := by
  intro rootBytes config snapshot height transaction cell object generation checkpoint current viewed write
    recipient amount funds reserve written reason patient narrow effects wrote decided
  rw [commitYield_transfer patient narrow effects wrote, decided]

theorem transferMoves : TransferMovesStatement := by
  intro book source recipient asset amount distinct
  have other : (recipient, asset) ≠ (source, asset) := fun h => distinct (congrArg Prod.fst h).symm
  have other' : (source, asset) ≠ (recipient, asset) := fun h => distinct (congrArg Prod.fst h)
  simp only [Operation.apply, Operation.posting, Operation.leaseRecord?, Operation.floorSetting?, Book.applyPosting,
    Book.balance, DFinsupp.coe_add, Pi.add_apply, DFinsupp.single_apply, other, other', if_true, if_false]
  constructor <;> simp <;> omega

/-- A committed yield whose await was refused wrote, posted and moved nothing. -/
theorem commitYield_refused_shape {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {transaction : TransactionId} {cell object : CellId} {generation : Nat} {checkpoint : Digest}
    {current : Option ObjectState} {viewed : Bool} {plan : PlanAwait} {funds : Funds} {reserve : Await → Nat}
    {committed : YieldCommit} {reason : EffectRefusal}
    (ok : commitYield config snapshot height transaction cell object generation checkpoint current viewed plan funds
      reserve = .ok committed)
    (source : committed.await.source = .performed (.refused reason)) :
    committed.written = none ∧ committed.posts = [] ∧ committed.effect = none := by
  unfold commitYield at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · split at ok
      · cases ok
      · split at ok
        · split at ok
          · cases ok
          · simp only [Except.ok.injEq] at ok; subst ok; cases source
        · split at ok
          · cases ok
          · simp only [Except.ok.injEq] at ok; subst ok; cases source
        · split at ok
          · cases ok
          · split at ok
            · simp only [Except.ok.injEq] at ok; subst ok; cases source
            · split at ok
              · simp only [Except.ok.injEq] at ok; subst ok; cases source
              · simp only [Except.ok.injEq] at ok; subst ok; exact ⟨rfl, rfl, rfl⟩

/-- An admitted delivery's yield commit is its segment's commit under the delivery's funds. -/
theorem delivery_commit {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {request : DeliverRequest} (delivery : Delivery config snapshot height request)
    {committed : YieldCommit} (yielded : delivery.yielded = some committed) :
    delivery.segment.yields = true ∧
      ∃ state plan funds reserve, delivery.segment = .yielded state plan ∧
        commitYield config snapshot height (deliveryTransaction delivery.await.id) request.record
          delivery.record.object (delivery.record.generation + 1)
          (checkpointDigest (checkpointBytes state)) (some delivery.view) true plan funds reserve = .ok committed := by
  have commit := resumedSegment_commit delivery.endExact
  rw [yielded] at commit
  obtain ⟨state, plan, isYield, committedExact⟩ := segmentCommit_spec commit
  refine ⟨by rw [isYield]; rfl, state, plan, _, _, isYield, committedExact⟩

theorem deliveryPerformed : DeliveryPerformedStatement := by
  intro rootBytes config snapshot height request delivery committed recipient amount yielded effect
  obtain ⟨yields, _⟩ := delivery_commit delivery yielded
  have settled := settlePurse_yields _ _ _ _ _ _ _ _ yields delivery.batchExact
  refine ⟨?_, delivery.conserves⟩
  rw [delivery.postedBatch, settled.1]
  simp only [effectOps, yielded, effect]

theorem deliveryRefused : DeliveryRefusedStatement := by
  intro rootBytes config snapshot height request delivery committed reason yielded source
  obtain ⟨yields, state, plan, funds, reserve, _, ok⟩ := delivery_commit delivery yielded
  obtain ⟨noWrite, noPosts, noEffect⟩ := commitYield_refused_shape ok source
  have settled := settlePurse_yields _ _ _ _ _ _ _ _ yields delivery.batchExact
  refine ⟨?_, noWrite, noPosts⟩
  rw [delivery.postedBatch, settled.1]
  simp only [effectOps, yielded, noEffect, Option.bind_some, noWrite]

theorem commitJudged : CommitJudgedStatement := by
  intro rootBytes config snapshot height request delivery state write committed written _ yielded writes
  exact judgeWritten_ok delivery.judged written (by rw [yielded]; exact writes)

theorem resumed : ResumedStatement := by
  refine ⟨?_, ?_⟩
  · intro rootBytes config snapshot height cell await verdict source
    unfold settle
    rw [source]
  · intro rootBytes config snapshot height request delivery verdict source
    have settledEq := delivery.settled
    unfold settle at settledEq
    rw [source] at settledEq
    have decided : delivery.settlement.decided = verdict.outcome := by
      rw [← Except.ok.inj settledEq]
    exact ⟨decided, decided ▸ delivery.resumeExact⟩

/-! ### The poles, proved -/

theorem poleBook_purse : purse poleBook poleAsset polePurse = 10 := by
  simp [purse, poleBook, Book.balance, polePurse, poleAsset]

theorem poleBook_payer_open : polePayer ∈ poleBook.accounts := by
  simp [poleBook, polePayer, polePurse]

theorem pole_unviewed_keep {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (object : CellId) (state : ObjectState) :
    stateWrite config snapshot object (some state) true (.record []) = .ok none := rfl

theorem premiseInhabited : PremiseInhabitedPole := by
  rintro config base written settledAwait ⟨asset, collectorPurse, collectorPayer, _⟩
  refine ⟨⟨show polePayer ≠ polePurse by decide, Ne.symm collectorPayer,
    show polePayer ≠ config.asset by rw [asset]; decide, poleBook_payer_open⟩, ?_⟩
  show 1 + poleReserve settledAwait ≤ purse poleBook config.asset polePurse
  rw [asset, poleBook_purse]
  show 1 + 3 ≤ 10
  decide

theorem satisfiable : SatisfiablePole := by
  intro rootBytes config snapshot height transaction cell object generation checkpoint state base view
    pole narrow
  have patient := pole.2.2.2
  have wrote := pole_unviewed_keep config snapshot object state
  refine ⟨⟨_, commitYield_commit patient narrow rfl wrote, rfl, rfl⟩, ?_⟩
  obtain ⟨admissible, covered⟩ := premiseInhabited config base none
    (decidedAwait cell generation checkpoint height .settled) pole
  have settled := transferVerdict_settled_iff.mpr ⟨admissible, covered⟩
  have committed := commitYield_transfer (recipient := polePayer) (amount := 1) (reserve := poleReserve)
    (transaction := transaction) (cell := cell) (generation := generation) (checkpoint := checkpoint)
    patient narrow (show (poleFunds base).effects = true from rfl) wrote
  rw [settled] at committed
  refine ⟨_, committed, rfl, by simp [effectOps, pole.1], ⟨.resumed, .settled, [], [], []⟩, ?_, rfl⟩
  exact (resumed.1 config snapshot height cell _ .settled rfl)

theorem teeth : TeethPole := by
  intro rootBytes config snapshot height transaction cell object generation checkpoint state base pole narrow
  have patient := pole.2.2.2
  have wrote := pole_unviewed_keep config snapshot object state
  refine ⟨?_, ?_, rfl⟩
  · rw [refused config snapshot height transaction cell object generation checkpoint (some state) true (.record [])
      polePayer 8 (poleFunds base) poleReserve none .unfunded patient narrow rfl wrote]
    obtain ⟨admissible, _⟩ := premiseInhabited config base none
      (decidedAwait cell generation checkpoint height .settled) pole
    apply (verdict config (poleFunds base) 3 none polePayer 8).1 admissible
    show purse poleBook config.asset polePurse < 8 + 3
    rw [pole.1, poleBook_purse]; decide
  · rw [refused config snapshot height transaction cell object generation checkpoint (some state) true (.record [])
      polePurse 1 (poleFunds base) poleReserve none .reserved patient narrow rfl wrote]
    exact (verdict config (poleFunds base) 3 none polePurse 1).2.1 (.inl rfl)

/-! ### The audited additions, proved -/

theorem fee_balances (book : Book) (payer collector : AccountId) (asset : AssetId) (amount : Nat)
    (key : AccountId × AssetId) :
    ((Operation.fee payer collector asset amount).apply book).balances key =
      book.balances key + (if key = (payer, asset) then -(Int.ofNat amount) else 0) +
        (if key = (collector, asset) then Int.ofNat amount else 0) := by
  simp only [Operation.apply, Operation.posting, Operation.leaseRecord?, Operation.floorSetting?,
    Book.applyPosting, DFinsupp.coe_add, Pi.add_apply, DFinsupp.single_apply]
  split <;> split <;> simp_all [eq_comm]

theorem applyOperations_accounts (book : Book) (operations : List Operation) :
    (applyOperations book operations).accounts = book.accounts := by
  induction operations generalizing book with
  | nil => rfl
  | cons operation rest ih => simp only [applyOperations, ih, Operation.apply_accounts]

theorem fundsAgree : FundsAgreeStatement := by
  refine ⟨?_, fun config snapshot request book cell written => ⟨rfl, rfl⟩⟩
  intro rootBytes config snapshot height request delivery written
  obtain ⟨accountApart, collectorApart⟩ := delivery.purseApart
  refine ⟨rfl, ?_, ?_⟩
  · simp only [deliveryFunds, purseCharges, deliveryCharges, Batch.apply, registerAccounts, deregisterAccounts,
      purse, Book.balance]
    congr 1
    split <;> split <;>
      simp [applyOperations, fee_balances, accountApart, collectorApart, Ne.symm accountApart,
        Ne.symm collectorApart] <;> omega
  · simp only [deliveryFunds, deliveryCharges, Batch.apply, registerAccounts, deregisterAccounts,
      applyOperations_accounts, deregisterAccounts_accounts, List.foldl]

/-- The records a yield stores for two verdicts differ only in the verdict. -/
theorem encodeRecord_length_verdict (base : Record) (generation : Nat) (state : State) (plan : PlanAwait)
    (id : Digest) (deadline yieldedAt : Nat) (verdict verdict' : Verdict)
    (written written' : Option StateWritten) (posts posts' : List Post) (effect effect' : Option (AccountId × Nat)) :
    (encodeRecord (nextRecord base generation (.yielded state plan)
        (some ⟨⟨id, .performed verdict, deadline, yieldedAt⟩, written, posts, effect⟩))).length =
      (encodeRecord (nextRecord base generation (.yielded state plan)
        (some ⟨⟨id, .performed verdict', deadline, yieldedAt⟩, written', posts', effect'⟩))).length := by
  let one := nextRecord base generation (.yielded state plan)
    (some ⟨⟨id, .performed verdict, deadline, yieldedAt⟩, written, posts, effect⟩)
  let two := nextRecord base generation (.yielded state plan)
    (some ⟨⟨id, .performed verdict', deadline, yieldedAt⟩, written', posts', effect'⟩)
  have masks : one.mask = two.mask := by
    simp [one, two, nextRecord, Record.mask, Phase.mask, Await.mask, Source.mask]
  have fitsIff : one.Fits ↔ two.Fits := by
    simp [one, two, nextRecord, Record.Fits, Record.DigestsFit, Phase.Fits, Await.Fits, Source.Fits]
  show (encodeRecord one).length = (encodeRecord two).length
  by_cases fits : one.Fits
  · rw [← encodeRecord_length_mask one fits, ← encodeRecord_length_mask two (fitsIff.mp fits), masks]
  · have fits' : ¬ two.Fits := fun h => fits (fitsIff.mpr h)
    unfold encodeRecord
    rw [dif_neg fits, dif_neg fits']

theorem depositIndependent : DepositIndependentStatement := by
  intro config base generation state plan id deadline yieldedAt verdict verdict' written written' posts posts'
    effect effect'
  have lengths := encodeRecord_length_verdict base generation state plan id deadline yieldedAt verdict verdict'
    written written' posts posts' effect effect'
  simp only [storageDeposit, nextRecord] at lengths ⊢
  rw [lengths]

theorem birthCommitJudged : BirthCommitJudgedStatement := by
  intro rootBytes config snapshot height request born state write committed written _ yielded writes
  exact judgeWritten_ok born.judged written (by rw [yielded]; exact writes)

theorem deliverLawRefuses : DeliverLawRefusesStatement := by
  intro rootBytes config snapshot height request head object tail book segment yielded reason
    hHead hObject hRuns hTail hCovered hHeap hExtract hTried hBook hApart hEnd hJudge
  unfold deliver
  split
  · rename_i h; rw [hHead] at h; cases h
  rename_i head' h
  rw [hHead] at h; cases h
  dsimp only
  split
  · rename_i h; rw [hObject] at h; cases h
  · rename_i h; rw [hObject] at h; cases h
  rename_i object' h
  rw [hObject] at h; cases h
  rw [dif_pos hRuns]
  split
  · rename_i h; rw [hTail] at h; cases h
  rename_i tail' h
  rw [hTail] at h; cases h
  rw [dif_pos hCovered, dif_pos hHeap, dif_pos hExtract, if_neg hTried]
  split
  · rename_i h; rw [hBook] at h; cases h
  rename_i book' h
  rw [hBook] at h; cases h
  rw [dif_pos hApart]
  split
  · rename_i h; rw [hEnd] at h; cases h
  rename_i segment' yielded' h
  rw [hEnd] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  split
  · rename_i h; rw [hJudge] at h; cases h; rfl
  · rename_i h; rw [hJudge] at h; cases h

theorem commitWrites : CommitWritesPole := by
  intro rootBytes config snapshot height transaction cell object generation checkpoint version base pole narrow
  have wrote : stateWrite config snapshot object (some ⟨version, .record [("n", .natural 0)]⟩) true
      (.record [("n", .variant "add" (.natural 1))]) =
      .ok (some ⟨some ⟨version, .record [("n", .natural 0)]⟩, ⟨version + 1, .record [("n", .natural 1)]⟩,
        postAt snapshot (stateCell config.domain object) (stateImage object ⟨version + 1, .record [("n", .natural 1)]⟩)⟩) := by
    rfl
  exact ⟨_, _, commitYield_commit pole.2.2.2 narrow rfl wrote, rfl, rfl, rfl⟩

theorem commitLawRefused : CommitLawRefusedPole := by
  intro post
  cases h : admitWrite ObjectRecord.teethSeedRecord (factsOf ⟨40⟩ 5 ⟨1⟩ 2 (some ⟨7⟩)) none (.natural 6) with
  | ok _ =>
    have refusedByLaw : ObjectRecord.accepted
        (admitWrite ObjectRecord.teethSeedRecord (factsOf ⟨40⟩ 5 ⟨1⟩ 2 (some ⟨7⟩)) none (.natural 6)) = false := by
      decide +kernel
    rw [h] at refusedByLaw; cases refusedByLaw
  | error reason => exact ⟨reason, by simp [judgeWritten, judgeWrite, h]⟩

/-- info: 'Minidregg.Kernel.ObjectiveActivityEffect.performed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms performed
#assert_axioms performed
#assert_axioms deliveryPerformed
#assert_axioms transferMoves
#assert_axioms refused
#assert_axioms verdict
#assert_axioms deliveryRefused
#assert_axioms commitJudged
#assert_axioms resumed
#assert_axioms satisfiable
#assert_axioms teeth
#assert_axioms premiseInhabited
#assert_axioms fundsAgree
#assert_axioms depositIndependent
#assert_axioms birthCommitJudged
#assert_axioms deliverLawRefuses
#assert_axioms commitWrites
#assert_axioms commitLawRefused

end Minidregg.Kernel.ObjectiveActivityEffect
