/-
# Kernel.ActivitySeatEnd — an ending activity closes the seats it holds, in the same turn

A seat may name an activity as its holder (`Seats.Seat.holder`, the activity's
record cell; only that activity's escrow payer may name it, while it awaits).
When the activity ENDS (its birth or a delivery finishes or faults, or it is
abandoned), the seats it holds are exited in that very turn: the kernel's own
`Seats.closeHeld` on the activity's holdings (`SeatStore.endHeld`) pays every
open held seat's whole allocation to its payee.

The ending turn stays ONE Book batch: the activity's own batch `b` (its fees,
its purse settlement) followed by the seat batch, admitted together on the
loaded Book (`Seats.Posts.seq`), so the turn conserves every asset
(`Joined.conserves`) and every held seat is closed (`Joined.closes`): swept to its
payee in every asset it holds, its Book account deregistered in the same batch,
removed from the world, its cell retired (`Joined.retires`). The
turn's Book post is the joint batch's post (`Joined.rewrite` replaces the
activity's own Book post), and the seat cells the closing changed are written
in the same intent.

An activity with no holdings is untouched: `join` returns `none` and the turn
is exactly the activity kernel's.
-/
import Kernel.SeatStore
import Kernel.ObjectiveAdmittedTurn

namespace Minidregg.Kernel.ActivitySeatEnd

open Minidregg.Theory Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.ObjectiveActivityWire
open Minidregg.Compiler.ResourceBirthCodec (LifecycleImage)
open Minidregg.Theory.CanonicalResourceKernel (Book Batch AccountId AssetId logicalBook AcceptedBatch)
open Minidregg.Kernel.ObjectiveActivity (Config BookCell Postings postAt)
open Minidregg.Kernel.Seats

set_option autoImplicit false

abbrev Snapshot (rootBytes : Bytes → Digest) := DataSnapshot rootBytes

/-- An activity turn's own Book side joined with the closing of the seats its
activity holds. -/
structure Joined {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height record : Nat) {pre : BookCell} (posted : Postings pre) where
  private mk ::
  held : SeatStore.HeldEnd config.domain snapshot height record (posted.batch.apply (logicalBook pre.logical))
  accepted : AcceptedBatch pre (seqBatch posted.batch held.batch)

theorem joint_admission {rootBytes : Bytes → Digest} {domain : Digest} {snapshot : Snapshot rootBytes}
    {height record : Nat} {pre : BookCell} (posted : Postings pre)
    (held : SeatStore.HeldEnd domain snapshot height record (posted.batch.apply (logicalBook pre.logical))) :
    (seqBatch posted.batch held.batch).Admission (logicalBook pre.logical) := by
  obtain ⟨_, _, heldPosts, none, _⟩ := held.closes
  exact (Posts.seq ⟨posted.accepted.admission, rfl⟩ heldPosts none).1

/-- Join an activity turn's postings with the closing of its held seats; `none`
when the activity holds no seat. -/
def join {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes) (height record : Nat)
    {pre : BookCell} (posted : Postings pre) :
    Except SeatStore.Refusal (Option (Joined config snapshot height record posted)) := do
  if (SeatStore.readHoldings snapshot config.domain record).isEmpty then return none
  let held ← SeatStore.endHeld config.domain snapshot height record (posted.batch.apply (logicalBook pre.logical))
  pure (some ⟨held, AcceptedBatch.ofAdmission (joint_admission posted held)⟩)

/-- The joint batch's Book post. -/
def Joined.bookPost {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height record : Nat} {pre : BookCell} {posted : Postings pre}
    (joined : Joined config snapshot height record posted) : Post :=
  postAt snapshot config.bookCell
    (LifecycleImage.bytes CanonicalCellRegistry.registry (.live ⟨.resourceBook, joined.accepted.post⟩))

/-- The ending turn's posts: the activity's own, its Book post replaced by the
joint batch's, then the seat cells the closing changed. -/
def Joined.rewrite {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height record : Nat} {pre : BookCell} {posted : Postings pre}
    (joined : Joined config snapshot height record posted) (posts : List Post) : List Post :=
  posts.map (fun post => if post.cell = config.bookCell then joined.bookPost else post) ++ joined.held.posts

/-- **The joint turn conserves every asset**: the activity's batch and the seat
closing are one admitted batch on the loaded Book. -/
theorem Joined.conserves {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height record : Nat} {pre : BookCell} {posted : Postings pre}
    (joined : Joined config snapshot height record posted) (asset : AssetId) :
    (logicalBook joined.accepted.post.logical).totalAsset asset = (logicalBook pre.logical).totalAsset asset :=
  joined.accepted.conserves asset

/-- **An ending activity closes every seat it holds**: every held seat that was
open on the loaded seat cells is gone from the world the turn writes, and
the Book the turn writes is the activity's batch followed by the seat closing,
admitted together on the loaded Book. -/
theorem Joined.closes {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height record : Nat} {pre : BookCell} {posted : Postings pre}
    (joined : Joined config snapshot height record posted) :
    (∀ seat ∈ heldOpen (joined.held.loaded.world (posted.batch.apply (logicalBook pre.logical))) height record,
        ∀ after ∈ joined.held.next.seats, after.account ≠ seat.account) ∧
      Posts (logicalBook pre.logical) (seqBatch posted.batch joined.held.batch) joined.held.next.book ∧
      logicalBook joined.accepted.post.logical = joined.held.next.book := by
  obtain ⟨closes, _, heldPosts, none, _⟩ := joined.held.closes
  have joint := Posts.seq ⟨posted.accepted.admission, rfl⟩ heldPosts none
  refine ⟨closes, joint, ?_⟩
  rw [AcceptedBatch.post_logicalBook]
  exact joint.2.symm

/-- **An ending activity deregisters the accounts of the seats it closes**: after the joint
batch no closed seat's account is a Book account. -/
theorem Joined.deregisters {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height record : Nat} {pre : BookCell} {posted : Postings pre}
    (joined : Joined config snapshot height record posted) :
    ∀ seat ∈ heldOpen (joined.held.loaded.world (posted.batch.apply (logicalBook pre.logical))) height record,
      seat.account ∉ (logicalBook joined.accepted.post.logical).accounts := by
  obtain ⟨_, gone, _⟩ := joined.held.closes
  obtain ⟨_, _, equal⟩ := joined.closes
  intro seat member
  rw [equal]
  exact gone seat member

/-- **An ending activity retires the seat cells it closes**: the turn's final posts include each
closed seat's cell at the retired image. -/
theorem Joined.retires {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height record : Nat} {pre : BookCell} {posted : Postings pre}
    (joined : Joined config snapshot height record posted) (posts : List Post) :
    ∀ seat ∈ heldOpen (joined.held.loaded.world (posted.batch.apply (logicalBook pre.logical))) height record,
      postAt snapshot (SeatStore.seatCell seat.account) ObjectiveActivity.retiredImage ∈ joined.rewrite posts := by
  intro seat member
  exact List.mem_append_right _ (joined.held.retires seat member)

/-- `join` is `none` only for an activity whose holdings cell lists no seat. -/
theorem join_none {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height record : Nat} {pre : BookCell} {posted : Postings pre}
    (joined : join config snapshot height record posted = .ok none) :
    SeatStore.readHoldings snapshot config.domain record = [] := by
  unfold join at joined
  by_cases empty : (SeatStore.readHoldings snapshot config.domain record).isEmpty = true
  · exact List.isEmpty_iff.mp empty
  · simp only [empty, Bool.false_eq_true, if_false] at joined
    cases h : SeatStore.endHeld config.domain snapshot height record
        (posted.batch.apply (logicalBook pre.logical)) with
    | error reason => rw [h] at joined; cases joined
    | ok held => rw [h] at joined; cases joined


/-! ## An ending turn's final posts

The activity kernel's admitted turn (`ObjectiveActivity.AdmittedTurn`) and the
turn the receiver commits differ only when the turn ENDS an activity that holds
seats: then the committed posts are the joint ones (`Joined.rewrite`) and the
intent carries the seat cells' guards as well. These are stated here, on the
kernel's turn, so the checkpoint invariant and the receiver share one
definition. -/

open Minidregg.Kernel.ObjectiveActivity (AdmittedTurn)

/-- The activity a turn ENDS, with its loaded Book and its postings: a birth or a
delivery whose record is no longer awaiting (done or faulted), every
abandonment, every abort after a drain deadline, and the old activity of every
rebirth. Other turns end nothing. -/
def AdmittedTurn.ending {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} :
    AdmittedTurn config snapshot height → Option (Nat × Σ pre : BookCell, Postings pre)
  | .birth _ _ born => match born.record.phase with
    | .awaiting _ => none
    | _ => some (born.cell.value, ⟨born.book, born.posted⟩)
  | .deliver request delivery => match delivery.next.phase with
    | .awaiting _ => none
    | _ => some (request.record.value, ⟨delivery.book, delivery.posted⟩)
  | .abandon request abandoned => some (request.record.value, ⟨abandoned.book, abandoned.posted⟩)
  | .abortDrained request aborted => some (request.record.value, ⟨aborted.book, aborted.posted⟩)
  | .rebirth request reborn => some (request.record.value, ⟨reborn.born.book, reborn.born.posted⟩)
  | _ => none

/-- The turn's final posts and extra guards: the kernel's own, or, when the turn
ends an activity that holds seats, the joint turn (`Joined.rewrite`). -/
def finalize {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (turn : AdmittedTurn config snapshot height) :
    Except SeatStore.Refusal (List Post × List ReadGuard) :=
  match AdmittedTurn.ending turn with
  | none => .ok (turn.posts, [])
  | some (record, ⟨_, posted⟩) =>
    match join config snapshot height record posted with
    | .error reason => .error reason
    | .ok none => .ok (turn.posts, [])
    | .ok (some joined) => .ok (joined.rewrite turn.posts, joined.held.guards)

/-- The units of domain judgment a turn's charged envelope declares (`Capacity.domainWork`):
the envelope whose public price (`Tariff.workOf`) the turn, or the turn that escrowed for it,
was charged. No wildcard: a new turn says what it paid for.
* `invoke`, `birth`, `adopt`, `rebirth`, `registerDomain`: the request's envelope (its fee is
  charged in the turn; a rebirth's from the old purse);
* `deliver`, `exhaust`, `abortDrained`: the turn's envelope (the escrowed envelope plus `extra`,
  each paid: the escrow at the yield, `extra` in the turn);
* `deliverMessage`: the message's envelope (paid as postage by the sending invocation);
* `migrate`: the adopted envelope when the migration runs a term (`migrateFee` charges it),
  else nothing;
* `publish`, `create`, `resolve`, `topUp`, `abandon`: nothing (no envelope is charged). -/
def AdmittedTurn.domainAllowance {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} : AdmittedTurn config snapshot height → Nat
  | .publish _ _ => 0
  | .create _ _ => 0
  | .birth request _ _ => request.envelope.domainWork
  | .resolve _ _ => 0
  | .deliver _ delivery => delivery.envelope.domainWork
  | .topUp _ _ => 0
  | .exhaust _ exhausted => exhausted.envelope.domainWork
  | .abandon _ _ => 0
  | .invoke request _ => request.envelope.domainWork
  | .deliverMessage _ delivered => delivered.message.envelope.domainWork
  | .adopt request _ => request.envelope.domainWork
  | .migrate _ migrated => if migrated.next.migration.isSome then migrated.next.envelope.domainWork else 0
  | .abortDrained _ aborted => aborted.envelope.domainWork
  | .rebirth request _ => request.envelope.domainWork
  | .registerDomain request _ => request.envelope.domainWork

/-- **A turn's end**: the seat join (`finalize`), then the invariant-domain judgment on the
final posts (`ObjectiveActivity.judgeDomains`): every domain of every object whose state the
turn writes must hold on the members' final states, and the judgment's units of work must fit
the turn's declared allowance (`domainUncovered`). The domain judgment adds read guards and
never changes the posts. -/
inductive EndRefusal where
  | seats (reason : SeatStore.Refusal)
  | kernel (reason : ObjectiveActivity.Refusal)
  deriving Repr

def finish {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (turn : AdmittedTurn config snapshot height) :
    Except EndRefusal (List Post × List ReadGuard) :=
  match finalize config snapshot height turn with
  | .error reason => .error (.seats reason)
  | .ok (posts, extra) =>
    match ObjectiveActivity.judgeDomains config snapshot posts with
    | .error reason => .error (.kernel reason)
    | .ok (guards, units) =>
      if units ≤ (AdmittedTurn.domainAllowance turn) then .ok (posts, extra ++ guards)
      else .error (.kernel (.domainUncovered units (AdmittedTurn.domainAllowance turn)))

theorem finish_finalize {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {turn : AdmittedTurn config snapshot height} {posts : List Post} {extra : List ReadGuard}
    (finished : finish config snapshot height turn = .ok (posts, extra)) :
    ∃ seats domains units, finalize config snapshot height turn = .ok (posts, seats) ∧
      ObjectiveActivity.judgeDomains config snapshot posts = .ok (domains, units) ∧
      units ≤ (AdmittedTurn.domainAllowance turn) ∧ extra = seats ++ domains := by
  unfold finish at finished
  split at finished
  · cases finished
  · rename_i final_ seats final
    split at finished
    · cases finished
    · rename_i domains units judged
      split at finished
      · rename_i covered
        simp only [Except.ok.injEq, Prod.mk.injEq] at finished
        obtain ⟨rfl, rfl⟩ := finished
        exact ⟨seats, domains, units, final, judged, covered, rfl⟩
      · cases finished

/-- The intent of an admitted turn over final posts and extra guards: the turn's own
transaction, guards and claims, with the extra guards (an ending turn's seat cells, the domain
judgment's reads) for EVERY turn. No wildcard: a new turn says what its intent is. -/
def AdmittedTurn.finalIntent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} (sealing : Seal) (posts : List Post) (extra : List ReadGuard) :
    AdmittedTurn config snapshot height → DataIntent rootBytes
  | .publish _ publication =>
      intentOf rootBytes (ObjectiveActivity.publishTransaction publication.pin) posts
        (publication.guards ++ extra) [] sealing
  | .create request _ =>
      intentOf rootBytes (ObjectiveActivity.createTransaction request) posts
        ([ObjectiveActivity.guardAt snapshot (ObjectiveActivity.packageCell config.domain request.pin),
          ObjectiveActivity.guardAt snapshot (ObjectiveActivity.stateCell config.domain request.object)] ++ extra)
        [] sealing
  | .birth request _ born =>
      intentOf rootBytes (ObjectiveActivity.birthTransaction request) posts
        (born.guards ++ extra) [] sealing
  | .resolve request resolution =>
      intentOf rootBytes (ObjectiveActivity.resolveTransaction request.slot) posts
        ([ObjectiveActivity.guardAt snapshot resolution.slot.activity] ++ extra)
        [AnswerSlot.decisionClaim request.slot] sealing
  | .deliver _ delivery =>
      intentOf rootBytes (ObjectiveActivity.deliveryTransaction delivery.await.id) posts
        (delivery.guards ++ extra) delivery.claims sealing
  | .topUp request _ =>
      intentOf rootBytes (ObjectiveActivity.topUpTransaction request) posts
        ([ObjectiveActivity.guardAt snapshot request.record] ++ extra) [] sealing
  | .exhaust request exhausted =>
      intentOf rootBytes (ObjectiveActivity.exhaustTransaction exhausted.await.id request) posts
        (exhausted.guards ++ extra) [] sealing
  | .abandon _ abandoned =>
      intentOf rootBytes (ObjectiveActivity.abandonTransaction abandoned.await.id) posts extra
        abandoned.claims sealing
  | .invoke request invoked =>
      intentOf rootBytes (ObjectiveCall.invokeTransaction request) posts (invoked.guards ++ extra) [] sealing
  | .deliverMessage _ delivered =>
      intentOf rootBytes (ObjectiveSend.messageTransaction delivered.message.id) posts
        (delivered.guards ++ extra) delivered.claims sealing
  | .adopt request adopted =>
      intentOf rootBytes (ObjectiveActivity.adoptTransaction request) posts (adopted.guards ++ extra) [] sealing
  | .migrate request migrated =>
      intentOf rootBytes (ObjectiveActivity.migrateTransaction request) posts
        ([ObjectiveActivity.guardAt snapshot (ObjectiveActivity.packageCell config.domain migrated.next.pin)] ++ extra)
        [] sealing
  | .abortDrained _ aborted =>
      intentOf rootBytes (ObjectiveActivity.abortTransaction aborted.await.id) posts
        ([ObjectiveActivity.guardAt snapshot (ObjectiveActivity.packageCell config.domain aborted.record.pin),
          ObjectiveActivity.guardAt snapshot (ObjectiveActivity.stateCell config.domain aborted.record.object)] ++ extra)
        aborted.claims sealing
  | .rebirth _ reborn =>
      intentOf rootBytes (ObjectiveActivity.rebirthTransaction reborn.await.id) posts
        (reborn.born.guards ++ extra) reborn.claims sealing
  | .registerDomain request registered =>
      intentOf rootBytes (ObjectiveActivity.registerTransaction request) posts
        (registered.guards ++ extra) [] sealing

/-- A cell an intent GUARDS: a read guard on it at the snapshot's root, or the intent writes it. -/
def Guarded {rootBytes : Bytes → Digest} (snapshot : Snapshot rootBytes) (intent : DataIntent rootBytes)
    (cell : CellId) : Prop :=
  ObjectiveActivity.guardAt snapshot cell ∈ intent.readGuards ∨ cell ∈ intent.writes.map DataWrite.cellId

/-- **Every extra guard reaches the final intent**, for EVERY turn kind: it is one of the intent's
read guards, or the intent writes its cell. -/
theorem finalIntent_guards {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} (sealing : Seal) (posts : List Post) (extra : List ReadGuard)
    (turn : AdmittedTurn config snapshot height) :
    ∀ guard ∈ extra, guard ∈ (AdmittedTurn.finalIntent sealing posts extra turn).readGuards ∨
      guard.cellId ∈ (AdmittedTurn.finalIntent sealing posts extra turn).writes.map DataWrite.cellId := by
  intro guard member
  by_cases written : guard.cellId ∈ (posts.map (Post.write rootBytes)).map DataWrite.cellId
  · right
    cases turn <;> exact written
  · left
    have kept : ∀ {guards : List ReadGuard}, guard ∈ guards → guard ∈ readOnly rootBytes posts guards :=
      fun inGuards => List.mem_filter.mpr ⟨inGuards, decide_eq_true written⟩
    cases turn <;> first
      | exact kept (List.mem_append_left _ (List.mem_append_right _ member))
      | exact kept (List.mem_append_left _ member)

/-- **What an admitted turn end guarantees about invariant domains.** For every object whose
declared state the final posts can change, every domain its record (as the turn leaves it) names
exists and its law holds on ALL members' final states, and the committed intent GUARDS every cell
that judgment read (each member's state cell, the domain cell, the written object's record cell):
a concurrent turn that changes an unwritten member, or the membership, conflicts with it. -/
theorem finish_domains {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {turn : AdmittedTurn config snapshot height} {posts : List Post} {extra : List ReadGuard}
    (finished : finish config snapshot height turn = .ok (posts, extra)) (sealing : Seal) :
    ∀ object ∈ ObjectiveActivity.writtenObjects snapshot posts,
      Guarded snapshot (AdmittedTurn.finalIntent sealing posts extra turn)
        (ObjectiveActivity.objectCell config.domain object) ∧
      ∀ record, ObjectiveActivity.finalRecord config snapshot posts object = .ok (some record) →
        ∀ id ∈ record.domains, ∃ domain states, ObjectiveActivity.domainFor id
            (ObjectiveActivity.afterPosts snapshot posts (ObjectiveActivity.domainCell config.domain id)) =
            .ok (some domain) ∧
          domain.members.mapM (fun member => ObjectiveActivity.stateFor member
            (ObjectiveActivity.afterPosts snapshot posts (ObjectiveActivity.stateCell config.domain member))) =
            .ok states ∧
          (∃ joint, ObjectiveActivity.jointSlots 0 states = some joint ∧
            Minidregg.Pred.eval domain.law ⟨joint⟩ ⟨joint⟩ = true) ∧
          Guarded snapshot (AdmittedTurn.finalIntent sealing posts extra turn)
            (ObjectiveActivity.domainCell config.domain id) ∧
          ∀ member ∈ domain.members, Guarded snapshot (AdmittedTurn.finalIntent sealing posts extra turn)
            (ObjectiveActivity.stateCell config.domain member) := by
  obtain ⟨seats, domains, _, _, judged, _, rfl⟩ := finish_finalize finished
  have reach : ∀ cell, ObjectiveActivity.guardAt snapshot cell ∈ domains →
      Guarded snapshot (AdmittedTurn.finalIntent sealing posts (seats ++ domains) turn) cell := fun cell inDomains =>
    finalIntent_guards sealing posts (seats ++ domains) turn _ (List.mem_append_right _ inDomains)
  intro object written
  obtain ⟨guardObject, judgedObject⟩ := ObjectiveActivity.judgeDomains_sound judged object written
  refine ⟨reach _ guardObject, fun record found named inDomains => ?_⟩
  obtain ⟨domain, states, read, mapped, holds, guardDomain, guardStates⟩ :=
    judgedObject record found named inDomains
  have after : (fun member => ObjectiveActivity.stateFor member
      (ObjectiveActivity.afterPosts snapshot posts (ObjectiveActivity.stateCell config.domain member))) =
      ObjectiveActivity.finalState config snapshot posts :=
    funext fun member => (ObjectiveActivity.finalState_after config snapshot posts member).symm
  exact ⟨domain, states, by rw [← ObjectiveActivity.finalDomain_after]; exact read, by rw [after]; exact mapped,
    holds, reach _ guardDomain,
    fun member inMembers => reach _ (guardStates member inMembers)⟩

/-- **A finished turn paid for its domain judgment.** For every domain the turn end judged
(named by a written object's final record, or posted), the turn's declared allowance covers
that domain's `|members| + 1` reads, and the envelope's public price includes the domain rate on
the whole allowance (`Tariff.workOf_domainWork`): the payer of the charged envelope paid at least
`tariff.domainWork * (|members| + 1)` for it. -/
theorem finish_domain_covered {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} {turn : AdmittedTurn config snapshot height} {posts : List Post} {extra : List ReadGuard}
    (finished : finish config snapshot height turn = .ok (posts, extra)) :
    ∀ id, ((∃ object ∈ ObjectiveActivity.writtenObjects snapshot posts, ∃ record,
        ObjectiveActivity.finalRecord config snapshot posts object = .ok (some record) ∧ id ∈ record.domains) ∨
        id ∈ ObjectiveActivity.postedDomains snapshot posts) →
      ∃ domain, ObjectiveActivity.finalDomain config snapshot posts id = .ok (some domain) ∧
        domain.members.length + 1 ≤ (AdmittedTurn.domainAllowance turn) ∧
        config.tariff.domainWork * (domain.members.length + 1) ≤
          config.tariff.domainWork * (AdmittedTurn.domainAllowance turn) := by
  obtain ⟨_, _, units, _, judged, covered, _⟩ := finish_finalize finished
  intro id which
  obtain ⟨domain, found, counted⟩ := ObjectiveActivity.judgeDomains_units judged id which
  exact ⟨domain, found, Nat.le_trans counted covered,
    Nat.mul_le_mul_left _ (Nat.le_trans counted covered)⟩

#assert_axioms finish_domain_covered
#assert_axioms joint_admission Joined.conserves Joined.closes Joined.deregisters Joined.retires join_none finish_finalize finalIntent_guards finish_domains

end Minidregg.Kernel.ActivitySeatEnd
