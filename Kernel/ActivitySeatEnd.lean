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
(`Joined.conserves`) and every held open seat is closed (`Joined.closes`). The
turn's Book post is the joint batch's post (`Joined.rewrite` replaces the
activity's own Book post), and the seat cells the closing changed are written
in the same intent.

An activity with no holdings is untouched: `join` returns `none` and the turn
is exactly the activity kernel's.
-/
import Kernel.SeatStore

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
  obtain ⟨_, heldPosts, none, _⟩ := held.closes
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
open on the loaded seat cells is closed in the seat cells the turn writes, and
the Book the turn writes is the activity's batch followed by the seat closing,
admitted together on the loaded Book. -/
theorem Joined.closes {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height record : Nat} {pre : BookCell} {posted : Postings pre}
    (joined : Joined config snapshot height record posted) :
    (∀ seat ∈ heldOpen (joined.held.loaded.world (posted.batch.apply (logicalBook pre.logical))) record,
        ∀ after ∈ joined.held.next.seats, after.account = seat.account → after.isOpen = false) ∧
      Posts (logicalBook pre.logical) (seqBatch posted.batch joined.held.batch) joined.held.next.book ∧
      logicalBook joined.accepted.post.logical = joined.held.next.book := by
  obtain ⟨closes, heldPosts, none, _⟩ := joined.held.closes
  have joint := Posts.seq ⟨posted.accepted.admission, rfl⟩ heldPosts none
  refine ⟨closes, joint, ?_⟩
  rw [AcceptedBatch.post_logicalBook]
  exact joint.2.symm

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
delivery whose record is no longer awaiting (done or faulted), and every
abandonment. Other turns end nothing. -/
def AdmittedTurn.ending {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} :
    AdmittedTurn config snapshot height → Option (Nat × Σ pre : BookCell, Postings pre)
  | .birth _ born => match born.record.phase with
    | .awaiting _ => none
    | _ => some (born.cell.value, ⟨born.book, born.posted⟩)
  | .deliver request delivery => match delivery.next.phase with
    | .awaiting _ => none
    | _ => some (request.record.value, ⟨delivery.book, delivery.posted⟩)
  | .abandon request abandoned => some (request.record.value, ⟨abandoned.book, abandoned.posted⟩)
  | _ => none

/-- The turn's final posts and extra guards: the kernel's own, or, when the turn
ends an activity that holds seats, the joint turn (`Joined.rewrite`). -/
def finalize {rootBytes : Bytes → Digest} (config : Config) (snapshot : Snapshot rootBytes)
    (height : Nat) (turn : AdmittedTurn config snapshot height) :
    Except SeatStore.Refusal (List Post × List ReadGuard) :=
  match turn.ending with
  | none => .ok (turn.posts, [])
  | some (record, ⟨_, posted⟩) =>
    match join config snapshot height record posted with
    | .error reason => .error reason
    | .ok none => .ok (turn.posts, [])
    | .ok (some joined) => .ok (joined.rewrite turn.posts, joined.held.guards)

/-- The intent of an admitted turn over final posts and extra guards (an ending
turn's own transaction, guards and claims). -/
def AdmittedTurn.finalIntent {rootBytes : Bytes → Digest} {config : Config} {snapshot : Snapshot rootBytes}
    {height : Nat} (sealing : Seal) (posts : List Post) (extra : List ReadGuard) :
    AdmittedTurn config snapshot height → DataIntent rootBytes
  | .birth request born =>
      ObjectiveActivity.intentOf rootBytes (ObjectiveActivity.birthTransaction request) posts
        (born.guards ++ extra) [] sealing
  | .deliver _ delivery =>
      ObjectiveActivity.intentOf rootBytes (ObjectiveActivity.deliveryTransaction delivery.await.id) posts
        (delivery.guards ++ extra) delivery.claims sealing
  | .abandon _ abandoned =>
      ObjectiveActivity.intentOf rootBytes (ObjectiveActivity.abandonTransaction abandoned.await.id) posts extra
        abandoned.claims sealing
  | turn => turn.intent sealing

#assert_axioms joint_admission Joined.conserves Joined.closes join_none

end Minidregg.Kernel.ActivitySeatEnd
