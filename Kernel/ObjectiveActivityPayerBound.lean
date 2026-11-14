/-
# Kernel.ObjectiveActivityPayerBound -- what each spending activity turn takes from its account

The activity receiver bounds a spending turn twice (`Kernel.ObjectiveActivityReceiverCore`):
at the gate, the amount the command declares (`spend`), before anything runs; and after the
decision, the account's gross debit in the Book operations the decided turn posts
(`decidedBound`, `Prepared.payer_bounded`). The second is the bound on what is posted, for
every turn kind. This module says, per kind, how the two relate.

## The declared amount is the debit

* `adopt_debit`, `register_debit`, `topUp_debit` -- the account's gross debit is exactly the
  declared amount: the envelope's public price, or the top-up's amount.
* `migrate_debit` -- a migration's is the pending upgrade's fee (`migrateFee`), which the
  command does not carry. The gate reads it from the object's record before the migration
  runs (`ObjectiveActivityReceiverCore.migrationGranted`), and the decided batch is bounded
  again.
* `exhaust_debit_le` -- an exhaustion's is at most the added envelope's price, when the
  account is not the activity's own purse.

## The declared amount is NOT the debit: an invocation

`invoke_debit_exceeds`: an invocation's operations take from the account the envelope's price
AND the postage of every message the run queued (`ObjectiveCall.creditTransfers`). The command
declares the envelope; how many messages the run sends is decided by the run. So the gate's
bound on the declared envelope price does not bound an invocation's debit, and the bound that
holds is the one on the decided batch. The lemma is over any mail with one queued credit. No
admitted invocation that has one is constructed here, and none is anywhere in the tree: an
`Invocation` is built only by `ObjectiveCall.invoke`, which runs a package's method through
the evaluator over a loaded snapshot, so the smallest instance needs a snapshot holding an
object, a package whose method sends, the target's inbox and a funded Book. That fixture
exists only as the native acceptance run (`native/resource-client/objective-activity-native-acceptance.py`).
What is proved of every admitted invocation is `ObjectiveSend.Invocation.escrows_every_send`:
one credit per message the run queued, in total the declared postage price per send plus the
sends' allowances and deposits. So an admitted invocation whose run queues exactly one message,
to another purse at a positive postage price, and whose controls return nothing, satisfies
this lemma's premises.

## The turn's end

A turn that ends an activity closes the seats the activity holds, in the same Book batch
(`ActivitySeatEnd.finish`), after the receiver's bound on the decided batch. `seatEnd_debit`:
the closing adds no debit of an account that is not one of those seats, so the bound on the
decided batch is the bound on the joint batch for it. A seat's own account is swept to its
payee by the seat's terms (`Seats.closeBatch`), set when the seat was offered; that is the
seat's exit and no grant of the ending turn's signer bounds it.

## Not here

A birth (envelope price plus deposit, then the purse settles), a delivery and a drained abort
(the purse's charges, the added envelope, then the purse settles) go through `settlePurse`,
whose remaining operations are sourced at the purse. That their debit of the account is the
declared amount is not proved here; `Prepared.payer_bounded` bounds what they post.
-/
module

public import Kernel.ObjectiveAdmittedTurn
public import Kernel.ActivitySeatEnd
public import Theory.CapabilityValueBound
import all Init.Data.List.Basic

@[expose] public section

namespace Minidregg.Kernel.ObjectiveActivityPayerBound

open Minidregg.Theory
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.CapabilityValueBound
open Minidregg.Kernel.ObjectiveActivity
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

variable {rootBytes : List UInt8 → TypedAuthorization.Digest} {config : Config}
  {snapshot : Snapshot rootBytes} {height : Nat}

theorem adopt_debit {request : AdoptRequest} (adopted : Adoption config snapshot height request) :
    grossDebit adopted.posted.batch.operations request.account config.asset =
      config.tariff.workOf request.envelope := by
  rw [adopted.postedBatch]
  simp [adoptBatch, grossDebit, debits, Operation.posting]

theorem register_debit {request : RegisterRequest}
    (registered : Registration config snapshot height request) :
    grossDebit registered.posted.batch.operations request.payer config.asset =
      config.tariff.workOf request.envelope := by
  rw [registered.postedBatch]
  simp [registerBatch, grossDebit, debits, Operation.posting]

theorem topUp_debit {request : TopUpRequest} (topped : TopUp config snapshot request) :
    grossDebit topped.posted.batch.operations request.account config.asset = request.amount := by
  rw [topped.postedBatch]
  simp [grossDebit, debits, Operation.posting]

theorem migrate_debit {request : MigrateRequest} (migrated : Migrated config snapshot height request) :
    grossDebit migrated.posted.batch.operations request.account config.asset =
      migrateFee config migrated.next := by
  rw [migrated.postedBatch]
  unfold migrateBatch
  by_cases free : migrateFee config migrated.next = 0
  · simp [free, grossDebit, debits]
  · simp [free, grossDebit, debits, Operation.posting]

theorem exhaust_debit_le {request : ExhaustRequest}
    (exhausted : Exhaustion config snapshot height request)
    (apart : heldAccount request.record ≠ request.account) :
    grossDebit exhausted.posted.batch.operations request.account config.asset ≤
      config.tariff.workOf request.extra := by
  rw [exhausted.postedBatch]
  unfold exhaustCharges
  by_cases tried : exhausted.record.tried = 0 <;>
    by_cases extra : request.extra = ObjectiveTariff.zeroCapacity <;>
    simp [tried, extra, apart, grossDebit, debits, Operation.posting]

/-- **An invocation's debit exceeds its declared envelope price** by the postage of what the
run queued: with one queued credit of `postage` to another purse and nothing returned, the
account pays the envelope's price plus `postage`. -/
theorem invoke_debit_exceeds (request : ObjectiveCall.InvokeRequest)
    (mail : ObjectiveCall.Mail config snapshot) (purse : AccountId) (postage : Nat)
    (credits : mail.credits = [(purse, postage)]) (refunds : mail.refunds = [])
    (other : purse ≠ request.account) (positive : postage ≠ 0) :
    grossDebit (ObjectiveCall.invokeOperations config request mail) request.account config.asset =
      config.tariff.workOf request.envelope + postage := by
  simp [ObjectiveCall.invokeOperations, ObjectiveCall.creditTransfers, ObjectiveCall.refundTransfers,
    credits, refunds, other, positive, grossDebit, debits, Operation.posting]

/-- **A turn's end adds no debit of an account that is not a seat the ending activity holds.**
Over the joint batch the turn posts (its own, then the seat closing), such an account's gross
debit is the one in the turn's own batch, which `Prepared.payer_bounded` bounds. -/
theorem seatEnd_debit {record : Nat} {pre : BookCell} {posted : Postings pre}
    (joined : ActivitySeatEnd.Joined config snapshot height record posted)
    (account : AccountId) (asset : AssetId)
    (apart : ∀ seat ∈ Seats.heldOpen
        (joined.held.loaded.world (posted.batch.apply (logicalBook pre.logical))) height record,
      seat.account ≠ account) :
    grossDebit (Seats.seqBatch posted.batch joined.held.batch).operations account asset =
      grossDebit posted.batch.operations account asset := by
  have none : (joined.held.batch.operations.map Operation.posting).filter
      (fun posting => decide (posting.source = account)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro posting member
    obtain ⟨operation, inBatch, rfl⟩ := List.mem_map.mp member
    obtain ⟨seat, held, same⟩ := List.mem_map.mp (joined.held_sources operation inBatch)
    have differs := apart seat held
    rw [same] at differs
    simpa using differs
  simp [grossDebit, debits, Seats.seqBatch, List.map_append, List.filter_append, none]

end Minidregg.Kernel.ObjectiveActivityPayerBound
