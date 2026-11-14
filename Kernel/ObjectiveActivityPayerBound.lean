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
  command does not carry; it is bounded on the decided batch only.
* `exhaust_debit_le` -- an exhaustion's is at most the added envelope's price, when the
  account is not the activity's own purse.

## The declared amount is NOT the debit: an invocation

`invoke_debit_exceeds`: an invocation's operations take from the account the envelope's price
AND the postage of every message the run queued (`ObjectiveCall.creditTransfers`). The command
declares the envelope; how many messages the run sends is decided by the run. So the gate's
bound on the declared envelope price does not bound an invocation's debit, and the bound that
holds is the one on the decided batch. The lemma is over any mail with one queued credit; it
does not construct an admitted invocation that has one.

## Not here

A birth (envelope price plus deposit, then the purse settles), a delivery and a drained abort
(the purse's charges, the added envelope, then the purse settles) go through `settlePurse`,
whose remaining operations are sourced at the purse. That their debit of the account is the
declared amount is not proved here; `Prepared.payer_bounded` bounds what they post.
-/
module

public import Kernel.ObjectiveAdmittedTurn
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

end Minidregg.Kernel.ObjectiveActivityPayerBound
