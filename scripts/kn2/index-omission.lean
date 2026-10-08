/-
T2.2 omission witness. The real append with an empty nullifier list returns a
transaction-only root. That root accepts a genuine absence proof for a nullifier
which the logical committed record consumed. The companion index-omission.sh
plants precisely this omitted-list bug in IndexRows.apply and requires the
unconditional apply_eq_setAll theorem to stop compiling.

Run: lake env lean scripts/kn2/index-omission.lean
No Store helper, compiler trust, or single-set correctness hypothesis is used.
-/
import Compiler.DurableIndex

open Minidregg.Compiler.DurableIndex
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableDataIntent

namespace IndexOmission

/-- All three claims concern the same transaction, consumed nullifier, and
height. The non-membership opening is honest for the wrong root. -/
theorem wrong_root_accepts_consumed_absence (record : IntentRecord)
    (nullifier : StableNullifier) (consumed : nullifier ∈ record.nullifiers) :
    IndexRows.apply (fun _ => none) emptyDigest 1 record.transactionId [] =
      .ok (dig (.leaf (transactionKey record.transactionId) (heightValue 1)),
        [([], .leaf (transactionKey record.transactionId) (heightValue 1))]) ∧
    LogicalIndex [record] (nullifierKey nullifier) = some (heightValue 1) ∧
    verify (dig (.leaf (transactionKey record.transactionId) (heightValue 1)))
      (nullifierKey nullifier) none
      ⟨[], .leaf (transactionKey record.transactionId) (heightValue 1)⟩ = true :=
  ⟨apply_transaction_only _ _ _, consumed_declared record nullifier consumed,
    omitted_nullifier_absence _ _ _⟩

#assert_axioms wrong_root_accepts_consumed_absence

end IndexOmission
