/-
# Kernel.ResourceMoneyValueBound -- the two gross-debit footprints, and when they agree

The resource-transaction path judges a money consent's scope at its own gross-debit footprint
(`ResourceMoneyReceiver.Prepared.grossDebitFootprint`); every other debiting receiver judges
at `Theory.CapabilityValueBound.debitFootprint`. They are two readings of one batch:

* `ResourceMoneyWire.debit batch entry asset` sums the postings at the POSITIONS the entry's
  signed consent lists.
* `CapabilityValueBound.grossDebit batch.operations entry.account asset` sums every posting
  whose SOURCE is the entry's account.

They differ on an arbitrary consent (`Witness.uncovered_differs`: a consent that lists fewer
positions than its account's postings reads a smaller debit). They agree under the receiver's
own admission condition `ResourceMoneyWire.Covered` (accounts distinct, each entry's
positions distinct and sourced at its account, every position consented by its source's
entry): then an entry's positions are exactly the positions its account is the source of.
That agreement is `Agreement`, stated here with its witnesses; its proof is owed.

The receiver's footprint has one more term, which is not an operation of the application
batch: the funding debit (`Prepared.fundingDebit`: `funding.credits` of `funding.asset` from
`funding.payer`). With it, `Prepared.grossDebitFootprint prepared entry` is
`debitFootprint` of the application operations followed by that one posting.
-/
module

public import Kernel.ResourceMoneyWire
public import Theory.CapabilityValueBound

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Kernel.ResourceMoneyValueBound

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Kernel.ResourceMoneyWire

set_option autoImplicit false

/-- The two readings agree on one batch: for every entry, the same debited assets and, in each
asset the batch posts, the same gross debit. -/
def Agrees (entries : List Entry) (batch : ApplicationBatch) : Prop :=
  ∀ entry ∈ entries,
    (∀ asset ∈ assets batch entry,
      asset ∈ CapabilityValueBound.debitAssetList batch.operations entry.account) ∧
    (∀ asset ∈ CapabilityValueBound.debitAssetList batch.operations entry.account,
      asset ∈ assets batch entry) ∧
    ∀ asset ∈ batch.operations.map fun operation => operation.posting.asset,
      debit batch entry asset =
        CapabilityValueBound.grossDebit batch.operations entry.account asset

instance (entries : List Entry) (batch : ApplicationBatch) : Decidable (Agrees entries batch) := by
  unfold Agrees
  infer_instance

/-- **The agreement.** Under the receiver's admission condition the two footprints read the
same debits. Stated; its proof is owed. -/
def Agreement : Prop :=
  ∀ (entries : List Entry) (batch : ApplicationBatch), Covered entries batch → Agrees entries batch

namespace Witness

/-- Account 7 pays 9 twice in asset 0 and once in asset 1; 9 pays 7 once in asset 0. -/
def batch : ApplicationBatch :=
  ⟨⟨0⟩, [.transfer 7 9 0 3, .transfer 9 7 0 10, .transfer 7 9 1 2, .transfer 7 9 0 4]⟩

/-- The covered consents: 7 lists its three positions (out of order), 9 its one. -/
def covered : List Entry := [⟨7, ⟨none, [3, 0, 2], none⟩⟩, ⟨9, ⟨none, [1], none⟩⟩]

/-- A consent that omits one of 7's postings. -/
def uncovered : List Entry := [⟨7, ⟨none, [0, 2], none⟩⟩, ⟨9, ⟨none, [1], none⟩⟩]

/-- Satisfiable, with the premise inhabited: a covered batch on which the readings agree, and
the agreed debit is not zero. -/
theorem covered_agrees :
    Covered covered batch ∧ Agrees covered batch ∧
      debit batch ⟨7, ⟨none, [3, 0, 2], none⟩⟩ 0 = 7 := by decide

/-- Teeth: without `Covered` the readings differ (5 against 7 here), so the premise is used. -/
theorem uncovered_differs : ¬ Covered uncovered batch ∧ ¬ Agrees uncovered batch := by decide

end Witness

#assert_axioms Witness.covered_agrees Witness.uncovered_differs

end Minidregg.Kernel.ResourceMoneyValueBound
