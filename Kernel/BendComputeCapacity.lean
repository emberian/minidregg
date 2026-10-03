/- Explicit capacity-unit funding bridge. This reuses the current source-loaded
Pay/Clock/Book quota and burn algorithms, while naming its argument honestly as
public canonical-IR capacity. It is never an invented Bend Eval source count.
Native capability/signature/law admission of the funding leg remains mandatory;
this prepared monetary token alone cannot authorize or commit the invocation.
-/
import Kernel.RunComputeBudgetDomain
import Compiler.BendPrivateCapacity

namespace Minidregg.Kernel.BendComputeCapacity
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

/-- The new profile explicitly prices public capacity units through the existing
compute allowance/credit meter. Legacy Nock calls continue supplying their real
source step count to their unchanged source-charge rule. -/
def contract : List UInt8 :=
  "DREGG.BEND.CAPACITY-FUNDING/v1:public-canonical-IR-capacity;source-loaded-pay-clock-book;shared-compute-allowance;exact-quoted-credit-burn;funding-first;current-signed-funding-law;no-source-count-substitution;no-private-use-refund".toUTF8.toList
def tariffId : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.CAPACITY-FUNDING/v1".toUTF8.toList contract).digest

structure Prepared (deployment : RunComputeBudgetDomain.Deployment)
    (physical : RunComputeBudgetDomain.Physical) (subject : SubjectId)
    (capacity : BendPrivateCapacity.Capacity) where
  private mk ::
  accounting : RunComputeBudgetDomain.Prepared deployment physical subject
  capacityUnitsExact : accounting.steps = capacity.proofWork
  capacityFeeExact : accounting.credits = capacity.feeDebit

inductive Reject where
  | accounting (reason : RunComputeBudgetDomain.Reject)
  | unitsChanged
  | quotedFeeChanged

def prepare (deployment : RunComputeBudgetDomain.Deployment)
    (physical : RunComputeBudgetDomain.Physical) (clock : ClockCell.Clock)
    (subject : SubjectId) (capacity : BendPrivateCapacity.Capacity)
    (funding : Option RunComputeBudgetDomain.FundingInput) :
    Except Reject (Prepared deployment physical subject capacity) := do
  let accounting ← (RunComputeBudgetDomain.prepare deployment physical clock subject
    capacity.proofWork funding).mapError Reject.accounting
  if unitsExact : accounting.steps = capacity.proofWork then
    if feeExact : accounting.credits = capacity.feeDebit then
      pure ⟨accounting, unitsExact, feeExact⟩
    else throw .quotedFeeChanged
  else throw .unitsChanged

/-- The financial operation adapter consumes this exact original Book and
accepted funding prefix, then applies application operations to its post and
emits one final Book write. It must not join two independent Book posts. -/
def Prepared.fundingPrefix {deployment : RunComputeBudgetDomain.Deployment}
    {physical : RunComputeBudgetDomain.Physical} {subject : SubjectId}
    {capacity : BendPrivateCapacity.Capacity}
    (prepared : Prepared deployment physical subject capacity) :
    RunComputeBudget.PreparedBook prepared.accounting.book.cell :=
  prepared.accounting.budget.book

theorem public_units_exact {deployment : RunComputeBudgetDomain.Deployment}
    {physical : RunComputeBudgetDomain.Physical} {subject : SubjectId}
    {capacity : BendPrivateCapacity.Capacity}
    (prepared : Prepared deployment physical subject capacity) :
    prepared.accounting.steps = capacity.proofWork := prepared.capacityUnitsExact
theorem fee_exact {deployment : RunComputeBudgetDomain.Deployment}
    {physical : RunComputeBudgetDomain.Physical} {subject : SubjectId}
    {capacity : BendPrivateCapacity.Capacity}
    (prepared : Prepared deployment physical subject capacity) :
    prepared.accounting.credits = capacity.feeDebit := prepared.capacityFeeExact

end Minidregg.Kernel.BendComputeCapacity
