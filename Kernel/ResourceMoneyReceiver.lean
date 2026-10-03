/- Native financial preparation shared by direct typed commands and checked
source plans. Entries are extracted from signed account targets by the parent
receiver; its existing current capability/law/signature admission is mandatory.
No accepted effect or durable receipt can be obtained from this token alone. -/
import Kernel.ResourceMoneyWire
import Compiler.ResourceAuthorityProjection

namespace Minidregg.Kernel.ResourceMoneyReceiver
open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Kernel.ResourceMoneyWire
open Minidregg.Kernel.DurableDataIntent
set_option autoImplicit false

abbrev Deployment := ResourceMoneyOperationDomain.Deployment
abbrev Physical := ResourceMoneyOperationDomain.Physical

inductive Reject where
  | bookUnavailable
  | funding (reason : RunComputeBudget.Reject)
  | batchCount
  | coverage
  | operation (reason : ResourceMoneyOperationDomain.Reject)
  deriving DecidableEq, Repr

structure Basis (deployment : Deployment) (physical : Physical) where
  book : RunComputeBudgetDomain.LoadedBook deployment physical
  funding : RunComputeBudget.PreparedBook book.cell

/-- Use the exact already-prepared accounting Book, never load a second view.
Direct unmetered commands use the admitted empty funding prefix. -/
def basis {deployment : Deployment} {physical : Physical} {subject : SubjectId}
    (accounting : Option (RunComputeBudgetDomain.Prepared deployment physical subject)) :
    Except Reject (Basis deployment physical) := do
  match accounting with
  | some prepared => pure ⟨prepared.book, prepared.budget.book⟩
  | none =>
    let some book := RunComputeBudgetDomain.loadBook deployment physical | throw .bookUnavailable
    let funding ← (RunComputeBudget.prepareBook book.cell none 0 none).mapError Reject.funding
    pure ⟨book, funding⟩

structure Prepared (deployment : Deployment) (physical : Physical) (entries : List Entry) where
  private mk ::
  loaded : Basis deployment physical
  batch : ApplicationBatch
  batchExact : entries.filterMap (fun entry => entry.consent.batch) = [batch]
  covered : Covered entries batch
  financial : ResourceMoneyOperationDomain.Prepared loaded.book batch.expectedBookRoot
    loaded.funding batch.operations

def prepare {deployment : Deployment} {physical : Physical} {subject : SubjectId}
    (accounting : Option (RunComputeBudgetDomain.Prepared deployment physical subject))
    (entries : List Entry) : Except Reject (Option (Prepared deployment physical entries)) := do
  if entries.isEmpty then pure none else
    let batches := entries.filterMap fun entry => entry.consent.batch
    match exact : batches with
    | [batch] =>
      if covered : Covered entries batch then
        let loaded ← basis accounting
        let financial ← (ResourceMoneyOperationDomain.prepareFrom loaded.book batch.expectedBookRoot
          loaded.funding batch.operations).mapError Reject.operation
        pure (some ⟨loaded, batch, exact, covered, financial⟩)
      else throw .coverage
    | _ => throw .batchCount

variable {deployment : Deployment} {physical : Physical} {entries : List Entry}

def Prepared.writes (prepared : Prepared deployment physical entries) : List DataWrite :=
  prepared.financial.writes

def Prepared.readGuards (prepared : Prepared deployment physical entries) : List ReadGuard :=
  prepared.financial.readGuards

def Prepared.fundingDebit (prepared : Prepared deployment physical entries)
    (account asset : Nat) : Nat :=
  match prepared.loaded.funding.funding with
  | none => 0
  | some funding =>
    if funding.payer = account ∧ funding.asset = asset then funding.credits else 0

def Prepared.fundingAssets (prepared : Prepared deployment physical entries) (account : Nat) :
    List AssetId :=
  match prepared.loaded.funding.funding with
  | none => []
  | some funding => if funding.payer = account then [funding.asset] else []

/-- Only coordinates actually consumed by this account's source/destination
roles, including funding issuer credits, enter its native policy view. Read capability narrowing is supplied by
the parent observation admission, separately from this debit scope. -/
def Prepared.roleAssets (prepared : Prepared deployment physical entries) (account : Nat) :
    List AssetId :=
  (prepared.financial.coordinates.filterMap fun coordinate =>
    if coordinate.1 = account then some coordinate.2 else none).eraseDups

/-- Scope bounds authorize every gross outgoing application debit plus the
actual funding debit. A later credit never discounts reserved outgoing value. -/
def Prepared.grossDebitFootprint (prepared : Prepared deployment physical entries) (entry : Entry) : Footprint :=
  let assets := (ResourceMoneyWire.assets prepared.batch entry ++
    prepared.fundingAssets entry.account).toFinset
  { touched := assets.image CellField.balance
    delta := fun field => match field with
      | .balance asset => -(Int.ofNat (ResourceMoneyWire.debit prepared.batch entry asset +
          prepared.fundingDebit entry.account asset))
      | _ => 0 }

/-- Preserve the existing scope contract: these are actual committed net
changes, including destination credits. Gross debit reservation is a separate
additional check, never a replacement of this actual transition footprint. -/
def Prepared.footprint (prepared : Prepared deployment physical entries) (entry : Entry) : Footprint :=
  { touched := (prepared.roleAssets entry.account).toFinset.image CellField.balance
    delta := fun field => match field with
      | .balance asset =>
          (logicalBook prepared.financial.post.logical).balance entry.account asset -
            (logicalBook prepared.loaded.book.cell.logical).balance entry.account asset
      | _ => 0 }

def Prepared.accountSlots (prepared : Prepared deployment physical entries) (account : Nat) :
    List (String × Int) :=
  (prepared.roleAssets account).flatMap fun asset =>
    let slotStem := "money/balance/" ++ toString asset
    [(slotStem ++ "/before", (logicalBook prepared.loaded.book.cell.logical).balance account asset),
     (slotStem ++ "/application-before", prepared.financial.applicationPre.balance account asset),
     (slotStem ++ "/after", (logicalBook prepared.financial.post.logical).balance account asset)]

/-- Per-operation current-law inputs use the actual intermediate Book, not a
caller-declared before/after number or an initial balance reused for every leg. -/
def Prepared.positionSlots (prepared : Prepared deployment physical entries) (entry : Entry) :
    List (String × Int) :=
  entry.consent.positions.flatMap fun position =>
    match prepared.batch.operations[position]? with
    | none => [] -- Covered forbids this branch in every prepared token.
    | some operation =>
      let before := applyOperations prepared.financial.applicationPre
        (prepared.batch.operations.take position)
      let after := operation.apply before
      let slotStem := "money/position/" ++ toString position
      [(slotStem ++ "/source", Int.ofNat operation.posting.source),
       (slotStem ++ "/destination", Int.ofNat operation.posting.destination),
       (slotStem ++ "/asset", Int.ofNat operation.posting.asset),
       (slotStem ++ "/amount", Int.ofNat operation.posting.amount),
       (slotStem ++ "/source/before", before.balance operation.posting.source operation.posting.asset),
       (slotStem ++ "/source/after", after.balance operation.posting.source operation.posting.asset)] ++
        ResourceAuthorityProjection.bytesSlots (slotStem ++ "/operation/bytes") 0
          (CanonicalResourcePageMaterializer.operationStream.encode operation)

theorem Prepared.conserves (prepared : Prepared deployment physical entries) (asset : AssetId) :
    (logicalBook prepared.financial.post.logical).totalAsset asset =
      (logicalBook prepared.loaded.book.cell.logical).totalAsset asset :=
  prepared.financial.conserves asset

theorem Prepared.exact_original_root (prepared : Prepared deployment physical entries) :
    prepared.batch.expectedBookRoot =
      physical.model.roots (RunComputeBudgetDomain.bookId deployment) :=
  prepared.financial.rootExact

theorem Prepared.one_batch (prepared : Prepared deployment physical entries) :
    (entries.filterMap fun entry => entry.consent.batch).length = 1 := by
  rw [prepared.batchExact]
  rfl

theorem Prepared.no_duplicate_accounts (prepared : Prepared deployment physical entries) :
    (entries.map Entry.account).Nodup := prepared.covered.1

end Minidregg.Kernel.ResourceMoneyReceiver
