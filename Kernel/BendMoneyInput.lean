/- Before-source monetary input from one actual fee-first Book.
Reader scopes and role coordinates are supplied by the native signed-input
receiver, never by the source result. This leaf checks scope membership and
Book provenance; it does not replace current capability/signature admission. -/
import Kernel.ResourceMoneySampleTable
import Kernel.ResourceMoneyWire

namespace Minidregg.Kernel.BendMoneyInput
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ResourceMoneyOperationDomain
set_option autoImplicit false

structure ReaderScope where
  account : Nat
  fields : Option (Finset CellField)
  deriving DecidableEq

abbrev Coordinate := Nat × Nat

/-- Declared roles include zero-fill/zero-operation accounts. Stable native
coordinate deduplication preserves shared accounts and distinct assets. -/
def coordinates (batch : ResourceMoneyWire.ApplicationBatch)
    (roles : List Coordinate) : List Coordinate :=
  (roles ++ batch.operations.flatMap fun operation =>
    [(operation.posting.source, operation.posting.asset),
      (operation.posting.destination, operation.posting.asset)]).eraseDups

def samplesOf {deployment : RunComputeBudgetDomain.Deployment}
    {physical : RunComputeBudgetDomain.Physical} {subject : SubjectId}
    (compute : RunComputeBudgetDomain.Prepared deployment physical subject)
    (batch : ResourceMoneyWire.ApplicationBatch) (roles : List Coordinate) : List Sample :=
  (coordinates batch roles).map fun coordinate =>
    ⟨coordinate.1, coordinate.2,
      ((CanonicalResourceKernel.logicalBook compute.budget.book.post.logical).balance
        coordinate.1 coordinate.2).toNat⟩

/-- Absent field restriction means all fields, following production NamedBy.
Missing account scopes fail. Duplicate account scopes fail rather than
silently joining restrictions from separately selected capabilities. -/
def ScopeCovered (scopes : List ReaderScope) (samples : List Sample) : Prop :=
  (scopes.map ReaderScope.account).Nodup ∧
  ∀ sample ∈ samples, ∃ scope ∈ scopes,
    scope.account = sample.account ∧ CellField.NamedBy scope.fields (.balance sample.asset)

instance (scopes : List ReaderScope) (samples : List Sample) :
    Decidable (ScopeCovered scopes samples) := by
  unfold ScopeCovered
  infer_instance

def bindingStream : StreamCodec ResourceMoneySampleTable.Binding :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat (StreamCodec.list StreamCodec.byte))
    (fun value => (value.token, value.native))
    (fun (token, native) => ⟨token, native⟩)
    (by intro value; cases value; rfl)

def rowStream : StreamCodec ResourceMoneySampleTable.Row :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat StreamCodec.nat))
    (fun value => (value.accountToken, value.assetToken, value.balance))
    (fun (account, asset, balance) => ⟨account, asset, balance⟩)
    (by intro value; cases value; rfl)

/-- Full canonical input frame, including original Book/ref and actual
after-funding balances. Built from lawful codecs, without host tag bytes. -/
def tableStream : StreamCodec ResourceMoneySampleTable.Table :=
  StreamCodec.xmap
    (StreamCodec.product (StreamCodec.list StreamCodec.byte)
      (StreamCodec.product (StreamCodec.list StreamCodec.byte)
        (StreamCodec.product (StreamCodec.list bindingStream)
          (StreamCodec.product (StreamCodec.list bindingStream) (StreamCodec.list rowStream)))))
    (fun table => (table.book, table.originalRoot, table.accountBindings, table.assetBindings, table.rows))
    (fun (book, root, accounts, assets, rows) => ⟨book, root, accounts, assets, rows⟩)
    (by intro table; cases table; rfl)

inductive Reject where
  | capacity
  | readerScope
  | funding (reason : ResourceMoneyOperationDomain.Reject)
  | table (reason : ResourceMoneySampleTable.Reject)
  deriving DecidableEq, Repr

structure Prepared {deployment : RunComputeBudgetDomain.Deployment}
    {physical : RunComputeBudgetDomain.Physical} {subject : SubjectId}
    (compute : RunComputeBudgetDomain.Prepared deployment physical subject)
    (batch : ResourceMoneyWire.ApplicationBatch) (scopes : List ReaderScope)
    (roles : List Coordinate) (bounds : ResourceMoneySampleTable.Bounds) : Type where
  private mk ::
  samples : List Sample
  generatedExact : samples = samplesOf compute batch roles
  scopeCovered : ScopeCovered scopes samples
  sampled : SampledFunding compute.book batch.expectedBookRoot compute.budget.book samples
  table : ResourceMoneySampleTable.Prepared sampled bounds

def prepare {deployment : RunComputeBudgetDomain.Deployment}
    {physical : RunComputeBudgetDomain.Physical} {subject : SubjectId}
    (compute : RunComputeBudgetDomain.Prepared deployment physical subject)
    (batch : ResourceMoneyWire.ApplicationBatch) (scopes : List ReaderScope)
    (roles : List Coordinate) (bounds : ResourceMoneySampleTable.Bounds) :
    Except Reject (Prepared compute batch scopes roles bounds) := do
  if (coordinates batch roles).length ≤ bounds.rows then
    let samples := samplesOf compute batch roles
    if covered : ScopeCovered scopes samples then
      let sampled ← (sampleFunding compute.book batch.expectedBookRoot compute.budget.book samples).mapError Reject.funding
      let table ← (ResourceMoneySampleTable.prepare sampled bounds).mapError Reject.table
      pure ⟨samples, rfl, covered, sampled, table⟩
    else throw .readerScope
  else throw .capacity

variable {deployment : RunComputeBudgetDomain.Deployment}
  {physical : RunComputeBudgetDomain.Physical} {subject : SubjectId}
  {compute : RunComputeBudgetDomain.Prepared deployment physical subject}
  {batch : ResourceMoneyWire.ApplicationBatch} {scopes : List ReaderScope}
  {roles : List Coordinate} {bounds : ResourceMoneySampleTable.Bounds}

def Prepared.bytes (prepared : Prepared compute batch scopes roles bounds) : List UInt8 :=
  tableStream.encode prepared.table.table

theorem Prepared.bytes_roundtrip (prepared : Prepared compute batch scopes roles bounds) :
    tableStream.toLawful.decode prepared.bytes = some prepared.table.table :=
  tableStream.toLawful.decode_encode _

theorem Prepared.original_root (prepared : Prepared compute batch scopes roles bounds) :
    batch.expectedBookRoot = physical.model.roots (RunComputeBudgetDomain.bookId deployment) :=
  prepared.sampled.rootExact

theorem Prepared.balance_after_funding (prepared : Prepared compute batch scopes roles bounds)
    (sample : Sample) (member : sample ∈ prepared.samples) :
    (CanonicalResourceKernel.logicalBook compute.budget.book.post.logical).balance
      sample.account sample.asset = Int.ofNat sample.balance :=
  (prepared.sampled.exact sample member).2

theorem Prepared.account_present (prepared : Prepared compute batch scopes roles bounds)
    (sample : Sample) (member : sample ∈ prepared.samples) :
    sample.account ∈ (CanonicalResourceKernel.logicalBook compute.budget.book.post.logical).accounts :=
  (prepared.sampled.exact sample member).1

theorem Prepared.observe_scope (prepared : Prepared compute batch scopes roles bounds)
    (sample : Sample) (member : sample ∈ prepared.samples) :
    ∃ scope ∈ scopes, scope.account = sample.account ∧
      CellField.NamedBy scope.fields (.balance sample.asset) :=
  prepared.scopeCovered.2 sample member

theorem Prepared.same_input (prepared : Prepared compute batch scopes roles bounds) :
    prepared.table.table = ResourceMoneySampleTable.generated deployment
      batch.expectedBookRoot (samplesOf compute batch roles) := by
  rw [prepared.table.generatedExact, prepared.generatedExact]

theorem missing_scope_refused (absent : ¬ ScopeCovered scopes (samplesOf compute batch roles))
    (fits : (coordinates batch roles).length ≤ bounds.rows) :
    prepare compute batch scopes roles bounds = .error .readerScope := by
  simp [prepare, fits, absent]
  rfl

#assert_axioms Prepared.bytes_roundtrip
#assert_axioms Prepared.original_root
#assert_axioms Prepared.balance_after_funding
#assert_axioms Prepared.account_present
#assert_axioms Prepared.observe_scope
#assert_axioms Prepared.same_input
#assert_axioms missing_scope_refused

end Minidregg.Kernel.BendMoneyInput
