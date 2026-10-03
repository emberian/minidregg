/- Compact source-facing names over the actual checked post-funding Book.
The input table is generated before source execution; source output never
supplies a replacement resolver. Native IDs remain exact canonical bytes. -/
import Kernel.ResourceMoneyOperationDomain
import Theory.AssertAxioms

namespace Minidregg.Kernel.ResourceMoneySampleTable
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.ResourceMoneyOperationDomain
set_option autoImplicit false

structure Binding where
  token : Nat
  native : List UInt8
  deriving DecidableEq, Repr

structure Row where
  accountToken : Nat
  assetToken : Nat
  balance : Nat
  deriving DecidableEq, Repr

structure Table where
  book : List UInt8
  originalRoot : List UInt8
  accountBindings : List Binding
  assetBindings : List Binding
  rows : List Row
  deriving DecidableEq, Repr

def accountIds (samples : List Sample) : List Nat := (samples.map Sample.account).eraseDups
def assetIds (samples : List Sample) : List Nat := (samples.map Sample.asset).eraseDups

def bindings (ids : List Nat) : List Binding :=
  ids.zipIdx.map fun pair => ⟨pair.2, StreamCodec.nat.encode pair.1⟩

def resolveBytes (table : List Binding) (token : Nat) : Option (List UInt8) :=
  (table.find? fun binding => binding.token == token).map Binding.native

def resolveNative (table : List Binding) (token : Nat) : Option Nat :=
  (resolveBytes table token).bind StreamCodec.nat.toLawful.decode

def sampleRow (samples : List Sample) (sample : Sample) : Row :=
  ⟨(accountIds samples).idxOf sample.account, (assetIds samples).idxOf sample.asset, sample.balance⟩

def generated (deployment : Deployment) (root : Digest) (samples : List Sample) : Table :=
  ⟨StreamCodec.nat.encode deployment.resourceBookId, digestStream.encode root,
    bindings (accountIds samples), bindings (assetIds samples), samples.map (sampleRow samples)⟩

/-- Both names and values refer to the immutable INPUT dictionary. The ordinal
sequence also gives bounded unique tokens, independently for each namespace. -/
def Exact (table : Table) (deployment : Deployment) (root : Digest)
    (samples : List Sample) : Prop :=
  table.book = StreamCodec.nat.encode deployment.resourceBookId ∧
  table.originalRoot = digestStream.encode root ∧
  table.accountBindings.map Binding.token = List.range (accountIds samples).length ∧
  table.assetBindings.map Binding.token = List.range (assetIds samples).length ∧
  table.rows = samples.map (sampleRow samples) ∧
  (∀ sample ∈ samples,
    resolveNative table.accountBindings (sampleRow samples sample).accountToken = some sample.account ∧
    resolveNative table.assetBindings (sampleRow samples sample).assetToken = some sample.asset)

instance (table : Table) (deployment : Deployment) (root : Digest) (samples : List Sample) :
    Decidable (Exact table deployment root samples) := by
  unfold Exact
  infer_instance

def nativeBytes (table : Table) : Nat :=
  table.book.length + table.originalRoot.length +
    (table.accountBindings.map fun binding => binding.native.length).sum +
    (table.assetBindings.map fun binding => binding.native.length).sum

structure Bounds where
  accounts : Nat
  assets : Nat
  rows : Nat
  nativeBytes : Nat
  deriving DecidableEq, Repr

def Fits (bounds : Bounds) (table : Table) : Prop :=
  table.accountBindings.length ≤ bounds.accounts ∧
  table.assetBindings.length ≤ bounds.assets ∧
  table.rows.length ≤ bounds.rows ∧ nativeBytes table ≤ bounds.nativeBytes

instance (bounds : Bounds) (table : Table) : Decidable (Fits bounds table) := by
  unfold Fits
  infer_instance

inductive Reject where
  | capacity
  | binding
  deriving DecidableEq, Repr

structure Prepared {deployment : Deployment} {physical : Physical}
    {book : LoadedBook deployment physical} {root : Digest}
    {funding : RunComputeBudget.PreparedBook book.cell} {samples : List Sample}
    (checked : SampledFunding book root funding samples) (bounds : Bounds) where
  private mk ::
  table : Table
  generatedExact : table = generated deployment root samples
  exact : Exact table deployment root samples
  fits : Fits bounds table

def prepare {deployment : Deployment} {physical : Physical}
    {book : LoadedBook deployment physical} {root : Digest}
    {funding : RunComputeBudget.PreparedBook book.cell} {samples : List Sample}
    (checked : SampledFunding book root funding samples) (bounds : Bounds) :
    Except Reject (Prepared checked bounds) := do
  if samples.length ≤ bounds.rows then
    let table := generated deployment root samples
    if fits : Fits bounds table then
      if exact : Exact table deployment root samples then pure ⟨table, rfl, exact, fits⟩
      else throw .binding
    else throw .capacity
  else throw .capacity

variable {deployment : Deployment} {physical : Physical}
  {book : LoadedBook deployment physical} {root : Digest}
  {funding : RunComputeBudget.PreparedBook book.cell} {samples : List Sample}
  {checked : SampledFunding book root funding samples} {bounds : Bounds}

theorem Prepared.account_exact (prepared : Prepared checked bounds) (sample : Sample)
    (member : sample ∈ samples) :
    resolveNative prepared.table.accountBindings (sampleRow samples sample).accountToken =
      some sample.account := (prepared.exact.2.2.2.2.2 sample member).1

theorem Prepared.asset_exact (prepared : Prepared checked bounds) (sample : Sample)
    (member : sample ∈ samples) :
    resolveNative prepared.table.assetBindings (sampleRow samples sample).assetToken =
      some sample.asset := (prepared.exact.2.2.2.2.2 sample member).2

theorem Prepared.balance_exact (_prepared : Prepared checked bounds) (sample : Sample)
    (member : sample ∈ samples) :
    (Minidregg.Theory.CanonicalResourceKernel.logicalBook funding.post.logical).balance
      sample.account sample.asset = Int.ofNat (sampleRow samples sample).balance :=
  (checked.exact sample member).2

/-- A source token cannot name two actual native accounts in the same input. -/
theorem Prepared.account_injective (prepared : Prepared checked bounds) (left right : Sample)
    (leftMember : left ∈ samples) (rightMember : right ∈ samples)
    (sameToken : (sampleRow samples left).accountToken = (sampleRow samples right).accountToken) :
    left.account = right.account := by
  have leftExact := prepared.account_exact left leftMember
  rw [sameToken, prepared.account_exact right rightMember] at leftExact
  exact Option.some.inj leftExact.symm

theorem Prepared.asset_injective (prepared : Prepared checked bounds) (left right : Sample)
    (leftMember : left ∈ samples) (rightMember : right ∈ samples)
    (sameToken : (sampleRow samples left).assetToken = (sampleRow samples right).assetToken) :
    left.asset = right.asset := by
  have leftExact := prepared.asset_exact left leftMember
  rw [sameToken, prepared.asset_exact right rightMember] at leftExact
  exact Option.some.inj leftExact.symm

theorem same_account_same_token (samples : List Sample) (left right : Sample)
    (sameAccount : left.account = right.account) :
    (sampleRow samples left).accountToken = (sampleRow samples right).accountToken := by
  simp [sampleRow, sameAccount]

#assert_axioms Prepared.account_exact
#assert_axioms Prepared.asset_exact
#assert_axioms Prepared.balance_exact
#assert_axioms Prepared.account_injective
#assert_axioms Prepared.asset_injective
#assert_axioms same_account_same_token

end Minidregg.Kernel.ResourceMoneySampleTable
