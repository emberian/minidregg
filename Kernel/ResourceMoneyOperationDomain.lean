/-
Canonical monetary operation preparation over the actual deployment Book.

Funding runs first. Domain samples therefore describe the exact Book AFTER
the validated funding prefix, while the eventual write still guards the
original durable Book root. The ordered application batch and funding burn
produce one final Book write. This token does not grant debit authority:
the invocation receiver must admit every actual source account, current law,
funding capability and source-derived operation before selecting a joint
intent containing the room state, return commitments and Pay usage as well.
-/
import Kernel.RunComputeBudgetDomain
import Theory.CanonicalResourceBookInvariant

namespace Minidregg.Kernel.ResourceMoneyOperationDomain

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

abbrev Deployment := RunComputeBudgetDomain.Deployment
abbrev Physical := RunComputeBudgetDomain.Physical
abbrev LoadedBook := RunComputeBudgetDomain.LoadedBook
abbrev BookCell := RunComputeBudget.BookCell

/-- No registrations, shadow balances or constructor tags supplied by a host. -/
def combinedBatch {pre : BookCell} (funding : RunComputeBudget.PreparedBook pre)
    (operations : List Operation) : Batch :=
  ⟨[], (RunComputeBudget.burnBatch funding.funding).operations ++ operations⟩

theorem applyOperations_append (book : Book) (prefix suffix : List Operation) :
    applyOperations book (prefix ++ suffix) =
      applyOperations (applyOperations book prefix) suffix := by
  induction prefix generalizing book with
  | nil => rfl
  | cons operation rest ih => exact ih (operation.apply book)

theorem combined_admitted {pre : BookCell}
    (funding : RunComputeBudget.PreparedBook pre) (operations : List Operation)
    (admitted : OperationsAdmitted (logicalBook funding.post.logical) operations) :
    (combinedBatch funding operations).Admission (logicalBook pre.logical) := by
  have prefix := funding.accepted.admission.2
  have post : logicalBook funding.post.logical =
      applyOperations (logicalBook pre.logical)
        (RunComputeBudget.burnBatch funding.funding).operations := by
    simpa [RunComputeBudget.PreparedBook.post, Batch.apply,
      RunComputeBudget.burnBatch, registerAccounts] using
      funding.accepted.post_logicalBook
  have suffix := admitted
  rw [post] at suffix
  exact ⟨trivial, (operationsAdmitted_append _ _ _).mpr ⟨prefix, suffix⟩⟩

inductive Reject where
  | staleBookRoot
  | originalBookLaw
  | operationsRefused
  | finalBookLaw
  | duplicateSampleCoordinate
  | samplesRefused
  deriving DecidableEq, Repr

structure Prepared {deployment : Deployment} {physical : Physical}
    (book : LoadedBook deployment physical) (expectedOriginalRoot : Digest)
    (funding : RunComputeBudget.PreparedBook book.cell)
    (operations : List Operation) where
  private mk ::
  rootExact : expectedOriginalRoot =
    physical.model.roots (RunComputeBudgetDomain.bookId deployment)
  originalLaw : CanonicalCellRegistry.CellLaw deployment deployment.resourceBookId
    ⟨.resourceBook, book.cell⟩
  applicationAdmitted : OperationsAdmitted (logicalBook funding.post.logical) operations
  accepted : AcceptedBatch book.cell (combinedBatch funding operations)
  finalLaw : CanonicalCellRegistry.CellLaw deployment deployment.resourceBookId
    ⟨.resourceBook, accepted.post⟩

def prepareFrom {deployment : Deployment} {physical : Physical}
    (book : LoadedBook deployment physical) (expectedOriginalRoot : Digest)
    (funding : RunComputeBudget.PreparedBook book.cell)
    (operations : List Operation) :
    Except Reject (Prepared book expectedOriginalRoot funding operations) := do
  if exact : expectedOriginalRoot =
      physical.model.roots (RunComputeBudgetDomain.bookId deployment) then
    if law : CanonicalCellRegistry.CellLaw deployment deployment.resourceBookId
        ⟨.resourceBook, book.cell⟩ then
      if admitted : OperationsAdmitted (logicalBook funding.post.logical) operations then
        let accepted := AcceptedBatch.ofAdmission (combined_admitted funding operations admitted)
        if finalLaw : CanonicalCellRegistry.CellLaw deployment deployment.resourceBookId
            ⟨.resourceBook, accepted.post⟩ then
          pure ⟨exact, law, admitted, accepted, finalLaw⟩
        else throw .finalBookLaw
      else throw .operationsRefused
    else throw .originalBookLaw
  else throw .staleBookRoot

variable {deployment : Deployment} {physical : Physical}
  {book : LoadedBook deployment physical} {expectedOriginalRoot : Digest}
  {funding : RunComputeBudget.PreparedBook book.cell} {operations : List Operation}

def Prepared.applicationPre
    (_prepared : Prepared book expectedOriginalRoot funding operations) : Book :=
  logicalBook funding.post.logical

def Prepared.post (prepared : Prepared book expectedOriginalRoot funding operations) : BookCell :=
  prepared.accepted.post

theorem Prepared.post_funding_first
    (prepared : Prepared book expectedOriginalRoot funding operations) :
    logicalBook prepared.post.logical = applyOperations prepared.applicationPre operations := by
  rw [Prepared.post, prepared.accepted.post_logicalBook]
  simp only [combinedBatch, Batch.apply, registerAccounts, applyOperations_append]
  have post := funding.accepted.post_logicalBook
  simpa [Prepared.applicationPre, RunComputeBudget.PreparedBook.post,
    Batch.apply, RunComputeBudget.burnBatch, registerAccounts] using
    congrArg (fun pre => applyOperations pre operations) post.symm

theorem Prepared.conserves (prepared : Prepared book expectedOriginalRoot funding operations)
    (asset : AssetId) :
    (logicalBook prepared.post.logical).totalAsset asset =
      (logicalBook book.cell.logical).totalAsset asset := prepared.accepted.conserves asset

theorem Prepared.accountSupported
    (prepared : Prepared book expectedOriginalRoot funding operations) :
    (logicalBook prepared.post.logical).AccountSupported :=
  prepared.accepted.accountSupported
    (CanonicalCellRegistry.book_accountSupported _ _ _ prepared.originalLaw)

/-- Includes funding payer/issuer and every application source/destination.
Repeated coordinates in ordered operations remain legal and are checked at
their actual intermediate balance; domain role samples have a separate check. -/
def Prepared.coordinates (_prepared : Prepared book expectedOriginalRoot funding operations) :
    List (AccountId × AssetId) :=
  (combinedBatch funding operations).operations.flatMap fun operation =>
    [(operation.posting.source, operation.posting.asset),
      (operation.posting.destination, operation.posting.asset)]

def Prepared.writes (prepared : Prepared book expectedOriginalRoot funding operations) :
    List DataWrite :=
  if (combinedBatch funding operations).operations.isEmpty then []
  else [book.write prepared.post]

def Prepared.readGuards (_prepared : Prepared book expectedOriginalRoot funding operations) :
    List ReadGuard :=
  if (combinedBatch funding operations).operations.isEmpty then [book.readGuard] else []

theorem Prepared.at_most_one_book_write
    (prepared : Prepared book expectedOriginalRoot funding operations) :
    prepared.writes.length ≤ 1 := by
  unfold Prepared.writes
  split <;> decide

theorem Prepared.writes_pre_exact
    (prepared : Prepared book expectedOriginalRoot funding operations) :
    ∀ write ∈ prepared.writes, write.expectedPre = physical.model.roots write.cellId := by
  intro write member
  unfold Prepared.writes at member
  split at member
  · cases member
  · simp only [List.mem_singleton] at member
    subst write
    rfl

theorem Prepared.writes_roots_bound
    (prepared : Prepared book expectedOriginalRoot funding operations) :
    ∀ write ∈ prepared.writes,
      ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost := by
  intro write member
  unfold Prepared.writes at member
  split at member
  · cases member
  · simp only [List.mem_singleton] at member
    subst write
    rfl

/-- Domain-facing Nat profile. Negative issuer balances are not silently
truncated; a sample requires exact Int.ofNat equality and membership. -/
structure Sample where
  account : AccountId
  asset : AssetId
  balance : Nat
  deriving DecidableEq, Repr

def SamplesExact (pre : Book) (samples : List Sample) : Prop :=
  ∀ sample ∈ samples, sample.account ∈ pre.accounts ∧
    pre.balance sample.account sample.asset = Int.ofNat sample.balance

instance (pre : Book) (samples : List Sample) : Decidable (SamplesExact pre samples) := by
  unfold SamplesExact
  infer_instance

structure CheckedSamples (prepared : Prepared book expectedOriginalRoot funding operations)
    (samples : List Sample) where
  private mk ::
  distinct : (samples.map fun sample => (sample.account, sample.asset)).Nodup
  exact : SamplesExact prepared.applicationPre samples

def Prepared.checkSamples (prepared : Prepared book expectedOriginalRoot funding operations)
    (samples : List Sample) : Except Reject (CheckedSamples prepared samples) := do
  if distinct : (samples.map fun sample => (sample.account, sample.asset)).Nodup then
    if exact : SamplesExact prepared.applicationPre samples then pure ⟨distinct, exact⟩
    else throw .samplesRefused
  else throw .duplicateSampleCoordinate

/-- Sampling precedes source execution. Bind the exact original Book and
validated funding prefix without requiring application operations first. -/
structure SampledFunding {deployment : Deployment} {physical : Physical}
    (book : LoadedBook deployment physical) (expectedRoot : Digest)
    (funding : RunComputeBudget.PreparedBook book.cell) (samples : List Sample) where
  private mk ::
  rootExact : expectedRoot = physical.model.roots (RunComputeBudgetDomain.bookId deployment)
  originalLaw : CanonicalCellRegistry.CellLaw deployment deployment.resourceBookId
    ⟨.resourceBook, book.cell⟩
  distinct : (samples.map fun sample => (sample.account, sample.asset)).Nodup
  exact : SamplesExact (logicalBook funding.post.logical) samples

def sampleFunding {deployment : Deployment} {physical : Physical}
    (book : LoadedBook deployment physical) (expectedRoot : Digest)
    (funding : RunComputeBudget.PreparedBook book.cell) (samples : List Sample) :
    Except Reject (SampledFunding book expectedRoot funding samples) := do
  if exactRoot : expectedRoot = physical.model.roots (RunComputeBudgetDomain.bookId deployment) then
    if law : CanonicalCellRegistry.CellLaw deployment deployment.resourceBookId
        ⟨.resourceBook, book.cell⟩ then
      if distinct : (samples.map fun sample => (sample.account, sample.asset)).Nodup then
        if exact : SamplesExact (logicalBook funding.post.logical) samples then
          pure ⟨exactRoot, law, distinct, exact⟩
        else throw .samplesRefused
      else throw .duplicateSampleCoordinate
    else throw .originalBookLaw
  else throw .staleBookRoot

theorem stale_root_refused (suppliedRoot : Digest)
    (stale : suppliedRoot ≠ physical.model.roots (RunComputeBudgetDomain.bookId deployment)) :
    prepareFrom book suppliedRoot funding operations = .error .staleBookRoot := by
  simp [prepareFrom, stale]

/-- A prepared token cannot certify a missing account or caller-spoofed balance.
This follows from the same post-funding sample used by source execution. -/
theorem CheckedSamples.balance_exact
    {prepared : Prepared book expectedOriginalRoot funding operations} {samples : List Sample}
    (checked : CheckedSamples prepared samples) (sample : Sample) (member : sample ∈ samples) :
    prepared.applicationPre.balance sample.account sample.asset = Int.ofNat sample.balance :=
  (checked.exact sample member).2

theorem CheckedSamples.account_present
    {prepared : Prepared book expectedOriginalRoot funding operations} {samples : List Sample}
    (checked : CheckedSamples prepared samples) (sample : Sample) (member : sample ∈ samples) :
    sample.account ∈ prepared.applicationPre.accounts := (checked.exact sample member).1

/-- Every application debit is checked after funding AND all earlier source
operations. Repeating a solvent initial snapshot cannot admit a later overdraft. -/
theorem Prepared.source_solvent_at
    (prepared : Prepared book expectedOriginalRoot funding operations)
    (prior suffix : List Operation) (operation : Operation)
    (position : operations = prior ++ operation :: suffix)
    (notMint : operation.isIssuerMint ≠ true) :
    Int.ofNat operation.posting.amount ≤
      (applyOperations prepared.applicationPre prior).balance
        operation.posting.source operation.posting.asset := by
  have ordered := prepared.applicationAdmitted
  rw [position, operationsAdmitted_append] at ordered
  exact ordered.2.1.sourceSolvent.resolve_left notMint

/-- The parent uses this list instead of accounting.writes: usage is retained,
and the funding Book post is replaced by the ONE funding+application Book post.
The source invocation effects must join this in the same selected DataIntent. -/
def Prepared.withQuotaWrites {subject : SubjectId}
    (accounting : RunComputeBudgetDomain.Prepared deployment physical subject)
    (expectedRoot : Digest) (ops : List Operation)
    (prepared : Prepared accounting.book expectedRoot accounting.budget.book ops) :
    List DataWrite :=
  [accounting.pay.write accounting.budget.quota.post] ++ prepared.writes

end Minidregg.Kernel.ResourceMoneyOperationDomain
