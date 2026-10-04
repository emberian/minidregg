/- Actual snapshot loading and physical posts for admitted compute accounting.
The invocation receiver is the sole consumer: it combines these posts with the
program effects and admits the signed funding capability/current law first.
-/
import Kernel.RunComputeBudget
import Kernel.PayCellDomain

namespace Minidregg.Kernel.RunComputeBudgetDomain

open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DurableDataIntent

set_option autoImplicit false

abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Physical := DataSnapshot ResourceBirthCodec.rootBytes
abbrev BookCell := RunComputeBudget.BookCell

def bookId (deployment : Deployment) : CellId := ⟨deployment.resourceBookId⟩
def bookBytes (cell : BookCell) : List UInt8 :=
  ResourceBirthCodec.LifecycleImage.bytes CanonicalCellRegistry.registry
    (.live ⟨.resourceBook, cell⟩)
def bookRoot (cell : BookCell) : Digest := ResourceBirthCodec.rootBytes (bookBytes cell)

def decodeBook (bytes : List UInt8) : Option BookCell :=
  match (ResourceBirthCodec.LifecycleImage.codec CanonicalCellRegistry.registry).decode bytes with
  | some (.live ⟨.resourceBook, cell⟩) => some cell
  | _ => none

theorem decodeBook_canonical {bytes : List UInt8} {cell : BookCell}
    (decoded : decodeBook bytes = some cell) : bookBytes cell = bytes := by
  unfold decodeBook at decoded
  split at decoded
  · rename_i payload image
    cases Option.some.inj decoded
    exact ResourceBirthCodec.LifecycleImage.decode_canonical CanonicalCellRegistry.registry image
  · cases decoded

structure LoadedBook (deployment : Deployment) (physical : Physical) where
  private mk ::
  cell : BookCell
  observed : physical.canonicalBytes (bookId deployment) = bookBytes cell

def loadBook (deployment : Deployment) (physical : Physical) : Option (LoadedBook deployment physical) :=
  match decoded : decodeBook (physical.canonicalBytes (bookId deployment)) with
  | none => none
  | some cell => some ⟨cell, (decodeBook_canonical decoded).symm⟩

def LoadedBook.write {deployment : Deployment} {physical : Physical}
    (_loaded : LoadedBook deployment physical) (post : BookCell) : DataWrite where
  cellId := bookId deployment
  expectedPre := physical.model.roots (bookId deployment)
  exactPost := bookRoot post
  canonicalPostBytes := bookBytes post

def LoadedBook.readGuard {deployment : Deployment} {physical : Physical}
    (_loaded : LoadedBook deployment physical) : ReadGuard :=
  ⟨bookId deployment, physical.model.roots (bookId deployment)⟩

inductive Reject where
  | payUnavailable
  | bookUnavailable
  | staleBookRoot
  | budget (reason : RunComputeBudget.Reject)
  deriving DecidableEq, Repr

/-- Exact consent from the signed account target. The Book root pins the
issuer well without disclosing that unrelated account's balance to the caller. -/
structure FundingInput where
  index : Nat
  payer : Nat
  capability : CapabilityId
  asset : Nat
  credits : Nat
  expectedPayerBalance : Int
  expectedBookRoot : Digest
  deriving DecidableEq, Repr

/-- Only prepare constructs this token, from the same actual snapshot's pay and
Book. The optional index is extracted by the receiver from a signed funding leg;
it is carried alongside the exact quote/burn, not accepted as a free exclusion. -/
structure Prepared (deployment : Deployment) (physical : Physical) (subject : SubjectId) where
  private mk ::
  pay : PayCellDomain.Loaded deployment physical
  book : LoadedBook deployment physical
  budget : RunComputeBudget.Prepared subject pay.cell pay.cell.root book.cell
  fundingIndex : Option Nat

/-- Proposal assembly may discover the funding target position only after the
source runs. Relocation changes only that bookkeeping position: the exact
loaded Pay/Book and accepted fee-first budget token are retained. Absence of
funding remains absence; this never creates a payer consent or acceptance. -/
def Prepared.relocateFundingIndex {deployment : Deployment} {physical : Physical}
    {subject : SubjectId} (prepared : Prepared deployment physical subject) (index : Nat) :
    Prepared deployment physical subject :=
  ⟨prepared.pay, prepared.book, prepared.budget, prepared.fundingIndex.map (fun _ => index)⟩

theorem Prepared.relocate_budget_exact {deployment : Deployment} {physical : Physical}
    {subject : SubjectId} (prepared : Prepared deployment physical subject) (index : Nat) :
    (prepared.relocateFundingIndex index).budget = prepared.budget := rfl

theorem Prepared.relocate_book_exact {deployment : Deployment} {physical : Physical}
    {subject : SubjectId} (prepared : Prepared deployment physical subject) (index : Nat) :
    (prepared.relocateFundingIndex index).book = prepared.book := rfl

#assert_axioms Prepared.relocate_budget_exact
#assert_axioms Prepared.relocate_book_exact

def prepare (deployment : Deployment) (physical : Physical)
    (clock : ClockCell.Clock) (subject : SubjectId) (steps : Nat)
    (funding : Option FundingInput) :
    Except Reject (Prepared deployment physical subject) := do
  let some pay := PayCellDomain.load deployment physical | throw .payUnavailable
  let some book := loadBook deployment physical | throw .bookUnavailable
  let consent ← match funding with
    | none => pure none
    | some supplied => do
      if supplied.expectedBookRoot != physical.model.roots (bookId deployment) then
        throw .staleBookRoot
      let logical := CanonicalResourceKernel.logicalBook book.cell.logical
      let consent : RunComputeBudget.Funding := {
        payer := supplied.payer
        capability := supplied.capability
        asset := supplied.asset
        credits := supplied.credits
        expectedPayerBalance := supplied.expectedPayerBalance
        expectedWellBalance := logical.balance supplied.asset supplied.asset }
      pure (some consent)
  let budget ← (RunComputeBudget.prepare subject clock pay.cell pay.cell.root book.cell
    steps consent).mapError Reject.budget
  pure ⟨pay, book, budget, funding.map FundingInput.index⟩

def Prepared.steps {deployment : Deployment} {physical : Physical} {subject : SubjectId}
    (prepared : Prepared deployment physical subject) : Nat := prepared.budget.quota.quoted.steps

def Prepared.credits {deployment : Deployment} {physical : Physical} {subject : SubjectId}
    (prepared : Prepared deployment physical subject) : Nat := prepared.budget.quota.quoted.credits

/-- Usage and the real Book debit belong to the same invocation intent. A free
call writes only usage; its read of the Book stays a guard. -/
def Prepared.writes {deployment : Deployment} {physical : Physical} {subject : SubjectId}
    (prepared : Prepared deployment physical subject) : List DataWrite :=
  [prepared.pay.write prepared.budget.quota.post] ++
    if prepared.credits = 0 then [] else [prepared.book.write prepared.budget.book.post]

def Prepared.readGuards {deployment : Deployment} {physical : Physical} {subject : SubjectId}
    (prepared : Prepared deployment physical subject) : List ReadGuard :=
  if prepared.credits = 0 then [prepared.book.readGuard] else []

theorem Prepared.writes_roots_bound {deployment : Deployment} {physical : Physical}
    {subject : SubjectId} (prepared : Prepared deployment physical subject) :
    ∀ write ∈ prepared.writes,
      ResourceBirthCodec.rootBytes write.canonicalPostBytes = write.exactPost := by
  intro write member
  simp only [Prepared.writes, List.mem_append, List.mem_singleton] at member
  rcases member with rfl | member
  · rfl
  · split at member
    · cases member
    · simp only [List.mem_singleton] at member
      subst write
      rfl

theorem Prepared.writes_pre_exact {deployment : Deployment} {physical : Physical}
    {subject : SubjectId} (prepared : Prepared deployment physical subject) :
    ∀ write ∈ prepared.writes, write.expectedPre = physical.model.roots write.cellId := by
  intro write member
  simp only [Prepared.writes, List.mem_append, List.mem_singleton] at member
  rcases member with rfl | member
  · rfl
  · split at member
    · cases member
    · simp only [List.mem_singleton] at member
      subst write
      rfl

end Minidregg.Kernel.RunComputeBudgetDomain
