/-
# Canonical resource Book support

Canonical resource cells may contain balances only for registered accounts.
This is a semantic cell law, not a codec restriction: malformed books remain
representable so loading can reject them explicitly. On supported books,
registration depends only on the public account namespace, never on hidden
balance coordinates. Every admitted resource operation preserves this law.
-/
import Theory.CanonicalResourceKernel

namespace Minidregg.Theory.CanonicalResourceKernel

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-- Only account membership is constrained. Asset balances can be negative
for issuer wells, and this law does not make any balance public. -/
def Book.AccountSupported (book : Book) : Prop :=
  ∀ coordinate ∈ book.balances.support, coordinate.1 ∈ book.accounts

instance (book : Book) : Decidable book.AccountSupported := by
  unfold Book.AccountSupported
  infer_instance

theorem Book.AccountSupported.balance_zero {book : Book}
    (supported : book.AccountSupported) {account : AccountId}
    (absent : account ∉ book.accounts) (asset : AssetId) :
    book.balance account asset = 0 := by
  by_contra nonzero
  exact absent (supported (account, asset)
    ((DFinsupp.mem_support_toFun _ _).mpr nonzero))

theorem Book.accountSupported_iff_zero_outside (book : Book) :
    book.AccountSupported ↔
      ∀ account ∉ book.accounts, ∀ asset, book.balance account asset = 0 := by
  constructor
  · exact fun supported account absent asset => supported.balance_zero absent asset
  · intro outside coordinate member
    by_contra absent
    exact ((DFinsupp.mem_support_toFun _ _).mp member)
      (outside coordinate.1 absent coordinate.2)

theorem Book.empty_accountSupported : Book.empty.AccountSupported := by
  simp [Book.AccountSupported, Book.empty]

theorem Book.zero_accountSupported (accounts : Finset AccountId)
    (leases : Π₀ _ : LeaseId, Option LeaseRecord) :
    (Book.mk accounts 0 leases).AccountSupported := by
  simp [Book.AccountSupported]

theorem Book.registerAccount_accountSupported (book : Book) (account : AccountId)
    (supported : book.AccountSupported) :
    (book.registerAccount account).AccountSupported := by
  intro coordinate member
  exact Finset.mem_insert_of_mem (supported coordinate member)

theorem Book.applyPosting_accountSupported (book : Book) (posting : Posting)
    (supported : book.AccountSupported)
    (sourcePresent : posting.source ∈ book.accounts)
    (destinationPresent : posting.destination ∈ book.accounts) :
    (book.applyPosting posting).AccountSupported := by
  rw [Book.accountSupported_iff_zero_outside]
  intro account absent asset
  have oldZero := supported.balance_zero absent asset
  have sourceDifferent : account ≠ posting.source := by
    intro same
    exact absent (same.symm ▸ sourcePresent)
  have destinationDifferent : account ≠ posting.destination := by
    intro same
    exact absent (same.symm ▸ destinationPresent)
  simpa [Book.applyPosting, Book.balance, DFinsupp.single_apply,
    sourceDifferent, Ne.symm sourceDifferent, destinationDifferent,
    Ne.symm destinationDifferent] using oldZero

theorem Operation.apply_accountSupported (operation : Operation) (book : Book)
    (supported : book.AccountSupported) (admitted : Admission book operation) :
    (operation.apply book).AccountSupported := by
  have posting := book.applyPosting_accountSupported operation.posting supported
    admitted.sourcePresent admitted.destinationPresent
  cases operation <;> exact posting

theorem Accepted.accountSupported {M : CellState.Materializer schema Digest}
    {pre : CellState.Materialized M} {operation : Operation}
    (accepted : Accepted pre operation)
    (supported : (logicalBook pre.logical).AccountSupported) :
    (logicalBook accepted.post.logical).AccountSupported := by
  rw [accepted.post_logicalBook]
  exact operation.apply_accountSupported _ supported accepted.admission

/-- The old hidden-support guard stays in the general admission predicate.
The canonical cell invariant proves it cannot distinguish balances during
registration of a fresh account. -/
theorem registrationAdmission_iff_fresh {book : Book} (supported : book.AccountSupported)
    (account : AccountId) :
    RegistrationAdmission book account ↔ account ∉ book.accounts := by
  constructor
  · exact And.left
  · intro absent
    refine ⟨absent, ?_⟩
    intro coordinate member same
    exact absent (same ▸ supported coordinate member)

def RegistrationsFresh (accounts : Finset AccountId) : List AccountId → Prop
  | [] => True
  | account :: rest => account ∉ accounts ∧ RegistrationsFresh (insert account accounts) rest

instance registrationsFreshDecidable (accounts : Finset AccountId)
    (registrations : List AccountId) : Decidable (RegistrationsFresh accounts registrations) := by
  induction registrations generalizing accounts with
  | nil => exact instDecidableTrue
  | cons account rest ih => unfold RegistrationsFresh; infer_instance

theorem registerAccounts_accountSupported (book : Book) (accounts : List AccountId)
    (supported : book.AccountSupported) :
    (registerAccounts book accounts).AccountSupported := by
  induction accounts generalizing book with
  | nil => exact supported
  | cons account rest ih =>
    exact ih _ (book.registerAccount_accountSupported account supported)

theorem registrationsAdmitted_iff_fresh (book : Book) (accounts : List AccountId)
    (supported : book.AccountSupported) :
    RegistrationsAdmitted book accounts ↔ RegistrationsFresh book.accounts accounts := by
  induction accounts generalizing book with
  | nil => rfl
  | cons account rest ih =>
    rw [RegistrationsAdmitted, RegistrationsFresh,
      registrationAdmission_iff_fresh supported,
      ih _ (book.registerAccount_accountSupported account supported)]
    rfl

/-- Supported books with identical account names have identical registration
outcomes, regardless of their private balances and lease records. -/
theorem registrationsAdmitted_accounts_only (left right : Book) (accounts : List AccountId)
    (leftSupported : left.AccountSupported) (rightSupported : right.AccountSupported)
    (sameAccounts : left.accounts = right.accounts) :
    RegistrationsAdmitted left accounts ↔ RegistrationsAdmitted right accounts := by
  rw [registrationsAdmitted_iff_fresh _ _ leftSupported,
    registrationsAdmitted_iff_fresh _ _ rightSupported, sameAccounts]

theorem applyOperations_accountSupported (book : Book) (operations : List Operation)
    (supported : book.AccountSupported) (admitted : OperationsAdmitted book operations) :
    (applyOperations book operations).AccountSupported := by
  induction operations generalizing book with
  | nil => exact supported
  | cons operation rest ih =>
    exact ih _ (operation.apply_accountSupported book supported admitted.1) admitted.2

theorem Batch.apply_accountSupported (batch : Batch) (book : Book)
    (supported : book.AccountSupported) (admitted : batch.Admission book) :
    (batch.apply book).AccountSupported :=
  applyOperations_accountSupported _ _
    (registerAccounts_accountSupported _ _ supported) admitted.2

theorem Batch.run_accountSupported (batch : Batch) (book post : Book)
    (supported : book.AccountSupported) (accepted : batch.run book = some post) :
    post.AccountSupported := by
  obtain ⟨admitted, rfl⟩ := (batch.run_accepts_iff book post).mp accepted
  exact batch.apply_accountSupported book supported admitted

theorem AcceptedBatch.accountSupported {M : CellState.Materializer schema Digest}
    {pre : CellState.Materialized M} {batch : Batch}
    (accepted : AcceptedBatch pre batch)
    (supported : (logicalBook pre.logical).AccountSupported) :
    (logicalBook accepted.post.logical).AccountSupported := by
  rw [accepted.post_logicalBook]
  exact batch.apply_accountSupported _ supported accepted.admission

theorem witnessHiddenBook_not_accountSupported : ¬witnessHiddenBook.AccountSupported := by
  intro supported
  have zero := supported.balance_zero (account := 9) (by decide) 0
  have nonzero : witnessHiddenBook.balance 9 0 ≠ 0 := by decide
  exact nonzero zero

end Minidregg.Theory.CanonicalResourceKernel
