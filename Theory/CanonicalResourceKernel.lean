/-
# Theory.CanonicalResourceKernel -- a typed asset/account nucleus

The original `KernelState` proves the right conservation equation, but its
ledger is a fixed field of an early monolithic state.  The canonical cell
kernel, by contrast, admits application-supplied `ResourceLaw`s and therefore
does not yet choose the meaning of an asset, an issuer well, a fee, or a lease.

This module closes that semantic gap without claiming to be a settlement
service.  It defines one canonical typed cell field containing a finite account
book, a small closed operation language, the exact typed patch for each
operation, and an accepted token joining policy admission to the verifier-
minted patch.  Every admitted operation normalizes to one debit/credit posting:

* transfer moves value between accounts;
* mint moves value out of the asset's issuer well (negative supply);
* burn returns value to that issuer well;
* fee moves value to an explicit collector;
* lease prepays `rate * epochs` to a lessor and installs the exact lease record.

Thus all five operations share one per-asset conservation theorem.  A separate
credit-only operation is deliberately excluded and proved to break the law.
Physical payment finality, wall-clock expiry, eviction, and durable CAS remain
handler obligations; a logical lease record does not pretend those occurred.

The account book is one typed store address in this bounded nucleus, written
by one guarded operation.  A production
layout may shard balances and leases into sparse fields while preserving the
same operation normalization and conservation law.
-/
import Mathlib.Data.DFinsupp.Encodable
import Theory.CellState
import Theory.TypedAuthorization

namespace Minidregg.Theory.CanonicalResourceKernel

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

/-! ## Names and the canonical account book -/

/-- Account identities and asset identities intentionally share the deployed
identifier shape: an asset is named by its issuer-well account. -/
abbrev AccountId := Nat
abbrev AssetId := Nat
abbrev LeaseId := Nat
abbrev Epoch := Nat

/-- The durable semantic content installed by a prepaid lease. -/
structure LeaseRecord where
  holder : AccountId
  lessor : AccountId
  asset : AssetId
  prepaid : Nat
  startsAt : Epoch
  expiresAt : Epoch
  deriving DecidableEq, Repr

deriving instance Countable for LeaseRecord

/-- A signed account book.  Issuer wells may be negative; ordinary admission
below prevents non-minting spenders from overdrawing. -/
structure Book where
  accounts : Finset AccountId
  balances : Π₀ _ : AccountId × AssetId, Int
  leaseRecords : Π₀ _ : LeaseId, Option LeaseRecord
  deriving DecidableEq

deriving instance Countable for Book

def Book.balance (book : Book) (account : AccountId) (asset : AssetId) : Int :=
  book.balances (account, asset)

def Book.leases (book : Book) (leaseId : LeaseId) : Option LeaseRecord :=
  book.leaseRecords leaseId

def Book.empty : Book where
  accounts := ∅
  balances := 0
  leaseRecords := 0

/-- The conserved total for one asset, including its issuer well. -/
def Book.totalAsset (book : Book) (asset : AssetId) : Int :=
  ∑ account ∈ book.accounts, book.balance account asset

/-! ## One posting algebra, five semantic operations -/

/-- The conserved normal form: exactly one debit and one equal credit. -/
structure Posting where
  source : AccountId
  destination : AccountId
  asset : AssetId
  amount : Nat
  deriving DecidableEq, Repr

def Book.applyPosting (book : Book) (posting : Posting) : Book where
  accounts := book.accounts
  balances :=
    book.balances +
      DFinsupp.single (posting.source, posting.asset) (-(Int.ofNat posting.amount)) +
      DFinsupp.single (posting.destination, posting.asset) (Int.ofNat posting.amount)
  leaseRecords := book.leaseRecords

/-- Every posting between present endpoints preserves the per-asset total. -/
theorem Book.applyPosting_conserves
    (book : Book) (posting : Posting)
    (sourcePresent : posting.source ∈ book.accounts)
    (destinationPresent : posting.destination ∈ book.accounts)
    (asset : AssetId) :
    (book.applyPosting posting).totalAsset asset = book.totalAsset asset := by
  classical
  unfold Book.totalAsset Book.applyPosting Book.balance
  simp only [DFinsupp.add_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  by_cases sameAsset : asset = posting.asset
  · subst sameAsset
    simp [DFinsupp.single_apply, sourcePresent, destinationPresent]
  · simp [DFinsupp.single_apply, Ne.symm sameAsset]

/-- The closed proof-native resource language.  `mint asset ...` debits account
`asset`, because the asset identifier is its issuer-well identifier. -/
inductive Operation
  | transfer (source destination : AccountId) (asset : AssetId) (amount : Nat)
  | mint (asset : AssetId) (destination : AccountId) (amount : Nat)
  | burn (source : AccountId) (asset : AssetId) (amount : Nat)
  | fee (payer collector : AccountId) (asset : AssetId) (amount : Nat)
  | lease (leaseId : LeaseId) (holder lessor : AccountId) (asset : AssetId)
      (rate epochs : Nat) (startsAt : Epoch)
  deriving DecidableEq, Repr

/-- Every operation has exactly one value posting. -/
def Operation.posting : Operation -> Posting
  | .transfer source destination asset amount =>
      ⟨source, destination, asset, amount⟩
  | .mint asset destination amount =>
      ⟨asset, destination, asset, amount⟩
  | .burn source asset amount =>
      ⟨source, asset, asset, amount⟩
  | .fee payer collector asset amount =>
      ⟨payer, collector, asset, amount⟩
  | .lease _ holder lessor asset rate epochs _ =>
      ⟨holder, lessor, asset, rate * epochs⟩

/-- Exact fee-like debit visible to metering.  Ordinary transfers, mint, and
burn have no intrinsic fee in this nucleus; fee and lease payments are exact. -/
def Operation.feeDebit : Operation -> Nat
  | .fee _ _ _ amount => amount
  | .lease _ _ _ _ rate epochs _ => rate * epochs
  | _ => 0

/-- The canonical lease record, when this operation installs one. -/
def Operation.leaseRecord? : Operation -> Option (LeaseId × LeaseRecord)
  | .lease leaseId holder lessor asset rate epochs startsAt =>
      some (leaseId,
        { holder := holder
          lessor := lessor
          asset := asset
          prepaid := rate * epochs
          startsAt := startsAt
          expiresAt := startsAt + epochs })
  | _ => none

/-- Apply the conserved posting, then install the lease metadata when present. -/
def Operation.apply (operation : Operation) (book : Book) : Book :=
  let paid := book.applyPosting operation.posting
  match operation.leaseRecord? with
  | none => paid
  | some (leaseId, record) =>
      { paid with leaseRecords := paid.leaseRecords.update leaseId (some record) }

@[simp] theorem Operation.apply_accounts (operation : Operation) (book : Book) :
    (operation.apply book).accounts = book.accounts := by
  cases operation <;> rfl

/-- Logical metadata cannot perturb the value spine. -/
theorem Operation.apply_total_eq_posting
    (operation : Operation) (book : Book) (asset : AssetId) :
    (operation.apply book).totalAsset asset =
      (book.applyPosting operation.posting).totalAsset asset := by
  cases operation <;> rfl

/-- The common conservation theorem for transfer, issuer-backed mint, burn,
fee, and prepaid lease. -/
theorem Operation.apply_conserves
    (operation : Operation) (book : Book)
    (sourcePresent : operation.posting.source ∈ book.accounts)
    (destinationPresent : operation.posting.destination ∈ book.accounts)
    (asset : AssetId) :
    (operation.apply book).totalAsset asset = book.totalAsset asset := by
  rw [Operation.apply_total_eq_posting]
  exact book.applyPosting_conserves operation.posting sourcePresent
    destinationPresent asset

/-! ## Admission: conservation plus the non-algebraic policy checks -/

/-- Mint alone may intentionally drive its issuer well farther negative. -/
def Operation.isIssuerMint : Operation -> Bool
  | .mint _ _ _ => true
  | _ => false

/-- Policy admission is indexed by the exact pre-book and operation.  Endpoint
membership makes the finite-sum law applicable.  Non-minting sources must fund
the debit.  A lease additionally has positive duration and a fresh identifier. -/
structure Admission (book : Book) (operation : Operation) : Prop where
  sourcePresent : operation.posting.source ∈ book.accounts
  destinationPresent : operation.posting.destination ∈ book.accounts
  sourceSolvent :
    operation.isIssuerMint = true \/
      Int.ofNat operation.posting.amount <=
        book.balance operation.posting.source operation.posting.asset
  leaseWellFormed :
    match operation with
    | .lease leaseId _ _ _ _ epochs _ =>
        0 < epochs /\ book.leases leaseId = none
    | _ => True

/-! ## Canonical typed-cell embedding -/

/-- This bounded nucleus uses one typed book address.  There is no untyped map
and no resource package whose authority could be forged independently. -/
inductive Field
  | book
  deriving DecidableEq, Repr

deriving instance Countable for Field

/-- One RAM namespace holding the book at the unit key. -/
abbrev layout : Layout.{0, 0, 0} where
  Namespace := Field
  Key := fun _ => Unit
  Value := fun _ => Book
  discipline := fun _ => .ram

/-- The one address of the book. -/
def bookAddress : Address layout := ⟨.book, ()⟩

/-- Absence of the book address denotes the empty book at the semantic layer. -/
def logicalBook (logical : Store layout) : Book :=
  (logical bookAddress).getD Book.empty

/-- The guarded patch installing `post` as the book: an overwrite guarded by the
exact present book, or an allocation when the book is absent.  The guard is
read from `store`, so the patch is valid there by construction. -/
def bookPatch (store : Store layout) (post : Book) : Patch layout :=
  match store bookAddress with
  | some before => [.write .book () before post]
  | none => [.allocate .book () post]

theorem bookPatch_valid (store : Store layout) (post : Book) :
    Patch.ValidFrom store (bookPatch store post) := by
  unfold bookPatch
  split
  · rename_i before present
    exact ⟨⟨rfl, present⟩, trivial⟩
  · rename_i absent
    exact ⟨⟨by decide, absent⟩, trivial⟩

@[simp] theorem logicalBook_run_bookPatch (store : Store layout) (post : Book) :
    logicalBook (Patch.run store (bookPatch store post)) = post := by
  unfold bookPatch logicalBook
  split <;> simp [Patch.run, Op.apply, bookAddress]

/-- The book patch writes only the book address. -/
theorem bookPatch_writeFootprint (store : Store layout) (post : Book) :
    Patch.writeFootprint (bookPatch store post) = {bookAddress} := by
  unfold bookPatch
  split <;> rfl

/-- The exact patch is derived from the exact materialized pre-cell.  Callers do
not supply balances, a post-book, a footprint, or a post-root. -/
def Operation.patch
    {M : CellState.Materializer layout Digest}
    (operation : Operation) (pre : CellState.Materialized M) : Patch layout :=
  bookPatch pre.logical (operation.apply (logicalBook pre.logical))

/-- The derived patch, quoted against the pre-cell's own root, is validated. -/
theorem Operation.validated
    {M : CellState.Materializer layout Digest}
    (operation : Operation) (pre : CellState.Materialized M) :
    CellState.ValidatedPatch M pre pre.root (operation.patch pre) := by
  obtain ⟨validated, _⟩ := CellState.validate_accepts M pre pre.root
    (operation.patch pre) rfl (bookPatch_valid _ _)
  exact validated

/-- The accepted resource token joins policy to the one derived typed patch.
It does not claim a database transaction or an external lease clock advanced. -/
structure Accepted
    {M : CellState.Materializer layout Digest}
    (pre : CellState.Materialized M) (operation : Operation) : Prop where
  admission : Admission (logicalBook pre.logical) operation
  validated : CellState.ValidatedPatch M pre pre.root (operation.patch pre)

/-- Once policy admission is proved, no host-supplied post data remains. -/
theorem Accepted.ofAdmission
    {M : CellState.Materializer layout Digest}
    {pre : CellState.Materialized M} {operation : Operation}
    (admission : Admission (logicalBook pre.logical) operation) :
    Accepted pre operation :=
  ⟨admission, operation.validated pre⟩

def Accepted.post
    {M : CellState.Materializer layout Digest}
    {pre : CellState.Materialized M} {operation : Operation}
    (accepted : Accepted pre operation) : CellState.Materialized M :=
  accepted.validated.apply

/-- Applying the accepted typed patch installs exactly `Operation.apply`. -/
@[simp] theorem Accepted.post_logicalBook
    {M : CellState.Materializer layout Digest}
    {pre : CellState.Materialized M} {operation : Operation}
    (accepted : Accepted pre operation) :
    logicalBook accepted.post.logical = operation.apply (logicalBook pre.logical) :=
  logicalBook_run_bookPatch _ _

/-- The accepted canonical post conserves every asset. -/
theorem Accepted.conserves
    {M : CellState.Materializer layout Digest}
    {pre : CellState.Materialized M} {operation : Operation}
    (accepted : Accepted pre operation) (asset : AssetId) :
    (logicalBook accepted.post.logical).totalAsset asset =
      (logicalBook pre.logical).totalAsset asset := by
  rw [accepted.post_logicalBook]
  exact operation.apply_conserves (logicalBook pre.logical)
    accepted.admission.sourcePresent accepted.admission.destinationPresent asset

/-! ## One atomic account-registration and payment batch

Registration is a semantic account-table update, not capability creation. Its
authority is supplied by the accepted birth/factory request in the kernel
adapter. Payment authority is required separately for every posting source.

The book can contain nonzero balance coordinates outside `accounts`; ignoring
those coordinates during registration would silently increase the conserved
total. The finite support check below therefore precedes every insertion.
-/

def Book.registerAccount (book : Book) (account : AccountId) : Book :=
  { book with accounts := insert account book.accounts }

/-- Freshness and absence of every hidden nonzero balance are both checked. -/
def RegistrationAdmission (book : Book) (account : AccountId) : Prop :=
  account ∉ book.accounts ∧
    ∀ coordinate ∈ book.balances.support, coordinate.1 ≠ account

instance (book : Book) (account : AccountId) :
    Decidable (RegistrationAdmission book account) := by
  unfold RegistrationAdmission
  infer_instance

theorem RegistrationAdmission.balance_zero
    {book : Book} {account : AccountId}
    (admitted : RegistrationAdmission book account) (asset : AssetId) :
    book.balance account asset = 0 := by
  by_contra nonzero
  exact admitted.2 (account, asset)
    ((DFinsupp.mem_support_toFun _ _).mpr nonzero) rfl

theorem Book.registerAccount_conserves
    (book : Book) (account : AccountId)
    (admitted : RegistrationAdmission book account) (asset : AssetId) :
    (book.registerAccount account).totalAsset asset = book.totalAsset asset := by
  change (∑ a ∈ insert account book.accounts, book.balance a asset) =
    ∑ a ∈ book.accounts, book.balance a asset
  rw [Finset.sum_insert admitted.1, admitted.balance_zero asset]
  simp

def registerAccounts (book : Book) : List AccountId → Book
  | [] => book
  | account :: rest => registerAccounts (book.registerAccount account) rest

def RegistrationsAdmitted (book : Book) : List AccountId → Prop
  | [] => True
  | account :: rest => RegistrationAdmission book account ∧
      RegistrationsAdmitted (book.registerAccount account) rest

instance registrationsDecidable (book : Book) (accounts : List AccountId) :
    Decidable (RegistrationsAdmitted book accounts) := by
  induction accounts generalizing book with
  | nil => exact instDecidableTrue
  | cons account rest ih =>
    unfold RegistrationsAdmitted
    exact instDecidableAnd

private def admissionConditions (book : Book) (operation : Operation) : Prop :=
  operation.posting.source ∈ book.accounts ∧
    operation.posting.destination ∈ book.accounts ∧
    (operation.isIssuerMint = true ∨
      Int.ofNat operation.posting.amount ≤
        book.balance operation.posting.source operation.posting.asset) ∧
    (match operation with
     | .lease leaseId _ _ _ _ epochs _ => 0 < epochs ∧ book.leases leaseId = none
     | _ => True)

instance admissionDecidable (book : Book) (operation : Operation) :
    Decidable (Admission book operation) := by
  haveI : Decidable (admissionConditions book operation) := by
    cases operation <;> unfold admissionConditions <;> infer_instance
  apply decidable_of_iff (admissionConditions book operation)
  cases operation <;>
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
      fun h => ⟨h.sourcePresent, h.destinationPresent, h.sourceSolvent,
        h.leaseWellFormed⟩⟩

def applyOperations (book : Book) : List Operation → Book
  | [] => book
  | operation :: rest => applyOperations (operation.apply book) rest

/-- Solvency is checked on the intermediate book. Two individually affordable
debits are not accepted if their ordered sum overdraws the shared source. -/
def OperationsAdmitted (book : Book) : List Operation → Prop
  | [] => True
  | operation :: rest => Admission book operation ∧
      OperationsAdmitted (operation.apply book) rest

instance operationsDecidable (book : Book) (operations : List Operation) :
    Decidable (OperationsAdmitted book operations) := by
  induction operations generalizing book with
  | nil => exact instDecidableTrue
  | cons operation rest ih =>
    unfold OperationsAdmitted
    exact instDecidableAnd

/-! ## Deregistration: closing a kernel-held account

The inverse of registration, and only for KERNEL-HELD accounts: ids at or above
`protectedBase` (2^256), the protected coordinate space that no birth and no
account cell can take (`ObjectiveActivityCell.reservedBase` is this constant).
The kernel turn that opens such an account derives its id fresh (an activity's
purse is its record cell's id, a function of its birth transaction), so a closed
id is never reopened and the Book keeps no list of closed ids. A user account is
never closed here: capabilities over it live in the authority cell keyed by its
id, and a reopened id would inherit them.

A deregistration is admitted when the account is present, holds no nonzero
balance in ANY asset (read from the balance support, so no hidden coordinate
survives the erase), and no lease record names it as holder or lessor (the Book
has no clock, so every recorded lease counts). Erasing an account with only
zero balances changes no asset's total (`Book.deregisterAccount_conserves`), and
after it every posting naming the account is refused: endpoint presence is part
of `Admission`. -/

/-- The floor of the protected coordinate space: kernel-held account ids. -/
def protectedBase : Nat := 2 ^ 256

def Book.deregisterAccount (book : Book) (account : AccountId) : Book :=
  { book with accounts := book.accounts.erase account }

/-- Whether a lease record names an account (as holder or lessor). -/
def LeaseRecord.names (record : LeaseRecord) (account : AccountId) : Bool :=
  record.holder == account || record.lessor == account

def DeregistrationAdmission (book : Book) (account : AccountId) : Prop :=
  protectedBase ≤ account ∧ account ∈ book.accounts ∧
    (∀ coordinate ∈ book.balances.support, coordinate.1 ≠ account) ∧
    ∀ leaseId ∈ book.leaseRecords.support,
      ((book.leaseRecords leaseId).all fun record => !record.names account) = true

instance (book : Book) (account : AccountId) :
    Decidable (DeregistrationAdmission book account) := by
  unfold DeregistrationAdmission
  infer_instance

theorem DeregistrationAdmission.balance_zero
    {book : Book} {account : AccountId}
    (admitted : DeregistrationAdmission book account) (asset : AssetId) :
    book.balance account asset = 0 := by
  by_contra nonzero
  exact admitted.2.2.1 (account, asset)
    ((DFinsupp.mem_support_toFun _ _).mpr nonzero) rfl

theorem Book.deregisterAccount_conserves
    (book : Book) (account : AccountId)
    (admitted : DeregistrationAdmission book account) (asset : AssetId) :
    (book.deregisterAccount account).totalAsset asset = book.totalAsset asset := by
  change (∑ a ∈ book.accounts.erase account, book.balance a asset) =
    ∑ a ∈ book.accounts, book.balance a asset
  rw [← Finset.add_sum_erase _ _ admitted.2.1, admitted.balance_zero asset, zero_add]

def deregisterAccounts (book : Book) : List AccountId → Book
  | [] => book
  | account :: rest => deregisterAccounts (book.deregisterAccount account) rest

def DeregistrationsAdmitted (book : Book) : List AccountId → Prop
  | [] => True
  | account :: rest => DeregistrationAdmission book account ∧
      DeregistrationsAdmitted (book.deregisterAccount account) rest

instance deregistrationsDecidable (book : Book) (accounts : List AccountId) :
    Decidable (DeregistrationsAdmitted book accounts) := by
  induction accounts generalizing book with
  | nil => exact instDecidableTrue
  | cons account rest ih =>
    unfold DeregistrationsAdmitted
    exact instDecidableAnd

@[simp] theorem deregisterAccounts_nil (book : Book) : deregisterAccounts book [] = book := rfl

@[simp] theorem deregistrationsAdmitted_nil (book : Book) : DeregistrationsAdmitted book [] ↔ True :=
  Iff.rfl

theorem deregisterAccounts_conserves
    (book : Book) (accounts : List AccountId)
    (admitted : DeregistrationsAdmitted book accounts) (asset : AssetId) :
    (deregisterAccounts book accounts).totalAsset asset = book.totalAsset asset := by
  induction accounts generalizing book with
  | nil => rfl
  | cons account rest ih =>
    exact (ih _ admitted.2).trans (book.deregisterAccount_conserves account admitted.1 asset)

@[simp] theorem Book.deregisterAccount_balances (book : Book) (account : AccountId) :
    (book.deregisterAccount account).balances = book.balances := rfl

@[simp] theorem deregisterAccounts_balances (book : Book) (accounts : List AccountId) :
    (deregisterAccounts book accounts).balances = book.balances := by
  induction accounts generalizing book with
  | nil => rfl
  | cons account rest ih => exact ih _

theorem deregisterAccounts_accounts (book : Book) (accounts : List AccountId) :
    (deregisterAccounts book accounts).accounts = accounts.foldl (·.erase ·) book.accounts := by
  induction accounts generalizing book with
  | nil => rfl
  | cons account rest ih => exact ih _

/-- One book-cell patch, regardless of the number of registrations, payments
and closures: register, then post, then close. Closing last lets one batch
drain an account and close it. -/
structure Batch where
  registrations : List AccountId
  operations : List Operation
  deregistrations : List AccountId
  deriving DecidableEq, Repr

def Batch.apply (batch : Batch) (book : Book) : Book :=
  deregisterAccounts
    (applyOperations (registerAccounts book batch.registrations) batch.operations)
    batch.deregistrations

def Batch.Admission (book : Book) (batch : Batch) : Prop :=
  RegistrationsAdmitted book batch.registrations ∧
    OperationsAdmitted (registerAccounts book batch.registrations) batch.operations ∧
    DeregistrationsAdmitted
      (applyOperations (registerAccounts book batch.registrations) batch.operations)
      batch.deregistrations

instance (book : Book) (batch : Batch) : Decidable (batch.Admission book) := by
  unfold Batch.Admission
  infer_instance

/-- Statement first: conservation concerns the actual resulting book. It is
not a caller's claimed resource delta or a count of balanced declarations. -/
def Batch.ConservationStatement : Prop :=
  ∀ (book : Book) (batch : Batch), batch.Admission book →
    ∀ asset, (batch.apply book).totalAsset asset = book.totalAsset asset

theorem registerAccounts_conserves
    (book : Book) (accounts : List AccountId)
    (admitted : RegistrationsAdmitted book accounts) (asset : AssetId) :
    (registerAccounts book accounts).totalAsset asset = book.totalAsset asset := by
  induction accounts generalizing book with
  | nil => rfl
  | cons account rest ih =>
    exact (ih _ admitted.2).trans (book.registerAccount_conserves account admitted.1 asset)

theorem applyOperations_conserves
    (book : Book) (operations : List Operation)
    (admitted : OperationsAdmitted book operations) (asset : AssetId) :
    (applyOperations book operations).totalAsset asset = book.totalAsset asset := by
  induction operations generalizing book with
  | nil => rfl
  | cons operation rest ih =>
    exact (ih _ admitted.2).trans (operation.apply_conserves book
      admitted.1.sourcePresent admitted.1.destinationPresent asset)

theorem operationsAdmitted_append (book : Book) (priorOps suffix : List Operation) :
    OperationsAdmitted book (priorOps ++ suffix) ↔
      OperationsAdmitted book priorOps ∧
        OperationsAdmitted (applyOperations book priorOps) suffix := by
  induction priorOps generalizing book with
  | nil => simp [OperationsAdmitted, applyOperations]
  | cons operation rest ih =>
    simp [OperationsAdmitted, applyOperations, ih, and_assoc]

/-- Every debit reads the exact book after all earlier operations, not the
initial balance reused for each leg. Mint's sole exception is the issuer well
selected by the operation constructor. -/
theorem Batch.source_solvent_at (book : Book) (batch : Batch)
    (admitted : batch.Admission book) (priorOps suffix : List Operation)
    (operation : Operation) (position : batch.operations = priorOps ++ operation :: suffix)
    (notMint : operation.isIssuerMint ≠ true) :
    Int.ofNat operation.posting.amount ≤
      (applyOperations (registerAccounts book batch.registrations) priorOps).balance
        operation.posting.source operation.posting.asset := by
  have ordered := admitted.2.1
  rw [position, operationsAdmitted_append] at ordered
  exact ordered.2.1.sourceSolvent.resolve_left notMint

theorem Batch.conservation : Batch.ConservationStatement := by
  intro book batch admitted asset
  exact (deregisterAccounts_conserves _ _ admitted.2.2 asset).trans
    ((applyOperations_conserves _ _ admitted.2.1 asset).trans
      (registerAccounts_conserves _ _ admitted.1 asset))

/-! ## The refusal, by name

`Batch.refusal?` decides `Batch.Admission` and names the first failing clause:
which registration, which operation (by position) and why, which closure and
why. `Batch.refusal?_eq_none_iff` makes it the admission decision itself, so a
named refusal is never a second judgment beside the admitted one. -/

inductive OperationRefusal where
  /-- The debited account is not registered (never opened, or closed). -/
  | sourceUnregistered (account : AccountId)
  /-- The credited account is not registered (never opened, or closed). -/
  | destinationUnregistered (account : AccountId)
  | overdrawn (account : AccountId) (asset : AssetId)
  | leaseMalformed (leaseId : LeaseId)
  deriving DecidableEq, Repr

inductive DeregistrationRefusal where
  /-- Below `protectedBase`: a user account, which the Book never closes. -/
  | notKernelHeld
  | unregistered
  /-- A nonzero balance remains in some asset. -/
  | balanceRemains
  /-- A lease record names the account. -/
  | leaseNames
  deriving DecidableEq, Repr

inductive BatchRefusal where
  | registration (account : AccountId)
  | operation (position : Nat) (reason : OperationRefusal)
  | deregistration (account : AccountId) (reason : DeregistrationRefusal)
  deriving DecidableEq, Repr

def Operation.refusal? (operation : Operation) (book : Book) : Option OperationRefusal :=
  if operation.posting.source ∉ book.accounts then
    some (.sourceUnregistered operation.posting.source)
  else if operation.posting.destination ∉ book.accounts then
    some (.destinationUnregistered operation.posting.destination)
  else if ¬ (operation.isIssuerMint = true ∨
      Int.ofNat operation.posting.amount ≤
        book.balance operation.posting.source operation.posting.asset) then
    some (.overdrawn operation.posting.source operation.posting.asset)
  else match operation with
    | .lease leaseId _ _ _ _ epochs _ =>
        if 0 < epochs ∧ book.leases leaseId = none then none else some (.leaseMalformed leaseId)
    | _ => none

theorem Operation.refusal?_eq_none_iff (operation : Operation) (book : Book) :
    operation.refusal? book = none ↔ Admission book operation := by
  unfold Operation.refusal?
  by_cases source : operation.posting.source ∈ book.accounts
  · rw [if_neg (not_not.mpr source)]
    by_cases destination : operation.posting.destination ∈ book.accounts
    · rw [if_neg (not_not.mpr destination)]
      by_cases solvent : operation.isIssuerMint = true ∨
          Int.ofNat operation.posting.amount ≤
            book.balance operation.posting.source operation.posting.asset
      · rw [if_neg (not_not.mpr solvent)]
        cases operation with
        | lease leaseId holder lessor asset rate epochs startsAt =>
            simp only
            by_cases wellFormed : 0 < epochs ∧ book.leases leaseId = none
            · rw [if_pos wellFormed]
              exact ⟨fun _ => ⟨source, destination, solvent, wellFormed⟩, fun _ => rfl⟩
            · rw [if_neg wellFormed]
              exact ⟨fun refused => (by cases refused),
                fun admitted => absurd admitted.leaseWellFormed wellFormed⟩
        | _ => exact ⟨fun _ => ⟨source, destination, solvent, trivial⟩, fun _ => rfl⟩
      · rw [if_pos solvent]
        exact ⟨fun refused => (by cases refused), fun admitted => absurd admitted.sourceSolvent solvent⟩
    · rw [if_pos destination]
      exact ⟨fun refused => (by cases refused),
        fun admitted => absurd admitted.destinationPresent destination⟩
  · rw [if_pos source]
    exact ⟨fun refused => (by cases refused), fun admitted => absurd admitted.sourcePresent source⟩

def registrationsRefusal? : Book → List AccountId → Option BatchRefusal
  | _, [] => none
  | book, account :: rest =>
      if RegistrationAdmission book account then registrationsRefusal? (book.registerAccount account) rest
      else some (.registration account)

theorem registrationsRefusal?_eq_none_iff (book : Book) (accounts : List AccountId) :
    registrationsRefusal? book accounts = none ↔ RegistrationsAdmitted book accounts := by
  induction accounts generalizing book with
  | nil => simp [registrationsRefusal?, RegistrationsAdmitted]
  | cons account rest ih =>
    by_cases admitted : RegistrationAdmission book account
    · simp [registrationsRefusal?, RegistrationsAdmitted, admitted, ih]
    · simp [registrationsRefusal?, RegistrationsAdmitted, admitted]

def operationsRefusal? : Nat → Book → List Operation → Option BatchRefusal
  | _, _, [] => none
  | position, book, operation :: rest =>
      match operation.refusal? book with
      | some reason => some (.operation position reason)
      | none => operationsRefusal? (position + 1) (operation.apply book) rest

theorem operationsRefusal?_eq_none_iff (position : Nat) (book : Book) (operations : List Operation) :
    operationsRefusal? position book operations = none ↔ OperationsAdmitted book operations := by
  induction operations generalizing book position with
  | nil => simp [operationsRefusal?, OperationsAdmitted]
  | cons operation rest ih =>
    simp only [operationsRefusal?, OperationsAdmitted]
    cases refused : operation.refusal? book with
    | some reason =>
        simp only [reduceCtorEq, false_iff, not_and]
        intro admitted
        rw [(Operation.refusal?_eq_none_iff operation book).mpr admitted] at refused
        cases refused
    | none =>
        rw [ih]
        simp [(Operation.refusal?_eq_none_iff operation book).mp refused]

def deregistrationRefusal? (book : Book) (account : AccountId) : Option DeregistrationRefusal :=
  if ¬ protectedBase ≤ account then some .notKernelHeld
  else if account ∉ book.accounts then some .unregistered
  else if ¬ ∀ coordinate ∈ book.balances.support, coordinate.1 ≠ account then some .balanceRemains
  else if ¬ ∀ leaseId ∈ book.leaseRecords.support,
      ((book.leaseRecords leaseId).all fun record => !record.names account) = true then
    some .leaseNames
  else none

theorem deregistrationRefusal?_eq_none_iff (book : Book) (account : AccountId) :
    deregistrationRefusal? book account = none ↔ DeregistrationAdmission book account := by
  unfold deregistrationRefusal? DeregistrationAdmission
  by_cases kernel : protectedBase ≤ account
  · rw [if_neg (not_not.mpr kernel)]
    by_cases present : account ∈ book.accounts
    · rw [if_neg (not_not.mpr present)]
      by_cases empty : ∀ coordinate ∈ book.balances.support, coordinate.1 ≠ account
      · rw [if_neg (not_not.mpr empty)]
        by_cases leases : ∀ leaseId ∈ book.leaseRecords.support,
            ((book.leaseRecords leaseId).all fun record => !record.names account) = true
        · rw [if_neg (not_not.mpr leases)]
          exact ⟨fun _ => ⟨kernel, present, empty, leases⟩, fun _ => rfl⟩
        · rw [if_pos leases]
          exact ⟨fun refused => (by cases refused), fun admitted => absurd admitted.2.2.2 leases⟩
      · rw [if_pos empty]
        exact ⟨fun refused => (by cases refused), fun admitted => absurd admitted.2.2.1 empty⟩
    · rw [if_pos present]
      exact ⟨fun refused => (by cases refused), fun admitted => absurd admitted.2.1 present⟩
  · rw [if_pos kernel]
    exact ⟨fun refused => (by cases refused), fun admitted => absurd admitted.1 kernel⟩

def deregistrationsRefusal? : Book → List AccountId → Option BatchRefusal
  | _, [] => none
  | book, account :: rest =>
      match deregistrationRefusal? book account with
      | some reason => some (.deregistration account reason)
      | none => deregistrationsRefusal? (book.deregisterAccount account) rest

theorem deregistrationsRefusal?_eq_none_iff (book : Book) (accounts : List AccountId) :
    deregistrationsRefusal? book accounts = none ↔ DeregistrationsAdmitted book accounts := by
  induction accounts generalizing book with
  | nil => simp [deregistrationsRefusal?, DeregistrationsAdmitted]
  | cons account rest ih =>
    simp only [deregistrationsRefusal?, DeregistrationsAdmitted]
    cases refused : deregistrationRefusal? book account with
    | some reason =>
        simp only [reduceCtorEq, false_iff, not_and]
        intro admitted
        rw [(deregistrationRefusal?_eq_none_iff book account).mpr admitted] at refused
        cases refused
    | none =>
        rw [ih]
        simp [(deregistrationRefusal?_eq_none_iff book account).mp refused]

/-- The first failing clause of a batch, or `none` when it is admitted. -/
def Batch.refusal? (batch : Batch) (book : Book) : Option BatchRefusal :=
  match registrationsRefusal? book batch.registrations with
  | some reason => some reason
  | none =>
    match operationsRefusal? 0 (registerAccounts book batch.registrations) batch.operations with
    | some reason => some reason
    | none => deregistrationsRefusal?
        (applyOperations (registerAccounts book batch.registrations) batch.operations)
        batch.deregistrations

/-- **The named refusal is the admission decision.** -/
theorem Batch.refusal?_eq_none_iff (batch : Batch) (book : Book) :
    batch.refusal? book = none ↔ batch.Admission book := by
  unfold Batch.refusal? Batch.Admission
  rw [← registrationsRefusal?_eq_none_iff, ← operationsRefusal?_eq_none_iff 0,
    ← deregistrationsRefusal?_eq_none_iff]
  cases registrationsRefusal? book batch.registrations <;>
    cases operationsRefusal? 0 (registerAccounts book batch.registrations) batch.operations <;>
    simp

/-- This is the executable fail-closed batch evaluator. A refused batch emits
no post-book. Intermediate registration/payment books are never exposed. -/
def Batch.run (batch : Batch) (book : Book) : Option Book :=
  if batch.Admission book then some (batch.apply book) else none

theorem Batch.run_accepts_iff (batch : Batch) (book post : Book) :
    batch.run book = some post ↔ batch.Admission book ∧ post = batch.apply book := by
  unfold Batch.run
  split_ifs with admitted <;> simp [admitted, eq_comm]

def Batch.patch {M : CellState.Materializer layout Digest}
    (batch : Batch) (pre : CellState.Materialized M) : Patch layout :=
  bookPatch pre.logical (batch.apply (logicalBook pre.logical))

theorem Batch.validated {M : CellState.Materializer layout Digest}
    (batch : Batch) (pre : CellState.Materialized M) :
    CellState.ValidatedPatch M pre pre.root (batch.patch pre) := by
  obtain ⟨validated, _⟩ := CellState.validate_accepts M pre pre.root
    (batch.patch pre) rfl (bookPatch_valid _ _)
  exact validated

structure AcceptedBatch {M : CellState.Materializer layout Digest}
    (pre : CellState.Materialized M) (batch : Batch) : Prop where
  admission : batch.Admission (logicalBook pre.logical)
  validated : CellState.ValidatedPatch M pre pre.root (batch.patch pre)

theorem AcceptedBatch.ofAdmission {M : CellState.Materializer layout Digest}
    {pre : CellState.Materialized M} {batch : Batch}
    (admission : batch.Admission (logicalBook pre.logical)) : AcceptedBatch pre batch :=
  ⟨admission, batch.validated pre⟩

def AcceptedBatch.post {M : CellState.Materializer layout Digest}
    {pre : CellState.Materialized M} {batch : Batch}
    (accepted : AcceptedBatch pre batch) : CellState.Materialized M := accepted.validated.apply

@[simp] theorem AcceptedBatch.post_logicalBook {M : CellState.Materializer layout Digest}
    {pre : CellState.Materialized M} {batch : Batch} (accepted : AcceptedBatch pre batch) :
    logicalBook accepted.post.logical = batch.apply (logicalBook pre.logical) :=
  logicalBook_run_bookPatch _ _

theorem AcceptedBatch.conserves {M : CellState.Materializer layout Digest}
    {pre : CellState.Materialized M} {batch : Batch}
    (accepted : AcceptedBatch pre batch) (asset : AssetId) :
    (logicalBook accepted.post.logical).totalAsset asset =
      (logicalBook pre.logical).totalAsset asset := by
  rw [accepted.post_logicalBook]
  exact Batch.conservation _ _ accepted.admission asset

/-! ## Positive poles: the five constructors do real work -/

theorem mint_debits_issuer
    (book : Book) (asset : AssetId) (destination : AccountId) (amount : Nat)
    (different : asset ≠ destination) :
    ((Operation.mint asset destination amount).apply book).balance asset asset =
      book.balance asset asset - Int.ofNat amount := by
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?,
    Book.applyPosting, Book.balance, DFinsupp.single_apply,
    Ne.symm different, sub_eq_add_neg]

theorem mint_credits_destination
    (book : Book) (asset : AssetId) (destination : AccountId) (amount : Nat)
    (different : destination ≠ asset) :
    ((Operation.mint asset destination amount).apply book).balance destination asset =
      book.balance destination asset + Int.ofNat amount := by
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?,
    Book.applyPosting, Book.balance, DFinsupp.single_apply,
    Ne.symm different]

theorem burn_returns_to_issuer
    (book : Book) (source : AccountId) (asset : AssetId) (amount : Nat)
    (different : asset ≠ source) :
    ((Operation.burn source asset amount).apply book).balance asset asset =
      book.balance asset asset + Int.ofNat amount := by
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?,
    Book.applyPosting, Book.balance, DFinsupp.single_apply,
    Ne.symm different]

theorem fee_debits_payer
    (book : Book) (payer collector : AccountId) (asset : AssetId) (amount : Nat)
    (different : payer ≠ collector) :
    ((Operation.fee payer collector asset amount).apply book).balance payer asset =
      book.balance payer asset - Int.ofNat amount := by
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?,
    Book.applyPosting, Book.balance, DFinsupp.single_apply,
    Ne.symm different, sub_eq_add_neg]

@[simp] theorem lease_installs_exact_record
    (book : Book) (leaseId : LeaseId) (holder lessor : AccountId)
    (asset : AssetId) (rate epochs : Nat) (startsAt : Epoch) :
    ((Operation.lease leaseId holder lessor asset rate epochs startsAt).apply book).leases
      leaseId = some
        { holder := holder
          lessor := lessor
          asset := asset
          prepaid := rate * epochs
          startsAt := startsAt
          expiresAt := startsAt + epochs } := by
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?,
    Book.applyPosting, Book.leases]

/-! ## One-operation batches and the per-asset frame (K-WELL)

A realm well's mint or burn is one signed operation, posted as the batch
`⟨[], [operation], []⟩`. Every operation posts in exactly one asset, so every other
asset's balances are untouched: issuing a realm asset never moves credit. -/

theorem burn_debits_source
    (book : Book) (source : AccountId) (asset : AssetId) (amount : Nat)
    (different : asset ≠ source) :
    ((Operation.burn source asset amount).apply book).balance source asset =
      book.balance source asset - Int.ofNat amount := by
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?,
    Book.applyPosting, Book.balance, DFinsupp.single_apply,
    different, sub_eq_add_neg]

/-- An operation moves only balances of its own posting asset. -/
theorem Operation.apply_balance_other_asset
    (operation : Operation) (book : Book) (account : AccountId) (asset : AssetId)
    (other : operation.posting.asset ≠ asset) :
    (operation.apply book).balance account asset = book.balance account asset := by
  have balances : (operation.apply book).balances = (book.applyPosting operation.posting).balances := by
    cases operation <;> rfl
  have source : ¬ ((operation.posting.source, operation.posting.asset) = (account, asset)) :=
    fun same => other (Prod.mk.inj same).2
  have destination :
      ¬ ((operation.posting.destination, operation.posting.asset) = (account, asset)) :=
    fun same => other (Prod.mk.inj same).2
  unfold Book.balance
  rw [balances]
  simp [Book.applyPosting, DFinsupp.add_apply, DFinsupp.single_apply, source, destination]

@[simp] theorem Batch.single_apply (operation : Operation) (book : Book) :
    (⟨[], [operation], []⟩ : Batch).apply book = operation.apply book := rfl

theorem Batch.single_admission (operation : Operation) (book : Book) :
    (⟨[], [operation], []⟩ : Batch).Admission book ↔ CanonicalResourceKernel.Admission book operation := by
  simp [Batch.Admission, RegistrationsAdmitted, OperationsAdmitted, DeregistrationsAdmitted,
    registerAccounts]

/-- The holders' sum of an asset is the negated well: `Σ_{x ≠ a} bal x a = -bal a a`
whenever the asset's total is zero and its well is a registered account. -/
theorem Book.holders_sum_eq_neg_well (book : Book) (asset : AssetId)
    (present : asset ∈ book.accounts) (zero : book.totalAsset asset = 0) :
    ∑ account ∈ book.accounts.erase asset, book.balance account asset =
      -(book.balance asset asset) := by
  have split := Finset.add_sum_erase book.accounts (fun account => book.balance account asset) present
  simp only at split
  unfold Book.totalAsset at zero
  linarith

/-! ## Negative pole: credit-only mint is not in the language -/

/-- A hostile credit with no issuer-well debit, used only to state the tooth. -/
def Book.creditOnly (book : Book) (destination : AccountId)
    (asset : AssetId) (amount : Nat) : Book where
  accounts := book.accounts
  balances := book.balances +
    DFinsupp.single (destination, asset) (Int.ofNat amount)
  leaseRecords := book.leaseRecords

theorem Book.creditOnly_adds
    (book : Book) (destination : AccountId) (asset : AssetId) (amount : Nat)
    (destinationPresent : destination ∈ book.accounts) :
    (book.creditOnly destination asset amount).totalAsset asset =
      book.totalAsset asset + Int.ofNat amount := by
  classical
  unfold Book.totalAsset Book.creditOnly Book.balance
  simp only [DFinsupp.add_apply]
  rw [Finset.sum_add_distrib]
  simp [DFinsupp.single_apply, destinationPresent]

/-- A positive credit-only mint genuinely violates conservation. -/
theorem Book.creditOnly_breaks_conservation
    (book : Book) (destination : AccountId) (asset : AssetId) (amount : Nat)
    (destinationPresent : destination ∈ book.accounts) (positive : 0 < amount) :
    (book.creditOnly destination asset amount).totalAsset asset ≠
      book.totalAsset asset := by
  have amountNonzero : (Int.ofNat amount : Int) ≠ 0 := by
    exact Int.ofNat_ne_zero.mpr (Nat.ne_of_gt positive)
  rw [book.creditOnly_adds destination asset amount destinationPresent]
  intro unchanged
  omega

/-! ## A concrete non-vacuity witness -/

def witnessBook : Book where
  accounts := {0, 1, 2}
  balances :=
    DFinsupp.single (0, 0) (-8) +
      DFinsupp.single (1, 0) 5 +
      DFinsupp.single (2, 0) 3
  leaseRecords := 0

def witnessLogical : Store layout :=
  (0 : Store layout).set bookAddress (some witnessBook)

/-- The guard of the book patch has teeth: a patch read at the empty store
allocates, and is refused at a store that already holds a book. -/
theorem stale_bookPatch_refused :
    ¬ Patch.ValidFrom witnessLogical (bookPatch 0 witnessBook) := by
  decide

/-- The same post, read at the store it runs against, is enabled there. -/
theorem fresh_bookPatch_valid :
    witnessLogical bookAddress = some witnessBook ∧
      Patch.ValidFrom witnessLogical (bookPatch witnessLogical witnessBook) := by
  decide

def witnessMintAdmission :
    Admission witnessBook (.mint 0 1 2) where
  sourcePresent := by decide
  destinationPresent := by decide
  sourceSolvent := Or.inl rfl
  leaseWellFormed := trivial

/-- An inhabited creation/payment batch: account 3 is opened at zero, a real
fee is paid, then the same payer funds the new account. -/
def witnessBirthBatch : Batch where
  registrations := [3]
  operations := [.fee 1 2 0 1, .transfer 1 3 0 2]
  deregistrations := []

theorem witnessBirthBatch_admitted : witnessBirthBatch.Admission witnessBook := by decide

theorem witnessBirthBatch_payer :
    (witnessBirthBatch.apply witnessBook).balance 1 0 = 2 := by decide

theorem witnessBirthBatch_collector :
    (witnessBirthBatch.apply witnessBook).balance 2 0 = 4 := by decide

theorem witnessBirthBatch_funding :
    (witnessBirthBatch.apply witnessBook).balance 3 0 = 2 := by decide

theorem witnessBirthBatch_conserves (asset : AssetId) :
    (witnessBirthBatch.apply witnessBook).totalAsset asset = witnessBook.totalAsset asset :=
  Batch.conservation _ _ witnessBirthBatch_admitted asset

/-- Both payments fit the initial balance separately, but not in sequence. -/
def witnessOverdrawBatch : Batch where
  registrations := [3]
  operations := [.fee 1 2 0 4, .transfer 1 3 0 2]
  deregistrations := []

theorem witnessOverdrawBatch_rejected : ¬ witnessOverdrawBatch.Admission witnessBook := by decide

theorem witnessOverdrawBatch_no_post : witnessOverdrawBatch.run witnessBook = none := by decide

/-! ### Closing a kernel-held account: the poles

A kernel-held purse (`protectedBase`) is opened, funded, drained and closed in
one batch; every asset's total is unchanged. The teeth: a closure with a
balance left, a closure of a user account, and any posting naming the closed
purse are each refused by name. -/

def witnessPurse : AccountId := protectedBase

/-- Open the purse, fund it, drain it back, close it. -/
def witnessCloseBatch : Batch where
  registrations := [witnessPurse]
  operations := [.transfer 1 witnessPurse 0 2, .transfer witnessPurse 1 0 2]
  deregistrations := [witnessPurse]

theorem witnessCloseBatch_admitted : witnessCloseBatch.Admission witnessBook := by decide

theorem witnessCloseBatch_conserves (asset : AssetId) :
    (witnessCloseBatch.apply witnessBook).totalAsset asset = witnessBook.totalAsset asset :=
  Batch.conservation _ _ witnessCloseBatch_admitted asset

theorem witnessCloseBatch_closed : witnessPurse ∉ (witnessCloseBatch.apply witnessBook).accounts := by
  decide

/-- Closing with a balance left is refused, naming the account and the clause. -/
theorem witness_close_with_balance_refused :
    (⟨[witnessPurse], [.transfer 1 witnessPurse 0 2], [witnessPurse]⟩ : Batch).refusal? witnessBook =
      some (.deregistration witnessPurse .balanceRemains) := by decide

/-- A user account is never closed. -/
theorem witness_close_user_refused :
    (⟨[], [.transfer 1 2 0 5], [1]⟩ : Batch).refusal? witnessBook =
      some (.deregistration 1 .notKernelHeld) := by decide

/-- **A closed account refuses every further posting, by name**: a top-up of
the closed purse names it as the unregistered destination. -/
theorem witness_closed_purse_refuses_posting :
    (⟨[], [.transfer 1 witnessPurse 0 1], []⟩ : Batch).refusal? (witnessCloseBatch.apply witnessBook) =
      some (.operation 0 (.destinationUnregistered witnessPurse)) := by decide

/-- And a debit of it names it as the unregistered source. -/
theorem witness_closed_purse_refuses_debit :
    (⟨[], [.transfer witnessPurse 1 0 0], []⟩ : Batch).refusal? (witnessCloseBatch.apply witnessBook) =
      some (.operation 0 (.sourceUnregistered witnessPurse)) := by decide

/-- In general: once closed, an account is no posting endpoint. -/
theorem deregistered_refuses_posting (book : Book) (account : AccountId) (operation : Operation)
    (names : operation.posting.source = account ∨ operation.posting.destination = account) :
    ¬ Admission (book.deregisterAccount account) operation := by
  intro admitted
  rcases names with same | same
  · exact Finset.notMem_erase account book.accounts (same ▸ admitted.sourcePresent)
  · exact Finset.notMem_erase account book.accounts (same ▸ admitted.destinationPresent)

def witnessHiddenBook : Book where
  accounts := ∅
  balances := DFinsupp.single (9, 0) 7
  leaseRecords := 0

theorem registration_rejects_hidden_balance {book : Book} {account : AccountId}
    {asset : AssetId} (hidden : book.balance account asset ≠ 0) :
    ¬ RegistrationAdmission book account :=
  fun admitted => hidden (admitted.balance_zero asset)

theorem witnessHiddenBook_registration_rejected :
    ¬ RegistrationAdmission witnessHiddenBook 9 := by decide

theorem witnessHiddenBook_unguarded_registration_changes_total :
    (witnessHiddenBook.registerAccount 9).totalAsset 0 ≠
      witnessHiddenBook.totalAsset 0 := by decide

theorem duplicate_registration_rejected (book : Book) (account : AccountId) :
    ¬ RegistrationsAdmitted book [account, account] := by
  intro admitted
  exact admitted.2.1.1 (by simp [Book.registerAccount])

example : witnessBook.totalAsset 0 = 0 := by
  simp only [Book.totalAsset, witnessBook]
  decide

example :
    ((Operation.mint 0 1 2).apply witnessBook).balance 0 0 = -10 := by decide

example :
    ((Operation.mint 0 1 2).apply witnessBook).balance 1 0 = 7 := by decide

example :
    ((Operation.mint 0 1 2).apply witnessBook).totalAsset 0 = 0 := by
  exact Operation.apply_conserves _ _ (by decide) (by decide) 0

example :
    (witnessBook.creditOnly 1 0 2).totalAsset 0 ≠ witnessBook.totalAsset 0 :=
  witnessBook.creditOnly_breaks_conservation 1 0 2 (by decide) (by decide)

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Operation.apply_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Operation.apply_conserves
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Operation.validated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Operation.validated
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Accepted.conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.conserves
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Book.creditOnly_breaks_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Book.creditOnly_breaks_conservation
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.lease_installs_exact_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lease_installs_exact_record

/-- info: 'Minidregg.Theory.CanonicalResourceKernel.burn_debits_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms burn_debits_source
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Operation.apply_balance_other_asset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Operation.apply_balance_other_asset
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Batch.single_admission' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Batch.single_admission
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Book.holders_sum_eq_neg_well' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Book.holders_sum_eq_neg_well
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Book.deregisterAccount_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Book.deregisterAccount_conserves
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Batch.conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Batch.conservation
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Batch.refusal?_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Batch.refusal?_eq_none_iff
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.deregistered_refuses_posting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deregistered_refuses_posting
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.witness_closed_purse_refuses_posting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms witness_closed_purse_refuses_posting

end Minidregg.Theory.CanonicalResourceKernel
