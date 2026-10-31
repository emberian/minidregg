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
* lease prepays `rate * epochs` to a lessor and installs the exact lease record;
* setFloor is a zero-value posting from the asset's issuer well to an account
  that installs that account's floor in the asset;
* sweep moves the exact `recycle` amount of an idle holder's balance to a
  commons account (or, with the issuer well as destination, destroys it).

Thus all seven operations share one per-asset conservation theorem.

Admission has one solvency rule for every account, the issuer well included:
a debit may take the source down to minus its floor
(`amount ≤ balance + floor`).  A floor of 0 is an ordinary account; a floor L
is a credit limit; the well's floor C is its issuance cap, so mint is capped
like every other debit and nets against burns (a lifetime gross-mint ceiling
is a monotone counter, not value, and is not modelled here).  Floors are Book
state, set only by `setFloor`, whose posting source is the issuer well: the
authority that may issue an asset is the authority that may extend credit in
it.  `outstanding_le_sum_floors` bounds the positive balances of an asset by
the sum of its floors.  A separate
credit-only operation is deliberately excluded and proved to break the law.
Physical payment finality, wall-clock expiry, eviction, and durable CAS remain
handler obligations; a logical lease record does not pretend those occurred.

The account book is one typed store address in this bounded nucleus, written
by one guarded operation.  A production
layout may shard balances and leases into sparse fields while preserving the
same operation normalization and conservation law.
-/
module

public import Mathlib.Tactic.DeriveCountable
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Countable.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.DFinsupp.Encodable
public import Theory.CellState
public import Theory.TypedAuthorization
public import Theory.AssertAxioms

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
import all Mathlib.Tactic.DeriveCountable

@[expose] public section

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

/-- A signed account book.  Any account may be negative down to minus its
floor in that asset (`floors`, absent = 0); admission below refuses every debit
that would take its source further. -/
structure Book where
  accounts : Finset AccountId
  balances : Π₀ _ : AccountId × AssetId, Int
  leaseRecords : Π₀ _ : LeaseId, Option LeaseRecord
  floors : Π₀ _ : AccountId × AssetId, Nat
  deriving DecidableEq

deriving instance Countable for Book

def Book.balance (book : Book) (account : AccountId) (asset : AssetId) : Int :=
  book.balances (account, asset)

def Book.leases (book : Book) (leaseId : LeaseId) : Option LeaseRecord :=
  book.leaseRecords leaseId

/-- How far below zero `account` may go in `asset`: 0 for an ordinary account,
a credit limit for a member, the issuance cap for the asset's issuer well. -/
def Book.floor (book : Book) (account : AccountId) (asset : AssetId) : Nat :=
  book.floors (account, asset)

def Book.empty : Book where
  accounts := ∅
  balances := 0
  leaseRecords := 0
  floors := 0

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
  floors := book.floors

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
  /-- Set `account`'s floor in `asset`. Its posting is zero value out of the
  issuer well `asset`, so the well's authority is the authority required. -/
  | setFloor (asset : AssetId) (account : AccountId) (floor : Nat)
  /-- Move `amount = recycle (balance holder asset) permille epochs` from
  `holder` to `commons`; with `commons = asset` it is destruction. -/
  | sweep (holder commons : AccountId) (asset : AssetId) (permille epochs amount : Nat)
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
  | .setFloor asset account _ =>
      ⟨asset, account, asset, 0⟩
  | .sweep holder commons asset _ _ amount =>
      ⟨holder, commons, asset, amount⟩

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

/-- The floor coordinate and value this operation installs, when it is a
`setFloor`. -/
def Operation.floorSetting? : Operation -> Option ((AccountId × AssetId) × Nat)
  | .setFloor asset account floor => some ((account, asset), floor)
  | _ => none

/-- Apply the conserved posting, then install the lease record or the floor
when the operation carries one. -/
def Operation.apply (operation : Operation) (book : Book) : Book :=
  let paid := book.applyPosting operation.posting
  match operation.leaseRecord?, operation.floorSetting? with
  | some (leaseId, record), _ =>
      { paid with leaseRecords := paid.leaseRecords.update leaseId (some record) }
  | none, some (coordinate, floor) =>
      { paid with floors := paid.floors.update coordinate floor }
  | none, none => paid

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
fee, prepaid lease, floor setting and sweep. -/
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

/-- The balance a holder keeps after `epochs` demurrage steps of `permille`
per mille each.  Each step rounds the removed part down, so every rounding
remainder stays with the holder. -/
def retained (permille : Nat) (balance : Nat) : Nat → Nat
  | 0 => balance
  | epochs + 1 =>
      let kept := retained permille balance epochs
      kept - kept * permille / 1000

/-- The amount a sweep moves: the part of a positive balance that `epochs`
demurrage steps remove. A balance at or below zero (credit in use) recycles
nothing. -/
def recycle (balance : Int) (permille epochs : Nat) : Nat :=
  balance.toNat - retained permille balance.toNat epochs

/-- The per-operation shape checks beside solvency: a lease has positive
duration and a fresh identifier; a floor is never set below the balance the
account already holds; a sweep moves exactly `recycle` of the pre-book
balance. -/
def Operation.WellFormed (book : Book) : Operation → Prop
  | .lease leaseId _ _ _ _ epochs _ => 0 < epochs ∧ book.leases leaseId = none
  | .setFloor asset account floor => -(Int.ofNat floor) ≤ book.balance account asset
  | .sweep holder _ asset permille epochs amount =>
      amount = recycle (book.balance holder asset) permille epochs
  | _ => True

instance Operation.wellFormedDecidable (book : Book) (operation : Operation) :
    Decidable (operation.WellFormed book) := by
  cases operation <;> unfold Operation.WellFormed <;> infer_instance

/-- Policy admission is indexed by the exact pre-book and operation.  Endpoint
membership makes the finite-sum law applicable.  Every source, the issuer well
included, may debit down to minus its floor and no further.  The operation's
own shape checks (`Operation.WellFormed`) also hold. -/
structure Admission (book : Book) (operation : Operation) : Prop where
  sourcePresent : operation.posting.source ∈ book.accounts
  destinationPresent : operation.posting.destination ∈ book.accounts
  sourceWithinFloor :
    Int.ofNat operation.posting.amount <=
      book.balance operation.posting.source operation.posting.asset +
        Int.ofNat (book.floor operation.posting.source operation.posting.asset)
  wellFormed : operation.WellFormed book

/-- A debit funded by the balance alone is within any floor. -/
theorem withinFloor_of_funded {book : Book} {operation : Operation}
    (funded : Int.ofNat operation.posting.amount ≤
      book.balance operation.posting.source operation.posting.asset) :
    Int.ofNat operation.posting.amount ≤
      book.balance operation.posting.source operation.posting.asset +
        Int.ofNat (book.floor operation.posting.source operation.posting.asset) :=
  le_trans funded (le_add_of_nonneg_right (Int.natCast_nonneg _))

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

/-- Freshness and absence of every hidden nonzero balance and hidden floor
are checked: a registered account starts at zero with floor zero. -/
def RegistrationAdmission (book : Book) (account : AccountId) : Prop :=
  account ∉ book.accounts ∧
    (∀ coordinate ∈ book.balances.support, coordinate.1 ≠ account) ∧
    ∀ coordinate ∈ book.floors.support, coordinate.1 ≠ account

instance (book : Book) (account : AccountId) :
    Decidable (RegistrationAdmission book account) := by
  unfold RegistrationAdmission
  infer_instance

theorem RegistrationAdmission.balance_zero
    {book : Book} {account : AccountId}
    (admitted : RegistrationAdmission book account) (asset : AssetId) :
    book.balance account asset = 0 := by
  by_contra nonzero
  exact admitted.2.1 (account, asset)
    ((DFinsupp.mem_support_toFun _ _).mpr nonzero) rfl

theorem RegistrationAdmission.floor_zero
    {book : Book} {account : AccountId}
    (admitted : RegistrationAdmission book account) (asset : AssetId) :
    book.floor account asset = 0 := by
  by_contra nonzero
  exact admitted.2.2 (account, asset)
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
    Int.ofNat operation.posting.amount ≤
      book.balance operation.posting.source operation.posting.asset +
        Int.ofNat (book.floor operation.posting.source operation.posting.asset) ∧
    operation.WellFormed book

instance admissionDecidable (book : Book) (operation : Operation) :
    Decidable (Admission book operation) := by
  haveI : Decidable (admissionConditions book operation) := by
    unfold admissionConditions; infer_instance
  apply decidable_of_iff (admissionConditions book operation)
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
    fun h => ⟨h.sourcePresent, h.destinationPresent, h.sourceWithinFloor, h.wellFormed⟩⟩

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
    (∀ leaseId ∈ book.leaseRecords.support,
      ((book.leaseRecords leaseId).all fun record => !record.names account) = true) ∧
    ∀ coordinate ∈ book.floors.support, coordinate.1 ≠ account

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

@[simp] theorem deregisterAccounts_floors (book : Book) (accounts : List AccountId) :
    (deregisterAccounts book accounts).floors = book.floors := by
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
initial balance reused for each leg, and no source (the issuer well included)
is excepted from its floor. -/
theorem Batch.source_within_floor_at (book : Book) (batch : Batch)
    (admitted : batch.Admission book) (priorOps suffix : List Operation)
    (operation : Operation) (position : batch.operations = priorOps ++ operation :: suffix) :
    let at_ := applyOperations (registerAccounts book batch.registrations) priorOps
    Int.ofNat operation.posting.amount ≤
      at_.balance operation.posting.source operation.posting.asset +
        Int.ofNat (at_.floor operation.posting.source operation.posting.asset) := by
  have ordered := admitted.2.1
  rw [position, operationsAdmitted_append] at ordered
  exact ordered.2.1.sourceWithinFloor

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
  /-- The debit would take the source below minus its floor in the asset
  (for the issuer well: past its issuance cap). -/
  | belowFloor (account : AccountId) (asset : AssetId)
  | leaseMalformed (leaseId : LeaseId)
  /-- The new floor is below what the account already owes. -/
  | floorBelowBalance (account : AccountId) (asset : AssetId)
  /-- The sweep amount is not `recycle` of the holder's balance. -/
  | sweepInexact (holder : AccountId) (asset : AssetId)
  deriving DecidableEq, Repr

inductive DeregistrationRefusal where
  /-- Below `protectedBase`: a user account, which the Book never closes. -/
  | notKernelHeld
  | unregistered
  /-- A nonzero balance remains in some asset. -/
  | balanceRemains
  /-- A lease record names the account. -/
  | leaseNames
  /-- A nonzero floor remains in some asset: close the credit line first. -/
  | floorRemains
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
  else if ¬ (Int.ofNat operation.posting.amount ≤
      book.balance operation.posting.source operation.posting.asset +
        Int.ofNat (book.floor operation.posting.source operation.posting.asset)) then
    some (.belowFloor operation.posting.source operation.posting.asset)
  else match operation with
    | .lease leaseId _ _ _ _ epochs _ =>
        if 0 < epochs ∧ book.leases leaseId = none then none else some (.leaseMalformed leaseId)
    | .setFloor asset account floor =>
        if -(Int.ofNat floor) ≤ book.balance account asset then none
        else some (.floorBelowBalance account asset)
    | .sweep holder _ asset permille epochs amount =>
        if amount = recycle (book.balance holder asset) permille epochs then none
        else some (.sweepInexact holder asset)
    | _ => none

theorem Operation.refusal?_eq_none_iff (operation : Operation) (book : Book) :
    operation.refusal? book = none ↔ Admission book operation := by
  unfold Operation.refusal?
  by_cases source : operation.posting.source ∈ book.accounts
  · rw [if_neg (not_not.mpr source)]
    by_cases destination : operation.posting.destination ∈ book.accounts
    · rw [if_neg (not_not.mpr destination)]
      by_cases within : Int.ofNat operation.posting.amount ≤
          book.balance operation.posting.source operation.posting.asset +
            Int.ofNat (book.floor operation.posting.source operation.posting.asset)
      · rw [if_neg (not_not.mpr within)]
        cases operation with
        | lease leaseId holder lessor asset rate epochs startsAt =>
            simp only
            by_cases formed : 0 < epochs ∧ book.leases leaseId = none
            · rw [if_pos formed]
              exact ⟨fun _ => ⟨source, destination, within, formed⟩, fun _ => rfl⟩
            · rw [if_neg formed]
              exact ⟨fun refused => (by cases refused),
                fun admitted => absurd admitted.wellFormed formed⟩
        | setFloor asset account floor =>
            simp only
            by_cases formed : -(Int.ofNat floor) ≤ book.balance account asset
            · rw [if_pos formed]
              exact ⟨fun _ => ⟨source, destination, within, formed⟩, fun _ => rfl⟩
            · rw [if_neg formed]
              exact ⟨fun refused => (by cases refused),
                fun admitted => absurd admitted.wellFormed formed⟩
        | sweep holder commons asset permille epochs amount =>
            simp only
            by_cases formed : amount = recycle (book.balance holder asset) permille epochs
            · rw [if_pos formed]
              exact ⟨fun _ => ⟨source, destination, within, formed⟩, fun _ => rfl⟩
            · rw [if_neg formed]
              exact ⟨fun refused => (by cases refused),
                fun admitted => absurd admitted.wellFormed formed⟩
        | _ => exact ⟨fun _ => ⟨source, destination, within, trivial⟩, fun _ => rfl⟩
      · rw [if_pos within]
        exact ⟨fun refused => (by cases refused), fun admitted => absurd admitted.sourceWithinFloor within⟩
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
  else if ¬ ∀ coordinate ∈ book.floors.support, coordinate.1 ≠ account then some .floorRemains
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
          by_cases floors : ∀ coordinate ∈ book.floors.support, coordinate.1 ≠ account
          · rw [if_neg (not_not.mpr floors)]
            exact ⟨fun _ => ⟨kernel, present, empty, leases, floors⟩, fun _ => rfl⟩
          · rw [if_pos floors]
            exact ⟨fun refused => (by cases refused), fun admitted => absurd admitted.2.2.2.2 floors⟩
        · rw [if_pos leases]
          exact ⟨fun refused => (by cases refused), fun admitted => absurd admitted.2.2.2.1 leases⟩
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

/-! ## Positive poles: the value constructors do real work -/

theorem mint_debits_issuer
    (book : Book) (asset : AssetId) (destination : AccountId) (amount : Nat)
    (different : asset ≠ destination) :
    ((Operation.mint asset destination amount).apply book).balance asset asset =
      book.balance asset asset - Int.ofNat amount := by
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?, Operation.floorSetting?,
    Book.applyPosting, Book.balance, DFinsupp.single_apply,
    Ne.symm different, sub_eq_add_neg]

theorem mint_credits_destination
    (book : Book) (asset : AssetId) (destination : AccountId) (amount : Nat)
    (different : destination ≠ asset) :
    ((Operation.mint asset destination amount).apply book).balance destination asset =
      book.balance destination asset + Int.ofNat amount := by
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?, Operation.floorSetting?,
    Book.applyPosting, Book.balance, DFinsupp.single_apply,
    Ne.symm different]

theorem burn_returns_to_issuer
    (book : Book) (source : AccountId) (asset : AssetId) (amount : Nat)
    (different : asset ≠ source) :
    ((Operation.burn source asset amount).apply book).balance asset asset =
      book.balance asset asset + Int.ofNat amount := by
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?, Operation.floorSetting?,
    Book.applyPosting, Book.balance, DFinsupp.single_apply,
    Ne.symm different]

theorem fee_debits_payer
    (book : Book) (payer collector : AccountId) (asset : AssetId) (amount : Nat)
    (different : payer ≠ collector) :
    ((Operation.fee payer collector asset amount).apply book).balance payer asset =
      book.balance payer asset - Int.ofNat amount := by
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?, Operation.floorSetting?,
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
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?, Operation.floorSetting?,
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
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?, Operation.floorSetting?,
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
  floors := book.floors

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

/-! ## Floors: one solvency rule for wells, credit and ordinary accounts

`Admission.sourceWithinFloor` is the only solvency check.  The four facts below
are what it buys: the floor law is an invariant of admitted operations and
batches; under it the positive balances of an asset never exceed the sum of
its floors; with ordinary floors at zero and a well whose floor covers its
mints, it decides exactly what the deleted `isIssuerMint ∨ amount ≤ balance`
rule decided; and the decayed display of a swept balance is what the sweep
writes. -/

/-- Every account holds at least minus its floor in `asset`. -/
def Book.WithinFloors (book : Book) (asset : AssetId) : Prop :=
  ∀ account, -(Int.ofNat (book.floor account asset)) ≤ book.balance account asset

private theorem single_pair_apply (p q : AccountId × AssetId) (v : Int) :
    (DFinsupp.single p v : Π₀ _ : AccountId × AssetId, Int) q = if p = q then v else 0 := by
  by_cases h : p = q
  · subst h; simp
  · rw [if_neg h, DFinsupp.single_apply, dif_neg h]

/-- One posting's effect on one coordinate, for every operation. -/
theorem Operation.apply_balance (operation : Operation) (book : Book)
    (account : AccountId) (asset : AssetId) :
    (operation.apply book).balance account asset =
      book.balance account asset
        - (if (operation.posting.source, operation.posting.asset) = (account, asset)
            then Int.ofNat operation.posting.amount else 0)
        + (if (operation.posting.destination, operation.posting.asset) = (account, asset)
            then Int.ofNat operation.posting.amount else 0) := by
  have balances :
      (operation.apply book).balances = (book.applyPosting operation.posting).balances := by
    cases operation <;> rfl
  unfold Book.balance
  rw [balances]
  simp only [Book.applyPosting, DFinsupp.add_apply, single_pair_apply]
  split_ifs <;> ring

/-- Only `setFloor` writes a floor. -/
theorem Operation.apply_floor_of_not_setFloor (operation : Operation) (book : Book)
    (account : AccountId) (asset : AssetId)
    (notSet : ∀ wellAsset target floor, operation ≠ .setFloor wellAsset target floor) :
    (operation.apply book).floor account asset = book.floor account asset := by
  cases operation with
  | setFloor wellAsset target floor => exact absurd rfl (notSet wellAsset target floor)
  | _ => rfl

theorem setFloor_floor (book : Book) (wellAsset target : AccountId) (floor : Nat)
    (account : AccountId) (asset : AssetId) :
    ((Operation.setFloor wellAsset target floor).apply book).floor account asset =
      if (account, asset) = (target, wellAsset) then floor else book.floor account asset := by
  simp [Operation.apply, Operation.leaseRecord?, Operation.floorSetting?, Book.floor,
    Book.applyPosting, DFinsupp.coe_update, Function.update_apply]

/-- A floor setting moves no value. -/
theorem setFloor_moves_no_value (book : Book) (wellAsset target : AccountId) (floor : Nat)
    (account : AccountId) (asset : AssetId) :
    ((Operation.setFloor wellAsset target floor).apply book).balance account asset =
      book.balance account asset := by
  rw [Operation.apply_balance]
  simp [Operation.posting]

/-- **Admitted operations preserve the floor law.** -/
theorem admitted_preserves_floors (book : Book) (operation : Operation) (asset : AssetId)
    (within : book.WithinFloors asset) (admitted : Admission book operation) :
    (operation.apply book).WithinFloors asset := by
  intro account
  have moved : -(Int.ofNat (book.floor account asset)) ≤
      (operation.apply book).balance account asset := by
    rw [Operation.apply_balance]
    have old := within account
    have debit := admitted.sourceWithinFloor
    have credit : (0 : Int) ≤
        (if (operation.posting.destination, operation.posting.asset) = (account, asset)
          then Int.ofNat operation.posting.amount else 0) := by
      split_ifs <;> simp
    by_cases source : (operation.posting.source, operation.posting.asset) = (account, asset)
    · rw [if_pos source]
      obtain ⟨sameAccount, sameAsset⟩ := Prod.mk.inj source
      rw [sameAccount, sameAsset] at debit
      linarith
    · rw [if_neg source]
      linarith
  cases operation with
  | setFloor wellAsset target floor =>
      rw [setFloor_floor]
      by_cases same : (account, asset) = (target, wellAsset)
      · rw [if_pos same, setFloor_moves_no_value]
        obtain ⟨sameAccount, sameAsset⟩ := Prod.mk.inj same
        rw [sameAccount, sameAsset]
        exact admitted.wellFormed
      · rw [if_neg same]
        exact moved
  | _ => exact moved

theorem applyOperations_preserves_floors (book : Book) (operations : List Operation)
    (asset : AssetId) (within : book.WithinFloors asset)
    (admitted : OperationsAdmitted book operations) :
    (applyOperations book operations).WithinFloors asset := by
  induction operations generalizing book with
  | nil => exact within
  | cons operation rest ih =>
      exact ih _ (admitted_preserves_floors book operation asset within admitted.1) admitted.2

theorem registerAccounts_withinFloors (book : Book) (accounts : List AccountId)
    (asset : AssetId) (within : book.WithinFloors asset) :
    (registerAccounts book accounts).WithinFloors asset := by
  induction accounts generalizing book with
  | nil => exact within
  | cons account rest ih => exact ih _ within

theorem deregisterAccounts_withinFloors (book : Book) (accounts : List AccountId)
    (asset : AssetId) (within : book.WithinFloors asset) :
    (deregisterAccounts book accounts).WithinFloors asset := by
  induction accounts generalizing book with
  | nil => exact within
  | cons account rest ih => exact ih _ within

/-- **An admitted batch preserves the floor law.** -/
theorem Batch.apply_withinFloors (book : Book) (batch : Batch) (asset : AssetId)
    (within : book.WithinFloors asset) (admitted : batch.Admission book) :
    (batch.apply book).WithinFloors asset :=
  deregisterAccounts_withinFloors _ _ asset
    (applyOperations_preserves_floors _ _ asset
      (registerAccounts_withinFloors _ _ asset within) admitted.2.1)

/-- **Outstanding value is bounded by the floors.**  Over a conserved asset
(its total, issuer well included, is zero) the positive balances sum to at
most the sum of the floors: the issuance cap plus every credit limit. -/
theorem outstanding_le_sum_floors (book : Book) (asset : AssetId)
    (within : book.WithinFloors asset) (conserved : book.totalAsset asset = 0) :
    ∑ account ∈ book.accounts, max 0 (book.balance account asset) ≤
      ∑ account ∈ book.accounts, Int.ofNat (book.floor account asset) := by
  have split : ∀ account, max 0 (book.balance account asset) =
      book.balance account asset + max 0 (-(book.balance account asset)) := by
    intro account
    simp only [max_def]
    split_ifs <;> linarith
  calc ∑ account ∈ book.accounts, max 0 (book.balance account asset)
      = ∑ account ∈ book.accounts,
          (book.balance account asset + max 0 (-(book.balance account asset))) :=
        Finset.sum_congr rfl (fun account _ => split account)
    _ = book.totalAsset asset +
          ∑ account ∈ book.accounts, max 0 (-(book.balance account asset)) := by
        rw [Finset.sum_add_distrib]; rfl
    _ = ∑ account ∈ book.accounts, max 0 (-(book.balance account asset)) := by
        rw [conserved, zero_add]
    _ ≤ ∑ account ∈ book.accounts, Int.ofNat (book.floor account asset) := by
        apply Finset.sum_le_sum
        intro account _
        have bound := within account
        exact max_le (by simp) (by linarith)

/-- **Floors reproduce the deleted solvency rule.**  Admission used to read
`isIssuerMint ∨ amount ≤ balance`: a mint was solvent unconditionally and
every other debit needed its balance.  When every non-mint source has floor 0
and the issuer well's floor covers the mint (the finite form of the old
unbounded well), the floor rule admits exactly the same debits. -/
theorem sourceWithinFloor_iff_preFloorRule (book : Book) (operation : Operation)
    (ordinaryZero : (∀ asset destination amount, operation ≠ .mint asset destination amount) →
      book.floor operation.posting.source operation.posting.asset = 0)
    (wellCovers : ∀ asset destination amount, operation = .mint asset destination amount →
      Int.ofNat amount ≤ book.balance asset asset + Int.ofNat (book.floor asset asset)) :
    (Int.ofNat operation.posting.amount ≤
        book.balance operation.posting.source operation.posting.asset +
          Int.ofNat (book.floor operation.posting.source operation.posting.asset)) ↔
      ((∃ asset destination amount, operation = .mint asset destination amount) ∨
        Int.ofNat operation.posting.amount ≤
          book.balance operation.posting.source operation.posting.asset) := by
  by_cases mint : ∃ asset destination amount, operation = .mint asset destination amount
  · obtain ⟨asset, destination, amount, rfl⟩ := mint
    exact ⟨fun _ => Or.inl ⟨asset, destination, amount, rfl⟩,
      fun _ => wellCovers asset destination amount rfl⟩
  · have zero := ordinaryZero
      (fun asset destination amount same => mint ⟨asset, destination, amount, same⟩)
    rw [zero]
    simp only [Int.ofNat_eq_natCast, Nat.cast_zero, add_zero]
    exact ⟨Or.inr, fun admitted => admitted.resolve_left mint⟩

/-- The same equivalence at the level of the whole admission: the remaining
clauses (endpoints present, lease shape) are the ones the pre-floor admission
had, and `setFloor`/`sweep` did not exist before. -/
theorem admission_iff_preFloorRule (book : Book) (operation : Operation)
    (ordinaryZero : (∀ asset destination amount, operation ≠ .mint asset destination amount) →
      book.floor operation.posting.source operation.posting.asset = 0)
    (wellCovers : ∀ asset destination amount, operation = .mint asset destination amount →
      Int.ofNat amount ≤ book.balance asset asset + Int.ofNat (book.floor asset asset)) :
    Admission book operation ↔
      (operation.posting.source ∈ book.accounts ∧
        operation.posting.destination ∈ book.accounts ∧
        ((∃ asset destination amount, operation = .mint asset destination amount) ∨
          Int.ofNat operation.posting.amount ≤
            book.balance operation.posting.source operation.posting.asset) ∧
        operation.WellFormed book) := by
  rw [← sourceWithinFloor_iff_preFloorRule book operation ordinaryZero wellCovers]
  exact ⟨fun admitted => ⟨admitted.sourcePresent, admitted.destinationPresent,
      admitted.sourceWithinFloor, admitted.wellFormed⟩,
    fun ⟨source, destination, within, formed⟩ => ⟨source, destination, within, formed⟩⟩

/-! ### Sweep: commons recycling (or destruction) as a posting -/

theorem retained_le (permille balance epochs : Nat) :
    retained permille balance epochs ≤ balance := by
  induction epochs with
  | zero => exact le_refl _
  | succ epochs ih =>
      simp only [retained]
      exact le_trans (Nat.sub_le _ _) ih

/-- A sweep is the posting `holder → commons` of exactly its amount. -/
@[simp] theorem sweep_posting (holder commons : AccountId) (asset : AssetId)
    (permille epochs amount : Nat) :
    (Operation.sweep holder commons asset permille epochs amount).posting =
      ⟨holder, commons, asset, amount⟩ := rfl

/-- What a holder's balance reads as after `epochs` demurrage steps: a view
computed from the Book, never stored in it. -/
def displayBalance (balance : Int) (permille epochs : Nat) : Int :=
  balance - Int.ofNat (recycle balance permille epochs)

/-- For a positive balance the display is exactly the retained amount. -/
theorem displayBalance_eq_retained (balance permille epochs : Nat) :
    displayBalance (Int.ofNat balance) permille epochs =
      Int.ofNat (retained permille balance epochs) := by
  have kept := retained_le permille balance epochs
  simp only [displayBalance, recycle, Int.toNat_natCast, Int.ofNat_eq_natCast]
  omega

/-- **The display is honest**: an admitted sweep writes exactly the displayed
balance into the Book. -/
theorem sweep_materializes_display (book : Book) (holder commons : AccountId)
    (asset : AssetId) (permille epochs amount : Nat) (distinct : holder ≠ commons)
    (admitted : Admission book (.sweep holder commons asset permille epochs amount)) :
    ((Operation.sweep holder commons asset permille epochs amount).apply book).balance
        holder asset =
      displayBalance (book.balance holder asset) permille epochs := by
  have exact : amount = recycle (book.balance holder asset) permille epochs :=
    admitted.wellFormed
  rw [Operation.apply_balance]
  simp [Ne.symm distinct, displayBalance, exact]

/-! ### A mutual-credit book: capped issuance, credit limits, one sweep -/

/-- Issuer well 10 (so asset 10), members 11 and 12, commons 13, all at zero
with no floors. -/
def creditBook : Book where
  accounts := {10, 11, 12, 13}
  balances := 0
  leaseRecords := 0
  floors := 0

theorem creditBook_withinFloors : creditBook.WithinFloors 10 := by
  intro account
  simp [creditBook, Book.balance, Book.floor]

/-- The well caps issuance at 100 and grants each member a credit limit of 20,
mints 50 to member 11, member 12 pays 15 on credit, and an idle-epoch sweep at
100 per mille moves 6 of member 11's 65 to the commons (6.5, rounded down; the
half stays with the holder). -/
def creditBatch : Batch where
  registrations := []
  operations :=
    [.setFloor 10 10 100, .setFloor 10 11 20, .setFloor 10 12 20,
     .mint 10 11 50,
     .transfer 12 11 10 15,
     .sweep 11 13 10 100 1 6]
  deregistrations := []

theorem creditBatch_admitted : creditBatch.Admission creditBook := by decide

def creditPost : Book := creditBatch.apply creditBook

theorem creditPost_balances :
    creditPost.balance 10 10 = -50 ∧ creditPost.balance 11 10 = 59 ∧
      creditPost.balance 12 10 = -15 ∧ creditPost.balance 13 10 = 6 := by decide

/-- The sweep wrote the displayed balance: 65 shown after one epoch is 59. -/
theorem creditPost_holder_display :
    creditPost.balance 11 10 = displayBalance 65 100 1 := by decide

theorem creditPost_withinFloors : creditPost.WithinFloors 10 :=
  Batch.apply_withinFloors _ _ 10 creditBook_withinFloors creditBatch_admitted

theorem creditPost_conserved : creditPost.totalAsset 10 = 0 := by
  rw [creditPost, Batch.conservation _ _ creditBatch_admitted]
  simp [Book.totalAsset, Book.balance, creditBook]

/-- 65 outstanding, bounded by the cap and both limits, 140. -/
theorem creditPost_outstanding :
    ∑ account ∈ creditPost.accounts, max 0 (creditPost.balance account 10) ≤
      ∑ account ∈ creditPost.accounts, Int.ofNat (creditPost.floor account 10) :=
  outstanding_le_sum_floors _ 10 creditPost_withinFloors creditPost_conserved

/-- **A debit past a credit limit is refused by name**: member 12 owes 15 of
its 20; paying 6 more would leave it at -21. -/
theorem credit_limit_refused :
    (⟨[], [.transfer 12 11 10 6], []⟩ : Batch).refusal? creditPost =
      some (.operation 0 (.belowFloor 12 10)) := by decide

/-- Paying 5 reaches the limit exactly and is admitted. -/
theorem credit_limit_reached_admitted :
    (⟨[], [.transfer 12 11 10 5], []⟩ : Batch).refusal? creditPost = none := by decide

/-- **A mint past the issuance cap is refused by name**: the well has issued 50
of 100; 51 more would leave it at -101. -/
theorem issuance_cap_refused :
    (⟨[], [.mint 10 11 51], []⟩ : Batch).refusal? creditPost =
      some (.operation 0 (.belowFloor 10 10)) := by decide

/-- Burns restore headroom: the cap bounds net issuance. -/
theorem issuance_cap_nets_burns :
    (⟨[], [.burn 11 10 10, .mint 10 11 60], []⟩ : Batch).refusal? creditPost = none := by
  decide

/-- A limit is never lowered under what the member already owes. -/
theorem floor_under_debt_refused :
    (⟨[], [.setFloor 10 12 10], []⟩ : Batch).refusal? creditPost =
      some (.operation 0 (.floorBelowBalance 12 10)) := by decide

/-- The book just before the sweep: member 11 holds 65. -/
def creditBeforeSweep : Book := (⟨[], creditBatch.operations.take 5, []⟩ : Batch).apply creditBook

/-- A sweep that moves anything but `recycle` of the balance is refused. -/
theorem sweep_inexact_refused :
    (⟨[], [.sweep 11 13 10 100 1 7], []⟩ : Batch).refusal? creditBeforeSweep =
      some (.operation 0 (.sweepInexact 11 10)) := by decide

/-- Destruction is the same posting with the issuer well as destination: the 6
return to the well, whose debt falls from 50 to 44. -/
theorem sweep_to_well_destroys :
    (⟨[], [.sweep 11 10 10 100 1 6], []⟩ : Batch).refusal? creditBeforeSweep = none ∧
      ((Operation.sweep 11 10 10 100 1 6).apply creditBeforeSweep).balance 10 10 = -44 := by
  decide

/-! ## A concrete non-vacuity witness -/

def witnessBook : Book where
  accounts := {0, 1, 2}
  balances :=
    DFinsupp.single (0, 0) (-8) +
      DFinsupp.single (1, 0) 5 +
      DFinsupp.single (2, 0) 3
  leaseRecords := 0
  floors := DFinsupp.single (0, 0) 10

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
  sourceWithinFloor := by decide
  wellFormed := trivial

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

theorem deregisterAccounts_not_mem (book : Book) (accounts : List AccountId) (account : AccountId)
    (closed : account ∈ accounts ∨ account ∉ book.accounts) :
    account ∉ (deregisterAccounts book accounts).accounts := by
  induction accounts generalizing book with
  | nil => simpa using closed
  | cons first rest ih =>
    apply ih
    rcases closed with member | absent
    · rcases List.mem_cons.mp member with same | later
      · subst same; exact Or.inr (Finset.notMem_erase _ _)
      · exact Or.inl later
    · exact Or.inr (fun present => absent (Finset.mem_of_mem_erase present))

/-- **A batch's closures hold after it**: an account the batch deregisters is no
account of the book it leaves. -/
theorem Batch.apply_deregistered (batch : Batch) (book : Book) (account : AccountId)
    (closed : account ∈ batch.deregistrations) : account ∉ (batch.apply book).accounts :=
  deregisterAccounts_not_mem _ _ _ (Or.inl closed)

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
  floors := 0

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
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Batch.apply_deregistered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Batch.apply_deregistered
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.witness_closed_purse_refuses_posting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms witness_closed_purse_refuses_posting

#assert_axioms admitted_preserves_floors
#assert_axioms Batch.apply_withinFloors
#assert_axioms outstanding_le_sum_floors
#assert_axioms sourceWithinFloor_iff_preFloorRule
#assert_axioms admission_iff_preFloorRule
#assert_axioms sweep_materializes_display
#assert_axioms displayBalance_eq_retained
#assert_axioms creditPost_outstanding
#assert_axioms credit_limit_refused
#assert_axioms issuance_cap_refused
#assert_axioms floor_under_debt_refused
#assert_axioms sweep_inexact_refused
#assert_axioms sweep_to_well_destroys

end Minidregg.Theory.CanonicalResourceKernel
