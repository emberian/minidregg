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

The account book is one typed field in this bounded nucleus.  A production
layout may shard balances and leases into sparse fields while preserving the
same operation normalization and conservation law.
-/
import Theory.CellState
import Theory.TypedAuthorization

namespace Minidregg.Theory.CanonicalResourceKernel

open Minidregg.Theory
open Minidregg.Theory.CellState
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

/-- This bounded nucleus uses one typed book field.  There is no untyped map and
no resource package whose authority could be forged independently. -/
inductive Field
  | book
  deriving DecidableEq, Repr

deriving instance Countable for Field

def schema : CellState.Schema.{0, 0, 0, 0} where
  Field := Field
  FieldType := fun _ => Book
  Resource := Empty
  ResourceType := fun resource => nomatch resource
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

local instance schemaFieldDecidableEq : DecidableEq schema.Field := by
  change DecidableEq Field
  infer_instance

local instance schemaResourceDecidableEq : DecidableEq schema.Resource := by
  change DecidableEq Empty
  infer_instance

/-- Absence of the book field denotes the empty book at the semantic layer. -/
def logicalBook (logical : CellState.LogicalState schema) : Book :=
  (logical.fields.read .book).getD Book.empty

/-- The exact patch is derived from the exact materialized pre-cell.  Callers do
not supply balances, a post-book, a footprint, or a post-root. -/
def Operation.patch
    {M : CellState.Materializer schema Digest}
    (operation : Operation) (pre : CellState.Materialized M) :
    CellState.Patch schema Digest where
  expectedPreRoot := pre.root
  fieldFootprint := {.book}
  resourceFootprint := ∅
  fieldWrites :=
    [{ field := .book, value := some (operation.apply (logicalBook pre.logical)) }]
  resourceWrites := []

/-- The derived patch always passes the structural cell validator. -/
theorem Operation.validated_nonempty
    {M : CellState.Materializer schema Digest}
    (operation : Operation) (pre : CellState.Materialized M) :
    Nonempty (CellState.ValidatedPatch M pre (operation.patch pre)) := by
  have accepted :
      ∃ validated : CellState.ValidatedPatch M pre (operation.patch pre),
        CellState.validate M pre (operation.patch pre) =
          .accepted validated := by
    unfold CellState.validate
    rw [dif_pos (show (operation.patch pre).expectedPreRoot = pre.root from rfl)]
    rw [dif_pos (show (operation.patch pre).fieldFootprint =
      (operation.patch pre).namedFields by
        simp [Operation.patch, CellState.Patch.namedFields])]
    rw [dif_pos (show (operation.patch pre).resourceFootprint =
      (operation.patch pre).namedResources by
        simp [Operation.patch, CellState.Patch.namedResources])]
    exact ⟨_, rfl⟩
  exact ⟨accepted.choose⟩

/-- Canonical selection of the verifier-minted proof produced above. -/
noncomputable def Operation.validated
    {M : CellState.Materializer schema Digest}
    (operation : Operation) (pre : CellState.Materialized M) :
    CellState.ValidatedPatch M pre (operation.patch pre) :=
  Classical.choice (operation.validated_nonempty pre)

/-- The accepted resource token joins policy to the one derived typed patch.
It does not claim a database transaction or an external lease clock advanced. -/
structure Accepted
    {M : CellState.Materializer schema Digest}
    (pre : CellState.Materialized M) (operation : Operation) : Prop where
  admission : Admission (logicalBook pre.logical) operation
  validated : CellState.ValidatedPatch M pre (operation.patch pre)

/-- Once policy admission is proved, no host-supplied post data remains. -/
noncomputable def Accepted.ofAdmission
    {M : CellState.Materializer schema Digest}
    {pre : CellState.Materialized M} {operation : Operation}
    (admission : Admission (logicalBook pre.logical) operation) :
    Accepted pre operation :=
  ⟨admission, operation.validated pre⟩

def Accepted.post
    {M : CellState.Materializer schema Digest}
    {pre : CellState.Materialized M} {operation : Operation}
    (accepted : Accepted pre operation) : CellState.Materialized M :=
  accepted.validated.apply

/-- Applying the accepted typed patch installs exactly `Operation.apply`. -/
@[simp] theorem Accepted.post_logicalBook
    {M : CellState.Materializer schema Digest}
    {pre : CellState.Materialized M} {operation : Operation}
  (accepted : Accepted pre operation) :
    logicalBook accepted.post.logical = operation.apply (logicalBook pre.logical) := by
  simp [Accepted.post, logicalBook, CellState.ValidatedPatch.apply,
    CellState.materialize, Operation.patch, CellState.applyFieldWrites,
    CellState.applyResourceWrites, CellState.FieldStore.read,
    CellState.FieldStore.assign]

/-- The accepted canonical post conserves every asset. -/
theorem Accepted.conserves
    {M : CellState.Materializer schema Digest}
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

/-- One book-cell patch, regardless of the number of registrations/payments. -/
structure Batch where
  registrations : List AccountId
  operations : List Operation
  deriving DecidableEq, Repr

def Batch.apply (batch : Batch) (book : Book) : Book :=
  applyOperations (registerAccounts book batch.registrations) batch.operations

def Batch.Admission (book : Book) (batch : Batch) : Prop :=
  RegistrationsAdmitted book batch.registrations ∧
    OperationsAdmitted (registerAccounts book batch.registrations) batch.operations

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
  have ordered := admitted.2
  rw [position, operationsAdmitted_append] at ordered
  exact ordered.2.1.sourceSolvent.resolve_left notMint

theorem Batch.conservation : Batch.ConservationStatement := by
  intro book batch admitted asset
  exact (applyOperations_conserves _ _ admitted.2 asset).trans
    (registerAccounts_conserves _ _ admitted.1 asset)

/-- This is the executable fail-closed batch evaluator. A refused batch emits
no post-book. Intermediate registration/payment books are never exposed. -/
def Batch.run (batch : Batch) (book : Book) : Option Book :=
  if batch.Admission book then some (batch.apply book) else none

theorem Batch.run_accepts_iff (batch : Batch) (book post : Book) :
    batch.run book = some post ↔ batch.Admission book ∧ post = batch.apply book := by
  unfold Batch.run
  split_ifs with admitted <;> simp [admitted, eq_comm]

def Batch.patch {M : CellState.Materializer schema Digest}
    (batch : Batch) (pre : CellState.Materialized M) : CellState.Patch schema Digest where
  expectedPreRoot := pre.root
  fieldFootprint := {.book}
  resourceFootprint := ∅
  fieldWrites := [{ field := .book, value := some (batch.apply (logicalBook pre.logical)) }]
  resourceWrites := []

theorem Batch.validated_nonempty {M : CellState.Materializer schema Digest}
    (batch : Batch) (pre : CellState.Materialized M) :
    Nonempty (CellState.ValidatedPatch M pre (batch.patch pre)) := by
  have accepted : ∃ validated : CellState.ValidatedPatch M pre (batch.patch pre),
      CellState.validate M pre (batch.patch pre) = .accepted validated := by
    unfold CellState.validate
    rw [dif_pos (show (batch.patch pre).expectedPreRoot = pre.root from rfl)]
    rw [dif_pos (show (batch.patch pre).fieldFootprint = (batch.patch pre).namedFields by
      simp [Batch.patch, CellState.Patch.namedFields])]
    rw [dif_pos (show (batch.patch pre).resourceFootprint = (batch.patch pre).namedResources by
      simp [Batch.patch, CellState.Patch.namedResources])]
    exact ⟨_, rfl⟩
  exact ⟨accepted.choose⟩

structure AcceptedBatch {M : CellState.Materializer schema Digest}
    (pre : CellState.Materialized M) (batch : Batch) : Prop where
  admission : batch.Admission (logicalBook pre.logical)
  validated : CellState.ValidatedPatch M pre (batch.patch pre)

def AcceptedBatch.ofAdmission {M : CellState.Materializer schema Digest}
    {pre : CellState.Materialized M} {batch : Batch}
    (admission : batch.Admission (logicalBook pre.logical)) : AcceptedBatch pre batch :=
  ⟨admission, Classical.choice (batch.validated_nonempty pre)⟩

def AcceptedBatch.post {M : CellState.Materializer schema Digest}
    {pre : CellState.Materialized M} {batch : Batch}
    (accepted : AcceptedBatch pre batch) : CellState.Materialized M := accepted.validated.apply

@[simp] theorem AcceptedBatch.post_logicalBook {M : CellState.Materializer schema Digest}
    {pre : CellState.Materialized M} {batch : Batch} (accepted : AcceptedBatch pre batch) :
    logicalBook accepted.post.logical = batch.apply (logicalBook pre.logical) := by
  simp [AcceptedBatch.post, logicalBook, CellState.ValidatedPatch.apply,
    CellState.materialize, Batch.patch, CellState.applyFieldWrites,
    CellState.applyResourceWrites, CellState.FieldStore.read, CellState.FieldStore.assign]

theorem AcceptedBatch.conserves {M : CellState.Materializer schema Digest}
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

def witnessLogical : CellState.LogicalState schema where
  fields := (0 : CellState.FieldStore schema).write .book witnessBook
  resources := fun resource => nomatch resource

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

theorem witnessOverdrawBatch_rejected : ¬ witnessOverdrawBatch.Admission witnessBook := by decide

theorem witnessOverdrawBatch_no_post : witnessOverdrawBatch.run witnessBook = none := by decide

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
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Operation.validated_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Operation.validated_nonempty
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Accepted.conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.conserves
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.Book.creditOnly_breaks_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Book.creditOnly_breaks_conservation
/-- info: 'Minidregg.Theory.CanonicalResourceKernel.lease_installs_exact_record' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lease_installs_exact_record

end Minidregg.Theory.CanonicalResourceKernel
