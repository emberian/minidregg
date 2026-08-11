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
import Kernel.State
import Theory.CellState
import Theory.MaterializerCardinality
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

/-- Projection to the old four-field state.  It is used only to inherit the
already-proved finite-sum algebra; no old executor is invoked. -/
def Book.asKernelState (book : Book) : Minidregg.Kernel.KernelState where
  accounts := book.accounts
  bal := book.balance
  caps := fun _ => []
  umap := fun _ => none

@[simp] theorem Book.asKernelState_totalAsset (book : Book) (asset : AssetId) :
    Minidregg.Kernel.totalAsset book.asKernelState asset = book.totalAsset asset :=
  rfl

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

local instance schemaFieldCountable : Countable schema.Field := by
  change Countable Field
  infer_instance

local instance schemaFieldTypeCountable
    (field : schema.Field) : Countable (schema.FieldType field) := by
  cases field
  change Countable Book
  infer_instance

local instance schemaLogicalStateCountable :
    Countable (CellState.LogicalState schema) :=
  MaterializerCardinality.sparse_schema_state_countable
    (S := schema) (by change IsEmpty Empty; infer_instance)

local instance schemaLogicalStateNonempty :
    Nonempty (CellState.LogicalState schema) :=
  ⟨{ fields := 0, resources := fun resource => nomatch resource }⟩

/-- The typed schema is genuinely materializable.  The unary codec inherited
from `MaterializerCardinality` is an existence witness, not a wire-format
recommendation; production must replace it with an audited canonical codec. -/
noncomputable def materializer : CellState.Materializer schema Digest where
  codec := Classical.choice
    (MaterializerCardinality.nonempty_lawfulCodec_of_countable
      (alpha := CellState.LogicalState schema))
  rootBytes := fun bytes => ⟨bytes.length⟩

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

@[simp] theorem Book.creditOnly_balance (book : Book) (destination : AccountId)
    (asset : AssetId) (amount : Nat) (account : AccountId) (otherAsset : AssetId) :
    (book.creditOnly destination asset amount).balance account otherAsset =
      Minidregg.Kernel.mintBal book.balance destination asset
        (Int.ofNat amount) account otherAsset := by
  simp only [Book.balance, Book.creditOnly, DFinsupp.add_apply,
    DFinsupp.single_apply, Minidregg.Kernel.mintBal]
  by_cases sameAsset : otherAsset = asset
  · subst sameAsset
    by_cases sameAccount : account = destination
    · subst sameAccount
      simp
    · simp [sameAccount, Ne.symm sameAccount]
  · simp [sameAsset, Ne.symm sameAsset]

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

noncomputable def witnessCell : CellState.Materialized materializer :=
  CellState.materialize materializer witnessLogical

@[simp] theorem witnessCell_logicalBook :
    logicalBook witnessCell.logical = witnessBook := by
  simp [witnessCell, witnessLogical, logicalBook, CellState.materialize,
    CellState.FieldStore.read]

def witnessMintAdmission :
    Admission witnessBook (.mint 0 1 2) where
  sourcePresent := by decide
  destinationPresent := by decide
  sourceSolvent := Or.inl rfl
  leaseWellFormed := trivial

noncomputable def witnessMintAccepted :
    Accepted witnessCell (.mint 0 1 2) :=
  Accepted.ofAdmission (by simpa using witnessMintAdmission)

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
    (logicalBook witnessMintAccepted.post.logical).totalAsset 0 =
      (logicalBook witnessCell.logical).totalAsset 0 :=
  witnessMintAccepted.conserves 0

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
