/-
# Theory.ConservationBridge -- the existing conservation results as corollaries

DATAMODEL.md §3.1 names two existing conservation results that are "the same
fact said once": `CanonicalResourceKernel.Book.applyPosting_conserves` (and its
batch form `Batch.conservation`) and `DeclaredActionLowering`'s
`Declaration.postingSum_zero` / `Accepted.conserves` over `run_balance`.  This
module gives each carrier a value view into `Theory.Conservation`, computes the
delta of its admitted transitions as a sum of postings, and re-derives the
existing statements from `posting_mem_ker` and `sum_accounts_eq_assetSum`.

Nothing is deleted here (that is B-wave work).  Two shape differences the
design did not name are handled explicitly:

* `Book.totalAsset` sums over the registered `accounts` Finset, not over the
  support of `balances`.  The homomorphism statement is about the support;
  the bridge is `sum_accounts_eq_assetSum`, which needs the delta to touch only
  registered accounts.  That is exactly what `Admission.sourcePresent` /
  `destinationPresent` supply, and it is the only use of those premises.
* Account registration is not a value transition at all (the balance vector is
  unchanged, so its delta is `0`), but it changes the account set the total is
  taken over.  `Batch.conservation` therefore still needs the existing
  hidden-balance check `registerAccounts_conserves`; the homomorphism covers the
  operation half.
-/
import Theory.Conservation
import Theory.CanonicalResourceKernel
import Theory.DeclaredActionLowering

namespace Minidregg.Theory.ConservationBridge

open Finsupp
open Minidregg.Theory.Conservation

set_option autoImplicit false

universe u v w

/-! ## The value view of a store namespace

`Theory.Conservation` is stated over an abstract value view `S → (K →₀ G)`.
For the one store (`Theory.Store`) that view is a single reader: fix a
namespace whose values form an additive group and read it with absence as `0`.
Absence stays a value of the representation (`none`); only this view, which
conservation is a statement about, identifies it with `0`. -/

section StoreView

open Minidregg.Theory.Store

variable {L : Layout.{u, v, w}}

/-- The namespace `space` of a store as a finitely supported value vector,
absence read as `0`. -/
noncomputable def valueView (space : L.Namespace) [AddCommGroup (L.Value space)]
    (store : Store L) : L.Key space →₀ L.Value space :=
  (finsuppAddEquivDFinsupp (ι := L.Key space) (M := L.Value space)).symm
    ((DFinsupp.comapDomain (Sigma.mk space) sigma_mk_injective store).mapRange
      (fun _ (o : Option (L.Value space)) => o.getD 0) (fun _ => rfl))

@[simp] theorem valueView_apply (space : L.Namespace) [AddCommGroup (L.Value space)]
    (store : Store L) (key : L.Key space) :
    valueView space store key = (store ⟨space, key⟩).getD 0 := by
  simp [valueView]

/-- The frame law, read through the value view: a patch changes the view only
at keys in its write footprint. -/
theorem valueView_run_frame (space : L.Namespace) [AddCommGroup (L.Value space)]
    (store : Store L) (patch : Patch L) (key : L.Key space)
    (outside : (⟨space, key⟩ : Address L) ∉ Patch.writeFootprint patch) :
    valueView space (Patch.run store patch) key = valueView space store key := by
  rw [valueView_apply, valueView_apply, Patch.run_frame store patch _ outside]

/-- The delta of a patch is supported inside its write footprint. -/
theorem delta_valueView_frame (space : L.Namespace) [AddCommGroup (L.Value space)]
    (store : Store L) (patch : Patch L) (key : L.Key space)
    (outside : (⟨space, key⟩ : Address L) ∉ Patch.writeFootprint patch) :
    delta (valueView space) store (Patch.run store patch) key = 0 := by
  rw [delta_apply, valueView_run_frame space store patch key outside, sub_self]

end StoreView

/-! ## The canonical resource `Book` -/

section Book

open Minidregg.Theory.CanonicalResourceKernel

/-- The Book's balance namespace as a finitely supported value vector. -/
noncomputable def bookValue (book : Book) : AccountId × AssetId →₀ ℤ :=
  (finsuppAddEquivDFinsupp (ι := AccountId × AssetId) (M := ℤ)).symm book.balances

@[simp] theorem bookValue_apply (book : Book) (x : AccountId × AssetId) :
    bookValue book x = book.balances x := by
  simp [bookValue]

/-- The vector one operation posts. -/
noncomputable def operationVector (operation : Operation) : AccountId × AssetId →₀ ℤ :=
  posting operation.posting.source operation.posting.destination operation.posting.asset
    (Int.ofNat operation.posting.amount)

theorem bookValue_applyPosting (book : Book) (p : Posting) :
    bookValue (book.applyPosting p) =
      bookValue book + posting p.source p.destination p.asset (Int.ofNat p.amount) := by
  classical
  ext x
  simp [Book.applyPosting, posting, DFinsupp.single_apply, Finsupp.single_apply, add_assoc]

theorem bookValue_operation_apply (operation : Operation) (book : Book) :
    bookValue (operation.apply book) = bookValue book + operationVector operation := by
  have balances : (operation.apply book).balances =
      (book.applyPosting operation.posting).balances := by
    cases operation <;> rfl
  have : bookValue (operation.apply book) = bookValue (book.applyPosting operation.posting) := by
    ext x
    simp [balances]
  rw [this, bookValue_applyPosting]
  rfl

theorem bookValue_registerAccounts (book : Book) (accounts : List AccountId) :
    bookValue (registerAccounts book accounts) = bookValue book := by
  induction accounts generalizing book with
  | nil => rfl
  | cons account rest ih => exact ih (book.registerAccount account)

theorem bookValue_deregisterAccounts (book : Book) (accounts : List AccountId) :
    bookValue (deregisterAccounts book accounts) = bookValue book := by
  unfold bookValue
  rw [deregisterAccounts_balances]

theorem bookValue_applyOperations (book : Book) (operations : List Operation) :
    bookValue (applyOperations book operations) =
      bookValue book + (operations.map operationVector).sum := by
  induction operations generalizing book with
  | nil => simp [applyOperations]
  | cons operation rest ih =>
      simp only [applyOperations, List.map_cons, List.sum_cons]
      rw [ih, bookValue_operation_apply, add_assoc]

theorem applyOperations_accounts (book : Book) (operations : List Operation) :
    (applyOperations book operations).accounts = book.accounts := by
  induction operations generalizing book with
  | nil => rfl
  | cons operation rest ih =>
      simp only [applyOperations]
      rw [ih, Operation.apply_accounts]

/-- The delta of any batch is a sum of operation postings. -/
theorem batch_delta (book : Book) (batch : Batch) :
    delta bookValue book (batch.apply book) = (batch.operations.map operationVector).sum := by
  apply delta_of_value_eq
  rw [Batch.apply, bookValue_deregisterAccounts, bookValue_applyOperations,
    bookValue_registerAccounts]

/-- **§4.1, the general theorem, Book form.** The delta of every batch in the
closed operation language lies in `ker assetSum`.  No admission premise is
needed: the operation *type* is what selects postings.  Admission is used only
for the finite-total form below. -/
theorem batch_delta_mem_ker (book : Book) (batch : Batch) :
    delta bookValue book (batch.apply book) ∈
      (assetSum : (AccountId × AssetId →₀ ℤ) →+ (AssetId →₀ ℤ)).ker := by
  rw [batch_delta]
  exact list_sum_mem fun _ hv => by
    obtain ⟨op, _, rfl⟩ := List.mem_map.mp hv
    exact posting_mem_ker _ _ _ _

theorem batch_conserves (book : Book) (batch : Batch) :
    ConservesBetween bookValue book (batch.apply book) :=
  (conserves_iff_delta_mem_ker _ _ _).mpr (batch_delta_mem_ker book batch)

/-- Bridge from a conserving delta to the Book's finite total. -/
theorem totalAsset_eq_of_conserves (pre post : Book) (sameAccounts : post.accounts = pre.accounts)
    (supported : SupportedIn pre.accounts (delta bookValue pre post))
    (conserves : ConservesBetween bookValue pre post) (asset : AssetId) :
    post.totalAsset asset = pre.totalAsset asset := by
  have zero := Conserves.sum_accounts_eq_zero conserves supported asset
  simp only [delta_apply, bookValue_apply] at zero
  rw [Finset.sum_sub_distrib, sub_eq_zero] at zero
  unfold Book.totalAsset Book.balance
  rw [sameAccounts]
  exact zero

/-- **Corollary: `Book.applyPosting_conserves`** from `posting_mem_ker`. -/
theorem applyPosting_conserves (book : Book) (p : Posting)
    (sourcePresent : p.source ∈ book.accounts)
    (destinationPresent : p.destination ∈ book.accounts) (asset : AssetId) :
    (book.applyPosting p).totalAsset asset = book.totalAsset asset := by
  classical
  have d : delta bookValue book (book.applyPosting p) =
      posting p.source p.destination p.asset (Int.ofNat p.amount) :=
    delta_of_value_eq _ (bookValue_applyPosting book p)
  refine totalAsset_eq_of_conserves book (book.applyPosting p) rfl ?_ ?_ asset
  · rw [d]
    exact supportedIn_posting _ _ sourcePresent destinationPresent
  · unfold ConservesBetween
    rw [d]
    exact (conserves_iff_mem_ker _).mpr (posting_mem_ker _ _ _ _)

theorem operations_supported (book : Book) (operations : List Operation)
    (admitted : OperationsAdmitted book operations) :
    SupportedIn book.accounts (operations.map operationVector).sum := by
  classical
  induction operations generalizing book with
  | nil => exact supportedIn_zero _
  | cons operation rest ih =>
      rw [List.map_cons, List.sum_cons]
      have tail := ih (operation.apply book) admitted.2
      rw [Operation.apply_accounts] at tail
      exact (supportedIn_posting _ _ admitted.1.sourcePresent
        admitted.1.destinationPresent).add tail

/-- **Corollary: `Batch.conservation`.** The operation half is the kernel
theorem; the registration half is the existing hidden-balance check. -/
theorem batch_conservation : Batch.ConservationStatement := by
  intro book batch admitted asset
  have ops : (applyOperations (registerAccounts book batch.registrations) batch.operations).totalAsset
      asset = (registerAccounts book batch.registrations).totalAsset asset := by
    have d : delta bookValue (registerAccounts book batch.registrations)
        (applyOperations (registerAccounts book batch.registrations) batch.operations) =
        (batch.operations.map operationVector).sum :=
      delta_of_value_eq _ (by rw [bookValue_applyOperations])
    refine totalAsset_eq_of_conserves (registerAccounts book batch.registrations)
      (applyOperations (registerAccounts book batch.registrations) batch.operations)
      (applyOperations_accounts _ _) ?_ ?_ asset
    · rw [d]
      exact operations_supported _ _ admitted.2.1
    · unfold ConservesBetween
      rw [d]
      exact (conserves_iff_mem_ker _).mpr (moves_sum_mem_ker_ops batch.operations)
  exact (deregisterAccounts_conserves _ _ admitted.2.2 asset).trans
    (ops.trans (registerAccounts_conserves _ _ admitted.1 asset))
where
  moves_sum_mem_ker_ops (operations : List Operation) :
      (operations.map operationVector).sum ∈
        (assetSum : (AccountId × AssetId →₀ ℤ) →+ (AssetId →₀ ℤ)).ker :=
    list_sum_mem fun _ hv => by
      obtain ⟨op, _, rfl⟩ := List.mem_map.mp hv
      exact posting_mem_ker _ _ _ _

/-! ### The Book cell as a store

The Book cell stores one `Book` at `bookAddress`; its value view is the balance
vector of the book it holds (absence is the empty book).  An accepted batch
conserves as a statement about the pre- and post-cell stores themselves. -/

/-- The value view of a Book cell's store. -/
noncomputable def bookStoreValue (store : Minidregg.Theory.Store.Store layout) :
    AccountId × AssetId →₀ ℤ :=
  bookValue (logicalBook store)

theorem acceptedBatch_conserves
    {M : Minidregg.Theory.CellState.Materializer layout
      Minidregg.Theory.TypedAuthorization.Digest}
    {pre : Minidregg.Theory.CellState.Materialized M} {batch : Batch}
    (accepted : AcceptedBatch pre batch) :
    ConservesBetween bookStoreValue pre.logical accepted.post.logical := by
  change ConservesBetween bookValue (logicalBook pre.logical)
    (logicalBook accepted.post.logical)
  rw [accepted.post_logicalBook]
  exact batch_conserves _ _

/-! ### Poles (§4.1) -/

/-- Satisfiable pole: a balanced two-account transfer on the witness book has
exactly the posting as its delta, and conserves. -/
theorem witness_transfer_delta :
    delta bookValue witnessBook ((Operation.transfer 1 2 0 3).apply witnessBook) =
      posting 1 2 0 3 := by
  apply delta_of_value_eq
  rw [bookValue_operation_apply]
  rfl

theorem witness_transfer_conserves :
    ConservesBetween bookValue witnessBook ((Operation.transfer 1 2 0 3).apply witnessBook) := by
  unfold ConservesBetween
  rw [witness_transfer_delta]
  exact (conserves_iff_mem_ker _).mpr (posting_mem_ker _ _ _ _)

/-- Satisfiable pole at §4.1's named instance: the admitted birth batch
(register 3, fee 1→2, transfer 1→3) has the sum of its two postings as delta. -/
theorem witnessBirthBatch_delta :
    delta bookValue witnessBook (witnessBirthBatch.apply witnessBook) =
      posting 1 2 0 1 + posting 1 3 0 2 := by
  rw [batch_delta]
  simp [witnessBirthBatch, operationVector, Operation.posting]

theorem witnessBirthBatch_kernel_conserves :
    ConservesBetween bookValue witnessBook (witnessBirthBatch.apply witnessBook) :=
  batch_conserves _ _

/-- Refutable pole, general: a positive credit-only mint's delta is outside the kernel. -/
theorem creditOnly_not_conserves (book : Book) (destination : AccountId) (asset : AssetId)
    (amount : Nat) (positive : 0 < amount) :
    ¬ ConservesBetween bookValue book (book.creditOnly destination asset amount) := by
  classical
  have d : delta bookValue book (book.creditOnly destination asset amount) =
      single (destination, asset) (Int.ofNat amount) := by
    apply delta_of_value_eq
    ext x
    simp [Book.creditOnly, DFinsupp.single_apply, Finsupp.single_apply]
  unfold ConservesBetween Conserves
  rw [d, assetSum_single]
  intro h
  rw [Finsupp.single_eq_zero, Int.ofNat_eq_natCast] at h
  omega

/-- Refutable pole, concrete: the witness book, credit-only 2 of asset 0 to account 1. -/
theorem witness_creditOnly_not_conserves :
    ¬ ConservesBetween bookValue witnessBook (witnessBook.creditOnly 1 0 2) :=
  creditOnly_not_conserves _ _ _ _ (by decide)

end Book

/-! ## The declared-action lowering -/

section Declared

open Minidregg.Theory.CellState
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.Store

abbrev BalanceKey := ResourceId .account × Digest

theorem accountBalance_injective :
    Function.Injective fun k : BalanceKey => StateKey.accountBalance k.1 k.2 := by
  rintro ⟨a, r⟩ ⟨a', r'⟩ h
  cases h
  rfl

/-- The balance keys of a declared-effect cell: the store's value view at its
one namespace, restricted along the injective `accountBalance` key. -/
noncomputable def effectValue (store : Store effectLayout) : BalanceKey →₀ ℤ :=
  Finsupp.comapDomain (fun k : BalanceKey => StateKey.accountBalance k.1 k.2)
    (valueView (L := effectLayout) () store) accountBalance_injective.injOn

@[simp] theorem effectValue_apply (store : Store effectLayout)
    (k : BalanceKey) : effectValue store k = balance store k.1 k.2 := by
  rw [effectValue, Finsupp.comapDomain_apply]
  exact valueView_apply (L := effectLayout) () store _

/-- The vector a posting list denotes. -/
noncomputable def postingVector (ps : List Posting) : BalanceKey →₀ ℤ :=
  (ps.map fun p => single (p.account, p.resource) p.amount).sum

theorem postingVector_apply (ps : List Posting) (k : BalanceKey) :
    postingVector ps k = postingDelta ps k.1 k.2 := by
  classical
  induction ps with
  | nil => simp [postingVector, postingDelta]
  | cons p rest ih =>
      simp only [postingVector, List.map_cons, List.sum_cons, Finsupp.add_apply] at ih ⊢
      rw [ih]
      simp [postingDelta, Finsupp.single_apply, Prod.ext_iff]

/-- The vector one action denotes: a posting for a move, `0` otherwise. -/
noncomputable def actionVector : Action → BalanceKey →₀ ℤ
  | .move source destination resource _ _ amount => posting source destination resource amount
  | _ => 0

theorem postingVector_action (action : Action) :
    postingVector action.postings = actionVector action := by
  cases action with
  | create => simp [postingVector, Action.postings, actionVector]
  | write => simp [postingVector, Action.postings, actionVector]
  | move source destination resource se de amount =>
      simp [postingVector, Action.postings, actionVector, posting]

theorem postingVector_append (l r : List Posting) :
    postingVector (l ++ r) = postingVector l + postingVector r := by
  simp [postingVector]

theorem postingVector_declaration {kind : ResourceKind} {target : ResourceId kind}
    (declaration : DeclaredActionLowering.Declaration target) :
    postingVector declaration.postings = (declaration.actions.map actionVector).sum := by
  change postingVector (declaration.actions.flatMap Action.postings) = _
  induction declaration.actions with
  | nil => simp [postingVector]
  | cons action rest ih =>
      rw [List.flatMap_cons, postingVector_append, postingVector_action, ih]
      simp

theorem actionVector_mem_ker (action : Action) :
    actionVector action ∈ (assetSum : (BalanceKey →₀ ℤ) →+ (Digest →₀ ℤ)).ker := by
  cases action with
  | move => exact posting_mem_ker _ _ _ _
  | create => exact zero_mem _
  | write => exact zero_mem _

theorem declaration_vector_mem_ker {kind : ResourceKind} {target : ResourceId kind}
    (declaration : DeclaredActionLowering.Declaration target) :
    postingVector declaration.postings ∈
      (assetSum : (BalanceKey →₀ ℤ) →+ (Digest →₀ ℤ)).ker := by
  rw [postingVector_declaration]
  exact list_sum_mem fun _ hv => by
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact actionVector_mem_ker a

/-- The delta of a successful run is the declaration's posting vector
(`run_balance`, restated as one vector equation). -/
theorem declaration_run_delta {kind : ResourceKind} {target : ResourceId kind}
    (declaration : DeclaredActionLowering.Declaration target)
    (fields post : Store effectLayout)
    (run : declaration.run fields = some post) :
    delta effectValue fields post = postingVector declaration.postings := by
  ext k
  rw [delta_apply, effectValue_apply, effectValue_apply, postingVector_apply]
  exact declaration.run_balance fields post run k.1 k.2

/-- **§4.1, the general theorem, declared-effect form.** Every successful
declared run conserves. -/
theorem declaration_run_conserves {kind : ResourceKind} {target : ResourceId kind}
    (declaration : DeclaredActionLowering.Declaration target)
    (fields post : Store effectLayout)
    (run : declaration.run fields = some post) :
    ConservesBetween effectValue fields post := by
  unfold ConservesBetween
  rw [declaration_run_delta declaration fields post run]
  exact (conserves_iff_mem_ker _).mpr (declaration_vector_mem_ker declaration)

theorem assetSum_postingVector (ps : List Posting) (resource : Digest) :
    assetSum (postingVector ps) resource = postingSum ps resource := by
  classical
  induction ps with
  | nil => simp [postingVector, postingSum]
  | cons p rest ih =>
      simp only [postingVector, List.map_cons, List.sum_cons, map_add,
        Finsupp.add_apply] at ih ⊢
      rw [ih, assetSum_single]
      simp [postingSum, Finsupp.single_apply]

/-- **Corollary: `Declaration.postingSum_zero`** from kernel membership. -/
theorem declaration_postingSum_zero {kind : ResourceKind} {target : ResourceId kind}
    (declaration : DeclaredActionLowering.Declaration target) (resource : Digest) :
    postingSum declaration.postings resource = 0 := by
  rw [← assetSum_postingVector, AddMonoidHom.mem_ker.mp (declaration_vector_mem_ker declaration)]
  rfl

theorem postingVector_supported {kind : ResourceKind} {target : ResourceId kind}
    (declaration : DeclaredActionLowering.Declaration target) :
    SupportedIn (balanceAccounts (Patch.writeFootprint declaration.patch))
      (postingVector declaration.postings) := by
  classical
  apply supportedIn_list_sum
  intro v hv
  obtain ⟨p, member, rfl⟩ := List.mem_map.mp hv
  exact supportedIn_single _ (declaration.posting_account_mem p member)

/-- **Corollary: `Accepted.conserves`**, from the delta equation plus the
support bridge. -/
theorem accepted_conserves {kind : ResourceKind} {target : ResourceId kind}
    {M : Materializer effectLayout Digest}
    {portal : Portal} {authState : AuthState} {context : RequestContext}
    {pre : Materialized M} {declaration : DeclaredActionLowering.Declaration target}
    (accepted : DeclaredActionLowering.Accepted portal authState context pre declaration)
    (resource : Digest) :
    (∑ account ∈ balanceAccounts (Patch.writeFootprint declaration.patch),
      (balance accepted.cellEffect.prepared.post.logical account resource -
        balance pre.logical account resource)) = 0 := by
  have d : delta effectValue pre.logical accepted.cellEffect.prepared.post.logical =
      postingVector declaration.postings := by
    ext k
    rw [delta_apply, effectValue_apply, effectValue_apply, postingVector_apply]
    exact accepted.balance_delta k.1 k.2
  have zero := Conserves.sum_accounts_eq_zero
    (show Conserves (postingVector declaration.postings) from
      (conserves_iff_mem_ker _).mpr (declaration_vector_mem_ker declaration))
    (postingVector_supported declaration) resource
  rw [← d] at zero
  simpa using zero

/-! ### Refutable pole: a raw balance write, with the admission premise removed -/

/-- A raw guarded write to an `accountBalance` key, as the unadmitted
lowering would emit it: the one guarded `Store.Op` adding `m`. -/
def rawBalanceWrite (account : ResourceId .account) (resource : Digest)
    (expected : Option Int) (m : Int) : Op effectLayout :=
  guardedSet (.accountBalance account resource) expected (expected.getD 0 + m)

/-- The raw write, when its guard passes, changes one coordinate by `m`. -/
theorem rawBalanceWrite_not_conserves (account : ResourceId .account) (resource : Digest)
    (expected : Option Int) (m : Int) (nonzero : m ≠ 0)
    (fields : Store effectLayout)
    (valid : Patch.ValidFrom fields [rawBalanceWrite account resource expected m]) :
    ¬ ConservesBetween effectValue fields
      (Patch.run fields [rawBalanceWrite account resource expected m]) := by
  classical
  have d : delta effectValue fields
      (Patch.run fields [rawBalanceWrite account resource expected m]) =
        single (account, resource) m := by
    ext k
    rw [delta_apply, effectValue_apply, effectValue_apply]
    rw [patch_run_balance _ fields valid k.1 k.2]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      rawBalanceWrite, guardedSet_balanceDelta, Finsupp.single_apply,
      StateKey.accountBalance.injEq, add_sub_cancel_left]
    by_cases h : (account, resource) = k
    · subst h
      simp
    · have h' : ¬ (account = k.1 ∧ resource = k.2) := fun ⟨a, b⟩ => h (by subst a b; rfl)
      simp [h, h']
  unfold ConservesBetween Conserves
  rw [d, assetSum_single]
  simpa using nonzero

/-- And the admission check refuses exactly that action on every target kind. -/
theorem raw_balance_write_refused {kind : ResourceKind} (target : ResourceId kind)
    (account : ResourceId .account) (resource : Digest) (expected : Option Int) (v : Int) :
    ¬ (Action.write (.accountBalance account resource) expected v).Admitted target := by
  cases kind <;> simp [Action.Admitted, Action.admissionCheck, writableKeyCheck]

/-! ### Per-grant bound, declared form (§3.7) -/

theorem abs_actionVector_apply_le (maxDelta : ℤ) (action : Action)
    (bounded : ∀ s d r se de amount, action = .move s d r se de amount → |amount| ≤ maxDelta)
    (zeroLe : 0 ≤ maxDelta) (k : BalanceKey) :
    |actionVector action k| ≤ maxDelta := by
  cases action with
  | move s d r se de amount =>
      exact (abs_posting_apply_le _ _ _ _ _).trans (bounded s d r se de amount rfl)
  | create => simpa [actionVector] using zeroLe
  | write => simpa [actionVector] using zeroLe

theorem abs_actions_sum_apply_le (maxDelta : ℤ) (zeroLe : 0 ≤ maxDelta)
    (actions : List Action)
    (bounded : ∀ s d r se de amount, Action.move s d r se de amount ∈ actions → |amount| ≤ maxDelta)
    (k : BalanceKey) :
    |(actions.map actionVector).sum k| ≤ actions.length • maxDelta := by
  induction actions with
  | nil => simp
  | cons action rest ih =>
      rw [List.map_cons, List.sum_cons, Finsupp.add_apply, List.length_cons, succ_nsmul']
      refine (abs_add_le _ _).trans (add_le_add ?_ (ih fun s d r se de amount h =>
        bounded s d r se de amount (List.mem_cons_of_mem _ h)))
      exact abs_actionVector_apply_le maxDelta action
        (fun s d r se de amount h => bounded s d r se de amount (h ▸ List.mem_cons_self))
        zeroLe k

/-- The delta of a successful declared run is bounded at every key by
`maxDelta` times the number of actions, when every move is within `maxDelta`. -/
theorem declaration_run_delta_bounded {kind : ResourceKind} {target : ResourceId kind}
    (declaration : DeclaredActionLowering.Declaration target)
    (fields post : Store effectLayout)
    (run : declaration.run fields = some post) (maxDelta : ℤ) (zeroLe : 0 ≤ maxDelta)
    (bounded : ∀ s d r se de amount,
      Action.move s d r se de amount ∈ declaration.actions → |amount| ≤ maxDelta)
    (k : BalanceKey) :
    |delta effectValue fields post k| ≤ declaration.actions.length • maxDelta := by
  rw [declaration_run_delta declaration fields post run, postingVector_declaration]
  exact abs_actions_sum_apply_le maxDelta zeroLe _ bounded k

end Declared

/-! ## Axiom pins -/

/-- info: 'Minidregg.Theory.ConservationBridge.delta_valueView_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms delta_valueView_frame
/-- info: 'Minidregg.Theory.ConservationBridge.effectValue_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms effectValue_apply
/-- info: 'Minidregg.Theory.ConservationBridge.batch_delta_mem_ker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms batch_delta_mem_ker
/-- info: 'Minidregg.Theory.ConservationBridge.applyPosting_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms applyPosting_conserves
/-- info: 'Minidregg.Theory.ConservationBridge.batch_conservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms batch_conservation
/-- info: 'Minidregg.Theory.ConservationBridge.acceptedBatch_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms acceptedBatch_conserves
/-- info: 'Minidregg.Theory.ConservationBridge.witness_transfer_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms witness_transfer_conserves
/-- info: 'Minidregg.Theory.ConservationBridge.creditOnly_not_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms creditOnly_not_conserves
/-- info: 'Minidregg.Theory.ConservationBridge.declaration_run_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declaration_run_conserves
/-- info: 'Minidregg.Theory.ConservationBridge.declaration_postingSum_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declaration_postingSum_zero
/-- info: 'Minidregg.Theory.ConservationBridge.accepted_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_conserves
/-- info: 'Minidregg.Theory.ConservationBridge.rawBalanceWrite_not_conserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rawBalanceWrite_not_conserves
/-- info: 'Minidregg.Theory.ConservationBridge.declaration_run_delta_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms declaration_run_delta_bounded

end Minidregg.Theory.ConservationBridge
