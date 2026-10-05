/- Seats: offer safety as a law judged on every reallocation, over the Book.

An `offer` presents an invitation (`Kernel.Invitation`) and a proposal
`{give, want, exit}`. The kernel spends the invitation, registers the seat's
Book account (on the native route, its seat cell's protected coordinate, at or
above `2^256`: no user can own, squat or pre-fund it), posts `give` from the
offerer's funding account into it, and installs the seat. From then on:

* the seat's balances are judged by its law `offerSafe proposal`, a `Pred`
  (`Pred.Core`) over a TOTAL view of the seat's Book balances: every asset the
  proposal names has a slot, so the fail-closed reading of an absent slot can
  never be what the law sees (`view_total`);
* a seat is debited only by (a) a `reallocate` OF its own contract instance,
  after which every seat the reallocation touched must satisfy its law, or (b)
  `exit`/`terminate`/the end of the activity that holds it, which post the
  seat's whole allocation to its payee and close it (`seat_debit_authorized`);
* `exit` is a kernel action: the contract's own clause is consulted for
  reallocations and never for an exit, so no contract clause can forbid it;
* `terminate` of an instance exits every open seat of that instance, and the
  end of an activity exits every open seat it holds (`closeHeld`).

**One Book batch per step.** Every step's postings are one
`CanonicalResourceKernel.Batch`, admitted on the step's own Book
(`Batch.Admission`: endpoints registered, every debit funded on the intermediate
book, a registered account fresh), and the next Book is that batch applied
(`step_posts`); a sequence of steps (a contract method's Plan, an activity's
end) posts the concatenation (`Posts.seq`). So every admitted step conserves
every asset by the Book's own posting theorem (`seat_conserves`).

**Who acts.** `Actor.subject` is a signer; `Actor.inst` is the contract
instance, which on the native route acts ONLY through the Plan its own package
method returns when the receiver re-executes it (`runPlan`): the content of a
reallocation or a mint comes from the contract code, never from a signer's
say-so. Offerers are protected by offer safety, exit and conservation, whoever
invoked the method; the contract can propose only what its code computes.
`Actor.activity` is the end of the activity (its record cell) that holds a seat.

T3 (design `MINI-PROGRAM-MODEL-20261004` §3, root rulings of 2026-10-05):
`seat_offer_safe_forever` (every open seat of every reachable world satisfies
its law), `exit_enabled` and `exit_pays_allocation` (an on-demand offerer can
always exit, and the exit moves exactly the seat's balances to its payee),
`seat_conserves` (every admitted step conserves every asset). Teeth and
inhabitants are at the end. The native route (`Kernel.SeatReceiver`) commits
exactly what `step`/`runPlan` decide over the cells it loads (`Kernel.SeatStore`).
Not here: fees (the receiver charges them), non-fungible (set) amounts. -/
import Kernel.Invitation
import Kernel.ProtectedCell

namespace Minidregg.Kernel.Seats
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.Invitations
open Minidregg.Pred (Pred)
set_option autoImplicit false

/-! ## Proposals and the offer-safety law -/

inductive ExitRule where
  /-- The offerer may exit at any height. -/
  | onDemand
  /-- Anyone may exit the seat at or after height `due`. -/
  | afterDeadline (due : Nat)
  deriving DecidableEq, Repr

structure Proposal where
  give : List (AssetId × Nat)
  want : List (AssetId × Nat)
  exit : ExitRule
  deriving DecidableEq, Repr

/-- The assets a proposal names, each once. -/
def Proposal.assets (proposal : Proposal) : List AssetId :=
  ((proposal.give ++ proposal.want).map Prod.fst).dedup

def assetSlot (asset : AssetId) : Pred.Slot := "seat/asset/" ++ toString asset

/-- `balance asset ≥ amount`. A zero amount is the always-true conjunction:
`n - 1` computed in `Nat` would turn "want 0" into "hold at least 1". -/
def atLeast (asset : AssetId) (amount : Nat) : Pred :=
  if amount = 0 then Pred.all [] else .not (.le (assetSlot asset) ((amount : Int) - 1))

/-- Offer safety (Zoe `isOfferSafe`): every `want` is met, or every `give` is
refunded. -/
def offerSafe (proposal : Proposal) : Pred :=
  Pred.any [Pred.all (proposal.want.map fun entry => atLeast entry.1 entry.2),
            Pred.all (proposal.give.map fun entry => atLeast entry.1 entry.2)]

/-- The total view of a seat account's balances the law reads. -/
def view (book : Book) (account : AccountId) (proposal : Proposal) : Pred.State :=
  ⟨proposal.assets.map fun asset => (assetSlot asset, book.balance account asset)⟩

def safeAt (book : Book) (account : AccountId) (proposal : Proposal) : Bool :=
  Pred.eval (offerSafe proposal) (view book account proposal) (view book account proposal)

/-! ## The view is total, and the law is monotone in balances -/

theorem view_get (book : Book) (account : AccountId) (proposal : Proposal) (slot : Pred.Slot) :
    (view book account proposal).get slot =
      (proposal.assets.find? (fun asset => assetSlot asset == slot)).map
        (fun asset => book.balance account asset) := by
  unfold view Pred.State.get
  rw [List.find?_map, Option.map_map]
  rfl

/-- Every slot the law names is present in the view. -/
theorem view_total (book : Book) (account : AccountId) (proposal : Proposal) {asset : AssetId}
    (named : asset ∈ proposal.assets) :
    (view book account proposal).get (assetSlot asset) ≠ none := by
  rw [view_get]
  intro absent
  rw [Option.map_eq_none_iff, List.find?_eq_none] at absent
  exact absent asset named (by simp)

theorem atLeast_mono {book book' : Book} {account account' : AccountId} {proposal : Proposal}
    (more : ∀ asset ∈ proposal.assets, book.balance account asset ≤ book'.balance account' asset)
    (asset : AssetId) (amount : Nat)
    (holds : Pred.eval (atLeast asset amount) (view book account proposal) (view book account proposal) = true) :
    Pred.eval (atLeast asset amount) (view book' account' proposal) (view book' account' proposal) = true := by
  unfold atLeast at holds ⊢
  split_ifs at holds ⊢
  · simp [Pred.eval_all]
  · rw [Pred.eval_not] at holds ⊢
    simp only [Pred.eval, Pred.evalWith, view_get] at holds ⊢
    revert holds
    have mem : ∀ found, proposal.assets.find? (fun a => assetSlot a == assetSlot asset) = some found →
        found ∈ proposal.assets := fun found h => List.mem_of_find?_eq_some h
    cases h : proposal.assets.find? (fun a => assetSlot a == assetSlot asset) with
    | none => simp
    | some found =>
      have le := more found (mem found h)
      simp only [Option.map_some, Bool.not_eq_true', decide_eq_false_iff_not, not_le]
      intro lt
      exact lt_of_lt_of_le lt le

/-- The law is monotone: crediting a seat never breaks it. -/
theorem safeAt_mono {book book' : Book} {account account' : AccountId} {proposal : Proposal}
    (more : ∀ asset ∈ proposal.assets, book.balance account asset ≤ book'.balance account' asset)
    (holds : safeAt book account proposal = true) : safeAt book' account' proposal = true := by
  unfold safeAt offerSafe at holds ⊢
  rw [Pred.eval_any] at holds ⊢
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Pred.eval_all,
    List.all_eq_true, List.mem_map] at holds ⊢
  rcases holds with want | give
  · left
    rintro _ ⟨entry, member, rfl⟩
    exact atLeast_mono more entry.1 entry.2 (want _ ⟨entry, member, rfl⟩)
  · right
    rintro _ ⟨entry, member, rfl⟩
    exact atLeast_mono more entry.1 entry.2 (give _ ⟨entry, member, rfl⟩)

theorem safeAt_congr {book book' : Book} {account account' : AccountId} {proposal : Proposal}
    (same : ∀ asset ∈ proposal.assets, book.balance account asset = book'.balance account' asset) :
    safeAt book account proposal = safeAt book' account' proposal :=
  Bool.eq_iff_iff.mpr ⟨safeAt_mono (fun asset member => (same asset member).le),
    safeAt_mono (fun asset member => (same asset member).ge)⟩


/-! ## Postings: Book operations, one batch per step -/

/-- A movement between Book accounts: one `Operation.transfer`. -/
structure Transfer where
  source : AccountId
  destination : AccountId
  asset : AssetId
  amount : Nat
  deriving DecidableEq, Repr

def Transfer.op (transfer : Transfer) : Operation :=
  .transfer transfer.source transfer.destination transfer.asset transfer.amount

def opsOf (transfers : List Transfer) : List Operation := transfers.map Transfer.op

theorem single_at (p : AccountId × AssetId) (v : Int) (account : AccountId) (asset : AssetId) :
    (DFinsupp.single p v : Π₀ _ : AccountId × AssetId, Int) (account, asset) =
      if account = p.1 ∧ asset = p.2 then v else 0 := by
  by_cases h : account = p.1 ∧ asset = p.2
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩]
    simp
  · rw [if_neg h, DFinsupp.single_apply, dif_neg]
    intro e
    apply h
    subst e
    exact ⟨rfl, rfl⟩

theorem balance_op (book : Book) (transfer : Transfer) (account : AccountId) (asset : AssetId) :
    (transfer.op.apply book).balance account asset =
      book.balance account asset
        - (if account = transfer.source ∧ asset = transfer.asset then (transfer.amount : Int) else 0)
        + (if account = transfer.destination ∧ asset = transfer.asset then (transfer.amount : Int) else 0) := by
  show ((book.balances + DFinsupp.single (transfer.source, transfer.asset) (-(Int.ofNat transfer.amount) : Int) +
      DFinsupp.single (transfer.destination, transfer.asset) (Int.ofNat transfer.amount : Int) :
        Π₀ _ : AccountId × AssetId, Int)) (account, asset) = _
  rw [DFinsupp.add_apply, DFinsupp.add_apply, single_at, single_at]
  simp only [Book.balance]
  split_ifs <;> simp
  all_goals omega

theorem applyOperations_accounts_eq (book : Book) (operations : List Operation) :
    (applyOperations book operations).accounts = book.accounts := by
  induction operations generalizing book with
  | nil => rfl
  | cons operation rest ih => simp only [applyOperations]; rw [ih, Operation.apply_accounts]

theorem applyOperations_append_eq (book : Book) (first later : List Operation) :
    applyOperations book (first ++ later) = applyOperations (applyOperations book first) later := by
  induction first generalizing book with
  | nil => rfl
  | cons operation rest ih => simp only [List.cons_append, applyOperations]; exact ih _

/-- An account no transfer names keeps every balance. -/
theorem ops_untouched {book : Book} {transfers : List Transfer} {account : AccountId}
    (away : ∀ transfer ∈ transfers, transfer.source ≠ account ∧ transfer.destination ≠ account)
    (asset : AssetId) : (applyOperations book (opsOf transfers)).balance account asset = book.balance account asset := by
  induction transfers generalizing book with
  | nil => rfl
  | cons transfer rest ih =>
    simp only [opsOf, List.map_cons, applyOperations]
    obtain ⟨notSource, notDestination⟩ := away transfer (by simp)
    rw [show List.map Transfer.op rest = opsOf rest from rfl, ih (fun t m => away t (by simp [m])), balance_op,
      if_neg (fun h => notSource h.1.symm), if_neg (fun h => notDestination h.1.symm)]
    simp

/-- Transfers in other assets leave every balance of `asset` alone. -/
theorem ops_other_asset {book : Book} {transfers : List Transfer} {asset : AssetId}
    (away : ∀ transfer ∈ transfers, transfer.asset ≠ asset) (account : AccountId) :
    (applyOperations book (opsOf transfers)).balance account asset = book.balance account asset := by
  induction transfers generalizing book with
  | nil => rfl
  | cons transfer rest ih =>
    simp only [opsOf, List.map_cons, applyOperations]
    have other := away transfer (by simp)
    rw [show List.map Transfer.op rest = opsOf rest from rfl, ih (fun t m => away t (by simp [m])), balance_op,
      if_neg (fun h => other h.2.symm), if_neg (fun h => other h.2.symm)]
    simp

/-- An account no transfer debits never loses balance. -/
theorem ops_credit_only {book : Book} {transfers : List Transfer} {account : AccountId}
    (away : ∀ transfer ∈ transfers, transfer.source ≠ account)
    (asset : AssetId) : book.balance account asset ≤ (applyOperations book (opsOf transfers)).balance account asset := by
  induction transfers generalizing book with
  | nil => exact le_rfl
  | cons transfer rest ih =>
    simp only [opsOf, List.map_cons, applyOperations]
    show book.balance account asset ≤ (applyOperations (transfer.op.apply book) (opsOf rest)).balance account asset
    have step := ih (book := transfer.op.apply book) (fun t m => away t (by simp [m]))
    have notSource := away transfer (by simp)
    rw [balance_op, if_neg (fun h => notSource h.1.symm)] at step
    split_ifs at step <;> omega

/-- Admitted transfers keep an account's balances non-negative: every debit is
funded on the intermediate book. -/
theorem ops_nonneg {book : Book} {transfers : List Transfer} {account : AccountId}
    (admitted : OperationsAdmitted book (opsOf transfers)) (nonneg : ∀ asset, 0 ≤ book.balance account asset)
    (asset : AssetId) : 0 ≤ (applyOperations book (opsOf transfers)).balance account asset := by
  induction transfers generalizing book with
  | nil => exact nonneg asset
  | cons transfer rest ih =>
    simp only [opsOf, List.map_cons, applyOperations, OperationsAdmitted] at admitted ⊢
    have funded : (transfer.amount : Int) ≤ book.balance transfer.source transfer.asset :=
      admitted.1.sourceSolvent.resolve_left (by simp [Transfer.op, Operation.isIssuerMint])
    apply ih admitted.2
    intro asset'
    rw [balance_op]
    have := nonneg asset'
    split_ifs with h1 h2 <;> (try obtain ⟨rfl, rfl⟩ := h1) <;> omega

/-! ## Closing an account commutes with postings that do not name it

A batch closes its accounts after its operations (`Batch.apply`). Two batches in
sequence close the first's accounts BEFORE the second's operations; their joint
batch (`seqBatch`) closes them after. The two agree, and the joint batch is
admitted, because every operation the second batch admits names only present
accounts, so none the first closed: closing changes only the account set, an
operation never reads it, and an operation that names neither endpoint leaves an
account's balances and leases as they were. -/

theorem Operation.apply_deregisterAccount (operation : Operation) (book : Book) (account : AccountId) :
    operation.apply (book.deregisterAccount account) = (operation.apply book).deregisterAccount account := by
  cases operation <;> rfl

theorem applyOperations_deregisterAccount (account : AccountId) :
    ∀ (operations : List Operation) (book : Book),
      applyOperations (book.deregisterAccount account) operations =
        (applyOperations book operations).deregisterAccount account
  | [], _ => rfl
  | operation :: rest, book => by
    simp only [applyOperations]
    rw [Operation.apply_deregisterAccount]
    exact applyOperations_deregisterAccount account rest _

theorem applyOperations_deregisterAccounts (operations : List Operation) :
    ∀ (accounts : List AccountId) (book : Book),
      applyOperations (deregisterAccounts book accounts) operations =
        deregisterAccounts (applyOperations book operations) accounts
  | [], _ => rfl
  | account :: rest, book => by
    simp only [deregisterAccounts]
    rw [applyOperations_deregisterAccounts operations rest, applyOperations_deregisterAccount]

theorem Operation.apply_deregisterAccounts (operation : Operation) (book : Book) (accounts : List AccountId) :
    operation.apply (deregisterAccounts book accounts) = deregisterAccounts (operation.apply book) accounts := by
  have := applyOperations_deregisterAccounts [operation] accounts book
  simpa only [applyOperations] using this

theorem deregisterAccounts_append :
    ∀ (book : Book) (first later : List AccountId),
      deregisterAccounts book (first ++ later) = deregisterAccounts (deregisterAccounts book first) later
  | _, [], _ => rfl
  | book, account :: rest, later => deregisterAccounts_append (book.deregisterAccount account) rest later

theorem deregistrationsAdmitted_append :
    ∀ (book : Book) (first later : List AccountId),
      DeregistrationsAdmitted book (first ++ later) ↔
        DeregistrationsAdmitted book first ∧ DeregistrationsAdmitted (deregisterAccounts book first) later
  | _, [], _ => by simp [DeregistrationsAdmitted, deregisterAccounts]
  | book, account :: rest, later => by
    simp only [List.cons_append, DeregistrationsAdmitted, deregisterAccounts]
    rw [deregistrationsAdmitted_append _ rest later, and_assoc]

theorem mem_of_mem_deregisterAccounts {account : AccountId} :
    ∀ {book : Book} {accounts : List AccountId},
      account ∈ (deregisterAccounts book accounts).accounts → account ∈ book.accounts
  | _, [], member => member
  | book, closed :: rest, member =>
    Finset.mem_of_mem_erase (mem_of_mem_deregisterAccounts (book := book.deregisterAccount closed) member)

theorem deregisterAccounts_leaseRecords :
    ∀ (book : Book) (accounts : List AccountId),
      (deregisterAccounts book accounts).leaseRecords = book.leaseRecords
  | _, [] => rfl
  | book, account :: rest => deregisterAccounts_leaseRecords (book.deregisterAccount account) rest

/-- An operation admitted after some accounts closed is admitted before. -/
theorem Admission.of_deregistered {book : Book} {accounts : List AccountId} {operation : Operation}
    (admitted : Admission (deregisterAccounts book accounts) operation) : Admission book operation where
  sourcePresent := mem_of_mem_deregisterAccounts admitted.sourcePresent
  destinationPresent := mem_of_mem_deregisterAccounts admitted.destinationPresent
  sourceSolvent := by
    have solvent := admitted.sourceSolvent
    simpa only [Book.balance, deregisterAccounts_balances] using solvent
  leaseWellFormed := by
    have formed := admitted.leaseWellFormed
    cases operation with
    | lease => simpa only [Book.leases, deregisterAccounts_leaseRecords] using formed
    | _ => trivial

theorem OperationsAdmitted.of_deregistered (accounts : List AccountId) :
    ∀ {book : Book} {operations : List Operation},
      OperationsAdmitted (deregisterAccounts book accounts) operations → OperationsAdmitted book operations
  | _, [], _ => trivial
  | book, operation :: rest, ⟨first, later⟩ => by
    refine ⟨Admission.of_deregistered first, ?_⟩
    rw [Operation.apply_deregisterAccounts] at later
    exact OperationsAdmitted.of_deregistered accounts later

theorem Operation.apply_balances (operation : Operation) (book : Book) :
    (operation.apply book).balances = (book.applyPosting operation.posting).balances := by
  cases operation <;> rfl

/-- An operation leaves the balances of an account it does not name. -/
theorem Operation.apply_balance_other {book : Book} {operation : Operation} {account : AccountId}
    (asset : AssetId) (source : operation.posting.source ≠ account)
    (destination : operation.posting.destination ≠ account) :
    (operation.apply book).balances (account, asset) = book.balances (account, asset) := by
  rw [Operation.apply_balances]
  show (book.balances + DFinsupp.single (operation.posting.source, operation.posting.asset)
      (-(Int.ofNat operation.posting.amount)) +
      DFinsupp.single (operation.posting.destination, operation.posting.asset)
        (Int.ofNat operation.posting.amount) : Π₀ _ : AccountId × AssetId, Int) (account, asset) = _
  rw [DFinsupp.add_apply, DFinsupp.add_apply, single_at, single_at,
    if_neg (fun h => source h.1.symm), if_neg (fun h => destination h.1.symm)]
  simp

/-- A closing stays admitted across an operation that names neither endpoint as it. -/
theorem deregistrationAdmission_apply {book : Book} {account : AccountId} {operation : Operation}
    (admitted : DeregistrationAdmission book account)
    (source : operation.posting.source ≠ account) (destination : operation.posting.destination ≠ account) :
    DeregistrationAdmission (operation.apply book) account := by
  obtain ⟨kernel, present, noBalance, noLease⟩ := admitted
  refine ⟨kernel, by rw [Operation.apply_accounts]; exact present, ?_, ?_⟩
  · intro coordinate member same
    obtain ⟨named, asset⟩ := coordinate
    simp only at same
    subst same
    have nonzero := (DFinsupp.mem_support_toFun _ _).mp member
    rw [Operation.apply_balance_other asset source destination] at nonzero
    exact noBalance _ ((DFinsupp.mem_support_toFun _ _).mpr nonzero) rfl
  · cases operation with
    | lease leaseId holder lessor asset rate epochs startsAt =>
      simp only [Operation.posting] at source destination
      intro id member
      have records : ((Operation.lease leaseId holder lessor asset rate epochs startsAt).apply book).leaseRecords id =
          if id = leaseId then some (⟨holder, lessor, asset, rate * epochs, startsAt, startsAt + epochs⟩ : LeaseRecord)
          else book.leaseRecords id := by
        by_cases same : id = leaseId
        · subst same
          simp [Operation.apply, Operation.leaseRecord?, DFinsupp.coe_update, Function.update_self]
        · simp [Operation.apply, Operation.leaseRecord?, DFinsupp.coe_update, Function.update_of_ne same, same,
            Book.applyPosting]
      rw [records]
      by_cases same : id = leaseId
      · rw [if_pos same]
        simp [LeaseRecord.names, source, destination]
      · rw [if_neg same]
        apply noLease
        rw [DFinsupp.mem_support_iff] at member ⊢
        rwa [records, if_neg same] at member
    | _ => exact noLease

theorem deregistrationsAdmitted_apply {operation : Operation} :
    ∀ {book : Book} {accounts : List AccountId}, DeregistrationsAdmitted book accounts →
      operation.posting.source ∉ accounts → operation.posting.destination ∉ accounts →
      DeregistrationsAdmitted (operation.apply book) accounts
  | _, [], _, _, _ => trivial
  | book, account :: rest, ⟨first, later⟩, source, destination => by
    refine ⟨deregistrationAdmission_apply first (fun h => source (by simp [h])) (fun h => destination (by simp [h])), ?_⟩
    rw [← Operation.apply_deregisterAccount]
    exact deregistrationsAdmitted_apply later (fun m => source (List.mem_cons_of_mem _ m))
      (fun m => destination (List.mem_cons_of_mem _ m))

/-- Closings stay admitted across operations admitted after them. -/
theorem deregistrationsAdmitted_afterOperations {accounts : List AccountId} :
    ∀ {book : Book} {operations : List Operation}, DeregistrationsAdmitted book accounts →
      OperationsAdmitted (deregisterAccounts book accounts) operations →
      DeregistrationsAdmitted (applyOperations book operations) accounts
  | _, [], closed, _ => closed
  | book, operation :: rest, closed, ⟨first, later⟩ => by
    have source : operation.posting.source ∉ accounts := fun member =>
      deregisterAccounts_not_mem book accounts _ (Or.inl member) first.sourcePresent
    have destination : operation.posting.destination ∉ accounts := fun member =>
      deregisterAccounts_not_mem book accounts _ (Or.inl member) first.destinationPresent
    rw [Operation.apply_deregisterAccounts] at later
    exact deregistrationsAdmitted_afterOperations (book := operation.apply book) (operations := rest)
      (deregistrationsAdmitted_apply closed source destination) later

/-- No postings. -/
def noPostings : Batch := ⟨[], [], []⟩

/-- Two batches in sequence: registrations, operations and closings each in
order (the second registers nothing: only an offer registers, and an offer is one
step on its own). -/
def seqBatch (first later : Batch) : Batch :=
  ⟨first.registrations ++ later.registrations, first.operations ++ later.operations,
    first.deregistrations ++ later.deregistrations⟩

/-- What a step posts: one batch admitted on the step's own Book, and the next
Book is that batch applied. -/
def Posts (book : Book) (batch : Batch) (next : Book) : Prop :=
  batch.Admission book ∧ next = batch.apply book

theorem Posts.conserves {book next : Book} {batch : Batch} (posted : Posts book batch next) (asset : AssetId) :
    next.totalAsset asset = book.totalAsset asset := by
  rw [posted.2]; exact Batch.conservation book batch posted.1 asset

theorem Posts.accounts {book next : Book} {batch : Batch} (posted : Posts book batch next)
    (none : batch.registrations = []) (kept : batch.deregistrations = []) : next.accounts = book.accounts := by
  rw [posted.2]; unfold Batch.apply; rw [none, kept, deregisterAccounts_nil, applyOperations_accounts_eq]; rfl

theorem posts_none (book : Book) : Posts book noPostings book := ⟨⟨trivial, trivial, trivial⟩, rfl⟩

/-- **Two batches in sequence post their joint batch**, the first's closings
included (`deregistrationsAdmitted_afterOperations`). -/
theorem Posts.seq {book middle next : Book} {first later : Batch} (p : Posts book first middle)
    (q : Posts middle later next) (none : later.registrations = []) : Posts book (seqBatch first later) next := by
  obtain ⟨⟨regs, ops, closes⟩, rfl⟩ := p
  obtain ⟨⟨_, ops', closes'⟩, rfl⟩ := q
  simp only [Batch.apply, none, registerAccounts] at ops' closes'
  rw [applyOperations_deregisterAccounts] at closes'
  refine ⟨⟨by simpa [seqBatch, none] using regs, ?_, ?_⟩, ?_⟩
  · show OperationsAdmitted (registerAccounts book (first.registrations ++ later.registrations))
      (first.operations ++ later.operations)
    rw [none, List.append_nil, operationsAdmitted_append]
    exact ⟨ops, OperationsAdmitted.of_deregistered _ ops'⟩
  · show DeregistrationsAdmitted (applyOperations (registerAccounts book (first.registrations ++ later.registrations))
      (first.operations ++ later.operations)) (first.deregistrations ++ later.deregistrations)
    rw [none, List.append_nil, applyOperations_append_eq, deregistrationsAdmitted_append]
    exact ⟨deregistrationsAdmitted_afterOperations closes ops', closes'⟩
  · show deregisterAccounts (applyOperations (registerAccounts (deregisterAccounts (applyOperations
        (registerAccounts book first.registrations) first.operations) first.deregistrations) later.registrations)
        later.operations) later.deregistrations =
      deregisterAccounts (applyOperations (registerAccounts book (first.registrations ++ later.registrations))
        (first.operations ++ later.operations)) (first.deregistrations ++ later.deregistrations)
    rw [none, List.append_nil, applyOperations_append_eq, deregisterAccounts_append]
    simp only [registerAccounts, applyOperations_deregisterAccounts]

/-- Why a batch was refused: a label for the signer, read off the first failing
posting (the decision itself is `Batch.Admission`). -/
inductive BookRefusal where
  | accountNotFresh (account : AccountId)
  | missing (account : AccountId)
  | unfunded (account : AccountId) (asset : AssetId)
  deriving DecidableEq, Repr

def diagnoseOps : Book → List Operation → BookRefusal
  | _, [] => .missing 0
  | book, operation :: rest =>
    let posting := operation.posting
    if posting.source ∉ book.accounts then .missing posting.source
    else if posting.destination ∉ book.accounts then .missing posting.destination
    else if book.balance posting.source posting.asset < posting.amount then .unfunded posting.source posting.asset
    else diagnoseOps (operation.apply book) rest

def diagnose (book : Book) (batch : Batch) : BookRefusal :=
  if RegistrationsAdmitted book batch.registrations then
    diagnoseOps (registerAccounts book batch.registrations) batch.operations
  else .accountNotFresh (batch.registrations.headD 0)

/-! ## Payout: a seat's whole allocation to its payee -/

/-- The transfers that move a seat's balance of each listed asset (as read on
`book`) to the payee. -/
def payoutTransfers (book : Book) (account payee : AccountId) (assets : List AssetId) : List Transfer :=
  assets.map fun asset => ⟨account, payee, asset, (book.balance account asset).toNat⟩

theorem payout_sources {book : Book} {account payee : AccountId} {assets : List AssetId} :
    ∀ transfer ∈ payoutTransfers book account payee assets, transfer.source = account := by
  intro transfer member
  simp only [payoutTransfers, List.mem_map] at member
  obtain ⟨_, _, rfl⟩ := member
  rfl

/-- Over distinct assets and non-negative balances, the payout is admitted on
any book that agrees with `pre` on the seat's listed balances. -/
theorem payout_admitted_from (pre : Book) (account payee : AccountId) (different : payee ≠ account) :
    ∀ (assets : List AssetId) (book : Book), assets.Nodup →
      account ∈ book.accounts → payee ∈ book.accounts →
      (∀ asset ∈ assets, book.balance account asset = pre.balance account asset ∧ 0 ≤ pre.balance account asset) →
      OperationsAdmitted book (opsOf (payoutTransfers pre account payee assets))
  | [], _, _, _, _, _ => trivial
  | first :: rest, book, nodup, accountIn, payeeIn, agree => by
    rw [List.nodup_cons] at nodup
    obtain ⟨same, nonneg⟩ := agree first (by simp)
    refine ⟨⟨accountIn, payeeIn, Or.inr ?_, trivial⟩, ?_⟩
    · show ((pre.balance account first).toNat : Int) ≤ book.balance account first
      rw [Int.toNat_of_nonneg nonneg, same]
    · apply payout_admitted_from pre account payee different rest _ nodup.2
        (by simpa using accountIn) (by simpa using payeeIn)
      intro asset member
      have ne : asset ≠ first := fun h => nodup.1 (h ▸ member)
      refine ⟨?_, (agree asset (by simp [member])).2⟩
      rw [balance_op]
      simp [ne, (agree asset (by simp [member])).1]

/-- Over distinct assets, a payout moves exactly the seat's non-negative
balances: the seat ends at zero and the payee gains exactly that much. -/
theorem payout_exact_from (pre : Book) (account payee : AccountId) (different : payee ≠ account) :
    ∀ (assets : List AssetId) (book : Book), assets.Nodup →
      (∀ asset ∈ assets, book.balance account asset = pre.balance account asset ∧ 0 ≤ pre.balance account asset) →
      ∀ asset ∈ assets,
        (applyOperations book (opsOf (payoutTransfers pre account payee assets))).balance account asset = 0 ∧
        (applyOperations book (opsOf (payoutTransfers pre account payee assets))).balance payee asset =
          book.balance payee asset + book.balance account asset
  | [], _, _, _, asset, named => by simp at named
  | first :: rest, book, nodup, agree, asset, named => by
    rw [List.nodup_cons] at nodup
    simp only [payoutTransfers, List.map_cons, opsOf, applyOperations]
    rw [show List.map Transfer.op (List.map (fun asset => (⟨account, payee, asset,
      (pre.balance account asset).toNat⟩ : Transfer)) rest) = opsOf (payoutTransfers pre account payee rest) from rfl]
    obtain ⟨same, nonneg⟩ := agree first (by simp)
    rcases List.mem_cons.mp named with rfl | member
    · have away : ∀ transfer ∈ payoutTransfers pre account payee rest, transfer.asset ≠ asset := by
        intro transfer tmem
        simp only [payoutTransfers, List.mem_map] at tmem
        obtain ⟨a, amem, rfl⟩ := tmem
        exact fun h => nodup.1 (h ▸ amem)
      rw [ops_other_asset away, ops_other_asset away, balance_op, balance_op]
      simp only [and_self, if_true, Ne.symm different, false_and, if_false, different]
      rw [Int.toNat_of_nonneg nonneg, same]
      constructor <;> simp
    · have ne : asset ≠ first := fun h => nodup.1 (h ▸ member)
      have := payout_exact_from pre account payee different rest
        ((Transfer.op ⟨account, payee, first, (pre.balance account first).toNat⟩).apply book) nodup.2 (fun a m => by
        have ne' : a ≠ first := fun h => nodup.1 (h ▸ m)
        refine ⟨?_, (agree a (by simp [m])).2⟩
        rw [balance_op]; simp [ne', (agree a (by simp [m])).1]) asset member
      refine ⟨this.1, ?_⟩
      rw [this.2, balance_op, balance_op]
      simp [ne]

/-- Accounts other than the seat only gain. -/
theorem payout_credit_only (book pre : Book) (account payee other : AccountId) (assets : List AssetId)
    (different : other ≠ account) (asset : AssetId) :
    book.balance other asset ≤
      (applyOperations book (opsOf (payoutTransfers pre account payee assets))).balance other asset :=
  ops_credit_only (fun transfer member => (payout_sources transfer member).symm ▸ Ne.symm different) asset

/-! ## The seat world -/

/-- The protected coordinate space seat accounts live in (`Kernel.ProtectedCell`). -/
abbrev reservedBase : Nat := Minidregg.Kernel.ProtectedCell.reservedBase

/-- An ordinary account (below the protected space) is never a protected one. -/
theorem ordinary_ne_protected {ordinary protected_ : Nat} (below : ¬ reservedBase ≤ ordinary)
    (above : ¬ protected_ < reservedBase) : ordinary ≠ protected_ :=
  fun same => below (same ▸ Nat.le_of_not_lt above)

structure Seat where
  account : AccountId
  inst : InstanceId
  offerer : SubjectId
  payee : AccountId
  proposal : Proposal
  /-- The activity (its record cell) that holds this seat, if any: the
  activity's end exits it (`closeHeld`). -/
  holder : Option Nat
  isOpen : Bool
  deriving DecidableEq, Repr

structure World where
  book : Book
  registry : Registry
  seats : List Seat

def World.seat? (world : World) (account : AccountId) : Option Seat :=
  world.seats.find? (fun seat => seat.account == account)

/-- Who acts: a subject signing, the contract instance (only through the Plan
its own method returns), or the end of the activity that holds a seat. -/
inductive Actor where
  | subject (subject : SubjectId)
  | inst (inst : InstanceId)
  | activity (record : Nat)
  deriving DecidableEq, Repr

inductive Action where
  | create (inst : Instance)
  | mint (invitation : Invitation)
  | handOver (id : InvitationId) (recipient : SubjectId)
  | offer (id : InvitationId) (expect : Expectation) (seat funding payee : AccountId) (proposal : Proposal)
      (holder : Option Nat)
  | reallocate (inst : InstanceId) (transfers : List Transfer)
  | exit (seat : AccountId)
  | terminate (inst : InstanceId)
  deriving Repr

/-- Only an offer registers a Book account. -/
def Action.registers : Action → Bool
  | .offer .. => true
  | _ => false

inductive Refusal where
  | invitation (reason : Invitations.Refusal)
  | notASubject | notAnInstance | notTheInstance (inst : InstanceId)
  | seatNotProtected (account : AccountId) | fundingProtected (account : AccountId)
  | payeeProtected (account : AccountId) | payeeMissing (account : AccountId)
  | book (reason : BookRefusal)
  | offerUnsafe (account : AccountId)
  | outsideSeats (transfer : Transfer) (inst : InstanceId)
  | contractClauseRefused (inst : InstanceId)
  | seatMissing (account : AccountId) | seatClosed (account : AccountId)
  | exitNotAuthorized (account : AccountId)
  | instanceExists (inst : InstanceId)
  deriving DecidableEq, Repr

/-- Admit one batch on a Book: its result, or the named refusal. -/
def admit (book : Book) (batch : Batch) : Except Refusal Book :=
  if batch.Admission book then .ok (batch.apply book) else .error (.book (diagnose book batch))

theorem admit_posts {book next : Book} {batch : Batch} (admitted : admit book batch = .ok next) :
    Posts book batch next := by
  unfold admit at admitted
  split at admitted
  · rename_i h; cases admitted; exact ⟨h, rfl⟩
  · cases admitted

def closeSeats (seats : List Seat) (account : AccountId) : List Seat :=
  seats.map fun seat => if seat.account = account then { seat with isOpen := false } else seat

/-- The batch that closes one seat: its whole allocation to its payee. -/
def closeBatch (book : Book) (seat : Seat) : Batch :=
  ⟨[], opsOf (payoutTransfers book seat.account seat.payee seat.proposal.assets), []⟩

/-- Close one open seat: pay its whole allocation to its payee. -/
def closeSeat (world : World) (seat : Seat) : Except Refusal (World × Batch) :=
  match admit world.book (closeBatch world.book seat) with
  | .error reason => .error reason
  | .ok book => .ok ({ world with book := book, seats := closeSeats world.seats seat.account },
      closeBatch world.book seat)

def closeAll (world : World) : List Seat → Except Refusal (World × Batch)
  | [] => .ok (world, noPostings)
  | seat :: rest =>
    match closeSeat world seat with
    | .error reason => .error reason
    | .ok (middle, first) =>
      match closeAll middle rest with
      | .error reason => .error reason
      | .ok (next, later) => .ok (next, seqBatch first later)

/-- Who may exit a seat: its offerer on demand; its contract; the activity that
holds it; anyone once a deadline seat's due height is reached. The contract's
clause is not an argument. -/
def exitAuthorized (height : Nat) (actor : Actor) (seat : Seat) : Bool :=
  match actor, seat.proposal.exit with
  | .subject subject, .onDemand => subject == seat.offerer
  | .inst inst, _ => inst == seat.inst
  | .activity record, _ => seat.holder == some record
  | .subject _, .afterDeadline due => decide (due ≤ height)

def openSeatsOf (world : World) (inst : InstanceId) : List Seat :=
  world.seats.filter fun seat => seat.isOpen && seat.inst == inst

def touches (transfers : List Transfer) (account : AccountId) : Bool :=
  transfers.any fun transfer => transfer.source == account || transfer.destination == account

/-- A reallocation moves value only between open seats of its own instance, and
credits a seat only in an asset its proposal names (so `exit`, which pays only
named assets, never strands value in a closed seat). -/
def addressed (seats : List Seat) (transfer : Transfer) : Bool :=
  seats.any (fun seat => seat.account == transfer.source) &&
    seats.any (fun seat => seat.account == transfer.destination && transfer.asset ∈ seat.proposal.assets)

/-- The first open seat a reallocation touched whose law now fails. -/
def firstUnsafe (seats : List Seat) (book : Book) (transfers : List Transfer) : Option Seat :=
  seats.find? fun seat => seat.isOpen && touches transfers seat.account && !safeAt book seat.account seat.proposal

def giveTransfers (funding seat : AccountId) (proposal : Proposal) : List Transfer :=
  proposal.give.map fun entry => ⟨funding, seat, entry.1, entry.2⟩

def requestState (action : Int) : Minidregg.Pred.State := ⟨[("request/action", action)]⟩

/-- The contract's own clause, consulted for reallocations only. -/
def contractAdmits (inst : Instance) : Bool :=
  Pred.eval inst.clause (requestState 1) (requestState 1)

def retireInstance (registry : Registry) (inst : InstanceId) : Registry :=
  { registry with
    instances := registry.instances.filter (fun i => i.id ≠ inst)
    live := registry.live.filter (fun v => v.inst ≠ inst)
    spent := (registry.live.filter (fun v => v.inst = inst)).map Invitation.id ++ registry.spent
    retired := inst :: registry.retired }

/-- The batch an offer posts: register the seat account, move `give` into it. -/
def offerBatch (funding seat : AccountId) (proposal : Proposal) : Batch :=
  ⟨[seat], opsOf (giveTransfers funding seat proposal), []⟩

/-- The one transition function of the seat world: the next world and the one
Book batch the step posts. -/
def step (world : World) (height : Nat) (actor : Actor) : Action → Except Refusal (World × Batch)
  | .create inst =>
    match actor with
    | .subject _ =>
      if (world.registry.instance? inst.id).isSome || world.registry.retired.contains inst.id then
        .error (.instanceExists inst.id)
      else .ok ({ world with registry := { world.registry with instances := inst :: world.registry.instances } },
        noPostings)
    | _ => .error .notASubject
  | .mint invitation =>
    match actor with
    | .inst acting =>
      match Invitations.mint world.registry acting invitation with
      | .error reason => .error (.invitation reason)
      | .ok registry => .ok ({ world with registry := registry }, noPostings)
    | _ => .error .notAnInstance
  | .handOver id recipient =>
    match actor with
    | .subject subject =>
      match Invitations.handOver world.registry subject id recipient with
      | .error reason => .error (.invitation reason)
      | .ok registry => .ok ({ world with registry := registry }, noPostings)
    | _ => .error .notASubject
  | .offer id expect seatAccount funding payee proposal holder =>
    match actor with
    | .subject subject =>
      match Invitations.spend world.registry subject id expect with
      | .error reason => .error (.invitation reason)
      | .ok (invitation, registry) =>
        if seatAccount < reservedBase then .error (.seatNotProtected seatAccount)
        else if reservedBase ≤ funding then .error (.fundingProtected funding)
        else if reservedBase ≤ payee then .error (.payeeProtected payee)
        else if payee ∉ world.book.accounts then .error (.payeeMissing payee)
        else
          match admit world.book (offerBatch funding seatAccount proposal) with
          | .error reason => .error reason
          | .ok book =>
            if safeAt book seatAccount proposal then
              .ok ({ book := book
                     registry := registry
                     seats := ⟨seatAccount, invitation.inst, subject, payee, proposal, holder, true⟩ :: world.seats },
                offerBatch funding seatAccount proposal)
            else .error (.offerUnsafe seatAccount)
    | _ => .error .notASubject
  | .reallocate instId transfers =>
    match actor with
    | .inst acting =>
      if acting ≠ instId then .error (.notTheInstance instId)
      else match world.registry.instance? instId with
      | none => .error (.invitation (.instanceMissing instId))
      | some inst =>
        if !contractAdmits inst then .error (.contractClauseRefused instId)
        else match transfers.find? (fun transfer => !addressed (openSeatsOf world instId) transfer) with
        | some transfer => .error (.outsideSeats transfer instId)
        | none =>
          match admit world.book ⟨[], opsOf transfers, []⟩ with
          | .error reason => .error reason
          | .ok book =>
            match firstUnsafe world.seats book transfers with
            | some seat => .error (.offerUnsafe seat.account)
            | none => .ok ({ world with book := book }, ⟨[], opsOf transfers, []⟩)
    | _ => .error .notAnInstance
  | .exit account =>
    match world.seat? account with
    | none => .error (.seatMissing account)
    | some seat =>
      if !seat.isOpen then .error (.seatClosed account)
      else if !exitAuthorized height actor seat then .error (.exitNotAuthorized account)
      else closeSeat world seat
  | .terminate instId =>
    match actor with
    | .inst acting =>
      if acting ≠ instId then .error (.notTheInstance instId)
      else match closeAll world (openSeatsOf world instId) with
      | .error reason => .error reason
      | .ok (closed, batch) => .ok ({ closed with registry := retireInstance closed.registry instId }, batch)
    | _ => .error .notAnInstance

/-! ## Every step posts one admitted batch -/

theorem closeSeat_spec {world next : World} {seat : Seat} {batch : Batch}
    (closed : closeSeat world seat = .ok (next, batch)) :
    batch = closeBatch world.book seat ∧ Posts world.book batch next.book ∧
      next = { world with book := next.book, seats := closeSeats world.seats seat.account } := by
  unfold closeSeat at closed
  split at closed
  · cases closed
  · rename_i book admitted
    cases closed
    exact ⟨rfl, admit_posts admitted, rfl⟩

theorem closeAll_posts {world next : World} {seats : List Seat} {batch : Batch}
    (closed : closeAll world seats = .ok (next, batch)) :
    Posts world.book batch next.book ∧ batch.registrations = [] := by
  induction seats generalizing world next batch with
  | nil => simp only [closeAll] at closed; cases closed; exact ⟨posts_none _, rfl⟩
  | cons seat rest ih =>
    simp only [closeAll] at closed
    split at closed
    · cases closed
    · rename_i middle first hfirst
      split at closed
      · cases closed
      · rename_i later hlater
        cases closed
        obtain ⟨rfl, posted, _⟩ := closeSeat_spec hfirst
        obtain ⟨postedLater, none⟩ := ih hlater
        exact ⟨posted.seq postedLater none, by simp [seqBatch, closeBatch, none]⟩

theorem step_posts {world next : World} {height : Nat} {actor : Actor} {action : Action} {batch : Batch}
    (admitted : step world height actor action = .ok (next, batch)) :
    Posts world.book batch next.book ∧ (action.registers = false → batch.registrations = []) := by
  cases action with
  | create inst =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨posts_none _, fun _ => rfl⟩
    · cases admitted
  | mint invitation =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨posts_none _, fun _ => rfl⟩
    · cases admitted
  | handOver id recipient =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨posts_none _, fun _ => rfl⟩
    · cases admitted
  | offer id expect seatAccount funding payee proposal holder =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · split at admitted
        · cases admitted
        split at admitted
        · cases admitted
        split at admitted
        · cases admitted
        split at admitted
        · cases admitted
        split at admitted
        · cases admitted
        · rename_i book hbook
          split at admitted
          · cases admitted; exact ⟨admit_posts hbook, fun h => by simp [Action.registers] at h⟩
          · cases admitted
    · cases admitted
  | reallocate instId transfers =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      · rename_i book hbook
        split at admitted
        · cases admitted
        · cases admitted; exact ⟨admit_posts hbook, fun _ => rfl⟩
    · cases admitted
  | exit account =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    obtain ⟨rfl, posted, _⟩ := closeSeat_spec admitted
    exact ⟨posted, fun _ => rfl⟩
  | terminate instId =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      · rename_i closed hclosed
        cases admitted
        obtain ⟨posted, none⟩ := closeAll_posts hclosed
        exact ⟨posted, fun _ => none⟩
    · cases admitted

/-- **T3 (c): every admitted step conserves every asset**, by the Book's own
posting theorem on the step's one batch. -/
theorem seat_conserves {world next : World} {height : Nat} {actor : Actor} {action : Action} {batch : Batch}
    (admitted : step world height actor action = .ok (next, batch)) (asset : AssetId) :
    next.book.totalAsset asset = world.book.totalAsset asset :=
  (step_posts admitted).1.conserves asset

/-! ## The invariant -/

structure Inv (world : World) : Prop where
  safe : ∀ seat ∈ world.seats, seat.isOpen = true → safeAt world.book seat.account seat.proposal = true
  nonneg : ∀ seat ∈ world.seats, seat.isOpen = true → ∀ asset, 0 ≤ world.book.balance seat.account asset
  member : ∀ seat ∈ world.seats, seat.account ∈ world.book.accounts ∧ seat.payee ∈ world.book.accounts
  /-- A seat account is a protected coordinate; its payee is not. So no funding
  account, payee or other seat's payee is a seat account. -/
  protect : ∀ seat ∈ world.seats, reservedBase ≤ seat.account ∧ seat.payee < reservedBase
  distinct : (world.seats.map Seat.account).Nodup

theorem Inv.genesis (world : World) (empty : world.seats = []) : Inv world := by
  constructor <;> simp [empty]

theorem Inv.payeeOther {world : World} (inv : Inv world) {seat : Seat} (member : seat ∈ world.seats) :
    seat.payee ≠ seat.account := by
  obtain ⟨above, below⟩ := inv.protect seat member
  exact Nat.ne_of_lt (lt_of_lt_of_le below above)

/-- In a world with distinct seat accounts, the seat found by account is the
one in the list. -/
theorem seat?_eq {world : World} (distinct : (world.seats.map Seat.account).Nodup) {seat : Seat}
    (member : seat ∈ world.seats) : world.seat? seat.account = some seat := by
  unfold World.seat?
  obtain ⟨found, hfound⟩ : ∃ found, world.seats.find? (fun s => s.account == seat.account) = some found := by
    cases h : world.seats.find? (fun s => s.account == seat.account) with
    | none => rw [List.find?_eq_none] at h; exact absurd (h seat member) (by simp)
    | some found => exact ⟨found, rfl⟩
  rw [hfound]
  have foundMember := List.mem_of_find?_eq_some hfound
  have sameAccount : found.account = seat.account := by simpa using List.find?_some hfound
  exact congrArg some (List.inj_on_of_nodup_map distinct foundMember member sameAccount)

theorem closeSeats_map_account (seats : List Seat) (account : AccountId) :
    (closeSeats seats account).map Seat.account = seats.map Seat.account := by
  unfold closeSeats
  rw [List.map_map]
  apply List.map_congr_left
  intro seat _
  simp only [Function.comp_apply]
  split_ifs <;> rfl

theorem mem_closeSeats {seats : List Seat} {account : AccountId} {seat : Seat}
    (member : seat ∈ closeSeats seats account) :
    ∃ original ∈ seats, original.account = seat.account ∧ original.payee = seat.payee ∧
      original.proposal = seat.proposal ∧ original.inst = seat.inst ∧ original.holder = seat.holder ∧
      (seat.isOpen = true → original.isOpen = true ∧ seat.account ≠ account) := by
  unfold closeSeats at member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  refine ⟨original, originalMember, ?_⟩
  split_ifs with same
  · simp
  · exact ⟨rfl, rfl, rfl, rfl, rfl, fun o => ⟨o, same⟩⟩

/-- Closing a seat changes the book only by its payout. -/
theorem closeSeat_book {world next : World} {seat : Seat} {batch : Batch}
    (closed : closeSeat world seat = .ok (next, batch)) :
    next.book = applyOperations world.book (opsOf (payoutTransfers world.book seat.account seat.payee
      seat.proposal.assets)) := by
  obtain ⟨rfl, posted, _⟩ := closeSeat_spec closed
  rw [posted.2]; rfl

/-- Closing one seat of the list preserves the invariant. -/
theorem closeSeat_inv {world next : World} {seat : Seat} {batch : Batch} (inv : Inv world)
    (closed : closeSeat world seat = .ok (next, batch)) : Inv next := by
  have book := closeSeat_book closed
  obtain ⟨rfl, posted, shape⟩ := closeSeat_spec closed
  have accounts := posted.accounts rfl rfl
  rw [shape]
  constructor
  · intro s hs openS
    obtain ⟨o, ho, account, _, proposal, _, _, opened⟩ := mem_closeSeats hs
    obtain ⟨oOpen, different⟩ := opened openS
    rw [← account, ← proposal]
    show safeAt next.book o.account o.proposal = true
    rw [book]
    exact safeAt_mono (fun asset _ => payout_credit_only _ _ _ _ _ _ (account ▸ different) asset)
      (inv.safe o ho oOpen)
  · intro s hs openS asset
    obtain ⟨o, ho, account, _, _, _, _, opened⟩ := mem_closeSeats hs
    obtain ⟨oOpen, different⟩ := opened openS
    rw [← account]
    show 0 ≤ next.book.balance o.account asset
    rw [book]
    exact le_trans (inv.nonneg o ho oOpen asset) (payout_credit_only _ _ _ _ _ _ (account ▸ different) asset)
  · intro s hs
    obtain ⟨o, ho, account, payee, _⟩ := mem_closeSeats hs
    rw [← account, ← payee]
    show o.account ∈ next.book.accounts ∧ o.payee ∈ next.book.accounts
    rw [accounts]; exact inv.member o ho
  · intro s hs
    obtain ⟨o, ho, account, payee, _⟩ := mem_closeSeats hs
    rw [← account, ← payee]
    exact inv.protect o ho
  · show ((closeSeats world.seats seat.account).map Seat.account).Nodup
    rw [closeSeats_map_account]; exact inv.distinct

theorem closeSeat_seats {world next : World} {seat : Seat} {batch : Batch}
    (closed : closeSeat world seat = .ok (next, batch)) : next.seats = closeSeats world.seats seat.account := by
  obtain ⟨_, _, shape⟩ := closeSeat_spec closed
  rw [shape]

theorem closeAll_inv {world next : World} {seats : List Seat} {batch : Batch} (inv : Inv world)
    (closed : closeAll world seats = .ok (next, batch)) : Inv next := by
  induction seats generalizing world next batch with
  | nil => simp only [closeAll] at closed; cases closed; exact inv
  | cons seat rest ih =>
    simp only [closeAll] at closed
    split at closed
    · cases closed
    · rename_i middle first hfirst
      split at closed
      · cases closed
      · rename_i later hlater
        cases closed
        exact ih (closeSeat_inv inv hfirst) hlater

/-- An account none of the closed seats owns only gains during `closeAll`. -/
theorem closeAll_credit_only {world next : World} {seats : List Seat} {batch : Batch} {account : AccountId}
    (closed : closeAll world seats = .ok (next, batch)) (away : ∀ seat ∈ seats, seat.account ≠ account)
    (asset : AssetId) : world.book.balance account asset ≤ next.book.balance account asset := by
  induction seats generalizing world next batch with
  | nil => simp only [closeAll] at closed; cases closed; exact le_rfl
  | cons seat rest ih =>
    simp only [closeAll] at closed
    split at closed
    · cases closed
    · rename_i middle first hfirst
      split at closed
      · cases closed
      · rename_i later hlater
        cases closed
        refine le_trans ?_ (ih hlater (fun s m => away s (by simp [m])))
        rw [closeSeat_book hfirst]
        exact payout_credit_only _ _ _ _ _ _ (Ne.symm (away seat (by simp))) asset

/-! ## The offer and reallocation cases -/

theorem offer_inv {world : World} (inv : Inv world) {seatAccount funding payee : AccountId}
    {subject : SubjectId} {proposal : Proposal} {book : Book} {inst : InstanceId} {registry : Registry}
    {holder : Option Nat}
    (protectedSeat : ¬ seatAccount < reservedBase) (fundingOrdinary : ¬ reservedBase ≤ funding)
    (payeeOrdinary : ¬ reservedBase ≤ payee) (payeeIn : payee ∈ world.book.accounts)
    (admitted : admit world.book (offerBatch funding seatAccount proposal) = .ok book)
    (safeNew : safeAt book seatAccount proposal = true) :
    Inv { book := book
          registry := registry
          seats := ⟨seatAccount, inst, subject, payee, proposal, holder, true⟩ :: world.seats } := by
  obtain ⟨⟨⟨registered, _⟩, _⟩, rfl⟩ := admit_posts admitted
  have fresh := registered.1
  have accountsEq : (Batch.apply (offerBatch funding seatAccount proposal) world.book).accounts =
      insert seatAccount world.book.accounts := by
    unfold Batch.apply
    rw [show (offerBatch funding seatAccount proposal).deregistrations = [] from rfl, deregisterAccounts_nil,
      applyOperations_accounts_eq]; rfl
  have fundingOther : funding ≠ seatAccount := ordinary_ne_protected fundingOrdinary protectedSeat
  have away : ∀ s ∈ world.seats, ∀ t ∈ giveTransfers funding seatAccount proposal,
      t.source ≠ s.account ∧ t.destination ≠ s.account := by
    intro s hs t ht
    simp only [giveTransfers, List.mem_map] at ht
    obtain ⟨e, _, rfl⟩ := ht
    have above := (inv.protect s hs).1
    refine ⟨fun eq => ordinary_ne_protected fundingOrdinary (Nat.not_lt.mpr above) (by simpa using eq),
      fun eq => fresh (by simp only at eq; rw [eq]; exact (inv.member s hs).1)⟩
  have untouched : ∀ s ∈ world.seats, ∀ asset,
      (Batch.apply (offerBatch funding seatAccount proposal) world.book).balance s.account asset =
        world.book.balance s.account asset := by
    intro s hs asset
    exact ops_untouched (away s hs) asset
  constructor
  · intro s hs openS
    rcases List.mem_cons.mp hs with rfl | old
    · exact safeNew
    · show safeAt (Batch.apply (offerBatch funding seatAccount proposal) world.book) s.account s.proposal = true
      rw [safeAt_congr (fun asset _ => untouched s old asset)]
      exact inv.safe s old openS
  · intro s hs openS asset
    rcases List.mem_cons.mp hs with rfl | old
    · have zero : (world.book.registerAccount seatAccount).balance seatAccount asset = 0 :=
        RegistrationAdmission.balance_zero registered asset
      have credit := ops_credit_only (book := world.book.registerAccount seatAccount)
        (transfers := giveTransfers funding seatAccount proposal) (account := seatAccount) (fun t ht => by
          simp only [giveTransfers, List.mem_map] at ht
          obtain ⟨e, _, rfl⟩ := ht
          exact fundingOther) asset
      rw [zero] at credit; exact credit
    · show 0 ≤ (Batch.apply (offerBatch funding seatAccount proposal) world.book).balance s.account asset
      rw [untouched s old]; exact inv.nonneg s old openS asset
  · intro s hs
    show s.account ∈ (Batch.apply (offerBatch funding seatAccount proposal) world.book).accounts ∧
      s.payee ∈ (Batch.apply (offerBatch funding seatAccount proposal) world.book).accounts
    rw [accountsEq]
    rcases List.mem_cons.mp hs with rfl | old
    · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem payeeIn⟩
    · exact ⟨Finset.mem_insert_of_mem (inv.member s old).1, Finset.mem_insert_of_mem (inv.member s old).2⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | old
    · exact ⟨Nat.le_of_not_lt protectedSeat, Nat.lt_of_not_le payeeOrdinary⟩
    · exact inv.protect s old
  · show ((⟨seatAccount, inst, subject, payee, proposal, holder, true⟩ :: world.seats).map Seat.account).Nodup
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun mem => ?_, inv.distinct⟩
    obtain ⟨s, hs, eq⟩ := List.mem_map.mp mem
    simp only at eq
    exact fresh (eq ▸ (inv.member s hs).1)

theorem reallocate_inv {world : World} (inv : Inv world) {transfers : List Transfer} {book : Book}
    (admitted : admit world.book ⟨[], opsOf transfers, []⟩ = .ok book)
    (noneUnsafe : firstUnsafe world.seats book transfers = none) :
    Inv { world with book := book } := by
  obtain ⟨⟨_, ops, _⟩, rfl⟩ := admit_posts admitted
  have bookEq : Batch.apply ⟨[], opsOf transfers, []⟩ world.book = applyOperations world.book (opsOf transfers) := rfl
  unfold firstUnsafe at noneUnsafe
  rw [List.find?_eq_none] at noneUnsafe
  rw [bookEq] at noneUnsafe ⊢
  constructor
  · intro s hs openS
    by_cases touched : touches transfers s.account = true
    · have := noneUnsafe s hs
      simpa [openS, touched] using this
    · have away : ∀ t ∈ transfers, t.source ≠ s.account ∧ t.destination ≠ s.account := by
        intro t ht
        simp only [touches, List.any_eq_true, Bool.or_eq_true, beq_iff_eq, not_exists, not_and,
          not_or] at touched
        exact touched t ht
      show safeAt (applyOperations world.book (opsOf transfers)) s.account s.proposal = true
      rw [safeAt_congr (fun asset _ => ops_untouched away asset)]
      exact inv.safe s hs openS
  · intro s hs openS asset
    exact ops_nonneg ops (inv.nonneg s hs openS) asset
  · intro s hs
    show s.account ∈ (applyOperations world.book (opsOf transfers)).accounts ∧
      s.payee ∈ (applyOperations world.book (opsOf transfers)).accounts
    rw [applyOperations_accounts_eq]; exact inv.member s hs
  · exact inv.protect
  · exact inv.distinct

/-! ## T3 (a): every open seat of every reachable world satisfies its law -/

theorem step_inv {world next : World} {height : Nat} {actor : Actor} {action : Action} {batch : Batch}
    (inv : Inv world) (admitted : step world height actor action = .ok (next, batch)) : Inv next := by
  cases action with
  | create inst =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨inv.safe, inv.nonneg, inv.member, inv.protect, inv.distinct⟩
    · cases admitted
  | mint invitation =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨inv.safe, inv.nonneg, inv.member, inv.protect, inv.distinct⟩
    · cases admitted
  | handOver id recipient =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨inv.safe, inv.nonneg, inv.member, inv.protect, inv.distinct⟩
    · cases admitted
  | offer id expect seatAccount funding payee proposal holder =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · rename_i invitation registry _
        split at admitted
        · cases admitted
        rename_i protectedSeat
        split at admitted
        · cases admitted
        rename_i fundingOrdinary
        split at admitted
        · cases admitted
        rename_i payeeOrdinary
        split at admitted
        · cases admitted
        rename_i payeeIn
        split at admitted
        · cases admitted
        · rename_i book hbook
          split at admitted
          · rename_i safeNew
            cases admitted
            exact offer_inv inv protectedSeat fundingOrdinary payeeOrdinary (not_not.mp payeeIn) hbook safeNew
          · cases admitted
    · cases admitted
  | reallocate instId transfers =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      · rename_i book hbook
        split at admitted
        · cases admitted
        · rename_i noneUnsafe
          cases admitted
          exact reallocate_inv inv hbook noneUnsafe
    · cases admitted
  | exit account =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    exact closeSeat_inv inv admitted
  | terminate instId =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      · rename_i closed hclosed
        cases admitted
        have := closeAll_inv inv hclosed
        exact ⟨this.safe, this.nonneg, this.member, this.protect, this.distinct⟩
    · cases admitted

inductive Reachable (genesis : World) : World → Prop
  | start : Reachable genesis genesis
  | admit {world next : World} {batch : Batch} (height : Nat) (actor : Actor) (action : Action) :
      Reachable genesis world → step world height actor action = .ok (next, batch) → Reachable genesis next

theorem reachable_inv {genesis world : World} (empty : genesis.seats = [])
    (reachable : Reachable genesis world) : Inv world := by
  induction reachable with
  | start => exact Inv.genesis genesis empty
  | admit _ _ _ _ admitted ih => exact step_inv ih admitted

/-- **T3 (a).** From a world with no seats, in every world reachable by admitted
steps, every open seat's Book balances satisfy its offer-safety law. -/
theorem seat_offer_safe_forever {genesis world : World} (empty : genesis.seats = [])
    (reachable : Reachable genesis world) :
    ∀ seat ∈ world.seats, seat.isOpen = true → safeAt world.book seat.account seat.proposal = true :=
  (reachable_inv empty reachable).safe

/-! ## T3 (b): exit is always available and pays exactly the allocation -/

theorem closeBatch_admitted {world : World} {seat : Seat} (inv : Inv world) (member : seat ∈ world.seats)
    (opened : seat.isOpen = true) : (closeBatch world.book seat).Admission world.book :=
  ⟨trivial, payout_admitted_from world.book seat.account seat.payee (inv.payeeOther member) _ world.book
    (List.nodup_dedup _) (inv.member seat member).1 (inv.member seat member).2
    (fun asset _ => ⟨rfl, inv.nonneg seat member opened asset⟩), trivial⟩

theorem exit_admitted {world : World} {height : Nat} {actor : Actor} {seat : Seat} (inv : Inv world)
    (member : seat ∈ world.seats) (opened : seat.isOpen = true)
    (authorized : exitAuthorized height actor seat = true) :
    step world height actor (.exit seat.account) =
      .ok ({ world with
        book := (closeBatch world.book seat).apply world.book
        seats := closeSeats world.seats seat.account }, closeBatch world.book seat) := by
  simp only [step, seat?_eq inv.distinct member, opened, authorized, Bool.not_true, if_false,
    Bool.false_eq_true]
  unfold closeSeat admit
  rw [if_pos (closeBatch_admitted inv member opened)]

/-- **T3 (b), the offerer's right.** An on-demand seat's offerer can exit at any
height, whatever any contract clause says: the step does not consult one. -/
theorem exit_enabled {world : World} {seat : Seat} (inv : Inv world) (member : seat ∈ world.seats)
    (opened : seat.isOpen = true) (onDemand : seat.proposal.exit = .onDemand) (height : Nat) :
    ∃ next, step world height (.subject seat.offerer) (.exit seat.account) = .ok next :=
  ⟨_, exit_admitted inv member opened (by simp [exitAuthorized, onDemand])⟩

/-- A seat with a deadline can be exited by anyone once the deadline is reached. -/
theorem exit_after_deadline {world : World} {seat : Seat} (inv : Inv world) (member : seat ∈ world.seats)
    (opened : seat.isOpen = true) {due height : Nat} (deadline : seat.proposal.exit = .afterDeadline due)
    (reached : due ≤ height) (anyone : SubjectId) :
    ∃ next, step world height (.subject anyone) (.exit seat.account) = .ok next :=
  ⟨_, exit_admitted inv member opened (by simp [exitAuthorized, deadline, reached])⟩

/-- The activity that holds a seat can always end it. -/
theorem exit_by_holder {world : World} {seat : Seat} (inv : Inv world) (member : seat ∈ world.seats)
    (opened : seat.isOpen = true) {record : Nat} (held : seat.holder = some record) (height : Nat) :
    ∃ next, step world height (.activity record) (.exit seat.account) = .ok next :=
  ⟨_, exit_admitted inv member opened (by simp [exitAuthorized, held])⟩

theorem closeBatch_pays {world : World} {seat : Seat} (inv : Inv world) (member : seat ∈ world.seats)
    (opened : seat.isOpen = true) :
    ∀ asset ∈ seat.proposal.assets,
      ((closeBatch world.book seat).apply world.book).balance seat.account asset = 0 ∧
      ((closeBatch world.book seat).apply world.book).balance seat.payee asset =
        world.book.balance seat.payee asset + world.book.balance seat.account asset :=
  payout_exact_from world.book seat.account seat.payee (inv.payeeOther member) _ world.book
    (List.nodup_dedup _) (fun asset _ => ⟨rfl, inv.nonneg seat member opened asset⟩)

/-- **T3 (b), what an exit pays.** The seat ends at zero in every asset its
proposal names, and its payee gains exactly the seat's balance. -/
theorem exit_pays_allocation {world next : World} {height : Nat} {actor : Actor} {seat : Seat}
    {batch : Batch} (inv : Inv world) (member : seat ∈ world.seats) (opened : seat.isOpen = true)
    (admitted : step world height actor (.exit seat.account) = .ok (next, batch)) :
    ∀ asset ∈ seat.proposal.assets, next.book.balance seat.account asset = 0 ∧
      next.book.balance seat.payee asset = world.book.balance seat.payee asset + world.book.balance seat.account asset := by
  have authorized : exitAuthorized height actor seat = true := by
    simp only [step, seat?_eq inv.distinct member, opened, Bool.not_true, if_false,
      Bool.false_eq_true] at admitted
    split at admitted
    · cases admitted
    · rename_i h; simpa using h
  rw [exit_admitted inv member opened authorized] at admitted
  cases admitted
  exact closeBatch_pays inv member opened

/-- **Who may exit.** An admitted exit was of an open seat, by an actor the
kernel's `exitAuthorized` admits: its offerer (on demand), its contract, the
activity that holds it, or anyone at or after its due height. The instance's
clause is not an argument of `exitAuthorized`: no contract can forbid an exit. -/
theorem exit_step_authorized {world next : World} {height : Nat} {actor : Actor} {account : AccountId}
    {batch : Batch} (admitted : step world height actor (.exit account) = .ok (next, batch)) :
    ∃ seat ∈ world.seats, seat.account = account ∧ seat.isOpen = true ∧ exitAuthorized height actor seat = true := by
  simp only [step] at admitted
  split at admitted
  · cases admitted
  rename_i seat found
  split at admitted
  · cases admitted
  rename_i opened
  split at admitted
  · cases admitted
  rename_i authorized
  refine ⟨seat, List.mem_of_find?_eq_some found, by simpa using List.find?_some found, ?_, ?_⟩
  · cases h : seat.isOpen <;> simp_all
  · cases h : exitAuthorized height actor seat <;> simp_all

/-! ## Who may debit a seat -/

/-- **A seat is debited only by its own instance's reallocation, its exit, or
its instance's termination.** -/
theorem seat_debit_authorized {world next : World} {height : Nat} {actor : Actor} {action : Action}
    {batch : Batch} (inv : Inv world) (admitted : step world height actor action = .ok (next, batch))
    {seat : Seat} (member : seat ∈ world.seats) {asset : AssetId}
    (debited : next.book.balance seat.account asset < world.book.balance seat.account asset) :
    (actor = .inst seat.inst ∧ ∃ transfers, action = .reallocate seat.inst transfers) ∨
      action = .exit seat.account ∨ (actor = .inst seat.inst ∧ action = .terminate seat.inst) := by
  cases action with
  | create inst =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact absurd debited (lt_irrefl _)
    · cases admitted
  | mint invitation =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact absurd debited (lt_irrefl _)
    · cases admitted
  | handOver id recipient =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact absurd debited (lt_irrefl _)
    · cases admitted
  | offer id expect seatAccount funding payee proposal holder =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · split at admitted
        · cases admitted
        split at admitted
        · cases admitted
        rename_i fundingOrdinary
        split at admitted
        · cases admitted
        split at admitted
        · cases admitted
        split at admitted
        · cases admitted
        · rename_i book hbook
          split at admitted
          · cases admitted
            obtain ⟨⟨⟨registered, _⟩, _⟩, rfl⟩ := admit_posts hbook
            have protect := (inv.protect seat member).1
            have away : ∀ t ∈ giveTransfers funding seatAccount proposal,
                t.source ≠ seat.account ∧ t.destination ≠ seat.account := by
              intro t ht
              simp only [giveTransfers, List.mem_map] at ht
              obtain ⟨e, _, rfl⟩ := ht
              exact ⟨fun eq => ordinary_ne_protected fundingOrdinary (Nat.not_lt.mpr protect) (by simpa using eq),
                fun eq => registered.1 (by simp only at eq; rw [eq]; exact (inv.member seat member).1)⟩
            have := ops_untouched (book := world.book.registerAccount seatAccount) away asset
            exact absurd (this.trans rfl ▸ debited) (lt_irrefl _)
          · cases admitted
    · cases admitted
  | reallocate instId transfers =>
    simp only [step] at admitted
    split at admitted
    · rename_i acting
      split at admitted
      · cases admitted
      rename_i sameInst
      split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      rename_i addressedAll
      split at admitted
      · cases admitted
      · rename_i book hbook
        split at admitted
        · cases admitted
        · cases admitted
          obtain ⟨_, rfl⟩ := admit_posts hbook
          have acting' : acting = instId := not_not.mp sameInst
          subst acting'
          have source : ∃ transfer ∈ transfers, transfer.source = seat.account := by
            by_contra none
            simp only [not_exists, not_and] at none
            exact absurd (ops_credit_only (book := world.book) (fun t m h => none t m h) asset) (not_le.mpr debited)
          obtain ⟨transfer, tmem, tsrc⟩ := source
          have within := List.find?_eq_none.mp addressedAll transfer tmem
          simp only [Bool.not_eq_true', Bool.not_eq_false, addressed, Bool.and_eq_true, List.any_eq_true,
            beq_iff_eq] at within
          obtain ⟨⟨s, smem, saccount⟩, _⟩ := within
          have sseat : s ∈ world.seats := (List.mem_filter.mp smem).1
          have sinst : s.inst = acting := by
            have := (List.mem_filter.mp smem).2
            simp only [Bool.and_eq_true, beq_iff_eq] at this
            exact this.2
          have same : s = seat := List.inj_on_of_nodup_map inv.distinct sseat member (saccount.trans tsrc)
          subst same
          exact Or.inl ⟨by rw [sinst], transfers, by rw [sinst]⟩
    · cases admitted
  | exit account =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    rename_i closing found
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    have book := closeSeat_book admitted
    have closingAccount : closing.account = account := by
      simpa using List.find?_some found
    by_cases same : seat.account = account
    · exact Or.inr (Or.inl (by rw [same]))
    · exfalso
      have := payout_credit_only world.book world.book closing.account closing.payee seat.account
        closing.proposal.assets (by rw [closingAccount]; exact same) asset
      rw [← book] at this
      exact absurd this (not_le.mpr debited)
  | terminate instId =>
    simp only [step] at admitted
    split at admitted
    · rename_i acting
      split at admitted
      · cases admitted
      rename_i sameInst
      split at admitted
      · cases admitted
      · rename_i closed hclosed
        cases admitted
        have acting' : acting = instId := not_not.mp sameInst
        subst acting'
        by_cases same : seat.inst = acting
        · exact Or.inr (Or.inr ⟨by rw [same], by rw [same]⟩)
        · exfalso
          have away : ∀ s ∈ openSeatsOf world acting, s.account ≠ seat.account := by
            intro s hs eq
            have sseat : s ∈ world.seats := (List.mem_filter.mp hs).1
            have sinst : s.inst = acting := by
              have := (List.mem_filter.mp hs).2
              simp only [Bool.and_eq_true, beq_iff_eq] at this
              exact this.2
            have := List.inj_on_of_nodup_map inv.distinct sseat member eq
            subst this
            exact same sinst
          exact absurd (closeAll_credit_only hclosed away asset) (not_le.mpr debited)
    · cases admitted

/-! ## A contract method's Plan, and an activity's end

On the native route the instance never signs. `reallocate`, `mint`, a
contract-initiated `exit` and `terminate` reach `step` only as the members of
the Plan the instance's own package method returns when the receiver
re-executes it (`Kernel.SeatReceiver`), each a step of the instance, in order,
under ONE batch: so every touched seat's law judges every reallocation, and the
whole Plan commits or nothing does. A minted invitation's id is the receiver's
`mintId index` (a digest of the instance, the invoking turn and the index), and
its package is the instance's own: the code chooses role, terms and holder,
never the id or the package. -/

inductive PlanAction where
  | reallocate (transfers : List Transfer)
  | mint (role : String) (terms : List (String × Nat)) (holder : SubjectId)
  | exit (seat : AccountId)
  | terminate
  deriving DecidableEq, Repr

def PlanAction.action (inst : Instance) (mintId : Nat → InvitationId) (index : Nat) : PlanAction → Action
  | .reallocate transfers => .reallocate inst.id transfers
  | .mint role terms holder => .mint ⟨mintId index, inst.id, inst.package, role, terms, holder⟩
  | .exit seat => .exit seat
  | .terminate => .terminate inst.id

def runPlan (height : Nat) (inst : Instance) (mintId : Nat → InvitationId) :
    World → Nat → List PlanAction → Except Refusal (World × Batch)
  | world, _, [] => .ok (world, noPostings)
  | world, index, first :: rest =>
    match step world height (.inst inst.id) (first.action inst mintId index) with
    | .error reason => .error reason
    | .ok (middle, posted) =>
      match runPlan height inst mintId middle (index + 1) rest with
      | .error reason => .error reason
      | .ok (next, later) => .ok (next, seqBatch posted later)

theorem PlanAction.action_registers (inst : Instance) (mintId : Nat → InvitationId) (index : Nat)
    (planned : PlanAction) : (planned.action inst mintId index).registers = false := by
  cases planned <;> rfl

theorem runPlan_posts {height : Nat} {inst : Instance} {mintId : Nat → InvitationId} :
    ∀ {world next : World} {index : Nat} {plan : List PlanAction} {batch : Batch},
      runPlan height inst mintId world index plan = .ok (next, batch) →
      Posts world.book batch next.book ∧ batch.registrations = []
  | world, next, index, [], batch, ran => by
    simp only [runPlan] at ran; cases ran; exact ⟨posts_none _, rfl⟩
  | world, next, index, first :: rest, batch, ran => by
    simp only [runPlan] at ran
    split at ran
    · cases ran
    · rename_i middle posted hstep
      split at ran
      · cases ran
      · rename_i later hrest
        cases ran
        obtain ⟨p, none⟩ := step_posts hstep
        obtain ⟨q, none'⟩ := runPlan_posts hrest
        have r := none (PlanAction.action_registers inst mintId index first)
        exact ⟨p.seq q none', by simp [seqBatch, r, none']⟩

theorem runPlan_reachable {height : Nat} {inst : Instance} {mintId : Nat → InvitationId} {genesis : World} :
    ∀ {world next : World} {index : Nat} {plan : List PlanAction} {batch : Batch},
      Reachable genesis world → runPlan height inst mintId world index plan = .ok (next, batch) →
      Reachable genesis next
  | world, next, index, [], batch, reachable, ran => by
    simp only [runPlan] at ran; cases ran; exact reachable
  | world, next, index, first :: rest, batch, reachable, ran => by
    simp only [runPlan] at ran
    split at ran
    · cases ran
    · rename_i middle posted hstep
      split at ran
      · cases ran
      · rename_i later hrest
        cases ran
        exact runPlan_reachable (Reachable.admit height _ _ reachable hstep) hrest

/-- The open seats an activity holds. -/
def heldOpen (world : World) (record : Nat) : List Seat :=
  world.seats.filter fun seat => seat.isOpen && seat.holder == some record

/-- The end of the activity at `record`: exit every open seat it holds, each a
step of `Actor.activity record`, under one batch. -/
def exitEach (height : Nat) (record : Nat) : World → List AccountId → Except Refusal (World × Batch)
  | world, [] => .ok (world, noPostings)
  | world, account :: rest =>
    match step world height (.activity record) (.exit account) with
    | .error reason => .error reason
    | .ok (middle, posted) =>
      match exitEach height record middle rest with
      | .error reason => .error reason
      | .ok (next, later) => .ok (next, seqBatch posted later)

def closeHeld (world : World) (height : Nat) (record : Nat) : Except Refusal (World × Batch) :=
  exitEach height record world ((heldOpen world record).map Seat.account)

theorem exitEach_posts {height record : Nat} :
    ∀ {world next : World} {accounts : List AccountId} {batch : Batch},
      exitEach height record world accounts = .ok (next, batch) →
      Posts world.book batch next.book ∧ batch.registrations = [] ∧
        ∀ {genesis : World}, Reachable genesis world → Reachable genesis next
  | world, next, [], batch, ran => by
    simp only [exitEach] at ran; cases ran; exact ⟨posts_none _, rfl, id⟩
  | world, next, account :: rest, batch, ran => by
    simp only [exitEach] at ran
    split at ran
    · cases ran
    · rename_i middle posted hstep
      split at ran
      · cases ran
      · rename_i later hrest
        cases ran
        obtain ⟨p, none⟩ := step_posts hstep
        obtain ⟨q, none', reach⟩ := exitEach_posts hrest
        exact ⟨p.seq q none', by simp [seqBatch, none rfl, none'],
          fun reachable => reach (Reachable.admit height _ _ reachable hstep)⟩

/-- A step that exits one seat keeps every other seat's open flag and its
account balances in other accounts' favour; after `exitEach` every listed seat
is closed. -/
theorem step_exit_closes {world next : World} {height : Nat} {actor : Actor} {account : AccountId}
    {batch : Batch} (admitted : step world height actor (.exit account) = .ok (next, batch)) :
    next.seats = closeSeats world.seats account := by
  simp only [step] at admitted
  split at admitted
  · cases admitted
  rename_i closing found
  split at admitted
  · cases admitted
  split at admitted
  · cases admitted
  rw [closeSeat_seats admitted]
  have : closing.account = account := by simpa using List.find?_some found
  rw [this]

theorem closeSeats_closed (seats : List Seat) (account : AccountId) :
    ∀ seat ∈ closeSeats seats account, seat.account = account → seat.isOpen = false := by
  intro seat member same
  obtain ⟨original, _, _, _, _, _, _, opened⟩ := mem_closeSeats member
  cases h : seat.isOpen
  · rfl
  · exact absurd same (opened h).2

theorem closeSeats_keeps_closed (seats : List Seat) (account : AccountId) (target : AccountId)
    (closed : ∀ seat ∈ seats, seat.account = target → seat.isOpen = false) :
    ∀ seat ∈ closeSeats seats account, seat.account = target → seat.isOpen = false := by
  intro seat member same
  obtain ⟨original, omem, oaccount, _, _, _, _, opened⟩ := mem_closeSeats member
  cases h : seat.isOpen
  · rfl
  · exact absurd (closed original omem (oaccount.trans same)) (by simp [(opened h).1])

theorem exitEach_keeps_closed {height record : Nat} {world next : World} {accounts : List AccountId} {batch : Batch}
    (ran : exitEach height record world accounts = .ok (next, batch)) (target : AccountId)
    (closed : ∀ seat ∈ world.seats, seat.account = target → seat.isOpen = false) :
    ∀ seat ∈ next.seats, seat.account = target → seat.isOpen = false := by
  induction accounts generalizing world next batch with
  | nil => simp only [exitEach] at ran; cases ran; exact closed
  | cons first rest ih =>
    simp only [exitEach] at ran
    split at ran
    · cases ran
    · rename_i middle posted hstep
      split at ran
      · cases ran
      · rename_i later hrest
        cases ran
        apply ih hrest
        rw [step_exit_closes hstep]
        exact closeSeats_keeps_closed _ _ _ closed

theorem exitEach_closes {height record : Nat} :
    ∀ {world next : World} {accounts : List AccountId} {batch : Batch},
      exitEach height record world accounts = .ok (next, batch) →
      ∀ account ∈ accounts, ∀ seat ∈ next.seats, seat.account = account → seat.isOpen = false
  | world, next, [], batch, _, account, named => by simp at named
  | world, next, first :: rest, batch, ran, account, named => by
    simp only [exitEach] at ran
    split at ran
    · cases ran
    · rename_i middle posted hstep
      split at ran
      · cases ran
      · rename_i later hrest
        cases ran
        rcases List.mem_cons.mp named with rfl | member
        · -- closed by the first exit, and no later exit reopens a seat
          have firstClosed : ∀ seat ∈ middle.seats, seat.account = account → seat.isOpen = false := by
            rw [step_exit_closes hstep]; exact closeSeats_closed _ _
          exact exitEach_keeps_closed hrest account firstClosed
        · exact exitEach_closes hrest account member

/-- **The end of an activity closes every seat it holds.** If the ending turn's
`closeHeld` is admitted, every seat that was open and held by the activity is
closed in the result, and the whole is one admitted batch that conserves every
asset. (Each exit pays its payee exactly the seat's allocation:
`exit_pays_allocation`; and `exit_by_holder` makes every such exit admissible
from any world satisfying `Inv`.) -/
theorem activity_end_closes_seats {world next : World} {height record : Nat} {batch : Batch}
    (ended : closeHeld world height record = .ok (next, batch)) :
    (∀ seat ∈ heldOpen world record, ∀ after ∈ next.seats, after.account = seat.account → after.isOpen = false) ∧
      Posts world.book batch next.book ∧ ∀ asset, next.book.totalAsset asset = world.book.totalAsset asset := by
  obtain ⟨posted, _, _⟩ := exitEach_posts ended
  refine ⟨fun seat member after amember same =>
    exitEach_closes ended seat.account (List.mem_map.mpr ⟨seat, member, rfl⟩) after amember same, posted,
    posted.conserves⟩

theorem closeHeld_reachable {genesis world next : World} {height record : Nat} {batch : Batch}
    (reachable : Reachable genesis world) (ended : closeHeld world height record = .ok (next, batch)) :
    Reachable genesis next :=
  (exitEach_posts ended).2.2 reachable

#assert_axioms view_total safeAt_mono payout_exact_from payout_admitted_from closeSeat_inv step_inv step_posts
  seat_offer_safe_forever exit_enabled exit_after_deadline exit_by_holder exit_pays_allocation seat_conserves
  seat_debit_authorized exit_step_authorized runPlan_posts runPlan_reachable activity_end_closes_seats closeHeld_reachable


/-! ## Inhabitants and teeth

A two-party swap. Alice holds 10 X and was quoted 5 Y for them; Bob holds 7 Y.
Each signs a RANGE, not an exact Plan: Alice gives 10 X and wants at least 5 Y;
Bob gives 7 Y and wants at least 9 X. By settlement the price has moved from the
quote (Bob pays 7 Y, not 5), and the swap still settles: an exact-plan signature
over "Alice receives 5 Y" would have been refused as stale. The instance acts
only through `runPlan`, as on the native route. -/

namespace Example

def X : AssetId := 100
def Y : AssetId := 200
def alice : SubjectId := ⟨1⟩
def bob : SubjectId := ⟨2⟩
def aliceAccount : AccountId := 10
def bobAccount : AccountId := 20
def aliceSeat : AccountId := reservedBase + 30
def bobSeat : AccountId := reservedBase + 31
def package : Digest := ⟨77⟩

def genesisBook : Book where
  accounts := {aliceAccount, bobAccount}
  balances := DFinsupp.single (aliceAccount, X) 10 + DFinsupp.single (bobAccount, Y) 7
  leaseRecords := 0

def genesis : World := ⟨genesisBook, ⟨[], [], [], []⟩, []⟩

/-- The swap contract's clause admits every reallocation. -/
def swapInstance : Instance := ⟨1, package, Pred.all []⟩

/-- The invoking turn's mint ids. -/
def mintIds : Nat → InvitationId := fun index => index + 1

/-- A script entry: a signed step, or the instance's method returning a Plan. -/
inductive Entry where
  | signed (height : Nat) (subject : SubjectId) (action : Action)
  | method (height : Nat) (inst : Instance) (plan : List PlanAction)
  | ended (height : Nat) (record : Nat)

def Entry.run (world : World) : Entry → Except Refusal (World × Batch)
  | .signed height subject action => step world height (.subject subject) action
  | .method height inst plan => runPlan height inst mintIds world 0 plan
  | .ended height record => closeHeld world height record

def run : World → List Entry → Except Refusal World
  | world, [] => .ok world
  | world, entry :: rest =>
    match entry.run world with
    | .error reason => .error reason
    | .ok (next, _) => run next rest

theorem run_reachable {genesis world next : World} {script : List Entry}
    (reachable : Reachable genesis world) (ran : run world script = .ok next) : Reachable genesis next := by
  induction script generalizing world with
  | nil => simp only [run] at ran; cases ran; exact reachable
  | cons entry rest ih =>
    simp only [run] at ran
    split at ran
    · cases ran
    · rename_i middle posted hmid
      apply ih _ ran
      cases entry with
      | signed height subject action =>
        simp only [Entry.run] at hmid; exact Reachable.admit height _ _ reachable hmid
      | method height inst plan => simp only [Entry.run] at hmid; exact runPlan_reachable reachable hmid
      | ended height record => simp only [Entry.run] at hmid; exact closeHeld_reachable reachable hmid

def opening : List Entry :=
  [ .signed 1 alice (.create swapInstance),
    .method 1 swapInstance [.mint "sell" [] alice, .mint "buy" [] bob],
    .signed 2 alice (.offer 1 ⟨1, package, "sell"⟩ aliceSeat aliceAccount aliceAccount
      ⟨[(X, 10)], [(Y, 5)], .onDemand⟩ none),
    .signed 3 bob (.offer 2 ⟨1, package, "buy"⟩ bobSeat bobAccount bobAccount
      ⟨[(Y, 7)], [(X, 9)], .onDemand⟩ none) ]

def settlement : List Entry :=
  [ .method 4 swapInstance [.reallocate [⟨aliceSeat, bobSeat, X, 10⟩, ⟨bobSeat, aliceSeat, Y, 7⟩]],
    .signed 5 alice (.exit aliceSeat),
    .signed 5 bob (.exit bobSeat) ]

def balances (world : World) : List Int :=
  [world.book.balance aliceAccount X, world.book.balance aliceAccount Y,
   world.book.balance bobAccount X, world.book.balance bobAccount Y]

/-- **The swap settles after the price moved.** Alice ends with 7 Y, Bob with
10 X; both seats are closed. -/
theorem swap_settles_after_price_move :
    (run genesis (opening ++ settlement)).map balances = .ok [0, 7, 10, 0] := by decide +kernel

/-- **Offer safety refuses a raid.** Taking Alice's 10 X while giving her only
4 Y (below her `want` and below her `give`) is refused by her seat's law. -/
theorem raid_refused :
    (run genesis (opening ++ [.method 4 swapInstance
      [.reallocate [⟨aliceSeat, bobSeat, X, 10⟩, ⟨bobSeat, aliceSeat, Y, 4⟩]]])).map balances =
      .error (.offerUnsafe aliceSeat) := by decide +kernel

/-- **A contract clause cannot forbid exit.** With a clause that refuses every
reallocation, the reallocation its own method emits is refused, and Alice's
exit still pays her whole allocation back. -/
def lockedInstance : Instance := ⟨1, package, Pred.any []⟩

def lockedOpening : List Entry :=
  .signed 1 alice (.create lockedInstance) ::
    .method 1 lockedInstance [.mint "sell" [] alice, .mint "buy" [] bob] :: opening.drop 2

theorem locked_contract_refuses_reallocation :
    (run genesis (lockedOpening ++ [.method 4 lockedInstance
      [.reallocate [⟨aliceSeat, bobSeat, X, 10⟩]]])).map balances =
      .error (.contractClauseRefused 1) := by decide +kernel

theorem locked_contract_cannot_stop_exit :
    (run genesis (lockedOpening ++ [.signed 4 alice (.exit aliceSeat)])).map balances =
      .ok [10, 0, 0, 0] := by decide +kernel

/-- Only the offerer (or the contract) may exit an on-demand seat. -/
theorem stranger_cannot_exit :
    (run genesis (opening ++ [.signed 4 bob (.exit aliceSeat)])).map balances =
      .error (.exitNotAuthorized aliceSeat) := by decide +kernel

/-- An invitation is spent by its offer: offering it again is refused. -/
theorem invitation_spent_once :
    (run genesis (opening ++ [.signed 4 alice (.offer 1 ⟨1, package, "sell"⟩ (reservedBase + 32) aliceAccount
      aliceAccount ⟨[(X, 10)], [(Y, 5)], .onDemand⟩ none)])).map balances =
      .error (.invitation (.invitationMissing 1)) := by decide +kernel

/-- An invitation must assay as the offerer expects (here: the wrong role). -/
theorem assay_refused :
    (run genesis (opening.take 2 ++ [.signed 2 alice (.offer 1 ⟨1, package, "buy"⟩ aliceSeat aliceAccount
      aliceAccount ⟨[(X, 10)], [(Y, 5)], .onDemand⟩ none)])).map balances =
      .error (.invitation (.assayFailed 1)) := by decide +kernel

/-- A signer cannot name an ordinary account as a seat: the seat account is a
protected coordinate. -/
theorem unprotected_seat_refused :
    (run genesis (opening.take 2 ++ [.signed 2 alice (.offer 1 ⟨1, package, "sell"⟩ 30 aliceAccount
      aliceAccount ⟨[(X, 10)], [(Y, 5)], .onDemand⟩ none)])).map balances =
      .error (.seatNotProtected 30) := by decide +kernel

/-- **Zero `want`.** A seat that gives 10 X and wants 0 Y is satisfied by an
allocation that holds nothing: the contract may take the whole gift. -/
def giftProposal : Proposal := ⟨[(X, 10)], [(Y, 0)], .onDemand⟩

theorem zero_want_satisfied : safeAt Book.empty aliceSeat giftProposal = true := by decide +kernel

/-- The tooth: the old `n - 1` encoding computed in `Nat` reads "want 0" as
"hold at least 1", so the same empty allocation would be refused. -/
def natPredecessorAtLeast (asset : AssetId) (amount : Nat) : Pred :=
  .not (.le (assetSlot asset) ((amount - 1 : Nat) : Int))

theorem nat_predecessor_encoding_refuses_zero_want :
    Pred.eval (Pred.any [Pred.all [natPredecessorAtLeast Y 0], Pred.all [natPredecessorAtLeast X 10]])
      (view Book.empty aliceSeat giftProposal) (view Book.empty aliceSeat giftProposal) = false := by
  decide +kernel

def giftOpening : List Entry :=
  opening.take 2 ++
    [ .signed 2 alice (.offer 1 ⟨1, package, "sell"⟩ aliceSeat aliceAccount aliceAccount giftProposal none),
      .signed 3 bob (.offer 2 ⟨1, package, "buy"⟩ bobSeat bobAccount bobAccount
        ⟨[(Y, 7)], [(X, 9)], .onDemand⟩ none) ]

/-- The contract takes the whole gift (Alice wanted 0 Y), and the reallocation
is admitted. -/
theorem zero_want_gift_admitted :
    (run genesis (giftOpening ++ [.method 4 swapInstance [.reallocate [⟨aliceSeat, bobSeat, X, 10⟩]],
      .signed 5 bob (.exit bobSeat)])).map balances = .ok [0, 0, 10, 7] := by decide +kernel

/-- The tooth for the total view: a view MISSING Alice's Y slot reads her
`want` of 5 Y as met (the fail-closed `le` on an absent slot is false, so its
negation is true). `view` always carries every named slot (`view_total`). -/
theorem absent_slot_reads_as_met :
    Pred.eval (atLeast Y 5) ⟨[]⟩ ⟨[]⟩ = true := by decide +kernel

/-- **An activity holding a seat ends, and the seat is paid back.** Alice's
seat is held by the activity at record 900; its end exits the seat and pays her
10 X back; Bob, who holds no seat of it, cannot end it. -/
def heldOpening : List Entry :=
  opening.take 2 ++
    [ .signed 2 alice (.offer 1 ⟨1, package, "sell"⟩ aliceSeat aliceAccount aliceAccount
        ⟨[(X, 10)], [(Y, 5)], .onDemand⟩ (some 900)) ]

theorem activity_end_pays_held_seat :
    (run genesis (heldOpening ++ [.ended 7 900])).map balances = .ok [10, 0, 0, 7] := by decide +kernel

theorem another_activity_ends_nothing :
    (run genesis (heldOpening ++ [.ended 7 901])).map balances = .ok [0, 0, 0, 7] := by decide +kernel

theorem swap_opening_two_seats : (run genesis opening).map (fun world => world.seats.length) = .ok 2 := by
  decide +kernel

/-- The premise of `seat_offer_safe_forever` is inhabited: the swap's opening
reaches a world with two open seats. -/
theorem swap_opening_reachable : ∃ world, Reachable genesis world ∧ world.seats.length = 2 := by
  have two := swap_opening_two_seats
  cases h : run genesis opening with
  | error reason => rw [h] at two; cases two
  | ok world =>
    rw [h] at two
    exact ⟨world, run_reachable Reachable.start h, by simpa [Except.map] using two⟩

#assert_axioms swap_settles_after_price_move raid_refused locked_contract_refuses_reallocation
  locked_contract_cannot_stop_exit stranger_cannot_exit invitation_spent_once assay_refused
  unprotected_seat_refused zero_want_satisfied nat_predecessor_encoding_refuses_zero_want
  zero_want_gift_admitted absent_slot_reads_as_met activity_end_pays_held_seat another_activity_ends_nothing
  swap_opening_reachable

end Example

end Minidregg.Kernel.Seats
