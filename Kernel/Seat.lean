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
  `exit`/`terminate`/the end of the activity that holds it, which sweep EVERY
  asset the seat's account holds to its payee, deregister the account in the
  same batch and remove the seat (`seat_debit_authorized`, `exit_deregisters`);
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
always exit, and the exit moves the seat's whole holding, in every asset, to its
payee), `seat_conserves` (every admitted step conserves every asset). Teeth and
inhabitants are at the end.

**A closed seat leaves no trace in the Book.** Closing a seat is ONE batch: a
sweep of every asset the account holds (read from the Book's balance support, so
a credit in an asset the proposal does not name cannot strand value or block the
closing), then the account's deregistration (`Batch.deregistrations`, the
precedent of an ending activity's purse). Afterwards the account is no Book
account (`exit_deregisters`) and every posting naming it is refused by the Book
(`closed_seat_posting_refused`). The seat leaves `World.seats`: a world holds
exactly the OPEN seats, so a replayed exit is refused `seatMissing`; the
retired seat cell and the deregistered account are the natively visible
refusals (`Kernel.SeatStore`). The Book itself cannot refuse a RE-registration
of a closed id; that never happens because a seat account is its seat cell's
coordinate `H(offer transaction)`, the cell is retired (never reused), and an
offer onto a retired or present cell is refused (`Kernel.SeatStore.offer_refuses_taken_cell`). The native route (`Kernel.SeatReceiver`) commits
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

/-- What the offerer lets the CONTRACT see of the seat's principals (GPT-6 row G: contract input is
identity-blind by default, with a narrow opt-in per field). The default discloses nothing: a contract
method sees a seat's coordinate, role, terms, proposal and allocation only (`SeatStore.seatView`,
`seatView_identity_blind`). Disclosure is the offerer's choice at offer, signed with the proposal; the
kernel's judgments (offer safety, exit authority, payout) never read it. -/
structure Disclosure where
  offerer : Bool := false
  payee : Bool := false
  holder : Bool := false
  deriving DecidableEq, Repr

structure Proposal where
  give : List (AssetId × Nat)
  want : List (AssetId × Nat)
  exit : ExitRule
  /-- The explicit DONATION marker. A proposal that wants nothing (every `want` amount zero, or no
  `want` at all) satisfies its offer-safety law whatever the seat holds, so the contract may take
  the whole `give`: that is a gift, and an offer must SAY so. `step` refuses an unmarked gift
  (`donationUnmarked`) and refuses the marker on a proposal that does want something
  (`donationMarkedWithWant`): the marker means exactly "wants nothing". A Bool, not a sum: the
  meaning is one bit and the law (`offerSafe`) does not read it. -/
  donate : Bool
  /-- Which of the seat's principals the contract's method is shown (default: none). -/
  disclose : Disclosure := {}
  deriving DecidableEq, Repr

/-- Whether a proposal wants nothing: every `want` amount is zero (the empty list included). -/
def Proposal.wantsNothing (proposal : Proposal) : Bool :=
  proposal.want.all fun entry => entry.2 == 0

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

/-- A finite set of naturals in ascending order, by insertion sort: the same list as
`Finset.sort` (`sortedNats_eq`), but kernel-reducible on lists of any length (the library's
merge sort is well-founded and stalls `decide` past one element), so the closing's sweep can be
evaluated in the teeth below. -/
def sortedNats (s : Finset ℕ) : List ℕ :=
  Quot.liftOn s.val (fun l => l.insertionSort (· ≤ ·)) fun _ _ h =>
    ((List.perm_insertionSort _ _).trans <| h.trans (List.perm_insertionSort _ _).symm).eq_of_pairwise'
      (List.pairwise_insertionSort _ _) (List.pairwise_insertionSort _ _)

theorem sortedNats_eq (s : Finset ℕ) : sortedNats s = s.sort := by
  obtain ⟨m, _⟩ := s
  induction m using Quot.inductionOn with
  | _ l => exact (List.mergeSort_eq_insertionSort (· ≤ ·) l).symm

/-- The assets an account holds a nonzero balance of, in ascending order, read
from the Book's balance support: a closing sweeps THESE, never only the assets a
proposal names, so no credit the account ever received can block its
deregistration. -/
def heldAssets (book : Book) (account : AccountId) : List AssetId :=
  sortedNats ((book.balances.support.filter (fun coordinate => coordinate.1 = account)).image Prod.snd)

theorem heldAssets_nodup (book : Book) (account : AccountId) : (heldAssets book account).Nodup := by
  unfold heldAssets
  rw [sortedNats_eq]
  exact Finset.sort_nodup _ _

theorem mem_heldAssets (book : Book) (account : AccountId) (asset : AssetId) :
    asset ∈ heldAssets book account ↔ book.balance account asset ≠ 0 := by
  unfold heldAssets
  rw [sortedNats_eq, Finset.mem_sort, Finset.mem_image]
  constructor
  · rintro ⟨⟨named, asset'⟩, member, rfl⟩
    obtain ⟨support, same⟩ := Finset.mem_filter.mp member
    simp only at same
    subst same
    exact (DFinsupp.mem_support_toFun _ _).mp support
  · intro nonzero
    exact ⟨(account, asset), Finset.mem_filter.mpr ⟨(DFinsupp.mem_support_toFun _ _).mpr nonzero, rfl⟩, rfl⟩

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

/-- The sweep of every asset an account holds leaves it with nothing, and the
payee with exactly what it held: in the listed assets by `payout_exact_from`, in
every other asset because the account held nothing and no transfer names it. -/
theorem payout_all_exact {book : Book} {account payee : AccountId} (different : payee ≠ account)
    (nonneg : ∀ asset, 0 ≤ book.balance account asset) (asset : AssetId) :
    (applyOperations book (opsOf (payoutTransfers book account payee (heldAssets book account)))).balance
        account asset = 0 ∧
      (applyOperations book (opsOf (payoutTransfers book account payee (heldAssets book account)))).balance
        payee asset = book.balance payee asset + book.balance account asset := by
  by_cases held : asset ∈ heldAssets book account
  · exact payout_exact_from book account payee different _ book (heldAssets_nodup book account)
      (fun a _ => ⟨rfl, nonneg a⟩) asset held
  · have zero : book.balance account asset = 0 := by
      by_contra nonzero
      exact held ((mem_heldAssets book account asset).mpr nonzero)
    have away : ∀ transfer ∈ payoutTransfers book account payee (heldAssets book account),
        transfer.asset ≠ asset := by
      intro transfer member
      simp only [payoutTransfers, List.mem_map] at member
      obtain ⟨a, amem, rfl⟩ := member
      intro same
      have same' : a = asset := same
      exact held (same' ▸ amem)
    rw [ops_other_asset away account, ops_other_asset away payee, zero]
    exact ⟨rfl, by simp⟩

theorem ops_leaseRecords (transfers : List Transfer) :
    ∀ book : Book, (applyOperations book (opsOf transfers)).leaseRecords = book.leaseRecords := by
  induction transfers with
  | nil => intro book; rfl
  | cons transfer rest ih =>
    intro book
    simp only [opsOf, List.map_cons, applyOperations]
    rw [show List.map Transfer.op rest = opsOf rest from rfl, ih]
    rfl

theorem deregisterAccounts_balance (book : Book) (accounts : List AccountId) (account : AccountId)
    (asset : AssetId) : (deregisterAccounts book accounts).balance account asset = book.balance account asset := by
  unfold Book.balance
  rw [deregisterAccounts_balances]

/-- Closing one account after postings: the account set loses exactly it. -/
theorem close_accounts (book : Book) (operations : List Operation) (closed : AccountId) :
    (deregisterAccounts (applyOperations book operations) [closed]).accounts = book.accounts.erase closed := by
  change (applyOperations book operations).accounts.erase closed = book.accounts.erase closed
  rw [applyOperations_accounts_eq]

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
  deriving DecidableEq, Repr

/-- A world's seats are exactly its OPEN seats: closing one removes it. -/
structure World where
  book : Book
  registry : Registry
  seats : List Seat

/-- No lease record names the account (as holder or lessor): the fourth clause
of the Book's `DeregistrationAdmission`. An offer onto an account some lease
names is refused (`seatLeased`), so a seat's closing is never blocked by one. -/
def LeaseFree (book : Book) (account : AccountId) : Prop :=
  ∀ leaseId ∈ book.leaseRecords.support,
    ((book.leaseRecords leaseId).all fun record => !record.names account) = true

instance (book : Book) (account : AccountId) : Decidable (LeaseFree book account) := by
  unfold LeaseFree
  infer_instance

theorem LeaseFree.of_eq {book book' : Book} (same : book.leaseRecords = book'.leaseRecords) {account : AccountId}
    (free : LeaseFree book account) : LeaseFree book' account := by
  unfold LeaseFree at free ⊢
  rw [← same]
  exact free

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
  | seatMissing (account : AccountId) | seatLeased (account : AccountId)
  | donationUnmarked (account : AccountId) | donationMarkedWithWant (account : AccountId)
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

/-- A closed seat leaves the world. -/
def removeSeat (seats : List Seat) (account : AccountId) : List Seat :=
  seats.filter fun seat => decide (seat.account ≠ account)

/-- The batch that closes one seat: EVERY asset its account holds to its payee,
then the account's deregistration. -/
def closeBatch (book : Book) (seat : Seat) : Batch :=
  ⟨[], opsOf (payoutTransfers book seat.account seat.payee (heldAssets book seat.account)), [seat.account]⟩

/-- Close one open seat: sweep its account to its payee, deregister the account,
remove the seat. -/
def closeSeat (world : World) (seat : Seat) : Except Refusal (World × Batch) :=
  match admit world.book (closeBatch world.book seat) with
  | .error reason => .error reason
  | .ok book => .ok ({ world with book := book, seats := removeSeat world.seats seat.account },
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
holds it, but on a deadline seat only once the due height is reached (a holder
is not a way around the seat's own exit rule); anyone once a deadline seat's due
height is reached. The contract's clause is not an argument. -/
def exitAuthorized (height : Nat) (actor : Actor) (seat : Seat) : Bool :=
  match actor, seat.proposal.exit with
  | .subject subject, .onDemand => subject == seat.offerer
  | .inst inst, _ => inst == seat.inst
  | .activity record, .onDemand => seat.holder == some record
  | .activity record, .afterDeadline due => seat.holder == some record && decide (due ≤ height)
  | .subject _, .afterDeadline due => decide (due ≤ height)

def openSeatsOf (world : World) (inst : InstanceId) : List Seat :=
  world.seats.filter fun seat => seat.inst == inst

theorem openSeatsOf_sub (world : World) (inst : InstanceId) : (openSeatsOf world inst).Sublist world.seats :=
  List.filter_sublist

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
  seats.find? fun seat => touches transfers seat.account && !safeAt book seat.account seat.proposal

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
        else if ¬ LeaseFree world.book seatAccount then .error (.seatLeased seatAccount)
        else if proposal.wantsNothing && !proposal.donate then .error (.donationUnmarked seatAccount)
        else if proposal.donate && !proposal.wantsNothing then .error (.donationMarkedWithWant seatAccount)
        else
          match admit world.book (offerBatch funding seatAccount proposal) with
          | .error reason => .error reason
          | .ok book =>
            if safeAt book seatAccount proposal then
              .ok ({ book := book
                     registry := registry
                     seats := ⟨seatAccount, invitation.inst, subject, payee, proposal, holder⟩ :: world.seats },
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
      if !exitAuthorized height actor seat then .error (.exitNotAuthorized account)
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
      next = { world with book := next.book, seats := removeSeat world.seats seat.account } := by
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

/-- **What an admitted exit was**: of a seat in the world, by an actor the
kernel's `exitAuthorized` admits, closed by `closeSeat`. -/
theorem exit_spec {world next : World} {height : Nat} {actor : Actor} {account : AccountId} {batch : Batch}
    (admitted : step world height actor (.exit account) = .ok (next, batch)) :
    ∃ seat ∈ world.seats, seat.account = account ∧ exitAuthorized height actor seat = true ∧
      closeSeat world seat = .ok (next, batch) := by
  simp only [step] at admitted
  split at admitted
  · cases admitted
  rename_i seat found
  split at admitted
  · cases admitted
  rename_i authorized
  refine ⟨seat, List.mem_of_find?_eq_some found, by simpa using List.find?_some found, ?_, admitted⟩
  cases h : exitAuthorized height actor seat
  · simp [h] at authorized
  · rfl

/-- **The donation marker means exactly "wants nothing".** In an admitted offer, a proposal wants
nothing (every `want` amount zero) if and only if it carries the donation marker. -/
theorem offer_donation {world next : World} {height : Nat} {actor : Actor} {id : InvitationId}
    {expect : Expectation} {seatAccount funding payee : AccountId} {proposal : Proposal}
    {holder : Option Nat} {batch : Batch}
    (admitted : step world height actor (.offer id expect seatAccount funding payee proposal holder) =
      .ok (next, batch)) : proposal.wantsNothing = proposal.donate := by
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
      split at admitted
      · cases admitted
      rename_i unmarked
      split at admitted
      · cases admitted
      rename_i marked
      revert unmarked marked
      cases proposal.wantsNothing <;> cases proposal.donate <;> simp
  · cases admitted

/-- **`empty_want_requires_marker`.** An admitted offer whose proposal wants nothing carries the
donation marker: a gift is never made silently. -/
theorem empty_want_requires_marker {world next : World} {height : Nat} {actor : Actor} {id : InvitationId}
    {expect : Expectation} {seatAccount funding payee : AccountId} {proposal : Proposal}
    {holder : Option Nat} {batch : Batch}
    (admitted : step world height actor (.offer id expect seatAccount funding payee proposal holder) =
      .ok (next, batch)) (nothing : proposal.wantsNothing = true) : proposal.donate = true := by
  have same := offer_donation admitted
  rw [nothing] at same
  exact same.symm

/-- The empty `want` list is the plainest case. -/
theorem empty_want_list_requires_marker {world next : World} {height : Nat} {actor : Actor}
    {id : InvitationId} {expect : Expectation} {seatAccount funding payee : AccountId}
    {proposal : Proposal} {holder : Option Nat} {batch : Batch}
    (admitted : step world height actor (.offer id expect seatAccount funding payee proposal holder) =
      .ok (next, batch)) (empty : proposal.want = []) : proposal.donate = true :=
  empty_want_requires_marker admitted (by simp [Proposal.wantsNothing, empty])

/-- **`marked_offer_has_empty_want`.** An admitted offer that carries the donation marker wants
nothing: the marker cannot be put on an offer that asks for something. -/
theorem marked_offer_has_empty_want {world next : World} {height : Nat} {actor : Actor}
    {id : InvitationId} {expect : Expectation} {seatAccount funding payee : AccountId}
    {proposal : Proposal} {holder : Option Nat} {batch : Batch}
    (admitted : step world height actor (.offer id expect seatAccount funding payee proposal holder) =
      .ok (next, batch)) (marked : proposal.donate = true) : proposal.wantsNothing = true := by
  have same := offer_donation admitted
  rw [marked] at same
  exact same

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
    obtain ⟨seat, _, _, _, closed⟩ := exit_spec admitted
    obtain ⟨rfl, posted, _⟩ := closeSeat_spec closed
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
  safe : ∀ seat ∈ world.seats, safeAt world.book seat.account seat.proposal = true
  nonneg : ∀ seat ∈ world.seats, ∀ asset, 0 ≤ world.book.balance seat.account asset
  member : ∀ seat ∈ world.seats, seat.account ∈ world.book.accounts ∧ seat.payee ∈ world.book.accounts
  /-- A seat account is a protected coordinate; its payee is not. So no funding
  account, payee or other seat's payee is a seat account. -/
  protect : ∀ seat ∈ world.seats, reservedBase ≤ seat.account ∧ seat.payee < reservedBase
  distinct : (world.seats.map Seat.account).Nodup
  /-- No lease names a seat account: the closing's deregistration is admitted. -/
  leases : ∀ seat ∈ world.seats, LeaseFree world.book seat.account

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

theorem mem_removeSeat {seats : List Seat} {account : AccountId} {seat : Seat} :
    seat ∈ removeSeat seats account ↔ seat ∈ seats ∧ seat.account ≠ account := by
  simp [removeSeat, List.mem_filter]

theorem removeSeat_map_nodup {seats : List Seat} (distinct : (seats.map Seat.account).Nodup)
    (account : AccountId) : ((removeSeat seats account).map Seat.account).Nodup :=
  distinct.sublist ((List.filter_sublist).map _)

/-- Closing a seat sweeps its account and deregisters it. -/
theorem closeSeat_book {world next : World} {seat : Seat} {batch : Batch}
    (closed : closeSeat world seat = .ok (next, batch)) :
    next.book = deregisterAccounts (applyOperations world.book (opsOf (payoutTransfers world.book seat.account
      seat.payee (heldAssets world.book seat.account)))) [seat.account] := by
  obtain ⟨rfl, posted, _⟩ := closeSeat_spec closed
  rw [posted.2]; rfl

theorem closeSeat_seats {world next : World} {seat : Seat} {batch : Batch}
    (closed : closeSeat world seat = .ok (next, batch)) : next.seats = removeSeat world.seats seat.account := by
  obtain ⟨_, _, shape⟩ := closeSeat_spec closed
  rw [shape]

/-- **The closing is admitted by the Book's deregistration rules.** After the
sweep the account holds nothing in any asset, it is registered, protected, and no
lease names it. -/
theorem closeDeregistration {world : World} {seat : Seat} (inv : Inv world) (member : seat ∈ world.seats) :
    DeregistrationAdmission (applyOperations world.book (opsOf (payoutTransfers world.book seat.account
      seat.payee (heldAssets world.book seat.account)))) seat.account := by
  refine ⟨(inv.protect seat member).1, ?_, ?_, ?_⟩
  · rw [applyOperations_accounts_eq]; exact (inv.member seat member).1
  · intro coordinate hmem same
    obtain ⟨named, asset⟩ := coordinate
    simp only at same
    subst same
    have nonzero := (DFinsupp.mem_support_toFun _ _).mp hmem
    exact nonzero (payout_all_exact (inv.payeeOther member) (inv.nonneg seat member) asset).1
  · have free : LeaseFree world.book seat.account := inv.leases seat member
    exact LeaseFree.of_eq (book' := applyOperations world.book (opsOf (payoutTransfers world.book seat.account
      seat.payee (heldAssets world.book seat.account)))) (ops_leaseRecords _ _).symm free

/-- Closing one seat of the world preserves the invariant. -/
theorem closeSeat_inv {world next : World} {seat : Seat} {batch : Batch} (inv : Inv world)
    (member : seat ∈ world.seats) (closed : closeSeat world seat = .ok (next, batch)) : Inv next := by
  have book := closeSeat_book closed
  have seatsEq := closeSeat_seats closed
  have leasesEq : next.book.leaseRecords = world.book.leaseRecords := by
    rw [book, deregisterAccounts_leaseRecords, ops_leaseRecords]
  have accounts : next.book.accounts = world.book.accounts.erase seat.account := by
    rw [book]; exact close_accounts _ _ _
  have above := (inv.protect seat member).1
  constructor
  · intro s hs
    rw [seatsEq] at hs
    obtain ⟨hmem, different⟩ := mem_removeSeat.mp hs
    rw [book]
    exact safeAt_mono (fun asset _ => by
        rw [deregisterAccounts_balance]
        exact payout_credit_only _ _ _ _ _ _ different asset) (inv.safe s hmem)
  · intro s hs asset
    rw [seatsEq] at hs
    obtain ⟨hmem, different⟩ := mem_removeSeat.mp hs
    rw [book, deregisterAccounts_balance]
    exact le_trans (inv.nonneg s hmem asset) (payout_credit_only _ _ _ _ _ _ different asset)
  · intro s hs
    rw [seatsEq] at hs
    obtain ⟨hmem, different⟩ := mem_removeSeat.mp hs
    rw [accounts]
    refine ⟨Finset.mem_erase.mpr ⟨different, (inv.member s hmem).1⟩,
      Finset.mem_erase.mpr ⟨?_, (inv.member s hmem).2⟩⟩
    exact Nat.ne_of_lt (lt_of_lt_of_le (inv.protect s hmem).2 above)
  · intro s hs
    rw [seatsEq] at hs
    exact inv.protect s (mem_removeSeat.mp hs).1
  · rw [seatsEq]; exact removeSeat_map_nodup inv.distinct _
  · intro s hs
    rw [seatsEq] at hs
    exact LeaseFree.of_eq leasesEq.symm (inv.leases s (mem_removeSeat.mp hs).1)

theorem closeAll_inv {world next : World} {seats : List Seat} {batch : Batch} (inv : Inv world)
    (member : ∀ s ∈ seats, s ∈ world.seats) (nodup : (seats.map Seat.account).Nodup)
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
        have nodup' : (seat.account :: rest.map Seat.account).Nodup := nodup
        have middleInv := closeSeat_inv inv (member seat (by simp)) hfirst
        refine ih middleInv (fun r hr => ?_) (List.nodup_cons.mp nodup').2 hlater
        rw [closeSeat_seats hfirst]
        exact mem_removeSeat.mpr ⟨member r (by simp [hr]),
          fun same => (List.nodup_cons.mp nodup').1 (List.mem_map.mpr ⟨r, hr, same⟩)⟩

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
        rw [closeSeat_book hfirst, deregisterAccounts_balance]
        exact payout_credit_only _ _ _ _ _ _ (Ne.symm (away seat (by simp))) asset

/-- Every closed seat's account is among the closing batch's deregistrations. -/
theorem closeAll_deregistrations {world next : World} {seats : List Seat} {batch : Batch}
    (closed : closeAll world seats = .ok (next, batch)) :
    ∀ seat ∈ seats, seat.account ∈ batch.deregistrations := by
  induction seats generalizing world next batch with
  | nil => intro seat m; simp at m
  | cons seat rest ih =>
    simp only [closeAll] at closed
    split at closed
    · cases closed
    · rename_i middle first hfirst
      split at closed
      · cases closed
      · rename_i later hlater
        cases closed
        obtain ⟨rfl, _, _⟩ := closeSeat_spec hfirst
        intro s hs
        rcases List.mem_cons.mp hs with rfl | m
        · simp [seqBatch, closeBatch]
        · simp only [seqBatch, List.mem_append]
          exact Or.inr (ih hlater s m)

/-- **`closeAll` deregisters every seat it closes**: afterwards no closed seat's
account is a Book account. -/
theorem closeAll_deregisters {world next : World} {seats : List Seat} {batch : Batch}
    (closed : closeAll world seats = .ok (next, batch)) :
    ∀ seat ∈ seats, seat.account ∉ next.book.accounts := by
  intro seat hseat
  obtain ⟨posted, _⟩ := closeAll_posts closed
  have gone := Batch.apply_deregistered batch world.book seat.account (closeAll_deregistrations closed seat hseat)
  rw [← posted.2] at gone
  exact gone

/-! ## The offer and reallocation cases -/

theorem offer_inv {world : World} (inv : Inv world) {seatAccount funding payee : AccountId}
    {subject : SubjectId} {proposal : Proposal} {book : Book} {inst : InstanceId} {registry : Registry}
    {holder : Option Nat}
    (protectedSeat : ¬ seatAccount < reservedBase) (fundingOrdinary : ¬ reservedBase ≤ funding)
    (payeeOrdinary : ¬ reservedBase ≤ payee) (payeeIn : payee ∈ world.book.accounts)
    (leaseFree : LeaseFree world.book seatAccount)
    (admitted : admit world.book (offerBatch funding seatAccount proposal) = .ok book)
    (safeNew : safeAt book seatAccount proposal = true) :
    Inv { book := book
          registry := registry
          seats := ⟨seatAccount, inst, subject, payee, proposal, holder⟩ :: world.seats } := by
  obtain ⟨⟨⟨registered, _⟩, _⟩, rfl⟩ := admit_posts admitted
  have fresh := registered.1
  have accountsEq : (Batch.apply (offerBatch funding seatAccount proposal) world.book).accounts =
      insert seatAccount world.book.accounts := by
    unfold Batch.apply
    rw [show (offerBatch funding seatAccount proposal).deregistrations = [] from rfl, deregisterAccounts_nil,
      applyOperations_accounts_eq]; rfl
  have fundingOther : funding ≠ seatAccount := ordinary_ne_protected fundingOrdinary protectedSeat
  have leasesEq : (Batch.apply (offerBatch funding seatAccount proposal) world.book).leaseRecords =
      world.book.leaseRecords := by
    show (applyOperations (registerAccounts world.book [seatAccount])
      (opsOf (giveTransfers funding seatAccount proposal))).leaseRecords = _
    rw [ops_leaseRecords]
    rfl
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
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | old
    · exact safeNew
    · show safeAt (Batch.apply (offerBatch funding seatAccount proposal) world.book) s.account s.proposal = true
      rw [safeAt_congr (fun asset _ => untouched s old asset)]
      exact inv.safe s old
  · intro s hs asset
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
      rw [untouched s old]; exact inv.nonneg s old asset
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
  · show ((⟨seatAccount, inst, subject, payee, proposal, holder⟩ :: world.seats).map Seat.account).Nodup
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun mem => ?_, inv.distinct⟩
    obtain ⟨s, hs, eq⟩ := List.mem_map.mp mem
    simp only at eq
    exact fresh (eq ▸ (inv.member s hs).1)
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | old
    · exact LeaseFree.of_eq leasesEq.symm leaseFree
    · exact LeaseFree.of_eq leasesEq.symm (inv.leases s old)

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
  · intro s hs
    by_cases touched : touches transfers s.account = true
    · have := noneUnsafe s hs
      simpa [touched] using this
    · have away : ∀ t ∈ transfers, t.source ≠ s.account ∧ t.destination ≠ s.account := by
        intro t ht
        simp only [touches, List.any_eq_true, Bool.or_eq_true, beq_iff_eq, not_exists, not_and,
          not_or] at touched
        exact touched t ht
      show safeAt (applyOperations world.book (opsOf transfers)) s.account s.proposal = true
      rw [safeAt_congr (fun asset _ => ops_untouched away asset)]
      exact inv.safe s hs
  · intro s hs asset
    exact ops_nonneg ops (inv.nonneg s hs) asset
  · intro s hs
    show s.account ∈ (applyOperations world.book (opsOf transfers)).accounts ∧
      s.payee ∈ (applyOperations world.book (opsOf transfers)).accounts
    rw [applyOperations_accounts_eq]; exact inv.member s hs
  · exact inv.protect
  · exact inv.distinct
  · intro s hs
    exact LeaseFree.of_eq (ops_leaseRecords _ _).symm (inv.leases s hs)

/-! ## T3 (a): every open seat of every reachable world satisfies its law -/

theorem step_inv {world next : World} {height : Nat} {actor : Actor} {action : Action} {batch : Batch}
    (inv : Inv world) (admitted : step world height actor action = .ok (next, batch)) : Inv next := by
  cases action with
  | create inst =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨inv.safe, inv.nonneg, inv.member, inv.protect, inv.distinct, inv.leases⟩
    · cases admitted
  | mint invitation =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨inv.safe, inv.nonneg, inv.member, inv.protect, inv.distinct, inv.leases⟩
    · cases admitted
  | handOver id recipient =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨inv.safe, inv.nonneg, inv.member, inv.protect, inv.distinct, inv.leases⟩
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
        rename_i leaseFree
        split at admitted
        · cases admitted
        split at admitted
        · cases admitted
        split at admitted
        · cases admitted
        · rename_i book hbook
          split at admitted
          · rename_i safeNew
            cases admitted
            exact offer_inv inv protectedSeat fundingOrdinary payeeOrdinary (not_not.mp payeeIn)
              (not_not.mp leaseFree) hbook safeNew
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
    obtain ⟨seat, member, _, _, closed⟩ := exit_spec admitted
    exact closeSeat_inv inv member closed
  | terminate instId =>
    simp only [step] at admitted
    split at admitted
    · split at admitted
      · cases admitted
      split at admitted
      · cases admitted
      · rename_i closed hclosed
        cases admitted
        have := closeAll_inv inv (fun s hs => (openSeatsOf_sub world instId).subset hs)
          (inv.distinct.sublist ((openSeatsOf_sub world instId).map _)) hclosed
        exact ⟨this.safe, this.nonneg, this.member, this.protect, this.distinct, this.leases⟩
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
    ∀ seat ∈ world.seats, safeAt world.book seat.account seat.proposal = true :=
  (reachable_inv empty reachable).safe

/-! ## T3 (b): exit is ENABLED for its named actor, and pays the whole holding

These are enabling theorems, not progress guarantees: each says the exit step is admitted
when its named actor submits it (the offerer of an on-demand seat; anyone at or after a
deadline; the holding activity's end). Nothing in the kernel submits a turn on its own, so a
seat leaves only when such an actor acts (GPT-6 row G: liveness claims name their actors). -/

theorem closeBatch_admitted {world : World} {seat : Seat} (inv : Inv world) (member : seat ∈ world.seats) :
    (closeBatch world.book seat).Admission world.book :=
  ⟨trivial, payout_admitted_from world.book seat.account seat.payee (inv.payeeOther member) _ world.book
    (heldAssets_nodup _ _) (inv.member seat member).1 (inv.member seat member).2
    (fun asset _ => ⟨rfl, inv.nonneg seat member asset⟩), closeDeregistration inv member, trivial⟩

theorem exit_admitted {world : World} {height : Nat} {actor : Actor} {seat : Seat} (inv : Inv world)
    (member : seat ∈ world.seats) (authorized : exitAuthorized height actor seat = true) :
    step world height actor (.exit seat.account) =
      .ok ({ world with
        book := (closeBatch world.book seat).apply world.book
        seats := removeSeat world.seats seat.account }, closeBatch world.book seat) := by
  simp only [step, seat?_eq inv.distinct member, authorized, Bool.not_true, if_false,
    Bool.false_eq_true]
  unfold closeSeat admit
  rw [if_pos (closeBatch_admitted inv member)]

/-- **T3 (b), the offerer's right.** An on-demand seat's offerer can exit at any
height, whatever any contract clause says: the step does not consult one. -/
theorem exit_enabled {world : World} {seat : Seat} (inv : Inv world) (member : seat ∈ world.seats)
    (onDemand : seat.proposal.exit = .onDemand) (height : Nat) :
    ∃ next, step world height (.subject seat.offerer) (.exit seat.account) = .ok next :=
  ⟨_, exit_admitted inv member (by simp [exitAuthorized, onDemand])⟩

/-- A seat with a deadline can be exited by anyone once the deadline is reached. -/
theorem exit_after_deadline {world : World} {seat : Seat} (inv : Inv world) (member : seat ∈ world.seats)
    {due height : Nat} (deadline : seat.proposal.exit = .afterDeadline due)
    (reached : due ≤ height) (anyone : SubjectId) :
    ∃ next, step world height (.subject anyone) (.exit seat.account) = .ok next :=
  ⟨_, exit_admitted inv member (by simp [exitAuthorized, deadline, reached])⟩

/-- The activity that holds a seat can end it: at any height on an on-demand seat, and on a
deadline seat once the due height is reached (and not before: `holder_respects_deadline`). -/
theorem exit_by_holder {world : World} {seat : Seat} (inv : Inv world) (member : seat ∈ world.seats)
    {record : Nat} (held : seat.holder = some record) (height : Nat)
    (due : ∀ d, seat.proposal.exit = .afterDeadline d → d ≤ height) :
    ∃ next, step world height (.activity record) (.exit seat.account) = .ok next :=
  ⟨_, exit_admitted inv member (by
    unfold exitAuthorized
    cases rule : seat.proposal.exit with
    | onDemand => simp [held]
    | afterDeadline d => simp [held, due d rule])⟩

/-- **`holder_respects_deadline`.** An admitted exit by the end of an activity on a deadline
seat implies the due height is reached: naming one's own activity as holder is no way to pull a
deadline seat early. -/
theorem holder_respects_deadline {world next : World} {height record : Nat} {account : AccountId}
    {batch : Batch} (admitted : step world height (.activity record) (.exit account) = .ok (next, batch)) :
    ∃ seat ∈ world.seats, seat.account = account ∧ seat.holder = some record ∧
      ∀ due, seat.proposal.exit = .afterDeadline due → due ≤ height := by
  obtain ⟨seat, member, same, authorized, _⟩ := exit_spec admitted
  refine ⟨seat, member, same, ?_, ?_⟩
  · revert authorized
    unfold exitAuthorized
    cases seat.proposal.exit <;> simp <;> tauto
  · intro due rule
    revert authorized
    simp [exitAuthorized, rule]

theorem closeBatch_balance (book : Book) (seat : Seat) (account : AccountId) (asset : AssetId) :
    ((closeBatch book seat).apply book).balance account asset =
      (applyOperations book (opsOf (payoutTransfers book seat.account seat.payee
        (heldAssets book seat.account)))).balance account asset :=
  deregisterAccounts_balance _ _ _ _

/-- **T3 (b), what an exit pays.** The seat ends at zero in EVERY asset (not only
those its proposal names), and its payee gains exactly the seat's balance in
every asset. -/
theorem exit_pays_allocation {world next : World} {height : Nat} {actor : Actor} {seat : Seat}
    {batch : Batch} (inv : Inv world) (member : seat ∈ world.seats)
    (admitted : step world height actor (.exit seat.account) = .ok (next, batch)) :
    ∀ asset, next.book.balance seat.account asset = 0 ∧
      next.book.balance seat.payee asset = world.book.balance seat.payee asset + world.book.balance seat.account asset := by
  have authorized : exitAuthorized height actor seat = true := by
    simp only [step, seat?_eq inv.distinct member, Bool.not_true, if_false,
      Bool.false_eq_true] at admitted
    split at admitted
    · cases admitted
    · rename_i h; simpa using h
  rw [exit_admitted inv member authorized] at admitted
  cases admitted
  intro asset
  have exact_ := payout_all_exact (inv.payeeOther member) (inv.nonneg seat member) asset
  rw [← closeBatch_balance world.book seat seat.account asset,
    ← closeBatch_balance world.book seat seat.payee asset] at exact_
  exact exact_

/-- **Who may exit.** An admitted exit was of a seat of the world, by an actor the
kernel's `exitAuthorized` admits: its offerer (on demand), its contract, the
activity that holds it, or anyone at or after its due height. The instance's
clause is not an argument of `exitAuthorized`: no contract can forbid an exit. -/
theorem exit_step_authorized {world next : World} {height : Nat} {actor : Actor} {account : AccountId}
    {batch : Batch} (admitted : step world height actor (.exit account) = .ok (next, batch)) :
    ∃ seat ∈ world.seats, seat.account = account ∧ exitAuthorized height actor seat = true := by
  obtain ⟨seat, member, same, authorized, _⟩ := exit_spec admitted
  exact ⟨seat, member, same, authorized⟩

/-! ## A closed seat leaves no trace in the Book -/

/-- **`exit_deregisters`.** After an admitted exit the seat's account is no Book
account. -/
theorem exit_deregisters {world next : World} {height : Nat} {actor : Actor} {account : AccountId}
    {batch : Batch} (admitted : step world height actor (.exit account) = .ok (next, batch)) :
    account ∉ next.book.accounts := by
  obtain ⟨seat, _, same, _, closed⟩ := exit_spec admitted
  obtain ⟨rfl, posted, _⟩ := closeSeat_spec closed
  have gone := Batch.apply_deregistered (closeBatch world.book seat) world.book seat.account
    (by simp [closeBatch])
  rw [← posted.2, same] at gone
  exact gone

/-- **An exit removes the seat from the world.** -/
theorem exit_removes_seat {world next : World} {height : Nat} {actor : Actor} {account : AccountId}
    {batch : Batch} (admitted : step world height actor (.exit account) = .ok (next, batch)) :
    ∀ seat ∈ next.seats, seat.account ≠ account := by
  obtain ⟨seat, _, same, _, closed⟩ := exit_spec admitted
  intro s hs
  rw [closeSeat_seats closed] at hs
  rw [← same]
  exact (mem_removeSeat.mp hs).2

/-- **Terminating an instance deregisters every seat it closes.** -/
theorem terminate_deregisters {world next : World} {height : Nat} {actor : Actor} {inst : InstanceId}
    {batch : Batch} (admitted : step world height actor (.terminate inst) = .ok (next, batch)) :
    ∀ seat ∈ openSeatsOf world inst, seat.account ∉ next.book.accounts := by
  simp only [step] at admitted
  split at admitted
  · split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    · rename_i closed hclosed
      cases admitted
      have gone := closeAll_deregisters hclosed
      exact gone
  · cases admitted

theorem registerAccounts_not_mem (account : AccountId) :
    ∀ (book : Book) (accounts : List AccountId), account ∉ book.accounts → account ∉ accounts →
      account ∉ (registerAccounts book accounts).accounts
  | _, [], absent, _ => absent
  | book, first :: rest, absent, fresh => by
    apply registerAccounts_not_mem account (book.registerAccount first) rest
    · show account ∉ insert first book.accounts
      rw [Finset.mem_insert]
      rintro (same | present)
      · exact fresh (by simp [same])
      · exact absent present
    · exact fun member => fresh (List.mem_cons_of_mem _ member)

theorem absent_not_named {account : AccountId} :
    ∀ {book : Book} {operations : List Operation}, account ∉ book.accounts →
      OperationsAdmitted book operations →
      ∀ operation ∈ operations, operation.posting.source ≠ account ∧ operation.posting.destination ≠ account
  | _, [], _, _, operation, member => by simp at member
  | book, first :: rest, absent, ⟨admitted, later⟩, operation, member => by
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨fun h => absent (h ▸ admitted.sourcePresent), fun h => absent (h ▸ admitted.destinationPresent)⟩
    · exact absent_not_named (by rw [Operation.apply_accounts]; exact absent) later operation member

/-- **`closed_seat_posting_refused`.** After an admitted exit, no later batch that
posts to or from the closed seat's account is admitted by the Book, unless it
registers the account afresh (which the seat kernel never does: a seat account is
its retired cell's coordinate, `Kernel.SeatStore.offer_refuses_taken_cell`). -/
theorem closed_seat_posting_refused {world next : World} {height : Nat} {actor : Actor}
    {account : AccountId} {batch : Batch}
    (admitted : step world height actor (.exit account) = .ok (next, batch)) (later : Batch)
    (fresh : account ∉ later.registrations)
    (names : ∃ operation ∈ later.operations,
      operation.posting.source = account ∨ operation.posting.destination = account) :
    ¬ later.Admission next.book := by
  rintro ⟨_, ops, _⟩
  obtain ⟨operation, member, same⟩ := names
  have absent : account ∉ (registerAccounts next.book later.registrations).accounts :=
    registerAccounts_not_mem account next.book later.registrations (exit_deregisters admitted) fresh
  have unnamed := absent_not_named absent ops operation member
  rcases same with h | h
  · exact unnamed.1 h
  · exact unnamed.2 h

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
            simpa using this
          have same : s = seat := List.inj_on_of_nodup_map inv.distinct sseat member (saccount.trans tsrc)
          subst same
          exact Or.inl ⟨by rw [sinst], transfers, by rw [sinst]⟩
    · cases admitted
  | exit account =>
    obtain ⟨closing, _, closingAccount, _, closed⟩ := exit_spec admitted
    have book := closeSeat_book closed
    by_cases same : seat.account = account
    · exact Or.inr (Or.inl (by rw [same]))
    · exfalso
      have credit : world.book.balance seat.account asset ≤ next.book.balance seat.account asset := by
        rw [book, deregisterAccounts_balance]
        exact payout_credit_only _ _ _ _ _ _ (by rw [closingAccount]; exact same) asset
      exact absurd credit (not_le.mpr debited)
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
              simpa using this
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

/-- The open seats an activity holds that its end may exit at `height`: a held deadline
seat before its due height stays open (`holder_respects_deadline`). -/
def heldOpen (world : World) (height record : Nat) : List Seat :=
  world.seats.filter fun seat => seat.holder == some record && exitAuthorized height (.activity record) seat

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
  exitEach height record world ((heldOpen world height record).map Seat.account)

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

/-- An admitted exit removes the seat from the world. -/
theorem step_exit_closes {world next : World} {height : Nat} {actor : Actor} {account : AccountId}
    {batch : Batch} (admitted : step world height actor (.exit account) = .ok (next, batch)) :
    next.seats = removeSeat world.seats account := by
  obtain ⟨seat, _, same, _, closed⟩ := exit_spec admitted
  rw [closeSeat_seats closed, same]

/-- An admitted exit's batch deregisters the exited account. -/
theorem step_exit_deregistrations {world next : World} {height : Nat} {actor : Actor} {account : AccountId}
    {batch : Batch} (admitted : step world height actor (.exit account) = .ok (next, batch)) :
    account ∈ batch.deregistrations := by
  obtain ⟨seat, _, same, _, closed⟩ := exit_spec admitted
  obtain ⟨rfl, _, _⟩ := closeSeat_spec closed
  rw [← same]
  simp [closeBatch]

theorem exitEach_sub {height record : Nat} :
    ∀ {world next : World} {accounts : List AccountId} {batch : Batch},
      exitEach height record world accounts = .ok (next, batch) → ∀ seat ∈ next.seats, seat ∈ world.seats
  | world, next, [], batch, ran => by
    simp only [exitEach] at ran; cases ran; exact fun _ h => h
  | world, next, account :: rest, batch, ran => by
    simp only [exitEach] at ran
    split at ran
    · cases ran
    · rename_i middle posted hstep
      split at ran
      · cases ran
      · rename_i later hrest
        cases ran
        intro seat member
        have inMiddle := exitEach_sub hrest seat member
        rw [step_exit_closes hstep] at inMiddle
        exact (mem_removeSeat.mp inMiddle).1

theorem exitEach_closes {height record : Nat} :
    ∀ {world next : World} {accounts : List AccountId} {batch : Batch},
      exitEach height record world accounts = .ok (next, batch) →
      ∀ account ∈ accounts, ∀ seat ∈ next.seats, seat.account ≠ account
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
        · intro seat inNext
          have inMiddle := exitEach_sub hrest seat inNext
          rw [step_exit_closes hstep] at inMiddle
          exact (mem_removeSeat.mp inMiddle).2
        · exact exitEach_closes hrest account member

/-- Every exited account is among the end's deregistrations. -/
theorem exitEach_deregistrations {height record : Nat} :
    ∀ {world next : World} {accounts : List AccountId} {batch : Batch},
      exitEach height record world accounts = .ok (next, batch) →
      ∀ account ∈ accounts, account ∈ batch.deregistrations
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
        simp only [seqBatch, List.mem_append]
        rcases List.mem_cons.mp named with rfl | member
        · exact Or.inl (step_exit_deregistrations hstep)
        · exact Or.inr (exitEach_deregistrations hrest account member)

/-- **The end of an activity closes every seat it holds.** If the ending turn's
`closeHeld` is admitted, every seat that was held by the activity is gone from
the result, its account is no Book account, and the whole is one admitted batch
that conserves every asset. (Each exit sweeps its payee's whole holding:
`exit_pays_allocation`; and `exit_by_holder` makes every such exit admissible
from any world satisfying `Inv`.) -/
theorem activity_end_closes_seats {world next : World} {height record : Nat} {batch : Batch}
    (ended : closeHeld world height record = .ok (next, batch)) :
    (∀ seat ∈ heldOpen world height record, ∀ after ∈ next.seats, after.account ≠ seat.account) ∧
      (∀ seat ∈ heldOpen world height record, seat.account ∉ next.book.accounts) ∧
      Posts world.book batch next.book ∧ ∀ asset, next.book.totalAsset asset = world.book.totalAsset asset := by
  obtain ⟨posted, _, _⟩ := exitEach_posts ended
  refine ⟨fun seat member after amember =>
    exitEach_closes ended seat.account (List.mem_map.mpr ⟨seat, member, rfl⟩) after amember, ?_, posted,
    posted.conserves⟩
  intro seat member
  have gone := Batch.apply_deregistered batch world.book seat.account
    (exitEach_deregistrations ended seat.account (List.mem_map.mpr ⟨seat, member, rfl⟩))
  rw [← posted.2] at gone
  exact gone

theorem closeHeld_reachable {genesis world next : World} {height record : Nat} {batch : Batch}
    (reachable : Reachable genesis world) (ended : closeHeld world height record = .ok (next, batch)) :
    Reachable genesis next :=
  (exitEach_posts ended).2.2 reachable

#assert_axioms view_total safeAt_mono payout_exact_from payout_admitted_from closeSeat_inv step_inv step_posts
  seat_offer_safe_forever exit_enabled exit_after_deadline exit_by_holder exit_pays_allocation seat_conserves
  seat_debit_authorized exit_step_authorized runPlan_posts runPlan_reachable activity_end_closes_seats closeHeld_reachable
  mem_heldAssets payout_all_exact closeDeregistration closeAll_deregisters exit_deregisters exit_removes_seat
  terminate_deregisters closed_seat_posting_refused exitEach_deregistrations holder_respects_deadline exit_by_holder
  offer_donation empty_want_requires_marker empty_want_list_requires_marker marked_offer_has_empty_want


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
      ⟨[(X, 10)], [(Y, 5)], .onDemand, false, {}⟩ none),
    .signed 3 bob (.offer 2 ⟨1, package, "buy"⟩ bobSeat bobAccount bobAccount
      ⟨[(Y, 7)], [(X, 9)], .onDemand, false, {}⟩ none) ]

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
      aliceAccount ⟨[(X, 10)], [(Y, 5)], .onDemand, false, {}⟩ none)])).map balances =
      .error (.invitation (.invitationMissing 1)) := by decide +kernel

/-- An invitation must assay as the offerer expects (here: the wrong role). -/
theorem assay_refused :
    (run genesis (opening.take 2 ++ [.signed 2 alice (.offer 1 ⟨1, package, "buy"⟩ aliceSeat aliceAccount
      aliceAccount ⟨[(X, 10)], [(Y, 5)], .onDemand, false, {}⟩ none)])).map balances =
      .error (.invitation (.assayFailed 1)) := by decide +kernel

/-- A signer cannot name an ordinary account as a seat: the seat account is a
protected coordinate. -/
theorem unprotected_seat_refused :
    (run genesis (opening.take 2 ++ [.signed 2 alice (.offer 1 ⟨1, package, "sell"⟩ 30 aliceAccount
      aliceAccount ⟨[(X, 10)], [(Y, 5)], .onDemand, false, {}⟩ none)])).map balances =
      .error (.seatNotProtected 30) := by decide +kernel

/-- **Zero `want`.** A seat that gives 10 X and wants 0 Y is satisfied by an
allocation that holds nothing: the contract may take the whole gift. -/
def giftProposal : Proposal := ⟨[(X, 10)], [(Y, 0)], .onDemand, true, {}⟩

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
        ⟨[(Y, 7)], [(X, 9)], .onDemand, false, {}⟩ none) ]

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
        ⟨[(X, 10)], [(Y, 5)], .onDemand, false, {}⟩ (some 900)) ]

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

/-- **A holder is no way around a deadline.** Alice's seat has exit rule `afterDeadline 10` and
names the activity at record 900 as its holder. That activity ending at height 7 leaves the seat
open with its whole allocation (and the activity's end is still admitted); once the due height is
reached the activity's end pays it, and before that anyone may exit it only from height 10. -/
def deadlineHeldOpening : List Entry :=
  opening.take 2 ++
    [ .signed 2 alice (.offer 1 ⟨1, package, "sell"⟩ aliceSeat aliceAccount aliceAccount
        ⟨[(X, 10)], [(Y, 5)], .afterDeadline 10, false, {}⟩ (some 900)) ]

theorem activity_end_leaves_deadline_seat_open :
    (run genesis (deadlineHeldOpening ++ [.ended 7 900])).map
      (fun world => (world.book.balance aliceSeat X, world.seats.length)) = .ok (10, 1) := by decide +kernel

theorem activity_end_pays_deadline_seat_after_due :
    (run genesis (deadlineHeldOpening ++ [.ended 10 900])).map balances = .ok [10, 0, 0, 7] := by decide +kernel

theorem anyone_exits_deadline_seat_after_due :
    (run genesis (deadlineHeldOpening ++ [.ended 7 900, .signed 10 bob (.exit aliceSeat)])).map balances =
      .ok [10, 0, 0, 7] := by decide +kernel

theorem stranger_cannot_exit_deadline_seat_early :
    (run genesis (deadlineHeldOpening ++ [.ended 7 900, .signed 9 bob (.exit aliceSeat)])).map balances =
      .error (.exitNotAuthorized aliceSeat) := by decide +kernel

/-- **An unmarked gift is refused by name.** An offer that wants nothing (here a zero amount, or no
`want` at all) and lacks the donation marker is refused, and a marker on an offer that asks for
something is refused too. -/
theorem unmarked_gift_refused :
    (run genesis (opening.take 2 ++ [.signed 2 alice (.offer 1 ⟨1, package, "sell"⟩ aliceSeat aliceAccount
      aliceAccount ⟨[(X, 10)], [(Y, 0)], .onDemand, false, {}⟩ none)])).map balances =
      .error (.donationUnmarked aliceSeat) := by decide +kernel

theorem empty_want_unmarked_refused :
    (run genesis (opening.take 2 ++ [.signed 2 alice (.offer 1 ⟨1, package, "sell"⟩ aliceSeat aliceAccount
      aliceAccount ⟨[(X, 10)], [], .onDemand, false, {}⟩ none)])).map balances =
      .error (.donationUnmarked aliceSeat) := by decide +kernel

theorem marked_donation_with_want_refused :
    (run genesis (opening.take 2 ++ [.signed 2 alice (.offer 1 ⟨1, package, "sell"⟩ aliceSeat aliceAccount
      aliceAccount ⟨[(X, 10)], [(Y, 5)], .onDemand, true, {}⟩ none)])).map balances =
      .error (.donationMarkedWithWant aliceSeat) := by decide +kernel

theorem marked_empty_want_accepted :
    (run genesis (opening.take 2 ++ [.signed 2 alice (.offer 1 ⟨1, package, "sell"⟩ aliceSeat aliceAccount
      aliceAccount ⟨[(X, 10)], [], .onDemand, true, {}⟩ none)])).map balances = .ok [0, 0, 0, 7] := by
  decide +kernel

/-- **An exit leaves no account behind.** After Alice exits, her seat is no Book
account and no seat of the world; Bob's seat is untouched. -/
theorem exit_deregisters_example :
    (run genesis (opening ++ [.signed 4 alice (.exit aliceSeat)])).map
      (fun world => (decide (aliceSeat ∈ world.book.accounts), decide (bobSeat ∈ world.book.accounts),
        world.seats.length)) = .ok (false, true, 1) := by decide +kernel

/-- A replayed exit is refused by name: the seat is gone from the world. -/
theorem replayed_exit_refused :
    (run genesis (opening ++ [.signed 4 alice (.exit aliceSeat), .signed 5 alice (.exit aliceSeat)])).map
      balances = .error (.seatMissing aliceSeat) := by decide +kernel

/-- Posting to the closed seat's account is refused by the Book. -/
theorem closed_seat_refuses_top_up :
    (run genesis (opening ++ [.signed 4 alice (.exit aliceSeat)])).map
      (fun world => decide (Batch.Admission world.book ⟨[], [.transfer aliceAccount aliceSeat X 0], []⟩)) =
      .ok false := by decide +kernel

/-- **The sweep takes every asset the account holds.** A credit in an asset the
seat's proposal does not name (here 5 of Z, posted outside the seat kernel) is
swept to the payee, and the account still closes: sweeping only the proposal's
assets would leave a balance and the Book would refuse the deregistration. -/
def Z : AssetId := 300

def strayGenesis : World :=
  { genesis with book := { genesisBook with
      balances := genesisBook.balances + DFinsupp.single (aliceAccount, Z) 5 } }

def credited (world : World) : World :=
  { world with book := (Operation.transfer aliceAccount aliceSeat Z 5).apply world.book }

theorem exit_sweeps_unnamed_asset :
    ((run strayGenesis opening).bind fun world => run (credited world) [.signed 4 alice (.exit aliceSeat)]).map
      (fun world => (world.book.balance aliceAccount Z, decide (aliceSeat ∈ world.book.accounts))) =
      .ok (5, false) := by decide +kernel

#assert_axioms swap_settles_after_price_move raid_refused locked_contract_refuses_reallocation
  locked_contract_cannot_stop_exit stranger_cannot_exit invitation_spent_once assay_refused
  unprotected_seat_refused zero_want_satisfied nat_predecessor_encoding_refuses_zero_want
  zero_want_gift_admitted absent_slot_reads_as_met activity_end_pays_held_seat another_activity_ends_nothing
  swap_opening_reachable exit_deregisters_example replayed_exit_refused closed_seat_refuses_top_up
  exit_sweeps_unnamed_asset activity_end_leaves_deadline_seat_open activity_end_pays_deadline_seat_after_due
  anyone_exits_deadline_seat_after_due stranger_cannot_exit_deadline_seat_early unmarked_gift_refused
  empty_want_unmarked_refused marked_donation_with_want_refused marked_empty_want_accepted

end Example

end Minidregg.Kernel.Seats
