/- Seats: offer safety as a law judged on every reallocation, over the Book.

An `offer` presents an invitation (`Kernel.Invitation`) and a proposal
`{give, want, exit}`. The kernel spends the invitation, registers a fresh Book
account for the seat, posts `give` from the offerer's funding account into it,
and installs the seat. From then on:

* the seat's balances are judged by its law `offerSafe proposal`, a `Pred`
  (`Pred.Core`) over a TOTAL view of the seat's Book balances: every asset the
  proposal names has a slot, so the fail-closed reading of an absent slot can
  never be what the law sees (`view_total`);
* a seat is debited only by (a) a `reallocate` turn OF its own contract
  instance, after which every seat the reallocation touched must satisfy its law,
  or (b) `exit`/`terminate`, which post the seat's whole allocation to its payee
  and close it (`seat_debit_authorized`);
* `exit` is a kernel action: the contract's own clause is consulted for
  reallocations and never for an exit, so no contract clause can forbid it
  (`exit_ignores_contract_clause`);
* `terminate` of an instance exits every open seat of that instance.

T3 (design `MINI-PROGRAM-MODEL-20261004` §3, root rulings of 2026-10-05):
`seat_offer_safe_forever` (every open seat of every reachable world satisfies
its law), `exit_enabled` and `exit_pays_allocation` (an on-demand offerer can
always exit, and the exit moves exactly the seat's balances to its payee),
`seat_conserves` (every admitted step conserves every asset). Teeth and
inhabitants are at the end: a two-party swap that settles after the price moved
from the quote, a zero-`want` seat, and refusals.

What is not here: the native signed-command route (`Kernel.ObjectiveBendNative*`
does not yet emit seat actions), activities holding seats (an activity ABORT must
call `closeSeat` for every seat it holds; `terminate` shows the shape), fees,
and non-fungible (set) amounts. -/
import Kernel.Invitation

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

/-! ## Postings -/

/-- A movement between Book accounts. -/
structure Transfer where
  source : AccountId
  destination : AccountId
  asset : AssetId
  amount : Nat
  deriving DecidableEq, Repr

def post (book : Book) (transfer : Transfer) : Book :=
  (Operation.transfer transfer.source transfer.destination transfer.asset transfer.amount).apply book

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

theorem balance_post (book : Book) (transfer : Transfer) (account : AccountId) (asset : AssetId) :
    (post book transfer).balance account asset =
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

@[simp] theorem post_accounts (book : Book) (transfer : Transfer) :
    (post book transfer).accounts = book.accounts := by
  simp [post]

theorem post_conserves (book : Book) (transfer : Transfer)
    (source : transfer.source ∈ book.accounts) (destination : transfer.destination ∈ book.accounts)
    (asset : AssetId) : (post book transfer).totalAsset asset = book.totalAsset asset :=
  Operation.apply_conserves (Operation.transfer transfer.source transfer.destination transfer.asset transfer.amount)
    book source destination asset

inductive Refusal where
  | invitation (reason : Invitations.Refusal)
  | notASubject | notAnInstance | notTheInstance (inst : InstanceId)
  | seatAccountNotFresh (account : AccountId) | seatAccountOwned (account : AccountId)
  | fundingNotOwned (account : AccountId) | payeeMissing (account : AccountId)
  | missing (account : AccountId) | unfunded (account : AccountId) (asset : AssetId)
  | offerUnsafe (account : AccountId)
  | outsideSeats (transfer : Transfer) (inst : InstanceId)
  | contractClauseRefused (inst : InstanceId)
  | seatMissing (account : AccountId) | seatClosed (account : AccountId)
  | exitNotAuthorized (account : AccountId)
  | instanceExists (inst : InstanceId)
  deriving DecidableEq, Repr

/-- Apply transfers in order; each needs both endpoints registered and a funded
source (no issuer mint happens here). -/
def settle (book : Book) : List Transfer → Except Refusal Book
  | [] => .ok book
  | transfer :: rest =>
    if transfer.source ∉ book.accounts then .error (.missing transfer.source)
    else if transfer.destination ∉ book.accounts then .error (.missing transfer.destination)
    else if book.balance transfer.source transfer.asset < transfer.amount then
      .error (.unfunded transfer.source transfer.asset)
    else settle (post book transfer) rest

theorem settle_accounts {book book' : Book} {transfers : List Transfer}
    (settled : settle book transfers = .ok book') : book'.accounts = book.accounts := by
  induction transfers generalizing book with
  | nil => simp only [settle] at settled; cases settled; rfl
  | cons transfer rest ih =>
    simp only [settle] at settled
    split at settled
    · cases settled
    split at settled
    · cases settled
    split at settled
    · cases settled
    rw [ih settled, post_accounts]

theorem settle_conserves {book book' : Book} {transfers : List Transfer}
    (settled : settle book transfers = .ok book') (asset : AssetId) :
    book'.totalAsset asset = book.totalAsset asset := by
  induction transfers generalizing book with
  | nil => simp only [settle] at settled; cases settled; rfl
  | cons transfer rest ih =>
    simp only [settle] at settled
    split at settled
    · cases settled
    rename_i source
    split at settled
    · cases settled
    rename_i destination
    split at settled
    · cases settled
    rw [ih settled, post_conserves book transfer (not_not.mp source) (not_not.mp destination)]

/-- An account no transfer names keeps every balance. -/
theorem settle_untouched {book book' : Book} {transfers : List Transfer} {account : AccountId}
    (settled : settle book transfers = .ok book')
    (away : ∀ transfer ∈ transfers, transfer.source ≠ account ∧ transfer.destination ≠ account)
    (asset : AssetId) : book'.balance account asset = book.balance account asset := by
  induction transfers generalizing book with
  | nil => simp only [settle] at settled; cases settled; rfl
  | cons transfer rest ih =>
    simp only [settle] at settled
    split at settled
    · cases settled
    split at settled
    · cases settled
    split at settled
    · cases settled
    obtain ⟨notSource, notDestination⟩ := away transfer (by simp)
    rw [ih settled (fun t m => away t (by simp [m])), balance_post,
      if_neg (fun h => notSource h.1.symm), if_neg (fun h => notDestination h.1.symm)]
    simp

/-- An account no transfer debits never loses balance. -/
theorem settle_credit_only {book book' : Book} {transfers : List Transfer} {account : AccountId}
    (settled : settle book transfers = .ok book')
    (away : ∀ transfer ∈ transfers, transfer.source ≠ account)
    (asset : AssetId) : book.balance account asset ≤ book'.balance account asset := by
  induction transfers generalizing book with
  | nil => simp only [settle] at settled; cases settled; exact le_rfl
  | cons transfer rest ih =>
    simp only [settle] at settled
    split at settled
    · cases settled
    split at settled
    · cases settled
    split at settled
    · cases settled
    have step := ih settled (fun t m => away t (by simp [m]))
    have notSource := away transfer (by simp)
    rw [balance_post, if_neg (fun h => notSource h.1.symm)] at step
    split_ifs at step <;> omega

/-- Settling keeps an account's balances non-negative: every debit is funded. -/
theorem settle_nonneg {book book' : Book} {transfers : List Transfer} {account : AccountId}
    (settled : settle book transfers = .ok book') (nonneg : ∀ asset, 0 ≤ book.balance account asset)
    (asset : AssetId) : 0 ≤ book'.balance account asset := by
  induction transfers generalizing book with
  | nil => simp only [settle] at settled; cases settled; exact nonneg asset
  | cons transfer rest ih =>
    simp only [settle] at settled
    split at settled
    · cases settled
    split at settled
    · cases settled
    split at settled
    · cases settled
    rename_i funded
    apply ih settled
    intro asset'
    rw [balance_post]
    have := nonneg asset'
    split_ifs with h1 h2 <;> (try obtain ⟨rfl, rfl⟩ := h1) <;> omega

/-! ## Payout: a seat's whole allocation to its payee -/

/-- Move the seat's current balance of each listed asset to the payee. Only
registered endpoints are admitted, so the move conserves; no funding check is
needed because the amount IS the balance. -/
def payout (book : Book) (account payee : AccountId) : List AssetId → Book
  | [] => book
  | asset :: rest =>
    payout (post book ⟨account, payee, asset, (book.balance account asset).toNat⟩) account payee rest

@[simp] theorem payout_accounts (book : Book) (account payee : AccountId) (assets : List AssetId) :
    (payout book account payee assets).accounts = book.accounts := by
  induction assets generalizing book with
  | nil => rfl
  | cons asset rest ih => simp [payout, ih]

theorem payout_conserves (book : Book) (account payee : AccountId) (assets : List AssetId)
    (accountMember : account ∈ book.accounts) (payeeMember : payee ∈ book.accounts) (asset : AssetId) :
    (payout book account payee assets).totalAsset asset = book.totalAsset asset := by
  induction assets generalizing book with
  | nil => rfl
  | cons first rest ih =>
    simp only [payout]
    rw [ih _ (by simpa using accountMember) (by simpa using payeeMember)]
    exact post_conserves _ _ accountMember payeeMember asset

/-- Accounts other than the seat only gain. -/
theorem payout_credit_only (book : Book) (account payee other : AccountId) (assets : List AssetId)
    (different : other ≠ account) (asset : AssetId) :
    book.balance other asset ≤ (payout book account payee assets).balance other asset := by
  induction assets generalizing book with
  | nil => exact le_rfl
  | cons first rest ih =>
    simp only [payout]
    refine le_trans ?_ (ih _)
    rw [balance_post]
    simp only [different, false_and, if_false, sub_zero]
    split_ifs <;> omega

/-- Over distinct assets, a payout moves exactly the seat's non-negative
balances: the seat ends at zero and the payee gains exactly that much. -/
theorem payout_exact (book : Book) (account payee : AccountId) (assets : List AssetId)
    (nodup : assets.Nodup) (different : payee ≠ account)
    (nonneg : ∀ asset ∈ assets, 0 ≤ book.balance account asset) (asset : AssetId) (named : asset ∈ assets) :
    (payout book account payee assets).balance account asset = 0 ∧
      (payout book account payee assets).balance payee asset =
        book.balance payee asset + book.balance account asset := by
  induction assets generalizing book with
  | nil => simp at named
  | cons first rest ih =>
    simp only [payout]
    rw [List.nodup_cons] at nodup
    have posted : ∀ a ∈ rest, (post book ⟨account, payee, first, (book.balance account first).toNat⟩).balance account a =
        book.balance account a := by
      intro a member
      have : a ≠ first := fun h => nodup.1 (h ▸ member)
      rw [balance_post]; simp [this, Ne.symm different]
    rcases List.mem_cons.mp named with rfl | member
    · -- the first asset is paid now and untouched by the rest
      have untouchedSeat : ∀ (b : Book) (as : List AssetId), asset ∉ as →
          (payout b account payee as).balance account asset = b.balance account asset ∧
          (payout b account payee as).balance payee asset = b.balance payee asset := by
        intro b as away
        induction as generalizing b with
        | nil => exact ⟨rfl, rfl⟩
        | cons a more ihm =>
          simp only [payout]
          have ne : asset ≠ a := fun h => away (h ▸ List.mem_cons_self)
          obtain ⟨h1, h2⟩ := ihm (post b ⟨account, payee, a, (b.balance account a).toNat⟩)
            (fun m => away (List.mem_cons_of_mem _ m))
          rw [h1, h2, balance_post, balance_post]
          simp [ne]
      obtain ⟨seat, gain⟩ := untouchedSeat _ rest nodup.1
      rw [seat, gain, balance_post, balance_post]
      have := nonneg asset (by simp)
      simp only [and_self, if_true, Ne.symm different, false_and, if_false, different]
      constructor <;> simp [Int.toNat_of_nonneg this]
    · have := ih _ nodup.2 (fun a m => (posted a m).symm ▸ nonneg a (List.mem_cons_of_mem _ m)) member
      have ne : asset ≠ first := fun h => nodup.1 (h ▸ member)
      rw [posted asset member] at this
      refine ⟨this.1, ?_⟩
      rw [this.2, balance_post]
      simp [ne]

/-! ## The seat world -/

structure Seat where
  account : AccountId
  inst : InstanceId
  offerer : SubjectId
  payee : AccountId
  proposal : Proposal
  isOpen : Bool
  deriving DecidableEq, Repr

structure World where
  book : Book
  /-- Which subject controls each ordinary (non-seat) Book account. -/
  owners : List (AccountId × SubjectId)
  registry : Registry
  seats : List Seat

def World.ownerOf (world : World) (account : AccountId) : Option SubjectId :=
  (world.owners.find? (fun entry => entry.1 == account)).map Prod.snd

def World.seat? (world : World) (account : AccountId) : Option Seat :=
  world.seats.find? (fun seat => seat.account == account)

/-- Who acts: a subject signing, or a turn of a contract instance. -/
inductive Actor where
  | subject (subject : SubjectId)
  | inst (inst : InstanceId)
  deriving DecidableEq, Repr

inductive Action where
  | create (inst : Instance)
  | mint (invitation : Invitation)
  | handOver (id : InvitationId) (recipient : SubjectId)
  | offer (id : InvitationId) (expect : Expectation) (seat funding payee : AccountId) (proposal : Proposal)
  | reallocate (inst : InstanceId) (transfers : List Transfer)
  | exit (seat : AccountId)
  | terminate (inst : InstanceId)
  deriving Repr

def closeSeats (seats : List Seat) (account : AccountId) : List Seat :=
  seats.map fun seat => if seat.account = account then { seat with isOpen := false } else seat

/-- Close one open seat: pay its whole allocation to its payee. -/
def closeSeat (world : World) (seat : Seat) : Except Refusal World :=
  if seat.account ∉ world.book.accounts then .error (.missing seat.account)
  else if seat.payee ∉ world.book.accounts then .error (.payeeMissing seat.payee)
  else .ok { world with
    book := payout world.book seat.account seat.payee seat.proposal.assets
    seats := closeSeats world.seats seat.account }

def closeAll (world : World) : List Seat → Except Refusal World
  | [] => .ok world
  | seat :: rest =>
    match closeSeat world seat with
    | .error reason => .error reason
    | .ok next => closeAll next rest

def exitAuthorized (height : Nat) (actor : Actor) (seat : Seat) : Bool :=
  match actor, seat.proposal.exit with
  | .subject subject, .onDemand => subject == seat.offerer
  | .inst inst, _ => inst == seat.inst
  | _, .afterDeadline due => decide (due ≤ height)

def openSeatsOf (world : World) (inst : InstanceId) : List Seat :=
  world.seats.filter fun seat => seat.isOpen && seat.inst == inst

def touches (transfers : List Transfer) (account : AccountId) : Bool :=
  transfers.any fun transfer => transfer.source == account || transfer.destination == account

/-- A reallocation moves value only between open seats of its own instance, and
credits a seat only in an asset its proposal names (so `exit` pays out
everything a seat holds). -/
def addressed (seats : List Seat) (transfer : Transfer) : Bool :=
  seats.any (fun seat => seat.account == transfer.source) &&
    seats.any (fun seat => seat.account == transfer.destination && transfer.asset ∈ seat.proposal.assets)

/-- The first open seat a reallocation touched whose law now fails. -/
def firstUnsafe (seats : List Seat) (book : Book) (transfers : List Transfer) : Option Seat :=
  seats.find? fun seat => seat.isOpen && touches transfers seat.account && !safeAt book seat.account seat.proposal

def giveTransfers (funding seat : AccountId) (proposal : Proposal) : List Transfer :=
  proposal.give.map fun entry => ⟨funding, seat, entry.1, entry.2⟩

def requestState (action : Int) : Pred.State := ⟨[("request/action", action)]⟩

/-- The contract's own clause, consulted for reallocations only. -/
def contractAdmits (inst : Instance) : Bool :=
  Pred.eval inst.clause (requestState 1) (requestState 1)

def retireInstance (registry : Registry) (inst : InstanceId) : Registry :=
  { registry with
    instances := registry.instances.filter (fun i => i.id ≠ inst)
    live := registry.live.filter (fun v => v.inst ≠ inst)
    spent := (registry.live.filter (fun v => v.inst = inst)).map Invitation.id ++ registry.spent }

/-- The one transition function of the seat world. -/
def step (world : World) (height : Nat) (actor : Actor) : Action → Except Refusal World
  | .create inst =>
    match actor with
    | .inst _ => .error .notASubject
    | .subject _ =>
      if (world.registry.instance? inst.id).isSome then .error (.instanceExists inst.id)
      else .ok { world with registry := { world.registry with instances := inst :: world.registry.instances } }
  | .mint invitation =>
    match actor with
    | .subject _ => .error .notAnInstance
    | .inst acting =>
      match Invitations.mint world.registry acting invitation with
      | .error reason => .error (.invitation reason)
      | .ok registry => .ok { world with registry := registry }
  | .handOver id recipient =>
    match actor with
    | .inst _ => .error .notASubject
    | .subject subject =>
      match Invitations.handOver world.registry subject id recipient with
      | .error reason => .error (.invitation reason)
      | .ok registry => .ok { world with registry := registry }
  | .offer id expect seatAccount funding payee proposal =>
    match actor with
    | .inst _ => .error .notASubject
    | .subject subject =>
      match Invitations.spend world.registry subject id expect with
      | .error reason => .error (.invitation reason)
      | .ok (invitation, registry) =>
        if ¬ RegistrationAdmission world.book seatAccount then .error (.seatAccountNotFresh seatAccount)
        else if (world.ownerOf seatAccount).isSome then .error (.seatAccountOwned seatAccount)
        else if world.ownerOf funding ≠ some subject then .error (.fundingNotOwned funding)
        else if payee ∉ world.book.accounts then .error (.payeeMissing payee)
        else
          match settle (world.book.registerAccount seatAccount) (giveTransfers funding seatAccount proposal) with
          | .error reason => .error reason
          | .ok book =>
            if safeAt book seatAccount proposal then
              .ok { world with
                book := book
                registry := registry
                seats := ⟨seatAccount, invitation.inst, subject, payee, proposal, true⟩ :: world.seats }
            else .error (.offerUnsafe seatAccount)
  | .reallocate instId transfers =>
    match actor with
    | .subject _ => .error .notAnInstance
    | .inst acting =>
      if acting ≠ instId then .error (.notTheInstance instId)
      else match world.registry.instance? instId with
      | none => .error (.invitation (.instanceMissing instId))
      | some inst =>
        if !contractAdmits inst then .error (.contractClauseRefused instId)
        else match transfers.find? (fun transfer => !addressed (openSeatsOf world instId) transfer) with
        | some transfer => .error (.outsideSeats transfer instId)
        | none =>
          match settle world.book transfers with
          | .error reason => .error reason
          | .ok book =>
            match firstUnsafe world.seats book transfers with
            | some seat => .error (.offerUnsafe seat.account)
            | none => .ok { world with book := book }
  | .exit account =>
    match world.seat? account with
    | none => .error (.seatMissing account)
    | some seat =>
      if !seat.isOpen then .error (.seatClosed account)
      else if !exitAuthorized height actor seat then .error (.exitNotAuthorized account)
      else closeSeat world seat
  | .terminate instId =>
    match actor with
    | .subject _ => .error .notAnInstance
    | .inst acting =>
      if acting ≠ instId then .error (.notTheInstance instId)
      else match closeAll world (openSeatsOf world instId) with
      | .error reason => .error reason
      | .ok closed => .ok { closed with registry := retireInstance closed.registry instId }

/-! ## The invariant -/

structure Inv (world : World) : Prop where
  safe : ∀ seat ∈ world.seats, seat.isOpen = true → safeAt world.book seat.account seat.proposal = true
  nonneg : ∀ seat ∈ world.seats, seat.isOpen = true → ∀ asset, 0 ≤ world.book.balance seat.account asset
  member : ∀ seat ∈ world.seats, seat.account ∈ world.book.accounts ∧ seat.payee ∈ world.book.accounts
  payeeOther : ∀ seat ∈ world.seats, seat.payee ≠ seat.account
  unowned : ∀ seat ∈ world.seats, world.ownerOf seat.account = none
  distinct : (world.seats.map Seat.account).Nodup

theorem Inv.genesis (world : World) (empty : world.seats = []) : Inv world := by
  constructor <;> simp [empty]

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

/-! ## Lemmas about the transitions -/

theorem closeSeat_spec {world next : World} {seat : Seat} (closed : closeSeat world seat = .ok next) :
    seat.account ∈ world.book.accounts ∧ seat.payee ∈ world.book.accounts ∧
    next = { world with
      book := payout world.book seat.account seat.payee seat.proposal.assets
      seats := closeSeats world.seats seat.account } := by
  unfold closeSeat at closed
  split at closed
  · cases closed
  · split at closed
    · cases closed
    · rename_i a p
      cases closed
      exact ⟨not_not.mp a, not_not.mp p, rfl⟩

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
      original.proposal = seat.proposal ∧ original.inst = seat.inst ∧
      (seat.isOpen = true → original.isOpen = true ∧ seat.account ≠ account) := by
  unfold closeSeats at member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  refine ⟨original, originalMember, ?_⟩
  split_ifs with same
  · simp
  · exact ⟨rfl, rfl, rfl, rfl, fun o => ⟨o, same⟩⟩

/-- Closing one seat of the list preserves the invariant. -/
theorem closeSeat_inv {world next : World} {seat : Seat} (inv : Inv world)
    (closed : closeSeat world seat = .ok next) : Inv next := by
  obtain ⟨_, _, rfl⟩ := closeSeat_spec closed
  constructor
  · intro s hs openS
    obtain ⟨o, ho, account, _, proposal, _, opened⟩ := mem_closeSeats hs
    obtain ⟨oOpen, different⟩ := opened openS
    rw [← account, ← proposal] at *
    exact safeAt_mono (fun asset _ => payout_credit_only _ _ _ _ _ different asset) (inv.safe o ho oOpen)
  · intro s hs openS asset
    obtain ⟨o, ho, account, _, _, _, opened⟩ := mem_closeSeats hs
    obtain ⟨oOpen, different⟩ := opened openS
    rw [← account] at *
    exact le_trans (inv.nonneg o ho oOpen asset) (payout_credit_only _ _ _ _ _ different asset)
  · intro s hs
    obtain ⟨o, ho, account, payee, _⟩ := mem_closeSeats hs
    rw [← account, ← payee]
    simpa using inv.member o ho
  · intro s hs
    obtain ⟨o, ho, account, payee, _⟩ := mem_closeSeats hs
    rw [← account, ← payee]
    exact inv.payeeOther o ho
  · intro s hs
    obtain ⟨o, ho, account, _⟩ := mem_closeSeats hs
    rw [← account]
    exact inv.unowned o ho
  · show ((closeSeats world.seats seat.account).map Seat.account).Nodup
    rw [closeSeats_map_account]; exact inv.distinct

theorem closeAll_inv {world next : World} {seats : List Seat} (inv : Inv world)
    (closed : closeAll world seats = .ok next) : Inv next := by
  induction seats generalizing world with
  | nil => simp only [closeAll] at closed; cases closed; exact inv
  | cons seat rest ih =>
    simp only [closeAll] at closed
    split at closed
    · cases closed
    · rename_i mid hmid
      exact ih (closeSeat_inv inv hmid) closed

theorem closeAll_conserves {world next : World} {seats : List Seat}
    (closed : closeAll world seats = .ok next) (asset : AssetId) :
    next.book.totalAsset asset = world.book.totalAsset asset := by
  induction seats generalizing world with
  | nil => simp only [closeAll] at closed; cases closed; rfl
  | cons seat rest ih =>
    simp only [closeAll] at closed
    split at closed
    · cases closed
    · rename_i mid hmid
      obtain ⟨a, p, rfl⟩ := closeSeat_spec hmid
      rw [ih closed]
      exact payout_conserves _ _ _ _ a p asset

/-- An account none of the closed seats owns only gains during `closeAll`. -/
theorem closeAll_credit_only {world next : World} {seats : List Seat} {account : AccountId}
    (closed : closeAll world seats = .ok next) (away : ∀ seat ∈ seats, seat.account ≠ account)
    (asset : AssetId) : world.book.balance account asset ≤ next.book.balance account asset := by
  induction seats generalizing world with
  | nil => simp only [closeAll] at closed; cases closed; exact le_rfl
  | cons seat rest ih =>
    simp only [closeAll] at closed
    split at closed
    · cases closed
    · rename_i mid hmid
      obtain ⟨_, _, rfl⟩ := closeSeat_spec hmid
      exact le_trans (payout_credit_only _ _ _ _ _ (Ne.symm (away seat (by simp))) asset)
        (ih closed (fun s m => away s (by simp [m])))

theorem registerAccount_balance (book : Book) (seat account : AccountId) (asset : AssetId) :
    (book.registerAccount seat).balance account asset = book.balance account asset := rfl

/-! ## The offer and reallocation cases -/

theorem offer_away {world : World} (inv : Inv world) {seatAccount funding : AccountId} {subject : SubjectId}
    (fresh : RegistrationAdmission world.book seatAccount)
    (funded : ¬ world.ownerOf funding ≠ some subject) (proposal : Proposal) :
    ∀ s ∈ world.seats, ∀ t ∈ giveTransfers funding seatAccount proposal,
      t.source ≠ s.account ∧ t.destination ≠ s.account := by
  intro s hs t ht
  simp only [giveTransfers, List.mem_map] at ht
  obtain ⟨e, _, rfl⟩ := ht
  refine ⟨fun eq => ?_, fun eq => fresh.1 (by simp only at eq; rw [eq]; exact (inv.member s hs).1)⟩
  have := inv.unowned s hs
  rw [← eq] at this
  rw [this] at funded
  exact funded (by simp)

/-- An offer leaves every existing seat's balances untouched. -/
theorem offer_untouched {world : World} (inv : Inv world) {seatAccount funding : AccountId} {subject : SubjectId}
    {proposal : Proposal} {book : Book}
    (fresh : RegistrationAdmission world.book seatAccount)
    (funded : ¬ world.ownerOf funding ≠ some subject)
    (settled : settle (world.book.registerAccount seatAccount) (giveTransfers funding seatAccount proposal) = .ok book)
    {seat : Seat} (member : seat ∈ world.seats) (asset : AssetId) :
    book.balance seat.account asset = world.book.balance seat.account asset := by
  rw [settle_untouched settled (offer_away inv fresh funded proposal seat member) asset]
  rfl

theorem offer_inv {world : World} (inv : Inv world) {seatAccount funding payee : AccountId}
    {subject : SubjectId} {proposal : Proposal} {book : Book} {inst : InstanceId} {registry : Registry}
    (fresh : RegistrationAdmission world.book seatAccount)
    (owned : ¬ (world.ownerOf seatAccount).isSome = true)
    (funded : ¬ world.ownerOf funding ≠ some subject)
    (payeeIn : payee ∈ world.book.accounts)
    (settled : settle (world.book.registerAccount seatAccount) (giveTransfers funding seatAccount proposal) = .ok book)
    (safeNew : safeAt book seatAccount proposal = true) :
    Inv { world with
      book := book
      registry := registry
      seats := ⟨seatAccount, inst, subject, payee, proposal, true⟩ :: world.seats } := by
  have accountsEq := settle_accounts settled
  have notOwned : world.ownerOf seatAccount = none := by
    cases h : world.ownerOf seatAccount <;> simp_all
  have fundingOther : funding ≠ seatAccount := by
    intro eq; rw [eq, notOwned] at funded; exact funded (by simp)
  constructor
  · intro s hs openS
    rcases List.mem_cons.mp hs with rfl | old
    · exact safeNew
    · rw [safeAt_congr (fun asset _ => offer_untouched inv fresh funded settled old asset)]
      exact inv.safe s old openS
  · intro s hs openS asset
    rcases List.mem_cons.mp hs with rfl | old
    · have zero : (world.book.registerAccount seatAccount).balance seatAccount asset = 0 :=
        fresh.balance_zero asset
      have credit := settle_credit_only settled (account := seatAccount) (fun t ht => by
        simp only [giveTransfers, List.mem_map] at ht
        obtain ⟨e, _, rfl⟩ := ht
        exact fundingOther) asset
      rw [zero] at credit; exact credit
    · rw [offer_untouched inv fresh funded settled old]; exact inv.nonneg s old openS asset
  · intro s hs
    show s.account ∈ book.accounts ∧ s.payee ∈ book.accounts
    rw [accountsEq]
    show s.account ∈ insert seatAccount world.book.accounts ∧ s.payee ∈ insert seatAccount world.book.accounts
    rcases List.mem_cons.mp hs with rfl | old
    · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem payeeIn⟩
    · exact ⟨Finset.mem_insert_of_mem (inv.member s old).1, Finset.mem_insert_of_mem (inv.member s old).2⟩
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | old
    · intro eq; simp only at eq; exact fresh.1 (eq ▸ payeeIn)
    · exact inv.payeeOther s old
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | old
    · exact notOwned
    · exact inv.unowned s old
  · show ((⟨seatAccount, inst, subject, payee, proposal, true⟩ :: world.seats).map Seat.account).Nodup
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun mem => ?_, inv.distinct⟩
    obtain ⟨s, hs, eq⟩ := List.mem_map.mp mem
    simp only at eq
    exact fresh.1 (eq ▸ (inv.member s hs).1)

theorem reallocate_inv {world : World} (inv : Inv world) {transfers : List Transfer} {book : Book}
    (settled : settle world.book transfers = .ok book)
    (noneUnsafe : firstUnsafe world.seats book transfers = none) :
    Inv { world with book := book } := by
  unfold firstUnsafe at noneUnsafe
  rw [List.find?_eq_none] at noneUnsafe
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
      show safeAt book s.account s.proposal = true
      rw [safeAt_congr (fun asset _ => settle_untouched settled away asset)]
      exact inv.safe s hs openS
  · intro s hs openS asset
    exact settle_nonneg settled (inv.nonneg s hs openS) asset
  · intro s hs
    show s.account ∈ book.accounts ∧ s.payee ∈ book.accounts
    rw [settle_accounts settled]; exact inv.member s hs
  · exact inv.payeeOther
  · exact inv.unowned
  · exact inv.distinct

/-! ## T3 (a): every open seat of every reachable world satisfies its law -/

theorem step_inv {world next : World} {height : Nat} {actor : Actor} {action : Action}
    (inv : Inv world) (admitted : step world height actor action = .ok next) : Inv next := by
  cases action with
  | create inst =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨inv.safe, inv.nonneg, inv.member, inv.payeeOther, inv.unowned, inv.distinct⟩
  | mint invitation =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨inv.safe, inv.nonneg, inv.member, inv.payeeOther, inv.unowned, inv.distinct⟩
  | handOver id recipient =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact ⟨inv.safe, inv.nonneg, inv.member, inv.payeeOther, inv.unowned, inv.distinct⟩
  | offer id expect seatAccount funding payee proposal =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    rename_i subject
    split at admitted
    · cases admitted
    rename_i invitation registry _
    split at admitted
    · cases admitted
    rename_i fresh
    split at admitted
    · cases admitted
    rename_i owned
    split at admitted
    · cases admitted
    rename_i funded
    split at admitted
    · cases admitted
    rename_i payeeIn
    split at admitted
    · cases admitted
    rename_i book settled
    split at admitted
    · rename_i safeNew
      cases admitted
      exact offer_inv inv (not_not.mp fresh) owned funded (not_not.mp payeeIn) settled safeNew
    · cases admitted
  | reallocate instId transfers =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    rename_i acting
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    rename_i inst _
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    rename_i book settled
    split at admitted
    · cases admitted
    rename_i noneUnsafe
    cases admitted
    exact reallocate_inv inv settled noneUnsafe
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
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    rename_i closed hclosed
    cases admitted
    have := closeAll_inv inv hclosed
    exact ⟨this.safe, this.nonneg, this.member, this.payeeOther, this.unowned, this.distinct⟩

inductive Reachable (genesis : World) : World → Prop
  | start : Reachable genesis genesis
  | admit {world next : World} (height : Nat) (actor : Actor) (action : Action) :
      Reachable genesis world → step world height actor action = .ok next → Reachable genesis next

theorem reachable_inv {genesis world : World} (empty : genesis.seats = [])
    (reachable : Reachable genesis world) : Inv world := by
  induction reachable with
  | start => exact Inv.genesis genesis empty
  | admit _ _ _ _ admitted ih => exact step_inv ih admitted

/-- **T3 (a).** From a world with no seats, in every world reachable by admitted
turns, every open seat's Book balances satisfy its offer-safety law. -/
theorem seat_offer_safe_forever {genesis world : World} (empty : genesis.seats = [])
    (reachable : Reachable genesis world) :
    ∀ seat ∈ world.seats, seat.isOpen = true → safeAt world.book seat.account seat.proposal = true :=
  (reachable_inv empty reachable).safe

/-! ## T3 (b): exit is always available and pays exactly the allocation -/

theorem exit_admitted {world : World} {height : Nat} {actor : Actor} {seat : Seat} (inv : Inv world)
    (member : seat ∈ world.seats) (opened : seat.isOpen = true)
    (authorized : exitAuthorized height actor seat = true) :
    step world height actor (.exit seat.account) =
      .ok { world with
        book := payout world.book seat.account seat.payee seat.proposal.assets
        seats := closeSeats world.seats seat.account } := by
  simp only [step, seat?_eq inv.distinct member, opened, authorized, Bool.not_true, if_false,
    Bool.false_eq_true]
  unfold closeSeat
  rw [if_neg (not_not.mpr (inv.member seat member).1), if_neg (not_not.mpr (inv.member seat member).2)]

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

/-- **T3 (b), what an exit pays.** The seat ends at zero in every asset its
proposal names, and its payee gains exactly the seat's balance. -/
theorem exit_pays_allocation {world next : World} {height : Nat} {actor : Actor} {seat : Seat}
    (inv : Inv world) (member : seat ∈ world.seats) (opened : seat.isOpen = true)
    (admitted : step world height actor (.exit seat.account) = .ok next) :
    ∀ asset ∈ seat.proposal.assets, next.book.balance seat.account asset = 0 ∧
      next.book.balance seat.payee asset = world.book.balance seat.payee asset + world.book.balance seat.account asset := by
  intro asset named
  have authorized : exitAuthorized height actor seat = true := by
    simp only [step, seat?_eq inv.distinct member, opened, Bool.not_true, if_false,
      Bool.false_eq_true] at admitted
    split at admitted
    · cases admitted
    · rename_i h; simpa using h
  rw [exit_admitted inv member opened authorized] at admitted
  cases admitted
  exact payout_exact _ _ _ _ (List.nodup_dedup _) (inv.payeeOther seat member)
    (fun a _ => inv.nonneg seat member opened a) asset named

/-! ## T3 (c): every admitted step conserves every asset -/

theorem seat_conserves {world next : World} {height : Nat} {actor : Actor} {action : Action}
    (admitted : step world height actor action = .ok next) (asset : AssetId) :
    next.book.totalAsset asset = world.book.totalAsset asset := by
  cases action with
  | create inst =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    · split at admitted
      · cases admitted
      · cases admitted; rfl
  | mint invitation =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    · split at admitted
      · cases admitted
      · cases admitted; rfl
  | handOver id recipient =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    · split at admitted
      · cases admitted
      · cases admitted; rfl
  | offer id expect seatAccount funding payee proposal =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    rename_i fresh
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    rename_i book settled
    split at admitted
    · cases admitted
      show book.totalAsset asset = world.book.totalAsset asset
      rw [settle_conserves settled, Book.registerAccount_conserves _ _ (not_not.mp fresh)]
    · cases admitted
  | reallocate instId transfers =>
    simp only [step] at admitted
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
    rename_i book settled
    split at admitted
    · cases admitted
    cases admitted
    exact settle_conserves settled asset
  | exit account =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    obtain ⟨a, p, rfl⟩ := closeSeat_spec admitted
    exact payout_conserves _ _ _ _ a p asset
  | terminate instId =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    rename_i closed hclosed
    cases admitted
    exact closeAll_conserves hclosed asset

/-! ## Who may debit a seat -/

/-- **A seat is debited only by its own instance's reallocation, its exit, or
its instance's termination.** -/
theorem seat_debit_authorized {world next : World} {height : Nat} {actor : Actor} {action : Action}
    (inv : Inv world) (admitted : step world height actor action = .ok next)
    {seat : Seat} (member : seat ∈ world.seats) (opened : seat.isOpen = true) {asset : AssetId}
    (debited : next.book.balance seat.account asset < world.book.balance seat.account asset) :
    (actor = .inst seat.inst ∧ ∃ transfers, action = .reallocate seat.inst transfers) ∨
      action = .exit seat.account ∨ (actor = .inst seat.inst ∧ action = .terminate seat.inst) := by
  cases action with
  | create inst =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact absurd debited (lt_irrefl _)
  | mint invitation =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact absurd debited (lt_irrefl _)
  | handOver id recipient =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    · split at admitted
      · cases admitted
      · cases admitted; exact absurd debited (lt_irrefl _)
  | offer id expect seatAccount funding payee proposal =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    rename_i fresh
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    rename_i funded
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    rename_i book settled
    split at admitted
    · cases admitted
      rw [offer_untouched inv (not_not.mp fresh) funded settled member] at debited
      exact absurd debited (lt_irrefl _)
    · cases admitted
  | reallocate instId transfers =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    rename_i acting
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
    rename_i book settled
    split at admitted
    · cases admitted
    cases admitted
    have acting' : acting = instId := not_not.mp sameInst
    subst acting'
    -- the seat was a source of some transfer, so it is an open seat of this instance
    have source : ∃ transfer ∈ transfers, transfer.source = seat.account := by
      by_contra none
      simp only [not_exists, not_and] at none
      exact absurd (settle_credit_only settled (fun t m h => none t m h) asset) (not_le.mpr debited)
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
  | exit account =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    rename_i closing found
    split at admitted
    · cases admitted
    split at admitted
    · cases admitted
    obtain ⟨_, _, rfl⟩ := closeSeat_spec admitted
    have closingAccount : closing.account = account := by
      simpa using List.find?_some found
    by_cases same : seat.account = account
    · exact Or.inr (Or.inl (by rw [same]))
    · exfalso
      have := payout_credit_only world.book closing.account closing.payee seat.account
        closing.proposal.assets (by rw [closingAccount]; exact same) asset
      exact absurd this (not_le.mpr debited)
  | terminate instId =>
    simp only [step] at admitted
    split at admitted
    · cases admitted
    rename_i acting
    split at admitted
    · cases admitted
    rename_i sameInst
    split at admitted
    · cases admitted
    rename_i closed hclosed
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

#assert_axioms view_total safeAt_mono settle_conserves payout_exact closeSeat_inv step_inv
  seat_offer_safe_forever exit_enabled exit_after_deadline exit_pays_allocation seat_conserves
  seat_debit_authorized


/-! ## Inhabitants and teeth

A two-party swap. Alice holds 10 X and was quoted 5 Y for them; Bob holds 7 Y.
Each signs a RANGE, not an exact Plan: Alice gives 10 X and wants at least 5 Y;
Bob gives 7 Y and wants at least 9 X. By settlement the price has moved from the
quote (Bob pays 7 Y, not 5), and the swap still settles: an exact-plan signature
over "Alice receives 5 Y" would have been refused as stale. -/

namespace Example

def X : AssetId := 100
def Y : AssetId := 200
def alice : SubjectId := ⟨1⟩
def bob : SubjectId := ⟨2⟩
def aliceAccount : AccountId := 10
def bobAccount : AccountId := 20
def aliceSeat : AccountId := 30
def bobSeat : AccountId := 31
def package : Digest := ⟨77⟩

def genesisBook : Book where
  accounts := {aliceAccount, bobAccount}
  balances := DFinsupp.single (aliceAccount, X) 10 + DFinsupp.single (bobAccount, Y) 7
  leaseRecords := 0

def genesis : World := ⟨genesisBook, [(aliceAccount, alice), (bobAccount, bob)], ⟨[], [], []⟩, []⟩

/-- The swap contract's clause admits every reallocation. -/
def swapInstance : Instance := ⟨1, package, Pred.all []⟩

def sell : Invitation := ⟨1, 1, package, "sell", [], alice⟩
def buy : Invitation := ⟨2, 1, package, "buy", [], bob⟩

def aliceProposal : Proposal := ⟨[(X, 10)], [(Y, 5)], .onDemand⟩
def bobProposal : Proposal := ⟨[(Y, 7)], [(X, 9)], .onDemand⟩

/-- Run a script of (height, actor, action). -/
def run : World → List (Nat × Actor × Action) → Except Refusal World
  | world, [] => .ok world
  | world, (height, actor, action) :: rest =>
    match step world height actor action with
    | .error reason => .error reason
    | .ok next => run next rest

theorem run_reachable {genesis world next : World} {script : List (Nat × Actor × Action)}
    (reachable : Reachable genesis world) (ran : run world script = .ok next) : Reachable genesis next := by
  induction script generalizing world with
  | nil => simp only [run] at ran; cases ran; exact reachable
  | cons entry rest ih =>
    obtain ⟨height, actor, action⟩ := entry
    simp only [run] at ran
    split at ran
    · cases ran
    · rename_i mid hmid
      exact ih (Reachable.admit height actor action reachable hmid) ran

def opening : List (Nat × Actor × Action) :=
  [ (1, .subject alice, .create swapInstance),
    (1, .inst 1, .mint sell),
    (1, .inst 1, .mint buy),
    (2, .subject alice, .offer 1 ⟨1, package, "sell"⟩ aliceSeat aliceAccount aliceAccount aliceProposal),
    (3, .subject bob, .offer 2 ⟨1, package, "buy"⟩ bobSeat bobAccount bobAccount bobProposal) ]

def settlement : List (Nat × Actor × Action) :=
  [ (4, .inst 1, .reallocate 1 [⟨aliceSeat, bobSeat, X, 10⟩, ⟨bobSeat, aliceSeat, Y, 7⟩]),
    (5, .subject alice, .exit aliceSeat),
    (5, .subject bob, .exit bobSeat) ]

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
    (run genesis (opening ++ [(4, .inst 1, .reallocate 1
      [⟨aliceSeat, bobSeat, X, 10⟩, ⟨bobSeat, aliceSeat, Y, 4⟩])])).map balances =
      .error (.offerUnsafe aliceSeat) := by decide +kernel

/-- **A contract clause cannot forbid exit.** With a clause that refuses every
reallocation, the reallocation is refused, and Alice's exit still pays her
whole allocation back. -/
def lockedInstance : Instance := ⟨1, package, Pred.any []⟩

def lockedOpening : List (Nat × Actor × Action) :=
  (1, .subject alice, .create lockedInstance) :: opening.tail

theorem locked_contract_refuses_reallocation :
    (run genesis (lockedOpening ++ [(4, .inst 1, .reallocate 1 [⟨aliceSeat, bobSeat, X, 10⟩])])).map balances =
      .error (.contractClauseRefused 1) := by decide +kernel

theorem locked_contract_cannot_stop_exit :
    (run genesis (lockedOpening ++ [(4, .subject alice, .exit aliceSeat)])).map balances =
      .ok [10, 0, 0, 0] := by decide +kernel

/-- Only the offerer (or the contract) may exit an on-demand seat. -/
theorem stranger_cannot_exit :
    (run genesis (opening ++ [(4, .subject bob, .exit aliceSeat)])).map balances =
      .error (.exitNotAuthorized aliceSeat) := by decide +kernel

/-- An invitation is spent by its offer: offering it again is refused. -/
theorem invitation_spent_once :
    (run genesis (opening ++ [(4, .subject alice, .offer 1 ⟨1, package, "sell"⟩ 32 aliceAccount aliceAccount
      aliceProposal)])).map balances = .error (.invitation (.invitationMissing 1)) := by decide +kernel

/-- An invitation must assay as the offerer expects (here: the wrong role). -/
theorem assay_refused :
    (run genesis (opening.take 3 ++ [(2, .subject alice, .offer 1 ⟨1, package, "buy"⟩ aliceSeat aliceAccount
      aliceAccount aliceProposal)])).map balances = .error (.invitation (.assayFailed 1)) := by decide +kernel

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

def giftOpening : List (Nat × Actor × Action) :=
  [ (1, .subject alice, .create swapInstance),
    (1, .inst 1, .mint sell),
    (1, .inst 1, .mint buy),
    (2, .subject alice, .offer 1 ⟨1, package, "sell"⟩ aliceSeat aliceAccount aliceAccount giftProposal),
    (3, .subject bob, .offer 2 ⟨1, package, "buy"⟩ bobSeat bobAccount bobAccount bobProposal) ]

/-- The contract takes the whole gift (Alice wanted 0 Y), and the reallocation
is admitted. -/
theorem zero_want_gift_admitted :
    (run genesis (giftOpening ++ [(4, .inst 1, .reallocate 1 [⟨aliceSeat, bobSeat, X, 10⟩]),
      (5, .subject bob, .exit bobSeat)])).map balances = .ok [0, 0, 10, 7] := by decide +kernel

/-- The tooth for the total view: a view MISSING Alice's Y slot reads her
`want` of 5 Y as met (the fail-closed `le` on an absent slot is false, so its
negation is true). `view` always carries every named slot (`view_total`). -/
theorem absent_slot_reads_as_met :
    Pred.eval (atLeast Y 5) ⟨[]⟩ ⟨[]⟩ = true := by decide +kernel

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
  zero_want_satisfied nat_predecessor_encoding_refuses_zero_want zero_want_gift_admitted
  absent_slot_reads_as_met swap_opening_reachable

end Example

end Minidregg.Kernel.Seats
