/-
# Kernel.PurseRefill — a Book burn funds an AgentGrain purse (PAY §2.7, lane P6)

A friend's Book account `A` funds the purse of an AgentGrain task `T` in one
joint turn over two cells:

* the **Book** leg: `Operation.burn A credit amount`, a `Batch` decided by
  `Batch.Admission` at the loaded Book (the payer must fund it: `bookRefused`),
  returning `amount` to the credit asset's issuer well;
* the **purse** leg: the AgentGrain `refill gain` edge on `T`
  (`AgentGrain.refillPolicy`), which only raises `remaining`.

The two legs are joined by the turn's resource law at the credit coordinate
(`delta`, `aggregateDelta`), the shape of `MultiCellHyperedge.ResourceLaw` /
`Commit.aggregateBalanced`: the Book leg's delta is its change in
*circulating* credit (the asset's total minus its well) and the purse leg's is
its change in allowance (`remaining + reserved`).  The decision refuses
`unbalanced` unless the sum is zero, so a purse leg claiming more than the burn
never commits (`overclaim_fails_commit`); accepted, the purse gained exactly
what the payer burned (`refill_conserves`).

The credit asset is the pay tariff's `asset` (P3 mints credit there), so a
refill requires a valid tariff.  The payer must hold the owner grant on `A`
(`refill_requires_owner`, the `PayAssignmentReceiver.OwnerGrant` fact) and may
not be the issuer well (`payerIsIssuer`): a burn from the well to itself moves
no value and would fund the purse from nothing.

`purse_never_mints` is the purse's audit statement: along any purse history
of generic transitions and accepted refills, the purse's allowance never
exceeds its start plus the sum of the burns that funded it.  The Book's side,
`−well` moving by exactly the credits minted minus the credits burned (into
purses and into jobs) plus the jobs' payouts, is `PayLedger.ledger_identity`.
-/
import Kernel.AgentGrain
import Kernel.PayAssignmentReceiver
import Kernel.PayObservationProofs

namespace Minidregg.Kernel.PurseRefill

open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayAssignmentReceiver (OwnerGrant)
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Refusals -/

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | payUnavailable
  | bookUnavailable | purseUnavailable | purseLawUnavailable
  | staleAuthority
  | tariffInvalid | notOwner | payerIsIssuer | zeroAmount | purseUnreadable
  | bookRefused | unbalanced | purseRefused
  | purseCell (reason : DeclaredResourceScalar.Reject)
  | replayedMarker | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving Repr

/-! ## The decided plan and the two legs -/

structure Plan where
  asset : AssetId
  account : AccountId
  /-- The Book leg: credit burned from `account`. -/
  amount : Nat
  /-- The purse leg: allowance the purse gains. -/
  gain : Nat
  before : AgentGrain.State
  deriving DecidableEq, Repr

/-- The Book leg: one burn, no registrations. -/
def Plan.batch (plan : Plan) : Batch := ⟨[], [.burn plan.account plan.asset plan.amount], []⟩

/-- The purse leg: the refill edge applied to the loaded purse. -/
def Plan.after (plan : Plan) : AgentGrain.State :=
  (AgentGrain.Operation.refill (Int.ofNat plan.gain)).after plan.before

/-- Credit held by accounts other than the asset's issuer well. -/
def circulating (book : Book) (asset : AssetId) : Int :=
  book.totalAsset asset - book.balance asset asset

/-- A purse's allowance: what it may still spend plus what it holds. -/
def budget (s : AgentGrain.State) : Int := s.remaining + s.reserved

inductive Leg where
  | book
  | purse
  deriving DecidableEq, Repr

/-- The turn's resource law at the credit coordinate: each incidence's delta,
computed from its own exact pre and post. -/
def delta (book : Book) (plan : Plan) : Leg → Int
  | .book => circulating (plan.batch.apply book) plan.asset - circulating book plan.asset
  | .purse => budget plan.after - budget plan.before

/-- The joint delta: the sum over both incidences (`MultiCellHyperedge.aggregateDelta`). -/
def aggregateDelta (book : Book) (plan : Plan) : Int :=
  ([Leg.book, Leg.purse].map (delta book plan)).sum

/-! ## The pure decision -/

/-- In order: a valid tariff (its `asset` is the credit), the owner grant on
the account, not the issuer well, a positive burn, a readable purse, the Book
admission of the burn, and the balanced joint delta. -/
def decideRefill (tariff : Option Tariff) (stored : Option (StoredCapability .account))
    (subject : SubjectId) (book : Book) (purse : Option AgentGrain.State)
    (account amount gain : Nat) : Except Reject Plan :=
  match tariff with
  | none => .error .tariffInvalid
  | some tariff =>
    if tariff.valid then
      if OwnerGrant stored subject account then
        if account = tariff.asset then .error .payerIsIssuer
        else if amount = 0 then .error .zeroAmount
        else match purse with
          | none => .error .purseUnreadable
          | some before =>
            let plan : Plan := ⟨tariff.asset, account, amount, gain, before⟩
            if plan.batch.Admission book then
              if aggregateDelta book plan = 0 then .ok plan else .error .unbalanced
            else .error .bookRefused
      else .error .notOwner
    else .error .tariffInvalid

/-- Everything an accepted refill establishes. -/
theorem decideRefill_ok {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {purse : Option AgentGrain.State}
    {account amount gain : Nat} {plan : Plan}
    (accepted : decideRefill tariff stored subject book purse account amount gain = .ok plan) :
    (∃ t, tariff = some t ∧ t.valid ∧ plan.asset = t.asset) ∧
      OwnerGrant stored subject account ∧ account ≠ plan.asset ∧ 0 < amount ∧
      purse = some plan.before ∧ plan.account = account ∧ plan.amount = amount ∧
      plan.gain = gain ∧ plan.batch.Admission book ∧ aggregateDelta book plan = 0 := by
  unfold decideRefill at accepted
  cases tariff with
  | none => cases accepted
  | some t =>
    simp only at accepted
    by_cases valid : t.valid
    · rw [if_pos valid] at accepted
      by_cases owner : OwnerGrant stored subject account
      · rw [if_pos owner] at accepted
        by_cases issuer : account = t.asset
        · rw [if_pos issuer] at accepted; cases accepted
        · rw [if_neg issuer] at accepted
          by_cases zero : amount = 0
          · rw [if_pos zero] at accepted; cases accepted
          · rw [if_neg zero] at accepted
            cases purse with
            | none => cases accepted
            | some before =>
              simp only at accepted
              by_cases admitted : (Plan.batch ⟨t.asset, account, amount, gain, before⟩).Admission book
              · rw [if_pos admitted] at accepted
                by_cases balanced : aggregateDelta book ⟨t.asset, account, amount, gain, before⟩ = 0
                · rw [if_pos balanced] at accepted
                  cases accepted
                  exact ⟨⟨t, rfl, valid, rfl⟩, owner, issuer, Nat.pos_of_ne_zero zero, rfl, rfl, rfl,
                    rfl, admitted, balanced⟩
                · rw [if_neg balanced] at accepted; cases accepted
              · rw [if_neg admitted] at accepted; cases accepted
      · rw [if_neg owner] at accepted; cases accepted
    · rw [if_neg valid] at accepted; cases accepted

/-! ## Book arithmetic of one burn -/

theorem batch_apply (plan : Plan) (book : Book) :
    plan.batch.apply book = (Operation.burn plan.account plan.asset plan.amount).apply book := rfl

/-- The burn's well: it gains exactly the burned amount when the payer is not the well. -/
theorem burn_well (plan : Plan) (book : Book) (notIssuer : plan.account ≠ plan.asset) :
    (plan.batch.apply book).balance plan.asset plan.asset =
      book.balance plan.asset plan.asset + Int.ofNat plan.amount := by
  rw [batch_apply]
  exact burn_returns_to_issuer book plan.account plan.asset plan.amount (Ne.symm notIssuer)

/-- The burn's payer: it loses exactly the burned amount. -/
theorem burn_payer (plan : Plan) (book : Book) (notIssuer : plan.account ≠ plan.asset) :
    (plan.batch.apply book).balance plan.account plan.asset =
      book.balance plan.account plan.asset - Int.ofNat plan.amount := by
  rw [batch_apply]
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?, Book.applyPosting,
    Book.balance, DFinsupp.single_apply, notIssuer, Ne.symm notIssuer, sub_eq_add_neg]

/-- A burn in one asset leaves every other asset's well untouched. -/
theorem burn_other_well (plan : Plan) (book : Book) (well : AssetId) (other : plan.asset ≠ well) :
    (plan.batch.apply book).balance well well = book.balance well well := by
  rw [batch_apply]
  simp [Operation.apply, Operation.posting, Operation.leaseRecord?, Book.applyPosting,
    Book.balance, DFinsupp.single_apply, other, Ne.symm other]

/-- The Book leg's delta: circulating credit falls by exactly the burn. -/
theorem book_delta (plan : Plan) (book : Book) (admitted : plan.batch.Admission book)
    (notIssuer : plan.account ≠ plan.asset) :
    delta book plan .book = -Int.ofNat plan.amount := by
  simp only [delta, circulating]
  rw [Batch.conservation book plan.batch admitted plan.asset, burn_well plan book notIssuer]
  ring

/-- The purse leg's delta: its allowance rises by exactly the gain. -/
theorem purse_delta (plan : Plan) (book : Book) :
    delta book plan .purse = Int.ofNat plan.gain := by
  simp [delta, budget, Plan.after, AgentGrain.refill_after]

theorem aggregateDelta_eq (plan : Plan) (book : Book) (admitted : plan.batch.Admission book)
    (notIssuer : plan.account ≠ plan.asset) :
    aggregateDelta book plan = Int.ofNat plan.gain - Int.ofNat plan.amount := by
  simp only [aggregateDelta, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [book_delta plan book admitted notIssuer, purse_delta]
  ring

/-! ## The theorems of the joint turn -/

/-- **The joint turn balances** (`Commit.aggregateBalanced`): an accepted
refill's two legs sum to zero at the credit coordinate. -/
theorem refill_balanced {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {purse : Option AgentGrain.State}
    {account amount gain : Nat} {plan : Plan}
    (accepted : decideRefill tariff stored subject book purse account amount gain = .ok plan) :
    aggregateDelta book plan = 0 :=
  (decideRefill_ok accepted).2.2.2.2.2.2.2.2.2

/-- **A purse leg claiming more than the burn fails the commit.** Whatever the
Book admits, a gain above the burn leaves the joint delta positive. -/
theorem overclaim_fails_commit (plan : Plan) (book : Book) (admitted : plan.batch.Admission book)
    (notIssuer : plan.account ≠ plan.asset) (overclaim : plan.amount < plan.gain) :
    aggregateDelta book plan ≠ 0 := by
  rw [aggregateDelta_eq plan book admitted notIssuer]
  simp only [Int.ofNat_eq_coe]
  omega

/-- The decision's face of it: a command whose purse leg claims more than its
burn is never accepted. -/
theorem overclaim_refused {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {purse : Option AgentGrain.State}
    {account amount gain : Nat} (overclaim : amount < gain) (plan : Plan) :
    decideRefill tariff stored subject book purse account amount gain ≠ .ok plan := by
  intro accepted
  obtain ⟨⟨t, _, _, asset⟩, _, issuer, _, _, acct, amt, gn, admitted, balanced⟩ :=
    decideRefill_ok accepted
  subst acct amt gn
  exact overclaim_fails_commit plan book admitted issuer overclaim balanced

/-- An accepted refill's purse gain is its burn. -/
theorem refill_gain_is_burn {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {purse : Option AgentGrain.State}
    {account amount gain : Nat} {plan : Plan}
    (accepted : decideRefill tariff stored subject book purse account amount gain = .ok plan) :
    plan.gain = plan.amount := by
  obtain ⟨_, _, issuer, _, _, acct, _, _, admitted, balanced⟩ := decideRefill_ok accepted
  subst acct
  rw [aggregateDelta_eq plan book admitted issuer] at balanced
  simp only [Int.ofNat_eq_coe] at balanced
  omega

/-- **The refill conserves.** The Book's total in the credit asset, well
included, is unchanged; the well recovers the burn; the payer pays it; the
purse's remaining allowance and its budget grow by exactly the burn, and
nothing else about the purse moves. -/
theorem refill_conserves {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {purse : Option AgentGrain.State}
    {account amount gain : Nat} {plan : Plan}
    (accepted : decideRefill tariff stored subject book purse account amount gain = .ok plan) :
    (plan.batch.apply book).totalAsset plan.asset = book.totalAsset plan.asset ∧
      (plan.batch.apply book).balance plan.asset plan.asset =
        book.balance plan.asset plan.asset + Int.ofNat amount ∧
      (plan.batch.apply book).balance account plan.asset =
        book.balance account plan.asset - Int.ofNat amount ∧
      plan.after.remaining = plan.before.remaining + Int.ofNat amount ∧
      budget plan.after = budget plan.before + Int.ofNat amount ∧
      plan.after.generation = plan.before.generation ∧ plan.after.status = plan.before.status ∧
      plan.after.reserved = plan.before.reserved := by
  have gainIsBurn := refill_gain_is_burn accepted
  obtain ⟨_, _, issuer, _, _, acct, amt, _, admitted, _⟩ := decideRefill_ok accepted
  subst acct amt
  refine ⟨Batch.conservation book plan.batch admitted plan.asset, burn_well plan book issuer,
    burn_payer plan book issuer, ?_, ?_, rfl, rfl, rfl⟩
  · simp [Plan.after, AgentGrain.refill_after, gainIsBurn]
  · simp [budget, Plan.after, AgentGrain.refill_after, gainIsBurn]; ring

/-- **A refill requires the owner grant** on the burned account. -/
theorem refill_requires_owner {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {purse : Option AgentGrain.State}
    {account amount gain : Nat} {plan : Plan}
    (accepted : decideRefill tariff stored subject book purse account amount gain = .ok plan) :
    OwnerGrant stored subject account :=
  (decideRefill_ok accepted).2.1

/-- **A refill requires the balance**: the payer held at least the burn. -/
theorem refill_requires_balance {tariff : Option Tariff}
    {stored : Option (StoredCapability .account)} {subject : SubjectId} {book : Book}
    {purse : Option AgentGrain.State} {account amount gain : Nat} {plan : Plan}
    (accepted : decideRefill tariff stored subject book purse account amount gain = .ok plan) :
    Int.ofNat amount ≤ book.balance account plan.asset := by
  obtain ⟨_, _, _, _, _, acct, amt, _, admitted, _⟩ := decideRefill_ok accepted
  subst acct amt
  have solvent := admitted.2.1.1.sourceSolvent
  simpa [Plan.batch, registerAccounts, Operation.isIssuerMint, Operation.posting] using solvent

/-! ## The audit statements -/

/-- One purse's history: generic transitions (the installed `transitionPolicy`,
which the generic receiver evaluates) and accepted refills, each refill
recording the burn that funded it. -/
inductive PurseLog : AgentGrain.State → List Nat → AgentGrain.State → Prop
  | nil (s : AgentGrain.State) : PurseLog s [] s
  | transition {before mid after : AgentGrain.State} {burns : List Nat}
      (accepted : AgentGrain.accepts before mid = true)
      (tail : PurseLog mid burns after) : PurseLog before burns after
  | refill {after : AgentGrain.State} {plan : Plan} {burns : List Nat}
      (decided : ∃ tariff stored subject book account amount gain,
        decideRefill tariff stored subject book (some plan.before) account amount gain = .ok plan)
      (tail : PurseLog plan.after burns after) :
      PurseLog plan.before (plan.amount :: burns) after

/-- **The purse never mints.** Along any purse history, its allowance never
exceeds its start plus the burns that funded it: the only increase is a refill,
and a refill's gain is its matching burn (`refill_gain_is_burn`). -/
theorem purse_never_mints {start final : AgentGrain.State} {burns : List Nat}
    (log : PurseLog start burns final) :
    budget final ≤ budget start + (burns.map Int.ofNat).sum := by
  induction log with
  | nil s => simp
  | transition accepted _ induction =>
      have step := AgentGrain.accepted_budget_nonincrease _ _ accepted
      simp only [budget] at induction ⊢
      omega
  | refill decided _ induction =>
      rename_i after plan rest
      obtain ⟨tariff, stored, subject, book, account, amount, gain, decision⟩ := decided
      have grows := (refill_conserves decision).2.2.2.2.1
      obtain ⟨_, _, _, _, _, _, amt, _, _, _⟩ := decideRefill_ok decision
      subst amt
      simp only [List.map_cons, List.sum_cons]
      rw [grows] at induction
      omega

/-! ## Poles, kernel-decided on a concrete Book and purse -/

def fixtureTariff : Tariff := PayTariff.exampleTariff

/-- Account 108 (owner subject 8) holds 60 credits of asset 0; well 0 is at −60. -/
def fixtureBook : Book :=
  ⟨{0, 108}, DFinsupp.single (108, 0) 60 + DFinsupp.single (0, 0) (-60), 0⟩

def ownerCap : StoredCapability .account := PayAssignmentReceiver.ownerCapability 8 108
def fixturePurse : AgentGrain.State := ⟨3, 1, 5, 0⟩

theorem fixture_refill_accepted :
    (decideRefill (some fixtureTariff) (some ownerCap) ⟨8⟩ fixtureBook (some fixturePurse)
      108 50 50 |>.toOption) = some ⟨fixtureTariff.asset, 108, 50, 50, fixturePurse⟩ := by decide +kernel

theorem fixture_overclaim_unbalanced :
    (decideRefill (some fixtureTariff) (some ownerCap) ⟨8⟩ fixtureBook (some fixturePurse)
      108 50 60 |>.toOption) = none := by decide +kernel

theorem fixture_insufficient_refused :
    (decideRefill (some fixtureTariff) (some ownerCap) ⟨8⟩ fixtureBook (some fixturePurse)
      108 61 61 |>.toOption) = none := by decide +kernel

theorem fixture_non_owner_refused :
    (decideRefill (some fixtureTariff) (some ownerCap) ⟨9⟩ fixtureBook (some fixturePurse)
      108 50 50 |>.toOption) = none := by decide +kernel

theorem fixture_issuer_refused :
    (decideRefill (some fixtureTariff) (some (PayAssignmentReceiver.ownerCapability 8 0)) ⟨8⟩
      fixtureBook (some fixturePurse) 0 50 50 |>.toOption) = none := by decide +kernel

theorem fixture_genesis_tariff_refused :
    (decideRefill (some PayTariff.genesisDefault) (some ownerCap) ⟨8⟩ fixtureBook
      (some fixturePurse) 108 50 50 |>.toOption) = none := by decide +kernel

#assert_axioms decideRefill_ok
#assert_axioms burn_well
#assert_axioms burn_payer
#assert_axioms burn_other_well
#assert_axioms book_delta
#assert_axioms purse_delta
#assert_axioms aggregateDelta_eq
#assert_axioms refill_balanced
#assert_axioms overclaim_fails_commit
#assert_axioms overclaim_refused
#assert_axioms refill_gain_is_burn
#assert_axioms refill_conserves
#assert_axioms refill_requires_owner
#assert_axioms refill_requires_balance
#assert_axioms purse_never_mints
#assert_axioms fixture_refill_accepted
#assert_axioms fixture_overclaim_unbalanced
#assert_axioms fixture_insufficient_refused
#assert_axioms fixture_non_owner_refused
#assert_axioms fixture_issuer_refused
#assert_axioms fixture_genesis_tariff_refused
#assert_axioms AgentGrain.refill_accepted_exact
#assert_axioms AgentGrain.refill_edge_accepted
#assert_axioms AgentGrain.policy_mutation_nonincrease_without_refill

end Minidregg.Kernel.PurseRefill
