/-
# Kernel.PayObservationProofs — what an accepted payment report does

* `observation_mints_exactly` / `report_credits_exactly`: the Book after a
  report is the Book before it plus exactly the tariff's credit to each payer.
* `well_tracks_observed`: the audit identity.  Along any log of accepted
  reports, the issuer well of an asset has moved by exactly the credits minted
  in that asset: `−well_h = −well_0 + Σ credited`.
* `overcap_mints_cap`: an observation above the cap mints the cap.
* `heartbeat_advances_clock`, `clock_monotone_by_observation`: every accepted
  report sets the clock to its tip, never behind the clock it replaces.
* `second_credit_refused`: an instance of
  `DurableDataIntent.consumed_nullifier_refused` — once a (signature, address)
  is spent, any report carrying it fails the durable preflight.
* `distinct_address_same_signature_admitted`: one transaction paying two
  deposit addresses is two credits (PAY §10 erratum 1).

Every statement has kernel-decided poles on concrete pay cells and Books.
-/
import Kernel.PayObservationReceiver

namespace Minidregg.Kernel.PayObservationProofs

open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.PayObservation
open Minidregg.Kernel.PayObservationReceiver
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.Store (Patch)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-! ## Book arithmetic of one mint -/

theorem mint_well_balance (book : Book) (asset destination : AccountId) (amount : Nat)
    (well : AssetId) (different : destination ≠ asset) :
    ((Operation.mint asset destination amount).apply book).balance well well =
      book.balance well well - (if asset = well then Int.ofNat amount else 0) := by
  by_cases same : asset = well
  · subst same
    rw [if_pos rfl]
    exact mint_debits_issuer book asset destination amount (Ne.symm different)
  · rw [if_neg same, sub_zero]
    simp [Operation.apply, Operation.posting, Operation.leaseRecord?, Book.applyPosting,
      Book.balance, DFinsupp.single_apply, same]

theorem mint_account_balance (book : Book) (asset destination : AccountId) (amount : Nat)
    (account : AccountId) (notWell : account ≠ asset) :
    ((Operation.mint asset destination amount).apply book).balance account asset =
      book.balance account asset + (if destination = account then Int.ofNat amount else 0) := by
  by_cases same : destination = account
  · subst same
    rw [if_pos rfl]
    exact mint_credits_destination book asset destination amount notWell
  · rw [if_neg same, add_zero]
    simp [Operation.apply, Operation.posting, Operation.leaseRecord?, Book.applyPosting,
      Book.balance, DFinsupp.single_apply, Ne.symm notWell, same]

/-- The mints of a list of credits. -/
def mints (asset : AssetId) (credits : List Credit) : List Operation :=
  credits.map fun credit => .mint asset credit.payer credit.credit

/-- Σ of the credits. -/
def creditSum (credits : List Credit) : Int := (credits.map fun credit => Int.ofNat credit.credit).sum

/-- Σ of the credits to one payer. -/
def creditTo (account : AccountId) (credits : List Credit) : Int :=
  ((credits.filter fun credit => credit.payer = account).map fun credit => Int.ofNat credit.credit).sum

theorem mints_well_balance (asset well : AssetId) :
    ∀ (book : Book) (credits : List Credit), (∀ credit ∈ credits, credit.payer ≠ asset) →
      (applyOperations book (mints asset credits)).balance well well =
        book.balance well well - (if asset = well then creditSum credits else 0)
  | book, [], _ => by simp [mints, applyOperations, creditSum]
  | book, credit :: rest, payers => by
      simp only [mints, List.map_cons, applyOperations]
      rw [show rest.map (fun credit => Operation.mint asset credit.payer credit.credit) =
        mints asset rest from rfl]
      rw [mints_well_balance asset well _ rest (fun c member => payers c (List.mem_cons_of_mem _ member)),
        mint_well_balance book asset credit.payer credit.credit well (payers credit List.mem_cons_self)]
      by_cases same : asset = well
      · simp [same, creditSum]; ring
      · simp [same]

theorem mints_account_balance (asset : AssetId) (account : AccountId) (notWell : account ≠ asset) :
    ∀ (book : Book) (credits : List Credit),
      (applyOperations book (mints asset credits)).balance account asset =
        book.balance account asset + creditTo account credits
  | book, [] => by simp [mints, applyOperations, creditTo]
  | book, credit :: rest => by
      simp only [mints, List.map_cons, applyOperations]
      rw [show rest.map (fun credit => Operation.mint asset credit.payer credit.credit) =
        mints asset rest from rfl]
      rw [mints_account_balance asset account notWell _ rest,
        mint_account_balance book asset credit.payer credit.credit account notWell]
      by_cases same : credit.payer = account
      · simp [same, creditTo]; ring
      · simp [same, creditTo]

theorem Plan.batch_apply (plan : Plan) (book : Book) :
    plan.batch.apply book = applyOperations book (mints plan.tariff.asset plan.credits) := rfl

/-! ## What a decided report's credits are -/

theorem forall₂_right {α β : Type} {R : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ R left right → ∀ b ∈ right, ∃ a ∈ left, R a b
  | _, _, .nil, _, member => by cases member
  | _, _, .cons (a := a) head tail, b, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨a, List.mem_cons_self, head⟩
      · obtain ⟨a', inLeft, related⟩ := forall₂_right tail b later
        exact ⟨a', List.mem_cons_of_mem _ inLeft, related⟩

/-- Every credit of an accepted report pays an assigned payer that is not the
issuer well, the tariff's credit for an observed transfer. -/
theorem decided_credit {store : PayStore} {clock : ClockCell.Clock} {book : Book} {tip : ChainTip}
    {observations : List Observation} {plan : Plan}
    (accepted : decideObservations store clock book tip observations = .ok plan)
    (credit : Credit) (member : credit ∈ plan.credits) :
    ∃ o ∈ observations, assignmentAt store o.index = some credit.payer ∧
      credit.payer ≠ plan.tariff.asset ∧ credit.credit = plan.tariff.creditFor o.amount := by
  obtain ⟨o, inReport, decided⟩ := forall₂_right
    (decideAll_forall₂ (decideObservations_ok accepted).2.2.2.2.2.2.1) credit member
  obtain ⟨-, -, -, -, -, assigned, notWell, -, -, exact⟩ := decideObservation_ok decided
  refine ⟨o, inReport, assigned, notWell, ?_⟩
  rw [exact]

theorem decided_payers {store : PayStore} {clock : ClockCell.Clock} {book : Book} {tip : ChainTip}
    {observations : List Observation} {plan : Plan}
    (accepted : decideObservations store clock book tip observations = .ok plan) :
    ∀ credit ∈ plan.credits, credit.payer ≠ plan.tariff.asset := fun credit member =>
  (decided_credit accepted credit member).elim fun _ facts => facts.2.2.1

/-! ## The mint -/

/-- The credits a decided list pays one account are the tariff's credits for
the observations whose index is assigned to it. -/
theorem creditTo_observed {store : PayStore} {tariff : Tariff} {tip : ChainTip} (account : AccountId) :
    ∀ {observations : List Observation} {credits : List Credit},
      List.Forall₂ (fun o credit => decideObservation store tariff tip o = .ok credit)
        observations credits →
      creditTo account credits =
        ((observations.filter fun o => assignmentAt store o.index = some account).map
          fun o => Int.ofNat (tariff.creditFor o.amount)).sum
  | _, _, .nil => by simp [creditTo]
  | o :: _, credit :: _, .cons head tail => by
      obtain ⟨-, -, -, -, -, assigned, -, -, -, exact⟩ := decideObservation_ok head
      have rest := creditTo_observed account tail
      have iff : assignmentAt store o.index = some account ↔ credit.payer = account := by
        rw [assigned, Option.some.injEq]
      by_cases same : credit.payer = account
      · have mine : assignmentAt store o.index = some account := iff.mpr same
        simp only [creditTo, List.filter_cons, same, mine, decide_true, if_true, List.map_cons,
          List.sum_cons] at rest ⊢
        rw [rest, exact]
      · have other : ¬ assignmentAt store o.index = some account := fun h => same (iff.mp h)
        simp only [creditTo, List.filter_cons, same, other, decide_false] at rest ⊢
        exact rest

/-- **A report credits exactly.**  After an accepted report, every account
other than the issuer well holds its balance plus the tariff's credit for each
observation whose book index is assigned to it. -/
theorem report_credits_exactly (store : PayStore) (clock : ClockCell.Clock) (book : Book)
    (tip : ChainTip) (observations : List Observation) (plan : Plan)
    (accepted : decideObservations store clock book tip observations = .ok plan)
    (account : AccountId) (notWell : account ≠ plan.tariff.asset) :
    (plan.batch.apply book).balance account plan.tariff.asset =
      book.balance account plan.tariff.asset +
        ((observations.filter fun o => assignmentAt store o.index = some account).map
          fun o => Int.ofNat (plan.tariff.creditFor o.amount)).sum := by
  rw [Plan.batch_apply, mints_account_balance plan.tariff.asset account notWell book plan.credits,
    creditTo_observed account (decideAll_forall₂ (decideObservations_ok accepted).2.2.2.2.2.2.1)]

/-- **An accepted observation mints exactly its credit to its payer**: the
account its book index is assigned to gains `creditFor amount` of the tariff's
asset. -/
theorem observation_mints_exactly (store : PayStore) (clock : ClockCell.Clock) (book : Book)
    (tip : ChainTip) (o : Observation)
    (plan : Plan) (accepted : decideObservations store clock book tip [o] = .ok plan) :
    ∃ payer, tariffOf store = some plan.tariff ∧ assignmentAt store o.index = some payer ∧
      payer ≠ plan.tariff.asset ∧
      (plan.batch.apply book).balance payer plan.tariff.asset =
        book.balance payer plan.tariff.asset + Int.ofNat (plan.tariff.creditFor o.amount) := by
  have facts := decideObservations_ok accepted
  have pair := decideAll_forall₂ facts.2.2.2.2.2.2.1
  generalize plan.credits = list at pair
  cases pair with
  | cons head tail =>
    rename_i credit rest
    cases tail
    obtain ⟨-, -, -, -, -, assigned, notWell, -, -, -⟩ := decideObservation_ok head
    refine ⟨credit.payer, facts.1, assigned, notWell, ?_⟩
    rw [report_credits_exactly store clock book tip [o] plan accepted credit.payer notWell]
    simp [assigned]

/-- **The observation cap**: an observation above `maxPerObservation` mints
exactly the cap. -/
theorem overcap_mints_cap {store : PayStore} {tariff : Tariff} {tip : ChainTip} {o : Observation}
    {credit : Credit} (accepted : decideObservation store tariff tip o = .ok credit)
    (aboveCap : tariff.maxPerObservation < o.amount) :
    credit.credit = tariff.maxPerObservation * tariff.creditPerAtomic := by
  obtain ⟨-, -, -, -, -, -, -, -, -, exact⟩ := decideObservation_ok accepted
  rw [exact]
  simp [Tariff.creditFor, Nat.min_eq_right (Nat.le_of_lt aboveCap)]

/-! ## The audit identity -/

/-- A log of accepted reports: each report decided at the Book the previous
ones produced. -/
inductive AcceptedLog : Book → List Plan → Book → Prop
  | nil (book : Book) : AcceptedLog book [] book
  | step {book final : Book} {plan : Plan} {rest : List Plan}
      (decided : ∃ store clock tip observations,
        decideObservations store clock book tip observations = .ok plan)
      (tail : AcceptedLog (plan.batch.apply book) rest final) :
      AcceptedLog book (plan :: rest) final

/-- Σ of the credits a log minted in `asset`. -/
def credited (asset : AssetId) (log : List Plan) : Int :=
  (log.map fun plan => if plan.tariff.asset = asset then creditSum plan.credits else 0).sum

/-- **The well tracks the observed payments.**  Along any log of accepted
reports, `−well_h = −well_0 + Σ credited`: the issuer well of `asset` moves by
exactly the credits minted in `asset`, whatever the tariffs in between. -/
theorem well_tracks_observed {initial final : Book} {log : List Plan}
    (accepted : AcceptedLog initial log final) (asset : AssetId) :
    -(final.balance asset asset) = -(initial.balance asset asset) + credited asset log := by
  induction accepted with
  | nil book => simp [credited]
  | step decided tail induction =>
      rename_i book final plan rest
      obtain ⟨store, clock, tip, observations, decision⟩ := decided
      rw [induction, Plan.batch_apply,
        mints_well_balance plan.tariff.asset asset book plan.credits (decided_payers decision)]
      by_cases same : plan.tariff.asset = asset
      · simp [credited, same]; ring
      · simp [credited, same]

/-! ## The clock (the deployment clock cell, `Kernel.ClockCell`) -/

theorem plan_clock (store : ClockCell.ClockStore) (plan : Plan) :
    ClockCell.clockOf (Patch.run store plan.patch) = some plan.nextClock :=
  Minidregg.Theory.Store.Store.set_eq _ _ _

/-- **An accepted report never moves the clock back**: it was decided at the
clock cell's current value, whose slot is at or before the tip; the clock after
it carries the tip's slot, and its `now` is at least the clock's. -/
theorem clock_monotone_by_observation (store : PayStore) (clock : ClockCell.Clock) (book : Book)
    (tip : ChainTip) (observations : List Observation) (plan : Plan)
    (accepted : decideObservations store clock book tip observations = .ok plan) :
    plan.clock = clock ∧ clock.slot ≤ tip.slot ∧ clock.now ≤ plan.nextClock.now ∧
      plan.nextClock.slot = tip.slot := by
  have facts := decideObservations_ok accepted
  have same : plan.clock = clock := facts.2.1
  refine ⟨same, ?_, ?_, ?_⟩
  · rw [← same]; exact facts.2.2.2.1
  · rw [← same]; exact Nat.le_max_left _ _
  · exact congrArg ChainTip.slot facts.2.2.2.2.2.2.2.1

/-- **A heartbeat advances the clock's slot and mints nothing**, and only once
`minTickSlots` have passed since the clock's slot. -/
theorem heartbeat_advances_clock (store : PayStore) (clock : ClockCell.Clock) (book : Book)
    (tip : ChainTip) (plan : Plan)
    (accepted : decideObservations store clock book tip [] = .ok plan) :
    plan.credits = [] ∧ plan.batch.apply book = book ∧ plan.nextClock.slot = tip.slot ∧
      ∃ tariff, tariffOf store = some tariff ∧ clock.slot + tariff.minTickSlots ≤ tip.slot := by
  have facts := decideObservations_ok accepted
  have empty : plan.credits = [] := by
    have decided := facts.2.2.2.2.2.2.1
    simp only [decideAll, Except.ok.injEq] at decided
    exact decided.symm
  have same : plan.clock = clock := facts.2.1
  refine ⟨empty, ?_, congrArg ChainTip.slot facts.2.2.2.2.2.2.2.1, plan.tariff, facts.1, ?_⟩
  · rw [Plan.batch_apply, empty]; rfl
  · have notSoon := facts.2.2.2.2.1
    simp only [true_and, not_lt] at notSoon
    rw [same] at notSoon
    exact notSoon

/-- A successful empty report retains the exact finalized chain evidence
while the existing heartbeat theorem proves that it mints no credit. -/
theorem heartbeat_retains_chain_tip (store : PayStore) (clock : ClockCell.Clock) (book : Book)
    (tip : ChainTip) (plan : Plan)
    (accepted : decideObservations store clock book tip [] = .ok plan) :
    chainTipOf (Patch.run store (PayChainTip.patch (chainTipOf store) plan.tip)) = some tip := by
  rw [decideObservations_tip accepted]
  exact PayChainTip.patch_tip _ _ _

/-! ## The nullifier -/

/-- Two observations of the same transfer (same signature and address — for
example a watcher's re-report at a later tip) name the same nullifier. -/
theorem same_transfer_same_nullifier (domain : Digest) (left right : Observation)
    (signature : left.signature = right.signature) (address : left.address = right.address) :
    nullifier domain left = nullifier domain right := by
  simp [nullifier, nullifierBytes, signature, address]

/-- **A second credit for the same transfer is refused**: once the transfer's
nullifier is consumed, any accepted report carrying it fails the durable
preflight (an instance of `consumed_nullifier_refused`). -/
theorem second_credit_refused {F : Type} [Field F] [DecidableEq F]
    {deployment : PayObservationReceiver.Deployment}
    {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
    {durable : PayObservationReceiver.Durable} {ingress : DecodedIngress}
    {laws : Minidregg.Kernel.ReceivingLaw.Laws PayObservationReceiver.Durable} {m : Type → Type}
    {oracle : Minidregg.Compiler.CredentialSignatureIO.Oracle m}
    (accepted : ((family deployment profile).receiver laws oracle).Accepted ambient durable ingress)
    (before : DataSnapshot Minidregg.Compiler.ResourceBirthCodec.rootBytes)
    (o : Observation) (member : o ∈ ingress.command.observations)
    (spent : before.model.consumed (nullifier deployment.domain o) = true) :
    (((family deployment profile).receiver laws oracle).intent accepted).preflight before ≠ .ok () :=
  DataIntent.consumed_nullifier_refused before _ _ (intent_spends accepted o member) spent

/-- A second report at a tip slot already spent is refused the same way. -/
theorem second_tick_refused {F : Type} [Field F] [DecidableEq F]
    {deployment : PayObservationReceiver.Deployment}
    {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
    {durable : PayObservationReceiver.Durable} {ingress : DecodedIngress}
    {laws : Minidregg.Kernel.ReceivingLaw.Laws PayObservationReceiver.Durable} {m : Type → Type}
    {oracle : Minidregg.Compiler.CredentialSignatureIO.Oracle m}
    (accepted : ((family deployment profile).receiver laws oracle).Accepted ambient durable ingress)
    (before : DataSnapshot Minidregg.Compiler.ResourceBirthCodec.rootBytes)
    (spent : before.model.consumed (tickNullifier deployment.domain ingress.command.tip) = true) :
    (((family deployment profile).receiver laws oracle).intent accepted).preflight before ≠ .ok () :=
  DataIntent.consumed_nullifier_refused before _ _ (intent_spends_tick accepted) spent

/-! ## Concrete poles (kernel `decide` on real cells and Books) -/

def rowA : Address32 := List.replicate 32 1
def rowB : Address32 := List.replicate 32 2
def rowC : Address32 := List.replicate 32 3
def signature₁ : List UInt8 := List.replicate 64 5
def signature₂ : List UInt8 := List.replicate 64 6

/-- A pay cell with the example tariff (asset 0, cap 10¹⁰, heartbeat 1500),
rows A, B, C at indices 0, 1, 2, index 0 assigned to account 8, index 1 to
account 9, index 2 unassigned, and the genesis clock. -/
def fixtureStore : PayStore :=
  (((((genesisStore.set tariffAddress (some exampleTariff)).set (bookAddress 0) (some rowA)).set
    (bookAddress 1) (some rowB)).set (bookAddress 2) (some rowC)).set
    (assignmentAddress 0) (some (8 : Nat))).set (assignmentAddress 1) (some (9 : Nat))

/-- The same cell with a two-unit cap. -/
def cappedStore : PayStore :=
  fixtureStore.set tariffAddress (some { exampleTariff with maxPerObservation := 2 })

/-- The deployment clock at slot 1000, `now` 1759250000. -/
def tickedClock : ClockCell.Clock := ⟨1759250000, 1000⟩

/-- A Book holding the well 0 and the payers 8 and 9. -/
def fixtureBook : Book := ⟨{0, 8, 9}, 0, 0⟩

def fixtureTip : ChainTip := ⟨1000, 1759250000⟩

def observed (index : Nat) (address : Address32) (signature : List UInt8) (amount : Nat) :
    Observation :=
  ⟨index, address, signature, 900, 1759249950, amount, List.replicate 32 7, List.replicate 32 9,
    .absent⟩

/-- Satisfiable pole: an observation to row A credits account 8. -/
theorem fixture_observation_credited :
    decideObservations fixtureStore ClockCell.genesisClock fixtureBook fixtureTip [observed 0 rowA signature₁ 1000] =
      .ok ⟨exampleTariff, ⟨0, 0⟩, fixtureTip, [⟨0, 8, 1000, 1000⟩]⟩ := by
  decide +kernel

/-- The §10 pole: one transaction paying rows A and B is two credits. -/
theorem distinct_address_same_signature_admitted :
    decideObservations fixtureStore ClockCell.genesisClock fixtureBook fixtureTip
        [observed 0 rowA signature₁ 1000, observed 1 rowB signature₁ 250] =
      .ok ⟨exampleTariff, ⟨0, 0⟩, fixtureTip, [⟨0, 8, 1000, 1000⟩, ⟨1, 9, 250, 250⟩]⟩ ∧
    ∀ domain, nullifier domain (observed 0 rowA signature₁ 1000) ≠
      nullifier domain (observed 1 rowB signature₁ 250) := by
  refine ⟨by decide +kernel, fun domain same => ?_⟩
  have bytes := congrArg StableNullifier.canonicalBytes same
  simp only [nullifier, nullifierBytes, observed, List.append_assoc,
    List.append_cancel_left_eq] at bytes
  exact absurd bytes (by decide)

/-- Refuting pole of the §10 pole: the same transfer twice in one report. -/
theorem duplicate_in_batch_refused :
    decideObservations fixtureStore ClockCell.genesisClock fixtureBook fixtureTip
        [observed 0 rowA signature₁ 1000, observed 0 rowA signature₁ 1000] =
      .error .duplicateInBatch := by
  decide +kernel

/-- A different transfer to the same address is not spent by the first
report: its nullifier's bytes are none of the first report's. -/
theorem fresh_transfer_unspent (domain : Digest) :
    (nullifier domain (observed 0 rowA signature₂ 7)).canonicalBytes ∉
      (nullifiers domain ⟨⟨8⟩, ⟨1⟩, 0, ⟨0⟩, ⟨0⟩, fixtureTip, [observed 0 rowA signature₁ 1000]⟩).map
        StableNullifier.canonicalBytes := by
  change nullifierBytes (observed 0 rowA signature₂ 7) ∉
    [nullifierBytes (observed 0 rowA signature₁ 1000), tickBytes fixtureTip]
  decide +kernel

/-- …while the same transfer re-reported at a later tip is. -/
theorem same_transfer_spent (domain : Digest) :
    nullifier domain (observed 0 rowA signature₁ 1000) ∈
      nullifiers domain ⟨⟨8⟩, ⟨1⟩, 0, ⟨0⟩, ⟨0⟩, fixtureTip, [observed 0 rowA signature₁ 1000]⟩ :=
  List.mem_append_left _ (List.mem_singleton_self _)

theorem wrong_mint_refused :
    decideObservations fixtureStore ClockCell.genesisClock fixtureBook fixtureTip
        [{ observed 0 rowA signature₁ 1000 with mint := List.replicate 32 8 }] =
      .error .wrongMint := by
  decide +kernel

theorem unassigned_index_refused :
    decideObservations fixtureStore ClockCell.genesisClock fixtureBook fixtureTip [observed 2 rowC signature₁ 1000] =
      .error .unassignedIndex := by
  decide +kernel

theorem address_mismatch_refused :
    decideObservations fixtureStore ClockCell.genesisClock fixtureBook fixtureTip [observed 0 rowB signature₁ 1000] =
      .error .addressMismatch := by
  decide +kernel

theorem zero_amount_refused :
    decideObservations fixtureStore ClockCell.genesisClock fixtureBook fixtureTip [observed 0 rowA signature₁ 0] =
      .error .zeroAmount := by
  decide +kernel

/-- A payer the Book does not hold is refused by the Book admission. -/
theorem unknown_payer_refused :
    decideObservations fixtureStore ClockCell.genesisClock ⟨{0, 8}, 0, 0⟩ fixtureTip [observed 1 rowB signature₁ 5] =
      .error .bookAdmission := by
  decide +kernel

/-- Satisfiable pole of the cap: 1000 units against a cap of 2 credit 2. -/
theorem overcap_fixture :
    decideObservations cappedStore ClockCell.genesisClock fixtureBook fixtureTip [observed 0 rowA signature₁ 1000] =
      .ok ⟨{ exampleTariff with maxPerObservation := 2 }, ⟨0, 0⟩, fixtureTip, [⟨0, 8, 1000, 2⟩]⟩ := by
  decide +kernel

/-- Refuting pole of the cap: below it, the credit is the amount. -/
theorem undercap_fixture :
    decideObservations cappedStore ClockCell.genesisClock fixtureBook fixtureTip [observed 0 rowA signature₁ 1] =
      .ok ⟨{ exampleTariff with maxPerObservation := 2 }, ⟨0, 0⟩, fixtureTip, [⟨0, 8, 1, 1⟩]⟩ := by
  decide +kernel

/-- Satisfiable pole of the heartbeat: 1500 slots after the clock. -/
theorem heartbeat_fixture :
    decideObservations fixtureStore tickedClock fixtureBook ⟨2500, 1759251000⟩ [] =
      .ok ⟨exampleTariff, tickedClock, ⟨2500, 1759251000⟩, []⟩ := by
  decide +kernel

/-- Finalized block time is monotone independently of the wall-clock value. -/
theorem finalized_time_regression_refused :
    decideObservations (fixtureStore.set chainTipAddress (some fixtureTip))
      tickedClock fixtureBook ⟨2500, 1759249999⟩ [] =
        .error .tipInvalidOrRegressing := by
  decide +kernel

/-- A finalized slot cannot acquire a different timestamp in a later report. -/
theorem finalized_same_slot_time_mutation_refused :
    decideObservations (fixtureStore.set chainTipAddress (some fixtureTip))
      tickedClock fixtureBook ⟨1000, 1759250001⟩ [observed 0 rowA signature₁ 1000] =
        .error .tipInvalidOrRegressing := by
  decide +kernel

theorem zero_tip_refused :
    decideObservations fixtureStore ClockCell.genesisClock fixtureBook ⟨0, 0⟩ [] =
      .error .tipInvalidOrRegressing := by
  decide +kernel

/-- Empty ingress updates retained evidence after the heartbeat interval. -/
theorem retained_tip_heartbeat_fixture :
    decideObservations (fixtureStore.set chainTipAddress (some fixtureTip))
      tickedClock fixtureBook ⟨2500, 1759251000⟩ [] =
      .ok ⟨exampleTariff, tickedClock, ⟨2500, 1759251000⟩, []⟩ := by
  decide +kernel

/-- Refuting pole: 1499 slots after the clock is too soon. -/
theorem tick_too_soon_refused :
    decideObservations fixtureStore tickedClock fixtureBook ⟨2499, 1759251000⟩ [] = .error .tickTooSoon := by
  decide +kernel

/-- Refuting pole of monotonicity: a tip behind the clock is refused. -/
theorem tip_behind_clock_refused :
    decideObservations fixtureStore tickedClock fixtureBook ⟨999, 1759251000⟩
        [observed 0 rowA signature₁ 1000] = .error .tipBehindClock := by
  decide +kernel

/-- A wall ticker ahead of chain finality does not move backward. A retained
chain tip, when present, independently constrains finalized block time. -/
theorem block_time_behind_now_keeps_now :
    (decideObservations fixtureStore tickedClock fixtureBook ⟨5000, 1759249999⟩ []).map
      Plan.nextClock = .ok ⟨1759250000, 5000⟩ := by
  decide +kernel

/-- …and a later block time moves `now` forward. -/
theorem block_time_ahead_moves_now :
    (decideObservations fixtureStore tickedClock fixtureBook ⟨5000, 1759251000⟩ []).map
      Plan.nextClock = .ok ⟨1759251000, 5000⟩ := by
  decide +kernel

/-- An observation after the tip it is reported at is refused. -/
theorem observation_after_tip_refused :
    decideObservations fixtureStore ClockCell.genesisClock fixtureBook ⟨899, 1759250000⟩ [observed 0 rowA signature₁ 1000] =
      .error .observationAfterTip := by
  decide +kernel

/-- The genesis placeholder tariff credits nothing. -/
theorem genesis_tariff_refused :
    decideObservations (fixtureStore.set tariffAddress (some genesisDefault)) ClockCell.genesisClock fixtureBook fixtureTip
      [observed 0 rowA signature₁ 1000] = .error .tariffInvalid := by
  decide +kernel

/-- Satisfiable pole of the audit identity: two accepted reports (1000 to
account 8, then 1000 + 250 to accounts 8 and 9) move the well by 2250. -/
theorem fixture_log :
    AcceptedLog fixtureBook
      [⟨exampleTariff, ⟨0, 0⟩, fixtureTip, [⟨0, 8, 1000, 1000⟩]⟩,
       ⟨exampleTariff, ⟨0, 0⟩, fixtureTip, [⟨0, 8, 1000, 1000⟩, ⟨1, 9, 250, 250⟩]⟩]
      (Plan.batch ⟨exampleTariff, ⟨0, 0⟩, fixtureTip, [⟨0, 8, 1000, 1000⟩, ⟨1, 9, 250, 250⟩]⟩ |>.apply
        (Plan.batch ⟨exampleTariff, ⟨0, 0⟩, fixtureTip, [⟨0, 8, 1000, 1000⟩]⟩ |>.apply fixtureBook)) := by
  refine .step ⟨fixtureStore, ClockCell.genesisClock, fixtureTip, _, fixture_observation_credited⟩
    (.step ?_ (.nil _))
  refine ⟨fixtureStore, ClockCell.genesisClock, fixtureTip, [observed 0 rowA signature₂ 1000, observed 1 rowB signature₁ 250], ?_⟩
  decide +kernel

theorem fixture_well_moved :
    credited 0 [⟨exampleTariff, ⟨0, 0⟩, fixtureTip, [⟨0, 8, 1000, 1000⟩]⟩,
       ⟨exampleTariff, ⟨0, 0⟩, fixtureTip, [⟨0, 8, 1000, 1000⟩, ⟨1, 9, 250, 250⟩]⟩] = 2250 := by
  decide

/-- Refuting pole of the audit identity: a credit with no debit of the well
(`Book.creditOnly`, which no operation produces) breaks it. -/
theorem credit_only_breaks_audit :
    -((fixtureBook.creditOnly 8 0 1000).balance 0 0) ≠
      -(fixtureBook.balance 0 0) + credited 0 [⟨exampleTariff, ⟨0, 0⟩, fixtureTip, [⟨0, 8, 1000, 1000⟩]⟩] := by
  simp [Book.creditOnly, Book.balance, credited, creditSum, fixtureBook, DFinsupp.single_apply,
    exampleTariff]

#assert_axioms mint_well_balance
#assert_axioms mint_account_balance
#assert_axioms mints_well_balance
#assert_axioms mints_account_balance
#assert_axioms Plan.batch_apply
#assert_axioms forall₂_right
#assert_axioms decided_payers
#assert_axioms plan_clock
#assert_axioms decided_credit
#assert_axioms creditTo_observed
#assert_axioms report_credits_exactly
#assert_axioms observation_mints_exactly
#assert_axioms overcap_mints_cap
#assert_axioms well_tracks_observed
#assert_axioms clock_monotone_by_observation
#assert_axioms heartbeat_advances_clock
#assert_axioms heartbeat_retains_chain_tip
#assert_axioms finalized_time_regression_refused
#assert_axioms finalized_same_slot_time_mutation_refused
#assert_axioms zero_tip_refused
#assert_axioms retained_tip_heartbeat_fixture
#assert_axioms same_transfer_same_nullifier
#assert_axioms second_credit_refused
#assert_axioms second_tick_refused
#assert_axioms fixture_observation_credited
#assert_axioms distinct_address_same_signature_admitted
#assert_axioms duplicate_in_batch_refused
#assert_axioms fresh_transfer_unspent
#assert_axioms same_transfer_spent
#assert_axioms wrong_mint_refused
#assert_axioms unassigned_index_refused
#assert_axioms address_mismatch_refused
#assert_axioms zero_amount_refused
#assert_axioms unknown_payer_refused
#assert_axioms overcap_fixture
#assert_axioms undercap_fixture
#assert_axioms heartbeat_fixture
#assert_axioms tick_too_soon_refused
#assert_axioms tip_behind_clock_refused
#assert_axioms block_time_behind_now_keeps_now
#assert_axioms observation_after_tip_refused
#assert_axioms genesis_tariff_refused
#assert_axioms fixture_log
#assert_axioms fixture_well_moved
#assert_axioms credit_only_breaks_audit

end Minidregg.Kernel.PayObservationProofs
