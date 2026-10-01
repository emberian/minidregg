/-
# Kernel.JobMoney — a job's money: escrow, bond and payout as conservation-checked Book turns
(COMPUTE §2.6, lane C3 K-JOB-MONEY)

A job is one declared object (COMPUTE §2.2).  Its credit is held by the
**Book**, in an account whose id is the job cell's own id (`heldAccount`): the
Book's `held` term.  The job cell's fields `escrow` and `bond` are the law's
view of it, and every money turn keeps the two equal (`held_agrees`).  Three
money edges move it, each one joint turn over the job cell and the Book:

* **fund** (`Move.fund`): the caller moves `price` from its own account into
  the job's held account (state 0, escrow 0 → price); the held account is
  registered fresh in the same turn;
* **claim** (`Move.claim`): a provider moves a bond of at least `price` in and
  takes the job (state 0 → 1; `provider`, `providerAcct`, `bond` written) —
  the bond leg of §2.3's claim edge, in the same turn, so no job is ever
  claimed and unbonded;
* **settle** (`Move.settle`): from a terminal state (3 upheld · 4 slashed ·
  5 void) the job closes (state 6, escrow 0, bond 0) and `payouts` — a pure
  function of the job, never of the command — leave the held account for the
  accounts the job's own fields name.  A slashed bond splits by the tariff
  line `slashCallerPermille` (§9 D4: half to the caller); the rest is burned
  into the well.

A payout can never exceed what the Book holds for the job: the decision
refuses `heldMismatch` unless the held account holds exactly what the cell
says, so a cell that claims credit it was never given pays nothing
(`fixture_forged_held_refused`).  The turn's resource law has three legs at
the credit coordinate (`delta`): circulating credit, the job's held credit,
and the well; they sum to zero (`escrow_conserved`), so
`Δheld + Δcirculating = 0` on fund and claim and `= −retired` on a slash, the
retired credit having gone into the well.

The job cell's FIELDS and its non-money law edges belong to C1 JOB-LAW
(`Kernel/Job.lean` on the mud line).  The field numbers below are C1's
(`deploy/shell/templates/job/fields.json`: escrow 8, provider 9, providerAcct
10, bond 11; there is no `window` field).  `moneyPolicy`
is the slot-gated branch C1's law must carry; `standInLaw` (pinned as
`jobLaw`) is the job law of this branch until C1's lands.
-/
import Kernel.PurseRefill

namespace Minidregg.Kernel.JobMoney

open Minidregg.Compiler
open Minidregg.Kernel
open Minidregg.Kernel.PayTariff
open Minidregg.Kernel.PayCell
open Minidregg.Kernel.PayAssignmentReceiver (OwnerGrant)
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.DeclaredActionLowering
open Minidregg.Theory.Store (Store)
open Minidregg.Pred

set_option autoImplicit false

/-! ## The job cell's money fields (C1 JOB-LAW's `deploy/shell/templates/job/fields.json`) -/

/-- `state`: 0 open · 1 claimed · 2 answered · 3 upheld · 4 slashed · 5 void · 6 closed. -/
def stateField : Nat := 0
def callerField : Nat := 3
def callerAcctField : Nat := 4
def priceField : Nat := 5
def escrowField : Nat := 8
def providerField : Nat := 9
def providerAcctField : Nat := 10
def bondField : Nat := 11

/-- The money view of a job cell.  `provider = 0` means unclaimed. -/
structure Job where
  state : Nat
  caller : Nat
  callerAcct : Nat
  price : Nat
  escrow : Nat
  provider : Nat
  providerAcct : Nat
  bond : Nat
  deriving DecidableEq, Repr

/-- Credit the job holds: owed back out of the well when it closes. -/
def Job.held (j : Job) : Nat := j.escrow + j.bond

/-- The eight money fields, field number first, in the store's canonical
order (fields 3, 4, 5, 8, 9, 10, 11, then 0; see `DeclaredFields`). -/
def Job.fields (j : Job) : List (Nat × Nat) :=
  [(callerField, j.caller), (callerAcctField, j.callerAcct), (priceField, j.price),
   (escrowField, j.escrow), (providerField, j.provider), (providerAcctField, j.providerAcct),
   (bondField, j.bond), (stateField, j.state)]

def Job.values (j : Job) : DeclaredResourceProjection.Values :=
  j.fields.map fun p => (p.1, Int.ofNat p.2)

/-- A field read as a non-negative integer; a negative or absent field is no job. -/
def readField (job field : Nat) (store : Store effectLayout) : Option Nat :=
  match DeclaredFields.read job field store with
  | some (.ofNat n) => some n
  | _ => none

def readJob (job : Nat) (store : Store effectLayout) : Option Job := do
  let read := fun f => readField job f store
  return ⟨← read stateField, ← read callerField, ← read callerAcctField, ← read priceField,
    ← read escrowField, ← read providerField, ← read providerAcctField, ← read bondField⟩

/-- An order's store: the caller, its refund account and the price; nothing
funded, nobody claimed (the stand-in for C1's `order` edge). -/
def ordered (caller callerAcct price : Nat) : Job := ⟨0, caller, callerAcct, price, 0, 0, 0, 0⟩

def initialStore (job caller callerAcct price : Nat) : Store effectLayout :=
  DeclaredFields.store job (ordered caller callerAcct price).values

/-- The money leg as the job's declared writes: every money field compared at
its old value and written at its new one (unchanged fields re-written), so a
job that moved between plan and submission refuses. -/
def actions (job : Nat) (before after : Job) : List Action :=
  (before.fields.zip after.fields).map fun pair =>
    .write (DeclaredFields.key job pair.1.1) (some (Int.ofNat pair.1.2)) (Int.ofNat pair.2.2)

/-! ## Payouts — a pure function of the terminal job (COMPUTE §2.3, last column) -/

structure Payouts where
  /-- Paid to `providerAcct`. -/
  provider : Nat
  /-- Paid to `callerAcct`. -/
  caller : Nat
  /-- Burned into the well (the slashed share of a bond nobody is paid). -/
  retired : Nat
  deriving DecidableEq, Repr

/-- The caller's share of a slashed bond under a split in thousandths, never
more than the bond. -/
def callerShare (split bond : Nat) : Nat := min bond (bond * split / 1000)

/-- 3 upheld: the provider is paid the price (out of the escrow) and gets its
bond back; the caller gets the rest of the escrow.  4 slashed: the caller gets
the escrow and its share of the bond; the rest of the bond is retired into
the well.  5 void: everyone gets back what they put in.  Any other state: no payout. -/
def payouts (split : Nat) (j : Job) : Option Payouts :=
  if j.state = 3 then
    some ⟨min j.price j.escrow + j.bond, j.escrow - min j.price j.escrow, 0⟩
  else if j.state = 4 then
    some ⟨0, j.escrow + callerShare split j.bond, j.bond - callerShare split j.bond⟩
  else if j.state = 5 then
    some ⟨j.bond, j.escrow, 0⟩
  else none

/-! ## The Book holds the job's credit -/

/-- The Book account that holds a job's credit is the job cell's own id
("held under the job cell's id").  The directory gives that id to the job
object, so no account cell — and so no account capability — can exist at it;
`fund` registers it fresh in the Book (`RegistrationAdmission`), and only this
module's moves debit it. -/
def heldAccount (job : Nat) : AccountId := job

/-- The payouts as Book operations out of the held account, one per non-zero
amount: transfers to the payees, and a burn of the retired share into the well. -/
def Payouts.ops (asset job : Nat) (j : Job) (p : Payouts) : List Operation :=
  ([(Operation.transfer job j.providerAcct asset p.provider, p.provider),
    (Operation.transfer job j.callerAcct asset p.caller, p.caller),
    (Operation.burn job asset p.retired, p.retired)].filter fun x => x.2 ≠ 0).map Prod.fst

/-! ## The decided plan and its three legs -/

inductive Move where
  | fund (account amount : Nat)
  | claim (provider account amount : Nat)
  | settle (payouts : Payouts)
  deriving DecidableEq, Repr

structure Plan where
  asset : AssetId
  /-- The job cell's id, which is also its held account. -/
  job : Nat
  before : Job
  move : Move
  deriving DecidableEq, Repr

/-- The job leg: what the money edge writes. -/
def Plan.after (plan : Plan) : Job :=
  match plan.move with
  | .fund _ _ => { plan.before with escrow := plan.before.price }
  | .claim provider account amount =>
      { plan.before with state := 1, provider := provider, providerAcct := account, bond := amount }
  | .settle _ => { plan.before with state := 6, escrow := 0, bond := 0 }

/-- The Book leg: a deposit into the held account (fund registers it), or the
payouts out of it. -/
def Plan.batch (plan : Plan) : Batch :=
  match plan.move with
  | .fund account amount => ⟨[plan.job], [.transfer account plan.job plan.asset amount]⟩
  | .claim _ account amount => ⟨[], [.transfer account plan.job plan.asset amount]⟩
  | .settle p => ⟨[], p.ops plan.asset plan.job plan.before⟩

/-- Credit moved from an account into the job. -/
def Plan.deposited (plan : Plan) : Nat :=
  match plan.move with
  | .fund _ amount => amount
  | .claim _ _ amount => amount
  | .settle _ => 0

/-- Credit paid out of the job to its payees. -/
def Plan.paid (plan : Plan) : Nat :=
  match plan.move with
  | .settle p => p.provider + p.caller
  | _ => 0

/-- Credit the turn burns from the job into the well. -/
def Plan.retired (plan : Plan) : Nat :=
  match plan.move with
  | .settle p => p.retired
  | _ => 0

/-- Credit outside the well and outside this job's held account. -/
def circulating (book : Book) (asset job : Nat) : Int :=
  book.totalAsset asset - book.balance asset asset - book.balance job asset

inductive Leg where
  | book
  | job
  | well
  deriving DecidableEq, Repr

/-- The turn's resource law at the credit coordinate: the change in
circulating credit, the change in what the job cell says it holds, and the
change in the well.  The Book conserves circulating + Book-held + well, so
their sum is zero exactly when the job cell moved with its Book account. -/
def delta (book : Book) (plan : Plan) : Leg → Int
  | .book => circulating (plan.batch.apply book) plan.asset plan.job -
      circulating book plan.asset plan.job
  | .job => Int.ofNat plan.after.held - Int.ofNat plan.before.held
  | .well => (plan.batch.apply book).balance plan.asset plan.asset - book.balance plan.asset plan.asset

def aggregateDelta (book : Book) (plan : Plan) : Int :=
  ([Leg.book, Leg.job, Leg.well].map (delta book plan)).sum

/-! ## Refusals -/

inductive Reject where
  | malformedIngress | directoryUnavailable | authorityUnavailable | payUnavailable
  | bookUnavailable | jobUnavailable | jobLawUnavailable | notJobLaw
  | staleAuthority
  | tariffInvalid | jobUnreadable | unknownAction | jobIsIssuer
  | notOpen | notCaller | notOwner | wrongAccount | payerIsIssuer | payerIsHeld | zeroAmount
  | alreadyFunded | heldAccountTaken
  | notFunded | alreadyClaimed | noProvider | bondBelowPrice | insufficientBalance | heldMismatch
  | notTerminal | alreadySettled | badPayee | bookRefused | unbalanced
  | jobRefused
  | jobCell (reason : DeclaredResourceScalar.Reject)
  | replayedMarker | validation | physicalPreparation
  | policyUnavailable | capabilityRejected | policyRejected | policyInputRange | policyCastAlias
  | signature (reason : CredentialSignatureAdmission.Reject)
  deriving Repr

/-! ## The pure decisions -/

/-- The Book admits the leg and the three legs balance. -/
def commit (book : Book) (plan : Plan) (refused : Reject) : Except Reject Plan :=
  if plan.batch.Admission book then
    if aggregateDelta book plan = 0 then .ok plan else .error .unbalanced
  else .error refused

theorem commit_ok {book : Book} {candidate plan : Plan} {refused : Reject}
    (accepted : commit book candidate refused = .ok plan) :
    plan = candidate ∧ plan.batch.Admission book ∧ aggregateDelta book plan = 0 := by
  unfold commit at accepted
  split_ifs at accepted with admitted balanced
  cases accepted
  exact ⟨rfl, admitted, balanced⟩

/-- **Fund**: the job's caller deposits the price from the job's refund
account into the job's (fresh) held account. -/
def decideFund (t : Tariff) (stored : Option (StoredCapability .account)) (subject : SubjectId)
    (book : Book) (job : Nat) (j : Job) (account amount : Nat) : Except Reject Plan :=
  if j.state ≠ 0 then .error .notOpen
  else if subject.value ≠ j.caller then .error .notCaller
  else if ¬ OwnerGrant stored subject account then .error .notOwner
  else if account ≠ j.callerAcct then .error .wrongAccount
  else if account = t.asset then .error .payerIsIssuer
  else if account = job then .error .payerIsHeld
  else if amount = 0 then .error .zeroAmount
  else if j.escrow ≠ 0 ∨ j.bond ≠ 0 then .error .alreadyFunded
  else if job ∈ book.accounts then .error .heldAccountTaken
  else commit book ⟨t.asset, job, j, .fund account amount⟩ .insufficientBalance

/-- **Claim**: a provider bonds at least the price and takes a funded, open job. -/
def decideClaim (t : Tariff) (stored : Option (StoredCapability .account)) (subject : SubjectId)
    (book : Book) (job : Nat) (j : Job) (account amount : Nat) : Except Reject Plan :=
  if j.state ≠ 0 then .error .notOpen
  else if j.price = 0 ∨ j.escrow ≠ j.price then .error .notFunded
  else if j.provider ≠ 0 ∨ j.bond ≠ 0 then .error .alreadyClaimed
  else if subject.value = 0 then .error .noProvider
  else if ¬ OwnerGrant stored subject account then .error .notOwner
  else if account = t.asset then .error .payerIsIssuer
  else if account = job then .error .payerIsHeld
  else if amount < j.price then .error .bondBelowPrice
  else if book.balance job t.asset ≠ Int.ofNat j.held then .error .heldMismatch
  else commit book ⟨t.asset, job, j, .claim subject.value account amount⟩ .insufficientBalance

/-- A payee of a non-zero payout is neither the well nor the job's own account. -/
def Payouts.badPayee (asset job : Nat) (j : Job) (p : Payouts) : Prop :=
  (p.provider ≠ 0 ∧ (j.providerAcct = asset ∨ j.providerAcct = job)) ∨
    (p.caller ≠ 0 ∧ (j.callerAcct = asset ∨ j.callerAcct = job))

instance (asset job : Nat) (j : Job) (p : Payouts) : Decidable (p.badPayee asset job j) := by
  unfold Payouts.badPayee; infer_instance

/-- **Settle**: a terminal job closes and its payouts leave its held account. -/
def decideSettle (t : Tariff) (book : Book) (job : Nat) (j : Job) : Except Reject Plan :=
  if j.state = 6 then .error .alreadySettled
  else match payouts t.slashCallerPermille j with
    | none => .error .notTerminal
    | some p =>
      if p.badPayee t.asset job j then .error .badPayee
      else if book.balance job t.asset ≠ Int.ofNat j.held then .error .heldMismatch
      else commit book ⟨t.asset, job, j, .settle p⟩ .bookRefused

def fundAction : Nat := 1
def claimAction : Nat := 2
def settleAction : Nat := 3

/-- One money command on job cell `job`: a valid tariff (its `asset` is the
credit), a job that is not the well, a readable job, then the action's own
decision.  A settle carries no account and no amount: the payouts come from
the job, never from the command. -/
def decideMoney (tariff : Option Tariff) (stored : Option (StoredCapability .account))
    (subject : SubjectId) (book : Book) (job : Nat) (j : Option Job)
    (action account amount : Nat) : Except Reject Plan :=
  match tariff with
  | none => .error .tariffInvalid
  | some t =>
    if t.valid then
      if job = t.asset then .error .jobIsIssuer
      else match j with
      | none => .error .jobUnreadable
      | some j =>
        if action = fundAction then decideFund t stored subject book job j account amount
        else if action = claimAction then decideClaim t stored subject book job j account amount
        else if action = settleAction ∧ account = 0 ∧ amount = 0 then decideSettle t book job j
        else .error .unknownAction
    else .error .tariffInvalid

/-! ## What an accepted decision establishes -/

theorem decideFund_ok {t : Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {j : Job} {account amount : Nat} {plan : Plan}
    (accepted : decideFund t stored subject book job j account amount = .ok plan) :
    plan = ⟨t.asset, job, j, .fund account amount⟩ ∧ j.state = 0 ∧ subject.value = j.caller ∧
      OwnerGrant stored subject account ∧ account = j.callerAcct ∧ account ≠ t.asset ∧
      account ≠ job ∧ 0 < amount ∧ j.escrow = 0 ∧ j.bond = 0 ∧ job ∉ book.accounts ∧
      plan.batch.Admission book ∧ aggregateDelta book plan = 0 := by
  unfold decideFund at accepted
  split_ifs at accepted with h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨rfl, admitted, balanced⟩ := commit_ok accepted
  exact ⟨rfl, by omega, by omega, by simpa using h3, by omega, h5, h6, by omega, by omega,
    by omega, h9, admitted, balanced⟩

theorem decideClaim_ok {t : Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {j : Job} {account amount : Nat} {plan : Plan}
    (accepted : decideClaim t stored subject book job j account amount = .ok plan) :
    plan = ⟨t.asset, job, j, .claim subject.value account amount⟩ ∧ j.state = 0 ∧
      0 < j.price ∧ j.escrow = j.price ∧ j.provider = 0 ∧ j.bond = 0 ∧ subject.value ≠ 0 ∧
      OwnerGrant stored subject account ∧ account ≠ t.asset ∧ account ≠ job ∧ j.price ≤ amount ∧
      book.balance job t.asset = Int.ofNat j.held ∧
      plan.batch.Admission book ∧ aggregateDelta book plan = 0 := by
  unfold decideClaim at accepted
  split_ifs at accepted with h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨rfl, admitted, balanced⟩ := commit_ok accepted
  exact ⟨rfl, by omega, by omega, by omega, by omega, by omega, h4, by simpa using h5, h6, h7,
    by omega, by simpa using h9, admitted, balanced⟩

theorem decideSettle_ok {t : Tariff} {book : Book} {job : Nat} {j : Job} {plan : Plan}
    (accepted : decideSettle t book job j = .ok plan) :
    ∃ p, payouts t.slashCallerPermille j = some p ∧ plan = ⟨t.asset, job, j, .settle p⟩ ∧
      j.state ≠ 6 ∧ ¬ p.badPayee t.asset job j ∧ book.balance job t.asset = Int.ofNat j.held ∧
      plan.batch.Admission book ∧ aggregateDelta book plan = 0 := by
  unfold decideSettle at accepted
  by_cases h1 : j.state = 6
  · simp [h1] at accepted
  · rw [if_neg h1] at accepted
    cases hp : payouts t.slashCallerPermille j with
    | none => simp [hp] at accepted
    | some p =>
      rw [hp] at accepted
      simp only at accepted
      by_cases h2 : p.badPayee t.asset job j
      · rw [if_pos h2] at accepted; cases accepted
      · rw [if_neg h2] at accepted
        by_cases h3 : book.balance job t.asset ≠ Int.ofNat j.held
        · rw [if_pos h3] at accepted; cases accepted
        · rw [if_neg h3] at accepted
          obtain ⟨rfl, admitted, balanced⟩ := commit_ok accepted
          exact ⟨p, rfl, rfl, h1, h2, by simpa using h3, admitted, balanced⟩

/-- Which action an accepted command took, with everything it establishes. -/
theorem decideMoney_ok {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {jo : Option Job} {action account amount : Nat}
    {plan : Plan}
    (accepted : decideMoney tariff stored subject book job jo action account amount = .ok plan) :
    ∃ t j, tariff = some t ∧ t.valid ∧ job ≠ t.asset ∧ jo = some j ∧ plan.asset = t.asset ∧
      plan.job = job ∧ plan.before = j ∧
      ((action = fundAction ∧ decideFund t stored subject book job j account amount = .ok plan) ∨
       (action = claimAction ∧ decideClaim t stored subject book job j account amount = .ok plan) ∨
       (action = settleAction ∧ account = 0 ∧ amount = 0 ∧
         decideSettle t book job j = .ok plan)) := by
  unfold decideMoney at accepted
  rcases tariff with _ | t
  · cases accepted
  · rcases jo with _ | j
    · simp only at accepted
      split_ifs at accepted
    · simp only at accepted
      split_ifs at accepted with valid issuer fund claim settle
      · obtain ⟨rfl, -⟩ := decideFund_ok accepted
        exact ⟨t, j, rfl, valid, issuer, rfl, rfl, rfl, rfl, Or.inl ⟨fund, accepted⟩⟩
      · obtain ⟨rfl, -⟩ := decideClaim_ok accepted
        exact ⟨t, j, rfl, valid, issuer, rfl, rfl, rfl, rfl, Or.inr (Or.inl ⟨claim, accepted⟩)⟩
      · obtain ⟨p, -, rfl, -⟩ := decideSettle_ok accepted
        exact ⟨t, j, rfl, valid, issuer, rfl, rfl, rfl, rfl,
          Or.inr (Or.inr ⟨settle.1, settle.2.1, settle.2.2, accepted⟩)⟩

/-! ## Payout arithmetic -/

theorem callerShare_le (split bond : Nat) : callerShare split bond ≤ bond := Nat.min_le_left _ _

/-- **Every payout vector sums to what the job held.** -/
theorem payouts_sum {split : Nat} {j : Job} {p : Payouts} (paid : payouts split j = some p) :
    p.provider + p.caller + p.retired = j.held := by
  unfold payouts at paid
  have share := callerShare_le split j.bond
  have least := Nat.min_le_right j.price j.escrow
  split_ifs at paid <;> cases paid <;> simp only [Job.held] <;> omega

/-- **The slashed bond splits exactly**: the caller's share plus the retired
rest is the bond, and the caller's share is the tariff's split of it. -/
theorem slash_split_sums_to_bond {split : Nat} {j : Job} (slashed : j.state = 4) :
    ∃ p, payouts split j = some p ∧ p.provider = 0 ∧
      p.caller = j.escrow + callerShare split j.bond ∧
      callerShare split j.bond + p.retired = j.bond := by
  refine ⟨⟨0, j.escrow + callerShare split j.bond, j.bond - callerShare split j.bond⟩, ?_, rfl,
    rfl, ?_⟩
  · simp [payouts, slashed]
  · have := callerShare_le split j.bond
    simp only
    omega

/-- At the default split (500‰) a slashed bond is halved: the caller gets ⌊bond/2⌋. -/
theorem half_split (bond : Nat) : callerShare 500 bond = bond / 2 := by
  unfold callerShare
  omega

/-- **The provider is paid iff the job was upheld** (reached state 3 unchallenged
past its window, or by a truth equal to its output — C1's `decide → 3`): only
then does it receive more than its own bond back, and then it receives exactly
`price + bond` out of a funded escrow. -/
theorem provider_paid_iff_unchallenged_or_upheld {split : Nat} {j : Job} {p : Payouts}
    (paid : payouts split j = some p) (funded : j.price ≤ j.escrow) (priced : 0 < j.price) :
    (j.bond < p.provider ↔ j.state = 3) ∧ (j.state = 3 → p.provider = j.price + j.bond) := by
  unfold payouts at paid
  split_ifs at paid with h3 h4 h5 <;> cases paid <;> simp only
  · rw [Nat.min_eq_left funded]
    exact ⟨⟨fun _ => h3, fun _ => by omega⟩, fun _ => by omega⟩
  · exact ⟨⟨fun lt => by omega, fun s => by omega⟩, fun s => by omega⟩
  · exact ⟨⟨fun lt => by omega, fun s => by omega⟩, fun s => by omega⟩

/-- A job is terminal for settlement exactly in states 3, 4 and 5. -/
theorem payouts_isSome_iff (split : Nat) (j : Job) :
    (payouts split j).isSome ↔ (j.state = 3 ∨ j.state = 4 ∨ j.state = 5) := by
  unfold payouts
  split_ifs <;> simp_all

/-! ## The Book leg's arithmetic -/

/-- What one posting does to one balance. -/
def flowIn (a : AccountId) (asset : AssetId) (op : Operation) : Int :=
  (if a = op.posting.destination ∧ asset = op.posting.asset then Int.ofNat op.posting.amount
    else 0) -
  (if a = op.posting.source ∧ asset = op.posting.asset then Int.ofNat op.posting.amount else 0)

theorem applyPosting_balance (book : Book) (p : Minidregg.Theory.CanonicalResourceKernel.Posting) (a : AccountId) (asset : AssetId) :
    (book.applyPosting p).balance a asset =
      book.balance a asset +
        ((if a = p.destination ∧ asset = p.asset then Int.ofNat p.amount else 0) -
          (if a = p.source ∧ asset = p.asset then Int.ofNat p.amount else 0)) := by
  unfold Book.applyPosting Book.balance
  simp only [DFinsupp.add_apply, DFinsupp.single_apply, Prod.mk.injEq]
  by_cases hA : asset = p.asset
  · subst hA
    by_cases hS : a = p.source <;> by_cases hD : a = p.destination
    · subst hS; simp [← hD]
    · subst hS; simp [hD, Ne.symm hD]
    · subst hD; simp [hS, Ne.symm hS]
    · simp [hS, hD, Ne.symm hS, Ne.symm hD]
  · simp [hA, Ne.symm hA]

/-- Operations without a lease record. -/
def plainOp : Operation → Prop
  | .lease .. => False
  | _ => True

theorem apply_balance (op : Operation) (plain : plainOp op) (book : Book) (a : AccountId)
    (asset : AssetId) :
    (op.apply book).balance a asset = book.balance a asset + flowIn a asset op := by
  cases op <;> simp only [plainOp] at plain <;>
    simp [Operation.apply, Operation.leaseRecord?, applyPosting_balance, flowIn]

theorem applyOperations_balance (book : Book) (ops : List Operation)
    (plain : ∀ op ∈ ops, plainOp op) (a : AccountId) (asset : AssetId) :
    (applyOperations book ops).balance a asset =
      book.balance a asset + (ops.map (flowIn a asset)).sum := by
  induction ops generalizing book with
  | nil => simp [applyOperations]
  | cons op rest ih =>
      simp only [applyOperations, List.map_cons, List.sum_cons]
      rw [ih _ (fun o m => plain o (List.mem_cons_of_mem _ m)),
        apply_balance op (plain op List.mem_cons_self)]
      ring

theorem registerAccounts_balance (book : Book) (accounts : List AccountId) (a : AccountId)
    (asset : AssetId) : (registerAccounts book accounts).balance a asset = book.balance a asset := by
  induction accounts generalizing book with
  | nil => rfl
  | cons account rest ih => exact ih _

theorem ops_plain (asset job : Nat) (j : Job) (p : Payouts) : ∀ op ∈ p.ops asset job j, plainOp op := by
  intro op member
  simp only [Payouts.ops, List.mem_map, List.mem_filter, List.mem_cons, List.mem_nil_iff,
    or_false] at member
  obtain ⟨x, ⟨rfl | rfl | rfl, -⟩, rfl⟩ := member <;> simp [plainOp]

/-- Filtering out zero-amount operations changes no balance. -/
theorem ops_flow (asset job : Nat) (j : Job) (p : Payouts) (a : AccountId) (asset' : AssetId) :
    ((p.ops asset job j).map (flowIn a asset')).sum =
      flowIn a asset' (.transfer job j.providerAcct asset p.provider) +
        flowIn a asset' (.transfer job j.callerAcct asset p.caller) +
        flowIn a asset' (.burn job asset p.retired) := by
  unfold Payouts.ops
  by_cases a1 : p.provider = 0 <;> by_cases a2 : p.caller = 0 <;> by_cases a3 : p.retired = 0 <;>
    simp [a1, a2, a3, flowIn, Operation.posting] <;> ring

/-- Every plan's Book leg, as one sum of flows. -/
theorem plan_balance (plan : Plan) (book : Book) (a : AccountId) (asset : AssetId) :
    (plan.batch.apply book).balance a asset =
      book.balance a asset +
        match plan.move with
        | .fund account amount => flowIn a asset (.transfer account plan.job plan.asset amount)
        | .claim _ account amount => flowIn a asset (.transfer account plan.job plan.asset amount)
        | .settle p => flowIn a asset (.transfer plan.job plan.before.providerAcct plan.asset p.provider) +
            flowIn a asset (.transfer plan.job plan.before.callerAcct plan.asset p.caller) +
            flowIn a asset (.burn plan.job plan.asset p.retired) := by
  obtain ⟨asset₀, job, before, move⟩ := plan
  cases move with
  | fund account amount =>
      simp only [Plan.batch, Batch.apply]
      rw [applyOperations_balance _ _ (by simp [plainOp]), registerAccounts_balance]
      simp
  | claim provider account amount =>
      simp only [Plan.batch, Batch.apply, registerAccounts]
      rw [applyOperations_balance _ _ (by simp [plainOp])]
      simp
  | settle p =>
      simp only [Plan.batch, Batch.apply, registerAccounts]
      rw [applyOperations_balance _ _ (ops_plain _ _ _ _), ops_flow]

/-! ## Conservation -/

/-- What an accepted command's plan satisfies, whichever action it took. -/
theorem decideMoney_plan {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {jo : Option Job} {action account amount : Nat}
    {plan : Plan}
    (accepted : decideMoney tariff stored subject book job jo action account amount = .ok plan) :
    plan.batch.Admission book ∧ aggregateDelta book plan = 0 ∧ plan.job ≠ plan.asset ∧
      plan.job = job ∧
      (match plan.move with
       | .fund account _ => account ≠ plan.asset ∧ account ≠ plan.job ∧
           book.balance plan.job plan.asset = Int.ofNat plan.before.held
       | .claim _ account _ => account ≠ plan.asset ∧ account ≠ plan.job ∧
           book.balance plan.job plan.asset = Int.ofNat plan.before.held
       | .settle p => ¬ p.badPayee plan.asset plan.job plan.before ∧
           book.balance plan.job plan.asset = Int.ofNat plan.before.held) := by
  obtain ⟨t, j, -, -, issuer, -, -, -, -, branch⟩ := decideMoney_ok accepted
  rcases branch with ⟨-, fund⟩ | ⟨-, claim⟩ | ⟨-, -, -, settle⟩
  · obtain ⟨rfl, -, -, -, -, payer, held, -, escrow, bond, fresh, admitted, balanced⟩ :=
      decideFund_ok fund
    refine ⟨admitted, balanced, issuer, rfl, payer, held, ?_⟩
    have absent := admitted.1
    simp only [Plan.batch, RegistrationsAdmitted, RegistrationAdmission] at absent
    have zero : book.balance job t.asset = 0 := by
      by_contra nonzero
      exact absent.1.2 (job, t.asset) (DFinsupp.mem_support_iff.mpr nonzero) rfl
    simp [zero, Job.held, escrow, bond]
  · obtain ⟨rfl, -, -, -, -, -, -, -, payer, held, -, agrees, admitted, balanced⟩ :=
      decideClaim_ok claim
    exact ⟨admitted, balanced, issuer, rfl, payer, held, agrees⟩
  · obtain ⟨p, -, rfl, -, payees, agrees, admitted, balanced⟩ := decideSettle_ok settle
    exact ⟨admitted, balanced, issuer, rfl, payees, agrees⟩

/-- The well's change: only a slash's retired share reaches it. -/
theorem well_after {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {jo : Option Job} {action account amount : Nat}
    {plan : Plan}
    (accepted : decideMoney tariff stored subject book job jo action account amount = .ok plan)
    (well : AssetId) :
    (plan.batch.apply book).balance well well =
      book.balance well well + (if plan.asset = well then Int.ofNat plan.retired else 0) := by
  obtain ⟨-, -, issuer, -, facts⟩ := decideMoney_plan accepted
  rw [plan_balance]
  obtain ⟨asset, job', before, move⟩ := plan
  simp only at issuer facts ⊢
  cases move with
  | fund a n =>
      obtain ⟨payer, -, -⟩ := facts
      by_cases same : asset = well
      · subst same; simp [flowIn, Operation.posting, Plan.retired, Ne.symm payer, Ne.symm issuer]
      · simp [flowIn, Operation.posting, Plan.retired, same, Ne.symm same]
  | claim pr a n =>
      obtain ⟨payer, -, -⟩ := facts
      by_cases same : asset = well
      · subst same; simp [flowIn, Operation.posting, Plan.retired, Ne.symm payer, Ne.symm issuer]
      · simp [flowIn, Operation.posting, Plan.retired, same, Ne.symm same]
  | settle p =>
      obtain ⟨payees, -⟩ := facts
      simp only [Payouts.badPayee, not_or, not_and, not_not] at payees
      by_cases same : asset = well
      · subst same
        by_cases a1 : p.provider = 0 <;> by_cases a2 : p.caller = 0 <;>
          simp_all [flowIn, Operation.posting, Plan.retired, Ne.symm issuer, eq_comm]
      · simp [flowIn, Operation.posting, Plan.retired, same, Ne.symm same]

/-- **The Book and the job cell agree**: after an accepted money turn the
job's held account holds exactly what the job cell says it holds. -/
theorem held_agrees {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {jo : Option Job} {action account amount : Nat}
    {plan : Plan}
    (accepted : decideMoney tariff stored subject book job jo action account amount = .ok plan) :
    (plan.batch.apply book).balance plan.job plan.asset = Int.ofNat plan.after.held := by
  obtain ⟨admitted, balanced, -, -, facts⟩ := decideMoney_plan accepted
  have before : book.balance plan.job plan.asset = Int.ofNat plan.before.held := by
    obtain ⟨asset, job', b, move⟩ := plan
    cases move <;> simp only at facts ⊢ <;> first | exact facts.2.2 | exact facts.2
  have total := Batch.conservation book plan.batch admitted plan.asset
  simp only [aggregateDelta, delta, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    circulating] at balanced
  rw [total] at balanced
  simp only [Int.ofNat_eq_natCast] at balanced before ⊢
  omega

/-- **Escrow is conserved** (COMPUTE §2.6's rule): every accepted fund, claim
or settle leaves the Book's total in the credit asset (well included)
unchanged; the change in the job's held credit, the change in circulating
credit and the change in the well sum to zero; the well moves only by a
slash's retired share — so `Δheld + Δcirculating = 0` on fund and claim, and
`= −retired` on a slash, the retired credit having gone into the well. -/
theorem escrow_conserved {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {jo : Option Job} {action account amount : Nat}
    {plan : Plan}
    (accepted : decideMoney tariff stored subject book job jo action account amount = .ok plan) :
    (plan.batch.apply book).totalAsset plan.asset = book.totalAsset plan.asset ∧
      (Int.ofNat plan.after.held - Int.ofNat plan.before.held) +
        (circulating (plan.batch.apply book) plan.asset plan.job -
          circulating book plan.asset plan.job) + Int.ofNat plan.retired = 0 ∧
      (plan.batch.apply book).balance plan.asset plan.asset =
        book.balance plan.asset plan.asset + Int.ofNat plan.retired ∧
      (action ≠ settleAction → plan.retired = 0) := by
  obtain ⟨admitted, balanced, -, -, -⟩ := decideMoney_plan accepted
  have well := well_after accepted plan.asset
  rw [if_pos rfl] at well
  refine ⟨Batch.conservation book plan.batch admitted plan.asset, ?_, well, ?_⟩
  · simp only [aggregateDelta, delta, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at balanced
    linarith
  · intro notSettle
    obtain ⟨t, j, -, -, -, -, -, -, -, branch⟩ := decideMoney_ok accepted
    rcases branch with ⟨-, fund⟩ | ⟨-, claim⟩ | ⟨settle, -⟩
    · obtain ⟨rfl, -⟩ := decideFund_ok fund; rfl
    · obtain ⟨rfl, -⟩ := decideClaim_ok claim; rfl
    · exact absurd settle notSettle

/-- The fund's exact effect: the deposit is the price, and the job (cell and
Book alike) now holds exactly it. -/
theorem fund_holds_price {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {jo : Option Job} {account amount : Nat}
    {plan : Plan}
    (accepted : decideMoney tariff stored subject book job jo fundAction account amount = .ok plan) :
    amount = plan.before.price ∧ plan.after.held = amount := by
  have agrees := held_agrees accepted
  obtain ⟨-, -, -, -, facts⟩ := decideMoney_plan accepted
  obtain ⟨t, j, -, -, -, -, -, -, -, branch⟩ := decideMoney_ok accepted
  rcases branch with ⟨-, fund⟩ | ⟨bad, -⟩ | ⟨bad, -⟩
  · obtain ⟨rfl, -, -, -, -, -, own, -, escrow, bond, -⟩ := decideFund_ok fund
    obtain ⟨-, -, before⟩ := facts
    rw [plan_balance] at agrees
    simp only [Plan.after, Job.held, escrow, bond, flowIn, Operation.posting] at agrees before ⊢
    simp [Ne.symm own] at agrees
    simp only [Int.ofNat_eq_natCast] at agrees before
    omega
  · exact absurd bad (by decide)
  · exact absurd bad (by decide)

/-! ## Who may move the money -/

/-- **A fund requires the caller**: the signer is the job's caller, holds the
owner grant on the account it pays from, and that account is the job's refund
account; the job held nothing and its held account did not exist. -/
theorem fund_requires_caller {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {jo : Option Job} {account amount : Nat}
    {plan : Plan}
    (accepted : decideMoney tariff stored subject book job jo fundAction account amount = .ok plan) :
    ∃ j, jo = some j ∧ subject.value = j.caller ∧ OwnerGrant stored subject account ∧
      account = j.callerAcct ∧ j.held = 0 ∧ job ∉ book.accounts := by
  obtain ⟨t, j, -, -, -, rfl, -, -, -, branch⟩ := decideMoney_ok accepted
  rcases branch with ⟨-, fund⟩ | ⟨bad, -⟩ | ⟨bad, -⟩
  · obtain ⟨-, -, caller, owner, acct, -, -, -, escrow, bond, fresh, -⟩ := decideFund_ok fund
    exact ⟨j, rfl, caller, owner, acct, by simp [Job.held, escrow, bond], fresh⟩
  · exact absurd bad (by decide)
  · exact absurd bad (by decide)

/-- **A claim requires a funded, open, unclaimed job and a bond of at least
the price** (COMPUTE §9 D3), paid from an account the signer owns. -/
theorem claim_requires_bond {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {jo : Option Job} {account amount : Nat}
    {plan : Plan}
    (accepted : decideMoney tariff stored subject book job jo claimAction account amount = .ok plan) :
    ∃ j, jo = some j ∧ j.state = 0 ∧ j.escrow = j.price ∧ j.provider = 0 ∧
      OwnerGrant stored subject account ∧ j.price ≤ amount ∧
      plan.after.provider = subject.value ∧ plan.after.providerAcct = account ∧
      plan.after.bond = amount := by
  obtain ⟨t, j, -, -, -, rfl, -, -, -, branch⟩ := decideMoney_ok accepted
  rcases branch with ⟨bad, -⟩ | ⟨-, claim⟩ | ⟨bad, -⟩
  · exact absurd bad (by decide)
  · obtain ⟨rfl, state, -, escrow, provider, -, -, owner, -, -, bond, -⟩ := decideClaim_ok claim
    exact ⟨j, rfl, state, escrow, provider, owner, bond, rfl, rfl, rfl⟩
  · exact absurd bad (by decide)

/-- **A settle requires a terminal job**: it starts in state 3, 4 or 5, pays
exactly `payouts` of that job, and leaves the job closed and empty — in the
cell and in the Book. -/
theorem settle_requires_terminal {tariff : Option Tariff}
    {stored : Option (StoredCapability .account)} {subject : SubjectId} {book : Book}
    {job : Nat} {jo : Option Job} {account amount : Nat} {plan : Plan}
    (accepted : decideMoney tariff stored subject book job jo settleAction account amount = .ok plan) :
    ∃ t j p, tariff = some t ∧ jo = some j ∧ (j.state = 3 ∨ j.state = 4 ∨ j.state = 5) ∧
      payouts t.slashCallerPermille j = some p ∧ plan.move = .settle p ∧
      plan.after.state = 6 ∧ plan.after.held = 0 ∧
      (plan.batch.apply book).balance job plan.asset = 0 := by
  have agrees := held_agrees accepted
  obtain ⟨t, j, rfl, -, -, rfl, -, same, -, branch⟩ := decideMoney_ok accepted
  rcases branch with ⟨bad, -⟩ | ⟨bad, -⟩ | ⟨-, -, -, settle⟩
  · exact absurd bad (by decide)
  · exact absurd bad (by decide)
  · obtain ⟨p, paid, rfl, -⟩ := decideSettle_ok settle
    refine ⟨t, j, p, rfl, rfl, (payouts_isSome_iff _ j).mp (by rw [paid]; rfl), paid, rfl, rfl,
      rfl, ?_⟩
    simpa [Plan.after, Job.held] using agrees

/-- **No double settle**: a settled job is closed, and no money command —
settle, fund or claim — is accepted on it again. -/
theorem no_double_settle {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {jo : Option Job} {account amount : Nat}
    {plan : Plan}
    (accepted : decideMoney tariff stored subject book job jo settleAction account amount = .ok plan)
    (tariff' : Option Tariff) (stored' : Option (StoredCapability .account)) (subject' : SubjectId)
    (book' : Book) (action' account' amount' : Nat) (plan' : Plan) :
    decideMoney tariff' stored' subject' book' job (some plan.after) action' account' amount' ≠
      .ok plan' := by
  obtain ⟨-, -, -, -, -, -, -, -, closed, -⟩ := settle_requires_terminal accepted
  intro again
  obtain ⟨t, j, -, -, -, same, -, -, -, branch⟩ := decideMoney_ok again
  cases same
  rcases branch with ⟨-, fund⟩ | ⟨-, claim⟩ | ⟨-, -, -, settle⟩
  · have := (decideFund_ok fund).2.1; omega
  · have := (decideClaim_ok claim).2.1; omega
  · have := (decideSettle_ok settle).choose_spec.2.2.1; exact this closed

/-! ## Griefing (COMPUTE §2.7): what a challenge that fails costs, and whom -/

/-- The Book leg of a `truth` turn: its submitter pays the re-execution fee.
C4 NOCK-FEE supplies the fee (`run/steps × perStep`, the oracle's count);
this branch has no fee term, so it is a parameter here. -/
def truthFee (submitter asset fee : Nat) : Batch := ⟨[], [.burn submitter asset fee]⟩

/-- **A false challenge costs its submitter the fee and the provider nothing.**
A `truth` that equals the output leaves the job upheld (C1's `decide → 3`):
the submitter's balance falls by exactly the fee (so by at least the
re-execution fee C4 binds it to), the Book's total is unchanged, and the
settle pays the provider its full `price + bond` — no bond moved. -/
theorem griefing_cost_bounded (split : Nat) (j : Job) (book : Book) (submitter asset fee : Nat)
    (upheld : j.state = 3) (funded : j.price ≤ j.escrow)
    (admitted : (truthFee submitter asset fee).Admission book) (notWell : submitter ≠ asset) :
    ((truthFee submitter asset fee).apply book).balance submitter asset =
        book.balance submitter asset - Int.ofNat fee ∧
      ((truthFee submitter asset fee).apply book).totalAsset asset = book.totalAsset asset ∧
      payouts split j = some ⟨j.price + j.bond, j.escrow - j.price, 0⟩ := by
  refine ⟨?_, Batch.conservation book _ admitted asset, ?_⟩
  · simp [truthFee, Batch.apply, registerAccounts, applyOperations, Operation.apply,
      Operation.posting, Operation.leaseRecord?, Book.applyPosting, Book.balance,
      DFinsupp.single_apply, Ne.symm notWell, sub_eq_add_neg]
  · simp [payouts, upheld, Nat.min_eq_left funded]

/-! ## The law: the money branch is gated by a slot only the money receiver projects -/

/-- Projected only by `JobMoneyReceiver`; no other receiver may project a slot of this name. -/
def moneySlot : String := "authority/operation/job-money"
def actionSlot : String := "job/money/action"
def accountSlot : String := "job/money/account"
def amountSlot : String := "job/money/amount"

private def nonnegative (slot : String) : Pred := .not (.le slot (-1))

/-- The fields a money edge never changes except as listed. -/
def fundEdge : Pred := .all [
  .eq actionSlot 1,
  .eq "resource/field/0/before" 0, .eq "resource/field/0/after" 0,
  .eqSlots "request/subject" "resource/field/3/before",
  .eqSlots accountSlot "resource/field/4/before",
  .eq "resource/field/8/before" 0,
  .eqSlots "resource/field/8/after" "resource/field/5/after",
  .eqSlots amountSlot "resource/field/5/after",
  .eq "resource/field/3/delta" 0, .eq "resource/field/4/delta" 0, .eq "resource/field/5/delta" 0,
  .eq "resource/field/9/delta" 0, .eq "resource/field/10/delta" 0,
  .eq "resource/field/11/delta" 0]

def claimEdge : Pred := .all [
  .eq actionSlot 2,
  .eq "resource/field/0/before" 0, .eq "resource/field/0/after" 1,
  .not (.le "resource/field/5/before" 0),
  .eqSlots "resource/field/8/before" "resource/field/5/before",
  .eq "resource/field/9/before" 0, .eq "resource/field/11/before" 0,
  .eqSlots "resource/field/9/after" "request/subject",
  .eqSlots "resource/field/10/after" accountSlot,
  .eqSlots "resource/field/11/after" amountSlot,
  .leSlots "resource/field/5/after" "resource/field/11/after",
  .eq "resource/field/3/delta" 0, .eq "resource/field/4/delta" 0, .eq "resource/field/5/delta" 0,
  .eq "resource/field/8/delta" 0]

def settleEdge : Pred := .all [
  .eq actionSlot 3,
  .memberOf "resource/field/0/before" [3, 4, 5], .eq "resource/field/0/after" 6,
  .eq "resource/field/8/after" 0, .eq "resource/field/11/after" 0,
  nonnegative "resource/field/8/before", nonnegative "resource/field/11/before",
  .eq "resource/field/3/delta" 0, .eq "resource/field/4/delta" 0, .eq "resource/field/5/delta" 0,
  .eq "resource/field/9/delta" 0, .eq "resource/field/10/delta" 0]

/-- The branch C1's job law carries for the money edges.  The amounts are not
the law's: the receiver computes them from the job (`decideMoney`, `payouts`). -/
def moneyPolicy : Pred := .all [.eq moneySlot 1, .any [fundEdge, claimEdge, settleEdge]]

/-- The stand-in for C1's non-money edges on this branch: any mutation that
changes only the state, never into or out of closed, and never a money field. -/
def handSetEdge : Pred := .all [
  .not (.eq moneySlot 1), .eq "request/verb" 2,
  .not (.eq "resource/field/0/before" 6),
  .memberOf "resource/field/0/after" [0, 1, 2, 3, 4, 5],
  .eq "resource/field/3/delta" 0, .eq "resource/field/4/delta" 0, .eq "resource/field/5/delta" 0,
  .eq "resource/field/8/delta" 0, .eq "resource/field/9/delta" 0,
  .eq "resource/field/10/delta" 0, .eq "resource/field/11/delta" 0]

/-- The job law of this branch until C1's `Job.law` lands (birth storage `job`). -/
def standInLaw : Pred := .any [handSetEdge, moneyPolicy, .memberOf "request/verb" [1, 3]]

/-- **Without the money slot, a job's money never moves**: a mutation the
stand-in law admits without `moneySlot` leaves escrow and bond unchanged and
never closes the job. -/
theorem standInLaw_money_frozen_without_slot (old st : Minidregg.Pred.State)
    (accepted : Minidregg.Pred.eval standInLaw old st = true)
    (mutation : st.get "request/verb" = some 2)
    (noSlot : st.get moneySlot ≠ some 1) :
    st.get "resource/field/8/delta" = some 0 ∧ st.get "resource/field/11/delta" = some 0 ∧
      st.get "resource/field/0/after" ≠ some 6 := by
  unfold standInLaw at accepted
  rw [eval_any] at accepted
  obtain ⟨branch, member, holds⟩ := List.any_eq_true.mp accepted
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl
  · unfold handSetEdge at holds
    rw [eval_all] at holds
    have e := (List.all_eq_true.mp holds) (.eq "resource/field/8/delta" 0) (by simp)
    have b := (List.all_eq_true.mp holds) (.eq "resource/field/11/delta" 0) (by simp)
    have s := (List.all_eq_true.mp holds) (.memberOf "resource/field/0/after" [0, 1, 2, 3, 4, 5])
      (by simp)
    simp only [Minidregg.Pred.eval, Minidregg.Pred.evalWith, decide_eq_true_eq] at e b s
    refine ⟨e, b, fun six => ?_⟩
    simp [six] at s
  · unfold moneyPolicy at holds
    rw [eval_all] at holds
    have r := (List.all_eq_true.mp holds) (.eq moneySlot 1) (by simp)
    simp only [Minidregg.Pred.eval, Minidregg.Pred.evalWith, decide_eq_true_eq] at r
    exact absurd r noSlot
  · simp [Minidregg.Pred.eval, Minidregg.Pred.evalWith, mutation] at holds

/-- **The law closes a job only from a terminal state**: a turn the money
branch admits that writes state 6 starts in 3, 4 or 5. -/
theorem moneyPolicy_closes_only_terminal (old st : Minidregg.Pred.State)
    (accepted : Minidregg.Pred.eval moneyPolicy old st = true) (closes : st.get "resource/field/0/after" = some 6) :
    ∃ s, st.get "resource/field/0/before" = some s ∧ (s = 3 ∨ s = 4 ∨ s = 5) := by
  unfold moneyPolicy at accepted
  rw [eval_all] at accepted
  have edges := (List.all_eq_true.mp accepted) (.any [fundEdge, claimEdge, settleEdge]) (by simp)
  rw [eval_any] at edges
  obtain ⟨edge, member, holds⟩ := List.any_eq_true.mp edges
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl
  · unfold fundEdge at holds
    rw [eval_all] at holds
    have zero := (List.all_eq_true.mp holds) (.eq "resource/field/0/after" 0) (by simp)
    simp only [Minidregg.Pred.eval, Minidregg.Pred.evalWith, decide_eq_true_eq] at zero
    rw [closes] at zero; cases zero
  · unfold claimEdge at holds
    rw [eval_all] at holds
    have one := (List.all_eq_true.mp holds) (.eq "resource/field/0/after" 1) (by simp)
    simp only [Minidregg.Pred.eval, Minidregg.Pred.evalWith, decide_eq_true_eq] at one
    rw [closes] at one; cases one
  · unfold settleEdge at holds
    rw [eval_all] at holds
    have from_ := (List.all_eq_true.mp holds) (.memberOf "resource/field/0/before" [3, 4, 5])
      (by simp)
    simp only [Minidregg.Pred.eval, Minidregg.Pred.evalWith] at from_
    cases h : st.get "resource/field/0/before" with
    | none => simp [h] at from_
    | some s => exact ⟨s, rfl, by simp [h] at from_; omega⟩


/-- The job law the money receiver accepts: an installed law that is exactly
this predicate.  It has no management branch, so it cannot be replaced.  When
C1's `Job.law` lands, it is the pinned law (and carries `moneyPolicy`). -/
def jobLaw : Pred := standInLaw

/-! ## Poles, kernel-decided on a concrete Book and job -/

def fixtureTariff : Tariff := PayTariff.exampleTariff

/-- Account 108 (subject 8, the caller) and 109 (subject 9, the provider) hold
60 credits each of asset 0; the well 0 is at −120.  Job 50's held account does
not exist yet. -/
def fixtureBook : Book :=
  ⟨{0, 108, 109}, DFinsupp.single (108, 0) 60 + DFinsupp.single (109, 0) 60 +
    DFinsupp.single (0, 0) (-120), 0⟩

def callerCap : StoredCapability .account := PayAssignmentReceiver.ownerCapability 8 108
def providerCap : StoredCapability .account := PayAssignmentReceiver.ownerCapability 9 109

/-- An order: caller 8, refund account 108, price 10. -/
def fixtureJob : Job := ordered 8 108 10
def fundedJob : Job := { fixtureJob with escrow := 10 }
def claimedJob : Job := { fundedJob with state := 1, provider := 9, providerAcct := 109, bond := 10 }
def afterFund : Book := (Plan.batch ⟨0, 50, fixtureJob, .fund 108 10⟩).apply fixtureBook
def afterClaim : Book := (Plan.batch ⟨0, 50, fundedJob, .claim 9 109 10⟩).apply afterFund

theorem fixture_fund_accepted :
    (decideMoney (some fixtureTariff) (some callerCap) ⟨8⟩ fixtureBook 50 (some fixtureJob) 1 108 10
      |>.toOption) = some ⟨0, 50, fixtureJob, .fund 108 10⟩ := by decide +kernel

theorem fixture_fund_twice_refused :
    (decideMoney (some fixtureTariff) (some callerCap) ⟨8⟩ afterFund 50 (some fundedJob) 1 108 10
      |>.toOption) = none := by decide +kernel

theorem fixture_fund_not_caller_refused :
    (decideMoney (some fixtureTariff) (some providerCap) ⟨9⟩ fixtureBook 50 (some fixtureJob) 1 109
      10 |>.toOption) = none := by decide +kernel

theorem fixture_fund_unbalanced :
    (decideMoney (some fixtureTariff) (some callerCap) ⟨8⟩ fixtureBook 50 (some fixtureJob) 1 108 9
      |>.toOption) = none := by decide +kernel

theorem fixture_fund_insufficient_refused :
    (decideMoney (some fixtureTariff) (some callerCap) ⟨8⟩ fixtureBook 50
      (some { fixtureJob with price := 61 }) 1 108 61 |>.toOption) = none := by decide +kernel

/-- A job whose id is already a Book account (109, the provider's) cannot hold credit. -/
theorem fixture_fund_held_taken_refused :
    (decideMoney (some fixtureTariff) (some callerCap) ⟨8⟩ fixtureBook 109 (some fixtureJob) 1 108 10
      |>.toOption) = none := by decide +kernel

theorem fixture_claim_accepted :
    (decideMoney (some fixtureTariff) (some providerCap) ⟨9⟩ afterFund 50 (some fundedJob) 2 109 10
      |>.toOption) = some ⟨0, 50, fundedJob, .claim 9 109 10⟩ := by decide +kernel

theorem fixture_claim_bond_below_price_refused :
    (decideMoney (some fixtureTariff) (some providerCap) ⟨9⟩ afterFund 50 (some fundedJob) 2 109 9
      |>.toOption) = none := by decide +kernel

theorem fixture_claim_unfunded_refused :
    (decideMoney (some fixtureTariff) (some providerCap) ⟨9⟩ fixtureBook 50 (some fixtureJob) 2 109
      10 |>.toOption) = none := by decide +kernel

/-- Upheld: the provider is paid price + bond = 20 out of the held account. -/
theorem fixture_settle_upheld :
    (decideMoney (some fixtureTariff) none ⟨8⟩ afterClaim 50 (some { claimedJob with state := 3 }) 3
      0 0 |>.toOption) = some ⟨0, 50, { claimedJob with state := 3 }, .settle ⟨20, 0, 0⟩⟩ := by
  decide +kernel

/-- Slashed: the caller is paid escrow + half the bond = 15; 5 is burned into the well. -/
theorem fixture_settle_slashed :
    (decideMoney (some fixtureTariff) none ⟨8⟩ afterClaim 50 (some { claimedJob with state := 4 }) 3
      0 0 |>.toOption) = some ⟨0, 50, { claimedJob with state := 4 }, .settle ⟨0, 15, 5⟩⟩ := by
  decide +kernel

/-- **A forged job mints nothing**: a cell claiming escrow and bond its Book
account never received is refused, whatever its state says. -/
theorem fixture_forged_held_refused :
    (decideMoney (some fixtureTariff) none ⟨8⟩ fixtureBook 50 (some { claimedJob with state := 3 }) 3
      0 0 |>.toOption) = none := by decide +kernel

theorem fixture_settle_not_terminal_refused :
    (decideMoney (some fixtureTariff) none ⟨8⟩ afterClaim 50 (some claimedJob) 3 0 0
      |>.toOption) = none := by decide +kernel

theorem fixture_settle_closed_refused :
    (decideMoney (some fixtureTariff) none ⟨8⟩ afterClaim 50
      (some { claimedJob with state := 6, escrow := 0, bond := 0 }) 3 0 0 |>.toOption) = none := by
  decide +kernel

theorem fixture_genesis_tariff_refused :
    (decideMoney (some PayTariff.genesisDefault) (some callerCap) ⟨8⟩ fixtureBook 50
      (some fixtureJob) 1 108 10 |>.toOption) = none := by decide +kernel

/-- The Book after fund, claim and an upheld settle: the caller paid 10, the
provider gained 10 (its bond back plus the price), the job's account is empty
and the well never moved. -/
theorem fixture_round_trip_upheld :
    let final := (Plan.batch ⟨0, 50, { claimedJob with state := 3 }, .settle ⟨20, 0, 0⟩⟩).apply
      afterClaim
    final.balance 108 0 = 50 ∧ final.balance 109 0 = 70 ∧ final.balance 50 0 = 0 ∧
      final.balance 0 0 = -120 := by
  decide +kernel

/-- After a slash: the caller is up 5, the provider down 10, the job's account
is empty, and the 5 retired credits are in the well. -/
theorem fixture_round_trip_slashed :
    let final := (Plan.batch ⟨0, 50, { claimedJob with state := 4 }, .settle ⟨0, 15, 5⟩⟩).apply
      afterClaim
    final.balance 108 0 = 65 ∧ final.balance 109 0 = 50 ∧ final.balance 50 0 = 0 ∧
      final.balance 0 0 = -115 := by
  decide +kernel

#assert_axioms commit_ok
#assert_axioms decideFund_ok
#assert_axioms decideClaim_ok
#assert_axioms decideSettle_ok
#assert_axioms decideMoney_ok
#assert_axioms callerShare_le
#assert_axioms payouts_sum
#assert_axioms slash_split_sums_to_bond
#assert_axioms half_split
#assert_axioms provider_paid_iff_unchallenged_or_upheld
#assert_axioms payouts_isSome_iff
#assert_axioms applyPosting_balance
#assert_axioms apply_balance
#assert_axioms applyOperations_balance
#assert_axioms registerAccounts_balance
#assert_axioms ops_flow
#assert_axioms plan_balance
#assert_axioms decideMoney_plan
#assert_axioms well_after
#assert_axioms held_agrees
#assert_axioms escrow_conserved
#assert_axioms fund_holds_price
#assert_axioms fund_requires_caller
#assert_axioms claim_requires_bond
#assert_axioms settle_requires_terminal
#assert_axioms no_double_settle
#assert_axioms griefing_cost_bounded
#assert_axioms standInLaw_money_frozen_without_slot
#assert_axioms moneyPolicy_closes_only_terminal
#assert_axioms fixture_fund_accepted
#assert_axioms fixture_fund_twice_refused
#assert_axioms fixture_fund_not_caller_refused
#assert_axioms fixture_fund_unbalanced
#assert_axioms fixture_fund_insufficient_refused
#assert_axioms fixture_fund_held_taken_refused
#assert_axioms fixture_claim_accepted
#assert_axioms fixture_claim_bond_below_price_refused
#assert_axioms fixture_claim_unfunded_refused
#assert_axioms fixture_settle_upheld
#assert_axioms fixture_settle_slashed
#assert_axioms fixture_forged_held_refused
#assert_axioms fixture_settle_not_terminal_refused
#assert_axioms fixture_settle_closed_refused
#assert_axioms fixture_genesis_tariff_refused
#assert_axioms fixture_round_trip_upheld
#assert_axioms fixture_round_trip_slashed

end Minidregg.Kernel.JobMoney
