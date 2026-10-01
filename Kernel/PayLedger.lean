/-
# Kernel.PayLedger — the audit identity of the credit asset (PAY P3, P6; COMPUTE §2.6)

Every posting the pay line makes to the Book in the credit asset is one of:

* an observation report (P3): credit minted from the well for an observed payment;
* a purse refill (P6): credit burned from an account into an AgentGrain purse;
* a job-money turn (C3): credit moved into a job's held account (escrow,
  bond) or out of it (payouts), and a slash's retired share burned into the well.

`ledger_identity` is the well's side: along any log of accepted postings,
`−well_h = −well_0 + credited − refilled − retired`.  Job deposits and payouts
move credit between accounts and the job's held account and never touch the
well; a slash returns its retired share to it.  The job side is
`escrow_conserved_log`: along a job's history, what it holds now plus what it
paid out plus what it retired is what was deposited into it, and the Book's
held account always holds exactly that (`JobMoney.held_agrees`).
-/
import Kernel.JobMoney

namespace Minidregg.Kernel.PayLedger

open Minidregg.Kernel
open Minidregg.Kernel.PayTariff
open Minidregg.Theory.CanonicalResourceKernel
open Minidregg.Theory.CredentialAuthorityState
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

/-- One accepted posting to the Book of the pay line. -/
inductive Entry where
  | observe (plan : PayObservation.Plan)
  | refill (plan : PurseRefill.Plan)
  | job (plan : JobMoney.Plan)

def Entry.batch : Entry → Batch
  | .observe plan => plan.batch
  | .refill plan => plan.batch
  | .job plan => plan.batch

/-- A log of accepted postings, each decided at the Book the previous ones produced. -/
inductive LedgerLog : Book → List Entry → Book → Prop
  | nil (book : Book) : LedgerLog book [] book
  | observe {book final : Book} {plan : PayObservation.Plan} {rest : List Entry}
      (decided : ∃ store tip observations,
        PayObservation.decideObservations store book tip observations = .ok plan)
      (tail : LedgerLog (plan.batch.apply book) rest final) :
      LedgerLog book (.observe plan :: rest) final
  | refill {book final : Book} {plan : PurseRefill.Plan} {rest : List Entry}
      (decided : ∃ tariff stored subject purse account amount gain,
        PurseRefill.decideRefill tariff stored subject book purse account amount gain = .ok plan)
      (tail : LedgerLog (plan.batch.apply book) rest final) :
      LedgerLog book (.refill plan :: rest) final
  | job {book final : Book} {plan : JobMoney.Plan} {rest : List Entry}
      (decided : ∃ tariff stored subject job jo action account amount,
        JobMoney.decideMoney tariff stored subject book job jo action account amount = .ok plan)
      (tail : LedgerLog (plan.batch.apply book) rest final) :
      LedgerLog book (.job plan :: rest) final

/-- Σ credited in `asset` by the log's observation reports. -/
def creditedIn (asset : AssetId) : List Entry → Int
  | [] => 0
  | .observe plan :: rest =>
      (if plan.tariff.asset = asset then PayObservationProofs.creditSum plan.credits else 0) +
        creditedIn asset rest
  | _ :: rest => creditedIn asset rest

/-- Σ burned in `asset` by the log's refills. -/
def refilledIn (asset : AssetId) : List Entry → Int
  | [] => 0
  | .refill plan :: rest =>
      (if plan.asset = asset then Int.ofNat plan.amount else 0) + refilledIn asset rest
  | _ :: rest => refilledIn asset rest

/-- Σ burned into the well in `asset` by slashes. -/
def retiredIn (asset : AssetId) : List Entry → Int
  | [] => 0
  | .job plan :: rest =>
      (if plan.asset = asset then Int.ofNat plan.retired else 0) + retiredIn asset rest
  | _ :: rest => retiredIn asset rest

/-- **The ledger identity**: along any log of accepted reports, refills and
job-money turns, `−well_h = −well_0 + Σ credited − Σ refilled − Σ retired`. -/
theorem ledger_identity {initial final : Book} {log : List Entry}
    (accepted : LedgerLog initial log final) (asset : AssetId) :
    -(final.balance asset asset) =
      -(initial.balance asset asset) + creditedIn asset log - refilledIn asset log -
        retiredIn asset log := by
  induction accepted with
  | nil book => simp [creditedIn, refilledIn, retiredIn]
  | observe decided tail induction =>
      rename_i book final plan rest
      obtain ⟨store, tip, observations, decision⟩ := decided
      rw [induction, PayObservationProofs.Plan.batch_apply,
        PayObservationProofs.mints_well_balance plan.tariff.asset asset book plan.credits
          (PayObservationProofs.decided_payers decision)]
      by_cases same : plan.tariff.asset = asset
      · simp [creditedIn, refilledIn, retiredIn, same]; ring
      · simp [creditedIn, refilledIn, retiredIn, same]
  | refill decided tail induction =>
      rename_i book final plan rest
      obtain ⟨tariff, stored, subject, purse, account, amount, gain, decision⟩ := decided
      obtain ⟨_, _, issuer, _, _, acct, _, _, _, _⟩ := PurseRefill.decideRefill_ok decision
      subst acct
      rw [induction]
      by_cases same : plan.asset = asset
      · subst same
        rw [PurseRefill.burn_well plan book issuer]
        simp [creditedIn, refilledIn, retiredIn]; ring
      · rw [PurseRefill.burn_other_well plan book asset same]
        simp [creditedIn, refilledIn, retiredIn, same]
  | job decided tail induction =>
      rename_i book final plan rest
      obtain ⟨tariff, stored, subject, job, jo, action, account, amount, decision⟩ := decided
      rw [induction, JobMoney.well_after decision asset]
      by_cases same : plan.asset = asset
      · simp [creditedIn, refilledIn, retiredIn, same]; ring
      · simp [creditedIn, refilledIn, retiredIn, same]

/-- One accepted money turn, at the job: what it holds after, plus what it
paid out, plus what it retired, is what it held before plus what was deposited. -/
theorem job_turn_balance {tariff : Option Tariff} {stored : Option (StoredCapability .account)}
    {subject : SubjectId} {book : Book} {job : Nat} {jo : Option JobMoney.Job}
    {action account amount : Nat} {plan : JobMoney.Plan}
    (accepted : JobMoney.decideMoney tariff stored subject book job jo action account amount =
      .ok plan) :
    plan.after.held + plan.paid + plan.retired = plan.before.held + plan.deposited := by
  have agrees := JobMoney.held_agrees accepted
  obtain ⟨-, -, issuer, -, facts⟩ := JobMoney.decideMoney_plan accepted
  rw [JobMoney.plan_balance] at agrees
  obtain ⟨asset, job', before, move⟩ := plan
  cases move with
  | fund a n =>
      obtain ⟨-, own, held⟩ := facts
      simp only at agrees ⊢
      rw [held] at agrees
      simp [JobMoney.flowIn, Operation.posting, Ne.symm own, JobMoney.Plan.paid,
        JobMoney.Plan.retired, JobMoney.Plan.deposited] at agrees ⊢
      omega
  | claim pr a n =>
      obtain ⟨-, own, held⟩ := facts
      simp only at agrees ⊢
      rw [held] at agrees
      simp [JobMoney.flowIn, Operation.posting, Ne.symm own, JobMoney.Plan.paid,
        JobMoney.Plan.retired, JobMoney.Plan.deposited] at agrees ⊢
      omega
  | settle p =>
      obtain ⟨payees, held⟩ := facts
      simp only at agrees payees issuer ⊢
      rw [held] at agrees
      simp only [JobMoney.Payouts.badPayee, not_or, not_and] at payees
      obtain ⟨hp, hc⟩ := payees
      have out : ∀ (payee amt : Nat), (amt ≠ 0 → ¬payee = asset ∧ ¬payee = job') →
          JobMoney.flowIn job' asset (.transfer job' payee asset amt) = -(amt : Int) := by
        intro payee amt ok
        by_cases z : amt = 0
        · simp [JobMoney.flowIn, Operation.posting, z]
        · have : payee ≠ job' := (ok z).2
          simp [JobMoney.flowIn, Operation.posting, Ne.symm this]
      have burnt : JobMoney.flowIn job' asset (.burn job' asset p.retired) = -(p.retired : Int) := by
        simp [JobMoney.flowIn, Operation.posting, issuer]
      rw [out _ _ hp, out _ _ hc, burnt] at agrees
      simp only [JobMoney.Plan.after, JobMoney.Job.held, JobMoney.Plan.paid, JobMoney.Plan.retired,
        JobMoney.Plan.deposited, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_zero] at agrees ⊢
      omega

/-- One job's history: edges of its law that move no money (C1's non-money
edges; on this branch `JobMoney.standInLaw_money_frozen_without_slot` is that
fact at the law's slots), and accepted money turns. -/
inductive JobLog : JobMoney.Job → List JobMoney.Plan → JobMoney.Job → Prop
  | nil (j : JobMoney.Job) : JobLog j [] j
  | edge {before mid after : JobMoney.Job} {plans : List JobMoney.Plan}
      (frozen : mid.escrow = before.escrow ∧ mid.bond = before.bond)
      (tail : JobLog mid plans after) : JobLog before plans after
  | money {after : JobMoney.Job} {plan : JobMoney.Plan} {rest : List JobMoney.Plan}
      (decided : ∃ tariff stored subject book job action account amount,
        JobMoney.decideMoney tariff stored subject book job (some plan.before) action account
          amount = .ok plan)
      (tail : JobLog plan.after rest after) : JobLog plan.before (plan :: rest) after

/-- **Escrow is conserved over a job's whole history**: what it holds at the
end, plus everything paid out and retired, is what it held at the start plus
everything deposited into it.  A closed job holds nothing, so there the burns are
exactly the payouts plus the retired share of a slashed bond. -/
theorem escrow_conserved_log {start final : JobMoney.Job} {plans : List JobMoney.Plan}
    (log : JobLog start plans final) :
    final.held + (plans.map fun p => p.paid + p.retired).sum =
      start.held + (plans.map JobMoney.Plan.deposited).sum := by
  induction log with
  | nil j => simp
  | edge frozen _ induction =>
      rename_i before mid after rest
      simp only [JobMoney.Job.held] at induction ⊢
      omega
  | money decided _ induction =>
      rename_i after plan rest
      obtain ⟨tariff, stored, subject, book, job, action, account, amount, decision⟩ := decided
      have turn := job_turn_balance decision
      simp only [List.map_cons, List.sum_cons]
      omega

#assert_axioms ledger_identity
#assert_axioms job_turn_balance
#assert_axioms escrow_conserved_log

end Minidregg.Kernel.PayLedger
