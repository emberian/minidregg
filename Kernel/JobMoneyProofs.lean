/-
# Kernel.JobMoneyProofs — what the job-money receiver writes into the job

`actions_readJob`: the money leg's declared writes land exactly the plan's job
on any store, so `Prepared.job_after` — the job the receiver commits reads back
as `plan.after` — and the job side of `PayLedger.escrow_conserved_log` is the
receiver's own post, not a model beside it.
-/
import Kernel.JobMoneyReceiver
import Kernel.PayLedger

namespace Minidregg.Kernel.JobMoneyReceiver
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.Store (Store Patch)
open Minidregg.Kernel.JobMoney
set_option autoImplicit false

private theorem set_field_other (store : Store effectLayout) (job i j : Nat) (value : Option Int)
    (different : j ≠ i) :
    store.set (StateKey.objectField ⟨job⟩ ⟨i⟩).address value
        (StateKey.objectField ⟨job⟩ ⟨j⟩).address =
      store (StateKey.objectField ⟨job⟩ ⟨j⟩).address := by
  apply Minidregg.Theory.Store.Store.set_ne
  intro same
  have := StateKey.address_injective same
  simp at this
  exact different this

/-- The money leg's patch writes exactly the plan's job: whatever store it
runs on, the job's eight money fields read back as `after`. -/
theorem actions_readJob (store : Store effectLayout) (job subject capability root nullifier : Nat)
    (before after : Job) :
    readJob job (Patch.run store (DeclaredResourceScalar.cellPatch
      ⟨.object, job, ⟨subject⟩, ⟨capability⟩, 1, ⟨root⟩, nullifier,
        JobMoney.actions job before after⟩)) = some after := by
  obtain ⟨s, c, ca, p, e, pr, pa, b⟩ := after
  simp [DeclaredResourceScalar.cellPatch, DeclaredResourceScalar.Command.declaration,
    Minidregg.Theory.DeclaredActionLowering.Declaration.patch,
    JobMoney.actions, Job.fields, Minidregg.Theory.DeclaredActionLowering.Action.ops,
    readJob, readField, DeclaredFields.read, DeclaredFields.key, set_field_other,
    stateField, callerField, callerAcctField, priceField, escrowField, providerField,
    providerAcctField, bondField]

theorem jobPatch_readJob (command : Command) (d : Declaration) (store : Store effectLayout) :
    readJob command.job (Patch.run store (jobPatch command d)) = some d.plan.after :=
  actions_readJob store command.job command.subject.value command.capability.value
    d.expectedPreRoot.value d.operationNullifier d.plan.before d.plan.after

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {durable : Durable} {command : Command}

/-- The job the money turn writes is the plan's job. -/
theorem Prepared.job_after (prepared : Prepared deployment profile ambient durable command) :
    readJob command.job prepared.jobPost.logical = some prepared.plan.after :=
  jobPatch_readJob command
    (declaration prepared.authority.snapshot.domain profile.semantics command prepared.job.root
      prepared.plan) prepared.job.logical

/-- With `PayLedger.job_turn_balance`: the job the receiver commits holds the
loaded job's credit plus the deposit, minus the payouts and the retired share. -/
theorem Prepared.job_held (prepared : Prepared deployment profile ambient durable command) :
    ∃ after, readJob command.job prepared.jobPost.logical = some after ∧
      ∃ before, readJob command.job prepared.job.logical = some before ∧
        after.held + prepared.plan.paid + prepared.plan.retired =
          before.held + prepared.plan.deposited :=
  ⟨prepared.plan.after, prepared.job_after, prepared.plan.before, prepared.job_before,
    PayLedger.job_turn_balance prepared.decided⟩

#assert_axioms actions_readJob
#assert_axioms jobPatch_readJob
#assert_axioms Prepared.job_after
#assert_axioms Prepared.job_held

end Minidregg.Kernel.JobMoneyReceiver
