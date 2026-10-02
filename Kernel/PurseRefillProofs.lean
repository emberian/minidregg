/-
# Kernel.PurseRefillProofs — what the refill receiver writes into the purse

`pursePatch_readState`: the purse leg's declared writes land exactly the
plan's refilled state on any store, so `Prepared.purse_after` — the purse the
receiver commits reads back as `plan.after` — and `PurseRefill.purse_never_mints`'s
refill step is the receiver's own post, not a model beside it.
-/
import Kernel.PurseRefillReceiver

namespace Minidregg.Kernel.PurseRefillReceiver
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.Store (Store Patch)
open Minidregg.Kernel.PurseRefill
set_option autoImplicit false

private theorem set_field_other (store : Store effectLayout) (task i j : Nat) (value : Option Int)
    (different : j ≠ i) :
    store.set (StateKey.objectField ⟨task⟩ ⟨i⟩).address value
        (StateKey.objectField ⟨task⟩ ⟨j⟩).address =
      store (StateKey.objectField ⟨task⟩ ⟨j⟩).address := by
  apply Minidregg.Theory.Store.Store.set_ne
  intro same
  have := StateKey.address_injective same
  simp at this
  exact different this

/-- The purse leg's patch writes exactly the plan's refilled state: whatever
store it runs on, the task's four coordinates read back as `plan.after`. -/
theorem pursePatch_readState (command : Command) (d : Declaration) (store pre : Store effectLayout)
    (height : Nat) :
    AgentGrain.readState command.task (Patch.run store (pursePatch command d pre height)) =
      some d.plan.after := by
  rw [pursePatch, Patch.run_append]
  have ratchet : ∀ s : Store effectLayout, AgentGrain.readState command.task
      (Patch.run s (Minidregg.Compiler.DeclaredEffectCell.blinding.patch pre height)) =
        AgentGrain.readState command.task s := by
    intro s
    simp only [AgentGrain.readState, DeclaredFields.read_ratchet]
  rw [ratchet]
  obtain ⟨⟨asset, account, amount, gain, ⟨g, st, r, h⟩⟩, root, nullifier⟩ := d
  simp [DeclaredResourceScalar.cellPatch, scalarCommand,
    DeclaredResourceScalar.Command.declaration,
    Minidregg.Theory.DeclaredActionLowering.Declaration.patch,
    AgentGrain.actions, AgentGrain.State.values, Plan.after, AgentGrain.refill_after,
    Minidregg.Theory.DeclaredActionLowering.Action.ops, AgentGrain.readState, DeclaredFields.read,
    AgentGrain.key, DeclaredFields.key, List.range, List.range.loop, set_field_other]

variable {F : Type} [Field F] {deployment : Deployment}
  {profile : Minidregg.Compiler.CanonicalRuntimeProfile.Profile F} {ambient : Ambient}
  {durable : Durable} {command : Command}

/-- The purse the refill writes is the plan's refilled state. -/
theorem Prepared.purse_after (prepared : Prepared deployment profile ambient durable command) :
    AgentGrain.readState command.task prepared.pursePost.logical = some prepared.plan.after :=
  pursePatch_readState command
    (declaration prepared.authority.snapshot.domain profile.semantics command prepared.purse.root
      prepared.plan) prepared.purse.logical prepared.purse.logical ambient.height

/-- With `refill_conserves`: the purse the receiver commits holds exactly the
loaded allowance plus the burn. -/
theorem Prepared.purse_budget (prepared : Prepared deployment profile ambient durable command) :
    ∃ after, AgentGrain.readState command.task prepared.pursePost.logical = some after ∧
      ∃ before, AgentGrain.readState command.task prepared.purse.logical = some before ∧
        budget after = budget before + Int.ofNat command.amount :=
  ⟨prepared.plan.after, prepared.purse_after, prepared.plan.before, prepared.purse_before,
    (refill_conserves prepared.decided).2.2.2.2.1⟩

#assert_axioms pursePatch_readState
#assert_axioms Prepared.purse_after
#assert_axioms Prepared.purse_budget

end Minidregg.Kernel.PurseRefillReceiver
