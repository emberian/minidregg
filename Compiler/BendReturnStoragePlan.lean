/- Canonical independent returns are source-derived content effects. Application
matching uses a local view of the original command in which ONLY complete
return-only content payloads are observations. Native signatures, authority,
funding, current law and final writes always use the original command.
This module neither encrypts clear returns nor authorizes a release. -/
import Compiler.BendWorldPlan

namespace Minidregg.Compiler.BendReturnStoragePlan
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel
set_option autoImplicit false

def schema : Digest :=
  (Sp800185Cshake256.hash "DREGG.BEND.RETURN-STORAGE/v1".toUTF8.toList []).digest

def action (slot : BendWorldPlan.ReturnSlot) : ContentResource.Action :=
  .createAtom ⟨BendWorldPlan.returnId slot⟩ (.inlineObject schema)
    (BendWorldPlan.encodeReturn slot)

/-- Every action, including its order and complete bytes, is a canonical return
publication from the decoded source slots. Empty/mixed content is not erased. -/
def Carrier (slots : List BendWorldPlan.ReturnSlot) : Payload → Prop
  | .content content => content.actions ≠ [] ∧
      ∀ a ∈ content.actions, ∃ slot ∈ slots, a = action slot
  | _ => False

instance (slots : List BendWorldPlan.ReturnSlot) (payload : Payload) :
    Decidable (Carrier slots payload) := by
  unfold Carrier
  split <;> infer_instance

def projectTarget (slots : List BendWorldPlan.ReturnSlot) (target : Target) : Target :=
  if Carrier slots target.payload then { target with payload := .read } else target

/-- This is a comparison view, not a separately signed invocation. -/
def applicationCommand (slots : List BendWorldPlan.ReturnSlot) (command : Command) : Command :=
  { command with targets := command.targets.map (projectTarget slots) }

def Stored (slots : List BendWorldPlan.ReturnSlot) (command : Command) : Prop :=
  ∀ slot ∈ slots, ∃ target ∈ command.targets,
    Carrier slots target.payload ∧ match target.payload with
      | .content content => action slot ∈ content.actions
      | _ => False

instance (slots : List BendWorldPlan.ReturnSlot) (command : Command) :
    Decidable (Stored slots command) := by
  unfold Stored
  infer_instance

structure Normalized (base : BendWorldPlan.Plan) (command : Command) where
  private mk ::
  plan : BendWorldPlan.Plan
  applicationExact : BendWorldPlan.matchesCommand base (applicationCommand base.returns command) = true
  stored : Stored base.returns command
  effectsExact : plan.effects = BendWorldPlan.effectsOf command
  returnsExact : plan.returns = base.returns
  readsExact : plan.reads = base.reads
  nativeExact : BendWorldPlan.matchesCommand plan command = true

def normalize (base : BendWorldPlan.Plan) (command : Command) :
    Option (Normalized base command) :=
  if exact : BendWorldPlan.matchesCommand base (applicationCommand base.returns command) = true then
    if stored : Stored base.returns command then
      let plan : BendWorldPlan.Plan := ⟨BendWorldPlan.effectsOf command,base.returns,base.reads⟩
      if native : BendWorldPlan.matchesCommand plan command = true then
        some ⟨plan,exact,stored,rfl,rfl,rfl,native⟩
      else none
    else none
  else none

theorem projected_identity (slots : List BendWorldPlan.ReturnSlot) (target : Target) :
    (projectTarget slots target).target = target.target ∧
    (projectTarget slots target).kind = target.kind ∧
    (projectTarget slots target).expectedTargetRoot = target.expectedTargetRoot := by
  simp only [projectTarget]
  split <;> exact ⟨rfl,rfl,rfl⟩

theorem projected_subject (slots : List BendWorldPlan.ReturnSlot) (command : Command) :
    (applicationCommand slots command).subject = command.subject := rfl

theorem projected_nonce (slots : List BendWorldPlan.ReturnSlot) (command : Command) :
    (applicationCommand slots command).nonce = command.nonce := rfl

theorem projected_claims (slots : List BendWorldPlan.ReturnSlot) (command : Command) :
    (applicationCommand slots command).run = command.run ∧
    (applicationCommand slots command).family = command.family := ⟨rfl,rfl⟩

theorem return_action_exact (slots : List BendWorldPlan.ReturnSlot)
    (content : ContentResource.Command) (carrier : Carrier slots (.content content))
    (a : ContentResource.Action) (member : a ∈ content.actions) :
    ∃ slot ∈ slots, a = .createAtom ⟨BendWorldPlan.returnId slot⟩
      (.inlineObject schema) (BendWorldPlan.encodeReturn slot) :=
  carrier.2 a member

theorem complete_effects (base : BendWorldPlan.Plan) (command : Command)
    (bound : Normalized base command) : bound.plan.effects = BendWorldPlan.effectsOf command :=
  bound.effectsExact

end Minidregg.Compiler.BendReturnStoragePlan
