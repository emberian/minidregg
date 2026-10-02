/- Audience epochs are distinct from policy revisions. This state machine specifies
admitted publication, not secrecy of client-generated key material. -/

namespace Minidregg.Theory.ObjectAudience
set_option autoImplicit false

inductive Mode where
  | active | frozen
  deriving DecidableEq, Repr

structure State where
  object : Nat
  epoch : Nat
  parent : Nat
  transition : Nat
  audience : Nat
  devices : Nat
  history : Nat
  manifest : Nat
  mode : Mode
  /-- Root used to prepare this epoch; checked only at enrollment/resume. -/
  authoritySnapshot : Nat := 0
  /-- Actual object content image containing the recipient-device records. -/
  deviceSnapshot : Nat := 0
  deriving DecidableEq, Repr

/-- Fresh invocation and release admissions require the currently active epoch.
Exact historical receipt recovery does not invoke this predicate. -/
def Fresh (state : State) (object : Nat) (epoch : Option Nat) : Prop :=
  state.object = object ∧ state.mode = .active ∧ epoch = some state.epoch
instance (s : State) (o : Nat) (e : Option Nat) : Decidable (Fresh s o e) := by
  unfold Fresh; infer_instance

/-- Freeze retains the admitted old key bindings and selects a fresh transition.
Resume publishes a new epoch and a complete manifest against the frozen parent.
Revocation occurs while frozen under existing current capability authorization. -/
inductive Step : State → State → Prop where
  | freeze (s : State) (id : Nat) (active : s.mode = .active)
      (fresh : id ≠ s.transition) :
      Step s { s with parent := s.transition, transition := id, mode := .frozen }
  | resume (s : State) (audience devices history manifest authoritySnapshot deviceSnapshot : Nat)
      (frozen : s.mode = .frozen) (material : manifest ≠ 0) :
      Step s { s with epoch := s.epoch + 1, audience := audience, devices := devices, history := history, manifest := manifest, mode := .active, authoritySnapshot := authoritySnapshot, deviceSnapshot := deviceSnapshot }

theorem frozen_refuses_fresh (s : State) (frozen : s.mode = .frozen)
    (object : Nat) (epoch : Option Nat) : ¬ Fresh s object epoch := by
  intro accepted
  have impossible : Mode.frozen = Mode.active := frozen.symm.trans accepted.2.1
  cases impossible

theorem missing_epoch_refused (s : State) (object : Nat) : ¬ Fresh s object none := by
  intro accepted; cases accepted.2.2

theorem stale_epoch_refused (s : State) (object epoch : Nat) (stale : epoch ≠ s.epoch) :
    ¬ Fresh s object (some epoch) := by
  intro accepted
  exact stale (Option.some.inj accepted.2.2)

theorem step_object_preserved {before after : State} (step : Step before after) :
    after.object = before.object := by cases step <;> rfl

theorem step_epoch_nondecreasing {before after : State} (step : Step before after) :
    before.epoch ≤ after.epoch := by
  cases step
  · exact Nat.le_refl _
  · exact Nat.le_succ _

theorem resume_refuses_old_epoch (s : State) (a d h m : Nat) (object : Nat) :
    ¬ Fresh {s with epoch := s.epoch + 1, audience := a, devices := d, history := h, manifest := m, mode := .active} object (some s.epoch) := by
  apply stale_epoch_refused
  exact Nat.ne_of_lt (Nat.lt_succ_self _)

end Minidregg.Theory.ObjectAudience
