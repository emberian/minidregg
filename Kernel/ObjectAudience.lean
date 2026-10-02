import Theory.ObjectAudience

namespace Minidregg.Kernel.ObjectAudience
open Minidregg.Theory.ObjectAudience
set_option autoImplicit false

inductive Reject where
  | malformed | frozen | wrongObject | epoch | transition
  deriving DecidableEq, Repr

def checkFresh (audience : Option State) (object : Nat) (epoch : Option Nat) : Except Reject Unit :=
  match audience with
  | none => .ok ()
  | some state =>
      if state.object ≠ object then .error .wrongObject
      else if state.mode ≠ .active then .error .frozen
      else if epoch ≠ some state.epoch then .error .epoch
      else .ok ()

/-- This check composes with the existing resource-authorized revocation, not
with an owner bypass. Ordinary objects retain their existing revocation route. -/
def checkRevoke (audience : Option State) (object : Nat) : Except Reject Unit :=
  match audience with
  | none => .ok ()
  | some state =>
      if state.object ≠ object then .error .wrongObject
      else if state.mode ≠ .frozen then .error .transition
      else .ok ()

theorem checkFresh_protected_sound {object : Nat} {epoch : Option Nat}
    {state : State} (accepted : checkFresh (some state) object epoch = .ok ()) :
    Fresh state object epoch := by
  simp only [checkFresh] at accepted
  split at accepted
  · contradiction
  · next ho =>
      split at accepted
      · contradiction
      · next hm =>
          split at accepted
          · contradiction
          · next he => exact ⟨by simpa using ho, by simpa using hm, by simpa using he⟩

/-- A protected object's accepted revocation necessarily follows freeze.
Current capability/policy authorization is checked by the existing controller. -/
theorem checkRevoke_protected_sound {object : Nat} {state : State}
    (accepted : checkRevoke (some state) object = .ok ()) :
    state.object = object ∧ state.mode = .frozen := by
  simp only [checkRevoke] at accepted
  split at accepted
  · contradiction
  · next ho =>
      split at accepted
      · contradiction
      · next hm => exact ⟨by simpa using ho, by simpa using hm⟩

theorem frozen_fresh_refused (state : State) (object : Nat) (epoch : Option Nat)
    (frozen : state.mode = .frozen) : checkFresh (some state) object epoch ≠ .ok () := by
  intro accepted
  exact frozen_refuses_fresh state frozen object epoch (checkFresh_protected_sound accepted)

theorem unbound_fresh_refused (state : State) (object : Nat) :
    checkFresh (some state) object none ≠ .ok () := by
  intro accepted
  exact missing_epoch_refused state object (checkFresh_protected_sound accepted)

end Minidregg.Kernel.ObjectAudience
