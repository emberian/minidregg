/- Current policy-control authorization remains the authority for these edits.
This validator adds phase discipline; it does not authenticate a manager or
prove that ciphertext wraps contain the claimed key. -/
import Kernel.ObjectAudience

namespace Minidregg.Kernel.ObjectAudienceController
open Minidregg.Theory.ObjectAudience
set_option autoImplicit false

/-- Explicit confidential enrollment. Existing ordinary objects stay ordinary
until an authorized policy installation carries this metadata. -/
def Initial (object : Nat) (state : State) : Prop :=
  state.object = object ∧ state.mode = .active ∧ state.manifest ≠ 0
instance (o : Nat) (s : State) : Decidable (Initial o s) := by unfold Initial; infer_instance

/-- State-preserving law updates are allowed. Removing the metadata is refused:
privacy-contract exit needs a separately named, authorized construction. -/
def Valid (object : Nat) (before after : Option State) : Prop :=
  match before, after with
  | none, none => True
  | none, some state => Initial object state
  | some old, none => False
  | some old, some next => old.object = object ∧
      (next = old ∨
       (old.mode = .active ∧ next = {old with parent := old.transition, transition := next.transition, mode := .frozen} ∧ next.transition ≠ old.transition) ∨
       (old.mode = .frozen ∧ next = {old with epoch := old.epoch + 1, audience := next.audience, devices := next.devices, history := next.history, manifest := next.manifest, mode := .active, authoritySnapshot := next.authoritySnapshot, deviceSnapshot := next.deviceSnapshot} ∧ next.manifest ≠ 0 ∧
         next.manifest ≠ old.manifest))

instance (o : Nat) (b a : Option State) : Decidable (Valid o b a) := by
  unfold Valid; split <;> infer_instance

def check (object : Nat) (before after : Option State) : Bool := decide (Valid object before after)

/-- Current authority snapshot is a preparation dependency, not a permanent
whole-authority equality requirement on later ordinary invocations. Recipient
package correctness is the authenticated distributor's responsibility. -/
def Bound (object authorityRoot deviceRoot : Nat) (before after : Option State) : Prop :=
  Valid object before after ∧
  match before, after with
  | none, some state => state.authoritySnapshot = authorityRoot ∧ state.deviceSnapshot = deviceRoot
  | some old, some next =>
      if old.mode = .frozen ∧ next.mode = .active then next.authoritySnapshot = authorityRoot ∧ next.deviceSnapshot = deviceRoot else True
  | _, _ => True
instance (o r d : Nat) (b a : Option State) : Decidable (Bound o r d b a) := by
  cases b <;> cases a <;> unfold Bound <;> infer_instance

def checkBound (object authorityRoot deviceRoot : Nat) (before after : Option State) : Bool :=
  decide (Bound object authorityRoot deviceRoot before after)

@[simp] theorem checkBound_iff (object authorityRoot deviceRoot : Nat) (before after : Option State) :
    checkBound object authorityRoot deviceRoot before after = true ↔ Bound object authorityRoot deviceRoot before after := by
  simp [checkBound]

@[simp] theorem check_iff (object : Nat) (before after : Option State) :
    check object before after = true ↔ Valid object before after := by simp [check]

theorem cannot_drop (object : Nat) (old : State) : check object (some old) none = false := by
  simp [check, Valid]

theorem valid_transition {object : Nat} {old next : State}
    (valid : Valid object (some old) (some next)) : next = old ∨ Step old next := by
  rcases valid.2 with same | freeze | resume
  · exact .inl same
  · rcases freeze with ⟨active, exactNext, fresh⟩
    exact .inr (exactNext ▸ Step.freeze old next.transition active fresh)
  · rcases resume with ⟨frozen, exactNext, material, _⟩
    exact .inr (exactNext ▸ Step.resume old next.audience next.devices next.history next.manifest next.authoritySnapshot next.deviceSnapshot frozen material)

/-- Package preparation at a different authority image cannot activate the epoch. -/
theorem resume_snapshot_bound {object authorityRoot deviceRoot : Nat} {old next : State}
    (accepted : checkBound object authorityRoot deviceRoot (some old) (some next) = true)
    (frozen : old.mode = .frozen) (active : next.mode = .active) :
    next.authoritySnapshot = authorityRoot ∧ next.deviceSnapshot = deviceRoot := by
  have bound := (checkBound_iff object authorityRoot deviceRoot (some old) (some next)).mp accepted
  simpa [frozen, active] using bound.2

end Minidregg.Kernel.ObjectAudienceController
