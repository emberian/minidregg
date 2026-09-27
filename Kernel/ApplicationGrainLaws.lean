/- Kernel facts about the proposed application resource law. These are
properties of the source predicate and canonical codec, not evidence that a
physical SPK process ran or an HTTP request was authorized for dispatch. -/
import Kernel.ApplicationGrain

namespace Minidregg.Kernel.ApplicationGrain
open Minidregg.Pred
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.DeclaredResourceProjection
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Full canonical dispatch bytes retain every intent field. A future private
receiver must still check those fields against current app/interface/session
authority before minting a permit. -/
theorem dispatch_bytes_injective : Function.Injective DispatchIntent.canonicalBytes := by
  intro left right same
  have decoded := congrArg dispatchCodec.decode same
  exact Option.some.inj (by
    simpa only [DispatchIntent.canonicalBytes, dispatchCodec.decode_encode] using decoded)

theorem completion_without_checked_slot_refused :
    eval completionGate ⟨[]⟩ ⟨[]⟩ = false := by decide

theorem completion_with_zero_slot_refused :
    eval completionGate ⟨[]⟩ ⟨[(completionSlot, 0)]⟩ = false := by decide

theorem reconciliation_without_checked_slot_refused :
    eval reconciliationGate ⟨[]⟩ ⟨[]⟩ = false := by decide

theorem reconciliation_with_zero_slot_refused :
    eval reconciliationGate ⟨[]⟩ ⟨[(reconciliationSlot, 0)]⟩ = false := by decide

theorem serving_witness_exact (before : State) :
    Operation.after .servingWitness before = before := by
  rfl

/-- The ordinary four-field scalar projection never manufactures a checked
completion slot. A checked native receiver must add it from independent
evidence; a candidate action cannot smuggle it through its page values. -/
theorem scalar_slots_no_completion (before after : State) :
    (⟨slots before after⟩ : Minidregg.Pred.State).get completionSlot = none := by
  simp [Minidregg.Pred.State.get, slots, State.coordinates,
    DeclaredResourceProjection.scalarSlots,
    Minidregg.Kernel.DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    completionSlot, Nat.repr_eq_ofList_toDigits, Nat.toDigits,
    Nat.toDigitsCore, Nat.digitChar, toString]

theorem scalar_slots_no_reconciliation (before after : State) :
    (⟨slots before after⟩ : Minidregg.Pred.State).get reconciliationSlot = none := by
  simp [Minidregg.Pred.State.get, slots, State.coordinates,
    DeclaredResourceProjection.scalarSlots,
    Minidregg.Kernel.DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    reconciliationSlot, Nat.repr_eq_ofList_toDigits, Nat.toDigits,
    Nat.toDigitsCore, Nat.digitChar, toString]

/-- Any transition admitted by the installed application predicate keeps or
advances lifecycle generation. `joint` is the receiver's prepared projection of
the other authorized targets. -/
theorem accepted_generation_nondec (packageTarget snapshotTarget : Nat)
    (distinct : packageTarget ≠ snapshotTarget) (before after : State)
    (joint : List (String × Int))
    (accepted : eval (transitionPolicy packageTarget snapshotTarget) ⟨[]⟩
      ⟨slots before after ++ joint⟩ = true) :
    before.generation ≤ after.generation := by
  unfold transitionPolicy at accepted
  simp only [if_neg distinct] at accepted
  rw [eval_all] at accepted
  have bound := (List.all_eq_true.mp accepted)
    (.memberOf "resource/field/0/delta" [0,1]) (by simp)
  simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates,
    DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
    DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
    Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar,
    toString] at bound
  omega

/-- The app law refuses a package-version advance unless the same prepared
joint command contains an actual content operation at the configured manifest
target. The content resource's own law supplies the converse restriction. -/
theorem accepted_package_advance_requires_content (packageTarget snapshotTarget : Nat)
    (distinct : packageTarget ≠ snapshotTarget) (before after : State)
    (joint : List (String × Int))
    (accepted : eval (transitionPolicy packageTarget snapshotTarget) ⟨[]⟩
      ⟨slots before after ++ joint⟩ = true)
    (advanced : before.packageVersion < after.packageVersion) :
    eval (contentChanged packageTarget)
      ⟨[]⟩ ⟨slots before after ++ joint⟩ = true := by
  unfold transitionPolicy at accepted
  simp only [if_neg distinct] at accepted
  rw [eval_all] at accepted
  have coupled := (List.all_eq_true.mp accepted)
    (.any [.eq "resource/field/2/delta" 0, contentChanged packageTarget]) (by simp)
  rw [eval_any] at coupled
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at coupled
  rcases coupled with zero | content
  · simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates,
      DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
      DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
      Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar,
      toString] at zero
    omega
  · exact content

theorem accepted_snapshot_advance_requires_content (packageTarget snapshotTarget : Nat)
    (distinct : packageTarget ≠ snapshotTarget) (before after : State)
    (joint : List (String × Int))
    (accepted : eval (transitionPolicy packageTarget snapshotTarget) ⟨[]⟩
      ⟨slots before after ++ joint⟩ = true)
    (advanced : before.snapshotVersion < after.snapshotVersion) :
    eval (contentChanged snapshotTarget)
      ⟨[]⟩ ⟨slots before after ++ joint⟩ = true := by
  unfold transitionPolicy at accepted
  simp only [if_neg distinct] at accepted
  rw [eval_all] at accepted
  have coupled := (List.all_eq_true.mp accepted)
    (.any [.eq "resource/field/3/delta" 0, contentChanged snapshotTarget]) (by simp)
  rw [eval_any] at coupled
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at coupled
  rcases coupled with zero | content
  · simp [eval, evalWith, Minidregg.Pred.State.get, slots, State.coordinates,
      DeclaredResourceProjection.scalarSlots, DeclaredResourceProjection.get,
      DeclaredResourceProjection.fieldName, DeclaredResourceProjection.pairName,
      Nat.repr_eq_ofList_toDigits, Nat.toDigits, Nat.toDigitsCore, Nat.digitChar,
      toString] at zero
    omega
  · exact content

theorem operation_generation_nondec (operation : Operation) (before : State) :
    before.generation ≤ (operation.after before).generation := by
  cases operation <;> simp [Operation.after]

theorem operation_package_nondec (operation : Operation) (before : State) :
    before.packageVersion ≤ (operation.after before).packageVersion := by
  cases operation <;> simp [Operation.after]

theorem operation_snapshot_nondec (operation : Operation) (before : State) :
    before.snapshotVersion ≤ (operation.after before).snapshotVersion := by
  cases operation <;> simp [Operation.after]

theorem only_checkpoint_changes_snapshot (operation : Operation) (before : State)
    (notCheckpoint : operation ≠ .checkpoint) :
    (operation.after before).snapshotVersion = before.snapshotVersion := by
  cases operation <;> simp_all [Operation.after]

theorem only_completion_changes_package (operation : Operation) (before : State)
    (notInstall : operation ≠ .completeInstall)
    (notUpgrade : operation ≠ .completeUpgrade) :
    (operation.after before).packageVersion = before.packageVersion := by
  cases operation <;> simp_all [Operation.after]

theorem checkpoint_preserves_serving_generation (before : State) :
    (Operation.checkpoint.after before).generation = before.generation ∧
    (Operation.checkpoint.after before).phase = before.phase := by
  simp [Operation.after]

theorem completed_stop_does_not_retire (before : State) :
    (Operation.completeStop.after before).phase = 2 := by
  simp [Operation.after]

theorem lifecycle_command_retains_content (operation : Operation) (subject : SubjectId)
    (authorityRoot : Digest) (nonce app : Nat) (capability : CapabilityId)
    (expectedRoot : Digest) (before : State)
    (contentTargets : List DeclaredResourceController.Target)
    (observeCapability : Option CapabilityId) :
    (operation.command subject authorityRoot nonce app capability expectedRoot before
      contentTargets observeCapability).targets.tail = contentTargets := rfl

end Minidregg.Kernel.ApplicationGrain
