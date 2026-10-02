/-
Pending paid-entry custody uses the existing source pre-rotation gate. The
synthetic two-row authority view is local to this decision: it grants no OS
membership or capability. A successful result updates pending custody and records its immutable epoch;
first admission later installs this CURRENT key under the stable identity.
-/
import Kernel.PayCell
import Kernel.PayClaimCommand

namespace Minidregg.Kernel.PayPendingRotation
open Minidregg.Compiler
open Minidregg.Compiler.CredentialSignatureAdmission
open Minidregg.Theory
open Minidregg.Theory.Store
open Minidregg.Theory.CredentialSigningKey
open Minidregg.Theory.TypedAuthorization (Digest SubjectId)
open Minidregg.Kernel.PayEnrolClaim (PendingOwner)
set_option autoImplicit false

/-- Synthetic records exist solely to reuse KeyPreRotation.Successor/gate.
The final receiving key id/lifetime comes from ordinary enrollment authoring. -/
def ownerRecord (owner : PendingOwner) : KeyRecord :=
  ⟨PayEnrolMemo.subjectOf owner.identityKey, owner.epoch, ed25519Algorithm,
    PayEnrolMemo.subjectOf owner.identityKey, owner.currentKey, 0, 2 ^ 64 - 1,
    some owner.nextKeyDigest⟩

def ownerAuthority (owner : PendingOwner) : Store CredentialAuthorityState.layout :=
  let subject : SubjectId := ⟨PayEnrolMemo.subjectOf owner.identityKey⟩
  ((0 : Store CredentialAuthorityState.layout).set ⟨.subjectKeyEpoch, subject⟩ (some owner.epoch)).set
    ⟨.subjectKey, (subject, owner.epoch)⟩ (some (ownerRecord owner))

def successorRecord (owner : PendingOwner) (rotation : PayClaimCommand.RotatePendingOwner) : KeyRecord :=
  { ownerRecord owner with publicKey := rotation.successorKey, keyEpoch := owner.epoch + 1,
    nextKeyDigest := some rotation.successorNextKeyDigest }

def rotationOf (owner : PendingOwner) (rotation : PayClaimCommand.RotatePendingOwner) :
    KeyPreRotation.Rotation :=
  ⟨⟨PayEnrolMemo.subjectOf owner.identityKey⟩, successorRecord owner rotation⟩

inductive Reject where
  | wrongAction | missingOwner | malformedOwner | malformedSuccessor
  | alreadyAdmitted | epochMismatch | publicKeyTaken
  | historyMismatch | historyAlreadyPresent
  | gate (reason : KeyPreRotation.Reject)
  deriving DecidableEq, Repr

/-- Current authority wins over retained pending custody. An admitted identity
must use SubjectKeyRotation and can never bypass the registry through this path.
The Checked signature is by the successor over the exact closed action frame. -/
def decide (pay : PayCell.PayStore) (authority : Store CredentialAuthorityState.layout)
    {domain semantics : Digest} (ingress : PayClaimCommand.DecodedIngress)
    (checked : PayClaimCommand.Checked domain semantics ingress) : Except Reject PendingOwner :=
  match ingress.command.action with
  | .inl _ => .error .wrongAction
  | .inr rotation =>
    match PayCell.pendingOwnerAt pay rotation.ownerIdentityKey with
    | none => .error .missingOwner
    | some owner =>
      if ¬owner.valid ∨ owner.identityKey ≠ rotation.ownerIdentityKey then .error .malformedOwner
      else if (show Option Nat from authority
          ⟨.subjectKeyEpoch, ⟨PayEnrolMemo.subjectOf owner.identityKey⟩⟩).isSome then
        .error .alreadyAdmitted
      else if rotation.expectedEpoch ≠ owner.epoch then .error .epochMismatch
      else if PayCell.pendingOwnerHistoryAt pay owner.identityKey owner.epoch ≠ some owner then
        .error .historyMismatch
      else if (PayCell.pendingOwnerHistoryAt pay owner.identityKey (owner.epoch + 1)).isSome then
        .error .historyAlreadyPresent
      else if ¬(PayEnrolClaim.rotatedOwner owner rotation.successorKey
          rotation.successorNextKeyDigest).valid then .error .malformedSuccessor
      else if ¬ParticipantKeyEnrollment.allKeys authority
          (fun key => key.publicKey != rotation.successorKey) then .error .publicKeyTaken
      else
        match KeyPreRotation.gate SubjectKeyRotation.nextKeyDigest (ownerAuthority owner)
            (rotationOf owner rotation)
            (fun key => _root_.decide (key = rotation.successorKey) && checked.valid) with
        | .error reason => .error (.gate reason)
        | .ok _ => .ok (PayEnrolClaim.rotatedOwner owner rotation.successorKey
            rotation.successorNextKeyDigest)

/-- Install only after decide accepts: the exact historical predecessor is
read, current custody is guarded, and the successor epoch is freshly allocated.
The old history is never overwritten and grants no registry authority. -/
def patch (before after : PendingOwner) : Patch PayCell.layout :=
  [.read .pendingOwnerHistory (before.identityKey, before.epoch) (some before),
   .write .pendingOwner before.identityKey before after,
   .allocate .pendingOwnerHistory (after.identityKey, after.epoch) after]

/-- Source decision and patch construction are joined; callers cannot supply a
different successor in place of the precommitted key accepted by the gate. -/
def decidedPatch (pay : PayCell.PayStore) (authority : Store CredentialAuthorityState.layout)
    {domain semantics : Digest} (ingress : PayClaimCommand.DecodedIngress)
    (checked : PayClaimCommand.Checked domain semantics ingress) : Except Reject (Patch PayCell.layout) := do
  let after ← decide pay authority ingress checked
  match PayCell.pendingOwnerAt pay after.identityKey with
  | none => .error .missingOwner
  | some before => .ok (patch before after)

theorem patch_requires_previous_history (pay : PayCell.PayStore) (before after : PendingOwner)
    (valid : Patch.ValidFrom pay (patch before after)) :
    PayCell.pendingOwnerHistoryAt pay before.identityKey before.epoch = some before :=
  valid.1

theorem patch_requires_exact_current (pay : PayCell.PayStore) (before after : PendingOwner)
    (valid : Patch.ValidFrom pay (patch before after)) :
    PayCell.pendingOwnerAt pay before.identityKey = some before :=
  valid.2.1.2

theorem patch_records_successor (pay : PayCell.PayStore) (before after : PendingOwner) :
    PayCell.pendingOwnerHistoryAt (Patch.run pay (patch before after))
      after.identityKey after.epoch = some after :=
  Store.set_eq _ _ _

theorem patch_updates_current (pay : PayCell.PayStore) (before after : PendingOwner) :
    PayCell.pendingOwnerAt (Patch.run pay (patch before after)) before.identityKey = some after := by
  change ((pay.set (PayCell.pendingOwnerAddress before.identityKey) (some after)).set
    (PayCell.pendingOwnerHistoryAddress after.identityKey after.epoch) (some after))
    (PayCell.pendingOwnerAddress before.identityKey) = some after
  rw [Store.set_ne _ _ _ _ (by intro same; cases same)]
  exact Store.set_eq _ _ _

theorem patch_requires_new_history (pay : PayCell.PayStore) (before after : PendingOwner)
    (valid : Patch.ValidFrom pay (patch before after)) :
    PayCell.pendingOwnerHistoryAt pay after.identityKey after.epoch = none := by
  have fresh := valid.2.2.1.2
  change (pay.set (PayCell.pendingOwnerAddress before.identityKey) (some after))
    (PayCell.pendingOwnerHistoryAddress after.identityKey after.epoch) = none at fresh
  rw [Store.set_ne _ _ _ _ (by intro same; cases same)] at fresh
  exact fresh

/-- Allocating a distinct successor epoch leaves the historical predecessor
byte-for-byte available for provenance checks after eventual admission. -/
theorem patch_preserves_previous_history (pay : PayCell.PayStore) (before after : PendingOwner)
    (different : before.epoch ≠ after.epoch) :
    PayCell.pendingOwnerHistoryAt (Patch.run pay (patch before after))
      before.identityKey before.epoch =
      PayCell.pendingOwnerHistoryAt pay before.identityKey before.epoch := by
  apply Patch.run_frame
  simp [patch, Patch.writeFootprint, Op.writeAddress?, Op.address,
    PayCell.pendingOwnerHistoryAddress, different]

/-- The source gate, rather than an alternative custody-specific crypto recipe,
requires the exact previously committed successor and its possession signature. -/
theorem gate_requires_precommitment (owner : PendingOwner)
    (rotation : PayClaimCommand.RotatePendingOwner) (signed : List UInt8 → Bool)
    (current : KeyRecord)
    (accepted : KeyPreRotation.gate SubjectKeyRotation.nextKeyDigest (ownerAuthority owner)
      (rotationOf owner rotation) signed = .ok current) :
    current.nextKeyDigest = some (SubjectKeyRotation.nextKeyDigest rotation.successorKey) :=
  (KeyPreRotation.rotation_requires_precommitted_key accepted).2

theorem successor_keeps_stable_identity (owner : PendingOwner)
    (rotation : PayClaimCommand.RotatePendingOwner) :
    (PayEnrolClaim.rotatedOwner owner rotation.successorKey rotation.successorNextKeyDigest).identityKey =
      owner.identityKey := rfl

#assert_axioms patch_preserves_previous_history
#assert_axioms patch_requires_previous_history
#assert_axioms patch_requires_exact_current
#assert_axioms patch_records_successor
#assert_axioms patch_updates_current
#assert_axioms patch_requires_new_history
#assert_axioms gate_requires_precommitment
#assert_axioms successor_keeps_stable_identity
end Minidregg.Kernel.PayPendingRotation
