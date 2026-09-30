/-
Native receiving boundary for one owner-signed, selected-content release. The
caller must supply a verifier-opened recipient image. Exact historical retry
selects the retained ingress before checking today's key or law; fresh work
uses the current owner signature, capability and policy admission and one
durable CAS. This receiver makes no claim that the private source operation
was historically admitted, nor that plaintext fn transport is confidential.
-/
import Kernel.FnSelectiveReleaseAdmission

namespace Minidregg.Kernel.FnSelectiveReleaseReceiver

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.FnSelectiveReleaseIngress

set_option autoImplicit false

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (ingress : Ingress) : Receipt :=
  ⟨transactionId ingress, (event ingress).eventId⟩

def ordinaryNullifier (config : NativeHost.Config) (ingress : Ingress) :
    StableNullifier :=
  CredentialAuthorityReplay.nullifier config.deployment.domain
    (DeclaredResourceController.operationMarker config.deployment.domain
      config.profile.semantics (command ingress))

/-- In a verifier-opened image, the original record's exact event bytes and
both marker families select only the original signed ingress. A changed
packet or changed current witness under the same release key is a conflict,
not a second release. -/
def replay (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : Ingress) : Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId ingress) opened.durable.snapshot.model.journal with
  | none => none
  | some recorded =>
      if recorded.transactionId = transactionId ingress ∧
          recorded.event.event = event ingress ∧
          recorded.nullifiers =
            [ordinaryNullifier config ingress, releaseNullifier ingress.packet.release] then
        some (.ok (receipt ingress))
      else some (.error ())

theorem replay_only_original (config : NativeHost.Config)
    (opened : NativeHost.Opened config) (ingress : Ingress) (selected : Receipt)
    (found : replay config opened ingress = some (.ok selected)) :
    selected = receipt ingress ∧
      ∃ recorded,
        DurableCommitProtocol.Snapshot.lookupRecorded
          (transactionId ingress) opened.durable.snapshot.model.journal = some recorded ∧
        recorded.event.event = event ingress ∧
        recorded.nullifiers =
          [ordinaryNullifier config ingress, releaseNullifier ingress.packet.release] := by
  unfold replay at found
  split at found
  · cases found
  · rename_i recorded selectedRecord
    split at found
    · rename_i exactRecord
      have same : receipt ingress = selected := by simpa using found
      exact ⟨same.symm, recorded, selectedRecord, exactRecord.2⟩
    · cases found

inductive Reject where
  | malformedIngress
  | admission (reason : FnSelectiveReleaseAdmission.Reject)
  | durable (reason : DurableDataIntent.RejectReason)

inductive Result where
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : Receipt)
  | rejected (reason : Reject)
  | transactionConflict
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

def receiveLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (bytes : List UInt8) : IO Result := do
  match ingressCodec.decode bytes with
  | none => return .rejected .malformedIngress
  | some ingress =>
      match replay config opened ingress with
      | some (.ok retained) => return .confirmed .replayed retained
      | some (.error _) => return .transactionConflict
      | none =>
          match ← FnSelectiveReleaseAdmission.admit config opened ingress with
          | .error reason => return .rejected (.admission reason)
          | .ok accepted =>
              match ← DurableReceiverIO.receiveLoaded config.transport
                  ResourceBirthCodec.rootBytes opened.durable
                  (accepted.intent config opened ingress) with
              | .confirmed kind _ => return .confirmed kind (receipt ingress)
              | .rejected reason => return .rejected (.durable reason)
              | .contention => return .contention
              | .unavailable detail => return .unavailable detail
              | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.FnSelectiveReleaseReceiver
