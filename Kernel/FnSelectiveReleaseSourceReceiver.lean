/-
Durable source authorization for one owner-selected public release. Current
`.delegateObject` authority and the exact selected content version are checked
before a read-guarded event-only CAS. Exact historical retry selects the
accepted packet/envelope without reapplying changed current law. Fn transport
may only attribute source authorization to an accepted event, not preparation.
-/
import Kernel.FnSelectiveReleaseSourceAuthority
import Kernel.NativeHostContext

namespace Minidregg.Kernel.FnSelectiveReleaseSourceReceiver

open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.FnSelectiveReleaseSourcePublication

set_option autoImplicit false

structure Receipt where
  transactionId : Digest
  eventId : Digest
  deriving DecidableEq, Repr

def receipt (ingress : Ingress) : Receipt :=
  ⟨transactionId ingress.spec, (event ingress).eventId⟩

def sourceContext (config : NativeHost.Config) (opened : NativeHost.Opened config) :
    ResourceObservationAdmission.Context config.deployment opened.durable :=
  ⟨opened.directory, opened.authority⟩

def replay {config : NativeHost.Config} (opened : NativeHost.Opened config) (ingress : Ingress) :
    Option (Except Unit Receipt) :=
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId ingress.spec) opened.durable.snapshot.model.journal with
  | none => none
  | some recorded =>
      if recorded.transactionId = transactionId ingress.spec ∧
          recorded.event.event = event ingress ∧
          recorded.nullifiers = [nullifier ingress.spec] then
        some (.ok (receipt ingress))
      else some (.error ())

def charge (ingress : Ingress) : ResourceCost.Charge
  | .incidences => 1
  | .turnBytes => (ingressCodec.encode ingress).length
  | .memoryTouches => 1
  | .storageBytes => (ingressCodec.encode ingress).length
  | .witnessBytes => (ingressCodec.encode ingress).length
  | .proofWork => 1
  | .sideEffectCount => 1
  | .feeDebit | .networkBytes | .leaseByteBlocks => 0

structure Accepted (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : Ingress) where
  private mk ::
  prepared : FnSelectiveReleaseSourceAuthority.Prepared
    (sourceContext config opened) config.profile config.federation
    (NativeHost.logicalHeight config opened.durable) ingress.spec
  checked : FnSelectiveReleaseSourceAuthority.Checked prepared ingress.nativeEnvelope

def admitLoaded (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : Ingress) : IO (Except String (Accepted config opened ingress)) := do
  let context := sourceContext config opened
  match FnSelectiveReleaseSourceAuthority.prepare context config.profile
      config.federation (NativeHost.logicalHeight config opened.durable)
      ingress.spec with
  | .error reason => return .error reason
  | .ok prepared =>
      match ← FnSelectiveReleaseSourceAuthority.check config.signature
          prepared ingress.nativeEnvelope with
      | .error reason => return .error reason
      | .ok checked => return .ok ⟨prepared, checked⟩

/-- Side effect count 1 charges the accepted authorization event. The fn POST
is external and cannot be inferred from this Mini receipt. -/
def Accepted.intent (config : NativeHost.Config) (opened : NativeHost.Opened config)
    (ingress : Ingress) (accepted : Accepted config opened ingress) :
    DataIntent ResourceBirthCodec.rootBytes :=
  { transactionId := transactionId ingress.spec
    writes := []
    readGuards := [FnSelectiveReleaseSourceAuthority.readGuard accepted.prepared] ++
      (sourceContext config opened).authority.readGuards
    nullifiers := [nullifier ingress.spec]
    exactCharge := charge ingress
    event := event ingress
    subject := some ⟨ingress.spec.packet.release.owner.subject⟩
    postRootsBound := by intro write present; cases present
    guardsReadOnly := by intro guard _; simp }

inductive Reject where
  | malformedIngress
  | sourceAuthority
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
  let some ingress := ingressCodec.decode bytes
    | return .rejected .malformedIngress
  match replay opened ingress with
  | some (.ok retained) => return .confirmed .replayed retained
  | some (.error _) => return .transactionConflict
  | none =>
      match ← admitLoaded config opened ingress with
      | .error _ => return .rejected .sourceAuthority
      | .ok accepted =>
          match ← DurableReceiverIO.receiveLoaded config.transport
              ResourceBirthCodec.rootBytes opened.durable
              (accepted.intent config opened ingress) with
          | .confirmed kind _ => return .confirmed kind (receipt ingress)
          | .rejected reason => return .rejected (.durable reason)
          | .contention => return .contention
          | .unavailable detail => return .unavailable detail
          | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.FnSelectiveReleaseSourceReceiver
