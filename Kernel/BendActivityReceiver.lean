/- Actual existing durable receiver for source-admitted Activity phase changes.
No separate journal: exact event62 source record, native CAS, tail law, readback
and original same-transaction retry are used. Appended is not external dispatch
permission or a private recovery qualification. -/
import Kernel.BendActivityIngress
namespace Minidregg.Kernel.BendActivityReceiver
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

/-- A private current Activity admission selects its exact whole record and
predecessor. Every other protected facet is checked before its own exception.
config.transport retains the consensus prohibition on unordered local append. -/
def transport {config : Config} {opened : Opened config}
    (admitted : BendActivityIngress.Admitted config opened) : DurableReceiverIO.Transport :=
  { config.transport with sourceGate := fun snapshot proposed => do
      config.otherFacetGate .activity snapshot proposed
      if DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent proposed) =
          DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent admitted.intent) ∧
          snapshot.canonicalBytes admitted.pin.cell = opened.durable.snapshot.canonicalBytes admitted.pin.cell
      then .ok () else .error (.durable .transactionConflict) }

inductive Result (config : Config) (opened : Opened config) where
  | appended (admitted : BendActivityIngress.Admitted config opened)
      (receipt : DurableReceiverIO.Appended ResourceBirthCodec.rootBytes opened.durable admitted.intent)
  | replayed (recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope)
  | refused (reason : String)
  | ordinary (result : DurableReceiverIO.Result ResourceBirthCodec.rootBytes)

/-- Exact previously recorded source bytes return their original receipt before
any new source computation/admission. A different envelope sharing a transaction
ID is a conflict. No missing reply is interpreted as a fresh operation. -/
def receive (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO (Result config opened) := do
  if bytes.length > 4194304 then return .refused "activity source envelope exceeds v1 cap"
  let some source := BendActivityIngress.decode bytes | return .refused "invalid activity source"
  let some (domain,semantics,signed) := decodeSignedBytes source.signedBytes
    | return .refused "invalid activity signed source"
  if domain != config.deployment.domain || semantics != config.profile.semantics then
    return .refused "activity scope mismatch"
  let some command := commandCodec.decode signed.commandBytes | return .refused "invalid activity command"
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics command) opened.durable.snapshot.model.journal with
  | some recorded =>
    if recorded.event.event.codecVersion = 62 ∧ recorded.event.event.domain = domain ∧
        recorded.event.event.canonicalBytes = bytes then return .replayed recorded
    else return .refused "activity transaction conflict"
  | none =>
    match ← BendActivityIngress.admit config opened bytes with
    | .error reason => return .refused reason
    | .ok admitted =>
      match ← DurableReceiverIO.receiveLoadedDetailed (transport admitted)
          ResourceBirthCodec.rootBytes opened.durable admitted.intent with
      | .exact _ appended => return .appended admitted appended
      | .ordinary result => return .ordinary result

#assert_axioms transport
#assert_axioms receive
end Minidregg.Kernel.BendActivityReceiver
