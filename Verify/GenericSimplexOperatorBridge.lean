import Verify.GenericSimplexSourceHarness
import Kernel.NativeHost

namespace Minidregg.Verify.GenericSimplexOperatorBridge
open Minidregg.Compiler
open Minidregg.Kernel.GenericSimplex
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexParticipant
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Verify.GenericSimplexSourceHarness
set_option autoImplicit false

/-- Recover the exact certified record already installed at any participant.
This searches native verified history, never an operator-supplied record: each
participant's accepted log is read in verified `Reader.range` windows
(`NativeHost.operatorAcceptedLog`, an operator tool, not a request path). -/
def retainedPayload (replicas : Array Replica) (ingress : Bytes) : IO (Option Bytes) := do
  for replica in replicas do
    let log ← Minidregg.Kernel.NativeHost.operatorAcceptedLogOfDurable replica.config
      replica.participant.source.target
    if let some payload := log.findSome? fun record =>
        if record.event.canonicalBytes == ingress then
          some (DurableCheckpointCodec.recordFrame.encode record)
        else none then
      return some payload
  return none

/-- Recover an offered complete source record from the actual durable engine
journal. Only exact canonical source-record bytes containing this original
signed ingress qualify. This is pending work, never an installed receipt. -/
def retainedOfferedPayload (replicas : Array Replica) (ingress : Bytes) :
    IO (Option Bytes) := do
  for replica in replicas do
    let p := replica.participant
    let some prior ← p.runtime.current
      | throw (IO.userError "pending recovery journal refused")
    let state := prior.state
    for payload in state.offers do
      if let some record := DurableCheckpointCodec.recordFrame.decode payload then
        if DurableCheckpointCodec.recordFrame.encode record == payload &&
            record.event.canonicalBytes == ingress then
          return some payload
  return none

/-- Completion compares the exact source prefix through this call. Later
independent agreed records may already have reached only some replicas. -/
def receiptPrefix (replica : Replica) (ingress : Bytes) : Option (List Bytes) := do
  let records := replica.participant.source.verified.opened.durable.image.accepted
  let index ← records.findIdx? (fun record => record.event.canonicalBytes == ingress)
  return (records.take (index + 1)).map DurableCheckpointCodec.recordFrame.encode

/-- `receiptPrefix` over the Reader's verified windows (the pure form above is kept
only for `Verify.NativeJointSourceFixture` until its lane ports it). -/
def receiptPrefixVerified (replica : Replica) (ingress : Bytes) : IO (Option (List Bytes)) := do
  let records ← Minidregg.Kernel.NativeHost.operatorAcceptedLogOfDurable replica.config
    replica.participant.source.target
  return do
    let index ← records.findIdx? (fun record => record.event.canonicalBytes == ingress)
    pure ((records.take (index + 1)).map DurableCheckpointCodec.recordFrame.encode)

def reload (replicas : Array Replica) : IO (Array Replica) := do
  let mut result := #[]
  for replica in replicas do
    try
      let (participant,_) ← reloadSource replica.participant
      result := result.push ⟨replica.config,participant⟩
    catch _ =>
      result := result.push replica
  return result

/-- A local four-participant operator consumer, not a new admission authority.
It accepts only the original native SignedCall. An already installed record is
caught up from retained consensus evidence before returning a receipt; it is
never submitted again. Unknown completion after an exception stays uncertain.
The fixed public diagnostic does not disclose private admission failures. -/
def submit (fuel : Nat) (replicas : Array Replica) (callBytes : Bytes) :
    IO (Array Replica × Outcome) := do
  let current ← reload replicas
  try
    require (current.size == 4) "operator requires four source participants"
    let some first := current[0]? | throw (IO.userError "missing source participant")
    for replica in current do
      require (replica.participant.runtime.context == first.participant.runtime.context)
        "operator participants differ in consensus context"
    let ingress ← IO.ofExcept (sourceIngressOfCall first.config callBytes)
    let previous ← retainedPayload current ingress
    let pending ← if previous.isSome then pure none else retainedOfferedPayload current ingress
    let finished ← match previous.orElse (fun _ => pending) with
      | some payload => drive fuel current payload []
      | none => runCall fuel current callBytes
    let some first := finished[0]? | throw (IO.userError "missing finished source participant")
    let some receipt := completedCall first.participant callBytes
      | throw (IO.userError "source agreement lacks original-call receipt")
    let some expectedPrefix ← receiptPrefixVerified first ingress
      | throw (IO.userError "source agreement lacks original-call prefix")
    for replica in finished do
      let some other := completedCall replica.participant callBytes
        | throw (IO.userError "source participant has no original-call receipt")
      require (receiptStream.encode other == receiptStream.encode receipt)
        "source participants disagree on exact receipt"
      require ((← receiptPrefixVerified replica ingress) == some expectedPrefix)
        "source participants disagree on the exact prefix through this call"
    let kind := if previous.isSome then DurableReceiverIO.Confirmation.replayed
      else DurableReceiverIO.Confirmation.installed
    return (finished,.confirmed kind receipt)
  catch error =>
    IO.eprintln s!"agreement operator: completion unavailable: {error}"
    let reloaded ← reload current
    return (reloaded,.uncertain "agreement completion unavailable; use exact original-call lookup".toUTF8.toList)

end Minidregg.Verify.GenericSimplexOperatorBridge
