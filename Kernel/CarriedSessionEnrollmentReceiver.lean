/- One current-profile event28 CAS after an authenticated carry anchor. The
receiver consumes the real suffix admission token and returns its extension;
old-prefix records are never represented as target-profile admitted history. -/
import Kernel.NativeHostReplay

namespace Minidregg.Kernel.CarriedSessionEnrollmentReceiver

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.ApplicationGrainSessionEnrollmentSource

set_option autoImplicit false

private def transaction (config : Config) (ingress : Ingress) :
    Option Minidregg.Theory.TypedAuthorization.Digest := do
  let (domain, semantics, signed) ←
    DeclaredResourceController.decodeSignedBytes ingress.signedBytes
  if domain != config.deployment.domain || semantics != config.profile.semantics then none else
  let command ← DeclaredResourceController.commandCodec.decode signed.commandBytes
  some (DeclaredResourceController.transactionId domain semantics command)

/-- Any occupied transaction is terminal for this attempt. An old-segment
transaction has no suffix receipt and must be queried through its own capsule;
we neither reconstruct its root under this profile nor retry it as fresh work. -/
def lookupVerified {config : Config} {anchor : Opened config} {target : Durable}
    (verified : NativeHostReplay.SuffixVerified config anchor target) (ingress : Ingress) :
    Option (Except String Receipt) := do
  let some tx := transaction config ingress
    | some (.error "noncanonical enrollment signed command")
  let some index := verified.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == tx)
    | none
  let some record := verified.opened.durable.image.accepted[index]?
    | some (.error "enrollment original record unavailable")
  let some receipt := verified.receiptAt index
    | some (.error "enrollment original receipt belongs to another segment or is unavailable")
  let event := ApplicationGrainSessionEnrollmentSource.event config.deployment.domain ingress
  if record.event == event && receipt.transactionId == tx &&
      receipt.eventId == event.eventId && receipt.acceptedCount == index + 1 then
    some (.ok receipt)
  else some (.error "enrollment transaction has a different original")

/-- Carries both the exact physical readback and the resulting native suffix
admission. Only this receiver constructs the value after checking their join. -/
structure Confirmed (config : Config) (anchor : Opened config) where
  private mk ::
  oldTarget : Durable
  old : NativeHostReplay.SuffixVerified config anchor oldTarget
  ingress : Ingress
  derived : NativeHostReplay.SuffixDerived config old.opened
  derivedEvent : derived.intent.event =
    ApplicationGrainSessionEnrollmentSource.event config.deployment.domain ingress
  appended : DurableReceiverIO.Appended rootBytes old.opened.durable derived.intent
  verified : NativeHostReplay.SuffixVerified config anchor appended.next
  receipt : Receipt
  receiptExact : verified.receiptAt old.opened.durable.height = some receipt
  confirmation : DurableReceiverIO.Confirmation

def Confirmed.target {config : Config} {anchor : Opened config}
    (confirmed : Confirmed config anchor) : Durable := confirmed.appended.next

theorem Confirmed.postRecord_exact {config : Config} {anchor : Opened config}
    (confirmed : Confirmed config anchor) :
    confirmed.appended.entry.record = DurableCheckpointCodec.recordFrame.encode
      (DurableReceiver.IntentRecord.ofIntent confirmed.derived.intent) :=
  confirmed.appended.entryExact

theorem Confirmed.original_receipt {config : Config} {anchor : Opened config}
    (confirmed : Confirmed config anchor) :
    confirmed.verified.receiptAt confirmed.old.opened.durable.height =
      some confirmed.receipt := confirmed.receiptExact

inductive Result (config : Config) (anchor : Opened config) where
  | confirmed (confirmed : Confirmed config anchor)
  | historical (receipt : Receipt)
  | rejected (detail : String)
  | transactionConflict
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- Lookup first, then current admission and one shared durable receive. A CAS
success is confirmed only after the actual readback image has extended the same
suffix verifier; inability to establish that postcondition remains uncertain. -/
def receiveVerified {config : Config} {anchor : Opened config} {target : Durable}
    (verified : NativeHostReplay.SuffixVerified config anchor target) (bytes : List UInt8) :
    IO (Result config anchor) := do
  let some ingress := ingressCodec.decode bytes
    | return .rejected "noncanonical enrollment ingress"
  unless ingress.canonicalBytes.toByteArray == bytes.toByteArray do
    return .rejected "noncanonical enrollment ingress"
  match lookupVerified verified ingress with
  | some (.ok receipt) => return .historical receipt
  | some (.error _) => return .transactionConflict
  | none =>
      let derived ← match ← NativeHostReplay.deriveSuffixVerified verified bytes with
        | .error detail => return .rejected detail
        | .ok derived => pure derived
      if derivedEvent : derived.intent.event =
          ApplicationGrainSessionEnrollmentSource.event config.deployment.domain ingress then
        let some tx := transaction config ingress
          | return .rejected "noncanonical enrollment signed command"
        if derived.intent.transactionId != tx then
          return .rejected "enrollment derived transaction differs"
        match ← DurableReceiverIO.receiveLoadedDetailed config.transport rootBytes
            verified.opened.durable derived.intent with
        | .exact kind appended =>
            match ← NativeHostReplay.extendSuffixVerified config verified appended.next with
            | .error failure => return .uncertain s!"enrollment post-image: {failure.detail}"
            | .ok extended =>
                match receiptExact : extended.receiptAt verified.opened.durable.height with
                | none => return .uncertain "enrollment original suffix receipt unavailable"
                | some receipt =>
                    if receipt.transactionId != tx ||
                        receipt.eventId != derived.intent.event.eventId ||
                        receipt.acceptedCount != verified.opened.durable.height + 1 ||
                        receipt.worldRoot != appended.next.worldRoot then
                      return .uncertain "enrollment original suffix receipt differs"
                    return .confirmed ⟨target, verified, ingress, derived, derivedEvent,
                      appended, extended, receipt, receiptExact, kind⟩
        | .ordinary ordinary =>
            match ordinary with
            | .confirmed _ _ => return .uncertain "enrollment lacks exact post-CAS readback"
            | .rejected _ => return .rejected "durable enrollment refused"
            | .contention => return .contention
            | .unavailable detail => return .unavailable detail
            | .uncertain detail => return .uncertain detail
      else return .rejected "enrollment derived event differs"

end Minidregg.Kernel.CarriedSessionEnrollmentReceiver
