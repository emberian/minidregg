/-
Fresh physical dispatch receiving. The only permit-producing branch is a new
special event 11 committed by CAS and confirmed against the exact complete
post-image bytes. Historical receipt recovery, generic DRC event 3, a
concurrent suffix, and an uncertain CAS response are not delivery permits.
-/
import Kernel.ApplicationDispatchProjection

namespace Minidregg.Kernel.ApplicationDispatchReceiver

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.IndexedProgram
open Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- The constructor is private. `readback` comes only from the exact physical
CAS branch, and `verified` extends that same source-admitted dispatch. -/
structure Permit (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationDispatchAdmissionIngress.Ingress
  admitted : NativeHostReplay.DispatchAt config old.opened ingress
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = admitted.intent
  confirmation : DurableReceiverIO.Confirmation

def Permit.projection {config : Config} (permit : Permit config) :
    ApplicationDispatchProjection.Candidate :=
  ApplicationDispatchProjection.ofDispatchAt permit.admitted

def Permit.verified {config : Config} (permit : Permit config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate permit.old
        permit.readback.derived permit.readback.ready) :=
  NativeHostReplay.extendExact permit.old permit.readback

def Permit.receipt {config : Config} (permit : Permit config) : NativeHostCodec.Receipt :=
  let old := permit.old
  let candidate := NativeHostReplay.exactCandidate old permit.readback.derived permit.readback.ready
  ⟨permit.readback.derived.intent.transactionId,
    permit.readback.derived.intent.event.eventId,
    old.opened.durable.image.accepted.length + 1,
    imageBoundary config candidate.image⟩

theorem Permit.receipt_in_verified {config : Config} (permit : Permit config) :
    permit.verified.receipts =
      permit.old.receipts ++ [permit.receipt] := by
  exact NativeHostReplay.extendExact_receipts
    permit.old permit.readback

/-- The permit's retained post-image is exactly the physical CAS readback,
not a later journal suffix or an asserted digest. -/
theorem Permit.postBytes_exact {config : Config} (permit : Permit config) :
    permit.verified.opened.durable.bytes = permit.readback.physicalBytes :=
  NativeHostReplay.extendExact_physicalBytes
    permit.old permit.readback

/-- A distinct wire frame ensures the physical host cannot confuse a checked
candidate with an actually committed dispatch permit. The host accepts this
frame only from its fixed native process, never from client HTTP bytes. -/
private def permitCodec : LawfulCodec
    (ApplicationDispatchProjection.Candidate × NativeHostCodec.Receipt) :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/DISPATCH-COMMITTED-PERMIT/v1".toUTF8.toList
    (StreamCodec.product ApplicationDispatchProjection.candidateStream
      NativeHostCodec.receiptStream)

/-- Strict read-only inspection of a committed-frame shape. Decoding bytes
does not establish CAS provenance: only `Permit.withFreshTip` may supply this
frame to the physical host's private op34 response channel. -/
def inspectCommittedBytes (bytes : List UInt8) :
    Option (ApplicationDispatchProjection.Candidate × NativeHostCodec.Receipt) :=
  permitCodec.decode bytes

private def Permit.canonicalBytes {config : Config} (permit : Permit config) : List UInt8 :=
  permitCodec.encode (permit.projection, permit.receipt)

/-- A committed frame is offered only while a fresh physical read still equals
the exact post-CAS bytes. The Host callback writes and flushes the native
response; app fd3 delivery is a later physical hop. This point-in-time check
is not a lease or cancellation barrier against later turns, and it does not
lock out concurrent writers after the read. -/
def Permit.withFreshTip {config : Config} {α : Type} (permit : Permit config)
    (handoff : List UInt8 → IO α) : IO (Except String α) := do
  let .ok (some current) ← config.storage.transport.read
    | return .error "dispatch physical tip unavailable before handoff"
  if exact : current.toByteArray == permit.readback.physicalBytes.toByteArray then
    have _currentExact : current = permit.readback.physicalBytes :=
      (DurableReceiverIO.byteArray_beq_exact _ _).mp exact
    return .ok (← handoff permit.canonicalBytes)
  else return .error "dispatch physical tip changed before handoff"

inductive Result (config : Config) where
  | permitted (permit : Permit config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- A warm Host session carries `old` from initial verified replay or exact
extension. Every request still runs fresh current native admission. No full
history walk is repeated merely to select the original share issue. A
duplicate ordinary DRC transaction ID, including a different outer HTTP
wrapper under the same signed command, conflicts before CAS. -/
def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes
    | return .rejected "noncanonical special dispatch ingress"
  if ingress.dispatch.dispatch.session.origin != .human then
    return .rejected "v1 committed dispatch permit requires human-origin session"
  let .ok admitted ← NativeHostReplay.admitDispatchVerified old ingress
    | return .rejected "dispatch issue absent from verified chronological prefix"
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "dispatch transaction identity already used"
  let result ← DurableReceiverIO.receiveLoadedDetailed config.storage.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind ready preparedEq readback readbackExact =>
      let candidate := NativeHostReplay.exactCandidate old derived ready
      match validated : validateLoaded config candidate with
      | .error detail => return .uncertain s!"dispatch post-image validation: {detail}"
      | .ok after =>
          if afterExact : after.durable.bytes.toByteArray == candidate.bytes.toByteArray then
            let proof : NativeHostReplay.ExactReadback config old :=
              { derived := derived
                ready := ready
                prepared := preparedEq
                physicalBytes := readback
                exactBytes := readbackExact
                after := after
                validated := validated
                afterExact := (DurableReceiverIO.byteArray_beq_exact _ _).mp afterExact }
            return .permitted ⟨target, old, ingress, admitted,
              proof, admitted.toDerived_intent, kind⟩
          else return .uncertain "dispatch validated successor bytes changed"
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "dispatch confirmation lacks exact fresh post-CAS readback"
      | .rejected _ => return .rejected "durable dispatch refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationDispatchReceiver
