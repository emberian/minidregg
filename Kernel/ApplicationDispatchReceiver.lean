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
structure Committed (config : Config) where
  private mk ::
  target : Durable
  old : NativeHostReplay.Verified config target
  ingress : ApplicationDispatchAdmissionIngress.Ingress
  admitted : NativeHostReplay.DispatchAt config old.opened ingress
  readback : NativeHostReplay.ExactReadback config old
  derivedExact : readback.derived.intent = admitted.intent
  confirmation : DurableReceiverIO.Confirmation
  freshCasWinner : Bool

def Committed.projection {config : Config} (permit : Committed config) :
    ApplicationDispatchProjection.Candidate :=
  ApplicationDispatchProjection.ofDispatchAt permit.admitted

def Committed.verified {config : Config} (permit : Committed config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate permit.old
        permit.readback.derived permit.readback.ready) :=
  NativeHostReplay.extendExact permit.old permit.readback

def Committed.receipt {config : Config} (permit : Committed config) : NativeHostCodec.Receipt :=
  let old := permit.old
  let candidate := NativeHostReplay.exactCandidate old permit.readback.derived permit.readback.ready
  ⟨permit.readback.derived.intent.transactionId,
    permit.readback.derived.intent.event.eventId,
    old.opened.durable.image.accepted.length + 1,
    candidate.worldRoot⟩

theorem Committed.receipt_in_verified {config : Config} (permit : Committed config) :
    permit.verified.receipts =
      permit.old.receipts ++ [permit.receipt] := by
  exact NativeHostReplay.extendExact_receipts
    permit.old permit.readback

/-- The permit's retained post-image is exactly the physical CAS readback,
not a later journal suffix or an asserted digest. -/
theorem Committed.postRecord_exact {config : Config} (permit : Committed config) :
    permit.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent permit.readback.derived.intent) :=
  NativeHostReplay.extendExact_physicalRecord permit.old permit.readback

/-- Receipt evidence alone cannot construct physical delivery authority. -/
structure Permit (config : Config) extends Committed config where
  private mk ::
  fresh : toCommitted.freshCasWinner = true
  installed : toCommitted.confirmation = .installed

def Permit.projection {config : Config} (permit : Permit config) :
    ApplicationDispatchProjection.Candidate := permit.toCommitted.projection

def Permit.verified {config : Config} (permit : Permit config) :
    NativeHostReplay.Verified config
      (NativeHostReplay.exactCandidate permit.old
        permit.readback.derived permit.readback.ready) := permit.toCommitted.verified

def Permit.receipt {config : Config} (permit : Permit config) : NativeHostCodec.Receipt :=
  permit.toCommitted.receipt

theorem Permit.receipt_in_verified {config : Config} (permit : Permit config) :
    permit.verified.receipts = permit.old.receipts ++ [permit.receipt] :=
  permit.toCommitted.receipt_in_verified

theorem Permit.postRecord_exact {config : Config} (permit : Permit config) :
    permit.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent permit.readback.derived.intent) :=
  permit.toCommitted.postRecord_exact

theorem Permit.won_fresh_installed {config : Config} (permit : Permit config) :
    permit.freshCasWinner = true ∧ permit.confirmation = .installed :=
  ⟨permit.fresh, permit.installed⟩

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
  unless permit.freshCasWinner && permit.confirmation == .installed do
    return .error "dispatch attempt did not freshly win physical CAS"
  let .ok current ← DurableReceiverIO.tipIs config.transport
      permit.readback.appended.next.image.accepted.length permit.readback.appended.entry
    | return .error "dispatch physical tip unavailable before handoff"
  if current then
    return .ok (← handoff permit.canonicalBytes)
  else return .error "dispatch physical tip changed before handoff"

inductive Result (config : Config) where
  | permitted (permit : Permit config)
  | committed (committed : Committed config)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- Only the successful physical CAS winner gets a permit. Exact readback
for an already-present or reply-lost request retains its original receipt. -/
def Committed.result {config : Config} (committed : Committed config) : Result config :=
  if fresh : committed.freshCasWinner = true then
    if installed : committed.confirmation = .installed then
      .permitted ⟨committed, fresh, installed⟩
    else .committed committed
  else .committed committed

theorem nonwinner_receipt_only {config : Config} (committed : Committed config)
    (notFresh : committed.freshCasWinner = false) :
    committed.result = .committed committed := by
  simp [Committed.result, notFresh]

theorem recovered_receipt_only {config : Config} (committed : Committed config)
    (recovered : committed.confirmation = .recoveredAfterUncertainResponse) :
    committed.result = .committed committed := by
  simp [Committed.result, recovered]

#assert_axioms nonwinner_receipt_only
#assert_axioms recovered_receipt_only
#assert_axioms Permit.won_fresh_installed

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
  let (freshCasWinner, result) ← DurableReceiverIO.receiveLoadedDetailedWithFresh config.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind appended =>
      match NativeHostReplay.ExactReadback.ofAppended old derived appended with
      | .error detail => return .uncertain s!"dispatch post-image validation: {detail}"
      | .ok ⟨proof, proofDerived⟩ =>
            let committed : Committed config := ⟨target, old, ingress, admitted,
              proof, ((congrArg NativeHostReplay.Derived.intent proofDerived).trans admitted.toDerived_intent),
              kind, freshCasWinner⟩
            return committed.result
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "dispatch confirmation lacks exact fresh post-CAS readback"
      | .rejected _ => return .rejected "durable dispatch refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

end Minidregg.Kernel.ApplicationDispatchReceiver
