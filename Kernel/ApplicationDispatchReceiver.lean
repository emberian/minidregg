/-
Fresh physical dispatch receiving. The only permit-producing branch is a new
special event 11 committed by CAS and confirmed against the exact complete
post-image bytes. Historical receipt recovery, generic DRC event 3, a
concurrent suffix, and an uncertain CAS response are not delivery permits.
-/
import Kernel.ApplicationDispatchProjection
import Kernel.ApplicationRouteAdmission

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
    candidate.worldRoot⟩

theorem Permit.receipt_in_verified {config : Config} (permit : Permit config) :
    permit.verified.receipts =
      permit.old.receipts ++ [permit.receipt] := by
  exact NativeHostReplay.extendExact_receipts
    permit.old permit.readback

/-- The permit's retained post-image is exactly the physical CAS readback,
not a later journal suffix or an asserted digest. -/
theorem Permit.postRecord_exact {config : Config} (permit : Permit config) :
    permit.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent permit.readback.derived.intent) :=
  NativeHostReplay.extendExact_physicalRecord permit.old permit.readback

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
  let .ok current ← DurableReceiverIO.tipIs config.transport
      permit.readback.appended.next.image.accepted.length permit.readback.appended.entry
    | return .error "dispatch physical tip unavailable before handoff"
  if current then
    return .ok (← handoff permit.canonicalBytes)
  else return .error "dispatch physical tip changed before handoff"

inductive Result (config : Config) where
  | permitted (permit : Permit config)
  | rejected (detail : String)
  /-- Emitted only before entering the durable receiver; no append was attempted. -/
  | noRecordRefused
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- The fresh private response uses a distinct exact tag/payload. A native
receiver may retire only this attempt's matching active marker on this verdict;
ordinary outcomes and transport errors are not equivalent evidence. -/
def noRecordRefusalBytes : List UInt8 :=
  "DREGG/APPLICATION/DISPATCH-NO-RECORD-REFUSAL/v1".toUTF8.toList

/-- A private resident's immutable route constraint. This grants no authority;
current signed dispatch admission remains mandatory. The distinct envelope
prevents accidental interpretation as an ordinary op34 request. -/
structure RouteConstraint where
  domain : Digest
  semantics : Digest
  binding : ApplicationStreamContinuity.Binding
  deriving DecidableEq

def routeConstraintStream : StreamCodec RouteConstraint :=
  StreamCodec.xmap
    (StreamCodec.product digestStream (StreamCodec.product digestStream
      ApplicationStreamContinuity.bindingStream))
    (fun c => (c.domain, c.semantics, c.binding))
    (fun (domain, semantics, binding) => ⟨domain, semantics, binding⟩)
    (by intro c; cases c; rfl)

def routeBoundCodec : LawfulCodec (RouteConstraint × List UInt8) :=
  NativeHostCodec.framed
    "DREGG/APPLICATION/ROUTE-BOUND-DISPATCH/v1".toUTF8.toList
    (StreamCodec.product routeConstraintStream bytesStream)

def routeMatches (config : Config) {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : NativeHostReplay.DispatchAt config opened ingress)
    (constraint : RouteConstraint) : Bool :=
  constraint.domain == config.deployment.domain &&
    constraint.semantics == config.profile.semantics &&
    constraint.binding == ApplicationStreamContinuity.bindingFor admitted

/-- The immutable route comparison and the spend use the SAME freshly checked
candidate. The existing signed roots and durable CAS guards remain unchanged;
a separate preflight observation cannot create a time-of-check gap here. -/
def receiveAdmitted (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (admitted : NativeHostReplay.DispatchAt config old.opened ingress)
    (constraint : Option RouteConstraint) : IO (Result config) := do
  if constraint.isSome && !(constraint.all (routeMatches config admitted)) then
    return .noRecordRefused
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .noRecordRefused
  let result ← DurableReceiverIO.receiveLoadedDetailed config.transport
    ResourceBirthCodec.rootBytes old.opened.durable derived.intent
  match result with
  | .exact kind appended =>
      match NativeHostReplay.ExactReadback.ofAppended old derived appended with
      | .error detail => return .uncertain s!"dispatch post-image validation: {detail}"
      | .ok ⟨proof, proofDerived⟩ =>
            return .permitted ⟨target, old, ingress, admitted,
              proof, ((congrArg NativeHostReplay.Derived.intent proofDerived).trans admitted.toDerived_intent), kind⟩
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ =>
          return .uncertain "dispatch confirmation lacks exact fresh post-CAS readback"
      | .rejected _ => return .rejected "durable dispatch refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail


/-- A mismatched locally registered route cannot invoke the durable receiver,
create a delivery permit, or bill a dispatch. This equality includes every
physical effect of this branch, rather than only its returned verdict. -/
theorem mismatched_route_never_submits (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (admitted : NativeHostReplay.DispatchAt config old.opened ingress)
    (constraint : RouteConstraint)
    (mismatch : routeMatches config admitted constraint = false) :
    receiveAdmitted config old ingress admitted (some constraint) =
      pure .noRecordRefused := by
  simp [receiveAdmitted, mismatch]

private def receiveVerifiedWith (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) (constraint : Option RouteConstraint) : IO (Result config) := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes
    | return .noRecordRefused
  if ApplicationStreamContinuity.reservedProbe ingress.dispatch.dispatch.request then
    return .noRecordRefused
  if ingress.dispatch.dispatch.session.origin != .human then
    return .noRecordRefused
  let .ok admitted ← NativeHostReplay.admitDispatchVerified old ingress
    | return .noRecordRefused
  receiveAdmitted config old ingress admitted constraint

/-- The ordinary receiver retains its existing signed current admission and
CAS behavior. Historical receipt recovery still cannot produce a permit. -/
def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) :=
  receiveVerifiedWith config old bytes none

/-- Private-only route-bound dispatch. The constraint is a resident restriction,
not a replacement for signed authority or an unsigned planning attestation. -/
def receiveRouteBoundVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some (constraint, ingress) := routeBoundCodec.decode bytes
    | return .noRecordRefused
  receiveVerifiedWith config old ingress (some constraint)

#assert_axioms mismatched_route_never_submits

/-- Even fully signed authority material for a continuity probe cannot be
submitted to the app-open receiver. Refusal occurs before admission/CAS. -/
theorem continuity_probe_never_submits (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (challenge : ApplicationStreamContinuity.Challenge)
    (probe : ingress.dispatch.dispatch.request =
      ApplicationStreamContinuity.probeRequest challenge) :
    receiveVerified config old (ApplicationDispatchAdmissionIngress.codec.encode ingress) =
      pure .noRecordRefused := by
  simp [receiveVerified, receiveVerifiedWith, ApplicationDispatchAdmissionIngress.codec.decode_encode,
    probe, ApplicationStreamContinuity.probe_reserved]

theorem route_probe_never_submits (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (challenge : ApplicationRouteAdmission.Challenge)
    (probe : ingress.dispatch.dispatch.request = ApplicationRouteAdmission.probeRequest challenge) :
    receiveVerified config old (ApplicationDispatchAdmissionIngress.codec.encode ingress) =
      pure .noRecordRefused := by
  simp [receiveVerified, receiveVerifiedWith, ApplicationDispatchAdmissionIngress.codec.decode_encode,
    probe, ApplicationRouteAdmission.probe_reserved]

#assert_axioms route_probe_never_submits
#assert_axioms continuity_probe_never_submits

end Minidregg.Kernel.ApplicationDispatchReceiver
