/-
Fresh physical dispatch receiving. The only permit-producing branch is a new
special event 11 committed by CAS and confirmed against the exact complete
post-image bytes. Historical receipt recovery, generic DRC event 3, a
concurrent suffix, and an uncertain CAS response are not delivery permits.
-/
import Compiler.ApplicationReceivingDomain
import Kernel.ApplicationDispatchProjection
import Kernel.ApplicationDispatchLookup
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
    old.opened.durable.height + 1,
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
    ApplicationReceivingDomain.dispatchCommittedPermitFrame
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
      permit.readback.appended.next.height permit.readback.appended.entry
    | return .error "dispatch physical tip unavailable before handoff"
  if current then
    return .ok (← handoff permit.canonicalBytes)
  else return .error "dispatch physical tip changed before handoff"

/-- The fresh private response uses a distinct exact tag/payload. A native
receiver may retire only this attempt's matching active marker on this verdict;
ordinary outcomes and transport errors are not equivalent evidence. -/
def noRecordRefusalBytes : List UInt8 :=
  ApplicationReceivingDomain.noRecordRefusalFrame

/-- Positive exact-call absence at one authenticated current image. The
token retains the full-history Verified witness, so an unchecked Opened
image cannot mint this verdict. It also keeps the canonical command selection
rather than trusting a plan label.
It is emitted only after a fresh physical-tip callback. -/
structure RefusalAtTip (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) where
  private mk ::
  selected : ApplicationDispatchCommand.Selection
  selectionExact : ApplicationDispatchAdmission.selectCommand ingress = some selected
  absent : old.opened.durable.image.accepted.findIdx? (fun record =>
    record.transactionId == DeclaredResourceController.transactionId ingress.dispatch.domain
      ingress.dispatch.semantics
      (ApplicationDispatchCommand.command ingress.dispatch selected ingress.parent)) = none

def refusalAtTip? {config : Config} {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) :
    Option (RefusalAtTip config old ingress) :=
  match selected : ApplicationDispatchAdmission.selectCommand ingress with
  | none => none
  | some selection =>
      if absent : old.opened.durable.image.accepted.findIdx? (fun record =>
          record.transactionId == DeclaredResourceController.transactionId ingress.dispatch.domain
            ingress.dispatch.semantics
            (ApplicationDispatchCommand.command ingress.dispatch selection ingress.parent)) = none then
        some ⟨selection, selected, absent⟩
      else none

def RefusalAtTip.withFreshTip {config : Config} {target : Durable}
    {old : NativeHostReplay.Verified config target}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress} {α : Type}
    (_refusal : RefusalAtTip config old ingress) (handoff : List UInt8 → IO α) :
    IO (Except String α) :=
  ApplicationStreamContinuity.withVerifiedFreshTip old (handoff noRecordRefusalBytes)

inductive Result (config : Config) where
  | permitted (permit : Permit config)
  | committed (committed : Committed config)
  | historical (receipt : NativeHostCodec.Receipt)
  | rejected (detail : String)
  /-- Positive call absence, emitted only while the same physical tip is current. -/
  | noRecordRefused {target : Durable} {old : NativeHostReplay.Verified config target}
      {ingress : ApplicationDispatchAdmissionIngress.Ingress}
      (refusal : RefusalAtTip config old ingress)
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
    ApplicationReceivingDomain.routeBoundDispatchFrame
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
    (constraint : Option RouteConstraint)
    (refusal : RefusalAtTip config old ingress) : IO (Result config) := do
  let derived := admitted.toDerived
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == derived.intent.transactionId) != none then
    return .rejected "dispatch transaction identity already used"
  if constraint.isSome && !(constraint.all (routeMatches config admitted)) then
    return .noRecordRefused refusal
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


/-- A mismatched locally registered route cannot invoke the durable receiver,
create a delivery permit, or bill a dispatch. This equality includes every
physical effect of this branch, rather than only its returned verdict. -/
theorem mismatched_route_never_submits (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (admitted : NativeHostReplay.DispatchAt config old.opened ingress)
    (constraint : RouteConstraint)
    (refusal : RefusalAtTip config old ingress)
    (absent : old.opened.durable.image.accepted.findIdx? (fun record =>
      record.transactionId == admitted.toDerived.intent.transactionId) = none)
    (mismatch : routeMatches config admitted constraint = false) :
    receiveAdmitted config old ingress admitted (some constraint) refusal =
      pure (.noRecordRefused refusal) := by
  simp [receiveAdmitted, absent, mismatch]
  rfl

private def receiveVerifiedWith (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) (constraint : Option RouteConstraint) : IO (Result config) := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes
    | return .rejected "noncanonical special dispatch ingress"
  -- An invalidated replay must retain its original receipt, never turn into
  -- an apparent new refusal because current authority changed after acceptance.
  match ApplicationDispatchLookup.lookupVerified old bytes with
  | .error _ => return .rejected "dispatch historical identity unavailable or conflicting"
  | .ok (some receipt) => return .historical receipt
  | .ok none => pure ()
  let some refusal := refusalAtTip? old ingress
    | return .rejected "dispatch exact-call absence unavailable"
  if ApplicationStreamContinuity.reservedProbe ingress.dispatch.dispatch.request then
    return .noRecordRefused refusal
  if ingress.dispatch.dispatch.session.origin != .human then
    return .noRecordRefused refusal
  let .ok admitted ← NativeHostReplay.admitDispatchVerified old ingress
    | return .noRecordRefused refusal
  receiveAdmitted config old ingress admitted constraint refusal

/-- The ordinary receiver retains its existing signed current admission and
CAS behavior. Historical receipt recovery still cannot produce a permit. -/
def receiveVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) :=
  receiveVerifiedWith config old bytes none

/-- A previously accepted exact call returns its original receipt before any
current-law check; revocation cannot relabel an accepted call as absent. -/
theorem historical_lookup_receipt_only (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (receipt : NativeHostCodec.Receipt)
    (found : ApplicationDispatchLookup.lookupVerified old
      (ApplicationDispatchAdmissionIngress.codec.encode ingress) = .ok (some receipt)) :
    receiveVerified config old (ApplicationDispatchAdmissionIngress.codec.encode ingress) =
      pure (.historical receipt) := by
  simp [receiveVerified, receiveVerifiedWith,
    ApplicationDispatchAdmissionIngress.codec.decode_encode, found]

/-- An occupied/conflicting or unreadable historical identity is never a
marker-clearing refusal, even if current admission would also fail. -/
theorem conflicting_lookup_not_clear (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (reason : ApplicationDispatchLookup.Error)
    (conflict : ApplicationDispatchLookup.lookupVerified old
      (ApplicationDispatchAdmissionIngress.codec.encode ingress) = .error reason) :
    receiveVerified config old (ApplicationDispatchAdmissionIngress.codec.encode ingress) =
      pure (.rejected "dispatch historical identity unavailable or conflicting") := by
  simp [receiveVerified, receiveVerifiedWith,
    ApplicationDispatchAdmissionIngress.codec.decode_encode, conflict]

#assert_axioms historical_lookup_receipt_only
#assert_axioms conflicting_lookup_not_clear

/-- Private-only route-bound dispatch. The constraint is a resident restriction,
not a replacement for signed authority or an unsigned planning attestation. -/
def receiveRouteBoundVerified (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (bytes : List UInt8) : IO (Result config) := do
  let some (constraint, ingress) := routeBoundCodec.decode bytes
    | return .rejected "noncanonical route-bound dispatch envelope"
  receiveVerifiedWith config old ingress (some constraint)

#assert_axioms mismatched_route_never_submits

/-- Even fully signed authority material for a continuity probe cannot be
submitted to the app-open receiver. Refusal occurs before admission/CAS. -/
theorem continuity_probe_never_submits (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (refusal : RefusalAtTip config old ingress)
    (lookupAbsent : ApplicationDispatchLookup.lookupVerified old
      (ApplicationDispatchAdmissionIngress.codec.encode ingress) = .ok none)
    (refusalExact : refusalAtTip? old ingress = some refusal)
    (challenge : ApplicationStreamContinuity.Challenge)
    (probe : ingress.dispatch.dispatch.request =
      ApplicationStreamContinuity.probeRequest challenge) :
    receiveVerified config old (ApplicationDispatchAdmissionIngress.codec.encode ingress) =
      pure (.noRecordRefused refusal) := by
  simp [receiveVerified, receiveVerifiedWith, ApplicationDispatchAdmissionIngress.codec.decode_encode,
    lookupAbsent, refusalExact, probe, ApplicationStreamContinuity.probe_reserved]
  rfl

theorem route_probe_never_submits (config : Config) {target : Durable}
    (old : NativeHostReplay.Verified config target)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress)
    (refusal : RefusalAtTip config old ingress)
    (lookupAbsent : ApplicationDispatchLookup.lookupVerified old
      (ApplicationDispatchAdmissionIngress.codec.encode ingress) = .ok none)
    (refusalExact : refusalAtTip? old ingress = some refusal)
    (challenge : ApplicationRouteAdmission.Challenge)
    (probe : ingress.dispatch.dispatch.request = ApplicationRouteAdmission.probeRequest challenge) :
    receiveVerified config old (ApplicationDispatchAdmissionIngress.codec.encode ingress) =
      pure (.noRecordRefused refusal) := by
  simp [receiveVerified, receiveVerifiedWith, ApplicationDispatchAdmissionIngress.codec.decode_encode,
    lookupAbsent, refusalExact, probe, ApplicationRouteAdmission.probe_reserved]
  rfl

#assert_axioms route_probe_never_submits
#assert_axioms continuity_probe_never_submits

end Minidregg.Kernel.ApplicationDispatchReceiver
