/- A physical dispatch receiver for an authenticated carried service. Both old
and new tickets retain their actual typed current admission. One exact CAS
extends the suffix; only its fresh winner can hand a physical permit to Host. -/
import Kernel.ApplicationDispatchReceiver
import Kernel.CarriedDispatchAdmission
import Kernel.ApplicationDispatchLookup

namespace Minidregg.Kernel.CarriedApplicationDispatchReceiver

open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.NativeHost
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram

set_option autoImplicit false

/-- Exact signed-ingress status under the suffix's original receipts. This
lookup deliberately runs before current authority checks, so later revocation
cannot turn an occupied transaction into absence or a fresh submission. -/
def lookupVerified {config : Config} {anchor : Opened config} {target : Durable}
    (verified : NativeHostReplay.SuffixVerified config anchor target) (bytes : List UInt8) :
    Except ApplicationDispatchLookup.Error (Option Receipt) := do
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes
    | throw .malformed
  if ingress.canonicalBytes != bytes then throw .malformed
  let some selection := ApplicationDispatchAdmission.selectCommand ingress
    | throw .malformed
  let some signedCommand := DeclaredResourceController.commandCodec.decode
      ingress.dispatch.signed.commandBytes
    | throw .malformed
  if !ApplicationDispatchCommand.matchesCommand ingress.dispatch selection ingress.parent
      signedCommand then throw .malformed
  let transactionId := DeclaredResourceController.transactionId ingress.dispatch.domain
    ingress.dispatch.semantics signedCommand
  let some index := verified.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == transactionId)
    | return none
  let some record := verified.opened.durable.image.accepted[index]?
    | throw .nativeHistoryUnavailable
  -- Earlier records belong to their retained interpreter; never reconstruct
  -- an old root through target-profile replay, even when bytes happen to parse.
  let some receipt := verified.receiptAt index
    | throw .nativeHistoryUnavailable
  let expectedEvent := ApplicationDispatchAdmissionIngress.event ingress
  let expectedNullifier := ApplicationDispatchAdmissionIngress.nullifier ingress
  if record.event == expectedEvent && record.nullifiers.contains expectedNullifier &&
      receipt.transactionId == transactionId && receipt.eventId == expectedEvent.eventId &&
      receipt.acceptedCount == index + 1 then
    return some receipt
  else throw .transactionConflict

/-- Positive absence over the full accepted Image, including the retained
pre-anchor records. No old transaction, unavailable original receipt, malformed
request or conflicting wrapper can construct this token. -/
structure RefusalAtTip (config : Config) {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target) (bytes : List UInt8) : Type where
  private mk ::
  absent : lookupVerified old bytes = .ok none

def refusalAtTip? {config : Config} {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target) (bytes : List UInt8) :
    Option (RefusalAtTip config old bytes) :=
  match checked : lookupVerified old bytes with
  | .ok none => some ⟨checked⟩
  | _ => none

/-- The exact absence decision is usable only while its same physical record
and MAC are still the Store tip. No ordinary Verified/token cast is involved. -/
def RefusalAtTip.withFreshTip {config : Config} {anchor : Opened config} {target : Durable}
    {old : NativeHostReplay.SuffixVerified config anchor target} {bytes : List UInt8} {α : Type}
    (_refusal : RefusalAtTip config old bytes) (handoff : List UInt8 → IO α) :
    IO (Except String α) :=
  ApplicationStreamContinuity.withOpenedFreshTip old.opened
    (handoff ApplicationDispatchReceiver.noRecordRefusalBytes)

/-- Computational admission evidence; the ordinary branch is obtained from
actual suffix provenance, never by eliminating a Prop or forging Verified. -/
inductive Admitted (config : Config) (opened : Opened config) where
  | ordinary (ingress : ApplicationDispatchAdmissionIngress.Ingress)
      (admitted : NativeHostReplay.DispatchAt config opened ingress)
  | carried (ingress : ApplicationDispatchAdmissionIngress.Ingress)
      (admitted : CarriedDispatchAdmission.Admitted config opened ingress)

def Admitted.intent {config : Config} {opened : Opened config} :
    Admitted config opened → DurableDataIntent.DataIntent rootBytes
  | .ordinary _ admitted => admitted.intent
  | .carried _ admitted => admitted.intent

def Admitted.derived {config : Config} {opened : Opened config} :
    Admitted config opened → NativeHostReplay.SuffixDerived config opened
  | .ordinary _ admitted => .ordinary admitted.toDerived
  | .carried ingress admitted => .carriedDispatch ingress admitted

private def carriedProjection {config : Config} {opened : Opened config}
    {ingress : ApplicationDispatchAdmissionIngress.Ingress}
    (admitted : CarriedDispatchAdmission.Admitted config opened ingress) :
    ApplicationDispatchProjection.Candidate :=
  let dispatch := ingress.dispatch.dispatch
  let checked := admitted.checked
  { dispatch := dispatch
    effectiveBits := checked.bits
    sessionFingerprint := checked.sessionFingerprint
    ticketResource := admitted.issue.issue.spec.ticket.resource
    ticketRoot := ingress.ticketRoot
    enrollmentResource := ingress.dispatch.enrollmentResource
    enrollmentRoot := ingress.dispatch.enrollmentRoot
    authorityRoot := opened.ground.authority.cell.root
    appRoot := ingress.dispatch.appRoot
    sessionRoot := checked.selection.sessionRoot
    issueTransaction := admitted.issue.issue.record.transactionId
    issueEvent := admitted.issue.issue.record.event.eventId
    dispatchTransaction := admitted.intent.transactionId
    dispatchEvent := admitted.intent.event.eventId
    currentWorldRoot := opened.durable.worldRoot
    physicalRequestDigest := ApplicationDispatchProjection.requestDigest dispatch.request }

def Admitted.projection {config : Config} {opened : Opened config} :
    Admitted config opened → ApplicationDispatchProjection.Candidate
  | .ordinary _ admitted => ApplicationDispatchProjection.ofDispatchAt admitted
  | .carried _ admitted => carriedProjection admitted

/-- This projection and the CAS intent use the same admitted object. The local
route restriction supplies no authority and cannot replace signed admission. -/
def routeMatches {config : Config} {opened : Opened config}
    (admitted : Admitted config opened)
    (constraint : ApplicationDispatchReceiver.RouteConstraint) : Bool :=
  let candidate := admitted.projection
  let dispatch := candidate.dispatch
  let binding : ApplicationStreamContinuity.Binding :=
    ⟨dispatch.app.resource, dispatch.app.generation, dispatch.session.resource,
      dispatch.session.generation, dispatch.session.subject.value,
      candidate.ticketResource, candidate.sessionFingerprint⟩
  constraint.domain == config.deployment.domain &&
    constraint.semantics == config.profile.semantics && constraint.binding == binding

/-- Exact durable commit evidence, also retained when this attempt did not win
freshly. A committed receipt by itself is never a physical delivery permit. -/
structure Committed (config : Config) (anchor : Opened config) where
  private mk ::
  oldTarget : Durable
  old : NativeHostReplay.SuffixVerified config anchor oldTarget
  admitted : Admitted config old.opened
  appended : DurableReceiverIO.Appended rootBytes old.opened.durable admitted.intent
  verified : NativeHostReplay.SuffixVerified config anchor appended.next
  receipt : Receipt
  receiptExact : verified.receiptAt old.opened.durable.height = some receipt
  confirmation : DurableReceiverIO.Confirmation
  freshCasWinner : Bool

def Committed.target {config : Config} {anchor : Opened config}
    (committed : Committed config anchor) : Durable := committed.appended.next

theorem Committed.postRecord_exact {config : Config} {anchor : Opened config}
    (committed : Committed config anchor) :
    committed.appended.entry.record = DurableCheckpointCodec.recordFrame.encode
      (DurableReceiver.IntentRecord.ofIntent committed.admitted.intent) :=
  committed.appended.entryExact

/-- Only the physical fresh-winner branch below can construct this. Recovered,
already-present and historical outcomes retain receipts, never this value. -/
structure Permit (config : Config) (anchor : Opened config) where
  private mk ::
  committed : Committed config anchor
  fresh : committed.freshCasWinner = true
  installed : committed.confirmation = .installed

def Permit.projection {config : Config} {anchor : Opened config}
    (permit : Permit config anchor) : ApplicationDispatchProjection.Candidate :=
  permit.committed.admitted.projection

def Permit.receipt {config : Config} {anchor : Opened config}
    (permit : Permit config anchor) : Receipt := permit.committed.receipt

def Permit.verified {config : Config} {anchor : Opened config}
    (permit : Permit config anchor) :
    NativeHostReplay.SuffixVerified config anchor permit.committed.appended.next :=
  permit.committed.verified

/-- Byte-compatible with the existing source-owned committed-permit frame.
Encoding this public shape is not authority; private Permit plus the callback
below supplies the physical provenance at the native response boundary. -/
private def permitCodec : LawfulCodec (ApplicationDispatchProjection.Candidate × Receipt) :=
  NativeHostCodec.framed "DREGG/APPLICATION/DISPATCH-COMMITTED-PERMIT/v1".toUTF8.toList
    (StreamCodec.product ApplicationDispatchProjection.candidateStream receiptStream)

/-- The fresh-winner guard is checked here, at actual emission, and the exact
CAS record must still be the physical tip. This is a point-in-time handoff;
the resident's generation/route lease remains the later physical obligation. -/
def Permit.withFreshTip {config : Config} {anchor : Opened config} {α : Type}
    (permit : Permit config anchor) (handoff : List UInt8 → IO α) : IO (Except String α) := do
  if !permit.committed.freshCasWinner || permit.committed.confirmation != .installed then
    return .error "dispatch attempt did not freshly win physical CAS"
  let .ok current ← DurableReceiverIO.tipIs config.transport
      permit.committed.appended.next.height permit.committed.appended.entry
    | return .error "dispatch physical tip unavailable before handoff"
  if current then
    return .ok (← handoff (permitCodec.encode (permit.projection, permit.receipt)))
  else return .error "dispatch physical tip changed before handoff"

inductive Result (config : Config) (anchor : Opened config) where
  | permitted (permit : Permit config anchor)
  | committed (committed : Committed config anchor)
  /-- Original receipt only, with no fresh delivery authority. -/
  | historical (receipt : Receipt)
  /-- May emit the private absence marker only through refusal.withFreshTip. -/
  | noRecordRefused {target : Durable}
      {old : NativeHostReplay.SuffixVerified config anchor target} {bytes : List UInt8}
      (refusal : RefusalAtTip config old bytes)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

private def receiveAdmitted {config : Config} {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target)
    (admitted : Admitted config old.opened)
    (constraint : Option ApplicationDispatchReceiver.RouteConstraint)
    {bytes : List UInt8} (refusal : RefusalAtTip config old bytes) :
    IO (Result config anchor) := do
  if constraint.isSome && !(constraint.all (routeMatches admitted)) then
    return .noRecordRefused refusal
  if old.opened.durable.image.accepted.findIdx?
      (fun record => record.transactionId == admitted.intent.transactionId) != none then
    return .rejected "dispatch pre-CAS request refused"
  let (freshCasWinner, result) ← DurableReceiverIO.receiveLoadedDetailedWithFresh
    config.transport rootBytes old.opened.durable admitted.intent
  match result with
  | .exact kind appended =>
      let ⟨_, reader⟩ ← match ← DurableHistoryStore.readerOf config.transport rootBytes appended.next with
        | .error detail => return .uncertain s!"post-append history reader: {detail}"
        | .ok reader => pure reader
      match ← NativeHostReplay.extendSuffixVerified config reader old appended.next with
      | .error failure => return .uncertain s!"dispatch post-image validation: {failure.detail}"
      | .ok extended =>
          match receiptExact : extended.receiptAt old.opened.durable.height with
          | none => return .uncertain "dispatch original suffix receipt unavailable"
          | some receipt =>
              if receipt.transactionId != admitted.intent.transactionId ||
                  receipt.eventId != admitted.intent.event.eventId ||
                  receipt.acceptedCount != old.opened.durable.height + 1 ||
                  receipt.worldRoot != appended.next.worldRoot then
                return .uncertain "dispatch original suffix receipt differs"
              let committed : Committed config anchor := ⟨target, old, admitted,
                appended, extended, receipt, receiptExact, kind, freshCasWinner⟩
              if fresh : committed.freshCasWinner = true then
                if installed : committed.confirmation = .installed then
                  return .permitted ⟨committed, fresh, installed⟩
                else return .committed committed
              else return .committed committed
  | .ordinary ordinary =>
      match ordinary with
      | .confirmed _ _ => return .uncertain "dispatch lacks exact post-CAS readback"
      | .rejected _ => return .rejected "durable dispatch refused"
      | .contention => return .contention
      | .unavailable detail => return .unavailable detail
      | .uncertain detail => return .uncertain detail

/-- The route mismatch branch performs no durable operation at all. -/
theorem mismatched_route_never_submits {config : Config} {anchor : Opened config}
    {target : Durable} (old : NativeHostReplay.SuffixVerified config anchor target)
    (admitted : Admitted config old.opened)
    (constraint : ApplicationDispatchReceiver.RouteConstraint)
    {bytes : List UInt8} (refusal : RefusalAtTip config old bytes)
    (mismatch : routeMatches admitted constraint = false) :
    receiveAdmitted old admitted (some constraint) refusal = pure (.noRecordRefused refusal) := by
  simp [receiveAdmitted, mismatch]

private def receiveVerifiedWith {config : Config} {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target) (bytes : List UInt8)
    (constraint : Option ApplicationDispatchReceiver.RouteConstraint) :
    IO (Result config anchor) := do
  let refusal : RefusalAtTip config old bytes ←
    match checked : lookupVerified old bytes with
    | .ok (some receipt) => return .historical receipt
    | .error .nativeHistoryUnavailable =>
        return .uncertain "dispatch original receipt belongs to another segment or is unavailable"
    | .error .transactionConflict => return .rejected "dispatch transaction has a different original"
    | .error .malformed => return .rejected "noncanonical dispatch ingress"
    | .ok none => pure ⟨checked⟩
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode bytes
    | return .rejected "dispatch pre-CAS request refused"
  if ingress.canonicalBytes != bytes then return .rejected "dispatch pre-CAS request refused"
  if ApplicationStreamContinuity.reservedProbe ingress.dispatch.dispatch.request then
    return .noRecordRefused refusal
  if ingress.dispatch.dispatch.session.origin != .human then return .noRecordRefused refusal
  let .ok derived ← NativeHostReplay.deriveSuffixVerified old bytes
    | return .noRecordRefused refusal
  match derived with
  | .carriedDispatch selected admitted =>
      if selected.canonicalBytes != bytes then return .rejected "dispatch pre-CAS request refused"
      receiveAdmitted old (.carried selected admitted) constraint refusal
  | .ordinary _ =>
      -- Derived's admission is a Prop. Obtain computational projection evidence
      -- through the same suffix's real issue cache and checked current image.
      let .ok admitted ← NativeHostReplay.admitDispatchSuffixVerified old ingress
        | return .noRecordRefused refusal
      receiveAdmitted old (.ordinary ingress admitted) constraint refusal
  | .carriedEnrollment _ _ => return .rejected "dispatch pre-CAS request refused"

def receiveVerified (config : Config) {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target) (bytes : List UInt8) :
    IO (Result config anchor) := receiveVerifiedWith old bytes none

/-- Malformed envelopes remain non-clearing. An inner request refusal can
carry an absence token only after exact full-image lookup; Host must still use
the token's physical-tip callback to emit the private marker. -/
def receiveRouteBoundVerified (config : Config) {anchor : Opened config} {target : Durable}
    (old : NativeHostReplay.SuffixVerified config anchor target) (bytes : List UInt8) :
    IO (Result config anchor) := do
  let some (constraint, ingress) := ApplicationDispatchReceiver.routeBoundCodec.decode bytes
    | return .rejected "dispatch pre-CAS request refused"
  receiveVerifiedWith old ingress (some constraint)

end Minidregg.Kernel.CarriedApplicationDispatchReceiver
