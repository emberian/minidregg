/- Guarded publication of an Activity's exact original native application.
The historical pending source admission is supplied by verified-prefix recovery,
never reconstructed from a bare checkpoint. The current pending-root guard is
part of the actual installed intent and event64 replay, so phase movement defeats
a stale worker. This route requires the real Bend fixed-capacity output admission;
ordinary exact-charge profiles need a separately versioned phase tariff.
-/
import Kernel.BendActivityPendingAdmission
import Kernel.BendPreparedOutput
import Kernel.BendActivityRoutePermit

namespace Minidregg.Kernel.BendActivityDispatch
open Minidregg.Theory
open TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

structure Action where
  pendingIndex : Nat
  pendingSource : List UInt8

def actionStream : StreamCodec Action :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat bytesStream)
    (fun a => (a.pendingIndex,a.pendingSource)) (fun (i,b) => ⟨i,b⟩)
    (by intro a; cases a; rfl)
def frame : List UInt8 := "DREGG/BEND/ACTIVITY-DISPATCH/v1".toUTF8.toList
def encode (action : Action) : List UInt8 := frame ++ actionStream.encode action
def decode (bytes : List UInt8) : Option Action := NockProgramCodec.framedDecode frame actionStream bytes

/-- The high-level recovery bridge must obtain historical from the actual
NativeHostReplay.VerifiedSelection.before and re-admit at that source prefix.
Matching the entire current accepted record prevents relabelled origin tokens. -/
structure Origin (config : Config) (opened : Opened config) (action : Action) where
  private mk ::
  historical : Opened config
  pending : BendActivityPendingAdmission.Admitted config historical
  sourceExact : BendActivityPendingAdmission.encode pending.action = action.pendingSource
  recorded : ∃ record, opened.durable.image.accepted[action.pendingIndex]? = some record ∧
    DurableReceiverCodec.intentStream.encode record =
      DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent pending.intent)

def bindOrigin {config : Config} (opened : Opened config) (action : Action)
    (historical : Opened config)
    (pending : BendActivityPendingAdmission.Admitted config historical) : Option (Origin config opened action) :=
  if sourceExact : BendActivityPendingAdmission.encode pending.action = action.pendingSource then
    match at : opened.durable.image.accepted[action.pendingIndex]? with
    | none => none
    | some record =>
      if exact : DurableReceiverCodec.intentStream.encode record =
          DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent pending.intent) then
        some ⟨historical,pending,sourceExact,record,at,exact⟩
      else none
  else none

def phaseGuard {config : Config} {opened : Opened config} {action : Action}
    (origin : Origin config opened action) : ReadGuard :=
  ⟨origin.pending.pin.cell,opened.durable.snapshot.model.roots origin.pending.pin.cell⟩

structure Admitted {config : Config} {opened : Opened config} {action : Action}
    (origin : Origin config opened action) where
  private mk ::
  application : BendActivityIngress.Current config opened
  routePermit : BendActivityRoutePermit.Permit opened.durable.snapshot origin.pending.pin
    application.command.nonce
    (signedBytes config.deployment.domain config.profile.semantics application.signed)
  signatureExact : signedBytes config.deployment.domain config.profile.semantics application.signed =
    origin.pending.action.applicationSignedBytes
  active : ContentControlFrame.readPayload origin.pending.pin
    (opened.durable.snapshot.canonicalBytes origin.pending.pin.cell) =
    some (BendActivity.encode origin.pending.pending.record)
  guardReadOnly : origin.pending.pin.cell ∉ application.intent.writes.map DataWrite.cellId
  output : BendPreparedOutput.Admitted application.prepared
    (signedBytes config.deployment.domain config.profile.semantics application.signed)
    application.intent.writes (phaseGuard origin :: application.intent.readGuards)
  intent : DataIntent ResourceBirthCodec.rootBytes
  writesExact : intent.writes = application.intent.writes
  guardsExact : intent.readGuards = phaseGuard origin :: application.intent.readGuards
  chargeExact : intent.exactCharge = application.intent.exactCharge
  transactionExact : intent.transactionId = application.intent.transactionId
  eventExact : intent.event.canonicalBytes = encode action
  ready : intent.preflight opened.durable.snapshot = .ok ()
  gates : config.sourceGate none opened.durable.snapshot intent = .ok ()

/-- Recheck real current output usage with all current audience dependencies
and the added physical LifecycleRoot guard. Fixed public charge is preserved;
a missing Bend capacity certificate is a refusal, not a silent Nock fallback. -/
def construct {config : Config} {opened : Opened config} {action : Action}
    (origin : Origin config opened action) (application : BendActivityIngress.Current config opened) :
    Option (Admitted origin) := do
  if signatureExact : signedBytes config.deployment.domain config.profile.semantics application.signed =
      origin.pending.action.applicationSignedBytes then
   if active : ContentControlFrame.readPayload origin.pending.pin
       (opened.durable.snapshot.canonicalBytes origin.pending.pin.cell) =
       some (BendActivity.encode origin.pending.pending.record) then
    if guardReadOnly : origin.pending.pin.cell ∉ application.intent.writes.map DataWrite.cellId then
      let routePermit ← BendActivityRoutePermit.admit opened.durable.snapshot origin.pending.pin
        application.command.nonce (signedBytes config.deployment.domain config.profile.semantics application.signed)
      let guards := phaseGuard origin :: application.intent.readGuards
      let .ok (some output) := BendPreparedOutput.admit application.prepared
        (signedBytes config.deployment.domain config.profile.semantics application.signed)
        application.intent.writes guards | none
      let base := application.intent
      let bytes := encode action
      let intent : DataIntent ResourceBirthCodec.rootBytes :=
        {base with
          readGuards := guards
          guardsReadOnly := by
            intro guard member
            rcases List.mem_cons.mp member with same | old
            · cases same
              exact guardReadOnly
            · exact base.guardsReadOnly guard old
          event := ⟨64,config.deployment.domain,ResourceBirthCodec.rootBytes bytes,bytes⟩}
      if ready : intent.preflight opened.durable.snapshot = .ok () then
        if gates : config.sourceGate none opened.durable.snapshot intent = .ok () then
          some ⟨application,routePermit,signatureExact,active,guardReadOnly,output,intent,
            rfl,rfl,rfl,rfl,rfl,ready,gates⟩
        else none
      else none
    else none
   else none
  else none

/-- General refusal theorem about the ACTUAL native preflight, not a local
worker boolean. A changed current pending root defeats this new admission. -/
theorem stale_phase_refused {config : Config} {opened : Opened config} {action : Action}
    {origin : Origin config opened action} (admitted : Admitted origin)
    (later : DataSnapshot ResourceBirthCodec.rootBytes)
    (moved : later.model.roots origin.pending.pin.cell != (phaseGuard origin).expectedRoot) :
    admitted.intent.preflight later = .error .staleReadGuard := by
  apply stale_read_guard_rejected
  refine ⟨phaseGuard origin,?_,moved⟩
  rw [admitted.guardsExact]
  exact List.mem_cons_self

def admit {config : Config} {opened : Opened config} {action : Action}
    (origin : Origin config opened action) : IO (Except String (Admitted origin)) := do
  let .ok application ← BendActivityPendingAdmission.readCurrent config opened
      origin.pending.action.applicationSignedBytes | return .error "current application authority refused"
  let some admitted := construct origin application | return .error "application phase/capacity/funding refused"
  return .ok admitted

/-- An application writes no protected Activity cell, so all ordinary facets
remain active. Exact record and pending bytes are rechecked before native CAS. -/
def transport {config : Config} {opened : Opened config} {action : Action}
    {origin : Origin config opened action} (admitted : Admitted origin) : DurableReceiverIO.Transport :=
  {config.transport with sourceGate := fun snapshot proposed => do
    config.sourceGate none snapshot proposed
    if DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent proposed) =
        DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent admitted.intent) ∧
        snapshot.canonicalBytes origin.pending.pin.cell = opened.durable.snapshot.canonicalBytes origin.pending.pin.cell
    then .ok () else .error (.durable .transactionConflict)}

inductive Result {config : Config} {opened : Opened config} {action : Action}
    (origin : Origin config opened action) where
  | appended (admitted : Admitted origin)
      (receipt : DurableReceiverIO.Appended ResourceBirthCodec.rootBytes opened.durable admitted.intent)
  | replayed (recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope)
  | refused (reason : String)
  | ordinary (result : DurableReceiverIO.Result ResourceBirthCodec.rootBytes)

/-- Exact already-recorded operation recovery precedes current re-admission.
No unknown reply causes a fresh operation identity or fresh signature. -/
def receive {config : Config} {opened : Opened config} {action : Action}
    (origin : Origin config opened action) : IO (Result origin) := do
  let id := transactionId config.deployment.domain config.profile.semantics origin.pending.application.command
  match DurableCommitProtocol.Snapshot.lookupRecorded id opened.durable.snapshot.model.journal with
  | some recorded =>
      if recorded.event.event.codecVersion = 64 ∧ recorded.event.event.domain = config.deployment.domain ∧
          recorded.event.event.canonicalBytes = encode action then return .replayed recorded
      else return .refused "application operation identity conflict"
  | none =>
      match ← admit origin with
      | .error reason => return .refused reason
      | .ok admitted =>
          match ← DurableReceiverIO.receiveLoadedDetailed (transport admitted)
              ResourceBirthCodec.rootBytes opened.durable admitted.intent with
          | .exact _ receipt => return .appended admitted receipt
          | .ordinary result => return .ordinary result

#assert_axioms bindOrigin
#assert_axioms construct
#assert_axioms stale_phase_refused
#assert_axioms receive
end Minidregg.Kernel.BendActivityDispatch
