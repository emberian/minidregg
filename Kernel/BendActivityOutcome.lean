/- Native publication outcome and source-owned cancellation for an Activity.
True means the original native application was published, not provider success.
False is an owner-authorized cancellation while that application is absent.
Unknown original outcomes remain pending. Both paths consume the same current
phase and inject the actual finite response into its retained continuation.
-/
import Kernel.BendActivityDispatch

namespace Minidregg.Kernel.BendActivityOutcome
open Minidregg.Theory
open TypedAuthorization ResourceCost
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false

structure Action where
  dispatch : BendActivityDispatch.Action
  /-- Some identifies an actual admitted publication; none requests cancellation. -/
  publicationIndex : Option Nat
  controlSignedBytes : List UInt8

def actionStream : StreamCodec Action :=
  StreamCodec.xmap (StreamCodec.product BendActivityDispatch.actionStream
    (StreamCodec.product (StreamCodec.option StreamCodec.nat) bytesStream))
    (fun a => (a.dispatch,a.publicationIndex,a.controlSignedBytes))
    (fun (d,p,c) => ⟨d,p,c⟩) (by intro a; cases a; rfl)
def frame : List UInt8 := "DREGG/BEND/ACTIVITY-OUTCOME/v1".toUTF8.toList
def encode (action : Action) : List UInt8 := frame ++ actionStream.encode action
def decode (bytes : List UInt8) : Option Action := NockProgramCodec.framedDecode frame actionStream bytes

def nonce (action : Action) : Nat :=
  (Sp800185Cshake256.hash "DREGG/BEND/ACTIVITY-OUTCOME-ACTION/v1".toUTF8.toList
    (actionStream.encode {action with controlSignedBytes := []})).digest.value

def applicationId {config : Config} {opened : Opened config} {action : Action}
    (origin : BendActivityDispatch.Origin config opened action.dispatch) : Digest :=
  transactionId config.deployment.domain config.profile.semantics origin.pending.application.command

/-- Concrete original-height dispatch admission plus whole-record inclusion.
The high replay bridge provides the historical prefix. Neither receipt-shaped
bytes nor the current pending payload can construct this witness. -/
structure Publication {config : Config} {opened : Opened config} {action : Action}
    (origin : BendActivityDispatch.Origin config opened action.dispatch) where
  private mk ::
  index : Nat
  selected : action.publicationIndex = some index
  historical : Opened config
  original : BendActivityDispatch.Origin config historical action.dispatch
  admitted : BendActivityDispatch.Admitted original
  samePending : BendActivity.encode original.pending.pending.record =
    BendActivity.encode origin.pending.pending.record
  recorded : ∃ record, opened.durable.image.accepted[index]? = some record ∧
    DurableReceiverCodec.intentStream.encode record =
      DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent admitted.intent)

def bindPublication {config : Config} {opened : Opened config} {action : Action}
    (origin : BendActivityDispatch.Origin config opened action.dispatch)
    (historical : Opened config)
    (original : BendActivityDispatch.Origin config historical action.dispatch)
    (admitted : BendActivityDispatch.Admitted original) : Option (Publication origin) := do
  let some index := action.publicationIndex | none
  if selected : action.publicationIndex = some index then
   if samePending : BendActivity.encode original.pending.pending.record =
       BendActivity.encode origin.pending.pending.record then
    match at : opened.durable.image.accepted[index]? with
    | none => none
    | some record =>
      if exact : DurableReceiverCodec.intentStream.encode record =
          DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent admitted.intent) then
        some ⟨index,selected,historical,original,admitted,samePending,record,at,exact⟩
      else none
   else none
  else none

inductive Resolution {config : Config} {opened : Opened config} {action : Action}
    (origin : BendActivityDispatch.Origin config opened action.dispatch) where
  | published (receipt : Publication origin)
  | cancelled (selected : action.publicationIndex = none)
      (absent : DurableCommitProtocol.Snapshot.lookupRecorded (applicationId origin)
        opened.durable.snapshot.model.journal = none)

def Resolution.bit {config : Config} {opened : Opened config} {action : Action}
    {origin : BendActivityDispatch.Origin config opened action.dispatch} : Resolution origin → Bool
  | .published _ => true
  | .cancelled _ _ => false

/-- A bounded reference to the source-verified journal entry, not recursively
embedded prior IntentRecords. Cancellation records its exact source decision;
only the actual native append makes that decision durable. -/
def outcome {config : Config} {opened : Opened config} {action : Action}
    (origin : BendActivityDispatch.Origin config opened action.dispatch)
    (resolution : Resolution origin) : BendActivity.Outcome :=
  ⟨origin.pending.identity, [if resolution.bit then 1 else 0],
    "DREGG/BEND/ACTIVITY-RECEIPT-REFERENCE/v1".toUTF8.toList ++
      (StreamCodec.product (StreamCodec.option StreamCodec.nat) digestStream).encode
        (action.publicationIndex,applicationId origin)⟩

def overhead {config : Config} {opened : Opened config} {action : Action}
    (origin : BendActivityDispatch.Origin config opened action.dispatch) : Charge
  | .turnBytes => (encode action).length
  | .memoryTouches => origin.pending.program.limits.heap.slots
  | .incidences | .storageBytes | .feeDebit | .networkBytes | .witnessBytes |
      .sideEffectCount | .leaseByteBlocks | .proofWork => 0

structure Admitted {config : Config} {opened : Opened config} {action : Action}
    (origin : BendActivityDispatch.Origin config opened action.dispatch) where
  private mk ::
  resolution : Resolution origin
  control : BendActivityIngress.Current config opened
  active : ContentControlFrame.readPayload origin.pending.pin
    (opened.durable.snapshot.canonicalBytes origin.pending.pin.cell) =
    some (BendActivity.encode origin.pending.pending.record)
  resumed : BendActivity.ResumedRecord origin.pending.program.limits
    origin.pending.program.compiled.library origin.pending.pending.record (outcome origin resolution)
  intent : DataIntent ResourceBirthCodec.rootBytes
  writesExact : intent.writes = control.intent.writes
  chargeExact : intent.exactCharge = control.intent.exactCharge + overhead origin
  carries : BendActivityControl.claim ResourceBirthCodec.rootBytes origin.pending.pin
    origin.pending.pending.record ∈ intent.nullifiers
  post : ∃ write ∈ intent.writes, write.cellId = origin.pending.pin.cell ∧
    ContentControlFrame.readPayload origin.pending.pin write.canonicalPostBytes =
      some (BendActivity.encode resumed.record)
  eventExact : intent.event.canonicalBytes = encode action
  ready : intent.preflight opened.durable.snapshot = .ok ()
  otherFacets : config.otherFacetGate .activity opened.durable.snapshot intent = .ok ()

def construct {config : Config} {opened : Opened config} {action : Action}
    (origin : BendActivityDispatch.Origin config opened action.dispatch)
    (resolution : Resolution origin) (control : BendActivityIngress.Current config opened) :
    Option (Admitted origin) := do
  let pin := origin.pending.pin
  if config.activityControl != some pin || control.command.subject != pin.owner ||
      control.command.nonce != nonce action || control.command.targets.length != 1 ||
      !control.command.targets.all (fun t => decide (t.kind = .object ∧ t.target = pin.cell.value)) then none else do
   if action.controlSignedBytes != signedBytes config.deployment.domain config.profile.semantics control.signed then none else do
    if active : ContentControlFrame.readPayload pin (opened.durable.snapshot.canonicalBytes pin.cell) =
        some (BendActivity.encode origin.pending.pending.record) then
      let resumed ← BendActivity.resumeCandidate origin.pending.program.limits
        origin.pending.program.compiled.library origin.pending.pending.record (outcome origin resolution)
      let base := control.intent
      let bytes := encode action
      let intent : DataIntent ResourceBirthCodec.rootBytes :=
        {base with nullifiers := BendActivityControl.claim ResourceBirthCodec.rootBytes pin origin.pending.pending.record :: base.nullifiers, exactCharge := base.exactCharge + overhead origin, event := ⟨64,config.deployment.domain,ResourceBirthCodec.rootBytes bytes,bytes⟩}
      if ready : intent.preflight opened.durable.snapshot = .ok () then
       if otherFacets : config.otherFacetGate .activity opened.durable.snapshot intent = .ok () then
        if post : ∃ write ∈ intent.writes, write.cellId = pin.cell ∧
            ContentControlFrame.readPayload pin write.canonicalPostBytes = some (BendActivity.encode resumed.record) then
          some ⟨resolution,control,active,resumed,intent,rfl,rfl,by simp [intent],post,rfl,ready,otherFacets⟩
        else none
       else none
      else none
    else none

/-- Cancellation tests the actual current native journal again at receiving.
If publication won the race, cancellation refuses; if cancellation wins, the
publication's pending-root guard refuses. No missing reply is treated as false. -/
def cancellationGate {config : Config} {opened : Opened config} {action : Action}
    {origin : BendActivityDispatch.Origin config opened action.dispatch}
    (admitted : Admitted origin) (snapshot : DataSnapshot ResourceBirthCodec.rootBytes) : Bool :=
  match admitted.resolution with
  | .published _ => true
  | .cancelled _ _ => (DurableCommitProtocol.Snapshot.lookupRecorded
      (applicationId origin) snapshot.model.journal).isNone

/-- An actually retained publication defeats the cancellation gate on every
later snapshot with that exact original operation recorded. -/
theorem cancellationGate_recorded {config : Config} {opened : Opened config} {action : Action}
    {origin : BendActivityDispatch.Origin config opened action.dispatch}
    (admitted : Admitted origin) (selected : action.publicationIndex = none)
    (absent : DurableCommitProtocol.Snapshot.lookupRecorded (applicationId origin)
      opened.durable.snapshot.model.journal = none)
    (cancelled : admitted.resolution = .cancelled selected absent)
    (later : DataSnapshot ResourceBirthCodec.rootBytes)
    (recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope)
    (present : DurableCommitProtocol.Snapshot.lookupRecorded (applicationId origin)
      later.model.journal = some recorded) :
    cancellationGate admitted later = false := by
  simp [cancellationGate,cancelled,present]

/-- A committed outcome consumes precisely the pending predecessor. Reusing
that predecessor for another newly admitted result is refused by the actual
native preflight, independent of the response value chosen by a stale worker. -/
theorem installed_outcome_refuses_new_admission {config : Config} {opened : Opened config} {action : Action}
    {origin : BendActivityDispatch.Origin config opened action.dispatch}
    (admitted : Admitted origin) (later : DataIntent ResourceBirthCodec.rootBytes)
    (sameClaim : BendActivityControl.claim ResourceBirthCodec.rootBytes origin.pending.pin
      origin.pending.pending.record ∈ later.nullifiers) :
    later.preflight (DataSnapshot.install opened.durable.snapshot admitted.intent) ≠ .ok () := by
  apply DataIntent.consumed_nullifier_refused _ later _ sameClaim
  change (DurableCommitProtocol.Snapshot.install opened.durable.snapshot.model admitted.intent.erase).consumed
    (BendActivityControl.claim ResourceBirthCodec.rootBytes origin.pending.pin origin.pending.pending.record) = true
  exact DurableCommitProtocol.Snapshot.install_consumes _ _ _ admitted.carries

def transport {config : Config} {opened : Opened config} {action : Action}
    {origin : BendActivityDispatch.Origin config opened action.dispatch}
    (admitted : Admitted origin) : DurableReceiverIO.Transport :=
  {config.transport with sourceGate := fun snapshot proposed => do
    config.otherFacetGate .activity snapshot proposed
    if DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent proposed) =
        DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent admitted.intent) ∧
        snapshot.canonicalBytes origin.pending.pin.cell = opened.durable.snapshot.canonicalBytes origin.pending.pin.cell ∧
        cancellationGate admitted snapshot = true
    then .ok () else .error (.durable .transactionConflict)}

theorem transport_other_facets {config : Config} {opened : Opened config} {action : Action}
    {origin : BendActivityDispatch.Origin config opened action.dispatch}
    (admitted : Admitted origin) (snapshot : DataSnapshot ResourceBirthCodec.rootBytes)
    (proposed : DataIntent ResourceBirthCodec.rootBytes)
    (accepted : (transport admitted).sourceGate snapshot proposed = .ok ()) :
    config.otherFacetGate .activity snapshot proposed = .ok () := by
  cases checked : config.otherFacetGate .activity snapshot proposed with
  | error reason => simp [transport,checked] at accepted
  | ok value => cases value; exact checked

theorem actual_resumed_control {config : Config} {opened : Opened config} {action : Action}
    {origin : BendActivityDispatch.Origin config opened action.dispatch} (admitted : Admitted origin) :
    admitted.resumed.record.checkpoint.state.control = .apply .Q1
      admitted.resumed.pending.response.continuation admitted.resumed.resumed.inputPointer :=
  admitted.resumed.actual_control

def admit {config : Config} {opened : Opened config} {action : Action}
    (origin : BendActivityDispatch.Origin config opened action.dispatch)
    (resolution : Resolution origin) : IO (Except String (Admitted origin)) := do
  let .ok control ← BendActivityPendingAdmission.readCurrent config opened action.controlSignedBytes
    | return .error "Activity outcome current control authority refused"
  let some admitted := construct origin resolution control
    | return .error "Activity outcome phase/type/funding refused"
  return .ok admitted

inductive Result {config : Config} {opened : Opened config} {action : Action}
    (origin : BendActivityDispatch.Origin config opened action.dispatch) where
  | appended (admitted : Admitted origin)
      (receipt : DurableReceiverIO.Appended ResourceBirthCodec.rootBytes opened.durable admitted.intent)
  | replayed (recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope)
  | refused (reason : String)
  | ordinary (result : DurableReceiverIO.Result ResourceBirthCodec.rootBytes)

def receive {config : Config} {opened : Opened config} {action : Action}
    (origin : BendActivityDispatch.Origin config opened action.dispatch)
    (resolution : Resolution origin) : IO (Result origin) := do
  let some (domain,semantics,signed) := decodeSignedBytes action.controlSignedBytes
    | return .refused "Activity outcome signature malformed"
  if domain != config.deployment.domain || semantics != config.profile.semantics then return .refused "Activity outcome scope mismatch"
  let some command := commandCodec.decode signed.commandBytes | return .refused "Activity outcome command malformed"
  match DurableCommitProtocol.Snapshot.lookupRecorded (transactionId domain semantics command)
      opened.durable.snapshot.model.journal with
  | some recorded =>
      if recorded.event.event.codecVersion = 64 ∧ recorded.event.event.domain = domain ∧
          recorded.event.event.canonicalBytes = encode action then return .replayed recorded
      else return .refused "Activity outcome transaction conflict"
  | none =>
      match ← admit origin resolution with
      | .error reason => return .refused reason
      | .ok admitted =>
          match ← DurableReceiverIO.receiveLoadedDetailed (transport admitted)
              ResourceBirthCodec.rootBytes opened.durable admitted.intent with
          | .exact _ receipt => return .appended admitted receipt
          | .ordinary result => return .ordinary result

#assert_axioms cancellationGate_recorded
#assert_axioms installed_outcome_refuses_new_admission
#assert_axioms bindPublication
#assert_axioms construct
#assert_axioms transport_other_facets
#assert_axioms actual_resumed_control
#assert_axioms receive
end Minidregg.Kernel.BendActivityOutcome
