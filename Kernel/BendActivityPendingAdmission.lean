/- Source event64, first retained application publication phase. The controller operation undergoes actual current native admission; the exact
application remains an inert signed proposal until guarded dispatch admission.
The complete source segment is independently checked against the retained heap;
the exact pending successor consumes the Activity predecessor. This admits only
the pending record, not the later application write or an external provider call.
-/
import Kernel.BendActivityIngress
import Compiler.BendActivitySuspension
import Compiler.BendActivityDispatchContext

namespace Minidregg.Kernel.BendActivityPendingAdmission
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
  program : BendActivityProgram.Source
  generation : Nat
  ordinal : Nat
  decodeTicks : Nat
  sourceLimits : BendRunCore.Limits
  response : BendClosureResponse.ABI
  signature : BendActivitySegment.TypePin
  homeProjectionBytes : Option (List UInt8)
  applicationSignedBytes : List UInt8
  controlSignedBytes : List UInt8

def limitsStream : StreamCodec BendRunCore.Limits :=
  StreamCodec.xmap (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
    (StreamCodec.product StreamCodec.nat StreamCodec.nat)))
    (fun l => (l.checkerTicks,l.classificationTicks,l.sourceSteps,l.outputTermSize))
    (fun (c,t,s,o) => ⟨c,t,s,o⟩) (by intro l; cases l; rfl)

def actionStream : StreamCodec Action :=
  StreamCodec.xmap
    (StreamCodec.product BendActivityProgram.sourceStream (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat
        (StreamCodec.product limitsStream (StreamCodec.product BendActivity.abiStream
          (StreamCodec.product BendActivitySegment.typePinStream
            (StreamCodec.product (StreamCodec.option bytesStream)
              (StreamCodec.product bytesStream bytesStream)))))))))
    (fun a => (a.program,a.generation,a.ordinal,a.decodeTicks,a.sourceLimits,a.response,
      a.signature,a.homeProjectionBytes,a.applicationSignedBytes,a.controlSignedBytes))
    (fun (p,g,o,d,l,r,s,h,a,c) => ⟨p,g,o,d,l,r,s,h,a,c⟩) (by intro a; cases a; rfl)

def frame : List UInt8 := "DREGG/BEND/ACTIVITY-PENDING/v2".toUTF8.toList
def encode (action : Action) : List UInt8 := frame ++ actionStream.encode action
def decode (bytes : List UInt8) : Option Action := NockProgramCodec.framedDecode frame actionStream bytes

/-- Original controller signature binds source bounds, exact application
signature and response ABI. Cryptographic digest assumptions remain explicit. -/
def nonce (action : Action) : Nat :=
  (Sp800185Cshake256.hash "DREGG/BEND/ACTIVITY-PENDING-ACTION/v1".toUTF8.toList
    (actionStream.encode {action with controlSignedBytes := []})).digest.value

/-- Exact explicit route context; no nonce interval is reserved. The pending
ordinal is the actual successor phase, while the complete preparation parameters
remain signed without recursively including either signature. -/
def applicationContext (pin : ContentControlFrame.Pin) (action : Action) : List UInt8 :=
  BendActivityDispatchContext.encode ⟨pin,action.generation,action.ordinal + 1,
    actionStream.encode {action with applicationSignedBytes := [], controlSignedBytes := []},
    action.homeProjectionBytes⟩

def overhead (action : Action) : Charge
  | .turnBytes => (encode action).length
  | .proofWork => action.program.checkerTicks + action.sourceLimits.checkerTicks +
      action.sourceLimits.classificationTicks * (action.sourceLimits.sourceSteps + 1)
  | .memoryTouches => action.program.slots * (action.decodeTicks + 2)
  | .incidences | .storageBytes | .feeDebit | .networkBytes | .witnessBytes |
      .sideEffectCount | .leaseByteBlocks => 0

/-- An inert exact signed proposal. Signature/current application authority is
checked only at dispatch, once its pending-phase permit exists. This object has
no AcceptedInvocation, no DataIntent and no permission to publish anything. -/
structure Application (domain semantics : Digest) (bytes : List UInt8) where
  private mk ::
  command : Command
  signed : SignedCommand
  scope : bytes = signedBytes domain semantics signed
  decoded : commandCodec.decode signed.commandBytes = some command

def parseApplication (domain semantics : Digest) (bytes : List UInt8) :
    Option (Application domain semantics bytes) := do
  let some (actualDomain,actualSemantics,signed) := decodeSignedBytes bytes | none
  if actualDomain != domain || actualSemantics != semantics then none else do
    if scope : bytes = signedBytes domain semantics signed then
      match decoded : commandCodec.decode signed.commandBytes with
      | none => none
      | some command => some ⟨command,signed,scope,decoded⟩
    else none

structure Admitted (config : Config) (opened : Opened config) where
  private mk ::
  action : Action
  pin : ContentControlFrame.Pin
  pinned : config.activityControl = some pin
  program : BendActivityProgram.Prepared action.program
  before : BendActivity.Record
  current : BendActivityControl.readRecord pin (opened.durable.snapshot.canonicalBytes pin.cell) = some before
  prepared : BendActivitySuspension.Prepared program before action.sourceLimits action.response action.signature
  application : Application config.deployment.domain config.profile.semantics action.applicationSignedBytes
  familyExact : application.command.family = some ⟨.activityDispatch,applicationContext pin action⟩
  control : BendActivityIngress.Current config opened
  applicationBytes : action.applicationSignedBytes =
    signedBytes config.deployment.domain config.profile.semantics application.signed
  controlBytes : action.controlSignedBytes =
    signedBytes config.deployment.domain config.profile.semantics control.signed
  identity : List UInt8
  identityExact : identity = digestStream.encode
    (transactionId config.deployment.domain config.profile.semantics application.command)
  pending : BendActivitySuspension.PendingCandidate prepared pin.cell identity action.applicationSignedBytes
  applicationCommand : pending.command = application.command
  intent : DataIntent ResourceBirthCodec.rootBytes
  writesExact : intent.writes = control.intent.writes
  guardsExact : intent.readGuards = control.intent.readGuards
  chargeExact : intent.exactCharge = control.intent.exactCharge + overhead action
  eventExact : intent.event.canonicalBytes = encode action
  carries : BendActivityControl.claim ResourceBirthCodec.rootBytes pin before ∈ intent.nullifiers
  post : ∃ write ∈ intent.writes, write.cellId = pin.cell ∧
    ContentControlFrame.readPayload pin write.canonicalPostBytes = some (BendActivity.encode pending.record)
  ready : intent.preflight opened.durable.snapshot = .ok ()
  otherFacets : config.otherFacetGate .activity opened.durable.snapshot intent = .ok ()

/-- Only the controller transition is authorized and installed here. The
source Plan must match the inert exact application proposal; its current law,
signature, full usage and funding are checked at guarded publication, not guessed
in advance. No application budget reservation is manufactured by preparation. -/
def construct {config : Config} {opened : Opened config}
    (action : Action) (pin : ContentControlFrame.Pin) (pinned : config.activityControl = some pin)
    (program : BendActivityProgram.Prepared action.program)
    (application : Application config.deployment.domain config.profile.semantics action.applicationSignedBytes)
    (control : BendActivityIngress.Current config opened) : Option (Admitted config opened) := do
  if familyExact : application.command.family = some ⟨.activityDispatch,applicationContext pin action⟩ then
   if control.command.subject != pin.owner || control.command.nonce != nonce action ||
       control.command.targets.length != 1 ||
       !control.command.targets.all (fun target => decide (target.kind = .object ∧ target.target = pin.cell.value)) then none else do
    if controlBytes : action.controlSignedBytes = signedBytes config.deployment.domain config.profile.semantics control.signed then
     match current : BendActivityControl.readRecord pin (opened.durable.snapshot.canonicalBytes pin.cell) with
     | none => none
     | some before =>
       if before.checkpoint.generation != action.generation || before.ordinal != action.ordinal then none else do
        let bytes := encode action
        let base := control.intent
        let intent : DataIntent ResourceBirthCodec.rootBytes :=
          {base with nullifiers := BendActivityControl.claim ResourceBirthCodec.rootBytes pin before :: base.nullifiers, exactCharge := base.exactCharge + overhead action, event := ⟨64,config.deployment.domain,ResourceBirthCodec.rootBytes bytes,bytes⟩}
        if ready : intent.preflight opened.durable.snapshot = .ok () then
         if otherFacets : config.otherFacetGate .activity opened.durable.snapshot intent = .ok () then
          let prepared ← BendActivitySuspension.prepare program before action.sourceLimits action.response action.signature action.decodeTicks
          let identity := digestStream.encode (transactionId config.deployment.domain config.profile.semantics application.command)
          let pending ← BendActivitySuspension.pendingCandidate prepared pin.cell identity action.applicationSignedBytes
          if applicationCommand : pending.command = application.command then
           if post : ∃ write ∈ intent.writes, write.cellId = pin.cell ∧
               ContentControlFrame.readPayload pin write.canonicalPostBytes = some (BendActivity.encode pending.record) then
             some ⟨action,pin,pinned,program,before,current,prepared,application,familyExact,control,
               application.scope,controlBytes,identity,rfl,pending,applicationCommand,
               intent,rfl,rfl,rfl,rfl,by simp [intent],post,ready,otherFacets⟩
           else none
          else none
         else none
        else none
    else none
  else none

/-- Reuses the actual native signer/current-controller admission at this loaded
prefix. The returned Current is not fabricated from signature-shaped bytes. -/
def readCurrent (config : Config) (opened : Opened config) (bytes : List UInt8) :
    IO (Except String (BendActivityIngress.Current config opened)) := do
  let some (domain,semantics,signed) := decodeSignedBytes bytes | return .error "malformed native application"
  if domain != config.deployment.domain || semantics != config.profile.semantics then return .error "native application scope mismatch"
  let some command := commandCodec.decode signed.commandBytes | return .error "native application command malformed"
  match prepareFrom config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable (some opened.directory) command with
  | .error _ => return .error "native current preparation refused"
  | .ok prepared =>
    if shape : PhysicalShape prepared then
      match ← DeclaredResourceController.admit config.signature prepared signed with
      | .error _ => return .error "native current authority refused"
      | .ok accepted => return .ok ⟨command,signed,prepared,shape,accepted⟩
    else return .error "native physical shape refused"

def admit (config : Config) (opened : Opened config) (bytes : List UInt8)
    (replay : Bool := false) : IO (Except String (Admitted config opened)) := do
  if bytes.length > 4194304 then return .error "pending envelope capacity"
  let some action := decode bytes | return .error "pending canonical envelope refused"
  if action.decodeTicks > 100000 || action.sourceLimits.checkerTicks > 100000 ||
      action.sourceLimits.classificationTicks > 100000 || action.sourceLimits.sourceSteps > 100000 ||
      action.sourceLimits.outputTermSize > 1048576 then return .error "pending semantic capacity"
  if !replay && action.sourceLimits.sourceSteps > config.activityTickLimit then return .error "pending live work limit"
  let some pin := config.activityControl | return .error "activity facet absent"
  if pinned : config.activityControl = some pin then
    let .ok control ← readCurrent config opened action.controlSignedBytes | return .error "pending control authority refused"
    if control.command.subject != pin.owner || control.command.nonce != nonce action then return .error "pending signed action mismatch"
    let some application := parseApplication config.deployment.domain config.profile.semantics action.applicationSignedBytes
      | return .error "pending application proposal malformed"
    let some program := BendActivityProgram.prepare action.program | return .error "pending source publication refused"
    let some admitted := construct action pin pinned program application control | return .error "pending source/phase/funding refused"
    return .ok admitted
  else return .error "pending pin changed"

/-- Exact typed pending admission exempts only its own protected facet; all
other facets see the same full intent. Consensus transport behavior is retained. -/
def transport {config : Config} {opened : Opened config}
    (admitted : Admitted config opened) : DurableReceiverIO.Transport :=
  {config.transport with sourceGate := fun snapshot proposed => do
    config.otherFacetGate .activity snapshot proposed
    if DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent proposed) =
        DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent admitted.intent) ∧
        snapshot.canonicalBytes admitted.pin.cell = opened.durable.snapshot.canonicalBytes admitted.pin.cell
    then .ok () else .error (.durable .transactionConflict)}

theorem transport_other_facets {config : Config} {opened : Opened config}
    (admitted : Admitted config opened) (snapshot : DataSnapshot ResourceBirthCodec.rootBytes)
    (proposed : DataIntent ResourceBirthCodec.rootBytes)
    (accepted : (transport admitted).sourceGate snapshot proposed = .ok ()) :
    config.otherFacetGate .activity snapshot proposed = .ok () := by
  cases checked : config.otherFacetGate .activity snapshot proposed with
  | error reason => simp [transport,checked] at accepted
  | ok value => cases value; exact checked

inductive Result (config : Config) (opened : Opened config) where
  | appended (admitted : Admitted config opened)
      (receipt : DurableReceiverIO.Appended ResourceBirthCodec.rootBytes opened.durable admitted.intent)
  | replayed (recorded : DurableCommitProtocol.Intent Digest Digest StableNullifier ReplayEnvelope)
  | refused (reason : String)
  | ordinary (result : DurableReceiverIO.Result ResourceBirthCodec.rootBytes)

/-- Commit the pending phase through the existing native durable protocol.
Exact same-operation source bytes recover the original receipt. A different
source action cannot reuse that transaction identity. No app effect runs here. -/
def receive (config : Config) (opened : Opened config) (bytes : List UInt8) : IO (Result config opened) := do
  if bytes.length > 4194304 then return .refused "pending envelope capacity"
  let some action := decode bytes | return .refused "pending canonical envelope refused"
  let some (domain,semantics,signed) := decodeSignedBytes action.controlSignedBytes
    | return .refused "pending original signature malformed"
  if domain != config.deployment.domain || semantics != config.profile.semantics then return .refused "pending scope mismatch"
  let some command := commandCodec.decode signed.commandBytes | return .refused "pending command malformed"
  match DurableCommitProtocol.Snapshot.lookupRecorded
      (transactionId domain semantics command) opened.durable.snapshot.model.journal with
  | some recorded =>
      if recorded.event.event.codecVersion = 64 ∧ recorded.event.event.domain = domain ∧
          recorded.event.event.canonicalBytes = bytes then return .replayed recorded
      else return .refused "pending transaction conflict"
  | none =>
      match ← admit config opened bytes with
      | .error reason => return .refused reason
      | .ok admitted =>
          match ← DurableReceiverIO.receiveLoadedDetailed (transport admitted)
              ResourceBirthCodec.rootBytes opened.durable admitted.intent with
          | .exact _ receipt => return .appended admitted receipt
          | .ordinary result => return .ordinary result

#assert_axioms parseApplication
#assert_axioms applicationContext
#assert_axioms transport_other_facets
#assert_axioms receive
#assert_axioms construct
#assert_axioms readCurrent
#assert_axioms admit
end Minidregg.Kernel.BendActivityPendingAdmission
