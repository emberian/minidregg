/- Source event62: current native signed admission plus exact Activity phase.
The event retains the source program, selected action and original signed call;
live admission and chronological replay reconstruct the same complete record.
No decoded checkpoint or transport receipt supplies current authority. -/
import Kernel.NativeHostContext
import Kernel.DeclaredResourceController
import Compiler.BendActivityProgram

namespace Minidregg.Kernel.BendActivityIngress
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.DeclaredResourceController
set_option autoImplicit false
set_option maxHeartbeats 800000

structure Source where
  program : BendActivityProgram.Source
  initialize : Bool
  generation : Nat
  ordinal : Nat
  ticks : Nat
  signedBytes : List UInt8

def sourceStream : StreamCodec Source :=
  StreamCodec.xmap (StreamCodec.product BendActivityProgram.sourceStream
    (StreamCodec.product StreamCodec.bool (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat (StreamCodec.product StreamCodec.nat bytesStream)))))
    (fun s => (s.program,s.initialize,s.generation,s.ordinal,s.ticks,s.signedBytes))
    (fun (p,i,g,o,t,s) => ⟨p,i,g,o,t,s⟩) (by intro s; cases s; rfl)

def frame : List UInt8 := "DREGG/BEND/ACTIVITY-SOURCE/v1".toUTF8.toList
def encode (source : Source) : List UInt8 := frame ++ sourceStream.encode source
def decode (bytes : List UInt8) : Option Source :=
  NockProgramCodec.framedDecode frame sourceStream bytes

/-- The original signed command nonce commits to the complete phase action and
its public tariff inputs, excluding only the signature envelope itself. Thus an
unsigned relay cannot increase ticks/checker cost on an absorbing result while
reusing the same signature. This uses the same explicit cryptographic digest
assumption as native command identity; it is not an injectivity theorem. -/
def actionBytes (source : Source) : List UInt8 :=
  BendActivityProgram.sourceStream.encode source.program ++
    (StreamCodec.product StreamCodec.bool (StreamCodec.product StreamCodec.nat
      (StreamCodec.product StreamCodec.nat StreamCodec.nat))).encode
      (source.initialize,source.generation,source.ordinal,source.ticks)

def actionNonce (source : Source) : Nat :=
  (Sp800185Cshake256.hash "DREGG/BEND/ACTIVITY-AUTHORIZED-ACTION/v1".toUTF8.toList
    (actionBytes source)).digest.value

/-- A public versioned verifier tariff. proofWork counts bounded controller
microticks; memoryTouches charges the fixed public arena/stack/input/lookup
capacity per tick. This is not a wall-clock bound or hidden source-step meter.
The original native operation retains all ten original charge lanes. -/
def overhead (source : Source) : Charge
  | .turnBytes => (encode source).length
  | .proofWork => source.ticks + source.program.checkerTicks
  | .memoryTouches => source.program.slots + source.ticks *
      (source.program.slots + source.program.frames + source.program.arguments + 1)
  | .incidences | .storageBytes | .feeDebit | .networkBytes | .witnessBytes |
      .sideEffectCount | .leaseByteBlocks => 0

structure Current (config : Config) (opened : Opened config) where
  command : Command
  signed : SignedCommand
  prepared : PreparedInvocation config.deployment config.profile
    ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable command
  shape : PhysicalShape prepared
  accepted : AcceptedInvocation prepared signed

def Current.intent {config : Config} {opened : Opened config}
    (current : Current config opened) : DataIntent ResourceBirthCodec.rootBytes :=
  current.accepted.dataIntent current.shape

/-- Every accepted phase certificate constrains the actual native intent. -/
inductive PhaseEvidence (config : Config) (opened : Opened config)
    (pin : ContentControlFrame.Pin) (source : Source)
    (program : BendActivityProgram.Prepared source.program)
    (intent : DataIntent ResourceBirthCodec.rootBytes) : Type
  | initialize (checked : BendActivityControl.CheckedInitialize pin
      (BendActivityProgram.binding source.program) source.generation program.limits
      program.compiled.library program.compiled.entry opened.durable.snapshot intent)
  | advance (checked : BendActivityControl.CheckedAdvance pin program.limits
      program.compiled.library source.ticks opened.durable.snapshot intent)

structure Admitted (config : Config) (opened : Opened config) where
  private mk ::
  source : Source
  pin : ContentControlFrame.Pin
  pinned : config.activityControl = some pin
  program : BendActivityProgram.Prepared source.program
  current : Current config opened
  signedExact : source.signedBytes = signedBytes config.deployment.domain config.profile.semantics current.signed
  intent : DataIntent ResourceBirthCodec.rootBytes
  writesExact : intent.writes = current.intent.writes
  guardsExact : intent.readGuards = current.intent.readGuards
  chargeExact : intent.exactCharge = current.intent.exactCharge + overhead source
  eventExact : intent.event.canonicalBytes = encode source
  phase : PhaseEvidence config opened pin source program intent
  ready : intent.preflight opened.durable.snapshot = .ok ()

def construct {config : Config} {opened : Opened config}
    (source : Source) (pin : ContentControlFrame.Pin)
    (pinned : config.activityControl = some pin)
    (program : BendActivityProgram.Prepared source.program)
    (current : Current config opened) : Option (Admitted config opened) := do
  if current.command.subject != pin.owner || current.command.nonce != actionNonce source then none else do
    if signedExact : source.signedBytes = signedBytes config.deployment.domain config.profile.semantics current.signed then do
      let base := current.intent
      let mut claims := base.nullifiers
      if !source.initialize then
        let before ← BendActivityControl.readRecord pin (opened.durable.snapshot.canonicalBytes pin.cell)
        claims := BendActivityControl.claim ResourceBirthCodec.rootBytes pin before :: claims
      let bytes := encode source
      let intent : DataIntent ResourceBirthCodec.rootBytes :=
        {base with nullifiers := claims, exactCharge := base.exactCharge + overhead source,
          event := ⟨62,config.deployment.domain,ResourceBirthCodec.rootBytes bytes,bytes⟩}
      if ready : intent.preflight opened.durable.snapshot = .ok () then
        if source.initialize then
          if source.ordinal != 0 || source.ticks != 0 then none else do
            let checked ← BendActivityControl.checkInitialize pin
              (BendActivityProgram.binding source.program) source.generation program.limits
              program.compiled.library program.compiled.entry opened.durable.snapshot intent
            some ⟨source,pin,pinned,program,current,signedExact,intent,rfl,rfl,rfl,rfl,.initialize checked,ready⟩
        else do
          let checked ← BendActivityControl.checkAdvance pin
            (BendActivityProgram.binding source.program) program.limits program.compiled.library source.ticks
            source.generation source.ordinal (opened.durable.snapshot.canonicalBytes pin.cell)
            opened.durable.snapshot intent
          some ⟨source,pin,pinned,program,current,signedExact,intent,rfl,rfl,rfl,rfl,.advance checked,ready⟩
      else none
    else none

/-- replay=true is used only by the chronological source verifier: operator
live workload caps cannot invalidate already-admitted history. Semantic caps,
source checking, current-prefix authority, exact phase and funding still run. -/
def admit (config : Config) (opened : Opened config) (bytes : List UInt8)
    (replay : Bool := false) : IO (Except String (Admitted config opened)) := do
  if bytes.length > 4194304 then return .error "activity source envelope exceeds v1 cap"
  let some source := decode bytes | return .error "noncanonical activity source"
  if !replay && source.ticks > config.activityTickLimit then return .error "activity live tick limit"
  let some pin := config.activityControl | return .error "activity facet not enabled"
  if pinned : config.activityControl = some pin then
    let some (domain,semantics,signed) := decodeSignedBytes source.signedBytes
      | return .error "malformed activity signed operation"
    if domain != config.deployment.domain || semantics != config.profile.semantics then
      return .error "activity source scope mismatch"
    let some command := commandCodec.decode signed.commandBytes | return .error "activity command malformed"
    match prepareFrom config.deployment config.profile
        ⟨config.federation,logicalHeight config opened.durable⟩ opened.durable (some opened.directory) command with
    | .error _ => return .error "activity current source preparation refused"
    | .ok prepared =>
      if shape : PhysicalShape prepared then
        match ← DeclaredResourceController.admit config.signature prepared signed with
        | .error _ => return .error "activity current source authority refused"
        | .ok accepted =>
          if command.subject != pin.owner || command.nonce != actionNonce source then
            return .error "activity owner or signed action mismatch"
          let some program := BendActivityProgram.prepare source.program
            | return .error "activity source admission refused"
          let current : Current config opened := ⟨command,signed,prepared,shape,accepted⟩
          let some admitted := construct source pin pinned program current
            | return .error "activity exact phase or funding refused"
          return .ok admitted
      else return .error "activity physical shape refused"
  else return .error "activity pin mismatch"

#assert_axioms construct
#assert_axioms admit
end Minidregg.Kernel.BendActivityIngress
