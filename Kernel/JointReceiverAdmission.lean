/- Atomic native reservation construction. The source-owned control update,
PENDING preparation and private repair envelopes form ONE existing DataIntent record.
The constructor consumes current ordinary AND purpose-specific permission and
a separately source-admitted control edit on the SAME actual Durable image. -/
import Kernel.JointPromiseAuthorization
import Compiler.JointControlFrame
namespace Minidregg.Kernel.JointReceiverAdmission
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.ResourceCost
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DeclaredResourceController
open Minidregg.Kernel.JointInvocationCandidate
open Minidregg.Kernel.JointReservation
open Minidregg.Kernel.JointControlCell
set_option autoImplicit false
set_option maxHeartbeats 800000

structure ReserveSource where
  candidateBytes : List UInt8
  participant : Nat
  promise : JointPromiseAuthorization.Signed
  controlSignedBytes : List UInt8

def reserveSourceStream : StreamCodec ReserveSource :=
  StreamCodec.xmap (StreamCodec.product bytesStream (StreamCodec.product StreamCodec.nat
    (StreamCodec.product JointPromiseAuthorization.signedStream bytesStream)))
    (fun s => (s.candidateBytes,s.participant,s.promise,s.controlSignedBytes))
    (fun (c,i,p,s) => ⟨c,i,p,s⟩) (by intro s; cases s; rfl)
def reserveSourceBytes (source : ReserveSource) : List UInt8 :=
  "DREGG/JOINT/SOURCE-RESERVE/v1".toUTF8.toList ++ reserveSourceStream.encode source

def decisionKey (candidate : List UInt8) (participant : Nat) : List UInt8 :=
  (StreamCodec.product bytesStream StreamCodec.nat).encode (candidate,participant)
def decisionValue (candidate : List UInt8) (participant : Nat) (yes : Bool) : List UInt8 :=
  (StreamCodec.product bytesStream StreamCodec.bool).encode (decisionKey candidate participant,yes)

def dependencies {rootBytes : List UInt8 → Digest} (effect : DataIntent rootBytes) : List ReadGuard :=
  effect.readGuards ++ effect.writes.map (fun w => ⟨w.cellId,w.expectedPre⟩)

/-- All ten lanes come from the actual new source record. Selected effect
charges stay in the reservation and will be debited at installation. Maintenance
is funded separately, not represented by a traffic priority bit. -/
def reserveOverhead {rootBytes : List UInt8 → Digest} (bytes : List UInt8)
    (effect : DataIntent rootBytes) (guards : List ReadGuard) : Charge
  | .incidences => effect.exactCharge .incidences * 2
  | .turnBytes => bytes.length
  | .memoryTouches => guards.length
  | .storageBytes => 0
  | .proofWork => effect.exactCharge .proofWork
  | .feeDebit | .networkBytes | .witnessBytes | .sideEffectCount | .leaseByteBlocks => 0

/-- The current control method's entire exact charge survives. The additional
source operation counts the selected admission and explicit promise admission,
the retained source envelope and extra guard inspection. It does not replace
feeDebit or any other lane with an invented cheaper receipt. -/
def reserveCharge {rootBytes : List UInt8 → Digest} (bytes : List UInt8)
    (control effect : DataIntent rootBytes) (guards : List ReadGuard) : Charge :=
  control.exactCharge + reserveOverhead bytes effect guards

/-- PENDING preparation is not a YES certificate. Physical allocation and
actual privateRecovery qualification precede a separate terminal YES record.
Native state-transition capability. The token is not a raw IntentRecord.
Its permission provenance is retained through the single physical append. -/
structure Reserved {F : Type} [Field F] [DecidableEq F]
    (deployment : Deployment) (profile : CanonicalRuntimeProfile.Profile F)
    (ambient : Ambient) (durable : Durable) where
  private mk ::
  intent : DataIntent ResourceBirthCodec.rootBytes
  original : DataIntent ResourceBirthCodec.rootBytes
  selected : DataIntent ResourceBirthCodec.rootBytes
  originalWrites : selected.writes = original.writes
  originalClaims : selected.nullifiers = original.nullifiers
  originalCharge : selected.exactCharge = original.exactCharge
  originalEvent : selected.event = original.event
  originalSubject : selected.subject = original.subject
  reservation : Reservation
  pin : JointControlFrame.Pin
  before : Control
  after : Control
  source : ReserveSource
  sourceCurrent : source.promise.declaration.sourceImageBytes = DurableReceiverCodec.imageStream.encode durable.image
  selectedExact : reservation.intent = IntentRecord.ofIntent selected
  allDependencies : ∀ g ∈ dependencies selected, g ∈ intent.readGuards
  beforeExact : JointControlFrame.readControl pin (durable.snapshot.canonicalBytes pin.cell) = some before
  controlWrite : ∃ w ∈ intent.writes, w.cellId = pin.cell ∧
    JointControlFrame.readControl pin w.canonicalPostBytes = some after
  funded : Charge.fundedCheck
    (heldCharge reservation.domain after.reservations + after.maintenanceReserve + intent.exactCharge)
    durable.snapshot.model.available = true
  currentPermission : ∃ (command : Command) (selected : SignedCommand)
    (prepared : PreparedInvocation deployment profile ambient durable command),
    ∃ accepted : JointPromiseAuthorization.Accepted prepared selected source.promise,
      IntentRecord.ofIntent original = IntentRecord.ofIntent (accepted.ordinary.dataIntent accepted.shape)

variable {Custody F : Type} [Field F] [DecidableEq F]
  {deployment : Deployment} {profile : CanonicalRuntimeProfile.Profile F}
  {ambient : Ambient} {durable : Durable} {command controlCommand : Command}
  {prepared : PreparedInvocation deployment profile ambient durable command}
  {controlPrepared : PreparedInvocation deployment profile ambient durable controlCommand}
  {selected controlSigned : SignedCommand} {promise : JointPromiseAuthorization.Signed}

def buildReserve (codec : StreamCodec Custody) (pin : JointControlFrame.Pin)
    (epoch : Nat) (plan : Plan Custody) (i : Fin plan.candidate.participants.length)
    (accepted : JointPromiseAuthorization.Accepted prepared selected promise)
    (controlShape : PhysicalShape controlPrepared)
    (controlAccepted : AcceptedInvocation controlPrepared controlSigned) : Option (Reserved deployment profile ambient durable) := do
  let p := plan.candidate.participants[i]
  let exact := (candidateStream codec).encode plan.candidate
  let effect := accepted.ordinary.dataIntent accepted.shape
  if candidateExact : promise.declaration.candidateBytes = exact then
    if projectionExactBytes : DurableReceiverCodec.intentStream.encode p.intent =
        DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent effect) then
      have projectionExact : p.intent = IntentRecord.ofIntent effect :=
        ResourceBirthCodec.lawful_encode_injective DurableReceiverCodec.intentStream.toLawful projectionExactBytes
      if sourceDomain : p.domain = deployment.domain then
        if promise.declaration.epoch != epoch || p.epoch != epoch ||
            promise.declaration.generation != p.generation then none else
        if (p.footprint.contains pin.cell) then none else
        match beforeExact : JointControlFrame.readControl pin (durable.snapshot.canonicalBytes pin.cell) with
        | none => none
        | some before =>
          if !(before.wellFormed deployment.domain pin.cell) then none else
          if before.reservations.any (fun r => r.domain == p.domain &&
              (r.lineage == plan.candidate.lineage || r.candidateBytes == exact)) then none else
          if before.decisions.any (fun entry => entry.1 == decisionKey exact i.val) then none else
          if !(allowed p.domain before.reservations p.intent durable.snapshot.model.available) then none else
          let control := controlAccepted.dataIntent controlShape
          let extra := control.readGuards.filter (fun g =>
            !(decide (g.cellId ∈ effect.writes.map DataWrite.cellId)))
          let installation : DataIntent ResourceBirthCodec.rootBytes :=
            { effect with
              readGuards := effect.readGuards ++ extra
              guardsReadOnly := by
                intro g hg
                rcases List.mem_append.mp hg with ordinary | added
                · exact effect.guardsReadOnly g ordinary
                · have permitted := (List.mem_filter.mp added).2
                  simpa using permitted }
          if !(allowed p.domain before.reservations (IntentRecord.ofIntent installation)
              durable.snapshot.model.available) then none else
          let held : Reservation := ⟨p.domain,exact,plan.candidate.lineage,IntentRecord.ofIntent installation,
            promise.declaration.sourceImageBytes,p.generation⟩
          let after : Control :=
            ⟨before.reservations ++ [held],
              before.decisions,
              before.repairOutbox ++ promise.declaration.repairEnvelopes,
              before.maintenanceReserve + promise.declaration.maintenance⟩
          if !(after.wellFormed deployment.domain pin.cell) then none else
          match writesExact : control.writes with
          | [write] =>
            if cellExact : write.cellId = pin.cell then
              match readPostExact : JointControlFrame.readControl pin write.canonicalPostBytes with
              | none => none
              | some actualPost =>
                if postExactBytes : controlStream.encode actualPost = controlStream.encode after then
                  have postExact : actualPost = after :=
                    ResourceBirthCodec.lawful_encode_injective controlStream.toLawful postExactBytes
                  let guards := control.readGuards ++ dependencies installation
                  if disjoint : ∀ g ∈ guards, g.cellId ∉ control.writes.map DataWrite.cellId then
                    let source : ReserveSource := ⟨exact,i.val,promise,signedBytes deployment.domain profile.semantics controlSigned⟩
                    let bytes := reserveSourceBytes source
                    let charge := reserveCharge bytes control effect guards
                    let intent : DataIntent ResourceBirthCodec.rootBytes :=
                      { control with
                        readGuards := guards
                        exactCharge := charge
                        nullifiers := control.nullifiers ++
                          [invocationNullifier deployment.domain
                            (JointPromiseAuthorization.commitment deployment.domain profile.semantics promise.declaration).value]
                        event := ⟨60,deployment.domain,
                          JointPromiseAuthorization.commitment deployment.domain profile.semantics promise.declaration,bytes⟩
                        guardsReadOnly := disjoint }
                    if funded : Charge.fundedCheck
                        (heldCharge held.domain after.reservations + after.maintenanceReserve + intent.exactCharge)
                        durable.snapshot.model.available = true then
                      if intent.preflight durable.snapshot != .ok () then none else
                      if effect.preflight durable.snapshot != .ok () then none else
                      let controlPost : ∃ w ∈ intent.writes, w.cellId = pin.cell ∧
                          JointControlFrame.readControl pin w.canonicalPostBytes = some after := by
                        refine ⟨write,?_,?_,?_⟩
                        · change write ∈ control.writes
                          rw [writesExact]
                          exact List.mem_singleton_self write
                        · exact cellExact
                        · rw [readPostExact,postExact]
                      some ⟨intent,effect,installation,rfl,rfl,rfl,rfl,rfl,held,pin,before,after,source,accepted.sourceExact,
                        rfl,by intro g hg; exact List.mem_append_right _ hg,
                        beforeExact,controlPost,funded,
                        ⟨command,selected,prepared,accepted,rfl⟩⟩
                    else none
                  else none
                else none
            else none
          | _ => none
      else none
    else none
  else none

/-- Every selected write pre-root and every actual retained source-law,
authority, clock, negative-predicate and audience guard belongs to the atomic
reservation record. This does not rely on digest injectivity. -/
theorem reserve_retains_dependencies (durable : Durable) (r : Reserved deployment profile ambient durable)
    (guard : ReadGuard) (member : guard ∈ dependencies r.selected) : guard ∈ r.intent.readGuards :=
  r.allDependencies guard member

theorem reserve_has_one_control_commit (durable : Durable) (r : Reserved deployment profile ambient durable) :
    ∃ w ∈ r.intent.writes, w.cellId = r.pin.cell ∧
      JointControlFrame.readControl r.pin w.canonicalPostBytes = some r.after := r.controlWrite

end Minidregg.Kernel.JointReceiverAdmission
