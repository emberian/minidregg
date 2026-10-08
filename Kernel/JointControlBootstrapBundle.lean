/- Recoverable two-record source-control birth. The first source operation
retains the exact signed initializer and admits it on the exact final predicted
post-birth prefix before allowing the bare phase. Prediction is not a physical
receipt or future permission: the second operation re-admits current native
law on that same prefix. No unrelated operation is allowed between phases.
Authored WIP; source opcode 61 and replay/ordered receiver joins are pending.
The predicted prefix is the opened image extended by the first record
(`Loaded.extend`), never a genesis replay of the whole history.
-/
import Kernel.JointControlBootstrap
import Kernel.ResourceBirthReceiver
import Compiler.Sp800185Cshake256
import Theory.AssertAxioms
namespace Minidregg.Kernel.JointControlBootstrapBundle
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
  birthIngressBytes : List UInt8
  initializerSignedBytes : List UInt8
def sourceStream : StreamCodec Source :=
  StreamCodec.xmap (StreamCodec.product bytesStream bytesStream)
    (fun s => (s.birthIngressBytes,s.initializerSignedBytes))
    (fun s => ⟨s.1,s.2⟩) (by intro s; cases s; rfl)
def frame : List UInt8 := "DREGG/JOINT/CONTROL-BOOTSTRAP/v1".toUTF8.toList
def sourceBytes (s : Source) : List UInt8 := frame ++ sourceStream.encode s
def decodeSource (bytes : List UInt8) : Option Source := do
  if bytes.take frame.length != frame then none else
  let source ← sourceStream.toLawful.decode (bytes.drop frame.length)
  if sourceBytes source != bytes then none else some source

/-- Additional operation accounting preserves all ten birth lanes. Source
bytes and two extra current-law validations receive explicit deterministic
charges. This quote is a source operation rule, not a CPU refinement proof. -/
def overhead (source : Source) : Charge
  | .turnBytes => (sourceBytes source).length
  | .proofWork => 2
  | .memoryTouches => 1
  | .incidences | .storageBytes | .feeDebit | .networkBytes | .witnessBytes |
      .sideEffectCount | .leaseByteBlocks => 0

def birthIntent {config : Config} {opened : Opened config}
    (source : Source)
    (accepted : ResourceBirthPolicyController.Concrete.AcceptedBirth config.profile config.deployment
      opened.pins opened.durable (logicalHeight config opened.durable)) :
    DataIntent ResourceBirthCodec.rootBytes :=
  let ordinary := ResourceBirthReceiver.intent accepted
  { ordinary with
    exactCharge := ordinary.exactCharge + overhead source
    event := ⟨61,config.deployment.domain,
      (Sp800185Cshake256.hash frame (sourceBytes source)).digest,sourceBytes source⟩ }

/-- Bootstrap is a creator-owned source resource: the ordinary current creator
signature is also the configured current owner permission. General separately
owned application birth remains the independently consented birth method. -/
def ownerBirthCheck {config : Config} {opened : Opened config}
    (pin : JointControlFrame.Pin)
    (accepted : ResourceBirthPolicyController.Concrete.AcceptedBirth config.profile config.deployment
      opened.pins opened.durable (logicalHeight config opened.durable)) : Bool :=
  decide (accepted.descriptor.creator = pin.owner) &&
  match accepted.descriptor.births with
  | [item] =>
      decide (item.owner = pin.owner) && decide (item.create.cellId = pin.cell.value) &&
      decide (item.create.cell.kind = .content) &&
      decide (JointControlBootstrap.phase pin
        (opened.durable.snapshot.canonicalBytes pin.cell) = some .absent) &&
      (ResourceBirthReceiver.intent accepted).writes.any (fun w =>
        w.cellId == pin.cell &&
        JointControlBootstrap.phase pin w.canonicalPostBytes == some .bare)
  | _ => false

/-- The actual ordinary current initializer admission at the predicted image.
There is no constructor from an envelope, a verification Bool, or old grants. -/
structure Initialization (config : Config) (predicted : Opened config) where
  private mk ::
  signed : SignedCommand
  command : Command
  prepared : PreparedInvocation config.deployment config.profile
    ⟨config.federation,logicalHeight config predicted.durable⟩ predicted.ground command
  shape : PhysicalShape prepared
  accepted : AcceptedInvocation prepared signed
  intent : DataIntent ResourceBirthCodec.rootBytes
  intentExact : intent = accepted.dataIntent shape
  bootstrap : JointControlBootstrap.Admission config predicted intent

/-- A bare source prefix is admitted only together with a CURRENT lawful,
funded, exact initializer, retained verbatim in the first source record. -/
structure Accepted (config : Config) (opened : Opened config) (source : Source) where
  private mk ::
  pin : JointControlFrame.Pin
  pinned : config.jointControl = some pin
  birth : ResourceBirthPolicyController.Concrete.AcceptedBirth config.profile config.deployment
    opened.pins opened.durable (logicalHeight config opened.durable)
  creatorOwner : ownerBirthCheck pin birth = true
  intent : DataIntent ResourceBirthCodec.rootBytes
  intentExact : intent = birthIntent source birth
  birthPreflight : intent.preflight opened.durable.snapshot = .ok ()
  predicted : Opened config
  predictedExact : predicted.durable.image = opened.durable.image.append intent
  initialization : Initialization config predicted
  initializerExact : source.initializerSignedBytes =
    signedBytes config.deployment.domain config.profile.semantics initialization.signed
  initializerFunded : (initialization.accepted.dataIntent initialization.shape).preflight
    predicted.durable.snapshot = .ok ()

def admit (config : Config) (opened : Opened config) (source : Source) :
    IO (Except String (Accepted config opened source)) := do
  let some pin := config.jointControl | return .error "source control not configured"
  if pinned : config.jointControl = some pin then
    let some ingress := ResourceBirthPolicyController.Concrete.decodeIngress source.birthIngressBytes
      | return .error "noncanonical retained bootstrap birth"
    match ← ResourceBirthPolicyController.Concrete.admitDecodedNative config.profile config.deployment
        opened.pins config.signature opened.durable (logicalHeight config opened.durable) ingress with
    | .error reason => return .error s!"bootstrap birth current permission refused: {repr reason}"
    | .ok birth =>
      if creatorOwner : ownerBirthCheck pin birth = true then
        let intent := birthIntent source birth
        if birthPreflight : intent.preflight opened.durable.snapshot = .ok () then
          let image := opened.durable.image.append intent
          -- The prediction is the opened image advanced by exactly this intent through the shared
          -- executor (`DurableCheckpoint.prepare`, then `Loaded.extend`, as a receive advances it);
          -- the history is not replayed again.
          match DurableCheckpoint.prepare opened.durable.image opened.durable.baseHeight opened.durable.base
              opened.durable.snapshot opened.durable.withinLog opened.durable.resumed intent with
          | .inr _ => return .error "bootstrap first source record does not execute at the opened state"
          | .inl ready =>
            let predictedDurable := opened.durable.extend ready
            match validated : validateLoadedFrom config opened predictedDurable with
            | .error detail => return .error detail
            | .ok predicted =>
              let some (domain,semantics,signed) := decodeSignedBytes source.initializerSignedBytes
                | return .error "noncanonical retained bootstrap initializer"
              if domain != config.deployment.domain || semantics != config.profile.semantics then
                return .error "bootstrap initializer domain/profile mismatch"
              if initializerExact : source.initializerSignedBytes =
                  signedBytes config.deployment.domain config.profile.semantics signed then
                let some command := commandCodec.decode signed.commandBytes
                  | return .error "bootstrap initializer command is noncanonical"
                match prepare config.deployment config.profile
                    ⟨config.federation,logicalHeight config predicted.durable⟩
                    predicted.ground command with
                | .error reason => return .error s!"bootstrap initializer preparation refused: {repr reason}"
                | .ok prepared =>
                  if shape : PhysicalShape prepared then
                    match ← DeclaredResourceController.admit config.signature prepared signed with
                    | .error reason => return .error s!"bootstrap initializer current law refused: {repr reason}"
                    | .ok accepted =>
                      let some bootstrap := JointControlBootstrap.admitInitialize shape accepted
                        | return .error "bootstrap initializer is not the exact configured empty control"
                      if initializerFunded : (accepted.dataIntent shape).preflight
                          predicted.durable.snapshot = .ok () then
                        have predictedExact : predicted.durable.image = image := by
                          have durableExact : predicted.durable = predictedDurable := by
                            apply validateLoaded_durable
                            rw [← validateLoadedFrom_eq config opened predictedDurable]
                            exact validated
                          rw [durableExact]
                          rfl
                        return .ok ⟨pin,pinned,birth,creatorOwner,intent,rfl,birthPreflight,
                          predicted,predictedExact,⟨signed,command,prepared,shape,accepted,accepted.dataIntent shape,rfl,bootstrap⟩,
                          initializerExact,initializerFunded⟩
                      else return .error "bootstrap second source record is not funded"
                  else return .error "bootstrap initializer physical shape refused"
              else return .error "bootstrap initializer canonical roundtrip refused"
        else return .error "bootstrap first source record preflight refused"
      else return .error "bootstrap birth owner/phase/shape refused"
  else return .error "bootstrap configured pin mismatch"

/-- Exact first-operation exception only, retaining physical CAS and TailBound.
The actual source readback is still required before executing phase two. -/
def transport {config : Config} {opened : Opened config} {source : Source}
    (accepted : Accepted config opened source) : DurableReceiverIO.Transport :=
  { config.physicalTransport with sourceGate := fun snapshot proposed => do
      config.otherFacetGate .joint snapshot proposed
      if DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent proposed) =
          DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent accepted.intent) ∧
          snapshot.canonicalBytes accepted.pin.cell =
            opened.durable.snapshot.canonicalBytes accepted.pin.cell then .ok ()
      else .error (.durable .transactionConflict) }

def retained_initializer_current_permission {config : Config} {opened : Opened config}
    {source : Source} (accepted : Accepted config opened source) :
    AcceptedInvocation accepted.initialization.prepared accepted.initialization.signed :=
  accepted.initialization.accepted

theorem retained_initializer_has_current_permission {config : Config} {opened : Opened config}
    {source : Source} (accepted : Accepted config opened source) :
    Nonempty (AcceptedInvocation accepted.initialization.prepared accepted.initialization.signed) :=
  ⟨accepted.initialization.accepted⟩

theorem bare_phase_has_exact_funded_next {config : Config} {opened : Opened config}
    {source : Source} (accepted : Accepted config opened source) :
    (accepted.initialization.accepted.dataIntent accepted.initialization.shape).preflight
      accepted.predicted.durable.snapshot = .ok () := accepted.initializerFunded

theorem predicted_source_is_exact_first_record {config : Config} {opened : Opened config}
    {source : Source} (accepted : Accepted config opened source) :
    accepted.predicted.durable.image = opened.durable.image.append accepted.intent :=
  accepted.predictedExact

#assert_axioms retained_initializer_current_permission
#assert_axioms retained_initializer_has_current_permission
#assert_axioms bare_phase_has_exact_funded_next
#assert_axioms predicted_source_is_exact_first_record
end Minidregg.Kernel.JointControlBootstrapBundle
