/- Native dispatch on the refreshed light session. Private entry-to-handoff code joins
the selected historical admissions, current signed authority, exact readback and CAS winner. -/
module
public import Kernel.ApplicationDispatchReceiver
public import Kernel.ApplicationDispatchAgentReceiver
public import Kernel.ApplicationAgentLifetimeDispatchReceiver
public import Kernel.ApplicationAgentLifetimeGrantReceiver

@[expose] public section
namespace Minidregg.Kernel.ApplicationDispatchLightReceiver
open Minidregg.Compiler Minidregg.Compiler.ResourceBirthCodec Minidregg.Kernel.NativeHost

set_option autoImplicit false

/-- A handoff minted by the receiver. Its action repeats the physical tip comparison at
the instant the private frame is written. -/
structure LightHandoff where
  private mk ::
  run : (ByteArray → IO Unit) → IO (Except String Unit)

inductive LightResult (Absence : Type) where
  | permitted (permit : LightHandoff)
  | confirmed (kind : DurableReceiverIO.Confirmation) (receipt : NativeHostCodec.Receipt)
  | noRecordRefused (refusal : Absence)
  | rejected (detail : String)
  | contention
  | unavailable (detail : String)
  | uncertain (detail : String)

/-- Validate the successor of an actual served append. A delivery frame leaves only
through the callback of a winning install whose exact record and tag are still the tip. -/
private def finishReadback {config : Config} {Absence : Type} (light : NativeHostLight.Light config)
    (intent : DurableDataIntent.DataIntent rootBytes) (readback : DurableServed.Received rootBytes light.opening intent)
    (encode : NativeHostCodec.Receipt → ByteArray) (adopt : NativeHostLight.Adopt light.opening)
    (recoverReceipt : Bool) : IO (LightResult Absence) := do
  match readback with
  | .appended kind next _ entry _ fresh moved =>
    let written := intent.writes.map DurableDataIntent.DataWrite.cellId
    if let .error detail := light.adoptStep next written moved then return .uncertain detail
    let receipt : NativeHostCodec.Receipt := ⟨intent.transactionId, intent.event.eventId, next.head.height, next.head.root⟩
    if fresh && kind == .installed then
      let frame := encode receipt
      return .permitted ⟨fun handoff => do
        let .ok true ← DurableReceiverIO.tipIs config.transport next.head.height entry
          | return .error "dispatch physical tip changed before handoff"
        handoff frame
        adopt next written moved
        return .ok ()⟩
    unless recoverReceipt do return .uncertain "lifetime dispatch exact readback without fresh CAS winner"
    adopt next written moved
    return .confirmed kind receipt
  | .replayed _ => return .uncertain "dispatch confirmation lacks exact fresh post-CAS readback"
  | .rejected reason => return .rejected s!"durable dispatch refused: {repr reason}"
  | .contention => return .contention
  | .unavailable detail => return .unavailable detail
  | .uncertain detail => return .uncertain detail

private def receiveLightIngress (config : Config) (light : NativeHostLight.Light config)
    (ingress : ApplicationDispatchAdmissionIngress.Ingress) (constraint : Option ApplicationDispatchReceiver.RouteConstraint) (adopt : NativeHostLight.Adopt light.opening) :
    IO (LightResult LightHandoff) := do
  let some selection := ApplicationDispatchAdmission.selectCommand ingress
    | return .rejected "dispatch exact-call absence unavailable"
  let cmd := ApplicationDispatchCommand.command ingress.dispatch selection ingress.parent
  let tx := DeclaredResourceController.transactionId ingress.dispatch.domain ingress.dispatch.semantics cmd
  let reader := light.opening.reader config.transport rootBytes
  match ← reader.byTx tx with
  | .error refusal => return .unavailable refusal.message
  | .ok (.present found) =>
    let record := found.read.record
    if record.event == ApplicationDispatchAdmissionIngress.event ingress &&
        record.nullifiers.contains (ApplicationDispatchAdmissionIngress.nullifier ingress) then
      return .confirmed .replayed (receiptOfRecord found.read)
    return .rejected "dispatch transaction identity conflict"
  | .ok (.absent _) =>
    let refusal : LightHandoff := ⟨fun handoff =>
      ApplicationStreamContinuity.withLightFreshTip light (handoff ApplicationDispatchReceiver.noRecordRefusalBytes.toByteArray)⟩
    if ApplicationStreamContinuity.reservedProbe ingress.dispatch.dispatch.request ||
        ingress.dispatch.dispatch.session.origin != .human then return .noRecordRefused refusal
    let .ok admitted ← (ApplicationDispatchLight.admit config light ingress).run | return .noRecordRefused refusal
    if !constraint.all (fun route => route.domain == config.deployment.domain &&
        route.semantics == config.profile.semantics && route.binding == ApplicationStreamContinuity.lightBinding admitted) then
      return .noRecordRefused refusal
    let intent := ApplicationDispatchPending.candidateIntent admitted.checked.checked
    if tx != intent.transactionId then return .rejected "dispatch transaction differs from checked command"
    let readback ← DurableServed.receiveServed config.transport rootBytes light.opening intent
    finishReadback light intent readback (fun receipt => (ApplicationDispatchReceiver.committedCodec.encode
      (ApplicationDispatchProjection.ofChecked admitted.checked intent light.opening.head.root, receipt)).toByteArray) adopt true

def receiveHuman (config : Config) (light : NativeHostLight.Light config) (bytes : ByteArray)
    (routeBound : Bool) (adopt : NativeHostLight.Adopt light.opening) : IO (LightResult LightHandoff) := do
  let envelope := if routeBound then
      (ApplicationDispatchReceiver.routeBoundCodec.decode bytes.toList).map fun (route, source) => (some route, source)
    else some (none, bytes.toList)
  let some (constraint, source) := envelope | return .rejected "noncanonical route-bound dispatch envelope"
  let some ingress := ApplicationDispatchAdmissionIngress.codec.decode source
    | return .rejected "noncanonical special dispatch ingress"
  receiveLightIngress config light ingress constraint adopt

private def proposedAgent {config : Config} (light : NativeHostLight.Light config) (ingress : ApplicationDispatchAgentIngress.Ingress) :
    ExceptT String IO (DurableDataIntent.DataIntent ResourceBirthCodec.rootBytes × ApplicationDispatchAgentProjection.Paid) := do
  let .agent _ _ := ingress.dispatch.dispatch.dispatch.session.origin | throw "paid dispatch requires agent origin"
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let ⟨index, issue⟩ ← ApplicationDispatchLight.selectSignedIssue config light ingress.dispatch
  if index ≥ ingress.reserveIndex then throw "issued ticket must precede reserve"
  let raw ← ExceptT.mk ((·.mapError (·.message)) <$> (NativeHostReplay.selectReserve config reader ingress.reserveIndex).run)
  let bound ← raw.bindContext ingress.reserveContext
  discard <| ApplicationDispatchLight.reserveLastWrite reader ingress.reserveIndex ⟨ingress.reserveContext.purseTask⟩
    "purse changed after original reserve"
  let basis ← ApplicationDispatchLight.paidBasis config light ingress.dispatch ingress.payerSigned
  let checked ← ExceptT.mk (ApplicationDispatchAgentCore.checkCurrent config (.ofBasis basis) ingress issue.evidence bound)
  let some projection := ApplicationDispatchAgentProjection.ofChecked checked ingress.reserveIndex raw.receipt
    | throw "agent dispatch physical projection refused"
  let intent := ApplicationDispatchAgentCore.candidateIntent checked
  let some none := (ServedBasis.Ground.ofBasis basis).recorded intent.transactionId
    | throw "dispatch transaction identity already used"
  return (intent, projection)

def receiveAgent {config : Config} (light : NativeHostLight.Light config) (bytes : ByteArray)
    (adopt : NativeHostLight.Adopt light.opening) : IO (LightResult Empty) := do
  let some ingress := ApplicationDispatchAgentIngress.codec.decode bytes.toList | return .rejected "noncanonical paid dispatch"
  match ← (proposedAgent light ingress).run with
  | .error detail => return .rejected detail
  | .ok (intent, projection) =>
    let readback ← DurableServed.receiveServed config.transport ResourceBirthCodec.rootBytes light.opening intent
    finishReadback light intent readback (fun receipt => (ApplicationDispatchAgentReceiver.committedCodec.encode (projection, receipt)).toByteArray)
      adopt true


private def proposedLifetime {config : Config} (light : NativeHostLight.Light config) (ingress : ApplicationAgentLifetimeDispatchIngress.Ingress) :
    ExceptT String IO (DurableDataIntent.DataIntent ResourceBirthCodec.rootBytes × ApplicationAgentLifetimeDispatchProjection.Paid) := do
  let .agent _ _ := ingress.dispatch.dispatch.dispatch.session.origin | throw "paid dispatch requires agent origin"
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let selected ← ExceptT.mk ((·.mapError (·.message)) <$>
    (ApplicationAgentLifetimeGrantReceiver.selectGrant config light ingress.reserveContext.grantIssueIndex).run)
  let issued := selected.ticket.evidence
  let grant := selected.ingress.spec.grant
  if ingress.reserveContext.grantIssueIndex ≥ ingress.reserveIndex then throw "grant must precede reserve"
  let root := (ResourceBirthController.birthWrite selected.accepted.sourceReady.birth.create).exactPost
  let raw ← ExceptT.mk ((·.mapError (·.message)) <$> (NativeHostReplay.selectReserve config reader ingress.reserveIndex).run)
  let bound ← ApplicationAgentLifetimeDispatchReserveCore.bindContext raw ingress.reserveContext
  discard <| ApplicationDispatchLight.reserveLastWrite reader ingress.reserveIndex ⟨ingress.reserveContext.base.purseTask⟩
    "purse changed after original reserve"
  let basis ← ApplicationDispatchLight.paidBasis config light ingress.dispatch ingress.payerSigned
  let checked ← ExceptT.mk (ApplicationAgentLifetimeDispatchCore.checkCurrent config (.ofBasis basis) ingress
    issued.spec issued.descriptor grant grant.source.issueIndex (receiptOfRecord selected.ticket.candidate.read)
    issued.ingressBytes ingress.reserveContext.grantIssueIndex root bound)
  let some projection := ApplicationAgentLifetimeDispatchProjection.ofChecked issued checked (receiptOfRecord selected.candidate.read)
    ingress.reserveIndex raw.receipt | throw "lifetime dispatch physical projection refused"
  let intent := ApplicationAgentLifetimeDispatchCore.candidateIntent checked
  let some none := (ServedBasis.Ground.ofBasis basis).recorded intent.transactionId
    | throw "dispatch transaction identity already used"
  return (intent, projection)

def receiveLifetime {config : Config} (light : NativeHostLight.Light config) (bytes : ByteArray)
    (adopt : NativeHostLight.Adopt light.opening) : IO (LightResult Empty) := do
  let some ingress := ApplicationAgentLifetimeDispatchIngress.codec.decode bytes.toList | return .rejected "noncanonical paid dispatch"
  match ← (proposedLifetime light ingress).run with
  | .error detail => return .rejected detail
  | .ok (intent, projection) =>
    let readback ← DurableServed.receiveServed config.transport ResourceBirthCodec.rootBytes light.opening intent
    finishReadback light intent readback (fun receipt => (ApplicationAgentLifetimeDispatchReceiver.committedCodec.encode (projection, receipt)).toByteArray)
      adopt false


end Minidregg.Kernel.ApplicationDispatchLightReceiver
