import Compiler.GenericSimplexController
import Kernel.JointOrderedSourceReceiver
import Theory.AssertAxioms

namespace Minidregg.Compiler.GenericSimplexParticipant
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.GenericSimplexNative
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

abbrev SourceConfig := Minidregg.Kernel.NativeHost.Config
abbrev Durable := Minidregg.Kernel.NativeHost.Durable
abbrev Verified := Minidregg.Kernel.NativeHostReplay.Verified
abbrev Pending := Minidregg.Compiler.GenericSimplexPending.Queue

/-- Only native replay can construct the verified source component. -/
structure Source (config : SourceConfig) where
  target : Durable
  verified : Verified config target

/-- These cursors are transport scheduling hints, not acknowledged-delivery
claims. Restart may reset every cursor: the exact journal retains all messages.
A retry round freezes its end, so a growing fresh outbox cannot starve old sends. -/
structure Schedule where
  fresh : Nat := 0
  retry : Nat := 0
  retryEnd : Nat := 0
  certificates : List (Nat × Block) := []

structure Participant (config : SourceConfig) where
  runtime : Runtime
  source : Source config
  pending : Pending := {}
  schedule : Schedule := {}

/-- The envelope distinguishes authenticated protocol traffic from a transferable
quorum. Canonical decoding rejects aliases and trailing bytes. -/
def frameStream : StreamCodec (Nat × Bytes) :=
  StreamCodec.product StreamCodec.nat bytesStream
def protocolFrame (bytes : Bytes) : Bytes := frameStream.encode (0,bytes)
def certificateFrame (bytes : Bytes) : Bytes := frameStream.encode (1,bytes)

/-- Opening checks the exact configured source genesis against the consensus
anchor through the real historical validator. A journal alone cannot select the
source seed or committee. -/
def openParticipant (config : SourceConfig) (native : Native) (expected : Context)
    (source : Source config) : IO (Except String (Participant config)) := do
  match ← Minidregg.Kernel.JointSourcePrefixValidation.validate config
      source.verified.origin expected [] with
  | .accepted _ =>
    let runtime ← openRuntime native expected
    let some (_,state) := restore expected (← (storage native).read)
      | return .error "invalid durable agreement journal"
    return .ok ⟨runtime,source,
      Minidregg.Compiler.GenericSimplexPending.discover state {},{}⟩
  | .rejected detail => return .error detail
  | .retry failure => return .error failure.detail

/-- Every ingress is durably authenticated before it enters the engine. A
certificate imports its original COMMIT signatures atomically, and discovery
then schedules source validation; neither path grants Input.checked itself. -/
def receive {config : SourceConfig} (p : Participant config) (bytes : Bytes) :
    IO (Participant config × GenericSimplexIO.Result) := do
  let some (tag,payload) := frameStream.toLawful.decode bytes | return (p,.invalid)
  if frameStream.encode (tag,payload) != bytes then return (p,.invalid)
  let result ← match tag with
    | 0 => GenericSimplexNative.receive p.runtime payload
    | 1 => GenericSimplexNative.receiveFinality p.runtime payload
    | _ => pure .invalid
  match result with
  | .durable state =>
    return ({p with pending :=
      Minidregg.Compiler.GenericSimplexPending.discover state p.pending},result)
  | _ => return (p,result)

/-- Preserve the existing outer native call family before generic historical
replay. In particular, a signed invocation hidden inside a birth/install frame
must not bypass the live invocation budget or another family's receiver. These
are the existing native parsers, not alternate signature/admission validators. -/
def sourceCallShape : Minidregg.Compiler.NativeHostCodec.SignedCall → Bool
  | .invoke _ => true
  | .birth bytes =>
      (Minidregg.Kernel.GrainResourceBirthPolicyController.decodeIngress bytes).isSome ||
      (Minidregg.Kernel.ResourceBirthPolicyController.Concrete.decodeIngress bytes).isSome
  | .install bytes => (Minidregg.Kernel.PolicyInstallReceiver.decodeIngress bytes).isSome
  | .delegate bytes => (Minidregg.Kernel.CapabilityDelegationReceiver.decodeIngress bytes).isSome
  | .revoke bytes => (Minidregg.Kernel.CapabilityRevocationReceiver.decodeIngress bytes).isSome
  | .renounce bytes => (Minidregg.Kernel.CapabilityRenounce.decodeIngress bytes).isSome

/-- The resident client retains NativeHostCodec.SignedCall in call.bin.
Historical source records retain the inner signed ingress; ordinary invocation
adds only this deployment's fixed domain/profile using the existing native
codec. This is decoding, not admission: propose still calls deriveVerified. -/
def sourceIngressOfCall (config : SourceConfig) (callBytes : Bytes) : Except String Bytes := do
  let some call := Minidregg.Compiler.NativeHostCodec.callCodec.decode callBytes
    | throw "unsupported or noncanonical native signed call"
  unless Minidregg.Compiler.NativeHostCodec.callCodec.encode call == callBytes do
    throw "noncanonical native signed call"
  unless sourceCallShape call do
    throw "native signed call tag does not match its ingress"
  match call with
  | .invoke signed =>
    pure (Minidregg.Kernel.DeclaredResourceController.signedBytes
      config.deployment.domain config.profile.semantics signed)
  | .birth bytes | .install bytes | .delegate bytes | .revoke bytes | .renounce bytes =>
    pure bytes

/-- Ordinary ingress is admitted at the actual verified source tip to obtain
the exact complete record proposal. It is only queued, never physically appended
here. The historical validator independently validates any later chosen parent. -/
def propose {config : SourceConfig} (p : Participant config) (signedIngress : Bytes) :
    IO (Participant config × Except String Bytes) := do
  match ← Minidregg.Kernel.NativeHostReplay.deriveVerified p.source.verified signedIngress with
  | .error detail => return (p,.error detail)
  | .ok derived =>
    let payload := Minidregg.Compiler.DurableCheckpointCodec.recordFrame.encode
      (Minidregg.Kernel.DurableReceiver.IntentRecord.ofIntent derived.intent)
    let prior ← (storage p.runtime.native).read
    match ← persist (storage p.runtime.native) p.runtime.context prior (.offer payload) with
    | .durable state =>
      return ({p with pending :=
        Minidregg.Compiler.GenericSimplexPending.discover state p.pending},.ok payload)
    | .invalid => return (p,.error "invalid engine journal")
    | .conflict => return (p,.error "engine journal changed; retry admission")
    | .uncertain => return (p,.error "engine append uncertain; recover journal before retry")

/-- Preserve the existing live submit-only synchronous execution bound.
Historical replay and recovery deliberately do not apply today's local bound to
an older admitted call. This is not a substitute for source admission. -/
def checkLocalCall (config : SourceConfig) (callBytes : Bytes) : Except String Unit := do
  let some call := Minidregg.Compiler.NativeHostCodec.callCodec.decode callBytes
    | throw "unsupported or noncanonical native signed call"
  match call with
  | .invoke signed =>
    let some command := Minidregg.Kernel.DeclaredResourceController.commandCodec.decode signed.commandBytes
      | throw "noncanonical invocation command"
    -- Same live-submit criterion as NativeHost.overSyncBudget. Keep the
    -- historical receiver independent of the full command-line Host closure.
    if let some claim := command.run then
      if config.nockFSync < claim.steps then
        throw s!"overSyncBudget: run claim of {claim.steps} Lean steps exceeds the operator's synchronous budget nockFSync {config.nockFSync}"
    pure ()
  | _ => pure ()

def proposeCall {config : SourceConfig} (p : Participant config) (callBytes : Bytes) :
    IO (Participant config × Except String Bytes) := do
  match checkLocalCall config callBytes with
  | .error detail => return (p,.error detail)
  | .ok () => pure ()
  match sourceIngressOfCall config callBytes with
  | .error detail => return (p,.error detail)
  | .ok ingress => propose p ingress

/-- Ordinary propose/await consumer: return only the receipt recomputed by the
native verified source history for the exact complete proposal bytes. A protocol
commit, send, pending offer or local transport acknowledgement yields nothing. -/
def completedReceipt {config : SourceConfig} (p : Participant config) (payload : Bytes) :
    Option Minidregg.Compiler.NativeHostCodec.Receipt := do
  let index ← (Minidregg.Kernel.JointReceiver.sourcePrefix
    p.source.verified.opened.durable).zipIdx.findSome? (fun (record,index) =>
      if record == payload then some index else none)
  p.source.verified.receipts[index]?

/-- Lost submit responses can be recovered from the exact original signed
ingress, even when the caller never received the derived proposal bytes. -/
def completedIngress {config : SourceConfig} (p : Participant config) (signedIngress : Bytes) :
    Option Minidregg.Compiler.NativeHostCodec.Receipt := do
  let index ← p.source.verified.opened.durable.image.accepted.zipIdx.findSome?
    (fun (record,index) => if record.event.canonicalBytes == signedIngress then some index else none)
  p.source.verified.receipts[index]?

def completedCall {config : SourceConfig} (p : Participant config) (callBytes : Bytes) :
    Option Minidregg.Compiler.NativeHostCodec.Receipt := do
  let ingress ← (sourceIngressOfCall config callBytes).toOption
  completedIngress p ingress

/-- One flat fanout slot. Skipping self also consumes a slot, keeping service
finite independently of committee size. -/
def packetAt {config : SourceConfig} (p : Participant config) (state : State)
    (slot : Nat) : IO (Option (Nat × Bytes)) := do
  let parties := p.runtime.context.config.parties
  if parties == 0 then return none
  let recipient := slot % parties
  if recipient == state.self then return none
  let index := slot / parties
  let some message := state.outbox[index]? | return none
  let packet ← sealPacket p.runtime.native ⟨p.runtime.context,recipient,index,message⟩
  return some (recipient,protocolFrame packet)

/-- Fresh and retry work have independent positive service budgets. A retry
round finishes its old snapshot before including later messages. No send removes
a durable obligation or treats a lost reply as semantic failure. -/
def outgoing {config : SourceConfig} (p : Participant config) (freshBudget retryBudget : Nat) :
    IO (Participant config × List (Nat × Bytes)) := do
  let some (_,state) := restore p.runtime.context (← (storage p.runtime.native).read)
    | return (p,[])
  let total := state.outbox.length * p.runtime.context.config.parties
  let mut schedule := p.schedule
  let mut packets := []
  for _ in List.range freshBudget do
    if schedule.fresh < total then
      if let some packet ← packetAt p state schedule.fresh then
        packets := packets ++ [packet]
      schedule := {schedule with fresh := schedule.fresh + 1}
  if schedule.retry ≥ schedule.retryEnd then
    schedule := {schedule with retry := 0,retryEnd := total}
  for _ in List.range retryBudget do
    if schedule.retry < schedule.retryEnd then
      if let some packet ← packetAt p state schedule.retry then
        packets := packets ++ [packet]
      schedule := {schedule with retry := schedule.retry + 1}
  return ({p with schedule := schedule},packets)

/-- A certificate scan round also freezes its finite candidates. Received
witnesses are durable; a crash only restarts the scan. -/
def certificateCandidates (journal : Journal) (state : State) : List (Nat × Block) :=
  ((state.views.filterMap fun view => view.sentCommit.map (fun block => (view.number,block))) ++
    journal.commitWitnesses.map (fun w => (w.view,w.block))).eraseDups

/-- Recover the actual authoritative source after a lost append reply or CAS
conflict. Every retained ingress is re-admitted at its original prefix; no engine
flag or stale in-memory Source is promoted into a readback receipt. -/
def reloadSource {config : SourceConfig} (p : Participant config) :
    IO (Participant config × String) := do
  match ← Minidregg.Compiler.DurableReceiverIO.load config.physicalTransport
      Minidregg.Compiler.ResourceBirthCodec.rootBytes with
  | .error detail => return (p,"source reload: " ++ detail)
  | .ok target =>
    match ← Minidregg.Kernel.NativeHostReplay.verifyLoaded config target with
    | .error failure => return (p,"source replay: " ++ failure.detail)
    | .ok verified => return ({p with source := ⟨target,verified⟩},"source reloaded and verified")

/-- A descendant certificate installs only the next actual record, by fresh
native derivation and the existing ordered physical CAS/readback receiver. The
same full certificate can then catch up another record in a later service slice.
Return "applied" only after the receiver's opaque Applied token exists. -/
def applyNext {config : SourceConfig} (p : Participant config)
    (certificate : VerifiedCommit p.runtime.context) : IO (Participant config × String) := do
  let records := applicationHistory certificate.block
  let index := p.source.verified.opened.durable.image.accepted.length
  let some bytes := records[index]? | return (p,"source already caught up")
  let some record := Minidregg.Compiler.DurableCheckpointCodec.recordFrame.decode bytes
    | return (p,"certificate payload is not a source record")
  if Minidregg.Compiler.DurableCheckpointCodec.recordFrame.encode record != bytes then
    return (p,"noncanonical source record")
  match ← Minidregg.Kernel.JointOrderedSourceReceiver.apply
      p.source.verified p.runtime.context certificate record.event.canonicalBytes with
  | .applied receipt =>
    let verified := receipt.verified
    return ({p with source := ⟨_,verified⟩},"applied")
  | .refused detail => return (p,detail)
  | .ordinary _ => reloadSource p

def certificateSlice {config : SourceConfig} (p : Participant config) :
    IO (Participant config × List (Nat × Bytes) × String) := do
  let some (journal,state) := restore p.runtime.context (← (storage p.runtime.native).read)
    | return (p,[],"invalid engine journal")
  let queue := if p.schedule.certificates.isEmpty then certificateCandidates journal state
    else p.schedule.certificates
  let (view,block)::rest := queue | return (p,[],"no certificate work")
  let p := {p with schedule := {p.schedule with certificates := rest}}
  let some certificate ← recoverCommitment (storage p.runtime.native) (crypto p.runtime.native)
      p.runtime.context view block | return (p,[],"waiting for COMMIT witnesses")
  let packets := ((List.range p.runtime.context.config.parties).filter (· != journal.self)).map
    (fun recipient => (recipient,certificateFrame certificate.bytes))
  let (next,status) ← applyNext p certificate
  return (next,packets,status)

/-- A finite host service call. The host supplies due arrivals before this call.
It consumes reserved validation, continuation, fresh, retry and certificate
opportunities separately. Fair repeated positive slices plus available native
historical validation are progress premises; this API does not invent funding.
Ordinary callers await exact source receipt, never an engine-local flag. -/
def service {config : SourceConfig} (p : Participant config)
    (validationBudget freshBudget retryBudget : Nat) :
    IO (Participant config × List (Nat × Bytes) × List GenericSimplexController.Outcome × String) := do
  let (pending,checks) ← GenericSimplexController.service p.runtime config p.source.verified.origin
    validationBudget p.pending
  let p := {p with pending := pending}
  let _ ← GenericSimplexNative.poll p.runtime
  let _ ← GenericSimplexNative.tick p.runtime
  let (p,packets) ← outgoing p freshBudget retryBudget
  let (p,certificates,status) ← certificateSlice p
  return (p,packets ++ certificates,checks,status)

theorem invocation_call_preserves_signed (config : SourceConfig)
    (signed : Minidregg.Kernel.DeclaredResourceController.SignedCommand) :
    sourceIngressOfCall config (Minidregg.Compiler.NativeHostCodec.callCodec.encode (.invoke signed)) =
      .ok (Minidregg.Kernel.DeclaredResourceController.signedBytes
        config.deployment.domain config.profile.semantics signed) := by
  simp [sourceIngressOfCall,sourceCallShape] <;> rfl

theorem birth_call_preserves_ingress (config : SourceConfig) (bytes : Bytes)
    (valid : sourceCallShape (.birth bytes) = true) :
    sourceIngressOfCall config (Minidregg.Compiler.NativeHostCodec.callCodec.encode (.birth bytes)) =
      .ok bytes := by
  simp [sourceIngressOfCall,valid] <;> rfl

theorem mismatched_call_refused (config : SourceConfig)
    (call : Minidregg.Compiler.NativeHostCodec.SignedCall)
    (mismatch : sourceCallShape call = false) :
    sourceIngressOfCall config (Minidregg.Compiler.NativeHostCodec.callCodec.encode call) =
      .error "native signed call tag does not match its ingress" := by
  simp [sourceIngressOfCall,mismatch] <;> rfl

#assert_axioms mismatched_call_refused
#assert_axioms invocation_call_preserves_signed
#assert_axioms birth_call_preserves_ingress
end Minidregg.Compiler.GenericSimplexParticipant
