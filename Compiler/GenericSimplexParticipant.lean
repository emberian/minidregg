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
  /-- Last application-candidate relay per recipient: (recipient, height, ms). -/
  candidateSent : List (Nat × Nat × Nat) := []
  /-- Earliest monotonic ms for the next certificate repair slice. -/
  certificateDue : Nat := 0
  /-- Earliest monotonic ms for the next retry slice. -/
  retryDue : Nat := 0

/-- Resend interval for the same unvalidated candidate to the same peer, and the
pace of certificate repair. A changed candidate height is relayed at once. -/
def candidateResendMs : Nat := 5000
def certificateEveryMs : Nat := 1000
/-- Pace of the retry round over the retained outbox. Retry is availability
repair for a connection that dropped frames, not first delivery (fresh sends
go out at once); unpaced, every peer resent its whole retained outbox
continuously and each replica spent most of its time authenticating and
discarding duplicates. -/
def retryEveryMs : Nat := 1000

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
def candidateFrame (bytes : Bytes) : Bytes := frameStream.encode (2,bytes)

/-- Opening checks the exact configured source genesis against the consensus
anchor through the real historical validator. A journal alone cannot select the
source seed or committee. -/
def openParticipant (config : SourceConfig) (runtime : Runtime)
    (source : Source config) : IO (Except String (Participant config)) := do
  let expected := runtime.context
  match ← Minidregg.Kernel.JointSourcePrefixValidation.validate config
      source.verified.origin expected [] with
  | .accepted _ =>
    let some prior ← runtime.current
      | return .error "invalid durable agreement journal"
    let state := prior.state
    -- After a restart, resend as fresh every message of every view this
    -- replica has not locally decided: a COMMIT or READY for an older
    -- undecided view (the stalled view 17/18 sends) is exactly what peers may
    -- still need. Decided views are covered by certificate repair, and the
    -- independent retry round still covers the entire retained outbox. This is
    -- a scheduling hint, never an acknowledgement.
    let decided := lastCommittedView state
    let firstUndecided := (state.outbox.findIdx? (fun message =>
      decide (decided < message.view))).getD state.outbox.length
    let schedule : Schedule :=
      { fresh := firstUndecided * expected.config.parties
        retryEnd := state.outbox.length * expected.config.parties }
    return .ok ⟨runtime,source,
      Minidregg.Compiler.GenericSimplexPending.discover state {},schedule⟩
  | .rejected detail => return .error detail
  | .retry failure => return .error failure.detail

/-- Every ingress is durably authenticated before it enters the engine. A
certificate imports its original COMMIT signatures atomically, and discovery
then schedules source validation; neither path grants Input.checked itself. -/
def receive {config : SourceConfig} (p : Participant config) (bytes : Bytes) :
    IO (Participant config × GenericSimplexIO.Result) := do
  let some (tag,payload) := frameStream.toLawful.decode bytes | return (p,.invalid)
  if frameStream.encode (tag,payload) != bytes then return (p,.invalid)
  if tag == 2 then
    let (result,block) ← GenericSimplexNative.receiveCandidate p.runtime payload
    match result,block with
    | .durable state,some candidate =>
      let pending := Minidregg.Compiler.GenericSimplexPending.retry p.pending
        (applicationHistory candidate)
      return ({p with pending :=
        Minidregg.Compiler.GenericSimplexPending.discover state pending},result)
    | _,_ => return (p,result)
  let before := (← p.runtime.current).map (·.length)
  let result ← match tag with
    | 0 => GenericSimplexNative.receive p.runtime payload
    | 1 => GenericSimplexNative.receiveFinality p.runtime payload
    | _ => pure .invalid
  match result with
  | .durable state =>
    -- A retransmission already represented in the durable image appends
    -- nothing (the journal length is unchanged) and leaves the engine state as
    -- it was, so there is nothing new to discover. Peers resend their retained
    -- outboxes continuously, so this is most packets.
    if (← p.runtime.current).map (·.length) == before then return (p,result)
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
    match ← persist (storage p.runtime.native) p.runtime.context (.offer payload) with
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
round finishes its old snapshot before including later messages; one retry slice
runs at most once per `retryEveryMs`. No send removes a durable obligation or
treats a lost reply as semantic failure. -/
def outgoing {config : SourceConfig} (p : Participant config) (freshBudget retryBudget : Nat) :
    IO (Participant config × List (Nat × Bytes)) := do
  let some prior ← p.runtime.current | return (p,[])
  let state := prior.state
  let total := state.outbox.length * p.runtime.context.config.parties
  let mut schedule := p.schedule
  let mut packets := []
  for _ in List.range freshBudget do
    if schedule.fresh < total then
      if let some packet ← packetAt p state schedule.fresh then
        packets := packets ++ [packet]
      schedule := {schedule with fresh := schedule.fresh + 1}
  let now ← IO.monoMsNow
  if now < schedule.retryDue then return ({p with schedule := schedule},packets)
  schedule := {schedule with retryDue := now + retryEveryMs}
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
def certificateCandidates {context : Context} (prior : Restored context) : List (Nat × Block) :=
  ((prior.state.views.filterMap fun view => view.sentCommit.map (fun block => (view.number,block))) ++
    prior.witnesses.map (fun w => (w.view,w.block))).eraseDups

/-- Recover the actual authoritative source after a lost append reply or CAS
conflict. The retained source is a `Verified` minted by native replay; the
physical readback must extend it byte for byte (seed and every prior record:
`extendVerified` refuses rollback or any rewritten record), and every new
retained ingress is re-admitted at its original prefix. No engine flag or stale
in-memory Source is promoted into a readback receipt. A genesis re-admission of
the whole history is the operator `audit`, not a per-certificate cost. -/
def reloadSource {config : SourceConfig} (p : Participant config) :
    IO (Participant config × String) := do
  match ← Minidregg.Compiler.DurableReceiverIO.load config.physicalTransport
      Minidregg.Compiler.ResourceBirthCodec.rootBytes with
  | .error detail => return (p,"source reload: " ++ detail)
  | .ok target =>
    match ← Minidregg.Kernel.NativeHostReplay.extendVerified config p.source.verified target with
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
  let now ← IO.monoMsNow
  if now < p.schedule.certificateDue then return (p,[],"certificate repair paced")
  let p := {p with schedule := {p.schedule with certificateDue := now + certificateEveryMs}}
  let some prior ← p.runtime.current | return (p,[],"invalid engine journal")
  let queue := if p.schedule.certificates.isEmpty then certificateCandidates prior
    else p.schedule.certificates
  let (view,block)::rest := queue | return (p,[],"no certificate work")
  let p := {p with schedule := {p.schedule with certificates := rest}}
  let some certificate ← recoverCommitment (storage p.runtime.native) (crypto p.runtime.native)
      p.runtime.context view block | return (p,[],"waiting for COMMIT witnesses")
  let packets := ((List.range p.runtime.context.config.parties).filter (· != prior.self)).map
    (fun recipient => (recipient,certificateFrame certificate.bytes))
  let (next,status) ← applyNext p certificate
  return (next,packets,status)

/-- Disseminate a complete checked source candidate before its owner's next
leader turn. Each peer independently rechecks it; a MAC never transfers source
authority. Already installed local prefixes need no offer relay: their original
COMMIT certificates continue through the separate positive repair budget. The
same candidate goes to the same peer at most once per `candidateResendMs`; a
longer candidate is relayed at once. The relay is availability, not delivery:
a peer that lost it is served again after the interval. -/
def candidateSlice {config : SourceConfig} (p : Participant config) :
    IO (Participant config × List (Nat × Bytes)) := do
  let some prior ← p.runtime.current | return (p,[])
  let state := prior.state
  let height := p.source.verified.opened.durable.image.accepted.length
  let some block := state.checked.find? (fun block => height < (applicationHistory block).length)
    | return (p,[])
  let length := (applicationHistory block).length
  let now ← IO.monoMsNow
  let mut packets := []
  let mut sent := p.schedule.candidateSent
  for recipient in List.range p.runtime.context.config.parties do
    if recipient != state.self then
      let due := match sent.find? (fun (r,_,_) => r == recipient) with
        | none => true
        | some (_,h,last) => h != length || now ≥ last + candidateResendMs
      if due then
        packets := packets ++ [(recipient,candidateFrame (← sealCandidate p.runtime recipient block))]
        sent := (sent.filter (fun (r,_,_) => r != recipient)) ++ [(recipient,length,now)]
  return ({p with schedule := {p.schedule with candidateSent := sent}},packets)

/-- A finite host service call. The host supplies due arrivals before this call.
It consumes reserved validation, continuation, fresh, retry and certificate
opportunities separately. Fair repeated positive slices plus available native
historical validation are progress premises; this API does not invent funding.
Ordinary callers await exact source receipt, never an engine-local flag. -/
def service {config : SourceConfig} (p : Participant config)
    (validationBudget freshBudget retryBudget : Nat) :
    IO (Participant config × List (Nat × Bytes) × List GenericSimplexController.Outcome × String) := do
  let t0 ← IO.monoMsNow
  let (pending,checks) ← GenericSimplexController.service p.runtime config p.source.verified.origin
    validationBudget p.pending
  let p := {p with pending := pending}
  let t1 ← IO.monoMsNow
  -- A standing replica serves on a fixed tick. Journal a poll or tick only when
  -- step can act on it: an exhausted pump (needsPoll), or a due timer not yet
  -- fired. Otherwise a tick changes only the logical clock, which every
  -- deliveryAt input already advances. Omitting an input is always a lawful
  -- schedule; the retained journal stays the exact input sequence replayed.
  if let some prior ← p.runtime.current then
    let state := prior.state
    if state.needsPoll then
      let _ ← GenericSimplexNative.poll p.runtime
    let now ← p.runtime.now
    if state.needsPoll || (now ≥ state.deadline && !(viewAt state state.current).disableRequested) then
      let _ ← GenericSimplexNative.tick p.runtime
  let t2 ← IO.monoMsNow
  let (p,packets) ← outgoing p freshBudget retryBudget
  let t3 ← IO.monoMsNow
  let (p,candidates) ← candidateSlice p
  let t4 ← IO.monoMsNow
  let (p,certificates,status) ← certificateSlice p
  let t5 ← IO.monoMsNow
  if t5 - t0 ≥ 1000 then
    IO.eprintln s!"service ms: validation {t1-t0} ({checks.length} checks, {p.pending.pending.length} pending) clock {t2-t1} outgoing {t3-t2} ({packets.length}) candidate {t4-t3} certificate {t5-t4} [{status}]"
  return (p,packets ++ candidates ++ certificates,checks,status)

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
