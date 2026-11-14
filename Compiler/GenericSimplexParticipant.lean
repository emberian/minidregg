module

public import Compiler.GenericSimplexController
public import Kernel.JointOrderedSourceReceiver
public import Theory.AssertAxioms

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic
import all Init.System.ST
import all Init.System.IO

@[expose] public section

namespace Minidregg.Compiler.GenericSimplexParticipant
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.GenericSimplexNative
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
set_option autoImplicit false

abbrev SourceConfig := Minidregg.Kernel.NativeHost.Config
abbrev Durable := Minidregg.Kernel.NativeHost.Durable
abbrev Verified := Minidregg.Kernel.NativeHostReplay.Verified
abbrev Pending := Minidregg.Compiler.GenericSimplexPending.Queue

/-- Only native replay can construct the verified source component. -/
structure Source (config : SourceConfig) where
  target : Durable
  verified : Verified config target

/-- Volatile scheduling state. Restart may reset all of it: the journal keeps the replica's
undrained output and its committed payloads the application has not taken. -/
structure Schedule where
  /-- How many of the replica's broadcasts and owed messages the last slice handed to its
  caller for sending. The next slice acknowledges exactly these in the journal
  (`Entry.flush`), so an output is durable before it is sent and is sent again after a
  crash that lost the acknowledgement. -/
  sent : Nat := 0
  owed : Nat := 0
  /-- Last application-candidate relay per recipient: (recipient, height, ms). -/
  candidateSent : List (Nat × Nat × Nat) := []

/-- Resend interval for the same unvalidated candidate to the same peer. A changed
candidate height is relayed at once. -/
def candidateResendMs : Nat := 5000

structure Participant (config : SourceConfig) where
  runtime : Runtime
  source : Source config
  pending : Pending := {}
  schedule : Schedule := {}

/-- The first octet of a frame distinguishes authenticated protocol traffic from
application-candidate dissemination. -/
def protocolFrame (bytes : ByteArray) : ByteArray := ByteArray.mk #[0] ++ bytes
def candidateFrame (bytes : ByteArray) : ByteArray := ByteArray.mk #[2] ++ bytes

/-- Opening checks the exact configured source genesis against the consensus
anchor through the real historical validator. A journal alone cannot select the
source seed or committee. Whatever output the replica had not acknowledged as sent is sent
by the first slice; nothing else is resent, and a peer that missed a message asks by
repeating its CANDIDATE(⊥). -/
def openParticipant (config : SourceConfig) (runtime : Runtime)
    (source : Source config) : IO (Except String (Participant config)) := do
  let expected := runtime.context
  match ← Minidregg.Kernel.JointSourcePrefixValidation.validate config
      source.verified.origin expected [] with
  | .accepted _ =>
    let some prior ← runtime.current
      | return .error "invalid durable agreement journal"
    return .ok ⟨runtime,source,
      Minidregg.Compiler.GenericSimplexPending.discover prior.state {},{}⟩
  | .rejected detail => return .error detail
  | .retry failure => return .error failure.detail

/-- The blocks carried by the newest journal delta's deliveries, as this replica reads them
now (the payloads above its committed height): exactly what the just-acknowledged packet
added to its observed set. -/
def latestObserved {context : Context} (r : Restored context) : List Block :=
  match r.log.recent with
  | d :: _ => d.events.filterMap fun e =>
      match decodeEntry e with
      | some (.input (.delivery m)) => m.value.bind (above m.height r.state.height)
      | some (.input (.deliveryAt _ m)) => m.value.bind (above m.height r.state.height)
      | _ => none
  | [] => []

/-- Every ingress is durably authenticated before it enters the engine, and discovery
then schedules source validation; no path here grants a checked input itself. -/
def receive {config : SourceConfig} (p : Participant config) (bytes : ByteArray) :
    IO (Participant config × GenericSimplexIO.Result) := do
  if bytes.size == 0 then return (p,.invalid)
  let payload := bytes.extract 1 bytes.size
  if bytes.get! 0 == 2 then
    let (result,candidate) ← GenericSimplexNative.receiveCandidate p.runtime payload
    match result,candidate with
    | .durable state,some (height,records) =>
      return ({p with pending :=
        Minidregg.Compiler.GenericSimplexPending.discoverFrom state [] p.pending [⟨height,records⟩]},result)
    | _,_ => return (p,result)
  if bytes.get! 0 != 0 then return (p,.invalid)
  let before := (← p.runtime.current).map (·.length)
  let result ← GenericSimplexNative.receive p.runtime payload
  match result with
  | .durable state =>
    -- A settled delivery appends nothing (the journal length is unchanged) and leaves the
    -- replica as it was, so there is nothing new to discover.
    let some now ← p.runtime.current | return (p,result)
    if some now.length == before then return (p,result)
    return ({p with pending :=
      Minidregg.Compiler.GenericSimplexPending.discoverFrom state (latestObserved now) p.pending},result)
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
    match ← persist (storage p.runtime.native) p.runtime.context (.input (.offer payload)) with
    | .durable state =>
      return ({p with pending :=
        Minidregg.Compiler.GenericSimplexPending.discoverFrom state [] p.pending},.ok payload)
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

/-- The replica's output since the last acknowledged drain, sealed: every broadcast to every
other member, every owed message to the member it is owed to. The previous slice's packets
are acknowledged first (`Entry.flush` with their counts), so the journal never drops an
output this participant has not handed to its transport. Nothing is resent on a timer: the
kernel answers a member that repeats its CANDIDATE(⊥) with what it is owed. -/
def outgoing {config : SourceConfig} (p : Participant config) :
    IO (Participant config × List (Nat × ByteArray)) := do
  let context := p.runtime.context
  if p.schedule.sent > 0 || p.schedule.owed > 0 then
    match ← persist (storage p.runtime.native) context (.flush p.schedule.sent p.schedule.owed) with
    | .durable _ => pure ()
    | _ => return (p,[])
  let p := {p with schedule := {p.schedule with sent := 0, owed := 0}}
  let some prior ← p.runtime.current | return (p,[])
  let replica := prior.state
  let self := prior.self
  let mut packets := []
  for message in replica.sends do
    if let some proof ← messageProof p.runtime.native context message then
      for recipient in List.range context.config.parties do
        if recipient != self then
          packets := (recipient,protocolFrame
            (← sealPacket p.runtime.native ⟨context,self,recipient,message⟩ proof)) :: packets
  for (recipient,message) in replica.owed do
    if recipient != self && recipient < context.config.parties then
      if let some proof ← messageProof p.runtime.native context message then
        packets := (recipient,protocolFrame
          (← sealPacket p.runtime.native ⟨context,self,recipient,message⟩ proof)) :: packets
  return ({p with schedule := {p.schedule with sent := replica.sends.length, owed := replica.owed.length}},
    packets.reverse)

/-- Recover the actual authoritative source after a lost append reply or CAS
conflict. The retained source is a `Verified` minted by native replay; the
physical readback must extend it (`extendFrom`: the log chain continues from the
retained one and every new tag verifies, so a rollback or a rewritten record
refuses), and every new
retained ingress is re-admitted at its original prefix. No engine flag or stale
in-memory Source is promoted into a readback receipt. A genesis re-admission of
the whole history is the operator `audit`, not a per-certificate cost. -/
def reloadSource {config : SourceConfig} (p : Participant config) :
    IO (Participant config × String) := do
  -- Only the entries after the retained source are read (`extendFrom`: the chain continues
  -- from it and every new tag verifies), and its append proof extends the retained proof
  -- (`extendVerifiedAppended`): no full reload, no re-encoding of the whole prefix (law 17).
  match ← Minidregg.Compiler.DurableReceiverIO.extendFrom config.physicalTransport
      Minidregg.Compiler.ResourceBirthCodec.rootBytes p.source.target with
  | .error detail => return (p,"source reload: " ++ detail)
  | .ok ⟨target, seedExact, acceptedExact, _⟩ =>
    -- The extension's history reads go through the Reader of the Store just read
    -- (its MAC-bound head); an unavailable Reader is reported, never read as absent.
    match ← Minidregg.Compiler.DurableHistoryStore.readerOf config.physicalTransport
        Minidregg.Compiler.ResourceBirthCodec.rootBytes target with
    | .error detail => return (p,"source history reader: " ++ detail)
    | .ok ⟨_, reader⟩ =>
    match ← Minidregg.Kernel.NativeHostReplay.extendVerifiedAppended config reader p.source.verified
        target seedExact acceptedExact with
    | .error failure => return (p,"source replay: " ++ failure.detail)
    | .ok verified => return ({p with source := ⟨target,verified⟩},"source reloaded and verified")

/-- Hand the application the next committed payload the replica keeps for it. An empty
protocol payload is taken at once. A source record is installed by fresh native derivation
and the existing ordered physical CAS/readback receiver, under the certificate of the
replica's newest commit: its signed digest must be that of the source prefix, this record
and the committed records after it (`JointReceiver.order`). Only then is the payload
acknowledged (`Entry.consume`), so a crash in between hands it over again and the record
already in the source is recognised by its position. Return "applied" only after the
receiver's opaque Applied token exists. -/
def applyNext {config : SourceConfig} (p : Participant config) : IO (Participant config × String) := do
  let context := p.runtime.context
  let some prior ← p.runtime.current | return (p,"invalid engine journal")
  let replica := prior.state
  let payload :: later := replica.committed | return (p,"no committed work")
  let taken (p : Participant config) (status : String) : IO (Participant config × String) := do
    match ← persist (storage p.runtime.native) context (.consume 1) with
    | .durable _ => return (p,status)
    | _ => return (p,"engine journal refused the application's acknowledgement")
  if payload.isEmpty then return ← taken p "protocol payload"
  let index := replica.records - (applicationHistory replica.committed).length
  let height := p.source.verified.opened.durable.height
  if index < height then
    let held := p.source.verified.opened.durable.image.accepted[index]?.map
      Minidregg.Compiler.DurableCheckpointCodec.recordFrame.encode
    if held == some payload then return ← taken p "source already holds the record"
    return (p,"the source's record at this height is not the committed one")
  if height < index then return (p,"the source is behind the committed records")
  let some record := Minidregg.Compiler.DurableCheckpointCodec.recordFrame.decode payload
    | return (p,"committed payload is not a source record")
  let some certificate ← recoverCommitment (storage p.runtime.native) (crypto p.runtime.native) context
    | return (p,"waiting for COMMIT witnesses")
  match ← Minidregg.Kernel.JointOrderedSourceReceiver.apply
      p.source.verified context certificate (applicationHistory later) record.event.canonicalBytes with
  | .applied receipt =>
    let verified := receipt.verified
    taken {p with source := ⟨_,verified⟩} "applied"
  | .refused detail => return (p,detail)
  | .ordinary _ => reloadSource p
  | .uncertain _ => reloadSource p

/-- Disseminate a checked source history before its owner's next leader turn: the records
this replica has checked above its committed ones. Each peer independently rechecks it; a
MAC never transfers source authority. The same candidate goes to the same peer at most once
per `candidateResendMs`; a longer candidate is relayed at once. The relay is availability,
not delivery: a peer that lost it is served again after the interval. -/
def candidateSlice {config : SourceConfig} (p : Participant config) :
    IO (Participant config × List (Nat × ByteArray)) := do
  let some prior ← p.runtime.current | return (p,[])
  let replica := prior.state
  let some records := replica.core.checked.head? | return (p,[])
  let length := replica.records + records.length
  let now ← IO.monoMsNow
  let mut packets := []
  let mut sent := p.schedule.candidateSent
  for recipient in List.range p.runtime.context.config.parties do
    if recipient != prior.self then
      let due := match sent.find? (fun (r,_,_) => r == recipient) with
        | none => true
        | some (_,h,last) => h != length || now ≥ last + candidateResendMs
      if due then
        packets := packets ++ [(recipient,candidateFrame
          (← sealCandidate p.runtime recipient replica.records records))]
        sent := (sent.filter (fun (r,_,_) => r != recipient)) ++ [(recipient,length,now)]
  return ({p with schedule := {p.schedule with candidateSent := sent}},packets)

/-- A finite host service call. The host supplies due arrivals before this call.
It consumes reserved validation and continuation opportunities, sends the replica's whole
undrained output, and hands the application at most one committed payload. Fair repeated
positive slices plus available native historical validation are progress premises; this API
does not invent funding. Ordinary callers await exact source receipt, never an engine-local
flag. -/
def service {config : SourceConfig} (p : Participant config) (validationBudget : Nat) :
    IO (Participant config × List (Nat × ByteArray) × List GenericSimplexController.Outcome × String) := do
  let t0 ← IO.monoMsNow
  -- The committed source history, for the validator: the source's records, then the
  -- committed records the application has not taken yet. Built only when work is attempted.
  let committed : Unit → Block := fun _ =>
    Minidregg.Kernel.JointReceiver.sourcePrefix p.source.verified.opened.durable
  let committedRecords ← do
    match ← p.runtime.current with
    | some prior => pure (applicationHistory prior.state.committed)
    | none => pure []
  let (pending,checks) ← GenericSimplexController.service p.runtime config p.source.verified.origin
    (fun unit => committed unit ++ committedRecords) validationBudget p.pending
  let p := {p with pending := pending}
  let t1 ← IO.monoMsNow
  -- A standing replica serves on a fixed tick. Journal a poll only for an exhausted pump
  -- (needsPoll), and a tick only when the view's deadline is due: the kernel then asks to
  -- leave the view, or asks again a whole timeout later (the repeat a peer answers with
  -- what this replica is owed), or, with no reason to leave, moves the deadline one
  -- timeout ahead. Omitting an input is always a lawful schedule; the retained journal
  -- stays the exact input sequence replayed.
  if let some prior ← p.runtime.current then
    let core := prior.state.core
    if core.needsPoll then
      let _ ← GenericSimplexNative.poll p.runtime
    let now ← p.runtime.now
    if core.needsPoll || now ≥ core.deadline then
      let _ ← GenericSimplexNative.tick p.runtime
  let t2 ← IO.monoMsNow
  let (p,packets) ← outgoing p
  let t3 ← IO.monoMsNow
  let (p,candidates) ← candidateSlice p
  let t4 ← IO.monoMsNow
  let (p,status) ← applyNext p
  let t5 ← IO.monoMsNow
  if t5 - t0 ≥ 1000 then
    IO.eprintln s!"service ms: validation {t1-t0} ({checks.length} checks, {p.pending.pending.length} pending) clock {t2-t1} outgoing {t3-t2} ({packets.length}) candidate {t4-t3} apply {t5-t4} [{status}]"
  return (p,packets ++ candidates,checks,status)

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
