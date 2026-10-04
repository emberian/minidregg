import Compiler.GenericSimplexParticipant

/-!
Standing replica service. Each replica is its own long-lived process: it
receives authenticated packets over persistent connections, journals them,
runs one finite service slice on a fixed tick, and sends over persistent
connections. Engines never depend on a client being connected: a client only
places a request (propose, or watch) in a replica's owner-private spool and
awaits every replica's exact source receipt. A client deadline is uncertainty
for that client; it never stops, signals or resets an engine.
-/
namespace Minidregg.Compiler.GenericSimplexServe
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.GenericSimplexNative
open Minidregg.Compiler.GenericSimplexParticipant
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

/-- Finite reserved capacity for one iteration. The fresh budget is large enough
to drain every newly emitted message; retry rounds resend the whole retained
outbox over successive iterations. -/
structure Budget where
  validation : Nat := 1
  fresh : Nat := 4096
  retry : Nat := 64
  inbound : Nat := 512
  deriving Repr, Inhabited

structure IterationReport where
  received : Nat := 0
  refused : Nat := 0
  sent : Nat := 0
  status : String := ""
  deriving Repr, Inhabited

/-- One replica iteration, shared by the standing loop and the in-process
four-replica harness: authenticate and journal each delivered packet, then one
finite service slice. A packet that fails authentication is dropped (a Byzantine
peer can send anything); a journal conflict or uncertain append stops the
replica, which recovers only by reopening its durable image. -/
def iteration {config : SourceConfig} (p : Participant config) (inbound : List Bytes)
    (budget : Budget) : IO (Participant config × List (Nat × Bytes) × IterationReport) := do
  let mut p := p
  let mut refused := 0
  for packet in inbound do
    let (next,result) ← GenericSimplexParticipant.receive p packet
    p := next
    match result with
    | .durable _ => pure ()
    | .invalid => refused := refused + 1
    | .conflict => throw (IO.userError "agreement journal conflict: reopen the replica")
    | .uncertain => throw (IO.userError "agreement journal append uncertain: reopen the replica")
  let (serviced,packets,_,status) ← service p budget.validation budget.fresh budget.retry
  return (serviced,packets,{received := inbound.length,refused := refused,sent := packets.length,status := status})

/-! ## Request spool -/

def requestDirectory (replica : System.FilePath) : System.FilePath := replica / "requests"

/-- Exact receipt file: native receipt bytes, the complete source prefix through
the call, and whether the call was already installed when first requested. -/
def receiptFileStream : StreamCodec (Bytes × List Bytes × Bool) :=
  StreamCodec.product bytesStream (StreamCodec.product (StreamCodec.list bytesStream) StreamCodec.bool)

def prefixThrough {config : SourceConfig} (p : Participant config) (ingress : Bytes) :
    Option (List Bytes) := do
  let records := p.source.verified.opened.durable.image.accepted
  let index ← records.findIdx? (fun record => record.event.canonicalBytes == ingress)
  return (records.take (index + 1)).map Minidregg.Compiler.DurableCheckpointCodec.recordFrame.encode

/-- The exact source record for this ingress is already offered in this
replica's durable engine state: pending work, never a receipt. -/
def retainedOffer {config : SourceConfig} (p : Participant config) (ingress : Bytes) : IO Bool := do
  let some prior ← p.runtime.current | return false
  return prior.state.offers.any fun payload =>
    match Minidregg.Compiler.DurableCheckpointCodec.recordFrame.decode payload with
    | some record => Minidregg.Compiler.DurableCheckpointCodec.recordFrame.encode record == payload &&
        record.event.canonicalBytes == ingress
    | none => false

def writeAtomic (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let temporary := path.withExtension "partial"
  writePrivate temporary bytes
  IO.FS.rename temporary path

structure SpoolEntry where
  id : String
  firstSeenInstalled : Option Bool := none
  lastProposalMs : Option Nat := none
  done : Bool := false
  deriving Inhabited

/-- Serve one request. A `.call` request may propose (once per `retryMs` while
not installed and not already offered); a `.watch` request only reports.
Proposal is ordinary source admission at this replica's verified tip. -/
def serveRequest {config : SourceConfig} (p : Participant config) (directory : System.FilePath)
    (entry : SpoolEntry) (propose : Bool) (call : Bytes) (retryMs : Nat) :
    IO (Participant config × SpoolEntry) := do
  match sourceIngressOfCall config call with
  | .error detail =>
    IO.eprintln s!"serve: request {entry.id} is not a native signed call: {detail}"
    return (p,{entry with done := true})
  | .ok ingress =>
    match completedCall p call with
    | some receipt =>
      let installedBefore := entry.firstSeenInstalled.getD true
      let some prefixRecords := prefixThrough p ingress | return (p,entry)
      writeAtomic (directory / (entry.id ++ ".receipt"))
        (receiptFileStream.encode (Minidregg.Compiler.NativeHostCodec.receiptStream.encode receipt,
          prefixRecords,installedBefore)).toByteArray
      return (p,{entry with firstSeenInstalled := some installedBefore,done := true})
    | none =>
      let entry := {entry with firstSeenInstalled := some (entry.firstSeenInstalled.getD false)}
      unless propose do return (p,entry)
      let now ← IO.monoMsNow
      let due := match entry.lastProposalMs with
        | none => true
        | some last => now ≥ last + retryMs
      unless due do return (p,entry)
      let entry := {entry with lastProposalMs := some now}
      if ← retainedOffer p ingress then return (p,entry)
      let (next,result) ← proposeCall p call
      match result with
      | .ok _ => IO.eprintln s!"serve: proposed {entry.id}"
      | .error detail => IO.eprintln s!"serve: proposal {entry.id} not admitted now: {detail}"
      return (next,entry)

/-- Serve every pending request in the spool. -/
def serviceRequests {config : SourceConfig} (p : Participant config)
    (directory : System.FilePath) (entries : List SpoolEntry) (retryMs : Nat) :
    IO (Participant config × List SpoolEntry) := do
  unless ← directory.pathExists do return (p,entries)
  let mut p := p
  let mut entries := entries
  for item in ← directory.readDir do
    let name := item.fileName
    let propose := name.endsWith ".call"
    unless propose || name.endsWith ".watch" do continue
    let id := (name.toList.take (name.length - if propose then 5 else 6)).asString
    let entry := (entries.find? (·.id == id)).getD {id := id}
    if entry.done then continue
    let call := (← IO.FS.readBinFile item.path).toList
    let (next,updated) ← serveRequest p directory entry propose call retryMs
    p := next
    entries := entries.filter (·.id != id) ++ [updated]
  return (p,entries)

/-- The standing per-replica loop. Never returns; supervision restarts it. -/
partial def serveLoop {config : SourceConfig} (p : Participant config) (spool : System.FilePath)
    (budget : Budget) (tickMs retryMs : Nat) (entries : List SpoolEntry) : IO Unit := do
  let helper := p.runtime.native.helper
  let inbound ← helper.receive budget.inbound
  let (p,packets,report) ← iteration p inbound budget
  for (recipient,packet) in packets do
    helper.send recipient packet
  let (p,entries) ← serviceRequests p spool entries retryMs
  if report.refused > 0 then
    IO.eprintln s!"serve: dropped {report.refused} unauthenticated packets"
  if inbound.isEmpty then IO.sleep tickMs.toUInt32
  serveLoop p spool budget tickMs retryMs entries

/-! ## Client: propose and await -/

inductive Awaited where
  | confirmed (kind : Minidregg.Compiler.DurableReceiverIO.Confirmation)
      (receipt : Minidregg.Compiler.NativeHostCodec.Receipt)
  | uncertain

def placeRequest (directory : System.FilePath) (name : String) (call : Bytes) : IO Unit := do
  IO.FS.createDirAll directory
  let path := directory / name
  if ← path.pathExists then
    if (← IO.FS.readBinFile path).toList != call then
      throw (IO.userError "request id already names a different call")
    return
  writeAtomic path call.toByteArray

/-- Place the exact original call at the proposer and a watch at every other
replica, then wait for all exact receipts and prefixes to agree. The deadline
returns `uncertain`; requests remain and engines keep serving them. -/
def awaitCall (replicas : List System.FilePath) (proposer : Nat) (id : String) (call : Bytes)
    (deadlineMs : Nat) : IO Awaited := do
  for (replica,index) in replicas.zipIdx do
    placeRequest (requestDirectory replica) (id ++ if index == proposer then ".call" else ".watch") call
  let stop := (← IO.monoMsNow) + deadlineMs
  repeat
    let mut found := []
    for replica in replicas do
      let path := requestDirectory replica / (id ++ ".receipt")
      if ← path.pathExists then
        if let some decoded := receiptFileStream.toLawful.decode (← IO.FS.readBinFile path).toList then
          found := found ++ [decoded]
    if found.length == replicas.length then
      let some (receiptBytes,prefixRecords,_) := found.head? | return .uncertain
      unless found.all (fun (r,q,_) => r == receiptBytes && q == prefixRecords) do
        throw (IO.userError "replicas disagree on the exact receipt or source prefix")
      let some (_,_,before) := found[proposer]? | return .uncertain
      let some receipt := Minidregg.Compiler.NativeHostCodec.receiptStream.toLawful.decode receiptBytes
        | throw (IO.userError "noncanonical replica receipt")
      return .confirmed (if before then .replayed else .installed) receipt
    if (← IO.monoMsNow) ≥ stop then return .uncertain
    IO.sleep 200
  return .uncertain

end Minidregg.Compiler.GenericSimplexServe
