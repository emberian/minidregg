module

public import Compiler.GenericSimplexParticipant

@[expose] public section

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

/-- Finite reserved capacity for one iteration. Every iteration sends the replica's whole
undrained output; nothing is resent on a timer. -/
structure Budget where
  validation : Nat := 1
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
def iteration {config : SourceConfig} (p : Participant config) (inbound : List ByteArray)
    (budget : Budget) : IO (Participant config × List (Nat × ByteArray) × IterationReport) := do
  let mut p := p
  let mut refused := 0
  unless inbound.isEmpty do wake p
  for packet in inbound do
    let (next,result) ← GenericSimplexParticipant.receive p packet
    p := next
    match result with
    | .durable _ => pure ()
    | .invalid => refused := refused + 1
    | .conflict => throw (IO.userError "agreement journal conflict: reopen the replica")
    | .uncertain => throw (IO.userError "agreement journal append uncertain: reopen the replica")
  let (serviced,packets,_,status) ← service p budget.validation
  return (serviced,packets,{received := inbound.length,refused := refused,sent := packets.length,status := status})

/-! ## Request spool

A client places `ID.call` (propose and report) or `ID.watch` (report only) in a replica's
`requests` directory and reads `ID.receipt` from its `receipts` directory. A served request
is removed, so the spool holds only pending requests and a slice's cost does not grow with
the requests ever served. -/

def requestDirectory (replica : System.FilePath) : System.FilePath := replica / "requests"
def receiptDirectory (replica : System.FilePath) : System.FilePath := replica / "receipts"

/-- Receipt file: the native receipt bytes, and whether the call was already installed when
first requested. The receipt carries the accepted count and the world root at the call's
height (`NativeHostCodec.Receipt`), and the root folds every accepted record, so equal
receipts are equal source prefixes through the call up to a collision of the deployed hash:
the prefix itself is not written. -/
def receiptFileStream : StreamCodec (Bytes × Bool) :=
  StreamCodec.product bytesStream StreamCodec.bool

/-- The exact source record for this ingress is already offered in this
replica's durable engine state: pending work, never a receipt. -/
def retainedOffer {config : SourceConfig} (p : Participant config) (ingress : Bytes) : IO Bool := do
  let some prior ← p.runtime.current | return false
  return prior.state.core.offers.any fun payload =>
    match Minidregg.Compiler.DurableCheckpointCodec.recordFrame.decode payload with
    | some record => Minidregg.Compiler.DurableCheckpointCodec.recordFrame.encode record == payload &&
        record.event.canonicalBytes == ingress
    | none => false

def writeAtomic (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let temporary := path.withExtension "partial"
  writePrivate temporary bytes
  IO.FS.rename temporary path

/-- A pending request, read from its file once. `searched` counts the source records
already searched for its ingress: a slice searches only the records appended since, and
nothing while the source has not grown. -/
structure SpoolEntry where
  id : String
  path : System.FilePath
  propose : Bool
  call : Bytes
  ingress : Bytes
  installedBefore : Option Bool := none
  lastProposalMs : Option Nat := none
  searched : Nat := 0
  deriving Inhabited

/-- The receipt of this ingress among the source records from `searched` on. The first
search of a request walks the whole history once (there is no index by ingress); a receipt
is read along one tree path (`Verified.receiptAt`). -/
def completedFrom {config : SourceConfig} (p : Participant config) (ingress : Bytes) (searched : Nat) :
    Option Minidregg.Compiler.NativeHostCodec.Receipt := do
  let index ← (p.source.verified.opened.durable.image.accepted.drop searched).findIdx?
    (fun record => record.event.canonicalBytes == ingress)
  p.source.verified.receiptAt (searched + index)

/-- Serve one pending request; `none` when it is served and removed. A `.call` request may
propose (once per `retryMs` while not installed and not already offered); a `.watch`
request only reports. Proposal is ordinary source admission at this replica's verified tip. -/
def serveRequest {config : SourceConfig} (p : Participant config) (receipts : System.FilePath)
    (entry : SpoolEntry) (retryMs : Nat) : IO (Participant config × Option SpoolEntry) := do
  let height := p.source.verified.opened.durable.height
  let found := if entry.installedBefore.isSome && entry.searched == height then none
    else completedFrom p entry.ingress entry.searched
  match found with
  | some receipt =>
    IO.FS.createDirAll receipts
    writeAtomic (receipts / (entry.id ++ ".receipt"))
      (receiptFileStream.encode (Minidregg.Compiler.NativeHostCodec.receiptStream.encode receipt,
        entry.installedBefore.getD true)).toByteArray
    IO.FS.removeFile entry.path
    return (p,none)
  | none =>
    let entry := {entry with installedBefore := some (entry.installedBefore.getD false), searched := height}
    unless entry.propose do return (p,some entry)
    let now ← IO.monoMsNow
    let due := match entry.lastProposalMs with
      | none => true
      | some last => now ≥ last + retryMs
    unless due do return (p,some entry)
    let entry := {entry with lastProposalMs := some now}
    if ← retainedOffer p entry.ingress then return (p,some entry)
    let (next,result) ← proposeCall p entry.call
    match result with
    | .ok _ => IO.eprintln s!"serve: {now} ms proposed {entry.id}"
    | .error detail => IO.eprintln s!"serve: proposal {entry.id} not admitted now: {detail}"
    return (next,some entry)

/-- Serve every pending request in the spool. A file that is not a native signed call is
renamed `ID.refused` and not read again. -/
def serviceRequests {config : SourceConfig} (p : Participant config)
    (replica : System.FilePath) (entries : List SpoolEntry) (retryMs : Nat) :
    IO (Participant config × List SpoolEntry) := do
  let directory := requestDirectory replica
  unless ← directory.pathExists do return (p,entries)
  let mut p := p
  let mut kept := []
  for item in ← directory.readDir do
    let name := item.fileName
    let propose := name.endsWith ".call"
    unless propose || name.endsWith ".watch" do continue
    let id := (name.toList.take (name.length - if propose then 5 else 6)).asString
    let entry ← match entries.find? (fun e => e.id == id && e.propose == propose) with
      | some entry => pure (some entry)
      | none => do
        let call := (← IO.FS.readBinFile item.path).toList
        match sourceIngressOfCall config call with
        | .ok ingress => pure (some {id := id, path := item.path, propose := propose, call := call, ingress := ingress})
        | .error detail =>
          IO.eprintln s!"serve: request {id} is not a native signed call: {detail}"
          IO.FS.rename item.path (directory / (id ++ ".refused"))
          pure none
    let some entry := entry | continue
    let (next,updated) ← serveRequest p (receiptDirectory replica) entry retryMs
    p := next
    kept := kept ++ updated.toList
  return (p,kept)

/-- One minute of serve-loop accounting, printed and reset per window. -/
structure ServeStats where
  since : Nat := 0
  packets : Nat := 0
  busyMs : Nat := 0
  iterations : Nat := 0
  /-- The last service slice's application status, printed when it changes. -/
  status : String := ""
  deriving Inhabited

def statsWindowMs : Nat := 60000

/-- The standing per-replica loop. Never returns; supervision restarts it.
Once a minute it prints a `stats:` line (packets received, receive+service
milliseconds, retained views, deltas since the last checkpoint, journal bytes)
so per-input cost can be followed over uptime. Every `checkpointEvery` deltas
it checkpoints the journal. -/
partial def serveLoop {config : SourceConfig} (p : Participant config) (replica : System.FilePath)
    (budget : Budget) (tickMs retryMs : Nat) (entries : List SpoolEntry) (stats : ServeStats := {}) :
    IO Unit := do
  let helper := p.runtime.native.helper
  let t0 ← IO.monoMsNow
  let stats := if stats.since == 0 then {stats with since := t0} else stats
  let inbound := (← helper.receive budget.inbound).toList
  let (p,packets,report) ← iteration p inbound budget
  let t1 ← IO.monoMsNow
  if let some prior ← p.runtime.current then
    if prior.deltas ≥ checkpointEvery then
      match ← checkpoint (storage p.runtime.native) p.runtime.context with
      | .durable =>
        IO.eprintln s!"serve: {← IO.monoMsNow} ms checkpoint after {prior.deltas} deltas ({prior.length} B replaced)"
      | _ => throw (IO.userError "agreement journal checkpoint refused: reopen the replica")
  for (recipient,packet) in packets do
    helper.send recipient packet
  let t2 ← IO.monoMsNow
  let (p,entries) ← serviceRequests p replica entries retryMs
  let t3 ← IO.monoMsNow
  if t3 - t0 ≥ (← slowSliceMs) then
    IO.eprintln s!"iteration ms: receive+service {t1-t0} ({inbound.length} in) send {t2-t1} ({packets.length} out) requests {t3-t2}"
  if report.refused > 0 then
    IO.eprintln s!"serve: dropped {report.refused} unauthenticated packets"
  if report.status == "applied" then
    IO.eprintln s!"serve: {← IO.monoMsNow} ms applied certified source record; height {p.source.verified.opened.durable.height}"
  else if report.status != stats.status && report.status != "no committed work" then
    IO.eprintln s!"serve: {← IO.monoMsNow} ms application: {report.status}"
  let stats : ServeStats := { stats with
    packets := stats.packets + inbound.length
    busyMs := stats.busyMs + (t1 - t0)
    iterations := stats.iterations + 1
    status := report.status }
  let stats ← if t3 - stats.since < statsWindowMs then pure stats else do
    if let some prior ← p.runtime.current then
      let perPacket := if stats.packets == 0 then 0 else stats.busyMs * 1000 / stats.packets
      IO.eprintln s!"stats: {t3} ms window {(t3 - stats.since) / 1000} s: {stats.packets} packets in {stats.iterations} iterations, receive+service {stats.busyMs} ms ({perPacket} us/packet); view {prior.state.core.current}, views {prior.state.core.views.length}, height {prior.state.height}, deltas since checkpoint {prior.deltas}, journal {prior.length} B"
    pure ({since := t3, status := stats.status} : ServeStats)
  if inbound.isEmpty then IO.sleep tickMs.toUInt32
  serveLoop p replica budget tickMs retryMs entries stats

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
replica, then wait for every replica's receipt and for them to be one receipt. The deadline
returns `uncertain`; requests remain and engines keep serving them. -/
def awaitCall (replicas : List System.FilePath) (proposer : Nat) (id : String) (call : Bytes)
    (deadlineMs : Nat) : IO Awaited := do
  for (replica,index) in replicas.zipIdx do
    IO.FS.createDirAll (receiptDirectory replica)
    placeRequest (requestDirectory replica) (id ++ if index == proposer then ".call" else ".watch") call
  let stop := (← IO.monoMsNow) + deadlineMs
  repeat
    let mut found := []
    for replica in replicas do
      let path := receiptDirectory replica / (id ++ ".receipt")
      if ← path.pathExists then
        if let some decoded := receiptFileStream.decodeBytes (← IO.FS.readBinFile path) then
          found := found ++ [decoded]
    if found.length == replicas.length then
      let some (receiptBytes,_) := found.head? | return .uncertain
      unless found.all (fun (r,_) => r == receiptBytes) do
        throw (IO.userError "replicas disagree on the exact receipt")
      let some (_,before) := found[proposer]? | return .uncertain
      let some receipt := Minidregg.Compiler.NativeHostCodec.receiptStream.toLawful.decode receiptBytes
        | throw (IO.userError "noncanonical replica receipt")
      return .confirmed (if before then .replayed else .installed) receipt
    if (← IO.monoMsNow) ≥ stop then return .uncertain
    IO.sleep 200
  return .uncertain

end Minidregg.Compiler.GenericSimplexServe
