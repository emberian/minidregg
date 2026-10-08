/- Durable judgment and append over the shared loaded-image core. -/
import Compiler.DurableReceiverCore
import Kernel.ObjectiveAdmissible

namespace Minidregg.Compiler.DurableReceiverIO

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.DurableCheckpoint
open Minidregg.Compiler.DurableReceiverCodec
open Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Compiler.DurableLogTags (chainPrefixes verifyTags)
open Minidregg.Compiler.DurableHistory (Carried trailer trailerCarried leafDigest frontierDigest)

set_option autoImplicit false

/-- Read back the entry at `height`; exact equality with what this attempt
proposed is the only confirmation. -/
private def readBackEntry (transport : Transport) (height : Nat) :
    IO (Except String (Option Entry)) := do
  match ← transport.read height false with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) => return .ok stored.entries.head?

/-- The ordinary arm must pass the protected-cell gate. The OB arm contains
an exact receiver certificate; it has no independent intent argument. -/
inductive Candidate {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) where
  | ordinary (intent : DataIntent rootBytes)
  | objective (concrete : rootBytes = ResourceBirthCodec.rootBytes)
      {ob : ObjectiveActivity.Config} {t : ObjectiveAdmissible.T}
      (certificate : ObjectiveAdmissible.CheckedCommit ob (cast (congrArg Loaded concrete) loaded) t)

def Candidate.intent {rootBytes : List UInt8 → Digest} {loaded : Loaded rootBytes} :
    Candidate loaded → DataIntent rootBytes
  | .ordinary intent => intent
  | .objective concrete certificate => cast (congrArg DataIntent concrete.symm) certificate.intent

def Candidate.gate {rootBytes : List UInt8 → Digest} {loaded : Loaded rootBytes} :
    Candidate loaded → Except RejectReason Unit
  | .ordinary intent => ObjectiveActivityGate.ordinaryGate intent
  | .objective _ _ => .ok ()

/-- All three obligations travel to the only physical writer. The source and
tail gates are not discarded when the receiver supplies its certificate. -/
structure CommitEvidence {rootBytes : List UInt8 → Digest} {loaded : Loaded rootBytes}
    (candidate : Candidate loaded) (sourceResult tailResult : Except RejectReason Unit) : Type where
  reserved : candidate.gate = .ok ()
  source : sourceResult = .ok ()
  tail : tailResult = .ok ()

/-- Only the transport's admission policy indexes evidence. Changing its IO
writers (as dry-run does) neither changes nor invalidates admission. -/
abbrev Commit {rootBytes : List UInt8 → Digest} (transport : Transport)
    (loaded : Loaded rootBytes) (candidate : Candidate loaded) : Type :=
  CommitEvidence candidate (transport.sourceGate loaded.snapshot candidate.intent)
    (match transport.systemCell with
    | none => (Except.ok () : Except RejectReason Unit)
    | some systemId => Kernel.TailBound.gate systemId (loaded.height + 1)
        loaded.chain loaded.snapshot candidate.intent)

/-- Admission now returns the evidence consumed by the append, rather than
throwing away the judgment as Unit. -/
def Loaded.judge {rootBytes : List UInt8 → Digest} (transport : Transport)
    (loaded : Loaded rootBytes) (candidate : Candidate loaded) :
    Except RejectReason (Commit transport loaded candidate) :=
  match reserved : candidate.gate with
  | .error reason => .error reason
  | .ok () =>
    match source : transport.sourceGate loaded.snapshot candidate.intent with
    | .error reason => .error reason
    | .ok () =>
      match tail : (match transport.systemCell with
        | none => (Except.ok () : Except RejectReason Unit)
        | some systemId => Kernel.TailBound.gate systemId (loaded.height + 1)
            loaded.chain loaded.snapshot candidate.intent) with
      | .error reason => .error reason
      | .ok () => .ok ⟨reserved, source, tail⟩

theorem Commit.tail_pinned {rootBytes : List UInt8 → Digest} {transport : Transport}
    {loaded : Loaded rootBytes} {candidate : Candidate loaded}
    (commit : Commit transport loaded candidate) (systemId : CellId)
    (pinned : transport.systemCell = some systemId) :
    Kernel.TailBound.gate systemId (loaded.height + 1) loaded.chain loaded.snapshot candidate.intent = .ok () := by
  simpa only [pinned] using commit.tail

/-- An ordinary certificate cannot write any OB-protected coordinate, for
every execution schedule, including the successful physical commit. -/
theorem Commit.ordinary_preserves {rootBytes : List UInt8 → Digest} {transport : Transport}
    {loaded : Loaded rootBytes} {intent : DataIntent rootBytes}
    (commit : Commit transport loaded (.ordinary intent))
    (schedule : DurableCommitProtocol.Schedule) {cell : CellId}
    (isProtected : ObjectiveActivityGate.Protected cell) :
    ((execute schedule loaded.snapshot intent).storeAfter loaded.snapshot).canonicalBytes cell =
      loaded.snapshot.canonicalBytes cell :=
  ObjectiveActivityGate.ordinary_execute_protected schedule loaded.snapshot commit.reserved isProtected

#assert_axioms Commit.tail_pinned Commit.ordinary_preserves

/-- A replay admission retains the candidate and its evidence, with exact
source-intent equality for the replay executor. -/
structure Judged {rootBytes : List UInt8 → Digest} (transport : Transport)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) where
  candidate : Candidate loaded
  intentExact : candidate.intent = intent
  commit : Commit transport loaded candidate

def Judged.retarget {rootBytes : List UInt8 → Digest} {transport : Transport}
    {loaded : Loaded rootBytes} {intent other : DataIntent rootBytes}
    (judged : Judged transport loaded intent) (exact : intent = other) :
    Judged transport loaded other :=
  ⟨judged.candidate, judged.intentExact.trans exact, judged.commit⟩

theorem Judged.tail_pinned {rootBytes : List UInt8 → Digest} {transport : Transport}
    {loaded : Loaded rootBytes} {intent : DataIntent rootBytes}
    (judged : Judged transport loaded intent) (systemId : CellId)
    (pinned : transport.systemCell = some systemId) :
    Kernel.TailBound.gate systemId (loaded.height + 1) loaded.chain loaded.snapshot intent = .ok () := by
  rw [← judged.intentExact]
  exact Commit.tail_pinned judged.commit systemId pinned

theorem Commit.route {transport : Transport} {loaded : Loaded ResourceBirthCodec.rootBytes}
    {candidate : Candidate loaded} (commit : Commit transport loaded candidate) :
    ObjectiveAdmissible.Route loaded candidate.intent := by
  cases candidate with
  | ordinary intent => exact Or.inr (Or.inr commit.reserved)
  | objective concrete certificate => exact certificate.source.route

theorem Judged.route {transport : Transport} {loaded : Loaded ResourceBirthCodec.rootBytes}
    {intent : DataIntent ResourceBirthCodec.rootBytes} (judged : Judged transport loaded intent) :
    ObjectiveAdmissible.Route loaded intent :=
  judged.intentExact ▸ Commit.route judged.commit

#assert_axioms Commit.route Judged.route

def Loaded.judgeOrdinary {rootBytes : List UInt8 → Digest} (transport : Transport)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) :
    Except String (Judged transport loaded intent) :=
  match loaded.judge transport (.ordinary intent) with
  | .error reason => .error s!"derived durable intent refused: {repr reason}"
  | .ok commit => .ok ⟨.ordinary intent, rfl, commit⟩

def Loaded.judgeObjective (transport : Transport) (loaded : Loaded ResourceBirthCodec.rootBytes)
    (proposal : ObjectiveAdmissible.Proposal loaded) :
    Except String (Judged transport loaded proposal.intent) := do
  let ⟨_, ⟨certificate, exact⟩⟩ ← proposal.check
  match loaded.judge transport (.objective rfl certificate) with
  | .error reason => .error s!"derived durable intent refused: {repr reason}"
  | .ok commit => .ok ⟨.objective rfl certificate, exact, commit⟩

#assert_axioms Judged.tail_pinned

/-- What an append writes, prepared from the loaded image and the Store's
reads (the head tag's index root, the index rows): the entry (record and v4
trailer), the node rows, the extended image and the index root after it. -/
structure PreparedAppend {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes)
    (intent : DataIntent rootBytes) where
  entry : Entry
  entryExact : entry.record = recordFrame.encode (IntentRecord.ofIntent intent)
  nodes : List NodeWrite
  extended : Loaded rootBytes
  extendedImage : extended.image = loaded.image.append intent
  indexAfter : Digest

def prepareAppend (transport : Transport) {rootBytes : List UInt8 → Digest}
    (loaded : Loaded rootBytes) {intent : DataIntent rootBytes}
    (ready : Ready rootBytes loaded.image loaded.baseHeight loaded.base loaded.snapshot intent)
    (key : MacKey) : IO (Except String (PreparedAppend loaded intent)) := do
  let height := loaded.image.accepted.length + 1
  let recordBytes := recordFrame.encode (IntentRecord.ofIntent intent)
  let chain := loaded.chainAfterIntent intent
  let some frontier := loaded.frontier
    | return .error "this opening carries no accumulator frontier (it was not read from the Store)"
  -- The index after the head (MAC-verified), then this record's rows (IndexRows.changes) applied.
  let indexBefore ← match ← loaded.headIndexRoot transport key with
    | .ok root => pure root
    | .error message => return .error message
  let keys := DurableIndex.IndexRows.keys intent.transactionId intent.nullifiers
  let (indexAfter, indexWrites) ← match ← withIndexRows transport loaded.image.accepted.length keys
      (fun rows => DurableIndex.IndexRows.apply rows indexBefore height intent.transactionId
        intent.nullifiers) with
    | .ok result => pure result
    | .error message => return .error message
  -- The tag keeps this record's receipt root, the root the extended image
  -- serves, the accumulator frontier after it and the index root after it.
  let extended := loaded.extend ready
  let leaf := leafDigest height recordBytes chain extended.worldRoot
  let frontierAfter := DurableHistory.Frontier.push frontier leaf
  let nodes := appendNodes (DurableHistory.completedNodes frontier height leaf) indexWrites
  let entry : Entry := ⟨recordBytes, trailer key height
    ⟨extended.worldRoot, chain, frontierDigest height frontierAfter, indexAfter⟩⟩
  return .ok ⟨entry, rfl, nodes, extended, rfl, indexAfter⟩

/-- What the receiving loop does after the append's observation: confirm by
exact readback (seal a due checkpoint), or report contention. -/
def publishAfter (transport : Transport) (rootBytes : List UInt8 → Digest) (loaded : Loaded rootBytes)
    (intent : DataIntent rootBytes) (prepared : PreparedAppend loaded intent)
    (observation : CasObservation) : IO (Bool × DetailedResult rootBytes loaded intent) := do
  let height := loaded.image.accepted.length + 1
  let entry := prepared.entry
  let extended := prepared.extended
  let indexAfter := prepared.indexAfter
  let confirm := fun (installed : Bool) (kind : Confirmation) => do
    match ← readBackEntry transport height with
    | .error message =>
        return (false, DetailedResult.ordinary (.uncertain s!"append attempted; readback unavailable: {message}"))
    | .ok none =>
        return (false, .ordinary (.uncertain "append attempted; entry absent on readback"))
    | .ok (some stored) =>
        if stored = entry then
          let tagged := { extended with headTag := some entry.tag }
          let checkpointStored ←
            if checkpointDue transport tagged then storeCheckpoint transport rootBytes tagged indexAfter
            else pure false
          return (installed, .exact kind
            ⟨afterCheckpoint tagged checkpointStored,
              (afterCheckpoint_image tagged checkpointStored).trans prepared.extendedImage, entry,
              prepared.entryExact⟩)
        else return (false, .ordinary .contention)
  match observation with
  | .installed => confirm true .installed
  | .alreadyPresent => confirm false .installed
  | .conflict => return (false, .ordinary .contention)
  | .uncertain _ => confirm false .recoveredAfterUncertainResponse

/-- Append a prepared entry at `loaded.height + 1` (the receiving loop's only
Store write), then `publishAfter`. -/
def publish (transport : Transport) (rootBytes : List UInt8 → Digest) (loaded : Loaded rootBytes)
    {candidate : Candidate loaded} (_commit : Commit transport loaded candidate)
    (prepared : PreparedAppend loaded candidate.intent) :
    IO (Bool × DetailedResult rootBytes loaded candidate.intent) :=
  transport.append (loaded.image.accepted.length + 1) prepared.entry prepared.nodes >>=
    publishAfter transport rootBytes loaded candidate.intent prepared

/-- A conflicting append is contention, and nothing else is read or written. -/
theorem publishAfter_conflict (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) (prepared : PreparedAppend loaded intent) :
    publishAfter transport rootBytes loaded intent prepared .conflict =
      pure (false, .ordinary .contention) := rfl

/-- Publish against the exact image on which the controller admitted the
operation: append entry `h + 1` only while the head is `h`. One attempt, no
rebase; a lost response never becomes a refusal. The Bool is whether this
call installed the entry. -/
def receiveCandidateWithFresh (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (candidate : Candidate loaded) :
    IO (Bool × DetailedResult rootBytes loaded candidate.intent) := do
  match prepare loaded.image loaded.baseHeight loaded.base loaded.snapshot loaded.withinLog
      loaded.resumed candidate.intent with
  | .inr (.replayed _) => return (false, .ordinary (.confirmed .replayed loaded.snapshot))
  | .inr (.rejected reason) => return (false, .ordinary (.rejected reason))
  | .inr _ => return (false, .ordinary (.unavailable "unexpected complete-schedule outcome"))
  | .inl ready =>
      match loaded.judge transport candidate with
      | .error reason => return (false, .ordinary (.rejected reason))
      | .ok commit =>
        let .ok key ← transport.key
          | return (false, .ordinary (.unavailable "checkpoint MAC key unavailable"))
        match ← prepareAppend transport loaded ready key with
        | .error message => return (false, .ordinary (.unavailable message))
        | .ok prepared => publish transport rootBytes loaded commit prepared

/-- The raw wrapper constructs only the ordinary arm. In particular, choosing
a permissive transport source gate cannot bypass the protected-cell check. -/
def receiveLoadedDetailedWithFresh (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) :
    IO (Bool × DetailedResult rootBytes loaded intent) :=
  receiveCandidateWithFresh transport rootBytes loaded (.ordinary intent)

/-- The receiver supplies its checked run; only its derived certificate can
enter the common writer. The durable record encoding is unchanged. -/
def receiveObjective (transport : Transport) (loaded : Loaded ResourceBirthCodec.rootBytes)
    (proposal : ObjectiveAdmissible.Proposal loaded) : IO (Result ResourceBirthCodec.rootBytes) := do
  match proposal.check with
  | .error detail => return .unavailable detail
  | .ok ⟨_, ⟨certificate, _⟩⟩ =>
    return (← receiveCandidateWithFresh transport ResourceBirthCodec.rootBytes loaded
      (.objective rfl certificate)).2.toResult

def receiveLoadedDetailed (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) :
    IO (DetailedResult rootBytes loaded intent) := do
  return (← receiveLoadedDetailedWithFresh transport rootBytes loaded intent).2

def receiveLoaded (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) (intent : DataIntent rootBytes) :
    IO (Result rootBytes) := do
  return (← receiveLoadedDetailed transport rootBytes loaded intent).toResult

/-- Whether the store's head is still exactly this entry at this height — a
point-in-time check, not a lease. -/
def tipIs (transport : Transport) (height : Nat) (entry : Entry) : IO (Except String Bool) := do
  match ← transport.read height false with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) => return .ok (stored.head = height && stored.entries == [entry])

/-- Bounded contention retry for an internal intent whose admission does not
depend on a journal-wide clock. Each retry reloads. -/
def receive (transport : Transport) (rootBytes : List UInt8 → Digest)
    (intent : DataIntent rootBytes) : Nat → IO (Result rootBytes)
  | 0 => pure .contention
  | attempts + 1 => do
      match ← load transport rootBytes with
      | .error message => return .unavailable message
      | .ok loaded =>
          match ← receiveLoaded transport rootBytes loaded intent with
          | .contention => receive transport rootBytes intent attempts
          | result => return result

/-- Rebasing at the head keeps the image and the log start. -/
theorem Loaded.rebase_image {rootBytes : List UInt8 → Digest} {loaded rebased : Loaded rootBytes}
    (done : loaded.rebase = some rebased) :
    rebased.image = loaded.image ∧ rebased.logStart = loaded.logStart := by
  unfold Loaded.rebase at done
  dsimp only at done
  split at done
  · cases done
  · cases done
    exact ⟨rfl, rfl⟩

/-- Replay stored records onto a loaded image through the shared executor, one
`Loaded.extend` each. The result's image is the given one followed by exactly
these records. -/
def Loaded.replay {rootBytes : List UInt8 → Digest} (loaded : Loaded rootBytes) :
    (records : List IntentRecord) →
    Except String {next : Loaded rootBytes //
      next.image = ⟨loaded.image.seed, loaded.image.accepted ++ records⟩ ∧
        next.logStart = loaded.logStart}
  | [] => .ok ⟨loaded, by rw [List.append_nil], rfl⟩
  | record :: rest =>
      match bound : record.bind? rootBytes with
      | none => .error "durable log record does not bind its roots"
      | some intent =>
          match prepare loaded.image loaded.baseHeight loaded.base loaded.snapshot
              loaded.withinLog loaded.resumed intent with
          | .inl ready =>
              match (loaded.extend ready).replay rest with
              | .error message => .error message
              | .ok ⟨next, imaged, started⟩ =>
                  .ok ⟨next, by
                    rw [imaged]
                    show (⟨loaded.image.seed, (loaded.image.accepted ++
                      [IntentRecord.ofIntent intent]) ++ rest⟩ : Image) = _
                    rw [IntentRecord.bind_exact bound, List.append_assoc, List.singleton_append],
                    started⟩
          | .inr _ => .error "durable log suffix does not replay through the canonical executor"

/-- Extend a live loaded image by entries a concurrent writer appended after
it: the chain must continue, every new entry's tag must verify, and every new
record must be accepted by the shared executor in order. The result is the
given image followed by exactly the new records (by construction, so a
verified history over the old image extends without comparing prefixes:
`NativeHostReplay.extendVerifiedAppended`). -/
def extendFrom (transport : Transport) (rootBytes : List UInt8 → Digest)
    (loaded : Loaded rootBytes) : IO (Except String {next : Loaded rootBytes //
      next.image.seed = loaded.image.seed ∧
        next.image.accepted = loaded.image.accepted ++
          next.image.accepted.drop loaded.image.accepted.length ∧
        next.logStart = loaded.logStart}) := do
  let key ← match ← transport.key with
    | .error message => return .error message
    | .ok key => pure key
  let height := loaded.image.accepted.length
  match ← transport.read (height + 1) false with
  | .error message => return .error message
  | .ok none => return .error "durable store is not initialized"
  | .ok (some stored) =>
      if stored.head = height then return .ok ⟨loaded, rfl, by simp, rfl⟩
      if stored.head < height then return .error "durable log shrank beneath the session"
      let records ← match decodeRecordsFrom (height + 1) stored.entries with
        | .error message => return .error message
        | .ok records => pure records
      let chain := chainAfter loaded.chain records
      if height + stored.entries.length ≠ stored.head then
        return .error "durable log head does not match its entries"
      if let .error message := verifyTags key height (chainPrefixes loaded.chain records)
          (stored.entries.map (·.tag)) then
        return .error message
      -- Every new tag carries the frontier the accumulator reaches at its height.
      if let some frontier := loaded.frontier then
        if let .error message := walkFrontier height frontier
            (stored.entries.zip ((chainPrefixes loaded.chain records).drop 1)) then
          return .error message
      match loaded.replay records with
      | .error message => return .error message
      | .ok ⟨current, imaged, started⟩ =>
        have extended : current.image.seed = loaded.image.seed ∧
            current.image.accepted = loaded.image.accepted ++
              current.image.accepted.drop loaded.image.accepted.length ∧
            current.logStart = loaded.logStart := by
          rw [imaged]
          exact ⟨rfl, by simp, started⟩
        if current.chain ≠ chain then return .error "durable log chain mismatch"
        -- Every new entry's stored root is the root its replay served.
        let replayed := (current.rootLog.extract height current.rootLog.size).toList
        if replayed ≠ stored.entries.map (fun entry =>
            some ((trailerCarried entry.tag).map (·.root) |>.getD ⟨0⟩)) then
          return .error "durable log root tag differs from the replayed root"
        let current := { current with headTag := stored.entries.getLast?.map (·.tag) }
        if current.image.accepted.length ≥ current.baseHeight + 2 * max 1 transport.checkpointEvery then
          match rebased : current.rebase with
          | some next =>
              have kept := Loaded.rebase_image rebased
              return .ok ⟨next, by rw [kept.1]; exact extended.1,
                by rw [kept.1]; exact extended.2.1, by rw [kept.2]; exact extended.2.2⟩
          | none => return .error "rebase at the head does not resume through the canonical executor"
        return .ok ⟨current, extended⟩

/-- Explicit bootstrap, separate from receipt acceptance. An existing different
seed is never replaced; initialization is confirmed by a full `load`. -/
def bootstrap (transport : Transport) (rootBytes : List UInt8 → Digest)
    (seed : Seed) : IO (Except String Unit) := do
  if (loadSeed rootBytes (transport.logStart seed) seed).toOption.isNone then
    return .error "invalid bootstrap seed"
  let observation ← transport.initializeSeed (seedFrame.encode seed)
  match ← load transport rootBytes with
  | .ok loaded =>
      if loaded.image.accepted.isEmpty ∧ seedFrame.encode loaded.image.seed = seedFrame.encode seed then
        return .ok ()
      else return .error s!"bootstrap did not install exact seed: {repr observation}"
  | .error message => return .error s!"bootstrap outcome uncertain: {message}"

/-- Write an accepted image into an EMPTY Store through `transport`: its seed
bootstrapped, then each record bound (`IntentRecord.bind?`) and appended in order
through the one receive path (`receiveLoadedDetailed`), each read back exactly, the
opening advanced by the appended entry (no re-open per record). The result is the
Store's opening at the image's height, so a history `Reader` of a portable image
(a foreign accepted prefix) is a Reader of a real Store, never an in-memory one.
Refuses, naming the height, a record that does not bind, does not re-encode to
itself, or is not appended exactly; and a Store whose final image is not `image`. -/
def writeImage (transport : Transport) (rootBytes : List UInt8 → Digest) (image : Image) :
    IO (Except String (Loaded rootBytes)) := do
  match ← bootstrap transport rootBytes image.seed with
  | .error detail => return .error s!"scratch Store: {detail}"
  | .ok () => pure ()
  let genesis ← match ← load transport rootBytes with
    | .ok loaded => pure loaded
    | .error detail => return .error s!"scratch Store: genesis open: {detail}"
  let rec go (height : Nat) (loaded : Loaded rootBytes) :
      List IntentRecord → IO (Except String (Loaded rootBytes))
    | [] => return .ok loaded
    | record :: rest => do
        let some intent := record.bind? rootBytes
          | return .error s!"scratch Store: record {height + 1} does not bind its roots"
        if recordFrame.encode (IntentRecord.ofIntent intent) != recordFrame.encode record then
          return .error s!"scratch Store: record {height + 1} does not re-encode to itself"
        match ← receiveLoadedDetailed transport rootBytes loaded intent with
        | .exact _ appended => go (height + 1) appended.next rest
        | .ordinary _ => return .error s!"scratch Store: record {height + 1} was not appended exactly"
  match ← go 0 genesis image.accepted with
  | .error detail => return .error detail
  | .ok loaded =>
      if (loaded.image.accepted.map fun record => recordFrame.encode record) =
          image.accepted.map (fun record => recordFrame.encode record) then
        return .ok loaded
      else return .error "scratch Store: the written image is not the image"

end Minidregg.Compiler.DurableReceiverIO
