/- One ordered receiver for native ordinary and joint source transitions.
The exact complete source record selected by the common domain log is still
freshly derived by the real native receiver at the exact current source prefix.
Only then can the unchanged physical CAS/readback append it. -/
module

public import Kernel.NativeHostReplay
public import Kernel.JointReceiver
public import Compiler.GenericSimplexSourceAnchor

@[expose] public section

namespace Minidregg.Kernel.JointOrderedSourceReceiver
open Minidregg.Theory
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.GenericSimplexSourceAnchor
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.NativeHostReplay
set_option autoImplicit false

/-- A verified ordering permits the actual physical append callback, while
retaining the SAME current source gate chosen by the privately derived native
admission. No API accepts an arbitrary client gate/ignore list. -/
def orderedTransport {config : Config} {opened : Opened config}
    (derived : Derived config opened) : DurableReceiverIO.Transport :=
  { derived.transport with append := config.physicalTransport.append }

/-- Engine commitment and source application are separate witnesses. This
private token contains actual exact source readback and a complete native
history extension, plus the exact matching ordered block. It has no byte decoder. -/
structure Applied (config : Config) {target : Durable}
    (old : Verified config target) (expected : Context) where
  private mk ::
  contextPinned : config.jointConsensus = some expected
  readback : ExactReadback config old
  ordered : JointReceiver.Ordered expected old.opened.durable readback.derived.intent
  /-- The Store the record was appended to, and its history Reader at the appended
  head (`DurableHistoryStore.readerOf`): the extension's history reads go through it. -/
  store : DurableHistory.StoreIdentity
  reader : DurableHistoryReader.Reader ResourceBirthCodec.rootBytes store

inductive Result (config : Config) {target : Durable}
    (old : Verified config target) (expected : Context) where
  | applied (receipt : Applied config old expected)
  | refused (detail : String)
  | ordinary (result : DurableReceiverIO.Result ResourceBirthCodec.rootBytes)
  /-- The record was appended and read back, but the Store's history Reader at the
  new head is unavailable: not a refusal (the record is durable); the caller
  re-reads the Store. -/
  | uncertain (detail : String)

/-- Typed ingress from the fixed deployment-native certificate verifier. The
request supplies only source bytes; expected/context/helper are controller
configuration. `later` are the committed records after this one that the caller holds, up
to the certified chain, and `history` is the running digest of the source's records
(`JointReceiver.History`). A quorum certificate authorizes order, not source permission.
This call obtains both independently before one existing source-record CAS. -/
def apply {config : Config} {target : Durable} (old : Verified config target)
    (expected : Context) (commitment : VerifiedCommit expected)
    (history : JointReceiver.History old.opened.durable)
    (later : Minidregg.Kernel.GenericSimplex.Block) (sourceBytes : List UInt8) :
    IO (Result config old expected) := do
  if contextPinned : config.jointConsensus = some expected then
    if expected.scope != digestStream.encode config.deployment.domain then
      return .refused "source consensus scope mismatch"
    if expected.instanceBytes != anchorBytes config.genesisHeight old.opened.durable.image.seed then
      return .refused "source consensus exact genesis mismatch"
    -- Operator measurement control (as `MINI_OPEN_TIMING`): MINI_APPEND_TIMING=1 prints where
    -- one ordered append spent its time, in microseconds, to stderr.
    let timing := (← IO.getEnv "MINI_APPEND_TIMING") == some "1"
    let t0 ← IO.monoNanosNow
    match ← deriveVerified old sourceBytes with
    | .error detail => return .refused detail
    | .ok derived =>
      let t1 ← IO.monoNanosNow
      let some ordered := JointReceiver.order expected old.opened.durable derived.intent commitment history later
        | return .refused "the commitment's digest is not that of the source prefix, the derived record and the later committed records"
      let t2 ← IO.monoNanosNow
      match ← DurableReceiverIO.receiveLoadedDetailed (orderedTransport derived)
          ResourceBirthCodec.rootBytes old.opened.durable derived.intent with
      | .ordinary result => return .ordinary result
      | .exact _ appended =>
        let t3 ← IO.monoNanosNow
        match ExactReadback.ofAppended old derived appended with
        | .error detail => return .refused detail
        | .ok readback =>
          have sourceOrder : JointReceiver.Ordered expected old.opened.durable readback.val.derived.intent :=
            readback.property.symm ▸ ordered
          let t4 ← IO.monoNanosNow
          match ← DurableHistoryStore.readerOf (orderedTransport derived) ResourceBirthCodec.rootBytes
              appended.next with
          | .error detail => return .uncertain s!"post-append history reader: {detail}"
          | .ok ⟨store, reader⟩ =>
            if timing then
              IO.eprintln s!"ordered append us at height {old.opened.durable.height + 1}: derive {(t1-t0)/1000} order {(t2-t1)/1000} store {(t3-t2)/1000} readback {(t4-t3)/1000} reader {((← IO.monoNanosNow)-t4)/1000}"
            return .applied ⟨contextPinned,readback.val,sourceOrder,store,reader⟩
  else return .refused "source consensus context not deployment pinned"

/-- The actual source history extension reuses the same admitted intent and
exact physical source readback; engine journal flags cannot construct it. -/
def Applied.verified {config : Config} {target : Durable}
    {old : Verified config target} {expected : Context} (applied : Applied config old expected) :
    Verified config (exactCandidate old applied.readback.derived applied.readback.ready applied.readback.tag) :=
  extendExact applied.reader old applied.readback

/-- The applied source's records are the old ones and the record just appended. -/
theorem Applied.sourcePrefix_verified {config : Config} {target : Durable}
    {old : Verified config target} {expected : Context} (applied : Applied config old expected) :
    JointReceiver.sourcePrefix applied.verified.opened.durable =
      JointReceiver.sourcePrefix old.opened.durable ++
        [JointReceiver.sourcePayload applied.readback.derived.intent] := by
  simp only [JointReceiver.sourcePrefix, JointReceiver.sourcePayload]
  rw [applied.verified.exactImage]
  simp [exactCandidate, DurableReceiverIO.Loaded.extend, DurableReceiver.Image.append]

/-- The running digest of the applied source: the old one extended by the appended record. -/
def Applied.history {config : Config} {target : Durable}
    {old : Verified config target} {expected : Context} (applied : Applied config old expected)
    (history : JointReceiver.History old.opened.durable) :
    JointReceiver.History applied.verified.opened.durable :=
  history.extend [JointReceiver.sourcePayload applied.readback.derived.intent]
    applied.sourcePrefix_verified

/-- The applied source's accepted records are the old ones and the record just appended. -/
theorem Applied.accepted_verified {config : Config} {target : Durable}
    {old : Verified config target} {expected : Context} (applied : Applied config old expected) :
    applied.verified.opened.durable.image.accepted =
      old.opened.durable.image.accepted ++
        [DurableReceiver.IntentRecord.ofIntent applied.readback.derived.intent] := by
  rw [applied.verified.exactImage]
  simp [exactCandidate, DurableReceiverIO.Loaded.extend, DurableReceiver.Image.append]

/-- The index by ingress of the applied source: the old one and the appended record. -/
def Applied.ingress {config : Config} {target : Durable}
    {old : Verified config target} {expected : Context} (applied : Applied config old expected)
    (index : JointReceiver.Ingress old.opened.durable) :
    JointReceiver.Ingress applied.verified.opened.durable :=
  index.extend _ applied.accepted_verified

theorem applied_exact_source_record {config : Config} {target : Durable}
    {old : Verified config target} {expected : Context} (applied : Applied config old expected) :
    applied.readback.appended.entry.record.toList =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent applied.readback.derived.intent) :=
  applied.readback.appended.entryExact

end Minidregg.Kernel.JointOrderedSourceReceiver
