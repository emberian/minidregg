/- One ordered receiver for native ordinary and joint source transitions.
The exact complete source record selected by the common domain log is still
freshly derived by the real native receiver at the exact current source prefix.
Only then can the unchanged physical CAS/readback append it. -/
import Kernel.NativeHostReplay
import Kernel.JointReceiver
import Compiler.GenericSimplexSourceAnchor
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
configuration. A quorum certificate authorizes order, not source permission.
This call obtains both independently before one existing source-record CAS. -/
def apply {config : Config} {target : Durable} (old : Verified config target)
    (expected : Context) (commitment : VerifiedCommit expected) (sourceBytes : List UInt8) :
    IO (Result config old expected) := do
  if contextPinned : config.jointConsensus = some expected then
    if expected.scope != digestStream.encode config.deployment.domain then
      return .refused "source consensus scope mismatch"
    if expected.instanceBytes != anchorBytes config.genesisHeight old.opened.durable.image.seed then
      return .refused "source consensus exact genesis mismatch"
    match ← deriveVerified old sourceBytes with
    | .error detail => return .refused detail
    | .ok derived =>
      let some ordered := JointReceiver.order expected old.opened.durable derived.intent commitment
        | return .refused "committed block is not exact source prefix plus derived record"
      match ← DurableReceiverIO.receiveLoadedDetailed (orderedTransport derived)
          ResourceBirthCodec.rootBytes old.opened.durable derived.intent with
      | .ordinary result => return .ordinary result
      | .exact _ appended =>
        match ExactReadback.ofAppended old derived appended with
        | .error detail => return .refused detail
        | .ok readback =>
          have sourceOrder : JointReceiver.Ordered expected old.opened.durable readback.val.derived.intent :=
            readback.property.symm ▸ ordered
          match ← DurableHistoryStore.readerOf (orderedTransport derived) ResourceBirthCodec.rootBytes
              appended.next with
          | .error detail => return .uncertain s!"post-append history reader: {detail}"
          | .ok ⟨store, reader⟩ => return .applied ⟨contextPinned,readback.val,sourceOrder,store,reader⟩
  else return .refused "source consensus context not deployment pinned"

/-- The actual source history extension reuses the same admitted intent and
exact physical source readback; engine journal flags cannot construct it. -/
def Applied.verified {config : Config} {target : Durable}
    {old : Verified config target} {expected : Context} (applied : Applied config old expected) :
    Verified config (exactCandidate old applied.readback.derived applied.readback.ready) :=
  extendExact applied.reader old applied.readback

theorem applied_exact_source_record {config : Config} {target : Durable}
    {old : Verified config target} {expected : Context} (applied : Applied config old expected) :
    applied.readback.appended.entry.record =
      DurableCheckpointCodec.recordFrame.encode
        (DurableReceiver.IntentRecord.ofIntent applied.readback.derived.intent) :=
  applied.readback.appended.entryExact

end Minidregg.Kernel.JointOrderedSourceReceiver
