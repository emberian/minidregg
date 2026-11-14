/- Ordered native reservation receiver. Source records, not replica-local MACs
or engine arrivals, occupy the shared consensus prefix. Physical allocation
receives only an actual read-back receipt; this module does NOT export YES.
SourceReady needs a real custody/privateRecovery receiver, still a separate join.
-/
module

public import Kernel.JointReceiverAdmission
public import Kernel.NativeHostContext
public import Compiler.GenericSimplexIO
public import Kernel.NativeHostServed

@[expose] public section

namespace Minidregg.Kernel.JointReceiver
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
open Minidregg.Kernel.JointReceiverAdmission
set_option autoImplicit false

/-- Canonical common source bytes omit replica-specific MAC/tag/checkpoint data. -/
def sourcePrefix (durable : Durable) : List (List UInt8) :=
  durable.image.accepted.map (fun r => DurableCheckpointCodec.recordFrame.encode r)
def sourcePayload (intent : DataIntent ResourceBirthCodec.rootBytes) : List UInt8 :=
  DurableCheckpointCodec.recordFrame.encode (IntentRecord.ofIntent intent)

/-- Source-private application capability. The caller cannot decode one from
bytes or replace expected context with the roster advertised by a packet.

A commitment names its chain by a digest and carries no payload. `history` is the
application history this reader takes it to order: the loaded source prefix, the record,
and the committed records after it that the reader already holds. `reads` is the check that
makes it so: the running digest of `history` is the application half of the signed digest.
That no other history has that digest is the digest's collision-freedom, an assumption
wherever two such tokens are compared (`GenericSimplexReceiverSafety`). -/
structure Ordered (expected : Context) (loaded : Durable)
    (intent : DataIntent ResourceBirthCodec.rootBytes) where
  private mk ::
  commitment : VerifiedCommit expected
  history : Minidregg.Kernel.GenericSimplex.Block
  reads : commitment.Reads history
  sourceOrdered : (sourcePrefix loaded ++ [sourcePayload intent]).IsPrefix history

/-- `later` are the committed records after this one, in order, up to the commitment's
chain. The digest is computed over the whole history from its origin: linear in the source
history, as `sourcePrefix` already is. -/
def order (expected : Context) (loaded : Durable)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (commitment : VerifiedCommit expected)
    (later : Minidregg.Kernel.GenericSimplex.Block) :
    Option (Ordered expected loaded intent) :=
  if reads : commitment.Reads (sourcePrefix loaded ++ [sourcePayload intent] ++ later) then
    some ⟨commitment,_,reads,⟨later,rfl⟩⟩ else none

/-- The ordinary deployment gate cannot exempt controller writes. This transport
is minted from the exact current source-admitted reservation token and accepts
only that complete canonical record and its current control pre-image. It keeps
all physical append/readback and TailBound mechanisms unchanged. -/
def reservedTransport (config : Config) (opened : Opened config)
    (r : Reserved config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.ground) :
    DurableReceiverIO.Transport :=
  { config.physicalTransport with sourceGate := fun snapshot intent => do
      config.otherFacetGate .joint snapshot intent
      if DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent intent) =
          DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent r.intent) ∧
          snapshot.canonicalBytes r.pin.cell = opened.durable.snapshot.canonicalBytes r.pin.cell then
        .ok () else .error (.durable .transactionConflict) }

/-- PENDING physical allocation authority comes only from the exact appended
source reservation, full readback, pinned consensus order and retained actual
current-source promise. It cannot certify recoverable private output or YES. -/
structure Pending (config : Config) (opened : Opened config) (expected : Context)
    (r : Reserved config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.ground) where
  private mk ::
  contextPinned : config.jointConsensus = some expected
  ordered : Ordered expected opened.durable r.intent
  appended : DurableReceiverIO.Appended ResourceBirthCodec.rootBytes opened.durable r.intent

inductive Result (config : Config) (opened : Opened config) (expected : Context)
    (r : Reserved config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.ground) where
  | pending (receipt : Pending config opened expected r)
  | refused
  | ordinary (result : DurableReceiverIO.Result ResourceBirthCodec.rootBytes)

/-- ONE existing source record CAS. Lost responses require exact readback;
ordinary replay confirmation alone does not mint a new allocation capability. -/
def applyReserved (config : Config) (opened : Opened config) (expected : Context)
    (r : Reserved config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.ground)
    (ordered : Ordered expected opened.durable r.intent) :
    IO (Result config opened expected r) := do
  if contextPinned : config.jointConsensus = some expected then
    if expected.scope != digestStream.encode config.deployment.domain ||
        expected.epoch != r.source.promise.declaration.epoch then return .refused
    if config.jointControl != some r.pin then return .refused
    match config.sourceGate none opened.durable.snapshot r.original with
    | .error _ => return .refused
    | .ok () => pure ()
    match ← DurableReceiverIO.receiveLoadedDetailed (reservedTransport config opened r)
        ResourceBirthCodec.rootBytes opened.durable r.intent with
    | .exact _ appended => return .pending ⟨contextPinned,ordered,appended⟩
    | .ordinary result => return .ordinary result
  else return .refused

/-- Receipt conservation is about the actual next source image, not an output
flag in a local protocol journal. Reservation/outbox/funding either all appear
in this source record or no Pending capability is returned. -/
theorem pending_exact_source_image {config : Config} {opened : Opened config}
    {expected : Context}
    {r : Reserved config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.ground}
    (receipt : Pending config opened expected r) :
    receipt.appended.next.image = opened.durable.image.append r.intent := receipt.appended.image

theorem pending_preserves_order {config : Config} {opened : Opened config}
    {expected : Context}
    {r : Reserved config.deployment config.profile
      ⟨config.federation,logicalHeight config opened.durable⟩ opened.ground}
    (receipt : Pending config opened expected r) :
    (sourcePrefix opened.durable ++ [sourcePayload r.intent]).IsPrefix
      receipt.ordered.history := receipt.ordered.sourceOrdered

end Minidregg.Kernel.JointReceiver
