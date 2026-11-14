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
public import Std.Data.HashMap

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

/-- The running application digest of a loaded source's records (`historyDigest`), kept
beside the source: computed once when the source is opened and extended by each append, so
ordering a record hashes nothing below it. -/
structure History (loaded : Durable) where
  expected : Context
  digest : Minidregg.Kernel.GenericSimplex.Bytes
  exact : digest = (historyDigest expected).of (sourcePrefix loaded)

/-- Linear in the source history: once, where the source is opened or reread. -/
def History.start (expected : Context) (loaded : Durable) : History loaded := ⟨expected,_,rfl⟩

/-- The digest after `records` were appended: one extension per appended record. -/
def History.extend {loaded next : Durable} (h : History loaded)
    (records : Minidregg.Kernel.GenericSimplex.Block)
    (appended : sourcePrefix next = sourcePrefix loaded ++ records) : History next :=
  ⟨h.expected,(historyDigest h.expected).over h.digest records, by
    rw [appended, h.exact]
    exact (Minidregg.Kernel.GenericSimplexRelative.ChainDigest.over_append _ _ _ _).symm⟩

/-! ## The index of a source's records by their original ingress

A request asks whether an original signed ingress has been installed. The answer is kept
beside the source like its running digest: built once where the source is opened or reread,
extended by each append, so no request walks the accepted records. -/

/-- Original ingress bytes (a record's `event.canonicalBytes`) to the position of the first
record that carries them. -/
abbrev IngressTable := Std.HashMap Minidregg.Kernel.GenericSimplex.Bytes Nat

/-- Every entry of the table names a record that carries its key as the original ingress. -/
def IngressSound (table : IngressTable) (records : List IntentRecord) : Prop :=
  ∀ ingress index, table[ingress]? = some index →
    (records[index]?).map (fun (record : IntentRecord) => record.event.canonicalBytes) = some ingress

theorem IngressSound.empty (records : List IntentRecord) : IngressSound {} records := by
  intro ingress index found
  simp at found

/-- One appended record: its ingress enters at the old length unless an earlier record
already carries it (the first installation is the one a receipt is for). -/
theorem IngressSound.snoc {table : IngressTable} {records : List IntentRecord}
    (h : IngressSound table records) (record : IntentRecord) :
    IngressSound (table.insertIfNew record.event.canonicalBytes records.length)
      (records ++ [record]) := by
  intro ingress index found
  rw [Std.HashMap.getElem?_insertIfNew] at found
  split at found
  · rename_i hit
    cases found
    have same : record.event.canonicalBytes = ingress := by simpa using hit.1
    simp [same]
  · have old := h ingress index found
    cases held : records[index]? with
    | none => simp [held] at old
    | some value =>
      have within : index < records.length := (List.getElem?_eq_some_iff.mp held).1
      rw [List.getElem?_append_left within, held]
      simpa [held] using old

/-- The table of a whole record list, in one pass. -/
def ingressTable (records : List IntentRecord) : IngressTable :=
  (records.foldl (fun (acc : IngressTable × Nat) record =>
    (acc.1.insertIfNew record.event.canonicalBytes acc.2, acc.2 + 1)) ({}, 0)).1

theorem ingressTable_sound (records : List IntentRecord) :
    IngressSound (ingressTable records) records := by
  have general : ∀ (todo done : List IntentRecord) (table : IngressTable),
      IngressSound table done →
      IngressSound (todo.foldl (fun (acc : IngressTable × Nat) record =>
        (acc.1.insertIfNew record.event.canonicalBytes acc.2, acc.2 + 1)) (table, done.length)).1
        (done ++ todo) := by
    intro todo
    induction todo with
    | nil => intro done table h; simpa using h
    | cons record rest ih =>
      intro done table h
      have step := ih (done ++ [record]) _ (h.snoc record)
      simpa [List.foldl_cons, List.length_append, List.append_assoc] using step
  simpa [ingressTable] using general records [] {} (IngressSound.empty [])

/-- The index by ingress of a loaded source's records, kept beside the source. A hit is the
position of a record carrying exactly that ingress (`sound`); the first installation wins. -/
structure Ingress (loaded : Durable) where
  table : IngressTable
  sound : IngressSound table loaded.image.accepted

/-- Linear in the source history: once, where the source is opened or reread. -/
def Ingress.start (loaded : Durable) : Ingress loaded :=
  ⟨ingressTable loaded.image.accepted, ingressTable_sound _⟩

/-- The index after one record was appended: one insertion. -/
def Ingress.extend {loaded next : Durable} (i : Ingress loaded) (record : IntentRecord)
    (appended : next.image.accepted = loaded.image.accepted ++ [record]) : Ingress next :=
  ⟨i.table.insertIfNew record.event.canonicalBytes loaded.height, by
    rw [appended]
    exact i.sound.snoc record⟩

/-- Where this ingress was installed, if it was: one table lookup. -/
def Ingress.find {loaded : Durable} (i : Ingress loaded) (ingress : Minidregg.Kernel.GenericSimplex.Bytes) : Option Nat :=
  i.table[ingress]?

theorem Ingress.find_sound {loaded : Durable} (i : Ingress loaded) {ingress : Minidregg.Kernel.GenericSimplex.Bytes} {index : Nat}
    (found : i.find ingress = some index) :
    (loaded.image.accepted[index]?).map (fun (record : IntentRecord) => record.event.canonicalBytes) = some ingress :=
  i.sound ingress index found

/-- Source-private application capability. The caller cannot decode one from
bytes or replace expected context with the roster advertised by a packet.

A commitment names its chain by a digest and carries no payload. `history` is the
application history this reader takes it to order: the loaded source prefix, the record,
and the committed records after it that the reader already holds (`later`). `reads` is the
check that makes it so: the running digest of `history` is the application half of the
signed digest. That no other history has that digest is the digest's collision-freedom, an
assumption wherever two such tokens are compared (`GenericSimplexReceiverSafety`). The
history is named, never built: the token holds only `later`. -/
structure Ordered (expected : Context) (loaded : Durable)
    (intent : DataIntent ResourceBirthCodec.rootBytes) where
  private mk ::
  commitment : VerifiedCommit expected
  later : Minidregg.Kernel.GenericSimplex.Block
  reads : commitment.Reads (sourcePrefix loaded ++ [sourcePayload intent] ++ later)

def Ordered.history {expected : Context} {loaded : Durable}
    {intent : DataIntent ResourceBirthCodec.rootBytes} (o : Ordered expected loaded intent) :
    Minidregg.Kernel.GenericSimplex.Block :=
  sourcePrefix loaded ++ [sourcePayload intent] ++ o.later

theorem Ordered.sourceOrdered {expected : Context} {loaded : Durable}
    {intent : DataIntent ResourceBirthCodec.rootBytes} (o : Ordered expected loaded intent) :
    (sourcePrefix loaded ++ [sourcePayload intent]).IsPrefix o.history := ⟨o.later,rfl⟩

/-- `later` are the committed records after this one, in order, up to the commitment's
chain. `history` is the running digest of the loaded source's records: the check extends it
by this record and `later`, and hashes nothing of the source prefix. -/
def order (expected : Context) (loaded : Durable)
    (intent : DataIntent ResourceBirthCodec.rootBytes) (commitment : VerifiedCommit expected)
    (history : History loaded) (later : Minidregg.Kernel.GenericSimplex.Block) :
    Option (Ordered expected loaded intent) :=
  if same : history.expected = expected then
    if reads : (historyDigest expected).over history.digest (sourcePayload intent :: later) =
        historyHalf commitment.digest then
      some ⟨commitment,later,by
        have exact := history.exact
        rw [same] at exact
        show (historyDigest expected).over (historyDigest expected).origin
          (sourcePrefix loaded ++ [sourcePayload intent] ++ later) = historyHalf commitment.digest
        rw [List.append_assoc, Minidregg.Kernel.GenericSimplexRelative.ChainDigest.over_append,
          ← reads, exact]
        rfl⟩
    else none
  else none

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
