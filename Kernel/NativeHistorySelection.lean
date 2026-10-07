/-
Conditional selection of one original record and its exact prefix from a
physically loaded Mini image. This lower module does not certify that earlier
records were semantically admitted and exposes no commit or host permit. The
upper native history verifier supplies that separate inductive provenance.
-/
import Kernel.NativeHostContext
import Compiler.DurableHistoryReader

namespace Minidregg.Kernel.NativeHistorySelection

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

def prefixImage {config : Config} (opened : Opened config) (index : Nat) : DurableReceiver.Image :=
  { opened.durable.image with accepted := opened.durable.image.accepted.take index }

/-- A selected record is tied to the supplied current image and a prefix
reconstructed from that image, never an independently caller-supplied Store. -/
structure Candidate (config : Config) (opened : Opened config) (index : Nat) where
  private mk ::
  prior : Opened config
  record : DurableReceiver.IntentRecord
  atIndex : opened.durable.image.accepted[index]? = some record
  priorImageExact : prior.durable.image = prefixImage opened index

def select (config : Config) (opened : Opened config) (index : Nat) :
    Except String (Candidate config opened index) := do
  match found : opened.durable.image.accepted[index]? with
  | none => .error "historical record index unavailable"
  | some record =>
      match built : DurableReceiverIO.loadImage rootBytes opened.durable.logStart (prefixImage opened index) with
      | .error detail => .error detail
      | .ok loaded =>
          match validated : validateLoaded config loaded with
          | .error detail => .error detail
          | .ok prior =>
              .ok ⟨prior, record, found,
                (congrArg DurableReceiverIO.Loaded.image (validateLoaded_durable validated)).trans
                  (DurableReceiverIO.loadImage_image built)⟩

/-- The same canonical intent-record stream used by the native replay
verifier compares all writes, guards, ten charge lanes, nullifiers and event. -/
def recordMatches (record : DurableReceiver.IntentRecord)
    (intent : DataIntent rootBytes) : Bool :=
  decide (DurableReceiverCodec.intentStream.encode record =
    DurableReceiverCodec.intentStream.encode (DurableReceiver.IntentRecord.ofIntent intent))

theorem recordMatches_iff (record : DurableReceiver.IntentRecord)
    (intent : DataIntent rootBytes) :
    recordMatches record intent = true ↔
      record = DurableReceiver.IntentRecord.ofIntent intent := by
  simp only [recordMatches, decide_eq_true_eq]
  exact (lawful_encode_injective DurableReceiverCodec.intentStream.toLawful).eq_iff

structure Matched {config : Config} {opened : Opened config} {index : Nat}
    (candidate : Candidate config opened index) (intent : DataIntent rootBytes) where
  private mk ::
  selectedRecord : DurableReceiver.IntentRecord
  selected : selectedRecord = candidate.record
  exact : selectedRecord = DurableReceiver.IntentRecord.ofIntent intent

def matchIntent {config : Config} {opened : Opened config} {index : Nat}
    (candidate : Candidate config opened index) (intent : DataIntent rootBytes) :
    Except String (Matched candidate intent) :=
  if same : recordMatches candidate.record intent = true then
    .ok ⟨candidate.record, rfl, (recordMatches_iff candidate.record intent).mp same⟩
  else .error "historical record differs from source-admitted intent"

/-! ## Prefixes the replay walk already holds

A lifecycle admission (claim, completion, failed START recovery, created) names
an earlier record and needs the exact opened prefix before it, and often the
one after it. `select` rebuilds such a prefix from genesis: the whole executor
replay, a full world-root tree and a full validation, once per selection and
several times per record. During a replay walk those prefixes were just
constructed, record by record. The walk retains the ones a later lifecycle
record can name (`NativeHostReplay.walk`), and `selectIO`/`loadPrefix` reuse
them.

This is a memo, never an authority: an entry is used only when its height,
log start and complete canonical image equal the requested prefix exactly
(the image comparison encodes both images) and it is a genesis replay
(`baseHeight = 0`, as every walk opening is); otherwise the genesis
reconstruction runs. A reused prefix is validated by the same `validateLoaded`.
Only the replay walk retains entries; the memo is bounded. -/

initialize retainedPrefixes : IO.Ref (List (DurableReceiverIO.Loaded rootBytes)) ←
  IO.mkRef []

/-- Bound on retained prefixes (each is a persistent opening sharing structure
with its neighbours). -/
def retainedPrefixBound : Nat := 512

/-- Retain one genesis-replayed prefix produced by the replay walk. -/
def retainPrefix (loaded : DurableReceiverIO.Loaded rootBytes) : IO Unit :=
  if loaded.baseHeight == 0 then
    retainedPrefixes.modify fun held => (loaded :: held).take retainedPrefixBound
  else pure ()

/-- The genesis-replayed Loaded of exactly `image`: a retained walk prefix
when one matches byte for byte, else `DurableReceiverIO.loadImage`. -/
def loadPrefix (logStart : Digest) (image : DurableReceiver.Image) :
    IO (Except String {loaded : DurableReceiverIO.Loaded rootBytes // loaded.image = image}) := do
  -- Operator measurement control (like MINI_AUDIT_TIMING): =1 forces the
  -- genesis reconstruction so one binary can time and diff both paths.
  let held ← if (← IO.getEnv "MINI_AUDIT_RECONSTRUCT_PREFIXES") == some "1" then pure []
    else retainedPrefixes.get
  let height := image.accepted.length
  let hit := held.find? fun loaded =>
    loaded.baseHeight == 0 && loaded.height == height &&
      loaded.logStart == logStart && decide (loaded.image = image)
  match hit with
  | some loaded =>
      if exact : loaded.image = image then return .ok ⟨loaded, exact⟩
      else return .error "retained prefix image differs"
  | none =>
      match built : DurableReceiverIO.loadImage rootBytes logStart image with
      | .error detail => return .error detail
      | .ok loaded => return .ok ⟨loaded, DurableReceiverIO.loadImage_image built⟩

/-- `select` through `loadPrefix`: the same candidate, the same validation and
refusals, without a genesis replay when the walk already holds the prefix. -/
def selectIO (config : Config) (opened : Opened config) (index : Nat) :
    IO (Except String (Candidate config opened index)) := do
  match found : opened.durable.image.accepted[index]? with
  | none => return .error "historical record index unavailable"
  | some record =>
      match ← loadPrefix opened.durable.logStart (prefixImage opened index) with
      | .error detail => return .error detail
      | .ok ⟨loaded, imageExact⟩ =>
          match validated : validateLoaded config loaded with
          | .error detail => return .error detail
          | .ok prior =>
              return .ok ⟨prior, record, found,
                (congrArg DurableReceiverIO.Loaded.image (validateLoaded_durable validated)).trans
                  imageExact⟩

/-! ## Bounded windows over the Store's verified records

Operator and validation paths that must compare or export a long run of
records read them through the `Reader` in windows of at most `windowSize`
records, handing each window to a step that either threads its state or
refuses. A `Refusal` surfaces by its message (it names the height); nothing is
mapped to "absent". Callers that carry a size bound stop inside `step`, so the
scan is bounded by the bound they state, not by the history. -/

def windowSize : Nat := 1024

def foldRange {root : List UInt8 → Digest} {store : Minidregg.Compiler.DurableHistory.StoreIdentity}
    {σ : Type}
    (reader : Minidregg.Compiler.DurableHistoryReader.Reader root store)
    (first last : Nat) (init : σ)
    (step : σ → List DurableReceiver.IntentRecord → Except String σ) :
    IO (Except String σ) := do
  let mut state := init
  let mut cursor := first
  for _ in List.range ((last + 1 - first) / windowSize + 1) do
    if cursor > last then break
    let upto := min last (cursor + windowSize - 1)
    match ← reader.range cursor upto with
    | .error refusal => return .error refusal.message
    | .ok reads =>
        match step state (reads.map (·.2.record)) with
        | .error detail => return .error detail
        | .ok next => state := next
    cursor := upto + 1
  return .ok state

end Minidregg.Kernel.NativeHistorySelection
