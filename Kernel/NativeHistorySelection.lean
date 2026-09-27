/-
Conditional selection of one original record and its exact prefix from a
physically loaded Mini image. This lower module does not certify that earlier
records were semantically admitted and exposes no commit or host permit. The
upper native history verifier supplies that separate inductive provenance.
-/
import Kernel.NativeHostContext

namespace Minidregg.Kernel.NativeHistorySelection

open Minidregg.Compiler
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Kernel.NativeHost

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
  priorBytesExact : prior.durable.bytes = DurableReceiverCodec.encode (prefixImage opened index)

def select (config : Config) (opened : Opened config) (index : Nat) :
    Except String (Candidate config opened index) := do
  match found : opened.durable.image.accepted[index]? with
  | none => .error "historical record index unavailable"
  | some record => do
      let bytes := DurableReceiverCodec.encode (prefixImage opened index)
      let loaded ← DurableReceiverIO.loadBytes rootBytes bytes
      let prior ← validateLoaded config loaded
      if exact : prior.durable.bytes = bytes then
        return ⟨prior, record, found, exact⟩
      else .error "historical prefix bytes changed"

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

end Minidregg.Kernel.NativeHistorySelection
