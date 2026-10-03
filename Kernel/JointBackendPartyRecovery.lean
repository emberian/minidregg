/- Retained-prefix source authority for restarting a designated backend worker.
The producer reads actual protected Store, reconstructs historical current native
admission, checks the entire accepted record and retains the full certified
history. Receipt decoding or present-day manifest selection cannot mint this. -/
import Kernel.JointBackendPartyReceiver
import Kernel.NativeHostReplay
import Compiler.GenericSimplexNative
namespace Minidregg.Kernel.JointBackendPartyRecovery
open Minidregg.Compiler
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
open Minidregg.Compiler.JointBackendPartyCodec
open Minidregg.Kernel.DurableReceiver
open Minidregg.Kernel.NativeHost
set_option autoImplicit false

structure Recovered (config : Config) (expected : Context) (index : Nat)
    (request : JointBackendPartyCodec.Request) where
  private mk ::
  contextPinned : config.jointConsensus = some expected
  target : Durable
  selection : NativeHostReplay.VerifiedSelection config target index
  pin : EndpointPin
  endpointExact : config.privatePartyEndpoint = some pin
  admitted : JointBackendPartyReceiver.Admitted config selection.selected.before pin request
  recordExact : IntentRecord.ofIntent admitted.intent = selection.selected.record
  ordered : JointReceiver.Ordered expected selection.selected.before.durable admitted.intent

/-- Takes an INTERNAL verified full commitment, not certificate bytes, a roster
from a packet, or a verification callback. The native ingress must verify raw
certificate bytes with its own configured deployment-pinned crypto producer. -/
def recover (config : Config) (expected : Context) (index : Nat)
    (request : JointBackendPartyCodec.Request) (commitment : VerifiedCommit expected) :
    IO (Except String (Recovered config expected index request)) := do
  if pinned : config.jointConsensus = some expected then
    match endpointExact : config.privatePartyEndpoint with
    | none => return .error "private-party endpoint disabled"
    | some pin =>
      match ← DurableReceiverIO.load config.physicalTransport ResourceBirthCodec.rootBytes with
      | .error detail => return .error detail
      | .ok target =>
        match ← NativeHostReplay.verifyLoadedSelected config target index with
        | .error failure => return .error s!"original source audit failed at {failure.index}: {failure.detail}"
        | .ok selection =>
          match ← JointBackendPartyReceiver.admit config selection.selected.before pin request with
          | .error detail => return .error detail
          | .ok admitted =>
            if same : DurableReceiverCodec.intentStream.encode (IntentRecord.ofIntent admitted.intent) =
                DurableReceiverCodec.intentStream.encode selection.selected.record then
              have recordExact : IntentRecord.ofIntent admitted.intent = selection.selected.record :=
                DurableReceiverCodec.intentStream.toLawful.encode_injective same
              match ordered : JointReceiver.order expected selection.selected.before.durable admitted.intent commitment with
              | none => return .error "full certified history does not cover exact original source dispatch"
              | some order => return .ok ⟨pinned,target,selection,pin,endpointExact,admitted,recordExact,order⟩
            else return .error "original source dispatch differs from complete re-admitted record"
  else return .error "unconfigured source consensus context"

/-- Actual byte-ingress verifier. `native` is the closed host deployment's
operator-pinned helper/settings object, never parsed from a request or supplied
as a Crypto callback. Full expected roster/context is checked against Config.
The verified certificate stays unchanged for ancestor-prefix recovery. -/
def recoverCertificateBytes (config : Config) (native : GenericSimplexNative.Native)
    (expected : Context) (index : Nat) (request : JointBackendPartyCodec.Request)
    (certificateBytes : List UInt8) : IO (Except String (Recovered config expected index request)) := do
  if config.jointConsensus != some expected then
    return .error "unconfigured source consensus context"
  let some commitment ← GenericSimplexIO.verifyCommittedBytes
      (GenericSimplexNative.crypto native) expected certificateBytes
    | return .error "invalid full source commitment certificate"
  recover config expected index request commitment

/-- Exact private configured-worker argument projections. These bytes are
claims outside this private native token and cannot construct Recovered. -/
def Recovered.requestBytes {config : Config} {expected : Context} {index : Nat}
    {request : JointBackendPartyCodec.Request} (_r : Recovered config expected index request) : List UInt8 :=
  JointBackendPartyCodec.requestBytes request

def Recovered.enrollmentBytes {config : Config} {expected : Context} {index : Nat}
    {request : JointBackendPartyCodec.Request} (r : Recovered config expected index request) : List UInt8 :=
  enrollmentStream.encode r.admitted.prepared.row

def Recovered.sourceRecordBytes {config : Config} {expected : Context} {index : Nat}
    {request : JointBackendPartyCodec.Request} (r : Recovered config expected index request) : List UInt8 :=
  DurableCheckpointCodec.recordFrame.encode r.selection.selected.record

def Recovered.sourceReceiptBytes {config : Config} {expected : Context} {index : Nat}
    {request : JointBackendPartyCodec.Request} (r : Recovered config expected index request) : List UInt8 :=
  NativeHostCodec.receiptStream.encode r.selection.selected.receipt

def Recovered.commitmentBytes {config : Config} {expected : Context} {index : Nat}
    {request : JointBackendPartyCodec.Request} (r : Recovered config expected index request) : List UInt8 :=
  r.ordered.commitment.bytes

theorem recovered_dispatch_at_exact_index {config : Config} {expected : Context} {index : Nat}
    {request : JointBackendPartyCodec.Request} (r : Recovered config expected index request) :
    r.target.image.accepted[index]? = some (IntentRecord.ofIntent r.admitted.intent) := by
  rw [r.recordExact]
  exact r.selection.record_at

theorem recovered_full_history_covers_original {config : Config} {expected : Context} {index : Nat}
    {request : JointBackendPartyCodec.Request} (r : Recovered config expected index request) :
    (JointReceiver.sourcePrefix r.selection.selected.before.durable ++
      [JointReceiver.sourcePayload r.admitted.intent]).IsPrefix
        (r.ordered.commitment.block.filter (fun b => !b.isEmpty)) := r.ordered.sourceOrdered
#assert_axioms recovered_dispatch_at_exact_index
#assert_axioms recovered_full_history_covers_original
end Minidregg.Kernel.JointBackendPartyRecovery
