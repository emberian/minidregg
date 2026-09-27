/-
Historical Mini admission selector for ACKing one fn selected-release poll.
The caller must first use the pinned native fn projection on the exact retained
cursor and event. This selector neither invokes fn nor ACKs a cursor. It reads
the accepted Mini event, rather than trusting a caller-supplied ingress or
receipt, and binds it to the projected owner-signed article.
-/
import Host.FnSelectiveReleaseFnReceiving
import Kernel.FnSelectiveReleaseReceiver
import Kernel.NativeHostReplay

namespace Minidregg.Host.FnSelectiveReleaseFnAck

open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.FnSelectiveReleaseIngress
open Minidregg.Kernel.FnSelectiveReleaseArticle

set_option autoImplicit false

structure Selected where
  private mk ::
  ingressBytes : List UInt8
  receipt : Minidregg.Compiler.NativeHostCodec.Receipt

/- The original event is selected only from a complete native-admitted replay.
An `Opened` image alone proves physical coherence, not that its retained
chronology was semantically admitted. The caller must refresh and verify the
current physical image before supplying this private-constructor witness. -/
def selectOriginal (config : Minidregg.Kernel.NativeHost.Config)
    (target : Minidregg.Kernel.NativeHost.Durable)
    (verified : Minidregg.Kernel.NativeHostReplay.Verified config target)
    (miniTransactionId : Digest)
    (projectedSource projectedMessageId : List UInt8) :
    Except String Selected := do
  let some record := Minidregg.Kernel.DurableCommitProtocol.Snapshot.lookupRecorded
      miniTransactionId verified.opened.durable.snapshot.model.journal
    | throw "selected release Mini transaction is absent"
  let event := record.event.event
  unless event.codecVersion == 13 do
    throw "Mini transaction is not a selected release event"
  let some ingress := ingressCodec.decode event.canonicalBytes
    | throw "accepted selected release event is noncanonical"
  unless transactionId ingress == miniTransactionId &&
      event == Minidregg.Kernel.FnSelectiveReleaseIngress.event ingress do
    throw "selected release event differs from accepted transaction"
  unless decide (Minidregg.Kernel.FnSelectiveReleaseReceiver.replay config verified.opened ingress =
      some (.ok (Minidregg.Kernel.FnSelectiveReleaseReceiver.receipt ingress))) do
    throw "selected release historical signed command differs"
  let article ← extract projectedSource
  unless article.packet.release.destination.messageId == projectedMessageId &&
      article.packet == ingress.packet do
    throw "fn projection differs from accepted selected release"
  let some historical := Minidregg.Kernel.NativeHost.historicalReceipt config
      verified.opened.durable miniTransactionId event.eventId
    | throw "selected release original receipt is unavailable"
  pure ⟨ingressCodec.encode ingress, historical⟩

end Minidregg.Host.FnSelectiveReleaseFnAck
