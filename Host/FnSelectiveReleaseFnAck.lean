/-
Historical Mini admission selector for ACKing one fn selected-release poll.
The caller must first use the pinned native fn projection on the exact retained
cursor and event. This selector neither invokes fn nor ACKs a cursor. It reads
the accepted Mini event, rather than trusting a caller-supplied ingress or
receipt, and binds it to the projected owner-signed article.
-/
module

public import Host.FnSelectiveReleaseFnReceiving
public import Kernel.FnSelectiveReleaseReceiver
public import Kernel.NativeHostLight

-- Bodies this file reduces or derives through, not exposed by their modules (module system).
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.ToString.Extra
import all Init.Data.Array.Basic
import all Init.Data.ByteArray.Basic
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Control.Except
import all Init.Data.List.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.Format.Basic
import all Init.Data.List.Scan.Basic

@[expose] public section

namespace Minidregg.Host.FnSelectiveReleaseFnAck

open Minidregg.Compiler
open Minidregg.Theory.TypedAuthorization
open Minidregg.Kernel.FnSelectiveReleaseIngress
open Minidregg.Kernel.FnSelectiveReleaseArticle

set_option autoImplicit false

structure Selected where
  private mk ::
  ingressBytes : List UInt8
  receipt : Minidregg.Compiler.NativeHostCodec.Receipt

private def selectRecord (config : Minidregg.Kernel.NativeHost.Config)
    (miniTransactionId : Digest)
    (projectedSource projectedMessageId : List UInt8)
    (record : Minidregg.Kernel.DurableReceiver.IntentRecord)
    (historical : Minidregg.Compiler.NativeHostCodec.Receipt) :
    Except String Selected := do
  let event := record.event
  unless event.codecVersion == 13 do
    throw "Mini transaction is not a selected release event"
  let some ingress := ingressCodec.decode event.canonicalBytes
    | throw "accepted selected release event is noncanonical"
  unless transactionId ingress == miniTransactionId &&
       record.transactionId == transactionId ingress &&
       event == Minidregg.Kernel.FnSelectiveReleaseIngress.event ingress do
    throw "selected release event differs from accepted transaction"
  unless record.nullifiers ==
      [Minidregg.Kernel.FnSelectiveReleaseReceiver.ordinaryNullifier config ingress,
       releaseNullifier ingress.packet.release] do
    throw "selected release historical signed command differs"
  let article ← extract projectedSource
  unless article.packet.release.destination.messageId == projectedMessageId &&
      article.packet == ingress.packet do
    throw "fn projection differs from accepted selected release"
  pure ⟨ingressCodec.encode ingress, historical⟩

def selectOriginalLight (config : Minidregg.Kernel.NativeHost.Config)
    (light : Minidregg.Kernel.NativeHostLight.Light config)
    (miniTransactionId : Digest)
    (projectedSource projectedMessageId : List UInt8) :
    IO (Except String Selected) := do
  let reader := light.opening.reader config.transport ResourceBirthCodec.rootBytes
  let found ← match ← reader.byTx miniTransactionId with
    | .error refusal => return .error refusal.message
    | .ok (.absent _) => return .error "selected release Mini transaction is absent"
    | .ok (.present found) => pure found
  return selectRecord config miniTransactionId projectedSource projectedMessageId
    found.read.record (Minidregg.Kernel.NativeHost.receiptOfFound miniTransactionId found)

end Minidregg.Host.FnSelectiveReleaseFnAck
