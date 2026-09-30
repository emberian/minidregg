/-
Derive one recipient ingress from the exact `source` field of a native fn
consumer projection. Host.Main owns the fn process, pinned scope, cursor and
event files. This helper only parses the bounded authored source and binds its
owner-signed Message-ID to the projection; it does not assert that fn delivered
anything or that Mini recipient admission will succeed.
-/
import Host.FnSelectiveReleaseAuthoring
import Kernel.FnSelectiveReleaseArticle

namespace Minidregg.Host.FnSelectiveReleaseFnReceiving

open Minidregg.Kernel.FnSelectiveReleaseSignature
open Minidregg.Kernel.FnSelectiveReleaseArticle

set_option autoImplicit false

structure Candidate where
  packetBytes : List UInt8
  ingressBytes : List UInt8
  messageId : List UInt8

def derive (projectedSource projectedMessageId : List UInt8)
    (capability : Minidregg.Theory.TypedAuthorization.CapabilityId)
    (targetRoot : Minidregg.Theory.TypedAuthorization.Digest) :
    Except String Candidate := do
  let article ← extract projectedSource
  unless article.packet.release.destination.messageId == projectedMessageId do
    throw "fn projected Message-ID differs from selected release"
  let packetBytes := packetCodec.encode article.packet
  let ingressBytes ← FnSelectiveReleaseAuthoring.assembleIngress packetBytes
    capability targetRoot
  pure ⟨packetBytes, ingressBytes, projectedMessageId⟩

end Minidregg.Host.FnSelectiveReleaseFnReceiving
