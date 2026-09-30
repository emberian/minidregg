/-
Strict operator JSON and receipt metadata for the read-only grain-origin
preparation command. The input names article bytes, signed target selection,
and whole-prefix disclosure intent; it does not convey signing keys or invoke
fn transport. The output describes exact prepared bytes, not publication.
-/
import Host.GrainOriginPreparation
import Host.Json
import Lean.Data.Json

namespace Minidregg.Host.GrainOriginCommand

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.Sp800185Cshake256

set_option autoImplicit false

structure Request where
  context : GrainOriginSource.ArticleContext
  selection : GrainOriginSource.Selection
  disclosureIntent : GrainOriginPreparation.DisclosureIntent

private def canonicalNat (name value : String) : Except String Nat := do
  let some parsed := value.toNat?
    | throw s!"grain origin {name} must be a canonical decimal string"
  unless toString parsed == value do
    throw s!"grain origin {name} must be a canonical decimal string"
  return parsed

/-- Main first uses the duplicate-key-rejecting `Host.Json.parse`. This
decoder then rejects missing and unknown fields and keeps large task IDs in
canonical decimal strings. -/
def decodeRequest (json : Lean.Json) : Except String Request := do
  let object ← json.getObj?
  let expected := ["fromMailbox", "group", "date", "subject",
    "messageIdDomain", "grainTask", "parentTask", "publicationTarget",
    "wholePrefixDisclosure", "destinationNewsgroup", "audienceAcknowledgement"]
  let actual := object.foldl (init := []) (fun fields key _ => key :: fields)
  unless actual.length == expected.length && actual.all expected.contains do
    throw "grain origin request has missing or unknown fields"
  let fromMailbox ← json.getObjValAs? String "fromMailbox"
  let group ← json.getObjValAs? String "group"
  let date ← json.getObjValAs? String "date"
  let subject ← json.getObjValAs? String "subject"
  let messageIdDomain ← json.getObjValAs? String "messageIdDomain"
  let grainTask ← canonicalNat "grainTask" (← json.getObjValAs? String "grainTask")
  let parentTask ← canonicalNat "parentTask" (← json.getObjValAs? String "parentTask")
  let publicationTarget ← canonicalNat "publicationTarget"
    (← json.getObjValAs? String "publicationTarget")
  let wholePrefixDisclosure ← json.getObjValAs? Bool "wholePrefixDisclosure"
  let destinationNewsgroup ← json.getObjValAs? String "destinationNewsgroup"
  let audienceAcknowledgement ← json.getObjValAs? String "audienceAcknowledgement"
  return ⟨⟨fromMailbox, group, date, subject, messageIdDomain⟩,
    ⟨grainTask, parentTask, publicationTarget⟩,
    ⟨wholePrefixDisclosure, destinationNewsgroup, audienceAcknowledgement⟩⟩

def sourceDigest (bytes : List UInt8) : List UInt8 :=
  cshake256Bytes "DREGG/FN/ORIGIN-SOURCE/v1".toUTF8.toList bytes

/-- The scope identifies what the local source contains. It does not claim
the Boolean acknowledgement authorizes release or constrain fn's later
readers after peering. -/
def scopeJson (prepared : GrainOriginPreparation.Prepared) : Lean.Json :=
  let scope := prepared.scope
  let rendered := prepared.rendered
  Lean.Json.mkObj
    [("type", toJson "verified-grain-origin-preparation-v1"),
     ("stage", toJson "prepared-local-source"),
     ("disclosureScope", toJson "full-genesis-and-all-accepted-records-through-original-receipt"),
     ("wholePrefixDisclosureIntent", toJson prepared.disclosureIntent.wholePrefixDisclosure),
     ("destinationNewsgroup", toJson scope.destinationNewsgroup),
     ("audienceAcknowledgement", toJson scope.audienceAcknowledgement),
     ("originDomain", toJson (toString scope.originDomain.value)),
     ("originSemantics", toJson (toString scope.originSemantics.value)),
     ("originGenesisPin", toJson (toString scope.originGenesisPin.value)),
     ("transactionId", toJson (toString scope.originalReceipt.transactionId.value)),
     ("eventId", toJson (toString scope.originalReceipt.eventId.value)),
     ("acceptedCount", toJson (toString scope.acceptedCount)),
     ("worldRoot", toJson (toString scope.originalReceipt.worldRoot.value)),
     ("packageLength", toJson scope.packageLength),
     ("packageDigest", toJson (Json.encodeHex scope.packageDigest)),
     ("prefixLength", toJson scope.prefixLength),
     ("prefixDigest", toJson (Json.encodeHex scope.prefixDigest)),
     ("sourceLength", toJson rendered.source.length),
     ("sourceDigest", toJson (Json.encodeHex (sourceDigest rendered.source))),
     ("fromMailbox", toJson rendered.context.fromMailbox),
     ("date", toJson rendered.context.date),
     ("group", toJson rendered.context.group),
     ("subject", toJson rendered.context.subject),
     ("messageIdDomain", toJson rendered.context.messageIdDomain),
     ("messageId", toJson rendered.messageId),
     ("grainTask", toJson (toString rendered.selection.grainTask)),
     ("parentTask", toJson (toString rendered.selection.parentTask)),
     ("publicationTarget", toJson (toString rendered.selection.publicationTarget)),
     ("signedTargets", toJson (rendered.signedTargets.map toString))]

end Minidregg.Host.GrainOriginCommand
