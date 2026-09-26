/-
Read-only, source-owned presentation of a Mini resource view. The caller
supplies the complete canonical view.bin produced by a native `mini query`
under its current observe grant; query authority is established by that
retained native attempt, not this pure decoder. This decoder does not admit a
foreign operation, rerun fn signatures, or apply its carried publication at B.
-/
import Host.Json
import Kernel.FnConsumerOperation

namespace Minidregg.Host.FnInboxView

open Lean
open Minidregg.Compiler
open Minidregg.Compiler.NativeHostCodec
open Minidregg.Kernel
open Minidregg.Kernel.FnConsumerOperation

private def number (n : Nat) : Json := toJson (toString n)
private def signed (n : Int) : Json := toJson (toString n)
private def hex (bytes : List UInt8) : Json := toJson (Minidregg.Host.Json.encodeHex bytes)

private def digit (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 97 + 10)
  else none

private def decodeHexChars (input : String) : Option (List UInt8) := Id.run do
  let chars := input.toUTF8
  if chars.size % 2 != 0 then return none
  let mut output := ByteArray.empty
  for i in [:chars.size / 2] do
    let some hi := digit (Char.ofNat chars[2 * i]!.toNat) | return none
    let some lo := digit (Char.ofNat chars[2 * i + 1]!.toNat) | return none
    output := output.push (UInt8.ofNat (16 * hi + lo))
  return some output.toList

private def receiptJson (receipt : NativeHostCodec.Receipt) : Json := .mkObj
  [("transactionId", number receipt.transactionId.value),
   ("eventId", number receipt.eventId.value),
   ("acceptedCount", number receipt.acceptedCount),
   ("imageBoundary", number receipt.imageBoundary.value)]

private def keyJson : Minidregg.Theory.EffectDeclaration.StateKey → Json
  | .objectField resource field => .mkObj
      [("type", toJson "object"), ("resource", number resource.value),
       ("field", number field.value)]
  | .accountBalance account resource => .mkObj
      [("type", toJson "account"), ("resource", number account.value),
       ("field", number resource.value)]
  | .programCode program => .mkObj
      [("type", toJson "program"), ("resource", number program.value)]

private def actionJson : Minidregg.Theory.DeclaredActionLowering.Action → Json
  | .create key value => .mkObj
      [("type", toJson "create"), ("key", keyJson key), ("value", signed value)]
  | .write key before after => .mkObj
      [("type", toJson "write"), ("key", keyJson key),
       ("expected", before.map signed |>.getD Json.null), ("replacement", signed after)]
  | .move source destination resource expectedSource expectedDestination amount => .mkObj
      [("type", toJson "move"), ("source", number source.value),
       ("destination", number destination.value), ("resource", number resource.value),
       ("expectedSource", expectedSource.map signed |>.getD Json.null),
       ("expectedDestination", expectedDestination.map signed |>.getD Json.null),
       ("amount", signed amount)]

private def targetJson (target : DeclaredResourceController.Target) : Json :=
  let kind := match target.kind with
    | .object => "object" | .account => "account" | .program => "program"
  let payload := match target.payload with
    | .scalar actions => .mkObj
        [("type", toJson "scalar"),
         ("actions", .arr (actions.toArray.map actionJson))]
    | .content command => .mkObj
        [("type", toJson "content"), ("actionCount", number command.actions.length)]
  .mkObj [("kind", toJson kind), ("target", number target.target),
    ("payload", payload)]

private def originJson (bytes : List UInt8) : Except String Json := do
  let package ← FnEvidenceCodec.decodeChecked bytes
  let some signedCall := callCodec.decode package.signedCall
    | throw "carried Mini origin call is noncanonical"
  let call ← match signedCall with
    | .birth ingressBytes => do
        let some ingress := ResourceBirthPolicyController.Concrete.ingressCodec.decode ingressBytes
          | throw "carried Mini birth ingress is noncanonical"
        let some descriptor := CanonicalCellRegistry.sourceEncoding.codec.decode ingress.descriptorBytes
          | throw "carried Mini birth descriptor is noncanonical"
        pure <| Json.mkObj
          [("type", toJson "birth"), ("exactIngressBytes", number ingressBytes.length),
           ("exactDescriptorBytes", number ingress.descriptorBytes.length),
           ("createdResourceCount", number descriptor.createRequests.length),
           ("resourceOperationCount", number descriptor.resourceBatch.operations.length)]
    | .invoke invocation => do
        let some command := DeclaredResourceController.commandCodec.decode invocation.commandBytes
          | throw "carried Mini invocation command is noncanonical"
        pure <| Json.mkObj
          [("type", toJson "invoke"), ("exactCommandBytes", number invocation.commandBytes.length),
           ("signedTargets", .arr (command.targets.toArray.map targetJson))]
    | .install ingressBytes => pure (Json.mkObj
        [("type", toJson "install"), ("exactIngressBytes", number ingressBytes.length)])
    | .delegate ingressBytes => pure (Json.mkObj
        [("type", toJson "delegate"), ("exactIngressBytes", number ingressBytes.length)])
    | .revoke ingressBytes => pure (Json.mkObj
        [("type", toJson "revoke"), ("exactIngressBytes", number ingressBytes.length)])
  pure <| .mkObj
    [("verification", toJson "decoded carried package; consult original B admission for historical verification"),
     ("domain", number package.domain.value),
     ("semantics", number package.semantics.value),
     ("genesisPin", number package.genesisPin.value),
     ("exactPackageBytes", number bytes.length),
     ("exactSignedCallBytes", number package.signedCall.length),
     ("exactAcceptedPrefixBytes", number package.acceptedPrefix.length),
     ("receipt", receiptJson package.originalReceipt),
     ("signedCall", call)]

private def typedAtom (schema : String) (payload : List UInt8) : Except String Json := do
  match schema with
  | "1" =>
      let some binding := bindingCodec.decode payload
        | throw "fn binding atom is noncanonical"
      let origin ← originJson binding.package
      let package ← FnEvidenceCodec.decodeChecked binding.package
      unless sameBytes binding.operation (originOperation package) &&
          sameBytes binding.reply.operation binding.operation &&
          sameBytes binding.reply.application binding.application &&
          sameBytes binding.reply.sourceIdentity binding.provenance.sourceIdentity &&
          decide (binding.reply.miniReceipt = package.originalReceipt) do
        throw "fn binding does not match its carried Mini origin"
      pure <| Json.mkObj
        [("type", toJson "binding"), ("applicationHex", hex binding.application),
         ("operationHex", hex binding.operation),
         ("sourceIdentity", hex binding.provenance.sourceIdentity),
         ("fnHistory", hex binding.provenance.history),
         ("fnIncarnation", hex binding.provenance.incarnation),
         ("fnVerdictRef", hex binding.provenance.fnVerdictRef),
         ("origin", origin)]
  | "2" =>
      let some reply := replyCodec.decode payload
        | throw "fn reply atom is noncanonical"
      pure <| Json.mkObj
        [("type", toJson "reply"), ("applicationHex", hex reply.application),
         ("operationHex", hex reply.operation),
         ("sourceIdentity", hex reply.sourceIdentity),
         ("carriedMiniReceipt", receiptJson reply.miniReceipt)]
  | "3" =>
      let some conflict := conflictCodec.decode payload
        | throw "fn conflict atom is noncanonical"
      pure <| Json.mkObj
        [("type", toJson "conflict"), ("applicationHex", hex conflict.application),
         ("operationHex", hex conflict.operation),
         ("sourceIdentity", hex conflict.provenance.sourceIdentity),
         ("origin", ← originJson conflict.package)]
  | "4" =>
      let some inbox := portableInboxCodec.decode payload
        | throw "fn portable inbox atom is noncanonical"
      pure <| Json.mkObj
        [("type", toJson "portableInbox"), ("sourceIdentity", hex inbox.sourceIdentity),
         ("principal", hex inbox.principal), ("edPublicKey", hex inbox.edPublicKey),
         ("mlPublicKey", hex inbox.mlPublicKey),
         ("exactCarrierBytes", number inbox.carrier.length)]
  | "5" =>
      let some poll := storePollCodec.decode payload
        | throw "fn Store poll atom is noncanonical"
      pure <| Json.mkObj
        [("type", toJson "storePollInbox"),
         ("pollCallObserved", toJson poll.pollCallObserved),
         ("sourceIdentity", hex poll.sourceIdentity),
         ("sequence", number poll.sequence),
         ("transactionId", number poll.transactionId),
         ("messageIdHex", hex poll.messageId),
         ("verdictPrincipal", hex poll.verdictPrincipal),
         ("exactEventBytes", number poll.event.length)]
  | _ => pure (Json.mkObj [("type", toJson "other"), ("schema", toJson schema),
      ("exactPayloadBytes", number payload.length)])

/-- Full canonical native resource view in; bounded typed summary out. The
retained native signed query and its `view.bin` remain the exact-byte evidence.
No atom or page entry is silently omitted from the summary. -/
def render (viewBin : List UInt8) : Except String Json := do
  let raw ← Minidregg.Host.Json.inspect "view-resource" viewBin
  let some page := (raw.getObjVal? "page").toOption
    | throw "native query returned no resource page"
  let some entries := (page.getObjVal? "entries").toOption.bind (·.getArr?.toOption)
    | throw "resource is not a content page"
  let mut summaries : Array Json := #[]
  for entry in entries do
    let some entryType := (entry.getObjValAs? String "type").toOption
      | throw "content page entry has no type"
    if entryType != "atom" then
      summaries := summaries.push <| .mkObj
        [("type", toJson entryType), ("id", (entry.getObjVal? "id").toOption.getD .null)]
    else
      let some kind := (entry.getObjVal? "kind").toOption
        | throw "content atom has no kind"
      let some schema := (kind.getObjValAs? String "schema").toOption
        | throw "content atom has no inline schema"
      let some payloadHex := (entry.getObjValAs? String "payload").toOption
        | throw "content atom has no payload"
      let some payload := decodeHexChars payloadHex
        | throw "content atom payload is not canonical lowercase hex"
      summaries := summaries.push <| .mkObj
        [("type", toJson "atom"), ("id", (entry.getObjVal? "id").toOption.getD .null),
         ("schema", toJson schema), ("typed", ← typedAtom schema payload)]
  pure <| .mkObj
    [("type", toJson "fn-inbox-resource-summary-v1"),
     ("resourceRoot", (page.getObjVal? "root").toOption.getD .null),
     ("contentDomain", (page.getObjVal? "contentDomain").toOption.getD .null),
     ("document", (page.getObjVal? "document").toOption.getD .null),
     ("pageNumber", (page.getObjVal? "pageNumber").toOption.getD .null),
     ("entryCount", number entries.size), ("entries", .arr summaries),
     ("interpretation", toJson
       "decoded B resource view and carried A evidence; consult retained signed query; remote publication is not a B mutation")]

end Minidregg.Host.FnInboxView
