/-
Strict source-owned presentation of provider-reported usage from the exact
retained Chat Completions request and response. A valid report is a configured
tariff quote over provider-asserted counts, not an invoice attestation or Mini
admission verdict. Missing or ambiguous usage refuses construction.
-/
import Host.Json
import Kernel.ProviderMetering

namespace Minidregg.Host.ProviderUsage

open Lean
open Minidregg.Kernel
open Minidregg.Kernel.ProviderMetering

set_option autoImplicit false

abbrev Result := Except String

private def field (json : Json) (name : String) : Result Json :=
  (json.getObjVal? name).mapError (fun _ => s!"missing {name}")

private def stringField (json : Json) (name : String) : Result String := do
  (← field json name).getStr?.mapError (fun _ => s!"{name} must be a string")

private def canonicalNat (json : Json) (name : String) : Result Nat := do
  let value ← stringField json name
  if value.length > 20 then throw s!"{name} exceeds decimal width"
  match value.toNat? with
  | some n =>
      if toString n = value then pure n
      else .error s!"{name} must be canonical decimal"
  | none => .error s!"{name} must be canonical decimal"

/-- The tariff is fixed controller configuration. Only source-owned canonical
decimal parsing can turn it into arithmetic. -/
def parseTariff (source : String) : Result Tariff := do
  let json ← Minidregg.Host.Json.parse source
  let obj ← json.getObj?.mapError (fun _ => "tariff must be an object")
  let expected := ["version", "model", "inputMicroPerMillion", "outputMicroPerMillion"]
  let actual := obj.foldl (init := []) (fun names key _ => key :: names)
  unless actual.length = expected.length && actual.all expected.contains do
    throw "tariff fields differ from the four-field v1 schema"
  let tariff : Tariff := {
    version := ← canonicalNat json "version"
    model := ← stringField json "model"
    inputMicroPerMillion := ← canonicalNat json "inputMicroPerMillion"
    outputMicroPerMillion := ← canonicalNat json "outputMicroPerMillion" }
  unless 0 < tariff.version && 0 < tariff.model.toUTF8.size &&
      tariff.model.toUTF8.size ≤ 256 &&
      tariff.inputMicroPerMillion ≤ maxRate &&
      tariff.outputMicroPerMillion ≤ maxRate do
    throw "tariff version, model, or rate exceeds the v1 bound"
  pure tariff

private def usageOfJson (json : Json) : Result Usage := do
  let usage : Usage := {
    promptTokens := ← (← field json "prompt_tokens").getNat?.mapError
      (fun _ => "prompt_tokens must be an unsigned JSON integer")
    completionTokens := ← (← field json "completion_tokens").getNat?.mapError
      (fun _ => "completion_tokens must be an unsigned JSON integer")
    totalTokens := ← (← field json "total_tokens").getNat?.mapError
      (fun _ => "total_tokens must be an unsigned JSON integer") }
  unless usage.totalTokens == usage.promptTokens + usage.completionTokens &&
      usage.promptTokens ≤ maxReportedTokens &&
      usage.completionTokens ≤ maxReportedTokens do
    throw "reported usage is inconsistent or exceeds the token bound"
  pure usage

private def textOfBytes (label : String) (bytes : List UInt8) (limit : Nat) : Result String := do
  if bytes.length > limit then throw s!"{label} exceeds byte bound"
  match String.fromUTF8? bytes.toByteArray with
  | some value => pure value
  | none => throw s!"{label} is not UTF-8"

private def parseRequest (tariff : Tariff) (bytes : List UInt8) : Result Bool := do
  let text ← textOfBytes "request" bytes 1048576
  let json ← Minidregg.Host.Json.parse text
  unless (← stringField json "model") = tariff.model do
    throw "request model differs from the operator tariff"
  let streaming ← match json.getObjVal? "stream" with
    | .ok value => value.getBool?.mapError (fun _ => "stream must be boolean")
    | .error _ => pure false
  match json.getObjVal? "n" with
  | .ok count =>
      unless count.getNat?.toOption == some 1 do
        throw "only one Chat Completion choice is metered"
  | .error _ => pure ()
  pure streaming

private def checkModel (tariff : Tariff) (json : Json) : Result Unit := do
  unless (← stringField json "model") = tariff.model do
    throw "response model differs from the operator tariff"

private def parseJsonResponse (tariff : Tariff) (text : String) : Result Usage := do
  let json ← Minidregg.Host.Json.parse text
  checkModel tariff json
  unless (← stringField json "object") = "chat.completion" do
    throw "response is not a Chat Completion"
  if (← stringField json "id").isEmpty then
    throw "response completion id is empty"
  let choices ← (← field json "choices").getArr?.mapError
    (fun _ => "choices must be an array")
  unless choices.size = 1 do throw "exactly one Chat Completion choice required"
  let choice := choices[0]!
  unless (← field choice "index").getNat?.toOption == some 0 do
    throw "choice index is not zero"
  let finish ← stringField choice "finish_reason"
  if finish.isEmpty then throw "completion finish reason is empty"
  usageOfJson (← field json "usage")

private def fieldValue (line : String) : String × String :=
  let parts := line.splitOn ":"
  let name := parts.head!
  let value := String.intercalate ":" parts.tail
  let value := if value.startsWith " " then String.ofList (value.toList.drop 1) else value
  (name, value)

/-- WHATWG SSE allows comment-only keepalives and multiple data lines per
event. The exact original bytes remain in Quote; framing normalization only
selects the JSON payload. -/
private def dataPayload (frame : String) : Result (Option String) := do
  let mut data : List String := []
  for line in frame.splitOn "\n" do
    if line.isEmpty || line.startsWith ":" then continue
    let (name, value) := fieldValue line
    if name = "data" then
      data := value :: data
    else if name = "event" then
      if value = "error" then throw "SSE error event"
    else if name = "id" then
      if value.contains (Char.ofNat 0) then throw "SSE id contains NUL"
    else if name = "retry" then
      pure ()
    else
      pure ()
  if data.isEmpty then pure none
  else pure (some (String.intercalate "\n" data.reverse))

private def mediaType (source : String) : Result String := do
  let parts := source.toLower.splitOn ";"
  match parts with
  | [base] => pure base.trimAscii.toString
  | [base, parameter] =>
      unless parameter.trimAscii.toString = "charset=utf-8" do
        throw "unsupported Content-Type parameter"
      pure base.trimAscii.toString
  | _ => throw "ambiguous Content-Type parameters"

/-- Accept a complete stream with exactly one terminal usage event, after a
finish reason and immediately before [DONE]. No usage is inferred from deltas. -/
private def parseSseResponse (tariff : Tariff) (text : String) : Result Usage := do
  let normalized := (text.replace "\r\n" "\n").replace "\r" "\n"
  let normalized := if normalized.startsWith (String.ofList [Char.ofNat 65279]) then
      String.ofList (normalized.toList.drop 1) else normalized
  let segments := normalized.splitOn "\n\n"
  let suffix := segments[segments.length - 1]!
  if !(← dataPayload suffix).isNone then
    throw "SSE final data event lacks a blank-line terminator"
  let frames := (segments.take (segments.length - 1)).filter (· != "")
  if frames.isEmpty || frames.length > 4096 then
    throw "SSE frame count outside bound"
  let mut finished := false
  let mut done := false
  let mut usage : Option Usage := none
  let mut completionId : Option String := none
  for frame in frames do
    let some payload ← dataPayload frame | continue
    if payload = "[DONE]" then
      if done || !finished || usage.isNone then
        throw "SSE completion lacks one terminal usage record"
      done := true
    else
      if done || usage.isSome then throw "SSE data follows terminal usage"
      let event ← Minidregg.Host.Json.parse payload
      checkModel tariff event
      unless (← stringField event "object") = "chat.completion.chunk" do
        throw "SSE event is not a Chat Completion chunk"
      let eventId ← stringField event "id"
      if eventId.isEmpty || completionId.isSome && completionId != some eventId then
        throw "SSE completion ids differ"
      completionId := some eventId
      let choices ← (← field event "choices").getArr?.mapError
        (fun _ => "SSE choices must be an array")
      if choices.isEmpty then
        unless finished do throw "usage precedes finish reason"
        usage := some (← usageOfJson (← field event "usage"))
      else
        if finished || choices.size != 1 then
          throw "SSE choices continue after finish or contain multiple indices"
        for choice in choices do
          unless (← field choice "index").getNat?.toOption == some 0 do
            throw "SSE choice index is not zero"
          let reason ← field choice "finish_reason"
          if reason != .null then
            let name ← reason.getStr?.mapError (fun _ => "finish_reason must be a string")
            if name.isEmpty then throw "empty finish_reason"
            finished := true
          match event.getObjVal? "usage" with
          | .ok value =>
              if value != .null then
                unless finished do throw "usage precedes finish reason"
                usage := some (← usageOfJson value)
          | .error _ => pure ()
  unless done do throw "SSE [DONE] marker absent"
  match usage with
  | some observed => pure observed
  | none => throw "SSE terminal usage absent"

/-- This function consumes retained exact bytes, not worker-supplied counts.
The caller must separately pin the quote's reserve to the signed provider hold
and submit the generated operation through ordinary Mini admission. -/
def quoteResponse (tariff : Tariff) (request response : List UInt8)
    (contentType : String) (status reserve : Nat) : Result Quote := do
  unless status = 200 do throw "provider HTTP status is not 200"
  let streaming ← parseRequest tariff request
  let text ← textOfBytes "response" response 8388608
  let contentType ← mediaType contentType
  let usage ← if streaming then
      if contentType != "text/event-stream" then
        throw "stream response content type differs"
      parseSseResponse tariff text
    else
      if contentType != "application/json" then
        throw "JSON response content type differs"
      parseJsonResponse tariff text
  match prepare tariff usage request response reserve with
  | some quote => pure quote
  | none => throw "reported usage quote exceeds the held allowance or tariff bound"

/-- Bounded typed projection. The request/response files remain the exact
evidence; digest equality is a collision-resistance assumption, not a proof of
provider truth. -/
def reportJson (providerResourceId : Nat) (quote : Quote) : Json :=
  .mkObj [
    ("type", toJson "minidregg-provider-metering-v1"),
    ("status", toJson "quoted-reported-usage"),
    ("providerResourceId", toJson (toString providerResourceId)),
    ("model", toJson quote.tariff.model),
    ("tariffVersion", toJson (toString quote.tariff.version)),
    ("tariffDigest", toJson (toString (tariffDigest quote.tariff).value)),
    ("requestDigest", toJson (toString (requestDigest quote.request).value)),
    ("responseDigest", toJson (toString (responseDigest quote.response).value)),
    ("requestBytes", toJson (toString quote.request.length)),
    ("responseBytes", toJson (toString quote.response.length)),
    ("promptTokens", toJson (toString quote.usage.promptTokens)),
    ("completionTokens", toJson (toString quote.usage.completionTokens)),
    ("totalTokens", toJson (toString quote.usage.totalTokens)),
    ("reserve", toJson (toString quote.reserve)),
    ("charge", toJson (toString quote.amount)),
    ("operation", .mkObj [("type", toJson "settle"),
      ("charge", toJson (toString quote.amount))]),
    ("claim", toJson "provider-reported usage under operator tariff; not invoice-verified")]

private def splitPairBounded (payload : List UInt8) (maximum : Nat) :
    Result (List UInt8 × List UInt8) := do
  if payload.length < 4 then throw "short provider metering pair"
  let width := payload[0]!.toNat + 256 * payload[1]!.toNat +
    65536 * payload[2]!.toNat + 16777216 * payload[3]!.toNat
  if width = 0 || width > maximum || width > payload.length - 4 then
    throw "provider metering pair exceeds bound"
  pure ((payload.drop 4).take width, payload.drop (4 + width))

/-- Read-only socket op payload: u32LE metadata length, strict metadata JSON,
u32LE exact request length, exact request bytes, then exact response bytes.
The Host Settings supply tariff and providerResourceId; neither comes from the
request. Its v1 metadata is {status,contentType,reserve}, decimal strings for
integers. No provider key or Mini signer enters this operation. -/
def quotePayload (providerResourceId : Nat) (tariff : Tariff)
    (payload : List UInt8) : Result Json := do
  let (metadataBytes, remainder) ← splitPairBounded payload 4096
  let (request, response) ← splitPairBounded remainder 1048576
  if response.isEmpty || response.length > 8388608 then
    throw "provider metering response exceeds byte bound"
  let metadataText ← textOfBytes "metadata" metadataBytes 4096
  let metadata ← Minidregg.Host.Json.parse metadataText
  let obj ← metadata.getObj?.mapError (fun _ => "metadata must be an object")
  let expected := ["status", "contentType", "reserve"]
  let actual := obj.foldl (init := []) (fun names key _ => key :: names)
  unless actual.length = expected.length && actual.all expected.contains do
    throw "provider metering metadata differs from the v1 schema"
  let status ← canonicalNat metadata "status"
  let contentType ← stringField metadata "contentType"
  let reserve ← canonicalNat metadata "reserve"
  let quote ← quoteResponse tariff request response contentType status reserve
  pure (reportJson providerResourceId quote)

end Minidregg.Host.ProviderUsage
