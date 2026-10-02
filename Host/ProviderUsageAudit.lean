/- Source-level regression facts for provider-metering admission data. The
general arithmetic proof is ProviderMetering.charge_rounding; these closed
inputs check the intended Chat Completions framing and refusal boundaries. -/
import Host.ProviderUsage

namespace Minidregg.Host.ProviderUsageAudit

open Minidregg.Host.ProviderUsage
open Minidregg.Kernel.ProviderMetering

set_option autoImplicit false

private def tariff : Tariff := ⟨1, "fixture", 4, ⟨2, 1000000, 2000000⟩, ⟨0, 1000000, 2000000⟩⟩
private def request : List UInt8 :=
  "{\"model\":\"fixture\",\"stream\":true}".toUTF8.toList
private def finished : String :=
  "data: {\"id\":\"a\",\"object\":\"chat.completion.chunk\",\"model\":\"fixture\",\"choices\":[{\"index\":0,\"finish_reason\":\"stop\"}]}"
private def metered : String :=
  "data: {\"id\":\"a\",\"object\":\"chat.completion.chunk\",\"model\":\"fixture\",\"choices\":[],\"usage\":{\"prompt_tokens\":1,\"completion_tokens\":2,\"total_tokens\":3}}"
private def complete : List UInt8 :=
  (": keepalive\r\n\r\n" ++ finished ++ "\r\n\r\n" ++ metered ++
    "\r\n\r\ndata: [DONE]\r\n\r\n").toUTF8.toList
private def truncated : List UInt8 :=
  (finished ++ "\n\n" ++ metered ++ "\n\ndata: [DONE]").toUTF8.toList
private def absent : List UInt8 :=
  (finished ++ "\n\ndata: [DONE]\n\n").toUTF8.toList

-- The provider may repeat its inert final choice on the sole usage event.
-- These synthetic counts and shape match the retained OpenRouter response.
private def echoChoice : String :=
  r#"{"index":0,"delta":{"content":"","role":"assistant"},"finish_reason":"stop","native_finish_reason":"stop"}"#
private def echoUsage : String :=
  r#", "usage":{"prompt_tokens":3042,"completion_tokens":38,"total_tokens":3080}"#
private def echoEvent (choice : String) (usage : String := "") : String :=
  r#"data: {"id":"a","object":"chat.completion.chunk","model":"fixture","choices":["# ++
    choice ++ "]" ++ usage ++ "}"
private def echoPrefix : String := echoEvent echoChoice ++ "\n\n"
private def doneFrame : String := "data: [DONE]\n\n"
private def echoStream (event : String) : String := echoPrefix ++ event ++ "\n\n" ++ doneFrame

private def checkTerminalEcho : IO Unit := do
  let terminal := echoEvent echoChoice echoUsage
  let positive := (quoteResponse tariff .pool request (echoStream terminal).toUTF8.toList
    "text/event-stream" 200 3120).map (fun quote => (quote.usage, quote.amount))
  unless positive == .ok (some ⟨3042, 38, 3080⟩, 3120) do
    throw (IO.userError s!"inert terminal echo changed: {repr positive}")
  let vectors : List (String × String × String) := [
    ("changed index", echoStream (terminal.replace r#""index":0"# r#""index":1"#),
      "SSE choice index is not zero"),
    ("changed reason", echoStream (terminal.replace r#""finish_reason":"stop""#
      r#""finish_reason":"length""#), "SSE terminal choice finish reason differs"),
    ("new text", echoStream (terminal.replace r#""content":"""# r#""content":"later""#),
      "SSE terminal choice delta is not inert"),
    ("tool delta", echoStream (terminal.replace r#""content":"""# r#""tool_calls":[]"#),
      "SSE terminal choice delta is not inert"),
    ("function delta", echoStream (terminal.replace r#""content":"""# r#""function_call":{}"#),
      "SSE terminal choice delta is not inert"),
    ("audio delta", echoStream (terminal.replace r#""content":"""# r#""audio":{}"#),
      "SSE terminal choice delta is not inert"),
    ("changed role", echoStream (terminal.replace r#""role":"assistant""# r#""role":"user""#),
      "SSE terminal choice delta is not inert"),
    ("extra choice output", echoStream (terminal.replace r#""index":0"# r#""index":0,"text":"later""#),
      "SSE terminal choice contains extra output"),
    ("changed model", echoStream (terminal.replace r#""model":"fixture""# r#""model":"other""#),
      "response model differs from the operator tariff"),
    ("changed generation", echoStream (terminal.replace r#""id":"a""# r#""id":"b""#),
      "SSE completion ids differ"),
    ("multiple indices", echoStream (echoEvent (echoChoice ++ "," ++ echoChoice) echoUsage),
      "SSE choices contain multiple indices"),
    ("duplicate usage", echoPrefix ++ terminal ++ "\n\n" ++ terminal ++ "\n\n" ++ doneFrame,
      "SSE data follows terminal usage"),
    ("data after done", echoStream terminal ++ terminal ++ "\n\n",
      "SSE data follows terminal usage"),
    ("absent terminator", echoPrefix ++ terminal ++ "\n\ndata: [DONE]",
      "SSE final data event lacks a blank-line terminator"),
    ("nonterminal usage", (echoEvent (echoChoice.replace r#""finish_reason":"stop""#
      r#""finish_reason":null"#) echoUsage) ++ "\n\n" ++ doneFrame,
      "usage precedes finish reason"),
    ("echo without usage", echoStream (echoEvent echoChoice), "missing usage")]
  for (label, response, expected) in vectors do
    let result := (quoteResponse tariff .pool request response.toUTF8.toList
      "text/event-stream" 200 3120).map (·.amount)
    unless result == .error expected do
      throw (IO.userError s!"terminal echo {label} changed: {repr result}")

/-- Executable parser regression gate. Its closed examples do not replace the
general arithmetic theorem in `Kernel.ProviderMetering`. It raises an error
during this module's narrow Lean check if any framing/refusal result changes. -/
def check : IO Unit := do
  checkTerminalEcho
  let positive := (quoteResponse tariff .pool request complete
    "text/event-stream; charset=UTF-8" 200 7).map (·.amount)
  unless positive == .ok 7 do
    throw (IO.userError s!"complete stream changed: {repr positive}")
  let truncatedResult := (quoteResponse tariff .pool request truncated
    "text/event-stream" 200 5).map (·.amount)
  unless truncatedResult == .error "SSE final data event lacks a blank-line terminator" do
    throw (IO.userError s!"truncated stream changed: {repr truncatedResult}")
  let absentResult := (quoteResponse tariff .pool request absent
    "text/event-stream" 200 5).map (·.amount)
  unless absentResult == .error "SSE completion lacks one terminal usage record" do
    throw (IO.userError s!"missing usage changed: {repr absentResult}")
  let overResult := (quoteResponse tariff .pool request complete
    "text/event-stream" 200 6).map (·.amount)
  unless overResult == .error "reported usage quote exceeds the held allowance or tariff bound" do
    throw (IO.userError s!"over-reserve changed: {repr overResult}")
  -- The user route charges the fee alone, reads no usage, and refuses a hold
  -- below the fee.
  let user := (quoteResponse tariff .user request absent "text/plain" 429 4).map (·.amount)
  unless user == .ok 4 do
    throw (IO.userError s!"user fee changed: {repr user}")
  let userOver := (quoteResponse tariff .user request complete
    "text/event-stream" 200 3).map (·.amount)
  unless userOver == .error "reported usage quote exceeds the held allowance or tariff bound" do
    throw (IO.userError s!"user over-reserve changed: {repr userOver}")

#eval check

end Minidregg.Host.ProviderUsageAudit
