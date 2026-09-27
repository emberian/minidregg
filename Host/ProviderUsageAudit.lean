/- Source-level regression facts for provider-metering admission data. The
general arithmetic proof is ProviderMetering.charge_rounding; these closed
inputs check the intended Chat Completions framing and refusal boundaries. -/
import Host.ProviderUsage

namespace Minidregg.Host.ProviderUsageAudit

open Minidregg.Host.ProviderUsage
open Minidregg.Kernel.ProviderMetering

set_option autoImplicit false

private def tariff : Tariff := ⟨1, "fixture", 1000000, 2000000⟩
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

/-- Executable parser regression gate. Its closed examples do not replace the
general arithmetic theorem in `Kernel.ProviderMetering`. It raises an error
during this module's narrow Lean check if any framing/refusal result changes. -/
def check : IO Unit := do
  let positive := (quoteResponse tariff request complete
    "text/event-stream; charset=UTF-8" 200 5).map (·.amount)
  unless positive == .ok 5 do
    throw (IO.userError s!"complete stream changed: {repr positive}")
  let truncatedResult := (quoteResponse tariff request truncated
    "text/event-stream" 200 5).map (·.amount)
  unless truncatedResult == .error "SSE final data event lacks a blank-line terminator" do
    throw (IO.userError s!"truncated stream changed: {repr truncatedResult}")
  let absentResult := (quoteResponse tariff request absent
    "text/event-stream" 200 5).map (·.amount)
  unless absentResult == .error "SSE completion lacks one terminal usage record" do
    throw (IO.userError s!"missing usage changed: {repr absentResult}")
  let overResult := (quoteResponse tariff request complete
    "text/event-stream" 200 4).map (·.amount)
  unless overResult == .error "reported usage quote exceeds the held allowance or tariff bound" do
    throw (IO.userError s!"over-reserve changed: {repr overResult}")

#eval check

end Minidregg.Host.ProviderUsageAudit
