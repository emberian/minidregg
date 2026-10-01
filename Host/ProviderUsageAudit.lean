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

/-- Executable parser regression gate. Its closed examples do not replace the
general arithmetic theorem in `Kernel.ProviderMetering`. It raises an error
during this module's narrow Lean check if any framing/refusal result changes. -/
def check : IO Unit := do
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
