/- Generic consumer of actual source producer packet: the annotated checker
and whole-source demand/data/Plan pipeline consume exactly the SAME decoded
Term. Reports a proposal only; actual native admission is a separate receiver. -/
import Theory.ObjectiveBendTyping
import Compiler.ObjectiveBendPlanAdapter
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandData
open Minidregg.Compiler.ObjectiveBendPlanAdapter
open Lean (Json toJson)
def main (paths : List String) : IO UInt32 := do
  let [path] := paths | do IO.eprintln "one typed source packet required"; return 2
  let text ← IO.FS.readFile path
  let packetResult := do
    let json ← Json.parse text
    decodePacket json
  let .ok packet := packetResult | do IO.eprintln "source packet decode refused"; return 1
  if !packet.context.isEmpty then IO.eprintln "source packet must be closed"; return 1
  let some checked := check packet.source packet.context packet.fuel
    | do IO.eprintln "actual annotated checker refused"; return 1
  let .ok executed := execute ⟨8192,1024⟩ ⟨4096,4096,65536⟩ packet.source.term
    | do IO.eprintln "whole source/data budget or execution refused"; return 1
  let some proposal := decode executed.extraction.result.value
    | do IO.eprintln "exact scalar-record Plan ABI refused"; return 1
  let writes := proposal.effects.flatMap fun effect => effect.writes.map fun write =>
    Json.mkObj [("resource",toJson (toString effect.ref.resourceID)),
      ("root",toJson (toString effect.ref.root.value)),("field",toJson (toString write.field)),
      ("before",toJson (toString write.before)),("after",toJson (toString write.after))]
  IO.println ((Json.mkObj [("schema",toJson "dregg.objective-bend.scalar-proposal-check.v1"),
    ("sameDecodedTerm",toJson true),("actualTyping",toJson true),
    ("uses",toJson checked.uses),("reads",toJson (proposal.reads.map (fun r => toString r.resourceID))),
    ("writes",toJson writes),("remainingTicks",toJson (toString executed.extraction.result.remaining.ticks)),
    ("authority",toJson "none; proposal before native current-law admission")]).compress)
  return 0
