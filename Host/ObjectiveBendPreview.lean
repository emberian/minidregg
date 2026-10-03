/- Generic typed clear preview: the checker and executor consume the SAME
actual decoded core term. No generated Lean source interpreter, output oracle,
current native authority or effect receipt is introduced. -/
import Theory.ObjectiveBendTyping
import Theory.ObjectiveBendDemandMachine

namespace Minidregg.Host.ObjectiveBendPreview
open Lean (Json toJson)
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine
set_option autoImplicit false

def natural (json : Json) (key : String) : Except String Nat := do
  let value ← jsonNat (← json.getObjVal? key)
  if value = 0 || value > 100000 then throw ("preview capacity refused: " ++ key)
  pure value

def valueJson : RuntimeValue → Json
  | .boolean value => Json.mkObj [("tag",toJson "boolean"),("value",toJson value)]
  | .natural value => Json.mkObj [("tag",toJson "natural"),("value",toJson (toString value))]
  | .label value => Json.mkObj [("tag",toJson "label"),("value",toJson value)]
  | .closure _ _ => Json.mkObj [("tag",toJson "closure"),("status",toJson "unforced body")]
  | .record fields => Json.mkObj [("tag",toJson "record"),("fields",toJson (fields.map Prod.fst))]
  | .specification _ _ => Json.mkObj [("tag",toJson "specification"),("status",toJson "unforced extension")]
  | .prototype _ _ => Json.mkObj [("tag",toJson "prototype"),("status",toJson "unforced target")]

/-- Receives an actual annotated packet; typing and bounded demand use exactly
packet.source.term. A Boolean assertion supplied by the caller cannot replace
its Checked proof-producing result. -/
def preview (typed limits : Json) : Except String Json := do
  let packet ← decodePacket typed
  if !packet.context.isEmpty then throw "preview requires a closed source context"
  let heap ← natural limits "heap"
  let stack ← natural limits "stack"
  let ticks ← natural limits "ticks"
  let some checked := check packet.source packet.context packet.fuel
    | throw "annotated typing/ownership refused or checker budget insufficient"
  let outcome := runBounded ⟨heap,stack⟩ ticks (initial packet.source.term)
  let state := match outcome with
    | .finished _ state | .suspended _ state | .divergent _ state | .refused _ state => state
  let (status,value,diagnostic) := match outcome with
    | .finished value _ => ("finished",valueJson value,Json.null)
    | .suspended reason _ => ("suspended",Json.null,toJson (reprStr reason))
    | .divergent _ _ => ("divergent",Json.null,toJson "blackhole; no catchable source exception")
    | .refused reason _ => ("refused",Json.null,toJson (reprStr reason))
  pure <| Json.mkObj [("schema",toJson "dregg.objective-bend.typed-preview.v2"),
    ("edition",toJson "objective-bend-1"),("status",toJson status),
    ("type",typeJson checked.type),("uses",toJson checked.uses),
    ("typing",toJson "accepted by actual annotated checker"),
    ("sameDecodedTerm",toJson true),("result",value),("diagnostic",diagnostic),
    ("heap",toJson (toString state.heap.size)),("stack",toJson (toString state.stack.length)),
    ("limits",limits),("laws",toJson "undischarged unless independent law providers are supplied"),
    ("authority",toJson "none; clear source preview"),
    ("proofScope",toJson "actual compiled checker/executor join; preservation and elaboration adequacy separate")]

end Minidregg.Host.ObjectiveBendPreview

def main (arguments : List String) : IO UInt32 := do
  let [packetPath,limitsPath] := arguments | do
    IO.eprintln "usage: objective-preview TYPED_CORE_PACKET_JSON LIMITS_JSON"
    return 2
  try
    let packet ← IO.FS.readFile packetPath
    let limits ← IO.FS.readFile limitsPath
    let result := do
      Minidregg.Host.ObjectiveBendPreview.preview (← Lean.Json.parse packet) (← Lean.Json.parse limits)
    match result with
    | .ok output => IO.println output.compress; return 0
    | .error message =>
      IO.eprintln (Lean.Json.mkObj [("schema",Lean.toJson "dregg.bend.compiler-diagnostic.v1"),
        ("stage",Lean.toJson "objective-typed-preview"),("message",Lean.toJson message)]).compress
      return 2
  catch error => IO.eprintln error.toString; return 2
