/- Generic typed clear preview: the checker and executor consume the SAME
actual decoded core term. No generated Lean source interpreter, output oracle,
current native authority or effect receipt is introduced. An activity runs to
its first yield; the preview prints the typed Plan, resumes with each supplied
response (checked against the entry's declared response type) and runs to the
next yield. Responses stand in for the kernel: nothing is admitted. -/
import Theory.ObjectiveBendTyping
import Theory.ObjectiveBendDemandMachine
import Theory.ObjectiveBendDemandData
import Theory.ObjectiveBendCheckpoint
import Compiler.ObjectiveBendDataWire

namespace Minidregg.Host.ObjectiveBendPreview
open Lean (Json toJson)
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendTypes (Ty)
open Minidregg.Theory.ObjectiveBendDemandData (Data)
open Minidregg.Compiler.ObjectiveBendDataWire
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
  | .variant label _ => Json.mkObj [("tag",toJson "variant"),("label",toJson label),("status",toJson "unforced payload")]

/-- Run one turn: to a finish, a yield, or a refusal/suspension/divergence. -/
def runTurn (limits : Limits) (ticks : Nat) (state : State) : Outcome := runBounded limits ticks state

/-- Turns: run, and at each yield extract the Plan, then resume with the next
supplied response if it conforms to the declared response type. -/
def runTurns (limits : Limits) (ticks : Nat) (budget : Minidregg.Theory.ObjectiveBendDemandData.Budget)
    (response? : Option Ty) : List Data → State → Array Json → Except String (Outcome × Array Json)
  | responses, state, turns =>
    match runTurn limits ticks state with
    | .yielded plan yielded => do
      let extracted ← match Minidregg.Theory.ObjectiveBendDemandData.yieldedPlan limits budget yielded with
        | .ok result => pure result
        | .error (failure,_) => throw ("yielded plan not extractable as data: " ++ reprStr failure)
      let checkpoint := Minidregg.Theory.ObjectiveBendCheckpoint.encodeState extracted.state
      let turn : List (String × Json) := [("plan",dataJson extracted.value),("planAddress",toJson (toString plan)),
        ("checkpointTokens",toJson (toString checkpoint.length)),
        ("checkpointRoundTrips",toJson (Minidregg.Theory.ObjectiveBendCheckpoint.roundTrips extracted.state)),
        ("quiescent",toJson (extracted.state.heap.toList.all fun cell => match cell with
          | .evaluating _ => false | _ => true))]
      match responses with
      | [] => pure (.yielded plan extracted.state, turns.push (Json.mkObj turn))
      | response :: rest => do
        let some declared := response? | throw "a yield needs an Activity entry type"
        if !response.conforms declared then
          throw ("response refused: it does not conform to the declared response type " ++ (typeJson declared).compress)
        let some resumed := resume response.term extracted.state | throw "internal: yielded state did not resume"
        runTurns limits ticks budget response? rest resumed
          (turns.push (Json.mkObj (turn ++ [("response",dataJson response)])))
    | other => pure (other, turns)
termination_by responses => responses.length

/-- Receives an actual annotated packet; typing and bounded demand use exactly
packet.source.term. A Boolean assertion supplied by the caller cannot replace
its Checked proof-producing result. -/
def preview (typed limits : Json) (responsesJson : Json := Json.arr #[]) : Except String Json := do
  let packet ← decodePacket typed
  if !packet.context.isEmpty then throw "preview requires a closed source context"
  let heap ← natural limits "heap"
  let stack ← natural limits "stack"
  let ticks ← natural limits "ticks"
  let responses ← (← responsesJson.getArr?).toList.mapM (decodeData 64)
  if responses.length > 64 then throw "preview response capacity refused"
  let some checked := check packet.source packet.context packet.fuel
    | throw "annotated typing/ownership refused or checker budget insufficient (activities: an Activity is refused as an argument, record/extend field, specification or prototype component, or sum payload; a Plan must be a sum of first-order data; a response must be first-order data)"
  let response? : Option Ty := match checked.type with
    | .computation _ response _ => some response
    | _ => none
  let (outcome,turns) ← runTurns ⟨heap,stack⟩ ticks ⟨heap,ticks,1048576⟩ response? responses
    (initial packet.source.term) #[]
  let state := match outcome with
    | .finished _ state | .suspended _ state | .divergent _ state | .refused _ state | .yielded _ state => state
  let (status,value,diagnostic) := match outcome with
    | .finished value _ => ("finished",valueJson value,Json.null)
    | .suspended reason _ => ("suspended",Json.null,toJson (reprStr reason))
    | .divergent _ _ => ("divergent",Json.null,toJson "blackhole; no catchable source exception")
    | .refused reason _ => ("refused",Json.null,toJson (reprStr reason))
    | .yielded _ _ => ("yielded",Json.null,toJson "waiting for a response")
  pure <| Json.mkObj [("schema",toJson "dregg.objective-bend.typed-preview.v2"),
    ("edition",toJson "objective-bend-1"),("status",toJson status),
    ("type",typeJson checked.type),("uses",toJson checked.uses),
    ("typing",toJson "accepted by actual annotated checker"),
    ("sameDecodedTerm",toJson true),("result",value),("diagnostic",diagnostic),
    ("turns",Json.arr turns),
    ("heap",toJson (toString state.heap.size)),("stack",toJson (toString state.stack.length)),
    ("limits",limits),("laws",toJson "undischarged unless independent law providers are supplied"),
    ("authority",toJson "none; clear source preview; responses are supplied, not admitted"),
    ("proofScope",toJson "actual compiled checker/executor join; preservation and elaboration adequacy separate")]

end Minidregg.Host.ObjectiveBendPreview

def main (arguments : List String) : IO UInt32 := do
  let paths : Option (String × String × Option String) := match arguments with
    | [packet,limits] => some (packet,limits,none)
    | [packet,limits,responses] => some (packet,limits,some responses)
    | _ => none
  let some (packetPath,limitsPath,responsesPath?) := paths | do
    IO.eprintln "usage: objective-preview TYPED_CORE_PACKET_JSON LIMITS_JSON [RESPONSES_JSON]"
    return 2
  try
    let packet ← IO.FS.readFile packetPath
    let limits ← IO.FS.readFile limitsPath
    let responses ← match responsesPath? with
      | some path => IO.FS.readFile path
      | none => pure "[]"
    let result := do
      Minidregg.Host.ObjectiveBendPreview.preview (← Lean.Json.parse packet) (← Lean.Json.parse limits)
        (← Lean.Json.parse responses)
    match result with
    | .ok output => IO.println output.compress; return 0
    | .error message =>
      IO.eprintln (Lean.Json.mkObj [("schema",Lean.toJson "dregg.bend.compiler-diagnostic.v1"),
        ("stage",Lean.toJson "objective-typed-preview"),("message",Lean.toJson message)]).compress
      return 2
  catch error => IO.eprintln error.toString; return 2
