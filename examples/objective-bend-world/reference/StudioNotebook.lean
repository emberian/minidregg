import Theory.ObjectiveBendDemandMachine
open Lean (Json toJson)
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
def authoredTerm : Term := (Term.get (Term.fix (Term.lam (Term.lam (Term.record [("Base.seed", (Term.nat 7)), ("Notebook.remember", (Term.nat 8))]))) (Term.record [])) "Notebook.remember")
def previewLimits : Limits := ⟨8192,1024⟩
def measured : Nat → State → List Nat → Outcome × List Nat
  | 0,state,entered => (runBounded previewLimits 0 state,entered)
  | ticks+1,state,entered =>
    let entered := match state.control with
      | .enter address => match state.heap[address]? with
        | some (.suspended _) => address::entered
        | _ => entered
      | _ => entered
    match step previewLimits state with
    | .suspended .ticks next => measured ticks next entered
    | other => (other,entered)
def resultJson : RuntimeValue → Json
  | .natural value => Json.mkObj [("tag",toJson "natural"),("value",toJson (toString value))]
  | .label value => Json.mkObj [("tag",toJson "label"),("value",toJson value)]
  | .closure _ _ => Json.mkObj [("tag",toJson "closure"),("status",toJson "unforced body")]
  | .record fields => Json.mkObj [("tag",toJson "record"),("fields",toJson (fields.map Prod.fst))]
  | .specification _ _ => Json.mkObj [("tag",toJson "specification"),("status",toJson "unforced extension")]
  | .prototype _ _ => Json.mkObj [("tag",toJson "prototype"),("status",toJson "unforced target")]
def main : IO Unit := do
  let (outcome,entered) := measured 4096 (initial authoredTerm) []
  let state : State := match outcome with
    | .finished _ state | .suspended _ state | .divergent _ state | .refused _ state => state
  let (status,value,diagnostic) := match outcome with
    | .finished value _ => ("finished",resultJson value,Json.null)
    | .suspended reason _ => ("suspended",Json.null,toJson (reprStr reason))
    | .divergent _ _ => ("divergent",Json.null,toJson "blackhole; no catchable source exception")
    | .refused reason _ => ("refused",Json.null,toJson (reprStr reason))
  let addresses := state.heap.toList.foldl (fun (prior : List Nat) (cell : Cell) => match cell with
    | .cached _ (.record fields) => match fields.find? (fun field => field.1 == "costly") with
      | some (_,address) => if prior.contains address then prior else address::prior
      | none => prior
    | _ => prior) ([] : List Nat)
  let demands := addresses.map fun address => Json.mkObj
    [("address",toJson (toString address)),("firstEntries",toJson (toString ((entered.filter (· == address)).length)))]
  IO.println ((Json.mkObj [("schema",toJson "dregg.objective-bend.reference-result.v1"),
    ("sourceEntry",toJson "Notebook.remember"),("edition",toJson "objective-bend-1"),
    ("status",toJson status),("result",value),("diagnostic",diagnostic),
    ("heap",toJson (toString state.heap.size)),("stack",toJson (toString state.stack.length)),
    ("sharingProbe",Json.arr demands.toArray),("authority",toJson "none; clear source preview")]).compress)
