import Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
def authoredTerm : Term := (Term.get (Term.fix (Term.lam (Term.lam (Term.record [("ReflectLazyPrototype.Named", (Term.specification (Term.record [("name", (Term.label "ReflectLazyPrototype.Named")), ("interface", (Term.label "{\"targetType\":\"Nat\",\"requirements\":[],\"methods\":[]}")), ("laws", (Term.record [("retained", (Term.lam (Term.lam (Term.label "true"))))]))]) (Term.lam (Term.lam (Term.extend (Term.bound 0) []))))), ("ReflectLazyPrototype.Identity", (Term.lam (Term.lam (Term.bound 1)))), ("ReflectLazyPrototype.inspect", (Term.get (Term.metadata (Term.reflect (Term.prototype (Term.get (Term.bound 1) "ReflectLazyPrototype.Named") (Term.fix (Term.get (Term.bound 1) "ReflectLazyPrototype.Identity") (Term.nat 0))))) "name"))]))) (Term.record [])) "ReflectLazyPrototype.inspect")
def measured : Nat → State → List Nat → State × List Nat
  | 0,state,entered => (state,entered)
  | ticks+1,state,entered =>
    let entered := match state.control with
      | .enter address => match state.heap[address]? with
        | some (.suspended _) => address::entered
        | _ => entered
      | _ => entered
    match step ⟨100000,100000⟩ state with
    | .suspended .ticks next => measured ticks next entered
    | .finished _ retained | .suspended _ retained | .divergent _ retained | .refused _ retained => (retained,entered)
def main : IO Unit := do
  let (result,entered) := measured 100000 (initial authoredTerm) []
  IO.println (reprStr result.control)
  IO.println s!"heap={result.heap.size} stack={result.stack.length}"
  for cell in result.heap do
    match cell with
    | .cached _ (.record fields) =>
      match fields.find? (fun field => field.1 == "costly") with
      | some (_,address) => IO.println s!"costlyThunk={address} evaluations={(entered.filter (· == address)).length}"
      | none => pure ()
    | _ => pure ()
