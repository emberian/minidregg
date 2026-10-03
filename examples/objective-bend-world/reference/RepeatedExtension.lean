import Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
def authoredTerm : Term := (Term.app (Term.get (Term.fix (Term.lam (Term.lam (Term.record [("RepeatedExtension.AddOne", (Term.lam (Term.lam (Term.binary Primitive.add (Term.bound 0) (Term.nat 1))))), ("RepeatedExtension.repeated", (Term.lam (Term.fix (Term.specification (Term.record [("operator", (Term.label "compose")), ("inherited", (Term.get (Term.bound 2) "RepeatedExtension.AddOne")), ("wrapping", (Term.get (Term.bound 2) "RepeatedExtension.AddOne"))]) (Term.mix (Term.get (Term.bound 2) "RepeatedExtension.AddOne") (Term.get (Term.bound 2) "RepeatedExtension.AddOne"))) (Term.bound 0))))]))) (Term.record [])) "RepeatedExtension.repeated") (Term.nat 7))
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
