import Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
def authoredTerm : Term := (Term.get (Term.fix (Term.lam (Term.lam (Term.record [("LazyUnusedField.Fields", (Term.lam (Term.lam (Term.record [("good", (Term.nat 7)), ("bad", (Term.get (Term.bound 1) "bad"))])))), ("LazyUnusedField.result", (Term.get (Term.fix (Term.get (Term.bound 1) "LazyUnusedField.Fields") (Term.record [("good", (Term.nat 0)), ("bad", (Term.nat 0))])) "good"))]))) (Term.record [])) "LazyUnusedField.result")
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
