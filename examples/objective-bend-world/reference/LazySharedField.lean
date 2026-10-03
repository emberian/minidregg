import Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
def authoredTerm : Term := (Term.get (Term.fix (Term.lam (Term.lam (Term.record [("LazySharedField.work", (Term.lam (Term.ifZero (Term.bound 0) (Term.nat 1) (Term.binary Primitive.add (Term.app (Term.get (Term.bound 3) "LazySharedField.work") (Term.bound 0)) (Term.app (Term.get (Term.bound 3) "LazySharedField.work") (Term.bound 0)))))), ("LazySharedField.Fields", (Term.lam (Term.lam (Term.record [("costly", (Term.app (Term.get (Term.bound 3) "LazySharedField.work") (Term.nat 8))), ("twice", (Term.binary Primitive.add (Term.get (Term.bound 1) "costly") (Term.get (Term.bound 1) "costly")))])))), ("LazySharedField.result", (Term.get (Term.fix (Term.get (Term.bound 1) "LazySharedField.Fields") (Term.record [("costly", (Term.nat 0)), ("twice", (Term.nat 0))])) "twice"))]))) (Term.record [])) "LazySharedField.result")
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
