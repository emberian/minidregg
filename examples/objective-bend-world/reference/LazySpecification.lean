import Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
def authoredTerm : Term := (Term.app (Term.get (Term.app (Term.get (Term.fix (Term.lam (Term.lam (Term.record [("LazySpecification.Incomplete", (Term.specification (Term.record [("name", (Term.label "LazySpecification.Incomplete")), ("interface", (Term.label "{\"targetType\":\"MissingTarget\",\"requirements\":[{\"name\":\"missing\",\"parameters\":[{\"name\":\"value\",\"type\":\"Nat\",\"quantity\":\"default\"}],\"resultType\":\"Nat\",\"span\":{\"start\":142,\"end\":177,\"line\":8}}],\"methods\":[{\"name\":\"result\",\"parameters\":[{\"name\":\"value\",\"type\":\"Nat\",\"quantity\":\"default\"}],\"resultType\":\"Nat\",\"span\":{\"start\":180,\"end\":210,\"line\":9}}]}")), ("laws", (Term.record []))]) (Term.lam (Term.lam (Term.extend (Term.bound 0) [("result", (Term.lam (Term.app (Term.get (Term.bound 2) "missing") (Term.bound 0))))]))))), ("LazySpecification.Filling", (Term.specification (Term.record [("name", (Term.label "LazySpecification.Filling")), ("interface", (Term.label "{\"targetType\":\"MissingTarget\",\"requirements\":[],\"methods\":[{\"name\":\"missing\",\"parameters\":[{\"name\":\"value\",\"type\":\"Nat\",\"quantity\":\"default\"}],\"resultType\":\"Nat\",\"span\":{\"start\":270,\"end\":301,\"line\":13}}]}")), ("laws", (Term.record []))]) (Term.lam (Term.lam (Term.extend (Term.bound 0) [("missing", (Term.lam (Term.binary Primitive.add (Term.bound 0) (Term.nat 1))))]))))), ("LazySpecification.unforced", (Term.get (Term.bound 1) "LazySpecification.Incomplete")), ("LazySpecification.completed", (Term.lam (Term.fix (Term.specification (Term.record [("operator", (Term.label "compose")), ("inherited", (Term.get (Term.bound 2) "LazySpecification.Incomplete")), ("wrapping", (Term.get (Term.bound 2) "LazySpecification.Filling"))]) (Term.mix (Term.get (Term.bound 2) "LazySpecification.Incomplete") (Term.get (Term.bound 2) "LazySpecification.Filling"))) (Term.bound 0))))]))) (Term.record [])) "LazySpecification.completed") (Term.record [])) "result") (Term.nat 4))
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
