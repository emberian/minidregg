import Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
def authoredTerm : Term := (Term.app (Term.get (Term.app (Term.get (Term.fix (Term.lam (Term.lam (Term.record [("EvenOdd.Even", (Term.specification (Term.record [("name", (Term.label "EvenOdd.Even")), ("interface", (Term.label "{\"targetType\":\"Parity\",\"requirements\":[{\"name\":\"odd\",\"parameters\":[{\"name\":\"n\",\"type\":\"Nat\",\"quantity\":\"default\"}],\"resultType\":\"Bool\",\"span\":{\"start\":110,\"end\":138,\"line\":8}}],\"methods\":[{\"name\":\"even\",\"parameters\":[{\"name\":\"n\",\"type\":\"Nat\",\"quantity\":\"default\"}],\"resultType\":\"Bool\",\"span\":{\"start\":141,\"end\":166,\"line\":9}}]}")), ("laws", (Term.record []))]) (Term.lam (Term.lam (Term.extend (Term.bound 0) [("even", (Term.lam (Term.ifZero (Term.bound 0) (Term.label "true") (Term.app (Term.get (Term.bound 3) "odd") (Term.bound 0)))))]))))), ("EvenOdd.Odd", (Term.specification (Term.record [("name", (Term.label "EvenOdd.Odd")), ("interface", (Term.label "{\"targetType\":\"Parity\",\"requirements\":[{\"name\":\"even\",\"parameters\":[{\"name\":\"n\",\"type\":\"Nat\",\"quantity\":\"default\"}],\"resultType\":\"Bool\",\"span\":{\"start\":259,\"end\":288,\"line\":15}}],\"methods\":[{\"name\":\"odd\",\"parameters\":[{\"name\":\"n\",\"type\":\"Nat\",\"quantity\":\"default\"}],\"resultType\":\"Bool\",\"span\":{\"start\":291,\"end\":315,\"line\":16}}]}")), ("laws", (Term.record []))]) (Term.lam (Term.lam (Term.extend (Term.bound 0) [("odd", (Term.lam (Term.ifZero (Term.bound 0) (Term.label "false") (Term.app (Term.get (Term.bound 3) "even") (Term.bound 0)))))]))))), ("EvenOdd.parity", (Term.lam (Term.fix (Term.specification (Term.record [("operator", (Term.label "compose")), ("inherited", (Term.get (Term.bound 2) "EvenOdd.Even")), ("wrapping", (Term.get (Term.bound 2) "EvenOdd.Odd"))]) (Term.mix (Term.get (Term.bound 2) "EvenOdd.Even") (Term.get (Term.bound 2) "EvenOdd.Odd"))) (Term.bound 0))))]))) (Term.record [])) "EvenOdd.parity") (Term.record [])) "even") (Term.nat 7))
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
