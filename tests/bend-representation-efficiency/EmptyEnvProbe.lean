import Theory.BendTTSource
open Minidregg.Theory.BendTT

def tree : Nat → Term
  | 0 => .Lab "leaf"
  | n + 1 => let t := tree n; .Tup .Q2 t t

def main : IO Unit := do
  let t := tree 19
  let ck : Lib := {}
  let before ← IO.monoMsNow
  let result := Term.run ck false 1 t [] []
  match result with
  | (some (.Tup .Q2 _ _), 0) => pure ()
  | _ => throw (IO.userError "unexpected actual run result/fuel")
  let after ← IO.monoMsNow
  if result != (some t, 0) then throw (IO.userError "actual run changed complete term/fuel")
  IO.println s!"actual Term.run shared depth19 identity environment: {after-before}ms; full term/fuel equality PASS"
