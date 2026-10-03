import Theory.BendLiveMachine

open Minidregg.Theory
open BendTT BendLiveMachine

/-- Many small definitions and a call chain isolate lookup from substitution
and data traversal. Full evaluation still constructs the source trace. -/
def chainBook (count : Nat) : Book :=
  (List.range (count + 1)).map fun index =>
    { k := s!"definition_{index}", T := .Enu ["done"],
      v := if index = 0 then .Lab "done" else .Ref s!"definition_{index - 1}", o := false }

def assertOutcome (book : Book) (ticks steps : Nat) (term : Term) : IO Unit := do
  let fast := (executeChecked book ticks steps term).outcome
  let reference := (executeReference book ticks steps term).outcome
  if fast != reference then
    throw (IO.userError s!"indexed/reference mismatch: {repr fast} / {repr reference}")

def bench (count : Nat) : IO Unit := do
  let book := chainBook count
  let entry := Term.Ref s!"definition_{count}"
  let begin ← IO.monoMsNow
  let reference := (executeReference book 8 (count + 1) entry).outcome
  if reference != .complete (.Lab "done") (count + 1) then
    throw (IO.userError "reference chain did not complete")
  let middle ← IO.monoMsNow
  let fast := (executeChecked book 8 (count + 1) entry).outcome
  if fast != reference then
    throw (IO.userError s!"chain did not complete exactly: {repr fast}")
  let finish ← IO.monoMsNow
  IO.println s!"BOOK-INDEX chain={count} reference_ms={middle - begin} indexed_ms={finish - middle} (indexed includes preparation)"

def main : IO Unit := do
  let duplicate : Book :=
    [{ k := "same", T := .Enu ["first"], v := .Lab "first", o := false },
     { k := "same", T := .Enu ["second"], v := .Lab "second", o := false }]
  for ticks in [0, 1, 2, 8] do
    for steps in [0, 1, 4] do
      for term in [.Ref "same", .Ref "missing", .App .Q1 (.Lam .Q1 (.Var 0)) (.Lab "x"),
          .Rwt .Rfl (.Var 999) (.Lab "cast"), .Ref "under"] do
        assertOutcome duplicate ticks steps term
  let under : Book := [{ k := "under", T := .Enu [], v := .Lam .Q1 (.Var 0), o := false }]
  assertOutcome under 8 0 (.Ref "under")
  if (executeChecked duplicate 8 2 (.Ref "same")).outcome != .complete (.Lab "first") 1 then
    throw (IO.userError "duplicate name did not retain first-definition wins")
  for count in [1000, 5000, 10000] do bench count
  IO.println "BEND BOOK INDEX EXECUTION PASS"
