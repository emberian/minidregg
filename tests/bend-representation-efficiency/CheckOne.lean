import Theory.BendTTSource
open Minidregg.Theory.BendTT

def main (paths : List String) : IO UInt32 := do
  for path in paths do
    let source ← IO.FS.readFile path
    let .ok book := Book.parse source | return 1
    let some definition := book[262]? | return 1
    if definition.k != "DrEXSettlementPlanDemonstration.actual_uniform_collects_then_distributes" then
      return 1
    let libs := (Lib.of book, Lib.of (book.map ({ · with o := false })))
    IO.eprintln s!"FORK DEF CHECK BEGIN 262 {definition.k}"
    (← IO.getStderr).flush
    let before ← IO.monoMsNow
    match Def.check book libs 262 definition with
    | .error detail => IO.eprintln s!"FORK DEF CHECK REFUSED {detail}"; return 1
    | .ok () =>
      let after ← IO.monoMsNow
      IO.eprintln s!"FORK DEF CHECK PASS 262 {after-before}ms"
  return 0
