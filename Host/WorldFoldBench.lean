/-
# world-fold-bench -- wall-clock of the compiled `fold` over a 1000-turn log

Runs `Kernel.World.fold` over `Kernel.WorldBench.benchLog n` (default 1000),
`reps` times (default 5), and prints each run's milliseconds and the
summary it reached.  The log is built outside the timed region.
-/
import Kernel.WorldBench

open Minidregg.Kernel.World
open Minidregg.Kernel.WorldBench

def main (args : List String) : IO UInt32 := do
  let n := (args[0]? >>= String.toNat?).getD 1000
  let reps := (args[1]? >>= String.toNat?).getD 5
  let log := benchLog n
  IO.println s!"turns={log.length}"
  let mut ok := true
  for rep in [0:reps] do
    let t0 ← IO.monoNanosNow
    let result := fold benchH benchGenesis log
    let s := result.map summary
    -- force the result before stopping the clock
    let rendered := match s with
      | none => "refused"
      | some (h, v0, v99) => s!"head={h.map Prod.fst} v0={v0} v99={v99}"
    let t1 ← IO.monoNanosNow
    IO.println s!"rep={rep} ms={(t1 - t0).toFloat / 1.0e6} {rendered}"
    if s.isNone then ok := false
  return if ok then 0 else 1
