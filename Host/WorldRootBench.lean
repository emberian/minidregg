/-
# world-root-bench -- wall-clock of the compiled deployed world root

Builds `n` entries (the system slot and `n - 1` cells with distinct roots) and
times `Kernel.WorldRoot.deployedRoot` over them, `reps` times.  The entries are
built outside the timed region; the empty-subtree table is forced first.
-/
import Kernel.WorldRoot

open Minidregg.Kernel.WorldRoot
open Minidregg.Theory.TypedAuthorization

def main (args : List String) : IO UInt32 := do
  let n := (args[0]? >>= String.toNat?).getD 20
  let reps := (args[1]? >>= String.toNat?).getD 3
  let cells : List (Key × Digest) :=
    (List.range (n - 1)).map fun i => (Key.cell (i * 7919 + 13), ⟨i + 1⟩)
  IO.println s!"entries={cells.length + 1} table={deployedTable.size}"
  for rep in [0:reps] do
    let t0 ← IO.monoNanosNow
    -- the system slot depends on the clock read, so the root cannot be hoisted
    -- above `t0`; the branch on its value forces it before `t1`
    let es := (Key.system, (⟨7 + rep + t0 % 2⟩ : Digest)) :: cells
    let r := deployedRoot es
    if r.value == 0 then IO.println "zero root"
    let t1 ← IO.monoNanosNow
    let rendered := toString r.value
    IO.println s!"rep={rep} ms={(t1 - t0).toFloat / 1.0e6} root={rendered.take 12}"
  return 0
