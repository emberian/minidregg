/-
# Kernel.WorldBench -- a compiled 1000-turn fold (DATAMODEL §5 B2 exit)

A deterministic log over the real `World.step`: 100 creates (one cell each,
allocating key 0), then 900 writes, each guarded at the cell's current value
and carrying a read guard on a neighbouring cell.  The parameters are toy
(`Nat` keys and values, a `UInt64` mixing digest in place of stage-F cSHAKE,
which is C1's); the code path is the kernel's own `admit`/`fold`.

`bench_fold_1000` checks the fold's outcome in compiled code
(`native_decide`; each pin confesses the compiled-evaluation axiom
`<name>._native.native_decide.ax_1_1` that Lean 4.30 mints for it); the timing is taken by
the executable `world-fold-bench` (`Host/WorldFoldBench.lean`).
-/
import Kernel.World

namespace Minidregg.Kernel.WorldBench

open Minidregg.Theory.Store
open Minidregg.Kernel.World

set_option autoImplicit false

def benchLayout : Layout.{0, 0, 0} where
  Namespace := Unit
  Key := fun _ => Nat
  Value := fun _ => Nat
  discipline := fun _ => .ram

def benchR : Registry where
  Kind := Unit
  layout := fun _ => benchLayout

abbrev BenchTurn := Turn benchR Nat Unit UInt64
abbrev BenchWorld := World benchR Nat UInt64

/-- FNV-style mixing over the ops of every leg: a function of the turn's
content, standing in for cSHAKE over its canonical bytes. -/
def mix (h : UInt64) (n : Nat) : UInt64 := (h ^^^ n.toUInt64) * 1099511628211

def opDigest (h : UInt64) : Op benchLayout → UInt64
  | .read _ k (some v) => mix (mix (mix h 1) k) v
  | .read _ k none => mix (mix h 2) k
  | .write _ k b a => mix (mix (mix (mix h 3) k) b) a
  | .allocate _ k v => mix (mix (mix h 4) k) v
  | .free _ k b => mix (mix (mix h 5) k) b

def turnDigest (t : BenchTurn) : UInt64 :=
  let h0 := mix 14695981039346656037 t.txId
  let h1 := t.creates.foldl (fun h c => mix (mix h 6) c.1) h0
  t.legs.foldl (fun h l => l.patch.foldl opDigest (mix (mix h 7) l.cell)) h1

def benchH : History benchR Nat Unit UInt64 where
  turnDigest := turnDigest
  chain := fun r d => mix (mix r 8) d.toNat
  logRoot0 := 0
  -- The bench measures the fold, not the meter: no leg is charged storage.
  legBytes := fun _ => 0

def benchGenesis : BenchWorld := genesis benchH 0

def cells : Nat := 100

def allocOp (k v : Nat) : Op benchLayout := .allocate () k v
def writeOp (k b a : Nat) : Op benchLayout := .write () k b a
def readOp (k v : Nat) : Op benchLayout := .read () k (some v)

/-- Turn `i` of the log. -/
def benchTurn (i : Nat) : BenchTurn :=
  if i < cells then
    { txId := i + 1, creates := [(i, (), none)], legs := [⟨i, (), [allocOp 0 0]⟩], retires := [],
      event := () }
  else
    let c := i % cells
    let r := i / cells
    let n := (c + 1) % cells
    let seen := if c + 1 = cells then r else r - 1
    { txId := i + 1, creates := [], legs := [⟨c, (), [writeOp 0 (r - 1) r]⟩, ⟨n, (), [readOp 0 seen]⟩],
      retires := [], event := () }

def benchLog (n : Nat) : List BenchTurn := (List.range n).map benchTurn

/-- What the benchmark checks: the height, and the key-0 value of cells 0 and 99. -/
def summary (w : BenchWorld) : Option (Nat × UInt64) × Option Nat × Option Nat :=
  let v := fun (c : Nat) => (w.cells c).bind fun cell => (cell.storeAt ()).bind fun s => s ⟨(), (0 : Nat)⟩
  (w.head, v 0, v 99)

/-- The compiled 1000-turn fold is accepted, reaches height 1000, and leaves
every cell at round 9. -/
theorem bench_fold_1000 :
    ((fold benchH benchGenesis (benchLog 1000)).map fun w =>
      ((summary w).1.map Prod.fst, (summary w).2)) =
      some (some 1000, some 9, some 9) := by
  native_decide

/-- The same log with one stale guard (turn 500 guarded at a value its cell
does not hold) is refused. -/
theorem bench_fold_1000_stale_refused :
    (fold benchH benchGenesis
      ((benchLog 1000).set 500
        { txId := 501, creates := [], legs := [⟨0, (), [writeOp 0 7 8]⟩], retires := [],
          event := () })).isNone = true := by
  native_decide

/-- info: 'Minidregg.Kernel.WorldBench.bench_fold_1000' depends on axioms: [propext, Classical.choice, Quot.sound, bench_fold_1000._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms bench_fold_1000
/-- info: 'Minidregg.Kernel.WorldBench.bench_fold_1000_stale_refused' depends on axioms: [propext, Classical.choice, Quot.sound, bench_fold_1000_stale_refused._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms bench_fold_1000_stale_refused

end Minidregg.Kernel.WorldBench
