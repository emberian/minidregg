/- KN2 LinkIndex timed probe (executed). One write of one cell's links at
G cells x 3 links each, 500 targets: the retired step (set the cell's entries,
then `invert` the whole forward map) against `setCell` (drop the cell's old
backlink pairs, add the new ones). Each is timed over `rounds` writes of
rotating cells; the final backlink maps are compared by membership.

Usage: lake env lean --run scripts/kn2/linkindex-bench.lean [G] [rounds] -/
import Kernel.LinkIndex

open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.Hyperdocument
open Minidregg.Kernel.LinkIndex
open Minidregg.Kernel.DurableDataIntent (CellId)

def dig (n : Nat) : Digest := ⟨n⟩

def link (n target : Nat) : LinkKey :=
  (⟨dig (n + 1000000)⟩,
   { sourceDocument := ⟨dig n⟩, source := none, target := .document ⟨dig target⟩,
     relation := dig 0, author := ⟨⟨0⟩, .object, ⟨0⟩⟩, operation := ⟨dig n⟩,
     tombstonedAt := none })

def linksOf (cell salt : Nat) : List LinkKey :=
  (List.range 3).map fun i => link (cell * 10 + i) ((cell * 7 + i * 13 + salt) % 500)

def build (g : Nat) : Sources × Reverse :=
  let sources : Sources := (List.range g).foldl (fun acc cell =>
    store acc ⟨cell⟩ (refresh [] 1 (linksOf cell 0))) []
  (sources, invert sources)

def oldStep (acc : Sources × Reverse) (cell : CellId) (height : Nat) (links : List LinkKey) :
    Sources × Reverse :=
  let sources := store acc.1 cell (refresh (lookup acc.1 cell) height links)
  (sources, invert sources)

def time (label : String) (rounds : Nat) (acc0 : Sources × Reverse)
    (step : Sources × Reverse → CellId → Nat → List LinkKey → Sources × Reverse) (g : Nat) :
    IO (Sources × Reverse) := do
  let start ← IO.monoMsNow
  let mut acc := acc0
  for round in List.range rounds do
    let cell := (round * 37) % g
    acc := step acc ⟨cell⟩ (round + 2) (linksOf cell (round + 1))
  let stop ← IO.monoMsNow
  IO.println s!"{label}: {rounds} writes at G={g}: {stop - start} ms total, {(stop - start) * 1000 / rounds} us/write"
  return acc

def main (args : List String) : IO Unit := do
  let g := (args.head? >>= String.toNat?).getD 1000
  let rounds := (args.tail.head? >>= String.toNat?).getD 20
  let base := build g
  IO.println s!"built G={g}: {base.1.length} cells, {(pairs base.1).length} pairs"
  let a ← time "retired (invert per write)" rounds base oldStep g
  let b ← time "setCell (incremental)     " rounds base setCell g
  -- agreement: same pairs under every target the old map holds
  let keys := (invert a.1).map (·.1)
  let same := keys.all fun key =>
    ((lookup (invert a.1) key).all fun pair => decide (pair ∈ lookup b.2 key)) &&
    ((lookup b.2 key).all fun pair => decide (pair ∈ lookup (invert a.1) key))
  unless same && a.1 == b.1 do throw (IO.userError "FAIL: the incremental backlink map differs from the inversion")
  IO.println "agree: incremental backlink map equals invert(sources) by membership under every target"
