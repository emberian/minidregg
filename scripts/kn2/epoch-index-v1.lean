/- A Store born before the journal sequence rows (`index/trie-v1`) is refused by name.

The Store epoch's accumulator component names the index layout. `index/trie-v2`
added family 2 (the last write of a cell) and families 3 and 4 (journal sequences). This Host
writes `index/trie-v3`, which folds a sequence item's position into its path: a v2 Store holds
the same rows under other paths and is refused by name as well.
A v1 Store's index root covers no such rows, so its reads would answer verified absences
for sequences that have members. The open refuses it at the seed frame instead:

* `differing_accumulator` (kernel-checked): a Store whose accumulator label differs is
  named by that component, and only it;
* the executed check below reads the seed frame of a Store labelled exactly as the previous
  Host labelled it and requires the refusal the open gives (`SeedEpoch.refusal`) to quote both
  labels; the control is this Host's own frame, which passes.

Usage: lake lean scripts/kn2/epoch-index-v1.lean
-/
import Compiler.DurableCheckpointCodec
import Theory.AssertAxioms

open Minidregg.Compiler
open Minidregg.Compiler.DurableCheckpointCodec
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Compiler.Tower256ConcreteBackend

/-- **An accumulator break is named, and only it.** -/
theorem differing_accumulator (host : StoreEpoch) (accumulator : String)
    (changed : accumulator ≠ host.accumulator) :
    StoreEpoch.differing { host with accumulator } host =
      [s!"history accumulator: Store {accumulator}, this Host {host.accumulator}"] := by
  simp [StoreEpoch.differing, changed]

#assert_axioms differing_accumulator

def previousAccumulator : String := "history/mmr-v1;index/trie-v1;checkpoint/v5"

def previous : StoreEpoch := { StoreEpoch.current with accumulator := previousAccumulator }

#eval show IO Unit from do
  let own := (SeedEpoch.ofBytes (bytesStream.encode seedFrame.frame)).refusal
  unless own == none do
    throw (IO.userError s!"CONTROL FAILED: this Host's own seed frame is refused: {own}")
  let expected := s!"this Store was born in another epoch (history accumulator: Store {previousAccumulator}, this Host {StoreEpoch.current.accumulator}); re-genesis the world"
  let refusal := (SeedEpoch.ofBytes (bytesStream.encode (seedFrameFor previous).frame)).refusal
  unless refusal == some expected do
    throw (IO.userError s!"FAIL: an index/trie-v1 Store is not refused by name: {refusal}")
  let v2 := "history/mmr-v1;index/trie-v2;checkpoint/v5"
  let expectedV2 := s!"this Store was born in another epoch (history accumulator: Store {v2}, this Host {StoreEpoch.current.accumulator}); re-genesis the world"
  let refusalV2 := (SeedEpoch.ofBytes (bytesStream.encode (seedFrameFor { StoreEpoch.current with accumulator := v2 }).frame)).refusal
  unless refusalV2 == some expectedV2 do
    throw (IO.userError s!"FAIL: an index/trie-v2 Store is not refused by name: {refusalV2}")
  unless StoreEpoch.current.accumulator == "history/mmr-v1;index/trie-v3;checkpoint/v5" do
    throw (IO.userError "FAIL: this Host's accumulator label is not index/trie-v3")
  IO.println s!"CONTROL: this Host's seed frame passes\nRED: {expected}\nRED: {expectedV2}"
