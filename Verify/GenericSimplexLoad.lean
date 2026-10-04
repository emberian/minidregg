import Kernel.GenericSimplex
namespace Minidregg.Verify.GenericSimplexLoad
open Minidregg.Kernel.GenericSimplex
set_option autoImplicit false

/-! Per-operation cost of the agreement engine over a long busy run. Four
replicas, instant delivery. Operation k: every replica checks the exact source
history [p1..pk]; the network then runs until every replica's committed tip
carries pk. Reports wall time per operation over consecutive windows. -/

def cfg : Config := ⟨4,1,100,64,0⟩
def payloadOf (k : Nat) : Bytes := [1, UInt8.ofNat (k / 65536 % 256), UInt8.ofNat (k / 256 % 256), UInt8.ofNat (k % 256)]

structure Net where
  nodes : Array State
  queue : Array (Nat × Message)
  head : Nat := 0
  inputs : Nat := 0

def fan (s : State) (old : Nat) : Array (Nat × Message) := Id.run do
  let mut out := #[]
  for m in s.outbox.drop old do
    for r in List.range cfg.parties do
      if r != s.self then out := out.push (r,m)
  return out

def act (n : Net) (i : Nat) (input : Input) : Net :=
  let old := n.nodes[i]!
  let next := step cfg old input
  { n with nodes := n.nodes.set! i next, queue := n.queue ++ fan next old.outbox.length,
           inputs := n.inputs + 1 }

partial def drain (n : Net) (done : Net → Bool) (fuel : Nat) : Net :=
  if fuel == 0 || done n then n else
  match n.queue[n.head]? with
  | none => n
  | some (i,m) =>
    let n := { n with head := n.head + 1 }
    let n := if n.head ≥ 4096 then { n with queue := n.queue.extract n.head n.queue.size, head := 0 } else n
    drain (act n i (.delivery m)) done (fuel - 1)

def committed (k : Nat) (n : Net) : Bool :=
  n.nodes.all fun s => s.committedTip.getLast? == some (payloadOf k)

def initial : Net :=
  let nodes := (List.range cfg.parties).map fun i => start cfg i 0 [] []
  { nodes := nodes.toArray, queue := nodes.foldl (fun q s => q ++ fan s 0) #[] }

def main (args : List String) : IO UInt32 := do
  let total := (args.head? >>= String.toNat?).getD 1000
  let window := (args[1]? >>= String.toNat?).getD 100
  let mut n := initial
  let mut history : Block := []
  let mut t0 ← IO.monoNanosNow
  let mut inputs0 := 0
  IO.println "ops\tus_per_op\tinputs_per_op\tus_per_input\tviews\toutbox\taudit\tchecked\tcurrent"
  for k in List.range total do
    let k := k + 1
    history := history ++ [payloadOf k]
    for i in List.range cfg.parties do
      n := act n i (.checked history)
    n := drain n (committed k) 1000000
    unless committed k n do
      IO.eprintln s!"FAIL op {k} did not commit"
      return 1
    if k % window == 0 then
      let t1 ← IO.monoNanosNow
      let s := n.nodes[0]!
      let us := (t1 - t0) / 1000 / window
      let ins := (n.inputs - inputs0) / window
      IO.println s!"{k}\t{us}\t{ins}\t{(t1 - t0) / 1000 / max 1 (n.inputs - inputs0)}\t{s.views.length}\t{s.outbox.length}\t{s.audit.length}\t{s.checked.length}\t{s.current}"
      (← IO.getStdout).flush
      t0 ← IO.monoNanosNow
      inputs0 := n.inputs
  return 0
end Minidregg.Verify.GenericSimplexLoad
def main (args : List String) : IO UInt32 := Minidregg.Verify.GenericSimplexLoad.main args
