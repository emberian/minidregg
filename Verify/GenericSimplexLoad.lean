import Compiler.GenericSimplexIO
namespace Minidregg.Verify.GenericSimplexLoad
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexRelative
open Minidregg.Compiler.GenericSimplexCodec
open Minidregg.Compiler.GenericSimplexIO
set_option autoImplicit false

/-! Per-operation cost of the native agreement layer over a long busy run. Four replicas,
instant delivery, each a journal image driven through `appendRestored`: every input is
encoded as a journal entry, replayed through `Replica.step` under the deployed cSHAKE256
chain digest, and framed for the append; outputs are drained and acknowledged (`flush`),
committed payloads taken (`consume`), and the image is checkpointed every `checkpointEvery`
deltas, as the standing replica does. Signatures, MACs and the disk are not in it.
Operation k: every replica's checker reports source record k; the network then runs until
every replica has committed it. Reports wall time per operation over consecutive windows,
and the size of a checkpoint, which must not grow with the committed height. -/

def context : Context :=
  ⟨[1,2,3], 0, [4,5,6], ⟨4,1,100,64,0⟩,
    (List.range 4).map fun i => List.replicate 1952 (UInt8.ofNat (i + 1))⟩
def payloadOf (k : Nat) : Bytes := [1, UInt8.ofNat (k / 65536 % 256), UInt8.ofNat (k / 256 % 256), UInt8.ofNat (k % 256)]

structure Net where
  nodes : Array (Restored context)
  queue : Array (Nat × WireMessage)
  head : Nat := 0
  inputs : Nat := 0
  bytes : Nat := 0
  failed : Bool := false

def append (r : Restored context) (entry : Entry) : Option (Restored context × Nat) :=
  (appendRestored r [encodeEntry entry] []).map fun (next,frame) => (next,frame.length)

/-- One acknowledged input at replica `i`, then what its driver does with the outputs. -/
def act (n : Net) (i : Nat) (input : WireInput) : Net :=
  match n.nodes[i]?.bind (append · (.input input)) with
  | none => { n with failed := true }
  | some (r,size) =>
    let replica := r.state
    let fanned := replica.sends.foldl (fun out m =>
      (List.range context.config.parties).foldl (fun out peer => if peer != i then out.push (peer,m) else out) out) #[]
    let queue := n.queue ++ fanned ++ replica.owed.toArray
    let r := if replica.sends.isEmpty && replica.owed.isEmpty then some (r,0)
      else append r (.flush replica.sends.length replica.owed.length)
    let r := r.bind fun (r,flushed) =>
      if replica.committed.isEmpty then some (r,flushed)
      else (append r (.consume replica.committed.length)).map fun (r,taken) => (r,flushed + taken)
    match r with
    | none => { n with failed := true }
    | some (r,more) =>
      let r := if r.deltas ≥ checkpointEvery then (checkpointRestored r).1 else r
      { n with nodes := n.nodes.set! i r, queue := queue, inputs := n.inputs + 1, bytes := n.bytes + size + more }

partial def drain (n : Net) (done : Net → Bool) (fuel : Nat) : Net :=
  if fuel == 0 || n.failed || done n then n else
  match n.queue[n.head]? with
  | none => n
  | some (i,m) =>
    let n := { n with head := n.head + 1 }
    let n := if n.head ≥ 4096 then { n with queue := n.queue.extract n.head n.queue.size, head := 0 } else n
    drain (act n i (.delivery m)) done (fuel - 1)

def committed (k : Nat) (n : Net) : Bool :=
  n.nodes.all fun r => r.state.records ≥ k

def main (args : List String) : IO UInt32 := do
  let total := (args.head? >>= String.toNat?).getD 1000
  let window := (args[1]? >>= String.toNat?).getD 100
  let mut nodes := #[]
  for i in List.range context.config.parties do
    let some r := openRestored context (Log.encode ⟨⟨context,i,0,[],[],none⟩,[]⟩)
      | IO.eprintln "FAIL base journal refused"; return 1
    nodes := nodes.push r
  -- The start replicas' own first outputs, as the driver sends them.
  let mut n : Net := { nodes := nodes, queue := #[] }
  for i in List.range context.config.parties do n := act n i .poll
  let mut t0 ← IO.monoNanosNow
  let mut inputs0 := n.inputs
  let mut bytes0 := n.bytes
  IO.println "ops\tus_per_op\tinputs_per_op\tus_per_input\tjournal_bytes_per_op\tviews\theight\tcheckpoint_bytes"
  for k in List.range total do
    let k := k + 1
    for i in List.range context.config.parties do
      n := act n i (.checked (k - 1) [payloadOf k])
    n := drain n (committed k) 1000000
    unless committed k n && !n.failed do
      IO.eprintln s!"FAIL op {k} did not commit"
      return 1
    if k % window == 0 then
      let t1 ← IO.monoNanosNow
      let some r := n.nodes[0]? | return 1
      let us := (t1 - t0) / 1000 / window
      let ins := (n.inputs - inputs0) / window
      IO.println s!"{k}\t{us}\t{ins}\t{(t1 - t0) / 1000 / max 1 (n.inputs - inputs0)}\t{(n.bytes - bytes0) / window}\t{r.state.core.views.length}\t{r.state.height}\t{(checkpointRestored r).2.length}"
      (← IO.getStdout).flush
      t0 ← IO.monoNanosNow
      inputs0 := n.inputs
      bytes0 := n.bytes
  return 0
end Minidregg.Verify.GenericSimplexLoad
def main (args : List String) : IO UInt32 := Minidregg.Verify.GenericSimplexLoad.main args
