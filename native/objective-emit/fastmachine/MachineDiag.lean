/- Diagnostic driver (lane FASTMACHINE step 1): where does `runBounded`'s time go?
  profile CORE TICKS        per-tick counters over the stepRaw iteration
  time    CORE MODE TICKS   one timed run; MODE = bounded | raw | rawlen | boundedcopy
Not a semantics; reads the reference functions only. -/
import Lean.Data.Json
import Theory.ObjectiveBendTyping
import Theory.ObjectiveBendDemandMachine
open Lean (Json toJson)
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine

namespace FastMachineDiag

partial def nodes : Term → Nat
  | .bound _ | .nat _ | .boolean _ | .label _ => 1
  | .lam b | .reflect b | .metadata b | .project b | .inject _ b | .perform b | .done b | .get b _ => 1 + nodes b
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b | .binary _ a b => 1 + nodes a + nodes b
  | .ifZero a b c | .ifBool a b c => 1 + nodes a + nodes b + nodes c
  | .extend a fs => 1 + nodes a + fs.foldl (fun n f => n + nodes f.2) 0
  | .record fs => 1 + fs.foldl (fun n f => n + nodes f.2) 0
  | .case a fs => 1 + nodes a + fs.foldl (fun n f => n + nodes f.2) 0

def loadTerm (path : String) : IO Term := do
  let text ← IO.FS.readFile path
  match (do Minidregg.Theory.ObjectiveBendTyping.decodeTerm 4096 (← (← Json.parse text).getObjVal? "term")) with
  | .ok t => pure t
  | .error e => throw (IO.userError e)

def termTag : Term → String
  | .bound _ => "bound" | .lam _ => "lam" | .app _ _ => "app" | .mix _ _ => "mix" | .fix _ _ => "fix"
  | .specification _ _ => "specification" | .prototype _ _ => "prototype" | .reflect _ => "reflect"
  | .metadata _ => "metadata" | .project _ => "project" | .nat _ => "nat" | .boolean _ => "boolean"
  | .label _ => "label" | .binary _ _ _ => "binary" | .extend _ _ => "extend" | .record _ => "record"
  | .get _ _ => "get" | .ifZero _ _ _ => "ifZero" | .inject _ _ => "inject" | .case _ _ => "case"
  | .ifBool _ _ _ => "ifBool" | .perform _ => "perform" | .done _ => "done"
def frameTag : Frame → String
  | .argument _ _ => "argument" | .update _ => "update" | .field _ => "field" | .reflect => "reflect"
  | .metadata => "metadata" | .project => "project" | .extend _ _ => "extend" | .condition _ _ _ => "condition"
  | .binaryLeft _ _ _ => "binaryLeft" | .binaryRight _ _ => "binaryRight" | .case _ _ => "case" | .ifBool _ _ _ => "ifBool"

structure Counters where
  kinds : Std.HashMap String Nat := {}
  ticks : Nat := 0
  heapWrites : Nat := 0       -- set! (enter suspended, update)
  heapPushes : Nat := 0
  heapSizeAtWrite : Nat := 0  -- Σ heap size at each tick that writes the heap (copy cost if shared)
  stackLenSum : Nat := 0      -- Σ stack length (what `step`'s List.length walks)
  maxStack : Nat := 0
  envIndexSum : Nat := 0      -- Σ de Bruijn index at `bound` (List indexing walk)
  maxEnvLen : Nat := 0
  fixRenameNodes : Nat := 0   -- Σ nodes renamed at `fix`
  mixRenameNodes : Nat := 0   -- Σ nodes renamed at `mix`
  fieldScan : Nat := 0        -- Σ record length at `field` frames (find?)
  extendWork : Nat := 0       -- Σ |inherited|·|fields| at extend frames
  caseScan : Nat := 0

def bump (c : Counters) (k : String) : Counters := {c with kinds := c.kinds.insert k (c.kinds.getD k 0 + 1)}

def observe (c : Counters) (s : State) : Counters :=
  let len := s.stack.length
  let c := {c with ticks := c.ticks + 1, stackLenSum := c.stackLenSum + len, maxStack := max c.maxStack len}
  let next := stepRaw s
  let pushes := next.heap.size - s.heap.size
  let c := if pushes > 0 then {c with heapPushes := c.heapPushes + pushes, heapSizeAtWrite := c.heapSizeAtWrite + s.heap.size} else c
  match s.control with
  | .evaluate t env =>
    let c := bump c s!"evaluate.{termTag t}"
    let c := {c with maxEnvLen := max c.maxEnvLen env.length}
    match t with
    | .bound i => {c with envIndexSum := c.envIndexSum + i}
    | .fix a b => {c with fixRenameNodes := c.fixRenameNodes + nodes a + nodes b}
    | .mix a b => {c with mixRenameNodes := c.mixRenameNodes + nodes a + nodes b}
    | _ => c
  | .enter a => match s.heap[a]? with
    | some (.suspended _) => {bump c "enter.suspended" with heapWrites := c.heapWrites + 1, heapSizeAtWrite := c.heapSizeAtWrite + s.heap.size}
    | some (.cached _ _) => bump c "enter.cached"
    | _ => bump c "enter.other"
  | .returned v => match s.stack with
    | [] => bump c "returned.empty"
    | f :: _ =>
      let c := bump c s!"returned.{frameTag f}"
      match f, v with
      | .update _, _ => {c with heapWrites := c.heapWrites + 1, heapSizeAtWrite := c.heapSizeAtWrite + s.heap.size}
      | .field _, .record fs => {c with fieldScan := c.fieldScan + fs.length}
      | .extend fs _, .record inh => {c with extendWork := c.extendWork + fs.length * inh.length}
      | .case arms _, _ => {c with caseScan := c.caseScan + arms.length}
      | _, _ => c
  | _ => bump c "terminal"

def profileLoop : Nat → Counters → State → Counters × State
  | 0, c, s => (c, s)
  | n+1, c, s => match s.control with
    | .complete _ | .refused _ | .blackhole _ | .yielded _ => (c, s)
    | _ => profileLoop n (observe c s) (stepRaw s)

def rawIterate : Nat → State → State
  | 0, s => s
  | n+1, s => match s.control with
    | .complete _ | .refused _ | .blackhole _ | .yielded _ => s
    | _ => rawIterate n (stepRaw s)

/-- stepRaw iteration plus `List.length` of the stack per tick, no retained state. -/
def rawLenIterate (limit : Nat) : Nat → State → State
  | 0, s => s
  | n+1, s => match s.control with
    | .complete _ | .refused _ | .blackhole _ | .yielded _ => s
    | _ => let next := stepRaw s
           if next.stack.length ≤ limit then rawLenIterate limit n next else next

def summarize (o : Outcome) : String × State := match o with
  | .finished _ s => ("finished", s) | .suspended .ticks s => ("suspended-ticks", s)
  | .suspended .capacity s => ("suspended-capacity", s) | .divergent _ s => ("divergent", s)
  | .refused _ s => ("refused", s) | .yielded _ s => ("yielded", s)

end FastMachineDiag
open FastMachineDiag

def main (args : List String) : IO UInt32 := do
  match args with
  | ["profile", core, ticks] =>
    let t ← loadTerm core
    let (c, s) := profileLoop ticks.toNat! {} (initial t)
    let kinds := c.kinds.toList.toArray.qsort (fun a b => a.2 > b.2)
    IO.println (Json.mkObj [("termNodes", toJson (nodes t)), ("ticks", toJson c.ticks), ("finalHeap", toJson s.heap.size),
      ("heapWrites", toJson c.heapWrites), ("heapPushes", toJson c.heapPushes), ("heapSizeAtWriteSum", toJson c.heapSizeAtWrite),
      ("stackLenSum", toJson c.stackLenSum), ("maxStack", toJson c.maxStack), ("envIndexSum", toJson c.envIndexSum),
      ("maxEnvLen", toJson c.maxEnvLen), ("fixRenameNodes", toJson c.fixRenameNodes), ("mixRenameNodes", toJson c.mixRenameNodes),
      ("fieldScan", toJson c.fieldScan), ("extendWork", toJson c.extendWork), ("caseScan", toJson c.caseScan),
      ("kinds", Json.mkObj (kinds.toList.map fun (k, n) => (k, toJson n)))]).pretty
    pure 0
  | ["time", core, mode, ticks] =>
    let t ← loadTerm core
    let n := ticks.toNat!
    let before ← IO.monoNanosNow
    let (kind, heap, stack) ← match mode with
      | "bounded" => let (k, s) := summarize (runBounded ⟨4000000, 4000000⟩ n (initial t)); pure (k, s.heap.size, s.stack.length)
      | "raw" => let s := rawIterate n (initial t); pure ("raw", s.heap.size, s.stack.length)
      | "rawlen" => let s := rawLenIterate 4000000 n (initial t); pure ("rawlen", s.heap.size, s.stack.length)
      | _ => throw (IO.userError "mode")
    let after ← IO.monoNanosNow
    IO.println (Json.mkObj [("mode", toJson mode), ("outcome", toJson kind), ("heap", toJson heap), ("stack", toJson stack),
      ("ms", toJson ((after - before).toFloat / 1e6))]).compress
    pure 0
  | _ => IO.eprintln "usage"; pure 2
