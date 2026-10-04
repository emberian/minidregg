/- Lane FASTMACHINE: the Lean machine's differential and timing driver.

This one source is compiled twice by `build.sh` (same directory):
* `objective-machine-reference`: as written. It imports only the definition
  modules, so `stepRaw`/`step`/`runBounded` run their own compiled code (the
  `@[csimp]` lemmas live in modules it does not import) and `forceUnderTest` is
  `forceReference`, a verbatim copy of `ObjectiveBendDemandData.forceWith`
  (an executable oracle, nothing is proved about it here).
* `objective-machine-fast`: with the `@FAST@` lines switched on, it imports
  `Theory.ObjectiveBendDemandData`, so every call below compiles to the
  `ObjectiveBendDemandMachineFast` implementations, and `forceUnderTest` is
  `ObjectiveBendDemandData.forceWith` (compiled as `forceWithFast`).

  cases CORE OUT_DIR   every case of one packet: one JSON line each on stdout,
                       the final State's checkpoint tokens in OUT_DIR/<case>.state
  bench CORE MODE      one timed run, MODE = run | force | step -/
import Lean.Data.Json
import Theory.ObjectiveBendDemandMachine
import Theory.ObjectiveBendCheckpoint
import Theory.ObjectiveBendTyping
-- @FAST@ import Theory.ObjectiveBendDemandData
open Lean (Json toJson)
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine

namespace FastMachineRun

/-- Verbatim copy of `ObjectiveBendDemandData.forceWith` (the oracle side). -/
def forceReference (policy : State → Bool) (limits : Limits) : Nat → State → Outcome × Nat
  | 0,state => (runBounded limits 0 state,0)
  | ticks+1,state => match state.control with
    | .complete _ | .refused _ | .blackhole _ | .yielded _ => (runBounded limits 0 state,ticks+1)
    | _ => if !policy state then (.suspended .capacity state,ticks+1) else
      match runBounded limits 1 state with
      | .suspended .ticks next => forceReference policy limits ticks next
      | other => (other,ticks)

def forceUnderTest := forceReference -- @REFERENCE@
-- @FAST@ def forceUnderTest := Minidregg.Theory.ObjectiveBendDemandData.forceWith

def stepTimes (limits : Limits) : Nat → State → Outcome
  | 0, state => .suspended .ticks state
  | n+1, state => match step limits state with
    | .suspended .ticks next => stepTimes limits n next
    | other => other

def loadTerm (path : String) : IO Term := do
  let text ← IO.FS.readFile path
  match (do Minidregg.Theory.ObjectiveBendTyping.decodeTerm 4096 (← (← Json.parse text).getObjVal? "term")) with
  | .ok term => pure term
  | .error message => throw (IO.userError s!"core packet refused: {message}")

def refusalName : Refusal → String
  | .unbound => "unbound" | .missingCell => "missingCell" | .missingField => "missingField"
  | .wrongValue => "wrongValue" | .invalidUpdate => "invalidUpdate" | .capacity => "capacity"
  | .missingArm => "missingArm" | .sharedEffect => "sharedEffect"

def describe : Outcome → String × String × State
  | .finished _ s => ("finished", "", s)
  | .suspended .ticks s => ("suspended-ticks", "", s)
  | .suspended .capacity s => ("suspended-capacity", "", s)
  | .divergent address s => ("divergent", toString address, s)
  | .refused reason s => ("refused", refusalName reason, s)
  | .yielded plan s => ("yielded", toString plan, s)

def tokenText (tokens : Minidregg.Theory.ObjectiveBendCheckpoint.Tokens) : String :=
  tokens.foldl (fun out token => match token with
    | .nat n => out ++ "n" ++ toString n ++ ";"
    | .text t => out ++ "t" ++ toString t.utf8ByteSize ++ ":" ++ t ++ ";") ""

def big : Limits := ⟨4000000, 4000000⟩
def budget : Nat := 20000000

/-- A policy that refuses large naturals: drives capacity suspensions through `forceWith`. -/
def smallNaturals (state : State) : Bool :=
  match state.control with
  | .returned (.natural n) => n < 1000
  | _ => true

def record (outDir name : String) (outcome : Outcome) (remaining : Option Nat) : IO State := do
  let (kind, detail, state) := describe outcome
  IO.FS.writeFile s!"{outDir}/{name}.state"
    (tokenText (Minidregg.Theory.ObjectiveBendCheckpoint.encodeState state))
  IO.println (Json.mkObj [("case", toJson name), ("outcome", toJson kind), ("detail", toJson detail),
    ("remaining", match remaining with | some r => toJson r | none => Json.null),
    ("heap", toJson state.heap.size), ("stack", toJson state.stack.length)]).compress
  pure state

def cases (corePath outDir : String) : IO UInt32 := do
  let term ← loadTerm corePath
  let start := initial term
  let full ← record outDir "run-full" (runBounded big budget start) none
  let (forced, remaining) := forceUnderTest (fun _ => true) big budget start
  let _ ← record outDir "force-full" forced (some remaining)
  let used := budget - remaining
  let _ ← record outDir "run-third" (runBounded big (used / 3) start) none
  let _ ← record outDir "run-two-thirds" (runBounded big (2 * used / 3) start) none
  let _ ← record outDir "step-third" (stepTimes big (used / 3) start) none
  let tight : Limits := ⟨full.heap.size / 2, big.stack⟩
  let halfHeap ← record outDir "run-heap-half" (runBounded tight budget start) none
  let _ ← record outDir "run-resume-capacity" (runBounded big budget halfHeap) none
  let _ ← record outDir "run-stack-three" (runBounded ⟨big.heap, 3⟩ budget start) none
  let half ← record outDir "run-half" (runBounded big (used / 2) start) none
  let _ ← record outDir "run-resume-half" (runBounded big budget half) none
  let (o, r) := forceUnderTest smallNaturals big budget start
  let _ ← record outDir "force-small-naturals" o (some r)
  let (o, r) := forceUnderTest (fun _ => true) tight budget start
  let _ ← record outDir "force-heap-half" o (some r)
  let (o, r) := forceUnderTest (fun _ => true) ⟨big.heap, 3⟩ budget start
  let _ ← record outDir "force-stack-three" o (some r)
  let (o, r) := forceUnderTest (fun _ => true) big (used / 2) start
  let forcedHalf ← record outDir "force-half" o (some r)
  let (o, r) := forceUnderTest (fun _ => true) big budget forcedHalf
  let _ ← record outDir "force-resume-half" o (some r)
  match full.control, resume (.record []) full with
  | .yielded _, some resumed =>
    let _ ← record outDir "run-resume-yield" (runBounded big budget resumed) none
    let (o, r) := forceUnderTest (fun _ => true) big budget resumed
    let _ ← record outDir "force-resume-yield" o (some r)
  | _, _ => pure ()
  pure 0

def bench (corePath mode : String) : IO UInt32 := do
  let term ← loadTerm corePath
  let before ← IO.monoNanosNow
  let (kind, heap, stack, remaining) ← match mode with
    | "run" => let (k, _, s) := describe (runBounded big budget (initial term)); pure (k, s.heap.size, s.stack.length, 0)
    | "force" => let (o, r) := forceUnderTest (fun _ => true) big budget (initial term)
                 let (k, _, s) := describe o; pure (k, s.heap.size, s.stack.length, r)
    | "step" => let (k, _, s) := describe (stepTimes big budget (initial term)); pure (k, s.heap.size, s.stack.length, 0)
    | _ => throw (IO.userError "bench MODE: run | force | step")
  let after ← IO.monoNanosNow
  IO.println (Json.mkObj [("mode", toJson mode), ("outcome", toJson kind), ("heap", toJson heap),
    ("stack", toJson stack), ("ticks", toJson (if mode == "force" then budget - remaining else 0)),
    ("ms", toJson ((after - before).toFloat / 1e6))]).compress
  pure 0

end FastMachineRun

def main (arguments : List String) : IO UInt32 := do
  try
    match arguments with
    | ["cases", core, outDir] => FastMachineRun.cases core outDir
    | ["bench", core, mode] => FastMachineRun.bench core mode
    | _ => IO.eprintln "usage: cases CORE OUT_DIR | bench CORE MODE"; pure 2
  catch error =>
    IO.eprintln (Json.mkObj [("error", toJson error.toString)]).compress
    pure 2
