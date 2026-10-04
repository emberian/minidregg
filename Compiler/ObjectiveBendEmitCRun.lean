/- Driver for the Objective Bend C backend and its differential reference.

  emit   CORE_JSON OUT_C                       ROM of the packet's term → C table
  run    CORE_JSON HEAP STACK TICKS OUT_STATE   the Lean machine: `runBounded`
  suite  CORE_JSON OUT_DIR HEAP STACK TICKS     emit + every differential case
  bench  CORE_JSON HEAP STACK TICKS             time `runBounded` alone (one run)
  typing TYPED_JSON                            the preview path's checker verdict

`run` is the reference side of native/objective-emit/differential.sh. Its
outcome and final State are `runBounded`'s own (the function the soundness
theorems are about); the tick count and per-tick fingerprint come from
`traceRun`, whose final State must encode to the same bytes or the driver
refuses. Output: one JSON line, plus the canonical State bytes in OUT_STATE. -/
import Lean.Data.Json
import Theory.ObjectiveBendTyping
import Compiler.ObjectiveBendEmitC

open Lean (Json toJson)
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendTyping
open Minidregg.Compiler.ObjectiveBendEmitC

namespace Minidregg.Compiler.ObjectiveBendEmitCRun

def romCapacity : Nat := 1000000
def romFuel : Nat := 100000

def decodeCore (text : String) : Except String Term := do
  decodeTerm 4096 (← (← Json.parse text).getObjVal? "term")

def loadTerm (path : String) : IO Term := do
  let text ← IO.FS.readFile path
  match decodeCore text with
  | .ok term => pure term
  | .error message => throw (IO.userError s!"core packet refused: {message}")

def compileChecked (term : Term) : IO Compiled := do
  match compile romCapacity romFuel term with
  | .error message => throw (IO.userError s!"ROM refused: {message}")
  | .ok compiled =>
    match compiled.rom.audit (romFuel + compiled.rom.nodes.size) with
    | .error message => throw (IO.userError s!"ROM audit failed: {message}")
    | .ok () => pure compiled

def hex64 (value : UInt64) : String :=
  let digits := Nat.toDigits 16 value.toNat
  String.ofList (List.replicate (16 - digits.length) '0' ++ digits)

def parseNat (label text : String) : IO Nat :=
  match text.toNat? with
  | some n => pure n
  | none => throw (IO.userError s!"{label}: decimal natural required")

def describe : Outcome → String × String
  | .finished _ _ => ("finished", "")
  | .suspended .ticks _ => ("suspended-ticks", "")
  | .suspended .capacity _ => ("suspended-capacity", "")
  | .divergent address _ => ("divergent", toString address)
  | .refused reason _ => ("refused", refusalName reason)

def retained : Outcome → State
  | .finished _ s | .suspended _ s | .divergent _ s | .refused _ s => s

def runReference (corePath : String) (heap stack ticks : Nat) (outPath : String) : IO UInt32 := do
  let term ← loadTerm corePath
  let compiled ← compileChecked term
  let limits : Limits := ⟨heap, stack⟩
  let start := initial term
  let outcome := runBounded limits ticks start
  let final := retained outcome
  let (traced, used, hash) := traceRun limits ticks start 0 fnvOffset
  let some bytes := (encodeState compiled.rom final).toOption
    | throw (IO.userError "codec refused the runBounded state")
  let some tracedBytes := (encodeState compiled.rom traced).toOption
    | throw (IO.userError "codec refused the traced state")
  if bytes != tracedBytes then
    throw (IO.userError "traceRun and runBounded disagree on the final state")
  IO.FS.writeBinFile outPath bytes
  let (kind, detail) := describe outcome
  IO.println (Json.mkObj [("outcome", toJson kind), ("detail", toJson detail),
    ("ticks", toJson used), ("trace", toJson (hex64 hash)),
    ("heap", toJson final.heap.size), ("stack", toJson final.stack.length),
    ("bytes", toJson bytes.size)]).compress
  pure 0

/-- One reference case: `runBounded` from `start` under `limits`/`ticks`, with
the traced tick count and fingerprint. Writes the final State bytes. -/
def referenceCase (compiled : Compiled) (limits : Limits) (ticks : Nat) (start : State)
    (statePath : String) : IO (Json × State × Nat) := do
  let outcome := runBounded limits ticks start
  let final := retained outcome
  let (traced, used, hash) := traceRun limits ticks start 0 fnvOffset
  let some bytes := (encodeState compiled.rom final).toOption
    | throw (IO.userError "codec refused the runBounded state")
  let some tracedBytes := (encodeState compiled.rom traced).toOption
    | throw (IO.userError "codec refused the traced state")
  if bytes != tracedBytes then
    throw (IO.userError "traceRun and runBounded disagree on the final state")
  IO.FS.writeBinFile statePath bytes
  let (kind, detail) := describe outcome
  pure (Json.mkObj [("outcome", toJson kind), ("detail", toJson detail),
    ("ticks", toJson used), ("trace", toJson (hex64 hash)),
    ("heap", toJson final.heap.size), ("stack", toJson final.stack.length),
    ("bytes", toJson bytes.size)], final, used)

/-- Every differential case for one packet. Tick and capacity cases are cut
from the full run's own numbers; resume cases start the C side from a State
the LEAN machine suspended in (Lean→C migration through the codec). -/
def suite (corePath outDir : String) (heap stack ticks : Nat) : IO UInt32 := do
  let term ← loadTerm corePath
  let compiled ← compileChecked term
  match emitC compiled with
  | .error message => throw (IO.userError s!"C emission refused: {message}")
  | .ok text => IO.FS.writeFile s!"{outDir}/program.c" text
  let limits : Limits := ⟨heap, stack⟩
  let start := initial term
  let mut cases : Array Json := #[]
  let record := fun (name : String) (h s t : Nat) (resume : Option String) (expected : Json) =>
    Json.mkObj [("case", toJson name), ("heap", toJson h), ("stack", toJson s), ("ticks", toJson t),
      ("resume", (match resume with | some r => toJson r | none => Json.null)),
      ("state", toJson s!"{outDir}/{name}.lean.state"), ("lean", expected)]
  let (full, fullState, fullTicks) ← referenceCase compiled limits ticks start s!"{outDir}/full.lean.state"
  cases := cases.push (record "full" heap stack ticks none full)
  if fullTicks ≥ 3 then
    for (name, cut) in [("ticks-third", fullTicks / 3), ("ticks-two-thirds", 2 * fullTicks / 3)] do
      let (expected, _, _) ← referenceCase compiled limits cut start s!"{outDir}/{name}.lean.state"
      cases := cases.push (record name heap stack cut none expected)
  if fullState.heap.size ≥ 2 then
    let tight : Limits := ⟨fullState.heap.size / 2, stack⟩
    let (expected, suspendedState, used) ←
      referenceCase compiled tight ticks start s!"{outDir}/heap-half.lean.state"
    cases := cases.push (record "heap-half" tight.heap stack ticks none expected)
    -- resume the capacity-suspended state with the original bounds
    let (resumed, _, _) ← referenceCase compiled limits (ticks - used) suspendedState
      s!"{outDir}/resume-capacity.lean.state"
    cases := cases.push (record "resume-capacity" heap stack (ticks - used)
      (some s!"{outDir}/heap-half.lean.state") resumed)
  let (stackTight, _, _) ← referenceCase compiled ⟨heap, 3⟩ ticks start s!"{outDir}/stack-three.lean.state"
  cases := cases.push (record "stack-three" heap 3 ticks none stackTight)
  if fullTicks ≥ 2 then
    let half := fullTicks / 2
    let (_, halfState, _) ← referenceCase compiled limits half start s!"{outDir}/half.lean.state"
    let (resumed, _, _) ← referenceCase compiled limits (ticks - half) halfState
      s!"{outDir}/resume-half.lean.state"
    cases := cases.push (record "resume-half" heap stack (ticks - half)
      (some s!"{outDir}/half.lean.state") resumed)
  IO.FS.writeFile s!"{outDir}/cases.json" ((Json.arr cases).compress ++ "\n")
  IO.println (Json.mkObj [("nodes", toJson compiled.rom.nodes.size),
    ("labels", toJson compiled.rom.labels.size), ("cases", toJson cases.size),
    ("fullTicks", toJson fullTicks)]).compress
  pure 0

/-- One timed `runBounded` (plus the State encoding), for the wall-time row. -/
def bench (corePath : String) (heap stack ticks : Nat) : IO UInt32 := do
  let term ← loadTerm corePath
  let compiled ← compileChecked term
  let before ← IO.monoMsNow
  let outcome := runBounded ⟨heap, stack⟩ ticks (initial term)
  let some bytes := (encodeState compiled.rom (retained outcome)).toOption
    | throw (IO.userError "codec refused the state")
  let after ← IO.monoMsNow
  let (kind, _) := describe outcome
  IO.println (Json.mkObj [("outcome", toJson kind), ("bytes", toJson bytes.size),
    ("runBoundedPlusEncodeMs", toJson (after - before))]).compress
  pure 0

/-- Diagnostic: `stepRaw` iterated `ticks` times WITHOUT `step`'s capacity
check (which keeps the pre-transition State alive across the transition).
Not a reference semantics; it isolates the cost of retaining that State. -/
def rawIterate : Nat → State → State
  | 0, s => s
  | n+1, s => rawIterate n (stepRaw s)

def benchRaw (corePath : String) (ticks : Nat) : IO UInt32 := do
  let term ← loadTerm corePath
  let compiled ← compileChecked term
  let before ← IO.monoMsNow
  let final := rawIterate ticks (initial term)
  let some bytes := (encodeState compiled.rom final).toOption
    | throw (IO.userError "codec refused the state")
  let after ← IO.monoMsNow
  IO.println (Json.mkObj [("bytes", toJson bytes.size), ("heap", toJson final.heap.size),
    ("stepRawIteratePlusEncodeMs", toJson (after - before))]).compress
  pure 0

def emit (corePath outPath : String) : IO UInt32 := do
  let compiled ← compileChecked (← loadTerm corePath)
  match emitC compiled with
  | .error message => throw (IO.userError s!"C emission refused: {message}")
  | .ok text =>
    IO.FS.writeFile outPath text
    IO.println (Json.mkObj [("nodes", toJson compiled.rom.nodes.size),
      ("labels", toJson compiled.rom.labels.size), ("entry", toJson compiled.entry),
      ("audit", toJson "every node decodes to its key; fix/mix pointers equal the stepRaw probes")]).compress
    pure 0

def typing (typedPath : String) : IO UInt32 := do
  let text ← IO.FS.readFile typedPath
  let verdict : Except String String := do
    let packet ← decodePacket (← Json.parse text)
    if !packet.context.isEmpty then throw "open context"
    match check packet.source packet.context packet.fuel with
    | some checked => pure s!"accepted:{(typeJson checked.type).compress}"
    | none => pure "refused"
  match verdict with
  | .ok v => IO.println (Json.mkObj [("typing", toJson v)]).compress; pure 0
  | .error message => IO.println (Json.mkObj [("typing", toJson s!"undecodable:{message}")]).compress; pure 0

end Minidregg.Compiler.ObjectiveBendEmitCRun

open Minidregg.Compiler.ObjectiveBendEmitCRun in
def main (arguments : List String) : IO UInt32 := do
  try
    match arguments with
    | ["emit", core, out] => emit core out
    | ["run", core, heap, stack, ticks, out] =>
      runReference core (← parseNat "heap" heap) (← parseNat "stack" stack) (← parseNat "ticks" ticks) out
    | ["suite", core, out, heap, stack, ticks] =>
      suite core out (← parseNat "heap" heap) (← parseNat "stack" stack) (← parseNat "ticks" ticks)
    | ["bench", core, heap, stack, ticks] =>
      bench core (← parseNat "heap" heap) (← parseNat "stack" stack) (← parseNat "ticks" ticks)
    | ["bench-raw", core, ticks] => benchRaw core (← parseNat "ticks" ticks)
    | ["typing", typed] => typing typed
    | _ =>
      IO.eprintln "usage: emit CORE OUT_C | run CORE HEAP STACK TICKS OUT_STATE | suite CORE OUT_DIR HEAP STACK TICKS | bench CORE HEAP STACK TICKS | typing TYPED"
      pure 2
  catch error =>
    IO.eprintln (Json.mkObj [("error", toJson error.toString)]).compress
    pure 2
