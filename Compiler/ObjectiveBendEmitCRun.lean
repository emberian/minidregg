/- Driver for the Objective Bend C backend and its differential reference.

  emit   CORE_JSON OUT_C                       ROM of the packet's term → C table
  run    CORE_JSON HEAP STACK TICKS OUT_STATE   the Lean machine: `runBounded`
  suite  CORE_JSON OUT_DIR HEAP STACK TICKS [RESPONSES_JSON]
                                               emit + every differential case
  bench  CORE_JSON HEAP STACK TICKS             time `runBounded` alone (one run)
  typing TYPED_JSON                            the preview path's checker verdict

`run` is the reference side of native/objective-emit/differential.sh. Its
outcome and final State are `runBounded`'s own (the function the soundness
theorems are about); the tick count and per-tick fingerprint come from
`traceRun`, whose final State must encode to the same bytes or the driver
refuses. Output: one JSON line, plus the canonical State bytes in OUT_STATE.

Activities: `suite` takes the item's responses (the preview's wire, decoded by
Compiler/ObjectiveBendDataWire, made terms by `Data.term`). Every case runs the
TURN CHAIN: `runBounded`; at a yield, `resume` with the next response and
continue under the remaining ticks of the same budget; with none left the
outcome is `yielded`. The C driver runs the same chain over the same responses
(interned as ROM roots). Per yield the suite also starts the C side from the
Lean yielded state and from the preview's checkpoint (the state after Plan
extraction, `yieldedPlan`), so a resume is checked across the codec too. -/
import Lean.Data.Json
import Theory.ObjectiveBendTyping
import Theory.ObjectiveBendDemandData
import Compiler.ObjectiveBendEmitC
import Compiler.ObjectiveBendDataWire

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

def compileChecked (term : Term) (responses : List Term := []) : IO Compiled := do
  match compile romCapacity romFuel term responses with
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
  | .yielded plan _ => ("yielded", toString plan)

def retained : Outcome → State
  | .finished _ s | .suspended _ s | .divergent _ s | .refused _ s | .yielded _ s => s

/-- Responses on the preview's wire (a JSON array of typed data), as the closed
terms `resume` evaluates. -/
def loadResponses (path : String) : IO (List Term) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let items ← IO.ofExcept json.getArr?
  items.toList.mapM fun item => do
    let data ← IO.ofExcept (Minidregg.Compiler.ObjectiveBendDataWire.decodeData 64 item)
    pure data.term

/-- One segment of the turn chain: `runBounded` for its outcome and State,
`traceRun` for the tick count and fingerprint; their final States must encode
identically. -/
def segment (compiled : Compiled) (limits : Limits) (ticks : Nat) (start : State) (hash : UInt64) :
    IO (Outcome × Nat × UInt64) := do
  let outcome := runBounded limits ticks start
  let (traced, used, hash) := traceRun limits ticks start 0 hash
  let some bytes := (encodeState compiled.rom (retained outcome)).toOption
    | throw (IO.userError "codec refused the runBounded state")
  let some tracedBytes := (encodeState compiled.rom traced).toOption
    | throw (IO.userError "codec refused the traced state")
  if bytes != tracedBytes then
    throw (IO.userError "traceRun and runBounded disagree on the final state")
  pure (outcome, used, hash)

/-- The turn chain from `start` with `responses` still to deliver: returns the
final outcome, ticks used, fingerprint, resumes performed, and every yielded
State met on the way that was resumed (with the response index it took). -/
def chain (compiled : Compiled) (limits : Limits) :
    List Term → Nat → Nat → State → Nat → UInt64 → Nat → Array (Nat × State) →
      IO (Outcome × Nat × UInt64 × Nat × Array (Nat × State))
  | responses, index, ticks, start, used, hash, resumes, yields => do
    let (outcome, spent, hash) ← segment compiled limits ticks start hash
    match outcome, responses with
    | .yielded _ waiting, response :: rest =>
      let some resumed := resume response waiting
        | throw (IO.userError "internal: a yielded state did not resume")
      chain compiled limits rest (index + 1) (ticks - spent) resumed (used + spent) hash (resumes + 1)
        (yields.push (index, waiting))
    | _, _ => pure (outcome, used + spent, hash, resumes, yields)

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

/-- One reference case: the turn chain from `start` (next response `first`)
under `limits`/`ticks`. Writes the final State bytes. Returns the expected JSON,
the final State, the ticks used, the next response index, and the yields. -/
def referenceCase (compiled : Compiled) (responses : List Term) (limits : Limits) (ticks : Nat)
    (start : State) (first : Nat) (statePath : String) :
    IO (Json × State × Nat × Nat × Array (Nat × State)) := do
  let (outcome, used, hash, resumes, yields) ←
    chain compiled limits (responses.drop first) first ticks start 0 fnvOffset 0 #[]
  let final := retained outcome
  let some bytes := (encodeState compiled.rom final).toOption
    | throw (IO.userError "codec refused the final state")
  IO.FS.writeBinFile statePath bytes
  let (kind, detail) := describe outcome
  pure (Json.mkObj [("outcome", toJson kind), ("detail", toJson detail),
    ("ticks", toJson used), ("trace", toJson (hex64 hash)),
    ("heap", toJson final.heap.size), ("stack", toJson final.stack.length),
    ("bytes", toJson bytes.size), ("resumes", toJson resumes)], final, used, first + resumes, yields)

/-- Every differential case for one packet. Tick and capacity cases are cut
from the full run's own numbers; resume cases start the C side from a State
the LEAN machine stopped in (Lean→C migration through the codec), with the
index of the next response. Activities add, per resumed yield, a start from the
yielded State and from the preview's checkpoint of it (`yieldedPlan`). -/
def suite (corePath outDir : String) (heap stack ticks : Nat) (responsesPath : Option String) :
    IO UInt32 := do
  let term ← loadTerm corePath
  let responses ← match responsesPath with
    | some path => loadResponses path
    | none => pure []
  let compiled ← compileChecked term responses
  match emitC compiled with
  | .error message => throw (IO.userError s!"C emission refused: {message}")
  | .ok text => IO.FS.writeFile s!"{outDir}/program.c" text
  let limits : Limits := ⟨heap, stack⟩
  let start := initial term
  let mut cases : Array Json := #[]
  let record := fun (name : String) (h s t : Nat) (resume : Option String) (first : Nat) (expected : Json) =>
    Json.mkObj [("case", toJson name), ("heap", toJson h), ("stack", toJson s), ("ticks", toJson t),
      ("resume", (match resume with | some r => toJson r | none => Json.null)), ("first", toJson first),
      ("state", toJson s!"{outDir}/{name}.lean.state"), ("lean", expected)]
  let (full, fullState, fullTicks, _, yields) ←
    referenceCase compiled responses limits ticks start 0 s!"{outDir}/full.lean.state"
  cases := cases.push (record "full" heap stack ticks none 0 full)
  if fullTicks ≥ 3 then
    for (name, cut) in [("ticks-third", fullTicks / 3), ("ticks-two-thirds", 2 * fullTicks / 3)] do
      let (expected, _, _, _, _) ← referenceCase compiled responses limits cut start 0 s!"{outDir}/{name}.lean.state"
      cases := cases.push (record name heap stack cut none 0 expected)
  if fullState.heap.size ≥ 2 then
    let tight : Limits := ⟨fullState.heap.size / 2, stack⟩
    let (expected, suspendedState, used, next, _) ←
      referenceCase compiled responses tight ticks start 0 s!"{outDir}/heap-half.lean.state"
    cases := cases.push (record "heap-half" tight.heap stack ticks none 0 expected)
    -- resume the capacity-suspended state with the original bounds
    let (resumed, _, _, _, _) ← referenceCase compiled responses limits (ticks - used) suspendedState next
      s!"{outDir}/resume-capacity.lean.state"
    cases := cases.push (record "resume-capacity" heap stack (ticks - used)
      (some s!"{outDir}/heap-half.lean.state") next resumed)
  let (stackTight, _, _, _, _) ←
    referenceCase compiled responses ⟨heap, 3⟩ ticks start 0 s!"{outDir}/stack-three.lean.state"
  cases := cases.push (record "stack-three" heap 3 ticks none 0 stackTight)
  if fullTicks ≥ 2 then
    let half := fullTicks / 2
    let (_, halfState, _, next, _) ←
      referenceCase compiled responses limits half start 0 s!"{outDir}/half.lean.state"
    let (resumed, _, _, _, _) ← referenceCase compiled responses limits (ticks - half) halfState next
      s!"{outDir}/resume-half.lean.state"
    cases := cases.push (record "resume-half" heap stack (ticks - half)
      (some s!"{outDir}/half.lean.state") next resumed)
  if !responses.isEmpty then
    -- the first yield with no response delivered
    let (firstYield, _, _, _, _) ← referenceCase compiled responses limits ticks start responses.length
      s!"{outDir}/no-response.lean.state"
    cases := cases.push (record "no-response" heap stack ticks none responses.length firstYield)
  let budget : Minidregg.Theory.ObjectiveBendDemandData.Budget := ⟨heap, ticks, 1048576⟩
  for (index, waiting) in yields do
    let yieldedPath := s!"{outDir}/yield-{index}.lean.state"
    let some yieldedBytes := (encodeState compiled.rom waiting).toOption
      | throw (IO.userError "codec refused a yielded state")
    IO.FS.writeBinFile yieldedPath yieldedBytes
    let (fromYield, _, _, _, _) ← referenceCase compiled responses limits ticks waiting index
      s!"{outDir}/resume-yield-{index}.lean.state"
    cases := cases.push (record s!"resume-yield-{index}" heap stack ticks (some yieldedPath) index fromYield)
    match Minidregg.Theory.ObjectiveBendDemandData.yieldedPlan limits budget waiting with
    | .error _ => pure ()   -- no checkpoint: the preview would refuse this yield
    | .ok extracted =>
      let checkpointPath := s!"{outDir}/checkpoint-{index}.lean.state"
      let some checkpointBytes := (encodeState compiled.rom extracted.state).toOption
        | throw (IO.userError "codec refused a checkpoint state")
      IO.FS.writeBinFile checkpointPath checkpointBytes
      let (fromCheckpoint, _, _, _, _) ← referenceCase compiled responses limits ticks extracted.state index
        s!"{outDir}/resume-checkpoint-{index}.lean.state"
      cases := cases.push (record s!"resume-checkpoint-{index}" heap stack ticks (some checkpointPath) index
        fromCheckpoint)
  IO.FS.writeFile s!"{outDir}/cases.json" ((Json.arr cases).compress ++ "\n")
  IO.println (Json.mkObj [("nodes", toJson compiled.rom.nodes.size),
    ("labels", toJson compiled.rom.labels.size), ("cases", toJson cases.size),
    ("fullTicks", toJson fullTicks), ("responses", toJson responses.length),
    ("yields", toJson yields.size)]).compress
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
def dispatch (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["emit", core, out] => emit core out
  | ["run", core, heap, stack, ticks, out] =>
    runReference core (← parseNat "heap" heap) (← parseNat "stack" stack) (← parseNat "ticks" ticks) out
  | ["suite", core, out, heap, stack, ticks] =>
    suite core out (← parseNat "heap" heap) (← parseNat "stack" stack) (← parseNat "ticks" ticks) none
  | ["suite", core, out, heap, stack, ticks, responses] =>
    suite core out (← parseNat "heap" heap) (← parseNat "stack" stack) (← parseNat "ticks" ticks)
      (some responses)
  | ["bench", core, heap, stack, ticks] =>
    bench core (← parseNat "heap" heap) (← parseNat "stack" stack) (← parseNat "ticks" ticks)
  | ["bench-raw", core, ticks] => benchRaw core (← parseNat "ticks" ticks)
  | ["typing", typed] => typing typed
  | _ =>
    IO.eprintln "usage: emit CORE OUT_C | run CORE HEAP STACK TICKS OUT_STATE | suite CORE OUT_DIR HEAP STACK TICKS [RESPONSES] | bench CORE HEAP STACK TICKS | typing TYPED | serve"
    pure 2

open Minidregg.Compiler.ObjectiveBendEmitCRun in
/-- `serve`: one long-lived worker for a batch driver. Each stdin line is the argument
list of a `suite` or `typing` command (words separated by one space); the answer is that
command's stdout lines, an `{"error":...}` line if it threw, then `##done RC`. The same
`dispatch` as the one-shot entry, so a served verdict is a one-shot verdict. -/
partial def serveLoop (stdin : IO.FS.Stream) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let words := (line.trimAscii.toString.splitOn " ").filter (· != "")
  let code ← try
      match words with
      | "suite" :: _ | "typing" :: _ => dispatch words
      | _ => do IO.println (Json.mkObj [("error", toJson "serve accepts suite and typing")]).compress; pure 2
    catch error =>
      IO.println (Json.mkObj [("error", toJson error.toString)]).compress
      pure 2
  IO.println s!"##done {code}"
  (← IO.getStdout).flush
  serveLoop stdin

def main (arguments : List String) : IO UInt32 := do
  try
    match arguments with
    | ["serve"] => serveLoop (← IO.getStdin)
    | _ => dispatch arguments
  catch error =>
    IO.eprintln (Json.mkObj [("error", toJson error.toString)]).compress
    pure 2
