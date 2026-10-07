/- The checkpoint-transparency differential (gate row `transparency` of
scripts/check-objective-proofs.sh).

  lake env lean --run scripts/ObjectiveCheckpointTransparency.lean CORE_JSON HEAP STACK TICKS RESPONSES_JSON [MUTANT]

One activity, two turn chains over the same responses, every segment under the same full
tick budget and the same limits counted from the segment's own heap end
(`ObjectiveBendDemandCollect.limitsPast`, what `Kernel.ObjectiveActivity.segmentLimits`
runs a segment under):

  lazy    resume the YIELDED state (the machine's own, uncollected);
  kernel  resume what `Kernel.ObjectiveActivity.runSegment` stores: the Plan
          extraction's state, settled and collected (`ObjectiveBendDemandCollect.checkpoint`).

Per segment both chains must end alike: the same outcome constructor (and reason), the
same extracted Plan Data at a yield, the same result Data at the end, and the kernel
chain may use no more ticks than the lazy one (forcing only ever saves work). The
number of segments must agree. Each segment prints one JSON row (the outcome, both
tick counts, both checkpoint byte counts as `checkpointBytes` encodes them); the last
line is the verdict. Exit 0 iff every segment agrees.

What this measures and what it does not: it EXECUTES the claim that
`Kernel.ObjectiveResumeContract.ForcingTransparent` states, on these programs and these
responses: an executed cross-check of `forcingTransparent_of_yieldedPlan` (proved at every
lexically valid yield), and of the codec and kernel paths around it the proof does not cover.

MUTANT (self-test only): `drop-stack-roots` stores a checkpoint whose collection traces
only the control, so cells live through the stack are dropped. The gate requires the
row to go red under it. -/
import Lean.Data.Json
import Kernel.ObjectiveActivityWire
import Compiler.ObjectiveBendDataWire
import Theory.ObjectiveBendDemandCollect

open Lean (Json toJson)
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open Minidregg.Theory.ObjectiveBendDemandData
open Minidregg.Theory.ObjectiveBendDemandCollect

namespace Minidregg.Scripts.CheckpointTransparency

def loadTerm (path : String) : IO Term := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  IO.ofExcept (Minidregg.Theory.ObjectiveBendTyping.decodeTerm 4096 (← IO.ofExcept (json.getObjVal? "term")))

def loadResponses (path : String) : IO (List Term) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let items ← IO.ofExcept json.getArr?
  items.toList.mapM fun item => do
    let data ← IO.ofExcept (Minidregg.Compiler.ObjectiveBendDataWire.decodeData 64 item)
    pure data.term

/-- The planted fault: collect from the control alone (the stack's cells are dropped). -/
def dropStackRoots (state : State) : State :=
  let rootless : State := {state with stack := []}
  let marks := liveMarks rootless
  let ranked := rankTable marks
  let f := relocate state.heap.size ranked.2 ranked.1
  ⟨compact f state.heap marks, renameControl f state.control, state.stack.map (renameFrame f)⟩

def store (mutant : Option String) (state : State) : State :=
  match mutant with
  | some "drop-stack-roots" => dropStackRoots (settle state)
  | _ => checkpoint state

/-- `runBounded`, with the number of transitions it took. -/
def counted (limits : Limits) : Nat → State → Nat → Outcome × Nat
  | 0, state, used => (runBounded limits 0 state, used)
  | ticks + 1, state, used => match step limits state with
    | .suspended .ticks next => counted limits ticks next (used + 1)
    | other => (other, used)

def kind : Outcome → String
  | .finished _ _ => "finished"
  | .suspended .ticks _ => "suspended-ticks"
  | .suspended .capacity _ => "suspended-capacity"
  | .divergent _ _ => "divergent"
  | .refused reason _ => s!"refused:{reprStr reason}"
  | .yielded _ _ => "yielded"

/-- What a segment ends in, as comparable text: the outcome, and the extracted Plan or
result Data (canonically encoded). -/
def observe (limits : Limits) (budget : Budget) (outcome : Outcome) : String :=
  let show? (r : Except (Failure × State) Result) : String := match r with
    | .ok result => match encoded budget.nodes result.value with
      | some bytes => toString bytes
      | none => "unencodable"
    | .error (failure, _) => s!"extraction-failed:{reprStr failure}"
  match outcome with
  | .yielded _ y => s!"yielded {show? (yieldedPlan limits budget y)}"
  | .finished _ y => s!"finished {show? (complete limits budget y)}"
  | other => kind other

structure Chain where
  state : State
  done : Bool := false

def main (arguments : List String) : IO UInt32 := do
  let (core, heap, stack, ticks, responsesPath, mutant) ← match arguments with
    | [c, h, s, t, r] => pure (c, h, s, t, r, none)
    | [c, h, s, t, r, m] => pure (c, h, s, t, r, some m)
    | _ => throw (IO.userError "usage: CORE_JSON HEAP STACK TICKS RESPONSES_JSON [MUTANT]")
  let some heap := heap.toNat? | throw (IO.userError "HEAP: natural")
  let some stack := stack.toNat? | throw (IO.userError "STACK: natural")
  let some ticks := ticks.toNat? | throw (IO.userError "TICKS: natural")
  let term ← loadTerm core
  let responses ← loadResponses responsesPath
  let limits : Limits := ⟨heap, stack⟩
  let budget : Budget := ⟨heap, ticks, 1048576⟩
  let mut lazy := initial term
  let mut kernel := initial term
  let mut agree := true
  let mut segment := 0
  let mut pending := responses
  repeat
    let lazyLimits := limitsPast limits lazy
    let kernelLimits := limitsPast limits kernel
    let (lazyOutcome, lazyTicks) := counted lazyLimits ticks lazy 0
    let (kernelOutcome, kernelTicks) := counted kernelLimits ticks kernel 0
    let lazyObserved := observe lazyLimits budget lazyOutcome
    let kernelObserved := observe kernelLimits budget kernelOutcome
    -- the checkpoint each chain would store at this yield
    let (lazyStored, kernelStored) := match lazyOutcome, kernelOutcome with
      | .yielded _ y, .yielded _ y' =>
        (some y, match yieldedPlan kernelLimits budget y' with
          | .ok extracted => some (store mutant extracted.state)
          | .error _ => none)
      | _, _ => (none, none)
    let bytes := fun (s : Option State) => match s with
      | some s => toJson (Minidregg.Kernel.ObjectiveActivityWire.checkpointBytes (collect s)).length
      | none => Json.null
    let kernelBytes := match kernelStored with
      | some s => toJson (Minidregg.Kernel.ObjectiveActivityWire.checkpointBytes s).length
      | none => Json.null
    let same := lazyObserved == kernelObserved && kernelTicks ≤ lazyTicks
    if !same then agree := false
    let row : List (String × Json) := [("segment", toJson segment), ("outcome", toJson (kind lazyOutcome)),
      ("lazyTicks", toJson lazyTicks), ("kernelTicks", toJson kernelTicks),
      ("lazyCollectedBytes", bytes lazyStored), ("kernelCheckpointBytes", kernelBytes),
      ("agree", toJson same)]
    let detail : List (String × Json) :=
      if same then [] else [("lazy", toJson lazyObserved), ("kernel", toJson kernelObserved)]
    IO.println (Json.mkObj (row ++ detail)).compress
    segment := segment + 1
    match lazyOutcome, kernelStored, pending with
    | .yielded _ y, some stored, response :: rest =>
      match resume response y, resume response stored with
      | some l, some k => lazy := l; kernel := k; pending := rest
      | _, _ => agree := false; break
    | _, _, _ => break
  IO.println (Json.mkObj [("segments", toJson segment), ("responsesLeft", toJson pending.length),
    ("mutant", toJson (mutant.getD "none")), ("verdict", toJson (if agree then "agree" else "DISAGREE"))]).compress
  pure (if agree then 0 else 1)

end Minidregg.Scripts.CheckpointTransparency

def main (arguments : List String) : IO UInt32 :=
  Minidregg.Scripts.CheckpointTransparency.main arguments
