/- Full Core4 data extraction through the same bounded demand machine. Global
node/tick/canonical encoded output budgets are shared across all fields. Budget suspension
retains the exact graph, never a partial successful Plan or invalid-program claim. -/
import Theory.ObjectiveBendDemandMachine
import Theory.ObjectiveBendTypes
namespace Minidregg.Theory.ObjectiveBendDemandData
open ObjectiveBendDemandMachine
inductive Data where
  | natural (value : Nat) | boolean (value : Bool) | label (value : String)
  | record (fields : List (String × Data))
  | variant (label : String) (payload : Data)
  deriving Repr
def lengthBytes (n : Nat) : List UInt8 := (toString n).toUTF8.toList ++ [0]
def encoded : Nat → Data → Option (List UInt8)
  | 0,_ => none
  | _+1,.natural n => some ([0] ++ lengthBytes n)
  | _+1,.boolean b => some [1,if b then 1 else 0]
  | _+1,.label s => some ([2] ++ lengthBytes s.utf8ByteSize ++ s.toUTF8.toList)
  | depth+1,.record fields => do
      let children ← fields.mapM fun field => do
        pure (lengthBytes field.1.utf8ByteSize ++ field.1.toUTF8.toList ++ (← encoded depth field.2))
      pure ([3] ++ lengthBytes fields.length ++ children.flatten)
  | depth+1,.variant label payload => do
      pure ([4] ++ lengthBytes label.utf8ByteSize ++ label.toUTF8.toList ++ (← encoded depth payload))
inductive Failure where
  | budget | duplicateField | executableValue | suspended | divergent | refused
  /-- The program yielded a Plan: it is an activity, not a pure value. -/
  | yielded
  deriving Repr
structure Budget where
  nodes : Nat
  ticks : Nat
  bytes : Nat
  deriving Repr
structure Result where
  value : Data
  state : State
  remaining : Budget
  deriving Repr
/-- One-tick calls consume one global allowance; terminal inspection is free.
No field receives a fresh allowance. Heap/stack limits stay common throughout. -/
def forceWith (policy : State → Bool) (limits : Limits) : Nat → State → Outcome × Nat
  | 0,state => (runBounded limits 0 state,0)
  | ticks+1,state => match state.control with
    | .complete _ | .refused _ | .blackhole _ | .yielded _ => (runBounded limits 0 state,ticks+1)
    | _ => if !policy state then (.suspended .capacity state,ticks+1) else
      match runBounded limits 1 state with
      | .suspended .ticks next => forceWith policy limits ticks next
      | other => (other,ticks)

def materializeWith (policy : State → Bool) (limits : Limits) : Nat → Budget → RuntimeValue → State → Except (Failure × State) Result
  | 0, _, _, state => .error (.budget,state)
  | depth+1, budget, value, state => do
    if budget.nodes = 0 then throw (.budget,state)
    let remaining := {budget with nodes:=budget.nodes-1}
    match value with
    | .natural n =>
      let bytes := (toString n).utf8ByteSize + 2
      if bytes > remaining.bytes then throw (.budget,state)
      pure ⟨.natural n,state,{remaining with bytes:=remaining.bytes-bytes}⟩
    | .boolean b =>
      if remaining.bytes < 2 then throw (.budget,state)
      pure ⟨.boolean b,state,{remaining with bytes:=remaining.bytes-2}⟩
    | .label s =>
      let bytes := s.utf8ByteSize + (toString s.utf8ByteSize).utf8ByteSize + 2
      if bytes > remaining.bytes then throw (.budget,state)
      pure ⟨.label s,state,{remaining with bytes:=remaining.bytes-bytes}⟩
    | .record fields =>
      let headerBytes := (toString fields.length).utf8ByteSize+2
      if headerBytes > remaining.bytes then throw (.budget,state)
      let remaining := {remaining with bytes:=remaining.bytes-headerBytes}
      if (fields.map Prod.fst).eraseDups.length != fields.length then throw (.duplicateField,state)
      if fields.length > remaining.nodes then throw (.budget,state)
      let pair ← fields.foldlM (fun (prior : List (String × Data) × State × Budget) field => do
        let bytes := field.1.utf8ByteSize+(toString field.1.utf8ByteSize).utf8ByteSize+1
        if bytes > prior.2.2.bytes || prior.2.2.nodes = 0 then throw (.budget,prior.2.1)
        let entered : State := {prior.2.1 with control:=.enter field.2,stack:=[]}
        let (outcome,ticks) := forceWith policy limits prior.2.2.ticks entered
        let nextBudget := {prior.2.2 with ticks:=ticks,bytes:=prior.2.2.bytes-bytes}
        match outcome with
        | .finished forced retained =>
          let child ← materializeWith policy limits depth nextBudget forced retained
          pure ((field.1,child.value)::prior.1,child.state,child.remaining)
        | .suspended _ retained => throw (.suspended,retained)
        | .divergent _ retained => throw (.divergent,retained)
        | .refused _ retained => throw (.refused,retained)
        | .yielded _ retained => throw (.yielded,retained)) ([],state,remaining)
      pure ⟨.record pair.1.reverse,pair.2.1,pair.2.2⟩
    | .variant label payload =>
      let bytes := label.utf8ByteSize+(toString label.utf8ByteSize).utf8ByteSize+2
      if bytes > remaining.bytes || remaining.nodes = 0 then throw (.budget,state)
      let entered : State := {state with control:=.enter payload,stack:=[]}
      let (outcome,ticks) := forceWith policy limits remaining.ticks entered
      let nextBudget := {remaining with ticks:=ticks,bytes:=remaining.bytes-bytes}
      match outcome with
      | .finished forced retained =>
        let child ← materializeWith policy limits depth nextBudget forced retained
        pure ⟨.variant label child.value,child.state,child.remaining⟩
      | .suspended _ retained => throw (.suspended,retained)
      | .divergent _ retained => throw (.divergent,retained)
      | .refused _ retained => throw (.refused,retained)
      | .yielded _ retained => throw (.yielded,retained)
    | .closure _ _ | .specification _ _ | .prototype _ _ => throw (.executableValue,state)

def completeWith (policy : State → Bool) (limits : Limits) (budget : Budget) (state : State) : Except (Failure × State) Result :=
  if !policy state then .error (.suspended,state) else
  match state.control,state.stack with
  | .complete value,[] => do
    let result ← materializeWith policy limits budget.nodes budget value state
    let some bytes := encoded budget.nodes result.value | throw (.budget,result.state)
    if bytes.length > budget.bytes then throw (.budget,result.state)
    pure result
  | _,_ => .error (.suspended,state)
/-- A receiver keeps this exact graph-to-full-data correspondence alongside
its independently checked source/state-origin evidence. -/
structure ExtractionWith (policy : State → Bool) (limits : Limits) (budget : Budget) (state : State) where
  private mk ::
  result : Result
  exact : completeWith policy limits budget state = .ok result

def extractWith (policy : State → Bool) (limits : Limits) (budget : Budget) (state : State) :
    Except (Failure × State) (ExtractionWith policy limits budget state) :=
  match equation : completeWith policy limits budget state with
  | .error failure => .error failure
  | .ok result => .ok ⟨result,equation⟩
/-- One whole source-and-materialization allowance; native callers do not need
an untrusted source tick estimate or a fresh budget at WHNF completion. -/
structure ExecutionWith (policy : State → Bool) (limits : Limits) (budget : Budget)
    (term : Minidregg.Theory.ObjectiveBendOpenRecursion.Term) where
  private mk ::
  value : RuntimeValue
  state : State
  remainingTicks : Nat
  runExact : forceWith policy limits budget.ticks (initial term) =
    (.finished value state,remainingTicks)
  extraction : ExtractionWith policy limits {budget with ticks:=remainingTicks} state

def executeWith (policy : State → Bool) (limits : Limits) (budget : Budget)
    (term : Minidregg.Theory.ObjectiveBendOpenRecursion.Term) :
    Except (Failure × State) (ExecutionWith policy limits budget term) :=
  match equation : forceWith policy limits budget.ticks (initial term) with
  | (.finished value state,ticks) => do
    let extraction ← extractWith policy limits {budget with ticks:=ticks} state
    pure ⟨value,state,ticks,equation,extraction⟩
  | (.suspended _ state,_) => .error (.suspended,state)
  | (.divergent _ state,_) => .error (.divergent,state)
  | (.refused _ state,_) => .error (.refused,state)
  | (.yielded _ state,_) => .error (.yielded,state)
/-- Existing clear preview behavior remains the unrestricted raw language. -/
def force := forceWith (fun _ => true)
def materialize := materializeWith (fun _ => true)
def complete := completeWith (fun _ => true)
abbrev Extraction := ExtractionWith (fun _ => true)
def extract := extractWith (fun _ => true)
abbrev Execution := ExecutionWith (fun _ => true)
def execute := executeWith (fun _ => true)

/-! ## Activities: the yielded Plan is data; the response is typed data -/

open Minidregg.Theory.ObjectiveBendTypes in
/-- The member type of a first-order row (no rigid variables in data types). -/
def rowMember : Ty → String → Option Ty
  | .field name member tail, query => if name = query then some member else rowMember tail query
  | _, _ => none

open Minidregg.Theory.ObjectiveBendTypes in
def rowNames : Ty → List String
  | .field name _ tail => name :: rowNames tail
  | _ => []

open Minidregg.Theory.ObjectiveBendTypes in
mutual
/-- Exact first-order conformance of data to a data type: every record field
is declared once and every declared field is present; a variant's label is one
of the sum's labels and its payload conforms. -/
def Data.conforms : Data → Ty → Bool
  | .natural _, .natural | .boolean _, .boolean | .label _, .label => true
  | .record fields, row =>
      fields.length == (rowNames row).length &&
      (fields.map Prod.fst).eraseDups.length == fields.length && fieldsConform fields row
  | .variant label payload, .variant row => match rowMember row label with
      | some member => payload.conforms member
      | none => false
  | _, _ => false
def fieldsConform : List (String × Data) → Ty → Bool
  | [], _ => true
  | (name,value) :: rest, row =>
      (match rowMember row name with
        | some member => value.conforms member
        | none => false) && fieldsConform rest row
end

mutual
/-- A closed Core4 term for decoded data: the response a kernel resumes with. -/
def Data.term : Data → Minidregg.Theory.ObjectiveBendOpenRecursion.Term
  | .natural n => .nat n
  | .boolean b => .boolean b
  | .label s => .label s
  | .record fields => .record (fieldsTerm fields)
  | .variant label payload => .inject label payload.term
def fieldsTerm : List (String × Data) → List (String × Minidregg.Theory.ObjectiveBendOpenRecursion.Term)
  | [] => []
  | (name,value) :: rest => (name,value.term) :: fieldsTerm rest
end

/-- Extract the Plan of a yielded state through the same budgeted
materialization as every other Data: enter its cell with an empty stack. -/
def yieldedPlanWith (policy : State → Bool) (limits : Limits) (budget : Budget) (state : State) :
    Except (Failure × State) Result :=
  match state.control with
  | .yielded plan =>
    let entered : State := {state with control:=.enter plan,stack:=[]}
    match forceWith policy limits budget.ticks entered with
    | (.finished forced retained,ticks) => do
      -- Materialization runs on the scratch copy; the checkpoint keeps its stack.
      let result ← materializeWith policy limits budget.nodes {budget with ticks:=ticks} forced retained
      pure {result with state:={result.state with control:=state.control,stack:=state.stack}}
    | (.suspended _ retained,_) => .error (.suspended,retained)
    | (.divergent _ retained,_) => .error (.divergent,retained)
    | (.refused _ retained,_) => .error (.refused,retained)
    | (.yielded _ retained,_) => .error (.yielded,retained)
  | _ => .error (.suspended,state)
def yieldedPlan := yieldedPlanWith (fun _ => true)

end Minidregg.Theory.ObjectiveBendDemandData
