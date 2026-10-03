/- Executable bounded closure/continuation controller for live Bend.
It never calls stepChecked, executeChecked, WNF, or a source-evaluation oracle.
This clear reference is NOT yet qualified for native effects/private execution:
the controller-to-Eval simulation and fixed-network lowering remain required.
-/
import Theory.BendClosureArena

namespace Minidregg.Theory.BendClosureMachine
open BendTT BendClosureArena
set_option autoImplicit false

structure Limits where
  heap : Shape
  frames : Nat
  arguments : Nat

/-- Definition order must match the exact checked Book. Names refer to Program's
table; lookup retains first-definition semantics, including transparent models
for opaque definitions. There is no foreign-function replacement here. -/
structure Library where
  program : Program
  definitions : Array (Nat × Nat)

/-- Exact ordered runtime definition projection of the admitted source Book.
Type/opaque/source bytes remain bound by publication; operational Eval unfolds
the model even for opaque definitions. This relation does not mint admission. -/
def Library.SourceCorrespondence (library : Library) (book : Book) : Prop :=
  All₂ (fun entry definition =>
    library.program.names[entry.1]? = some definition.k ∧
    CodeDenotes library.program entry.2 definition.v)
    library.definitions.toList book

def Library.lookupName (library : Library) (name : String) : Option Nat :=
  (library.definitions.toList.find? (fun entry =>
    library.program.names[entry.1]? == some name)).map Prod.snd

private def codeFits (bound : Nat) : Code → Bool
  | .var a | .ref a | .lab a | .enu a | .prj a => a < bound
  | .lam _ a => a < bound
  | .ann a b | .lett _ a b | .all _ a b | .app _ a b |
    .sig _ a b | .tup _ a b => a < bound && b < bound
  | .mat a b c | .eql a b c | .rwt a b c => a < bound && b < bound && c < bound
  | .typ _ | .efq | .rfl => true

/-- Publication/startup rejects unrepresentable controller words. This does
not replace the exact source/Book or acyclic-code certificates. -/
def Library.fits (limits : Limits) (library : Library) : Bool :=
  let bound := 2 ^ limits.heap.wordBits
  library.program.code.size ≤ bound && library.program.names.size ≤ bound &&
  library.program.enumerations.size ≤ bound && library.definitions.size ≤ bound &&
  limits.frames < bound && limits.arguments < bound &&
  library.program.code.all (codeFits bound) &&
  library.definitions.all (fun entry => entry.1 < bound && entry.2 < bound)

inductive Failure where
  | arena (reason : BendClosureArena.Refusal)
  | programCapacity
  | notData
  | argumentCapacity
  | callHead
  | caseArgument
  | liveArgument
  | caseNode
  | pairRequired
  | codePointer
  | continuationCapacity
  | functionRequired
  | heapPointer
  | labelPointer
  | labelRequired
  | notTerm
  | quantity
  | rewriteEvidence
  | unbound
  | unknownDefinition
  deriving DecidableEq, Repr

inductive Frame where
  | function (quantity : Quan) (argument environment : Nat)
  | argument (quantity : Quan) (function : Nat)
  | knownArgument (quantity : Quan) (argument : Nat)
  | lett (quantity : Quan) (body environment : Nat)
  | first (quantity : Quan) (second environment : Nat)
  | second (quantity : Quan) (first : Nat)
  | rewrite (body environment : Nat)
  deriving DecidableEq, Repr

inductive LookupResume where
  | evaluateValue
  | walkArgument (quantity : Quan) (function environment original : Nat)
      (args : List (Quan × Nat))
  deriving DecidableEq, Repr

inductive Control where
  | evaluate (code environment : Nat)
  | lookup (index environment : Nat) (resume : LookupResume)
  | returned (pointer : Nat)
  | apply (quantity : Quan) (function argument : Nat)
  | unspine (pointer original : Nat) (args : List (Quan × Nat))
  | walk (code environment original : Nat) (args : List (Quan × Nat))
  | classify (code environment original cursor : Nat) (args : List (Quan × Nat))
  | reverseArguments (code environment : Nat)
      (remaining reversed : List (Quan × Nat))
  | installArguments (code environment : Nat) (remaining : List (Quan × Nat))
  | complete (pointer : Nat)
  | refused (reason : Failure)
  deriving DecidableEq, Repr

structure State where
  heap : Heap
  /-- Cached structural Data facts; allocation computes these, never the caller.
  The pending simulation invariant must prove each true bit denotes source Data. -/
  data : Array Bool
  stack : List Frame
  control : Control
  sourceSteps : Nat := 0
  deriving DecidableEq, Repr

abbrev Work := StateT State (Except Failure)

private def fail {α : Type} (reason : Failure) : Work α := throw reason

def code (library : Library) (pointer : Nat) : Work Code :=
  match library.program.code[pointer]? with
  | some row => pure row
  | none => fail .codePointer

def row (pointer : Nat) : Work Row := do
  match (← get).heap.get? pointer with
  | some value => pure value
  | none => fail .heapPointer

def isData (pointer : Nat) : Work Bool := do
  pure ((← get).data[pointer]?.getD false)

def push (limits : Limits) (frame : Frame) : Work Unit := do
  let state ← get
  if state.stack.length ≥ limits.frames then fail .continuationCapacity
  else set {state with stack := frame :: state.stack}

def go (control : Control) : Work Unit := modify fun s => {s with control}
def sourceStep : Work Unit := modify fun s => {s with sourceSteps := s.sourceSteps + 1}

def allocate (limits : Limits) (library : Library) (value : Row) : Work Nat := do
  let state ← get
  let qualifies ← match value with
    | .pair quantity first second =>
      pure ((!quantity.live || state.data[first]?.getD false) && state.data[second]?.getD false)
    | .closure pc _ => do
      match ← code library pc with
      | .lab _ | .rfl => pure true
      | _ => pure false
    | _ => pure false
  match BendClosureArena.allocate limits.heap library.program.code.size state.heap value with
  | .error reason => fail (.arena reason)
  | .ok (pointer, heap) =>
    let data := (state.data.toList.zipIdx.map fun p =>
      if p.2 = pointer then qualifies else p.1).toArray
    set {state with heap, data}
    pure pointer

def closure (limits : Limits) (library : Library) (pc environment : Nat) : Work Nat :=
  allocate limits library (.closure pc environment)

def bind (limits : Limits) (library : Library) (quantity : Quan)
    (value environment : Nat) : Work Nat := do
  if quantity == .Q2 && !(← isData value) then fail .notData
  allocate limits library (.environment value environment)

def evaluatePointer (pointer : Nat) : Work Unit := do
  match ← row pointer with
  | .closure pc environment => go (.evaluate pc environment)
  | .pair .. | .application .. => go (.returned pointer)
  | _ => fail .notTerm

private def labelOf (library : Library) (pointer : Nat) : Work String := do
  match ← row pointer with
  | .closure pc _ =>
    match ← code library pc with
    | .lab label =>
      match library.program.names[label]? with
      | some name => pure name
      | none => fail .labelPointer
    | _ => fail .labelRequired
  | _ => fail .labelRequired

private def labelName (library : Library) (label : Nat) : Work String :=
  match library.program.names[label]? with
  | some name => pure name
  | none => fail .labelPointer

private def definition (library : Library) (name : Nat) : Work Nat := do
  let wanted ← labelName library name
  match library.lookupName wanted with
  | some body => pure body
  | none => fail .unknownDefinition

private def boundedArgs (limits : Limits) (args : List (Quan × Nat)) : Work Unit :=
  if args.length ≤ limits.arguments then pure () else fail .argumentCapacity

def returnValue (limits : Limits) (library : Library) (pointer : Nat) : Work Unit := do
  let state ← get
  match state.stack with
  | [] => go (.complete pointer)
  | frame :: rest =>
    set {state with stack := rest}
    match frame with
    | .function q argument environment =>
      if q.live then
        push limits (.argument q pointer)
        go (.evaluate argument environment)
      else
        let argument ← closure limits library argument environment
        go (.apply q pointer argument)
    | .argument q function => go (.apply q function pointer)
    | .knownArgument q argument =>
      /- A case-tree variable may retain a dead thunk. Do not infer Value
      merely because an argument came from the captured environment. -/
      if q.live then
        push limits (.argument q pointer)
        evaluatePointer argument
      else go (.apply q pointer argument)
    | .lett q body environment =>
      let environment ← bind limits library q pointer environment
      sourceStep
      go (.evaluate body environment)
    | .first q second environment =>
      push limits (.second q pointer)
      go (.evaluate second environment)
    | .second q first =>
      let pair ← allocate limits library (.pair q first pointer)
      go (.returned pair)
    | .rewrite body environment =>
      match ← row pointer with
      | .closure pc _ =>
        match ← code library pc with
        | .rfl => sourceStep; go (.evaluate body environment)
        | _ => fail .rewriteEvidence
      | _ => fail .rewriteEvidence

def evaluate (limits : Limits) (library : Library) (pc environment : Nat) : Work Unit := do
  match ← code library pc with
  | .var index => go (.lookup index environment .evaluateValue)
  | .ref _ =>
    let original ← closure limits library pc environment
    go (.unspine original original [])
  | .ann value _ => sourceStep; go (.evaluate value environment)
  | .lett q value body =>
    if q.live then
      push limits (.lett q body environment)
      go (.evaluate value environment)
    else
      let value ← closure limits library value environment
      let environment ← bind limits library q value environment
      sourceStep
      go (.evaluate body environment)
  | .app q function argument =>
    push limits (.function q argument environment)
    go (.evaluate function environment)
  | .tup q first second =>
    if q.live then
      push limits (.first q second environment)
      go (.evaluate first environment)
    else
      let first ← closure limits library first environment
      push limits (.second q first)
      go (.evaluate second environment)
  | .rwt evidence _ body =>
    push limits (.rewrite body environment)
    go (.evaluate evidence environment)
  | _ =>
    let value ← closure limits library pc environment
    go (.returned value)

def apply (limits : Limits) (library : Library)
    (q : Quan) (function argument : Nat) : Work Unit := do
  match ← row function with
  | .closure pc environment =>
    match ← code library pc with
    | .lam binder body =>
      if binder.live != q.live then fail .quantity
      let environment ← bind limits library binder argument environment
      sourceStep
      go (.evaluate body environment)
    | .prj handler =>
      if !q.live then fail .liveArgument
      match ← row argument with
      | .pair firstQ first second =>
        push limits (.knownArgument q second)
        push limits (.knownArgument (Quan.fld firstQ q) first)
        sourceStep
        go (.evaluate handler environment)
      | _ => fail .pairRequired
    | .mat label yes no =>
      if !q.live then fail .liveArgument
      let actual ← labelOf library argument
      let wanted ← labelName library label
      sourceStep
      if actual == wanted then go (.evaluate yes environment)
      else
        push limits (.knownArgument q argument)
        go (.evaluate no environment)
    | _ =>
      let original ← allocate limits library (.application q function argument)
      go (.unspine function original [(q, argument)])
  | .application .. =>
    let original ← allocate limits library (.application q function argument)
    go (.unspine function original [(q, argument)])
  | _ => fail .functionRequired

def unspine (limits : Limits) (library : Library)
    (pointer original : Nat) (args : List (Quan × Nat)) : Work Unit := do
  boundedArgs limits args
  match ← row pointer with
  | .application q function argument =>
    let args := (q, argument) :: args
    boundedArgs limits args
    go (.unspine function original args)
  | .closure pc _ =>
    match ← code library pc with
    | .ref name =>
      let body ← definition library name
      /- Row zero is the initial empty environment and is never overwritten. -/
      go (.walk body 0 original args)
    | _ => fail .callHead
  | _ => fail .callHead

def walk (limits : Limits) (library : Library) (isNode : Bool)
    (pc environment original : Nat) (args : List (Quan × Nat)) : Work Unit := do
  boundedArgs limits args
  let instruction ← code library pc
  if isNode then
    match instruction with
    | .app q function argument =>
      match ← code library argument with
      | .var index =>
        go (.lookup index environment (.walkArgument q function environment original args))
      | _ => fail .caseNode
    | _ =>
      match args with
      | [] => go (.returned original)
      | (q, argument) :: rest =>
        match instruction with
        | .lam binder body =>
          if binder.live != q.live then fail .quantity
          let environment ← bind limits library binder argument environment
          go (.walk body environment original rest)
        | .prj handler =>
          if !q.live then fail .liveArgument
          match ← row argument with
          | .pair firstQ first second =>
            let args := (Quan.fld firstQ q, first) :: (q, second) :: rest
            boundedArgs limits args
            go (.walk handler environment original args)
          | _ => fail .pairRequired
        | .mat label yes no =>
          if !q.live then fail .liveArgument
          let actual ← labelOf library argument
          let wanted ← labelName library label
          if actual == wanted then go (.walk yes environment original rest)
          else go (.walk no environment original args)
        | _ => fail .caseArgument
  else
    /- The whole case tree has finished before any leaf is exposed. -/
    /- Check the whole reservation before the source call step. Reversal and
    frame installation then take one argument per physical tick; no hidden
    argument-capacity-sized loop is charged as a constant-time microstep. -/
    if (← get).stack.length + args.length > limits.frames then
      fail .continuationCapacity
    sourceStep
    go (.reverseArguments pc environment args [])

/-- Once a full Walk exposes its leaf, Eval.call has occurred. These controls
administratively install the residual application spine without evaluating it.
The source simulation therefore interprets them as the post-call leaf spine. -/
def reverseArguments (pc environment : Nat)
    (remaining reversed : List (Quan × Nat)) : Work Unit :=
  match remaining with
  | [] => go (.installArguments pc environment reversed)
  | argument :: rest => go (.reverseArguments pc environment rest (argument :: reversed))

def installArguments (limits : Limits) (pc environment : Nat)
    (remaining : List (Quan × Nat)) : Work Unit := do
  match remaining with
  | [] => go (.evaluate pc environment)
  | argument :: rest =>
    push limits (.knownArgument argument.1 argument.2)
    go (.installArguments pc environment rest)

/-- Case-node classification follows one code spine edge per physical tick.
No hidden code-sized recursion is charged as a single constant-time read. -/
def startWalk (limits : Limits) (library : Library)
    (pc environment original : Nat) (args : List (Quan × Nat)) : Work Unit := do
  match ← code library pc with
  | .app _ function argument =>
    match ← code library argument with
    | .var _ => go (.classify pc environment original function args)
    | _ => walk limits library false pc environment original args
  | .lam .. | .prj .. | .mat .. | .efq =>
    walk limits library true pc environment original args
  | _ => walk limits library false pc environment original args

def classify (limits : Limits) (library : Library)
    (pc environment original cursor : Nat) (args : List (Quan × Nat)) : Work Unit := do
  match ← code library cursor with
  | .app _ function _ => go (.classify pc environment original function args)
  | .lam .. | .prj .. | .mat .. | .efq =>
    walk limits library true pc environment original args
  | _ => walk limits library false pc environment original args

/-- Environment traversal is itself a microstep, not a hidden heap-sized
loop inside a single controller tick. Q0 positions are retained. -/
def lookup (limits : Limits) (index environment : Nat)
    (resume : LookupResume) : Work Unit := do
  match ← row environment with
  | .environment value tail =>
    match index with
    | next + 1 => go (.lookup next tail resume)
    | 0 =>
      match resume with
      | .evaluateValue => evaluatePointer value
      | .walkArgument q function environment original args =>
        let args := (q, value) :: args
        boundedArgs limits args
        go (.walk function environment original args)
  | _ => fail .unbound

/-- One bounded clear microstep. On refusal no effect certificate exists and
the original state remains available for diagnosis; capacity is never success. -/
def step (limits : Limits) (library : Library) (state : State) : State :=
  let work := match state.control with
    | .evaluate pc environment => evaluate limits library pc environment
    | .lookup index environment resume => lookup limits index environment resume
    | .returned pointer => returnValue limits library pointer
    | .apply q function argument => apply limits library q function argument
    | .unspine pointer original args => unspine limits library pointer original args
    | .walk pc environment original args => startWalk limits library pc environment original args
    | .classify pc environment original cursor args => classify limits library pc environment original cursor args
    | .reverseArguments pc environment remaining reversed =>
      reverseArguments pc environment remaining reversed
    | .installArguments pc environment remaining =>
      installArguments limits pc environment remaining
    | .complete _ | .refused _ => pure ()
  match work.run state with
  | .ok (_, next) => next
  | .error reason => {state with control := .refused reason}

/-- A public number of physical ticks; complete/refused states are absorbing.
SourceSteps is private witness metadata, never automatically a public fee. -/
def run (limits : Limits) (library : Library) : Nat → State → State
  | 0, state => state
  | ticks + 1, state => run limits library ticks (step limits library state)

def start (limits : Limits) (library : Library) (entry : Nat) : Except Failure State :=
  if !library.fits limits || entry ≥ library.program.code.size then .error .programCapacity
  else
    match BendClosureArena.allocate limits.heap 0 (Heap.empty limits.heap) .nil with
    | .error reason => .error (.arena reason)
    | .ok (_, heap) =>
      .ok {
        heap := heap
        data := Array.replicate limits.heap.slots false
        stack := []
        control := .evaluate entry 0 }

theorem complete_absorbing (limits : Limits) (library : Library) (state : State)
    (pointer : Nat) (done : state.control = .complete pointer) :
    step limits library state = state := by
  simp [step, done]
  rfl

theorem refused_absorbing (limits : Limits) (library : Library) (state : State)
    (reason : Failure) (done : state.control = .refused reason) :
    step limits library state = state := by
  simp [step, done]
  rfl

theorem run_of_absorbing (limits : Limits) (library : Library) (state : State)
    (stable : step limits library state = state) (ticks : Nat) :
    run limits library ticks state = state := by
  induction ticks with
  | zero => rfl
  | succ ticks ih => simpa [run, stable] using ih

theorem complete_padding (limits : Limits) (library : Library) (state : State)
    (pointer : Nat) (done : state.control = .complete pointer) (ticks : Nat) :
    run limits library ticks state = state :=
  run_of_absorbing limits library state (complete_absorbing limits library state pointer done) ticks

theorem refusal_padding (limits : Limits) (library : Library) (state : State)
    (reason : Failure) (done : state.control = .refused reason) (ticks : Nat) :
    run limits library ticks state = state :=
  run_of_absorbing limits library state (refused_absorbing limits library state reason done) ticks

/-- Splitting a fixed public tick budget does not restart source evaluation or
reset its heap/correlation identity. Physical correlation ownership is external
and remains monotone even when semantic state is absorbing. -/
theorem run_add (limits : Limits) (library : Library) (first second : Nat) (state : State) :
    run limits library (first + second) state =
      run limits library second (run limits library first state) := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih => simpa [Nat.succ_add, run] using ih (step limits library state)

#assert_axioms run_of_absorbing
#assert_axioms complete_padding
#assert_axioms refusal_padding
#assert_axioms run_add
#assert_axioms complete_absorbing
#assert_axioms refused_absorbing
/- Stable public proof views keep the original private constants and every
operational definition intact. Existing compiled consumers remain compatible. -/
def boundedArgsFn (limits : Limits) (args : List (Quan × Nat)) : Work Unit :=
  boundedArgs limits args

def definitionFn (library : Library) (name : Nat) : Work Nat :=
  definition library name

def labelNameFn (library : Library) (name : Nat) : Work String :=
  labelName library name

def labelOfFn (library : Library) (pointer : Nat) : Work String :=
  labelOf library pointer

theorem boundedArgs_eq (limits : Limits) (args : List (Quan × Nat)) :
    boundedArgs limits args = boundedArgsFn limits args := rfl

theorem definition_eq (library : Library) (name : Nat) :
    definition library name = definitionFn library name := rfl

theorem labelName_eq (library : Library) (name : Nat) :
    labelName library name = labelNameFn library name := rfl

theorem labelOf_eq (library : Library) (pointer : Nat) :
    labelOf library pointer = labelOfFn library pointer := rfl

#assert_axioms boundedArgs_eq
#assert_axioms definition_eq
#assert_axioms labelName_eq
#assert_axioms labelOf_eq
end Minidregg.Theory.BendClosureMachine

