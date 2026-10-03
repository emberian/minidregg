/-
An executable bounded continuation machine for the ACTUAL Nock 4K opcodes.
No call to Nock.exec/run/oracle occurs in this execution path. A fixed public
microstep schedule is separate from native rule fuel. Heap reads and writes scan
all public slots; circuit lowering must also make mode/stack/arithmetic muxes
oblivious. This clear executable machine alone is not malicious-private MPC.
-/
import Theory.Nock
import Theory.AssertAxioms

namespace Minidregg.Theory.BoundedNockMachine
open Noun
set_option autoImplicit false

structure Limits where
  heapSlots : Nat
  stackSlots : Nat
  equalitySlots : Nat
  atomBits : Nat
  deriving DecidableEq, Repr

inductive Overflow
  | heap | stack | equality | atom | ticks | invalidHeap
  deriving DecidableEq, Repr

inductive Node
  | atom (value : Nat)
  | cell (head tail : Nat)
  deriving DecidableEq, Repr

inductive Halt
  | value (pointer : Nat)
  | crash
  | exhausted
  | overflow (reason : Overflow)
  deriving DecidableEq, Repr

inductive Mode
  | eval (subject formula : Nat)
  | ret (value : Nat)
  | axis (axis subject : Nat)
  | edit (axis patch tree : Nat)
  | equal (pending : List (Nat × Nat))
  | halted (outcome : Halt)
  deriving DecidableEq, Repr

inductive Frame
  | consRight (subject formula : Nat)
  | consFinish (head : Nat)
  | evalRight (subject formula : Nat)
  | evalFinish (subject : Nat)
  | wut
  | lus
  | tisRight (subject formula : Nat)
  | tisFinish (left : Nat)
  | six (subject yes no : Nat)
  | seven (formula : Nat)
  | eight (subject formula : Nat)
  | nine (axis : Nat)
  | nineFinish (core : Nat)
  | tenPatch (subject axis patchFormula : Nat)
  | tenFinish (axis tree : Nat)
  | hint (subject formula : Nat)
  | axisBit (odd : Bool)
  | editJoin (axis patch tree : Nat)
  deriving DecidableEq, Repr

structure State where
  limits : Limits
  /-- Fixed public length, including unallocated/dummy slots. -/
  heap : Array (Option Node)
  allocated : Nat
  stack : List Frame
  mode : Mode
  remaining : Nat
  used : Nat
  deriving DecidableEq, Repr

/-- Every heap lookup traverses all public slots in the reference access IR. -/
def read (state : State) (pointer : Nat) : Option Node :=
  (state.heap.toList.zipIdx).foldr
    (fun entry tail => if entry.2 = pointer then entry.1 else tail) none

def stop (state : State) (outcome : Halt) : State := { state with mode := .halted outcome }

def capacity (state : State) (reason : Overflow) : State := stop state (.overflow reason)

def push (state : State) (frame : Frame) (mode : Mode) : State :=
  if state.stack.length < state.limits.stackSlots then
    { state with stack := frame :: state.stack, mode := mode }
  else capacity state .stack

/-- Append-only noun nodes: edits allocate a new spine, never mutate a noun
already used by another continuation or alias. Every write visits all slots. -/
def allocate (state : State) (node : Node) : Except Overflow (State × Nat) := do
  match node with
  | .atom value => if value ≥ 2 ^ state.limits.atomBits then throw .atom
  | .cell head tail =>
      if head ≥ state.allocated || tail ≥ state.allocated then throw .invalidHeap
  if state.allocated ≥ state.limits.heapSlots then throw .heap
  let pointer := state.allocated
  let heap := state.heap.mapIdx fun index old => if index = pointer then some node else old
  pure ({ state with heap := heap, allocated := pointer + 1 }, pointer)

def withAllocation (state : State) (node : Node) (next : State → Nat → State) : State :=
  match allocate state node with
  | .error reason => capacity state reason
  | .ok (allocated, pointer) => next allocated pointer

def returnAtom (state : State) (value : Nat) : State :=
  withAllocation state (.atom value) fun next pointer => { next with mode := .ret pointer }

inductive Instruction
  | cons (headFormula tailFormula : Nat)
  | slot (axis : Nat)
  | quote (value : Nat)
  | eval (subjectFormula formulaFormula : Nat)
  | wut (formula : Nat)
  | lus (formula : Nat)
  | tis (left right : Nat)
  | six (test yes no : Nat)
  | seven (first second : Nat)
  | eight (first second : Nat)
  | nine (axis formula : Nat)
  | ten (axis patch tree : Nat)
  | hintS (body : Nat)
  | hintD (clue body : Nat)
  deriving DecidableEq, Repr

/-- Native parse shapes, preserving autocons and dynamic-hint evaluation.
Scry (12) and unknown/malformed opcodes remain native crash, not overflow. -/
def parse (state : State) (formula : Nat) : Option Instruction := do
  let .cell head args ← read state formula | none
  match ← read state head with
  | .cell _ _ => some (.cons head args)
  | .atom opcode =>
    match opcode with
    | 0 => let .atom axis ← read state args | none
           some (.slot axis)
    | 1 => some (.quote args)
    | 2 => let .cell first second ← read state args | none
           some (.eval first second)
    | 3 => some (.wut args)
    | 4 => some (.lus args)
    | 5 => let .cell first second ← read state args | none
           some (.tis first second)
    | 6 => let .cell test rest ← read state args | none
           let .cell yes no ← read state rest | none
           some (.six test yes no)
    | 7 => let .cell first second ← read state args | none
           some (.seven first second)
    | 8 => let .cell first second ← read state args | none
           some (.eight first second)
    | 9 => let .cell axis formula ← read state args | none
           let .atom axisValue ← read state axis | none
           some (.nine axisValue formula)
    | 10 => let .cell pair tree ← read state args | none
            let .cell axis patch ← read state pair | none
            let .atom axisValue ← read state axis | none
            some (.ten axisValue patch tree)
    | 11 => let .cell hint body ← read state args | none
            match ← read state hint with
            | .atom _ => some (.hintS body)
            | .cell tag clue =>
              let .atom _ ← read state tag | none
              some (.hintD clue body)
    | _ => none

def enter (state : State) (subject : Nat) : Instruction → State
  | .cons first second => push state (.consRight subject second) (.eval subject first)
  | .slot axis => { state with mode := .axis axis subject }
  | .quote value => { state with mode := .ret value }
  | .eval first second => push state (.evalRight subject second) (.eval subject first)
  | .wut formula => push state .wut (.eval subject formula)
  | .lus formula => push state .lus (.eval subject formula)
  | .tis first second => push state (.tisRight subject second) (.eval subject first)
  | .six test yes no => push state (.six subject yes no) (.eval subject test)
  | .seven first second => push state (.seven second) (.eval subject first)
  | .eight first second => push state (.eight subject second) (.eval subject first)
  | .nine axis formula => push state (.nine axis) (.eval subject formula)
  /- Native opcode10 evaluates tree BEFORE patch. -/
  | .ten axis patch tree => push state (.tenPatch subject axis patch) (.eval subject tree)
  | .hintS body => { state with mode := .eval subject body }
  | .hintD clue body => push state (.hint subject body) (.eval subject clue)

def resume (state : State) (value : Nat) : Frame → State
  | .consRight subject formula => push state (.consFinish value) (.eval subject formula)
  | .consFinish head => withAllocation state (.cell head value)
      fun next pointer => { next with mode := .ret pointer }
  | .evalRight subject formula => push state (.evalFinish value) (.eval subject formula)
  | .evalFinish subject => { state with mode := .eval subject value }
  | .wut => match read state value with
      | some (.cell _ _) => returnAtom state 0
      | some (.atom _) => returnAtom state 1
      | none => capacity state .invalidHeap
  | .lus => match read state value with
      | some (.atom n) => returnAtom state (n + 1)
      | some (.cell _ _) => stop state .crash
      | none => capacity state .invalidHeap
  | .tisRight subject formula => push state (.tisFinish value) (.eval subject formula)
  | .tisFinish left =>
      if 0 < state.limits.equalitySlots then { state with mode := .equal [(left, value)] }
      else capacity state .equality
  | .six subject yes no => match read state value with
      | some (.atom 0) => { state with mode := .eval subject yes }
      | some (.atom 1) => { state with mode := .eval subject no }
      | some _ => stop state .crash
      | none => capacity state .invalidHeap
  | .seven formula => { state with mode := .eval value formula }
  | .eight subject formula => withAllocation state (.cell value subject)
      fun next pointer => { next with mode := .eval pointer formula }
  | .nine axis => push state (.nineFinish value) (.axis axis value)
  | .nineFinish core => { state with mode := .eval core value }
  | .tenPatch subject axis formula => push state (.tenFinish axis value) (.eval subject formula)
  | .tenFinish axis tree => { state with mode := .edit axis value tree }
  | .hint subject formula => { state with mode := .eval subject formula }
  | .axisBit odd => match read state value with
      | some (.cell head tail) => { state with mode := .ret (if odd then tail else head) }
      | some (.atom _) => stop state .crash
      | none => capacity state .invalidHeap
  | .editJoin axis patch tree => match read state value with
      | some (.cell head tail) =>
        withAllocation state (if axis % 2 = 0 then .cell patch tail else .cell head patch)
          fun next pointer => { next with mode := .edit (axis / 2) pointer tree }
      | some (.atom _) => stop state .crash
      | none => capacity state .invalidHeap

/-- One bounded microinstruction. Only entering a Nock rule consumes native
fuel. Internal axis/edit/equality/return work consumes public ticks instead. -/
def step (state : State) : State :=
  match state.mode with
  | .halted _ => state
  | .eval subject formula =>
      if state.remaining = 0 then stop state .exhausted
      else
        let charged := { state with remaining := state.remaining - 1, used := state.used + 1 }
        match parse charged formula with
        | none => stop charged .crash
        | some instruction => enter charged subject instruction
  | .ret value => match state.stack with
      | [] => stop state (.value value)
      | frame :: tail => resume { state with stack := tail } value frame
  | .axis axis subject =>
      if axis = 0 then stop state .crash
      else if axis = 1 then { state with mode := .ret subject }
      else push state (.axisBit (decide (axis % 2 = 1))) (.axis (axis / 2) subject)
  | .edit axis patch tree =>
      if axis = 0 then stop state .crash
      else if axis = 1 then { state with mode := .ret patch }
      else push state (.editJoin axis patch tree) (.axis (axis / 2) tree)
  | .equal pending => match pending with
      | [] => returnAtom state 0
      | (left, right) :: tail =>
          match read state left, read state right with
          | some (.atom x), some (.atom y) =>
              if x = y then { state with mode := .equal tail } else returnAtom state 1
          | some (.cell lh lt), some (.cell rh rt) =>
              if tail.length + 2 ≤ state.limits.equalitySlots then
                { state with mode := .equal ((lh, rh) :: (lt, rt) :: tail) }
              else capacity state .equality
          | some _, some _ => returnAtom state 1
          | _, _ => capacity state .invalidHeap

/-- Always execute exactly the public number of microticks. Halting is
absorbing, so padding does not change success/crash/exhaustion or the meter. -/
def runTicks : Nat → State → State
  | 0, state => state
  | ticks + 1, state => runTicks ticks (step state)

def initial (limits : Limits) (fuel : Nat) : State :=
  ⟨limits, Array.replicate limits.heapSlots none, 0, [], .halted (.overflow .invalidHeap), fuel, 0⟩

/-- External entry encoding is exact and refuses bounds, never wraps atom bits.
Private deployments must compile this codec or authenticate already shared heap
records; plaintext encoding here is not a private input protocol. -/
def encode (state : State) : Noun → Except Overflow (State × Nat)
  | .atom value => allocate state (.atom value)
  | .cell head tail => do
      let (afterHead, headPointer) ← encode state head
      let (afterTail, tailPointer) ← encode afterHead tail
      allocate afterTail (.cell headPointer tailPointer)

def start (limits : Limits) (fuel : Nat) (subject formula : Noun) : Except Overflow State := do
  let (withSubject, subjectPointer) ← encode (initial limits fuel) subject
  let (withFormula, formulaPointer) ← encode withSubject formula
  pure { withFormula with mode := .eval subjectPointer formulaPointer }

/-- Output decoding follows only earlier nodes. Fuel heapSlots is intended to suffice for well-formed append-only heaps.
The required global append-only/decoding refinement remains an explicit obligation. -/
def decode : Nat → State → Nat → Option Noun
  | 0, _, _ => none
  | depth + 1, state, pointer => do
      match ← read state pointer with
      | .atom value => some (.atom value)
      | .cell head tail => do
          let headValue ← decode depth state head
          let tailValue ← decode depth state tail
          some (.cell headValue tailValue)

inductive Result
  | value (noun : Noun) (steps : Nat)
  | crash (steps : Nat)
  | exhausted (steps : Nat)
  | overflow (reason : Overflow)
  deriving DecidableEq, Repr

def finish (state : State) : Result :=
  match state.mode with
  | .halted (.value pointer) => match decode state.limits.heapSlots state pointer with
      | some noun => .value noun state.used
      | none => .overflow .invalidHeap
  | .halted .crash => .crash state.used
  | .halted .exhausted => .exhausted state.used
  | .halted (.overflow reason) => .overflow reason
  | _ => .overflow .ticks

def run (limits : Limits) (ticks fuel : Nat) (subject formula : Noun) : Result :=
  match start limits fuel subject formula with
  | .error reason => .overflow reason
  | .ok state => finish (runTicks ticks state)

@[simp] theorem step_halted (state : State) (outcome : Halt) :
    step { state with mode := .halted outcome } = { state with mode := .halted outcome } := rfl

theorem runTicks_halted (ticks : Nat) (state : State) (outcome : Halt) :
    runTicks ticks { state with mode := .halted outcome } = { state with mode := .halted outcome } := by
  induction ticks with
  | zero => rfl
  | succ ticks ih => simpa only [runTicks, step_halted] using ih

#assert_axioms runTicks_halted

end Minidregg.Theory.BoundedNockMachine
