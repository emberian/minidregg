/- Concrete finite-enum response injection into the actual closure machine.
This starts a new PURE segment. The external response is an Activity transition,
not an upstream Eval edge from the preceding yielded Plan/continuation pair.
The caller must consume the authorized pending phase; this function is pure.
-/
import Theory.BendClosureMachine
import Theory.BendClosureDecode
import Theory.BendClosureReification

namespace Minidregg.Theory.BendClosureResponse
open BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

def responseTerm (bit : Bool) : Term := .Lab (if bit then "true" else "false")
def responseType : Term := .Enu ["false", "true"]

def decodeResponse : List UInt8 → Option Bool
  | [0] => some false
  | [1] => some true
  | _ => none

/-- This is explicitly the finite enum ABI, not an implicit claim about the
Prelude Bool sigma/tag/unit representation. Both code pointers and the empty
environment are selected by the admitted pending request continuation. -/
structure ABI where
  falseCode : Nat
  trueCode : Nat
  emptyEnvironment : Nat
  continuation : Nat
  deriving DecidableEq, Repr

inductive Reject where
  | code | label | environment | capacity | dataShape
  | allocation (reason : BendClosureArena.Refusal)
  deriving DecidableEq, Repr

structure Injected (program : Program) (before : Heap) (bit : Bool) where
  heap : Heap
  pointer : Nat
  extension : Extends before heap
  exact : Denotes program heap pointer (responseTerm bit)

/-- Inspect exact existing publication code and actual empty-environment row;
then use the same checked immutable allocator as the runtime. -/
def inject (limits : Limits) (program : Program) (abi : ABI)
    (before : Heap) (bit : Bool) : Except Reject (Injected program before bit) := do
  let pc := if bit then abi.trueCode else abi.falseCode
  let some decoded := decodeCode program 1 pc | .error .code
  if same : decoded.term = responseTerm bit then
    let codeExact : CodeDenotes program pc (responseTerm bit) := by
      rw [← same]
      exact decoded.exact
    if empty : before.get? abi.emptyEnvironment = some .nil then
      let environmentExact : EnvironmentDenotes program before abi.emptyEnvironment [] := .nil empty
      if room : before.used < before.rows.size then
        match allocated : BendClosureArena.allocate limits.heap program.code.size before
            (.closure pc abi.emptyEnvironment) with
        | .error reason => .error (.allocation reason)
        | .ok (pointer, heap) =>
          have shape := allocate_shape allocated
          have extension : Extends before heap := allocate_extends allocated
          have newRow : heap.get? pointer = some (.closure pc abi.emptyEnvironment) := by
            obtain ⟨rfl, rfl⟩ := shape
            exact append_reads_new before (.closure pc abi.emptyEnvironment) room
          have exact : Denotes program heap pointer (responseTerm bit) := by
            have closure := Denotes.closure newRow codeExact (environmentExact.extends extension)
            cases bit <;> simpa [responseTerm, Term.sub] using closure
          .ok ⟨heap, pointer, extension, exact⟩
      else .error .capacity
    else .error .environment
  else .error .label

structure Resumed (program : Program) (before : State) (abi : ABI) (bit : Bool) where
  state : State
  inputPointer : Nat
  extension : Extends before.heap state.heap
  inputExact : Denotes program state.heap inputPointer (responseTerm bit)
  controlExact : state.control = .apply .Q1 abi.continuation inputPointer
  emptyStack : state.stack = []
  newSegment : state.sourceSteps = 0

/-- Replay protection/authority is deliberately not hidden here: the Activity
CAS must consume one pending response before installing this new pure segment.
The previous segment source count remains in the durable Activity outcome. -/
def resume (limits : Limits) (program : Program) (abi : ABI)
    (before : State) (bit : Bool) : Except Reject (Resumed program before abi bit) := do
  if before.data.size != limits.heap.slots then .error .dataShape else do
    let result ← inject limits program abi before.heap bit
    let data := (before.data.toList.zipIdx.map fun pair =>
      if pair.2 = result.pointer then true else pair.1).toArray
    let state : State := { heap := result.heap, data := data, stack := [], control := .apply .Q1 abi.continuation result.pointer, sourceSteps := 0 }
    .ok ⟨state, result.pointer, result.extension, result.exact, rfl, rfl, rfl⟩

theorem response_typed (book : Book) (bit : Bool) :
    Typed book [] (responseTerm bit) responseType := by
  apply Typed.lab
  cases bit <;> simp [responseTerm, responseType]

theorem response_value (book : Book) (bit : Bool) : Value book (responseTerm bit) := .lab

theorem response_data (bit : Bool) : Data (responseTerm bit) := .lab

/-- A retained exact continuation remains the same source term after injection;
it is not looked up by an untyped callback name. -/
theorem continuation_retained {program : Program} {before : State} {abi : ABI}
    {bit : Bool} (resumed : Resumed program before abi bit) {source : Term}
    (continuation : Denotes program before.heap abi.continuation source) :
    Denotes program resumed.state.heap abi.continuation source :=
  continuation.extends resumed.extension

#assert_axioms inject
#assert_axioms resume
#assert_axioms response_typed
#assert_axioms response_value
#assert_axioms response_data
#assert_axioms continuation_retained
end Minidregg.Theory.BendClosureResponse
