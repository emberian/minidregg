/- Executable equality witnesses for the complete persistent demand state.
Term comparison is bounded; a refusal never grants a state equality. -/
import Theory.ObjectiveBendDemandMachine
import Theory.ObjectiveTermEquality
namespace Minidregg.Compiler.ObjectiveDemandStateEquality
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
set_option autoImplicit false

def scalar {α : Type} [DecidableEq α] (left right : α) : Option (PLift (left = right)) :=
  if same : left = right then some ⟨same⟩ else none

def listEqual {α : Type} (compare : (left right : α) → Option (PLift (left = right))) :
    (left right : List α) → Option (PLift (left = right))
  | [],[] => some ⟨rfl⟩
  | a::as,b::bs => do
    let head ← compare a b
    let tail ← listEqual compare as bs
    pure ⟨by cases head.down; cases tail.down; rfl⟩
  | _,_ => none

def closure (fuel : Nat) (left right : Closure) : Option (PLift (left = right)) := do
  let term ← termEqual fuel left.term right.term
  let env ← scalar left.environment right.environment
  pure ⟨by cases left; cases right; cases term.down; cases env.down; rfl⟩

def value (fuel : Nat) : (left right : RuntimeValue) → Option (PLift (left = right))
  | .closure a e,.closure b f => do
    let term ← termEqual fuel a b
    let env ← scalar e f
    pure ⟨by cases term.down; cases env.down; rfl⟩
  | .natural a,.natural b => do let same ← scalar a b; pure ⟨by cases same.down; rfl⟩
  | .boolean a,.boolean b => do let same ← scalar a b; pure ⟨by cases same.down; rfl⟩
  | .label a,.label b => do let same ← scalar a b; pure ⟨by cases same.down; rfl⟩
  | .record a,.record b => do let same ← scalar a b; pure ⟨by cases same.down; rfl⟩
  | .specification a b,.specification c d => do
    let first ← scalar a c; let second ← scalar b d
    pure ⟨by cases first.down; cases second.down; rfl⟩
  | .prototype a b,.prototype c d => do
    let first ← scalar a c; let second ← scalar b d
    pure ⟨by cases first.down; cases second.down; rfl⟩
  | _,_ => none

def cell (fuel : Nat) : (left right : Cell) → Option (PLift (left = right))
  | .suspended a,.suspended b => do let same ← closure fuel a b; pure ⟨by cases same.down; rfl⟩
  | .evaluating a,.evaluating b => do let same ← closure fuel a b; pure ⟨by cases same.down; rfl⟩
  | .cached a v,.cached b w => do
    let origin ← closure fuel a b; let result ← value fuel v w
    pure ⟨by cases origin.down; cases result.down; rfl⟩
  | _,_ => none

def refusalCode : Refusal → Nat
  | .unbound => 0 | .missingCell => 1 | .missingField => 2
  | .wrongValue => 3 | .invalidUpdate => 4 | .capacity => 5

def refusalOf : Nat → Refusal
  | 1 => .missingCell | 2 => .missingField | 3 => .wrongValue
  | 4 => .invalidUpdate | 5 => .capacity | _ => .unbound

theorem refusal_roundtrip (r : Refusal) : refusalOf (refusalCode r) = r := by cases r <;> rfl

def refusal (left right : Refusal) : Option (PLift (left = right)) := do
  let same ← scalar (refusalCode left) (refusalCode right)
  pure ⟨by simpa only [refusal_roundtrip] using congrArg refusalOf same.down⟩

def control (fuel : Nat) : (left right : Control) → Option (PLift (left = right))
  | .evaluate a e,.evaluate b f => do
    let term ← termEqual fuel a b; let env ← scalar e f
    pure ⟨by cases term.down; cases env.down; rfl⟩
  | .enter a,.enter b => do let same ← scalar a b; pure ⟨by cases same.down; rfl⟩
  | .blackhole a,.blackhole b => do let same ← scalar a b; pure ⟨by cases same.down; rfl⟩
  | .returned a,.returned b => do let same ← value fuel a b; pure ⟨by cases same.down; rfl⟩
  | .complete a,.complete b => do let same ← value fuel a b; pure ⟨by cases same.down; rfl⟩
  | .refused a,.refused b => do let same ← refusal a b; pure ⟨by cases same.down; rfl⟩
  | _,_ => none

def frame (fuel : Nat) : (left right : Frame) → Option (PLift (left = right))
  | .argument a e,.argument b f => do
    let term ← termEqual fuel a b; let env ← scalar e f
    pure ⟨by cases term.down; cases env.down; rfl⟩
  | .update a,.update b => do let same ← scalar a b; pure ⟨by cases same.down; rfl⟩
  | .field a,.field b => do let same ← scalar a b; pure ⟨by cases same.down; rfl⟩
  | .reflect,.reflect | .metadata,.metadata | .project,.project => some ⟨rfl⟩
  | .extend a e,.extend b f => do
    let fields ← fieldsEqual fuel a b; let env ← scalar e f
    pure ⟨by cases fields.down; cases env.down; rfl⟩
  | .condition a b e,.condition c d f => do
    let first ← termEqual fuel a c; let second ← termEqual fuel b d; let env ← scalar e f
    pure ⟨by cases first.down; cases second.down; cases env.down; rfl⟩
  | .binaryLeft p a e,.binaryLeft q b f => do
    let prim ← scalar p q; let term ← termEqual fuel a b; let env ← scalar e f
    pure ⟨by cases prim.down; cases term.down; cases env.down; rfl⟩
  | .binaryRight p a,.binaryRight q b => do
    let prim ← scalar p q; let result ← value fuel a b
    pure ⟨by cases prim.down; cases result.down; rfl⟩
  | _,_ => none

def state (fuel : Nat) (left right : State) : Option (PLift (left = right)) := do
  let heap ← listEqual (cell fuel) left.heap.toList right.heap.toList
  let focus ← control fuel left.control right.control
  let stack ← listEqual (frame fuel) left.stack right.stack
  have heaps : left.heap = right.heap := by
    simpa using congrArg List.toArray heap.down
  pure ⟨by cases left; cases right; cases heaps; cases focus.down; cases stack.down; rfl⟩

def outcome (fuel : Nat) : (left right : Outcome) → Option (PLift (left = right))
  | .finished a s,.finished b t => do
    let result ← value fuel a b; let states ← state fuel s t
    pure ⟨by cases result.down; cases states.down; rfl⟩
  | .suspended .ticks s,.suspended .ticks t => do
    let states ← state fuel s t; pure ⟨by cases states.down; rfl⟩
  | .suspended .capacity s,.suspended .capacity t => do
    let states ← state fuel s t; pure ⟨by cases states.down; rfl⟩
  | .divergent a s,.divergent b t => do
    let address ← scalar a b; let states ← state fuel s t
    pure ⟨by cases address.down; cases states.down; rfl⟩
  | .refused a s,.refused b t => do
    let reason ← refusal a b; let states ← state fuel s t
    pure ⟨by cases reason.down; cases states.down; rfl⟩
  | _,_ => none

#assert_axioms outcome

#assert_axioms state
#assert_axioms refusal_roundtrip
end Minidregg.Compiler.ObjectiveDemandStateEquality
