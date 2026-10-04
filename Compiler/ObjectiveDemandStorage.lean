/- Objective runtime storage references and their literal source meaning.
All seven runtime values and all frames/controls are represented. Heap cycles
are ordinary thunk addresses: decoding an environment/record never recursively
forces those addresses. This is a representation decoder, not an evaluator.
Fixed-bit serialization and emitted transition refinement consume this seam. -/
import Compiler.ObjectiveDemandCode
import Theory.ObjectiveBendDemandMachine

namespace Minidregg.Compiler.ObjectiveDemandStorage
open Minidregg.Theory.ObjectiveBendOpenRecursion
open Minidregg.Theory.ObjectiveBendDemandMachine
open ObjectiveDemandCode
set_option autoImplicit false

/-- Finite shared storage tables. Every environment/field list has a public
capacity in the physical layout. Contents and selected indices may be secret.
The code table may also be shared input; public constant ROM is an optimization,
not a requirement that authored private behavior be disclosed. -/
structure Tables where
  program : Program
  environments : Array (List Nat)
  fields : Array (List (Nat × Nat))
  deriving Repr

structure ClosureRef where
  code : Nat
  environment : Nat
  deriving Repr, DecidableEq

inductive ValueRef where
  | closure (body environment : Nat)
  | natural (value : Nat)
  | boolean (value : Bool)
  | label (name : Nat)
  | record (fields : Nat)
  | specification (metadata extension : Nat)
  | prototype (specification target : Nat)
  deriving Repr, DecidableEq

inductive CellRef where
  | suspended (origin : ClosureRef)
  | evaluating (origin : ClosureRef)
  | cached (origin : ClosureRef) (value : ValueRef)
  deriving Repr, DecidableEq

inductive FrameRef where
  | argument (term environment : Nat)
  | update (address : Nat)
  | field (name : Nat)
  | reflect | metadata | project
  | extend (fields environment : Nat)
  | condition (zero successorBody environment : Nat)
  | binaryLeft (primitive : Primitive) (right environment : Nat)
  | binaryRight (primitive : Primitive) (left : ValueRef)
  deriving Repr, DecidableEq

private def refusalDecEq : DecidableEq Refusal := by
  intro left right
  cases left <;> cases right <;>
    first | exact isTrue rfl | exact isFalse (by intro same; cases same)

local instance : DecidableEq Refusal := refusalDecEq

inductive ControlRef where
  | evaluate (term environment : Nat)
  | enter (address : Nat)
  | blackhole (address : Nat)
  | returned (value : ValueRef)
  | complete (value : ValueRef)
  | refused (reason : Refusal)
  deriving Repr, DecidableEq

structure StateRef where
  heap : Array CellRef
  control : ControlRef
  stack : List FrameRef
  deriving Repr, DecidableEq

def closure (tables : Tables) (depth : Nat) (reference : ClosureRef) : Option Closure := do
  pure ⟨← ObjectiveDemandCode.decode tables.program depth reference.code,
    ← tables.environments[reference.environment]?⟩

def addressFields (tables : Tables) (index : Nat) : Option (List (String × Nat)) := do
  let fields ← tables.fields[index]?
  fields.mapM fun (name,address) => do pure (← tables.program.names[name]?,address)

def termFields (tables : Tables) (depth index : Nat) : Option (List (String × Minidregg.Theory.ObjectiveBendOpenRecursion.Term)) := do
  let fields ← tables.fields[index]?
  fields.mapM fun (name,code) => do
    pure (← tables.program.names[name]?,← ObjectiveDemandCode.decode tables.program depth code)

def value (tables : Tables) (depth : Nat) : ValueRef → Option RuntimeValue
  | .closure body environment => do
    pure (.closure (← ObjectiveDemandCode.decode tables.program depth body) (← tables.environments[environment]?))
  | .natural number => pure (.natural number)
  | .boolean bit => pure (.boolean bit)
  | .label name => do pure (.label (← tables.program.names[name]?))
  | .record fields => do pure (.record (← addressFields tables fields))
  | .specification metadata extension => pure (.specification metadata extension)
  | .prototype specification target => pure (.prototype specification target)

def cell (tables : Tables) (depth : Nat) : CellRef → Option Cell
  | .suspended origin => do pure (.suspended (← closure tables depth origin))
  | .evaluating origin => do pure (.evaluating (← closure tables depth origin))
  | .cached origin cached => do pure (.cached (← closure tables depth origin) (← value tables depth cached))

def frame (tables : Tables) (depth : Nat) : FrameRef → Option Frame
  | .argument term environment => do
    pure (.argument (← ObjectiveDemandCode.decode tables.program depth term) (← tables.environments[environment]?))
  | .update address => pure (.update address)
  | .field name => do pure (.field (← tables.program.names[name]?))
  | .reflect => pure .reflect
  | .metadata => pure .metadata
  | .project => pure .project
  | .extend fields environment => do
    pure (.extend (← termFields tables depth fields) (← tables.environments[environment]?))
  | .condition zero successorBody environment => do
    pure (.condition (← ObjectiveDemandCode.decode tables.program depth zero)
      (← ObjectiveDemandCode.decode tables.program depth successorBody) (← tables.environments[environment]?))
  | .binaryLeft primitive right environment => do
    pure (.binaryLeft primitive (← ObjectiveDemandCode.decode tables.program depth right)
      (← tables.environments[environment]?))
  | .binaryRight primitive left => do pure (.binaryRight primitive (← value tables depth left))

def control (tables : Tables) (depth : Nat) : ControlRef → Option Control
  | .evaluate term environment => do
    pure (.evaluate (← ObjectiveDemandCode.decode tables.program depth term) (← tables.environments[environment]?))
  | .enter address => pure (.enter address)
  | .blackhole address => pure (.blackhole address)
  | .returned result => do pure (.returned (← value tables depth result))
  | .complete result => do pure (.complete (← value tables depth result))
  | .refused reason => pure (.refused reason)

def decode (tables : Tables) (depth : Nat) (reference : StateRef) : Option State := do
  pure ⟨← reference.heap.mapM (cell tables depth), ← control tables depth reference.control,
    ← reference.stack.mapM (frame tables depth)⟩

def initialTables (program : Program) : Tables := ⟨program,#[[]],#[]⟩
def initialRef (entry : Nat) : StateRef := ⟨#[],.evaluate entry 0,[]⟩

/-- Actual compiler output establishes the source initial-state interpretation;
the caller does not supply an initial representation assertion. -/
theorem initial_exact {source : Minidregg.Theory.ObjectiveBendOpenRecursion.Term}
    (compiled : Compiled source) :
    decode (initialTables compiled.program) compiled.decodeDepth (initialRef compiled.entry) =
      some (initial source) := by
  simp [decode,initialTables,initialRef,control,compiled.exact,initial]

/-- Cached update preserves the exact original source closure, even when the
cached value contains a pointer cycle through the same thunk address. -/
theorem cached_origin {tables : Tables} {depth : Nat} {origin : ClosureRef} {cached : ValueRef}
    {sourceOrigin : Closure} {sourceValue : RuntimeValue}
    (originExact : closure tables depth origin = some sourceOrigin)
    (valueExact : value tables depth cached = some sourceValue) :
    cell tables depth (.cached origin cached) = some (.cached sourceOrigin sourceValue) := by
  simp [cell,originExact,valueExact]

#assert_axioms initial_exact
#assert_axioms cached_origin
end Minidregg.Compiler.ObjectiveDemandStorage

