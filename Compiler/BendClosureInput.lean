/- Source-connected bounded loader for the actual closure heap.
This clear publication/native conformance loader uses a fixed admitted code
table. It never compiles secret literal syntax into public ROM. It is not itself
a private protocol: secret input loading must realize the same row relation with
a fixed schedule and malicious input qualification. -/
import Compiler.BendClosureCompile
import Theory.BendClosureDecode

namespace Minidregg.Compiler.BendClosureInput
open Minidregg.Theory BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

/-- Structural first-order input data. Q0 arbitrary dead syntax is deliberately
not represented here; an existing qualified thunk has a separate custody path. -/
inductive DataTree where
  | label (name : String)
  | refl
  | pair (quantity : Quan) (first second : DataTree)
  deriving DecidableEq, Repr

def DataTree.source : DataTree → Term
  | .label name => .Lab name
  | .refl => .Rfl
  | .pair q first second => .Tup q first.source second.source

theorem DataTree.source_data (tree : DataTree) : Data tree.source := by
  induction tree with
  | label => exact .lab
  | refl => exact .rfl
  | pair q first second ihFirst ihSecond => exact .tup (fun _ => ihFirst) ihSecond

inductive Failure where
  | missingLiteral
  | arena (reason : Refusal)
  | missingEmptyEnvironment
  | validation
  deriving DecidableEq, Repr

/-- First matching literal instruction. Fixed-program private lowering uses
the corresponding public lookup relation, not a secret String host lookup. -/
def literal (program : Program) (tree : DataTree) : Option Nat :=
  ((program.code.toList.zipIdx).find? fun item =>
    match tree, item.1 with
    | .label name, .lab index => program.names[index]? == some name
    | .refl, .rfl => true
    | _, _ => false).map Prod.snd

abbrev Load := StateT Heap (Except Failure)

def append (shape : Shape) (program : Program) (row : Row) : Load Nat := do
  let heap ← get
  match BendClosureArena.allocate shape program.code.size heap row with
  | .error reason => throw (.arena reason)
  | .ok (pointer, next) => set next; pure pointer

def lower (shape : Shape) (program : Program) (emptyEnvironment : Nat) :
    DataTree → Load Nat
  | .label name => do
    match literal program (.label name) with
    | none => throw .missingLiteral
    | some pc => append shape program (.closure pc emptyEnvironment)
  | .refl => do
    match literal program .refl with
    | none => throw .missingLiteral
    | some pc => append shape program (.closure pc emptyEnvironment)
  | .pair quantity first second => do
    let first ← lower shape program emptyEnvironment first
    let second ← lower shape program emptyEnvironment second
    append shape program (.pair quantity first second)

structure Loaded (program : Program) (tree : DataTree) where
  heap : Heap
  pointer : Nat
  exact : Denotes program heap pointer tree.source

/-- Reification validates the exact source value of the actual allocated heap.
It supplies no authorization, input-share consistency, or MPC privacy evidence.
A missing admitted literal code or capacity overflow is an explicit refusal. -/
def load (shape : Shape) (program : Program) (heap : Heap)
    (emptyEnvironment : Nat) (tree : DataTree) : Except Failure (Loaded program tree) := do
  if heap.get? emptyEnvironment != some .nil then throw .missingEmptyEnvironment
  let (pointer, next) ← (lower shape program emptyEnvironment tree).run heap
  match decode program next (next.used + program.code.size + 1) pointer with
  | none => throw .validation
  | some decoded =>
    if same : decoded.term = tree.source then
      pure ⟨next, pointer, same ▸ decoded.exact⟩
    else throw .validation

theorem loaded_exact {program : Program} {tree : DataTree}
    (loaded : Loaded program tree) : Denotes program loaded.heap loaded.pointer tree.source :=
  loaded.exact

theorem loaded_data {program : Program} {tree : DataTree}
    (_loaded : Loaded program tree) : Data tree.source := tree.source_data

#assert_axioms DataTree.source_data
#assert_axioms load
#assert_axioms loaded_exact
#assert_axioms loaded_data
end Minidregg.Compiler.BendClosureInput
