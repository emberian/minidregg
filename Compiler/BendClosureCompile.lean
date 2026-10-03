/- Actual source-to-arena compiler for Objective Bend publication.
All source constructors survive. A proof-producing translation-validation pass
binds the final arrays back to the exact Book and entry; no runtime result is
supplied by the source evaluator. General compiler completeness is a separate
obligation. The receiving layer still supplies entry typing, authority, and
the controller simulation before accepting native effects. -/
import Theory.BendClosureMachine
import Theory.BendClosureDecode

namespace Minidregg.Compiler.BendClosureCompile
open Minidregg.Theory BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

abbrev Build := StateM Program

def internName (name : String) : Build Nat := do
  let program ← get
  match program.names.findIdx? (· == name) with
  | some index => pure index
  | none =>
    set {program with names := program.names.push name}
    pure program.names.size

def internEnumeration (labels : List String) : Build Nat := do
  let program ← get
  match program.enumerations.findIdx? (· == labels) with
  | some index => pure index
  | none =>
    set {program with enumerations := program.enumerations.push labels}
    pure program.enumerations.size

def emit (instruction : Code) : Build Nat := do
  let program ← get
  set {program with code := program.code.push instruction}
  pure program.code.size

/-- Postorder append keeps every child strictly before its parent. Q0 syntax
and rewrite motives remain available for exact source identity and checking. -/
def term : Term → Build Nat
  | .Var index => emit (.var index)
  | .Ref name => do emit (.ref (← internName name))
  | .Ann value type => do
    let value ← term value
    let type ← term type
    emit (.ann value type)
  | .Let quantity value body => do
    let value ← term value
    let body ← term body
    emit (.lett quantity value body)
  | .Typ quantity => emit (.typ quantity)
  | .All quantity domain body => do
    let domain ← term domain
    let body ← term body
    emit (.all quantity domain body)
  | .Lam quantity body => do emit (.lam quantity (← term body))
  | .App quantity function argument => do
    let function ← term function
    let argument ← term argument
    emit (.app quantity function argument)
  | .Sig quantity domain body => do
    let domain ← term domain
    let body ← term body
    emit (.sig quantity domain body)
  | .Tup quantity first second => do
    let first ← term first
    let second ← term second
    emit (.tup quantity first second)
  | .Prj handler => do emit (.prj (← term handler))
  | .Enu labels => do emit (.enu (← internEnumeration labels))
  | .Lab label => do emit (.lab (← internName label))
  | .Mat label yes no => do
    let label ← internName label
    let yes ← term yes
    let no ← term no
    emit (.mat label yes no)
  | .Efq => emit .efq
  | .Eql left right type => do
    let left ← term left
    let right ← term right
    let type ← term type
    emit (.eql left right type)
  | .Rfl => emit .rfl
  | .Rwt evidence motive body => do
    let evidence ← term evidence
    let motive ← term motive
    let body ← term body
    emit (.rwt evidence motive body)

def build (book : Book) (entry : Term) : Library × Nat := Id.run do
  let work : Build (Array (Nat × Nat) × Nat) := do
    let mut definitions := #[]
    for definition in book do
      let name ← internName definition.k
      let body ← term definition.v
      definitions := definitions.push (name, body)
    let pointer ← term entry
    pure (definitions, pointer)
  let (result, program) := work.run ⟨#[], #[], #[]⟩
  return (⟨program, result.1⟩, result.2)

structure CodeWitness (program : Program) (pointer : Nat) (source : Term) : Type where
  exact : CodeDenotes program pointer source

def validateCode (program : Program) (ticks pointer : Nat) (source : Term) :
    Option (CodeWitness program pointer source) := do
  let decoded ← decodeCode program ticks pointer
  if same : decoded.term = source then
    pure ⟨same ▸ decoded.exact⟩
  else none

def DefinitionRelation (program : Program) (projection : Nat × Nat)
    (definition : Def) : Prop :=
  program.names[projection.1]? = some definition.k ∧
    CodeDenotes program projection.2 definition.v

def validateDefinitions (program : Program) (ticks : Nat) :
    (definitions : List (Nat × Nat)) → (book : Book) →
      Option (PLift (All₂ (DefinitionRelation program) definitions book))
  | [], [] => some ⟨.nil⟩
  | projection :: rest, definition :: tail => do
    if name : program.names[projection.1]? = some definition.k then
      let body ← validateCode program ticks projection.2 definition.v
      let remaining ← validateDefinitions program ticks rest tail
      pure ⟨.cons ⟨name, body.exact⟩ remaining.down⟩
    else none
  | _, _ => none

structure Compiled (book : Book) (source : Term) where
  library : Library
  entry : Nat
  bookChecked : Book.check book = .ok ()
  definitions : library.SourceCorrespondence book
  exactEntry : CodeDenotes library.program entry source

/-- Runtime bounds are checked by Machine.start. This publication pass uses
the produced code-table size plus one as an explicit decoding budget. Failure
remains a compilation/validation refusal, never an execution success. -/
def compile (book : Book) (source : Term) : Option (Compiled book source) :=
  match checked : Book.check book with
  | .error _ => none
  | .ok () => do
    let (library, entry) := build book source
    let ticks := library.program.code.size + 1
    let definitions ← validateDefinitions library.program ticks library.definitions.toList book
    let exact ← validateCode library.program ticks entry source
    pure ⟨library, entry, checked, definitions.down, exact.exact⟩

theorem compiled_source {book : Book} {source : Term} (result : Compiled book source) :
    result.library.SourceCorrespondence book ∧
      CodeDenotes result.library.program result.entry source :=
  ⟨result.definitions, result.exactEntry⟩

theorem compiled_book_checked {book : Book} {source : Term}
    (result : Compiled book source) : Book.check book = .ok () :=
  result.bookChecked

#assert_axioms validateCode
#assert_axioms validateDefinitions
#assert_axioms compile
#assert_axioms compiled_source
#assert_axioms compiled_book_checked
end Minidregg.Compiler.BendClosureCompile
