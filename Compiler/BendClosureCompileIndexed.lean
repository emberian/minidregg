/- Indexed publication compiler with exact immutable-code sharing.
Every constructor (including Q0 fields and live Rwt evidence) survives. Ordered
Book definitions remain ordered; names/enumerations/code are interned exactly.
The existing translation validator supplies the SAME Compiled certificate.
This changes representation and physical publication work, not source identity,
source resource charging, or private controller semantics.
-/
import Compiler.BendClosureCompile
import Std.Data.HashMap

namespace Minidregg.Compiler.BendClosureCompileIndexed
open Minidregg.Theory BendTT BendClosureArena BendClosureMachine
set_option autoImplicit false

/-- Pin separately from source identity when retaining a lowered artifact. -/
def edition : String := "bendtt-indexed-code-v1"

private def quantityKey : Quan → Nat
  | .Q0 => 0
  | .Q1 => 1
  | .Q2 => 2

/-- Constructor tags and every field form an exact structural key. Hash
collisions are resolved by List Nat equality, never by a lossy digest. -/
def codeKey : Code → List Nat
  | .var i => [0,i]
  | .ref n => [1,n]
  | .ann v t => [2,v,t]
  | .lett q v f => [3,quantityKey q,v,f]
  | .typ q => [4,quantityKey q]
  | .all q a b => [5,quantityKey q,a,b]
  | .lam q f => [6,quantityKey q,f]
  | .app q f x => [7,quantityKey q,f,x]
  | .sig q a b => [8,quantityKey q,a,b]
  | .tup q a b => [9,quantityKey q,a,b]
  | .prj h => [10,h]
  | .enu ks => [11,ks]
  | .lab k => [12,k]
  | .mat k h m => [13,k,h,m]
  | .efq => [14]
  | .eql a b t => [15,a,b,t]
  | .rfl => [16]
  | .rwt e p f => [17,e,p,f]

private theorem quantityKey_eq_iff (left right : Quan) :
    quantityKey left = quantityKey right ↔ left = right := by
  cases left <;> cases right <;> decide

/-- Equal intern keys mean equal complete code instructions, including the
quantity and every child/name/enumeration index. -/
theorem codeKey_injective (left right : Code) (same : codeKey left = codeKey right) :
    left = right := by
  cases left <;> cases right <;> simp_all [codeKey, quantityKey_eq_iff]

structure BuildState where
  program : Program := ⟨#[], #[], #[]⟩
  names : Std.HashMap String Nat := {}
  enumerations : Std.HashMap (List String) Nat := {}
  code : Std.HashMap (List Nat) Nat := {}

abbrev Build := StateM BuildState

def internName (name : String) : Build Nat := do
  let state ← get
  match state.names[name]? with
  | some index => pure index
  | none =>
    let index := state.program.names.size
    let program := { state.program with names := state.program.names.push name }
    set { state with program := program, names := state.names.insert name index }
    pure index

def internEnumeration (labels : List String) : Build Nat := do
  let state ← get
  match state.enumerations[labels]? with
  | some index => pure index
  | none =>
    let index := state.program.enumerations.size
    let program := { state.program with enumerations := state.program.enumerations.push labels }
    set { state with program := program, enumerations := state.enumerations.insert labels index }
    pure index

def emit (instruction : Code) : Build Nat := do
  let state ← get
  let key := codeKey instruction
  match state.code[key]? with
  | some index => pure index
  | none =>
    let index := state.program.code.size
    let program := { state.program with code := state.program.code.push instruction }
    set { state with program := program, code := state.code.insert key index }
    pure index

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
  let (result, state) := work.run {}
  return (⟨state.program, result.1⟩, result.2)

/-- A previously admitted immutable Book avoids a second whole-Book check.
The caller supplies the real checker theorem; there is no trusted Boolean or
unchecked foreign compiler success. Every result uses the existing validators. -/
def compileChecked (book : Book) (source : Term) (checked : Book.check book = .ok ()) :
    Option (BendClosureCompile.Compiled book source) := do
  let (library, entry) := build book source
  let ticks := library.program.code.size + 1
  let definitions ← BendClosureCompile.validateDefinitions library.program ticks library.definitions.toList book
  let exact ← BendClosureCompile.validateCode library.program ticks entry source
  pure ⟨library, entry, checked, definitions.down, exact.exact⟩

/-- Standalone publication retains actual checker admission. -/
def compile (book : Book) (source : Term) : Option (BendClosureCompile.Compiled book source) :=
  match checked : Book.check book with
  | .error _ => none
  | .ok () => compileChecked book source checked

theorem compiled_source {book : Book} {source : Term}
    (result : BendClosureCompile.Compiled book source) :
    result.library.SourceCorrespondence book ∧
      CodeDenotes result.library.program result.entry source :=
  BendClosureCompile.compiled_source result

#assert_axioms codeKey
#assert_axioms codeKey_injective
#assert_axioms build
#assert_axioms compileChecked
#assert_axioms compile
#assert_axioms compiled_source
end Minidregg.Compiler.BendClosureCompileIndexed
