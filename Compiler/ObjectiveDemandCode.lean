/- Sole Objective language public code ROM. All actual Core4 constructors are
represented, including lazy fix/mix, reflective specifications/prototypes and
per-field records. This is a source compiler and translation validator, not a
second evaluator. Runtime generated closures still need the demand-machine
representation/simulation bridge. No BendTT modules are imported. -/
import Theory.ObjectiveTermEquality

namespace Minidregg.Compiler.ObjectiveDemandCode
open Minidregg.Theory.ObjectiveBendOpenRecursion
set_option autoImplicit false

inductive Code where
  | bound (index : Nat)
  | lam (body : Nat)
  | app (function argument : Nat)
  | mix (lower upper : Nat)
  | fix (specification inherited : Nat)
  | specification (metadata extension : Nat)
  | prototype (specification target : Nat)
  | reflect (target : Nat)
  | metadata (target : Nat)
  | project (target : Nat)
  | natural (value : Nat)
  | boolean (value : Bool)
  | label (name : Nat)
  | binary (primitive : Primitive) (left right : Nat)
  | extend (inherited : Nat) (fields : List (Nat × Nat))
  | record (fields : List (Nat × Nat))
  | get (target name : Nat)
  | ifZero (value zero successor : Nat)
  deriving Repr, DecidableEq

structure Program where
  names : Array String := #[]
  code : Array Code := #[]
  deriving Repr, DecidableEq

structure Limits where
  codeSlots : Nat
  nameSlots : Nat
  sourceDepth : Nat
  deriving Repr

abbrev Build := StateT Program Option

def intern (limits : Limits) (name : String) : Build Nat := do
  let program ← get
  match program.names.findIdx? (· == name) with
  | some index => pure index
  | none =>
    if program.names.size < limits.nameSlots then
      set {program with names := program.names.push name}
      pure program.names.size
    else failure

def emit (limits : Limits) (code : Code) : Build Nat := do
  let program ← get
  match program.code.findIdx? (fun old => decide (old = code)) with
  | some index => pure index
  | none =>
    if program.code.size < limits.codeSlots then
      set {program with code := program.code.push code}
      pure program.code.size
    else failure

mutual
  def lower (limits : Limits) : Nat → Term → Build Nat
    | 0, _ => failure
    | fuel+1, term => do
      let code ← match term with
        | .bound index => pure (.bound index)
        | .lam body => pure (.lam (← lower limits fuel body))
        | .app function argument => pure (.app (← lower limits fuel function) (← lower limits fuel argument))
        | .mix lowerTerm upper => pure (.mix (← lower limits fuel lowerTerm) (← lower limits fuel upper))
        | .fix spec inherited => pure (.fix (← lower limits fuel spec) (← lower limits fuel inherited))
        | .specification metadata extension => pure (.specification (← lower limits fuel metadata) (← lower limits fuel extension))
        | .prototype spec target => pure (.prototype (← lower limits fuel spec) (← lower limits fuel target))
        | .reflect target => pure (.reflect (← lower limits fuel target))
        | .metadata target => pure (.metadata (← lower limits fuel target))
        | .project target => pure (.project (← lower limits fuel target))
        | .nat value => pure (.natural value)
        | .boolean value => pure (.boolean value)
        | .label name => pure (.label (← intern limits name))
        | .binary primitive left right => pure (.binary primitive (← lower limits fuel left) (← lower limits fuel right))
        | .extend inherited fields => pure (.extend (← lower limits fuel inherited) (← lowerFields limits fuel fields))
        | .record fields => pure (.record (← lowerFields limits fuel fields))
        | .get target name => pure (.get (← lower limits fuel target) (← intern limits name))
        | .ifZero value zero successor => pure (.ifZero (← lower limits fuel value) (← lower limits fuel zero) (← lower limits fuel successor))
      emit limits code

  def lowerFields (limits : Limits) : Nat → List (String × Term) → Build (List (Nat × Nat))
    | _, [] => pure []
    | 0, _ :: _ => failure
    | fuel+1, (name,term) :: rest => do
      let label ← intern limits name
      let code ← lower limits fuel term
      let fields ← lowerFields limits fuel rest
      pure ((label,code) :: fields)
end

mutual
  def decode (program : Program) : Nat → Nat → Option Term
    | 0, _ => none
    | fuel+1, pointer => do
      match ← program.code[pointer]? with
      | .bound index => pure (.bound index)
      | .lam body => pure (.lam (← decode program fuel body))
      | .app function argument => pure (.app (← decode program fuel function) (← decode program fuel argument))
      | .mix lower upper => pure (.mix (← decode program fuel lower) (← decode program fuel upper))
      | .fix spec inherited => pure (.fix (← decode program fuel spec) (← decode program fuel inherited))
      | .specification metadata extension => pure (.specification (← decode program fuel metadata) (← decode program fuel extension))
      | .prototype spec target => pure (.prototype (← decode program fuel spec) (← decode program fuel target))
      | .reflect target => pure (.reflect (← decode program fuel target))
      | .metadata target => pure (.metadata (← decode program fuel target))
      | .project target => pure (.project (← decode program fuel target))
      | .natural value => pure (.nat value)
      | .boolean value => pure (.boolean value)
      | .label name => pure (.label (← program.names[name]?))
      | .binary primitive left right => pure (.binary primitive (← decode program fuel left) (← decode program fuel right))
      | .extend inherited fields => pure (.extend (← decode program fuel inherited) (← decodeFields program fuel fields))
      | .record fields => pure (.record (← decodeFields program fuel fields))
      | .get target name => pure (.get (← decode program fuel target) (← program.names[name]?))
      | .ifZero value zero successor => pure (.ifZero (← decode program fuel value) (← decode program fuel zero) (← decode program fuel successor))

  def decodeFields (program : Program) : Nat → List (Nat × Nat) → Option (List (String × Term))
    | _, [] => some []
    | 0, _ :: _ => none
    | fuel+1, (name,pointer) :: rest => do
      pure ((← program.names[name]?, ← decode program fuel pointer) :: (← decodeFields program fuel rest))
end

def Code.references : Code → List Nat
  | .bound _ | .natural _ | .boolean _ | .label _ => []
  | .lam body | .reflect body | .metadata body | .project body | .get body _ => [body]
  | .app a b | .mix a b | .fix a b | .specification a b | .prototype a b | .binary _ a b => [a,b]
  | .record fields => fields.map (·.2)
  | .extend inherited fields => inherited :: fields.map (·.2)
  | .ifZero a b c => [a,b,c]

def Code.names : Code → List Nat
  | .label name | .get _ name => [name]
  | .record fields | .extend _ fields => fields.map (·.1)
  | _ => []

def Program.valid (program : Program) : Bool :=
  (program.code.toList.zipIdx).all (fun (code,index) =>
    code.references.all (· < index) && code.names.all (· < program.names.size)) &&
  decide program.names.toList.Nodup

/-- Successful publication carries exact decode-to-source evidence. It does
not accept a hash-only source identity or a caller-provided evaluator result. -/
structure Compiled (source : Term) where
  program : Program
  entry : Nat
  decodeDepth : Nat
  valid : program.valid = true
  exact : decode program decodeDepth entry = some source

/-- Compilation refusal is explicit when any public construction/validation
budget is insufficient. Completeness at sufficient bounds is a separate proof. -/
def compile (limits : Limits) (source : Term) : Option (Compiled source) := do
  let (entry,program) ← lower limits limits.sourceDepth source {}
  if valid : program.valid = true then
    let depth := limits.sourceDepth + program.code.size + 1
    match decoded : decode program depth entry with
    | none => none
    | some recovered =>
      match termEqual depth recovered source with
      | some same => some ⟨program,entry,depth,valid,by simpa only [same.down] using decoded⟩
      | none => none
  else none

theorem compiled_source {source : Term} (compiled : Compiled source) :
    decode compiled.program compiled.decodeDepth compiled.entry = some source := compiled.exact

theorem compiled_postorder {source : Term} (compiled : Compiled source) :
    compiled.program.valid = true := compiled.valid

#assert_axioms compiled_source
#assert_axioms compiled_postorder
end Minidregg.Compiler.ObjectiveDemandCode
