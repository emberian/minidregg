/- Partial prototype calls elaborate to ordinary pinned BendTT references.
The resulting complete Book is parsed and checked by BendCoreAdmission. No
second object evaluator, copied closure, arbitrary fixed point or host lazy
initialization is introduced. -/
import Compiler.ObjectiveBendComposition
import Compiler.BendCoreAdmission
import Theory.AssertAxioms

namespace Minidregg.Compiler.ObjectiveBendElaboration
open Minidregg.Theory.BendTT
open ObjectiveBendComposition
set_option autoImplicit false

/-- Generated names bind owner, position and interface; the original source
entry remains in Selected.provision.entry for source inspection/attribution. -/
def coreName (selected : Selected) : String :=
  "objective." ++ toString selected.owner ++ "." ++ toString selected.provider ++
    "." ++ selected.provision.interface.selector

def reference (layers : List Spec) (cursor : Nat) (required : Requirement) : Option Minidregg.Theory.BendTT.Term :=
  (resolve layers cursor required).map (fun selected => .Ref (coreName selected))

/-- This is an exact core reference to the selected provision, not a statement
that an externally generated manifest happened to name the same method. -/
theorem reference_exact (layers : List Spec) (cursor : Nat) (required : Requirement)
    (selected : Selected) (found : resolve layers cursor required = some selected) :
    reference layers cursor required = some (.Ref (coreName selected)) := by
  simp [reference, found]

/-- Rename global method references structurally in the actual source AST.
Binders/de Bruijn variables, quantities, types and dead terms are preserved. -/
def rewriteRefs (rename : String → String) : Minidregg.Theory.BendTT.Term → Minidregg.Theory.BendTT.Term
  | .Var index => .Var index
  | .Ref name => .Ref (rename name)
  | .Ann value type => .Ann (rewriteRefs rename value) (rewriteRefs rename type)
  | .Let q value body => .Let q (rewriteRefs rename value) (rewriteRefs rename body)
  | .Typ q => .Typ q
  | .All q domain range => .All q (rewriteRefs rename domain) (rewriteRefs rename range)
  | .Lam q body => .Lam q (rewriteRefs rename body)
  | .App q function argument => .App q (rewriteRefs rename function) (rewriteRefs rename argument)
  | .Sig q first second => .Sig q (rewriteRefs rename first) (rewriteRefs rename second)
  | .Tup q first second => .Tup q (rewriteRefs rename first) (rewriteRefs rename second)
  | .Prj body => .Prj (rewriteRefs rename body)
  | .Enu labels => .Enu labels
  | .Lab label => .Lab label
  | .Mat label yes no => .Mat label (rewriteRefs rename yes) (rewriteRefs rename no)
  | .Efq => .Efq
  | .Eql first second type => .Eql (rewriteRefs rename first) (rewriteRefs rename second) (rewriteRefs rename type)
  | .Rfl => .Rfl
  | .Rwt equality motive body => .Rwt (rewriteRefs rename equality) (rewriteRefs rename motive) (rewriteRefs rename body)

theorem rewrite_identity (term : Minidregg.Theory.BendTT.Term) : rewriteRefs id term = term := by
  induction term <;> simp_all [rewriteRefs]

def authoredName (required : Requirement) : String :=
  (match required.scope with | .finalSelf => "self." | .priorSuper => "super.") ++
    required.interface.selector

def resolvedNames (layers : List Spec) (cursor : Nat) (spec : Spec) : List (String × String) :=
  spec.requirements.filterMap fun required =>
    (resolve layers cursor required).map (fun selected => (authoredName required, coreName selected))

def rename (names : List (String × String)) (name : String) : String :=
  match names.find? (fun pair => pair.1 == name) with
  | some pair => pair.2
  | none => name

/-- Captured immutable Data is substituted into the authored method. The
complete Book check rejects invalid affine usage, unresolved refs, illegal
recursive calls and type mismatches after self/super resolution. -/
def definition (layers : List Spec) (cursor : Nat) (spec : Spec) (provision : Provision) : Def :=
  let names := resolvedNames layers cursor spec
  { k := coreName ⟨cursor, spec.id, provision⟩
    T := rewriteRefs (rename names) (Minidregg.Theory.BendTT.Term.sub (Env.sub provision.captured) provision.interface.type)
    v := rewriteRefs (rename names) (Minidregg.Theory.BendTT.Term.sub (Env.sub provision.captured) provision.body)
    o := false }

/-- Core declaration order is explicit. A caller chooses a topological order
or guarded/bounded source construction; inheritance order alone is not proof
of the Bend live-call restriction. The checker is the admission boundary. -/
def admit (book : Book) : Except String BendCoreAdmission.Checked :=
  BendCoreAdmission.admit (BendCoreAdmission.encode book)

/-- Construction is a closed, lawful source elaboration into a checked core.
Every authored method is an exact definition in that Book; a separate metadata
manifest or Boolean success flag cannot witness these equalities. Admission of
captured Data is explicit. Source attribution/persistent identity is supplied by
the canonical source loader, separately from this semantic certificate. -/
structure Construction where
  root : Spec
  layers : List Spec
  lawful : OrderCertificate root layers
  complete : closed layers = true
  captures : ∀ spec ∈ layers, ∀ provision ∈ spec.provisions, capturedData provision
  core : BendCoreAdmission.Checked
  entries : ∀ (index : Fin layers.length) (provision : Provision),
    provision ∈ layers[index].provisions →
    Book.get core.book (coreName ⟨index.val, layers[index].id, provision⟩) =
      some (definition layers index.val layers[index] provision)

/-- The implementation installed in the actual checked Book is exactly the
elaboration of its authored body, captures and selected self/super references. -/
theorem constructed_method_exact (construction : Construction)
    (index : Fin construction.layers.length) (provision : Provision)
    (present : provision ∈ construction.layers[index].provisions) :
    Book.get construction.core.book
      (coreName ⟨index.val, construction.layers[index].id, provision⟩) =
    some (definition construction.layers index.val construction.layers[index] provision) :=
  construction.entries index provision present

/-- An invocation of an installed authored method is an ACTUAL upstream
Eval.call with its exact source Walk. This is one source call step; it does not
claim that the method's inline beta/match count equals the call-step count. -/
theorem constructed_invocation (construction : Construction)
    (index : Fin construction.layers.length) (provision : Provision)
    (present : provision ∈ construction.layers[index].provisions)
    (arguments : List Arg) (output : Minidregg.Theory.BendTT.Term)
    (values : Values construction.core.book arguments)
    (walked : Walk construction.core.book
      (definition construction.layers index.val construction.layers[index] provision).v
      [] arguments (some output)) :
    Eval construction.core.book
      (Minidregg.Theory.BendTT.Term.spine (.Ref (coreName ⟨index.val, construction.layers[index].id, provision⟩))
        arguments) output :=
  .call (constructed_method_exact construction index provision present) values walked

/-- Dispatch selection and captured/source body elaboration meet the same core
call boundary. No metadata/provider name can substitute for the installed body. -/
theorem resolved_invocation (construction : Construction) (cursor : Nat)
    (required : Requirement) (index : Fin construction.layers.length)
    (provision : Provision) (present : provision ∈ construction.layers[index].provisions)
    (selected : resolve construction.layers cursor required =
      some ⟨index.val, construction.layers[index].id, provision⟩)
    (arguments : List Arg) (output : Minidregg.Theory.BendTT.Term)
    (values : Values construction.core.book arguments)
    (walked : Walk construction.core.book
      (definition construction.layers index.val construction.layers[index] provision).v
      [] arguments (some output)) :
    reference construction.layers cursor required =
      some (.Ref (coreName ⟨index.val, construction.layers[index].id, provision⟩)) ∧
    Eval construction.core.book
      (Minidregg.Theory.BendTT.Term.spine (.Ref (coreName ⟨index.val, construction.layers[index].id, provision⟩))
        arguments) output :=
  ⟨reference_exact _ _ _ _ selected,
    constructed_invocation construction index provision present arguments output values walked⟩

/-- Every admitted elaborated Book inherits the exact upstream typing and live
termination contract. This does not assert a surface parser refinement or
universal FAREOO fixed-point correspondence. -/
theorem admitted_core_sound (core : BendCoreAdmission.Checked) :
    Book.WellTyped core.book ∧ Book.Live core.book := BendCoreAdmission.checked_live core

#assert_axioms reference_exact
#assert_axioms rewrite_identity
#assert_axioms constructed_method_exact
#assert_axioms constructed_invocation
#assert_axioms resolved_invocation
#assert_axioms admitted_core_sound
end Minidregg.Compiler.ObjectiveBendElaboration
