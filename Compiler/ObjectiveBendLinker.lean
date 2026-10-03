/- Deterministic declaration linking for Objective Bend. This is not another
runtime: retained bodies are checked by the pinned BendTT kernel. -/
import Compiler.ObjectiveBendElaboration
import Theory.AssertAxioms
namespace Minidregg.Compiler.ObjectiveBendLinker
open Minidregg.Theory.BendTT
open ObjectiveBendComposition ObjectiveBendElaboration
set_option autoImplicit false
private abbrev CoreTerm := Minidregg.Theory.BendTT.Term

private def defKey (d : Def) := (d.k, d.T, d.v, d.o)
private theorem defKey_injective (a b : Def) (h : defKey a = defKey b) : a = b := by
  cases a; cases b; simp_all [defKey]
private instance : DecidableEq Def := fun a b =>
  if h : defKey a = defKey b then isTrue (defKey_injective a b h)
  else isFalse (fun e => h (congrArg defKey e))

/-- Includes references in types and erased syntax too: omission cannot hide
an unresolved helper. Self calls remain subject to the kernel's descent check. -/
def references : CoreTerm → List String
  | .Ref name => [name]
  | .Var _ | .Typ _ | .Enu _ | .Lab _ | .Efq | .Rfl => []
  | .Ann a b | .Let _ a b | .All _ a b | .App _ a b | .Sig _ a b
  | .Tup _ a b | .Mat _ a b => references a ++ references b
  | .Lam _ a | .Prj a => references a
  | .Eql a b c | .Rwt a b c => references a ++ references b ++ references c

/-- Only live references constrain declaration order. Dead type syntax may
refer forward (recursive Data declarations depend on precisely this distinction).
Full reference closure is separately checked and then Book.check validates it. -/
def liveReferences : CoreTerm → List String
  | .Ref name => [name]
  | .Var _ | .Typ _ | .Enu _ | .Lab _ | .Efq | .Rfl
  | .All _ _ _ | .Sig _ _ _ | .Eql _ _ _ => []
  | .Ann value _ => liveReferences value
  | .Let q value body => (if q == .Q0 then [] else liveReferences value) ++ liveReferences body
  | .App q function argument => liveReferences function ++ (if q == .Q0 then [] else liveReferences argument)
  | .Tup q first second => (if q == .Q0 then [] else liveReferences first) ++ liveReferences second
  | .Mat _ yes no => liveReferences yes ++ liveReferences no
  | .Lam _ body | .Prj body => liveReferences body
  | .Rwt evidence _ body => liveReferences evidence ++ liveReferences body

def dependencies (d : Def) : List String :=
  (liveReferences d.v).filter (fun name => name != d.k)

def ready (emitted : Book) (d : Def) : Bool :=
  (dependencies d).all (fun name => (emitted.map Def.k).contains name)

inductive Diagnostic where
  | duplicateName (name : String)
  | missingReference (owner dependency : String)
  | cycle (blocked : List (String × List String))
  | kernel (message : String)
  | changedBook
  | lostDefinition
  | incompleteMethod (owner : Nat) (required : Requirement)
  | missingMethod (name : String)
  | changedMethod (name : String)
  deriving Repr

/-- Stable Kahn order. Fuel is definition count, not evaluation fuel. A cycle
is refused rather than transformed into an unproved mutual dispatcher. -/
def orderLoop : Nat → Book → Book → Except Diagnostic Book
  | 0, [], emitted => .ok emitted
  | 0, pending, _ => .error (.cycle (pending.map fun d => (d.k, dependencies d)))
  | fuel + 1, pending, emitted =>
    if pending.isEmpty then .ok emitted else
    match pending.find? (ready emitted) with
    | none => .error (.cycle (pending.map fun d => (d.k,
        (dependencies d).filter (fun n => !(emitted.map Def.k).contains n))))
    | some next => orderLoop fuel (pending.filter (fun d => d.k != next.k)) (emitted ++ [next])

def order (book : Book) : Except Diagnostic Book := do
  let names := book.map Def.k
  let rec duplicate : List String → Option String
    | [] => none
    | name :: tail => if tail.contains name then some name else duplicate tail
  if let some name := duplicate names then throw (.duplicateName name)
  for d in book do
    for dep in references d.T ++ references d.v do
      if !names.contains dep then throw (.missingReference d.k dep)
  orderLoop book.length book []

/-- Behavioral order supplies method resolution; it does not supply the
kernel declaration order. Helpers participate in the same dependency graph. -/
def generated (layers : List Spec) : Book :=
  (List.finRange layers.length).flatMap fun i =>
    layers[i].provisions.map (definition layers i.val layers[i])

/-- Callback wrappers call the retained source helper rather than claiming a
fresh handwritten body was elaborated from that source. Argument quantities
are explicit and are checked against the helper type by Book.check. -/
def applyArguments (entry : String) (arguments : List (Quan × CoreTerm)) : CoreTerm :=
  arguments.foldl (fun function argument => .App argument.1 function argument.2) (.Ref entry)

def fromEntry {core : BendCoreAdmission.Checked} (entry : BendCoreAdmission.Entry core)
    (source : Nat) (interface : Interface) (arguments : List (Quan × CoreTerm)) : Provision :=
  { interface := interface, source := source, entry := entry.name,
    body := applyArguments entry.name arguments, captured := [] }

theorem fromEntry_exact {core : BendCoreAdmission.Checked}
    (entry : BendCoreAdmission.Entry core) (source : Nat) (interface : Interface)
    (arguments : List (Quan × CoreTerm)) :
    (fromEntry entry source interface arguments).body = applyArguments entry.name arguments ∧
    Book.get core.book (fromEntry entry source interface arguments).entry = some entry.definition :=
  ⟨rfl, entry.exact⟩

def candidate (helpers : Book) (layers : List Spec) : Book := helpers ++ generated layers

structure Linked (helpers : Book) (layers : List Spec) where
  ordered : Book
  ordering : order (candidate helpers layers) = .ok ordered
  retainedDefinitions : ordered.Perm (candidate helpers layers)
  core : BendCoreAdmission.Checked
  retained : core.book = ordered
  helperEntries : ∀ d ∈ helpers, Book.get core.book d.k = some d
  entries : ∀ (i : Fin layers.length) (p : Provision), p ∈ layers[i].provisions →
    Book.get core.book (coreName ⟨i.val, layers[i].id, p⟩) =
      some (definition layers i.val layers[i] p)

/-- Runtime checking constructs exact equalities, including every method body,
type, capture substitution and selected self/super reference. -/
def link (helpers : Book) (layers : List Spec) : Except Diagnostic (Linked helpers layers) := do
  if !closed layers then
    for i in List.finRange layers.length do
      for required in layers[i].requirements do
        if (resolve layers i.val required).isNone then
          throw (.incompleteMethod layers[i].id required)
    throw (.kernel "incompatible signatures or duplicate local declarations")
  let ordered ← order (candidate helpers layers)
  if retainedDefinitions : ordered.Perm (candidate helpers layers) then
    pure ()
  else throw .lostDefinition
  let core ← (admit ordered).mapError Diagnostic.kernel
  if retained : core.book = ordered then
    letI : Decidable (∀ d ∈ generated layers, Book.get core.book d.k = some d) :=
      List.decidableBAll (fun d => Book.get core.book d.k = some d) (generated layers)
    if generatedEntries : ∀ d ∈ generated layers, Book.get core.book d.k = some d then
      have entries : ∀ (i : Fin layers.length) (p : Provision), p ∈ layers[i].provisions →
          Book.get core.book (coreName ⟨i.val, layers[i].id, p⟩) =
            some (definition layers i.val layers[i] p) := by
        intro i p present
        have member : definition layers i.val layers[i] p ∈ generated layers := by
          apply List.mem_flatMap.mpr
          refine ⟨i, List.mem_finRange i, ?_⟩
          exact List.mem_map.mpr ⟨p, present, rfl⟩
        exact generatedEntries (definition layers i.val layers[i] p) member
      -- The successful order equation is recovered below by dependent matching.
      match ordering : order (candidate helpers layers) with
      | .error e => throw e
      | .ok book =>
        if same : book = ordered then
          if retainedDefinitions : ordered.Perm (candidate helpers layers) then
            letI : Decidable (∀ d ∈ helpers, Book.get core.book d.k = some d) :=
              List.decidableBAll (fun d => Book.get core.book d.k = some d) helpers
            if helperEntries : ∀ d ∈ helpers, Book.get core.book d.k = some d then
              pure ⟨ordered, by simpa [same] using ordering, retainedDefinitions, core, retained, helperEntries, entries⟩
            else throw .lostDefinition
          else throw .lostDefinition
        else throw .changedBook
    else throw (.changedMethod "generated methods")
  else throw .changedBook

/-- Link one exact source-admitted helper Book, including its entire closure. -/
def linkSource (source : BendCoreAdmission.Checked) (layers : List Spec) :
    Except Diagnostic (Linked source.book layers) := link source.book layers

variable {helpers : Book} {layers : List Spec}

/-- The actual consumer certificate: no independently checked unrelated Book
can stand in for the resolved source definitions. -/
def construction (linked : Linked helpers layers) (root : Spec)
    (lawful : OrderCertificate root layers) (complete : closed layers = true)
    (captures : ∀ spec ∈ layers, ∀ p ∈ spec.provisions, capturedData p) : Construction :=
  ⟨root, layers, lawful, complete, captures, linked.core, linked.entries⟩

theorem linked_retains (linked : Linked helpers layers) : linked.core.book = linked.ordered :=
  linked.retained

theorem linked_definitions (linked : Linked helpers layers) :
    linked.core.book.Perm (candidate helpers layers) := by
  rw [linked.retained]
  exact linked.retainedDefinitions

theorem linked_helper (linked : Linked helpers layers) (d : Def) (present : d ∈ helpers) :
    Book.get linked.core.book d.k = some d := linked.helperEntries d present

theorem linked_method (linked : Linked helpers layers) (i : Fin layers.length)
    (p : Provision) (present : p ∈ layers[i].provisions) :
    Book.get linked.core.book (coreName ⟨i.val, layers[i].id, p⟩) =
      some (definition layers i.val layers[i] p) := linked.entries i p present

theorem linked_eval_retained (linked : Linked helpers layers) (before after : CoreTerm) :
    Eval linked.core.book before after ↔ Eval linked.ordered before after := by
  rw [linked.retained]

theorem linked_live (linked : Linked helpers layers) :
    Book.WellTyped linked.core.book ∧ Book.Live linked.core.book :=
  BendCoreAdmission.checked_live linked.core

#assert_axioms fromEntry_exact
#assert_axioms linked_eval_retained
#assert_axioms linked_live
#assert_axioms linked_retains
#assert_axioms linked_method
#assert_axioms linked_helper
#assert_axioms linked_definitions
end Minidregg.Compiler.ObjectiveBendLinker
