/- Bounded immutable closure arena for the pinned live Bend machine.
This representation is shared by the clear microstep interpreter, the fixed
controller circuit and the trace witness. No source Term is stored in a runtime
row. Code/publication supplies a separate CodeDenotes certificate.

This module does NOT yet prove that a controller step implements source Eval.
The representation and persistent-extension lemmas are the seam for that proof.
-/
import Theory.BendLiveMachine

namespace Minidregg.Theory.BendClosureArena
open BendTT
set_option autoImplicit false
universe u v

/-- Ordered elementwise correspondence without a Mathlib dependency. -/
inductive All₂ {α : Type u} {β : Type v} (relation : α → β → Prop) :
    List α → List β → Prop
  | nil : All₂ relation [] []
  | cons {a b left right} : relation a b → All₂ relation left right →
      All₂ relation (a :: left) (b :: right)


/-- All source constructors survive lowering, including dead type/evidence
syntax. Child pointers address an immutable, bounded published code table. -/
inductive Code where
  | var (index : Nat)
  | ref (name : Nat)
  | ann (value type : Nat)
  | lett (quantity : Quan) (value body : Nat)
  | typ (quantity : Quan)
  | all (quantity : Quan) (domain body : Nat)
  | lam (quantity : Quan) (body : Nat)
  | app (quantity : Quan) (function argument : Nat)
  | sig (quantity : Quan) (domain body : Nat)
  | tup (quantity : Quan) (first second : Nat)
  | prj (handler : Nat)
  | enu (labels : Nat)
  | lab (label : Nat)
  | mat (label yes no : Nat)
  | efq
  | eql (left right type : Nat)
  | rfl
  | rwt (evidence motive body : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Names and enumeration lists are interned at source publication. They are
not runtime variable-length string operations. The codec/source publisher must
bind every table byte and prove CodeDenotes for the checked Book/entry. -/
structure Program where
  code : Array Code
  names : Array String
  enumerations : Array (List String)
  deriving Repr

/-- Runtime rows are immutable, except unused rows filled on append. An
environment is a list of value/thunk pointers; a closure captures code+env.
Applications retain the original normalized call spine for underapplication. -/
inductive Row where
  | vacant
  | nil
  | environment (value tail : Nat)
  | closure (code environment : Nat)
  | pair (quantity : Quan) (first second : Nat)
  | application (quantity : Quan) (function argument : Nat)
  deriving DecidableEq, Repr, Inhabited

structure Shape where
  slots : Nat
  wordBits : Nat
  fits : slots ≤ 2 ^ wordBits

structure Heap where
  rows : Array Row
  used : Nat
  deriving DecidableEq, Repr

/-- Pure logical read. The runtime read circuit is the full-scan network,
whose separate refinement must establish this interface for valid addresses. -/
def Heap.get? (heap : Heap) (pointer : Nat) : Option Row :=
  if pointer < heap.used then heap.rows[pointer]? else none

def Row.fits (limit : Nat) : Row → Bool
  | .vacant | .nil => true
  | .environment value tail | .closure value tail => value < limit && tail < limit
  | .pair _ first second | .application _ first second => first < limit && second < limit

def Heap.valid (shape : Shape) (heap : Heap) : Bool :=
  heap.rows.size = shape.slots && heap.used ≤ shape.slots &&
  heap.rows.all (Row.fits (2 ^ shape.wordBits))

def Heap.empty (shape : Shape) : Heap :=
  {rows := Array.replicate shape.slots .vacant, used := 0}

inductive Refusal where
  | shape | capacity | word | dangling
  deriving DecidableEq, Repr

/-- Every runtime heap reference points strictly backwards. Code pointers use
the separate code bound; they are never mistaken for heap references. -/
def Row.referencesFit (codeBound used : Nat) : Row → Bool
  | .vacant => false
  | .nil => true
  | .environment value tail => value < used && tail < used
  | .closure code captured => code < codeBound && captured < used
  | .pair _ first second | .application _ first second => first < used && second < used

/-- A fixed-size functional write touches every row in the reference schedule.
This is not a claim about the clear Lean compiler's side channels; the generated
ObliviousNetwork.writeNetwork implements the physical fixed gate schedule. -/
def fill (rows : Array Row) (pointer : Nat) (value : Row) : Array Row :=
  (rows.toList.zipIdx.map fun pair =>
    if pair.2 = pointer then value else pair.1).toArray

def allocate (shape : Shape) (codeBound : Nat) (heap : Heap) (value : Row) :
    Except Refusal (Nat × Heap) :=
  if !heap.valid shape then .error .shape
  else if heap.used ≥ shape.slots then .error .capacity
  else if !value.fits (2 ^ shape.wordBits) then .error .word
  else if !value.referencesFit codeBound heap.used then .error .dangling
  else .ok (heap.used, {rows := fill heap.rows heap.used value, used := heap.used + 1})

/-- Store extension speaks about exact existing rows, not digest equality.
Every future semantic simulation can transport previously decoded values
without rerunning the source evaluator or assuming a reference oracle. -/
def Extends (old next : Heap) : Prop :=
  ∀ pointer row, old.get? pointer = some row → next.get? pointer = some row

theorem Extends.refl (heap : Heap) : Extends heap heap := by
  intro pointer row found
  exact found

theorem Extends.trans {first middle last : Heap}
    (left : Extends first middle) (right : Extends middle last) : Extends first last := by
  intro pointer row found
  exact right pointer row (left pointer row found)

/-- Publication's exact source-tree relation. It retains every one of the
eighteen source constructors, including live Rwt evidence and dead motives. -/
inductive CodeDenotes (program : Program) : Nat → Term → Prop
  | var {p i} : program.code[p]? = some (.var i) → CodeDenotes program p (.Var i)
  | ref {p k name} : program.code[p]? = some (.ref k) →
      program.names[k]? = some name → CodeDenotes program p (.Ref name)
  | ann {p x t X T} : program.code[p]? = some (.ann x t) →
      CodeDenotes program x X → CodeDenotes program t T → CodeDenotes program p (.Ann X T)
  | lett {p q v f V F} : program.code[p]? = some (.lett q v f) →
      CodeDenotes program v V → CodeDenotes program f F → CodeDenotes program p (.Let q V F)
  | typ {p q} : program.code[p]? = some (.typ q) → CodeDenotes program p (.Typ q)
  | all {p q a b A B} : program.code[p]? = some (.all q a b) →
      CodeDenotes program a A → CodeDenotes program b B → CodeDenotes program p (.All q A B)
  | lam {p q f F} : program.code[p]? = some (.lam q f) →
      CodeDenotes program f F → CodeDenotes program p (.Lam q F)
  | app {p q f x F X} : program.code[p]? = some (.app q f x) →
      CodeDenotes program f F → CodeDenotes program x X → CodeDenotes program p (.App q F X)
  | sig {p q a b A B} : program.code[p]? = some (.sig q a b) →
      CodeDenotes program a A → CodeDenotes program b B → CodeDenotes program p (.Sig q A B)
  | tup {p q a b A B} : program.code[p]? = some (.tup q a b) →
      CodeDenotes program a A → CodeDenotes program b B → CodeDenotes program p (.Tup q A B)
  | prj {p h H} : program.code[p]? = some (.prj h) →
      CodeDenotes program h H → CodeDenotes program p (.Prj H)
  | enu {p k names} : program.code[p]? = some (.enu k) →
      program.enumerations[k]? = some names → CodeDenotes program p (.Enu names)
  | lab {p k name} : program.code[p]? = some (.lab k) →
      program.names[k]? = some name → CodeDenotes program p (.Lab name)
  | mat {p k h m name H M} : program.code[p]? = some (.mat k h m) →
      program.names[k]? = some name → CodeDenotes program h H → CodeDenotes program m M →
      CodeDenotes program p (.Mat name H M)
  | efq {p} : program.code[p]? = some .efq → CodeDenotes program p .Efq
  | eql {p a b t A B T} : program.code[p]? = some (.eql a b t) →
      CodeDenotes program a A → CodeDenotes program b B → CodeDenotes program t T →
      CodeDenotes program p (.Eql A B T)
  | rfl {p} : program.code[p]? = some .rfl → CodeDenotes program p .Rfl
  | rwt {p e m f E M F} : program.code[p]? = some (.rwt e m f) →
      CodeDenotes program e E → CodeDenotes program m M → CodeDenotes program f F →
      CodeDenotes program p (.Rwt E M F)

mutual

/-- Heap reification is a proof relation. Large unary arithmetic source terms
may occur in this erased relation, never as a mandatory runtime witness. -/
inductive Denotes (program : Program) (heap : Heap) : Nat → Term → Prop
  | closure {pointer code environment term values} :
      heap.get? pointer = some (.closure code environment) →
      CodeDenotes program code term → EnvironmentDenotes program heap environment values →
      Denotes program heap pointer (Term.sub (Env.sub values) term)
  | pair {pointer q first second A B} :
      heap.get? pointer = some (.pair q first second) →
      Denotes program heap first A → Denotes program heap second B →
      Denotes program heap pointer (.Tup q A B)
  | application {pointer q function argument F X} :
      heap.get? pointer = some (.application q function argument) →
      Denotes program heap function F → Denotes program heap argument X →
      Denotes program heap pointer (.App q F X)

inductive EnvironmentDenotes (program : Program) (heap : Heap) : Nat → List Term → Prop
  | nil {pointer} : heap.get? pointer = some .nil →
      EnvironmentDenotes program heap pointer []
  | cons {pointer value tail term values} :
      heap.get? pointer = some (.environment value tail) →
      Denotes program heap value term → EnvironmentDenotes program heap tail values →
      EnvironmentDenotes program heap pointer (term :: values)
end

/-- Denotation is intentionally independent of authority. Source publication
and native receiving bind the versioned method graph and current authority;
neither is inferred from this evaluator relation. -/
structure Entry (program : Program) (heap : Heap) (source : Term) where
  pointer : Nat
  exact : Denotes program heap pointer source

#assert_axioms Extends.refl
#assert_axioms Extends.trans
end Minidregg.Theory.BendClosureArena

