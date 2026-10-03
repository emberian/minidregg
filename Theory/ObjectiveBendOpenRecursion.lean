/- Reference runtime core for Objective Bend's own language edition.
Weak-head call-by-name gives an independent partial meaning to lazy mix/fix.
A sharing implementation must prove representation adequacy; this reference
relation does not claim a heap machine, type safety, termination, proof
consistency, or authority. BendTT's existing total calculus is a distinct
supported embedding, not an admission theorem for these new constructors. -/
namespace Minidregg.Theory.ObjectiveBendOpenRecursion
set_option autoImplicit false

inductive Term where
  | bound (index : Nat)
  | lam (body : Term)
  | app (function argument : Term)
  | mix (inheritedExtension wrappingExtension : Term)
  | fix (specification inherited : Term)
  | nat (value : Nat)
  | record (fields : List (String × Term))
  | get (target : Term) (name : String)
  | ifZero (value zero successorBody : Term)
  deriving Repr

def liftRename (rename : Nat → Nat) : Nat → Nat
  | 0 => 0 | n + 1 => rename n + 1

def Term.rename (rename : Nat → Nat) : Term → Term
  | .bound index => .bound (rename index)
  | .lam body => .lam (body.rename (liftRename rename))
  | .app function argument => .app (function.rename rename) (argument.rename rename)
  | .mix first second => .mix (first.rename rename) (second.rename rename)
  | .fix spec inherited => .fix (spec.rename rename) (inherited.rename rename)
  | .nat value => .nat value
  | .record fields => .record (fields.map fun (name,body) => (name,body.rename rename))
  | .get target name => .get (target.rename rename) name
  | .ifZero value zero successorBody =>
      .ifZero (value.rename rename) (zero.rename rename)
        (successorBody.rename (liftRename rename))

def liftSubstitution (substitution : Nat → Term) : Nat → Term
  | 0 => .bound 0
  | n + 1 => (substitution n).rename Nat.succ

def Term.substitute (substitution : Nat → Term) : Term → Term
  | .bound index => substitution index
  | .lam body => .lam (body.substitute (liftSubstitution substitution))
  | .app function argument => .app (function.substitute substitution) (argument.substitute substitution)
  | .mix first second => .mix (first.substitute substitution) (second.substitute substitution)
  | .fix spec inherited => .fix (spec.substitute substitution) (inherited.substitute substitution)
  | .nat value => .nat value
  | .record fields => .record (fields.map fun (name,body) => (name,body.substitute substitution))
  | .get target name => .get (target.substitute substitution) name
  | .ifZero value zero successorBody =>
      .ifZero (value.substitute substitution) (zero.substitute substitution)
        (successorBody.substitute (liftSubstitution substitution))

def instantiate (body argument : Term) : Term :=
  body.substitute (fun index => match index with | 0 => argument | n + 1 => .bound n)

/-- `λself. λsuper. upper self (lower self super)`: the inherited target is a
computation; both extensions receive the identical final self expression. -/
def mixBody (lower upper : Term) : Term :=
  .lam (.lam (.app (.app (upper.rename (fun n => n + 2)) (.bound 1))
    (.app (.app (lower.rename (fun n => n + 2)) (.bound 1)) (.bound 0))))

inductive Value : Term → Prop where
  | function (body : Term) : Value (.lam body)
  | natural (n : Nat) : Value (.nat n)
  | record (fields : List (String × Term)) : Value (.record fields)

inductive Step : Term → Term → Prop where
  | beta (body argument : Term) : Step (.app (.lam body) argument) (instantiate body argument)
  | application {function next : Term} (argument : Term) :
      Step function next → Step (.app function argument) (.app next argument)
  | mix (lower upper : Term) : Step (.mix lower upper) (mixBody lower upper)
  | fix (spec inherited : Term) :
      Step (.fix spec inherited) (.app (.app spec (.fix spec inherited)) inherited)
  | target {target next : Term} (name : String) :
      Step target next → Step (.get target name) (.get next name)
  | field (fields : List (String × Term)) (name : String) (body : Term) :
      fields.find? (fun field => field.1 == name) = some (name,body) →
      Step (.get (.record fields) name) body
  | condition {value next : Term} (zero successorBody : Term) :
      Step value next → Step (.ifZero value zero successorBody) (.ifZero next zero successorBody)
  | zero (zero successorBody : Term) : Step (.ifZero (.nat 0) zero successorBody) zero
  | successor (n : Nat) (zero successorBody : Term) :
      Step (.ifZero (.nat (n + 1)) zero successorBody) (instantiate successorBody (.nat n))

inductive Steps : Term → Term → Prop where
  | refl (term : Term) : Steps term term
  | next {initial middle result : Term} : Step initial middle → Steps middle result → Steps initial result

def Evaluates (initial result : Term) : Prop := Steps initial result ∧ Value result

/-- Refinement is a substantive consumer obligation over independently defined
source steps. It cannot be discharged by naming a resolved method a new Eval. -/
structure Representation (State : Type) where
  represents : State → Term → Prop
  step : State → State
  /-- Administrative sharing/cache steps may stutter. Semantic steps must
  simulate the independent core, rather than redefine it from this machine. -/
  simulation : ∀ state source, represents state source →
    ∃ next, represents (step state) next ∧ (next = source ∨ Step source next)

theorem lazy_fixed_function :
    Evaluates (.fix (.lam (.lam (.lam (.bound 0)))) (.nat 7)) (.lam (.bound 0)) := by
  constructor
  · exact .next (.fix _ _) (.next (.application _ (.beta _ _)) (.next (.beta _ _) (.refl _)))
  · exact .function _

end Minidregg.Theory.ObjectiveBendOpenRecursion
