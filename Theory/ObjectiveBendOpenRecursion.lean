/- Reference runtime core for Objective Bend's own language edition.
Core scalar edition 2 distinguishes Booleans from arbitrary String labels.
Weak-head call-by-name gives an independent partial meaning to lazy mix/fix.
A sharing implementation must prove representation adequacy; this reference
relation does not claim a heap machine, type safety, termination, proof
consistency, or authority. BendTT's existing total calculus is a distinct
supported embedding, not an admission theorem for these new constructors. -/
import Lean
namespace Minidregg.Theory.ObjectiveBendOpenRecursion
set_option autoImplicit false

inductive Primitive where
  | add | multiply | equal | conjunction
  deriving Repr, DecidableEq

inductive Term where
  | bound (index : Nat)
  | lam (body : Term)
  | app (function argument : Term)
  | mix (inheritedExtension wrappingExtension : Term)
  | fix (specification inherited : Term)
  | specification (metadata extension : Term)
  | prototype (specification target : Term)
  | reflect (prototype : Term)
  | metadata (specification : Term)
  | project (prototype : Term)
  | nat (value : Nat)
  | boolean (value : Bool)
  | label (value : String)
  | binary (primitive : Primitive) (left right : Term)
  | extend (inherited : Term) (fields : List (String × Term))
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
  | .specification descriptor extension => .specification (descriptor.rename rename) (extension.rename rename)
  | .prototype spec target => .prototype (spec.rename rename) (target.rename rename)
  | .reflect target => .reflect (target.rename rename)
  | .metadata spec => .metadata (spec.rename rename)
  | .project target => .project (target.rename rename)
  | .nat value => .nat value
  | .boolean value => .boolean value
  | .label value => .label value
  | .binary primitive left right => .binary primitive (left.rename rename) (right.rename rename)
  | .extend inherited fields => .extend (inherited.rename rename)
      (fields.map fun field => (field.1,field.2.rename rename))
  | .record fields => .record (fields.map fun field => (field.1,field.2.rename rename))
  | .get target name => .get (target.rename rename) name
  | .ifZero value zero successorBody =>
      .ifZero (value.rename rename) (zero.rename rename)
        (successorBody.rename (liftRename rename))

termination_by source => sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf field.snd < sizeOf field := by
         cases field
         simp +arith
       omega)

def liftSubstitution (substitution : Nat → Term) : Nat → Term
  | 0 => .bound 0
  | n + 1 => (substitution n).rename Nat.succ

def Term.substitute (substitution : Nat → Term) : Term → Term
  | .bound index => substitution index
  | .lam body => .lam (body.substitute (liftSubstitution substitution))
  | .app function argument => .app (function.substitute substitution) (argument.substitute substitution)
  | .mix first second => .mix (first.substitute substitution) (second.substitute substitution)
  | .fix spec inherited => .fix (spec.substitute substitution) (inherited.substitute substitution)
  | .specification descriptor extension => .specification (descriptor.substitute substitution) (extension.substitute substitution)
  | .prototype spec target => .prototype (spec.substitute substitution) (target.substitute substitution)
  | .reflect target => .reflect (target.substitute substitution)
  | .metadata spec => .metadata (spec.substitute substitution)
  | .project target => .project (target.substitute substitution)
  | .nat value => .nat value
  | .boolean value => .boolean value
  | .label value => .label value
  | .binary primitive left right => .binary primitive (left.substitute substitution) (right.substitute substitution)
  | .extend inherited fields => .extend (inherited.substitute substitution)
      (fields.map fun field => (field.1,field.2.substitute substitution))
  | .record fields => .record (fields.map fun field => (field.1,field.2.substitute substitution))
  | .get target name => .get (target.substitute substitution) name
  | .ifZero value zero successorBody =>
      .ifZero (value.substitute substitution) (zero.substitute substitution)
        (successorBody.substitute (liftSubstitution substitution))

termination_by source => sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rename_i hmem
       have hlist := List.sizeOf_lt_of_mem hmem
       have hpair : sizeOf field.snd < sizeOf field := by
         cases field
         simp +arith
       omega)

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
  | boolean (value : Bool) : Value (.boolean value)
  | label (name : String) : Value (.label name)
  | record (fields : List (String × Term)) : Value (.record fields)
  | specification (metadata extension : Term) : Value (.specification metadata extension)
  | prototype (spec target : Term) : Value (.prototype spec target)

/-- A record-target fragment only. Other target kinds use ordinary extensions.
New fields shadow inherited fields; the inherited computation remains super. -/
def extendFields (inherited fields : List (String × Term)) : List (String × Term) :=
  fields ++ inherited.filter (fun prior => !(fields.any fun field => field.1 == prior.1))

def primitiveResult : Primitive → Term → Term → Option Term
  | .add, .nat a, .nat b => some (.nat (a + b))
  | .multiply, .nat a, .nat b => some (.nat (a * b))
  | .equal, .nat a, .nat b => some (.boolean (a == b))
  | .conjunction, .boolean a, .boolean b => some (.boolean (a && b))
  | _, _, _ => none

/-- All String labels, including true/false, are excluded from Boolean operations. -/
theorem conjunction_labels_refused (left right : String) :
    primitiveResult .conjunction (.label left) (.label right) = none := rfl

theorem conjunction_boolean_exact (left right : Bool) :
    primitiveResult .conjunction (.boolean left) (.boolean right) =
      some (.boolean (left && right)) := rfl

theorem equality_boolean_exact (left right : Nat) :
    primitiveResult .equal (.nat left) (.nat right) = some (.boolean (left == right)) := rfl

inductive Step : Term → Term → Prop where
  | beta (body argument : Term) : Step (.app (.lam body) argument) (instantiate body argument)
  | application {function next : Term} (argument : Term) :
      Step function next → Step (.app function argument) (.app next argument)
  | mix (lower upper : Term) : Step (.mix lower upper) (mixBody lower upper)
  | fix (spec inherited : Term) :
      Step (.fix spec inherited) (.app (.app spec (.fix spec inherited)) inherited)
  | applySpecification (metadata extension argument : Term) :
      Step (.app (.specification metadata extension) argument) (.app extension argument)
  | reflectPrototype (spec target : Term) : Step (.reflect (.prototype spec target)) spec
  | metadataSpecification (metadata extension : Term) : Step (.metadata (.specification metadata extension)) metadata
  | projectPrototype (spec target : Term) : Step (.project (.prototype spec target)) target
  | reflectStep {term next : Term} : Step term next → Step (.reflect term) (.reflect next)
  | metadataStep {term next : Term} : Step term next → Step (.metadata term) (.metadata next)
  | projectStep {term next : Term} : Step term next → Step (.project term) (.project next)
  | target {target next : Term} (name : String) :
      Step target next → Step (.get target name) (.get next name)
  | field (fields : List (String × Term)) (name : String) (body : Term) :
      fields.find? (fun field => field.1 == name) = some (name,body) →
      Step (.get (.record fields) name) body
  | extendTarget {inherited next : Term} (fields : List (String × Term)) :
      Step inherited next → Step (.extend inherited fields) (.extend next fields)
  | extendRecord (inherited fields : List (String × Term)) :
      Step (.extend (.record inherited) fields) (.record (extendFields inherited fields))
  | binaryLeft {left next : Term} (primitive : Primitive) (right : Term) :
      Step left next → Step (.binary primitive left right) (.binary primitive next right)
  | binaryRight {right next : Term} (primitive : Primitive) (left : Term) :
      Value left → Step right next → Step (.binary primitive left right) (.binary primitive left next)
  | primitive (primitive : Primitive) (left right result : Term) :
      Value left → Value right → primitiveResult primitive left right = some result →
      Step (.binary primitive left right) result
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
inductive PositiveSteps : Term → Term → Prop where
  | begin {initial middle result : Term} : Step initial middle → Steps middle result → PositiveSteps initial result

/- This contract rules out an always-stuttering evaluator. Shared heap updates
may correspond to several reference reductions; cyclic heaps require a graph
logical relation, not naive finite-tree unfolding. A concrete implementation
must inhabit all fields before any adequacy claim is made. -/
/-- Ground observations only: closure/record contextual approximation needs a
separate relation and is not syntactic equality of residual lambda bodies. -/
inductive Observation where
  | natural (value : Nat)
  | boolean (value : Bool)
  | label (value : String)
  deriving Repr, DecidableEq
inductive Observes : Term → Observation → Prop where
  | natural (value : Nat) : Observes (.nat value) (.natural value)
  | boolean (value : Bool) : Observes (.boolean value) (.boolean value)
  | label (value : String) : Observes (.label value) (.label value)

inductive Transition (State : Type) where
  | advanced (next : State)
  | finished (result : Observation)
  | suspended (retained : State)
  | refused (diagnostic : String)

inductive MachineSteps {State : Type} (step : State → Transition State) : State → State → Prop where
  | refl (state : State) : MachineSteps step state state
  | next {initial middle result : State} : step initial = .advanced middle →
      MachineSteps step middle result → MachineSteps step initial result

/-- Supported is fixed by the intended source edition/domain, not chosen by an
implementation to make initialization/completeness vacuous. Administrative
progress applies only to running transitions. Final values and capacity
suspension have separate observations. Completeness is an explicit obligation
for the supported adequately provisioned domain; no instance is claimed here. -/
structure Representation (State : Type) (Supported : Term → Prop) where
  represents : State → Term → Prop
  start : Term → Option State
  initializesSupported : ∀ source, Supported source → ∃ state, start source = some state
  initialized : ∀ source state, start source = some state → represents state source
  step : State → Transition State
  administrativeRank : State → Nat
  simulation : ∀ state successor source, represents state source → step state = .advanced successor →
    ∃ next, represents successor next ∧
      ((next = source ∧ administrativeRank successor < administrativeRank state) ∨
        PositiveSteps source next)
  valueAdequacy : ∀ state source result, represents state source → step state = .finished result →
    ∃ value, Steps source value ∧ Value value ∧ Observes value result
  suspensionExact : ∀ state retained, step state = .suspended retained → retained = state
  evaluationComplete : ∀ source value result, Supported source → Evaluates source value → Observes value result →
    ∃ initial final, start source = some initial ∧ MachineSteps step initial final ∧
      step final = .finished result

/-- Generic Fix returns the target, never implicitly wraps it in a prototype.
Prototype conflation is an explicit library knot whose spec can be inspected
without demanding the recursive target. `self` here is the whole prototype. -/
def instantiatePrototype (spec seed : Term) : Term :=
  .fix (.lam (.lam (.prototype (spec.rename (fun n => n + 2))
    (.app (.app (spec.rename (fun n => n + 2)) (.bound 1)) (.bound 0))))) seed

theorem prototype_metadata_unforced (spec divergent : Term) :
    Step (.reflect (.prototype spec divergent)) spec := .reflectPrototype _ _

theorem specification_metadata_unforced (metadata divergent : Term) :
    Step (.metadata (.specification metadata divergent)) metadata := .metadataSpecification _ _

theorem lazy_fixed_function :
    Evaluates (.fix (.lam (.lam (.lam (.bound 0)))) (.nat 7)) (.lam (.bound 0)) := by
  constructor
  · refine .next (.fix _ _) ?_
    have first : Step
        (.app (.app (.lam (.lam (.lam (.bound 0))))
          (.fix (.lam (.lam (.lam (.bound 0)))) (.nat 7))) (.nat 7))
        (.app (.lam (.lam (.bound 0))) (.nat 7)) := by
      simpa [instantiate, Term.substitute, liftSubstitution, Term.rename, liftRename] using
        (Step.application (.nat 7) (Step.beta (.lam (.lam (.bound 0)))
          (.fix (.lam (.lam (.lam (.bound 0)))) (.nat 7))))
    have second : Step (.app (.lam (.lam (.bound 0))) (.nat 7)) (.lam (.bound 0)) := by
      simpa [instantiate, Term.substitute, liftSubstitution, Term.rename, liftRename] using
        (Step.beta (.lam (.bound 0)) (.nat 7))
    exact .next first (.next second (.refl _))
  · exact .function _

end Minidregg.Theory.ObjectiveBendOpenRecursion
