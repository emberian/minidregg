/- Independent, context/target-parametric modular-extension meaning. This is neither
selector resolution nor an authorization model. Inherited and provided target types may differ. A target may be a number,
function, document, record, or another specification. Partial specifications
retain their requirements and laws before any fixed point is available.
The implementation must separately represent this meaning in executable code. -/
/- FixedPoint below is an algebraic equation only. It does not choose the least or
computational fixed point or imply operational convergence. Behavioral law
retention is an optional compatible-interface policy, not all ModExt semantics. -/
namespace Minidregg.Theory.ObjectiveBendExtensions
set_option autoImplicit false

/-- OPEN modular extensions may strengthen/change their inherited target.
Context-dependent target families retain self-sensitive typing. Homogeneous
endomorphisms below are only the closed special case. -/
abbrev OpenExtension (C : Type) (V W : C → Type) := (context : C) → V context → W context

def composeOpen {C : Type} {U V W : C → Type}
    (earlier : OpenExtension C U V) (later : OpenExtension C V W) : OpenExtension C U W :=
  fun context inherited => later context (earlier context inherited)

def OpenFixedPoint {C : Type} {U : C → Type}
    (extension : OpenExtension C U (fun _ => C)) (self : C) (inherited : U self) : Prop :=
  extension self inherited = self

/-- A genuine changing-target witness: Unit→List Nat→Nat under final context
Nat. This cannot be expressed as a homogeneous Nat endomorphism composition. -/
theorem heterogeneous_fixed_point :
    OpenFixedPoint (composeOpen
      (fun (self : Nat) (_ : Unit) => [self])
      (fun (_ : Nat) (inherited : List Nat) => inherited.length)) 1 () := rfl

abbrev Extension (A : Type) := A → A → A

/-- Bind the SAME final self at every extension; super is the entire inherited
partial target, not merely a method-table cursor. Later extensions act last. -/
def mix {A : Type} (extensions : List (Extension A)) (self inherited : A) : A :=
  extensions.foldl (fun prior extension => extension self prior) inherited

def FixedPoint {A : Type} (extensions : List (Extension A)) (inherited self : A) : Prop :=
  mix extensions self inherited = self

/-- Replacement discards super; wrapping retains it as an explicit argument. -/
def replacement {A : Type} (body : A → A) : Extension A := fun self _ => body self
def wrapping {A : Type} (body : A → A → A) : Extension A := body

structure Specification (A : Type) where
  extensions : List (Extension A)
  /-- Predicates may depend on the complete final target. -/
  requirements : List (A → Prop)
  /-- An override must re-establish every retained behavioral law. These laws
  grant no permission to perform a persistent effect. -/
  laws : List (A → Prop)

def Specification.compose {A : Type} (first second : Specification A) : Specification A :=
  ⟨first.extensions ++ second.extensions,
    first.requirements ++ second.requirements, first.laws ++ second.laws⟩

def Specification.Closed {A : Type} (spec : Specification A) (inherited self : A) : Prop :=
  FixedPoint spec.extensions inherited self ∧
  (∀ requirement ∈ spec.requirements, requirement self) ∧
  (∀ law ∈ spec.laws, law self)

/-- An ordinary immutable specification transformation; no closure/publication
or current-world authority is inferred merely by constructing the result. -/
def Specification.require {A : Type} (spec : Specification A) (requirement : A → Prop) : Specification A :=
  { spec with requirements := spec.requirements ++ [requirement] }
def Specification.enforce {A : Type} (spec : Specification A) (law : A → Prop) : Specification A :=
  { spec with laws := spec.laws ++ [law] }

theorem mix_append {A : Type} (first second : List (Extension A)) (self inherited : A) :
    mix (first ++ second) self inherited = mix second self (mix first self inherited) := by
  exact List.foldl_append

theorem mix_identity {A : Type} (self inherited : A) : mix [] self inherited = inherited := rfl

theorem composition_associative {A : Type} (a b c : Specification A) :
    (a.compose b).compose c = a.compose (b.compose c) := by
  cases a; cases b; cases c
  simp [Specification.compose, List.append_assoc]

/-- Law retention has teeth: later replacement cannot erase an earlier law. -/
theorem composed_law_retained {A : Type} (first second : Specification A)
    (inherited self : A) (closed : (first.compose second).Closed inherited self)
    (law : A → Prop) (member : law ∈ first.laws) : law self :=
  closed.2.2 law (List.mem_append_left _ member)

/-- Composition is deliberately noncommutative, already for a non-record target. -/
theorem replacing_then_wrapping :
    mix [replacement (fun (_ : Nat) => 0), wrapping (fun _ super => super + 1)] 99 7 = 1 := rfl
theorem wrapping_then_replacing :
    mix [wrapping (fun (_ : Nat) super => super + 1), replacement (fun _ => 0)] 99 7 = 0 := rfl

/-- This is an inhabited non-record fixed point, independent of any linker. -/
theorem scalar_fixed_point :
    FixedPoint [replacement (fun (_ : Nat) => 0), wrapping (fun _ super => super + 1)] 7 1 := rfl

/-- Unrestricted fix is partial: an extension need not have a fixed point. A
runtime budget/refusal must not be presented as a proof of its totality. -/
theorem no_successor_fixed_point (inherited self : Nat) :
    ¬ FixedPoint [replacement (fun final => final + 1)] inherited self := by
  simp [FixedPoint, mix, replacement]

end Minidregg.Theory.ObjectiveBendExtensions
