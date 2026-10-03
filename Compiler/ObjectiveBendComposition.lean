/- Objective Bend partial specifications. Behavior composition is elaboration
into the pinned BendTT core; it is independent of the governance/authority DAG.
This module has no object evaluator and does not admit unrestricted recursion.
-/
import Theory.BendTTSource
import Theory.AssertAxioms

namespace Minidregg.Compiler.ObjectiveBendComposition
open Minidregg.Theory.BendTT
set_option autoImplicit false

inductive Scope where
  | finalSelf
  | priorSuper
  deriving DecidableEq, Repr

/-- A method interface is an exact core type, rather than a numeric output slot. -/
structure Interface where
  selector : String
  type : Term
  deriving DecidableEq, Repr

structure Requirement where
  scope : Scope
  interface : Interface
  deriving DecidableEq, Repr

/-- Source identity and entry are retained through dispatch. Raw partial bodies
may contain unresolved method references; the composed Book must pass the real
Bend checker after elaboration. Persistent closure values are not stored here. -/
structure Provision where
  interface : Interface
  source : Nat
  entry : String
  body : Term
  captured : List Term
  deriving DecidableEq, Repr

structure Spec where
  id : Nat
  directParents : List Nat
  order : List Nat
  requirements : List Requirement
  provisions : List Provision
  deriving DecidableEq, Repr

/-- The provider is a layer index, not an authority or a reusable closure. -/
structure Selected where
  provider : Nat
  owner : Nat
  provision : Provision
  deriving DecidableEq, Repr

/-- Ordered inheritance is base to extension. A diamond occurs once. A lawful
order preserves the declared order of every parent's complete ancestor order;
different lawful orders can intentionally produce different behavior. -/
structure OrderCertificate (root : Spec) (layers : List Spec) : Type where
  unique : (layers.map Spec.id).Nodup
  rootLast : layers.getLast? = some root
  rootOrder : root.order = layers.map Spec.id
  parentsEarlier : ∀ (index : Fin layers.length) (parent : Nat),
    parent ∈ layers[index].directParents → parent ∈ (layers.take index.val).map Spec.id
  exactAncestors : ∀ layer ∈ layers, ∀ ancestor,
    ancestor ∈ layer.order ↔ ancestor = layer.id ∨
      ∃ parent ∈ layer.directParents, ∃ parentSpec ∈ layers,
        parentSpec.id = parent ∧ ancestor ∈ parentSpec.order
  inheritedOrder : ∀ layer ∈ layers, ∀ parentSpec ∈ layers,
    parentSpec.id ∈ layer.directParents → parentSpec.order.Sublist layer.order
  directOrder : ∀ layer ∈ layers, layer.directParents.Sublist layer.order
  layerOrder : ∀ layer ∈ layers, layer.order.Sublist (layers.map Spec.id)
  layerLast : ∀ layer ∈ layers, layer.order.getLast? = some layer.id

private def localSelect (spec : Spec) (interface : Interface) : Option Provision :=
  spec.provisions.find? (fun provision => provision.interface == interface)

/-- Rightmost matching provider wins. All requirements are resolved with exact
signature equality; an ambiguous local overload is rejected by `closed`. -/
def select (interface : Interface) : List Spec → Nat → Option Selected
  | [], _ => none
  | spec :: tail, index =>
      match select interface tail (index + 1) with
      | some selected => some selected
      | none => (localSelect spec interface).map (fun provision => ⟨index, spec.id, provision⟩)

theorem select_provider_bounded (interface : Interface) (layers : List Spec)
    (start : Nat) (selected : Selected)
    (found : select interface layers start = some selected) :
    start ≤ selected.provider ∧ selected.provider < start + layers.length := by
  induction layers generalizing start selected with
  | nil => simp [select] at found
  | cons spec tail inductionHypothesis =>
      cases tailFound : select interface tail (start + 1) with
      | some later =>
          simp only [select, tailFound, Option.some.injEq] at found
          subst selected
          have bound := inductionHypothesis (start + 1) later tailFound
          simp only [List.length_cons]
          omega
      | none =>
          simp only [select, tailFound] at found
          cases localFound : localSelect spec interface with
          | none => simp [localFound] at found
          | some provision =>
              simp [localFound] at found
              subst selected
              simp only [List.length_cons]
              constructor <;> omega

def resolve (layers : List Spec) (cursor : Nat) (requirement : Requirement) : Option Selected :=
  match requirement.scope with
  | .finalSelf => select requirement.interface layers 0
  | .priorSuper => select requirement.interface (layers.take cursor) 0

/-- Every occurrence sees the same composed final self. Super sees only the
strict predecessor prefix, including when an unrelated extension is appended. -/
theorem finalSelf_cursor_independent (layers : List Spec) (left right : Nat)
    (interface : Interface) :
    resolve layers left ⟨.finalSelf, interface⟩ =
      resolve layers right ⟨.finalSelf, interface⟩ := rfl

theorem priorSuper_is_prefix (layers : List Spec) (cursor : Nat) (interface : Interface) :
    resolve layers cursor ⟨.priorSuper, interface⟩ =
      select interface (layers.take cursor) 0 := rfl

theorem super_provider_strictly_earlier (layers : List Spec) (cursor : Nat)
    (interface : Interface) (selected : Selected)
    (found : resolve layers cursor ⟨.priorSuper, interface⟩ = some selected) :
    selected.provider < cursor := by
  have bounded := select_provider_bounded interface (layers.take cursor) 0 selected found
  have lengthBound := List.length_take_le cursor layers
  omega

/-- A closed composition checks each requirement where its spec occurs. A
partial spec can remain useful while open; only instance construction requires
closure. Signatures and captures are checked again in the composed core Book. -/
def compatible (layers : List Spec) : Bool :=
  let provisions := layers.flatMap Spec.provisions
  provisions.all fun left => provisions.all fun right =>
    left.interface.selector != right.interface.selector ||
      decide (left.interface.type = right.interface.type)

def capturedData (provision : Provision) : Prop :=
  ∀ term ∈ provision.captured, Minidregg.Theory.BendTT.Data term

def closed (layers : List Spec) : Bool :=
  compatible layers && (List.finRange layers.length).all fun index =>
    let spec := layers[index]
    decide ((spec.provisions.map (fun p => p.interface.selector)).Nodup) &&
    decide ((spec.requirements.map (fun r => (r.scope, r.interface.selector))).Nodup) &&
    spec.requirements.all (fun required => (resolve layers index.val required).isSome)

/-- A call request contains Data identity/cursor only. An actual affine closure
is instantiated for this demand by the Bend backend, never copied from a spec. -/
structure Call where
  finalSelf : Nat
  cursor : Nat
  requirement : Requirement
  deriving DecidableEq, Repr

structure ResolvedCall where
  finalSelf : Nat
  selected : Selected
  deriving DecidableEq, Repr

def dispatch (layers : List Spec) (call : Call) : Option ResolvedCall :=
  (resolve layers call.cursor call.requirement).map (fun selected => ⟨call.finalSelf, selected⟩)

theorem same_final_self (layers : List Spec) (call : Call) (result : ResolvedCall)
    (found : dispatch layers call = some result) : result.finalSelf = call.finalSelf := by
  unfold dispatch at found
  cases resolution : resolve layers call.cursor call.requirement <;> simp [resolution] at found
  subst result
  rfl

/-- Exact source attribution is carried with the selected implementation. -/
theorem dispatched_source (layers : List Spec) (call : Call) (result : ResolvedCall)
    (found : dispatch layers call = some result) :
    resolve layers call.cursor call.requirement = some result.selected := by
  unfold dispatch at found
  cases resolution : resolve layers call.cursor call.requirement <;> simp [resolution] at found
  subst result
  rfl

#assert_axioms select_provider_bounded
#assert_axioms super_provider_strictly_earlier
#assert_axioms finalSelf_cursor_independent
#assert_axioms priorSuper_is_prefix
#assert_axioms same_final_self
#assert_axioms dispatched_source
end Minidregg.Compiler.ObjectiveBendComposition
