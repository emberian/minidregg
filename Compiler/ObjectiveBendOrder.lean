/- Executable finite lawful-order validation for Objective Bend prototypes.
Authoring partial specs is independent from instance construction: the latter
requires complete exact ancestry and a lawful ordered composition certificate.
-/
import Compiler.ObjectiveBendComposition
import Theory.AssertAxioms

namespace Minidregg.Compiler.ObjectiveBendOrder
open ObjectiveBendComposition
set_option autoImplicit false

def ancestorPool (layers : List Spec) (layer : Spec) : List Nat :=
  layer.id :: (layers.filter (fun parent => decide (parent.id ∈ layer.directParents))).flatMap Spec.order

def SameMembers (left right : List Nat) : Prop :=
  (∀ member ∈ left, member ∈ right) ∧ (∀ member ∈ right, member ∈ left)

instance (left right : List Nat) : Decidable (SameMembers left right) := by
  unfold SameMembers
  infer_instance

theorem sameMembers_iff (left right : List Nat) (equal : SameMembers left right)
    (member : Nat) : member ∈ left ↔ member ∈ right :=
  ⟨equal.1 member, equal.2 member⟩

theorem ancestorPool_exact (layers : List Spec) (layer : Spec) (ancestor : Nat) :
    ancestor ∈ ancestorPool layers layer ↔ ancestor = layer.id ∨
      ∃ parent ∈ layer.directParents, ∃ parentSpec ∈ layers,
        parentSpec.id = parent ∧ ancestor ∈ parentSpec.order := by
  simp only [ancestorPool, List.mem_cons, List.mem_flatMap, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro (same | ⟨parentSpec, ⟨present, parent⟩, inherited⟩)
    · exact Or.inl same
    · exact Or.inr ⟨parentSpec.id, parent, parentSpec, present, rfl, inherited⟩
  · rintro (same | ⟨parent, direct, parentSpec, present, identity, inherited⟩)
    · exact Or.inl same
    · exact Or.inr ⟨parentSpec, ⟨present, by simpa [identity] using direct⟩, inherited⟩

/-- Every independent partial specification has a lawful singleton ancestry.
Requirements may remain open; this does not yet permit instance construction. -/
def singletonCertificate (spec : Spec) (noParents : spec.directParents = [])
    (ownOrder : spec.order = [spec.id]) : OrderCertificate spec [spec] where
  unique := by simp
  rootLast := rfl
  rootOrder := by simpa using ownOrder
  parentsEarlier := by
    intro index parent present
    have identity : ([spec] : List Spec)[index] = spec := by simp
    rw [identity, noParents] at present
    simp at present
  exactAncestors := by
    intro layer present ancestor
    have identity : layer = spec := by simpa using present
    subst layer
    simp [ownOrder, noParents]
  inheritedOrder := by
    intro layer present parentSpec parentPresent direct
    have identity : layer = spec := by simpa using present
    subst layer
    simp [noParents] at direct
  directOrder := by
    intro layer present
    have identity : layer = spec := by simpa using present
    subst layer
    simp [noParents]
  layerOrder := by
    intro layer present
    have identity : layer = spec := by simpa using present
    subst layer
    simp [ownOrder]
  layerLast := by
    intro layer present
    have identity : layer = spec := by simpa using present
    subst layer
    simp [ownOrder]

/-- This returns a proof-carrying certificate by deciding finite predicates on
actual source specs. It refuses missing parents, cycles/backward dependencies,
duplicate diamonds, extra/missing ancestry and incompatible parent precedence.
No unbounded Nat quantifier or trusted Boolean graph oracle is executed. -/
def check (root : Spec) (layers : List Spec) : Option (OrderCertificate root layers) :=
  letI earlierPred : DecidablePred (fun index : Fin layers.length =>
      ∀ parent ∈ layers[index].directParents, parent ∈ (layers.take index.val).map Spec.id) :=
    fun index => List.decidableBAll
      (fun parent => parent ∈ (layers.take index.val).map Spec.id) layers[index].directParents
  letI earlierDec : Decidable (∀ index ∈ List.finRange layers.length, ∀ parent ∈
      layers[index].directParents, parent ∈ (layers.take index.val).map Spec.id) :=
    List.decidableBAll _ (List.finRange layers.length)
  if unique : (layers.map Spec.id).Nodup then
    if last : layers.getLast? = some root then
      if rootOrder : root.order = layers.map Spec.id then
        match earlierDec with
        | .isFalse _ => none
        | .isTrue earlier =>
          if ancestors : ∀ layer ∈ layers, SameMembers layer.order (ancestorPool layers layer) then
            if inherited : ∀ layer ∈ layers, ∀ parentSpec ∈ layers,
                parentSpec.id ∈ layer.directParents → parentSpec.order.Sublist layer.order then
              if directOrder : ∀ layer ∈ layers, layer.directParents.Sublist layer.order then
                if layerOrder : ∀ layer ∈ layers, layer.order.Sublist (layers.map Spec.id) then
                  if layerLast : ∀ layer ∈ layers, layer.order.getLast? = some layer.id then
                    some {
                      unique := unique
                      rootLast := last
                      rootOrder := rootOrder
                      parentsEarlier := fun index => earlier index (List.mem_finRange index)
                      exactAncestors := by
                        intro layer present ancestor
                        exact (sameMembers_iff _ _ (ancestors layer present) ancestor).trans
                          (ancestorPool_exact layers layer ancestor)
                      inheritedOrder := inherited
                      directOrder := directOrder
                      layerOrder := layerOrder
                      layerLast := layerLast }
                  else none
                else none
              else none
            else none
          else none
      else none
    else none
  else none

theorem checked_exact_ancestry (root : Spec) (layers : List Spec)
    (certificate : OrderCertificate root layers) (layer : Spec) (present : layer ∈ layers)
    (ancestor : Nat) : ancestor ∈ layer.order ↔ ancestor = layer.id ∨
      ∃ parent ∈ layer.directParents, ∃ parentSpec ∈ layers,
        parentSpec.id = parent ∧ ancestor ∈ parentSpec.order :=
  certificate.exactAncestors layer present ancestor

#assert_axioms singletonCertificate
#assert_axioms sameMembers_iff
#assert_axioms ancestorPool_exact
#assert_axioms checked_exact_ancestry
end Minidregg.Compiler.ObjectiveBendOrder
