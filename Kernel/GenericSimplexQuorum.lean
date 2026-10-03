import Mathlib.Data.Finset.Card
import Theory.AssertAxioms
namespace Minidregg.Kernel.GenericSimplexQuorum
set_option autoImplicit false
/-- Same concrete committee/model as Config.wellFormed. This supplies the honest
intersection used by COMMIT-vs-CANDIDATE exclusion and exported local-commit
certificates. It does not replace the distributed protocol refinement proof. -/
theorem honest_intersection (roster faulty left right : Finset Nat) (f : Nat)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (leftMembers : left ⊆ roster) (rightMembers : right ⊆ roster)
    (leftQuorum : 2 * f + 1 ≤ left.card) (rightQuorum : 2 * f + 1 ≤ right.card) :
    ∃ member, member ∈ left ∧ member ∈ right ∧ member ∉ faulty := by
  by_contra missing
  have overlap : left ∩ right ⊆ faulty := by
    intro member both
    have l := (Finset.mem_inter.mp both).1
    have r := (Finset.mem_inter.mp both).2
    by_contra honest
    exact missing ⟨member,l,r,honest⟩
  have union : left ∪ right ⊆ roster := by
    intro member one
    rcases Finset.mem_union.mp one with l | r
    · exact leftMembers l
    · exact rightMembers r
  have h₁ := Finset.card_le_card overlap
  have h₂ := Finset.card_le_card union
  have h₃ := Finset.card_union_add_card_inter left right
  omega
#assert_axioms honest_intersection
end Minidregg.Kernel.GenericSimplexQuorum
