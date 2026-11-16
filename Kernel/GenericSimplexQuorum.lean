module

public import Mathlib.Data.Finset.Card
public import Theory.AssertAxioms

@[expose] public section

namespace Minidregg.Kernel.GenericSimplexQuorum
set_option autoImplicit false
/-- Any roster size: an `a`-set and a `b`-set of roster members with
`a + b ≥ n + f + 1` share a member outside any `f`-bounded faulty set. -/
theorem honest_intersection_of_overlap (roster faulty left right : Finset Nat) (f a b : Nat)
    (overlap : roster.card + f + 1 ≤ a + b) (faultBound : faulty.card ≤ f)
    (leftMembers : left ⊆ roster) (rightMembers : right ⊆ roster)
    (leftQuorum : a ≤ left.card) (rightQuorum : b ≤ right.card) :
    ∃ member, member ∈ left ∧ member ∈ right ∧ member ∉ faulty := by
  by_contra missing
  have shared : left ∩ right ⊆ faulty := by
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
  have h₁ := Finset.card_le_card shared
  have h₂ := Finset.card_le_card union
  have h₃ := Finset.card_union_add_card_inter left right
  omega

/-- The legacy `n = 3f + 1` committee (the smallest one `Config.wellFormed` admits). This supplies the honest
intersection used by COMMIT-vs-CANDIDATE exclusion and exported local-commit
certificates. It does not replace the distributed protocol refinement proof. -/
theorem honest_intersection (roster faulty left right : Finset Nat) (f : Nat)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (leftMembers : left ⊆ roster) (rightMembers : right ⊆ roster)
    (leftQuorum : 2 * f + 1 ≤ left.card) (rightQuorum : 2 * f + 1 ≤ right.card) :
    ∃ member, member ∈ left ∧ member ∈ right ∧ member ∉ faulty :=
  honest_intersection_of_overlap roster faulty left right f (2 * f + 1) (2 * f + 1)
    (by omega) faultBound leftMembers rightMembers leftQuorum rightQuorum

/-- Threshold profile of a roster of `n` parties with at most `f` faulty, for any
`n` (not only `n = 3f+1`): `q` is the VOTE/COMMIT quorum, `c` the CANDIDATE count
that sends a core READY, and `r` the READY count that clears a view (prepares or
disables). Each field is exactly one safety use: two `q`-sets share an honest
member; a `q`-set and a `c`-set share an honest member; a `q`-, `c`- or `r`-set
holds an honest member. Safety only: liveness needs `q, c, r ≤ n - f` too, and
READY totality needs `2f + 1 ≤ r`; no field here states either. -/
structure Thresholds (n f q c r : Nat) : Prop where
  quorumOverlap : n + f + 1 ≤ q + q
  candidateOverlap : n + f + 1 ≤ q + c
  quorumHonest : f + 1 ≤ q
  candidateHonest : f + 1 ≤ c
  readyHonest : f + 1 ≤ r

/-- The kernel's own guards for every admitted roster `n ≥ 3f + 1`: VOTE/COMMIT
at `n - f`, CANDIDATE→READY and READY→clear at `2f + 1` (the clockdag
mesh-simplex `Config::quorum` and its unchanged `2f+1` guards). -/
theorem thresholds_standard {n f : Nat} (admitted : 3 * f + 1 ≤ n) :
    Thresholds n f (n - f) (2 * f + 1) (2 * f + 1) :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- The legacy `n = 3f + 1` profile, where `n - f = 2f + 1`. -/
theorem thresholds_legacy {n f : Nat} (size : n = 3 * f + 1) :
    Thresholds n f (2 * f + 1) (2 * f + 1) (2 * f + 1) :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- The smallest safe VOTE/COMMIT quorum `⌈(n + f + 1) / 2⌉` (n = 6, f = 1 needs 4;
n = 600, f = 199 needs 400). It is safe ONLY with the CANDIDATE→READY guard raised
from `2f + 1` to `n + f + 1 - q = ⌊(n + f + 1) / 2⌋`; READY→clear may stay `2f + 1`. -/
theorem thresholds_small_quorum {n f : Nat} (admitted : 3 * f + 1 ≤ n) :
    Thresholds n f ((n + f + 2) / 2) (n + f + 1 - (n + f + 2) / 2) (2 * f + 1) :=
  ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- With `n > 3f + 1` the unchanged `2f + 1` VOTE quorum is NOT safe: two such
sets may share only faulty members. Witness: `n = 5`, `f = 1`, the sets
`{0,1,2}` and `{2,3,4}` meet only in the faulty `{2}`. -/
theorem two_f_plus_one_quorum_unsafe_above_legacy :
    ∃ roster faulty left right : Finset Nat, roster.card = 5 ∧ faulty.card ≤ 1 ∧
      left ⊆ roster ∧ right ⊆ roster ∧ 2 * 1 + 1 ≤ left.card ∧ 2 * 1 + 1 ≤ right.card ∧
      left ∩ right ⊆ faulty :=
  ⟨{0,1,2,3,4}, {2}, {0,1,2}, {2,3,4}, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

#assert_axioms honest_intersection_of_overlap
#assert_axioms honest_intersection
#assert_axioms thresholds_standard
#assert_axioms thresholds_legacy
#assert_axioms thresholds_small_quorum
#assert_axioms two_f_plus_one_quorum_unsafe_above_legacy
end Minidregg.Kernel.GenericSimplexQuorum
