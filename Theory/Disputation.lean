/-
# Theory.Disputation — constructive adjudication (the witness-fibre reflector).

Port of breadstuffs `metatheory/Metatheory/Disputation.lean` onto Mini's
`Theory/EpistemicConsensus.lean` (itself the port of that file's base).
Candidate-independent: it imports only `Theory`.

The structure, as Bread's four-lens review left it (the `Predicate ⊣ Witness`
"agreement and adjudication are two adjoints" thesis was refuted 4/4 and is not
formalized):

* knowledge is a graded family of per-agent modalities; **agreement is a limit** —
  the meet `DistKnows` of `Theory/EpistemicConsensus.lean`;
* **adjudication is a separately built reflector `R_r` indexed by the evidence
  regime `r`.** Its good behaviour is exactly what fails in the ballot regime
  (Arrow / List–Pettit).

This module is the witness-regime reflector `R_witness`: the verdict is read off a
discharging WITNESS, never off a vote, so it is Byzantine-majority-proof on the
certifiable domain. It escapes the aggregation impossibility by restricting the
domain to claims that admit a certificate.

## Changes from the ancestor (each deliberate)

* Mini's `EpistemicConsensus` dropped the reflexivity premise
  `∀ i, Honest i → Indist i actual actual` (an instance of the frame's
  `indist_refl` field) and renamed `honest_dist_knowledge_iff_holds` to
  `holds_of_honest_distKnows_verified`; the two proofs below call the Mini names and
  no longer pass that premise. Statements are unchanged.
* `Frame.verified` is `verified` at the module namespace in Mini.
-/
import Theory.EpistemicConsensus

namespace Minidregg.Theory.Disputation

open Minidregg.Theory Minidregg.Theory.EpistemicConsensus

universe u v
variable {Ω : Type u} {ι : Type v} (F : Frame Ω ι)
variable {P W : Type u} [Verifiable P W]

/-- A **dispute**: two parties press competing claims; the adjudicator must return a
verdict. (The binary shape is the smallest non-trivial profile.) -/
structure Dispute (P : Type u) where
  /-- the claim pressed by the proponent. -/
  pro : Claim P
  /-- the claim pressed by the opponent. -/
  con : Claim P

/-- **Constructive adjudication — the witness-fibre reflector `R_witness`.** A claim is
**upheld** iff it constructively `Holds`: a discharging witness exists. The verdict is
read off the witness, never off a vote. -/
def upheld (X : Claim P) : Prop := Holds (W := W) X

/-- **`upheld_iff_witness` — the verdict IS the witness.** -/
theorem upheld_iff_witness (X : Claim P) :
    upheld (W := W) X ↔ ∃ w : W, Discharged (P := P) (W := W) X.stmt w :=
  holds_iff_discharged_witness X

/-- **`verdict_is_honest_distributed_knowledge` — witness-determined, not
vote-determined.** `upheld X` iff, for some offered witness, the honest agents have
distributed knowledge of its discharge. -/
theorem verdict_is_honest_distributed_knowledge (X : Claim P) :
    upheld (W := W) X ↔
      ∃ w₀ : W, F.DistKnows F.Honest (verified (Ω := Ω) X w₀) F.actual := by
  constructor
  · rintro ⟨w₀, hd⟩
    exact ⟨w₀, F.honest_distributed_knows_discharged X w₀ hd⟩
  · rintro ⟨w₀, hk⟩
    exact F.holds_of_honest_distKnows_verified X w₀ hk

/-- **`byzantine_majority_cannot_uphold` — the aggregation-impossibility escape.** If
no witness exists, no offered witness lets the honest group distributedly know the
claim: a Byzantine majority cannot vote it into the verdict. -/
theorem byzantine_majority_cannot_uphold (X : Claim P) (hno : ¬ upheld (W := W) X)
    (w₀ : W) :
    ¬ F.DistKnows F.Honest (verified (Ω := Ω) X w₀) F.actual :=
  F.no_dist_knowledge_of_unrealizable X w₀ hno

/-! ## Axiom pins — each equals the ancestor's `#print axioms` (none). -/

/-- info: 'Minidregg.Theory.Disputation.upheld_iff_witness' does not depend on any axioms -/
#guard_msgs in #print axioms upheld_iff_witness

/-- info: 'Minidregg.Theory.Disputation.verdict_is_honest_distributed_knowledge' does not depend on any axioms -/
#guard_msgs in #print axioms verdict_is_honest_distributed_knowledge

/-- info: 'Minidregg.Theory.Disputation.byzantine_majority_cannot_uphold' does not depend on any axioms -/
#guard_msgs in #print axioms byzantine_majority_cannot_uphold

end Minidregg.Theory.Disputation
