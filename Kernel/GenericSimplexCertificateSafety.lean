import Kernel.GeneralSimplexReachability
import Mathlib.Data.List.Infix

namespace Minidregg.Kernel.GenericSimplexCertificateSafety
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GenericSimplexQuorum
open Minidregg.Kernel.GeneralSimplexReachability
set_option autoImplicit false

/-- Transferable certificates attest actual durable COMMIT sends, NOT local
commit outputs. Byzantine signers have no protocol-behavior premise. Native
signature/export attribution must construct this relation for the exact context. -/
def AttributedCommitSends (tr : Trace) (roster faulty : Finset Nat) (f view : Nat)
    (block : Block) : Prop :=
  ∃ signers : Finset Nat, signers ⊆ roster ∧ 2 * f + 1 ≤ signers.card ∧
    ∀ party ∈ signers, party ∉ faulty → ∃ time, Sent tr time party view .commit (some block)

theorem certificate_honest_send {tr : Trace} {roster faulty : Finset Nat}
    {f view : Nat} {block : Block} (faultBound : faulty.card ≤ f)
    (cert : AttributedCommitSends tr roster faulty f view block) :
    ∃ party, party ∉ faulty ∧ ∃ time, Sent tr time party view .commit (some block) := by
  obtain ⟨signers, _, count, exports⟩ := cert
  have existsHonest : ∃ p ∈ signers, p ∉ faulty := by
    by_contra missing
    have included : signers ⊆ faulty := by
      intro p hp
      by_contra honest
      exact missing ⟨p, hp, honest⟩
    have bound := Finset.card_le_card included
    omega
  obtain ⟨p, hp, honest⟩ := existsHonest
  exact ⟨p, honest, exports p hp honest⟩

theorem certificate_vote_core {tr : Trace} {roster faulty : Finset Nat}
    {f view : Nat} {block : Block} (rules : LocalFaithful tr roster faulty f)
    (faultBound : faulty.card ≤ f)
    (cert : AttributedCommitSends tr roster faulty f view block) :
    ∃ time, Support tr roster time view .vote (some block) (2 * f + 1) := by
  obtain ⟨p, honest, time, sent⟩ := certificate_honest_send faultBound cert
  exact ⟨time, rules.commitSend time p view block honest sent⟩

theorem certificate_safe_origin {tr : Trace} {roster faulty : Finset Nat}
    {f view : Nat} {block : Block} (rules : LocalFaithful tr roster faulty f)
    (faultBound : faulty.card ≤ f)
    (cert : AttributedCommitSends tr roster faulty f view block) :
    ∃ time party, party ∉ faulty ∧ SafeAt tr time party view block := by
  obtain ⟨time, votes⟩ := certificate_vote_core rules faultBound cert
  obtain ⟨p, _, honest, vt, _, sent⟩ := support_honest faultBound (by omega) votes
  obtain ⟨st, _, q, hq, safe⟩ := honest_vote_has_safe_origin rules faultBound vt p view block honest sent
  exact ⟨st, q, hq, safe⟩

theorem certificate_positive {tr : Trace} {roster faulty : Finset Nat}
    {f view : Nat} {block : Block} (rules : LocalFaithful tr roster faulty f)
    (faultBound : faulty.card ≤ f)
    (cert : AttributedCommitSends tr roster faulty f view block) : 0 < view := by
  obtain ⟨_, _, _, _, previous, before, _, _⟩ := certificate_safe_origin rules faultBound cert
  omega

theorem certificate_candidate_same {tr : Trace} {roster faulty : Finset Nat}
    {f view time : Nat} {block : Block} {arg : Argument}
    (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (cert : AttributedCommitSends tr roster faulty f view block)
    (candidates : Support tr roster time view .candidate arg (2 * f + 1)) :
    arg = some block := by
  obtain ⟨signers, sm, sc, exports⟩ := cert
  obtain ⟨senders, tm, tc, sends⟩ := candidates
  obtain ⟨p, ps, pt, honest⟩ := honest_intersection roster faulty signers senders f
    size faultBound sm tm sc tc
  obtain ⟨ct, committed⟩ := exports p ps honest
  obtain ⟨st, _, candidate⟩ := sends p pt
  exact rules.commitCandidateLock ct st p view block arg honest committed candidate

theorem certificate_ready_same {tr : Trace} {roster faulty : Finset Nat}
    {f view time : Nat} {block : Block} {arg : Argument}
    (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (cert : AttributedCommitSends tr roster faulty f view block)
    (readies : Support tr roster time view .ready arg (2 * f + 1)) : arg = some block := by
  obtain ⟨p, _, honest, st, _, sent⟩ := support_honest faultBound (by omega) readies
  obtain ⟨ct, _, candidates⟩ := ready_has_candidate_core rules faultBound st p view arg honest sent
  exact certificate_candidate_same rules size faultBound cert candidates

theorem certificate_known_same {tr : Trace} {roster faulty : Finset Nat}
    {f view : Nat} {block other : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (cert : AttributedCommitSends tr roster faulty f view block)
    (known : KnownValue tr faulty view other) : other = block := by
  obtain ⟨time, votes⟩ := certificate_vote_core rules faultBound cert
  rcases known with ⟨zero, _⟩ | ⟨t, p, honest, prepared | committed⟩
  · have positive := certificate_positive rules faultBound cert
    omega
  · rcases rules.prepareOutput t p view other honest prepared with ov | ready | commits
    · exact (vote_cores_unique rules size faultBound votes ov).symm
    · exact Option.some.inj (certificate_ready_same rules size faultBound cert ready)
    · obtain ⟨_, _, ov⟩ := commit_core_has_vote_core rules faultBound commits
      exact (vote_cores_unique rules size faultBound votes ov).symm
  · obtain ⟨_, _, ov⟩ := commit_core_has_vote_core rules faultBound
      (rules.commitOutput t p view other honest committed)
    exact (vote_cores_unique rules size faultBound votes ov).symm

theorem certificates_same_view {tr : Trace} {roster faulty : Finset Nat}
    {f view : Nat} {left right : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (a : AttributedCommitSends tr roster faulty f view left)
    (b : AttributedCommitSends tr roster faulty f view right) : left = right := by
  obtain ⟨_, av⟩ := certificate_vote_core rules faultBound a
  obtain ⟨_, bv⟩ := certificate_vote_core rules faultBound b
  exact vote_cores_unique rules size faultBound av bv

theorem certificate_not_disabled {tr : Trace} {roster faulty : Finset Nat}
    {f view time party : Nat} {block : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (cert : AttributedCommitSends tr roster faulty f view block)
    (honest : party ∉ faulty) (disabled : tr time = .disable party view) : False := by
  have bad := certificate_ready_same rules size faultBound cert
    (rules.disableOutput time party view honest disabled)
  cases bad

def EvidenceValue (tr : Trace) (roster faulty : Finset Nat) (f view : Nat)
    (block : Block) : Prop :=
  KnownValue tr faulty view block ∨ AttributedCommitSends tr roster faulty f view block

theorem evidence_parent {tr : Trace} {roster faulty : Finset Nat}
    {f view : Nat} {block : Block} (rules : LocalFaithful tr roster faulty f)
    (faultBound : faulty.card ≤ f) (positive : 0 < view)
    (known : EvidenceValue tr roster faulty f view block) :
    ∃ previous < view, KnownValue tr faulty previous block.dropLast ∧
      ∀ skipped, previous < skipped → skipped < view →
        ∃ time party, party ∉ faulty ∧ tr time = .disable party skipped := by
  rcases known with known | cert
  · exact known_parent rules faultBound positive known
  · obtain ⟨time, party, honest, _, previous, before, parent, skipped⟩ :=
      certificate_safe_origin rules faultBound cert
    refine ⟨previous, before, ?_, ?_⟩
    · rcases parent with genesis | ⟨pt, _, prepared⟩
      · exact Or.inl genesis
      · exact Or.inr ⟨pt, party, honest, Or.inl prepared⟩
    · intro v lo hi
      obtain ⟨dt, _, disabled⟩ := skipped v lo hi
      exact ⟨dt, party, honest, disabled⟩

theorem certificate_ancestor_of_later {tr : Trace} {roster faulty : Finset Nat} {f : Nat}
    (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f) (view : Nat) :
    ∀ previous block ancestor, EvidenceValue tr roster faulty f view block →
      AttributedCommitSends tr roster faulty f previous ancestor → previous ≤ view →
      ancestor.IsPrefix block := by
  induction view using Nat.strong_induction_on with
  | h view ih =>
    intro previous block ancestor known cert order
    by_cases same : previous = view
    · subst previous
      have eq : block = ancestor := by
        rcases known with known | other
        · exact certificate_known_same rules size faultBound cert known
        · exact certificates_same_view rules size faultBound other cert
      subst block
      exact List.prefix_refl ancestor
    · have before : previous < view := by omega
      obtain ⟨pv, pbefore, parent, skipped⟩ := evidence_parent rules faultBound (by omega) known
      have lower : previous ≤ pv := by
        by_contra bad
        obtain ⟨t, p, honest, disabled⟩ := skipped previous (by omega) before
        exact certificate_not_disabled rules size faultBound cert honest disabled
      exact (ih pv pbefore previous block.dropLast ancestor (Or.inl parent) cert lower).trans
        (List.dropLast_prefix block)

theorem attributed_commit_sends_prefix_consistent {tr : Trace} {roster faulty : Finset Nat}
    {f v w : Nat} {left right : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (a : AttributedCommitSends tr roster faulty f v left)
    (b : AttributedCommitSends tr roster faulty f w right) :
    left.IsPrefix right ∨ right.IsPrefix left := by
  rcases Nat.le_total v w with order | order
  · exact Or.inl (certificate_ancestor_of_later rules size faultBound w v right left (Or.inr b) a order)
  · exact Or.inr (certificate_ancestor_of_later rules size faultBound v w left right (Or.inr a) b order)

/-- A descendant certificate covers every application sourcePrefix. No new signature
or certificate for that truncated sourcePrefix is constructed. -/
abbrev sourceHistory := Minidregg.Kernel.GenericSimplex.applicationHistory

theorem sourceHistory_preserves_prefix {a b : Block} (h : a.IsPrefix b) :
    (sourceHistory a).IsPrefix (sourceHistory b) := List.IsPrefix.filter _ h

theorem certified_source_histories_compatible {tr : Trace} {roster faulty : Finset Nat}
    {f v w : Nat} {left right : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (a : AttributedCommitSends tr roster faulty f v left)
    (b : AttributedCommitSends tr roster faulty f w right) :
    (sourceHistory left).IsPrefix (sourceHistory right) ∨
      (sourceHistory right).IsPrefix (sourceHistory left) :=
  (attributed_commit_sends_prefix_consistent rules size faultBound a b).imp
    sourceHistory_preserves_prefix sourceHistory_preserves_prefix

/-- Equal-length next prefixes of one history contain the same next record. -/
theorem same_history_next {sourcePrefix history : Block} {left right : Bytes}
    (a : (sourcePrefix ++ [left]).IsPrefix history)
    (b : (sourcePrefix ++ [right]).IsPrefix history) : left = right := by
  have between : (sourcePrefix ++ [left]).IsPrefix (sourcePrefix ++ [right]) :=
    List.prefix_of_prefix_length_le a b (by simp)
  have equal := between.eq_of_length (by simp)
  have tails := List.append_cancel_left equal
  simpa using tails

theorem compatible_histories_next {sourcePrefix a b : Block} {left right : Bytes}
    (compatible : a.IsPrefix b ∨ b.IsPrefix a)
    (leftCovered : (sourcePrefix ++ [left]).IsPrefix a)
    (rightCovered : (sourcePrefix ++ [right]).IsPrefix b) : left = right := by
  rcases compatible with before | after
  · exact same_history_next (leftCovered.trans before) rightCovered
  · exact same_history_next leftCovered (rightCovered.trans after)

/-- Consumer contract: full descendant certificates remain unchanged, while the
receiver applies exactly one covered record at its durable source index. -/
theorem certified_next_record_unique {tr : Trace} {roster faulty : Finset Nat}
    {f v w : Nat} {a b sourcePrefix : Block} {left right : Bytes}
    (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (certA : AttributedCommitSends tr roster faulty f v a)
    (certB : AttributedCommitSends tr roster faulty f w b)
    (coveredA : (sourcePrefix ++ [left]).IsPrefix (sourceHistory a))
    (coveredB : (sourcePrefix ++ [right]).IsPrefix (sourceHistory b)) : left = right :=
  compatible_histories_next
    (certified_source_histories_compatible rules size faultBound certA certB) coveredA coveredB

theorem covered_next_at_exact_index {sourcePrefix history : Block} {record : Bytes}
    (covered : (sourcePrefix ++ [record]).IsPrefix history) :
    history[sourcePrefix.length]? = some record := by
  obtain ⟨suffix, equality⟩ := covered
  rw [← equality]
  simp [List.append_assoc, List.getElem?_append]

#assert_axioms certified_next_record_unique
#assert_axioms covered_next_at_exact_index

#assert_axioms certificate_positive
#assert_axioms certificate_known_same
#assert_axioms certificate_not_disabled
#assert_axioms certificate_ancestor_of_later
#assert_axioms attributed_commit_sends_prefix_consistent
#assert_axioms certified_source_histories_compatible
end Minidregg.Kernel.GenericSimplexCertificateSafety
