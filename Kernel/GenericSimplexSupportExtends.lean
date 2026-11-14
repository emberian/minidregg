import Kernel.GenericSimplexObservationSafety
import Kernel.GenericSimplexGlobalSupport

/-! What a correct member supports above a committed view strictly extends the commit.

Two facts the running replica (`GenericSimplexRelative`) rests on, first on the abstract
trace model (`LocalFaithful`), then on the specification's reachable networks.

* `support_extends_commit`, `reachable_support_extends`: a VOTE, CANDIDATE, READY or COMMIT
  that a correct member sends for a block in a view above a committed view is for a block
  that strictly extends the committed one. So a receiver that has committed `c` reads the
  block the sender meant from the payloads above `c`, and a replica that moves its origin
  to `c` loses nothing a correct member sent. PROPOSE is not covered and need not be: no
  obligation of `LocalFaithful` reads a proposal.
* `reachable_counted_extends`, `conflicting_count_small`: a block that does not strictly
  extend the commit is counted for at most `faults` members in any view above it, below
  every threshold a rule reads (`faults + 1`, `2 * faults + 1`, `quorum`). The rules of a
  correct replica are therefore insensitive to those messages. -/
namespace Minidregg.Kernel.GenericSimplexSupportExtends
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplexGlobalSupport
open Minidregg.Kernel.GenericSimplexEngineSafety
open Minidregg.Kernel.GenericSimplexObservationSafety
set_option autoImplicit false

/-- `c` is a strict prefix of `x`. -/
def StrictlyExtends (c x : Block) : Prop := c <+: x ∧ c.length < x.length

/-- Behind every support message of a correct member is a correct member's VOTE for the
same block in the same view, no later. -/
theorem support_has_honest_vote {tr : Trace} {roster faulty : Finset Nat} {f t p v : Nat}
    {kind : Kind} {x : Block} (rules : LocalFaithful tr roster faulty f)
    (faultBound : faulty.card ≤ f) (hp : p ∉ faulty) (support : kind ≠ .propose)
    (sent : Sent tr t p v kind (some x)) :
    ∃ q, q ∉ faulty ∧ ∃ s ≤ t, Sent tr s q v .vote (some x) := by
  have fromCandidate : ∀ u r, r ∉ faulty → Sent tr u r v .candidate (some x) →
      ∃ q, q ∉ faulty ∧ ∃ s ≤ u, Sent tr s q v .vote (some x) := by
    intro u r hr candidate
    obtain ⟨q, _, hq, s, before, vote⟩ :=
      support_honest faultBound (Nat.le_refl (f + 1)) (rules.candidateSend u r v x hr candidate)
    exact ⟨q, hq, s, by omega, vote⟩
  cases kind with
  | propose => exact absurd rfl support
  | vote => exact ⟨p, hp, t, Nat.le_refl t, sent⟩
  | commit =>
    obtain ⟨q, _, hq, s, before, vote⟩ :=
      support_honest faultBound (by omega) (rules.commitSend t p v x hp sent)
    exact ⟨q, hq, s, by omega, vote⟩
  | candidate => exact fromCandidate t p hp sent
  | ready =>
    obtain ⟨core, coreLe, candidates⟩ := ready_has_candidate_core rules faultBound t p v (some x) hp sent
    obtain ⟨r, _, hr, u, before, candidate⟩ := support_honest faultBound (by omega) candidates
    obtain ⟨q, hq, s, sLe, vote⟩ := fromCandidate u r hr candidate
    exact ⟨q, hq, s, by omega, vote⟩

/-- A correct member's VOTE above a committed view is for a block whose parent already
extends the commit. -/
theorem vote_extends_commit {tr : Trace} {roster faulty : Finset Nat} {f s q w v : Nat}
    {c x : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (commit : CommittedAt tr faulty w c) (above : w < v) (hq : q ∉ faulty)
    (vote : Sent tr s q v .vote (some x)) : StrictlyExtends c x := by
  obtain ⟨origin, _, r, hr, nonempty, previous, before, parent, skipped⟩ :=
    honest_vote_has_safe_origin rules faultBound s q v x hq vote
  have notBelow : w ≤ previous := by
    by_contra below
    obtain ⟨e, _, disabled⟩ := skipped w (by omega) above
    exact committed_not_disabled rules size faultBound commit hr disabled
  have known : KnownValue tr faulty previous x.dropLast := by
    rcases parent with genesis | ⟨e, _, prepared⟩
    · exact Or.inl genesis
    · exact Or.inr ⟨e, r, hr, Or.inl prepared⟩
  have ancestor := committed_ancestor_of_later rules size faultBound previous w x.dropLast c
    known commit notBelow
  have longer : x.dropLast.length < x.length := by
    rw [List.length_dropLast]
    have := List.length_pos_iff.mpr nonempty
    omega
  exact ⟨ancestor.trans (List.dropLast_prefix x), by have := ancestor.length_le; omega⟩

/-- **Support above a commit extends it** (abstract model). -/
theorem support_extends_commit {tr : Trace} {roster faulty : Finset Nat} {f t p w v : Nat}
    {kind : Kind} {c x : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (commit : CommittedAt tr faulty w c) (above : w < v) (hp : p ∉ faulty)
    (support : kind ≠ .propose) (sent : Sent tr t p v kind (some x)) : StrictlyExtends c x := by
  obtain ⟨q, hq, s, _, vote⟩ := support_has_honest_vote rules faultBound hp support sent
  exact vote_extends_commit rules size faultBound commit above hq vote

/-- **Support above a commit extends it** (the specification's reachable networks): if a
correct replica has committed `c` in view `w`, every VOTE, CANDIDATE, READY and COMMIT a
correct member has sent for a block in a view above `w` is for a strict extension of `c`. -/
theorem reachable_support_extends {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net)
    (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    {p q w v : Nat} {kind : Kind} {tip x : Block}
    (qm : q < c.parties) (qh : q ∉ faulty)
    (committed : (viewAt (net.localState q) w).committed = some tip) (above : w < v)
    (ph : p ∉ faulty) (support : kind ≠ .propose)
    (sent : (.send ⟨p, v, kind, some x⟩ : Minidregg.Kernel.GenericSimplex.AuditEvent) ∈ net.audit) :
    StrictlyExtends tip x := by
  have refinement := actual_audit_refinement reachable size
  obtain ⟨index, atIndex⟩ := List.mem_iff_getElem?.mp sent
  exact support_extends_commit refinement.faithful (by simpa using size) faultBound
    (refinement.commits q w tip qm qh committed) above ph support
    (t := index) (by simp only [Sent, auditTrace, atIndex, Option.getD_some])

/-- **What a rule can count above a commit extends it**: `faults + 1` members counted for a
block in a view above a committed view include a correct one, so the block strictly extends
the commit. -/
theorem reachable_counted_extends {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net)
    (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    {p q w v : Nat} {kind : Kind} {tip x : Block}
    (pm : p < c.parties) (ph : p ∉ faulty) (qm : q < c.parties) (qh : q ∉ faulty)
    (committed : (viewAt (net.localState q) w).committed = some tip) (above : w < v)
    (support : kind ≠ .propose)
    (counted : c.faults + 1 ≤ count (viewAt (net.localState p) v) kind (some x)) :
    StrictlyExtends tip x := by
  have refinement := actual_audit_refinement reachable size
  obtain ⟨r, _, hr, s, _, sent⟩ := support_honest faultBound (Nat.le_refl _)
    (actual_count_support_now reachable p v pm ph kind (some x) (c.faults + 1) counted)
  exact support_extends_commit refinement.faithful (by simpa using size) faultBound
    (refinement.commits q w tip qm qh committed) above hr support sent

/-- **Rules are insensitive to conflicting messages**: a block that does not strictly
extend a commit is counted for at most `faults` members in a view above it. Every
threshold of `valueRules` and `argumentRules` is at least `faults + 1`. -/
theorem conflicting_count_small {c : Config} {faulty : Finset Nat}
    {checked : Network → Nat → Block → Prop} {time : Nat} {net : Network}
    (reachable : Reachable c faulty checked time net)
    (size : c.parties = 3 * c.faults + 1) (faultBound : faulty.card ≤ c.faults)
    {p q w v : Nat} {kind : Kind} {tip x : Block}
    (pm : p < c.parties) (ph : p ∉ faulty) (qm : q < c.parties) (qh : q ∉ faulty)
    (committed : (viewAt (net.localState q) w).committed = some tip) (above : w < v)
    (support : kind ≠ .propose) (conflict : ¬ StrictlyExtends tip x) :
    count (viewAt (net.localState p) v) kind (some x) ≤ c.faults := by
  by_contra large
  exact conflict (reachable_counted_extends reachable size faultBound pm ph qm qh committed above
    support (by omega))

/-- The thresholds the rules read are all above `faults`. -/
theorem thresholds_above_faults (c : Config) (size : c.parties = 3 * c.faults + 1) :
    c.faults + 1 ≤ c.quorum ∧ c.faults + 1 ≤ 2 * c.faults + 1 := by
  unfold Config.quorum
  omega

end Minidregg.Kernel.GenericSimplexSupportExtends
