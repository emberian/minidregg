module

public import Kernel.GenericSimplex
public import Kernel.GenericSimplexQuorum
public import Mathlib.Data.List.Basic

@[expose] public section

/- Global safety of causally justified 1/3-VA events. LocalFaithful contains ONLY
local send guards, receive provenance and output causes. It does not assume VA
agreement or prefix consistency. The executable start/step extraction is owned
by GenericSimplexLocal and is a required, presently separate refinement join.
No theorem here alone certifies a native VerifiedCommit. -/
namespace Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexQuorum
set_option autoImplicit false

/-- The audit events are emitted by the ACTUAL executable r2 core. -/
abbrev AuditEvent := Minidregg.Kernel.GenericSimplex.AuditEvent
abbrev Trace := Nat → AuditEvent

def Sent (tr : Trace) (time party view : Nat) (kind : Kind) (arg : Argument) : Prop :=
  tr time = .send ⟨party, view, kind, arg⟩
def Support (tr : Trace) (roster : Finset Nat) (time view : Nat)
    (kind : Kind) (arg : Argument) (threshold : Nat) : Prop :=
  ∃ voters : Finset Nat, voters ⊆ roster ∧ threshold ≤ voters.card ∧
    ∀ party ∈ voters, ∃ sentTime < time, Sent tr sentTime party view kind arg

def PreparedBefore (tr : Trace) (time party view : Nat) (block : Block) : Prop :=
  (view = 0 ∧ block = []) ∨ ∃ earlier < time, tr earlier = .prepare party view block

def SafeAt (tr : Trace) (time party view : Nat) (block : Block) : Prop :=
  block ≠ [] ∧ ∃ previous < view,
    PreparedBefore tr time party previous block.dropLast ∧
    ∀ skipped, previous < skipped → skipped < view →
      ∃ earlier < time, tr earlier = .disable party skipped

/-- EXACT local extraction obligations; none is a consensus assumption.
The trace orders each internal broadcast/output, including multiple pump actions.
Quorum support comes from authenticated prior sends, not asserted signatures.
Thresholds are explicit for any roster size: `q` is the VOTE/COMMIT quorum
(`Config.quorum = n - f`), `c` the CANDIDATE count for a core READY and `r` the
READY count that clears a view. `LocalFaithful` is the legacy `n = 3f + 1`
instance, where all three equal `2f + 1`. -/
structure LocalFaithfulAt (tr : Trace) (roster faulty : Finset Nat) (f q c r : Nat) : Prop where
  voteOnce : ∀ t u p v x y, p ∉ faulty →
    Sent tr t p v .vote (some x) → Sent tr u p v .vote (some y) → x = y
  commitSend : ∀ t p v x, p ∉ faulty → Sent tr t p v .commit (some x) →
    Support tr roster t v .vote (some x) q
  commitCandidateLock : ∀ t u p v x a, p ∉ faulty →
    Sent tr t p v .commit (some x) → Sent tr u p v .candidate a → a = some x
  candidateSend : ∀ t p v x, p ∉ faulty → Sent tr t p v .candidate (some x) →
    Support tr roster t v .vote (some x) (f + 1)
  readySend : ∀ t p v a, p ∉ faulty → Sent tr t p v .ready a →
    Support tr roster t v .candidate a c ∨
    Support tr roster t v .ready a (f + 1)
  prepareOutput : ∀ t p v x, p ∉ faulty → tr t = .prepare p v x →
    Support tr roster t v .vote (some x) q ∨
    Support tr roster t v .ready (some x) r ∨
    Support tr roster t v .commit (some x) q
  disableOutput : ∀ t p v, p ∉ faulty → tr t = .disable p v →
    Support tr roster t v .ready none r
  commitOutput : ∀ t p v x, p ∉ faulty → tr t = .commit p v x →
    Support tr roster t v .commit (some x) q
  voteOrigin : ∀ t p v x, p ∉ faulty → Sent tr t p v .vote (some x) →
    SafeAt tr t p v x ∨ ∃ earlier < t, tr earlier = .prepare p v x
  preparePositive : ∀ t p v x, p ∉ faulty → tr t = .prepare p v x → 0 < v
  commitPositive : ∀ t p v x, p ∉ faulty → tr t = .commit p v x → 0 < v
  disablePositive : ∀ t p v, p ∉ faulty → tr t = .disable p v → 0 < v

/-- The legacy fixed `n = 3f + 1` committee: every quorum guard is `2f + 1`. -/
abbrev LocalFaithful (tr : Trace) (roster faulty : Finset Nat) (f : Nat) : Prop :=
  LocalFaithfulAt tr roster faulty f (2 * f + 1) (2 * f + 1) (2 * f + 1)

/-- The executable profile `(q, 2f + 1, 2f + 1)` is the legacy one where `q = 2f + 1`
(the VOTE/COMMIT quorum `n - f` at `n = 3f + 1`). -/
theorem LocalFaithfulAt.toLegacy {tr : Trace} {roster faulty : Finset Nat} {f q : Nat}
    (rules : LocalFaithfulAt tr roster faulty f q (2 * f + 1) (2 * f + 1))
    (quorum : q = 2 * f + 1) : LocalFaithful tr roster faulty f := by
  subst quorum
  exact rules

theorem support_honest {tr : Trace} {roster faulty : Finset Nat} {f t v q : Nat}
    {kind : Kind} {arg : Argument} (faultBound : faulty.card ≤ f)
    (enough : f + 1 ≤ q) (support : Support tr roster t v kind arg q) :
    ∃ p, p ∈ roster ∧ p ∉ faulty ∧ ∃ s < t, Sent tr s p v kind arg := by
  obtain ⟨voters, members, size, sends⟩ := support
  have existsHonest : ∃ p ∈ voters, p ∉ faulty := by
    by_contra missing
    have contained : voters ⊆ faulty := by
      intro p hp
      by_contra honest
      exact missing ⟨p, hp, honest⟩
    have bound := Finset.card_le_card contained
    omega
  obtain ⟨p, hp, honest⟩ := existsHonest
  exact ⟨p, members hp, honest, sends p hp⟩

theorem support_intersection_at {tr : Trace} {roster faulty : Finset Nat}
    {f t u v a' b' : Nat} {k l : Kind} {a b : Argument}
    (overlap : roster.card + f + 1 ≤ a' + b') (faultBound : faulty.card ≤ f)
    (left : Support tr roster t v k a a')
    (right : Support tr roster u v l b b') :
    ∃ p, p ∉ faulty ∧ (∃ s < t, Sent tr s p v k a) ∧
      (∃ s < u, Sent tr s p v l b) := by
  obtain ⟨ls, lm, lc, le⟩ := left
  obtain ⟨rs, rm, rc, re⟩ := right
  obtain ⟨p, lp, rp, honest⟩ := honest_intersection_of_overlap roster faulty ls rs f a' b'
    overlap faultBound lm rm lc rc
  exact ⟨p, honest, le p lp, re p rp⟩

theorem support_intersection {tr : Trace} {roster faulty : Finset Nat}
    {f t u v : Nat} {k l : Kind} {a b : Argument}
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (left : Support tr roster t v k a (2 * f + 1))
    (right : Support tr roster u v l b (2 * f + 1)) :
    ∃ p, p ∉ faulty ∧ (∃ s < t, Sent tr s p v k a) ∧
      (∃ s < u, Sent tr s p v l b) :=
  support_intersection_at (by omega) faultBound left right

/-- READY relays cannot manufacture a root: strictly earlier honest READY
support forces well-founded descent to an actual candidate quorum. -/
theorem ready_has_candidate_core_at {tr : Trace} {roster faulty : Finset Nat} {f q c r : Nat}
    (rules : LocalFaithfulAt tr roster faulty f q c r) (faultBound : faulty.card ≤ f)
    (t : Nat) : ∀ p v a, p ∉ faulty → Sent tr t p v .ready a →
      ∃ core ≤ t, Support tr roster core v .candidate a c := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro p v a honest sent
    rcases rules.readySend t p v a honest sent with core | relay
    · exact ⟨t, Nat.le_refl t, core⟩
    · obtain ⟨p', _, honest', earlier, lt, sent'⟩ :=
        support_honest faultBound (Nat.le_refl (f + 1)) relay
      obtain ⟨core, before, support⟩ := ih earlier lt p' v a honest' sent'
      exact ⟨core, by omega, support⟩

theorem ready_has_candidate_core {tr : Trace} {roster faulty : Finset Nat} {f : Nat}
    (rules : LocalFaithful tr roster faulty f) (faultBound : faulty.card ≤ f)
    (t : Nat) : ∀ p v a, p ∉ faulty → Sent tr t p v .ready a →
      ∃ core ≤ t, Support tr roster core v .candidate a (2 * f + 1) :=
  ready_has_candidate_core_at rules faultBound t

theorem vote_cores_unique_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r t u v : Nat} {x y : Block} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (th : Thresholds roster.card f q c r) (faultBound : faulty.card ≤ f)
    (left : Support tr roster t v .vote (some x) q)
    (right : Support tr roster u v .vote (some y) q) : x = y := by
  obtain ⟨p, honest, ⟨ts, _, sx⟩, ⟨us, _, sy⟩⟩ :=
    support_intersection_at th.quorumOverlap faultBound left right
  exact rules.voteOnce ts us p v x y honest sx sy

theorem vote_cores_unique {tr : Trace} {roster faulty : Finset Nat}
    {f t u v : Nat} {x y : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (left : Support tr roster t v .vote (some x) (2 * f + 1))
    (right : Support tr roster u v .vote (some y) (2 * f + 1)) : x = y :=
  vote_cores_unique_at rules (thresholds_legacy size) faultBound left right

theorem commit_core_has_vote_core_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r t v : Nat} {x : Block} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (quorumHonest : f + 1 ≤ q) (faultBound : faulty.card ≤ f)
    (commitCore : Support tr roster t v .commit (some x) q) :
    ∃ earlier < t, Support tr roster earlier v .vote (some x) q := by
  obtain ⟨p, _, honest, earlier, lt, sent⟩ := support_honest faultBound quorumHonest commitCore
  exact ⟨earlier, lt, rules.commitSend earlier p v x honest sent⟩

theorem commit_core_has_vote_core {tr : Trace} {roster faulty : Finset Nat}
    {f t v : Nat} {x : Block} (rules : LocalFaithful tr roster faulty f)
    (faultBound : faulty.card ≤ f)
    (commitCore : Support tr roster t v .commit (some x) (2 * f + 1)) :
    ∃ earlier < t, Support tr roster earlier v .vote (some x) (2 * f + 1) :=
  commit_core_has_vote_core_at rules (by omega) faultBound commitCore

theorem commit_candidate_core_same_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r t u v : Nat} {x : Block} {a : Argument}
    (rules : LocalFaithfulAt tr roster faulty f q c r)
    (th : Thresholds roster.card f q c r) (faultBound : faulty.card ≤ f)
    (commitCore : Support tr roster t v .commit (some x) q)
    (candidateCore : Support tr roster u v .candidate a c) : a = some x := by
  obtain ⟨p, honest, ⟨ts, _, sx⟩, ⟨us, _, sa⟩⟩ :=
    support_intersection_at th.candidateOverlap faultBound commitCore candidateCore
  exact rules.commitCandidateLock ts us p v x a honest sx sa

theorem commit_candidate_core_same {tr : Trace} {roster faulty : Finset Nat}
    {f t u v : Nat} {x : Block} {a : Argument} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (commitCore : Support tr roster t v .commit (some x) (2 * f + 1))
    (candidateCore : Support tr roster u v .candidate a (2 * f + 1)) : a = some x :=
  commit_candidate_core_same_at rules (thresholds_legacy size) faultBound commitCore candidateCore

theorem commit_ready_core_same_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r t u v : Nat} {x : Block} {a : Argument}
    (rules : LocalFaithfulAt tr roster faulty f q c r)
    (th : Thresholds roster.card f q c r) (faultBound : faulty.card ≤ f)
    (commitCore : Support tr roster t v .commit (some x) q)
    (readyCore : Support tr roster u v .ready a r) : a = some x := by
  obtain ⟨p, _, honest, earlier, _, sent⟩ := support_honest faultBound th.readyHonest readyCore
  obtain ⟨core, _, candidates⟩ :=
    ready_has_candidate_core_at rules faultBound earlier p v a honest sent
  exact commit_candidate_core_same_at rules th faultBound commitCore candidates

theorem commit_ready_core_same {tr : Trace} {roster faulty : Finset Nat}
    {f t u v : Nat} {x : Block} {a : Argument} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (commitCore : Support tr roster t v .commit (some x) (2 * f + 1))
    (readyCore : Support tr roster u v .ready a (2 * f + 1)) : a = some x :=
  commit_ready_core_same_at rules (thresholds_legacy size) faultBound commitCore readyCore

/-- Cross-party, cross-time VA consistency; NOT just two simultaneous tallies. -/
theorem committed_excludes_other_prepare_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r t u p p' v : Nat} {x y : Block} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (th : Thresholds roster.card f q c r) (faultBound : faulty.card ≤ f)
    (hp : p ∉ faulty) (hq : p' ∉ faulty)
    (committed : tr t = .commit p v x) (prepared : tr u = .prepare p' v y) : y = x := by
  have cc := rules.commitOutput t p v x hp committed
  obtain ⟨tc, _, vc⟩ := commit_core_has_vote_core_at rules th.quorumHonest faultBound cc
  rcases rules.prepareOutput u p' v y hq prepared with votes | readies | commits
  · exact (vote_cores_unique_at rules th faultBound vc votes).symm
  · exact Option.some.inj (commit_ready_core_same_at rules th faultBound cc readies)
  · obtain ⟨ty, _, vy⟩ := commit_core_has_vote_core_at rules th.quorumHonest faultBound commits
    exact (vote_cores_unique_at rules th faultBound vc vy).symm

theorem committed_excludes_other_prepare {tr : Trace} {roster faulty : Finset Nat}
    {f t u p q v : Nat} {x y : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (hp : p ∉ faulty) (hq : q ∉ faulty)
    (committed : tr t = .commit p v x) (prepared : tr u = .prepare q v y) : y = x :=
  committed_excludes_other_prepare_at rules (thresholds_legacy size) faultBound hp hq
    committed prepared

theorem committed_excludes_disable_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r t u p p' v : Nat} {x : Block} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (th : Thresholds roster.card f q c r) (faultBound : faulty.card ≤ f)
    (hp : p ∉ faulty) (hq : p' ∉ faulty)
    (committed : tr t = .commit p v x) (disabled : tr u = .disable p' v) : False := by
  have impossible := commit_ready_core_same_at rules th faultBound
    (rules.commitOutput t p v x hp committed) (rules.disableOutput u p' v hq disabled)
  cases impossible

theorem committed_excludes_disable {tr : Trace} {roster faulty : Finset Nat}
    {f t u p q v : Nat} {x : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (hp : p ∉ faulty) (hq : q ∉ faulty)
    (committed : tr t = .commit p v x) (disabled : tr u = .disable q v) : False :=
  committed_excludes_disable_at rules (thresholds_legacy size) faultBound hp hq
    committed disabled

theorem committed_unique_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r t u p p' v : Nat} {x y : Block} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (th : Thresholds roster.card f q c r) (faultBound : faulty.card ≤ f)
    (hp : p ∉ faulty) (hq : p' ∉ faulty)
    (left : tr t = .commit p v x) (right : tr u = .commit p' v y) : x = y := by
  obtain ⟨tc, _, vc⟩ := commit_core_has_vote_core_at rules th.quorumHonest faultBound
    (rules.commitOutput t p v x hp left)
  obtain ⟨td, _, vd⟩ := commit_core_has_vote_core_at rules th.quorumHonest faultBound
    (rules.commitOutput u p' v y hq right)
  exact vote_cores_unique_at rules th faultBound vc vd

theorem committed_unique {tr : Trace} {roster faulty : Finset Nat}
    {f t u p q v : Nat} {x y : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (hp : p ∉ faulty) (hq : q ∉ faulty)
    (left : tr t = .commit p v x) (right : tr u = .commit q v y) : x = y :=
  committed_unique_at rules (thresholds_legacy size) faultBound hp hq left right

/-- Prepared output has an honest earlier vote even when reached through READY
amplification or doCommit's implicit preparation. -/
theorem prepared_has_honest_vote_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r t p v : Nat} {x : Block} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (quorumHonest : f + 1 ≤ q) (candidateHonest : f + 1 ≤ c) (readyHonest : f + 1 ≤ r)
    (faultBound : faulty.card ≤ f) (hp : p ∉ faulty)
    (prepared : tr t = .prepare p v x) :
    ∃ q', q' ∉ faulty ∧ ∃ earlier < t, Sent tr earlier q' v .vote (some x) := by
  rcases rules.prepareOutput t p v x hp prepared with votes | readies | commits
  · obtain ⟨w, _, hw, earlier, lt, sent⟩ := support_honest faultBound quorumHonest votes
    exact ⟨w, hw, earlier, lt, sent⟩
  · obtain ⟨w, _, hw, rt, rlt, rs⟩ := support_honest faultBound readyHonest readies
    obtain ⟨ct, cle, candidates⟩ :=
      ready_has_candidate_core_at rules faultBound rt w v (some x) hw rs
    obtain ⟨s, _, hs, st, slt, ss⟩ := support_honest faultBound candidateHonest candidates
    have votes := rules.candidateSend st s v x hs ss
    obtain ⟨w', _, hw', vt, vlt, vs⟩ := support_honest faultBound (Nat.le_refl (f + 1)) votes
    exact ⟨w', hw', vt, by omega, vs⟩
  · obtain ⟨ct, clt, votes⟩ := commit_core_has_vote_core_at rules quorumHonest faultBound commits
    obtain ⟨w, _, hw, vt, vlt, vs⟩ := support_honest faultBound quorumHonest votes
    exact ⟨w, hw, vt, by omega, vs⟩

theorem prepared_has_honest_vote {tr : Trace} {roster faulty : Finset Nat}
    {f t p v : Nat} {x : Block} (rules : LocalFaithful tr roster faulty f)
    (faultBound : faulty.card ≤ f) (hp : p ∉ faulty)
    (prepared : tr t = .prepare p v x) :
    ∃ q, q ∉ faulty ∧ ∃ earlier < t, Sent tr earlier q v .vote (some x) :=
  prepared_has_honest_vote_at rules (by omega) (by omega) (by omega) faultBound hp prepared

/-- Catch-up votes do not invent unsafe parents: following their earlier prepare
causes eventually reaches a proposal vote with an actual safe-parent witness. -/
theorem honest_vote_has_safe_origin_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r : Nat} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (quorumHonest : f + 1 ≤ q) (candidateHonest : f + 1 ≤ c) (readyHonest : f + 1 ≤ r)
    (faultBound : faulty.card ≤ f)
    (t : Nat) : ∀ p v x, p ∉ faulty → Sent tr t p v .vote (some x) →
      ∃ earlier ≤ t, ∃ q', q' ∉ faulty ∧ SafeAt tr earlier q' v x := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro p v x hp sent
    rcases rules.voteOrigin t p v x hp sent with safe | catchup
    · exact ⟨t, Nat.le_refl t, p, hp, safe⟩
    · obtain ⟨pt, plt, prepared⟩ := catchup
      obtain ⟨w, hw, vt, vlt, vote⟩ := prepared_has_honest_vote_at rules quorumHonest
        candidateHonest readyHonest faultBound hp prepared
      obtain ⟨st, sle, w', hw', safe⟩ := ih vt (by omega) w v x hw vote
      exact ⟨st, by omega, w', hw', safe⟩

theorem honest_vote_has_safe_origin {tr : Trace} {roster faulty : Finset Nat} {f : Nat}
    (rules : LocalFaithful tr roster faulty f) (faultBound : faulty.card ≤ f)
    (t : Nat) : ∀ p v x, p ∉ faulty → Sent tr t p v .vote (some x) →
      ∃ earlier ≤ t, ∃ q, q ∉ faulty ∧ SafeAt tr earlier q v x :=
  honest_vote_has_safe_origin_at rules (by omega) (by omega) (by omega) faultBound t

#assert_axioms LocalFaithfulAt.toLegacy
#assert_axioms support_honest
#assert_axioms ready_has_candidate_core
#assert_axioms committed_excludes_other_prepare
#assert_axioms committed_excludes_disable
#assert_axioms committed_unique
#assert_axioms prepared_has_honest_vote
#assert_axioms honest_vote_has_safe_origin
#assert_axioms support_intersection_at
#assert_axioms ready_has_candidate_core_at
#assert_axioms vote_cores_unique_at
#assert_axioms commit_core_has_vote_core_at
#assert_axioms commit_candidate_core_same_at
#assert_axioms commit_ready_core_same_at
#assert_axioms committed_excludes_other_prepare_at
#assert_axioms committed_excludes_disable_at
#assert_axioms committed_unique_at
#assert_axioms prepared_has_honest_vote_at
#assert_axioms honest_vote_has_safe_origin_at
end Minidregg.Kernel.GenericSimplexVAInvariant
