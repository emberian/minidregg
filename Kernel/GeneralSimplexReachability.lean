module

public import Kernel.GenericSimplexVAInvariant

@[expose] public section

namespace Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexVAInvariant
open Minidregg.Kernel.GenericSimplexQuorum
set_option autoImplicit false

/-- Includes genesis. Unlike a single-value prepare invariant, this permits
multiple prepared values in an uncommitted view, as 1/3-VA requires. -/
def KnownValue (tr : Trace) (faulty : Finset Nat) (view : Nat) (block : Block) : Prop :=
  (view = 0 ∧ block = []) ∨ ∃ time party, party ∉ faulty ∧
    (tr time = .prepare party view block ∨ tr time = .commit party view block)
def CommittedAt (tr : Trace) (faulty : Finset Nat) (view : Nat) (block : Block) : Prop :=
  (view = 0 ∧ block = []) ∨ ∃ time party, party ∉ faulty ∧ tr time = .commit party view block

theorem committed_known {tr : Trace} {faulty : Finset Nat} {v : Nat} {b : Block}
    (h : CommittedAt tr faulty v b) : KnownValue tr faulty v b := by
  rcases h with genesis | ⟨t, p, honest, committed⟩
  · exact Or.inl genesis
  · exact Or.inr ⟨t, p, honest, Or.inr committed⟩

theorem known_zero {tr : Trace} {roster faulty : Finset Nat} {f q c r : Nat} {b : Block}
    (rules : LocalFaithfulAt tr roster faulty f q c r) (known : KnownValue tr faulty 0 b) :
    b = [] := by
  rcases known with ⟨_, empty⟩ | ⟨t, p, honest, prepared | committed⟩
  · exact empty
  · have bad := rules.preparePositive t p 0 b honest prepared
    omega
  · have bad := rules.commitPositive t p 0 b honest committed
    omega

theorem known_eq_committed_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r v : Nat} {b d : Block} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (th : Thresholds roster.card f q c r) (faultBound : faulty.card ≤ f)
    (known : KnownValue tr faulty v b) (commit : CommittedAt tr faulty v d) : b = d := by
  rcases commit with ⟨zero, empty⟩ | ⟨t, p, hp, committed⟩
  · subst v
    exact (known_zero rules known).trans empty.symm
  · rcases known with ⟨zero, _⟩ | ⟨u, p', hq, prepared | otherCommit⟩
    · have pos := rules.commitPositive t p v d hp committed
      omega
    · exact committed_excludes_other_prepare_at rules th faultBound hp hq committed prepared
    · exact (committed_unique_at rules th faultBound hp hq committed otherCommit).symm

theorem known_eq_committed {tr : Trace} {roster faulty : Finset Nat}
    {f v : Nat} {b c : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (known : KnownValue tr faulty v b) (commit : CommittedAt tr faulty v c) : b = c :=
  known_eq_committed_at rules (thresholds_legacy size) faultBound known commit

theorem committed_not_disabled_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r v t p : Nat} {d : Block} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (th : Thresholds roster.card f q c r) (faultBound : faulty.card ≤ f)
    (commit : CommittedAt tr faulty v d) (hp : p ∉ faulty)
    (disabled : tr t = .disable p v) : False := by
  rcases commit with ⟨zero, _⟩ | ⟨u, p', hq, committed⟩
  · have pos := rules.disablePositive t p v hp disabled
    omega
  · exact committed_excludes_disable_at rules th faultBound hq hp committed disabled

theorem committed_not_disabled {tr : Trace} {roster faulty : Finset Nat}
    {f v t p : Nat} {c : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (commit : CommittedAt tr faulty v c) (hp : p ∉ faulty)
    (disabled : tr t = .disable p v) : False :=
  committed_not_disabled_at rules (thresholds_legacy size) faultBound commit hp disabled

/-- A real earlier safe vote supplies a prepared parent and every skipped-view
clear. This closes the catch-up-vote cycle through well-founded event causality. -/
theorem known_parent_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r v : Nat} {b : Block} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (quorumHonest : f + 1 ≤ q) (candidateHonest : f + 1 ≤ c) (readyHonest : f + 1 ≤ r)
    (faultBound : faulty.card ≤ f) (positive : 0 < v)
    (known : KnownValue tr faulty v b) :
    ∃ previous < v, KnownValue tr faulty previous b.dropLast ∧
      ∀ skipped, previous < skipped → skipped < v →
        ∃ t p, p ∉ faulty ∧ tr t = .disable p skipped := by
  rcases known with ⟨zero, _⟩ | ⟨t, p, hp, output⟩
  · omega
  · have voter : ∃ w, w ∉ faulty ∧ ∃ earlier < t, Sent tr earlier w v .vote (some b) := by
      rcases output with prepared | committed
      · exact prepared_has_honest_vote_at rules quorumHonest candidateHonest readyHonest
          faultBound hp prepared
      · have cc := rules.commitOutput t p v b hp committed
        obtain ⟨ct, clt, votes⟩ := commit_core_has_vote_core_at rules quorumHonest faultBound cc
        obtain ⟨w, _, hw, vt, vlt, sent⟩ := support_honest faultBound quorumHonest votes
        exact ⟨w, hw, vt, by omega, sent⟩
    obtain ⟨w, hw, vt, _, sent⟩ := voter
    obtain ⟨st, _, w', hw', _, previous, prevLt, parent, skipped⟩ :=
      honest_vote_has_safe_origin_at rules quorumHonest candidateHonest readyHonest
        faultBound vt w v b hw sent
    refine ⟨previous, prevLt, ?_, ?_⟩
    · rcases parent with genesis | ⟨pt, _, prepared⟩
      · exact Or.inl genesis
      · exact Or.inr ⟨pt, w', hw', Or.inl prepared⟩
    · intro u low high
      obtain ⟨dt, _, disabled⟩ := skipped u low high
      exact ⟨dt, w', hw', disabled⟩

theorem known_parent {tr : Trace} {roster faulty : Finset Nat}
    {f v : Nat} {b : Block} (rules : LocalFaithful tr roster faulty f)
    (faultBound : faulty.card ≤ f) (positive : 0 < v)
    (known : KnownValue tr faulty v b) :
    ∃ previous < v, KnownValue tr faulty previous b.dropLast ∧
      ∀ skipped, previous < skipped → skipped < v →
        ∃ t p, p ∉ faulty ∧ tr t = .disable p skipped :=
  known_parent_at rules (by omega) (by omega) (by omega) faultBound positive known

/-- Global outer-prefix theorem over the same executable-event audit obligations,
for any roster size whose thresholds satisfy `Thresholds`.
No assumption says that committed blocks are compatible. -/
theorem committed_ancestor_of_later_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r : Nat} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (th : Thresholds roster.card f q c r) (faultBound : faulty.card ≤ f)
    (v : Nat) : ∀ previous b d,
      KnownValue tr faulty v b → CommittedAt tr faulty previous d → previous ≤ v →
      d.IsPrefix b := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    intro previous b d known commit order
    by_cases same : previous = v
    · subst previous
      have eq := known_eq_committed_at rules th faultBound known commit
      subst b
      exact List.prefix_refl d
    · have before : previous < v := by omega
      obtain ⟨parentView, parentLt, parent, skipped⟩ :=
        known_parent_at rules th.quorumHonest th.candidateHonest th.readyHonest
          faultBound (by omega) known
      have lower : previous ≤ parentView := by
        by_contra bad
        obtain ⟨t, p, hp, disabled⟩ := skipped previous (by omega) before
        exact committed_not_disabled_at rules th faultBound commit hp disabled
      have ancestor := ih parentView parentLt previous b.dropLast d parent commit lower
      exact ancestor.trans (List.dropLast_prefix b)

/-- Global outer-prefix theorem over the same executable-event audit obligations.
No assumption says that committed blocks are compatible. -/
theorem committed_ancestor_of_later {tr : Trace} {roster faulty : Finset Nat} {f : Nat}
    (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (v : Nat) : ∀ previous b c,
      KnownValue tr faulty v b → CommittedAt tr faulty previous c → previous ≤ v →
      c.IsPrefix b :=
  committed_ancestor_of_later_at rules (thresholds_legacy size) faultBound v

/-- Committed-prefix safety for ANY roster size: `Thresholds` holds for the kernel's
own `n - f` / `2f + 1` guards whenever `3f + 1 ≤ n` (`thresholds_standard`). -/
theorem committed_prefix_consistency_at {tr : Trace} {roster faulty : Finset Nat}
    {f q c r v w : Nat} {b d : Block} (rules : LocalFaithfulAt tr roster faulty f q c r)
    (th : Thresholds roster.card f q c r) (faultBound : faulty.card ≤ f)
    (left : CommittedAt tr faulty v b) (right : CommittedAt tr faulty w d) :
    b.IsPrefix d ∨ d.IsPrefix b := by
  rcases Nat.le_total v w with order | order
  · exact Or.inl (committed_ancestor_of_later_at rules th faultBound w v d b
      (committed_known right) left order)
  · exact Or.inr (committed_ancestor_of_later_at rules th faultBound v w b d
      (committed_known left) right order)

/-- The kernel's own guards (`n - f` VOTE/COMMIT, `2f + 1` CANDIDATE/READY) are
safe at every admitted roster `n ≥ 3f + 1`, not only `n = 3f + 1`. -/
theorem committed_prefix_consistency_admitted {tr : Trace} {roster faulty : Finset Nat}
    {f v w : Nat} {b d : Block}
    (rules : LocalFaithfulAt tr roster faulty f (roster.card - f) (2 * f + 1) (2 * f + 1))
    (admitted : 3 * f + 1 ≤ roster.card) (faultBound : faulty.card ≤ f)
    (left : CommittedAt tr faulty v b) (right : CommittedAt tr faulty w d) :
    b.IsPrefix d ∨ d.IsPrefix b :=
  committed_prefix_consistency_at rules (thresholds_standard admitted) faultBound left right

theorem committed_prefix_consistency {tr : Trace} {roster faulty : Finset Nat}
    {f v w : Nat} {b c : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (left : CommittedAt tr faulty v b) (right : CommittedAt tr faulty w c) :
    b.IsPrefix c ∨ c.IsPrefix b :=
  committed_prefix_consistency_at rules (thresholds_legacy size) faultBound left right

/- Actual executable authenticated-event reachability. This deliberately uses
GenericSimplex.start/step rather than a second protocol. Authentication is an
explicit adversary premise; source checks are an independent current native
validity relation. The r2 core retains audit across drainOutbox. Journal compaction still needs
a history-preserving refinement before reuse. -/
structure Network where
  localState : Nat → State
  /-- Proof-side linearization of the actual retained local audit deltas. -/
  audit : List Minidregg.Kernel.GenericSimplex.AuditEvent

def initial (c : Config) (initialTime : Nat) : Network :=
  let states := fun party => start c party initialTime
  ⟨states, (List.range c.parties).flatMap (fun party => (states party).audit)⟩

def auditTrace (net : Network) : Trace := fun time => (net.audit[time]?).getD .idle

/-- Byzantine sends are unconstrained except for enrolled identity. Each delivered
Byzantine message is placed before its receive-side transitions. Honest sends
must already occur in retained sender history by authenticDelivery. -/
def byzantineInputAudit (faulty : Finset Nat) (input : Input) : List Minidregg.Kernel.GenericSimplex.AuditEvent :=
  match input with
  | .delivery m | .deliveryAt _ m => if m.sender ∈ faulty then [.send m] else []
  | .tick _ | .checked _ | .offer _ | .poll => []

def authenticDelivery (c : Config) (faulty : Finset Nat) (net : Network) (m : Message) : Prop :=
  m.sender < c.parties ∧ (m.sender ∈ faulty ∨ .send m ∈ (net.localState m.sender).audit)

def AllowedInput (c : Config) (faulty : Finset Nat)
    (sourceChecked : Network → Nat → Block → Prop) (net : Network) (receiver : Nat)
    (input : Input) : Prop :=
  receiver < c.parties ∧ receiver ∉ faulty ∧
  match input with
  | .delivery m | .deliveryAt _ m => authenticDelivery c faulty net m
  | .checked block => sourceChecked net receiver block
  | .tick _ | .offer _ | .poll => True

def advance (c : Config) (faulty : Finset Nat) (net : Network)
    (party : Nat) (input : Input) : Network :=
  let prior := net.localState party
  let next := step c prior input
  { localState := fun other => if other = party then next else net.localState other
    audit := net.audit ++ byzantineInputAudit faulty input ++ next.audit.drop prior.audit.length }

theorem advance_audit_prefix (c : Config) (faulty : Finset Nat) (net : Network)
    (party : Nat) (input : Input) : net.audit.IsPrefix (advance c faulty net party input).audit := by
  refine ⟨byzantineInputAudit faulty input ++
    (step c (net.localState party) input).audit.drop (net.localState party).audit.length, ?_⟩
  simp [advance, List.append_assoc]

inductive Reachable (c : Config) (faulty : Finset Nat)
    (sourceChecked : Network → Nat → Block → Prop) (initialTime : Nat) : Network → Prop where
  | initial : Reachable c faulty sourceChecked initialTime (initial c initialTime)
  | next {net : Network} (prior : Reachable c faulty sourceChecked initialTime net)
      (party : Nat) (input : Input)
      (allowed : AllowedInput c faulty sourceChecked net party input) :
      Reachable c faulty sourceChecked initialTime (advance c faulty net party input)

/-- The executable guards of an admitted configuration (`3f + 1 ≤ n`, `Config.wellFormed`)
satisfy `Thresholds`: VOTE/COMMIT at `Config.quorum = n - f`, CANDIDATE→READY and
READY→clear at `2f + 1`. -/
theorem config_thresholds {c : Config} (admitted : 3 * c.faults + 1 ≤ c.parties) :
    Thresholds (Finset.range c.parties).card c.faults c.quorum
      (2 * c.faults + 1) (2 * c.faults + 1) := by
  have card : (Finset.range c.parties).card = c.parties := by simp
  rw [card]
  exact thresholds_standard admitted

/-- At `n = 3f + 1` the widened admission computes the old one (`parties == 3 * faults + 1`),
so `start` and `step`, which read the configuration's size only through `wellFormed`,
`quorum` and the unchanged guards, behave exactly as before on every such roster. -/
theorem wellFormed_at_legacy (c : Config) (size : c.parties = 3 * c.faults + 1) :
    c.wellFormed = (c.parties == 3 * c.faults + 1 && c.timeout > 0 && c.pumpBudget > 0) := by
  rcases c with ⟨parties, faults, timeout, pumpBudget, backoffCap⟩
  dsimp only at size
  cases faults with
  | zero =>
    have hp : parties = 1 := by omega
    simp [Config.wellFormed, hp]
  | succ f =>
    have hpos : 0 < f + 1 := by omega
    simp [Config.wellFormed, hpos, size]

/-- At `n = 3f + 1` the executable VOTE/COMMIT quorum is the legacy `2f + 1`. -/
theorem config_quorum_legacy {c : Config} (size : c.parties = 3 * c.faults + 1) :
    c.quorum = 2 * c.faults + 1 := by
  unfold Config.quorum
  omega

/-- Executable observation refinement, constructed from actual Reachable by
GenericSimplexObservationSafety.actual_audit_refinement. Local fidelity is
proved from real start/step and retained audit causes, at the executable guards
(`c.quorum`, `2f + 1`, `2f + 1`) for any roster size; committed and delivered
observations are joined through the actual output-history invariant.
Cryptographic signature origin and liveness remain separate obligations. -/
structure AuditRefinement (c : Config) (faulty : Finset Nat) (net : Network) where
  faithful : LocalFaithfulAt (auditTrace net) (Finset.range c.parties) faulty c.faults
    c.quorum (2 * c.faults + 1) (2 * c.faults + 1)
  commits : ∀ party view block, party < c.parties → party ∉ faulty →
    (viewAt (net.localState party) view).committed = some block →
    CommittedAt (auditTrace net) faulty view block
  delivered : ∀ party block, party < c.parties → party ∉ faulty →
    block ∈ (net.localState party).delivered →
    ∃ view, CommittedAt (auditTrace net) faulty view block

/-- Conditional join target for source export. It is intentionally named as a
refinement consequence, never as an unconditional property of VerifiedCommit. -/
theorem refined_engine_commits_compatible {c : Config} {faulty : Finset Nat} {net : Network}
    (audit : AuditRefinement c faulty net) (admitted : 3 * c.faults + 1 ≤ c.parties)
    (faultBound : faulty.card ≤ c.faults) {p q v w : Nat} {b d : Block}
    (pm : p < c.parties) (qm : q < c.parties) (ph : p ∉ faulty) (qh : q ∉ faulty)
    (left : (viewAt (net.localState p) v).committed = some b)
    (right : (viewAt (net.localState q) w).committed = some d) :
    b.IsPrefix d ∨ d.IsPrefix b := by
  exact committed_prefix_consistency_at audit.faithful (config_thresholds admitted) faultBound
    (audit.commits p v b pm ph left) (audit.commits q w d qm qh right)

/-- Historical local-output attestation consequence; NOT the production portable
certificate: 1/3VA does not guarantee enough replicas reach doCommit. The repaired
COMMIT-send certificate is proved in GenericSimplexCertificateSafety.
Cryptographic/native boundary to be supplied by verified signature origin,
durable exporter replay and the executable audit refinement. Merely counting
signatures does not construct this fact. No consensus property is a field. -/
def LocalCommitOutputAttestations (tr : Trace) (roster faulty : Finset Nat) (f view : Nat)
    (block : Block) : Prop :=
  ∃ signers : Finset Nat, signers ⊆ roster ∧ 2 * f + 1 ≤ signers.card ∧
    ∀ party ∈ signers, party ∉ faulty →
      ∃ time, tr time = .commit party view block

theorem local_output_attestations_committed {tr : Trace} {roster faulty : Finset Nat}
    {f view : Nat} {block : Block} (faultBound : faulty.card ≤ f)
    (cert : LocalCommitOutputAttestations tr roster faulty f view block) :
    CommittedAt tr faulty view block := by
  obtain ⟨signers, _, count, exports⟩ := cert
  have honestSigner : ∃ p ∈ signers, p ∉ faulty := by
    by_contra missing
    have contained : signers ⊆ faulty := by
      intro p hp
      by_contra honest
      exact missing ⟨p, hp, honest⟩
    have bound := Finset.card_le_card contained
    omega
  obtain ⟨p, member, honest⟩ := honestSigner
  obtain ⟨time, committed⟩ := exports p member honest
  exact Or.inr ⟨time, p, honest, committed⟩

/-- Portable receiving consequence after ACTUAL signature/export attribution.
This is not a theorem for arbitrary bytes accepted by an unconstrained Crypto IO. -/
theorem local_output_attestations_prefix_consistent {tr : Trace} {roster faulty : Finset Nat}
    {f v w : Nat} {b c : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (left : LocalCommitOutputAttestations tr roster faulty f v b)
    (right : LocalCommitOutputAttestations tr roster faulty f w c) :
    b.IsPrefix c ∨ c.IsPrefix b := by
  exact committed_prefix_consistency rules size faultBound
    (local_output_attestations_committed faultBound left)
    (local_output_attestations_committed faultBound right)

#assert_axioms local_output_attestations_committed
#assert_axioms local_output_attestations_prefix_consistent

#assert_axioms advance_audit_prefix
#assert_axioms known_parent
#assert_axioms committed_ancestor_of_later
#assert_axioms committed_prefix_consistency
#assert_axioms refined_engine_commits_compatible
#assert_axioms known_zero
#assert_axioms known_eq_committed
#assert_axioms committed_not_disabled
#assert_axioms known_eq_committed_at
#assert_axioms committed_not_disabled_at
#assert_axioms known_parent_at
#assert_axioms committed_ancestor_of_later_at
#assert_axioms committed_prefix_consistency_at
#assert_axioms committed_prefix_consistency_admitted
#assert_axioms config_thresholds
#assert_axioms wellFormed_at_legacy
#assert_axioms config_quorum_legacy
end Minidregg.Kernel.GeneralSimplexReachability
