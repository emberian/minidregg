import Kernel.GenericSimplexVAInvariant

namespace Minidregg.Kernel.GeneralSimplexReachability
open Minidregg.Kernel.GenericSimplex
open Minidregg.Kernel.GenericSimplexVAInvariant
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

theorem known_zero {tr : Trace} {roster faulty : Finset Nat} {f : Nat} {b : Block}
    (rules : LocalFaithful tr roster faulty f) (known : KnownValue tr faulty 0 b) : b = [] := by
  rcases known with ⟨_, empty⟩ | ⟨t, p, honest, prepared | committed⟩
  · exact empty
  · have bad := rules.preparePositive t p 0 b honest prepared
    omega
  · have bad := rules.commitPositive t p 0 b honest committed
    omega

theorem known_eq_committed {tr : Trace} {roster faulty : Finset Nat}
    {f v : Nat} {b c : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (known : KnownValue tr faulty v b) (commit : CommittedAt tr faulty v c) : b = c := by
  rcases commit with ⟨zero, empty⟩ | ⟨t, p, hp, committed⟩
  · subst v
    exact (known_zero rules known).trans empty.symm
  · rcases known with ⟨zero, _⟩ | ⟨u, q, hq, prepared | otherCommit⟩
    · have pos := rules.commitPositive t p v c hp committed
      omega
    · exact committed_excludes_other_prepare rules size faultBound hp hq committed prepared
    · exact (committed_unique rules size faultBound hp hq committed otherCommit).symm

theorem committed_not_disabled {tr : Trace} {roster faulty : Finset Nat}
    {f v t p : Nat} {c : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (commit : CommittedAt tr faulty v c) (hp : p ∉ faulty)
    (disabled : tr t = .disable p v) : False := by
  rcases commit with ⟨zero, _⟩ | ⟨u, q, hq, committed⟩
  · have pos := rules.disablePositive t p v hp disabled
    omega
  · exact committed_excludes_disable rules size faultBound hq hp committed disabled

/-- A real earlier safe vote supplies a prepared parent and every skipped-view
clear. This closes the catch-up-vote cycle through well-founded event causality. -/
theorem known_parent {tr : Trace} {roster faulty : Finset Nat}
    {f v : Nat} {b : Block} (rules : LocalFaithful tr roster faulty f)
    (faultBound : faulty.card ≤ f) (positive : 0 < v)
    (known : KnownValue tr faulty v b) :
    ∃ previous < v, KnownValue tr faulty previous b.dropLast ∧
      ∀ skipped, previous < skipped → skipped < v →
        ∃ t p, p ∉ faulty ∧ tr t = .disable p skipped := by
  rcases known with ⟨zero, _⟩ | ⟨t, p, hp, output⟩
  · omega
  · have voter : ∃ q, q ∉ faulty ∧ ∃ earlier < t, Sent tr earlier q v .vote (some b) := by
      rcases output with prepared | committed
      · exact prepared_has_honest_vote rules faultBound hp prepared
      · have cc := rules.commitOutput t p v b hp committed
        obtain ⟨ct, clt, votes⟩ := commit_core_has_vote_core rules faultBound cc
        obtain ⟨q, _, hq, vt, vlt, sent⟩ := support_honest faultBound (by omega) votes
        exact ⟨q, hq, vt, by omega, sent⟩
    obtain ⟨q, hq, vt, _, sent⟩ := voter
    obtain ⟨st, _, r, hr, _, previous, prevLt, parent, skipped⟩ :=
      honest_vote_has_safe_origin rules faultBound vt q v b hq sent
    refine ⟨previous, prevLt, ?_, ?_⟩
    · rcases parent with genesis | ⟨pt, _, prepared⟩
      · exact Or.inl genesis
      · exact Or.inr ⟨pt, r, hr, Or.inl prepared⟩
    · intro w low high
      obtain ⟨dt, _, disabled⟩ := skipped w low high
      exact ⟨dt, r, hr, disabled⟩

/-- Global outer-prefix theorem over the same executable-event audit obligations.
No assumption says that committed blocks are compatible. -/
theorem committed_ancestor_of_later {tr : Trace} {roster faulty : Finset Nat} {f : Nat}
    (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (v : Nat) : ∀ previous b c,
      KnownValue tr faulty v b → CommittedAt tr faulty previous c → previous ≤ v →
      c.IsPrefix b := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    intro previous b c known commit order
    by_cases same : previous = v
    · subst previous
      have eq := known_eq_committed rules size faultBound known commit
      subst b
      exact List.prefix_refl c
    · have before : previous < v := by omega
      obtain ⟨parentView, parentLt, parent, skipped⟩ :=
        known_parent rules faultBound (by omega) known
      have lower : previous ≤ parentView := by
        by_contra bad
        obtain ⟨t, p, hp, disabled⟩ := skipped previous (by omega) before
        exact committed_not_disabled rules size faultBound commit hp disabled
      have ancestor := ih parentView parentLt previous b.dropLast c parent commit lower
      exact ancestor.trans (List.dropLast_prefix b)

theorem committed_prefix_consistency {tr : Trace} {roster faulty : Finset Nat}
    {f v w : Nat} {b c : Block} (rules : LocalFaithful tr roster faulty f)
    (size : roster.card = 3 * f + 1) (faultBound : faulty.card ≤ f)
    (left : CommittedAt tr faulty v b) (right : CommittedAt tr faulty w c) :
    b.IsPrefix c ∨ c.IsPrefix b := by
  rcases Nat.le_total v w with order | order
  · exact Or.inl (committed_ancestor_of_later rules size faultBound w v c b
      (committed_known right) left order)
  · exact Or.inr (committed_ancestor_of_later rules size faultBound v w b c
      (committed_known left) right order)

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

/-- This is a demanded refinement RESULT, not an axiom and not a certificate gate.
Its constructor must be produced inductively from Reachable using the local
extraction lemmas; that construction remains owned by GenericSimplexLocal.
Until it exists, actual engine prefix safety is NOT claimed proved. -/
structure AuditRefinement (c : Config) (faulty : Finset Nat) (net : Network) where
  faithful : LocalFaithful (auditTrace net) (Finset.range c.parties) faulty c.faults
  commits : ∀ party view block, party < c.parties → party ∉ faulty →
    (viewAt (net.localState party) view).committed = some block →
    CommittedAt (auditTrace net) faulty view block
  delivered : ∀ party block, party < c.parties → party ∉ faulty →
    block ∈ (net.localState party).delivered →
    ∃ view, CommittedAt (auditTrace net) faulty view block

/-- Conditional join target for source export. It is intentionally named as a
refinement consequence, never as an unconditional property of VerifiedCommit. -/
theorem refined_engine_commits_compatible {c : Config} {faulty : Finset Nat} {net : Network}
    (audit : AuditRefinement c faulty net) (size : c.parties = 3 * c.faults + 1)
    (faultBound : faulty.card ≤ c.faults) {p q v w : Nat} {b d : Block}
    (pm : p < c.parties) (qm : q < c.parties) (ph : p ∉ faulty) (qh : q ∉ faulty)
    (left : (viewAt (net.localState p) v).committed = some b)
    (right : (viewAt (net.localState q) w).committed = some d) :
    b.IsPrefix d ∨ d.IsPrefix b := by
  exact committed_prefix_consistency audit.faithful (by simpa using size) faultBound
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
end Minidregg.Kernel.GeneralSimplexReachability
