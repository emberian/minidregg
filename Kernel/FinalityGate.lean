/-
# Kernel.FinalityGate -- the fail-closed finality decider (Lean is the live decider)

ATLAS §3 item 11 names breadstuffs' `Distributed/FinalityGate.lean` pattern:
Lean is the live decider, fail-closed, `@[export]` from day one.
`ReplicatedSettlementFinality` carries the SAFETY of quorum finality -- but its
`Finalized` is a `Type`-valued certificate; nothing there computes a `Bool` and
nothing is exported.  This module is the decider.

* **`Cert`** is the wire datum: WHO is claimed to have voted.  Nothing else on
  the wire is trusted.  The checker re-reads the vote book for every claimed
  voter, so a presented voter set can be neither inflated (an unvoted node is
  refused) nor thinned into a non-quorum.
* **`check`** is a bare `&&` of the two positive conditions, decided.  The
  unfolding lemma `check_eq_true_iff` is the load-bearing statement (the
  `gateOK_eq_true_iff` role): `true` means exactly quorum ∧ every claimed voter
  recorded this candidate.
* **Soundness IS construction**: `certificate` turns a `true` verdict into the
  existing `Finalized` certificate (voters := the presented set), so every
  safety theorem of the replicated layer is inherited through the checker
  (`checked_logs_comparable`, `checked_no_conflict`,
  `checked_transaction_unique_at_slot`) -- reused, never re-proved.
  `check_complete` closes the loop: every `Finalized` certificate's voter set
  checks `true`; `check_eq_true_iff_exists_finalized` is the exact
  characterization.
* **Fail-closed teeth**: `check_false_of_not_quorum`, `check_false_of_unvoted`,
  `check_false_of_no_quorum` -- each with the OTHER condition still available,
  so a refusal is attributable to exactly one leg.
* **Closed instance, computed**: on `ReplicatedSettlementFinality.ClosedInstance`
  (`Fin 3`, core quorum `{0, 1}`), the honest cert and its superset are
  accepted, the thin cert `{0}`, a tampered book (node 1 silent), and a forged
  same-slot candidate are refused -- each by `decide`, each beside the leg that
  still holds.  The inherited safety theorems FIRE on the closed instance.
* **The export symbol** `minidregg_finality_check` (`checkExport`) is the
  monomorphic decision a Rust caller links against -- the Gate §10 pattern:
  the export path EXISTS; marshalling is the rust lane's.

Decidable equality on `Intent`/`Candidate` is derived here (§1): `Charge` is
a function on the finite `Lane` alphabet, decided pointwise via `Fintype Lane`.

**Not closed -- prose residuals.**
`[FINALITY-GATE-authenticated]` the vote book is TRUSTED DATA here; signed
votes live in `Kernel/AuthenticatedSettlementFinality.lean`
(`AuthenticatedFinalized`, `eraseBook`), and the checker over signed votes that
erases to this one is not built.
`[FINALITY-GATE-liveness]` no progress is decided; `AvailableQuorum` /
`FairDelivery` / `Responsive` stay premises of the replicated layer.
`[FINALITY-GATE-rust]` the breadstuffs "unverified fallback only behind an
explicit labeled env var" discipline is Rust-side and not represented here.
`[FINALITY-GATE-receipt-seam]` no connection yet to the hyperedge receipt
chain's seam `post-root i = pre-root (i+1)`.
-/
import Kernel.ReplicatedSettlementFinality

namespace Minidregg.Kernel.FinalityGate

open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.ReplicatedSettlementFinality

set_option autoImplicit false

universe u v w x n

variable {TxId : Type u} {CellId : Type v} {Nullifier : Type w} {Event : Type x}
variable {Node : Type n} [DecidableEq Node]

/-! ## §1. Decidable equality on the replicated carriers.

`Intent.exactCharge : Charge = Lane → Nat`; equality is decided pointwise over
the finite lane alphabet (`Fintype.decidablePiFintype`).  Nothing else in the
carrier is exotic. -/

deriving instance DecidableEq for Intent
deriving instance DecidableEq for Candidate

/-! ## §2. The wire datum and the decider. -/

/-- The presented certificate: the claimed voter set, and nothing else.  Every
other fact the verdict rests on is re-derived from the vote book. -/
structure Cert (Node : Type n) where
  voters : Finset Node

/-- The fail-closed decider: quorum, AND every claimed voter recorded this exact
candidate.  A bare conjunction of positive checks -- absence of evidence is
refusal. -/
def check (quorums : QuorumSystem Node) [DecidablePred quorums.isQuorum]
    [DecidableEq (Candidate TxId CellId Nullifier Event)]
    (book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
      (Nullifier := Nullifier) (Event := Event))
    (candidate : Candidate TxId CellId Nullifier Event) (cert : Cert Node) : Bool :=
  decide (quorums.isQuorum cert.voters) &&
    decide (∀ node ∈ cert.voters, candidate ∈ book node)

section Generic

variable (quorums : QuorumSystem Node) [DecidablePred quorums.isQuorum]
  [DecidableEq (Candidate TxId CellId Nullifier Event)]
  (book : VoteBook (Node := Node) (TxId := TxId) (CellId := CellId)
    (Nullifier := Nullifier) (Event := Event))

/-- The unfolding lemma: `true` means exactly the two conditions. -/
theorem check_eq_true_iff (candidate : Candidate TxId CellId Nullifier Event)
    (cert : Cert Node) :
    check quorums book candidate cert = true ↔
      quorums.isQuorum cert.voters ∧ ∀ node ∈ cert.voters, candidate ∈ book node := by
  simp [check]

/-! ## §3. Soundness is construction; completeness closes the loop. -/

/-- A `true` verdict CONSTRUCTS the replicated layer's certificate, with the
presented voter set as the certificate's voters. -/
def certificate {candidate : Candidate TxId CellId Nullifier Event} {cert : Cert Node}
    (accepted : check quorums book candidate cert = true) :
    Finalized quorums book candidate where
  voters := cert.voters
  quorum := ((check_eq_true_iff quorums book candidate cert).mp accepted).1
  voted := fun node member =>
    ((check_eq_true_iff quorums book candidate cert).mp accepted).2 node member

theorem certificate_voters {candidate : Candidate TxId CellId Nullifier Event}
    {cert : Cert Node} (accepted : check quorums book candidate cert = true) :
    (certificate quorums book accepted).voters = cert.voters := rfl

theorem check_sound {candidate : Candidate TxId CellId Nullifier Event} {cert : Cert Node}
    (accepted : check quorums book candidate cert = true) :
    Nonempty (Finalized quorums book candidate) :=
  ⟨certificate quorums book accepted⟩

/-- Every certificate of the replicated layer checks `true` on its own voter
set: the decider refuses nothing the safety layer would accept. -/
theorem check_complete {candidate : Candidate TxId CellId Nullifier Event}
    (finalized : Finalized quorums book candidate) :
    check quorums book candidate ⟨finalized.voters⟩ = true :=
  (check_eq_true_iff quorums book candidate _).mpr ⟨finalized.quorum, finalized.voted⟩

/-- Exact characterization: the decider accepts precisely the voter sets of
`Finalized` certificates. -/
theorem check_eq_true_iff_exists_finalized
    (candidate : Candidate TxId CellId Nullifier Event) (cert : Cert Node) :
    check quorums book candidate cert = true ↔
      ∃ finalized : Finalized quorums book candidate, finalized.voters = cert.voters := by
  constructor
  · intro accepted
    exact ⟨certificate quorums book accepted, rfl⟩
  · rintro ⟨finalized, voters⟩
    have := check_complete quorums book finalized
    rwa [voters] at this

/-! ## §4. Inherited safety -- through the checker, never re-proved. -/

theorem checked_logs_comparable (discipline : PrefixDiscipline book)
    {left right : Candidate TxId CellId Nullifier Event} {certL certR : Cert Node}
    (acceptedL : check quorums book left certL = true)
    (acceptedR : check quorums book right certR = true) :
    left.log.IsPrefix right.log ∨ right.log.IsPrefix left.log :=
  finalized_logs_comparable discipline
    (certificate quorums book acceptedL) (certificate quorums book acceptedR)

theorem checked_transaction_unique_at_slot (discipline : PrefixDiscipline book)
    {left right : Candidate TxId CellId Nullifier Event} {certL certR : Cert Node}
    (acceptedL : check quorums book left certL = true)
    (acceptedR : check quorums book right certR = true)
    (sameSlot : left.slot = right.slot) :
    left.intent = right.intent :=
  finalized_transaction_unique_at_slot discipline
    (certificate quorums book acceptedL) (certificate quorums book acceptedR) sameSlot

theorem checked_no_conflict (discipline : PrefixDiscipline book)
    {left right : Candidate TxId CellId Nullifier Event} {certL certR : Cert Node}
    (acceptedL : check quorums book left certL = true)
    (acceptedR : check quorums book right certR = true) :
    ¬ ConflictsAtSlot left right :=
  no_conflicting_finalized_transactions discipline
    (certificate quorums book acceptedL) (certificate quorums book acceptedR)

/-! ## §5. Fail-closed teeth -- one leg fails, the verdict is `false`. -/

/-- Quorum leg: a presented set that is not a quorum is refused, whatever the
book says about its members. -/
theorem check_false_of_not_quorum {candidate : Candidate TxId CellId Nullifier Event}
    {cert : Cert Node} (notQuorum : ¬ quorums.isQuorum cert.voters) :
    check quorums book candidate cert = false :=
  Bool.eq_false_iff.mpr fun accepted =>
    notQuorum ((check_eq_true_iff quorums book candidate cert).mp accepted).1

/-- Vote leg: one claimed voter whose book lacks the candidate refuses the
whole certificate, whatever the quorum leg says. -/
theorem check_false_of_unvoted {candidate : Candidate TxId CellId Nullifier Event}
    {cert : Cert Node} {node : Node} (member : node ∈ cert.voters)
    (absent : candidate ∉ book node) :
    check quorums book candidate cert = false :=
  Bool.eq_false_iff.mpr fun accepted =>
    absent (((check_eq_true_iff quorums book candidate cert).mp accepted).2 node member)

/-- No quorum system-wide: the decider manufactures nothing (the computed face
of `no_finality_without_any_quorum`). -/
theorem check_false_of_no_quorum {candidate : Candidate TxId CellId Nullifier Event}
    (cert : Cert Node) (none : ∀ voters, ¬ quorums.isQuorum voters) :
    check quorums book candidate cert = false :=
  check_false_of_not_quorum quorums book (none cert.voters)

end Generic

/-! ## §6. The closed instance, computed (both poles, each refusal attributable). -/

namespace ClosedInstance

open Minidregg.Kernel.ReplicatedSettlementFinality.ClosedInstance

/-- `quorums.isQuorum voters` is `core ⊆ voters`, decided on `Fin 3`. -/
instance quorumsDecidable : DecidablePred quorums.isQuorum :=
  fun voters => inferInstanceAs (Decidable (core ⊆ voters))

/-- The honest wire: exactly the core. -/
def honest : Cert ReplicaNode := ⟨{0, 1}⟩
/-- A superset of the core is still a quorum here. -/
def full : Cert ReplicaNode := ⟨{0, 1, 2}⟩
/-- Thinned below the core. -/
def thin : Cert ReplicaNode := ⟨{0}⟩

/-- *Satisfiable*: the honest cert is accepted -- COMPUTED. -/
theorem honest_accepted : check quorums book candidate honest = true := by decide
theorem full_accepted : check quorums book candidate full = true := by decide

/-- *Teeth* (quorum leg): `{0}` is refused, while every claimed voter DID vote
-- the refusal is the quorum leg's alone. -/
theorem thin_refused : check quorums book candidate thin = false := by decide
theorem thin_voted : ∀ node ∈ thin.voters, candidate ∈ book node := by decide
theorem thin_not_quorum : ¬ quorums.isQuorum thin.voters := by decide

/-- *Teeth* (vote leg, tampered book): node 1 is silent.  The honest cert still
names a quorum; the refusal is the vote leg's alone. -/
def tamperedBook : VoteBook (Node := ReplicaNode) (TxId := Nat) (CellId := Nat)
    (Nullifier := Nat) (Event := Nat) :=
  fun node => if node = 1 then [] else [candidate]

theorem tampered_refused : check quorums tamperedBook candidate honest = false := by decide
theorem tampered_quorum : quorums.isQuorum honest.voters := by decide
theorem tampered_unvoted : candidate ∉ tamperedBook 1 := by decide

/-- *Teeth* (vote leg, forged candidate): the same slot and log prefix, one
different event.  Nobody voted for it; the honest quorum cannot check it in. -/
def forged : Candidate Nat Nat Nat Nat :=
  { candidate with intent := { candidate.intent with event := 43 } }

theorem forged_same_slot : forged.slot = candidate.slot := rfl
theorem forged_differs : forged.intent ≠ candidate.intent := by decide
theorem forged_refused : check quorums book forged honest = false := by decide

/-- Inherited safety FIRES on the closed instance: any candidate the checker
accepts under any presented cert is prefix-comparable with the honest one and
cannot conflict with it at its slot. -/
theorem closed_checked_logs_comparable {other : Candidate Nat Nat Nat Nat}
    {cert : Cert ReplicaNode} (accepted : check quorums book other cert = true) :
    candidate.log.IsPrefix other.log ∨ other.log.IsPrefix candidate.log :=
  checked_logs_comparable quorums book discipline honest_accepted accepted

theorem closed_checked_no_conflict {other : Candidate Nat Nat Nat Nat}
    {cert : Cert ReplicaNode} (accepted : check quorums book other cert = true) :
    ¬ ConflictsAtSlot candidate other :=
  checked_no_conflict quorums book discipline honest_accepted accepted

/-- Two concrete verdicts feeding the inherited theorem. -/
example : candidate.log.IsPrefix candidate.log ∨ candidate.log.IsPrefix candidate.log :=
  closed_checked_logs_comparable full_accepted

/-! ## §7. The FFI seam -- `@[export]` (the Gate §10 pattern).

The monomorphic decision is a compiled symbol (`minidregg_finality_check`) a
Rust caller links against; the wire voter list is deduplicated into the
`Finset` the decider reads.  Handles, codecs, and the labeled-fallback
discipline are `[FINALITY-GATE-rust]`. -/

@[export minidregg_finality_check]
def checkExport (voters : List ReplicaNode) : Bool :=
  check quorums book candidate ⟨voters.toFinset⟩

theorem checkExport_eq (voters : List ReplicaNode) :
    checkExport voters = check quorums book candidate ⟨voters.toFinset⟩ := rfl

example : checkExport [0, 1] = true := by decide
example : checkExport [1, 0, 1] = true := by decide
example : checkExport [1] = false := by decide
example : checkExport [] = false := by decide

end ClosedInstance

/-! ## §8. Axiom pins (exact-output, self-verifying -- State §8's discipline). -/

/-- info: 'Minidregg.Kernel.FinalityGate.check_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_eq_true_iff

/-- info: 'Minidregg.Kernel.FinalityGate.check_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_sound

/-- info: 'Minidregg.Kernel.FinalityGate.check_complete' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_complete

/-- info: 'Minidregg.Kernel.FinalityGate.check_eq_true_iff_exists_finalized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_eq_true_iff_exists_finalized

/-- info: 'Minidregg.Kernel.FinalityGate.checked_logs_comparable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checked_logs_comparable

/-- info: 'Minidregg.Kernel.FinalityGate.checked_no_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms checked_no_conflict

/-- info: 'Minidregg.Kernel.FinalityGate.check_false_of_not_quorum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_false_of_not_quorum

/-- info: 'Minidregg.Kernel.FinalityGate.check_false_of_unvoted' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms check_false_of_unvoted

/-- info: 'Minidregg.Kernel.FinalityGate.ClosedInstance.honest_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ClosedInstance.honest_accepted

/-- info: 'Minidregg.Kernel.FinalityGate.ClosedInstance.thin_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ClosedInstance.thin_refused

/-- info: 'Minidregg.Kernel.FinalityGate.ClosedInstance.tampered_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ClosedInstance.tampered_refused

/-- info: 'Minidregg.Kernel.FinalityGate.ClosedInstance.forged_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ClosedInstance.forged_refused

/-- info: 'Minidregg.Kernel.FinalityGate.ClosedInstance.closed_checked_no_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ClosedInstance.closed_checked_no_conflict

end Minidregg.Kernel.FinalityGate
