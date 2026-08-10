/-
# Assurance.ProofCompositionGame -- one game for proof-system composition

The semantic clauses deliberately leave concrete PCS, commitment binding, and
Fiat--Shamir security outside their deterministic Lean theorems.  Those
premises must nevertheless not be supplied as unrelated `Prop`s if we want an
end-to-end soundness statement: every failure event has to live on one coin
space and every challenge has to come from one roots-before-challenges oracle
schedule.

This module provides that missing typed boundary.  It does not assert PCS,
ROM, CR, or ZK security.  A deployment supplies actual events and actual
probability bounds.  Lean then proves the only lawful composition step: a
false accepting execution covered by the tagged events has probability at
most their sum.

`SharedOracleSchedule` is intentionally data rather than a scheduling `Prop`.
At round `j`, roots and the oracle query receive only a `Fin j` challenge
prefix.  The current challenge is an answer from the one game oracle to a
domain-separated query.  This shape can host LogUp, history/WARP folds,
additive FRI, and query sampling as phases of one transcript.
-/

import Compiler.AuthenticatedColumnLogupBridge
import Compiler.AdditiveFriReceiptClause
import Loom.OracleLogLinkedTwoPhaseSoundness

namespace Minidregg.Assurance.ProofCompositionGame

open Minidregg.Compiler.AuthenticatedColumnLogupBridge
open Minidregg.Compiler.Logup256ReceiptClause
open Minidregg.Compiler.AdditiveFriReceiptClause
open Minidregg.Loom
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe uRoot uPayload uChallenge uPhase uκ

noncomputable section

/-! ## One prefix-typed, domain-separated oracle transcript -/

/-- The public query sent to the shared oracle.  Domain separation is data in
the query, not a prose promise about two independently modeled hashes. -/
structure DomainSeparatedQuery (Payload : Type uPayload) where
  domain : Digest
  payload : Payload

/-- Restrict a complete challenge vector to the challenges strictly before
round `j`. -/
def challengePrefix {Challenge : Type uChallenge} {rounds : Nat}
    (challenges : Fin rounds -> Challenge) (j : Fin rounds) :
    Fin j -> Challenge :=
  fun i => challenges ⟨i, lt_trans i.isLt j.isLt⟩

/-- A single public-coin transcript schedule for all proof dialects.

`rootsAt j` and `queryAt j` can inspect only challenges `0 .. j-1` by their
types.  `challengeExact` says the current challenge is obtained from the one
oracle table selected by `omega`.  `queryDomainExact` pins every phase to its
declared domain, so two dialects share an oracle without sharing a namespace.
-/
structure SharedOracleSchedule
    (Omega : Type) (Root : Type uRoot) (Payload : Type uPayload)
    (Challenge : Type uChallenge) (Phase : Type uPhase) (rounds : Nat) where
  phase : Fin rounds -> Phase
  domainFor : Phase -> Digest
  rootsAt : (j : Nat) -> (Fin j -> Challenge) -> List Root
  queryAt : (j : Fin rounds) -> (Fin j -> Challenge) ->
    DomainSeparatedQuery Payload
  oracle : Omega -> DomainSeparatedQuery Payload -> Challenge
  challenges : Omega -> Fin rounds -> Challenge
  challengeExact : forall omega j,
    challenges omega j =
      oracle omega (queryAt j (challengePrefix (challenges omega) j))
  queryDomainExact : forall j priorChallenges,
    (queryAt j priorChallenges).domain = domainFor (phase j)
  /-- Every draw is anchored in at least one already-emitted root.  A phase
that needs several roots states that stronger condition in its local bridge. -/
  rootAnchor : forall omega (j : Fin rounds),
    rootsAt j (challengePrefix (challenges omega) j) ≠ []

namespace SharedOracleSchedule

variable {Omega : Type} {Root : Type uRoot} {Payload : Type uPayload}
variable {Challenge : Type uChallenge} {Phase : Type uPhase} {rounds : Nat}

/-- Roots visible at a round are determined entirely by the preceding
challenge prefix. -/
theorem roots_before_challenge
    (schedule : SharedOracleSchedule Omega Root Payload Challenge Phase rounds)
    (left right : Omega) (j : Fin rounds)
    (samePrefix : challengePrefix (schedule.challenges left) j =
      challengePrefix (schedule.challenges right) j) :
    schedule.rootsAt j (challengePrefix (schedule.challenges left) j) =
      schedule.rootsAt j (challengePrefix (schedule.challenges right) j) := by
  rw [samePrefix]

/-- The query itself is fixed before the answer to that query. -/
theorem query_before_challenge
    (schedule : SharedOracleSchedule Omega Root Payload Challenge Phase rounds)
    (left right : Omega) (j : Fin rounds)
    (samePrefix : challengePrefix (schedule.challenges left) j =
      challengePrefix (schedule.challenges right) j) :
    schedule.queryAt j (challengePrefix (schedule.challenges left) j) =
      schedule.queryAt j (challengePrefix (schedule.challenges right) j) := by
  rw [samePrefix]

/-- Viewing the root prefix at a prospective current challenge makes the
non-dependence tooth directly usable by a controller proof. -/
def rootsAtProspectiveChallenge
    (schedule : SharedOracleSchedule Omega Root Payload Challenge Phase rounds)
    (omega : Omega) (j : Fin rounds) (_current : Challenge) : List Root :=
  schedule.rootsAt j (challengePrefix (schedule.challenges omega) j)

theorem roots_independent_of_current_challenge
    (schedule : SharedOracleSchedule Omega Root Payload Challenge Phase rounds)
    (omega : Omega) (j : Fin rounds) (left right : Challenge) :
    schedule.rootsAtProspectiveChallenge omega j left =
      schedule.rootsAtProspectiveChallenge omega j right :=
  rfl

/-- Every scheduled oracle lookup uses the domain pinned by its phase. -/
theorem challenge_uses_phase_domain
    (schedule : SharedOracleSchedule Omega Root Payload Challenge Phase rounds)
    (omega : Omega) (j : Fin rounds) :
    (schedule.queryAt j
      (challengePrefix (schedule.challenges omega) j)).domain =
      schedule.domainFor (schedule.phase j) :=
  schedule.queryDomainExact j _

end SharedOracleSchedule

/-! ## One tagged failure ledger on one coin space -/

/-- The cryptographic/probabilistic seams currently exposed by the composed
proof stack.  Algebraic semantic failure is not a tag here: deterministic
Lean theorems reduce it to these deployment events. -/
inductive FailureClass where
  | logupAlgebra
  | logupPcs
  | historyPcs
  | additiveProximity
  | commitmentBinding
  | oracleTransport
  | oracleLog
  | zeroKnowledge
deriving DecidableEq, Fintype, Repr

/-- One priced event in the common game.  `bound` is supplied by a real
security theorem or concrete deployment argument; this structure creates no
security assumption on its own. -/
structure PricedFailure (Omega : Type) [Fintype Omega] where
  event : Omega -> Prop
  price : Real
  bound : uniformProb Omega event <= price

/-- A total ledger assigns an event and proved bound to every failure class.
Using a function prevents a component from being silently omitted. -/
abbrev FailureLedger (Omega : Type) [Fintype Omega] :=
  FailureClass -> PricedFailure Omega

namespace FailureLedger

variable {Omega : Type} [Fintype Omega]

/-- At least one named component fails on this game coin. -/
def Bad (ledger : FailureLedger Omega) (omega : Omega) : Prop :=
  (ledger .logupAlgebra).event omega ∨
  (ledger .logupPcs).event omega ∨
  (ledger .historyPcs).event omega ∨
  (ledger .additiveProximity).event omega ∨
  (ledger .commitmentBinding).event omega ∨
  (ledger .oracleTransport).event omega ∨
  (ledger .oracleLog).event omega ∨
  (ledger .zeroKnowledge).event omega

/-- The exact additive envelope. -/
def total (ledger : FailureLedger Omega) : Real :=
  (ledger .logupAlgebra).price +
  (ledger .logupPcs).price +
  (ledger .historyPcs).price +
  (ledger .additiveProximity).price +
  (ledger .commitmentBinding).price +
  (ledger .oracleTransport).price +
  (ledger .oracleLog).price +
  (ledger .zeroKnowledge).price

/-- The real finite union bound on the common coin space.  This is the
composition step that is unavailable for bounds stated over unrelated coin
types. -/
theorem bad_le_total (ledger : FailureLedger Omega) :
    uniformProb Omega ledger.Bad <= ledger.total := by
  have h1 := uniformProb_or_le (ledger .logupAlgebra).event (fun omega =>
    (ledger .logupPcs).event omega ∨
    (ledger .historyPcs).event omega ∨
    (ledger .additiveProximity).event omega ∨
    (ledger .commitmentBinding).event omega ∨
    (ledger .oracleTransport).event omega ∨
    (ledger .oracleLog).event omega ∨
    (ledger .zeroKnowledge).event omega)
  have h2 := uniformProb_or_le (ledger .logupPcs).event (fun omega =>
    (ledger .historyPcs).event omega ∨
    (ledger .additiveProximity).event omega ∨
    (ledger .commitmentBinding).event omega ∨
    (ledger .oracleTransport).event omega ∨
    (ledger .oracleLog).event omega ∨
    (ledger .zeroKnowledge).event omega)
  have h3 := uniformProb_or_le (ledger .historyPcs).event (fun omega =>
    (ledger .additiveProximity).event omega ∨
    (ledger .commitmentBinding).event omega ∨
    (ledger .oracleTransport).event omega ∨
    (ledger .oracleLog).event omega ∨
    (ledger .zeroKnowledge).event omega)
  have h4 := uniformProb_or_le (ledger .additiveProximity).event (fun omega =>
    (ledger .commitmentBinding).event omega ∨
    (ledger .oracleTransport).event omega ∨
    (ledger .oracleLog).event omega ∨
    (ledger .zeroKnowledge).event omega)
  have h5 := uniformProb_or_le (ledger .commitmentBinding).event (fun omega =>
    (ledger .oracleTransport).event omega ∨
    (ledger .oracleLog).event omega ∨
    (ledger .zeroKnowledge).event omega)
  have h6 := uniformProb_or_le (ledger .oracleTransport).event (fun omega =>
    (ledger .oracleLog).event omega ∨
    (ledger .zeroKnowledge).event omega)
  have h7 := uniformProb_or_le (ledger .oracleLog).event
    (ledger .zeroKnowledge).event
  unfold Bad total
  linarith [(ledger .logupAlgebra).bound, (ledger .logupPcs).bound,
    (ledger .historyPcs).bound,
    (ledger .additiveProximity).bound, (ledger .commitmentBinding).bound,
    (ledger .oracleTransport).bound, (ledger .oracleLog).bound,
    (ledger .zeroKnowledge).bound]

/-- A component's good event is the complement of its named bad event. -/
def Good (ledger : FailureLedger Omega)
    (failure : FailureClass) (omega : Omega) : Prop :=
  ¬(ledger failure).event omega

theorem good_of_not_bad (ledger : FailureLedger Omega) {omega : Omega}
    (good : ¬ledger.Bad omega) (failure : FailureClass) :
    ledger.Good failure omega := by
  intro bad
  cases failure with
  | logupAlgebra => exact good (Or.inl bad)
  | logupPcs => exact good (Or.inr (Or.inl bad))
  | historyPcs => exact good (Or.inr (Or.inr (Or.inl bad)))
  | additiveProximity =>
      exact good (Or.inr (Or.inr (Or.inr (Or.inl bad))))
  | commitmentBinding =>
      exact good (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl bad)))))
  | oracleTransport =>
      exact good
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl bad))))))
  | oracleLog =>
      exact good
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl bad)))))))
  | zeroKnowledge =>
      exact good
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr bad)))))))

theorem not_bad_of_all_good (ledger : FailureLedger Omega) {omega : Omega}
    (good : forall failure, ledger.Good failure omega) :
    ¬ledger.Bad omega := by
  rintro (h | h | h | h | h | h | h | h)
  · exact good .logupAlgebra h
  · exact good .logupPcs h
  · exact good .historyPcs h
  · exact good .additiveProximity h
  · exact good .commitmentBinding h
  · exact good .oracleTransport h
  · exact good .oracleLog h
  · exact good .zeroKnowledge h

end FailureLedger

/-! ## The composed proof-native game -/

/-- One game owns one oracle schedule, one exhaustive failure ledger, and the
pointwise reduction from false acceptance to a named failure.  The cover is
the deployment-specific composition proof: it is where the concrete LogUp,
history PCS, additive-FRI, OracleLog, CR, ROM, and ZK theorems meet.

The interface keeps that hard obligation explicit while making its conclusion
unambiguous and mechanically composable. -/
structure SecurityGame
    (Omega : Type) [Fintype Omega]
    (Root : Type uRoot) (Payload : Type uPayload)
    (Challenge : Type uChallenge) (Phase : Type uPhase) (rounds : Nat) where
  transcript : SharedOracleSchedule Omega Root Payload Challenge Phase rounds
  ledger : FailureLedger Omega
  falseAccept : Omega -> Prop
  failureCover : forall omega, falseAccept omega -> ledger.Bad omega

namespace SecurityGame

variable {Omega : Type} [Fintype Omega]
variable {Root : Type uRoot} {Payload : Type uPayload}
variable {Challenge : Type uChallenge} {Phase : Type uPhase} {rounds : Nat}

/-- End-to-end soundness of the typed common game.  There is no independence
premise: the union bound is valid for correlated events because all of them
are predicates on the same `Omega`. -/
theorem falseAccept_le
    (game : SecurityGame Omega Root Payload Challenge Phase rounds) :
    uniformProb Omega game.falseAccept <= game.ledger.total :=
  le_trans (uniformProb_mono game.failureCover) game.ledger.bad_le_total

/-- Outside every priced failure, false acceptance is impossible. -/
theorem falseAccept_impossible_of_all_good
    (game : SecurityGame Omega Root Payload Challenge Phase rounds)
    {omega : Omega}
    (good : forall failure, game.ledger.Good failure omega) :
    ¬game.falseAccept omega := by
  intro accepted
  exact game.ledger.not_bad_of_all_good good (game.failureCover omega accepted)

end SecurityGame

/-! ## Exact adapters for the existing LogUp/additive premise shapes -/

/-- The LogUp PCS predicate induced by one exact common-game coin.  It cannot
be reused for another claim or trace, and its only cryptographic content is
the ledger's `logupPcs` good event. -/
def LogupPcsLaw
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    {F : Type*} {k : Nat} {kappa : Type uκ}
    (expectedClaim : IndexedTableReceiptClaim F kappa k)
    (expectedTrace : CommittedSemanticTrace kappa k)
    (candidateClaim : IndexedTableReceiptClaim F kappa k)
    (candidateTrace : CommittedSemanticTrace kappa k) : Prop :=
  candidateClaim = expectedClaim ∧ candidateTrace = expectedTrace ∧
    ledger.Good .logupPcs omega

/-- The exact-claim commitment law drawn from the same game and coin. -/
def LogupBindingLaw
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    {F : Type*} {k : Nat} {kappa : Type uκ}
    (expectedClaim : IndexedTableReceiptClaim F kappa k)
    (expectedTrace : CommittedSemanticTrace kappa k)
    (candidateClaim : IndexedTableReceiptClaim F kappa k)
    (candidateTrace : CommittedSemanticTrace kappa k) : Prop :=
  candidateClaim = expectedClaim ∧ candidateTrace = expectedTrace ∧
    ledger.Good .commitmentBinding omega

/-- The exact-claim ROM transport law drawn from the same game and coin. -/
def LogupRomLaw
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    {F : Type*} {k : Nat} {kappa : Type uκ}
    (expectedClaim : IndexedTableReceiptClaim F kappa k)
    (candidateClaim : IndexedTableReceiptClaim F kappa k) : Prop :=
  candidateClaim = expectedClaim ∧ ledger.Good .oracleTransport omega

theorem logupPcsLaw_exact
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    {F : Type*} {k : Nat} {kappa : Type uκ}
    (claim : IndexedTableReceiptClaim F kappa k)
    (trace : CommittedSemanticTrace kappa k)
    (good : ledger.Good .logupPcs omega) :
    LogupPcsLaw ledger omega claim trace claim trace :=
  ⟨rfl, rfl, good⟩

theorem logupBindingLaw_exact
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    {F : Type*} {k : Nat} {kappa : Type uκ}
    (claim : IndexedTableReceiptClaim F kappa k)
    (trace : CommittedSemanticTrace kappa k)
    (good : ledger.Good .commitmentBinding omega) :
    LogupBindingLaw ledger omega claim trace claim trace :=
  ⟨rfl, rfl, good⟩

theorem logupRomLaw_exact
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    {F : Type*} {k : Nat} {kappa : Type uκ}
    (claim : IndexedTableReceiptClaim F kappa k)
    (good : ledger.Good .oracleTransport omega) :
    LogupRomLaw ledger omega claim claim :=
  ⟨rfl, good⟩

/-- Additive-FRI external premises selected from the same ledger coin.  The
arithmetic check remains deterministic Lean evidence and is not assigned a
probability price. -/
def additiveExternalPremises
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    (bindingGood : ledger.Good .commitmentBinding omega)
    (romGood : ledger.Good .oracleTransport omega)
    {ArithmeticBufferCheck : Prop} (arithmeticChecked : ArithmeticBufferCheck) :
    ExternalPremises (ledger.Good .commitmentBinding omega)
      (ledger.Good .oracleTransport omega) ArithmeticBufferCheck where
  commitmentBinding := bindingGood
  cshakeRom := romGood
  arithmeticBufferChecked := arithmeticChecked

/-! `twoPhaseOracleLogFsSoundness_le` is the concrete theorem intended to
price the `oracleLog` entry when the common `Omega` is its staged OracleLog
coin space.  Its CR and ZK predicates should populate the corresponding
ledger entries on that identical type; this module intentionally does not
postulate those bounds or transport them across a different coin space. -/

/-- info: 'Minidregg.Assurance.ProofCompositionGame.SharedOracleSchedule.roots_before_challenge' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms SharedOracleSchedule.roots_before_challenge
/-- info: 'Minidregg.Assurance.ProofCompositionGame.FailureLedger.bad_le_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FailureLedger.bad_le_total
/-- info: 'Minidregg.Assurance.ProofCompositionGame.SecurityGame.falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SecurityGame.falseAccept_le
/-- info: 'Minidregg.Assurance.ProofCompositionGame.additiveExternalPremises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveExternalPremises

end

end Minidregg.Assurance.ProofCompositionGame
