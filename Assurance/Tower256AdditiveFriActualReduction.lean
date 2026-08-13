/-
# Assurance.Tower256AdditiveFriActualReduction -- the actual additive-FRI cover

This module removes the arbitrary pointwise `failureCover` from the concrete
Tower256 additive-FRI admission.  Its coin space is literally the ideal
challenge/query sample measured by `Selvage.additiveFriAdaptive_coherent_sampled_sound_UD`.
The `additiveProximity` ledger entry is replaced, by construction, with that
exact acceptance event and its proved UD price.

An accepted native reply contributes only bytes.  Lean decoding and checking
produce an `AcceptedReceipt`; the existing controller theorem then produces
the exact ideal additive-FRI sample accepted by Selvage.  The only pointwise
transport premise says that, outside the common `oracleTransport` event, this
Lean-derived cSHAKE sample is the game coin.  Consequently false acceptance is
covered by `additiveProximity` or `oracleTransport`, hence by the requested
three-event envelope including `commitmentBinding`.  No caller supplies a
false-accept cover.

The current `MerklePcs` type already contains `PositionBinding` for every
concrete level.  Thus binding is an exact global premise of the verifier, not a
conditional theorem derived here from a cSHAKE collision game.  The absent
Merkle-collision-to-`PositionBinding` reduction is stated honestly by retaining
that exact projection; conditionalizing it on the common coin would require a
raw (non-binding) PCS/controller interface.  This module does not pretend that
functional Merkle correctness proves collision resistance.
-/

import Assurance.Tower256AdditiveFriControllerAdmission

namespace Minidregg.Assurance.Tower256AdditiveFriActualReduction

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.Tower256AdditiveFriControllerAdmission
open Minidregg.Compiler.AdditiveFriReceiptClause
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Selvage
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

variable {ell m queryCount : Nat}
variable {manifest : Manifest}
variable {pcs : MerklePcs ell}
variable {clause : FriClause pcs m manifest}
variable {verifier : Verifier (queryCount := queryCount) pcs clause}

local instance : Fintype Tower256 := Fintype.ofFinite _
local instance : DecidableEq Tower256 := Classical.decEq _

/-! ## The exact ideal coin and its proved price -/

/-- The precise uniform sample space in the landed additive-FRI theorem. -/
abbrev IdealCoin (clause : FriClause pcs m manifest) :=
  (Fin m -> Tower256) ×
    (Fin clause.queryCount -> PowerTwoFriLevels ell 1)

/-- The actual ideal-binding acceptance predicate, without a renamed proxy. -/
def IdealAccept (clause : FriClause pcs m manifest)
    (coin : IdealCoin clause) : Prop :=
  AdditiveFriAdaptiveCoherentAccepts clause.tower pcs.commitment clause.degree
    clause.transcript clause.queryCount coin.1 coin.2

/-- The additive ledger entry is constructed from the real UD theorem. -/
def additiveProximityFailure
    {radius : Nat -> Real} {tau : Real}
    (certificate : FarWordSoundnessCertificate clause radius tau) :
    PricedFailure (IdealCoin clause) where
  event := IdealAccept clause
  price := (m : Real) * (2 ^ (ell - 1) : Nat) /
      (Fintype.card Tower256 : Real) + (1 - tau) ^ clause.queryCount
  bound := certificate.exact_ud_challenge_query_error

/-- Replace only the additive entry.  Every other event and price remains on
the identical ideal-sample coin space supplied by the application. -/
def exactLedger
    {radius : Nat -> Real} {tau : Real}
    (base : FailureLedger (IdealCoin clause))
    (certificate : FarWordSoundnessCertificate clause radius tau) :
    FailureLedger (IdealCoin clause)
  | .additiveProximity => additiveProximityFailure certificate
  | .logupAlgebra => base .logupAlgebra
  | .logupPcs => base .logupPcs
  | .historyPcs => base .historyPcs
  | .commitmentBinding => base .commitmentBinding
  | .oracleTransport => base .oracleTransport
  | .oracleLog => base .oracleLog
  | .zeroKnowledge => base .zeroKnowledge

@[simp] theorem exactLedger_additive_event
    {radius : Nat -> Real} {tau : Real}
    (base : FailureLedger (IdealCoin clause))
    (certificate : FarWordSoundnessCertificate clause radius tau)
    (coin : IdealCoin clause) :
    (exactLedger base certificate .additiveProximity).event coin <->
      IdealAccept clause coin :=
  Iff.rfl

@[simp] theorem exactLedger_binding_event
    {radius : Nat -> Real} {tau : Real}
    (base : FailureLedger (IdealCoin clause))
    (certificate : FarWordSoundnessCertificate clause radius tau)
    (coin : IdealCoin clause) :
    (exactLedger base certificate .commitmentBinding).event coin <->
      (base .commitmentBinding).event coin :=
  Iff.rfl

@[simp] theorem exactLedger_transport_event
    {radius : Nat -> Real} {tau : Real}
    (base : FailureLedger (IdealCoin clause))
    (certificate : FarWordSoundnessCertificate clause radius tau)
    (coin : IdealCoin clause) :
    (exactLedger base certificate .oracleTransport).event coin <->
      (base .oracleTransport).event coin :=
  Iff.rfl

/-! ## Accepted controller bytes select an ideal sample -/

/-- The exact ideal sample extracted from a Lean-accepted controller reply.
The witness is chosen from the controller theorem, not from native data. -/
def acceptedIdealCoin {request : List UInt8}
    (reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request) : IdealCoin clause :=
  (reply.receipt.challenges,
    Classical.choose
      (accepts_additiveFriAdaptiveCoherentAccepts pcs clause verifier.pins
        reply.receipt reply.accepted))

theorem acceptedIdealCoin_accepts {request : List UInt8}
    (reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request) :
    IdealAccept clause (acceptedIdealCoin reply) :=
  Classical.choose_spec
    (accepts_additiveFriAdaptiveCoherentAccepts pcs clause verifier.pins
      reply.receipt reply.accepted)

/-- In particular, the final controller word is in the exact advertised
Reed--Solomon code; there is no separate native `codeExact` assertion. -/
theorem acceptedFinalReedSolomon {request : List UInt8}
    (reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request) :
    clause.transcript.wordAt reply.receipt.challenges m le_rfl ∈
      reedSolomonCode (clause.tower.dom m) (clause.degree m) :=
  (acceptedIdealCoin_accepts reply).2

/-- Exact binding premise already embedded in the concrete PCS selected by
the controller.  Obtaining this projection from a concrete adaptive cSHAKE
Merkle collision game is the remaining CR theorem; it is not manufactured by
the reduction below. -/
theorem concreteLevelPositionBinding (n : Nat) :
    (pcs.level n).scheme.PositionBinding :=
  pcs.positionBinding n

/-! ## Same-coin concrete execution and ROM transport -/

/-- A concrete execution family with no false-accept cover field.

`transportExact` is the exact ROM residual: outside the named transport event,
the challenge/query sample reconstructed by Lean from accepted bytes equals
the uniform ideal coin.  The shared schedule is pinned to the challenge half
and to every controller root prefix. -/
structure ActualReductionFamily
    {radius : Nat -> Real} {tau : Real}
    (certificate : FarWordSoundnessCertificate clause radius tau)
    (Error : Type) (request : List UInt8) where
  baseLedger : FailureLedger (IdealCoin clause)
  schedule : SharedOracleSchedule (IdealCoin clause) Digest (List UInt8)
    Tower256 Digest m
  execution : IdealCoin clause -> Option
    (AcceptedReceipt (queryCount := queryCount) pcs clause verifier request)
  runner : IdealCoin clause -> OpaqueProofRunner Error
  executionExact : forall coin reply,
    execution coin = some reply ->
      run (queryCount := queryCount) pcs clause verifier
        (runner coin) request = .ok reply
  transportExact : forall coin reply,
    execution coin = some reply ->
      (exactLedger baseLedger certificate).Good .oracleTransport coin ->
      acceptedIdealCoin reply = coin
  scheduleChallengesExact : forall coin,
    schedule.challenges coin = coin.1
  scheduleRootsExact : forall coin reply,
    execution coin = some reply -> forall j : Fin m,
      schedule.rootsAt (j : Nat)
          (challengePrefix (schedule.challenges coin) j) =
        rootsBefore (clause := clause) reply.receipt j
  scheduleDomainExact : forall j,
    schedule.domainFor (schedule.phase j) =
      verifier.pins.challengeDomainId

namespace ActualReductionFamily

variable {radius : Nat -> Real} {tau : Real}
variable {certificate : FarWordSoundnessCertificate clause radius tau}
variable {Error : Type} {request : List UInt8}

/-- The false statement certified by the UD theorem, stated as a proposition
rather than confused with the certificate's proof field. -/
def FarInitial (clause : FriClause pcs m manifest) (radius : Nat -> Real) : Prop :=
  ¬close (radius 0)
    (reedSolomonCode (clause.tower.dom 0) (clause.degree 0))
    (clause.transcript.word 0 (fun i => i.elim0))

def ledger
    (family : ActualReductionFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request) :
    FailureLedger (IdealCoin clause) :=
  exactLedger family.baseLedger certificate

/-- False acceptance by the real bytes/decoder/checker path against the far
initial word certified for this exact clause. -/
def FalseAccept
    (family : ActualReductionFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    (coin : IdealCoin clause) : Prop :=
  exists reply, family.execution coin = some reply /\ FarInitial clause radius

theorem falseAccept_of_execution
    (family : ActualReductionFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    {coin : IdealCoin clause}
    {reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request}
    (selected : family.execution coin = some reply) :
    family.FalseAccept coin :=
  ⟨reply, selected, certificate.initialFar⟩

theorem execution_runner_bytes
    (family : ActualReductionFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    {coin : IdealCoin clause}
    {reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request}
    (selected : family.execution coin = some reply) :
    family.runner coin request = .ok reply.proofBytes :=
  run_success_runner_bytes (queryCount := queryCount) pcs clause verifier
    (family.runner coin) request reply
    (family.executionExact coin reply selected)

/-- Outside ROM transport failure, the common schedule's challenge vector is
literally the challenge vector decoded and accepted by the controller. -/
theorem schedule_challenges_eq_receipt
    (family : ActualReductionFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    {coin : IdealCoin clause}
    {reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request}
    (selected : family.execution coin = some reply)
    (transportGood : family.ledger.Good .oracleTransport coin) :
    family.schedule.challenges coin = reply.receipt.challenges := by
  rw [family.scheduleChallengesExact coin]
  exact (congrArg Prod.fst
    (family.transportExact coin reply selected transportGood)).symm

/-- The query half is equally exact; no independently sampled query vector is
smuggled into the ideal theorem. -/
theorem schedule_queries_eq_accepted
    (family : ActualReductionFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    {coin : IdealCoin clause}
    {reply : AcceptedReceipt (queryCount := queryCount)
      pcs clause verifier request}
    (selected : family.execution coin = some reply)
    (transportGood : family.ledger.Good .oracleTransport coin) :
    coin.2 = (acceptedIdealCoin reply).2 :=
  (congrArg Prod.snd
    (family.transportExact coin reply selected transportGood)).symm

/-- The real cover.  The additive branch is the exact Selvage acceptance event,
not an application-supplied proposition.  Commitment binding is already a
global premise of `pcs`; therefore this stronger cover needs only proximity or
oracle transport and embeds directly into the requested three-event envelope. -/
theorem falseAccept_three_event_cover
    (family : ActualReductionFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    (coin : IdealCoin clause) (accepted : family.FalseAccept coin) :
    (family.ledger .additiveProximity).event coin \/
      (family.ledger .commitmentBinding).event coin \/
      (family.ledger .oracleTransport).event coin := by
  obtain ⟨reply, selected, _far⟩ := accepted
  by_cases transportBad :
      (family.ledger .oracleTransport).event coin
  · exact Or.inr (Or.inr transportBad)
  · left
    have transported := family.transportExact coin reply selected transportBad
    rw [← transported]
    exact acceptedIdealCoin_accepts reply

/-- Embedding of the concrete two-event reduction into the exhaustive common
proof-composition ledger. -/
theorem falseAccept_bad
    (family : ActualReductionFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    (coin : IdealCoin clause) (accepted : family.FalseAccept coin) :
    family.ledger.Bad coin := by
  rcases family.falseAccept_three_event_cover coin accepted with
    proximity | binding | transport
  · exact Or.inr (Or.inr (Or.inr (Or.inl proximity)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl binding))))
  · exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl transport)))))

/-- The exact controller reduction inhabits the repository's common game. -/
def securityGame
    (family : ActualReductionFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request) :
    SecurityGame (IdealCoin clause) Digest (List UInt8) Tower256 Digest m where
  transcript := family.schedule
  ledger := family.ledger
  falseAccept := family.FalseAccept
  failureCover := family.falseAccept_bad

theorem falseAccept_le
    (family : ActualReductionFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request) :
    uniformProb (IdealCoin clause) family.FalseAccept <=
      family.ledger.total :=
  family.securityGame.falseAccept_le

theorem falseAccept_impossible_of_all_good
    (family : ActualReductionFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    {coin : IdealCoin clause}
    (good : forall failure, family.ledger.Good failure coin) :
    ¬family.FalseAccept coin :=
  family.securityGame.falseAccept_impossible_of_all_good good

end ActualReductionFamily

/-- info: 'Minidregg.Assurance.Tower256AdditiveFriActualReduction.additiveProximityFailure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms additiveProximityFailure
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriActualReduction.acceptedIdealCoin_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms acceptedIdealCoin_accepts
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriActualReduction.acceptedFinalReedSolomon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms acceptedFinalReedSolomon
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriActualReduction.concreteLevelPositionBinding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms concreteLevelPositionBinding
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriActualReduction.ActualReductionFamily.schedule_challenges_eq_receipt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ActualReductionFamily.schedule_challenges_eq_receipt
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriActualReduction.ActualReductionFamily.falseAccept_three_event_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ActualReductionFamily.falseAccept_three_event_cover
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriActualReduction.ActualReductionFamily.falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ActualReductionFamily.falseAccept_le

end

end Minidregg.Assurance.Tower256AdditiveFriActualReduction
