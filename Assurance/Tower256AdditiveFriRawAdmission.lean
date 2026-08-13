/-
# Assurance.Tower256AdditiveFriRawAdmission -- conditional additive Merkle binding

This module prices the raw additive controller on one common coin space.  It
constructs, rather than assumes, the false-accept cover:

* `additiveProximity` is exactly Selvage's ideal challenge/query acceptance event
  and is priced by `additiveFriAdaptive_coherent_sampled_sound_UD`;
* `commitmentBinding` is exactly an accepted controller receipt carrying a
  path-specific `ExtractedCollision` from the concrete Merkle checker; and
* `oracleTransport` is the only transcript-distribution residual, requiring
  equality between the Lean-derived accepted sample and the same game coin.

The collision event's probability bound remains an explicit CR premise on
this identical coin space.  No cSHAKE CR or ROM probability is claimed, and
native authority still ends at bytes/error.
-/

import Assurance.ProofCompositionGame
import Compiler.Tower256AdditiveFriRawController

namespace Minidregg.Assurance.Tower256AdditiveFriRawAdmission

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256AdditiveFriRawController
open Minidregg.Selvage
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

variable {ell m queryCount : Nat}
variable {pcs : RawMerklePcs ell}
variable {statement : Statement pcs m}
variable {verifier : Verifier (queryCount := queryCount) pcs statement}

local instance : Fintype Tower256 := Fintype.ofFinite _
local instance : DecidableEq Tower256 := Classical.decEq _

/-! ## Exact ideal sample and landed UD price -/

abbrev IdealCoin (statement : Statement pcs m) :=
  (Fin m -> Tower256) ×
    (Fin statement.queryCount -> PowerTwoFriLevels ell 1)

structure FarSoundnessCertificate
    (statement : Statement pcs m) (radius : Nat -> Real) (tau : Real) : Prop where
  tau_le_one : tau <= 1
  finalRadius_nonneg : 0 <= radius m
  radius_shrinks : forall j : Fin m, radius (j + 1) + tau <= radius j
  degree_halves : forall j : Fin m,
    statement.degree j = 2 * statement.degree (j + 1)
  foldedDegree_positive : forall j : Fin m, 0 < statement.degree (j + 1)
  roundRadius_positive : forall j : Fin m, 0 < radius j
  udBand : forall j : Fin m, radius j < 1 -
    (2 + (statement.degree (j + 1) : Real) /
      ((statement.tower.transversal j j.isLt).card : Real)) / 3
  initialFar : ¬close (radius 0)
    (reedSolomonCode (statement.tower.dom 0) (statement.degree 0))
    (statement.transcript.word 0 (fun i => i.elim0))

namespace FarSoundnessCertificate

def certify (statement : Statement pcs m) (radius : Nat -> Real) (tau : Real)
    (tau_le_one : tau <= 1)
    (finalRadius_nonneg : 0 <= radius m)
    (radius_shrinks : forall j : Fin m, radius (j + 1) + tau <= radius j)
    (degree_halves : forall j : Fin m,
      statement.degree j = 2 * statement.degree (j + 1))
    (foldedDegree_positive : forall j : Fin m,
      0 < statement.degree (j + 1))
    (roundRadius_positive : forall j : Fin m, 0 < radius j)
    (udBand : forall j : Fin m, radius j < 1 -
      (2 + (statement.degree (j + 1) : Real) /
        ((statement.tower.transversal j j.isLt).card : Real)) / 3)
    (initialFar : ¬close (radius 0)
      (reedSolomonCode (statement.tower.dom 0) (statement.degree 0))
      (statement.transcript.word 0 (fun i => i.elim0))) :
    FarSoundnessCertificate statement radius tau where
  tau_le_one := tau_le_one
  finalRadius_nonneg := finalRadius_nonneg
  radius_shrinks := radius_shrinks
  degree_halves := degree_halves
  foldedDegree_positive := foldedDegree_positive
  roundRadius_positive := roundRadius_positive
  udBand := udBand
  initialFar := initialFar

theorem ideal_accept_le
    {radius : Nat -> Real} {tau : Real}
    (certificate : FarSoundnessCertificate statement radius tau) :
    uniformProb (IdealCoin statement)
        (fun coin => IdealAccept statement coin.1 coin.2) <=
      (m : Real) * (2 ^ (ell - 1) : Nat) /
        (Fintype.card Tower256 : Real) +
        (1 - tau) ^ statement.queryCount := by
  exact additiveFriAdaptive_coherent_sampled_sound_UD statement.tower
    (fun n => idealCommitment Tower256 (AdditiveFriLevels ell n))
    statement.degree statement.transcript.toIdeal radius statement.queryCount
    certificate.tau_le_one certificate.finalRadius_nonneg
    certificate.radius_shrinks certificate.degree_halves
    certificate.foldedDegree_positive certificate.roundRadius_positive
    certificate.udBand certificate.initialFar

end FarSoundnessCertificate

/-! ## Raw byte execution and exact collision event -/

def rootsBefore (statement : Statement pcs m)
    (receipt : Receipt ell m queryCount) (j : Fin m) : List Digest :=
  List.ofFn fun n : Fin ((j : Nat) + 1) =>
    have hn : (n : Nat) <= m := by omega
    statement.transcript.rootAt receipt.challenges n hn

structure RawGameFamily
    {radius : Nat -> Real} {tau : Real}
    (certificate : FarSoundnessCertificate statement radius tau)
    (Error : Type) (request : List UInt8) where
  baseLedger : FailureLedger (IdealCoin statement)
  schedule : SharedOracleSchedule (IdealCoin statement) Digest (List UInt8)
    Tower256 Digest m
  execution : IdealCoin statement -> Option
    (Minidregg.Compiler.Tower256AdditiveFriRawController.AcceptedReceipt
      (queryCount := queryCount) pcs statement verifier request)
  runner : IdealCoin statement ->
    Minidregg.Compiler.Tower256AdditiveFriRawController.OpaqueProofRunner Error
  executionExact : forall coin reply,
    execution coin = some reply ->
      Minidregg.Compiler.Tower256AdditiveFriRawController.run
        (queryCount := queryCount) pcs statement verifier
        (runner coin) request = Except.ok reply
  /-- Exact CR price premise: the event is fixed below from accepted receipt
  paths and `ExtractedCollision`, not selected by the caller. -/
  collisionPrice : Real
  collisionBound : uniformProb (IdealCoin statement) (fun coin =>
    exists reply, execution coin = some reply /\
      ReceiptCollision pcs statement reply.receipt) <= collisionPrice
  /-- Exact ROM residual on the same coin.  Any ideal witness extracted from
  accepted bytes must equal the game's challenge/query sample. -/
  transportExact : forall coin reply querySeed,
    execution coin = some reply ->
    IdealAccept statement reply.receipt.challenges querySeed ->
    baseLedger.Good .oracleTransport coin ->
    (reply.receipt.challenges, querySeed) = coin
  scheduleChallengesExact : forall coin,
    schedule.challenges coin = coin.1
  scheduleRootsExact : forall coin reply,
    execution coin = some reply -> forall j : Fin m,
      schedule.rootsAt (j : Nat)
          (challengePrefix (schedule.challenges coin) j) =
        rootsBefore statement reply.receipt j
  scheduleDomainExact : forall j,
    schedule.domainFor (schedule.phase j) = verifier.pins.challengeDomainId

namespace RawGameFamily

variable {radius : Nat -> Real} {tau : Real}
variable {certificate : FarSoundnessCertificate statement radius tau}
variable {Error : Type} {request : List UInt8}

def CollisionEvent
    (family : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    (coin : IdealCoin statement) : Prop :=
  exists reply, family.execution coin = some reply /\
    ReceiptCollision pcs statement reply.receipt

def additiveFailure
    (_family : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request) :
    PricedFailure (IdealCoin statement) where
  event := fun coin => IdealAccept statement coin.1 coin.2
  price := (m : Real) * (2 ^ (ell - 1) : Nat) /
      (Fintype.card Tower256 : Real) +
      (1 - tau) ^ statement.queryCount
  bound := certificate.ideal_accept_le

def collisionFailure
    (family : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request) :
    PricedFailure (IdealCoin statement) where
  event := family.CollisionEvent
  price := family.collisionPrice
  bound := family.collisionBound

/-- The common ledger with exact additive and collision events. -/
def ledger
    (family : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request) :
    FailureLedger (IdealCoin statement)
  | .additiveProximity => family.additiveFailure
  | .commitmentBinding => family.collisionFailure
  | .logupAlgebra => family.baseLedger .logupAlgebra
  | .logupPcs => family.baseLedger .logupPcs
  | .historyPcs => family.baseLedger .historyPcs
  | .oracleTransport => family.baseLedger .oracleTransport
  | .oracleLog => family.baseLedger .oracleLog
  | .zeroKnowledge => family.baseLedger .zeroKnowledge

def FalseAccept
    (family : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    (coin : IdealCoin statement) : Prop :=
  exists reply, family.execution coin = some reply

theorem execution_runner_bytes
    (family : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    {coin : IdealCoin statement}
    {reply : Minidregg.Compiler.Tower256AdditiveFriRawController.AcceptedReceipt
      (queryCount := queryCount) pcs statement verifier request}
    (selected : family.execution coin = some reply) :
    family.runner coin request = Except.ok reply.proofBytes :=
  (Minidregg.Compiler.Tower256AdditiveFriRawController.run_success_integrity
    pcs statement verifier (family.runner coin) request
    reply (family.executionExact coin reply selected)).1

/-- The actual raw-controller cover: ideal proximity, extracted collision, or
same-coin ROM transport failure. -/
theorem falseAccept_three_event_cover
    (family : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    (coin : IdealCoin statement) (accepted : family.FalseAccept coin) :
    (family.ledger .additiveProximity).event coin \/
      (family.ledger .commitmentBinding).event coin \/
      (family.ledger .oracleTransport).event coin := by
  obtain ⟨reply, selected⟩ := accepted
  rcases accepts_ideal_or_receiptCollision pcs statement verifier.pins
      reply.receipt reply.accepted with collision | ⟨querySeed, ideal⟩
  · exact Or.inr (Or.inl ⟨reply, selected, collision⟩)
  · by_cases transportBad :
        (family.baseLedger .oracleTransport).event coin
    · exact Or.inr (Or.inr transportBad)
    · left
      have transported := family.transportExact coin reply querySeed selected
        ideal transportBad
      rw [← transported]
      exact ideal

theorem falseAccept_bad
    (family : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request)
    (coin : IdealCoin statement) (accepted : family.FalseAccept coin) :
    family.ledger.Bad coin := by
  rcases family.falseAccept_three_event_cover coin accepted with
    proximity | collision | transport
  · exact Or.inr (Or.inr (Or.inr (Or.inl proximity)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl collision))))
  · exact Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl transport)))))

def securityGame
    (family : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request) :
    SecurityGame (IdealCoin statement) Digest (List UInt8) Tower256 Digest m where
  transcript := family.schedule
  ledger := family.ledger
  falseAccept := family.FalseAccept
  failureCover := family.falseAccept_bad

theorem falseAccept_le
    (family : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request) :
    uniformProb (IdealCoin statement) family.FalseAccept <=
      family.ledger.total :=
  family.securityGame.falseAccept_le

end RawGameFamily

/-- info: 'Minidregg.Assurance.Tower256AdditiveFriRawAdmission.FarSoundnessCertificate.ideal_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FarSoundnessCertificate.ideal_accept_le
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriRawAdmission.RawGameFamily.execution_runner_bytes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RawGameFamily.execution_runner_bytes
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriRawAdmission.RawGameFamily.falseAccept_three_event_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RawGameFamily.falseAccept_three_event_cover
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriRawAdmission.RawGameFamily.falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RawGameFamily.falseAccept_le

end

end Minidregg.Assurance.Tower256AdditiveFriRawAdmission
