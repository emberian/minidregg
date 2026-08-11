/-
# Assurance.Tower256AdditiveFriCanonicalExecutionGame -- exact transport event

`Tower256AdditiveFriRawAdmission.RawGameFamily` correctly leaves random-oracle
transport as a residual, but its `transportExact` field quantifies over an
arbitrary ideal query witness.  The raw controller already contains a more
canonical object: every accepted receipt carries its own challenge vector and
query vector.  This module makes that object the comparison coin.

For an arbitrary coin-indexed opaque runner, Lean executes the actual raw
controller and classifies every successful receipt into exactly one of:

* ideal additive acceptance at the receipt-derived coin;
* an exact path-specific cSHAKE/Merkle collision extracted from that receipt;
* a literal mismatch between the receipt-derived coin and the external game
  coin.

The mismatch event is therefore constructed, not selected by a caller.  Its
probability remains an explicit ROM/transcript premise, just as the extracted
collision event retains an explicit CR price.  No distribution theorem is
invented here.
-/

import Assurance.Tower256AdditiveFriRawAdmission
import Compiler.Tower256AdditiveFriRawDeployment

namespace Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.Tower256AdditiveFriRawAdmission
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256AdditiveFriRawController
open Minidregg.Loom

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

variable {ell m queryCount : Nat}
variable {pcs : RawMerklePcs ell}
variable {statement : Statement pcs m}
variable {verifier :
  Minidregg.Compiler.Tower256AdditiveFriRawController.Verifier
    (queryCount := queryCount) pcs statement}
variable {Error : Type} {request : List UInt8}

local instance : Fintype Tower256 := Fintype.ofFinite _
local instance : DecidableEq Tower256 := Classical.decEq _

local notation "Coin" => IdealCoin statement
local notation "Reply" =>
  Minidregg.Compiler.Tower256AdditiveFriRawController.AcceptedReceipt
    (queryCount := queryCount) pcs statement verifier request
local notation "Runner" =>
  Minidregg.Compiler.Tower256AdditiveFriRawController.OpaqueProofRunner Error

/-- The exact ideal query vector carried by an accepted receipt.  The
controller's first acceptance conjunct supplies the only cast involved. -/
def idealQuerySeed (reply : Reply) :
    Fin statement.queryCount -> PowerTwoFriLevels ell 1 :=
  fun index => reply.receipt.querySeed (Fin.cast reply.accepted.1.symm index)

/-- The canonical ideal coin read from the Lean-accepted receipt. -/
def idealCoin (reply : Reply) : Coin :=
  (reply.receipt.challenges, idealQuerySeed reply)

@[simp] theorem idealCoin_challenges (reply : Reply) :
    (idealCoin reply).1 = reply.receipt.challenges := rfl

/-! ## The controller's canonical ideal witness -/

/-- Raw acceptance reaches ideal acceptance at the receipt's OWN query vector,
unless the same receipt exposes an extracted Merkle collision.  This is the
canonical strengthening of `accepts_ideal_or_receiptCollision`: it does not
return an arbitrary existential query witness. -/
theorem accepts_idealAtReceipt_or_collision
    (receipt : Receipt ell m queryCount)
    (accepted : Accepts pcs statement verifier.pins receipt) :
    ReceiptCollision pcs statement receipt ∨
      IdealAccept statement receipt.challenges
        (fun index => receipt.querySeed (Fin.cast accepted.1.symm index)) := by
  by_cases collision : ReceiptCollision pcs statement receipt
  · exact Or.inl collision
  · right
    have queryCountExact := accepted.1
    subst queryCount
    constructor
    · intro j
      refine ⟨fun a =>
        { left := statement.transcript.wordAt receipt.challenges j
            (Nat.le_of_lt j.isLt)
            (statement.tower.liftBit j j.isLt 0
              (additiveCoherentRound statement.tower.rounds_le j
                receipt.querySeed a))
          right := statement.transcript.wordAt receipt.challenges j
            (Nat.le_of_lt j.isLt)
            (statement.tower.liftBit j j.isLt 1
              (additiveCoherentRound statement.tower.rounds_le j
                receipt.querySeed a))
          next := statement.transcript.wordAt receipt.challenges (j + 1)
            (Nat.succ_le_iff.mpr j.isLt)
            (additiveCoherentRound statement.tower.rounds_le j
              receipt.querySeed a)
          leftPath := ()
          rightPath := ()
          nextPath := () }, ?_⟩
      intro a
      have literal := accepted_query_pins_or_collision pcs statement
        verifier.pins receipt accepted j a
      rcases literal with literal | queryCollision
      · exact ⟨rfl, rfl, rfl, literal⟩
      · exact False.elim (collision ⟨j, a, queryCollision⟩)
    · apply mem_reedSolomonCode_iff.mpr
      exact ⟨receipt.finalPolynomial, accepted.2.2.2.2.1,
        accepted.2.2.2.2.2⟩

theorem reply_idealAtOwnCoin_or_collision (reply : Reply) :
    ReceiptCollision pcs statement reply.receipt ∨
      IdealAccept statement (idealCoin reply).1 (idealCoin reply).2 := by
  simpa only [idealCoin, idealQuerySeed] using
    accepts_idealAtReceipt_or_collision (verifier := verifier)
      reply.receipt reply.accepted

/-! ## Actual raw execution, not a selected Option -/

/-- Evaluate the exact raw controller and retain only its successful reply. -/
def execute
    (runner : Coin -> Runner) (coin : Coin) : Option Reply :=
  match Minidregg.Compiler.Tower256AdditiveFriRawController.run
      (queryCount := queryCount) pcs statement verifier
      (runner coin) request with
  | .ok reply => some reply
  | .error _ => none

theorem execute_eq_some_iff
    (runner : Coin -> Runner) (coin : Coin) (reply : Reply) :
    execute (pcs := pcs) (statement := statement) (verifier := verifier)
        (request := request) runner coin = some reply <->
      Minidregg.Compiler.Tower256AdditiveFriRawController.run
        (queryCount := queryCount) pcs statement verifier
        (runner coin) request = .ok reply := by
  unfold execute
  split <;> simp_all

/-! ## Exact three-event ledger -/

inductive FailureClass where
  | additiveProximity
  | extractedCshakeCollision
  | oracleTransport
deriving DecidableEq, Fintype, Repr

local notation "ExactLedger" => FailureClass -> PricedFailure Coin

namespace ExactLedgerOps

def Bad (ledger : ExactLedger) (coin : Coin) : Prop :=
  (ledger .additiveProximity).event coin ∨
  (ledger .extractedCshakeCollision).event coin ∨
  (ledger .oracleTransport).event coin

def Price (ledger : ExactLedger) : Real :=
  (ledger .additiveProximity).price +
  (ledger .extractedCshakeCollision).price +
  (ledger .oracleTransport).price

theorem bad_le_price (ledger : ExactLedger) :
    uniformProb Coin (Bad ledger) <= Price ledger := by
  have outer := uniformProb_or_le
    (ledger .additiveProximity).event (fun coin =>
      (ledger .extractedCshakeCollision).event coin ∨
      (ledger .oracleTransport).event coin)
  have inner := uniformProb_or_le
    (ledger .extractedCshakeCollision).event
    (ledger .oracleTransport).event
  unfold Bad Price
  linarith [(ledger .additiveProximity).bound,
    (ledger .extractedCshakeCollision).bound,
    (ledger .oracleTransport).bound]

end ExactLedgerOps

/-- The only probabilistic inputs.  Every event is fixed below; callers can
only supply bounds for those exact sets. -/
structure PriceCertificate
    (runner : Coin -> Runner) where
  proximityPrice : Real
  proximityBound : uniformProb Coin
    (fun coin => IdealAccept statement coin.1 coin.2) <= proximityPrice
  collisionPrice : Real
  collisionBound : uniformProb Coin (fun coin =>
    exists reply,
      execute (pcs := pcs) (statement := statement) (verifier := verifier)
        (request := request) runner coin = some reply /\
      ReceiptCollision pcs statement reply.receipt) <= collisionPrice
  transportPrice : Real
  transportBound : uniformProb Coin (fun coin =>
    exists reply,
      execute (pcs := pcs) (statement := statement) (verifier := verifier)
        (request := request) runner coin = some reply /\
      idealCoin reply ≠ coin) <= transportPrice

def rawExactThreeLedger {runner : Coin -> Runner}
    (prices : PriceCertificate (pcs := pcs) (statement := statement)
    (verifier := verifier) (request := request) runner)
    (failure : FailureClass) : PricedFailure Coin :=
  match failure with
  | .additiveProximity =>
      { event := fun coin => IdealAccept statement coin.1 coin.2
        price := prices.proximityPrice
        bound := prices.proximityBound }
  | .extractedCshakeCollision =>
      { event := fun coin => exists reply,
          execute (pcs := pcs) (statement := statement) (verifier := verifier)
            (request := request) runner coin = some reply /\
          ReceiptCollision pcs statement reply.receipt
        price := prices.collisionPrice
        bound := prices.collisionBound }
  | .oracleTransport =>
      { event := fun coin => exists reply,
          execute (pcs := pcs) (statement := statement) (verifier := verifier)
            (request := request) runner coin = some reply /\
          idealCoin reply ≠ coin
        price := prices.transportPrice
        bound := prices.transportBound }

def rawFalseAcceptEvent {runner : Coin -> Runner}
    (_prices : PriceCertificate (pcs := pcs) (statement := statement)
    (verifier := verifier) (request := request) runner) (coin : Coin) : Prop :=
  exists reply,
    execute (pcs := pcs) (statement := statement) (verifier := verifier)
      (request := request) runner coin = some reply

/-- Every actual raw-controller success is covered without an abstract
`transportExact` field.  The transport branch is literal coin inequality. -/
theorem falseAccept_three_event_cover
    {runner : Coin -> Runner}
    (prices : PriceCertificate (pcs := pcs) (statement := statement)
      (verifier := verifier) (request := request) runner)
    (coin : Coin) (accepted : rawFalseAcceptEvent prices coin) :
    (rawExactThreeLedger prices .additiveProximity).event coin ∨
      (rawExactThreeLedger prices .extractedCshakeCollision).event coin ∨
      (rawExactThreeLedger prices .oracleTransport).event coin := by
  obtain ⟨reply, selected⟩ := accepted
  rcases reply_idealAtOwnCoin_or_collision reply with collision | ideal
  · exact Or.inr (Or.inl ⟨reply, selected, collision⟩)
  · by_cases aligned : idealCoin reply = coin
    · left
      change IdealAccept statement coin.1 coin.2
      rwa [← aligned]
    · exact Or.inr (Or.inr ⟨reply, selected, aligned⟩)

theorem falseAccept_bad
    {runner : Coin -> Runner}
    (prices : PriceCertificate (pcs := pcs) (statement := statement)
      (verifier := verifier) (request := request) runner)
    (coin : Coin) (accepted : rawFalseAcceptEvent prices coin) :
    ExactLedgerOps.Bad (rawExactThreeLedger prices) coin :=
  falseAccept_three_event_cover prices coin accepted

/-- Honest end-to-end bound: additive proximity plus the explicitly supplied
CR and exact receipt-coin mismatch prices. -/
theorem falseAccept_le
    {runner : Coin -> Runner}
    (prices : PriceCertificate (pcs := pcs) (statement := statement)
      (verifier := verifier) (request := request) runner) :
    uniformProb Coin (rawFalseAcceptEvent prices) <=
      ExactLedgerOps.Price (rawExactThreeLedger prices) :=
  le_trans (uniformProb_mono (falseAccept_bad prices))
    (ExactLedgerOps.bad_le_price (rawExactThreeLedger prices))

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.accepts_idealAtReceipt_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepts_idealAtReceipt_or_collision
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.falseAccept_three_event_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms falseAccept_three_event_cover
/-- info: 'Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame.falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms falseAccept_le

end

end Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame
