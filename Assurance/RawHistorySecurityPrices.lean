/-
# Assurance.RawHistorySecurityPrices -- honest prices for raw cSHAKE/history events

The raw history and additive controllers already retain exact path-specific
Merkle/cSHAKE collision witnesses and exact receipt-coin mismatch predicates.
Those deterministic reductions do not, by themselves, give a probability.
This file states and proves the strongest probability adapters supported by
the repository's landed ROM APIs.

There are two intentionally sharp conclusions.

* A raw extracted collision is reduced to the exact `MerkleCollision`
  predicate used by the concrete cSHAKE backend.  To apply the landed birthday
  theorem on the SAME finite game coin, an execution must additionally expose
  an exact uniform projection to its bounded vector of fresh ROM answers and
  prove that every extracted collision is a collision in that vector.
  `CollisionRomRealization` is precisely that missing trace theorem; its price
  is then derived, not supplied.
* Exact receipt-coin transport in the ideal ROM makes the literal mismatch
  event impossible and therefore costs zero.  Merely showing that two coin
  projections have uniform marginals is insufficient: the two-point
  anti-correlated coupling below has two exact uniform marginals and mismatches
  with probability one.  A future raw-history FS execution must therefore
  prove pointwise receipt-coin equality from its shared trace.  Sponge
  indifferentiability, once connected to concrete cSHAKE, belongs outside that
  ideal same-coin equality as a real-vs-ideal advantage term.

No collision-resistance number, independence premise, or cSHAKE-to-ROM theorem
is postulated here.  The only positive collision price is the existing
`birthday_bound_pow`, transported through an exact `UniformProjection`.
-/

import Assurance.SameCoinGameProduct
import Assurance.Tower256RawSemanticHistoryCanonicalGame
import Loom.CollisionResistanceROM

namespace Minidregg.Assurance.RawHistorySecurityPrices

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.RawSemanticHistoryCheckpointGame
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SameCoinGameProduct
open Minidregg.Assurance.Tower256AdditiveFriRawAdmission
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256AdditiveFriRawController
open Minidregg.Compiler.Tower256CshakeMerkleBinding
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Loom

set_option autoImplicit false

noncomputable section

/-! ## Exact deterministic collision endpoints -/

/-- Every path-specific extractor result contains the exact leaf-or-node
framed cSHAKE collision.  This projection forgets the paths, not the collision
inputs, customizations, or unequal-input proof retained by `MerkleCollision`.
-/
theorem merkleCollision_of_extractedCollision
    {Semantic Representation : Type} {k : Nat}
    {cshake : Cshake256} {domains : MerkleDomains cshake}
    {port : ColumnPort Semantic Representation (Fin (2 ^ k))}
    {attempt : OpeningPair Representation (Fin (2 ^ k))}
    (extracted : ExtractedCollision domains port attempt) :
    MerkleCollision domains port.representationCodec := by
  rcases extracted with
    ⟨_leftPath, _rightPath, _leftDecoded, _leftLength, _leftRoot,
      _rightDecoded, _rightLength, _rightRoot, _different, collision⟩
  exact collision

/-- A raw additive receipt collision reaches one collision predicate for the
single cSHAKE/Merkle backend shared by every level.  The level and submitted
opening remain present in the source witness; the endpoint uses the backend's
literal Tower256 codec, definitionally the codec of every level port. -/
theorem merkleCollision_of_receiptCollision
    {ell m queryCount : Nat} {pcs : RawMerklePcs ell}
    {statement : Statement pcs m} {receipt : Receipt ell m queryCount}
    (collision : ReceiptCollision pcs statement receipt) :
    MerkleCollision pcs.backend.merkle pcs.backend.tower.valueCodec := by
  rcases collision with ⟨j, a, low | high | next⟩
  · exact merkleCollision_of_extractedCollision low
  · exact merkleCollision_of_extractedCollision high
  · exact merkleCollision_of_extractedCollision next

/-! ### Retained raw-history specialization -/

universe uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome

abbrev TowerField :=
  Minidregg.Compiler.BinaryTower256Profile.Tower256

local instance : DecidableEq TowerField := Classical.decEq _
local instance : Fintype TowerField := Fintype.ofFinite _

variable {ell m n : Nat}
variable {pcs : RawMerklePcs ell} {statement : Statement pcs m}
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n TowerField}
    {headerCells : HistoryAdmissionContext -> BindingIx -> TowerField}
    {C : Submodule TowerField (BoundReceiptIx n -> TowerField)}
    {idealS : BindingCommitment
      Minidregg.Theory.TypedAuthorization.Digest TowerField
      (BoundReceiptIx n) (List UInt8)}

local notation "BoundCheckpoint" => RawCheckpoint
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS)

/-- The retained-history collision witness reaches the same concrete Merkle
collision predicate as the additive receipt witness.  It does not turn that
fixed predicate into a birthday-priced event; the outcome-tied ROM trace is
still required by `CollisionRomRealization`. -/
theorem merkleCollision_of_extractedHistoryCollision
    {checkpoint : BoundCheckpoint}
    {domain : BoundReceiptIx n ↪ TowerField}
    {degree openedCount : Nat}
    {transcript : CheckpointHistoryTranscript
      (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      checkpoint domain degree openedCount}
    (collision :
      CheckpointHistoryTranscript.ExtractedHistoryCollision
        (ell := ell) (pcs := pcs) (checkpoint := checkpoint) transcript) :
    MerkleCollision pcs.backend.merkle pcs.backend.tower.valueCodec := by
  rcases collision with
    ⟨_j, _i, _attempt, _root, _index, _left, _right, extracted⟩
  exact merkleCollision_of_extractedCollision extracted

/-! ## The exact same-coin birthday adapter -/

/-- The minimum trace theorem needed to price an outcome-tied raw collision
event by the landed ROM birthday theorem.

`answers` is not a caller-selected probability bound.  Its
`probabilityExact` field states that the answer vector is an exact uniform
marginal of this SAME `Omega`, for every event.  `extracts` is the missing
execution/query-log theorem: an actual raw collision outcome names two
different fresh-query slots whose ROM answers agree.

No fixed/non-adaptive query schedule is assumed here.  Query adaptivity is
handled before this interface: once an execution proves that its distinct
fresh query slots consume the projected uniform answer vector, the birthday
event depends only on that vector. -/
structure CollisionRomRealization
    (Omega : Type) [Fintype Omega]
    (queryBudget outputBits : Nat) (collisionEvent : Omega -> Prop) where
  answers : UniformProjection Omega
    (Fin queryBudget -> Fin (2 ^ outputBits))
  extracts : forall omega, collisionEvent omega ->
    Collides (answers.map omega)

namespace CollisionRomRealization

variable {Omega : Type} [Fintype Omega]
variable {queryBudget outputBits : Nat} {collisionEvent : Omega -> Prop}

/-- The raw collision event inherits the exact ROM birthday price.  This is
the only numeric collision bound in this module, and it is the repository's
already-proved `birthday_bound_pow`. -/
theorem event_le_birthday
    (realization : CollisionRomRealization Omega queryBudget outputBits
      collisionEvent) :
    uniformProb Omega collisionEvent <=
      (queryBudget : Real) * ((queryBudget : Real) - 1) /
        (2 ^ (outputBits + 1) : Real) := by
  calc
    uniformProb Omega collisionEvent <=
        uniformProb Omega
          (fun omega => Collides (realization.answers.map omega)) :=
      uniformProb_mono realization.extracts
    _ = uniformProb (Fin queryBudget -> Fin (2 ^ outputBits)) Collides :=
      realization.answers.probabilityExact Collides
    _ = collisionProb queryBudget (2 ^ outputBits) := rfl
    _ <= (queryBudget : Real) * ((queryBudget : Real) - 1) /
        (2 ^ (outputBits + 1) : Real) :=
      birthday_bound_pow queryBudget outputBits

/-- Package the derived birthday theorem as the exact `PricedFailure` shape
consumed by the raw joint ledger. -/
def pricedFailure
    (realization : CollisionRomRealization Omega queryBudget outputBits
      collisionEvent) : PricedFailure Omega where
  event := collisionEvent
  price := (queryBudget : Real) * ((queryBudget : Real) - 1) /
    (2 ^ (outputBits + 1) : Real)
  bound := realization.event_le_birthday

end CollisionRomRealization

/-! ## Exact common-coin transport to a native FS experiment -/

/-- The exact pair of lazy-ROM tapes consumed by the landed straightline
Fiat--Shamir theorem: adversarial query answers, then the final challenge
answers which were not already present in the query log. -/
abbrev NativeFsCoins (Challenge : Type) (queryBudget finalBudget : Nat) :=
  (Fin queryBudget -> Challenge) × (Fin finalBudget -> Challenge)

/-- A common execution coin realizes the native FS coin pair as an exact
uniform marginal.  This is the generic signature expected from
`raw_history_fs_execution`: its concrete `queryCoins` and `finalCoins` form
`coins`, and `probabilityExact` proves the distributional bridge for every
native event. -/
structure NativeFsCoinRealization
    (Omega Challenge : Type) [Fintype Omega] [Fintype Challenge]
    (queryBudget finalBudget : Nat) where
  queryCoins : Omega -> Fin queryBudget -> Challenge
  finalCoins : Omega -> Fin finalBudget -> Challenge
  probabilityExact : forall event :
      NativeFsCoins Challenge queryBudget finalBudget -> Prop,
    uniformProb Omega
        (fun omega => event (queryCoins omega, finalCoins omega)) =
      uniformProb (NativeFsCoins Challenge queryBudget finalBudget) event

namespace NativeFsCoinRealization

variable {Omega Challenge : Type} [Fintype Omega] [Fintype Challenge]
variable {queryBudget finalBudget : Nat}

/-- Expose the native tape pair as the repository-wide exact uniform
projection carrier. -/
def projection
    (realization : NativeFsCoinRealization Omega Challenge
      queryBudget finalBudget) :
    UniformProjection Omega
      (NativeFsCoins Challenge queryBudget finalBudget) where
  map := fun omega =>
    (realization.queryCoins omega, realization.finalCoins omega)
  probabilityExact := realization.probabilityExact

/-- Any already-proved native FS event bound transfers to the same `Omega`
without a new price or independence premise. -/
theorem event_le_of_native
    (realization : NativeFsCoinRealization Omega Challenge
      queryBudget finalBudget)
    (event : NativeFsCoins Challenge queryBudget finalBudget -> Prop)
    (price : Real)
    (nativeBound :
      uniformProb (NativeFsCoins Challenge queryBudget finalBudget) event <=
        price) :
    uniformProb Omega
        (fun omega => event
          (realization.queryCoins omega, realization.finalCoins omega)) <=
      price := by
  rw [realization.probabilityExact event]
  exact nativeBound

end NativeFsCoinRealization

/-! ## Exact ideal receipt-coin transport -/

/-- The literal mismatch predicate used by a receipt-carrying controller:
execution succeeds, but the coin reconstructed from the accepted receipt is
not the game coin selected on the same outcome. -/
def ReceiptCoinMismatch
    {Omega Coin Reply : Type}
    (execute : Omega -> Option Reply) (receiptCoin : Reply -> Coin)
    (gameCoin : Omega -> Coin) (omega : Omega) : Prop :=
  exists reply, execute omega = some reply /\
    receiptCoin reply ≠ gameCoin omega

/-- The exact ideal-ROM transport obligation.  A raw-history FS execution
should prove this from its single query trace and accepted receipt, rather
than assign a probability to an unrelated caller-selected predicate. -/
structure ExactReceiptCoinRealization
    {Omega Coin Reply : Type}
    (execute : Omega -> Option Reply) (receiptCoin : Reply -> Coin)
    (gameCoin : Omega -> Coin) : Prop where
  exact : forall omega reply, execute omega = some reply ->
    receiptCoin reply = gameCoin omega

namespace ExactReceiptCoinRealization

variable {Omega Coin Reply : Type}
variable {execute : Omega -> Option Reply} {receiptCoin : Reply -> Coin}
variable {gameCoin : Omega -> Coin}

/-- Exact ideal receipt-coin realization eliminates the pointwise transport
event. -/
theorem not_mismatch
    (realization : ExactReceiptCoinRealization execute receiptCoin gameCoin)
    (omega : Omega) :
    ¬ReceiptCoinMismatch execute receiptCoin gameCoin omega := by
  rintro ⟨reply, executed, unequal⟩
  exact unequal (realization.exact omega reply executed)

/-- Consequently the ideal same-coin transport price is exactly zero. -/
theorem mismatch_probability_zero [Fintype Omega]
    (realization : ExactReceiptCoinRealization execute receiptCoin gameCoin) :
    uniformProb Omega (ReceiptCoinMismatch execute receiptCoin gameCoin) = 0 :=
  uniformProb_false realization.not_mismatch

/-- The zero-cost ledger entry is constructible only from pointwise exactness.
No cryptographic real-vs-ideal claim is hidden in this constructor. -/
def zeroPricedFailure [Fintype Omega]
    (realization : ExactReceiptCoinRealization execute receiptCoin gameCoin) :
    PricedFailure Omega where
  event := ReceiptCoinMismatch execute receiptCoin gameCoin
  price := 0
  bound := le_of_eq realization.mismatch_probability_zero

end ExactReceiptCoinRealization

/-! ## Exact history root attribution -/

/-- The exact missing-attribution event before it is intersected with a
false-statement predicate. -/
def MissingRootAttribution
    {Omega Tape : Type} (run : Omega -> Option Tape)
    (rootPreimage : Tape -> Prop) (omega : Omega) : Prop :=
  exists tape, run omega = some tape /\ ¬rootPreimage tape

/-- An ideal raw-history execution must show that every returned tape's root
is the selected semantic checkpoint root.  This is a pointwise trace theorem,
not a cryptographic probability. -/
structure ExactRootAttribution
    {Omega Tape : Type} (run : Omega -> Option Tape)
    (rootPreimage : Tape -> Prop) : Prop where
  exact : forall omega tape, run omega = some tape -> rootPreimage tape

namespace ExactRootAttribution

variable {Omega Tape : Type} {run : Omega -> Option Tape}
variable {rootPreimage : Tape -> Prop}

theorem not_missing
    (realization : ExactRootAttribution run rootPreimage) (omega : Omega) :
    ¬MissingRootAttribution run rootPreimage omega := by
  rintro ⟨tape, executed, missing⟩
  exact missing (realization.exact omega tape executed)

theorem missing_probability_zero [Fintype Omega]
    (realization : ExactRootAttribution run rootPreimage) :
    uniformProb Omega (MissingRootAttribution run rootPreimage) = 0 :=
  uniformProb_false realization.not_missing

def zeroPricedFailure [Fintype Omega]
    (realization : ExactRootAttribution run rootPreimage) :
    PricedFailure Omega where
  event := MissingRootAttribution run rootPreimage
  price := 0
  bound := le_of_eq realization.missing_probability_zero

end ExactRootAttribution

/-! ## Canonical raw-additive receipt-coin specialization -/

namespace CanonicalReceiptTransport

open Minidregg.Assurance.Tower256AdditiveFriCanonicalExecutionGame

local instance : Fintype Tower256 := Fintype.ofFinite _
local instance : DecidableEq Tower256 := Classical.decEq _

variable {ell m queryCount : Nat}
variable {pcs : RawMerklePcs ell} {statement : Statement pcs m}
variable {verifier : Verifier (queryCount := queryCount) pcs statement}
variable {Error : Type} {request : List UInt8}

local notation "Coin" => IdealCoin statement
local notation "Reply" => AcceptedReceipt
  (queryCount := queryCount) pcs statement verifier request
local notation "Runner" =>
  Minidregg.Compiler.Tower256AdditiveFriRawController.OpaqueProofRunner Error

/-- The canonical controller's literal transport predicate is exactly the
generic receipt-coin mismatch on the identity game coin. -/
theorem event_iff_mismatch (runner : Coin -> Runner) (coin : Coin) :
    (exists reply,
      execute (pcs := pcs) (statement := statement) (verifier := verifier)
        (request := request) runner coin = some reply /\
      idealCoin reply ≠ coin) ↔
    ReceiptCoinMismatch
      (execute (pcs := pcs) (statement := statement) (verifier := verifier)
        (request := request) runner)
      idealCoin id coin :=
  Iff.rfl

/-- Exact shared-trace receipt reconstruction gives the canonical transport
event price zero.  This is the exact theorem signature the ideal raw FS
execution should target. -/
theorem mismatch_probability_zero
    (runner : Coin -> Runner)
    (receiptCoinExact : forall coin reply,
      execute (pcs := pcs) (statement := statement) (verifier := verifier)
        (request := request) runner coin = some reply ->
      idealCoin reply = coin) :
    uniformProb Coin (fun coin => exists reply,
      execute (pcs := pcs) (statement := statement) (verifier := verifier)
        (request := request) runner coin = some reply /\
      idealCoin reply ≠ coin) = 0 := by
  let realization : ExactReceiptCoinRealization
      (execute (pcs := pcs) (statement := statement) (verifier := verifier)
        (request := request) runner)
      idealCoin id := ⟨receiptCoinExact⟩
  exact realization.mismatch_probability_zero

end CanonicalReceiptTransport

/-! ## Teeth: uniform marginals do not couple two transcripts -/

namespace MarginalTransportTooth

/-- A uniform projection induced by a finite equivalence. -/
def projectionOfEquiv {A B : Type} [Fintype A] [Fintype B]
    (equiv : A ≃ B) : UniformProjection A B where
  map := equiv
  probabilityExact := fun event => uniformProb_equiv equiv event

/-- The first exact uniform marginal on the two-point coin. -/
def left : UniformProjection (Fin 2) (Fin 2) :=
  projectionOfEquiv (Equiv.refl (Fin 2))

/-- The second exact uniform marginal swaps the two outcomes. -/
def right : UniformProjection (Fin 2) (Fin 2) :=
  projectionOfEquiv (Equiv.swap (0 : Fin 2) 1)

/-- The two individually uniform marginals disagree on every common coin. -/
theorem left_ne_right (omega : Fin 2) :
    left.map omega ≠ right.map omega := by
  fin_cases omega <;> simp [left, right, projectionOfEquiv]

private theorem probability_one_of_everywhere
    {C : Type} [Fintype C] [Nonempty C] {event : C -> Prop}
    (everywhere : forall coin, event coin) :
    uniformProb C event = 1 := by
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv everywhere),
    Nat.card_eq_fintype_card]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

/-- **Counterexample.** Two exact uniform marginals can have mismatch
probability one on the same `Omega`.  Thus marginal uniformity, independence
of separately sampled games, or an equality of marginal probabilities cannot
discharge the raw controller's pointwise receipt-coin mismatch event. -/
theorem mismatch_probability_one :
    uniformProb (Fin 2) (fun omega => left.map omega ≠ right.map omega) = 1 :=
  probability_one_of_everywhere left_ne_right

end MarginalTransportTooth

/-! ## Teeth: a fixed collision proposition is not a ROM event -/

/-- A true proposition independent of the game coin has probability one.
In particular, replacing an outcome-tied extracted-collision event by the
global existential `MerkleCollision` and then invoking a birthday bound would
be invalid: the concrete cSHAKE function is fixed, so that proposition does
not vary with `Omega`. -/
theorem fixed_true_predicate_probability_one
    {Omega : Type} [Fintype Omega] [Nonempty Omega] (predicate : Prop)
    (truePredicate : predicate) :
    uniformProb Omega (fun _ => predicate) = 1 := by
  apply MarginalTransportTooth.probability_one_of_everywhere
  exact fun _ => truePredicate

/-- If a proposed birthday price is below one, it cannot bound a true fixed
collision proposition.  An outcome-tied query log is therefore load-bearing,
not optional bookkeeping. -/
theorem fixed_true_predicate_not_bounded_below_one
    {Omega : Type} [Fintype Omega] [Nonempty Omega]
    (predicate : Prop) (truePredicate : predicate) (price : Real)
    (priceLtOne : price < 1) :
    ¬(uniformProb Omega (fun _ => predicate) <= price) := by
  rw [fixed_true_predicate_probability_one predicate truePredicate]
  exact not_le_of_gt priceLtOne

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.RawHistorySecurityPrices.merkleCollision_of_receiptCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms merkleCollision_of_receiptCollision
/-- info: 'Minidregg.Assurance.RawHistorySecurityPrices.CollisionRomRealization.event_le_birthday' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms CollisionRomRealization.event_le_birthday
/-- info: 'Minidregg.Assurance.RawHistorySecurityPrices.ExactReceiptCoinRealization.mismatch_probability_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms ExactReceiptCoinRealization.mismatch_probability_zero
/-- info: 'Minidregg.Assurance.RawHistorySecurityPrices.MarginalTransportTooth.mismatch_probability_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms MarginalTransportTooth.mismatch_probability_one

end

end Minidregg.Assurance.RawHistorySecurityPrices
