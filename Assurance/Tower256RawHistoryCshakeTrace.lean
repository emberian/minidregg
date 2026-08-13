/-
# Assurance.Tower256RawHistoryCshakeTrace -- the exact raw-history ROM seam

The raw retained-history controller now executes the literal state-restoration
Fiat--Shamir run and retains its SR query/challenge trace.  That trace is NOT a
cSHAKE random-oracle trace: the concrete Merkle checker calls the pure
Lean-owned `Sp800185Cshake256` function directly.  In particular, neither
`AcceptedExecution` nor `IdealCoin` contains the fresh cSHAKE answers needed by
the ROM birthday theorem.

This module closes everything which can honestly be closed without inventing
those answers.

* `executedCollision_has_endpoint` starts from the collision event of the
  ACTUALLY EXECUTED history lane and returns two unequal, fully framed cSHAKE
  requests with equal concrete 256-bit answers.
* `FreshTraceRealization` states the smallest missing joint-trace theorem.  It
  records a bounded list of pairwise-distinct cSHAKE requests, an exact uniform
  answer projection on the SAME execution coin, pointwise agreement between
  those answers and the concrete checker, and coverage of every executed
  collision event by two recorded requests.
* `toCollisionRomRealization` proves that this joint trace, if constructed by
  a real-vs-ideal deployment game, is sufficient to instantiate the existing
  birthday adapter.  No birthday term is obtained from the FS-coin marginals.
* `no_constant_slot` proves a useful negative result: a fixed request evaluated
  by the deterministic concrete cSHAKE function cannot be relabelled as one
  uniformly fresh 256-bit answer slot.  A genuine ROM/sponge coupling (and a
  coin space carrying its answers) is therefore logically necessary.

No `PositionBinding`, collision-resistance axiom, or caller-selected numeric
price appears here.
-/

import Assurance.Tower256RawHistoryFsExecution
import Compiler.Sp800185Cshake256

namespace Minidregg.Assurance.Tower256RawHistoryCshakeTrace

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.RawHistorySecurityPrices
open Minidregg.Assurance.RawSemanticHistoryCheckpointGame
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SameCoinGameProduct
open Minidregg.Assurance.Tower256AdditiveFriRawAdmission
open Minidregg.Assurance.Tower256RawHistoryFsController
open Minidregg.Assurance.Tower256RawHistoryFsExecution
open Minidregg.Assurance.Tower256RawSemanticHistoryCanonicalGame
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Sp800185Cshake256
open Minidregg.Compiler.Tower256AdditiveFriRawController
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Selvage
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

noncomputable section

universe uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome

abbrev TowerField :=
  Minidregg.Compiler.BinaryTower256Profile.Tower256

local instance : DecidableEq TowerField := Classical.decEq _
local instance : Fintype TowerField := Fintype.ofFinite _

variable {ell m n : Nat}
variable {pcs : RawMerklePcs ell}
variable {statement : Statement pcs m}
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n TowerField}
    {headerCells : HistoryAdmissionContext -> BindingIx -> TowerField}
    {C : Submodule TowerField (BoundReceiptIx n -> TowerField)}
    {idealS : BindingCommitment Digest TowerField
      (BoundReceiptIx n) (List UInt8)}

local notation "Coin" => IdealCoin statement
local notation "BoundCheckpoint" => RawCheckpoint
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS)
local notation "BoundSpec" checkpoint =>
  Tower256RawHistoryFsController.Spec
    (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C) (idealS := idealS) checkpoint

/-! ## Concrete cSHAKE requests and their exact 256-bit answers -/

/-- The raw PCS pins its backend to the executable SP 800-185 controller, so
every cSHAKE digest has a canonical element of `Fin (2^256)`. -/
def queryAnswer (pcs : RawMerklePcs ell) (query : XofRequest) : Fin (2 ^ 256) :=
  ⟨(pcs.backend.cshake.xofDigest query.customization query.input).value, by
    rw [pcs.cshakeExact, controller_xofDigest]
    exact hash_digest_lt_two_pow_256 query.customization query.input⟩

@[simp] theorem queryAnswer_value (pcs : RawMerklePcs ell)
    (query : XofRequest) :
    (queryAnswer pcs query).val =
      (pcs.backend.cshake.xofDigest query.customization query.input).value :=
  rfl

/-- An exact collision endpoint in the request vocabulary consumed by the
concrete cSHAKE controller. -/
def RequestCollision (pcs : RawMerklePcs ell)
    (left right : XofRequest) : Prop :=
  left ≠ right ∧
    left.customization = right.customization ∧
    queryAnswer pcs left = queryAnswer pcs right

/-! ## The event is tied to the actually executed raw-history lane -/

/-- The exact extracted collision event of the constructed opaque-byte/SR/FS
history execution, not a free predicate on the common coin. -/
def ExecutedCollisionEvent {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    (runner : OpaqueRunner Error) (payload : List UInt8)
    (extraction : ExtractionPlan spec oracle) (coin : Coin) : Prop :=
  (historyLane (verifier := verifier) runner payload extraction).CollisionEvent
    coin

/-- Every collision found on an actually returned raw-history tape reaches two
unequal, same-customization cSHAKE requests with equal concrete 256-bit
answers.  The proof uses the accepted lane's tape and the path-specific Merkle
extractor; no parallel schedule or abstract binding carrier intervenes. -/
theorem executedCollision_has_endpoint {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    (runner : OpaqueRunner Error) (payload : List UInt8)
    (extraction : ExtractionPlan spec oracle) (coin : Coin)
    (collision : ExecutedCollisionEvent (verifier := verifier)
      runner payload extraction coin) :
    ∃ left right : XofRequest, RequestCollision pcs left right := by
  rcases collision with ⟨tape, _executed, _falseStatement, extracted⟩
  rcases exactCshakeCollision_of_extractedHistoryCollision extracted with
    ⟨customization, leftInput, rightInput, framed⟩
  refine ⟨⟨customization, leftInput⟩, ⟨customization, rightInput⟩, ?_⟩
  refine ⟨?_, rfl, ?_⟩
  · intro requestsEqual
    exact framed.inputsDifferent
      (congrArg XofRequest.input requestsEqual)
  · apply Fin.ext
    exact congrArg Digest.value framed.digestsEqual

/-! ## The smallest sufficient fresh-query trace theorem -/

/-- A complete bounded cSHAKE trace for the executed collision event.

`answers` is an exact uniform projection of the SAME `Coin`, not a marginal
bound. `answerExact` couples every recorded request to the concrete cSHAKE
answer used by the checker. `collisionCovered` is the missing run-level trace
theorem: whenever the actual raw-history execution extracts a collision, both
unequal requests occur in this trace. Pairwise request freshness is explicit;
replays are not counted as new birthday slots. -/
structure FreshTraceRealization {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    (runner : OpaqueRunner Error) (payload : List UInt8)
    (extraction : ExtractionPlan spec oracle) (queryBudget : Nat) where
  query : Coin -> Fin queryBudget -> XofRequest
  queryInjective : ∀ coin, Function.Injective (query coin)
  answers : UniformProjection Coin
    (Fin queryBudget -> Fin (2 ^ 256))
  answerExact : ∀ coin i,
    answers.map coin i = queryAnswer pcs (query coin i)
  collisionCovered : ∀ coin,
    ExecutedCollisionEvent (verifier := verifier)
      runner payload extraction coin ->
    ∃ i j : Fin queryBudget,
      RequestCollision pcs (query coin i) (query coin j)

namespace FreshTraceRealization

/-- The complete joint trace discharges exactly the `extracts` field of the
generic birthday adapter. -/
theorem extracts {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    {runner : OpaqueRunner Error} {payload : List UInt8}
    {extraction : ExtractionPlan spec oracle} {queryBudget : Nat}
    (trace : FreshTraceRealization (verifier := verifier)
      runner payload extraction queryBudget) (coin : Coin)
    (collision : ExecutedCollisionEvent (verifier := verifier)
      runner payload extraction coin) :
    Collides (trace.answers.map coin) := by
  rcases trace.collisionCovered coin collision with ⟨i, j, endpoint⟩
  have indicesDifferent : i ≠ j := by
    intro equal
    apply endpoint.1
    subst j
    rfl
  apply collides_of_ne indicesDifferent
  rw [trace.answerExact coin i, trace.answerExact coin j]
  exact endpoint.2.2

/-- Consequently the new trace is sufficient to instantiate the already
landed `CollisionRomRealization`; the birthday price is then derived by
`CollisionRomRealization.event_le_birthday`. -/
def toCollisionRomRealization {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    {runner : OpaqueRunner Error} {payload : List UInt8}
    {extraction : ExtractionPlan spec oracle} {queryBudget : Nat}
    (trace : FreshTraceRealization (verifier := verifier)
      runner payload extraction queryBudget) :
    CollisionRomRealization Coin queryBudget 256
      (ExecutedCollisionEvent (verifier := verifier)
        runner payload extraction) where
  answers := trace.answers
  extracts := trace.extracts

/-- The exact birthday theorem for the actually executed raw-history collision
event, conditional only on the complete joint trace realization above. -/
theorem executedCollision_le_birthday {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    {runner : OpaqueRunner Error} {payload : List UInt8}
    {extraction : ExtractionPlan spec oracle} {queryBudget : Nat}
    (trace : FreshTraceRealization (verifier := verifier)
      runner payload extraction queryBudget) :
    uniformProb Coin (ExecutedCollisionEvent (verifier := verifier)
        runner payload extraction) ≤
      (queryBudget : Real) * ((queryBudget : Real) - 1) /
        (2 ^ 257 : Real) := by
  simpa using trace.toCollisionRomRealization.event_le_birthday

end FreshTraceRealization

/-! ## Why deterministic concrete calls are not fresh ROM slots -/

private def fstSubtypeEquiv {A B : Type} (event : A -> Prop) :
    {coin : A × B // event coin.1} ≃ {a : A // event a} × B where
  toFun coin := (⟨coin.1.1, coin.2⟩, coin.1.2)
  invFun coin := ⟨(coin.1.1, coin.2), coin.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem uniformProb_fst_marginal {A B : Type}
    [Fintype A] [Fintype B] [Nonempty B] (event : A -> Prop) :
    uniformProb (A × B) (fun coin => event coin.1) =
      uniformProb A event := by
  have cardB : (Fintype.card B : Real) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold uniformProb
  rw [Nat.card_congr (fstSubtypeEquiv event), Nat.card_prod,
    Nat.card_eq_fintype_card (α := B), Fintype.card_prod]
  push_cast
  rw [← div_mul_div_comm, div_self cardB, mul_one]

private theorem uniformProb_snd_marginal {A B : Type}
    [Fintype A] [Fintype B] [Nonempty A] (event : B -> Prop) :
    uniformProb (A × B) (fun coin => event coin.2) =
      uniformProb B event :=
  (uniformProb_equiv (Equiv.prodComm A B)
    (fun coin : B × A => event coin.1)).trans
      (uniformProb_fst_marginal event)

private theorem uniformProb_eq_single {A : Type} [Fintype A] (value : A) :
    uniformProb A (fun candidate => candidate = value) =
      1 / (Fintype.card A : Real) := by
  classical
  unfold uniformProb
  rw [show Nat.card {candidate : A // candidate = value} = 1 by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_eq value, Nat.cast_one]

private theorem uniformProb_function_coordinate_eq {q N : Nat}
    (i : Fin q) (value : Fin N) :
    uniformProb (Fin q -> Fin N) (fun answers => answers i = value) =
      1 / (N : Real) := by
  letI : Nonempty (Fin N) := ⟨value⟩
  let Rest := {j : Fin q // j ≠ i} -> Fin N
  haveI : Nonempty Rest := ⟨fun _ => value⟩
  calc
    uniformProb (Fin q -> Fin N) (fun answers => answers i = value) =
        uniformProb (Rest × Fin N) (fun split => split.2 = value) := by
      simpa [Rest] using
        (uniformProb_equiv (splitCoord i)
          (fun split : Rest × Fin N => split.2 = value))
    _ = uniformProb (Fin N) (fun candidate => candidate = value) :=
      uniformProb_snd_marginal (A := Rest) (B := Fin N)
        (fun candidate : Fin N => candidate = value)
    _ = 1 / (N : Real) := by
      rw [uniformProb_eq_single, Fintype.card_fin]

private theorem uniformProb_certain {A : Type} [Fintype A] [Nonempty A]
    {event : A -> Prop} (certain : ∀ a, event a) :
    uniformProb A event = 1 := by
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv certain),
    Nat.card_eq_fintype_card]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

/-- No exact uniform answer projection can have a constant 256-bit coordinate.
This is the formal obstruction to rebranding the deterministic result of a
fixed cSHAKE call as a fresh ROM answer on the existing execution coin. -/
theorem no_constant_uniform_256_slot {Omega : Type} [Fintype Omega]
    [Nonempty Omega] {queryBudget : Nat}
    (answers : UniformProjection Omega
      (Fin queryBudget -> Fin (2 ^ 256)))
    (i : Fin queryBudget) (value : Fin (2 ^ 256))
    (constant : ∀ omega, answers.map omega i = value) : False := by
  have exact := answers.probabilityExact (fun output => output i = value)
  rw [uniformProb_certain constant,
    uniformProb_function_coordinate_eq] at exact
  have rangeGreaterThanOne : (1 : Real) < ((2 ^ 256 : Nat) : Real) := by
    exact_mod_cast Nat.one_lt_two_pow (by decide : 256 ≠ 0)
  have inverseLessThanOne :
      1 / (((2 ^ 256 : Nat) : Real)) < 1 :=
    (div_lt_one (by positivity)).2 rangeGreaterThanOne
  linarith

/-- In particular, a `FreshTraceRealization` cannot use one fixed concrete
cSHAKE request at a slot for every execution coin.  Its request/answer trace
must come from a genuine joint ROM/sponge experiment, not the current pure
function evaluation alone. -/
theorem FreshTraceRealization.no_constant_slot
    {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {oracle : OraclePlan spec}
    {verifier : Verifier spec oracle} {Error : Type}
    {runner : OpaqueRunner Error} {payload : List UInt8}
    {extraction : ExtractionPlan spec oracle} {queryBudget : Nat}
    (trace : FreshTraceRealization (verifier := verifier)
      runner payload extraction queryBudget)
    (i : Fin queryBudget) (request : XofRequest)
    (constant : ∀ coin, trace.query coin i = request) : False := by
  apply no_constant_uniform_256_slot trace.answers i (queryAnswer pcs request)
  intro coin
  rw [trace.answerExact coin i, constant coin]

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Tower256RawHistoryCshakeTrace.executedCollision_has_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms executedCollision_has_endpoint
/-- info: 'Minidregg.Assurance.Tower256RawHistoryCshakeTrace.FreshTraceRealization.toCollisionRomRealization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FreshTraceRealization.toCollisionRomRealization
/-- info: 'Minidregg.Assurance.Tower256RawHistoryCshakeTrace.no_constant_uniform_256_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_constant_uniform_256_slot
/-- info: 'Minidregg.Assurance.Tower256RawHistoryCshakeTrace.FreshTraceRealization.no_constant_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FreshTraceRealization.no_constant_slot

end

end Minidregg.Assurance.Tower256RawHistoryCshakeTrace
