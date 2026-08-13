/-
# Assurance.SameCoinGameProduct -- constructible common coins for heterogeneous games

The proof controllers currently expose several honest local security games,
but their coin types and failure registries are different.  Saying “put them
on one Omega” as a structure parameter does not construct that Omega and can
leave a top-level family permanently uninhabited.

This module supplies the missing probability-preserving plumbing:

* a `UniformProjection` records an exact marginal from a global coin;
* priced failures and finite indexed ledgers pull back along that projection;
* registered games join on a product coin with disjoint failure tags; and
* the raw additive, Ext6, note-spend, and BFV controller games have exact
  adapters whose covers are derived from their existing component theorems.

The product operation and its global cover are therefore actual constructions,
conditional on supplied local game interfaces; this module does not claim that
those local interfaces already have deployed instances.  It is deliberately a
*ledger/game* join, not yet a shared-ROM transcript join: Ext6, note-spend, and
BFV do not expose a `SharedOracleSchedule`.  Retained history is also not
smuggled through the old binding-closed `JointGameFamily`; its raw BCS/PCS join
remains a separate, explicit residual.
-/

import Assurance.BfvProofControllerAdmission
import Assurance.ExtensibleProofCompositionGame
import Assurance.NoteSpendProofControllerAdmission
import Assurance.Tower256AdditiveFriRawAdmission

namespace Minidregg.Assurance.SameCoinGameProduct

open scoped BigOperators
open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.ExtensibleProofCompositionGame
open Minidregg.Selvage

set_option autoImplicit false

noncomputable section

universe uClass uLeftClass uRightClass

/-! ## Exact uniform marginals -/

/-- A projection from one finite global coin to a local coin which preserves
the probability of every local event.  This can describe a product marginal
or a correlated master random tape with a proved uniform projection. -/
structure UniformProjection
    (Omega : Type) (LocalCoin : Type)
    [Fintype Omega] [Fintype LocalCoin] where
  map : Omega → LocalCoin
  probabilityExact : ∀ event : LocalCoin → Prop,
    uniformProb Omega (fun omega => event (map omega)) =
      uniformProb LocalCoin event

namespace UniformProjection

def fstSubtypeEquiv {A B : Type} (event : A → Prop) :
    {coin : A × B // event coin.1} ≃ {a : A // event a} × B where
  toFun coin := (⟨coin.1.1, coin.2⟩, coin.1.2)
  invFun coin := ⟨(coin.1.1, coin.2), coin.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- First projection of a nonempty finite product is exactly uniform. -/
def fst {A B : Type} [Fintype A] [Fintype B] [Nonempty B] :
    UniformProjection (A × B) A where
  map := Prod.fst
  probabilityExact := fun event => by
    have cardB : (Fintype.card B : Real) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    unfold uniformProb
    rw [Nat.card_congr (fstSubtypeEquiv event), Nat.card_prod,
      Nat.card_eq_fintype_card (α := B), Fintype.card_prod]
    push_cast
    rw [← div_mul_div_comm, div_self cardB, mul_one]

/-- Second projection of a nonempty finite product is exactly uniform. -/
def snd {A B : Type} [Fintype A] [Fintype B] [Nonempty A] :
    UniformProjection (A × B) B where
  map := Prod.snd
  probabilityExact := fun event =>
    (uniformProb_equiv (Equiv.prodComm A B)
      (fun coin : B × A => event coin.1)).trans
      ((fst (A := B) (B := A)).probabilityExact event)

/-- Uniform projections compose, so a nested global coin can expose any
component marginal without flattening its product representation. -/
def comp {Omega Mid LocalCoin : Type}
    [Fintype Omega] [Fintype Mid] [Fintype LocalCoin]
    (outer : UniformProjection Omega Mid)
    (inner : UniformProjection Mid LocalCoin) :
    UniformProjection Omega LocalCoin where
  map := inner.map ∘ outer.map
  probabilityExact := fun event => by
    change uniformProb Omega (fun omega => event (inner.map (outer.map omega))) = _
    rw [outer.probabilityExact (fun mid => event (inner.map mid)),
      inner.probabilityExact event]

end UniformProjection

/-! ## Pull back prices and ledgers -/

def pullbackFailure {Omega LocalCoin : Type}
    [Fintype Omega] [Fintype LocalCoin]
    (projection : UniformProjection Omega LocalCoin)
    (failure : PricedFailure LocalCoin) : PricedFailure Omega where
  event := failure.event ∘ projection.map
  price := failure.price
  bound := by
    change uniformProb Omega
      (fun omega => failure.event (projection.map omega)) ≤ failure.price
    rw [projection.probabilityExact failure.event]
    exact failure.bound

def pullbackLedger {Class : Type uClass} {Omega LocalCoin : Type}
    [Fintype Omega] [Fintype LocalCoin]
    (projection : UniformProjection Omega LocalCoin)
    (ledger : IndexedFailureLedger Class LocalCoin) :
    IndexedFailureLedger Class Omega :=
  fun failure => pullbackFailure projection (ledger failure)

@[simp] theorem pullbackLedger_event {Class : Type uClass}
    {Omega LocalCoin : Type} [Fintype Omega] [Fintype LocalCoin]
    (projection : UniformProjection Omega LocalCoin)
    (ledger : IndexedFailureLedger Class LocalCoin) (failure : Class)
    (omega : Omega) :
    (pullbackLedger projection ledger failure).event omega ↔
      (ledger failure).event (projection.map omega) :=
  Iff.rfl

@[simp] theorem pullbackLedger_price {Class : Type uClass}
    {Omega LocalCoin : Type} [Fintype Omega] [Fintype LocalCoin]
    (projection : UniformProjection Omega LocalCoin)
    (ledger : IndexedFailureLedger Class LocalCoin) (failure : Class) :
    (pullbackLedger projection ledger failure).price =
      (ledger failure).price :=
  rfl

/-! ## A schedule-independent registered game -/

/-- The common denominator of all current controller games: one exhaustive
finite failure registry and a derived pointwise cover.  Transcript-owning
controllers can retain their stronger `SecurityGame` beside this projection. -/
structure RegisteredGame (Class : Type uClass) (Omega : Type)
    [Fintype Class] [Fintype Omega] where
  ledger : IndexedFailureLedger Class Omega
  falseAccept : Omega → Prop
  failureCover : ∀ omega, falseAccept omega → ledger.Bad omega

namespace RegisteredGame

variable {Class : Type uClass} {Omega : Type}
variable [Fintype Class] [Fintype Omega]

theorem falseAccept_le_total (game : RegisteredGame Class Omega) :
    uniformProb Omega game.falseAccept ≤ game.ledger.total :=
  le_trans (uniformProb_mono game.failureCover)
    (IndexedFailureLedger.bad_le_total game.ledger)

theorem falseAccept_impossible_of_not_bad
    (game : RegisteredGame Class Omega) {omega : Omega}
    (good : ¬game.ledger.Bad omega) : ¬game.falseAccept omega := by
  intro accepted
  exact good (game.failureCover omega accepted)

/-- Pull a game onto a larger coin using an exact uniform marginal. -/
def pullback {GlobalCoin : Type}
    [Fintype GlobalCoin]
    (projection : UniformProjection GlobalCoin Omega)
    (game : RegisteredGame Class Omega) :
    RegisteredGame Class GlobalCoin where
  ledger := pullbackLedger projection game.ledger
  falseAccept := game.falseAccept ∘ projection.map
  failureCover := fun omega accepted => by
    obtain ⟨failure, failed⟩ := game.failureCover (projection.map omega) accepted
    exact ⟨failure, failed⟩

theorem pullback_probability_exact {GlobalCoin : Type}
    [Fintype GlobalCoin]
    (projection : UniformProjection GlobalCoin Omega)
    (game : RegisteredGame Class Omega) :
    uniformProb GlobalCoin (game.pullback projection).falseAccept =
      uniformProb Omega game.falseAccept :=
  projection.probabilityExact game.falseAccept

/-! ## Construct the global coin rather than assuming it -/

variable {LeftClass : Type uLeftClass} {RightClass : Type uRightClass}
variable {LeftCoin RightCoin : Type}
variable [Fintype LeftClass] [Fintype RightClass]
variable [Fintype LeftCoin] [Fintype RightCoin]
variable [Nonempty LeftCoin] [Nonempty RightCoin]

/-- Product join with disjoint failure names.  Both component probabilities
are exact marginals of the newly constructed global coin. -/
def product
    (left : RegisteredGame LeftClass LeftCoin)
    (right : RegisteredGame RightClass RightCoin) :
    RegisteredGame (LeftClass ⊕ RightClass) (LeftCoin × RightCoin) where
  ledger := Sum.elim
    (pullbackLedger UniformProjection.fst left.ledger)
    (pullbackLedger UniformProjection.snd right.ledger)
  falseAccept := fun coin => left.falseAccept coin.1 ∨ right.falseAccept coin.2
  failureCover := fun coin accepted => by
    rcases accepted with leftAccepted | rightAccepted
    · obtain ⟨failure, failed⟩ := left.failureCover coin.1 leftAccepted
      exact ⟨Sum.inl failure, failed⟩
    · obtain ⟨failure, failed⟩ := right.failureCover coin.2 rightAccepted
      exact ⟨Sum.inr failure, failed⟩

@[simp] theorem product_left_event_exact
    (left : RegisteredGame LeftClass LeftCoin)
    (right : RegisteredGame RightClass RightCoin)
    (failure : LeftClass) (coin : LeftCoin × RightCoin) :
    ((left.product right).ledger (Sum.inl failure)).event coin ↔
      (left.ledger failure).event coin.1 :=
  Iff.rfl

@[simp] theorem product_right_event_exact
    (left : RegisteredGame LeftClass LeftCoin)
    (right : RegisteredGame RightClass RightCoin)
    (failure : RightClass) (coin : LeftCoin × RightCoin) :
    ((left.product right).ledger (Sum.inr failure)).event coin ↔
      (right.ledger failure).event coin.2 :=
  Iff.rfl

theorem product_left_probability_exact
    (left : RegisteredGame LeftClass LeftCoin)
    (right : RegisteredGame RightClass RightCoin) :
    uniformProb (LeftCoin × RightCoin) (fun coin => left.falseAccept coin.1) =
      uniformProb LeftCoin left.falseAccept :=
  UniformProjection.fst.probabilityExact left.falseAccept

theorem product_right_probability_exact
    (left : RegisteredGame LeftClass LeftCoin)
    (right : RegisteredGame RightClass RightCoin) :
    uniformProb (LeftCoin × RightCoin) (fun coin => right.falseAccept coin.2) =
      uniformProb RightCoin right.falseAccept :=
  UniformProjection.snd.probabilityExact right.falseAccept

theorem product_total_exact
    (left : RegisteredGame LeftClass LeftCoin)
    (right : RegisteredGame RightClass RightCoin) :
    (left.product right).ledger.total = left.ledger.total + right.ledger.total := by
  simp only [IndexedFailureLedger.total, Fintype.sum_sum_type]
  rfl

theorem product_falseAccept_le
    (left : RegisteredGame LeftClass LeftCoin)
    (right : RegisteredGame RightClass RightCoin) :
    uniformProb (LeftCoin × RightCoin) (left.product right).falseAccept ≤
      left.ledger.total + right.ledger.total := by
  rw [← product_total_exact left right]
  exact (left.product right).falseAccept_le_total

end RegisteredGame

/-! ## Exact adapters for the current controllers -/

abbrev BaseFailureClass :=
  Minidregg.Assurance.ProofCompositionGame.FailureClass

abbrev Ext6FailureClass :=
  Minidregg.Assurance.Ext6GateProofControllerAdmission.Ext6FailureClass

abbrev NoteFailureClass :=
  Minidregg.Assurance.NoteSpendProofControllerAdmission.FailureClass

abbrev BfvFailureClass :=
  Minidregg.Assurance.BfvProofControllerAdmission.FailureClass

/-- Forget only the shared schedule of an existing common proof game; its
ledger, false-accept predicate, and cover remain exact. -/
def ofSecurityGame {Omega Root Payload Challenge Phase : Type}
    [Fintype Omega] {rounds : Nat}
    (game : SecurityGame Omega Root Payload Challenge Phase rounds) :
    RegisteredGame BaseFailureClass Omega where
  ledger := game.ledger
  falseAccept := game.falseAccept
  failureCover := fun omega accepted =>
    (ExtendedLedger.base_bad_iff_exists game.ledger omega).1
      (game.failureCover omega accepted)

namespace Ext6

open Minidregg.Assurance.Ext6GateProofControllerAdmission

def game {m nPadding : Nat}
    {suite : Minidregg.Compiler.Ext6GateProofController.Suite}
    {statement : Minidregg.Compiler.Ext6GateProofController.Statement m nPadding}
    {verifier : Minidregg.Compiler.Ext6GateProofController.Verifier suite statement}
    {Omega Error : Type} [Fintype Omega] {request : List UInt8}
    (family : GameFamily (suite := suite) (statement := statement)
      (verifier := verifier) Omega Error request) :
    RegisteredGame Ext6FailureClass Omega where
  ledger := family.ledger
  falseAccept := family.FalseAccept
  failureCover := fun omega accepted =>
    (Ext6GlobalLedger.ext6_bad_iff_exists family.ledger omega).1
      (family.falseAccept_bad omega accepted)

end Ext6

namespace NoteSpend

open Minidregg.Assurance.NoteSpendProofControllerAdmission

/-- Note-spend relation soundness and hiding remain distinct events.  The
privacy reduction is an explicit extra argument: a soundness-only family does
not acquire a hiding claim merely by being registered. -/
def game {Omega Error : Type} [Fintype Omega]
    {statement : Minidregg.Compiler.NoteSpendProofController.Statement}
    {bound : Minidregg.Compiler.NoteSpendProofController.BoundReflectedSuite statement}
    (family : CommonGameFamily Omega Error bound)
    (privacy : SameCoinHidingLaws family.ledger bound) :
    RegisteredGame NoteFailureClass Omega where
  ledger := family.ledger
  falseAccept := fun omega =>
    family.FalseAccept omega ∨ family.HidingFailure privacy omega
  failureCover := fun omega accepted => by
    rcases accepted with soundness | privacyFailure
    · rcases family.falseAccept_soundnessBad omega soundness with
        failed | failed | failed | failed | failed
      · exact ⟨.arithmeticSoundness, failed⟩
      · exact ⟨.pcsSoundness, failed⟩
      · exact ⟨.collisionResistance, failed⟩
      · exact ⟨.randomOracle, failed⟩
      · exact ⟨.proofOfKnowledge, failed⟩
    · exact ⟨.zeroKnowledgeHiding,
        family.hidingFailure_event privacy omega privacyFailure⟩

end NoteSpend

namespace Bfv

open Minidregg.Assurance.BfvProofControllerAdmission

def game {Omega Error : Type} [Fintype Omega]
    {statement : Minidregg.Compiler.BfvProofController.Statement}
    {bound : Minidregg.Compiler.BfvProofController.BoundReflectedChecker statement}
    {Witness : Type}
    (family : CommonGameFamily Omega Error bound Witness) :
    RegisteredGame BfvFailureClass Omega where
  ledger := family.ledger
  falseAccept := family.FalseAccept
  failureCover := fun omega accepted => by
    rcases family.falseAccept_bad omega accepted with
      failed | failed | failed | failed | failed
    · exact ⟨.arithmeticSoundness, failed⟩
    · exact ⟨.pcsSoundness, failed⟩
    · exact ⟨.collisionResistance, failed⟩
    · exact ⟨.randomOracle, failed⟩
    · exact ⟨.proofOfKnowledge, failed⟩

end Bfv

namespace RawAdditive

open Minidregg.Assurance.Tower256AdditiveFriRawAdmission
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256AdditiveFriRawController

local instance : Fintype Tower256 := Fintype.ofFinite _
local instance : DecidableEq Tower256 := Classical.decEq _

def game {ell m queryCount : Nat}
    {pcs : RawMerklePcs ell} {statement : Statement pcs m}
    {verifier : Verifier (queryCount := queryCount) pcs statement}
    {radius : Nat → Real} {tau : Real}
    {certificate : FarSoundnessCertificate statement radius tau}
    {Error : Type} {request : List UInt8}
    (family : RawGameFamily (queryCount := queryCount)
      (verifier := verifier) certificate Error request) :
    RegisteredGame BaseFailureClass (IdealCoin statement) :=
  ofSecurityGame family.securityGame

end RawAdditive

/-! ## The four-controller global product -/

/-- Failure names for the actual nested product.  Base/raw-additive, Ext6,
note-spend, and BFV classes are pairwise disjoint even when their prose names
coincide. -/
abbrev ControllerStackFailureClass :=
  ((BaseFailureClass ⊕ Ext6FailureClass) ⊕ NoteFailureClass) ⊕ BfvFailureClass

/-- Construct the global coin and its cover from four supplied component
games.  This is compositional plumbing rather than a deployment witness: raw
additive retains extractable Merkle collisions, while the other three retain
their exact local reduction-law residuals. -/
def controllerStack
    {RawCoin Ext6Coin NoteCoin BfvCoin : Type}
    [Fintype RawCoin] [Fintype Ext6Coin] [Fintype NoteCoin] [Fintype BfvCoin]
    [Nonempty RawCoin] [Nonempty Ext6Coin] [Nonempty NoteCoin] [Nonempty BfvCoin]
    (raw : RegisteredGame BaseFailureClass RawCoin)
    (ext6 : RegisteredGame Ext6FailureClass Ext6Coin)
    (note : RegisteredGame NoteFailureClass NoteCoin)
    (bfv : RegisteredGame BfvFailureClass BfvCoin) :
    RegisteredGame ControllerStackFailureClass
      (((RawCoin × Ext6Coin) × NoteCoin) × BfvCoin) :=
  ((raw.product ext6).product note).product bfv

theorem controllerStack_falseAccept_le
    {RawCoin Ext6Coin NoteCoin BfvCoin : Type}
    [Fintype RawCoin] [Fintype Ext6Coin] [Fintype NoteCoin] [Fintype BfvCoin]
    [Nonempty RawCoin] [Nonempty Ext6Coin] [Nonempty NoteCoin] [Nonempty BfvCoin]
    (raw : RegisteredGame BaseFailureClass RawCoin)
    (ext6 : RegisteredGame Ext6FailureClass Ext6Coin)
    (note : RegisteredGame NoteFailureClass NoteCoin)
    (bfv : RegisteredGame BfvFailureClass BfvCoin) :
    uniformProb (((RawCoin × Ext6Coin) × NoteCoin) × BfvCoin)
        (controllerStack raw ext6 note bfv).falseAccept ≤
      raw.ledger.total + ext6.ledger.total + note.ledger.total + bfv.ledger.total := by
  rw [show raw.ledger.total + ext6.ledger.total + note.ledger.total +
      bfv.ledger.total =
      (((raw.product ext6).product note).ledger.total + bfv.ledger.total) by
    rw [RegisteredGame.product_total_exact,
      RegisteredGame.product_total_exact]]
  exact RegisteredGame.product_falseAccept_le
    ((raw.product ext6).product note) bfv

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.SameCoinGameProduct.UniformProjection.fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms UniformProjection.fst
/-- info: 'Minidregg.Assurance.SameCoinGameProduct.RegisteredGame.product_falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RegisteredGame.product_falseAccept_le
/-- info: 'Minidregg.Assurance.SameCoinGameProduct.RawAdditive.game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RawAdditive.game
/-- info: 'Minidregg.Assurance.SameCoinGameProduct.controllerStack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms controllerStack
/-- info: 'Minidregg.Assurance.SameCoinGameProduct.controllerStack_falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms controllerStack_falseAccept_le

end

end Minidregg.Assurance.SameCoinGameProduct
