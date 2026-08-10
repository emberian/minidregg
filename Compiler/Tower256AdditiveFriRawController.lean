/-
# Compiler.Tower256AdditiveFriRawController -- additive FRI before binding

This module exposes the concrete Tower256 additive-FRI checker without putting
`PositionBinding` in the PCS type.  It uses the same `LevelSpec`, concrete
Merkle `CommitmentScheme`, cSHAKE challenge derivation, proof bytes, and fold
equations as `Tower256AdditiveFriController`.

For every claimed opening the checker compares against the honest opening of
the transcript word.  If the values differ, the landed deterministic Merkle
reduction extracts an exact `FramedXofCollision` (leaf or node) from the two
accepted paths.  If no such collision is extracted, all queried values equal
the literal committed words and the accepted receipt enters Loom's ideal
additive-FRI predicate.  No collision probability, ROM theorem, native
semantics, or universal binding assumption is introduced here.
-/

import Compiler.Tower256AdditiveFriController
import Compiler.Tower256CshakeMerkleBinding

namespace Minidregg.Compiler.Tower256AdditiveFriRawController

open Polynomial
open Minidregg.Compiler.AdditiveFriReceiptClause
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256CshakeMerkleBinding
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Loom
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

/-! ## Raw concrete Merkle family -/

/-- The exact concrete PCS metadata with no global binding field. -/
structure RawMerklePcs (ell : Nat) where
  backend : Backend Tower256
  towerExact : backend.tower = BinaryTower256Profile.profile
  cshakeAlgorithmId : Digest
  cshakeDigestCodecPin : CodecPin
  cshakeExact : backend.cshake =
    Sp800185Cshake256.controller cshakeAlgorithmId cshakeDigestCodecPin
  level : (n : Nat) -> LevelSpec backend ell n

def RawMerklePcs.ofConcrete {ell : Nat}
    (level : (n : Nat) -> LevelSpec
      Tower256ConcreteBackend.backend ell n) : RawMerklePcs ell where
  backend := Tower256ConcreteBackend.backend
  towerExact := Tower256ConcreteBackend.towerExact
  cshakeAlgorithmId := Tower256ConcreteBackend.cshakeAlgorithmId
  cshakeDigestCodecPin := Tower256ConcreteBackend.digestCodecPin
  cshakeExact := Tower256ConcreteBackend.cshakeExact
  level := level

namespace RawMerklePcs

variable {ell : Nat} (pcs : RawMerklePcs ell)

/-- The literal executable finite-index scheme at level `n`. -/
def finiteScheme (n : Nat) : CommitmentScheme (pcs.level n).port :=
  (pcs.level n).scheme

/-- Reindex the raw executable checker to additive coordinates, without adding
a binding proof. -/
def opening (n : Nat) :
    OpeningScheme Digest Tower256 (AdditiveFriLevels ell n) (List UInt8) where
  commit word := (pcs.finiteScheme n).commit fun index =>
    word ((additiveFriLevelEquivPowerTwo ell n).symm index)
  openAt word coordinate := (pcs.finiteScheme n).openAt
    (fun index => word ((additiveFriLevelEquivPowerTwo ell n).symm index))
    (additiveFriLevelEquivPowerTwo ell n coordinate)
  verifyOpen root coordinate value proof :=
    (pcs.finiteScheme n).verifyOpening root
      (additiveFriLevelEquivPowerTwo ell n coordinate) value proof = true
  verifyOpen_commit := by
    intro word coordinate
    simpa [finiteScheme] using (pcs.finiteScheme n).verifyOpening_commit
      (fun index => word ((additiveFriLevelEquivPowerTwo ell n).symm index))
      (additiveFriLevelEquivPowerTwo ell n coordinate)

/-- Finite-index word underlying one additive-coordinate word. -/
def finiteWord (n : Nat) (word : AdditiveFriLevels ell n -> Tower256) :
    PowerTwoFriLevels ell n -> Tower256 :=
  fun index => word ((additiveFriLevelEquivPowerTwo ell n).symm index)

/-- Compare one adversarial opening with the honest opening of a specified
word at the identical root and coordinate. -/
def attemptAgainstWord (n : Nat)
    (word : AdditiveFriLevels ell n -> Tower256)
    (root : Digest) (coordinate : AdditiveFriLevels ell n)
    (value : Tower256) (proof : List UInt8) :
    OpeningPair Tower256 (PowerTwoFriLevels ell n) where
  root := root
  index := additiveFriLevelEquivPowerTwo ell n coordinate
  left := value
  right := word coordinate
  leftProof := proof
  rightProof := (pcs.finiteScheme n).openAt (finiteWord n word)
    (additiveFriLevelEquivPowerTwo ell n coordinate)

/-- One unequal accepted raw opening extracts the landed path-specific framed
cSHAKE collision event. -/
theorem accepted_value_eq_or_extractedCollision
    (n : Nat) (word : AdditiveFriLevels ell n -> Tower256)
    (root : Digest) (coordinate : AdditiveFriLevels ell n)
    (value : Tower256) (proof : List UInt8)
    (rootExact : root = (pcs.opening n).commit word)
    (accepted : (pcs.opening n).verifyOpen root coordinate value proof) :
    value = word coordinate ∨
      ExtractedCollision pcs.backend.merkle (pcs.level n).port
        (pcs.attemptAgainstWord n word root coordinate value proof) := by
  by_cases equal : value = word coordinate
  · exact Or.inl equal
  · right
    apply bindingFailure_implies_extractedCollision pcs.backend.merkle
      (pcs.level n).port
    refine ⟨accepted, ?_, equal⟩
    have honest := (pcs.finiteScheme n).verifyOpening_commit
      (finiteWord n word) (additiveFriLevelEquivPowerTwo ell n coordinate)
    simpa [attemptAgainstWord, opening, finiteScheme, finiteWord, rootExact] using honest

end RawMerklePcs

/-! ## Raw adaptive statement and transcript -/

structure RawTranscript {ell : Nat} (pcs : RawMerklePcs ell) where
  word : forall n, (Fin n -> Tower256) -> AdditiveFriLevels ell n -> Tower256
  root : forall n, (Fin n -> Tower256) -> Digest
  root_eq_commit : forall n p,
    root n p = (pcs.opening n).commit (word n p)

namespace RawTranscript

variable {ell m : Nat} {pcs : RawMerklePcs ell}

def wordAt (transcript : RawTranscript pcs) (challenges : Fin m -> Tower256)
    (n : Nat) (hn : n <= m) : AdditiveFriLevels ell n -> Tower256 :=
  transcript.word n (friPrefix challenges n hn)

def rootAt (transcript : RawTranscript pcs) (challenges : Fin m -> Tower256)
    (n : Nat) (hn : n <= m) : Digest :=
  transcript.root n (friPrefix challenges n hn)

theorem rootAt_eq_commit (transcript : RawTranscript pcs)
    (challenges : Fin m -> Tower256) (n : Nat) (hn : n <= m) :
    transcript.rootAt challenges n hn =
      (pcs.opening n).commit (transcript.wordAt challenges n hn) :=
  transcript.root_eq_commit n _

/-- Identity commitments retain the same adaptive word strategy and remove
roots from the ideal probability theorem. -/
def toIdeal (transcript : RawTranscript pcs) :
    FriAdaptiveTranscript
      (fun n => idealCommitment Tower256 (AdditiveFriLevels ell n)) where
  word := transcript.word
  root := transcript.word
  root_eq_commit := by
    intro n p
    rfl

@[simp] theorem toIdeal_wordAt (transcript : RawTranscript pcs)
    (challenges : Fin m -> Tower256) (n : Nat) (hn : n <= m) :
    transcript.toIdeal.wordAt challenges n hn =
      transcript.wordAt challenges n hn :=
  rfl

end RawTranscript

variable {ell m queryCount : Nat}

structure Statement (pcs : RawMerklePcs ell) (m : Nat) where
  tower : AdditiveFriTower Tower256 ell m
  degree : Nat -> Nat
  transcript : RawTranscript pcs
  queryCount : Nat

/-! ## Exact Lean-owned transcript and raw acceptance -/

def challengeInput (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (pins : TranscriptPins) (receipt : Receipt ell m queryCount)
    (j : Fin m) : List UInt8 :=
  envelope pins.statementBytes ++
    (List.ofFn fun n : Fin ((j : Nat) + 1) =>
      have hn : (n : Nat) <= m := by omega
      let root := statement.transcript.rootAt receipt.challenges n hn
      envelope (encodeLength n) ++
        envelope (pcs.backend.cshake.digestCodec.encode root)).flatten

def derivedChallenge (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (pins : TranscriptPins) (receipt : Receipt ell m queryCount)
    (j : Fin m) : Tower256 :=
  digestTower (pcs.backend.cshake.xofDigest pins.challengeCustomization
    (challengeInput pcs statement pins receipt j))

def queryPrefix (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (pins : TranscriptPins) (receipt : Receipt ell m queryCount) : List UInt8 :=
  envelope pins.statementBytes ++
    (List.ofFn fun n : Fin (m + 1) =>
      have hn : (n : Nat) <= m := by omega
      envelope (encodeLength n) ++ envelope
        (pcs.backend.cshake.digestCodec.encode
          (statement.transcript.rootAt receipt.challenges n hn))).flatten ++
    (List.ofFn receipt.challenges).flatMap fun challenge =>
      envelope (BinaryTower256Profile.profile.valueCodec.encode challenge)

def derivedQuerySeed (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (pins : TranscriptPins) (receipt : Receipt ell m queryCount)
    (a : Fin queryCount) : PowerTwoFriLevels ell 1 :=
  let digest := pcs.backend.cshake.xofDigest pins.queryCustomization
    (queryPrefix pcs statement pins receipt ++ envelope (encodeLength a))
  ⟨digest.value % (2 ^ (ell - 1)), Nat.mod_lt _ (by positivity)⟩

def RawOpenedAdditiveFriQuery (pcs : RawMerklePcs ell)
    (statement : Statement pcs m) (j : Fin m)
    (receipt : Receipt ell m queryCount)
    (k : AdditiveFriLevels ell (j + 1))
    (opening : FriQueryOpening Tower256 (List UInt8) (List UInt8)) : Prop :=
  (pcs.opening j).verifyOpen
      (statement.transcript.rootAt receipt.challenges j (Nat.le_of_lt j.isLt))
      (statement.tower.liftBit j j.isLt 0 k) opening.left opening.leftPath ∧
  (pcs.opening (j + 1)).verifyOpen
      (statement.transcript.rootAt receipt.challenges (j + 1)
        (Nat.succ_le_iff.mpr j.isLt))
      k opening.next opening.nextPath ∧
  (pcs.opening j).verifyOpen
      (statement.transcript.rootAt receipt.challenges j (Nat.le_of_lt j.isLt))
      (statement.tower.liftBit j j.isLt 1 k) opening.right opening.rightPath ∧
  opening.next = opening.left +
    (statement.tower.dom j (statement.tower.liftBit j j.isLt 0 k) +
      receipt.challenges j) *
      ((opening.left + opening.right) /
        additiveTowerPivot ell statement.tower.beta j)

/-- The byte controller checks raw Merkle paths, transcript draws, folds, and
the exact final polynomial, but assumes no binding theorem. -/
def Accepts (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (pins : TranscriptPins) (receipt : Receipt ell m queryCount) : Prop :=
  queryCount = statement.queryCount ∧
  (forall j, receipt.challenges j = derivedChallenge pcs statement pins receipt j) ∧
  (forall a, receipt.querySeed a = derivedQuerySeed pcs statement pins receipt a) ∧
  (forall (j : Fin m) (a : Fin queryCount),
    RawOpenedAdditiveFriQuery pcs statement j receipt
      (additiveCoherentRound statement.tower.rounds_le j receipt.querySeed a)
      (receipt.opening j a)) ∧
  receipt.finalPolynomial.degree < (statement.degree m : WithBot Nat) ∧
  (forall point,
    statement.transcript.wordAt receipt.challenges m le_rfl point =
      receipt.finalPolynomial.eval (statement.tower.dom m point))

/-! ## Receipt-specific collision extraction -/

def lowAttempt (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (receipt : Receipt ell m queryCount) (j : Fin m) (a : Fin queryCount) :=
  let k := additiveCoherentRound statement.tower.rounds_le j receipt.querySeed a
  pcs.attemptAgainstWord j
    (statement.transcript.wordAt receipt.challenges j (Nat.le_of_lt j.isLt))
    (statement.transcript.rootAt receipt.challenges j (Nat.le_of_lt j.isLt))
    (statement.tower.liftBit j j.isLt 0 k)
    (receipt.opening j a).left (receipt.opening j a).leftPath

def highAttempt (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (receipt : Receipt ell m queryCount) (j : Fin m) (a : Fin queryCount) :=
  let k := additiveCoherentRound statement.tower.rounds_le j receipt.querySeed a
  pcs.attemptAgainstWord j
    (statement.transcript.wordAt receipt.challenges j (Nat.le_of_lt j.isLt))
    (statement.transcript.rootAt receipt.challenges j (Nat.le_of_lt j.isLt))
    (statement.tower.liftBit j j.isLt 1 k)
    (receipt.opening j a).right (receipt.opening j a).rightPath

def nextAttempt (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (receipt : Receipt ell m queryCount) (j : Fin m) (a : Fin queryCount) :=
  let k := additiveCoherentRound statement.tower.rounds_le j receipt.querySeed a
  pcs.attemptAgainstWord (j + 1)
    (statement.transcript.wordAt receipt.challenges (j + 1)
      (Nat.succ_le_iff.mpr j.isLt))
    (statement.transcript.rootAt receipt.challenges (j + 1)
      (Nat.succ_le_iff.mpr j.isLt))
    k (receipt.opening j a).next (receipt.opening j a).nextPath

def QueryCollision (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (receipt : Receipt ell m queryCount) (j : Fin m) (a : Fin queryCount) : Prop :=
  ExtractedCollision pcs.backend.merkle (pcs.level j).port
      (lowAttempt pcs statement receipt j a) ∨
  ExtractedCollision pcs.backend.merkle (pcs.level j).port
      (highAttempt pcs statement receipt j a) ∨
  ExtractedCollision pcs.backend.merkle (pcs.level (j + 1)).port
      (nextAttempt pcs statement receipt j a)

def ReceiptCollision (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (receipt : Receipt ell m queryCount) : Prop :=
  ∃ j a, QueryCollision pcs statement receipt j a

/-- One accepted raw fibre either equals the literal word/fold fibre or yields
an exact path-specific collision. -/
theorem accepted_query_pins_or_collision
    (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (pins : TranscriptPins) (receipt : Receipt ell m queryCount)
    (accepted : Accepts pcs statement pins receipt)
    (j : Fin m) (a : Fin queryCount) :
    statement.transcript.wordAt receipt.challenges (j + 1)
        (Nat.succ_le_iff.mpr j.isLt)
        (additiveCoherentRound statement.tower.rounds_le j receipt.querySeed a) =
      statement.tower.fold j j.isLt
        (statement.transcript.wordAt receipt.challenges j
          (Nat.le_of_lt j.isLt))
        (receipt.challenges j)
        (additiveCoherentRound statement.tower.rounds_le j receipt.querySeed a) ∨
      QueryCollision pcs statement receipt j a := by
  let k := additiveCoherentRound statement.tower.rounds_le j receipt.querySeed a
  let current := statement.transcript.wordAt receipt.challenges j
    (Nat.le_of_lt j.isLt)
  let next := statement.transcript.wordAt receipt.challenges (j + 1)
    (Nat.succ_le_iff.mpr j.isLt)
  let opening := receipt.opening j a
  have opened := accepted.2.2.2.1 j a
  have low := pcs.accepted_value_eq_or_extractedCollision j current
    (statement.transcript.rootAt receipt.challenges j (Nat.le_of_lt j.isLt))
    (statement.tower.liftBit j j.isLt 0 k) opening.left opening.leftPath
    (statement.transcript.rootAt_eq_commit receipt.challenges j
      (Nat.le_of_lt j.isLt)) opened.1
  rcases low with lowExact | lowCollision
  · have nextValue := pcs.accepted_value_eq_or_extractedCollision (j + 1) next
      (statement.transcript.rootAt receipt.challenges (j + 1)
        (Nat.succ_le_iff.mpr j.isLt))
      k opening.next opening.nextPath
      (statement.transcript.rootAt_eq_commit receipt.challenges (j + 1)
        (Nat.succ_le_iff.mpr j.isLt)) opened.2.1
    rcases nextValue with nextExact | nextCollision
    · have high := pcs.accepted_value_eq_or_extractedCollision j current
        (statement.transcript.rootAt receipt.challenges j (Nat.le_of_lt j.isLt))
        (statement.tower.liftBit j j.isLt 1 k) opening.right opening.rightPath
        (statement.transcript.rootAt_eq_commit receipt.challenges j
          (Nat.le_of_lt j.isLt)) opened.2.2.1
      rcases high with highExact | highCollision
      · left
        change next k = statement.tower.fold j j.isLt current
          (receipt.challenges j) k
        rw [← nextExact, opened.2.2.2, lowExact, highExact]
        rfl
      · exact Or.inr (Or.inr (Or.inl highCollision))
    · exact Or.inr (Or.inr (Or.inr nextCollision))
  · exact Or.inr (Or.inl lowCollision)

/-- The ideal predicate used by the landed additive soundness theorem, with
identity commitments over exactly the raw transcript's words. -/
def IdealAccept {pcs : RawMerklePcs ell} (statement : Statement pcs m)
    (challenges : Fin m -> Tower256)
    (querySeed : Fin statement.queryCount -> PowerTwoFriLevels ell 1) : Prop :=
  AdditiveFriAdaptiveCoherentAccepts statement.tower
    (fun n => idealCommitment Tower256 (AdditiveFriLevels ell n))
    statement.degree statement.transcript.toIdeal statement.queryCount
    challenges querySeed

/-- Raw controller acceptance reaches the exact ideal theorem unless one of
its own submitted-vs-honest opening pairs extracts a framed collision. -/
theorem accepts_ideal_or_receiptCollision
    (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (pins : TranscriptPins) (receipt : Receipt ell m queryCount)
    (accepted : Accepts pcs statement pins receipt) :
    ReceiptCollision pcs statement receipt ∨
      ∃ querySeed : Fin statement.queryCount -> PowerTwoFriLevels ell 1,
        IdealAccept statement receipt.challenges querySeed := by
  by_cases collision : ReceiptCollision pcs statement receipt
  · exact Or.inl collision
  · right
    have queryCountExact := accepted.1
    subst queryCount
    refine ⟨receipt.querySeed, ?_⟩
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
      have literal := accepted_query_pins_or_collision pcs statement pins receipt
        accepted j a
      rcases literal with literal | queryCollision
      · refine ⟨rfl, rfl, rfl, ?_⟩
        exact literal
      · exact False.elim (collision ⟨j, a, queryCollision⟩)
    · apply mem_reedSolomonCode_iff.mpr
      exact ⟨receipt.finalPolynomial, accepted.2.2.2.2.1,
        accepted.2.2.2.2.2⟩

/-! ## Opaque bytes/error runner -/

structure Verifier (pcs : RawMerklePcs ell) (statement : Statement pcs m) where
  pins : TranscriptPins
  proofCodecPin : CodecPin
  proofCodec : LawfulCodec (Receipt ell m queryCount)
  check : Receipt ell m queryCount -> Bool
  check_iff : forall receipt, check receipt = true <->
    Accepts pcs statement pins receipt

abbrev OpaqueProofRunner (Error : Type) :=
  List UInt8 -> Except Error (List UInt8)

inductive Failure (Error : Type)
  | native (error : Error)
  | invalidEncoding
  | rejected
deriving Repr

structure AcceptedReceipt (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (verifier : Verifier (queryCount := queryCount) pcs statement)
    (request : List UInt8) where
  proofBytes : List UInt8
  receipt : Receipt ell m queryCount
  decoded : verifier.proofCodec.decode proofBytes = some receipt
  accepted : Accepts pcs statement verifier.pins receipt

def run {Error : Type} (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (verifier : Verifier (queryCount := queryCount) pcs statement)
    (runner : OpaqueProofRunner Error) (request : List UInt8) :
    Except (Failure Error)
      (AcceptedReceipt (queryCount := queryCount) pcs statement verifier request) :=
  match returned : runner request with
  | .error error => .error (.native error)
  | .ok proofBytes =>
      match decoded : verifier.proofCodec.decode proofBytes with
      | none => .error .invalidEncoding
      | some receipt =>
          if checked : verifier.check receipt = true then
            .ok ⟨proofBytes, receipt, decoded,
              (verifier.check_iff receipt).mp checked⟩
          else .error .rejected

theorem run_success_integrity {Error : Type}
    (pcs : RawMerklePcs ell) (statement : Statement pcs m)
    (verifier : Verifier (queryCount := queryCount) pcs statement)
    (runner : OpaqueProofRunner Error) (request : List UInt8)
    (reply : AcceptedReceipt (queryCount := queryCount)
      pcs statement verifier request)
    (success : run (queryCount := queryCount) pcs statement verifier runner request =
      .ok reply) :
    runner request = .ok reply.proofBytes ∧
      verifier.proofCodec.decode reply.proofBytes = some reply.receipt ∧
      Accepts pcs statement verifier.pins reply.receipt := by
  unfold run at success
  split at success
  next error failed => simp at success
  next bytes returned =>
    split at success
    next decodeFailed => simp at success
    next receipt decoded =>
      split at success
      next checked =>
        simp only [Except.ok.injEq] at success
        subst reply
        exact ⟨returned, decoded, (verifier.check_iff receipt).mp checked⟩
      next rejected => simp at success

/-- info: 'Minidregg.Compiler.Tower256AdditiveFriRawController.RawMerklePcs.accepted_value_eq_or_extractedCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RawMerklePcs.accepted_value_eq_or_extractedCollision
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriRawController.accepted_query_pins_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_query_pins_or_collision
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriRawController.accepts_ideal_or_receiptCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepts_ideal_or_receiptCollision
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriRawController.run_success_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_success_integrity

end

end Minidregg.Compiler.Tower256AdditiveFriRawController
