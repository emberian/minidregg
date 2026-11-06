/-
# Compiler.Tower256AdditiveFriSuccinctController -- additive FRI over roots only

`Tower256AdditiveFriRawController.Statement` carries the prover's whole adaptive transcript:
its committed words, as functions. Its `Accepts` compares every opening with the honest
opening of those words and tests the final polynomial against the last word at every point.
A light client cannot hold that statement.

Here the statement is public data only: the additive tower (basis and offset), the degree
schedule, the query count, and the root of the committed input word. The receipt carries the
per-level roots, the challenges, the query seeds, the openings and the final polynomial as a
coordinate list. `SuccinctAccepts` reads nothing else. Every root it checks against is a
receipt or statement value, and the last root is recomputed from the final polynomial's
evaluations on the last domain.

Words appear only in the soundness theorem, as the prover's committed strategy `T` whose roots
are the receipt's (`Consistent`). `succinct_accepts_ideal_or_collision`: an accepted succinct
receipt, for every such `T`, either reaches the landed ideal additive-FRI predicate over `T`'s
words, or yields an explicit framed cSHAKE collision. The collision is at a query path
(`ReceiptCollision`) or at the last level, where `T`'s last word and the final polynomial's
evaluations share a root (`FinalCollision`).
-/

import Compiler.Tower256AdditiveFriRawController
import Compiler.Tower256FinalPolynomialCheck

namespace Minidregg.Compiler.Tower256AdditiveFriSuccinctController

open Polynomial
open Minidregg.Compiler.AdditiveFriReceiptClause
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Compiler.Tower256AdditiveFriRawController
open Minidregg.Compiler.Tower256CshakeMerkleBinding
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256FinalPolynomialCheck
open Minidregg.Selvage
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

variable {ell m queryCount : Nat}

/-! ## Public statement and receipt -/

/-- The public statement: no word, no transcript, no function of the prover. -/
structure SuccinctStatement (ell m : Nat) where
  tower : AdditiveFriTower Tower256 ell m
  degree : Nat → Nat
  queryCount : Nat
  initialRoot : Digest

/-- The proof: per-level roots, the transcript draws, the openings, and the final polynomial
as a coefficient list over `Coordinate 8`. -/
structure SuccinctReceipt (ell m queryCount : Nat) where
  roots : Fin (m + 1) → Digest
  challenges : Fin m → Tower256
  querySeed : Fin queryCount → PowerTwoFriLevels ell 1
  opening : (j : Fin m) → Fin queryCount →
    FriQueryOpening Tower256 (List UInt8) (List UInt8)
  finalCoeffs : List C8

namespace SuccinctReceipt

/-- The final polynomial the coefficient list denotes. -/
def finalPolynomial (r : SuccinctReceipt ell m queryCount) : Polynomial Tower256 :=
  polyOf (r.finalCoeffs.map toField)

/-- The final polynomial's evaluations on the last domain: the word the last root must commit. -/
def finalWord (statement : SuccinctStatement ell m) (r : SuccinctReceipt ell m queryCount) :
    AdditiveFriLevels ell m → Tower256 :=
  fun point => r.finalPolynomial.eval (statement.tower.dom m point)

/-- The root of level `n ≤ m`, read from the receipt. -/
def rootAt (r : SuccinctReceipt ell m queryCount) (n : Nat) (hn : n ≤ m) : Digest :=
  r.roots ⟨n, Nat.lt_succ_of_le hn⟩

/-- The same receipt in the raw controller's shape. -/
def toRaw (r : SuccinctReceipt ell m queryCount) : Receipt ell m queryCount where
  challenges := r.challenges
  querySeed := r.querySeed
  opening := r.opening
  finalPolynomial := r.finalPolynomial

end SuccinctReceipt

/-! ## The verifier, over roots only

Byte-for-byte the raw controller's transcript, with every root read from the receipt. -/

def challengeInput (pcs : RawMerklePcs ell) (statement : SuccinctStatement ell m)
    (pins : TranscriptPins) (r : SuccinctReceipt ell m queryCount) (j : Fin m) :
    List UInt8 :=
  envelope pins.statementBytes ++
    envelope (basisPrefix ell m statement.tower.beta statement.tower.offset) ++
    (List.ofFn fun n : Fin ((j : Nat) + 1) =>
      have hn : (n : Nat) <= m := by omega
      envelope (encodeLength n) ++
        envelope (pcs.backend.cshake.digestCodec.encode (r.rootAt n hn))).flatten

def derivedChallenge (pcs : RawMerklePcs ell) (statement : SuccinctStatement ell m)
    (pins : TranscriptPins) (r : SuccinctReceipt ell m queryCount) (j : Fin m) : Tower256 :=
  digestTower (pcs.backend.cshake.xofDigest pins.challengeCustomization
    (challengeInput pcs statement pins r j))

def queryPrefix (pcs : RawMerklePcs ell) (statement : SuccinctStatement ell m)
    (pins : TranscriptPins) (r : SuccinctReceipt ell m queryCount) : List UInt8 :=
  envelope pins.statementBytes ++
    envelope (basisPrefix ell m statement.tower.beta statement.tower.offset) ++
    (List.ofFn fun n : Fin (m + 1) =>
      have hn : (n : Nat) <= m := by omega
      envelope (encodeLength n) ++ envelope
        (pcs.backend.cshake.digestCodec.encode (r.rootAt n hn))).flatten ++
    (List.ofFn r.challenges).flatMap fun challenge =>
      envelope (BinaryTower256Profile.profile.valueCodec.encode challenge)

def derivedQuerySeed (pcs : RawMerklePcs ell) (statement : SuccinctStatement ell m)
    (pins : TranscriptPins) (r : SuccinctReceipt ell m queryCount)
    (a : Fin queryCount) : PowerTwoFriLevels ell 1 :=
  let digest := pcs.backend.cshake.xofDigest pins.queryCustomization
    (queryPrefix pcs statement pins r ++ envelope (encodeLength a))
  ⟨digest.value % (2 ^ (ell - 1)), Nat.mod_lt _ (by positivity)⟩

def OpenedQuery (pcs : RawMerklePcs ell) (statement : SuccinctStatement ell m) (j : Fin m)
    (r : SuccinctReceipt ell m queryCount) (k : AdditiveFriLevels ell (j + 1))
    (opening : FriQueryOpening Tower256 (List UInt8) (List UInt8)) : Prop :=
  (pcs.opening j).verifyOpen (r.rootAt j (Nat.le_of_lt j.isLt))
      (statement.tower.liftBit j j.isLt 0 k) opening.left opening.leftPath ∧
  (pcs.opening (j + 1)).verifyOpen (r.rootAt (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      k opening.next opening.nextPath ∧
  (pcs.opening j).verifyOpen (r.rootAt j (Nat.le_of_lt j.isLt))
      (statement.tower.liftBit j j.isLt 1 k) opening.right opening.rightPath ∧
  opening.next = opening.left +
    (statement.tower.dom j (statement.tower.liftBit j j.isLt 0 k) + r.challenges j) *
      ((opening.left + opening.right) / additiveTowerPivot ell statement.tower.beta j)

/-- **Succinct acceptance.** Every quantity is the statement's or the receipt's. -/
def SuccinctAccepts (pcs : RawMerklePcs ell) (statement : SuccinctStatement ell m)
    (pins : TranscriptPins) (r : SuccinctReceipt ell m queryCount) : Prop :=
  queryCount = statement.queryCount ∧
  r.roots 0 = statement.initialRoot ∧
  (∀ j, r.challenges j = derivedChallenge pcs statement pins r j) ∧
  (∀ a, r.querySeed a = derivedQuerySeed pcs statement pins r a) ∧
  (∀ (j : Fin m) (a : Fin queryCount),
    OpenedQuery pcs statement j r
      (additiveCoherentRound statement.tower.rounds_le j r.querySeed a) (r.opening j a)) ∧
  r.finalCoeffs.length ≤ statement.degree m ∧
  r.roots (Fin.last m) = (pcs.opening m).commit (r.finalWord statement)

/-! ## The prover's committed strategy, and the raw statement it induces -/

/-- `T` is a committed strategy for this receipt: its roots at the receipt's challenges are the
receipt's roots, and its input root is the statement's. This is where words enter. -/
def Consistent {pcs : RawMerklePcs ell} (statement : SuccinctStatement ell m)
    (r : SuccinctReceipt ell m queryCount) (T : RawTranscript pcs) : Prop :=
  ∀ (n : Nat) (hn : n ≤ m), T.rootAt r.challenges n hn = r.rootAt n hn

/-- The raw statement over `T`'s words. -/
def toRawStatement {pcs : RawMerklePcs ell} (statement : SuccinctStatement ell m)
    (T : RawTranscript pcs) : Statement pcs m where
  tower := statement.tower
  degree := statement.degree
  transcript := T
  queryCount := statement.queryCount

/-- The last-level collision: `T`'s last word and the final polynomial's evaluations disagree
at `point`, and the honest path of the latter opens the shared root there. -/
def FinalCollision (pcs : RawMerklePcs ell) (statement : SuccinctStatement ell m)
    (r : SuccinctReceipt ell m queryCount) (T : RawTranscript pcs) : Prop :=
  ∃ point : AdditiveFriLevels ell m,
    ExtractedCollision pcs.backend.merkle (pcs.level m).port
      (pcs.attemptAgainstWord m (T.wordAt r.challenges m le_rfl)
        (T.rootAt r.challenges m le_rfl) point (r.finalWord statement point)
        ((pcs.opening m).openAt (r.finalWord statement) point))

/-! ## Transport to the raw controller -/

theorem challengeInput_eq_raw (pcs : RawMerklePcs ell) (statement : SuccinctStatement ell m)
    (pins : TranscriptPins) (r : SuccinctReceipt ell m queryCount)
    (T : RawTranscript pcs) (hcons : Consistent statement r T) (j : Fin m) :
    Tower256AdditiveFriRawController.challengeInput pcs (toRawStatement statement T) pins
        r.toRaw j = challengeInput pcs statement pins r j := by
  unfold Tower256AdditiveFriRawController.challengeInput challengeInput
    Tower256AdditiveFriRawController.basisBinding
  congr 3
  funext n
  dsimp only [toRawStatement, SuccinctReceipt.toRaw]
  rw [hcons]

theorem queryPrefix_eq_raw (pcs : RawMerklePcs ell) (statement : SuccinctStatement ell m)
    (pins : TranscriptPins) (r : SuccinctReceipt ell m queryCount)
    (T : RawTranscript pcs) (hcons : Consistent statement r T) :
    Tower256AdditiveFriRawController.queryPrefix pcs (toRawStatement statement T) pins
        r.toRaw = queryPrefix pcs statement pins r := by
  unfold Tower256AdditiveFriRawController.queryPrefix queryPrefix
    Tower256AdditiveFriRawController.basisBinding
  congr 4
  funext n
  dsimp only [toRawStatement, SuccinctReceipt.toRaw]
  rw [hcons]

/-- If `T`'s last word is the final polynomial's evaluation, succinct acceptance is raw
acceptance over `T`. -/
theorem raw_accepts_of_succinct (pcs : RawMerklePcs ell) (statement : SuccinctStatement ell m)
    (pins : TranscriptPins) (r : SuccinctReceipt ell m queryCount)
    (T : RawTranscript pcs) (hcons : Consistent statement r T)
    (accepted : SuccinctAccepts pcs statement pins r)
    (finalExact : T.wordAt r.challenges m le_rfl = r.finalWord statement) :
    Accepts pcs (toRawStatement statement T) pins r.toRaw := by
  obtain ⟨hq, -, hch, hseed, hopen, hlen, -⟩ := accepted
  refine ⟨hq, fun j => ?_, fun a => ?_, fun j a => ?_, ?_, fun point => ?_⟩
  · show r.challenges j = _
    rw [hch j]
    unfold derivedChallenge Tower256AdditiveFriRawController.derivedChallenge
    rw [challengeInput_eq_raw pcs statement pins r T hcons]
    all_goals rfl
  · show r.querySeed a = _
    rw [hseed a]
    simp only [derivedQuerySeed, Tower256AdditiveFriRawController.derivedQuerySeed,
      queryPrefix_eq_raw pcs statement pins r T hcons]
  · have h := hopen j a
    unfold OpenedQuery at h
    obtain ⟨h₁, h₂, h₃, h₄⟩ := h
    refine ⟨?_, ?_, ?_, h₄⟩
    · show (pcs.opening j).verifyOpen (T.rootAt r.challenges j _) _ _ _
      rw [hcons]; exact h₁
    · show (pcs.opening (j + 1)).verifyOpen (T.rootAt r.challenges (j + 1) _) _ _ _
      rw [hcons]; exact h₂
    · show (pcs.opening j).verifyOpen (T.rootAt r.challenges j _) _ _ _
      rw [hcons]; exact h₃
  · show (polyOf (r.finalCoeffs.map toField)).degree < (statement.degree m : WithBot Nat)
    refine lt_of_lt_of_le (degree_polyOf_lt _) ?_
    rw [List.length_map]
    exact_mod_cast hlen
  · show T.wordAt r.challenges m le_rfl point = r.finalPolynomial.eval (statement.tower.dom m point)
    rw [finalExact]
    rfl

/-- **Soundness over roots only.** For every committed strategy consistent with the receipt,
an accepted succinct receipt reaches the landed ideal predicate over that strategy's words, or
yields an explicit framed collision at a query path or at the last level. -/
theorem succinct_accepts_ideal_or_collision (pcs : RawMerklePcs ell)
    (statement : SuccinctStatement ell m) (pins : TranscriptPins)
    (r : SuccinctReceipt ell m queryCount) (T : RawTranscript pcs)
    (hcons : Consistent statement r T) (accepted : SuccinctAccepts pcs statement pins r) :
    FinalCollision pcs statement r T ∨
      ReceiptCollision pcs (toRawStatement statement T) r.toRaw ∨
      ∃ querySeed : Fin statement.queryCount → PowerTwoFriLevels ell 1,
        IdealAccept (toRawStatement statement T) r.challenges querySeed := by
  classical
  by_cases finalExact : T.wordAt r.challenges m le_rfl = r.finalWord statement
  · right
    exact accepts_ideal_or_receiptCollision pcs (toRawStatement statement T) pins r.toRaw
      (raw_accepts_of_succinct pcs statement pins r T hcons accepted finalExact)
  · left
    obtain ⟨point, hpoint⟩ := Function.ne_iff.mp finalExact
    refine ⟨point, ?_⟩
    have hroot : T.rootAt r.challenges m le_rfl = (pcs.opening m).commit (r.finalWord statement) := by
      rw [hcons m le_rfl]
      exact accepted.2.2.2.2.2.2
    have hverify : (pcs.opening m).verifyOpen (T.rootAt r.challenges m le_rfl) point
        (r.finalWord statement point) ((pcs.opening m).openAt (r.finalWord statement) point) := by
      rw [hroot]
      exact (pcs.opening m).verifyOpen_commit _ point
    rcases pcs.accepted_value_eq_or_extractedCollision m (T.wordAt r.challenges m le_rfl)
        (T.rootAt r.challenges m le_rfl) point (r.finalWord statement point)
        ((pcs.opening m).openAt (r.finalWord statement) point)
        (T.rootAt_eq_commit r.challenges m le_rfl) hverify with equal | collision
    · exact False.elim (hpoint equal.symm)
    · exact collision

/-! ## Inhabitation: every transcript is consistent with the receipt that reads its roots -/

/-- Reading `T`'s roots into a receipt makes `T` consistent with it, so the soundness theorem
quantifies over a nonempty set of strategies for every receipt shape. -/
theorem consistent_of_roots {pcs : RawMerklePcs ell} (statement : SuccinctStatement ell m)
    (T : RawTranscript pcs) (challenges : Fin m → Tower256)
    (querySeed : Fin queryCount → PowerTwoFriLevels ell 1)
    (opening : (j : Fin m) → Fin queryCount → FriQueryOpening Tower256 (List UInt8) (List UInt8))
    (finalCoeffs : List C8) :
    Consistent statement
      ({ roots := fun n => T.rootAt challenges n (Nat.le_of_lt_succ n.isLt)
         challenges := challenges, querySeed := querySeed, opening := opening,
         finalCoeffs := finalCoeffs } : SuccinctReceipt ell m queryCount) T := by
  intro n hn
  rfl

/-- info: 'Minidregg.Compiler.Tower256AdditiveFriSuccinctController.raw_accepts_of_succinct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms raw_accepts_of_succinct
/-- info: 'Minidregg.Compiler.Tower256AdditiveFriSuccinctController.succinct_accepts_ideal_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms succinct_accepts_ideal_or_collision

end

end Minidregg.Compiler.Tower256AdditiveFriSuccinctController
