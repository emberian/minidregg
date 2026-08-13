/-
# Assurance.SemanticHistoryWARPAdditiveJoin -- pre-challenge links, post-challenge folds

This module makes the ordering distinction needed to connect semantic history
to the already-proved, unshifted BCS accumulator alphabet:

* the exact link word and its binding root are fixed before the round challenge;
* the next folded word/root are fixed only after that challenge; and
* the terminal folded root is the level-zero root of the existing additive-FRI
  checkpoint.

For a finite coordinate carrier, `BcsLinkOpenings` additionally reindexes the
same commitment and RS domain to `Fin _`.  The landed `bcsWord_committed`
theorem then proves that every opened BCS message synthesizes the exact link
word, and `bcsRounds_exact` identifies the entire unshifted BCS transcript.

This is deliberately not a new common security game.  The concrete PCS,
commitment collision resistance, and Fiat--Shamir ROM realization remain the
external premises of the imported layers.  Nor does this file claim that the
semantic claim carrier is definitionally the `Fin _` carrier required by
`accReductionBcs`; that separate claim/genesis reindexing is named at the
bottom.
-/

import Assurance.SemanticAdditiveFriCheckpoint
import Selvage.AccRbrBcs

namespace Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin

open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticHistoryStraightlinePcs
open Minidregg.Assurance.SemanticAdditiveFriCheckpoint
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.AdditiveFriReceiptClause
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Selvage
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe uOp

noncomputable section

/-! ## The canonical dual-root schedule -/

variable {F : Type} [Field F]
variable {ι : Type*} {Op : Type uOp}
variable {C : Submodule F (ι → F)}
variable {S : BindingCommitment Digest F ι Op}
variable {foldRoot : Digest → F → Digest → Digest}
variable {rounds : Nat}

/-- Restrict a complete challenge vector to the challenges strictly preceding
level `j`. -/
def challengePrefix (challenges : Fin rounds → F)
    (j : Nat) (hj : j ≤ rounds) : Fin j → F :=
  fun i => challenges ⟨i, lt_of_lt_of_le i.isLt hj⟩

/-- A `FoldRootSchedule` together with its actual Lean-controller challenges.
The link root below does not receive those challenges as an argument; the next
fold root does.  This is the unshifted WARP/BCS ordering. -/
structure DualRootSchedule where
  base : FoldRootSchedule C S foldRoot rounds
  challenges : Fin rounds → F

/-- Canonical constructor from a landed prefix-typed fold schedule. -/
def dualRootOfSchedule
    (base : FoldRootSchedule C S foldRoot rounds)
    (challenges : Fin rounds → F) :
    DualRootSchedule (C := C) (S := S) (foldRoot := foldRoot)
      (rounds := rounds) :=
  ⟨base, challenges⟩

namespace DualRootSchedule

variable (schedule : DualRootSchedule
  (C := C) (S := S) (foldRoot := foldRoot) (rounds := rounds))

/-- The root sent before round `j`'s challenge.  Its type and definition have
no challenge input. -/
def linkRoot (j : Fin rounds) : Digest :=
  S.commit (schedule.base.linkWord j)

/-- The accumulator root immediately before round `j`. -/
def priorRoot (j : Fin rounds) : Digest :=
  schedule.base.rootAt j (challengePrefix schedule.challenges j j.isLt.le)

/-- The accumulator root sent after round `j`'s challenge has been derived. -/
def foldedRoot (j : Fin rounds) : Digest :=
  schedule.base.rootAt (j + 1)
    (Fin.snoc (challengePrefix schedule.challenges j j.isLt.le)
      (schedule.challenges j))

/-- The pre-challenge root is exactly the binding commitment to the scheduled
link word. -/
@[simp] theorem linkRoot_exact (j : Fin rounds) :
    schedule.linkRoot j = S.commit (schedule.base.linkWord j) :=
  rfl

/-- View the already-fixed link root from a prospective challenge value. -/
def linkRootAtProspectiveChallenge (j : Fin rounds) (_gamma : F) : Digest :=
  schedule.linkRoot j

/-- A named ordering tooth: changing a prospective challenge cannot change
the already-fixed link root. -/
theorem linkRoot_before_challenge (j : Fin rounds) (left right : F) :
    schedule.linkRootAtProspectiveChallenge j left =
      schedule.linkRootAtProspectiveChallenge j right := by
  rfl

/-- After the challenge, the folded root is the exact `foldRoot` application
to the prior accumulator root, that challenge, and the precommitted link root. -/
theorem foldedRoot_after_challenge (j : Fin rounds) :
    schedule.foldedRoot j =
      foldRoot (schedule.priorRoot j) (schedule.challenges j)
        (schedule.linkRoot j) := by
  exact schedule.base.foldRootExact j
    (challengePrefix schedule.challenges j j.isLt.le)
    (schedule.challenges j)

/-- The same post-challenge root commits the literal arithmetic fold. -/
theorem foldedRoot_commits_folded_word (j : Fin rounds) :
    schedule.foldedRoot j =
      S.commit
        (schedule.base.wordAt j
            (challengePrefix schedule.challenges j j.isLt.le) +
          schedule.challenges j • schedule.base.linkWord j) := by
  rw [schedule.foldedRoot_after_challenge]
  exact schedule.base.foldRoot_commits_folded_word j
    (challengePrefix schedule.challenges j j.isLt.le)
    (schedule.challenges j)

/-- The terminal folded root for the complete challenge vector. -/
def terminalRoot : Digest :=
  schedule.base.rootAt rounds schedule.challenges

end DualRootSchedule

/-! ## Exact reindexing into the deployed `Fin _` BCS alphabet -/

section BcsProjection

variable [Fintype F] [DecidableEq F]
variable [Fintype ι] [DecidableEq ι]

abbrev FiniteCoordinateCount (ι : Type*) [Fintype ι] := Fintype.card ι

/-- Canonical finite-coordinate reindexing used only at the BCS API boundary. -/
noncomputable def coordinateEquiv :
    ι ≃ Fin (FiniteCoordinateCount ι) :=
  Fintype.equivFin ι

/-- A word on the semantic coordinate carrier, read in canonical `Fin` order. -/
noncomputable def reindexWord (word : ι → F) :
    Fin (FiniteCoordinateCount ι) → F :=
  fun k => word ((coordinateEquiv (ι := ι)).symm k)

/-- The same evaluation embedding in canonical `Fin` order. -/
noncomputable def reindexDomain (domain : ι ↪ F) :
    Fin (FiniteCoordinateCount ι) ↪ F :=
  ⟨fun k => domain ((coordinateEquiv (ι := ι)).symm k),
    fun _ _ h => (coordinateEquiv (ι := ι)).symm.injective (domain.injective h)⟩

/-- The same binding commitment, reindexed rather than recommitted. -/
noncomputable def reindexCommitment :
    BindingCommitment Digest F (Fin (FiniteCoordinateCount ι)) Op where
  commit word := S.commit (fun i => word (coordinateEquiv (ι := ι) i))
  openAt word k :=
    S.openAt (fun i => word (coordinateEquiv (ι := ι) i))
      ((coordinateEquiv (ι := ι)).symm k)
  verifyOpen root k value opening :=
    S.verifyOpen root ((coordinateEquiv (ι := ι)).symm k) value opening
  verifyOpen_commit := by
    intro word k
    simpa using S.verifyOpen_commit
      (fun i => word (coordinateEquiv (ι := ι) i))
      ((coordinateEquiv (ι := ι)).symm k)
  binding := by
    intro root k left right leftOpening rightOpening hleft hright
    exact S.binding root ((coordinateEquiv (ι := ι)).symm k)
      left right leftOpening rightOpening hleft hright

@[simp] theorem reindexCommitment_commit (word : ι → F) :
    (reindexCommitment (S := S)).commit (reindexWord word) = S.commit word := by
  change S.commit
    (fun i => reindexWord word (coordinateEquiv (ι := ι) i)) = S.commit word
  congr 1
  funext i
  simp [reindexWord]

/-- RS membership is invariant under this exact coordinate/domain reindexing. -/
theorem reindexWord_mem_reedSolomonCode
    (domain : ι ↪ F) (degree : Nat) (word : ι → F)
    (hword : word ∈ reedSolomonCode domain degree) :
    reindexWord word ∈ reedSolomonCode (reindexDomain domain) degree := by
  rw [mem_reedSolomonCode_iff] at hword ⊢
  obtain ⟨poly, hdegree, hpoly⟩ := hword
  refine ⟨poly, hdegree, fun k => ?_⟩
  simp only [reindexWord, reindexDomain]
  exact hpoly ((coordinateEquiv (ι := ι)).symm k)

/-- Concrete opened BCS messages for all pre-challenge link roots.  The only
message roots admitted here are the exact roots of `schedule.base.linkWord`.
Opening verification is carried explicitly and is the PCS/commitment seam. -/
structure BcsLinkOpenings
    {BcsOp : Type}
    (S0 : BindingCommitment Digest F ι BcsOp)
    (schedule : DualRootSchedule
      (C := C) (S := S0) (foldRoot := foldRoot) (rounds := rounds))
    (domain : ι ↪ F) (degree openedCount : Nat) where
  degreeLeOpened : degree ≤ openedCount
  queries : Fin openedCount → Fin (FiniteCoordinateCount ι)
  queriesDistinct : Function.Injective (reindexDomain domain ∘ queries)
  messages : Fin rounds → BcsMsg Digest F BcsOp openedCount
  rootExact : ∀ j,
    (messages j).root = schedule.linkRoot j
  columnsOpen : ∀ j,
    ColsOpen (reindexCommitment (S := S0)) queries (messages j)

namespace BcsLinkOpenings

variable {BcsOp : Type}
variable {S0 : BindingCommitment Digest F ι BcsOp}
variable {schedule : DualRootSchedule
  (C := C) (S := S0) (foldRoot := foldRoot) (rounds := rounds)}
variable {domain : ι ↪ F} {degree openedCount : Nat}

/-- Commitment binding plus erasure recovery identifies every BCS message's
synthesized word with the exact pre-challenge semantic link word. -/
theorem bcsWord_eq_link
    (links : BcsLinkOpenings S0 schedule domain degree openedCount)
    (codeExact : C = reedSolomonCode domain degree)
    (j : Fin rounds) :
    bcsWord (reindexDomain domain) degree links.queries (links.messages j) =
      reindexWord (schedule.base.linkWord j) := by
  apply bcsWord_committed (reindexCommitment (S := S0))
    (reindexDomain domain) links.degreeLeOpened links.queriesDistinct
  · apply reindexWord_mem_reedSolomonCode
    simpa only [← codeExact] using schedule.base.linkCodeword j
  · calc
      (links.messages j).root = schedule.linkRoot j := links.rootExact j
      _ = S0.commit (schedule.base.linkWord j) := rfl
      _ = (reindexCommitment (S := S0)).commit
          (reindexWord (schedule.base.linkWord j)) := by
        rw [reindexCommitment_commit]
  · exact links.columnsOpen j

/-- Exact transcript projection into `AccRbrBcs`'s unshifted word reader:
every root/opening message precedes and synthesizes its link word, while the
paired challenge is unchanged. -/
theorem bcsRounds_exact
    (links : BcsLinkOpenings S0 schedule domain degree openedCount)
    (codeExact : C = reedSolomonCode domain degree) :
    bcsRounds (reindexDomain domain) degree links.queries
        (List.ofFn fun j => (links.messages j, schedule.challenges j)) =
      List.ofFn fun j =>
        (reindexWord (schedule.base.linkWord j), schedule.challenges j) := by
  rw [bcsRounds_ofFn]
  apply congrArg List.ofFn
  funext j
  rw [links.bcsWord_eq_link codeExact j]

end BcsLinkOpenings

end BcsProjection

/-! ## The semantic/additive checkpoint join -/

universe uSemantics uFriOp uTranscript
  uClauseInput uClauseQuery uClauseReply uClauseOutcome uClauseEvidence

variable {F : Type} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
variable {ell m n : Nat} {FriOp : Nat → Type uFriOp}
variable (friS : ∀ level, BindingCommitment Digest F
  (AdditiveFriLevels ell level) (FriOp level))
variable [DecidableEq F]
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext → BindingIx → F}
    {clause : FriClause m manifest friS}
    {Coin : Type} [Fintype Coin] [DecidableEq Coin]
    {Transcript : Type uTranscript}

local notation "BoundCheckpoint" => Checkpoint
  (n := n) (F := F) (ell := ell) (m := m) (FriOp := FriOp)
  (manifest := manifest)
  (registry := registry) (clauseEvidence := clauseEvidence)
  (family := family) (headerCells := headerCells) friS clause

/-- The WARP dual-root view of a checkpoint is constructed from the
authoritative trace-retained challenges.  The caller supplies only the PCS
realization whose words are exactly bound to that trace. -/
def historyDualRootSchedule
    (checkpoint : BoundCheckpoint)
    (joined : StraightlineCheckpointExtraction
      (n := n) (F := F) (ell := ell) (m := m) (FriOp := FriOp)
      (manifest := manifest)
      (registry := registry) (clauseEvidence := clauseEvidence)
      (family := family) (headerCells := headerCells)
      friS clause checkpoint Coin Transcript) :=
  dualRootOfSchedule joined.schedule checkpoint.head.foldChallenges

/-- Every pre-challenge WARP/BCS link word is the exact word indexed by the
retained semantic history trace. -/
theorem historyDualRootSchedule_linkWord_exact
    (checkpoint : BoundCheckpoint)
    (joined : StraightlineCheckpointExtraction
      (n := n) (F := F) (ell := ell) (m := m) (FriOp := FriOp)
      (manifest := manifest)
      (registry := registry) (clauseEvidence := clauseEvidence)
      (family := family) (headerCells := headerCells)
      friS clause checkpoint Coin Transcript)
    (j : Fin checkpoint.head.foldRounds) :
    (historyDualRootSchedule friS checkpoint joined).base.linkWord j =
      checkpoint.head.foldLinkWord j := by
  simpa [historyDualRootSchedule, historyLinkWord] using
    joined.scheduleBinding.linkWordExact j

/-- The semantic schedule's terminal post-challenge fold root is exactly the
existing additive-FRI checkpoint's level-zero root.  No root-bridge premise is
introduced: both equalities are already proved by the imported layers. -/
theorem terminal_root_eq_additive_initial
    (checkpoint : BoundCheckpoint)
    (joined : StraightlineCheckpointExtraction
      (n := n) (F := F) (ell := ell) (m := m) (FriOp := FriOp)
      (manifest := manifest)
      (registry := registry) (clauseEvidence := clauseEvidence)
      (family := family) (headerCells := headerCells)
      friS clause checkpoint Coin Transcript) :
    (historyDualRootSchedule friS checkpoint joined).terminalRoot =
      clause.transcript.root 0 (fun i => i.elim0) := by
  calc
    (historyDualRootSchedule friS checkpoint joined).terminalRoot =
        checkpoint.head.accumulator.rt :=
      joined.scheduleBinding.finalRootExact checkpoint.head
    _ = clause.transcript.root 0 (fun i => i.elim0) :=
      (Checkpoint.initial_root_eq_semantic_head checkpoint).symm

/- Exact residual for the next layer.  `bcsRounds_exact` closes the deployed
message/root/opening transcript projection.  Invoking `accReductionBcs` itself
also requires an exact reindexing of the semantic genesis and every link
`AccClaim` to its `Fin _` carrier, plus the existing mutual-correlated-
agreement, ROM, commitment-CR, and PCS premises.  This boundary is recorded
without asserting that carrier join here. -/
/-- info: 'Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin.DualRootSchedule.foldedRoot_after_challenge' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DualRootSchedule.foldedRoot_after_challenge
/-- info: 'Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin.DualRootSchedule.foldedRoot_commits_folded_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DualRootSchedule.foldedRoot_commits_folded_word
/-- info: 'Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin.BcsLinkOpenings.bcsRounds_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BcsLinkOpenings.bcsRounds_exact
/-- info: 'Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin.historyDualRootSchedule_linkWord_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms historyDualRootSchedule_linkWord_exact
/-- info: 'Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin.terminal_root_eq_additive_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms terminal_root_eq_additive_initial

end

end Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin
