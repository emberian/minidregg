/-
# Assurance.SemanticHistoryBcsGame -- trace-derived BCS/common-game boundary

This module removes the last caller-selected semantic schedule from the
unshifted BCS accumulator boundary.  The genesis claim, link chain, link
words, and challenges are reconstructed by recursion on the
`HistoryFoldTrace` retained inside `VerifiedHistoryHead`.  The only supplied
BCS data are actual opened root/column messages and genuine deployment
premises: mutual correlated agreement, PCS opening soundness, commitment
binding/collision resistance, and oracle transport.

No second accumulator relation is introduced.  The chain below contains the
existing Loom `AccClaim`s of the post-genesis semantic entries, and its
aggregate is proved equal to the head's authoritative accumulator.  Native
code has no role in this construction.
-/

import Assurance.SemanticHistoryBcsClaimProjection
import Assurance.ProofCompositionGame

namespace Minidregg.Assurance.SemanticHistoryBcsGame

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryBcsClaimProjection
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticHistoryStraightlinePcs
open Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

universe uSemantics uClauseInput uClauseQuery uClauseReply
  uClauseOutcome uClauseEvidence uPayload uPhase

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : Nat} {Op : Type}
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext → BindingIx → F}
    {C : Submodule F (BoundReceiptIx n → F)}
    {S : BindingCommitment Digest F (BoundReceiptIx n) Op}

local notation "HistoryEntry" => VerifiedEntry
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C)

local notation "HistoryHead" => VerifiedHistoryHead
  (n := n) (F := F) (Op := Op) manifest registry clauseEvidence family
  headerCells C S

abbrev ReceiptChannels (n : Nat) := Fintype.card (BoundReceiptIx n)

theorem listGet_append_left {α : Type} (left right : List α)
    (k : Fin left.length) :
    (left ++ right).get
        ⟨k.val, lt_of_lt_of_le k.isLt (by simp)⟩ = left.get k := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact List.getElem_append_left k.isLt

theorem listGet_append_last {α : Type} (left : List α) (value : α) :
    (left ++ [value]).get ⟨left.length, by simp⟩ = value := by
  rw [List.get_eq_getElem]
  rw [List.getElem_append_right (le_refl left.length)]
  simp

/-! ## The unique unshifted carrier derived from `HistoryFoldTrace` -/

/-- A semantic entry viewed as the existing Loom history-link object.  Its
claim is literally the entry claim at the entry's binding root. -/
def entryLink (entry : HistoryEntry) :
    Link Digest F (BoundReceiptIx n) (ReceiptChannels n) where
  pre := entry.context.preStateRoot
  post := entry.context.postStateRoot
  claim := entry.claim.acc (entry.receiptRoot S)

/-- The genesis claim selected by a retained trace. -/
def traceGenesisClaim
    {rounds : Nat} {entries : List HistoryEntry}
    {accumulator : AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n)}
    {foldedWord initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord) :
    AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n) :=
  match trace with
  | .start entry => entry.claim.acc (entry.receiptRoot S)
  | .append prior _ _ _ => traceGenesisClaim prior

/-- The post-genesis chain selected by a retained trace. -/
def traceLinkChain
    {rounds : Nat} {entries : List HistoryEntry}
    {accumulator : AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n)}
    {foldedWord initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord) :
    Chain Digest F (BoundReceiptIx n) (ReceiptChannels n) :=
  match trace with
  | .start _ => []
  | .append prior entry _ _ =>
      traceLinkChain prior ++ [entryLink (S := S) entry]

/-- The exact post-genesis word list selected by a retained trace. -/
def traceLinkWords
    {rounds : Nat} {entries : List HistoryEntry}
    {accumulator : AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n)}
    {foldedWord initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord) :
    List (BoundReceiptIx n → F) :=
  match trace with
  | .start _ => []
  | .append prior entry _ _ => traceLinkWords prior ++ [entry.word]

theorem traceLinkChain_length
    {rounds : Nat} {entries : List HistoryEntry}
    {accumulator : AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n)}
    {foldedWord initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord) :
    (traceLinkChain trace).length = rounds := by
  induction trace with
  | start entry => rfl
  | append prior entry gamma rootExact ih =>
      simp [traceLinkChain, ih]

theorem traceLinkWords_length
    {rounds : Nat} {entries : List HistoryEntry}
    {accumulator : AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n)}
    {foldedWord initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord) :
    (traceLinkWords trace).length = rounds := by
  induction trace with
  | start entry => rfl
  | append prior entry gamma rootExact ih =>
      simp [traceLinkWords, ih]

/-- The recursively reconstructed word list is exactly the trace's indexed
link-word family; no consumer can substitute a parallel witness schedule. -/
theorem traceLinkWords_eq_ofFn
    {rounds : Nat} {entries : List HistoryEntry}
    {accumulator : AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n)}
    {foldedWord initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord) :
    traceLinkWords trace = List.ofFn linkWord := by
  induction trace with
  | start entry => simp [traceLinkWords]
  | @append rounds entries accumulator foldedWord initialWord challenges
      linkWord prior entry gamma rootExact ih =>
      rw [traceLinkWords, ih, List.ofFn_succ']
      simp

/-- Every retained trace reconstructs the authoritative accumulator exactly
by running Loom's existing aggregate over the reconstructed genesis and
post-genesis chain. -/
theorem traceAggregate_eq_accumulator
    {rounds : Nat} {entries : List HistoryEntry}
    {accumulator : AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n)}
    {foldedWord initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord) :
    aggregate foldRoot (padSched challenges) (traceGenesisClaim trace)
        (traceLinkChain trace) = accumulator := by
  induction trace with
  | start entry => rfl
  | @append rounds entries accumulator foldedWord initialWord challenges
      linkWord prior entry gamma rootExact ih =>
      rw [traceLinkChain, aggregate_snoc]
      have hprefix :
          aggregate foldRoot (padSched (Fin.snoc challenges gamma))
              (traceGenesisClaim prior) (traceLinkChain prior) =
            aggregate foldRoot (padSched challenges)
              (traceGenesisClaim prior) (traceLinkChain prior) := by
        apply aggregate_congr_sched
        intro j hj
        rw [traceLinkChain_length prior] at hj
        rw [padSched_lt _ (lt_trans hj (Nat.lt_succ_self rounds)),
          padSched_lt _ hj]
        exact @Fin.snoc_castSucc rounds (fun _ => F) gamma challenges ⟨j, hj⟩
      simp only [traceGenesisClaim]
      rw [hprefix, ih]
      have hlast :
          padSched (Fin.snoc challenges gamma) (traceLinkChain prior).length =
            gamma := by
        rw [traceLinkChain_length prior]
        rw [padSched_lt _ (Nat.lt_succ_self rounds)]
        exact @Fin.snoc_last rounds (fun _ => F) gamma challenges
      rw [hlast]
      rfl

/-- The word-side fold of the same trace-derived schedule is the head's
literal retained folded word. -/
theorem traceFoldWords_eq_foldedWord
    {rounds : Nat} {entries : List HistoryEntry}
    {accumulator : AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n)}
    {foldedWord initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord) :
    foldWords (padSched challenges) initialWord (traceLinkWords trace) = foldedWord := by
  induction trace with
  | start entry => rfl
  | @append rounds entries accumulator foldedWord initialWord challenges
      linkWord prior entry gamma rootExact ih =>
      rw [traceLinkWords, foldWords_snoc]
      have hprefix :
          foldWords (padSched (Fin.snoc challenges gamma)) initialWord
              (traceLinkWords prior) =
            foldWords (padSched challenges) initialWord (traceLinkWords prior) := by
        apply foldWords_congr_sched
        intro j hj
        rw [traceLinkWords_length prior] at hj
        rw [padSched_lt _ (lt_trans hj (Nat.lt_succ_self rounds)),
          padSched_lt _ hj]
        exact @Fin.snoc_castSucc rounds (fun _ => F) gamma challenges ⟨j, hj⟩
      rw [hprefix, ih]
      have hlast :
          padSched (Fin.snoc challenges gamma) (traceLinkWords prior).length =
            gamma := by
        rw [traceLinkWords_length prior]
        rw [padSched_lt _ (Nat.lt_succ_self rounds)]
        exact @Fin.snoc_last rounds (fun _ => F) gamma challenges
      rw [hlast]

/-- Every trace-derived genesis claim has the canonical semantic receipt
channel, independently of history depth. -/
theorem traceGenesis_weights
    {rounds : Nat} {entries : List HistoryEntry}
    {accumulator : AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n)}
    {foldedWord initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord)
    (channel : Fin (ReceiptChannels n)) :
    (traceGenesisClaim trace).weights channel =
      boundEvalAt (boundReceiptCoord channel) := by
  induction trace with
  | start entry => rfl
  | append prior entry gamma rootExact ih =>
      exact ih

/-- Each indexed trace link word is an admitted semantic codeword. -/
theorem traceLinkWord_mem
    {rounds : Nat} {entries : List HistoryEntry}
    {accumulator : AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n)}
    {foldedWord initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord) :
    ∀ j, linkWord j ∈ C := by
  induction trace with
  | start entry =>
      intro j
      exact j.elim0
  | @append rounds entries accumulator foldedWord initialWord challenges
      linkWord prior entry gamma rootExact ih =>
      intro j
      refine Fin.lastCases ?_ (fun priorIndex => ?_) j
      · simpa using entry.codeword
      · simpa using ih priorIndex

/-- The genesis word and every trace-derived link word satisfy exactly the
source relation of the unshifted accumulator reduction. -/
theorem traceSource_aligned
    {rounds : Nat} {entries : List HistoryEntry}
    {accumulator : AccClaim Digest F (BoundReceiptIx n) (ReceiptChannels n)}
    {foldedWord initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord) :
    AccClaim.Satisfies C (traceGenesisClaim trace) initialWord ∧
      ∀ j : Fin rounds,
        TypedLinkAligned C (traceGenesisClaim trace) (traceLinkChain trace)
          (Fin.cast (traceLinkChain_length trace).symm j) (linkWord j) := by
  induction trace with
  | start entry =>
      constructor
      · exact (entry.claim.acc_satisfies_iff (entry.receiptRoot S) entry.word).mpr
          ⟨entry.codeword, rfl⟩
      · intro j
        exact j.elim0
  | @append rounds entries accumulator foldedWord initialWord challenges
      linkWord prior entry gamma rootExact ih =>
      refine ⟨ih.1, ?_⟩
      intro j
      refine Fin.lastCases ?_ (fun priorIndex => ?_) j
      · have hindex :
            Fin.cast (traceLinkChain_length
              (prior.append entry gamma rootExact)).symm (Fin.last rounds) =
              ⟨(traceLinkChain prior).length, by
                rw [traceLinkChain]
                simp⟩ := by
          apply Fin.ext
          simp [traceLinkChain_length prior]
        rw [hindex]
        simp only [traceGenesisClaim, Fin.snoc_last]
        change TypedLinkAligned C (traceGenesisClaim prior)
          (traceLinkChain prior ++ [entryLink (S := S) entry])
          ⟨(traceLinkChain prior).length, by simp⟩ entry.word
        unfold TypedLinkAligned
        rw [listGet_append_last]
        have hsat :=
          (entry.claim.acc_satisfies_iff (entry.receiptRoot S) entry.word).mpr
            ⟨entry.codeword, rfl⟩
        refine ⟨entry.codeword, fun channel => ?_⟩
        rw [traceGenesis_weights prior]
        simpa [traceLinkChain, entryLink] using hsat.2 channel
      · have hprior := ih.2 priorIndex
        have hindex :
            Fin.cast (traceLinkChain_length
              (prior.append entry gamma rootExact)).symm priorIndex.castSucc =
              ⟨priorIndex.val, by
                rw [traceLinkChain]
                simp [traceLinkChain_length prior]⟩ := by
          apply Fin.ext
          rfl
        rw [hindex]
        simp only [traceGenesisClaim, Fin.snoc_castSucc]
        change TypedLinkAligned C (traceGenesisClaim prior)
          (traceLinkChain prior ++ [entryLink (S := S) entry])
          ⟨priorIndex.val, by
            rw [List.length_append]
            simp only [List.length_singleton, Nat.lt_add_one_iff]
            have hp : priorIndex.val < (traceLinkChain prior).length := by
              simpa only [traceLinkChain_length] using priorIndex.isLt
            exact Nat.le_of_lt hp⟩ (linkWord priorIndex)
        unfold TypedLinkAligned at hprior ⊢
        refine ⟨hprior.1, fun channel => ?_⟩
        have hp : priorIndex.val < (traceLinkChain prior).length := by
          simpa only [traceLinkChain_length] using priorIndex.isLt
        have hget :
            (traceLinkChain prior ++ [entryLink (S := S) entry]).get
                ⟨priorIndex.val, by
                  rw [List.length_append]
                  simp only [List.length_singleton, Nat.lt_add_one_iff]
                  exact Nat.le_of_lt hp⟩ =
              (traceLinkChain prior).get ⟨priorIndex.val, hp⟩ :=
          listGet_append_left (traceLinkChain prior)
            [entryLink (S := S) entry] ⟨priorIndex.val, hp⟩
        rw [hget]
        have hk : (⟨priorIndex.val, hp⟩ : Fin (traceLinkChain prior).length) =
            Fin.cast (traceLinkChain_length prior).symm priorIndex := Fin.ext rfl
        rw [hk]
        exact hprior.2 channel

/-! ## Head-derived reduction and opened BCS transcript -/

/-- The unique Loom genesis claim retained by this head. -/
def historyGenesisClaim (head : HistoryHead) :=
  traceGenesisClaim head.foldTrace

/-- The unique post-genesis Loom chain retained by this head. -/
def historyChain (head : HistoryHead) :=
  traceLinkChain head.foldTrace

@[simp] theorem historyChain_length (head : HistoryHead) :
    (historyChain head).length = head.foldRounds :=
  traceLinkChain_length head.foldTrace

/-- Canonical equivalence between reduction rounds and retained trace rounds. -/
def historyRoundEquiv (head : HistoryHead) :
    Fin (historyChain head).length ≃ Fin head.foldRounds :=
  Fin.castOrderIso (historyChain_length head)

/-- The reduction witness is read only from the head's retained link words. -/
def historyLinkWitness (head : HistoryHead) :
    Fin (historyChain head).length → BoundReceiptIx n → F :=
  fun k => head.foldLinkWord (historyRoundEquiv head k)

/-- The reduction challenges are read only from the head's retained fold
challenges. -/
def historyChallenge (head : HistoryHead) :
    Fin (historyChain head).length → F :=
  fun k => head.foldChallenges (historyRoundEquiv head k)

/-- The head's authoritative accumulator is exactly the trace-derived
unshifted aggregate. -/
theorem history_aggregate_exact (head : HistoryHead) :
    aggregate head.foldRoot (padSched head.foldChallenges)
        (historyGenesisClaim head) (historyChain head) = head.accumulator :=
  traceAggregate_eq_accumulator head.foldTrace

/-- The head's authoritative folded word is exactly the trace-derived
unshifted word fold. -/
theorem history_foldedWord_exact (head : HistoryHead) :
    foldWords (padSched head.foldChallenges) head.initialWord
        (List.ofFn head.foldLinkWord) = head.foldedWord := by
  rw [← traceLinkWords_eq_ofFn head.foldTrace]
  exact traceFoldWords_eq_foldedWord head.foldTrace

/-- Every retained head link word is in the semantic code, as a consequence
of its proof-relevant fold trace rather than a parallel witness schedule. -/
theorem historyLinkWord_mem (head : HistoryHead) (j : Fin head.foldRounds) :
    head.foldLinkWord j ∈ C :=
  traceLinkWord_mem head.foldTrace j

/-- Reindexing the round type changes no challenge consumed by the chain. -/
theorem history_aggregate_at_round_index_exact (head : HistoryHead) :
    aggregate head.foldRoot (padSched (historyChallenge head))
        (historyGenesisClaim head) (historyChain head) = head.accumulator := by
  rw [← history_aggregate_exact head]
  apply aggregate_congr_sched
  intro j hj
  rw [padSched_lt _ hj, padSched_lt _ (by simpa [historyChain_length] using hj)]
  rfl

/-- The reindexed round family enumerates exactly the retained link-word
family; the cast witnesses only the proved length equality. -/
theorem historyLinkWitness_ofFn (head : HistoryHead) :
    List.ofFn (historyLinkWitness head) = List.ofFn head.foldLinkWord := by
  apply List.ext_get
  · simp [historyChain_length]
  · intro j hleft hright
    simp [historyLinkWitness, historyRoundEquiv]

/-- The reduction-indexed word fold is therefore the head's literal retained
folded word. -/
theorem history_foldedWord_at_round_index_exact (head : HistoryHead) :
    foldWords (padSched (historyChallenge head)) head.initialWord
        (List.ofFn (historyLinkWitness head)) = head.foldedWord := by
  rw [historyLinkWitness_ofFn]
  rw [← history_foldedWord_exact head]
  apply foldWords_congr_sched
  intro j hj
  rw [List.length_ofFn] at hj
  rw [padSched_lt _ (by simpa [historyChain_length] using hj),
    padSched_lt _ hj]
  rfl

/-- The trace-derived source relation, with no caller-selected chain, genesis,
word family, or challenge schedule. -/
theorem history_source_aligned (head : HistoryHead) :
    AccClaim.Satisfies C (historyGenesisClaim head) head.initialWord ∧
      ∀ k : Fin (historyChain head).length,
        TypedLinkAligned C (historyGenesisClaim head) (historyChain head) k
          (historyLinkWitness head k) := by
  refine ⟨(traceSource_aligned head.foldTrace).1, fun k => ?_⟩
  simpa [historyGenesisClaim, historyChain, historyLinkWitness,
    historyRoundEquiv] using
    (traceSource_aligned head.foldTrace).2 (historyRoundEquiv head k)

/-- Semantic receipt coordinates are nonempty independently of history
depth: the binding/header summand has constructors. -/
theorem receiptCoordinateCountPositive :
    0 < CoordinateCount (BoundReceiptIx n) := by
  exact Fintype.card_pos

/-- Actual BCS messages for the exact roots and words retained by one head.
The structure is the PCS/commitment seam: it contains verified openings, not
a Boolean or an unconstrained parallel schedule. -/
structure HistoryBcsOpenings
    (head : HistoryHead)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat) where
  codeExact : C = reedSolomonCode domain degree
  degreeLeOpened : degree ≤ openedCount
  queries : Fin openedCount → Fin (CoordinateCount (BoundReceiptIx n))
  queriesDistinct : Function.Injective (reindexDomain domain ∘ queries)
  messages : Fin head.foldRounds → BcsMsg Digest F Op openedCount
  rootExact : ∀ j,
    (messages j).root = S.commit (head.foldLinkWord j)
  columnsOpen : ∀ j,
    ColsOpen (reindexCommitment (S := S)) queries (messages j)

/-- A carrier-generic binding/recovery tooth used by the head-specific
transcript theorem below. -/
theorem reindexedBcsWord_committed
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (degreeLeOpened : degree ≤ openedCount)
    (queries : Fin openedCount → Fin (CoordinateCount (BoundReceiptIx n)))
    (queriesDistinct : Function.Injective (reindexDomain domain ∘ queries))
    (word : BoundReceiptIx n → F)
    (wordInCode : word ∈ reedSolomonCode domain degree)
    (message : BcsMsg Digest F Op openedCount)
    (rootExact : message.root = S.commit word)
    (columnsOpen : ColsOpen (reindexCommitment (S := S)) queries message) :
    bcsWord (reindexDomain domain) degree queries message = reindexWord word := by
  apply bcsWord_committed (reindexCommitment (S := S))
    (reindexDomain domain) degreeLeOpened queriesDistinct
  · exact reindexWord_mem_reedSolomonCode domain degree word wordInCode
  · calc
      message.root = S.commit word := rootExact
      _ = (reindexCommitment (S := S)).commit (reindexWord word) := by
        rw [reindexCommitment_commit]
  · exact columnsOpen

namespace HistoryBcsOpenings

variable {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}

/-- Every opened BCS message synthesizes the exact retained trace word.
This is the binding + erasure-recovery step, applied at the actual history
root rather than at a caller-selected schedule. -/
theorem bcsWord_eq_historyLink
    (head : HistoryHead)
    (openings : HistoryBcsOpenings (S := S) head domain degree openedCount)
    (j : Fin head.foldRounds) :
    bcsWord (reindexDomain domain) degree openings.queries
        (openings.messages j) =
      reindexWord (head.foldLinkWord j) := by
  let word := head.foldLinkWord j
  let message := openings.messages j
  have wordInCode : word ∈ reedSolomonCode domain degree := by
    simpa only [← openings.codeExact] using historyLinkWord_mem head j
  have rootExact : message.root = S.commit word := openings.rootExact j
  have columnsOpen :
      ColsOpen (reindexCommitment (S := S)) openings.queries message :=
    openings.columnsOpen j
  exact reindexedBcsWord_committed (S := S) domain degree openedCount
    openings.degreeLeOpened openings.queries openings.queriesDistinct
    word wordInCode message rootExact columnsOpen

/-- The entire opened root/column transcript reads as the head's exact
unshifted word/challenge transcript. -/
theorem bcsRounds_exact
    (head : HistoryHead)
    (openings : HistoryBcsOpenings (S := S) head domain degree openedCount) :
    bcsRounds (reindexDomain domain) degree openings.queries
        (List.ofFn fun j : Fin head.foldRounds =>
          (openings.messages j, head.foldChallenges j)) =
      List.ofFn fun j : Fin head.foldRounds =>
        (reindexWord (head.foldLinkWord j), head.foldChallenges j) := by
  rw [Minidregg.Loom.bcsRounds_ofFn]
  apply congrArg List.ofFn
  funext j
  rw [bcsWord_eq_historyLink head openings j]

end HistoryBcsOpenings

/-! ## The actual trace-derived unshifted BCS reduction -/

/-- `accReductionBcs` at the exact semantic head carrier.  Every semantic
input is derived from `head`; only the protocol parameters and opened PCS
messages remain supplied. -/
@[reducible] noncomputable def historyBcsReduction
    (head : HistoryHead) (historyHasLink : 0 < head.foldRounds)
    (deltaStar : Real) (deltaStarPositive : 0 < deltaStar)
    (deltaStarLeOne : deltaStar ≤ 1)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (openings : HistoryBcsOpenings (S := S) head domain degree openedCount) : Reduction :=
  semanticBcsReduction C head.foldRoot (historyChain head)
    receiptCoordinateCountPositive
    (by simpa [historyChain_length] using historyHasLink)
    deltaStar deltaStarPositive deltaStarLeOne
    (reindexCommitment (S := S)) (reindexDomain domain) degree openings.queries

/-- The actual statement consumed by the history BCS reduction. -/
def historyBcsStatement
    (head : HistoryHead) (historyHasLink : 0 < head.foldRounds)
    (deltaStar : Real) (deltaStarPositive : 0 < deltaStar)
    (deltaStarLeOne : deltaStar ≤ 1)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (openings : HistoryBcsOpenings (S := S) head domain degree openedCount) :
    Stmt (historyBcsReduction head historyHasLink deltaStar deltaStarPositive
      deltaStarLeOne domain degree openedCount openings) :=
  ⟨(), reindexClaim (historyGenesisClaim head), reindexWord head.initialWord⟩

/-- The projected witness family contains exactly the retained semantic link
words, indexed only through the proved round equivalence. -/
def historyBcsWitness (head : HistoryHead) :
    Fin (reindexChain (historyChain head)).length →
      Fin (CoordinateCount (BoundReceiptIx n)) → F :=
  reindexWitness (historyChain head) (historyLinkWitness head)

/-- Deployed messages read on the reduction's exact round type. -/
def historyBcsMessages
    {head : HistoryHead} {domain : BoundReceiptIx n ↪ F}
    {degree openedCount : Nat}
    (openings : HistoryBcsOpenings (S := S) head domain degree openedCount) :
    Fin (reindexChain (historyChain head)).length →
      BcsMsg Digest F Op openedCount :=
  fun k => openings.messages
    (historyRoundEquiv head (chainIndexEquiv (historyChain head) k))

/-- Every reduction-indexed opened message synthesizes the corresponding
trace-derived link word. -/
theorem historyBcsMessages_word
    {head : HistoryHead} {domain : BoundReceiptIx n ↪ F}
    {degree openedCount : Nat}
    (openings : HistoryBcsOpenings (S := S) head domain degree openedCount)
    (k : Fin (reindexChain (historyChain head)).length) :
    bcsWord (reindexDomain domain) degree openings.queries
        (historyBcsMessages openings k) =
      reindexWord
        (historyLinkWitness head (chainIndexEquiv (historyChain head) k)) := by
  exact HistoryBcsOpenings.bcsWord_eq_historyLink head openings
    (historyRoundEquiv head (chainIndexEquiv (historyChain head) k))

/-- The trace-derived statement and witness inhabit the BCS reduction's
source relation. -/
theorem historyBcsReduction_source
    (head : HistoryHead) (historyHasLink : 0 < head.foldRounds)
    (deltaStar : Real) (deltaStarPositive : 0 < deltaStar)
    (deltaStarLeOne : deltaStar ≤ 1)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (openings : HistoryBcsOpenings (S := S) head domain degree openedCount) :
    (historyBcsReduction head historyHasLink deltaStar deltaStarPositive
      deltaStarLeOne domain degree openedCount openings).R
      () (reindexClaim (historyGenesisClaim head))
      (reindexWord head.initialWord) (historyBcsWitness head) := by
  simpa [historyBcsReduction, historyBcsWitness] using
    (semanticBcsReduction_source_iff C head.foldRoot (historyChain head)
      receiptCoordinateCountPositive
      (by simpa [historyChain_length] using historyHasLink)
      deltaStar deltaStarPositive deltaStarLeOne
      (reindexCommitment (S := S)) (reindexDomain domain) degree
      openings.queries (historyGenesisClaim head) head.initialWord
      (historyLinkWitness head)).mpr (history_source_aligned head)

/-- The authoritative head claim and folded word inhabit the target relation
of the same actual BCS reduction. -/
theorem historyBcsReduction_target
    (head : HistoryHead) (historyHasLink : 0 < head.foldRounds)
    (deltaStar : Real) (deltaStarPositive : 0 < deltaStar)
    (deltaStarLeOne : deltaStar ≤ 1)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (openings : HistoryBcsOpenings (S := S) head domain degree openedCount) :
    (historyBcsReduction head historyHasLink deltaStar deltaStarPositive
      deltaStarLeOne domain degree openedCount openings).R'
      () (reindexClaim head.accumulator) (reindexWord head.foldedWord)
      (historyBcsWitness head) := by
  exact (reindexClaim_satisfies_iff C head.accumulator head.foldedWord).mpr
    head.satisfies

/-! ## Ideal mathematics and one common-game deployment boundary -/

/-- The mathematical hypotheses of the ideal unshifted BCS theorem.  These
facts concern the exact reindexed semantic code.  They do not mention a
deployment ledger: in particular, PCS, commitment, and ROM events do not
cause the ideal theorem below. -/
structure HistoryBcsMath (deltaStar : Real) where
  dC : Real
  Bstar : Real
  errstar : Real → Real
  minimumDistance : ∀ u ∈ reindexCode C, ∀ v ∈ reindexCode C,
    u ≠ v → dC ≤ relDist u v
  mutualCorrelatedAgreement :
    HasMutualCorrelatedAgreement (affineGenerator F) (reindexCode C)
      Bstar errstar
  deltaBelowAgreement : deltaStar ≤ 1 - Bstar
  deltaBelowHalfDistance : deltaStar ≤ dC / 2
  errorNonnegative : ∀ delta ∈ Set.Ioo (0 : Real) deltaStar,
    0 ≤ errstar delta

namespace HistoryBcsMath

variable {head : HistoryHead} {historyHasLink : 0 < head.foldRounds}
variable {deltaStar : Real} {deltaStarPositive : 0 < deltaStar}
variable {deltaStarLeOne : deltaStar ≤ 1}
variable {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}
variable {openings : HistoryBcsOpenings (S := S) head domain degree openedCount}

/-- The ideal Def-4.2 BCS knowledge-soundness object for this retained head.
There is no independent genesis, chain, or challenge schedule among its
arguments, and no deployment good event is used to prove it. -/
noncomputable def knowledgeSoundness
    (math : HistoryBcsMath (C := C) deltaStar) :
    RbrKnowledgeSoundness
      (historyBcsReduction head historyHasLink deltaStar deltaStarPositive
        deltaStarLeOne domain degree openedCount openings) :=
  accRbrKnowledgeSoundBcs (reindexCode C) head.foldRoot
    (reindexChain (historyChain head)) receiptCoordinateCountPositive
    (by simpa [historyChain_length] using historyHasLink)
    deltaStar deltaStarPositive deltaStarLeOne
    (reindexCommitment (S := S)) (reindexDomain domain) degree openings.queries
    math.errstar math.minimumDistance
    math.mutualCorrelatedAgreement math.deltaBelowAgreement
    math.deltaBelowHalfDistance math.errorNonnegative

/-- The exact error expression of the trace-derived BCS/Fiat--Shamir
instance.  Naming it keeps the conditional wrapper below definitionally tied
to the very same reduction round count. -/
noncomputable def fsError (head : HistoryHead) (errstar : Real → Real) :
    Nat → Nat → Real → Real :=
  fun _saltBudget grindingBudget delta =>
    ((grindingBudget : Real) +
        ((reindexChain (historyChain head)).length : Real)) *
      accRbrError F errstar delta

/-- Ideal Fiat--Shamir knowledge soundness for the trace-derived BCS
alphabet.  Its proof string has the opened roots/columns/openings shape,
but this theorem itself consumes only the mathematical BCS premises. -/
noncomputable def fiatShamirSoundness
    (math : HistoryBcsMath (C := C) deltaStar)
    (Z : Set (Stmt (historyBcsReduction head historyHasLink deltaStar
      deltaStarPositive deltaStarLeOne domain degree openedCount openings))) :
    FsStraightlineKnowledgeSoundness
      (historyBcsReduction head historyHasLink deltaStar deltaStarPositive
        deltaStarLeOne domain degree openedCount openings) Z
      (fsError (F := F) head math.errstar) :=
  accFsSound_bcs (F := F) (reindexCode C) head.foldRoot
    (reindexChain (historyChain head)) receiptCoordinateCountPositive
    (by simpa [historyChain_length] using historyHasLink)
    deltaStar deltaStarPositive deltaStarLeOne
    (reindexCommitment (S := S)) (reindexDomain domain) degree openings.queries
    math.errstar math.minimumDistance
    math.mutualCorrelatedAgreement math.deltaBelowAgreement
    math.deltaBelowHalfDistance math.errorNonnegative Z

end HistoryBcsMath

/-- Admission of one trace-derived BCS instance to the shared deployment
game.  The constructor is private so `ofNotBad` below is the sole way this
module manufactures the three exact good events on a common coin.  The
mathematical payload remains visibly separate. -/
structure HistoryBcsGameSecurity
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    (head : HistoryHead) (historyHasLink : 0 < head.foldRounds)
    (deltaStar : Real) (domain : BoundReceiptIx n ↪ F)
    (degree openedCount : Nat)
    (openings : HistoryBcsOpenings (S := S) head domain degree openedCount) where
  private mk ::
  math : HistoryBcsMath (C := C) deltaStar
  historyPcs : ledger.Good .historyPcs omega
  commitmentBinding : ledger.Good .commitmentBinding omega
  oracleTransport : ledger.Good .oracleTransport omega

/-- A proof-relevant conditional deployment record: it retains the exact
three common-coin good events beside (rather than pretending they imply) the
ideal FS theorem.  It is not a concrete deployed implementation. -/
structure DeployedHistoryBcsSoundness
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    (head : HistoryHead) (historyHasLink : 0 < head.foldRounds)
    (deltaStar : Real) (deltaStarPositive : 0 < deltaStar)
    (deltaStarLeOne : deltaStar ≤ 1)
    (domain : BoundReceiptIx n ↪ F) (degree openedCount : Nat)
    (openings : HistoryBcsOpenings (S := S) head domain degree openedCount)
    (Z : Set (Stmt (historyBcsReduction head historyHasLink deltaStar
      deltaStarPositive deltaStarLeOne domain degree openedCount openings))) where
  admission : HistoryBcsGameSecurity ledger omega head historyHasLink
    deltaStar domain degree openedCount openings
  idealFiatShamir : FsStraightlineKnowledgeSoundness
    (historyBcsReduction head historyHasLink deltaStar deltaStarPositive
      deltaStarLeOne domain degree openedCount openings) Z
    (HistoryBcsMath.fsError (F := F) head admission.math.errstar)

namespace HistoryBcsGameSecurity

variable {Omega : Type} [Fintype Omega]
variable {ledger : FailureLedger Omega} {omega : Omega}
variable {head : HistoryHead} {historyHasLink : 0 < head.foldRounds}
variable {deltaStar : Real} {deltaStarPositive : 0 < deltaStar}
variable {deltaStarLeOne : deltaStar ≤ 1}
variable {domain : BoundReceiptIx n ↪ F} {degree openedCount : Nat}
variable {openings : HistoryBcsOpenings (S := S) head domain degree openedCount}

/-- Outside the global game's union bad event, the three cryptographic good
events needed by this history lane are obtained from that same coin.  The MCA
facts remain explicit mathematical inputs; they are not manufactured from a
ledger tag. -/
def ofNotBad
    (notBad : ¬ledger.Bad omega)
    (math : HistoryBcsMath (C := C) deltaStar) :
    HistoryBcsGameSecurity ledger omega head historyHasLink deltaStar
      domain degree openedCount openings where
  math := math
  historyPcs := ledger.good_of_not_bad notBad .historyPcs
  commitmentBinding := ledger.good_of_not_bad notBad .commitmentBinding
  oracleTransport := ledger.good_of_not_bad notBad .oracleTransport

/-- Attach the ideal theorem to the admitted deployment coin without erasing
the proof-relevant PCS/CR/ROM good events. -/
noncomputable def deployedSoundness
    (security : HistoryBcsGameSecurity ledger omega head historyHasLink
      deltaStar domain degree openedCount openings)
    (Z : Set (Stmt (historyBcsReduction head historyHasLink deltaStar
      deltaStarPositive deltaStarLeOne domain degree openedCount openings))) :
    DeployedHistoryBcsSoundness ledger omega head historyHasLink deltaStar
      deltaStarPositive deltaStarLeOne domain degree openedCount openings Z where
  admission := security
  idealFiatShamir := security.math.fiatShamirSoundness Z

end HistoryBcsGameSecurity

/-! ## The history lane's exact sub-ledger on the common coin space -/

/-- A false deployment assumption for this lane is exactly PCS, commitment
binding/CR, or ROM transport failure on the shared game coin. -/
def HistoryBcsBad {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega) : Prop :=
  (ledger .historyPcs).event omega ∨
  (ledger .commitmentBinding).event omega ∨
  (ledger .oracleTransport).event omega

/-- Exact additive price of the history lane's three cryptographic seams. -/
def HistoryBcsPrice {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) : Real :=
  (ledger .historyPcs).price +
  (ledger .commitmentBinding).price +
  (ledger .oracleTransport).price

/-- The history lane's genuine three-event union bound.  No independence is
assumed because all predicates inhabit the same `Omega`. -/
theorem historyBcsBad_le_price {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) :
    uniformProb Omega (HistoryBcsBad ledger) ≤ HistoryBcsPrice ledger := by
  have houter := uniformProb_or_le (ledger .historyPcs).event (fun omega =>
    (ledger .commitmentBinding).event omega ∨
    (ledger .oracleTransport).event omega)
  have hinner := uniformProb_or_le (ledger .commitmentBinding).event
    (ledger .oracleTransport).event
  unfold HistoryBcsBad HistoryBcsPrice
  linarith [(ledger .historyPcs).bound,
    (ledger .commitmentBinding).bound, (ledger .oracleTransport).bound]

/-- The lane-specific bad event is covered by the exhaustive common ledger. -/
theorem historyBcsBad_implies_commonBad
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) {omega : Omega} :
    HistoryBcsBad ledger omega → ledger.Bad omega := by
  rintro (pcs | binding | rom)
  · exact Or.inr (Or.inr (Or.inl pcs))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl binding))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rom)))))

/-- info: 'Minidregg.Assurance.SemanticHistoryBcsGame.traceAggregate_eq_accumulator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms traceAggregate_eq_accumulator
/-- info: 'Minidregg.Assurance.SemanticHistoryBcsGame.traceSource_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms traceSource_aligned
/-- info: 'Minidregg.Assurance.SemanticHistoryBcsGame.HistoryBcsOpenings.bcsRounds_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HistoryBcsOpenings.bcsRounds_exact
/-- info: 'Minidregg.Assurance.SemanticHistoryBcsGame.historyBcsReduction_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms historyBcsReduction_source
/-- info: 'Minidregg.Loom.accRbrKnowledgeSoundBcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accRbrKnowledgeSoundBcs
/-- info: 'Minidregg.Loom.accFsSound_bcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accFsSound_bcs
/-- info: 'Minidregg.Assurance.SemanticHistoryBcsGame.historyBcsBad_le_price' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms historyBcsBad_le_price

end

end Minidregg.Assurance.SemanticHistoryBcsGame
