/-
# Assurance.SemanticHistoryStraightlinePcs -- the honest WARP-shaped seam

This module joins `SemanticHistoryFamily` to an external, straightline-
extractable linear-code PCS without claiming a complete WARP protocol.

The semantic side remains authoritative: a `VerifiedHistoryHead` contains the
proof-relevant admitted entries, their causal chain, the folded Selvage claim,
and its exact satisfying word. The PCS side is a separate interface whose
types force the SAME carrier `F` and coordinate type `BoundReceiptIx n` and
whose fields state, rather than assume silently:

* the code is exactly an RS linear code and the semantic folded word is in it;
* round root `j` is a function only of challenges before `j`;
* every root commits the scheduled word and every fold root binds the literal
  linear combination;
* schedule genesis/link words are exact projections of the retained semantic
  trace, whose challenges determine the actual execution;
* terminal word/root equalities are derived from that trace and the schedule
  laws rather than supplied by a caller;
* verified distinct openings with `degree <= openedCount` feed the landed
  erasure-correction theorem; and
* the straightline KS price has WARP's `(moves + rounds) * roundError` shape,
  while the commitment/ROM floor remains a separate external ledger entry.

What is proved here is deliberately smaller than full WARP: deterministic
root-attributed recovery of the semantic head and its accumulator witness,
plus an upper envelope for the externally supplied KS failure event. This
does not instantiate a `Reduction`, `KStateFn`, Fiat--Shamir ROM, Merkle CR,
or the constrained-mask lagged-root schedule.
-/

import Assurance.SemanticHistoryFamily
import Selvage.Erasure
import Selvage.Rbr

namespace Minidregg.Assurance.SemanticHistoryStraightlinePcs

open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Selvage
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe uSemantics uOp uTranscript
  uClauseInput uClauseQuery uClauseReply uClauseOutcome uClauseEvidence

noncomputable section

/-! ## Prefix-typed fold roots -/

variable {F : Type} [Field F]
variable {ι : Type*} {Op : Type uOp}

/-- A declarative fold/root strategy. At level `j`, both `wordAt` and `rootAt`
receive only a `Fin j` challenge prefix, so the current and future challenges
cannot influence the root by construction. `foldRootExact` is the explicit
recommitment/binding equation; it is data supplied by the PCS realization. -/
structure FoldRootSchedule
    (C : Submodule F (ι → F))
    (S : BindingCommitment Digest F ι Op)
    (foldRoot : Digest → F → Digest → Digest)
    (rounds : Nat) where
  initialWord : ι → F
  linkWord : Fin rounds → ι → F
  wordAt : ∀ j : Nat, (Fin j → F) → ι → F
  rootAt : ∀ j : Nat, (Fin j → F) → Digest

  initialWordExact : wordAt 0 (fun i => i.elim0) = initialWord
  rootCommits : ∀ j challengesPrefix,
    rootAt j challengesPrefix = S.commit (wordAt j challengesPrefix)
  initialCodeword : initialWord ∈ C
  linkCodeword : ∀ j, linkWord j ∈ C

  wordStep : ∀ (j : Fin rounds)
      (challengesPrefix : Fin j → F) (gamma : F),
    wordAt (j + 1) (Fin.snoc challengesPrefix gamma) =
      wordAt j challengesPrefix + gamma • linkWord j
  foldRootExact : ∀ (j : Fin rounds)
      (challengesPrefix : Fin j → F) (gamma : F),
    rootAt (j + 1) (Fin.snoc challengesPrefix gamma) =
      foldRoot (rootAt j challengesPrefix) gamma (S.commit (linkWord j))

namespace FoldRootSchedule

variable {C : Submodule F (ι → F)}
variable {S : BindingCommitment Digest F ι Op}
variable {foldRoot : Digest → F → Digest → Digest} {rounds : Nat}

/-- Named roots-before-current-challenge theorem. Equality of the preceding
prefix is all that can affect a level root. -/
theorem root_prefix_bound
    (schedule : FoldRootSchedule C S foldRoot rounds)
    {j : Nat} {left right : Fin j → F} (samePrefix : left = right) :
    schedule.rootAt j left = schedule.rootAt j right := by
  rw [samePrefix]

/-- The fold root is not merely syntactically scheduled: commitment binding
and the word recurrence identify it with the commitment of the literal folded
word. -/
theorem foldRoot_commits_folded_word
    (schedule : FoldRootSchedule C S foldRoot rounds)
    (j : Fin rounds) (challengesPrefix : Fin j → F) (gamma : F) :
    foldRoot (schedule.rootAt j challengesPrefix) gamma
        (S.commit (schedule.linkWord j)) =
      S.commit
        (schedule.wordAt j challengesPrefix + gamma • schedule.linkWord j) := by
  rw [← schedule.foldRootExact j challengesPrefix gamma,
    schedule.rootCommits, schedule.wordStep]

/-- Restrict a schedule to an initial segment.  Prefix words and roots are
literally the same functions, and no challenge at or after `kept` is made
available. -/
def truncate
    (schedule : FoldRootSchedule C S foldRoot rounds)
    (kept : Nat) (keptLe : kept ≤ rounds) :
    FoldRootSchedule C S foldRoot kept where
  initialWord := schedule.initialWord
  linkWord := fun j => schedule.linkWord
    ⟨j, lt_of_lt_of_le j.isLt keptLe⟩
  wordAt := schedule.wordAt
  rootAt := schedule.rootAt
  initialWordExact := schedule.initialWordExact
  rootCommits := schedule.rootCommits
  initialCodeword := schedule.initialCodeword
  linkCodeword := fun j => schedule.linkCodeword
    ⟨j, lt_of_lt_of_le j.isLt keptLe⟩
  wordStep := fun j => schedule.wordStep
    ⟨j, lt_of_lt_of_le j.isLt keptLe⟩
  foldRootExact := fun j => schedule.foldRootExact
    ⟨j, lt_of_lt_of_le j.isLt keptLe⟩

end FoldRootSchedule

/-! ## Semantic-head binding -/

section Semantic

variable
    {n : Nat} [DecidableEq F]
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext → BindingIx → F}
    {C : Submodule F (BoundReceiptIx n → F)}
    {S : BindingCommitment Digest F (BoundReceiptIx n) Op}
    {foldRoot : Digest → F → Digest → Digest}

local notation "HistoryHead" => VerifiedHistoryHead
  (n := n) (F := F) (Op := Op) manifest registry clauseEvidence family
  headerCells C S

/-- The exact list of semantic entry words retained by a verified head. -/
def historyWords (head : HistoryHead) : List (BoundReceiptIx n → F) :=
  head.entries.map fun entry => entry.word

/-- The genesis word derived from the authoritative proof-relevant fold
trace. -/
def historyInitialWord (head : HistoryHead) : BoundReceiptIx n → F :=
  head.initialWord

/-- The exact controller challenges retained by the authoritative fold
trace.  These are not supplied by a proof consumer. -/
def historyChallenges (head : HistoryHead) : Fin head.foldRounds → F :=
  head.foldChallenges

/-- The exact pre-challenge link words retained by the authoritative fold
trace.  Every word is derived from a `VerifiedEntry`, including its semantic
family and ordered clause evidence. -/
def historyLinkWord (head : HistoryHead) :
    Fin head.foldRounds → BoundReceiptIx n → F :=
  head.foldLinkWord

/-- A PCS fold schedule may choose its prefix-typed realization, but its
genesis and per-round link words are exact projections of the authoritative
history trace.  Challenges and terminal equations are deliberately absent:
they are derived below from the trace and schedule laws. -/
structure SemanticScheduleBinding
    (head : HistoryHead)
    (schedule : FoldRootSchedule C S head.foldRoot head.foldRounds) where
  initialWordExact : schedule.initialWord = historyInitialWord head
  linkWordExact : ∀ j, schedule.linkWord j = historyLinkWord head j

/-- Following the trace-retained challenges through any exactly bound
prefix-typed schedule reaches the trace-indexed folded word. -/
theorem FoldRootSchedule.wordAt_historyTrace
    {rounds : Nat} {entries : List (VerifiedEntry
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C))}
    {accumulator : AccClaim Digest F (BoundReceiptIx n)
      (Fintype.card (BoundReceiptIx n))}
    {foldedWord : BoundReceiptIx n → F}
    {initialWord : BoundReceiptIx n → F}
    {challenges : Fin rounds → F}
    {linkWord : Fin rounds → BoundReceiptIx n → F}
    {foldRoot : Digest → F → Digest → Digest}
    (trace : HistoryFoldTrace manifest registry clauseEvidence family
      headerCells C S foldRoot rounds entries accumulator foldedWord
        initialWord challenges linkWord)
    (schedule : FoldRootSchedule C S foldRoot rounds)
    (initialWordExact : schedule.initialWord = initialWord)
    (linkWordExact : ∀ j, schedule.linkWord j = linkWord j) :
    schedule.wordAt rounds challenges = foldedWord := by
  induction trace with
  | start entry =>
      calc
        schedule.wordAt 0 (fun index => index.elim0) =
            schedule.initialWord := schedule.initialWordExact
        _ = entry.word := initialWordExact
  | @append priorRounds priorEntries priorAccumulator priorWord
      priorInitial priorChallenges priorLink prior entry gamma rootExact ih =>
      let priorSchedule := schedule.truncate priorRounds (by omega)
      have priorInitialExact : priorSchedule.initialWord = priorInitial := by
        simpa [priorSchedule, FoldRootSchedule.truncate] using initialWordExact
      have priorLinkExact : ∀ j, priorSchedule.linkWord j =
          priorLink j := by
        intro j
        simpa [priorSchedule, FoldRootSchedule.truncate,
          Fin.snoc_castSucc] using
          linkWordExact j.castSucc
      have priorFinal := ih priorSchedule priorInitialExact priorLinkExact
      have priorFinal' :
          schedule.wordAt priorRounds priorChallenges = priorWord := by
        simpa [priorSchedule, FoldRootSchedule.truncate] using priorFinal
      calc
        schedule.wordAt (priorRounds + 1)
            (Fin.snoc priorChallenges gamma) =
            schedule.wordAt priorRounds
                priorChallenges +
              gamma • schedule.linkWord (Fin.last priorRounds) :=
          schedule.wordStep (Fin.last priorRounds)
            priorChallenges gamma
        _ = priorWord + gamma • entry.word := by
          rw [priorFinal']
          rw [linkWordExact (Fin.last priorRounds)]
          simp only [Fin.snoc_last]

namespace SemanticScheduleBinding

/-- The terminal word equation is a theorem, not caller-supplied schedule
data. -/
theorem finalWordExact
    (head : HistoryHead)
    {schedule : FoldRootSchedule C S head.foldRoot head.foldRounds}
    (binding : SemanticScheduleBinding head schedule) :
    schedule.wordAt head.foldRounds (historyChallenges head) =
      head.foldedWord :=
  schedule.wordAt_historyTrace head.foldTrace
    binding.initialWordExact binding.linkWordExact

/-- The terminal root equation follows from commitment exactness, the derived
terminal word theorem, and the authoritative head's root binding. -/
theorem finalRootExact
    (head : HistoryHead)
    {schedule : FoldRootSchedule C S head.foldRoot head.foldRounds}
    (binding : SemanticScheduleBinding head schedule) :
    schedule.rootAt head.foldRounds (historyChallenges head) =
      head.accumulator.rt := by
  rw [schedule.rootCommits, binding.finalWordExact head, head.rootBound]

end SemanticScheduleBinding

/-! ## External one-transcript PCS extractor and exact erasure bridge -/

/-- WARP-shaped error ledger. Erasure recovery is deterministic and therefore
priced at zero in this exact-codeword regime. `bindingRomFloor` is retained as
an external deployment price; no cryptographic event is modeled or proved
here. -/
structure KnowledgeErrorLedger
    (Coin : Type) [Fintype Coin] [DecidableEq Coin]
    (rounds : Nat) (ksFailure : Coin → Prop) where
  moveBudget : Nat
  roundError : Real
  knowledgeError : Real
  knowledgeErrorExact : knowledgeError =
    ((moveBudget : Real) + (rounds : Real)) * roundError
  knowledgeFailureBound : uniformProb Coin ksFailure ≤ knowledgeError

  erasureError : Real
  erasureErrorExact : erasureError = 0
  bindingRomFloor : Real
  bindingRomFloor_nonneg : 0 ≤ bindingRomFloor
  totalEnvelope : Real
  totalEnvelopeExact :
    totalEnvelope = bindingRomFloor + erasureError + knowledgeError

/-- An external PCS extraction view of one semantic head. `extract` is a pure
function of ONE transcript, hence straightline at this interface: no prover
callback or rewind operation exists. The only accepted values are verified by
the existing binding commitment, and `extractIsErasureRecovery` fixes the
extractor to the landed linear-code erasure algorithm. -/
structure StraightlinePcsExtraction
    (head : HistoryHead)
    (schedule : FoldRootSchedule C S head.foldRoot head.foldRounds)
    (scheduleBinding : SemanticScheduleBinding head schedule)
    (Coin : Type) [Fintype Coin] [DecidableEq Coin]
    (Transcript : Type uTranscript) where
  transcript : Coin → Transcript
  accepts : Transcript → Prop
  ksFailure : Coin → Prop

  degree : Nat
  openedCount : Nat
  domain : BoundReceiptIx n ↪ F
  codeExact : C = reedSolomonCode domain degree
  degreeLeOpened : degree ≤ openedCount

  opened : Transcript → Fin openedCount → BoundReceiptIx n
  values : Transcript → Fin openedCount → F
  openingProofs : Transcript → Fin openedCount → Op
  openedDistinct : ∀ tr, Function.Injective (domain ∘ opened tr)

  extract : Transcript → BoundReceiptIx n → F
  extractIsErasureRecovery : ∀ tr,
    extract tr = recoverFromColumns domain degree (opened tr) (values tr)
  acceptedOpeningsVerify : ∀ coin,
    accepts (transcript coin) → ¬ksFailure coin → ∀ j,
      S.verifyOpen head.accumulator.rt
        (opened (transcript coin) j) (values (transcript coin) j)
        (openingProofs (transcript coin) j)

  ledger : KnowledgeErrorLedger Coin head.foldRounds ksFailure

namespace StraightlinePcsExtraction

variable {Coin : Type} [Fintype Coin] [DecidableEq Coin]
variable {Transcript : Type uTranscript}

/-- The deterministic extraction join. Outside the explicitly priced KS
failure event, one accepted transcript erasure-recovers exactly the semantic
head's committed folded word. -/
theorem extract_eq_semantic_head
    (head : HistoryHead)
    {schedule : FoldRootSchedule C S head.foldRoot head.foldRounds}
    {scheduleBinding : SemanticScheduleBinding
      (n := n) (F := F) (Op := Op)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells)
      (C := C) (S := S) head schedule}
    (pcs : StraightlinePcsExtraction
      (n := n) (F := F) (Op := Op)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells)
      (C := C) (S := S)
      head schedule scheduleBinding Coin Transcript)
    (coin : Coin) (accepted : pcs.accepts (pcs.transcript coin))
    (ksGood : ¬pcs.ksFailure coin) :
    pcs.extract (pcs.transcript coin) = head.foldedWord := by
  rw [pcs.extractIsErasureRecovery]
  apply committed_word_recovered S pcs.domain pcs.degreeLeOpened
    (pcs.openedDistinct (pcs.transcript coin)) head.rootBound
  · simpa only [← pcs.codeExact] using head.satisfies.mem
  · exact pcs.acceptedOpeningsVerify coin accepted ksGood

/-- The extracted object is not only root-attributed: it is a genuine witness
of the semantic head's accumulated Selvage claim. -/
theorem extract_satisfies_semantic_head
    (head : HistoryHead)
    {schedule : FoldRootSchedule C S head.foldRoot head.foldRounds}
    {scheduleBinding : SemanticScheduleBinding
      (n := n) (F := F) (Op := Op)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells)
      (C := C) (S := S) head schedule}
    (pcs : StraightlinePcsExtraction
      (n := n) (F := F) (Op := Op)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells)
      (C := C) (S := S)
      head schedule scheduleBinding Coin Transcript)
    (coin : Coin) (accepted : pcs.accepts (pcs.transcript coin))
    (ksGood : ¬pcs.ksFailure coin) :
    AccClaim.Satisfies C head.accumulator (pcs.extract (pcs.transcript coin)) := by
  rw [extract_eq_semantic_head head pcs coin accepted ksGood]
  exact head.satisfies

/-- The ledger theorem intentionally prices only the modeled KS failure event.
The binding/ROM floor is an additive external envelope, not a proved event
reduction; deterministic erasure contributes exactly zero. -/
theorem knowledge_failure_le_totalEnvelope
    (head : HistoryHead)
    {schedule : FoldRootSchedule C S head.foldRoot head.foldRounds}
    {scheduleBinding : SemanticScheduleBinding
      (n := n) (F := F) (Op := Op)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells)
      (C := C) (S := S) head schedule}
    (pcs : StraightlinePcsExtraction
      (n := n) (F := F) (Op := Op)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells)
      (C := C) (S := S)
      head schedule scheduleBinding Coin Transcript) :
    uniformProb Coin pcs.ksFailure ≤ pcs.ledger.totalEnvelope := by
  refine le_trans pcs.ledger.knowledgeFailureBound ?_
  rw [pcs.ledger.totalEnvelopeExact, pcs.ledger.erasureErrorExact]
  linarith [pcs.ledger.bindingRomFloor_nonneg]

/-- Exact exposure of the WARP-shaped straightline KS ledger. This is an
interface equality, not a claim that this module constructed the RBR game. -/
theorem knowledge_error_shape
    (head : HistoryHead)
    {schedule : FoldRootSchedule C S head.foldRoot head.foldRounds}
    {scheduleBinding : SemanticScheduleBinding
      (n := n) (F := F) (Op := Op)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells)
      (C := C) (S := S) head schedule}
    (pcs : StraightlinePcsExtraction
      (n := n) (F := F) (Op := Op)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells)
      (C := C) (S := S)
      head schedule scheduleBinding Coin Transcript) :
    pcs.ledger.knowledgeError =
      ((pcs.ledger.moveBudget : Real) + (head.foldRounds : Real)) *
        pcs.ledger.roundError :=
  pcs.ledger.knowledgeErrorExact

end StraightlinePcsExtraction

end Semantic

/-- info: 'Minidregg.Assurance.SemanticHistoryStraightlinePcs.FoldRootSchedule.foldRoot_commits_folded_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FoldRootSchedule.foldRoot_commits_folded_word
/-- info: 'Minidregg.Assurance.SemanticHistoryStraightlinePcs.FoldRootSchedule.wordAt_historyTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FoldRootSchedule.wordAt_historyTrace
/-- info: 'Minidregg.Assurance.SemanticHistoryStraightlinePcs.SemanticScheduleBinding.finalRootExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SemanticScheduleBinding.finalRootExact
/-- info: 'Minidregg.Assurance.SemanticHistoryStraightlinePcs.StraightlinePcsExtraction.extract_eq_semantic_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms StraightlinePcsExtraction.extract_eq_semantic_head
/-- info: 'Minidregg.Assurance.SemanticHistoryStraightlinePcs.StraightlinePcsExtraction.extract_satisfies_semantic_head' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms StraightlinePcsExtraction.extract_satisfies_semantic_head
/-- info: 'Minidregg.Assurance.SemanticHistoryStraightlinePcs.StraightlinePcsExtraction.knowledge_failure_le_totalEnvelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms StraightlinePcsExtraction.knowledge_failure_le_totalEnvelope

end

end Minidregg.Assurance.SemanticHistoryStraightlinePcs
