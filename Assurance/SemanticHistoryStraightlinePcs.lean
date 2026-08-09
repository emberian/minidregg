/-
# Assurance.SemanticHistoryStraightlinePcs -- the honest WARP-shaped seam

This module joins `SemanticHistoryAccumulator` to an external, straightline-
extractable linear-code PCS without claiming a complete WARP protocol.

The semantic side remains authoritative: a `VerifiedHistoryHead` contains the
proof-relevant admitted entries, their causal chain, the folded Loom claim,
and its exact satisfying word. The PCS side is a separate interface whose
types force the SAME carrier `F` and coordinate type `BoundReceiptIx n` and
whose fields state, rather than assume silently:

* the code is exactly an RS linear code and the semantic folded word is in it;
* round root `j` is a function only of challenges before `j`;
* every root commits the scheduled word and every fold root binds the literal
  linear combination;
* the actual schedule terminates at the semantic head's word and root;
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

import Assurance.SemanticHistoryAccumulator
import Loom.Erasure
import Loom.Rbr

namespace Minidregg.Assurance.SemanticHistoryStraightlinePcs

open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SemanticTurnReceipt
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe uEffect uDisclosure uError uOp uTranscript

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

end FoldRootSchedule

/-! ## Semantic-head binding -/

section Semantic

variable
    {n : Nat} [DecidableEq F]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Effect : Type uEffect} {Disclosure : Type uDisclosure}
    {Error : Type uError}
    {stateCommitment : StateCommitment (Fin n) F}
    {effectSemantics : EffectSemantics (Fin n) F Effect}
    {disclosurePolicy : DisclosurePolicy Disclosure}
    {manifest : Manifest} {errorId : Error → Digest}
    {headerCells : AdmissionContext → BindingIx → F}
    {C : Submodule F (BoundReceiptIx n → F)}
    {S : BindingCommitment Digest F (BoundReceiptIx n) Op}
    {foldRoot : Digest → F → Digest → Digest}

local notation "HistoryHead" => VerifiedHistoryHead
  (n := n) (F := F) (portal := portal) (authState := authState)
  (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
  (Error := Error) (Op := Op) (stateCommitment := stateCommitment)
  (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
  manifest errorId headerCells C S

/-- The exact list of semantic entry words retained by a verified head. -/
def historyWords (head : HistoryHead) : List (BoundReceiptIx n → F) :=
  head.entries.map fun entry => entry.word

/-- Bind one actual challenge schedule to a semantic head. The list equation
ties every scheduled codeword to a verified semantic entry; the terminal
equations tie the external schedule back to the head's authoritative folded
word and root. -/
structure SemanticScheduleBinding
    (head : HistoryHead) (rounds : Nat)
    (schedule : FoldRootSchedule C S foldRoot rounds) where
  challenges : Fin rounds → F
  roundsSuccDepth : rounds + 1 = head.depth
  entryWordsExact :
    schedule.initialWord :: List.ofFn schedule.linkWord = historyWords head
  finalWordExact : schedule.wordAt rounds challenges = head.foldedWord
  finalRootExact : schedule.rootAt rounds challenges = head.accumulator.rt

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
    (head : HistoryHead) {rounds : Nat}
    (schedule : FoldRootSchedule C S foldRoot rounds)
    (scheduleBinding : SemanticScheduleBinding head rounds schedule)
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

  ledger : KnowledgeErrorLedger Coin rounds ksFailure

namespace StraightlinePcsExtraction

variable {rounds : Nat}
variable {Coin : Type} [Fintype Coin] [DecidableEq Coin]
variable {Transcript : Type uTranscript}

/-- The deterministic extraction join. Outside the explicitly priced KS
failure event, one accepted transcript erasure-recovers exactly the semantic
head's committed folded word. -/
theorem extract_eq_semantic_head
    (head : HistoryHead)
    {schedule : FoldRootSchedule C S foldRoot rounds}
    {scheduleBinding : SemanticScheduleBinding
      (n := n) (F := F) (portal := portal) (authState := authState)
      (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
      (Error := Error) (Op := Op) (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
      (manifest := manifest) (errorId := errorId) (headerCells := headerCells)
      (C := C) (S := S) (foldRoot := foldRoot) head rounds schedule}
    (pcs : StraightlinePcsExtraction
      (n := n) (F := F) (portal := portal) (authState := authState)
      (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
      (Error := Error) (Op := Op) (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
      (manifest := manifest) (errorId := errorId) (headerCells := headerCells)
      (C := C) (S := S) (foldRoot := foldRoot)
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
of the semantic head's accumulated Loom claim. -/
theorem extract_satisfies_semantic_head
    (head : HistoryHead)
    {schedule : FoldRootSchedule C S foldRoot rounds}
    {scheduleBinding : SemanticScheduleBinding
      (n := n) (F := F) (portal := portal) (authState := authState)
      (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
      (Error := Error) (Op := Op) (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
      (manifest := manifest) (errorId := errorId) (headerCells := headerCells)
      (C := C) (S := S) (foldRoot := foldRoot) head rounds schedule}
    (pcs : StraightlinePcsExtraction
      (n := n) (F := F) (portal := portal) (authState := authState)
      (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
      (Error := Error) (Op := Op) (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
      (manifest := manifest) (errorId := errorId) (headerCells := headerCells)
      (C := C) (S := S) (foldRoot := foldRoot)
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
    {schedule : FoldRootSchedule C S foldRoot rounds}
    {scheduleBinding : SemanticScheduleBinding
      (n := n) (F := F) (portal := portal) (authState := authState)
      (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
      (Error := Error) (Op := Op) (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
      (manifest := manifest) (errorId := errorId) (headerCells := headerCells)
      (C := C) (S := S) (foldRoot := foldRoot) head rounds schedule}
    (pcs : StraightlinePcsExtraction
      (n := n) (F := F) (portal := portal) (authState := authState)
      (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
      (Error := Error) (Op := Op) (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
      (manifest := manifest) (errorId := errorId) (headerCells := headerCells)
      (C := C) (S := S) (foldRoot := foldRoot)
      head schedule scheduleBinding Coin Transcript) :
    uniformProb Coin pcs.ksFailure ≤ pcs.ledger.totalEnvelope := by
  refine le_trans pcs.ledger.knowledgeFailureBound ?_
  rw [pcs.ledger.totalEnvelopeExact, pcs.ledger.erasureErrorExact]
  linarith [pcs.ledger.bindingRomFloor_nonneg]

/-- Exact exposure of the WARP-shaped straightline KS ledger. This is an
interface equality, not a claim that this module constructed the RBR game. -/
theorem knowledge_error_shape
    (head : HistoryHead)
    {schedule : FoldRootSchedule C S foldRoot rounds}
    {scheduleBinding : SemanticScheduleBinding
      (n := n) (F := F) (portal := portal) (authState := authState)
      (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
      (Error := Error) (Op := Op) (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
      (manifest := manifest) (errorId := errorId) (headerCells := headerCells)
      (C := C) (S := S) (foldRoot := foldRoot) head rounds schedule}
    (pcs : StraightlinePcsExtraction
      (n := n) (F := F) (portal := portal) (authState := authState)
      (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
      (Error := Error) (Op := Op) (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
      (manifest := manifest) (errorId := errorId) (headerCells := headerCells)
      (C := C) (S := S) (foldRoot := foldRoot)
      head schedule scheduleBinding Coin Transcript) :
    pcs.ledger.knowledgeError =
      ((pcs.ledger.moveBudget : Real) + (rounds : Real)) *
        pcs.ledger.roundError :=
  pcs.ledger.knowledgeErrorExact

end StraightlinePcsExtraction

end Semantic

#print axioms FoldRootSchedule.foldRoot_commits_folded_word
#print axioms StraightlinePcsExtraction.extract_eq_semantic_head
#print axioms StraightlinePcsExtraction.extract_satisfies_semantic_head
#print axioms StraightlinePcsExtraction.knowledge_failure_le_totalEnvelope

end

end Minidregg.Assurance.SemanticHistoryStraightlinePcs
