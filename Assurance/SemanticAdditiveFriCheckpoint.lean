/-
# Assurance.SemanticAdditiveFriCheckpoint -- semantic history enters additive FRI

This is the concrete join between the semantic-history accumulator, its
straightline linear-code PCS seam, and the additive-FRI receipt clause.

The key construction is not an assumed root equality. Semantic receipt
coordinates are injected into the level-zero additive cube and padded with
zero elsewhere. The semantic `BindingCommitment` is then DERIVED by reindexing
the clause's actual level-zero commitment. Consequently both layers use the
same field, the same hash root, the same opening relation, and the same bound
word. `initial_root_eq_semantic_head` proves the checkpoint equality from the
two landed commitment laws.

This remains an interface theorem, not a protocol mirror. Concrete Merkle CR,
cSHAKE/Fiat--Shamir ROM transport, proximity PCS realization, canonical
coordinate codecs, and the joint-game union bound remain explicit deployment
residuals. In particular, the additive-FRI UD error and semantic straightline
KS error are exposed as TWO component bounds; this file does not add them
without a common game/event space.
-/

import Compiler.AdditiveFriReceiptClause
import Assurance.SemanticHistoryStraightlinePcs

namespace Minidregg.Assurance.SemanticAdditiveFriCheckpoint

open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticHistoryStraightlinePcs
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SemanticTurnReceipt
open Minidregg.Compiler.AdditiveFriReceiptClause
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

universe uSemantics uFriOp uTranscript
  uClauseInput uClauseQuery uClauseReply uClauseOutcome uClauseEvidence

noncomputable section

/-! ## Canonical zero padding into the additive cube -/

/-- An injection with a partial inverse. `decode_sound` prevents a padded
coordinate outside the image from aliasing a semantic coordinate. -/
structure CoordinatePadding (ι κ : Type*) where
  encode : ι ↪ κ
  decode : κ → Option ι
  decode_encode : ∀ i, decode (encode i) = some i
  decode_sound : ∀ {k i}, decode k = some i → encode i = k

namespace CoordinatePadding

variable {ι κ F : Type*} [Field F]

/-- Extend a semantic word by zero on every additive-domain coordinate not
owned by the semantic codec. -/
def paddedWord (padding : CoordinatePadding ι κ) (word : ι → F) : κ → F :=
  fun k => match padding.decode k with
    | none => 0
    | some i => word i

@[simp] theorem paddedWord_encode (padding : CoordinatePadding ι κ)
    (word : ι → F) (i : ι) :
    padding.paddedWord word (padding.encode i) = word i := by
  simp [paddedWord, padding.decode_encode]

/-- Zero padding is linear, hence the pullback of any linear code remains a
linear code on semantic receipt coordinates. -/
def linearMap (padding : CoordinatePadding ι κ) :
    (ι → F) →ₗ[F] (κ → F) where
  toFun := padding.paddedWord
  map_add' := by
    intro left right
    funext k
    cases h : padding.decode k <;> simp [paddedWord, h]
  map_smul' := by
    intro scalar word
    funext k
    cases h : padding.decode k <;> simp [paddedWord, h]

@[simp] theorem linearMap_apply (padding : CoordinatePadding ι κ)
    (word : ι → F) : padding.linearMap word = padding.paddedWord word :=
  rfl

/-- Reindex a real binding commitment through the semantic coordinate
injection. This is the SAME root and verifier at the encoded positions, not a
second commitment plus a bridge assumption. -/
def paddedCommitment {Root Op : Type*}
    (padding : CoordinatePadding ι κ)
    (S : BindingCommitment Root F κ Op) : BindingCommitment Root F ι Op where
  commit word := S.commit (padding.paddedWord word)
  openAt word i := S.openAt (padding.paddedWord word) (padding.encode i)
  verifyOpen root i value opening :=
    S.verifyOpen root (padding.encode i) value opening
  verifyOpen_commit := by
    intro word i
    simpa only [paddedWord_encode] using
      S.verifyOpen_commit (padding.paddedWord word) (padding.encode i)
  binding := by
    intro root i left right leftOpening rightOpening hleft hright
    exact S.binding root (padding.encode i) left right leftOpening rightOpening
      hleft hright

@[simp] theorem paddedCommitment_commit {Root Op : Type*}
    (padding : CoordinatePadding ι κ)
    (S : BindingCommitment Root F κ Op) (word : ι → F) :
    (padding.paddedCommitment S).commit word =
      S.commit (padding.paddedWord word) :=
  rfl

@[simp] theorem paddedCommitment_verifyOpen {Root Op : Type*}
    (padding : CoordinatePadding ι κ)
    (S : BindingCommitment Root F κ Op)
    (root : Root) (i : ι) (value : F) (opening : Op) :
    (padding.paddedCommitment S).verifyOpen root i value opening ↔
      S.verifyOpen root (padding.encode i) value opening :=
  Iff.rfl

end CoordinatePadding

/-! ## The shared-code semantic checkpoint -/

variable {F : Type} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
variable {ell m n : Nat} {FriOp : Nat → Type uFriOp}
variable (friS : ∀ level, BindingCommitment Digest F
  (AdditiveFriLevels ell level) (FriOp level))

variable
    [DecidableEq F]
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext → BindingIx → F}

abbrev FriClause
    (m : Nat)
    (manifest : Manifest)
    (friS : ∀ level, BindingCommitment Digest F
      (AdditiveFriLevels ell level) (FriOp level)) :=
  Clause (F := F) (ell := ell) (m := m)
    (Root := fun _ => Digest) (Op := FriOp) manifest friS

/-! ## A non-vacuous additive-FRI manifest pin

The generic clause asks for controller equality. The former opaque V1 GF(2)
declaration did not have it (`431 != 500`), and the current base correctly
admits no dialect clause. This fresh declaration is a local manifest extension
whose controller is the actual outer manifest controller. -/

/-- First-order registry pins supplied by the concrete artifact. Keeping these
as data avoids silently identifying an arbitrary characteristic-two Lean field
with a particular native carrier profile. -/
structure CheckpointClausePins where
  clauseId : Digest
  relationId : Digest
  carrierProfileId : Digest
  statementCodecId : Digest
  proofCodecId : Digest
  proofSuiteId : Digest

/-- A fresh relation/proof-suite pin for this joined additive-FRI checkpoint.
It does not reuse any opaque base clause. Its controller is copied from the
actual base manifest, making controller equality constructive. -/
def checkpointClausePin (base : Manifest)
    (pins : CheckpointClausePins) : DialectClauseDecl where
  clauseId := pins.clauseId
  relationId := pins.relationId
  carrierProfileId := pins.carrierProfileId
  statementCodecId := pins.statementCodecId
  proofCodecId := pins.proofCodecId
  proofSuiteId := pins.proofSuiteId
  verifierControllerDigest := base.transcriptControllerDigest
  requiredBridgeIds := []

/-- An explicit extension independent of the base V1 clause registry. -/
def checkpointManifest (base : Manifest)
    (pins : CheckpointClausePins) : Manifest :=
  { base with dialectClauses := [checkpointClausePin base pins] }

theorem checkpointManifest_clauseIdsUnique (base : Manifest)
    (pins : CheckpointClausePins) :
    (checkpointManifest base pins).ClauseIdsUnique := by
  simp [checkpointManifest, Manifest.ClauseIdsUnique]

theorem checkpointClausePin_registered (base : Manifest)
    (pins : CheckpointClausePins) :
    (checkpointManifest base pins).lookupClause
        (checkpointClausePin base pins).clauseId =
      some (checkpointClausePin base pins) := by
  simp [checkpointManifest, checkpointClausePin, Manifest.lookupClause]

theorem checkpointClausePin_controllerExact (base : Manifest)
    (pins : CheckpointClausePins) :
    (checkpointClausePin base pins).verifierControllerDigest =
      (checkpointManifest base pins).transcriptControllerDigest := by
  rfl

/-- Positive constructor for the pinned clause. All administrative fields are
fixed here; callers supply only the actual additive tower, degree schedule,
committed transcript, and terminal coordinate. -/
def makeCheckpointClause
    (base : Manifest)
    (pins : CheckpointClausePins)
    (roundsWithinDomain : m ≤ ell)
    (tower : AdditiveFriTower F ell m)
    (degree : Nat → Nat)
    (degreeWithinDomain : ∀ level, level ≤ m →
      degree level ≤ 2 ^ (ell - level))
    (transcript : FriAdaptiveTranscript friS)
    (queryCount : Nat)
    (finalPoint : AdditiveFriLevels ell m) :
    Clause (F := F) (ell := ell) (m := m)
      (Root := fun _ => Digest) (Op := FriOp)
      (checkpointManifest base pins) friS where
  declaration := checkpointClausePin base pins
  manifestUnique := checkpointManifest_clauseIdsUnique base pins
  registered := checkpointClausePin_registered base pins
  controllerExact := checkpointClausePin_controllerExact base pins
  domainLog := ell
  domainLogExact := rfl
  rounds := m
  roundsExact := rfl
  roundsWithinDomain := roundsWithinDomain
  tower := tower
  basis := tower.beta
  basisExact := rfl
  offset := tower.offset
  offsetExact := rfl
  basisOrder := .reversedHighCoordinateFirst
  basisOrderExact := rfl
  domainSize := fun level => 2 ^ (ell - level)
  domainSizeExact := by simp
  degree := degree
  degreeWithinDomain := degreeWithinDomain
  rate := fun level => (degree level : Real) / (2 ^ (ell - level) : Nat)
  rateExact := by simp
  transcript := transcript
  rootSchedule := rootsBeforeChallenge_of_adaptive friS transcript
  queryCount := queryCount
  finalPoint := finalPoint
  finalValue := fun challenges =>
    transcript.wordAt challenges m le_rfl finalPoint
  finalValueExact := fun _ => rfl

/-- The semantic code is the exact pullback of the clause's level-zero RS
code through zero padding. Membership of the accumulated semantic word thus
implies membership of the actual additive-FRI input word definitionally. -/
def checkpointCode (clause : FriClause m manifest friS)
    (padding : CoordinatePadding (BoundReceiptIx n)
      (AdditiveFriLevels ell 0)) :
    Submodule F (BoundReceiptIx n → F) :=
  (reedSolomonCode (clause.tower.dom 0) (clause.degree 0)).comap
    padding.linearMap

/-- The semantic commitment is definitionally the actual additive-FRI
level-zero commitment reindexed through `padding`. -/
def semanticCommitment
    (padding : CoordinatePadding (BoundReceiptIx n)
      (AdditiveFriLevels ell 0)) :
    BindingCommitment Digest F (BoundReceiptIx n) (FriOp 0) :=
  padding.paddedCommitment (friS 0)

/-- A semantic history checkpoint whose accumulator root is literally a
level-zero additive-FRI root. The only cross-layer datum is the canonical
coordinate padding; the commitment and code are constructed from the clause. -/
structure Checkpoint (clause : FriClause m manifest friS) where
  padding : CoordinatePadding (BoundReceiptIx n) (AdditiveFriLevels ell 0)
  head : VerifiedHistoryHead
    (n := n) (F := F) (Op := FriOp 0)
    manifest registry clauseEvidence family headerCells
      (checkpointCode friS clause padding)
      (semanticCommitment friS padding)
  initialWordExact :
    clause.transcript.word 0 (fun i => i.elim0) =
      padding.paddedWord head.foldedWord

namespace Checkpoint

variable {friS : ∀ level, BindingCommitment Digest F
  (AdditiveFriLevels ell level) (FriOp level)}
variable {manifest : Manifest}
variable {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
  uClauseReply, uClauseOutcome}}
variable {clauseEvidence : ClauseEvidenceFamily manifest registry}
variable {clause : FriClause m manifest friS}

local notation "BoundCheckpoint" => Checkpoint
  (n := n) (F := F) (ell := ell) (m := m) (FriOp := FriOp)
  (manifest := manifest)
  (registry := registry) (clauseEvidence := clauseEvidence)
  (family := family) (headerCells := headerCells) friS clause

/-- The actual FRI input is a codeword because the semantic head already
proved membership in the exact pullback code. -/
theorem initial_word_mem_code (checkpoint : BoundCheckpoint) :
    checkpoint.padding.paddedWord checkpoint.head.foldedWord ∈
      reedSolomonCode (clause.tower.dom 0) (clause.degree 0) := by
  have hmem : checkpoint.head.foldedWord ∈
      checkpointCode friS clause checkpoint.padding :=
    checkpoint.head.satisfies.1
  change checkpoint.padding.linearMap checkpoint.head.foldedWord ∈
    reedSolomonCode (clause.tower.dom 0) (clause.degree 0) at hmem
  simpa using hmem

/-- **The load-bearing checkpoint theorem.** The additive-FRI initial root is
exactly the semantic accumulator root. It is DERIVED from `root_eq_commit`,
the padded initial-word equality, and the semantic head's `rootBound`. -/
theorem initial_root_eq_semantic_head (checkpoint : BoundCheckpoint) :
    clause.transcript.root 0 (fun i => i.elim0) =
      checkpoint.head.accumulator.rt := by
  calc
    clause.transcript.root 0 (fun i => i.elim0) =
        (friS 0).commit (clause.transcript.word 0 (fun i => i.elim0)) :=
      clause.transcript.root_eq_commit 0 (fun i => i.elim0)
    _ = (friS 0).commit
        (checkpoint.padding.paddedWord checkpoint.head.foldedWord) := by
      rw [checkpoint.initialWordExact]
    _ = (semanticCommitment friS checkpoint.padding).commit
        checkpoint.head.foldedWord := rfl
    _ = checkpoint.head.accumulator.rt := checkpoint.head.rootBound.symm

/-- The same equality at the runtime-shaped `rootAt` accessor: for EVERY full
challenge tuple, level zero is the semantic checkpoint and is fixed before the
first challenge. -/
theorem initial_root_before_challenges (checkpoint : BoundCheckpoint)
    (challenges : Fin m → F) :
    clause.transcript.rootAt challenges 0 (Nat.zero_le m) =
      checkpoint.head.accumulator.rt := by
  calc
    clause.transcript.rootAt challenges 0 (Nat.zero_le m) =
        clause.transcript.root 0 (fun i => i.elim0) := by
      unfold FriAdaptiveTranscript.rootAt
      congr 1
      funext i
      exact i.elim0
    _ = checkpoint.head.accumulator.rt :=
      checkpoint.initial_root_eq_semantic_head

/-- The clause's carried schedule theorem and the checkpoint theorem combine:
all challenge tuples see the same semantic level-zero root. -/
theorem initial_root_independent (checkpoint : BoundCheckpoint)
    (left right : Fin m → F) :
    clause.transcript.rootAt left 0 (Nat.zero_le m) =
      clause.transcript.rootAt right 0 (Nat.zero_le m) := by
  rw [checkpoint.initial_root_before_challenges left,
    checkpoint.initial_root_before_challenges right]

end Checkpoint

/-! ## Straightline extraction and accepted additive-FRI checkpoint -/

/-- Package the already-landed semantic straightline PCS around a checkpoint.
The semantic PCS uses the padded level-zero commitment itself; there is no
root bridge field to forge. -/
structure StraightlineCheckpointExtraction
    (clause : FriClause m manifest friS)
    (checkpoint : Checkpoint
      (n := n) (F := F) (ell := ell) (m := m) (FriOp := FriOp)
      (manifest := manifest)
      (registry := registry) (clauseEvidence := clauseEvidence)
      (family := family) (headerCells := headerCells) friS clause)
    (Coin : Type) [Fintype Coin] [DecidableEq Coin]
    (Transcript : Type uTranscript) where
  foldRoot : Digest → F → Digest → Digest
  semanticRounds : Nat
  schedule : FoldRootSchedule (checkpointCode friS clause checkpoint.padding)
    (semanticCommitment friS checkpoint.padding) foldRoot semanticRounds
  scheduleBinding : SemanticScheduleBinding
    (n := n) (F := F) (Op := FriOp 0)
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells)
    (C := checkpointCode friS clause checkpoint.padding)
    (S := semanticCommitment friS checkpoint.padding) (foldRoot := foldRoot)
    checkpoint.head semanticRounds schedule
  pcs : StraightlinePcsExtraction
    (n := n) (F := F) (Op := FriOp 0)
    (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells)
    (C := checkpointCode friS clause checkpoint.padding)
    (S := semanticCommitment friS checkpoint.padding) (foldRoot := foldRoot)
    checkpoint.head schedule scheduleBinding Coin Transcript

namespace StraightlineCheckpointExtraction

variable {friS : ∀ level, BindingCommitment Digest F
  (AdditiveFriLevels ell level) (FriOp level)}
variable {manifest : Manifest}
variable {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
  uClauseReply, uClauseOutcome}}
variable {clauseEvidence : ClauseEvidenceFamily manifest registry}
variable {clause : FriClause m manifest friS}
local notation "BoundCheckpoint" => Checkpoint
  (n := n) (F := F) (ell := ell) (m := m) (FriOp := FriOp)
  (manifest := manifest)
  (registry := registry) (clauseEvidence := clauseEvidence)
  (family := family) (headerCells := headerCells) friS clause
variable {checkpoint : BoundCheckpoint}
variable {Coin : Type} [Fintype Coin] [DecidableEq Coin]
variable {Transcript : Type uTranscript}

/-- A real receipt/checkpoint join: one additive-FRI accepted sample starts at
the semantic root, while one accepted KS-good PCS transcript extracts the
authoritative semantic word and its accumulated claim witness. -/
theorem accepted_sample_extracts_checkpoint
    (checkpoint : BoundCheckpoint)
    (joined : StraightlineCheckpointExtraction
      (n := n) (F := F) (ell := ell) (m := m) (FriOp := FriOp)
      (manifest := manifest)
      (registry := registry) (clauseEvidence := clauseEvidence)
      (family := family) (headerCells := headerCells)
      friS clause checkpoint Coin Transcript)
    {CommitmentBindingLaw CshakeRomLaw ArithmeticBufferCheck : Prop}
    (sample : AcceptedSample clause CommitmentBindingLaw CshakeRomLaw
      ArithmeticBufferCheck)
    (coin : Coin) (pcsAccepted : joined.pcs.accepts (joined.pcs.transcript coin))
    (ksGood : ¬joined.pcs.ksFailure coin) :
    joined.pcs.extract (joined.pcs.transcript coin) =
        checkpoint.head.foldedWord ∧
      AccClaim.Satisfies (checkpointCode friS clause checkpoint.padding)
        checkpoint.head.accumulator
        (joined.pcs.extract (joined.pcs.transcript coin)) ∧
      clause.transcript.rootAt sample.challenges 0 (Nat.zero_le m) =
        checkpoint.head.accumulator.rt ∧
      AdditiveFriAdaptiveCoherentAccepts clause.tower friS clause.degree
        clause.transcript clause.queryCount sample.challenges sample.querySeed := by
  have extractExact :
      joined.pcs.extract (joined.pcs.transcript coin) =
        checkpoint.head.foldedWord := by
    rw [joined.pcs.extractIsErasureRecovery]
    apply committed_word_recovered
      (semanticCommitment friS checkpoint.padding)
      joined.pcs.domain joined.pcs.degreeLeOpened
      (joined.pcs.openedDistinct (joined.pcs.transcript coin))
      checkpoint.head.rootBound
    · simpa only [← joined.pcs.codeExact] using checkpoint.head.satisfies.mem
    · exact joined.pcs.acceptedOpeningsVerify coin pcsAccepted ksGood
  constructor
  · exact extractExact
  constructor
  · rw [extractExact]
    exact checkpoint.head.satisfies
  constructor
  · exact checkpoint.initial_root_before_challenges sample.challenges
  · exact sample.accepted

/-- Keep the two probability spaces honest. The additive-FRI UD theorem and
semantic straightline KS theorem are both available, but no joint-event sum is
claimed before concrete ROM/PCS composition supplies a common game. -/
theorem component_error_bounds
    [Fintype F]
    (checkpoint : BoundCheckpoint)
    (joined : StraightlineCheckpointExtraction
      (n := n) (F := F) (ell := ell) (m := m) (FriOp := FriOp)
      (manifest := manifest)
      (registry := registry) (clauseEvidence := clauseEvidence)
      (family := family) (headerCells := headerCells)
      friS clause checkpoint Coin Transcript)
    {radius : Nat → Real} {tau : Real}
    (friSound : FarWordSoundnessCertificate clause radius tau) :
    (uniformProb
        ((Fin m → F) ×
          (Fin clause.queryCount → PowerTwoFriLevels ell 1))
        (fun sample => AdditiveFriAdaptiveCoherentAccepts clause.tower friS
          clause.degree clause.transcript clause.queryCount sample.1 sample.2) ≤
        (m : Real) * (2 ^ (ell - 1) : Nat) /
          (Fintype.card F : Real) + (1 - tau) ^ clause.queryCount) ∧
      uniformProb Coin joined.pcs.ksFailure ≤
        joined.pcs.ledger.totalEnvelope := by
  constructor
  · exact friSound.exact_ud_challenge_query_error
  · refine le_trans joined.pcs.ledger.knowledgeFailureBound ?_
    rw [joined.pcs.ledger.totalEnvelopeExact,
      joined.pcs.ledger.erasureErrorExact]
    linarith [joined.pcs.ledger.bindingRomFloor_nonneg]

end StraightlineCheckpointExtraction

#print axioms CoordinatePadding.paddedCommitment
#print axioms checkpointClausePin_registered
#print axioms Checkpoint.initial_root_eq_semantic_head
#print axioms Checkpoint.initial_word_mem_code
#print axioms StraightlineCheckpointExtraction.accepted_sample_extracts_checkpoint
#print axioms StraightlineCheckpointExtraction.component_error_bounds

end
end Minidregg.Assurance.SemanticAdditiveFriCheckpoint
