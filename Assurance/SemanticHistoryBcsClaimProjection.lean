/-
# Assurance.SemanticHistoryBcsClaimProjection -- exact semantic claims at the BCS carrier

`accReductionBcs` is deliberately stated on `Fin m`.  Semantic receipt claims,
however, live on their typed finite coordinate carrier.  This module closes
that carrier seam by transporting words, linear codes, accumulated claims,
links, and whole aggregates through the canonical finite equivalence.

The transport is exact: roots and targets are unchanged, functionals are
precomposed with the inverse coordinate map, satisfaction is an iff, and
folding commutes on the nose.  Consequently this file does not add a security
game or discharge PCS/ROM/commitment premises; it supplies the missing typed
input to the already-built unshifted BCS reduction.
-/

import Assurance.SemanticHistoryWARPAdditiveJoin

namespace Minidregg.Assurance.SemanticHistoryBcsClaimProjection

open Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

variable {Root : Type} {F : Type} {iota : Type} [Field F]
variable [Fintype iota] [DecidableEq iota]
variable {r : Nat}

abbrev CoordinateCount (iota : Type*) [Fintype iota] := Fintype.card iota

/-! ## The coordinate linear equivalence -/

/-- Read a canonically reindexed word back on its semantic carrier. -/
def restoreWord (word : Fin (CoordinateCount iota) → F) : iota → F :=
  fun i => word (coordinateEquiv (ι := iota) i)

@[simp] theorem restoreWord_reindexWord (word : iota → F) :
    restoreWord (reindexWord word) = word := by
  funext i
  simp [restoreWord, reindexWord]

@[simp] theorem reindexWord_restoreWord
    (word : Fin (CoordinateCount iota) → F) :
    reindexWord (restoreWord word) = word := by
  funext k
  simp [restoreWord, reindexWord]

/-- Canonical coordinate permutation as a linear equivalence. -/
def coordinateLinearEquiv :
    (iota → F) ≃ₗ[F] (Fin (CoordinateCount iota) → F) where
  toFun := reindexWord
  invFun := restoreWord
  left_inv := restoreWord_reindexWord
  right_inv := reindexWord_restoreWord
  map_add' := by
    intro left right
    funext k
    rfl
  map_smul' := by
    intro scalar word
    funext k
    rfl

@[simp] theorem coordinateLinearEquiv_symm_reindexWord
    (word : iota → F) :
    coordinateLinearEquiv.symm (reindexWord word) = word := by
  change restoreWord (reindexWord word) = word
  exact restoreWord_reindexWord word

/-- The semantic code transported to the exact `Fin _` carrier expected by
`accReductionBcs`.  `comap` makes its meaning definitionally explicit: a
finite word is admitted exactly when restoring its coordinates lies in the
semantic code. -/
def reindexCode (C : Submodule F (iota → F)) :
    Submodule F (Fin (CoordinateCount iota) → F) :=
  C.comap coordinateLinearEquiv.symm.toLinearMap

@[simp] theorem reindexWord_mem_reindexCode
    (C : Submodule F (iota → F)) (word : iota → F) :
    reindexWord word ∈ reindexCode C ↔ word ∈ C := by
  change coordinateLinearEquiv.symm (reindexWord word) ∈ C ↔ word ∈ C
  rw [coordinateLinearEquiv_symm_reindexWord]

/-! ## Claims and satisfaction -/

/-- Transport a semantic functional to the BCS carrier. -/
def reindexFunctional (functional : (iota → F) →ₗ[F] F) :
    (Fin (CoordinateCount iota) → F) →ₗ[F] F :=
  functional.comp coordinateLinearEquiv.symm.toLinearMap

@[simp] theorem reindexFunctional_reindexWord
    (functional : (iota → F) →ₗ[F] F) (word : iota → F) :
    reindexFunctional functional (reindexWord word) = functional word := by
  change functional (coordinateLinearEquiv.symm (reindexWord word)) =
    functional word
  rw [coordinateLinearEquiv_symm_reindexWord]

/-- Exact accumulated-claim projection.  The root and targets are retained;
only the coordinate presentation of each functional changes. -/
def reindexClaim (claim : AccClaim Root F iota r) :
    AccClaim Root F (Fin (CoordinateCount iota)) r where
  rt := claim.rt
  channel := fun j => (reindexFunctional (claim.weights j), claim.targets j)

@[simp] theorem reindexClaim_rt (claim : AccClaim Root F iota r) :
    (reindexClaim claim).rt = claim.rt := rfl

@[simp] theorem reindexClaim_weights (claim : AccClaim Root F iota r)
    (j : Fin r) :
    (reindexClaim claim).weights j = reindexFunctional (claim.weights j) :=
  rfl

@[simp] theorem reindexClaim_targets (claim : AccClaim Root F iota r)
    (j : Fin r) :
    (reindexClaim claim).targets j = claim.targets j := rfl

/-- Claim satisfaction is invariant under the exact coordinate projection. -/
theorem reindexClaim_satisfies_iff
    (C : Submodule F (iota → F)) (claim : AccClaim Root F iota r)
    (word : iota → F) :
    AccClaim.Satisfies (reindexCode C) (reindexClaim claim)
        (reindexWord word) ↔
      AccClaim.Satisfies C claim word := by
  constructor
  · rintro ⟨hmem, hchannel⟩
    refine ⟨(reindexWord_mem_reindexCode C word).mp hmem, fun j => ?_⟩
    have exactChannel := hchannel j
    change (reindexClaim claim).weights j (reindexWord word) =
      (reindexClaim claim).targets j at exactChannel
    rw [reindexClaim_weights, reindexFunctional_reindexWord,
      reindexClaim_targets] at exactChannel
    exact exactChannel
  · rintro ⟨hmem, hchannel⟩
    refine ⟨(reindexWord_mem_reindexCode C word).mpr hmem, fun j => ?_⟩
    change (reindexClaim claim).weights j (reindexWord word) =
      (reindexClaim claim).targets j
    rw [reindexClaim_weights, reindexFunctional_reindexWord,
      reindexClaim_targets]
    exact hchannel j

/-! ## Folding and history transport -/

/-- Reindexing commutes exactly with one cross-word fold. -/
theorem reindexClaim_foldClaims
    (foldRoot : Root → F → Root → Root)
    (left right : AccClaim Root F iota r) (gamma : F) :
    reindexClaim (foldClaims foldRoot left right gamma) =
      foldClaims foldRoot (reindexClaim left) (reindexClaim right) gamma := by
  cases left
  cases right
  rfl

/-- A semantic link with its claim expressed at the BCS carrier. -/
def reindexLink (link : Link Root F iota r) :
    Link Root F (Fin (CoordinateCount iota)) r where
  pre := link.pre
  post := link.post
  claim := reindexClaim link.claim

/-- A whole semantic chain at the BCS carrier. -/
def reindexChain (chain : Chain Root F iota r) :
    Chain Root F (Fin (CoordinateCount iota)) r :=
  chain.map reindexLink

@[simp] theorem reindexChain_length (chain : Chain Root F iota r) :
    (reindexChain chain).length = chain.length := by
  simp [reindexChain]

/-- The round-index equivalence induced by `List.map`; no round is inserted,
deleted, or reordered by carrier projection. -/
def chainIndexEquiv (chain : Chain Root F iota r) :
    Fin (reindexChain chain).length ≃ Fin chain.length where
  toFun := Fin.cast (reindexChain_length chain)
  invFun := Fin.cast (reindexChain_length chain).symm
  left_inv := fun k => Fin.ext rfl
  right_inv := fun k => Fin.ext rfl

@[simp] theorem reindexChain_get (chain : Chain Root F iota r)
    (k : Fin (reindexChain chain).length) :
    (reindexChain chain).get k =
      reindexLink (chain.get (chainIndexEquiv chain k)) := by
  let sourceIndex : Fin chain.length :=
    ⟨k.val, by simpa [reindexChain] using k.isLt⟩
  have indexExact : chainIndexEquiv chain k = sourceIndex := Fin.ext rfl
  rw [indexExact]
  simp [reindexChain, sourceIndex]

/-- A semantic family of per-link witnesses on the projected round indices. -/
def reindexWitness (chain : Chain Root F iota r)
    (witness : Fin chain.length → iota → F) :
    Fin (reindexChain chain).length → Fin (CoordinateCount iota) → F :=
  fun k => reindexWord (witness (chainIndexEquiv chain k))

/-- `LinkAligned` lifted verbatim from its deployed `Fin m` API to an
arbitrary typed finite carrier.  This is only a carrier-generic presentation
of the existing source relation, not a second accumulator or acceptance
relation. -/
def TypedLinkAligned
    (C : Submodule F (iota → F)) (genesis : AccClaim Root F iota r)
    (chain : Chain Root F iota r) (k : Fin chain.length)
    (word : iota → F) : Prop :=
  word ∈ C ∧ ∀ j,
    genesis.weights j word = (chain.get k).claim.targets j

/-- `LinkAligned`, the source relation used by `accReductionBcs`, is invariant
under claim/carrier projection. -/
theorem reindexLinkAligned_iff
    (C : Submodule F (iota → F)) (genesis : AccClaim Root F iota r)
    (chain : Chain Root F iota r)
    (witness : Fin chain.length → iota → F)
    (k : Fin (reindexChain chain).length) :
    LinkAligned (reindexCode C) (reindexClaim genesis) (reindexChain chain) k
        (reindexWitness chain witness k) ↔
      TypedLinkAligned C genesis chain (chainIndexEquiv chain k)
        (witness (chainIndexEquiv chain k)) := by
  unfold LinkAligned TypedLinkAligned reindexWitness
  rw [reindexWord_mem_reindexCode]
  simp only [reindexClaim_weights, reindexFunctional_reindexWord,
    reindexChain_get, reindexLink, reindexClaim_targets]

/-- The complete source relation of the projected BCS reduction is exactly
the semantic genesis-and-links relation, including every per-round witness. -/
theorem reindexedSourceRelation_iff
    (C : Submodule F (iota → F)) (genesis : AccClaim Root F iota r)
    (chain : Chain Root F iota r) (genesisWord : iota → F)
    (witness : Fin chain.length → iota → F) :
    (AccClaim.Satisfies (reindexCode C) (reindexClaim genesis)
        (reindexWord genesisWord) ∧
      ∀ k : Fin (reindexChain chain).length,
        LinkAligned (reindexCode C) (reindexClaim genesis)
          (reindexChain chain) k (reindexWitness chain witness k)) ↔
    (AccClaim.Satisfies C genesis genesisWord ∧
      ∀ k : Fin chain.length,
        TypedLinkAligned C genesis chain k (witness k)) := by
  constructor
  · rintro ⟨hgenesis, hlinks⟩
    refine ⟨(reindexClaim_satisfies_iff C genesis genesisWord).mp hgenesis,
      fun k => ?_⟩
    let projected := (chainIndexEquiv chain).symm k
    have hprojected :=
      (reindexLinkAligned_iff C genesis chain witness projected).mp
        (hlinks projected)
    simpa [projected] using hprojected
  · rintro ⟨hgenesis, hlinks⟩
    refine ⟨(reindexClaim_satisfies_iff C genesis genesisWord).mpr hgenesis,
      fun k => ?_⟩
    exact (reindexLinkAligned_iff C genesis chain witness k).mpr
      (hlinks (chainIndexEquiv chain k))

/-- Aggregate projection is exact for every challenge schedule. -/
theorem reindexClaim_aggregate
    (foldRoot : Root → F → Root → Root) (schedule : Nat → F)
    (genesis : AccClaim Root F iota r) (chain : Chain Root F iota r) :
    reindexClaim (aggregate foldRoot schedule genesis chain) =
      aggregate foldRoot schedule (reindexClaim genesis) (reindexChain chain) := by
  induction chain generalizing schedule genesis with
  | nil => rfl
  | cons link tail ih =>
      simp only [aggregate_cons, reindexChain, List.map_cons]
      rw [ih, reindexClaim_foldClaims]
      rfl

/-- Word folding is the same linear combination after coordinate projection. -/
theorem reindexWord_foldWords
    (schedule : Nat → F) (genesis : iota → F) (words : List (iota → F)) :
    reindexWord (foldWords schedule genesis words) =
      foldWords schedule (reindexWord genesis) (words.map reindexWord) := by
  induction words generalizing schedule genesis with
  | nil => rfl
  | cons word tail ih =>
      simp only [foldWords_cons, List.map_cons]
      rw [ih]
      congr 1

/-- The target satisfaction relation reached after the unshifted fold is
identical to semantic aggregate satisfaction. -/
theorem reindexedTargetRelation_iff
    (C : Submodule F (iota → F))
    (foldRoot : Root → F → Root → Root) (schedule : Nat → F)
    (genesis : AccClaim Root F iota r) (chain : Chain Root F iota r)
    (foldedWord : iota → F) :
    AccClaim.Satisfies (reindexCode C)
        (aggregate foldRoot schedule (reindexClaim genesis) (reindexChain chain))
        (reindexWord foldedWord) ↔
      AccClaim.Satisfies C (aggregate foldRoot schedule genesis chain)
        foldedWord := by
  rw [← reindexClaim_aggregate]
  exact reindexClaim_satisfies_iff C
    (aggregate foldRoot schedule genesis chain) foldedWord

/-! ## Direct projection of the authoritative semantic-family head -/

universe uSemantics uOp uClauseInput uClauseQuery uClauseReply
  uClauseOutcome uClauseEvidence

section SemanticHead

variable [DecidableEq F]
variable {n : Nat} {Op : Type uOp}
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext → BindingIx → F}
    {C : Submodule F (BoundReceiptIx n → F)}
    {S : BindingCommitment Digest F (BoundReceiptIx n) Op}

local notation "HistoryHead" => VerifiedHistoryHead
  (n := n) (F := F) (Op := Op) manifest registry clauseEvidence family
  headerCells C S

/-- The exact accumulated claim of a request-neutral semantic history, merely
re-presented on the canonical finite BCS carrier. -/
def reindexHistoryHeadClaim (head : HistoryHead) :
    AccClaim Digest F (Fin (CoordinateCount (BoundReceiptIx n)))
      (Fintype.card (BoundReceiptIx n)) :=
  reindexClaim head.accumulator

/-- The exact satisfying word of the same history at the BCS carrier. -/
def reindexHistoryHeadWord (head : HistoryHead) :
    Fin (CoordinateCount (BoundReceiptIx n)) → F :=
  reindexWord head.foldedWord

/-- Direct authoritative-input theorem: every admitted heterogeneous history
head supplies the projected BCS claim and its exact satisfying word.  This is
carrier transport only; it introduces no PCS, ROM, or binding premise. -/
theorem reindexHistoryHead_satisfies (head : HistoryHead) :
    AccClaim.Satisfies (reindexCode C) (reindexHistoryHeadClaim head)
      (reindexHistoryHeadWord head) :=
  (reindexClaim_satisfies_iff C head.accumulator head.foldedWord).mpr
    head.satisfies

/-- Carrier projection retains the authoritative accumulator root literally. -/
@[simp] theorem reindexHistoryHeadClaim_rt (head : HistoryHead) :
    (reindexHistoryHeadClaim head).rt = head.accumulator.rt :=
  rfl

end SemanticHead

/-! ## The actual unshifted BCS reduction at the semantic carrier -/

section BcsReduction

variable [Fintype F] [DecidableEq F]
variable {Root' Op : Type} {t : Nat}

/-- `accReductionBcs` instantiated on the canonical projection of one typed
semantic code and history.  This is the already-proved reduction, not a new
game; the definition only supplies its formerly-missing `Fin _` inputs. -/
@[reducible] noncomputable def semanticBcsReduction
    (C : Submodule F (iota → F))
    (foldRoot : Root → F → Root → Root) (chain : Chain Root F iota r)
    (coordinateCountPositive : 0 < CoordinateCount iota)
    (chainNonempty : 0 < chain.length)
    (deltaStar : Real) (deltaStarPositive : 0 < deltaStar)
    (deltaStarLeOne : deltaStar ≤ 1)
    (commitment : BindingCommitment Root' F (Fin (CoordinateCount iota)) Op)
    (domain : Fin (CoordinateCount iota) ↪ F) (degree : Nat)
    (queries : Fin t → Fin (CoordinateCount iota)) : Reduction :=
  accReductionBcs (reindexCode C) foldRoot (reindexChain chain)
    coordinateCountPositive (by simpa using chainNonempty)
    deltaStar deltaStarPositive deltaStarLeOne commitment domain degree queries

/-- The source relation of the actual unshifted BCS reduction is exactly the
semantic source relation after projecting its explicit claim, implicit word,
and proof-relevant per-link witnesses. -/
theorem semanticBcsReduction_source_iff
    (C : Submodule F (iota → F))
    (foldRoot : Root → F → Root → Root) (chain : Chain Root F iota r)
    (coordinateCountPositive : 0 < CoordinateCount iota)
    (chainNonempty : 0 < chain.length)
    (deltaStar : Real) (deltaStarPositive : 0 < deltaStar)
    (deltaStarLeOne : deltaStar ≤ 1)
    (commitment : BindingCommitment Root' F (Fin (CoordinateCount iota)) Op)
    (domain : Fin (CoordinateCount iota) ↪ F) (degree : Nat)
    (queries : Fin t → Fin (CoordinateCount iota))
    (genesis : AccClaim Root F iota r) (genesisWord : iota → F)
    (witness : Fin chain.length → iota → F) :
    (semanticBcsReduction C foldRoot chain coordinateCountPositive chainNonempty
        deltaStar deltaStarPositive deltaStarLeOne commitment domain degree queries).R
      () (reindexClaim genesis) (reindexWord genesisWord)
        (reindexWitness chain witness) ↔
      (AccClaim.Satisfies C genesis genesisWord ∧
        ∀ k : Fin chain.length,
          TypedLinkAligned C genesis chain k (witness k)) := by
  exact reindexedSourceRelation_iff C genesis chain genesisWord witness

/-- Likewise, the target relation reached by the actual BCS reduction reads
the projected folded claim/word exactly as semantic aggregate satisfaction.
The witness argument is retained because WARP uses one witness type on both
sides, although `accReductionBcs.R'` correctly does not inspect it. -/
theorem semanticBcsReduction_target_iff
    (C : Submodule F (iota → F))
    (foldRoot : Root → F → Root → Root) (chain : Chain Root F iota r)
    (coordinateCountPositive : 0 < CoordinateCount iota)
    (chainNonempty : 0 < chain.length)
    (deltaStar : Real) (deltaStarPositive : 0 < deltaStar)
    (deltaStarLeOne : deltaStar ≤ 1)
    (commitment : BindingCommitment Root' F (Fin (CoordinateCount iota)) Op)
    (domain : Fin (CoordinateCount iota) ↪ F) (degree : Nat)
    (queries : Fin t → Fin (CoordinateCount iota))
    (schedule : Nat → F) (genesis : AccClaim Root F iota r)
    (foldedWord : iota → F) (witness : Fin chain.length → iota → F) :
    (semanticBcsReduction C foldRoot chain coordinateCountPositive chainNonempty
        deltaStar deltaStarPositive deltaStarLeOne commitment domain degree queries).R'
      () (aggregate foldRoot schedule (reindexClaim genesis) (reindexChain chain))
        (reindexWord foldedWord) (reindexWitness chain witness) ↔
      AccClaim.Satisfies C (aggregate foldRoot schedule genesis chain)
        foldedWord := by
  exact reindexedTargetRelation_iff C foldRoot schedule genesis chain foldedWord

end BcsReduction

#print axioms reindexClaim_satisfies_iff
#print axioms reindexClaim_foldClaims
#print axioms reindexClaim_aggregate
#print axioms reindexWord_foldWords
#print axioms reindexedSourceRelation_iff
#print axioms reindexedTargetRelation_iff
#print axioms reindexHistoryHead_satisfies
#print axioms semanticBcsReduction_source_iff
#print axioms semanticBcsReduction_target_iff

end

end Minidregg.Assurance.SemanticHistoryBcsClaimProjection
