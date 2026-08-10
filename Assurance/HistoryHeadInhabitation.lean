/-
# Assurance.HistoryHeadInhabitation -- the retained-history layer is not vacuous

Every theorem about retained history in this tree is quantified over
`head : VerifiedHistoryHead`.  Until this module, **nothing in the tree ever
constructed one.**  `start` and `append` are the only ways to build a head and
neither was applied outside its own defining module; every other occurrence is
a bound hypothesis.  A development with that shape is indistinguishable from a
vacuous one: if the type were empty, `SemanticHistoryBcsGame`,
`SemanticHistoryTower256DeployedBcs`, `HyperdocumentHistoryAdmission`,
`SemanticHistoryPcsEventRealization`, and `RawHistoryBcsOpenings` would all be
trivially true and say nothing.

This module exhibits a head, at closed parameters, with a real fold round.
Nothing is postulated: the manifest, registry, clause-evidence family, entry
semantics, header cells, code, commitment scheme, and both entries are built,
and `start`/`append` are applied to them.

Two choices deserve to be visible rather than buried:

* the commitment is the honest one available at a `Digest` root -- the word
  space here is finite, so `Fintype.equivFin` gives an injective `commit`, and
  position binding is a THEOREM about it rather than a carried assumption.  It
  is not succinct and is not the deployed scheme; it is a witness.
* the fold root is chosen, which is legitimate because `start` takes
  `foldRoot` as an argument.  `FoldRecommitment` constrains the fold root at
  the entries it is applied to, and this module supplies a fold root meeting
  that constraint for its two entries.

What this does NOT show: that the DEPLOYED parameters admit a head, that any
particular semantic family is inhabited, or anything about cryptographic
security.  It shows the layer's theorems have subjects.
-/
import Assurance.SemanticHistoryFamily

namespace Minidregg.Assurance.HistoryHeadInhabitation

open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

/-- A small finite field, so the receipt word space is finite and an honest
injective `Digest` commitment exists. -/
abbrev Fld := ZMod 5

/-! ## Built parameters -/

/-- The empty-but-well-formed manifest. -/
def manifest : Manifest where
  manifestVersion := 1
  abiId := ⟨0⟩
  semanticProgramId := ⟨0⟩
  semanticRelationId := ⟨0⟩
  receiptCodecId := ⟨0⟩
  codecs := []
  carriers := []
  bridges := []
  dialectClauses := []
  transcriptControllerDigest := ⟨0⟩
  dimensions := []
  bounds := []

/-- No controllers, because the entries below carry no dialect clause. -/
def registry : ControllerRegistry.{0, 0, 0, 0} := ⟨[]⟩

/-- No clause evidence is ever demanded, so its carrier may be empty. -/
def clauseEvidence : ClauseEvidenceFamily manifest registry where
  Evidence := fun _ _ _ => PEmpty.{1}

/-- The header cells all read zero, which the entries below match exactly. -/
def headerCells : HistoryAdmissionContext → BindingIx → Fld := fun _ _ => 0

/-- The whole word space is the code, so membership is not the obstacle under
study here. -/
def code : Submodule Fld (BoundReceiptIx 1 → Fld) := ⊤

/-- Entry semantics that carry exactly their own rejection-atomicity
obligation.  This is the honest minimum: the family cannot be `Unit`, because
`rejectedCoreAtomic` is a real requirement about rejected contexts. -/
def family : EntrySemanticsFamily.{0} 1 Fld where
  Evidence := fun context claim =>
    PLift (∀ denial, context.outcome = .rejected denial →
      claim.witness.core.post = claim.witness.core.pre)
  rejectedCoreAtomic := by
    intro context claim evidence denial rejected
    exact evidence.down denial rejected

/-! ## An honest commitment at a `Digest` root -/

/-- Commit by the canonical finite enumeration of the word space.  Not
succinct, not deployed -- but injective, which is what binding needs. -/
def commitWord (word : BoundReceiptIx 1 → Fld) : Digest :=
  ⟨(Fintype.equivFin (BoundReceiptIx 1 → Fld) word).val⟩

theorem commitWord_injective : Function.Injective commitWord := by
  intro left right equal
  have vals : (Fintype.equivFin (BoundReceiptIx 1 → Fld) left).val =
      (Fintype.equivFin (BoundReceiptIx 1 → Fld) right).val :=
    congrArg Digest.value equal
  exact (Fintype.equivFin (BoundReceiptIx 1 → Fld)).injective (Fin.ext vals)

/-- The witness commitment: an opening is a claimed word, verification is that
it commits to the root and carries the claimed symbol.  Position binding is
PROVED from injectivity, not carried. -/
def scheme : BindingCommitment Digest Fld (BoundReceiptIx 1)
    (BoundReceiptIx 1 → Fld) where
  commit := commitWord
  openAt := fun word _ => word
  verifyOpen root index value opening :=
    commitWord opening = root ∧ opening index = value
  verifyOpen_commit := fun word index => ⟨rfl, rfl⟩
  binding := by
    rintro root index left right leftOpening rightOpening
      ⟨leftRoot, leftValue⟩ ⟨rightRoot, rightValue⟩
    have same : leftOpening = rightOpening :=
      commitWord_injective (leftRoot.trans rightRoot.symm)
    rw [← leftValue, ← rightValue, same]

/-! ## Two built entries -/

/-- The one satisfying receipt witness: nothing moves, nothing is touched. -/
def delta : ReceiptDelta (Key := Fin 1) (Value := Fld)
    (fun _ => 0) (fun _ => 0) where
  touched := ∅
  frame := fun _ _ => rfl

def witness : BoundReceiptWitness 1 Fld where
  binding := fun _ => 0
  core := ReceiptWitness.ofDelta delta

def claim : BoundSemanticReceiptClaim 1 Fld where
  witness := witness
  valid := ReceiptWitness.ofDelta_satisfies delta

/-- The genesis context: sequence zero, no predecessor, committed, no dialect
clauses, and both manifest identities exact. -/
def genesisContext : HistoryAdmissionContext where
  manifestAddress := manifest.contentAddress
  historyDomain := ⟨7⟩
  sequence := 0
  previousReceiptRoot := none
  semanticObjectRoot := ⟨0⟩
  semanticRelationId := manifest.semanticRelationId
  outcome := .committed
  preStateRoot := ⟨0⟩
  postStateRoot := ⟨0⟩
  effectRoot := ⟨0⟩
  authorizationRoot := ⟨0⟩
  disclosureRoot := ⟨0⟩
  dialectClauseRoots := []

theorem genesisContext_wellFormed : genesisContext.WellFormed manifest where
  manifestExact := rfl
  semanticRelationExact := rfl
  historyLink := Or.inl ⟨rfl, rfl⟩
  rejectedAtomic := trivial
  dialectClauseIdsUnique := List.nodup_nil
  dialectClausesClosed := fun _ absent => absurd absent (List.not_mem_nil)

def genesisEntry : VerifiedEntry (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := code) where
  context := genesisContext
  claim := claim
  semantics := PLift.up (fun _ rejected => by cases rejected)
  contextWellFormed := genesisContext_wellFormed
  dialectEvidence := ⟨fun index => index.elim0, fun index => index.elim0⟩
  bindingExact := by rfl
  codeword := Submodule.mem_top

/-- The successor context, linked to the genesis entry by its exact receipt
root and post-state. -/
def successorContext : HistoryAdmissionContext where
  manifestAddress := manifest.contentAddress
  historyDomain := ⟨7⟩
  sequence := 1
  previousReceiptRoot := some (commitWord (VerifiedEntry.word genesisEntry))
  semanticObjectRoot := ⟨1⟩
  semanticRelationId := manifest.semanticRelationId
  outcome := .committed
  preStateRoot := ⟨0⟩
  postStateRoot := ⟨0⟩
  effectRoot := ⟨0⟩
  authorizationRoot := ⟨0⟩
  disclosureRoot := ⟨0⟩
  dialectClauseRoots := []

theorem successorContext_wellFormed : successorContext.WellFormed manifest where
  manifestExact := rfl
  semanticRelationExact := rfl
  historyLink := Or.inr ⟨Nat.zero_lt_one, ⟨_, rfl⟩⟩
  rejectedAtomic := trivial
  dialectClauseIdsUnique := List.nodup_nil
  dialectClausesClosed := fun _ absent => absurd absent (List.not_mem_nil)

def successorEntry : VerifiedEntry (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := code) where
  context := successorContext
  claim := claim
  semantics := PLift.up (fun _ rejected => by cases rejected)
  contextWellFormed := successorContext_wellFormed
  dialectEvidence := ⟨fun index => index.elim0, fun index => index.elim0⟩
  bindingExact := by rfl
  codeword := Submodule.mem_top

/-! ## The head -/

/-- The chosen fold root.  Legitimate because `start` takes it as an argument;
`FoldRecommitment` constrains it only at the entries it is applied to. -/
def foldRoot : Digest → Fld → Digest → Digest :=
  fun _ _ _ => commitWord (VerifiedEntry.word genesisEntry +
    (1 : Fld) • VerifiedEntry.word successorEntry)

/-- **A head exists.**  One entry, zero fold rounds. -/
def genesisHead : VerifiedHistoryHead manifest registry clauseEvidence family
    headerCells code scheme :=
  VerifiedHistoryHead.start manifest registry clauseEvidence family
    headerCells code scheme foldRoot genesisEntry rfl rfl

theorem genesisHead_depth : genesisHead.depth = 1 := rfl

theorem genesisHead_foldRounds : genesisHead.foldRounds = 0 := rfl

theorem appendLink : VerifiedHistoryHead.AppendLink manifest registry clauseEvidence family
    headerCells code scheme genesisHead successorEntry where
  historyDomainExact := rfl
  sequenceExact := rfl
  predecessorExact := rfl
  stateExact := rfl

theorem foldRecommitment : VerifiedHistoryHead.FoldRecommitment manifest registry clauseEvidence
    family headerCells code scheme genesisHead successorEntry 1 where
  rootExact := rfl

/-- **A head with a real fold round exists.**  This is the object every
retained-history theorem quantifies over, and the one nothing in the tree had
ever produced. -/
def linkedHead : VerifiedHistoryHead manifest registry clauseEvidence family
    headerCells code scheme :=
  VerifiedHistoryHead.append manifest registry clauseEvidence family
    headerCells code scheme genesisHead successorEntry 1 appendLink
    foldRecommitment

/-- **The fold round is real.**  `0 < foldRounds` is the hypothesis
`historyBcsReduction`, `RawHistoryBcsOpenings`, and the checkpoint game all
require, and it is now discharged by a built object rather than assumed. -/
theorem linkedHead_foldRounds : linkedHead.foldRounds = 1 := rfl

theorem linkedHead_hasLink : 0 < linkedHead.foldRounds := by
  rw [linkedHead_foldRounds]
  exact Nat.zero_lt_one

theorem linkedHead_depth : linkedHead.depth = 2 := rfl

/-- The retained link word at the one fold round is the successor entry's
exact word -- the head really carries the entry it was appended, not a
placeholder. -/
theorem linkedHead_linkWord :
    linkedHead.foldLinkWord ⟨0, linkedHead_hasLink⟩ =
      VerifiedEntry.word successorEntry := rfl

/-- **Non-vacuity, stated as the audit wants it.**  The type every
retained-history theorem ranges over is inhabited, with a fold round. -/
theorem historyHead_nonempty :
    Nonempty { head : VerifiedHistoryHead manifest registry clauseEvidence
      family headerCells code scheme // 0 < head.foldRounds } :=
  ⟨⟨linkedHead, linkedHead_hasLink⟩⟩

#print axioms commitWord_injective
#print axioms genesisContext_wellFormed
#print axioms successorContext_wellFormed
#print axioms genesisHead_foldRounds
#print axioms linkedHead_foldRounds
#print axioms linkedHead_linkWord
#print axioms historyHead_nonempty

end

end Minidregg.Assurance.HistoryHeadInhabitation
