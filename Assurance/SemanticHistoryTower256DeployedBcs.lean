/-
# Assurance.SemanticHistoryTower256DeployedBcs -- the actual history FS event

This module replaces a caller-selected history `Prop` with the exact
Fiat--Shamir knowledge-failure event of the retained-history BCS reduction.
The proof string is checked by `fiatShamir`, hence by `accReductionBcs`'s
opening-checking verifier, on the exact head, chain, commitment, domain,
queries, and opened messages already stored by the checkpoint family.

The boundary is deliberately sharp:

* `joint.math` supplies the ideal MCA/minimum-distance hypotheses and proves
  the native random-oracle game bound;
* `pcs.positionBinding` is already an explicit CR premise of the concrete
  Tower256 PCS object;
* transporting an arbitrary common coin to the native FS coins is explicit;
* classifying an actual false acceptance as PCS, CR, or ROM failure remains
  an explicit computational reduction.  No landed theorem derives that
  pointwise classification from MCA or verifier execution alone;
* hiding is not used by this soundness statement.
-/

import Assurance.SemanticHistoryTower256CheckpointGame

namespace Minidregg.Assurance.SemanticHistoryTower256DeployedBcs

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryBcsGame
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticHistoryTower256CheckpointGame
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.Tower256AdditiveFriControllerAdmission
open Minidregg.Compiler.AdditiveFriReceiptClause
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriController
open Minidregg.Loom
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

universe uSemantics uTranscript uClauseInput uClauseQuery
  uClauseReply uClauseOutcome

variable {ell m queryCount n : Nat}
variable {manifest : Manifest}
variable {pcs : MerklePcs ell}
variable {clause : FriClause pcs m manifest}
variable {verifier : Verifier (queryCount := queryCount) pcs clause}

local instance : DecidableEq TowerField := Classical.decEq _
local instance : Fintype TowerField := Fintype.ofFinite _

variable
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n TowerField}
    {headerCells : HistoryAdmissionContext → BindingIx → TowerField}
variable {Omega : Type} [Fintype Omega] [DecidableEq Omega]
variable {Transcript : Type uTranscript}
variable {Error : Type} {request : List UInt8}

local notation "BoundJoint" => JointGameFamily
  (ell := ell) (m := m) (queryCount := queryCount) (n := n)
  (manifest := manifest) (pcs := pcs) (clause := clause)
  (verifier := verifier) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (Omega := Omega)
  (Transcript := Transcript) (Error := Error) (request := request)

/-- The exact unshifted BCS reduction determined by a retained checkpoint. -/
abbrev HistoryReduction (joint : BoundJoint) :=
  historyBcsReduction joint.checkpoint.head joint.historyHasLink
    joint.deltaStar joint.deltaStarPositive joint.deltaStarLeOne
    joint.domain joint.degree joint.openedCount joint.openings

/-- One native ROM experiment against the exact retained-history reduction. -/
structure NativeHistoryRun (joint : BoundJoint) where
  statementSet : Set (Stmt (HistoryReduction joint))
  saltBudget : Nat
  queryBudget : Nat
  delta : Real
  deltaInterior : delta ∈ Set.Ioo (0 : Real) (HistoryReduction joint).δstar
  prover : SrProver (HistoryReduction joint) saltBudget

namespace NativeHistoryRun

/-- The exact native lazy-ROM coin space used by `FsStraightlineKnowledgeSoundness`. -/
abbrev Coins (joint : BoundJoint) (run : NativeHistoryRun joint) :=
  (Fin run.queryBudget → (HistoryReduction joint).Chal) ×
    (Fin (HistoryReduction joint).k → (HistoryReduction joint).Chal)

/-- The straightline extractor supplied by the proved retained-history ideal
BCS theorem. -/
noncomputable def extractor (joint : BoundJoint)
    (run : NativeHistoryRun joint) :
    SrExtractor (HistoryReduction joint) run.saltBudget := by
  let sound := joint.idealHistoryFiatShamir run.statementSet
  unfold FsStraightlineKnowledgeSoundness at sound
  exact Classical.choose sound run.saltBudget

/-- The actual FS verifier accepts the adversary's proof and its proposed
target witness satisfies the relaxed target relation. -/
def VerifierAccepts (joint : BoundJoint) (run : NativeHistoryRun joint)
    (coins : run.Coins joint) : Prop :=
  let log := srTrace run.prover coins.1
  let output := run.prover.out (log.map Prod.snd)
  let challenges : Fin (HistoryReduction joint).k →
      (HistoryReduction joint).Chal :=
    srFinalChal run.prover coins.1 coins.2
  ∃ (x' : (HistoryReduction joint).X')
      (y' : Fin (HistoryReduction joint).n' → (HistoryReduction joint).A'),
    fiatShamir (HistoryReduction joint) run.saltBudget
        (fsOracle output challenges) output = some (x', y') ∧
      RelaxedMem (HistoryReduction joint).R' run.delta output.stmt.idx
        x' y' output.w'

/-- The exact knowledge-false-acceptance event: the output statement is in
scope, the actual FS verifier accepts a valid relaxed target, but the proved
straightline extractor fails the relaxed source relation. -/
def FalseAccept (joint : BoundJoint) (run : NativeHistoryRun joint)
    (coins : run.Coins joint) : Prop :=
  let log := srTrace run.prover coins.1
  let output := run.prover.out (log.map Prod.snd)
  let challenges : Fin (HistoryReduction joint).k →
      (HistoryReduction joint).Chal :=
    srFinalChal run.prover coins.1 coins.2
  output.stmt ∈ run.statementSet ∧
    ¬RelaxedMem (HistoryReduction joint).R run.delta output.stmt.idx
      output.stmt.x output.stmt.y
      (run.extractor joint output challenges log) ∧
    ∃ (x' : (HistoryReduction joint).X')
        (y' : Fin (HistoryReduction joint).n' → (HistoryReduction joint).A'),
      fiatShamir (HistoryReduction joint) run.saltBudget
          (fsOracle output challenges) output = some (x', y') ∧
        RelaxedMem (HistoryReduction joint).R' run.delta output.stmt.idx
          x' y' output.w'

/-- The landed MCA/BCS/Fiat--Shamir theorem bounds this literal verifier
event on its native lazy-ROM coin space. -/
theorem falseAccept_le (joint : BoundJoint) (run : NativeHistoryRun joint) :
    uniformProb (run.Coins joint) (run.FalseAccept joint) ≤
      joint.historyFsError run.saltBudget run.queryBudget run.delta := by
  have hsound := Classical.choose_spec
    (show ∃ E : (s : Nat) → SrExtractor (HistoryReduction joint) s,
      ∀ (s t : Nat), ∀ delta ∈ Set.Ioo (0 : Real)
          (HistoryReduction joint).δstar, ∀ P : SrProver (HistoryReduction joint) s,
        uniformProb ((Fin t → (HistoryReduction joint).Chal) ×
          (Fin (HistoryReduction joint).k → (HistoryReduction joint).Chal))
          (fun coins =>
            let log := srTrace P coins.1
            let output := P.out (log.map Prod.snd)
            let challenges : Fin (HistoryReduction joint).k →
                (HistoryReduction joint).Chal :=
              srFinalChal P coins.1 coins.2
            output.stmt ∈ run.statementSet ∧
              ¬RelaxedMem (HistoryReduction joint).R delta output.stmt.idx
                output.stmt.x output.stmt.y (E s output challenges log) ∧
              ∃ (x' : (HistoryReduction joint).X')
                  (y' : Fin (HistoryReduction joint).n' →
                    (HistoryReduction joint).A'),
                fiatShamir (HistoryReduction joint) s
                    (fsOracle output challenges) output = some (x', y') ∧
                  RelaxedMem (HistoryReduction joint).R' delta output.stmt.idx
                    x' y' output.w') ≤ joint.historyFsError s t delta by
        simpa only [FsStraightlineKnowledgeSoundness] using
          joint.idealHistoryFiatShamir run.statementSet)
  simpa [FalseAccept, extractor] using
    hsound run.saltBudget run.queryBudget run.delta run.deltaInterior run.prover

end NativeHistoryRun

/-! ## Exact realization on the common coin -/

/-- A concrete common-game coin supplies the two native lazy-ROM coin vectors.
This is data, not a parallel caller-selected challenge schedule. -/
structure CommonCoinHistoryRun (joint : BoundJoint) where
  native : NativeHistoryRun joint
  coins : Omega → native.Coins joint

namespace CommonCoinHistoryRun

/-- Actual history-verifier acceptance on the already-shared `Omega`. -/
def VerifierAccepts (joint : BoundJoint) (run : CommonCoinHistoryRun joint)
    (omega : Omega) : Prop :=
  run.native.VerifierAccepts joint (run.coins omega)

/-- Actual history knowledge failure on the already-shared `Omega`. -/
def FalseAccept (joint : BoundJoint) (run : CommonCoinHistoryRun joint)
    (omega : Omega) : Prop :=
  run.native.FalseAccept joint (run.coins omega)

/-- Exact uniform transport from the common coin to the native FS game.
This is the remaining probabilistic ROM/common-coin realization premise. -/
structure UniformRealization (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint) : Prop where
  probabilityExact : ∀ event : run.native.Coins joint → Prop,
    uniformProb Omega (fun omega => event (run.coins omega)) =
      uniformProb (run.native.Coins joint) event

/-- With exact coin transport, the native ideal theorem prices the literal
common-coin false-acceptance predicate. -/
theorem falseAccept_le_of_uniform (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint)
    (uniform : UniformRealization joint run) :
    uniformProb Omega (run.FalseAccept joint) ≤
      joint.historyFsError run.native.saltBudget run.native.queryBudget
        run.native.delta := by
  change uniformProb Omega
      (fun omega => run.native.FalseAccept joint (run.coins omega)) ≤ _
  rw [uniform.probabilityExact (run.native.FalseAccept joint)]
  exact run.native.falseAccept_le joint

end CommonCoinHistoryRun

/-! ## The remaining computational PCS/CR/ROM reduction -/

/-- The exact remaining deployment obligation.  Its domain is no longer a
caller-chosen proposition: it is the literal retained-history FS failure
defined above.  Its codomain is exactly PCS failure, concrete commitment
binding/CR failure, or ROM/common-coin transport failure on the same coin.

This is intentionally a structure, not a theorem manufactured here: the
landed ideal APIs provide a probability bound, while the common ledger needs
a pointwise computational classifier. -/
structure PcsCrRomReduction (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint) : Prop where
  classify : ∀ omega, run.FalseAccept joint omega →
    (joint.tower.ledger .historyPcs).event omega ∨
    (joint.tower.ledger .commitmentBinding).event omega ∨
    (joint.tower.ledger .oracleTransport).event omega

namespace PcsCrRomReduction

/-- The exact three-event common-ledger cover, now for the real FS event. -/
theorem falseAccept_cover (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint)
    (reduction : PcsCrRomReduction joint run) (omega : Omega) :
    run.FalseAccept joint omega → joint.tower.ledger.Bad omega := by
  intro falseAccept
  rcases reduction.classify omega falseAccept with pcs | binding | rom
  · exact Or.inr (Or.inr (Or.inl pcs))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl binding))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rom)))))

/-- The computational classifier is load-bearing: if an actual FS failure
occurs while all three named events are good, no such reduction can exist. -/
theorem impossible_of_falseAccept_and_threeGood (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint) (omega : Omega)
    (falseAccept : run.FalseAccept joint omega)
    (pcsGood : joint.tower.ledger.Good .historyPcs omega)
    (bindingGood : joint.tower.ledger.Good .commitmentBinding omega)
    (romGood : joint.tower.ledger.Good .oracleTransport omega) :
    ¬PcsCrRomReduction joint run := by
  intro reduction
  rcases reduction.classify omega falseAccept with pcs | binding | rom
  · exact pcsGood pcs
  · exact bindingGood binding
  · exact romGood rom

end PcsCrRomReduction

/-! ## Actual history plus concrete additive controller -/

namespace CommonCoinHistoryRun

/-- End-to-end false acceptance with the real history FS predicate and the
existing concrete additive-controller predicate. -/
def JointFalseAccept (joint : BoundJoint) (run : CommonCoinHistoryRun joint)
    (omega : Omega) : Prop :=
  run.FalseAccept joint omega ∨ joint.tower.FalseAccept omega

/-- Both actual component predicates reduce to the same four events at the
same `omega`; no independence assumption appears. -/
theorem jointFalseAccept_bad (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint)
    (reduction : PcsCrRomReduction joint run) (omega : Omega) :
    run.JointFalseAccept joint omega → joint.Bad omega := by
  rintro (history | additive)
  · rcases reduction.classify omega history with pcs | binding | rom
    · exact Or.inl pcs
    · exact Or.inr (Or.inr (Or.inl binding))
    · exact Or.inr (Or.inr (Or.inr rom))
  · obtain ⟨reply, selected, falseStatement⟩ := additive
    rcases joint.tower.failureCover omega reply selected falseStatement with
      proximity | binding | rom
    · exact Or.inr (Or.inl proximity)
    · exact Or.inr (Or.inr (Or.inl binding))
    · exact Or.inr (Or.inr (Or.inr rom))

/-- The common security game with the external history predicate removed. -/
def securityGame (joint : BoundJoint) (run : CommonCoinHistoryRun joint)
    (reduction : PcsCrRomReduction joint run) :
    SecurityGame Omega Digest (List UInt8) TowerField Digest m where
  transcript := joint.tower.schedule
  ledger := joint.tower.ledger
  falseAccept := run.JointFalseAccept joint
  failureCover := fun omega accepted =>
    joint.bad_implies_ledgerBad omega
      (run.jointFalseAccept_bad joint reduction omega accepted)

/-- The sharpened four-event end-to-end price. -/
theorem jointFalseAccept_le (joint : BoundJoint)
    (run : CommonCoinHistoryRun joint)
    (reduction : PcsCrRomReduction joint run) :
    uniformProb Omega (run.JointFalseAccept joint) ≤ joint.Price :=
  le_trans (uniformProb_mono (run.jointFalseAccept_bad joint reduction))
    joint.bad_le_price

end CommonCoinHistoryRun

#print axioms NativeHistoryRun.falseAccept_le
#print axioms CommonCoinHistoryRun.falseAccept_le_of_uniform
#print axioms PcsCrRomReduction.falseAccept_cover
#print axioms PcsCrRomReduction.impossible_of_falseAccept_and_threeGood
#print axioms CommonCoinHistoryRun.jointFalseAccept_bad
#print axioms CommonCoinHistoryRun.jointFalseAccept_le

end

end Minidregg.Assurance.SemanticHistoryTower256DeployedBcs
