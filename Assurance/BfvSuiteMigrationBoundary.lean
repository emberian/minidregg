/-
# Assurance.BfvSuiteMigrationBoundary -- the exact BFV suite cutover boundary

The release-free BFV kernel statement currently owns zero sentinels for its
proof codec, proof suite, and proof controller.  `BoundReflectedChecker` quite
correctly rejects that statement, but replacing the three zeros is not a
transparent metadata operation: the pins are part of the canonical statement
bytes and of the roots-before-challenges statement digest.

This module makes the only honest migration explicit.  Given a real
`ReflectedCheckerInterface`, `rebind` changes exactly the three deployment pins
and `rebindBound` constructs its `BoundReflectedChecker`.  All semantic payload
fields are preserved.  For a zero-pinned source, however, the target statement
and its canonical bytes are provably different.  If their cSHAKE statement
digests are equal, the equality is retained as the exact framed collision that
a security game must price.  A receipt accepted under both statements likewise
extracts that collision.

There is a second, equally important obstruction.  `ReflectedCheckerInterface`
only asks for a reflected checker; it does not ask for BFV arithmetic, a PCS,
knowledge, or hiding.  `controlOnlyChecker` is an executable countermodel with
nonzero pins which merely repeats the framing checker.  Its positive receipt
shows why constructing `Nonempty (BoundReflectedChecker statement)` alone would
be a misleading closure claim.  The load-bearing deployment object remains
`SameCoinReductionLaws` on one common coin, with arithmetic, PCS, CR, ROM, and
PoK priced separately.  No privacy or hiding claim is introduced here, and
opaque native code still crosses only the existing bytes/error boundary.
-/

import Assurance.BfvProofControllerAdmission
import Compiler.Tower256CshakeMerkleBinding

namespace Minidregg.Assurance.BfvSuiteMigrationBoundary

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Assurance.BfvProofControllerAdmission
open Minidregg.Compiler.BfvProofController
open Minidregg.Compiler.BfvReceiptClause
open Minidregg.Compiler.Tower256CshakeMerkleBinding
open Minidregg.Loom
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

/-! ## Exact deployment-pin migration -/

/-- Equality of every statement field except the three proof-deployment pins.
This is the exact semantic payload which a suite migration must preserve. -/
structure SameSemanticPayload (left right : Statement) : Prop where
  argsDigest : left.argsDigest = right.argsDigest
  effectsDigest : left.effectsDigest = right.effectsDigest
  preRoot : left.preRoot = right.preRoot
  publicInputDescriptor :
    left.publicInputDescriptor = right.publicInputDescriptor
  outputCommitment : left.outputCommitment = right.outputCommitment
  relationDescriptor : left.relationDescriptor = right.relationDescriptor
  clauseId : left.clauseId = right.clauseId
  relationId : left.relationId = right.relationId
  outputRepresentationId :
    left.outputRepresentationId = right.outputRepresentationId

/-- Rebind a statement to a supplied reflected checker.  This is deliberately not an
in-place cast: the three identities are statement data. -/
def rebind (source : Statement) (checker : ReflectedCheckerInterface) : Statement :=
  { source with
    proofCodecId := checker.proofCodecId
    proofSuiteId := checker.proofSuiteId
    controllerDigest := checker.controllerDigest }

theorem rebind_sameSemanticPayload (source : Statement)
    (checker : ReflectedCheckerInterface) :
    SameSemanticPayload source (rebind source checker) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rebind_pins_exact (source : Statement)
    (checker : ReflectedCheckerInterface) :
    (rebind source checker).proofCodecId = checker.proofCodecId ∧
      (rebind source checker).proofSuiteId = checker.proofSuiteId ∧
      (rebind source checker).controllerDigest = checker.controllerDigest := by
  exact ⟨rfl, rfl, rfl⟩

/-- Once an actual suite exists, the type-level binding itself is canonical;
there is no opportunity for a caller to choose different statement pins. -/
def rebindBound (source : Statement) (checker : ReflectedCheckerInterface) :
    BoundReflectedChecker (rebind source checker) where
  checker := checker
  proofCodecBound := rfl
  proofSuiteBound := rfl
  controllerBound := rfl

/-- A zero-pinned source cannot equal its assigned target. -/
theorem rebind_ne_of_unassignedProofCodec (source : Statement)
    (checker : ReflectedCheckerInterface)
    (sourceUnassigned : source.proofCodecId = unassignedProofCodecId) :
    source ≠ rebind source checker := by
  intro equal
  have pinsEqual := congrArg Statement.proofCodecId equal
  apply checker.proofCodecAssigned
  calc
    checker.proofCodecId = (rebind source checker).proofCodecId := rfl
    _ = source.proofCodecId := pinsEqual.symm
    _ = unassignedProofCodecId := sourceUnassigned
    _ = ⟨0⟩ := rfl

/-- The canonical statement byte stream changes at the cutover. -/
theorem rebind_encode_ne_of_unassignedProofCodec (source : Statement)
    (checker : ReflectedCheckerInterface)
    (sourceUnassigned : source.proofCodecId = unassignedProofCodecId) :
    statementCodec.encode source ≠ statementCodec.encode (rebind source checker) := by
  intro encodedEqual
  exact rebind_ne_of_unassignedProofCodec source checker sourceUnassigned
    (lawfulCodec_encode_injective statementCodec encodedEqual)

/-! ## Digest equality is an explicit cSHAKE collision, not migration glue -/

/-- The exact same-customization collision induced if two different canonical
BFV statements receive one statement digest. -/
def StatementDigestCollision (left right : Statement) : Prop :=
  FramedXofCollision cshake statementDigestCustomization
    (statementCodec.encode left) (statementCodec.encode right)

theorem statementDigestCollision_of_ne_of_digest_eq
    {left right : Statement} (different : left ≠ right)
    (digestEqual : derivedStatementDigest left = derivedStatementDigest right) :
    StatementDigestCollision left right := by
  refine ⟨?_, digestEqual⟩
  intro encodedEqual
  exact different (lawfulCodec_encode_injective statementCodec encodedEqual)

theorem rebind_statementDigestCollision_of_digest_eq (source : Statement)
    (checker : ReflectedCheckerInterface)
    (sourceUnassigned : source.proofCodecId = unassignedProofCodecId)
    (digestEqual :
      derivedStatementDigest source = derivedStatementDigest (rebind source checker)) :
    StatementDigestCollision source (rebind source checker) :=
  statementDigestCollision_of_ne_of_digest_eq
    (rebind_ne_of_unassignedProofCodec source checker sourceUnassigned) digestEqual

theorem rebind_digest_ne_of_collisionFree (source : Statement)
    (checker : ReflectedCheckerInterface)
    (sourceUnassigned : source.proofCodecId = unassignedProofCodecId)
    (collisionFree : ¬StatementDigestCollision source (rebind source checker)) :
    derivedStatementDigest source ≠ derivedStatementDigest (rebind source checker) := by
  intro digestEqual
  exact collisionFree
    (rebind_statementDigestCollision_of_digest_eq source checker sourceUnassigned
      digestEqual)

/-- One receipt cannot pass the deterministic controller under both the old
and assigned statements unless the exact statement-digest collision occurs.
This is the deterministic reduction; no CR probability is asserted. -/
theorem controlReplay_implies_statementDigestCollision
    {left right : Statement} (different : left ≠ right) (receipt : Receipt)
    (leftAccepted : ControlAccepts left receipt)
    (rightAccepted : ControlAccepts right receipt) :
    StatementDigestCollision left right := by
  have digestEqual : derivedStatementDigest left = derivedStatementDigest right := by
    calc
      derivedStatementDigest left = receipt.statementDigest :=
        leftAccepted.2.2.2.1.symm
      _ = derivedStatementDigest right := rightAccepted.2.2.2.1
  exact statementDigestCollision_of_ne_of_digest_eq different digestEqual

theorem no_controlReplay_of_collisionFree
    {left right : Statement} (different : left ≠ right)
    (collisionFree : ¬StatementDigestCollision left right) (receipt : Receipt) :
    ¬(ControlAccepts left receipt ∧ ControlAccepts right receipt) := by
  rintro ⟨leftAccepted, rightAccepted⟩
  exact collisionFree
    (controlReplay_implies_statementDigestCollision different receipt
      leftAccepted rightAccepted)

/-! ## The structural suite interface is intentionally not a security theorem -/

def controlOnlyProofCodecId : Digest := ⟨981⟩
def controlOnlyProofSuiteId : Digest := ⟨982⟩
def controlOnlyControllerDigest : Digest := ⟨983⟩

/-- Countermodel: assigned identities plus an executable reflected checker,
but no BFV arithmetic, PCS opening, extraction, PoK, or hiding semantics.  This
exists to prevent reflected-checker inhabitation from being mistaken for deployment
closure. -/
def controlOnlyChecker : ReflectedCheckerInterface where
  proofCodecId := controlOnlyProofCodecId
  proofSuiteId := controlOnlyProofSuiteId
  controllerDigest := controlOnlyControllerDigest
  proofCodecAssigned := by decide
  proofSuiteAssigned := by decide
  controllerAssigned := by decide
  ReflectedAccepts := ControlAccepts
  check := controlCheck
  check_iff := controlCheck_iff

def controlOnlyStatement (source : Statement) : Statement :=
  rebind source controlOnlyChecker

def controlOnlyBound (source : Statement) :
  BoundReflectedChecker (controlOnlyStatement source) :=
  rebindBound source controlOnlyChecker

theorem controlOnlyChecker_accepts_iff_control (statement : Statement)
    (receipt : Receipt) :
    (controlOnlyBound statement).checker.ReflectedAccepts
        (controlOnlyStatement statement) receipt ↔
      ControlAccepts (controlOnlyStatement statement) receipt := by
  rfl

/-- A canonical nonempty frame whose challenge is derived after both roots.
The proof bytes are deliberately meaningless. -/
def controlOnlyReceipt (statement : Statement)
    (arithmeticRoot pcsRoot : Digest) : Receipt :=
  let seed : Receipt :=
    { statementDigest := derivedStatementDigest statement
      arithmeticRoot := arithmeticRoot
      pcsRoot := pcsRoot
      challenge := ⟨0⟩
      arithmeticProof := [0]
      pcsProof := [0] }
  { seed with challenge := derivedChallenge statement seed }

theorem controlOnlyReceipt_controlled (statement : Statement)
    (arithmeticRoot pcsRoot : Digest)
    (relationDescriptorExact : statement.relationDescriptor = exactRelationDescriptor)
    (clauseExact : statement.clauseId = bfvClauseId)
    (relationExact : statement.relationId = bfvRelationId) :
    ControlAccepts statement (controlOnlyReceipt statement arithmeticRoot pcsRoot) := by
  refine ⟨relationDescriptorExact, clauseExact, relationExact, rfl, ?_, ?_, ?_⟩
  · apply derivedChallenge_independent_of_proofBytes
    exact ⟨rfl, rfl⟩
  · simp [controlOnlyReceipt]
  · simp [controlOnlyReceipt]

/-- Positive counterexample: the nonzero bound interface accepts a framed
receipt for every canonical BFV relation statement, despite checking no row.
The missing object is therefore the common-game `SameCoinReductionLaws`, not a
value of `BoundReflectedChecker`. -/
theorem controlOnlyBound_is_not_deployment_closure (source : Statement)
    (relationDescriptorExact : source.relationDescriptor = exactRelationDescriptor)
    (clauseExact : source.clauseId = bfvClauseId)
    (relationExact : source.relationId = bfvRelationId)
    (arithmeticRoot pcsRoot : Digest) :
    (controlOnlyBound source).checker.ReflectedAccepts
      (controlOnlyStatement source)
      (controlOnlyReceipt (controlOnlyStatement source) arithmeticRoot pcsRoot) := by
  apply controlOnlyReceipt_controlled
  · exact relationDescriptorExact
  · exact clauseExact
  · exact relationExact

/-! ## Same-coin replay pricing -/

variable {Omega : Type} [Fintype Omega]

/-- A suite cutover replay is selected by the same coin as the BFV execution;
native failure or rejection remains `none`. -/
def ReplayEvent (source target : Statement)
    (execution : Omega → Option Receipt) (omega : Omega) : Prop :=
  ∃ receipt, execution omega = some receipt ∧
    ControlAccepts source receipt ∧ ControlAccepts target receipt

/-- Exact adapter into the BFV common ledger's collision-resistance class.
`collisionCovers` is the deployment reduction/pricing obligation; it cannot be
manufactured by deterministic Lean code. -/
structure SameCoinReplayFamily (source target : Statement)
    (ledger : BfvProofControllerAdmission.FailureLedger Omega) where
  statementsDifferent : source ≠ target
  execution : Omega → Option Receipt
  collisionCovers : ∀ omega,
    ReplayEvent source target execution omega →
      (ledger .collisionResistance).event omega

namespace SameCoinReplayFamily

variable {source target : Statement}
variable {ledger : BfvProofControllerAdmission.FailureLedger Omega}

theorem replay_extracts_collision
    (family : SameCoinReplayFamily source target ledger) {omega : Omega}
    (replay : ReplayEvent source target family.execution omega) :
    StatementDigestCollision source target := by
  obtain ⟨receipt, -, sourceAccepted, targetAccepted⟩ := replay
  exact controlReplay_implies_statementDigestCollision
    family.statementsDifferent receipt sourceAccepted targetAccepted

theorem replay_le_collisionPrice
    (family : SameCoinReplayFamily source target ledger) :
    uniformProb Omega (ReplayEvent source target family.execution) ≤
      (ledger .collisionResistance).price :=
  le_trans (uniformProb_mono family.collisionCovers)
    (ledger .collisionResistance).bound

end SameCoinReplayFamily

/-! ## Axiom pins -/

/-- info: 'Minidregg.Assurance.BfvSuiteMigrationBoundary.rebind_encode_ne_of_unassignedProofCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms rebind_encode_ne_of_unassignedProofCodec
/-- info: 'Minidregg.Assurance.BfvSuiteMigrationBoundary.controlReplay_implies_statementDigestCollision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms controlReplay_implies_statementDigestCollision
/-- info: 'Minidregg.Assurance.BfvSuiteMigrationBoundary.controlOnlyBound_is_not_deployment_closure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms controlOnlyBound_is_not_deployment_closure
/-- info: 'Minidregg.Assurance.BfvSuiteMigrationBoundary.SameCoinReplayFamily.replay_le_collisionPrice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms SameCoinReplayFamily.replay_le_collisionPrice

end

end Minidregg.Assurance.BfvSuiteMigrationBoundary
