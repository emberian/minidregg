/-
# Assurance.SemanticHistoryRecursiveAir -- an exact stateless-history AIR adapter

This module closes one precise part of the recursive-receipt story.  A public
`StatelessHistoryStatement` names only the manifest/history domain, depth,
terminal state root, and current accumulator root.  A proof-relevant
`Realizes` object binds that small statement to an arbitrary-depth
`VerifiedHistoryHead`.

The recursive verifier circuit is assembled from the existing, proved
sumcheck verifier, FRI-query verifier, and Merkle-membership gadgets.  Its
keystone theorem is an iff with all three semantic checks.  The level-zero FRI
root wire is then tied literally to the semantic history accumulator root.

This is an honest recursive *adapter*, not a PCD theorem.  In particular it
does not manufacture:

* commitment collision resistance or a Fiat--Shamir ROM;
* ordinary soundness or knowledge soundness;
* zero knowledge; or
* simulation extractability.

Those four security notions are intentionally four independent proposition
parameters in `SecurityEvidence`; none follows from AIR acceptance.  The
module proves only the deterministic circuit/meaning equivalence and the
exact public-root attribution needed by a later concrete recursive argument.
-/

import Assurance.SemanticHistoryFamily
import Compiler.FriQueryVerifierAir
import Compiler.AirMembership

namespace Minidregg.Assurance.SemanticHistoryRecursiveAir

open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Compiler
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom

set_option autoImplicit false

universe uSemantics uOp uIdx
  uClauseInput uClauseQuery uClauseReply uClauseOutcome uClauseEvidence

noncomputable section

/-! ## A small public statement for an arbitrary-depth semantic history -/

/-- The public data needed to refer to one semantic history head without
carrying its entries or folded word.  Digests stay digests at the semantic
boundary; only the accumulator root is encoded into the recursive AIR field.
-/
structure StatelessHistoryStatement (F : Type*) where
  manifestAddress : Digest
  historyDomain : Digest
  depth : Nat
  terminalStateRoot : Digest
  accumulatorRoot : F
deriving Repr

section SemanticBinding

variable {F : Type*} [Field F] [DecidableEq F]
variable {n : Nat}
variable
    {Op : Type uOp}
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

/-- Exact semantic realization of the small public statement.  Every field is
derived from the verified head; callers cannot substitute an unrelated depth,
history domain, terminal state, or accumulator root. -/
structure StatelessHistoryStatement.Realizes
    (encodeDigest : Digest → F)
    (statement : StatelessHistoryStatement F)
    (head : HistoryHead) : Prop where
  manifestExact : statement.manifestAddress = manifest.contentAddress
  historyDomainExact :
    statement.historyDomain = head.latest.context.historyDomain
  depthExact : statement.depth = head.depth
  terminalStateExact :
    statement.terminalStateRoot = head.latest.context.postStateRoot
  accumulatorRootExact :
    statement.accumulatorRoot = encodeDigest head.accumulator.rt

/-- Canonical stateless projection of a verified semantic head. -/
def StatelessHistoryStatement.ofHead
    (encodeDigest : Digest → F) (head : HistoryHead) :
    StatelessHistoryStatement F where
  manifestAddress := manifest.contentAddress
  historyDomain := head.latest.context.historyDomain
  depth := head.depth
  terminalStateRoot := head.latest.context.postStateRoot
  accumulatorRoot := encodeDigest head.accumulator.rt

theorem StatelessHistoryStatement.ofHead_realizes
    (encodeDigest : Digest → F) (head : HistoryHead) :
    (StatelessHistoryStatement.ofHead encodeDigest head).Realizes
      encodeDigest head := by
  constructor <;> rfl

end SemanticBinding

/-! ## One shared-wire recursive verifier system -/

variable {F : Type uIdx} [Field F]
variable {Idx : Type uIdx}
variable {sumcheckRounds friRounds : Nat}

/-- Wire layout for one recursive verification.  Sharing an `Idx` value is
literal wire sharing.  In particular `friRoot 0` is the level-zero FRI root;
the typed receipt below binds that wire to the semantic accumulator root.

The next value of FRI round `k` is authenticated at root `k+1`, while its two
input openings are authenticated at root `k`. -/
structure RecursiveVerifierWiring (Idx : Type uIdx)
    (sumcheckRounds friRounds : Nat) where
  sumcheckClaim : Idx
  sumcheckFinal : Idx
  sumcheckG0 : Fin sumcheckRounds → Idx
  sumcheckG1 : Fin sumcheckRounds → Idx
  sumcheckChallenge : Fin sumcheckRounds → Idx
  sumcheckRoot : Idx
  sumcheckPath : List (Idx × Idx)

  friFinal : Idx
  friLo : Fin friRounds → Idx
  friHi : Fin friRounds → Idx
  friNext : Fin friRounds → Idx
  friChallenge : Fin friRounds → Idx
  friTwiddle : Fin friRounds → Idx
  friTwoX : Fin friRounds → Idx
  friRoot : Fin (friRounds + 1) → Idx
  friLoPath : Fin friRounds → List (Idx × Idx)
  friHiPath : Fin friRounds → List (Idx × Idx)
  friNextPath : Fin friRounds → List (Idx × Idx)

/-- Semantic meaning of one Merkle-membership gadget, kept as a named clause
so the composite verifier statement remains readable. -/
def MerkleOpeningAccepts (asg : Idx → F) (spec : PermSpec F 2)
    (leaf root : Idx) (path : List (Idx × Idx)) : Prop :=
  (∀ sd ∈ path, asg sd.2 = 0 ∨ asg sd.2 = 1) ∧
    asg root = merkleMuxExec spec (asg leaf)
      (path.map fun sd => (asg sd.1, asg sd.2))

/-- The three authenticated openings used by one FRI fold. -/
def friRoundOpeningGadget (spec : PermSpec F 2)
    (wiring : RecursiveVerifierWiring Idx sumcheckRounds friRounds)
    (round : Fin friRounds) : ConstraintSystem F Idx :=
  membershipGadget spec (wiring.friLo round)
      (wiring.friRoot ⟨round, Nat.lt_succ_of_lt round.isLt⟩)
      (wiring.friLoPath round) ++
    membershipGadget spec (wiring.friHi round)
      (wiring.friRoot ⟨round, Nat.lt_succ_of_lt round.isLt⟩)
      (wiring.friHiPath round) ++
    membershipGadget spec (wiring.friNext round)
      (wiring.friRoot ⟨round + 1, Nat.succ_lt_succ round.isLt⟩)
      (wiring.friNextPath round)

/-- Exact semantic meaning of the three authenticated FRI openings. -/
def FriRoundOpeningsAccept
    (asg : Idx → F) (spec : PermSpec F 2)
    (wiring : RecursiveVerifierWiring Idx sumcheckRounds friRounds)
    (round : Fin friRounds) : Prop :=
  MerkleOpeningAccepts asg spec (wiring.friLo round)
      (wiring.friRoot ⟨round, Nat.lt_succ_of_lt round.isLt⟩)
      (wiring.friLoPath round) ∧
    MerkleOpeningAccepts asg spec (wiring.friHi round)
      (wiring.friRoot ⟨round, Nat.lt_succ_of_lt round.isLt⟩)
      (wiring.friHiPath round) ∧
    MerkleOpeningAccepts asg spec (wiring.friNext round)
      (wiring.friRoot ⟨round + 1, Nat.succ_lt_succ round.isLt⟩)
      (wiring.friNextPath round)

/-- All FRI opening gadgets, in round order. -/
def friOpeningGadgets (spec : PermSpec F 2)
    (wiring : RecursiveVerifierWiring Idx sumcheckRounds friRounds) :
    ConstraintSystem F Idx :=
  (List.finRange friRounds).flatMap (friRoundOpeningGadget spec wiring)

/-- The recursive verifier AIR: sumcheck verification, FRI fold verification,
one authenticated sumcheck terminal opening, and all authenticated FRI query
openings.  All components are existing Lean-derived DSL gadgets. -/
def recursiveHistoryVerifierGadget
    (hashSpec : PermSpec F 2) (half : F)
    (wiring : RecursiveVerifierWiring Idx sumcheckRounds friRounds) :
    ConstraintSystem F Idx :=
  sumcheckVerifierGadget wiring.sumcheckClaim wiring.sumcheckFinal
      wiring.sumcheckG0 wiring.sumcheckG1 wiring.sumcheckChallenge ++
    friQueryVerifierGadget half wiring.friFinal wiring.friLo wiring.friHi
      wiring.friNext wiring.friChallenge wiring.friTwiddle wiring.friTwoX ++
    membershipGadget hashSpec wiring.sumcheckFinal wiring.sumcheckRoot
      wiring.sumcheckPath ++
    friOpeningGadgets hashSpec wiring

/-- Statement-first meaning of the complete recursive verifier AIR. -/
def RecursiveHistoryVerifierAccepts
    (asg : Idx → F) (hashSpec : PermSpec F 2) (half : F)
    (wiring : RecursiveVerifierWiring Idx sumcheckRounds friRounds) : Prop :=
  SumcheckVerifierAccepts (asg wiring.sumcheckClaim)
      (asg wiring.sumcheckFinal)
      (fun i => asg (wiring.sumcheckG0 i))
      (fun i => asg (wiring.sumcheckG1 i))
      (fun i => asg (wiring.sumcheckChallenge i)) ∧
    FriQueryAccepts half (asg wiring.friFinal)
      (fun i => asg (wiring.friLo i))
      (fun i => asg (wiring.friHi i))
      (fun i => asg (wiring.friNext i))
      (fun i => asg (wiring.friChallenge i))
      (fun i => asg (wiring.friTwiddle i))
      (fun i => asg (wiring.friTwoX i)) ∧
    MerkleOpeningAccepts asg hashSpec wiring.sumcheckFinal
      wiring.sumcheckRoot wiring.sumcheckPath ∧
    ∀ round, FriRoundOpeningsAccept asg hashSpec wiring round

theorem friRoundOpeningGadget_correct
    (asg : Idx → F) (spec : PermSpec F 2)
    (wiring : RecursiveVerifierWiring Idx sumcheckRounds friRounds)
    (round : Fin friRounds) :
    systemAccepts asg (friRoundOpeningGadget spec wiring round) ↔
      FriRoundOpeningsAccept asg spec wiring round := by
  unfold friRoundOpeningGadget FriRoundOpeningsAccept MerkleOpeningAccepts
  rw [systemAccepts_append, systemAccepts_append,
    membership_correct, membership_correct, membership_correct]

/-- A list of per-round constraint systems accepts exactly when every round's
system accepts. -/
theorem systemAccepts_flatMap_finRange
    (asg : Idx → F) (gadget : Fin friRounds → ConstraintSystem F Idx) :
    systemAccepts asg ((List.finRange friRounds).flatMap gadget) ↔
      ∀ round, systemAccepts asg (gadget round) := by
  unfold systemAccepts
  constructor
  · intro accepted round term termMem
    exact accepted term (List.mem_flatMap.mpr
      ⟨round, List.mem_finRange round, termMem⟩)
  · intro accepted term termMem
    obtain ⟨round, roundMem, termMem⟩ := List.mem_flatMap.mp termMem
    exact accepted round term termMem

theorem friOpeningGadgets_correct
    (asg : Idx → F) (spec : PermSpec F 2)
    (wiring : RecursiveVerifierWiring Idx sumcheckRounds friRounds) :
    systemAccepts asg (friOpeningGadgets spec wiring) ↔
      ∀ round, FriRoundOpeningsAccept asg spec wiring round := by
  rw [friOpeningGadgets, systemAccepts_flatMap_finRange]
  exact forall_congr' fun round =>
    friRoundOpeningGadget_correct asg spec wiring round

/-- Keystone: the emitted recursive verifier system accepts iff the existing
sumcheck, FRI, and every exact Merkle-opening meaning all hold. -/
theorem recursiveHistoryVerifier_correct
    (asg : Idx → F) (hashSpec : PermSpec F 2) (half : F)
    (wiring : RecursiveVerifierWiring Idx sumcheckRounds friRounds) :
    systemAccepts asg (recursiveHistoryVerifierGadget hashSpec half wiring) ↔
      RecursiveHistoryVerifierAccepts asg hashSpec half wiring := by
  unfold recursiveHistoryVerifierGadget RecursiveHistoryVerifierAccepts
  rw [systemAccepts_append, systemAccepts_append, systemAccepts_append,
    sumcheckVerifier_correct, friQueryVerifier_correct, membership_correct,
    friOpeningGadgets_correct]
  rfl

/-! ## Typed semantic-history receipt for the recursive AIR -/

section Receipt

variable [DecidableEq F]
variable {n : Nat}
variable
    {Op : Type uOp}
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

/-- An accepted recursive AIR instance bound to one exact arbitrary-depth
semantic history head.  This object deliberately stores AIR acceptance, not a
cryptographic recursive-proof theorem. -/
structure RecursiveHistoryAirReceipt
    (encodeDigest : Digest → F)
    (statement : StatelessHistoryStatement F)
    (head : HistoryHead)
    (hashSpec : PermSpec F 2) (half : F)
    (wiring : RecursiveVerifierWiring Idx sumcheckRounds friRounds) where
  realizes : statement.Realizes encodeDigest head
  assignment : Idx → F
  initialFriRootExact :
    assignment (wiring.friRoot 0) = statement.accumulatorRoot
  accepted : systemAccepts assignment
    (recursiveHistoryVerifierGadget hashSpec half wiring)

namespace RecursiveHistoryAirReceipt

variable {encodeDigest : Digest → F}
variable {statement : StatelessHistoryStatement F}
variable {head : HistoryHead}
variable {hashSpec : PermSpec F 2} {half : F}
variable {wiring : RecursiveVerifierWiring Idx sumcheckRounds friRounds}

/-- The level-zero FRI root wire is exactly the encoding of the authoritative
semantic accumulator root. -/
theorem initial_fri_root_is_semantic_head
    (receipt : RecursiveHistoryAirReceipt encodeDigest statement head
      hashSpec half wiring) :
    receipt.assignment (wiring.friRoot 0) =
      encodeDigest head.accumulator.rt := by
  rw [receipt.initialFriRootExact, receipt.realizes.accumulatorRootExact]

/-- An accepted typed receipt exposes all deterministic component meanings.
No security property is inferred. -/
theorem component_acceptance
    (receipt : RecursiveHistoryAirReceipt encodeDigest statement head
      hashSpec half wiring) :
    RecursiveHistoryVerifierAccepts receipt.assignment hashSpec half wiring :=
  (recursiveHistoryVerifier_correct receipt.assignment hashSpec half wiring).mp
    receipt.accepted

end RecursiveHistoryAirReceipt

end Receipt

/-! ## Security notions remain separate -/

/-- Evidence for four genuinely different recursive-argument properties.
The proposition parameters are supplied by a concrete protocol/game.  Keeping
four fields prevents an AIR-correctness theorem, ordinary soundness theorem,
or knowledge extractor from being silently reported as ZK or SE. -/
structure SecurityEvidence
    (OrdinarySoundness KnowledgeSoundness ZeroKnowledge
      SimulationExtractability : Prop) : Prop where
  ordinarySoundness : OrdinarySoundness
  knowledgeSoundness : KnowledgeSoundness
  zeroKnowledge : ZeroKnowledge
  simulationExtractability : SimulationExtractability

theorem SecurityEvidence.no_conflation
    {OrdinarySoundness KnowledgeSoundness ZeroKnowledge
      SimulationExtractability : Prop}
    (evidence : SecurityEvidence OrdinarySoundness KnowledgeSoundness
      ZeroKnowledge SimulationExtractability) :
    OrdinarySoundness ∧ KnowledgeSoundness ∧ ZeroKnowledge ∧
      SimulationExtractability :=
  ⟨evidence.ordinarySoundness, evidence.knowledgeSoundness,
    evidence.zeroKnowledge, evidence.simulationExtractability⟩

#print axioms StatelessHistoryStatement.ofHead_realizes
#print axioms recursiveHistoryVerifier_correct
#print axioms RecursiveHistoryAirReceipt.initial_fri_root_is_semantic_head
#print axioms RecursiveHistoryAirReceipt.component_acceptance

end

end Minidregg.Assurance.SemanticHistoryRecursiveAir
