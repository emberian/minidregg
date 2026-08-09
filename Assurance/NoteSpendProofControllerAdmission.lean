/-
# Assurance.NoteSpendProofControllerAdmission -- common-game note-spend admission

This module joins the sealed note-spend `AcceptedCellEffect` to the Lean-owned
bytes/error controller.  Its canonical controller statement is derived from
the already-authorized computation token: complete arguments, effects,
pre-root, public nullifier/root, committed output, and the literal emitted
relation descriptor are one statement.

The controller's deterministic acceptance remains separate from cryptographic
meaning.  PCS soundness, commitment collision resistance, random-oracle
transport, proof of knowledge, and hiding are distinct events and prices on
one finite game coin.  Relation satisfaction alone proves neither knowledge
nor hiding.
-/
import Assurance.NoteSpendCoreAcceptedCellEffect
import Assurance.ProofCompositionGame
import Compiler.NoteSpendProofController

namespace Minidregg.Assurance.NoteSpendProofControllerAdmission

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Compiler
open Minidregg.Compiler.NoteSpendProofController
open Minidregg.Loom
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

namespace CoreJoin

open Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect

set_option autoImplicit false

noncomputable section

/-! ## Canonical statement from the sole authorized computation -/

/-- No caller authors controller statement bytes.  Every field is projected
from the exact common request or its release-free note-spend request. -/
def statementOf
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    NoteSpendProofController.Statement :=
  let _acceptedOwner := accepted
  canonicalStatement commonRequest.argsDigest commonRequest.effectsDigest
    commonRequest.preStateRoot request.inputValue.nullifier
    request.inputValue.root request.outputCommitment

/-- The canonical statement inherits every load-bearing kernel/relation
binding from the accepted computation token. -/
theorem statementOf_exact
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    (statementOf accepted).argsDigest = adapter.completeRequestDigest request ∧
    (statementOf accepted).effectsDigest = adapter.completeEffectDigest request ∧
    (statementOf accepted).preRoot = pre.root ∧
    accepted.computation.cellEffect.prepared.nullifier =
      some (statementOf accepted).nullifier ∧
    (statementOf accepted).nullifier =
      accepted.computation.cellEffect.modeEvidence.computation.witness.assignment
        SWire.nullifierW ∧
    (statementOf accepted).root =
      accepted.computation.cellEffect.modeEvidence.computation.witness.assignment
        SWire.rootW ∧
    (statementOf accepted).outputCommitment =
      accepted.computation.cellEffect.modeEvidence.computation.witness.assignment
        SWire.commitW ∧
    (statementOf accepted).relationId = NoteSpendProofController.relationId ∧
    (statementOf accepted).relationDescriptor = exactRelationDescriptor ∧
    accepted.computation.cellEffect.disclosure = .sealed := by
  have kernel := accepted_kernel_bindings accepted
  have relation := accepted_relation accepted
  exact ⟨kernel.1, kernel.2.1, kernel.2.2.1,
    kernel.2.2.2.2.1,
    relation.2.2.2.2.1, relation.2.2.2.2.2.1,
    relation.2.2.2.2.2.2.2.1, rfl, rfl, kernel.2.2.2.2.2⟩

/-- Execute arbitrary proof-producing code only at the bytes/error boundary.
Acceptance is produced by `NoteSpendProofController.run`, never supplied by
the caller or inherited from the prior relation token. -/
def run
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result)
    {Error : Type} (runner : OpaqueProofRunner Error) :
    Except (Failure Error) (AcceptedReceipt (statementOf accepted)) :=
  NoteSpendProofController.run (statementOf accepted) runner

end

end CoreJoin

set_option autoImplicit false

noncomputable section

/-! ## Exact emitted-relation witness -/

/-- The semantic object a real argument/PCS reduction must extract.  It binds
all eleven authored variables, including the commitment at wire 6, to one
total vector satisfying the literal CSE'd emitted descriptor. -/
structure RelationWitness (statement : Statement) where
  values : Fin 11 → Scalar
  total : Nat → Scalar
  variablesExact : ∀ i : Fin 11, total i.val = values i
  descriptorAccepted : descriptorHolds spendDescriptorShared total
  nullifierExact : values 0 = statement.nullifier
  rootExact : values 1 = statement.root
  outputCommitmentExact : values 6 = statement.outputCommitment

theorem RelationWitness.airAccepts {statement : Statement}
    (witness : RelationWitness statement) :
    Minidregg.Compiler.systemAccepts witness.values spendSystem :=
  (cse_emit_accepts_iff_fin 11 2 witness.values spendSystem).mp
    ⟨witness.total, witness.variablesExact, witness.descriptorAccepted⟩

/-- The emitted descriptor bridge closes back to the existing note-spend
meaning theorem.  This remains an arithmetic spend statement only. -/
theorem RelationWitness.validSpend {statement : Statement}
    (witness : RelationWitness statement) :
    ValidSpend demoNfSpec demoSpec demoSpec 0 2 2
      statement.nullifier statement.root
      (fun i : Fin 2 =>
        witness.values ⟨2 + i.val, by have := i.isLt; omega⟩) := by
  have accepted : Minidregg.Compiler.systemAccepts witness.values
      (noteSpendSystem demoNfSpec demoSpec demoSpec
        (fun i : Fin 2 =>
          (⟨2 + i.val, by have := i.isLt; omega⟩ : Fin 11)) 0
        (fun i : Fin 2 =>
          (⟨4 + i.val, by have := i.isLt; omega⟩ : Fin 11))
        0 6 1 [(7, 9), (8, 10)]) := by
    simpa only [spendSystem] using witness.airAccepts
  have valid := noteSpend_binds witness.values demoNfSpec demoSpec demoSpec
    (fun i : Fin 2 =>
      (⟨2 + i.val, by have := i.isLt; omega⟩ : Fin 11)) 0
    (fun i : Fin 2 =>
      (⟨4 + i.val, by have := i.isLt; omega⟩ : Fin 11))
    0 6 1 [(7, 9), (8, 10)] accepted
  simpa only [List.length_cons, List.length_nil, Nat.reduceAdd,
    witness.nullifierExact, witness.rootExact] using valid

/-! ## Separately priced same-coin premises -/

/-- These are not synonyms.  Each tag names one real deployment theorem that
must be supplied on the same game coin. -/
inductive FailureClass
  | pcsSoundness
  | collisionResistance
  | randomOracle
  | proofOfKnowledge
  | zeroKnowledgeHiding
deriving DecidableEq, Fintype, Repr

abbrev FailureLedger (Omega : Type) [Fintype Omega] :=
  FailureClass → PricedFailure Omega

namespace FailureLedger

variable {Omega : Type} [Fintype Omega]

def Good (ledger : FailureLedger Omega) (failure : FailureClass)
    (omega : Omega) : Prop :=
  ¬(ledger failure).event omega

def SoundnessBad (ledger : FailureLedger Omega) (omega : Omega) : Prop :=
  (ledger .pcsSoundness).event omega ∨
  (ledger .collisionResistance).event omega ∨
  (ledger .randomOracle).event omega ∨
  (ledger .proofOfKnowledge).event omega

def soundnessPrice (ledger : FailureLedger Omega) : Real :=
  (ledger .pcsSoundness).price +
  (ledger .collisionResistance).price +
  (ledger .randomOracle).price +
  (ledger .proofOfKnowledge).price

def privacyPrice (ledger : FailureLedger Omega) : Real :=
  (ledger .zeroKnowledgeHiding).price

def totalPrice (ledger : FailureLedger Omega) : Real :=
  ledger.soundnessPrice + ledger.privacyPrice

theorem good_of_not_soundnessBad (ledger : FailureLedger Omega)
    {omega : Omega} (good : ¬ledger.SoundnessBad omega)
    (failure : FailureClass)
    (soundnessFailure : failure ≠ .zeroKnowledgeHiding) :
    ledger.Good failure omega := by
  intro bad
  cases failure with
  | pcsSoundness => exact good (Or.inl bad)
  | collisionResistance => exact good (Or.inr (Or.inl bad))
  | randomOracle => exact good (Or.inr (Or.inr (Or.inl bad)))
  | proofOfKnowledge => exact good (Or.inr (Or.inr (Or.inr bad)))
  | zeroKnowledgeHiding => exact (soundnessFailure rfl).elim

theorem soundnessBad_le (ledger : FailureLedger Omega) :
    uniformProb Omega ledger.SoundnessBad ≤ ledger.soundnessPrice := by
  have h1 := uniformProb_or_le (ledger .pcsSoundness).event (fun omega =>
    (ledger .collisionResistance).event omega ∨
    (ledger .randomOracle).event omega ∨
    (ledger .proofOfKnowledge).event omega)
  have h2 := uniformProb_or_le (ledger .collisionResistance).event (fun omega =>
    (ledger .randomOracle).event omega ∨
    (ledger .proofOfKnowledge).event omega)
  have h3 := uniformProb_or_le (ledger .randomOracle).event
    (ledger .proofOfKnowledge).event
  unfold SoundnessBad soundnessPrice
  linarith [(ledger .pcsSoundness).bound,
    (ledger .collisionResistance).bound,
    (ledger .randomOracle).bound,
    (ledger .proofOfKnowledge).bound]

end FailureLedger

/-! ## Common-game reduction and execution -/

/-- Exact deployment obligations.  Hiding is intentionally a different field
from extraction: relation satisfaction and PoK do not imply it. -/
structure ReductionLaws (Omega : Type) [Fintype Omega]
    (ledger : FailureLedger Omega) (statement : Statement) where
  HidingClaim : Receipt → Prop
  extract : ∀ omega receipt,
    Accepts statement receipt →
    ledger.Good .pcsSoundness omega →
    ledger.Good .collisionResistance omega →
    ledger.Good .randomOracle omega →
    ledger.Good .proofOfKnowledge omega →
    RelationWitness statement
  hidingLaw : ∀ omega receipt,
    Accepts statement receipt →
    ledger.Good .zeroKnowledgeHiding omega →
    HidingClaim receipt

/-- One finite coin selects runner behavior and every security event.  Native
error, decode failure, and Lean rejection are represented by `execution = none`.
No independence premise occurs. -/
structure CommonGameFamily
    (Omega : Type) [Fintype Omega] (Error : Type) (statement : Statement) where
  ledger : FailureLedger Omega
  laws : ReductionLaws Omega ledger statement
  runner : Omega → OpaqueProofRunner Error
  execution : Omega → Option (AcceptedReceipt statement)
  executionExact : ∀ omega reply, execution omega = some reply →
    NoteSpendProofController.run statement (runner omega) = .ok reply

namespace CommonGameFamily

variable {Omega : Type} [Fintype Omega]
variable {Error : Type} {statement : Statement}

/-- False relation acceptance: controller bytes accepted although no witness
can satisfy the exact statement-bound emitted descriptor. -/
def FalseAccept (family : CommonGameFamily Omega Error statement)
    (omega : Omega) : Prop :=
  ∃ reply, family.execution omega = some reply ∧
    ¬Nonempty (RelationWitness statement)

/-- Privacy failure is priced independently from soundness/extraction failure. -/
def HidingFailure (family : CommonGameFamily Omega Error statement)
    (omega : Omega) : Prop :=
  ∃ reply, family.execution omega = some reply ∧
    ¬family.laws.HidingClaim reply.receipt

theorem execution_runner_bytes
    (family : CommonGameFamily Omega Error statement)
    {omega : Omega} {reply : AcceptedReceipt statement}
    (selected : family.execution omega = some reply) :
    family.runner omega (statementCodec.encode statement) =
      .ok reply.proofBytes :=
  (run_success_integrity statement (family.runner omega) reply
    (family.executionExact omega reply selected)).1

theorem falseAccept_soundnessBad
    (family : CommonGameFamily Omega Error statement)
    (omega : Omega) (accepted : family.FalseAccept omega) :
    family.ledger.SoundnessBad omega := by
  by_contra good
  obtain ⟨reply, selected, falseRelation⟩ := accepted
  have pcs := family.ledger.good_of_not_soundnessBad good .pcsSoundness (by decide)
  have cr := family.ledger.good_of_not_soundnessBad good .collisionResistance (by decide)
  have rom := family.ledger.good_of_not_soundnessBad good .randomOracle (by decide)
  have pok := family.ledger.good_of_not_soundnessBad good .proofOfKnowledge (by decide)
  exact falseRelation ⟨family.laws.extract omega reply.receipt reply.accepted
    pcs cr rom pok⟩

theorem falseAccept_le
    (family : CommonGameFamily Omega Error statement) :
    uniformProb Omega family.FalseAccept ≤ family.ledger.soundnessPrice :=
  le_trans (uniformProb_mono family.falseAccept_soundnessBad)
    family.ledger.soundnessBad_le

theorem hidingFailure_event
    (family : CommonGameFamily Omega Error statement)
    (omega : Omega) (failure : family.HidingFailure omega) :
    (family.ledger .zeroKnowledgeHiding).event omega := by
  by_contra good
  obtain ⟨reply, selected, notHiding⟩ := failure
  exact notHiding (family.laws.hidingLaw omega reply.receipt reply.accepted good)

theorem hidingFailure_le
    (family : CommonGameFamily Omega Error statement) :
    uniformProb Omega family.HidingFailure ≤ family.ledger.privacyPrice :=
  le_trans (uniformProb_mono family.hidingFailure_event)
    (family.ledger .zeroKnowledgeHiding).bound

/-- Outside the four soundness failures, an accepted controller receipt yields
the emitted relation witness and hence the exact `ValidSpend`.  Hiding is not
part of this conclusion. -/
theorem validSpend_of_not_soundnessBad
    (family : CommonGameFamily Omega Error statement)
    {omega : Omega} {reply : AcceptedReceipt statement}
    (selected : family.execution omega = some reply)
    (good : ¬family.ledger.SoundnessBad omega) :
    ∃ witness : RelationWitness statement,
      ValidSpend demoNfSpec demoSpec demoSpec 0 2 2
        statement.nullifier statement.root
        (fun i : Fin 2 =>
          witness.values ⟨2 + i.val, by have := i.isLt; omega⟩) := by
  have pcs := family.ledger.good_of_not_soundnessBad good .pcsSoundness (by decide)
  have cr := family.ledger.good_of_not_soundnessBad good .collisionResistance (by decide)
  have rom := family.ledger.good_of_not_soundnessBad good .randomOracle (by decide)
  have pok := family.ledger.good_of_not_soundnessBad good .proofOfKnowledge (by decide)
  have _runnerBytes := family.execution_runner_bytes selected
  let witness := family.laws.extract omega reply.receipt reply.accepted pcs cr rom pok
  exact ⟨witness, witness.validSpend⟩

end CommonGameFamily

#print axioms CoreJoin.statementOf_exact
#print axioms RelationWitness.validSpend
#print axioms FailureLedger.soundnessBad_le
#print axioms CommonGameFamily.falseAccept_le
#print axioms CommonGameFamily.hidingFailure_le
#print axioms CommonGameFamily.validSpend_of_not_soundnessBad

end

end Minidregg.Assurance.NoteSpendProofControllerAdmission
