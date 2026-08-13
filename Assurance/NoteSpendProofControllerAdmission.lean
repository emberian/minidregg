/-
# Assurance.NoteSpendProofControllerAdmission -- honest note-spend admission

This module joins the sealed note-spend `AcceptedCellEffect` to the Lean-owned
bytes/error controller, while separating three different claims:

* deterministic control-envelope and reflected-suite acceptance;
* semantic `ValidSpend` admission under same-coin arithmetic, PCS,
  collision-resistance, random-oracle, and proof-of-knowledge laws; and
* optional hiding under a separate same-coin privacy law.

The current accepted request owns a zero proof-suite pin.  It can therefore
produce neither a bound reflected suite nor semantic admission.  Reaching a
deployed path requires the nonzero suite identity to enter the authorized
request and hence the canonical statement bytes.  This release-free family
remains sealed and exposes no release value.
-/
import Assurance.NoteSpendCoreAcceptedCellEffect
import Assurance.ProofCompositionGame
import Compiler.NoteSpendProofController

namespace Minidregg.Assurance.NoteSpendProofControllerAdmission

open Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect
open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Compiler
open Minidregg.Compiler.NoteSpendProofController
open Minidregg.Selvage
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

namespace CoreJoin

/-! ## Canonical statement from the sole authorized computation -/

/-- No caller authors controller statement bytes or a proof-suite pin.  Every
field is projected from the exact common request or its release-free
note-spend request. -/
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
    request.modeEvidencePins.proofSuiteId

/-- The canonical statement inherits every load-bearing kernel/relation
binding and the still-unassigned suite pin from the accepted computation. -/
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
    (statementOf accepted).proofSuiteId =
      request.modeEvidencePins.proofSuiteId ∧
    request.modeEvidencePins.proofSuiteId = ⟨0⟩ ∧
    accepted.computation.cellEffect.disclosure = .sealed := by
  have kernel := accepted_kernel_bindings accepted
  have relation := accepted_relation accepted
  have suiteZero : request.modeEvidencePins.proofSuiteId = ⟨0⟩ := by
    rw [relation.2.2.1]
    rfl
  exact ⟨kernel.1, kernel.2.1, kernel.2.2.1,
    kernel.2.2.2.2.1,
    relation.2.2.2.2.1, relation.2.2.2.2.2.1,
    relation.2.2.2.2.2.2.2.1, rfl, rfl, rfl, suiteZero,
    kernel.2.2.2.2.2⟩

/-- The accepted note-spend request is deliberately undeployed: its exact
statement cannot bind a suite whose identity is assigned. -/
theorem statementOf_no_boundReflectedSuite
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    ¬Nonempty (BoundReflectedSuite (statementOf accepted)) := by
  rintro ⟨bound⟩
  rcases statementOf_exact accepted with
    ⟨-, -, -, -, -, -, -, -, -, statementSuite, suiteZero, -⟩
  exact bound.suite.proofSuiteAssigned (by
    calc
      bound.suite.proofSuiteId = (statementOf accepted).proofSuiteId :=
        bound.proofSuiteBound.symm
      _ = request.modeEvidencePins.proofSuiteId := statementSuite
      _ = ⟨0⟩ := suiteZero)

/-! ## Control/reflection remains explicitly weak -/

inductive AdmissionFailure (Error : Type)
  | control (failure : Failure Error)
  | rejectedSuite
deriving Repr

/-- A reflected receipt carries decoding, framing, and one suite predicate.
It carries no arithmetic, PCS, PoK, or hiding reduction law. -/
structure ReflectedReceipt (statement : NoteSpendProofController.Statement)
    (bound : BoundReflectedSuite statement) where
  controlled : ControlledReceipt statement
  suiteAccepted : bound.suite.ReflectedAccepts statement controlled.receipt

/-- Lean runs the fixed decoder/control checker first and the supplied suite
checker second.  No caller provides an acceptance proposition. -/
def runReflected {Error : Type} (statement : NoteSpendProofController.Statement)
    (bound : BoundReflectedSuite statement) (runner : OpaqueProofRunner Error) :
    Except (AdmissionFailure Error) (ReflectedReceipt statement bound) :=
  match NoteSpendProofController.run statement runner with
  | .error failure => .error (.control failure)
  | .ok controlled =>
      if checked : bound.suite.check statement controlled.receipt = true then
        .ok ⟨controlled,
          (bound.suite.check_iff statement controlled.receipt).mp checked⟩
      else
        .error .rejectedSuite

/-- The core-specific weak runner always sends the exact accepted statement. -/
def runAcceptedReflected
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result)
    {Error : Type} (bound : BoundReflectedSuite (statementOf accepted))
    (runner : OpaqueProofRunner Error) :
    Except (AdmissionFailure Error)
      (ReflectedReceipt (statementOf accepted) bound) :=
  runReflected (statementOf accepted) bound runner

theorem runReflected_success_integrity {Error : Type}
    (statement : NoteSpendProofController.Statement)
    (bound : BoundReflectedSuite statement) (runner : OpaqueProofRunner Error)
    (reply : ReflectedReceipt statement bound)
    (success : runReflected statement bound runner = .ok reply) :
    runner (statementCodec.encode statement) = .ok reply.controlled.proofBytes ∧
    receiptCodec.decode reply.controlled.proofBytes =
      some reply.controlled.receipt ∧
    ControlAccepts statement reply.controlled.receipt ∧
    bound.suite.ReflectedAccepts statement reply.controlled.receipt := by
  unfold runReflected at success
  split at success
  next failure failed => simp at success
  next controlled controlledRun =>
    split at success
    next checked =>
      simp only [Except.ok.injEq] at success
      subst reply
      have integrity := NoteSpendProofController.run_success_integrity
        statement runner controlled controlledRun
      exact ⟨integrity.1, integrity.2.1, integrity.2.2,
        (bound.suite.check_iff statement controlled.receipt).mp checked⟩
    next rejected => simp at success

end CoreJoin

/-! ## Exact emitted-relation witness -/

/-- The semantic object a real argument/PCS reduction must extract.  It binds
all eleven authored variables, including the commitment at wire 6, to one
total vector satisfying the literal CSE'd emitted descriptor. -/
structure RelationWitness (statement : NoteSpendProofController.Statement) where
  values : Fin 11 → NoteSpendProofController.Scalar
  total : Nat → NoteSpendProofController.Scalar
  variablesExact : ∀ i : Fin 11, total i.val = values i
  descriptorAccepted : descriptorHolds spendDescriptorShared total
  nullifierExact : values 0 = statement.nullifier
  rootExact : values 1 = statement.root
  outputCommitmentExact : values 6 = statement.outputCommitment

theorem RelationWitness.airAccepts
    {statement : NoteSpendProofController.Statement}
    (witness : RelationWitness statement) :
    Minidregg.Compiler.systemAccepts witness.values spendSystem :=
  (cse_emit_accepts_iff_fin 11 2 witness.values spendSystem).mp
    ⟨witness.total, witness.variablesExact, witness.descriptorAccepted⟩

/-- The emitted descriptor bridge closes back to the existing note-spend
meaning theorem.  This remains an arithmetic spend statement only. -/
theorem RelationWitness.validSpend
    {statement : NoteSpendProofController.Statement}
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

/-- Each tag names one real deployment theorem.  Arithmetic satisfaction is
not silently renamed as PCS soundness or proof of knowledge, and hiding is a
separate privacy event. -/
inductive FailureClass
  | arithmeticSoundness
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
  (ledger .arithmeticSoundness).event omega ∨
  (ledger .pcsSoundness).event omega ∨
  (ledger .collisionResistance).event omega ∨
  (ledger .randomOracle).event omega ∨
  (ledger .proofOfKnowledge).event omega

def soundnessPrice (ledger : FailureLedger Omega) : Real :=
  (ledger .arithmeticSoundness).price +
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
  | arithmeticSoundness => exact good (Or.inl bad)
  | pcsSoundness => exact good (Or.inr (Or.inl bad))
  | collisionResistance => exact good (Or.inr (Or.inr (Or.inl bad)))
  | randomOracle => exact good (Or.inr (Or.inr (Or.inr (Or.inl bad))))
  | proofOfKnowledge => exact good (Or.inr (Or.inr (Or.inr (Or.inr bad))))
  | zeroKnowledgeHiding => exact (soundnessFailure rfl).elim

theorem soundnessBad_le (ledger : FailureLedger Omega) :
    uniformProb Omega ledger.SoundnessBad ≤ ledger.soundnessPrice := by
  have h1 := uniformProb_or_le (ledger .arithmeticSoundness).event (fun omega =>
    (ledger .pcsSoundness).event omega ∨
    (ledger .collisionResistance).event omega ∨
    (ledger .randomOracle).event omega ∨
    (ledger .proofOfKnowledge).event omega)
  have h2 := uniformProb_or_le (ledger .pcsSoundness).event (fun omega =>
    (ledger .collisionResistance).event omega ∨
    (ledger .randomOracle).event omega ∨
    (ledger .proofOfKnowledge).event omega)
  have h3 := uniformProb_or_le (ledger .collisionResistance).event (fun omega =>
    (ledger .randomOracle).event omega ∨
    (ledger .proofOfKnowledge).event omega)
  have h4 := uniformProb_or_le (ledger .randomOracle).event
    (ledger .proofOfKnowledge).event
  unfold SoundnessBad soundnessPrice
  linarith [(ledger .arithmeticSoundness).bound,
    (ledger .pcsSoundness).bound,
    (ledger .collisionResistance).bound,
    (ledger .randomOracle).bound,
    (ledger .proofOfKnowledge).bound]

end FailureLedger

/-! ## Soundness and privacy laws are different objects -/

/-- Exact same-coin soundness obligations for semantic note-spend admission.
This structure assigns no suite identity and proves no cryptographic law. -/
structure SameCoinReductionLaws
    {Omega : Type} [Fintype Omega] (ledger : FailureLedger Omega)
    {statement : NoteSpendProofController.Statement}
    (bound : BoundReflectedSuite statement) where
  extract : ∀ omega receipt,
    ControlAccepts statement receipt →
    bound.suite.ReflectedAccepts statement receipt →
    ledger.Good .arithmeticSoundness omega →
    ledger.Good .pcsSoundness omega →
    ledger.Good .collisionResistance omega →
    ledger.Good .randomOracle omega →
    ledger.Good .proofOfKnowledge omega →
    RelationWitness statement

/-- Hiding is optional and required only by a privacy theorem.  Relation
satisfaction and proof of knowledge do not manufacture this object. -/
structure SameCoinHidingLaws
    {Omega : Type} [Fintype Omega] (ledger : FailureLedger Omega)
    {statement : NoteSpendProofController.Statement}
    (bound : BoundReflectedSuite statement) where
  HidingClaim : Receipt → Prop
  proveHiding : ∀ omega receipt,
    ControlAccepts statement receipt →
    bound.suite.ReflectedAccepts statement receipt →
    ledger.Good .zeroKnowledgeHiding omega →
    HidingClaim receipt

/-! ## Semantic admission: exact spend on one good soundness coin -/

namespace CoreJoin

/-- A semantic receipt is indexed by the exact accepted sealed computation,
the exact nonzero suite binding, the five soundness reductions, and one coin
outside their union.  Hiding is intentionally absent. -/
structure AdmittedReceipt
    {Omega : Type} [Fintype Omega]
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result)
    (bound : BoundReflectedSuite (statementOf accepted))
    (ledger : FailureLedger Omega)
    (laws : SameCoinReductionLaws ledger bound)
    (omega : Omega) where
  reflected : ReflectedReceipt (statementOf accepted) bound
  outsideSoundnessFailures : ¬ledger.SoundnessBad omega

namespace AdmittedReceipt

variable {Omega : Type} [Fintype Omega]
variable {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
variable {M : CellState.Materializer S Digest}
variable {adapter : ComputationCellEffect.Adapter (S := S) declaration}
variable {portal : Portal} {authState : AuthState} {kind : ResourceKind}
variable {commonRequest : Request kind} {pre : CellState.Materialized M}
variable {request : CoreRequest} {result : CoreResult}
variable {accepted : Accepted (portal := portal) (authState := authState)
  adapter commonRequest pre request result}
variable {bound : BoundReflectedSuite (statementOf accepted)}
variable {ledger : FailureLedger Omega}
variable {laws : SameCoinReductionLaws ledger bound}
variable {omega : Omega}

/-- The relation witness is derived from suite acceptance and the five good
events; it is not a caller-authored receipt field. -/
noncomputable def witness
    (admitted : AdmittedReceipt accepted bound ledger laws omega) :
    RelationWitness (statementOf accepted) :=
  laws.extract omega admitted.reflected.controlled.receipt
    admitted.reflected.controlled.controlled admitted.reflected.suiteAccepted
    (ledger.good_of_not_soundnessBad admitted.outsideSoundnessFailures
      .arithmeticSoundness (by decide))
    (ledger.good_of_not_soundnessBad admitted.outsideSoundnessFailures
      .pcsSoundness (by decide))
    (ledger.good_of_not_soundnessBad admitted.outsideSoundnessFailures
      .collisionResistance (by decide))
    (ledger.good_of_not_soundnessBad admitted.outsideSoundnessFailures
      .randomOracle (by decide))
    (ledger.good_of_not_soundnessBad admitted.outsideSoundnessFailures
      .proofOfKnowledge (by decide))

theorem validSpend
    (admitted : AdmittedReceipt accepted bound ledger laws omega) :
    ValidSpend demoNfSpec demoSpec demoSpec 0 2 2
      (statementOf accepted).nullifier (statementOf accepted).root
      (fun i : Fin 2 =>
        admitted.witness.values ⟨2 + i.val, by have := i.isLt; omega⟩) :=
  admitted.witness.validSpend

/-- Semantic note-spend admission preserves the source kernel's sealed,
release-free disclosure state. -/
theorem source_sealed
    (_admitted : AdmittedReceipt accepted bound ledger laws omega) :
    accepted.computation.cellEffect.disclosure = .sealed :=
  (accepted_kernel_bindings accepted).2.2.2.2.2

end AdmittedReceipt

/-- The canonical semantic runner requires the exact suite binding, all five
same-coin soundness laws, and a proof that the selected coin is good. -/
def run
    {Omega : Type} [Fintype Omega]
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result)
    (bound : BoundReflectedSuite (statementOf accepted))
    (ledger : FailureLedger Omega)
    (laws : SameCoinReductionLaws ledger bound)
    (omega : Omega) (outsideSoundnessFailures : ¬ledger.SoundnessBad omega)
    {Error : Type} (runner : OpaqueProofRunner Error) :
    Except (AdmissionFailure Error)
      (AdmittedReceipt accepted bound ledger laws omega) :=
  match runReflected (statementOf accepted) bound runner with
  | .error failure => .error failure
  | .ok reflected => .ok ⟨reflected, outsideSoundnessFailures⟩

theorem run_success_integrity
    {Omega : Type} [Fintype Omega]
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result)
    (bound : BoundReflectedSuite (statementOf accepted))
    (ledger : FailureLedger Omega)
    (laws : SameCoinReductionLaws ledger bound)
    (omega : Omega) (outsideSoundnessFailures : ¬ledger.SoundnessBad omega)
    {Error : Type} (runner : OpaqueProofRunner Error)
    (reply : AdmittedReceipt accepted bound ledger laws omega)
    (success : run accepted bound ledger laws omega outsideSoundnessFailures
      runner = .ok reply) :
    runner (statementCodec.encode (statementOf accepted)) =
        .ok reply.reflected.controlled.proofBytes ∧
    receiptCodec.decode reply.reflected.controlled.proofBytes =
        some reply.reflected.controlled.receipt ∧
    ControlAccepts (statementOf accepted) reply.reflected.controlled.receipt ∧
    bound.suite.ReflectedAccepts (statementOf accepted)
        reply.reflected.controlled.receipt ∧
    ValidSpend demoNfSpec demoSpec demoSpec 0 2 2
      (statementOf accepted).nullifier (statementOf accepted).root
      (fun i : Fin 2 =>
        reply.witness.values ⟨2 + i.val, by have := i.isLt; omega⟩) := by
  unfold run at success
  split at success
  next failed => simp at success
  next reflected reflectedRun =>
    simp only [Except.ok.injEq] at success
    subst reply
    have integrity := runReflected_success_integrity
      (statementOf accepted) bound runner reflected reflectedRun
    exact ⟨integrity.1, integrity.2.1, integrity.2.2.1,
      integrity.2.2.2, AdmittedReceipt.validSpend _⟩

end CoreJoin

/-! ## One common coin controls reflected execution and every event -/

structure CommonGameFamily
    (Omega : Type) [Fintype Omega] (Error : Type)
    {statement : NoteSpendProofController.Statement}
    (bound : BoundReflectedSuite statement) where
  ledger : FailureLedger Omega
  laws : SameCoinReductionLaws ledger bound
  runner : Omega → OpaqueProofRunner Error
  execution : Omega → Option (CoreJoin.ReflectedReceipt statement bound)
  executionExact : ∀ omega reply, execution omega = some reply →
    CoreJoin.runReflected statement bound (runner omega) = .ok reply

namespace CommonGameFamily

variable {Omega : Type} [Fintype Omega] {Error : Type}
variable {statement : NoteSpendProofController.Statement}
variable {bound : BoundReflectedSuite statement}

def FalseAccept (family : CommonGameFamily Omega Error bound)
    (omega : Omega) : Prop :=
  ∃ reply, family.execution omega = some reply ∧
    ¬Nonempty (RelationWitness statement)

theorem execution_runner_bytes
    (family : CommonGameFamily Omega Error bound)
    {omega : Omega} {reply : CoreJoin.ReflectedReceipt statement bound}
    (selected : family.execution omega = some reply) :
    family.runner omega (statementCodec.encode statement) =
      .ok reply.controlled.proofBytes :=
  (CoreJoin.runReflected_success_integrity statement bound (family.runner omega)
    reply (family.executionExact omega reply selected)).1

theorem falseAccept_soundnessBad
    (family : CommonGameFamily Omega Error bound)
    (omega : Omega) (accepted : family.FalseAccept omega) :
    family.ledger.SoundnessBad omega := by
  by_contra good
  obtain ⟨reply, selected, falseRelation⟩ := accepted
  have arithmetic := family.ledger.good_of_not_soundnessBad good
    .arithmeticSoundness (by decide)
  have pcs := family.ledger.good_of_not_soundnessBad good .pcsSoundness (by decide)
  have cr := family.ledger.good_of_not_soundnessBad good
    .collisionResistance (by decide)
  have rom := family.ledger.good_of_not_soundnessBad good .randomOracle (by decide)
  have pok := family.ledger.good_of_not_soundnessBad good .proofOfKnowledge (by decide)
  exact falseRelation ⟨family.laws.extract omega reply.controlled.receipt
    reply.controlled.controlled reply.suiteAccepted arithmetic pcs cr rom pok⟩

theorem falseAccept_le
    (family : CommonGameFamily Omega Error bound) :
    uniformProb Omega family.FalseAccept ≤ family.ledger.soundnessPrice :=
  le_trans (uniformProb_mono family.falseAccept_soundnessBad)
    family.ledger.soundnessBad_le

/-- Outside the five soundness failures, reflected acceptance yields the exact
emitted relation witness.  This generic result carries no hiding claim. -/
theorem witness_of_not_soundnessBad
    (family : CommonGameFamily Omega Error bound)
    {omega : Omega} {reply : CoreJoin.ReflectedReceipt statement bound}
    (selected : family.execution omega = some reply)
    (good : ¬family.ledger.SoundnessBad omega) :
    Nonempty (RelationWitness statement) := by
  have arithmetic := family.ledger.good_of_not_soundnessBad good
    .arithmeticSoundness (by decide)
  have pcs := family.ledger.good_of_not_soundnessBad good .pcsSoundness (by decide)
  have cr := family.ledger.good_of_not_soundnessBad good
    .collisionResistance (by decide)
  have rom := family.ledger.good_of_not_soundnessBad good .randomOracle (by decide)
  have pok := family.ledger.good_of_not_soundnessBad good .proofOfKnowledge (by decide)
  have _runnerBytes := family.execution_runner_bytes selected
  exact ⟨family.laws.extract omega reply.controlled.receipt
    reply.controlled.controlled reply.suiteAccepted arithmetic pcs cr rom pok⟩

/-! ### Optional privacy game -/

def HidingFailure (family : CommonGameFamily Omega Error bound)
    (privacy : SameCoinHidingLaws family.ledger bound)
    (omega : Omega) : Prop :=
  ∃ reply, family.execution omega = some reply ∧
    ¬privacy.HidingClaim reply.controlled.receipt

theorem hidingFailure_event
    (family : CommonGameFamily Omega Error bound)
    (privacy : SameCoinHidingLaws family.ledger bound)
    (omega : Omega) (failure : family.HidingFailure privacy omega) :
    (family.ledger .zeroKnowledgeHiding).event omega := by
  by_contra good
  obtain ⟨reply, selected, notHiding⟩ := failure
  exact notHiding (privacy.proveHiding omega reply.controlled.receipt
    reply.controlled.controlled reply.suiteAccepted good)

theorem hidingFailure_le
    (family : CommonGameFamily Omega Error bound)
    (privacy : SameCoinHidingLaws family.ledger bound) :
    uniformProb Omega (family.HidingFailure privacy) ≤
      family.ledger.privacyPrice :=
  le_trans (uniformProb_mono (family.hidingFailure_event privacy))
    (family.ledger .zeroKnowledgeHiding).bound

end CommonGameFamily

/-! ## Specialization back to the exact accepted sealed spend -/

namespace NoteSpendCommonGame

variable {Omega : Type} [Fintype Omega] {Error : Type}
variable {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
variable {M : CellState.Materializer S Digest}
variable {adapter : ComputationCellEffect.Adapter (S := S) declaration}
variable {portal : Portal} {authState : AuthState} {kind : ResourceKind}
variable {commonRequest : Request kind} {pre : CellState.Materialized M}
variable {request : CoreRequest} {result : CoreResult}
variable {accepted : Accepted (portal := portal) (authState := authState)
  adapter commonRequest pre request result}
variable {bound : BoundReflectedSuite (CoreJoin.statementOf accepted)}

/-- The current accepted request cannot package semantic spend admission: its
suite pin is zero.  Reduction laws supplied out of band cannot repair the
missing request/statement identity. -/
theorem no_current_semantic_deployment :
    ¬∃ bound : BoundReflectedSuite (CoreJoin.statementOf accepted),
      ∃ ledger : FailureLedger Omega,
        Nonempty (SameCoinReductionLaws ledger bound) := by
  rintro ⟨candidate, -, -⟩
  exact CoreJoin.statementOf_no_boundReflectedSuite accepted ⟨candidate⟩

/-- Semantic admission together with evidence that this exact reflected
receipt was selected by the common-game coin. -/
structure AdmittedExecution
    (family : CommonGameFamily Omega Error bound) (omega : Omega) where
  semantic : CoreJoin.AdmittedReceipt accepted bound family.ledger family.laws omega
  selected : family.execution omega = some semantic.reflected

noncomputable def admitted_of_not_soundnessBad
    (family : CommonGameFamily Omega Error bound)
    {omega : Omega}
    {reply : CoreJoin.ReflectedReceipt (CoreJoin.statementOf accepted) bound}
    (selected : family.execution omega = some reply)
    (good : ¬family.ledger.SoundnessBad omega) :
    AdmittedExecution family omega where
  semantic := {
    reflected := reply
    outsideSoundnessFailures := good }
  selected := selected

/-- Outside the exact five soundness failures, the exact accepted sealed
computation upgrades to semantic `ValidSpend`.  Hiding remains absent. -/
theorem validSpend_of_not_soundnessBad
    (family : CommonGameFamily Omega Error bound)
    {omega : Omega}
    {reply : CoreJoin.ReflectedReceipt (CoreJoin.statementOf accepted) bound}
    (selected : family.execution omega = some reply)
    (good : ¬family.ledger.SoundnessBad omega) :
    ∃ witness : RelationWitness (CoreJoin.statementOf accepted),
      ValidSpend demoNfSpec demoSpec demoSpec 0 2 2
        (CoreJoin.statementOf accepted).nullifier
        (CoreJoin.statementOf accepted).root
        (fun i : Fin 2 =>
          witness.values ⟨2 + i.val, by have := i.isLt; omega⟩) := by
  let execution := admitted_of_not_soundnessBad family selected good
  exact ⟨execution.semantic.witness, execution.semantic.validSpend⟩

theorem admitted_source_sealed
    (family : CommonGameFamily Omega Error bound)
    {omega : Omega}
    (execution : AdmittedExecution family omega) :
    accepted.computation.cellEffect.disclosure = .sealed :=
  execution.semantic.source_sealed

end NoteSpendCommonGame

/-- info: 'Minidregg.Assurance.NoteSpendProofControllerAdmission.CoreJoin.statementOf_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CoreJoin.statementOf_exact
/-- info: 'Minidregg.Assurance.NoteSpendProofControllerAdmission.CoreJoin.statementOf_no_boundReflectedSuite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CoreJoin.statementOf_no_boundReflectedSuite
/-- info: 'Minidregg.Assurance.NoteSpendProofControllerAdmission.CoreJoin.runReflected_success_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CoreJoin.runReflected_success_integrity
/-- info: 'Minidregg.Assurance.NoteSpendProofControllerAdmission.CoreJoin.run_success_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CoreJoin.run_success_integrity
/-- info: 'Minidregg.Assurance.NoteSpendProofControllerAdmission.RelationWitness.validSpend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RelationWitness.validSpend
/-- info: 'Minidregg.Assurance.NoteSpendProofControllerAdmission.FailureLedger.soundnessBad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FailureLedger.soundnessBad_le
/-- info: 'Minidregg.Assurance.NoteSpendProofControllerAdmission.CommonGameFamily.falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CommonGameFamily.falseAccept_le
/-- info: 'Minidregg.Assurance.NoteSpendProofControllerAdmission.CommonGameFamily.hidingFailure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CommonGameFamily.hidingFailure_le
/-- info: 'Minidregg.Assurance.NoteSpendProofControllerAdmission.NoteSpendCommonGame.validSpend_of_not_soundnessBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NoteSpendCommonGame.validSpend_of_not_soundnessBad
/-- info: 'Minidregg.Assurance.NoteSpendProofControllerAdmission.NoteSpendCommonGame.no_current_semantic_deployment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms NoteSpendCommonGame.no_current_semantic_deployment

end

end Minidregg.Assurance.NoteSpendProofControllerAdmission
