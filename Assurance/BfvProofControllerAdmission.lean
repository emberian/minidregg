/-
# Assurance.BfvProofControllerAdmission -- honest BFV384 deployment boundary

This module derives the BFV controller statement from the release-free
`AcceptedCellEffect`, then separates deterministic control-envelope/reflected
checker acceptance from semantic BFV admission.

The common-game theorem says only this: if a future reflected suite checker
accepts, then outside separately priced arithmetic, PCS, collision-resistance,
random-oracle, and knowledge failures it must extract the existing exact
384-row BFV relation.  There is no hiding event, privacy theorem, release
value, or disclosure inference.  The current suite/controller/proof-codec pins
remain zero.  A reflected receipt is therefore explicitly weak; the semantic
`CoreJoin.AdmittedReceipt` can only be constructed on one good game coin from
the exact BFV `RelationWitness` reduction laws.
-/
import Assurance.BfvPrivateComputationJoin
import Assurance.ProofCompositionGame
import Compiler.BfvProofController

namespace Minidregg.Assurance.BfvProofControllerAdmission

open Minidregg.Assurance.BfvPrivateComputationJoin
open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Compiler
open Minidregg.Compiler.BfvCompressedEquation
open Minidregg.Compiler.BfvInputValidity
open Minidregg.Compiler.BfvProofController
open Minidregg.Compiler.BfvReceiptClause
open Minidregg.Loom
open Minidregg.Theory
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

namespace CoreJoin

/-! ## Canonical statement from the accepted sealed computation -/

/-- No caller authors BFV statement bytes or deployment pins.  The request and
effect digests, pre-root, public BFV identity, output commitment, and existing
zero mode pins are projected from the already-authorized computation. -/
def statementOf
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    (dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier)
    (adapter : ComputationCellEffect.Adapter (S := S) dialect.declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : dialect.declaration.Request} {result : dialect.declaration.Result}
    (accepted : ComputationCellEffect.Accepted (portal := portal)
      (authState := authState) dialect.declaration adapter commonRequest pre
      request result) : Statement :=
  let _acceptedOwner := accepted
  canonicalStatement commonRequest.argsDigest commonRequest.effectsDigest
    commonRequest.preStateRoot request.inputValue request.outputCommitment
    request.modeEvidencePins.outputRepresentationId bfvClauseDecl.proofCodecId
    request.modeEvidencePins.proofSuiteId request.modeEvidencePins.controllerDigest

/-- Every load-bearing statement field is inherited from the one accepted
kernel turn.  In particular all three deployment pins remain zero and the
source effect is sealed. -/
theorem statementOf_exact
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    (dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier)
    (adapter : ComputationCellEffect.Adapter (S := S) dialect.declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : dialect.declaration.Request} {result : dialect.declaration.Result}
    (accepted : ComputationCellEffect.Accepted (portal := portal)
      (authState := authState) dialect.declaration adapter commonRequest pre
      request result) :
    (statementOf dialect adapter accepted).argsDigest =
      adapter.completeRequestDigest request ∧
    (statementOf dialect adapter accepted).effectsDigest =
      adapter.completeEffectDigest request ∧
    (statementOf dialect adapter accepted).preRoot = pre.root ∧
    (statementOf dialect adapter accepted).publicInputDescriptor =
      publicInputDescriptor request.inputValue ∧
    (statementOf dialect adapter accepted).outputCommitment =
      result.outputRepresentation.commitmentId ∧
    (statementOf dialect adapter accepted).relationDescriptor =
      exactRelationDescriptor ∧
    (statementOf dialect adapter accepted).clauseId = bfvClauseId ∧
    (statementOf dialect adapter accepted).relationId = request.relation ∧
    (statementOf dialect adapter accepted).outputRepresentationId =
      outputRepresentationId ∧
    result.outputRepresentation.representationId = outputRepresentationId ∧
    (statementOf dialect adapter accepted).proofCodecId = ⟨0⟩ ∧
    (statementOf dialect adapter accepted).proofSuiteId =
      request.modeEvidencePins.proofSuiteId ∧
    request.modeEvidencePins.proofSuiteId = ⟨0⟩ ∧
    (statementOf dialect adapter accepted).controllerDigest =
      request.modeEvidencePins.controllerDigest ∧
    request.modeEvidencePins.controllerDigest = ⟨0⟩ ∧
    accepted.cellEffect.disclosure = .sealed := by
  rcases acceptedCore_bfv_semantics dialect adapter accepted with
    ⟨argsBound, effectsBound, sealed, programExact, relationExact, pinsExact,
      inputExact, outputExact, representationExact, commitmentExact, rowsExact⟩
  have preBound := accepted.cellEffect.preRootBound
  have suiteZero : request.modeEvidencePins.proofSuiteId = ⟨0⟩ := by
    rw [pinsExact]
    rfl
  have controllerZero : request.modeEvidencePins.controllerDigest = ⟨0⟩ := by
    rw [pinsExact]
    rfl
  have statementSuite :
      (statementOf dialect adapter accepted).proofSuiteId =
        request.modeEvidencePins.proofSuiteId := by
    change request.modeEvidencePins.proofSuiteId =
      request.modeEvidencePins.proofSuiteId
    rfl
  have statementController :
      (statementOf dialect adapter accepted).controllerDigest =
        request.modeEvidencePins.controllerDigest := by
    change request.modeEvidencePins.controllerDigest =
      request.modeEvidencePins.controllerDigest
    rfl
  have statementRepresentation :
      (statementOf dialect adapter accepted).outputRepresentationId =
        outputRepresentationId := by
    change request.modeEvidencePins.outputRepresentationId = outputRepresentationId
    rw [pinsExact]
    rfl
  exact ⟨argsBound, effectsBound, preBound, rfl, commitmentExact,
    rfl, rfl, relationExact.symm, statementRepresentation,
    representationExact, rfl, statementSuite, suiteZero,
    statementController, controllerZero, sealed⟩

/-- The accepted BFV core is still deliberately undeployed: its exact
statement cannot carry a suite whose codec, suite, and controller identities
are all assigned. -/
theorem statementOf_no_boundReflectedChecker
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    (dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier)
    (adapter : ComputationCellEffect.Adapter (S := S) dialect.declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : dialect.declaration.Request} {result : dialect.declaration.Result}
    (accepted : ComputationCellEffect.Accepted (portal := portal)
      (authState := authState) dialect.declaration adapter commonRequest pre
      request result) :
    ¬Nonempty (BoundReflectedChecker (statementOf dialect adapter accepted)) := by
  rintro ⟨bound⟩
  have exact := statementOf_exact dialect adapter accepted
  exact bound.checker.proofCodecAssigned (by
    rw [← bound.proofCodecBound]
    exact exact.2.2.2.2.2.2.2.2.2.2.1)

/-! ## Reflected checker admission remains explicitly weak -/

inductive AdmissionFailure (Error : Type)
  | control (failure : Failure Error)
  | rejectedChecker
deriving Repr

/-- Successful weak admission retains the concrete controller evidence and the
candidate checker's reflected proposition.  It carries no reduction laws. -/
structure ReflectedReceipt (statement : Statement)
    (bound : BoundReflectedChecker statement) where
  controlled : ControlledReceipt statement
  checkerAccepted : bound.checker.ReflectedAccepts statement controlled.receipt

/-- Lean runs the fixed decoder/control checker first and the supplied Lean
suite checker second.  There is no caller-provided acceptance proposition. -/
def runReflected {Error : Type} (statement : Statement)
    (bound : BoundReflectedChecker statement) (runner : OpaqueProofRunner Error) :
    Except (AdmissionFailure Error) (ReflectedReceipt statement bound) :=
  match Minidregg.Compiler.BfvProofController.run statement runner with
  | .error failure => .error (.control failure)
  | .ok controlled =>
      if checked : bound.checker.check statement controlled.receipt = true then
        .ok ⟨controlled,
          (bound.checker.check_iff statement controlled.receipt).mp checked⟩
      else
        .error .rejectedChecker

/-- The core-specific runner always sends the exact accepted-effect statement. -/
def runAcceptedReflected
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    (dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier)
    (adapter : ComputationCellEffect.Adapter (S := S) dialect.declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : dialect.declaration.Request} {result : dialect.declaration.Result}
    (accepted : ComputationCellEffect.Accepted (portal := portal)
      (authState := authState) dialect.declaration adapter commonRequest pre
      request result)
    {Error : Type}
    (bound : BoundReflectedChecker (statementOf dialect adapter accepted))
    (runner : OpaqueProofRunner Error) :
    Except (AdmissionFailure Error)
      (ReflectedReceipt (statementOf dialect adapter accepted) bound) :=
  runReflected (statementOf dialect adapter accepted) bound runner

theorem runReflected_success_integrity {Error : Type} (statement : Statement)
    (bound : BoundReflectedChecker statement) (runner : OpaqueProofRunner Error)
    (reply : ReflectedReceipt statement bound)
    (success : runReflected statement bound runner = .ok reply) :
    runner (statementCodec.encode statement) =
        .ok reply.controlled.proofBytes ∧
    receiptCodec.decode reply.controlled.proofBytes =
        some reply.controlled.receipt ∧
    ControlAccepts statement reply.controlled.receipt ∧
    bound.checker.ReflectedAccepts statement reply.controlled.receipt := by
  unfold runReflected at success
  split at success
  next failure failed => simp at success
  next controlled controlledRun =>
    split at success
    next checked =>
      simp only [Except.ok.injEq] at success
      subst reply
      have integrity :=
        Minidregg.Compiler.BfvProofController.run_success_integrity statement runner
          controlled controlledRun
      exact ⟨integrity.1, integrity.2.1, integrity.2.2,
        (bound.checker.check_iff statement controlled.receipt).mp checked⟩
    next rejected => simp at success

end CoreJoin

/-! ## Exact 384-row relation extracted by a future suite -/

/-- Proof-relevant satisfaction of the exact core statement.  The evidence
contains the existing `AcceptedToken`, hence one shared committed input and one
checked accumulator/call token for each of the 384 modulus-major rows. -/
structure RelationWitness
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    (dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier)
    (request : dialect.declaration.Request) (result : dialect.declaration.Result) where
  evidence : Evidence
  relationAccepted : CoreAccepts (dialect.declaration.statementOf request result)
    evidence

/-- Extracted relation satisfaction yields exactly the existing integer
equation for every one of the 384 rows.  It yields no privacy or hiding fact. -/
theorem RelationWitness.every_exact_integer_equation
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    {dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier}
    {request : dialect.declaration.Request} {result : dialect.declaration.Result}
    (witness : RelationWitness dialect request result)
    (rowIndex : Fin equationsPerOwner) :
    (result.outputRepresentation.equations.equation rowIndex).numerator
        witness.evidence.token.input.row =
      ((result.outputRepresentation.equations.equation rowIndex).rns.value : Int) *
        (witness.evidence.token.batch.rowCall rowIndex).witness.quotient.value := by
  rcases witness.relationAccepted with
    ⟨programExact, relationExact, pinsExact, claimExact, inputExact,
      outputExact, commitmentExact, privateExact⟩
  change result.outputRepresentation = witness.evidence.outputRepresentation at outputExact
  rw [outputExact]
  exact witness.evidence.every_exact_integer_equation rowIndex

/-! ## Separately priced same-coin deployment obligations -/

/-- These are five distinct proof obligations.  In particular relation
satisfaction is not renamed as proof of knowledge. -/
inductive FailureClass
  | arithmeticSoundness
  | pcsSoundness
  | collisionResistance
  | randomOracle
  | proofOfKnowledge
deriving DecidableEq, Fintype, Repr

abbrev FailureLedger (Omega : Type) [Fintype Omega] :=
  FailureClass → PricedFailure Omega

namespace FailureLedger

variable {Omega : Type} [Fintype Omega]

def Good (ledger : FailureLedger Omega) (failure : FailureClass)
    (omega : Omega) : Prop :=
  ¬(ledger failure).event omega

def Bad (ledger : FailureLedger Omega) (omega : Omega) : Prop :=
  (ledger .arithmeticSoundness).event omega ∨
  (ledger .pcsSoundness).event omega ∨
  (ledger .collisionResistance).event omega ∨
  (ledger .randomOracle).event omega ∨
  (ledger .proofOfKnowledge).event omega

def totalPrice (ledger : FailureLedger Omega) : Real :=
  (ledger .arithmeticSoundness).price +
  (ledger .pcsSoundness).price +
  (ledger .collisionResistance).price +
  (ledger .randomOracle).price +
  (ledger .proofOfKnowledge).price

theorem good_of_not_bad (ledger : FailureLedger Omega) {omega : Omega}
    (good : ¬ledger.Bad omega) (failure : FailureClass) :
    ledger.Good failure omega := by
  intro bad
  cases failure with
  | arithmeticSoundness => exact good (Or.inl bad)
  | pcsSoundness => exact good (Or.inr (Or.inl bad))
  | collisionResistance => exact good (Or.inr (Or.inr (Or.inl bad)))
  | randomOracle => exact good (Or.inr (Or.inr (Or.inr (Or.inl bad))))
  | proofOfKnowledge => exact good (Or.inr (Or.inr (Or.inr (Or.inr bad))))

theorem bad_le_total (ledger : FailureLedger Omega) :
    uniformProb Omega ledger.Bad ≤ ledger.totalPrice := by
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
  unfold Bad totalPrice
  linarith [(ledger .arithmeticSoundness).bound,
    (ledger .pcsSoundness).bound,
    (ledger .collisionResistance).bound,
    (ledger .randomOracle).bound,
    (ledger .proofOfKnowledge).bound]

end FailureLedger

/-! ## The exact unimplemented same-coin reduction shape -/

/-- A concrete BFV384 suite must prove this extraction law for its reflected
checker on the same game coin.  This structure does not implement the checker,
assign deployment pins, or turn the existing arithmetic token into a security
theorem. -/
structure SameCoinReductionLaws
    {Omega : Type} [Fintype Omega] (ledger : FailureLedger Omega)
    {statement : Statement} (bound : BoundReflectedChecker statement)
    (Witness : Type) where
  extract : ∀ omega receipt,
    ControlAccepts statement receipt →
    bound.checker.ReflectedAccepts statement receipt →
    ledger.Good .arithmeticSoundness omega →
    ledger.Good .pcsSoundness omega →
    ledger.Good .collisionResistance omega →
    ledger.Good .randomOracle omega →
    ledger.Good .proofOfKnowledge omega →
    Witness

/-! ## Semantic admission: exact BFV relation on one good coin -/

namespace CoreJoin

/-- A semantic BFV admission is intentionally much stronger than a reflected
receipt.  Its statement is the exact statement projected from one accepted
kernel computation; its reduction law extracts that computation's 384-row
`RelationWitness`; and the receipt names one coin outside the separately
priced arithmetic, PCS, CR, ROM, and PoK failures.

No hiding field occurs: this release-free lane makes no privacy claim. -/
structure AdmittedReceipt
    {Omega : Type} [Fintype Omega]
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    (dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier)
    (adapter : ComputationCellEffect.Adapter (S := S) dialect.declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : dialect.declaration.Request} {result : dialect.declaration.Result}
    (accepted : ComputationCellEffect.Accepted (portal := portal)
      (authState := authState) dialect.declaration adapter commonRequest pre
      request result)
    (bound : BoundReflectedChecker (statementOf dialect adapter accepted))
    (ledger : FailureLedger Omega)
    (laws : SameCoinReductionLaws ledger bound (RelationWitness dialect request result))
    (omega : Omega) where
  reflected : ReflectedReceipt (statementOf dialect adapter accepted) bound
  outsideFailures : ¬ledger.Bad omega

namespace AdmittedReceipt

variable {Omega : Type} [Fintype Omega]
variable {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
variable {M : CellState.Materializer S Digest}
variable {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
  Nullifier : Type}
variable {dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
  ResourceEffect Footprint Nullifier}
variable {adapter : ComputationCellEffect.Adapter (S := S) dialect.declaration}
variable {portal : Portal} {authState : AuthState} {kind : ResourceKind}
variable {commonRequest : Request kind} {pre : CellState.Materialized M}
variable {request : dialect.declaration.Request} {result : dialect.declaration.Result}
variable {accepted : ComputationCellEffect.Accepted (portal := portal)
  (authState := authState) dialect.declaration adapter commonRequest pre request result}
variable {bound : BoundReflectedChecker (statementOf dialect adapter accepted)}
variable {ledger : FailureLedger Omega}
variable {laws : SameCoinReductionLaws ledger bound
  (RelationWitness dialect request result)}
variable {omega : Omega}

/-- Extraction is derived from the exact checker acceptance and the five good
events carried by this receipt; it is not a caller-authored witness field. -/
noncomputable def witness
    (admitted : AdmittedReceipt dialect adapter accepted bound ledger laws omega) :
    RelationWitness dialect request result :=
  laws.extract omega admitted.reflected.controlled.receipt
    admitted.reflected.controlled.controlled admitted.reflected.checkerAccepted
    (ledger.good_of_not_bad admitted.outsideFailures .arithmeticSoundness)
    (ledger.good_of_not_bad admitted.outsideFailures .pcsSoundness)
    (ledger.good_of_not_bad admitted.outsideFailures .collisionResistance)
    (ledger.good_of_not_bad admitted.outsideFailures .randomOracle)
    (ledger.good_of_not_bad admitted.outsideFailures .proofOfKnowledge)

theorem every_exact_integer_equation
    (admitted : AdmittedReceipt dialect adapter accepted bound ledger laws omega)
    (rowIndex : Fin equationsPerOwner) :
    (result.outputRepresentation.equations.equation rowIndex).numerator
        admitted.witness.evidence.token.input.row =
      ((result.outputRepresentation.equations.equation rowIndex).rns.value : Int) *
        (admitted.witness.evidence.token.batch.rowCall rowIndex).witness.quotient.value :=
  admitted.witness.every_exact_integer_equation rowIndex

end AdmittedReceipt

/-- The canonical semantic runner is available only with the exact common-coin
reduction laws and a proof that this coin is outside all five failure events.
The weaker bytes/checker path remains `runReflected`. -/
def run
    {Omega : Type} [Fintype Omega]
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    (dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier)
    (adapter : ComputationCellEffect.Adapter (S := S) dialect.declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : dialect.declaration.Request} {result : dialect.declaration.Result}
    (accepted : ComputationCellEffect.Accepted (portal := portal)
      (authState := authState) dialect.declaration adapter commonRequest pre
      request result)
    (bound : BoundReflectedChecker (statementOf dialect adapter accepted))
    (ledger : FailureLedger Omega)
    (laws : SameCoinReductionLaws ledger bound
      (RelationWitness dialect request result))
    (omega : Omega) (outsideFailures : ¬ledger.Bad omega)
    {Error : Type} (runner : OpaqueProofRunner Error) :
    Except (AdmissionFailure Error)
      (AdmittedReceipt dialect adapter accepted bound ledger laws omega) :=
  match runReflected (statementOf dialect adapter accepted) bound runner with
  | .error failure => .error failure
  | .ok reflected => .ok ⟨reflected, outsideFailures⟩

theorem run_success_integrity
    {Omega : Type} [Fintype Omega]
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
      Nullifier : Type}
    (dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
      ResourceEffect Footprint Nullifier)
    (adapter : ComputationCellEffect.Adapter (S := S) dialect.declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : dialect.declaration.Request} {result : dialect.declaration.Result}
    (accepted : ComputationCellEffect.Accepted (portal := portal)
      (authState := authState) dialect.declaration adapter commonRequest pre
      request result)
    (bound : BoundReflectedChecker (statementOf dialect adapter accepted))
    (ledger : FailureLedger Omega)
    (laws : SameCoinReductionLaws ledger bound
      (RelationWitness dialect request result))
    (omega : Omega) (outsideFailures : ¬ledger.Bad omega)
    {Error : Type} (runner : OpaqueProofRunner Error)
    (reply : AdmittedReceipt dialect adapter accepted bound ledger laws omega)
    (success : run dialect adapter accepted bound ledger laws omega outsideFailures
      runner = .ok reply) :
    runner (statementCodec.encode (statementOf dialect adapter accepted)) =
        .ok reply.reflected.controlled.proofBytes ∧
      receiptCodec.decode reply.reflected.controlled.proofBytes =
        some reply.reflected.controlled.receipt ∧
      ControlAccepts (statementOf dialect adapter accepted)
        reply.reflected.controlled.receipt ∧
      bound.checker.ReflectedAccepts (statementOf dialect adapter accepted)
        reply.reflected.controlled.receipt ∧
      (∀ rowIndex : Fin equationsPerOwner,
        (result.outputRepresentation.equations.equation rowIndex).numerator
            reply.witness.evidence.token.input.row =
          ((result.outputRepresentation.equations.equation rowIndex).rns.value : Int) *
            (reply.witness.evidence.token.batch.rowCall rowIndex).witness.quotient.value) := by
  unfold run at success
  split at success
  next failed => simp at success
  next reflected reflectedRun =>
    simp only [Except.ok.injEq] at success
    subst reply
    have integrity := runReflected_success_integrity
      (statementOf dialect adapter accepted) bound runner reflected reflectedRun
    exact ⟨integrity.1, integrity.2.1, integrity.2.2.1, integrity.2.2.2,
      fun rowIndex => AdmittedReceipt.every_exact_integer_equation _ rowIndex⟩

end CoreJoin

/-! ## One common coin controls execution and all five failure events -/

structure CommonGameFamily
    (Omega : Type) [Fintype Omega] (Error : Type) {statement : Statement}
    (bound : BoundReflectedChecker statement) (Witness : Type) where
  ledger : FailureLedger Omega
  laws : SameCoinReductionLaws ledger bound Witness
  runner : Omega → OpaqueProofRunner Error
  execution : Omega → Option (CoreJoin.ReflectedReceipt statement bound)
  executionExact : ∀ omega reply, execution omega = some reply →
    CoreJoin.runReflected statement bound (runner omega) = .ok reply

namespace CommonGameFamily

variable {Omega : Type} [Fintype Omega] {Error : Type}
variable {statement : Statement} {bound : BoundReflectedChecker statement}
variable {Witness : Type}

def FalseAccept (family : CommonGameFamily Omega Error bound Witness)
    (omega : Omega) : Prop :=
  ∃ reply, family.execution omega = some reply ∧
    ¬Nonempty Witness

theorem execution_runner_bytes
    (family : CommonGameFamily Omega Error bound Witness)
    {omega : Omega}
    {reply : CoreJoin.ReflectedReceipt statement bound}
    (selected : family.execution omega = some reply) :
    family.runner omega (statementCodec.encode statement) =
        .ok reply.controlled.proofBytes := by
  exact (CoreJoin.runReflected_success_integrity statement bound (family.runner omega)
    reply (family.executionExact omega reply selected)).1

theorem falseAccept_bad
    (family : CommonGameFamily Omega Error bound Witness) (omega : Omega)
    (falseAccept : family.FalseAccept omega) : family.ledger.Bad omega := by
  by_contra good
  obtain ⟨reply, selected, falseRelation⟩ := falseAccept
  have arithmetic := family.ledger.good_of_not_bad good .arithmeticSoundness
  have pcs := family.ledger.good_of_not_bad good .pcsSoundness
  have collision := family.ledger.good_of_not_bad good .collisionResistance
  have oracle := family.ledger.good_of_not_bad good .randomOracle
  have knowledge := family.ledger.good_of_not_bad good .proofOfKnowledge
  exact falseRelation ⟨family.laws.extract omega reply.controlled.receipt
    reply.controlled.controlled reply.checkerAccepted arithmetic pcs collision oracle
    knowledge⟩

theorem falseAccept_le
    (family : CommonGameFamily Omega Error bound Witness) :
    uniformProb Omega family.FalseAccept ≤ family.ledger.totalPrice :=
  le_trans (uniformProb_mono family.falseAccept_bad) family.ledger.bad_le_total

/-- Outside the exact five failures, reflected suite acceptance yields the
witness type named by the suite laws. -/
theorem witness_of_not_bad
    (family : CommonGameFamily Omega Error bound Witness)
    {omega : Omega}
    {reply : CoreJoin.ReflectedReceipt statement bound}
    (selected : family.execution omega = some reply)
    (good : ¬family.ledger.Bad omega) :
    Nonempty Witness := by
  have arithmetic := family.ledger.good_of_not_bad good .arithmeticSoundness
  have pcs := family.ledger.good_of_not_bad good .pcsSoundness
  have collision := family.ledger.good_of_not_bad good .collisionResistance
  have oracle := family.ledger.good_of_not_bad good .randomOracle
  have knowledge := family.ledger.good_of_not_bad good .proofOfKnowledge
  have _runnerBytes := family.execution_runner_bytes selected
  let witness := family.laws.extract omega reply.controlled.receipt
    reply.controlled.controlled reply.checkerAccepted arithmetic pcs collision oracle
    knowledge
  exact ⟨witness⟩

end CommonGameFamily

/-! ## Specialization back to the exact accepted BFV core -/

namespace BfvCommonGame

variable {Omega : Type} [Fintype Omega] {Error : Type}
variable {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
variable {M : CellState.Materializer S Digest}
variable {CanonicalInput InputSourceWitness InputTargetWitness ResourceEffect Footprint
  Nullifier : Type}
variable {dialect : CoreDialect CanonicalInput InputSourceWitness InputTargetWitness
  ResourceEffect Footprint Nullifier}
variable {adapter : ComputationCellEffect.Adapter (S := S) dialect.declaration}
variable {portal : Portal} {authState : AuthState} {kind : ResourceKind}
variable {commonRequest : Request kind} {pre : CellState.Materialized M}
variable {request : dialect.declaration.Request} {result : dialect.declaration.Result}
variable {accepted : ComputationCellEffect.Accepted (portal := portal)
  (authState := authState) dialect.declaration adapter commonRequest pre request result}
variable {bound : BoundReflectedChecker (CoreJoin.statementOf dialect adapter accepted)}

/-- The current accepted request cannot even package a semantic BFV
deployment: its zero-pinned statement has no bound nonzero checker.  Supplying
reduction laws out of band cannot repair that; the pins must first enter the
authorized request and therefore its canonical statement bytes. -/
theorem no_current_semantic_deployment :
    ¬∃ bound : BoundReflectedChecker
        (CoreJoin.statementOf dialect adapter accepted),
      ∃ ledger : FailureLedger Omega,
        Nonempty (SameCoinReductionLaws ledger bound
          (RelationWitness dialect request result)) := by
  rintro ⟨candidate, -, -⟩
  exact CoreJoin.statementOf_no_boundReflectedChecker dialect adapter accepted
    ⟨candidate⟩

/-- The semantic receipt together with evidence that it is the execution
selected by this common-game coin. -/
structure AdmittedExecution
    (family : CommonGameFamily Omega Error bound
      (RelationWitness dialect request result)) (omega : Omega) where
  semantic : CoreJoin.AdmittedReceipt dialect adapter accepted bound family.ledger
    family.laws omega
  selected : family.execution omega = some semantic.reflected

/-- On a good common-game coin, the weak reflected execution upgrades to the
semantic receipt.  The result is indexed by the exact accepted core and exact
`RelationWitness` laws, so a control-only checker cannot inhabit this type. -/
noncomputable def admitted_of_not_bad
    (family : CommonGameFamily Omega Error bound
      (RelationWitness dialect request result))
    {omega : Omega}
    {reply : CoreJoin.ReflectedReceipt
      (CoreJoin.statementOf dialect adapter accepted) bound}
    (selected : family.execution omega = some reply)
    (good : ¬family.ledger.Bad omega) :
    AdmittedExecution family omega where
  semantic := {
    reflected := reply
    outsideFailures := good }
  selected := selected

/-- A future suite which closes the currently impossible bound-deployment
premise obtains all 384 exact integer equations.  No privacy, hiding, release,
or declassification conclusion is present. -/
theorem every_exact_integer_equation_of_not_bad
    (family : CommonGameFamily Omega Error bound
      (RelationWitness dialect request result))
    {omega : Omega}
    {reply : CoreJoin.ReflectedReceipt
      (CoreJoin.statementOf dialect adapter accepted) bound}
    (selected : family.execution omega = some reply)
    (good : ¬family.ledger.Bad omega) :
    ∃ witness : RelationWitness dialect request result,
      ∀ rowIndex : Fin equationsPerOwner,
        (result.outputRepresentation.equations.equation rowIndex).numerator
            witness.evidence.token.input.row =
          ((result.outputRepresentation.equations.equation rowIndex).rns.value : Int) *
            (witness.evidence.token.batch.rowCall rowIndex).witness.quotient.value := by
  let execution := admitted_of_not_bad family selected good
  exact ⟨execution.semantic.witness,
    execution.semantic.every_exact_integer_equation⟩

end BfvCommonGame

/-- info: 'Minidregg.Assurance.BfvProofControllerAdmission.CoreJoin.statementOf_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CoreJoin.statementOf_exact
/-- info: 'Minidregg.Assurance.BfvProofControllerAdmission.CoreJoin.statementOf_no_boundReflectedChecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CoreJoin.statementOf_no_boundReflectedChecker
/-- info: 'Minidregg.Assurance.BfvProofControllerAdmission.CoreJoin.runReflected_success_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CoreJoin.runReflected_success_integrity
/-- info: 'Minidregg.Assurance.BfvProofControllerAdmission.CoreJoin.run_success_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CoreJoin.run_success_integrity
/-- info: 'Minidregg.Assurance.BfvProofControllerAdmission.RelationWitness.every_exact_integer_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RelationWitness.every_exact_integer_equation
/-- info: 'Minidregg.Assurance.BfvProofControllerAdmission.FailureLedger.bad_le_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FailureLedger.bad_le_total
/-- info: 'Minidregg.Assurance.BfvProofControllerAdmission.CommonGameFamily.falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CommonGameFamily.falseAccept_le
/-- info: 'Minidregg.Assurance.BfvProofControllerAdmission.BfvCommonGame.every_exact_integer_equation_of_not_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BfvCommonGame.every_exact_integer_equation_of_not_bad
/-- info: 'Minidregg.Assurance.BfvProofControllerAdmission.BfvCommonGame.no_current_semantic_deployment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BfvCommonGame.no_current_semantic_deployment

end

end Minidregg.Assurance.BfvProofControllerAdmission
