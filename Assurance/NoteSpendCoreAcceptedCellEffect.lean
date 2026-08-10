/-
# Assurance.NoteSpendCoreAcceptedCellEffect -- sealed note spends enter the cell kernel

This module gives the Lean-authored note-spend relation a direct positive path
through the release-free `ComputationDeclaration` core.  The only transition
authority consumed is the common request-indexed `TypedAuthorization.Authorized`
token.  The note-spend witness is checked against `Compiler.NoteSpend`'s exact
constraint system; the eager nullifier, committed output, typed spend effect,
complete request/effect digests, and canonical pre-state are retained by the
accepted token and its one validated patch.

This is relation acceptance, not a deployed ZK verifier.  In particular, no
hiding, proof-of-knowledge, collision-resistance, random-oracle, PCS, or native
implementation claim is made here.  A later reveal or declassification remains
a separate accepted-cell effect because the computation family is sealed.
-/
import Compiler.NoteSpend
import Theory.AcceptedCellEffect

namespace Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## Exact first-order statement -/

abbrev Scalar := ZMod 13
abbrev Wire := SWire 2 2 2

/-- First-order identity of the Lean-authored demo note-spend program.  Zero
proof-suite/controller pins below mean unassigned, not implicitly deployed. -/
structure Program where
  relationId : Digest
deriving DecidableEq, Repr

def noteSpendRelationId : Digest := ⟨801⟩
def program : Program := ⟨noteSpendRelationId⟩

/-- The relation is a separate request field so a program identity cannot be
silently reused for a different arithmetization. -/
structure Relation where
  relationId : Digest
deriving DecidableEq, Repr

def relation : Relation := ⟨noteSpendRelationId⟩

/-- Public values exposed by the note-spend relation. -/
structure PublicInput where
  nullifier : Scalar
  root : Scalar
deriving DecidableEq, Repr

/-- The sealed output representation names only the committed note value. -/
structure OutputRepresentation where
  commitment : Scalar
deriving DecidableEq, Repr

/-- Exact typed state intent carried by the core request. -/
structure SpendEffect where
  nullifier : Scalar
  root : Scalar
  outputCommitment : Scalar
deriving DecidableEq, Repr

/-- First-order mode pins.  The zero proof-suite/controller identifiers are
explicit absence markers and are not interpreted as cryptographic evidence. -/
structure ModeEvidencePins where
  relationId : Digest
  proofSuiteId : Digest
  controllerDigest : Digest
deriving DecidableEq, Repr

def modeEvidencePins : ModeEvidencePins where
  relationId := noteSpendRelationId
  proofSuiteId := ⟨0⟩
  controllerDigest := ⟨0⟩

theorem cryptographic_pins_unassigned :
    modeEvidencePins.proofSuiteId = ⟨0⟩ ∧
      modeEvidencePins.controllerDigest = ⟨0⟩ := by
  decide

/-- The witness is ordinary Lean assignment data.  Acceptance is established
only by the portal relation below; this structure is not a proof object emitted
by a claimed deployed ZK prover. -/
structure Evidence where
  assignment : Wire → Scalar

/-- Only witness-ZK mode is inhabited by this language. -/
def language : PrivateComputationLanguage where
  Program := fun
    | .witnessZk => Program
    | .sharedMpc => PEmpty
    | .encryptedRnsFhe => PEmpty
  InputArtifact := fun
    | .witnessZk => PublicInput
    | .sharedMpc => PEmpty
    | .encryptedRnsFhe => PEmpty
  OutputArtifact := fun
    | .witnessZk => OutputRepresentation
    | .sharedMpc => PEmpty
    | .encryptedRnsFhe => PEmpty
  Evidence := fun
    | .witnessZk => Evidence
    | .sharedMpc => PEmpty
    | .encryptedRnsFhe => PEmpty

abbrev Statement :=
  CoreStatement language .witnessZk Relation PublicInput Scalar Unit
    ModeEvidencePins

def noteSpendConstraints :=
  noteSpendSystem demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW
    SWire.nullifierW SWire.commitW SWire.rootW (spendPath 2 2 2)

/-- Exact arithmetic relation checked for admission.  The public input and
output commitment are values of the same accepted assignment. -/
def Accepts (statement : Statement) (evidence : Evidence) : Prop :=
  statement.program = program ∧
  statement.relation = relation ∧
  statement.modeEvidencePins = modeEvidencePins ∧
  statement.inputArtifact = statement.inputValue ∧
  statement.inputValue.nullifier = evidence.assignment SWire.nullifierW ∧
  statement.inputValue.root = evidence.assignment SWire.rootW ∧
  statement.outputArtifact.commitment = statement.outputCommitment ∧
  statement.outputCommitment = evidence.assignment SWire.commitW ∧
  statement.privateOutput = () ∧
  systemAccepts evidence.assignment noteSpendConstraints

/-- A logical checker for the exact authored relation.  It does not claim to
be a deployed proof verifier and makes no hiding or knowledge statement. -/
def evidencePortal : PrivateEvidencePortal Statement Evidence := by
  classical
  exact {
    verify := fun statement evidence => decide (Accepts statement evidence)
    Accepts := Accepts
    accepted_law := by
      intro statement evidence accepted
      exact of_decide_eq_true accepted
  }

/-! ## Release-free declaration -/

def inputBridge : NamedRepresentationBridge Digest PublicInput Unit PublicInput Unit
    PublicInput where
  name := ⟨802⟩
  verifySource := fun artifact _ value => decide (artifact = value)
  verifyTarget := fun artifact _ value => decide (artifact = value)

def declaration : ComputationDeclaration language .witnessZk Relation Digest
    PublicInput PublicInput Unit Unit Scalar Unit SpendEffect Unit Scalar
    ModeEvidencePins where
  inputBridge := inputBridge
  computationPortal := evidencePortal

abbrev CoreRequest := declaration.Request
abbrev CoreResult := declaration.Result

def intendedEffect (request : CoreRequest) : SpendEffect where
  nullifier := request.inputValue.nullifier
  root := request.inputValue.root
  outputCommitment := request.outputCommitment

/-- Extra note-spend exactness retained around the generic computation token.
These are state/effect bindings, never a second authorization witness. -/
structure Accepted
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (adapter : ComputationCellEffect.Adapter (S := S) declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    (commonRequest : Request kind) (pre : CellState.Materialized M)
    (request : CoreRequest) (result : CoreResult) where
  computation : ComputationCellEffect.Accepted (portal := portal)
    (authState := authState) declaration adapter commonRequest pre request result
  resourceEffectsExact : request.resourceEffects = [intendedEffect request]
  eagerNullifierExact : request.nullifier = some request.inputValue.nullifier

/-- Direct positive join.  `authorization` is the sole transition-authority
argument.  The validated value is indexed by the one exact adapter patch. -/
def accept
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    (adapter : ComputationCellEffect.Adapter (S := S) declaration)
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (authorization : Authorized portal authState commonRequest)
    (argsDigestBound :
      commonRequest.argsDigest = adapter.completeRequestDigest request)
    (effectsDigestBound :
      commonRequest.effectsDigest = adapter.completeEffectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (completion : declaration.Completion request result)
    (resourceEffectsExact : request.resourceEffects = [intendedEffect request])
    (eagerNullifierExact : request.nullifier = some request.inputValue.nullifier)
    (validated : CellState.ValidatedPatch M pre (adapter.patch request result)) :
    Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result where
  computation := ComputationCellEffect.accept declaration adapter authorization
    argsDigestBound effectsDigestBound preRootBound completion validated
  resourceEffectsExact := resourceEffectsExact
  eagerNullifierExact := eagerNullifierExact

/-! ## What an accepted token proves -/

/-- The exact validated canonical patch retained by an accepted note spend. -/
def Accepted.validatedPatch
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    CellState.ValidatedPatch M pre (adapter.patch request result) :=
  accepted.computation.cellEffect.validated

/-- The note-spend completion retains the exact constraint acceptance proof and
all public bindings.  This theorem is deliberately arithmetic only. -/
theorem accepted_relation
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    request.program = program ∧
    request.relation = relation ∧
    request.modeEvidencePins = modeEvidencePins ∧
    request.computationInput = request.inputValue ∧
    request.inputValue.nullifier =
      accepted.computation.cellEffect.modeEvidence.computation.witness.assignment
        SWire.nullifierW ∧
    request.inputValue.root =
      accepted.computation.cellEffect.modeEvidence.computation.witness.assignment
        SWire.rootW ∧
    result.outputRepresentation.commitment = request.outputCommitment ∧
    request.outputCommitment =
      accepted.computation.cellEffect.modeEvidence.computation.witness.assignment
        SWire.commitW ∧
    systemAccepts
      accepted.computation.cellEffect.modeEvidence.computation.witness.assignment
      noteSpendConstraints := by
  have semantics := accepted.computation.cellEffect.modeEvidence.computation.accepts
  simpa only [ComputationDeclaration.statementOf] using
    ⟨semantics.1, semantics.2.1, semantics.2.2.1, semantics.2.2.2.1,
      semantics.2.2.2.2.1, semantics.2.2.2.2.2.1,
      semantics.2.2.2.2.2.2.1, semantics.2.2.2.2.2.2.2.1,
      semantics.2.2.2.2.2.2.2.2.2⟩

/-- Constraint acceptance entails exactly `Compiler.NoteSpend.ValidSpend` for
the accepted assignment's note.  It does not entail hiding or knowledge. -/
theorem accepted_validSpend
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    ValidSpend demoNfSpec demoSpec demoSpec 0 2 2
      request.inputValue.nullifier request.inputValue.root
      (fun i =>
        accepted.computation.cellEffect.modeEvidence.computation.witness.assignment
          (SWire.noteW i)) := by
  have relationAccepted := (accepted_relation accepted).2.2.2.2.2.2.2.2
  have valid := noteSpend_binds
    accepted.computation.cellEffect.modeEvidence.computation.witness.assignment
    demoNfSpec demoSpec demoSpec SWire.noteW 0 SWire.bitW SWire.nullifierW
    SWire.commitW SWire.rootW (spendPath 2 2 2) relationAccepted
  have nullifierBound := (accepted_relation accepted).2.2.2.2.1
  have rootBound := (accepted_relation accepted).2.2.2.2.2.1
  simpa only [spendPath_length, nullifierBound, rootBound] using valid

/-- Common request, effect, pre-state, eager-nullifier, and sealing facts remain
simultaneously available from the accepted token. -/
theorem accepted_kernel_bindings
    {S : CellState.Schema} [DecidableEq S.Field] [DecidableEq S.Resource]
    {M : CellState.Materializer S Digest}
    {adapter : ComputationCellEffect.Adapter (S := S) declaration}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : CoreRequest} {result : CoreResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    commonRequest.argsDigest = adapter.completeRequestDigest request ∧
    commonRequest.effectsDigest = adapter.completeEffectDigest request ∧
    commonRequest.preStateRoot = pre.root ∧
    request.resourceEffects = [intendedEffect request] ∧
    accepted.computation.cellEffect.prepared.nullifier =
      some request.inputValue.nullifier ∧
    accepted.computation.cellEffect.disclosure = .sealed := by
  exact ⟨accepted.computation.argsDigestBound,
    accepted.computation.cellEffect.effectsDigestBound,
    accepted.computation.cellEffect.preRootBound,
    accepted.resourceEffectsExact,
    by simpa only [ComputationCellEffect.accepted_nullifier]
      using accepted.eagerNullifierExact,
    accepted.computation.disclosure_sealed⟩

/-- info: 'Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.cryptographic_pins_unassigned' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms cryptographic_pins_unassigned
/-- info: 'Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.accepted_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_relation
/-- info: 'Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.accepted_validSpend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_validSpend
/-- info: 'Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.accepted_kernel_bindings' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_kernel_bindings
/-- info: 'Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.Accepted.validatedPatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Accepted.validatedPatch

end

end Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect
