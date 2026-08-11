/-
# Assurance.NoteSpendConcreteCellAdapter -- one concrete sealed spend patch

The note-spend core already fixes the semantic request, checked completion,
eager nullifier, and typed spend effect, but previously quantified over an
arbitrary `ComputationCellEffect.Adapter`.  This module supplies one concrete
adapter.  Its cell is deliberately coarse grained: one typed slot records the
complete effect list together with the request commitment and the checked
output representation.  The core declaration's `Unit` footprint therefore
lawfully names the exact singleton mutation for every request.

The request/result codecs below are lawful countable-carrier witnesses, not a
stable deployed wire format or codec pin.  Consequently this module closes the
semantic adapter/patch boundary while leaving codec deployment explicit.

The patch's expected pre-root is the canonical `Digest` embedding of the
note-spend public root.  A validated patch consequently joins that public root,
the common request pre-root, and the materialized cell root.  The positive path
still consumes exactly one common `Authorized` token and is necessarily sealed;
the computation family has no release carrier.  Proof-suite semantics remain
conditional on the separately indexed controller admission laws.
-/
import Assurance.NoteSpendProofControllerAdmission
import Theory.DeployedMaterializerWitness

namespace Minidregg.Assurance.NoteSpendConcreteCellAdapter

open Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect
open Minidregg.Assurance.NoteSpendProofControllerAdmission
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.DeployedMaterializerWitness
open Minidregg.Theory.IndexedProgram (LawfulCodec)
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## Concrete typed cell and lawful carrier codecs -/

abbrev SpendScalar :=
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.Scalar
abbrev SpendRequest :=
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.CoreRequest
abbrev SpendResult :=
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.CoreResult

/-- The sole cell value retains the complete authored effect intent and both
sides of the output-commitment join.  Completion proves the latter agree; the
adapter does not assume it for arbitrary unchecked request/result pairs. -/
structure CellValue where
  effects : List SpendEffect
  requestOutputCommitment : SpendScalar
  outputRepresentation : OutputRepresentation
deriving DecidableEq, Repr

/-- `Footprint = Unit` means the honest concrete realization is one coarse
typed slot.  It avoids pretending that a request-independent footprint can
name dynamically addressed nullifier and commitment keys. -/
def schema : CellState.Schema where
  Field := Unit
  FieldType := fun _ => CellValue
  Resource := Empty
  ResourceType := Empty.elim
  Authority := fun resource => nomatch resource
  Evidence := fun resource => nomatch resource

instance : DecidableEq schema.Field := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq schema.Resource := fun resource => resource.elim

deriving instance Countable for
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.Program
deriving instance Countable for
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.Relation
deriving instance Countable for
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.PublicInput
deriving instance Countable for
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.OutputRepresentation
deriving instance Countable for
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.SpendEffect
deriving instance Countable for
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.ModeEvidencePins
deriving instance Countable for CellValue
deriving instance Nonempty for Digest
deriving instance Nonempty for
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.Program
deriving instance Nonempty for
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.Relation
deriving instance Nonempty for
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.PublicInput
deriving instance Nonempty for
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.OutputRepresentation
deriving instance Nonempty for
  Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.ModeEvidencePins

/-- A nondependent wire mirror used only to obtain a lawful request codec.
Every core request field appears exactly once; no stable byte-format claim is
made by the countable-carrier choice. -/
structure RequestWire where
  program : Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.Program
  relation : Minidregg.Assurance.NoteSpendCoreAcceptedCellEffect.Relation
  canonicalInput : PublicInput
  computationInput : PublicInput
  inputValue : PublicInput
  inputBridgeName : Digest
  outputCommitment : SpendScalar
  resourceEffects : List SpendEffect
  footprint : Unit
  nullifier : Option SpendScalar
  modeEvidencePins : ModeEvidencePins
deriving Countable, Nonempty

def requestWire (request : SpendRequest) : RequestWire where
  program := request.program
  relation := request.relation
  canonicalInput := request.canonicalInput
  computationInput := request.computationInput
  inputValue := request.inputValue
  inputBridgeName := request.inputBridgeName
  outputCommitment := request.outputCommitment
  resourceEffects := request.resourceEffects
  footprint := request.footprint
  nullifier := request.nullifier
  modeEvidencePins := request.modeEvidencePins

def requestOfWire (wire : RequestWire) : SpendRequest where
  program := wire.program
  relation := wire.relation
  canonicalInput := wire.canonicalInput
  computationInput := wire.computationInput
  inputValue := wire.inputValue
  inputBridgeName := wire.inputBridgeName
  outputCommitment := wire.outputCommitment
  resourceEffects := wire.resourceEffects
  footprint := wire.footprint
  nullifier := wire.nullifier
  modeEvidencePins := wire.modeEvidencePins

@[simp] theorem requestOfWire_requestWire (request : SpendRequest) :
    requestOfWire (requestWire request) = request := by
  cases request
  rfl

instance : Countable SpendRequest := by
  exact (show Function.Injective requestWire from by
    intro left right same
    rw [← requestOfWire_requestWire left, ← requestOfWire_requestWire right,
      same]).countable

instance : Nonempty SpendRequest :=
  Nonempty.map requestOfWire (inferInstance : Nonempty RequestWire)

structure ResultWire where
  outputRepresentation : OutputRepresentation
  privateOutput : Unit
deriving Countable, Nonempty

def resultWire (result : SpendResult) : ResultWire where
  outputRepresentation := result.outputRepresentation
  privateOutput := result.privateOutput

def resultOfWire (wire : ResultWire) : SpendResult where
  outputRepresentation := wire.outputRepresentation
  privateOutput := wire.privateOutput

@[simp] theorem resultOfWire_resultWire (result : SpendResult) :
    resultOfWire (resultWire result) = result := by
  cases result
  rfl

instance : Countable SpendResult := by
  exact (show Function.Injective resultWire from by
    intro left right same
    rw [← resultOfWire_resultWire left, ← resultOfWire_resultWire right,
      same]).countable

instance : Nonempty SpendResult :=
  Nonempty.map resultOfWire (inferInstance : Nonempty ResultWire)

noncomputable def requestCodec : LawfulCodec SpendRequest :=
  codecOfCountable SpendRequest

noncomputable def resultCodec : LawfulCodec SpendResult :=
  codecOfCountable SpendResult

abbrev EffectIntent := List SpendEffect × Unit × Option SpendScalar

noncomputable def effectIntentCodec : LawfulCodec EffectIntent :=
  codecOfCountable EffectIntent

abbrev cshake := backend.cshake

def requestDigestCustomization : List UInt8 :=
  "minidregg/note-spend/core-request/v1".toUTF8.toList

def effectDigestCustomization : List UInt8 :=
  "minidregg/note-spend/effect-intent/v1".toUTF8.toList

def requestDigestBytes (bytes : List UInt8) : Digest :=
  cshake.xofDigest requestDigestCustomization bytes

def effectDigestBytes (bytes : List UInt8) : Digest :=
  cshake.xofDigest effectDigestCustomization bytes

/-- The demo relation's public root is a `ZMod 13` value.  This explicit
embedding is the adapter's pre-root interpretation; no collision or binding
claim is inferred from it. -/
def rootDigest (root : SpendScalar) : Digest :=
  ⟨root.val⟩

def cellValue (request : SpendRequest) (result : SpendResult) : CellValue where
  effects := request.resourceEffects
  requestOutputCommitment := request.outputCommitment
  outputRepresentation := result.outputRepresentation

/-- One exact singleton patch.  The result is retained in the cell value, but
only a checked completion may later identify it with the request commitment. -/
def spendPatch (request : SpendRequest) (result : SpendResult) :
    CellState.Patch schema Digest where
  expectedPreRoot := rootDigest request.inputValue.root
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some (cellValue request result) }]
  resourceWrites := []

/-- Exact realization relation used by the generic kernel adapter.  It says
only that this is the one patch constructed from these exact request/result
values; semantic request restrictions are retained by the accepted wrapper. -/
def RealizesResourceEffects (request : SpendRequest) (result : SpendResult)
    (patch : CellState.Patch schema Digest) : Prop :=
  patch = spendPatch request result

noncomputable def adapter :
    ComputationCellEffect.Adapter (S := schema) declaration where
  requestCodec := requestCodec
  resultCodec := resultCodec
  requestDigestBytes := requestDigestBytes
  effectIntentCodec := effectIntentCodec
  effectDigestBytes := effectDigestBytes
  patch := spendPatch
  fieldFootprint := fun _ => {()}
  resourceFootprint := fun _ => ∅
  RealizesResourceEffects := RealizesResourceEffects
  resourceEffectsRealized := by
    intro request result
    rfl
  fieldFootprintExact := by
    intro request result
    rfl
  resourceFootprintExact := by
    intro request result
    rfl

@[simp] theorem adapter_patch (request : SpendRequest) (result : SpendResult) :
    adapter.patch request result = spendPatch request result :=
  rfl

@[simp] theorem adapter_completeRequestDigest (request : SpendRequest) :
    adapter.completeRequestDigest request =
      requestDigestBytes (requestCodec.encode request) :=
  rfl

@[simp] theorem adapter_completeEffectDigest (request : SpendRequest) :
    adapter.completeEffectDigest request =
      effectDigestBytes (effectIntentCodec.encode
        (request.resourceEffects, request.footprint, request.nullifier)) :=
  rfl

/-! ## The sole positive construction -/

/-- A concrete note spend enters the common kernel through the existing
positive constructor.  `authorization` is the only transition-authority
argument; every other premise is exact data, checked completion, or validated
patch evidence. -/
def accept
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (authorization : Authorized portal authState commonRequest)
    (argsDigestBound :
      commonRequest.argsDigest = adapter.completeRequestDigest request)
    (effectsDigestBound :
      commonRequest.effectsDigest = adapter.completeEffectDigest request)
    (preRootBound : commonRequest.preStateRoot = pre.root)
    (completion : declaration.Completion request result)
    (resourceEffectsExact : request.resourceEffects = [intendedEffect request])
    (eagerNullifierExact : request.nullifier = some request.inputValue.nullifier)
    (validated : CellState.ValidatedPatch M pre
      (adapter.patch request result)) :
    Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result :=
  NoteSpendCoreAcceptedCellEffect.accept adapter authorization
    argsDigestBound effectsDigestBound preRootBound completion
    resourceEffectsExact eagerNullifierExact validated

/-! ## Exact patch and kernel bindings -/

theorem accepted_preRoot_exact
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    pre.root = rootDigest request.inputValue.root := by
  have bound := accepted.computation.cellEffect.validated.preRoot_bound
  exact bound.symm

theorem accepted_commonPreRoot_exact
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    commonRequest.preStateRoot = rootDigest request.inputValue.root :=
  accepted.computation.cellEffect.preRootBound.trans
    (accepted_preRoot_exact accepted)

theorem accepted_cellValue_exact
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    cellValue request result =
      { effects := [intendedEffect request]
        requestOutputCommitment := request.outputCommitment
        outputRepresentation := ⟨request.outputCommitment⟩ } := by
  have relationExact := accepted_relation accepted
  have outputExact : result.outputRepresentation.commitment =
      request.outputCommitment := relationExact.2.2.2.2.2.2.1
  rcases result with ⟨⟨commitment⟩, privateOutput⟩
  change commitment = request.outputCommitment at outputExact
  subst commitment
  simp [cellValue, accepted.resourceEffectsExact]

theorem accepted_patch_exact
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    adapter.patch request result =
      { expectedPreRoot := rootDigest request.inputValue.root
        fieldFootprint := {()}
        resourceFootprint := ∅
        fieldWrites := [{
          field := ()
          value := some {
            effects := [intendedEffect request]
            requestOutputCommitment := request.outputCommitment
            outputRepresentation := ⟨request.outputCommitment⟩ } }]
        resourceWrites := [] } := by
  rw [adapter_patch]
  unfold spendPatch
  rw [accepted_cellValue_exact accepted]

/-! ## Mismatch, replay, and disclosure teeth -/

theorem no_accepted_of_args_mismatch
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (mismatch : commonRequest.argsDigest ≠
      adapter.completeRequestDigest request) :
    IsEmpty (Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :=
  ⟨fun accepted => mismatch accepted.computation.argsDigestBound⟩

theorem no_accepted_of_effects_mismatch
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (mismatch : commonRequest.effectsDigest ≠
      adapter.completeEffectDigest request) :
    IsEmpty (Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :=
  ⟨fun accepted => mismatch accepted.computation.cellEffect.effectsDigestBound⟩

theorem no_accepted_of_preRoot_mismatch
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (mismatch : commonRequest.preStateRoot ≠
      rootDigest request.inputValue.root) :
    IsEmpty (Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :=
  ⟨fun accepted => mismatch (accepted_commonPreRoot_exact accepted)⟩

theorem no_accepted_of_resourceEffects_mismatch
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (mismatch : request.resourceEffects ≠ [intendedEffect request]) :
    IsEmpty (Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :=
  ⟨fun accepted => mismatch accepted.resourceEffectsExact⟩

theorem no_accepted_of_nullifier_mismatch
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (mismatch : request.nullifier ≠ some request.inputValue.nullifier) :
    IsEmpty (Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :=
  ⟨fun accepted => mismatch accepted.eagerNullifierExact⟩

theorem no_accepted_of_outputCommitment_mismatch
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (mismatch : result.outputRepresentation.commitment ≠
      request.outputCommitment) :
    IsEmpty (Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :=
  ⟨fun accepted => mismatch (accepted_relation accepted).2.2.2.2.2.2.1⟩

/-- The same authorized common request cannot be replayed against a cell with
a different canonical root. -/
theorem no_replay_at_different_preRoot
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind}
    {pre replayedPre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result)
    (different : replayedPre.root ≠ pre.root) :
    IsEmpty (Accepted (portal := portal) (authState := authState)
      adapter commonRequest replayedPre request result) := by
  constructor
  intro replayed
  apply different
  exact replayed.computation.cellEffect.preRootBound.symm.trans
    accepted.computation.cellEffect.preRootBound

theorem accepted_disclosure_sealed
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    accepted.computation.cellEffect.disclosure = .sealed :=
  accepted.computation.disclosure_sealed

theorem accepted_has_no_release
    {M : CellState.Materializer schema Digest}
    {request : SpendRequest} {result : SpendResult}
    (release : (ComputationCellEffect.family (M := M) declaration adapter).Release
      request result) : False :=
  ComputationCellEffect.family_no_release declaration adapter request result release

/-! ## Conditional semantic admission stays on this exact cell effect -/

/-- This wrapper has only the semantic receipt as data.  The concrete accepted
cell effect is an index, so admission cannot substitute a second authorization,
patch, request, or pre-state. -/
structure SemanticAcceptedCellEffect
    {Omega : Type} [Fintype Omega]
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result)
    (bound : Minidregg.Compiler.NoteSpendProofController.BoundReflectedSuite
      (CoreJoin.statementOf accepted))
    (ledger : FailureLedger Omega)
    (laws : SameCoinReductionLaws ledger bound)
    (omega : Omega) where
  admitted : CoreJoin.AdmittedReceipt accepted bound ledger laws omega

namespace SemanticAcceptedCellEffect

variable {Omega : Type} [Fintype Omega]
variable {M : CellState.Materializer schema Digest}
variable {portal : Portal} {authState : AuthState} {kind : ResourceKind}
variable {commonRequest : Request kind} {pre : CellState.Materialized M}
variable {request : SpendRequest} {result : SpendResult}
variable {accepted : Accepted (portal := portal) (authState := authState)
  adapter commonRequest pre request result}
variable {bound : Minidregg.Compiler.NoteSpendProofController.BoundReflectedSuite
  (CoreJoin.statementOf accepted)}
variable {ledger : FailureLedger Omega}
variable {laws : SameCoinReductionLaws ledger bound}
variable {omega : Omega}

/-- The sole transition authority remains the token inside the indexed
accepted cell effect. -/
def authorization
    (_semantic : SemanticAcceptedCellEffect accepted bound ledger laws omega) :
    Authorized portal authState commonRequest :=
  accepted.computation.cellEffect.authorization

/-- The exact validated patch is likewise the one already retained by the
accepted cell effect. -/
def validatedPatch
    (_semantic : SemanticAcceptedCellEffect accepted bound ledger laws omega) :
    CellState.ValidatedPatch M pre (adapter.patch request result) :=
  accepted.validatedPatch

theorem validSpend
    (semantic : SemanticAcceptedCellEffect accepted bound ledger laws omega) :
    Minidregg.Compiler.ValidSpend Minidregg.Compiler.demoNfSpec
      Minidregg.Compiler.demoSpec Minidregg.Compiler.demoSpec 0 2 2
      (CoreJoin.statementOf accepted).nullifier
      (CoreJoin.statementOf accepted).root
      (fun i : Fin 2 => semantic.admitted.witness.values
        ⟨2 + i.val, by have := i.isLt; omega⟩) :=
  semantic.admitted.validSpend

theorem disclosure_sealed
    (semantic : SemanticAcceptedCellEffect accepted bound ledger laws omega) :
    accepted.computation.cellEffect.disclosure = .sealed :=
  semantic.admitted.source_sealed

theorem no_release
    (_semantic : SemanticAcceptedCellEffect accepted bound ledger laws omega)
    (release : (ComputationCellEffect.family (M := M) declaration adapter).Release
      request result) : False :=
  accepted_has_no_release release

end SemanticAcceptedCellEffect

/-- The current zero-pinned note-spend request cannot inhabit even this
conditional semantic wrapper.  The concrete patch does not weaken the suite
migration obstruction. -/
theorem no_current_semanticAcceptedCellEffect
    {Omega : Type} [Fintype Omega]
    {M : CellState.Materializer schema Digest}
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {commonRequest : Request kind} {pre : CellState.Materialized M}
    {request : SpendRequest} {result : SpendResult}
    (accepted : Accepted (portal := portal) (authState := authState)
      adapter commonRequest pre request result) :
    ¬∃ bound : Minidregg.Compiler.NoteSpendProofController.BoundReflectedSuite
        (CoreJoin.statementOf accepted),
      ∃ ledger : FailureLedger Omega,
        ∃ laws : SameCoinReductionLaws ledger bound,
          ∃ omega : Omega,
            Nonempty
              (SemanticAcceptedCellEffect accepted bound ledger laws omega) := by
  rintro ⟨bound, -, -, -, -⟩
  exact CoreJoin.statementOf_no_boundReflectedSuite accepted ⟨bound⟩

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.NoteSpendConcreteCellAdapter.accepted_patch_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_patch_exact
/-- info: 'Minidregg.Assurance.NoteSpendConcreteCellAdapter.no_replay_at_different_preRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_replay_at_different_preRoot
/-- info: 'Minidregg.Assurance.NoteSpendConcreteCellAdapter.SemanticAcceptedCellEffect.validSpend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SemanticAcceptedCellEffect.validSpend
/-- info: 'Minidregg.Assurance.NoteSpendConcreteCellAdapter.no_current_semanticAcceptedCellEffect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_current_semanticAcceptedCellEffect

end

end Minidregg.Assurance.NoteSpendConcreteCellAdapter
