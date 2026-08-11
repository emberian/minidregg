/-
# Assurance.MpcSealedCellExecution -- a concrete sealed shared-MPC cell

`PrivateComputationKind.sharedMpc` previously occurred only as an empty branch
or as manifest data.  This module gives that mode one complete semantic subject:

* a three-party, threshold-two declaration with an executable Lean portal;
* an exact input-representation bridge and a declared-quorum agreement relation;
* one typed patch which stores the committed completion, never the private output;
* a concrete `ComputationCellEffect.Adapter`, validated sparse cell, complete
  request-indexed authority, completion, and accepted effect;
* a redacted public receipt which contains neither the core result nor a release;
* rejection teeth for an undersized quorum, a disagreeing quorum member, digest
  substitution, stale-root replay, and output-commitment substitution.

The agreement proved here is deliberately only agreement of the submitted,
portal-checked party views.  It is not malicious-MPC security.  Transcript
hiding, proof of knowledge, authentication soundness, and physical execution
are separate laws and are not fields of `Accepted`.  The output commitment is
an injectivity-free arithmetic tag, not a cryptographic commitment.  The
kernel-internal result retains its semantic private value so Lean can state the
relation; the public receipt below does not project it.  Declassification is
impossible at this boundary because both release carriers are `PEmpty`.
-/
import Theory.AcceptedCellEffect
import Theory.DeployedMaterializerWitness
import Theory.TypedAuthorizationWitness

namespace Minidregg.Assurance.MpcSealedCellExecution

open Minidregg.Theory
open Minidregg.Theory.CellState
open Minidregg.Theory.DeployedMaterializerWitness
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## First-order shared-MPC language -/

abbrev Party := Fin 3

structure Program where
  programId : Digest
deriving DecidableEq, Countable, Nonempty

structure Relation where
  relationId : Digest
deriving DecidableEq, Countable, Nonempty

def program : Program := ⟨⟨3101⟩⟩
def relation : Relation := ⟨⟨3102⟩⟩

/-- The semantic input and its mode-native artifact.  `expectedPreRoot` makes
the canonical cell binding part of the exact computation request.  The shares
are trusted Lean data here; no hiding statement follows from this record. -/
structure SharedInput where
  sessionId : Digest
  expectedPreRoot : Digest
  shares : Party → Nat
deriving DecidableEq, Countable, Nonempty

/-- Public, mode-native output representation. -/
structure OutputArtifact where
  sessionId : Digest
  transcriptDigest : Digest
  commitment : Digest
deriving DecidableEq, Countable, Nonempty

/-- One submitted party view.  `authenticated = true` is a checked bit in the
declared relation, not a theorem about signatures or a network participant. -/
structure PartyView where
  sessionId : Digest
  transcriptDigest : Digest
  output : Nat
  authenticated : Bool
deriving DecidableEq, Countable, Nonempty

/-- Ordinary evidence supplied to the Lean portal. -/
structure Evidence where
  views : Party → PartyView
  quorum : Finset Party
deriving DecidableEq, Countable, Nonempty

/-- Exact first-order state intent. -/
structure MpcEffect where
  sessionId : Digest
  outputCommitment : Digest
  transcriptDigest : Digest
deriving DecidableEq, Countable, Nonempty

/-- Protocol and federation identity.  Nonzero identities are deployment
names, not a cryptographic authentication theorem. -/
structure ModeEvidencePins where
  protocolId : Digest
  federationId : Digest
  transcriptAuthenticationId : Digest
  partyCount : Nat
  threshold : Nat
deriving DecidableEq, Countable, Nonempty

def pins : ModeEvidencePins where
  protocolId := ⟨3110⟩
  federationId := ⟨3111⟩
  transcriptAuthenticationId := ⟨3112⟩
  partyCount := 3
  threshold := 2

theorem pins_shape :
    pins.protocolId ≠ ⟨0⟩ ∧
      pins.federationId ≠ ⟨0⟩ ∧
      pins.transcriptAuthenticationId ≠ ⟨0⟩ ∧
      pins.partyCount = 3 ∧ pins.threshold = 2 := by
  decide

/-- Only the shared-MPC branch is inhabited. -/
def language : PrivateComputationLanguage where
  Program := fun
    | .witnessZk => PEmpty
    | .sharedMpc => Program
    | .encryptedRnsFhe => PEmpty
  InputArtifact := fun
    | .witnessZk => PEmpty
    | .sharedMpc => SharedInput
    | .encryptedRnsFhe => PEmpty
  OutputArtifact := fun
    | .witnessZk => PEmpty
    | .sharedMpc => OutputArtifact
    | .encryptedRnsFhe => PEmpty
  Evidence := fun
    | .witnessZk => PEmpty
    | .sharedMpc => Evidence
    | .encryptedRnsFhe => PEmpty

abbrev Statement :=
  CoreStatement language .sharedMpc Relation SharedInput Digest Nat
    ModeEvidencePins

def reconstructed (input : SharedInput) : Nat :=
  input.shares ⟨0, by decide⟩ +
    input.shares ⟨1, by decide⟩ +
    input.shares ⟨2, by decide⟩

/-- Arithmetic tag used only to bind this concrete witness.  No collision or
hiding property is claimed. -/
def outputTag (session transcript : Digest) (output : Nat) : Digest :=
  ⟨session.value + transcript.value + output⟩

/-- Agreement of the submitted quorum views.  This is the precise agreement
the executable portal checks. -/
def DeclaredQuorumAgreement (statement : Statement) (evidence : Evidence) : Prop :=
  statement.modeEvidencePins.threshold ≤ evidence.quorum.card ∧
    ∀ party, party ∈ evidence.quorum →
      (evidence.views party).authenticated = true ∧
      (evidence.views party).sessionId = statement.inputValue.sessionId ∧
      (evidence.views party).transcriptDigest =
        statement.outputArtifact.transcriptDigest ∧
      (evidence.views party).output = statement.privateOutput

/-- The exact semantic relation.  It proves arithmetic correctness and
declared-view quorum agreement, not hiding, PoK, malicious agreement, or
executor conformance. -/
def Accepts (statement : Statement) (evidence : Evidence) : Prop :=
  statement.program = program ∧
  statement.relation = relation ∧
  statement.modeEvidencePins = pins ∧
  statement.inputArtifact = statement.inputValue ∧
  statement.outputArtifact.sessionId = statement.inputValue.sessionId ∧
  statement.privateOutput = reconstructed statement.inputValue ∧
  statement.outputCommitment = statement.outputArtifact.commitment ∧
  statement.outputArtifact.commitment =
    outputTag statement.inputValue.sessionId
      statement.outputArtifact.transcriptDigest statement.privateOutput ∧
  DeclaredQuorumAgreement statement evidence

noncomputable def evidencePortal : PrivateEvidencePortal Statement Evidence := by
  classical
  exact {
    verify := fun statement evidence => decide (Accepts statement evidence)
    Accepts := Accepts
    accepted_law := by
      intro statement evidence accepted
      exact of_decide_eq_true accepted
  }

def inputBridge : NamedRepresentationBridge Digest SharedInput Unit
    SharedInput Unit SharedInput where
  name := ⟨3120⟩
  verifySource := fun artifact _ value => decide (artifact = value)
  verifyTarget := fun artifact _ value => decide (artifact = value)

def declaration : ComputationDeclaration language .sharedMpc Relation Digest
    SharedInput SharedInput Unit Unit Digest Nat MpcEffect Unit Digest
    ModeEvidencePins where
  inputBridge := inputBridge
  computationPortal := evidencePortal

abbrev MpcRequest := declaration.Request
abbrev MpcResult := declaration.Result

/-! ## Concrete sparse cell and adapter -/

/-- The canonical cell stores committed completion data and effect intent.  It
has deliberately no `privateOutput : Nat` field. -/
structure StoredCompletion where
  sessionId : Digest
  outputCommitment : Digest
  transcriptDigest : Digest
  effects : List MpcEffect
deriving DecidableEq, Countable, Nonempty

def schema : CellState.Schema where
  Field := Unit
  FieldType := fun _ => StoredCompletion
  Resource := Empty
  ResourceType := Empty.elim
  Authority := Empty.elim
  Evidence := Empty.elim

instance : DecidableEq schema.Field := inferInstanceAs (DecidableEq Unit)
instance : DecidableEq schema.Resource := fun resource => resource.elim
instance : Countable schema.Field := inferInstanceAs (Countable Unit)
instance (_field : schema.Field) : Countable (schema.FieldType _field) :=
  inferInstanceAs (Countable StoredCompletion)

noncomputable def materializer : CellState.Materializer schema Digest :=
  materializerOfCountable schema Empty.elim

noncomputable def pre : CellState.Materialized materializer :=
  CellState.materialize materializer (emptyLogical schema Empty.elim)

def storedCompletion (request : MpcRequest) (result : MpcResult) :
    StoredCompletion where
  sessionId := request.inputValue.sessionId
  outputCommitment := result.outputRepresentation.commitment
  transcriptDigest := result.outputRepresentation.transcriptDigest
  effects := request.resourceEffects

def sealedPatch (request : MpcRequest) (result : MpcResult) :
    CellState.Patch schema Digest where
  expectedPreRoot := request.inputValue.expectedPreRoot
  fieldFootprint := {()}
  resourceFootprint := ∅
  fieldWrites := [{ field := (), value := some (storedCompletion request result) }]
  resourceWrites := []

def RealizesResourceEffects (request : MpcRequest) (result : MpcResult)
    (patch : CellState.Patch schema Digest) : Prop :=
  patch = sealedPatch request result ∧
    (storedCompletion request result).effects = request.resourceEffects

/-! ### Lawful carrier codecs

These countable-carrier codecs prove that the adapter is constructible.  They
are not a stable wire format and are not manifest pins. -/

structure RequestWire where
  program : Program
  relation : Relation
  canonicalInput : SharedInput
  computationInput : SharedInput
  inputValue : SharedInput
  inputBridgeName : Digest
  outputCommitment : Digest
  resourceEffects : List MpcEffect
  footprint : Unit
  nullifier : Option Digest
  modeEvidencePins : ModeEvidencePins
deriving Countable, Nonempty

def requestWire (request : MpcRequest) : RequestWire where
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

def requestOfWire (wire : RequestWire) : MpcRequest where
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

@[simp] theorem requestOfWire_requestWire (request : MpcRequest) :
    requestOfWire (requestWire request) = request := by
  cases request
  rfl

instance : Countable MpcRequest := by
  exact (show Function.Injective requestWire from by
    intro left right same
    rw [← requestOfWire_requestWire left, ← requestOfWire_requestWire right,
      same]).countable

instance : Nonempty MpcRequest :=
  Nonempty.map requestOfWire (inferInstance : Nonempty RequestWire)

structure ResultWire where
  outputRepresentation : OutputArtifact
  privateOutput : Nat
deriving Countable, Nonempty

def resultWire (result : MpcResult) : ResultWire where
  outputRepresentation := result.outputRepresentation
  privateOutput := result.privateOutput

def resultOfWire (wire : ResultWire) : MpcResult where
  outputRepresentation := wire.outputRepresentation
  privateOutput := wire.privateOutput

@[simp] theorem resultOfWire_resultWire (result : MpcResult) :
    resultOfWire (resultWire result) = result := by
  cases result
  rfl

instance : Countable MpcResult := by
  exact (show Function.Injective resultWire from by
    intro left right same
    rw [← resultOfWire_resultWire left, ← resultOfWire_resultWire right, same]).countable

instance : Nonempty MpcResult :=
  Nonempty.map resultOfWire (inferInstance : Nonempty ResultWire)

noncomputable def requestCodec : LawfulCodec MpcRequest :=
  codecOfCountable MpcRequest

noncomputable def resultCodec : LawfulCodec MpcResult :=
  codecOfCountable MpcResult

abbrev EffectIntent := List MpcEffect × Unit × Option Digest

noncomputable def effectIntentCodec : LawfulCodec EffectIntent :=
  codecOfCountable EffectIntent

/-- Domain-separated but non-cryptographic digest interpretation. -/
def requestDigestBytes (bytes : List UInt8) : Digest :=
  ⟨3200 + bytes.length⟩

/-- Domain-separated but non-cryptographic digest interpretation. -/
def effectDigestBytes (bytes : List UInt8) : Digest :=
  ⟨3300 + bytes.length⟩

noncomputable def adapter :
    ComputationCellEffect.Adapter (S := schema) declaration where
  requestCodec := requestCodec
  resultCodec := resultCodec
  requestDigestBytes := requestDigestBytes
  effectIntentCodec := effectIntentCodec
  effectDigestBytes := effectDigestBytes
  patch := sealedPatch
  fieldFootprint := fun _ => {()}
  resourceFootprint := fun _ => ∅
  RealizesResourceEffects := RealizesResourceEffects
  resourceEffectsRealized := by
    intro request result
    exact ⟨rfl, rfl⟩
  fieldFootprintExact := by
    intro request result
    rfl
  resourceFootprintExact := by
    intro request result
    rfl

/-! ## One complete accepted execution -/

def sessionId : Digest := ⟨3401⟩
def transcriptDigest : Digest := ⟨3402⟩

noncomputable def honestInput : SharedInput where
  sessionId := sessionId
  expectedPreRoot := pre.root
  shares
    | ⟨0, _⟩ => 4
    | ⟨1, _⟩ => 5
    | ⟨2, _⟩ => 6

def honestOutput : Nat := 15

def honestOutputArtifact : OutputArtifact where
  sessionId := sessionId
  transcriptDigest := transcriptDigest
  commitment := outputTag sessionId transcriptDigest honestOutput

def honestView : PartyView where
  sessionId := sessionId
  transcriptDigest := transcriptDigest
  output := honestOutput
  authenticated := true

def honestEvidence : Evidence where
  views := fun _ => honestView
  quorum := Finset.univ

def honestEffect : MpcEffect where
  sessionId := sessionId
  outputCommitment := honestOutputArtifact.commitment
  transcriptDigest := transcriptDigest

noncomputable def honestRequest : MpcRequest where
  program := program
  relation := relation
  canonicalInput := honestInput
  computationInput := honestInput
  inputValue := honestInput
  inputBridgeName := inputBridge.name
  outputCommitment := honestOutputArtifact.commitment
  resourceEffects := [honestEffect]
  footprint := ()
  nullifier := none
  modeEvidencePins := pins

def honestResult : MpcResult where
  outputRepresentation := honestOutputArtifact
  privateOutput := honestOutput

noncomputable def honestCompletion : declaration.Completion honestRequest honestResult where
  inputIdentity := {
    nameBound := rfl
    sourceWitness := ()
    targetWitness := ()
    verified := by simp [NamedRepresentationBridge.verifyIdentity, inputBridge]
  }
  computation := {
    witness := honestEvidence
    verified := by native_decide
  }

theorem honestPatch_accepted :
    ∃ validated : CellState.ValidatedPatch materializer pre
        (adapter.patch honestRequest honestResult),
      CellState.validate materializer pre
          (adapter.patch honestRequest honestResult) =
        CellState.ValidationOutcome.accepted validated := by
  unfold CellState.validate
  rw [dif_pos (show
    (adapter.patch honestRequest honestResult).expectedPreRoot = pre.root from rfl)]
  rw [dif_pos (show
    (adapter.patch honestRequest honestResult).fieldFootprint =
      (adapter.patch honestRequest honestResult).namedFields by decide)]
  rw [dif_pos (show
    (adapter.patch honestRequest honestResult).resourceFootprint =
      (adapter.patch honestRequest honestResult).namedResources by decide)]
  exact ⟨_, rfl⟩

noncomputable def validated :
    CellState.ValidatedPatch materializer pre
      (adapter.patch honestRequest honestResult) :=
  honestPatch_accepted.choose

noncomputable def commonRequest : Request .object :=
  { Minidregg.Theory.TypedAuthorizationWitness.request with
    semantics := ⟨3410⟩
    target := ⟨3411⟩
    argsDigest := adapter.completeRequestDigest honestRequest
    effectsDigest := adapter.completeEffectDigest honestRequest
    nonce := 3412
    preStateRoot := pre.root }

noncomputable def authorization :
    Authorized Minidregg.Theory.TypedAuthorizationWitness.permissivePortal
      Minidregg.Theory.TypedAuthorizationWitness.authState commonRequest where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

/-- The missing positive shared-MPC kernel subject. -/
noncomputable def accepted :
    ComputationCellEffect.Accepted
      (portal := Minidregg.Theory.TypedAuthorizationWitness.permissivePortal)
      (authState := Minidregg.Theory.TypedAuthorizationWitness.authState)
      declaration adapter commonRequest pre honestRequest honestResult :=
  ComputationCellEffect.accept declaration adapter authorization
    rfl rfl rfl honestCompletion validated

theorem accepted_nonempty : Nonempty
    (ComputationCellEffect.Accepted
      (portal := Minidregg.Theory.TypedAuthorizationWitness.permissivePortal)
      (authState := Minidregg.Theory.TypedAuthorizationWitness.authState)
      declaration adapter commonRequest pre honestRequest honestResult) :=
  ⟨accepted⟩

/-! ## Exact positive semantics and the public sealed receipt -/

theorem accepted_declared_quorum_agreement :
    DeclaredQuorumAgreement
      (declaration.statementOf honestRequest honestResult) honestEvidence := by
  have semantic := accepted.cellEffect.modeEvidence.computation.accepts
  exact semantic.2.2.2.2.2.2.2.2

theorem accepted_private_output_exact :
    honestResult.privateOutput = reconstructed honestRequest.inputValue := by
  have semantic := accepted.cellEffect.modeEvidence.computation.accepts
  exact semantic.2.2.2.2.2.1.symm

theorem accepted_output_commitment_exact :
    honestResult.outputRepresentation.commitment =
      outputTag honestRequest.inputValue.sessionId
        honestResult.outputRepresentation.transcriptDigest
        honestResult.privateOutput := by
  have semantic := accepted.cellEffect.modeEvidence.computation.accepts
  exact semantic.2.2.2.2.2.2.2.2.1

theorem accepted_patch_stores_committed_completion :
    adapter.patch honestRequest honestResult =
      { expectedPreRoot := pre.root
        fieldFootprint := {()}
        resourceFootprint := ∅
        fieldWrites := [{
          field := ()
          value := some {
            sessionId := sessionId
            outputCommitment := honestOutputArtifact.commitment
            transcriptDigest := transcriptDigest
            effects := [honestEffect] } }]
        resourceWrites := [] } := by
  rfl

theorem accepted_disclosure_sealed :
    accepted.cellEffect.disclosure = .sealed :=
  accepted.disclosure_sealed

theorem accepted_has_no_release
    (release : (ComputationCellEffect.family (M := materializer)
      declaration adapter).Release honestRequest honestResult) : False :=
  ComputationCellEffect.family_no_release declaration adapter
    honestRequest honestResult release

theorem accepted_has_no_declassification_authority
    (authority : (ComputationCellEffect.family (M := materializer)
      declaration adapter).DeclassificationAuthority honestRequest honestResult) :
    False :=
  nomatch authority

/-- External receipt for a sealed computation.  Unlike the generic internal
semantic event, this carrier deliberately omits `MpcResult`, `Evidence`, and
therefore `privateOutput`. -/
structure PublicSealedReceipt where
  sessionId : Digest
  protocolId : Digest
  federationId : Digest
  partyCount : Nat
  threshold : Nat
  transcriptDigest : Digest
  outputCommitment : Digest
  effectDigest : Digest
  preRoot : Digest
  postRoot : Digest
deriving DecidableEq, Countable, Nonempty

noncomputable def publicReceipt : PublicSealedReceipt where
  sessionId := honestRequest.inputValue.sessionId
  protocolId := honestRequest.modeEvidencePins.protocolId
  federationId := honestRequest.modeEvidencePins.federationId
  partyCount := honestRequest.modeEvidencePins.partyCount
  threshold := honestRequest.modeEvidencePins.threshold
  transcriptDigest := honestResult.outputRepresentation.transcriptDigest
  outputCommitment := honestResult.outputRepresentation.commitment
  effectDigest := adapter.completeEffectDigest honestRequest
  preRoot := pre.root
  postRoot := accepted.cellEffect.prepared.postRoot

noncomputable def publicReceiptCodec : LawfulCodec PublicSealedReceipt :=
  codecOfCountable PublicSealedReceipt

theorem publicReceipt_exact :
    publicReceipt.sessionId = sessionId ∧
      publicReceipt.protocolId = pins.protocolId ∧
      publicReceipt.federationId = pins.federationId ∧
      publicReceipt.partyCount = 3 ∧
      publicReceipt.threshold = 2 ∧
      publicReceipt.transcriptDigest = transcriptDigest ∧
      publicReceipt.outputCommitment = honestOutputArtifact.commitment ∧
      publicReceipt.effectDigest = commonRequest.effectsDigest ∧
      publicReceipt.preRoot = commonRequest.preStateRoot := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    accepted.cellEffect.effectsDigestBound.symm,
    accepted.cellEffect.preRootBound.symm⟩

/-! ## Explicit executor boundary -/

/-- A bridge from submitted views to physical party runs.  The semantic
accepted token does not construct this structure.  Authentication soundness
and executor conformance belong here, not in declared quorum agreement. -/
structure ExecutorConformance (evidence : Evidence) where
  executed : Party → Prop
  actualOutput : Party → Nat
  actualTranscript : Party → Digest
  quorumExecuted : ∀ party, party ∈ evidence.quorum → executed party
  outputMatches : ∀ party, party ∈ evidence.quorum →
    actualOutput party = (evidence.views party).output
  transcriptMatches : ∀ party, party ∈ evidence.quorum →
    actualTranscript party = (evidence.views party).transcriptDigest

/-- Physical output agreement is conditional on the separate executor bridge.
No such bridge is manufactured by `accepted`. -/
theorem physical_quorum_output_agreement
    (executor : ExecutorConformance honestEvidence)
    {left right : Party}
    (leftMem : left ∈ honestEvidence.quorum)
    (rightMem : right ∈ honestEvidence.quorum) :
    executor.actualOutput left = executor.actualOutput right := by
  rw [executor.outputMatches left leftMem,
    executor.outputMatches right rightMem]
  have agreement := accepted_declared_quorum_agreement
  exact (agreement.2 left leftMem).2.2.2.trans
    (agreement.2 right rightMem).2.2.2.symm

/-! ## Rejection teeth -/

def undersizedEvidence : Evidence where
  views := fun _ => honestView
  quorum := {⟨0, by decide⟩}

theorem undersized_quorum_rejected :
    evidencePortal.verify
      (declaration.statementOf honestRequest honestResult)
      undersizedEvidence = false := by
  native_decide

def disagreeingEvidence : Evidence where
  views := fun party =>
    if party = ⟨0, by decide⟩ then { honestView with output := 16 }
    else honestView
  quorum := Finset.univ

theorem disagreeing_quorum_rejected :
    evidencePortal.verify
      (declaration.statementOf honestRequest honestResult)
      disagreeingEvidence = false := by
  native_decide

theorem no_accepted_of_args_mismatch
    {request : Request .object}
    (mismatch : request.argsDigest ≠
      adapter.completeRequestDigest honestRequest) :
    IsEmpty (ComputationCellEffect.Accepted
      (portal := Minidregg.Theory.TypedAuthorizationWitness.permissivePortal)
      (authState := Minidregg.Theory.TypedAuthorizationWitness.authState)
      declaration adapter request pre honestRequest honestResult) :=
  ⟨fun candidate => mismatch candidate.argsDigestBound⟩

theorem no_accepted_of_effects_mismatch
    {request : Request .object}
    (mismatch : request.effectsDigest ≠
      adapter.completeEffectDigest honestRequest) :
    IsEmpty (ComputationCellEffect.Accepted
      (portal := Minidregg.Theory.TypedAuthorizationWitness.permissivePortal)
      (authState := Minidregg.Theory.TypedAuthorizationWitness.authState)
      declaration adapter request pre honestRequest honestResult) :=
  ⟨fun candidate => mismatch candidate.cellEffect.effectsDigestBound⟩

theorem no_replay_at_different_preRoot
    {replayedPre : CellState.Materialized materializer}
    (different : replayedPre.root ≠ pre.root) :
    IsEmpty (ComputationCellEffect.Accepted
      (portal := Minidregg.Theory.TypedAuthorizationWitness.permissivePortal)
      (authState := Minidregg.Theory.TypedAuthorizationWitness.authState)
      declaration adapter commonRequest replayedPre honestRequest honestResult) := by
  constructor
  intro replayed
  apply different
  exact replayed.cellEffect.preRootBound.symm.trans
    accepted.cellEffect.preRootBound

def wrongCommitmentResult : MpcResult :=
  { honestResult with
    outputRepresentation :=
      { honestResult.outputRepresentation with commitment := ⟨999999⟩ } }

theorem wrong_output_commitment_rejected :
    evidencePortal.verify
      (declaration.statementOf honestRequest wrongCommitmentResult)
      honestEvidence = false := by
  native_decide

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.MpcSealedCellExecution.accepted_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_nonempty
/-- info: 'Minidregg.Assurance.MpcSealedCellExecution.accepted_declared_quorum_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_declared_quorum_agreement
/-- info: 'Minidregg.Assurance.MpcSealedCellExecution.accepted_has_no_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accepted_has_no_release
/-- info: 'Minidregg.Assurance.MpcSealedCellExecution.physical_quorum_output_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms physical_quorum_output_agreement
/-- info: 'Minidregg.Assurance.MpcSealedCellExecution.wrong_output_commitment_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_output_commitment_rejected

end

end Minidregg.Assurance.MpcSealedCellExecution
