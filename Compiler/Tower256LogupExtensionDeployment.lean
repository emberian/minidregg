/-
# Compiler.Tower256LogupExtensionDeployment -- concrete clause-404 carrier

This module closes one executable, extension-local `ControllerInputs` value
for Tower256 LogUp.  It deliberately does not insert clause 404 into base V1.
All columns, work slots, codecs, transcript inputs, and the two-call reply
table are selected by Lean against `Tower256ConcreteBackend.backend`.

The deployment proves deterministic control behavior only.  Merkle position
binding, PCS/sampled-decider soundness, commitment collision resistance,
cSHAKE/ROM transport, common-game history, and mutable-RAM consistency remain
admission residuals.
-/

import Compiler.Tower256LogupClauseDispatch

namespace Minidregg.Compiler.Tower256LogupExtensionDeployment

open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.AuthenticatedColumnLogupBridge
open Minidregg.Compiler.Logup256ReceiptClause
open Minidregg.Compiler.NativeKernelPlan (WorkKind)
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256LogupAcceptedRun
open Minidregg.Compiler.Tower256LogupClauseDispatch
open Minidregg.Compiler.Tower256LogupControllerPlan
open Minidregg.Loom
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

noncomputable section

abbrev Tower256 := BinaryTower256Profile.Tower256
def backend := Tower256ConcreteBackend.backend

local instance tower256DecidableEq : DecidableEq Tower256 := Classical.decEq _

def id (value : Nat) : Digest := Tower256ConcreteBackend.id value

/-! ## Extension identity and versioned pins -/

def controllerId : Digest := clausePin.verifierControllerDigest
def roundWorkSlotId : Digest := id 8901
def queryWorkSlotId : Digest := id 8902
def wrongWorkSlotIdA : Digest := id 8903
def wrongWorkSlotIdB : Digest := id 8904

def rowDomainCodecPin : CodecPin := ⟨id 8910, id 8920, 1⟩
def addressDomainCodecPin : CodecPin := ⟨id 8911, id 8921, 1⟩
def tableDomainCodecPin : CodecPin := ⟨id 8912, id 8922, 1⟩
def checkpointDomainCodecPin : CodecPin := ⟨id 8913, id 8923, 1⟩
def queryWorkInputCodecPin : CodecPin := ⟨id 8914, id 8924, 1⟩

structure VersionedId where
  value : Digest
  version : Nat
  valueAssigned : value ≠ ⟨0⟩
  versionAssigned : version ≠ 0

def controllerPin : VersionedId where
  value := controllerId
  version := 1
  valueAssigned := by decide
  versionAssigned := by decide

def roundWorkPin : VersionedId where
  value := roundWorkSlotId
  version := 1
  valueAssigned := by decide
  versionAssigned := by decide

def queryWorkPin : VersionedId where
  value := queryWorkSlotId
  version := 1
  valueAssigned := by decide
  versionAssigned := by decide

structure ExtensionArtifact where
  clause : DialectClauseDecl
  controllerPin : VersionedId
  transportPins : List CodecPin
  domainPins : List CodecPin
  workPins : List VersionedId
  clauseExact : clause = clausePin
  controllerExact : controllerPin.value = clause.verifierControllerDigest
  transportVersionsAssigned : ∀ pin ∈ transportPins, pin.version ≠ 0
  domainVersionsAssigned : ∀ pin ∈ domainPins, pin.version ≠ 0
  transportCodecIdsUnique : (transportPins.map CodecPin.codecId).Nodup
  domainCodecIdsUnique : (domainPins.map CodecPin.codecId).Nodup
  workSlotIdsUnique : (workPins.map VersionedId.value).Nodup

def artifact : ExtensionArtifact where
  clause := clausePin
  controllerPin := controllerPin
  transportPins :=
    [dispatchInputCodecPin, dispatchQueryCodecPin, dispatchReplyCodecPin]
  domainPins :=
    [rowDomainCodecPin, addressDomainCodecPin, tableDomainCodecPin,
      checkpointDomainCodecPin, queryWorkInputCodecPin]
  workPins := [roundWorkPin, queryWorkPin]
  clauseExact := rfl
  controllerExact := rfl
  transportVersionsAssigned := by simp [dispatchInputCodecPin,
    dispatchQueryCodecPin, dispatchReplyCodecPin]
  domainVersionsAssigned := by simp [rowDomainCodecPin, addressDomainCodecPin,
    tableDomainCodecPin, checkpointDomainCodecPin, queryWorkInputCodecPin]
  transportCodecIdsUnique := transport_codec_ids_unique
  domainCodecIdsUnique := by decide
  workSlotIdsUnique := by decide

/-! ## A small but nonempty concrete indexed lookup -/

abbrev RowLog : Nat := 1
abbrev TableLog : Nat := 1
abbrev CheckpointLog : Nat := 1

def finCodec (size : Nat) : LawfulCodec (Fin size) :=
  AuthenticatedColumnPlan.Tower256Example.finUnaryCodec size

def semanticSpec : AdditiveColumnSpec backend RowLog where
  role := .semanticTrace
  slotId := id 8930
  semanticTypeId := id 8940
  domainId := id 8950
  domainCodecPin := rowDomainCodecPin
  domainCodec := finCodec (2 ^ RowLog)

def addressSpec : AdditiveColumnSpec backend (RowLog + TableLog) where
  role := .lookupAddress
  slotId := id 8931
  semanticTypeId := id 8941
  domainId := id 8951
  domainCodecPin := addressDomainCodecPin
  domainCodec := finCodec (2 ^ (RowLog + TableLog))

def weightsSpec : AdditiveColumnSpec backend RowLog where
  role := .lookupWeight
  slotId := id 8932
  semanticTypeId := id 8942
  domainId := id 8950
  domainCodecPin := rowDomainCodecPin
  domainCodec := finCodec (2 ^ RowLog)

def tableSpec : AdditiveColumnSpec backend TableLog where
  role := .lookupTable
  slotId := id 8933
  semanticTypeId := id 8943
  domainId := id 8952
  domainCodecPin := tableDomainCodecPin
  domainCodec := finCodec (2 ^ TableLog)

def checkpointSpec : AdditiveColumnSpec backend CheckpointLog where
  role := .checkpoint
  slotId := id 8934
  semanticTypeId := id 8944
  domainId := id 8953
  domainCodecPin := checkpointDomainCodecPin
  domainCodec := finCodec (2 ^ CheckpointLog)

def zeroColumn {logSize : Nat} (spec : AdditiveColumnSpec backend logSize) :
    AdditiveColumn spec where
  bound :=
    { semantic := fun _ => 0
      represented := fun _ => 0
      representationExact := fun _ => rfl }

def semanticColumn : AdditiveColumn semanticSpec := zeroColumn semanticSpec
def addressColumn : AdditiveColumn addressSpec := zeroColumn addressSpec
def weightsColumn : AdditiveColumn weightsSpec := zeroColumn weightsSpec
def tableColumn : AdditiveColumn tableSpec := zeroColumn tableSpec
def checkpointColumn : AdditiveColumn checkpointSpec := zeroColumn checkpointSpec

def trace : CommittedSemanticTrace (Fin (2 ^ RowLog)) TableLog where
  semanticTraceRoot := semanticColumn.rootRecord.root
  addressRoot := addressColumn.rootRecord.root
  weightsRoot := weightsColumn.rootRecord.root
  tableRoot := tableColumn.rootRecord.root
  index := fun _ => 0
  addressBits := fun _ => binaryAddressBits TableLog 0

def claim : IndexedTableReceiptClaim Tower256 (Fin (2 ^ RowLog)) TableLog where
  semanticTraceRoot := semanticColumn.rootRecord.root
  addressRoot := addressColumn.rootRecord.root
  weightsRoot := weightsColumn.rootRecord.root
  tableRoot := tableColumn.rootRecord.root
  weights := fun _ => 0
  table := fun _ => 0
  claimedEvaluation := 0

def columns : LogupColumns backend trace claim where
  semanticSpec := semanticSpec
  semanticRole := rfl
  semantic := semanticColumn
  semanticRootExact := rfl
  addressSpec := addressSpec
  addressRole := rfl
  address := addressColumn
  addressRootExact := rfl
  weightsSpec := weightsSpec
  weightsRole := rfl
  weights := weightsColumn
  weightsRootExact := rfl
  tableSpec := tableSpec
  tableRole := rfl
  table := tableColumn
  tableRootExact := rfl

theorem finalStatement : LogupFinalStatement trace claim where
  canonicalAddressLinked := by
    intro row
    rfl
  towerArithmetic := by
    simp [claim, logupDot]
  pcsRootsBound := ⟨rfl, rfl, rfl⟩
  semanticTraceRootBound := rfl

local instance finalStatementDecidable : Decidable (LogupFinalStatement trace claim) :=
  isTrue finalStatement

@[simp] theorem finalStatement_decide :
    decide (LogupFinalStatement trace claim) = true := by
  exact decide_eq_true finalStatement

/-! ## Exact opaque work calls -/

def queryWorkInputCodec : LawfulCodec (Digest × Digest) :=
  (Tower256ConcreteBackend.StreamCodec.product
    Tower256ConcreteBackend.digestStream
    Tower256ConcreteBackend.digestStream).toLawful

def roundCall (roundChallenge : Digest) : NativeCall where
  Input := Digest
  Output := Tower256
  outputDecidableEq := inferInstance
  callSlotId := roundWorkSlotId
  kind := .arithmetic
  carrierProfileId := backend.tower.carrier.id
  inputCodecPin := backend.cshake.digestCodecPin
  outputCodecPin := backend.tower.valueCodecPin
  inputCodec := backend.cshake.digestCodec
  outputCodec := backend.tower.valueCodec
  input := roundChallenge
  claimedOutput := 0
  leanCheck := fun _ output => decide (output = 0)

def queryCall (roundChallenge queryChallenge : Digest) : NativeCall where
  Input := Digest × Digest
  Output := Tower256
  outputDecidableEq := inferInstance
  callSlotId := queryWorkSlotId
  kind := .arithmetic
  carrierProfileId := backend.tower.carrier.id
  inputCodecPin := queryWorkInputCodecPin
  outputCodecPin := backend.tower.valueCodecPin
  inputCodec := queryWorkInputCodec
  outputCodec := backend.tower.valueCodec
  input := (roundChallenge, queryChallenge)
  claimedOutput := 0
  leanCheck := fun _ output => decide (output = 0)

def digestIndex (value : Digest) : Fin 2 :=
  ⟨value.value % 2, Nat.mod_lt _ (by decide)⟩

def transcriptDomain : Digest := id 8960
def tableOpeningSlotId : Digest := id 8961
def checkpointOpeningSlotId : Digest := id 8962
def finalCheckerId : Digest := id 8963

def inputs : SharedInputs RowLog TableLog CheckpointLog trace claim where
  transcriptDomain := transcriptDomain
  publicContext := [0x4c, 0x4f, 0x47, 0x55, 0x50, 0x2f, 0x34, 0x30, 0x34]
  columns := columns
  roundCall := roundCall
  checkpointSpec := checkpointSpec
  checkpointRole := rfl
  checkpoint := fun _ => checkpointColumn
  queryCall := queryCall
  tableOpeningSlotId := tableOpeningSlotId
  tableQueryIndex := digestIndex
  checkpointOpeningSlotId := checkpointOpeningSlotId
  checkpointQueryIndex := digestIndex
  finalCheckerId := finalCheckerId

@[simp] theorem issuedQuery_clause (input : DispatchInput) :
    (issuedQuery inputs input).clauseId = clausePin.clauseId := rfl

@[simp] theorem issuedQuery_controller (input : DispatchInput) :
    (issuedQuery inputs input).controllerDigest = controllerId := rfl

@[simp] theorem issuedQuery_context (input : DispatchInput) :
    (issuedQuery inputs input).publicContext = inputs.publicContext := rfl

@[simp] theorem issuedQuery_seed (input : DispatchInput) :
    (issuedQuery inputs input).seed = input.seed := rfl

/-! ## Canonical reply tables and controller rejection -/

def zeroWorkBytes : List UInt8 := backend.tower.valueCodec.encode 0

def honestReply : DispatchReply :=
  ⟨[⟨roundWorkSlotId, zeroWorkBytes⟩,
    ⟨queryWorkSlotId, zeroWorkBytes⟩]⟩

def wrongCountReply : DispatchReply :=
  ⟨[⟨roundWorkSlotId, zeroWorkBytes⟩]⟩

def duplicateReply : DispatchReply :=
  ⟨[⟨roundWorkSlotId, zeroWorkBytes⟩,
    ⟨roundWorkSlotId, zeroWorkBytes⟩]⟩

/-- The round slot is present, but the required query slot is missing. -/
def missingReply : DispatchReply :=
  ⟨[⟨roundWorkSlotId, zeroWorkBytes⟩,
    ⟨wrongWorkSlotIdA, zeroWorkBytes⟩]⟩

/-- Both table entries use unique but entirely wrong slots. -/
def wrongSlotReply : DispatchReply :=
  ⟨[⟨wrongWorkSlotIdA, zeroWorkBytes⟩,
    ⟨wrongWorkSlotIdB, zeroWorkBytes⟩]⟩

@[simp] theorem inputs_roundCall (challenge : Digest) :
    inputs.roundCall challenge = roundCall challenge := rfl

@[simp] theorem inputs_queryCall (roundChallenge queryChallenge : Digest) :
    inputs.queryCall roundChallenge queryChallenge =
      queryCall roundChallenge queryChallenge := rfl

@[simp] theorem inputs_checkpoint (challenge : Digest) :
    inputs.checkpoint challenge = checkpointColumn := rfl

@[simp] theorem roundCall_accepts (challenge : Digest) :
    (roundCall challenge).acceptsReply zeroWorkBytes = true := by
  simp only [roundCall, NativeCall.acceptsReply, zeroWorkBytes,
    LawfulCodec.decode_encode, decide_true, Bool.true_and]

@[simp] theorem queryCall_accepts (roundChallenge queryChallenge : Digest) :
    (queryCall roundChallenge queryChallenge).acceptsReply zeroWorkBytes = true := by
  simp only [queryCall, NativeCall.acceptsReply, zeroWorkBytes,
    LawfulCodec.decode_encode, decide_true, Bool.true_and]

@[simp] theorem honestReply_runs_round (challenge : Digest) :
    honestReply.runner (roundCall challenge) = .ok zeroWorkBytes := by
  simp [honestReply, DispatchReply.runner, DispatchReply.lookup, roundCall,
    roundWorkSlotId, queryWorkSlotId, id, Tower256ConcreteBackend.id]

@[simp] theorem honestReply_runs_query (roundChallenge queryChallenge : Digest) :
    honestReply.runner (queryCall roundChallenge queryChallenge) =
      .ok zeroWorkBytes := by
  simp [honestReply, DispatchReply.runner, DispatchReply.lookup, queryCall,
    roundWorkSlotId, queryWorkSlotId, id, Tower256ConcreteBackend.id]

@[simp] theorem wrongSlotReply_misses_round (challenge : Digest) :
    wrongSlotReply.runner (roundCall challenge) =
      .error (.missingReply roundWorkSlotId) := by
  simp [wrongSlotReply, DispatchReply.runner, DispatchReply.lookup, roundCall,
    roundWorkSlotId, wrongWorkSlotIdA, wrongWorkSlotIdB, id,
    Tower256ConcreteBackend.id]

@[simp] theorem missingReply_runs_round (challenge : Digest) :
    missingReply.runner (roundCall challenge) = .ok zeroWorkBytes := by
  simp [missingReply, DispatchReply.runner, DispatchReply.lookup, roundCall,
    roundWorkSlotId, wrongWorkSlotIdA, id, Tower256ConcreteBackend.id]

@[simp] theorem missingReply_misses_query
    (roundChallenge queryChallenge : Digest) :
    missingReply.runner (queryCall roundChallenge queryChallenge) =
      .error (.missingReply queryWorkSlotId) := by
  simp [missingReply, DispatchReply.runner, DispatchReply.lookup, queryCall,
    roundWorkSlotId, queryWorkSlotId, wrongWorkSlotIdA, id,
    Tower256ConcreteBackend.id]

@[simp] theorem wrongCount_blocks (input : DispatchInput) :
    checkReply inputs input wrongCountReply =
      .blocked (.wrongReplyCount 1) := by
  apply wrong_reply_count_blocks
  decide

@[simp] theorem duplicate_blocks (input : DispatchInput) :
    checkReply inputs input duplicateReply =
      .blocked .duplicateReplySlot := by
  apply duplicate_reply_slot_blocks
  · decide
  · decide

theorem honestReply_isVerified (input : DispatchInput) :
    (checkReply inputs input honestReply).IsVerified := by
  have countExact : honestReply.nativeReplies.length = 2 := by decide
  have unique : honestReply.slotIds.Nodup := by decide
  simp only [checkReply, countExact, unique, ↓reduceDIte]
  simp [ControllerInputs.execute, AuthenticatedColumnPlan.execute,
    ControllerInputs.plan, AuthenticatedColumnPlan.run,
    logupFinalChecker, Outcome.IsVerified]

@[simp] theorem wrongSlot_blocks (input : DispatchInput) :
    checkReply inputs input wrongSlotReply =
      .blocked (.missingReply roundWorkSlotId) := by
  have countExact : wrongSlotReply.nativeReplies.length = 2 := by decide
  have unique : wrongSlotReply.slotIds.Nodup := by decide
  simp only [checkReply, countExact, unique, ↓reduceDIte]
  simp [ControllerInputs.execute, AuthenticatedColumnPlan.execute,
    ControllerInputs.plan, AuthenticatedColumnPlan.run]

@[simp] theorem missing_blocks (input : DispatchInput) :
    checkReply inputs input missingReply =
      .blocked (.missingReply queryWorkSlotId) := by
  have countExact : missingReply.nativeReplies.length = 2 := by decide
  have unique : missingReply.slotIds.Nodup := by decide
  simp only [checkReply, countExact, unique, ↓reduceDIte]
  simp [ControllerInputs.execute, AuthenticatedColumnPlan.execute,
    ControllerInputs.plan, AuthenticatedColumnPlan.run]

/-! ## Raw bytes/error framing -/

abbrev OpaqueDispatchRunner (Error : Type) :=
  List UInt8 -> Except Error (List UInt8)

inductive RawFailure (Error : Type)
  | native (error : Error)
  | invalidEncoding
deriving Repr

def runRaw {Error : Type} (runner : OpaqueDispatchRunner Error)
    (input : DispatchInput) :
    Except (RawFailure Error)
      (Outcome DispatchFailure backend.transcript.portal inputs.transcriptDomain) :=
  match runner (dispatchQueryCodec.encode (issuedQuery inputs input)) with
  | .error error => .error (.native error)
  | .ok bytes =>
      match dispatchReplyCodec.decode bytes with
      | none => .error .invalidEncoding
      | some reply => .ok (checkReply inputs input reply)

def nativeErrorRunner {Error : Type} (error : Error) : OpaqueDispatchRunner Error :=
  fun _ => .error error

@[simp] theorem native_error_rejects {Error : Type} (error : Error)
    (input : DispatchInput) :
    runRaw (nativeErrorRunner error) input = .error (.native error) := by
  simp [runRaw, nativeErrorRunner]

@[simp] theorem invalid_encoding_rejects {Error : Type}
    (runner : OpaqueDispatchRunner Error) (input : DispatchInput)
    (bytes : List UInt8)
    (returned : runner (dispatchQueryCodec.encode (issuedQuery inputs input)) =
      .ok bytes)
    (malformed : dispatchReplyCodec.decode bytes = none) :
    runRaw runner input = .error .invalidEncoding := by
  unfold runRaw
  rw [returned]
  simp only
  rw [malformed]

/-- Raw success retains the exact issued query, decoded reply, and reflected
controller outcome. -/
theorem runRaw_success_integrity {Error : Type}
    (runner : OpaqueDispatchRunner Error) (input : DispatchInput)
    (outcome : Outcome DispatchFailure backend.transcript.portal
      inputs.transcriptDomain)
    (success : runRaw runner input = .ok outcome) :
    ∃ bytes reply,
      runner (dispatchQueryCodec.encode (issuedQuery inputs input)) = .ok bytes ∧
      dispatchReplyCodec.decode bytes = some reply ∧
      checkReply inputs input reply = outcome := by
  unfold runRaw at success
  split at success
  · contradiction
  · rename_i bytes runnerExact
    split at success
    · contradiction
    · rename_i reply decoded
      exact ⟨bytes, reply, runnerExact, decoded, Except.ok.inj success⟩

def honestRawRunner : OpaqueDispatchRunner Empty :=
  fun _ => .ok (dispatchReplyCodec.encode honestReply)

theorem honestRaw_isVerified (input : DispatchInput) :
    ∃ outcome,
      runRaw honestRawRunner input = .ok outcome ∧ outcome.IsVerified := by
  refine ⟨checkReply inputs input honestReply, ?_, honestReply_isVerified input⟩
  simp only [runRaw, honestRawRunner]
  rw [dispatchReplyCodec.decode_encode]

/-- Concrete specialization of the generic reflection bridge: no semantic
security statement is added, but a verified controller result becomes the
proof-relevant execution trace consumed by admission. -/
noncomputable def acceptedExecution (input : DispatchInput)
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    (attestation : TerminalAttestation backend.transcript.portal
      inputs.transcriptDomain roots draws native openings edges)
    (accepted : checkReply inputs input honestReply = .verified attestation) :
    VerifiedExecution backend trace claim inputs honestReply.runner input.seed :=
  verifiedExecutionOfReply inputs input honestReply attestation accepted

/-! ## Base exclusion and axiom audit -/

theorem clause404_absent_from_base :
    MinidreggV1Artifact.manifest.lookupClause clausePin.clauseId = none :=
  clause404_still_absent_from_base

/-- info: 'Minidregg.Compiler.Tower256LogupExtensionDeployment.honestReply_isVerified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms honestReply_isVerified
/-- info: 'Minidregg.Compiler.Tower256LogupExtensionDeployment.missing_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms missing_blocks
/-- info: 'Minidregg.Compiler.Tower256LogupExtensionDeployment.runRaw_success_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms runRaw_success_integrity
/-- info: 'Minidregg.Compiler.Tower256LogupExtensionDeployment.acceptedExecution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms acceptedExecution
/-- info: 'Minidregg.Compiler.Tower256LogupExtensionDeployment.clause404_absent_from_base' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms clause404_absent_from_base

end


end Minidregg.Compiler.Tower256LogupExtensionDeployment
