/-
# Compiler.Tower256LogupClauseDispatch -- gated byte-only clause-404 dispatch

This module supplies the missing `DialectClauseDispatch.ControllerEntry` for
the extension-only Tower256 indexed-LogUp clause.  The controller closes over
one exact `Tower256LogupControllerPlan.ControllerInputs` value built against
the shared `Tower256ConcreteBackend.backend`.  Its external surface is entirely
first-order:

* an input containing only the transcript seed bytes;
* a query which pins the clause, controller, backend, transcript domain, public
  context, and seed; and
* a reply containing exactly two uniquely keyed native byte strings.

The reply is converted into an opaque `NativeRunner`; the existing Lean plan
decodes and checks every returned byte string.  A verified result therefore
constructs the existing proof-relevant `VerifiedExecution`.  This file does
not add clause 404 to base V1 or to a `DeploymentJoin`: position binding,
PCS/sampled-decider soundness, CR/ROM pricing, the common-game join, and a
`ClauseEvidenceFamily` remain required deployment evidence.
-/

import Compiler.DialectClauseDispatch
import Compiler.Tower256ConcreteBackend
import Compiler.Tower256LogupAcceptedRun

namespace Minidregg.Compiler.Tower256LogupClauseDispatch

open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.AuthenticatedColumnLogupBridge
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.Logup256ReceiptClause
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256LogupAcceptedRun
open Minidregg.Compiler.Tower256LogupControllerPlan
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Loom
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

abbrev Tower256 := BinaryTower256Profile.Tower256

/-! ## First-order transport values and codecs -/

/-- The only caller-selected controller input is the initial transcript state.
All semantic objects and plan continuations are already fixed by the selected
controller entry. -/
structure DispatchInput where
  seed : List UInt8
deriving DecidableEq, Repr

/-- Complete first-order identity of one issued clause-404 query. -/
structure DispatchQuery where
  clauseId : Digest
  controllerDigest : Digest
  cshakeAlgorithmId : Digest
  merkleSuiteId : Digest
  transcriptDomain : Digest
  publicContext : List UInt8
  seed : List UInt8
deriving DecidableEq, Repr

/-- One opaque native byte reply, keyed only by the Lean-selected call slot. -/
structure NativeByteReply where
  callSlotId : Digest
  bytes : List UInt8
deriving DecidableEq, Repr

/-- The concrete LogUp plan has exactly two native calls: round work and query
work.  Their actual call values remain selected by the challenge-indexed plan. -/
structure DispatchReply where
  nativeReplies : List NativeByteReply
deriving DecidableEq, Repr

def dispatchInputStream : Tower256ConcreteBackend.StreamCodec DispatchInput :=
  Tower256ConcreteBackend.StreamCodec.xmap
    Tower256ConcreteBackend.bytesStream
    DispatchInput.seed DispatchInput.mk
    (by intro input; cases input; rfl)

def dispatchInputCodec : LawfulCodec DispatchInput :=
  dispatchInputStream.toLawful

abbrev DispatchQueryWire :=
  Digest × Digest × Digest × Digest × Digest × List UInt8 × List UInt8

def dispatchQueryWireStream :
    Tower256ConcreteBackend.StreamCodec DispatchQueryWire :=
  Tower256ConcreteBackend.StreamCodec.product
    Tower256ConcreteBackend.digestStream
    (Tower256ConcreteBackend.StreamCodec.product
      Tower256ConcreteBackend.digestStream
      (Tower256ConcreteBackend.StreamCodec.product
        Tower256ConcreteBackend.digestStream
        (Tower256ConcreteBackend.StreamCodec.product
          Tower256ConcreteBackend.digestStream
          (Tower256ConcreteBackend.StreamCodec.product
            Tower256ConcreteBackend.digestStream
            (Tower256ConcreteBackend.StreamCodec.product
              Tower256ConcreteBackend.bytesStream
              Tower256ConcreteBackend.bytesStream)))))

def dispatchQueryStream : Tower256ConcreteBackend.StreamCodec DispatchQuery :=
  Tower256ConcreteBackend.StreamCodec.xmap dispatchQueryWireStream
    (fun query => (query.clauseId, query.controllerDigest,
      query.cshakeAlgorithmId, query.merkleSuiteId, query.transcriptDomain,
      query.publicContext, query.seed))
    (fun (clauseId, controllerDigest, cshakeAlgorithmId, merkleSuiteId,
        transcriptDomain, publicContext, seed) =>
      ⟨clauseId, controllerDigest, cshakeAlgorithmId, merkleSuiteId,
       transcriptDomain, publicContext, seed⟩)
    (by intro query; cases query; rfl)

def dispatchQueryCodec : LawfulCodec DispatchQuery :=
  dispatchQueryStream.toLawful

def nativeByteReplyStream :
    Tower256ConcreteBackend.StreamCodec NativeByteReply :=
  Tower256ConcreteBackend.StreamCodec.xmap
    (Tower256ConcreteBackend.StreamCodec.product
      Tower256ConcreteBackend.digestStream Tower256ConcreteBackend.bytesStream)
    (fun reply => (reply.callSlotId, reply.bytes))
    (fun (callSlotId, bytes) => ⟨callSlotId, bytes⟩)
    (by intro reply; cases reply; rfl)

def dispatchReplyStream : Tower256ConcreteBackend.StreamCodec DispatchReply :=
  Tower256ConcreteBackend.StreamCodec.xmap
    (Tower256ConcreteBackend.StreamCodec.list nativeByteReplyStream)
    DispatchReply.nativeReplies DispatchReply.mk
    (by intro reply; cases reply; rfl)

def dispatchReplyCodec : LawfulCodec DispatchReply :=
  dispatchReplyStream.toLawful

/-- Stable but extension-local transport pins.  They are not inserted into the
base manifest or authenticated native catalog by this module. -/
def dispatchInputCodecPin : CodecPin :=
  ⟨Tower256ConcreteBackend.id 8701, Tower256ConcreteBackend.id 8711, 1⟩

def dispatchQueryCodecPin : CodecPin :=
  ⟨Tower256ConcreteBackend.id 8702, Tower256ConcreteBackend.id 8712, 1⟩

def dispatchReplyCodecPin : CodecPin :=
  ⟨Tower256ConcreteBackend.id 8703, Tower256ConcreteBackend.id 8713, 1⟩

theorem transport_codec_ids_unique :
    ([dispatchInputCodecPin, dispatchQueryCodecPin,
      dispatchReplyCodecPin].map CodecPin.codecId).Nodup := by
  decide

/-! ## Reply table to byte-only native runner -/

inductive DispatchFailure
  | wrongReplyCount (actual : Nat)
  | duplicateReplySlot
  | missingReply (callSlotId : Digest)
deriving DecidableEq, Repr

def DispatchReply.slotIds (reply : DispatchReply) : List Digest :=
  reply.nativeReplies.map NativeByteReply.callSlotId

def DispatchReply.lookup (reply : DispatchReply) (callSlotId : Digest) :
    Option NativeByteReply :=
  reply.nativeReplies.find? fun candidate => decide (candidate.callSlotId = callSlotId)

/-- Native execution authority is exactly a byte lookup.  The reply cannot
provide a decoded field element, terminal attestation, proposition, or plan
continuation. -/
def DispatchReply.runner (reply : DispatchReply) : NativeRunner DispatchFailure :=
  fun call =>
    match reply.lookup call.callSlotId with
    | none => .error (.missingReply call.callSlotId)
    | some nativeReply => .ok nativeReply.bytes

@[simp] theorem DispatchReply.runner_missing
    (reply : DispatchReply) (call : NativeCall)
    (missing : reply.lookup call.callSlotId = none) :
    reply.runner call = .error (.missingReply call.callSlotId) := by
  simp [DispatchReply.runner, missing]

theorem DispatchReply.lookup_some_bytes
    (reply : DispatchReply) (call : NativeCall) (nativeReply : NativeByteReply)
    (found : reply.lookup call.callSlotId = some nativeReply) :
    reply.runner call = .ok nativeReply.bytes := by
  simp [DispatchReply.runner, found]

/-! ## Exact shared-backend controller -/

variable {rowLog tableLog checkpointLog : Nat}
variable {trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog}
variable {claim : IndexedTableReceiptClaim Tower256
  (Fin (2 ^ rowLog)) tableLog}

abbrev SharedInputs (rowLog tableLog checkpointLog : Nat)
    (trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog)
    (claim : IndexedTableReceiptClaim Tower256
      (Fin (2 ^ rowLog)) tableLog) :=
  ControllerInputs (checkpointLog := checkpointLog)
    Tower256ConcreteBackend.backend trace claim

def issuedQuery
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    (input : DispatchInput) : DispatchQuery where
  clauseId := clausePin.clauseId
  controllerDigest := clausePin.verifierControllerDigest
  cshakeAlgorithmId := Tower256ConcreteBackend.cshakeAlgorithmId
  merkleSuiteId := Tower256ConcreteBackend.merkleSuiteId
  transcriptDomain := inputs.transcriptDomain
  publicContext := inputs.publicContext
  seed := input.seed

/-- Execute only a canonical two-call reply table.  Duplicate, missing, short,
or overlong tables block; byte contents still pass through the exact existing
plan decoders and Lean checks. -/
noncomputable def checkReply
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    [Decidable (LogupFinalStatement trace claim)]
    (input : DispatchInput) (reply : DispatchReply) :
    Outcome DispatchFailure Tower256ConcreteBackend.backend.transcript.portal
      inputs.transcriptDomain :=
  if countExact : reply.nativeReplies.length = 2 then
    if unique : reply.slotIds.Nodup then
      inputs.execute reply.runner input.seed
    else
      .blocked .duplicateReplySlot
  else
    .blocked (.wrongReplyCount reply.nativeReplies.length)

noncomputable def controller
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    [Decidable (LogupFinalStatement trace claim)] :
    DialectController clausePin where
  Input := DispatchInput
  Query := fun _ => DispatchQuery
  Reply := fun _ _ => DispatchReply
  Outcome := fun _ =>
    Outcome DispatchFailure Tower256ConcreteBackend.backend.transcript.portal
      inputs.transcriptDomain
  issue := issuedQuery inputs
  check := fun input reply => checkReply inputs input reply

noncomputable def controllerEntry
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    [Decidable (LogupFinalStatement trace claim)] : ControllerEntry where
  declaration := clausePin
  controller := controller inputs

@[simp] theorem issuedQuery_exact
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    (input : DispatchInput) :
    issuedQuery inputs input =
      ⟨clausePin.clauseId, clausePin.verifierControllerDigest,
       Tower256ConcreteBackend.cshakeAlgorithmId,
       Tower256ConcreteBackend.merkleSuiteId, inputs.transcriptDomain,
       inputs.publicContext, input.seed⟩ := by
  rfl

@[simp] theorem wrong_reply_count_blocks
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    [Decidable (LogupFinalStatement trace claim)]
    (input : DispatchInput) (reply : DispatchReply)
    (wrong : reply.nativeReplies.length ≠ 2) :
    checkReply inputs input reply =
      .blocked (.wrongReplyCount reply.nativeReplies.length) := by
  simp [checkReply, wrong]

@[simp] theorem duplicate_reply_slot_blocks
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    [Decidable (LogupFinalStatement trace claim)]
    (input : DispatchInput) (reply : DispatchReply)
    (countExact : reply.nativeReplies.length = 2)
    (duplicate : ¬ reply.slotIds.Nodup) :
    checkReply inputs input reply = .blocked .duplicateReplySlot := by
  simp [checkReply, countExact, duplicate]

/-- The only successful controller branch is the exact existing verified plan
execution against the byte lookup runner reconstructed from the reply. -/
noncomputable def verifiedExecutionOfReply
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    [Decidable (LogupFinalStatement trace claim)]
    (input : DispatchInput) (reply : DispatchReply)
    {roots : List RootRecord} {draws : List DrawRecord}
    {native : List NativeRecord} {openings : List OpeningRecord}
    {edges : List ReprEqRecord}
    (attestation : TerminalAttestation
      Tower256ConcreteBackend.backend.transcript.portal inputs.transcriptDomain
      roots draws native openings edges)
    (verified : checkReply inputs input reply = .verified attestation) :
    VerifiedExecution Tower256ConcreteBackend.backend trace claim inputs
      reply.runner input.seed := by
  refine
    { roots := roots
      draws := draws
      native := native
      openings := openings
      edges := edges
      attestation := attestation
      resultExact := ?_ }
  unfold checkReply at verified
  split at verified
  · split at verified
    · exact verified
    · contradiction
  · contradiction

/-! ## Security-gated local registry and exact resolution -/

/-- This registry is intentionally local to the extension manifest.  Its
existence closes dispatch identity only; it is not deployment admission. -/
noncomputable def gatedRegistry
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    [Decidable (LogupFinalStatement trace claim)] : ControllerRegistry :=
  ⟨[controllerEntry inputs]⟩

theorem gatedRegistry_wellFormed
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    [Decidable (LogupFinalStatement trace claim)] :
    (gatedRegistry inputs).WellFormed Logup256ReceiptClause.manifest := by
  constructor
  · change ([clauseControllerKey clausePin] : List ControllerKey).Nodup
    simp
  · intro entry member
    change entry ∈ [controllerEntry inputs] at member
    rw [List.mem_singleton] at member
    subst entry
    exact clause_pin_registered
  · intro clause member
    change clause ∈ [clausePin] at member
    rw [List.mem_singleton] at member
    subst clause
    refine ⟨controllerEntry inputs, ?_⟩
    simp [gatedRegistry, ControllerRegistry.lookup, controllerEntry,
      ControllerEntry.key, clauseControllerKey]

noncomputable def gatedResolved
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    [Decidable (LogupFinalStatement trace claim)] :
    ResolvedClause Logup256ReceiptClause.manifest (gatedRegistry inputs)
      clausePin.clauseId :=
  resolveRegistered manifest_wellFormed (gatedRegistry_wellFormed inputs)
    clause_pin_registered

theorem resolved_declaration_exact
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    [Decidable (LogupFinalStatement trace claim)] :
    (gatedResolved inputs).clause = clausePin := by
  exact Logup256ReceiptClause.manifest.lookupClause_unique
    manifest_wellFormed.dialectClauseIdsUnique
    (gatedResolved inputs).clauseFound clause_pin_registered

theorem resolved_controller_exact
    (inputs : SharedInputs rowLog tableLog checkpointLog trace claim)
    [Decidable (LogupFinalStatement trace claim)] :
    (gatedResolved inputs).controllerEntry.declaration = clausePin := by
  exact (gatedResolved inputs).controllerExact.trans
    (resolved_declaration_exact inputs)

theorem clause404_still_absent_from_base :
    MinidreggV1Artifact.manifest.lookupClause clausePin.clauseId = none := by
  decide

/-- info: 'Minidregg.Compiler.Tower256LogupClauseDispatch.dispatchInputCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dispatchInputCodec
/-- info: 'Minidregg.Compiler.Tower256LogupClauseDispatch.dispatchQueryCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dispatchQueryCodec
/-- info: 'Minidregg.Compiler.Tower256LogupClauseDispatch.dispatchReplyCodec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dispatchReplyCodec
/-- info: 'Minidregg.Compiler.Tower256LogupClauseDispatch.wrong_reply_count_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms wrong_reply_count_blocks
/-- info: 'Minidregg.Compiler.Tower256LogupClauseDispatch.duplicate_reply_slot_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duplicate_reply_slot_blocks
/-- info: 'Minidregg.Compiler.Tower256LogupClauseDispatch.verifiedExecutionOfReply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifiedExecutionOfReply
/-- info: 'Minidregg.Compiler.Tower256LogupClauseDispatch.gatedRegistry_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms gatedRegistry_wellFormed
/-- info: 'Minidregg.Compiler.Tower256LogupClauseDispatch.resolved_controller_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms resolved_controller_exact
/-- info: 'Minidregg.Compiler.Tower256LogupClauseDispatch.clause404_still_absent_from_base' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms clause404_still_absent_from_base

end Minidregg.Compiler.Tower256LogupClauseDispatch
