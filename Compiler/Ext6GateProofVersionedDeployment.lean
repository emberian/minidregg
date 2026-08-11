/-
# Compiler.Ext6GateProofVersionedDeployment -- pinned Ext6 statement migration

The landed Ext6 controller already owns a nonzero suite, a nonzero controller,
four versioned codecs, and one exact 23-residual statement.  Its generic
`run`, however, deliberately treats the request as opaque input to the native
runner.  Native refusal of a stale request is useful evidence, but it is not a
Lean-owned deployment check.

This module makes that missing boundary first order.  A deployment statement
contains every identity and codec pin plus the canonical core statement bytes;
one lawful codec owns its wire representation.  The only accepted request is
the exact encoding of the V1 statement.  Migration from the all-zero V0 marker
is explicit and exact, and both V0 replay and a stale codec pin are rejected by
Lean before proof bytes are decoded.

This is still only controller deployment.  It introduces no PCS, proximity,
binding, random-oracle, challenge-sampling, or final-LDT law.
-/

import Compiler.Ext6GateProofPositiveRun

namespace Minidregg.Compiler.Ext6GateProofVersionedDeployment

open Minidregg.Compiler.Ext6GateProofController
open Minidregg.Compiler.Ext6GateProofDeployment
open Minidregg.Compiler.Ext6GateProofPositiveRun
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256ConcreteBackend
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

/-! ## One exact, versioned deployment statement -/

/-- The complete control-plane identity of the deployed Ext6 statement. -/
structure DeploymentStatement where
  version : Nat
  proofSuiteId : Digest
  controllerId : Digest
  babyBearCodecPin : CodecPin
  ext6CodecPin : CodecPin
  roundMessageCodecPin : CodecPin
  receiptCodecPin : CodecPin
  coreStatementBytes : List UInt8
deriving DecidableEq, Repr

def codecPinStream : StreamCodec CodecPin :=
  StreamCodec.xmap
    (StreamCodec.product digestStream
      (StreamCodec.product digestStream StreamCodec.nat))
    (fun pin => (pin.codecId, pin.valueTypeId, pin.version))
    (fun wire => ⟨wire.1, wire.2.1, wire.2.2⟩)
    (by intro pin; cases pin; rfl)

private def deploymentStatementWireStream :=
  StreamCodec.product StreamCodec.nat <|
    StreamCodec.product digestStream <|
      StreamCodec.product digestStream <|
        StreamCodec.product codecPinStream <|
          StreamCodec.product codecPinStream <|
            StreamCodec.product codecPinStream <|
              StreamCodec.product codecPinStream bytesStream

/-- Prefix-decodable deployment statement framing. -/
def deploymentStatementStream : StreamCodec DeploymentStatement :=
  StreamCodec.xmap deploymentStatementWireStream
    (fun statement =>
      (statement.version,
        (statement.proofSuiteId,
          (statement.controllerId,
            (statement.babyBearCodecPin,
              (statement.ext6CodecPin,
                (statement.roundMessageCodecPin,
                  (statement.receiptCodecPin, statement.coreStatementBytes))))))))
    (fun wire =>
      { version := wire.1
        proofSuiteId := wire.2.1
        controllerId := wire.2.2.1
        babyBearCodecPin := wire.2.2.2.1
        ext6CodecPin := wire.2.2.2.2.1
        roundMessageCodecPin := wire.2.2.2.2.2.1
        receiptCodecPin := wire.2.2.2.2.2.2.1
        coreStatementBytes := wire.2.2.2.2.2.2.2 })
    (by intro statement; cases statement; rfl)

def deploymentStatementCodec : LawfulCodec DeploymentStatement :=
  deploymentStatementStream.toLawful

theorem deploymentStatement_encode_injective :
    Function.Injective deploymentStatementCodec.encode := by
  intro left right equal
  have decoded := congrArg deploymentStatementCodec.decode equal
  rw [deploymentStatementCodec.decode_encode,
    deploymentStatementCodec.decode_encode] at decoded
  exact Option.some.inj decoded

def zeroCodecPin : CodecPin := ⟨⟨0⟩, ⟨0⟩, 0⟩

/-- The sole accepted source of the V0-to-V1 migration.  V0 names no suite,
controller, or codec; retaining the core bytes makes the statement migration
visible rather than silently changing the relation at the same time. -/
def legacyV0 : DeploymentStatement where
  version := 0
  proofSuiteId := ⟨0⟩
  controllerId := ⟨0⟩
  babyBearCodecPin := zeroCodecPin
  ext6CodecPin := zeroCodecPin
  roundMessageCodecPin := zeroCodecPin
  receiptCodecPin := zeroCodecPin
  coreStatementBytes := canonicalStatementPreimage suite statement

/-- Exact V1 pins for the existing nonzero Ext6 suite and controller. -/
def deployedV1 : DeploymentStatement where
  version := 1
  proofSuiteId := suiteId
  controllerId := controllerId
  babyBearCodecPin := babyBearCodecPin
  ext6CodecPin := ext6CodecPin
  roundMessageCodecPin := roundMessageCodecPin
  receiptCodecPin := receiptCodecPin
  coreStatementBytes := canonicalStatementPreimage suite statement

theorem deployedV1_exact :
    deployedV1.version = 1 ∧
    deployedV1.proofSuiteId = suiteId ∧
    deployedV1.controllerId = controllerId ∧
    deployedV1.babyBearCodecPin = babyBearCodecPin ∧
    deployedV1.ext6CodecPin = ext6CodecPin ∧
    deployedV1.roundMessageCodecPin = roundMessageCodecPin ∧
    deployedV1.receiptCodecPin = receiptCodecPin ∧
    deployedV1.coreStatementBytes = canonicalStatementPreimage suite statement ∧
    deployedV1.proofSuiteId ≠ ⟨0⟩ ∧
    deployedV1.controllerId ≠ ⟨0⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    suiteId_nonzero, controllerId_nonzero⟩

/-- Every V1 codec pin is assigned and versioned.  These are control-plane
identities only; nonzero numbers are not cryptographic assumptions. -/
theorem deployedV1_codec_pins_assigned :
    deployedV1.babyBearCodecPin.codecId ≠ ⟨0⟩ ∧
    deployedV1.ext6CodecPin.codecId ≠ ⟨0⟩ ∧
    deployedV1.roundMessageCodecPin.codecId ≠ ⟨0⟩ ∧
    deployedV1.receiptCodecPin.codecId ≠ ⟨0⟩ ∧
    deployedV1.babyBearCodecPin.version = 1 ∧
    deployedV1.ext6CodecPin.version = 1 ∧
    deployedV1.roundMessageCodecPin.version = 1 ∧
    deployedV1.receiptCodecPin.version = 1 := by
  decide

/-- Migration is deliberately partial: no arbitrary or already-versioned
statement is silently repinned. -/
def migrateV0ToV1 (source : DeploymentStatement) : Option DeploymentStatement :=
  if source = legacyV0 then some deployedV1 else none

@[simp] theorem migrateV0ToV1_exact :
    migrateV0ToV1 legacyV0 = some deployedV1 := by
  simp [migrateV0ToV1]

theorem migrateV0ToV1_only {source target : DeploymentStatement}
    (migrated : migrateV0ToV1 source = some target) :
    source = legacyV0 ∧ target = deployedV1 := by
  unfold migrateV0ToV1 at migrated
  split at migrated
  next sourceExact =>
    exact ⟨sourceExact, (Option.some.inj migrated).symm⟩
  next => simp at migrated

/-! ## Exact request bytes and a Lean-owned pinned runner -/

def canonicalRequest : List UInt8 :=
  deploymentStatementCodec.encode deployedV1

def zeroPinnedRequest : List UInt8 :=
  deploymentStatementCodec.encode legacyV0

theorem legacyV0_ne_deployedV1 : legacyV0 ≠ deployedV1 := by
  intro equal
  have suiteEqual := congrArg DeploymentStatement.proofSuiteId equal
  exact suiteId_nonzero (by simpa [legacyV0, deployedV1] using suiteEqual.symm)

theorem zeroPinnedRequest_ne_canonical : zeroPinnedRequest ≠ canonicalRequest := by
  intro equal
  exact legacyV0_ne_deployedV1
    (deploymentStatement_encode_injective equal)

/-- A V1-shaped request with the old zero receipt codec is not the deployed
statement.  This prevents pin-only rollback at the same version number. -/
def staleCodecV1 : DeploymentStatement :=
  { deployedV1 with receiptCodecPin := zeroCodecPin }

def staleCodecRequest : List UInt8 :=
  deploymentStatementCodec.encode staleCodecV1

theorem staleCodecV1_ne_deployedV1 : staleCodecV1 ≠ deployedV1 := by
  intro equal
  have pinEqual := congrArg DeploymentStatement.receiptCodecPin equal
  have codecIdEqual := congrArg CodecPin.codecId pinEqual
  norm_num [staleCodecV1, deployedV1, zeroCodecPin, receiptCodecPin] at codecIdEqual

theorem staleCodecRequest_ne_canonical : staleCodecRequest ≠ canonicalRequest := by
  intro equal
  exact staleCodecV1_ne_deployedV1
    (deploymentStatement_encode_injective equal)

inductive PinnedFailure (Error : Type)
  | wrongDeployment
  | proof (failure : Ext6GateProofController.Failure Error)
deriving Repr

/-- Lean checks the exact statement bytes before invoking the generic Ext6
proof controller.  The success type is indexed by `canonicalRequest`, so the
caller cannot relabel an accepted receipt with the bytes it supplied. -/
def runPinned {Error : Type} (runner : OpaqueProofRunner Error)
    (supplied : List UInt8) :
    Except (PinnedFailure Error)
      (AcceptedReceipt suite statement verifier canonicalRequest) :=
  if supplied = canonicalRequest then
    match run suite statement verifier runner canonicalRequest with
    | .error failure => .error (.proof failure)
    | .ok reply => .ok reply
  else
    .error .wrongDeployment

theorem runPinned_success_integrity {Error : Type}
    (runner : OpaqueProofRunner Error) (supplied : List UInt8)
    (reply : AcceptedReceipt suite statement verifier canonicalRequest)
    (success : runPinned runner supplied = .ok reply) :
    supplied = canonicalRequest ∧
    run suite statement verifier runner canonicalRequest = .ok reply := by
  have exactRequest : supplied = canonicalRequest := by
    by_contra different
    simp [runPinned, different] at success
  subst supplied
  constructor
  · rfl
  · unfold runPinned at success
    simp only [if_pos] at success
    split at success
    next failure ran => simp at success
    next candidate ran =>
      simp only [Except.ok.injEq] at success
      subst candidate
      exact ran

/-- The positive runner for the pinned endpoint has no authority beyond
returning the already-constructed canonical proof bytes. -/
def pinnedHonestRunner : OpaqueProofRunner Unit := fun supplied =>
  if supplied = canonicalRequest then .ok proofBytes else .error ()

noncomputable def pinnedAcceptedReceipt :
    AcceptedReceipt suite statement verifier canonicalRequest where
  proofBytes := proofBytes
  receipt := receipt
  decoded := proofBytes_decode
  accepted := receipt_accepts

theorem pinned_honest_run_succeeds :
    runPinned pinnedHonestRunner canonicalRequest = .ok pinnedAcceptedReceipt := by
  have checked : verifier.check receipt = true :=
    (verifier.check_iff receipt).mpr receipt_accepts
  have runnerExact : pinnedHonestRunner canonicalRequest = .ok proofBytes := by
    simp [pinnedHonestRunner]
  have core :
      run suite statement verifier pinnedHonestRunner canonicalRequest =
        .ok pinnedAcceptedReceipt := by
    unfold run
    simp only [runnerExact]
    split
    next decodeFailed =>
      have impossible : some receipt = (none : Option (Receipt Rounds)) :=
        proofBytes_decode.symm.trans decodeFailed
      cases impossible
    next decodedReceipt decoded =>
      have receiptExact : decodedReceipt = receipt :=
        Option.some.inj (decoded.symm.trans proofBytes_decode)
      subst decodedReceipt
      simp only [checked]
      congr
  simp [runPinned, core]

theorem zero_pinned_replay_rejected :
    runPinned pinnedHonestRunner zeroPinnedRequest =
      .error (.wrongDeployment) := by
  simp [runPinned, zeroPinnedRequest_ne_canonical]

theorem stale_codec_replay_rejected :
    runPinned pinnedHonestRunner staleCodecRequest =
      .error (.wrongDeployment) := by
  simp [runPinned, staleCodecRequest_ne_canonical]

/-! ## Axiom audit -/

/-- info: 'Minidregg.Compiler.Ext6GateProofVersionedDeployment.deploymentStatement_encode_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms deploymentStatement_encode_injective
/-- info: 'Minidregg.Compiler.Ext6GateProofVersionedDeployment.pinned_honest_run_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pinned_honest_run_succeeds
/-- info: 'Minidregg.Compiler.Ext6GateProofVersionedDeployment.zero_pinned_replay_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms zero_pinned_replay_rejected

end

end Minidregg.Compiler.Ext6GateProofVersionedDeployment
