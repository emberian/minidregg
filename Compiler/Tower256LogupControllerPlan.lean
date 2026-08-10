/-
# Compiler.Tower256LogupControllerPlan -- one real authenticated-column schedule

This module instantiates the generic authenticated-column phase machine with
the shared Tower256/cSHAKE/Merkle backend.  The schedule is no longer prose:

1. bind semantic, canonical-address, weight, and table Merkle roots;
2. derive the round challenge from that exact four-root prefix;
3. run fallible opaque Tower work and bind its additive checkpoint root;
4. derive a query challenge, run fallible opaque opening work;
5. verify logarithmic table and checkpoint Merkle openings; and
6. decide the exact `LogupFinalStatement` in Lean.

Native calls still return only encodings of outputs fixed in their `NativeCall`
objects and cannot choose this continuation.  This file does not claim that a
Rust Tower256 buffer has Lean field semantics.  Merkle position binding/CR,
PCS sampled-decider soundness, and cSHAKE-to-ROM transport remain the explicit
`Backend.SecurityPremises` required by clause admission.
-/

import Compiler.AuthenticatedColumnLogupBridge
import Compiler.Tower256CshakeMerkleController

namespace Minidregg.Compiler.Tower256LogupControllerPlan

open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.AuthenticatedColumnLogupBridge
open Minidregg.Compiler.Logup256ReceiptClause
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization (Digest)

set_option autoImplicit false

variable {F : Type} [Field F] [CharP F 2]
variable {rowLog tableLog checkpointLog : Nat}

/-! ## Backend-owned additive columns -/

/-- First-order port data for one power-of-two column.  The port and scheme
below are derived, so a caller cannot substitute another carrier, value codec,
hash, tree convention, or opening verifier. -/
structure AdditiveColumnSpec (backend : Backend F) (logSize : Nat) where
  role : ColumnRole
  slotId : Digest
  semanticTypeId : Digest
  domainId : Digest
  domainCodecPin : CodecPin
  domainCodec : LawfulCodec (Fin (2 ^ logSize))

def AdditiveColumnSpec.port
    {backend : Backend F} {logSize : Nat}
    (spec : AdditiveColumnSpec backend logSize) :
    ColumnPort F F (Fin (2 ^ logSize)) :=
  backend.towerPort spec.role spec.slotId spec.semanticTypeId spec.domainId
    spec.domainCodecPin spec.domainCodec

def AdditiveColumnSpec.scheme
    {backend : Backend F} {logSize : Nat}
    (spec : AdditiveColumnSpec backend logSize) : CommitmentScheme spec.port :=
  backend.additiveMerkleScheme spec.role spec.slotId spec.semanticTypeId
    spec.domainId spec.domainCodecPin spec.domainCodec

structure AdditiveColumn
    {backend : Backend F} {logSize : Nat}
    (spec : AdditiveColumnSpec backend logSize) where
  bound : BoundColumn spec.port spec.scheme

def AdditiveColumn.rootRecord
    {backend : Backend F} {logSize : Nat}
    {spec : AdditiveColumnSpec backend logSize}
    (column : AdditiveColumn spec) : RootRecord :=
  column.bound.rootRecord

def AdditiveColumn.honestOpening
    {backend : Backend F} {logSize : Nat}
    {spec : AdditiveColumnSpec backend logSize}
    (column : AdditiveColumn spec) (openingSlotId : Digest)
    (index : Fin (2 ^ logSize)) : ColumnOpening column.bound :=
  column.bound.honestOpening openingSlotId index

/-! ## Exact LogUp root bundle -/

/-- The four pre-challenge columns and their exact semantic claim roots.
Address/weight/table roles are enforced here rather than trusted from digest
equality alone.  The semantic trace column deliberately remains an independent
semantic root; canonical address linkage is decided by the terminal checker. -/
structure LogupColumns
    (backend : Backend F)
    (trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog)
    (claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog) where
  semanticSpec : AdditiveColumnSpec backend rowLog
  semanticRole : semanticSpec.role = .semanticTrace
  semantic : AdditiveColumn semanticSpec
  semanticRootExact : semantic.rootRecord.root = trace.semanticTraceRoot

  addressSpec : AdditiveColumnSpec backend (rowLog + tableLog)
  addressRole : addressSpec.role = .lookupAddress
  address : AdditiveColumn addressSpec
  addressRootExact : address.rootRecord.root = claim.addressRoot

  weightsSpec : AdditiveColumnSpec backend rowLog
  weightsRole : weightsSpec.role = .lookupWeight
  weights : AdditiveColumn weightsSpec
  weightsRootExact : weights.rootRecord.root = claim.weightsRoot

  tableSpec : AdditiveColumnSpec backend tableLog
  tableRole : tableSpec.role = .lookupTable
  table : AdditiveColumn tableSpec
  tableRootExact : table.rootRecord.root = claim.tableRoot

namespace LogupColumns

variable {backend : Backend F}
variable {trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog}
variable {claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog}

def required (columns : LogupColumns backend trace claim) :
    RequiredRoots trace claim where
  semanticTrace := columns.semantic.rootRecord
  address := columns.address.rootRecord
  weights := columns.weights.rootRecord
  table := columns.table.rootRecord
  semanticTraceExact := columns.semanticRootExact
  addressExact := columns.addressRootExact
  weightsExact := columns.weightsRootExact
  tableExact := columns.tableRootExact

theorem required_roles (columns : LogupColumns backend trace claim) :
    (columns.required.semanticTrace.slot.role = .semanticTrace) ∧
    (columns.required.address.slot.role = .lookupAddress) ∧
    (columns.required.weights.slot.role = .lookupWeight) ∧
    (columns.required.table.slot.role = .lookupTable) := by
  simp only [required, AdditiveColumn.rootRecord, BoundColumn.rootRecord,
    ColumnPort.rootSlot]
  exact ⟨columns.semanticRole, columns.addressRole,
    columns.weightsRole, columns.tableRole⟩

end LogupColumns

/-! ## Reflected final checker -/

/-- The actual checker used by this controller.  It decides the exact LogUp
statement retained in the terminal attestation; there is no untyped final
success bit. -/
def logupFinalChecker
    (trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog)
    (claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog)
    [Decidable (LogupFinalStatement trace claim)]
    (checkerId : Digest) (ledger : Ledger) : FinalChecker ledger where
  checkerId := checkerId
  Statement := LogupFinalStatement trace claim
  check := decide (LogupFinalStatement trace claim)
  check_iff := by simp

@[simp] theorem logupFinalChecker_statement
    (trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog)
    (claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog)
    [Decidable (LogupFinalStatement trace claim)]
    (checkerId : Digest) (ledger : Ledger) :
    (logupFinalChecker trace claim checkerId ledger).Statement =
      LogupFinalStatement trace claim :=
  rfl

/-! ## Concrete controller inputs and schedule -/

/-- Everything needed to generate the fixed controller plan.  Challenge-indexed
native calls and the checkpoint column may depend on Lean-derived coins.  Their
reply bytes cannot affect the already fixed continuations. -/
structure ControllerInputs
    (backend : Backend F)
    (trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog)
    (claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog) where
  transcriptDomain : Digest
  publicContext : List UInt8
  columns : LogupColumns backend trace claim

  roundCall : Digest -> NativeCall
  checkpointSpec : AdditiveColumnSpec backend checkpointLog
  checkpointRole : checkpointSpec.role = .checkpoint
  checkpoint : Digest -> AdditiveColumn checkpointSpec

  queryCall : Digest -> Digest -> NativeCall
  tableOpeningSlotId : Digest
  tableQueryIndex : Digest -> Fin (2 ^ tableLog)
  checkpointOpeningSlotId : Digest
  checkpointQueryIndex : Digest -> Fin (2 ^ checkpointLog)
  finalCheckerId : Digest

namespace ControllerInputs

variable {backend : Backend F}
variable {trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog}
variable {claim : IndexedTableReceiptClaim F (Fin (2 ^ rowLog)) tableLog}

/-- The generated authenticated-column schedule.  Four exact roots precede the
round challenge.  The additive checkpoint root is challenge-dependent and is
committed before the query challenge.  Both query openings use the backend's
proved Merkle verifier. -/
def plan (inputs : ControllerInputs (checkpointLog := checkpointLog)
    backend trace claim)
    [Decidable (LogupFinalStatement trace claim)] :
    Plan inputs.transcriptDomain .start :=
  .bindPublic inputs.publicContext <|
  .bindFirstRoot inputs.columns.semantic.bound <|
  .bindAdditionalRoot inputs.columns.address.bound <|
  .bindAdditionalRoot inputs.columns.weights.bound <|
  .bindAdditionalRoot inputs.columns.table.bound <|
  .drawRound fun roundChallenge =>
  .runRoundNative (inputs.roundCall roundChallenge) <|
  .bindNextRoundRoot (inputs.checkpoint roundChallenge).bound <|
  .drawQuery fun queryChallenge =>
  .runQueryNative (inputs.queryCall roundChallenge queryChallenge) <|
  .bindFirstOpening
    (inputs.columns.table.honestOpening inputs.tableOpeningSlotId
      (inputs.tableQueryIndex queryChallenge))
    (by
      simp [Ledger.empty, Ledger.addRoot, Ledger.addDraw, Ledger.addNative]) <|
  .bindAdditionalOpening
    ((inputs.checkpoint roundChallenge).honestOpening
      inputs.checkpointOpeningSlotId
      (inputs.checkpointQueryIndex queryChallenge))
    (by
      simp [Ledger.empty, Ledger.addRoot, Ledger.addDraw, Ledger.addNative,
        Ledger.addOpening]) <|
  .finalize (logupFinalChecker trace claim inputs.finalCheckerId _)

/-- This is literally a cSHAKE-framed controller plan, not merely a compatible
portal chosen later by a runner. -/
def execute {Error : Type}
    (inputs : ControllerInputs (checkpointLog := checkpointLog)
      backend trace claim)
    [Decidable (LogupFinalStatement trace claim)]
    (runner : NativeRunner Error) (seed : List UInt8) :
    Outcome Error backend.transcript.portal inputs.transcriptDomain :=
  AuthenticatedColumnPlan.execute backend.transcript.portal runner
    inputs.transcriptDomain inputs.plan seed

end ControllerInputs

/-- info: 'Minidregg.Compiler.Tower256LogupControllerPlan.LogupColumns.required_roles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms LogupColumns.required_roles
/-- info: 'Minidregg.Compiler.Tower256LogupControllerPlan.logupFinalChecker_statement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms logupFinalChecker_statement

end Minidregg.Compiler.Tower256LogupControllerPlan
