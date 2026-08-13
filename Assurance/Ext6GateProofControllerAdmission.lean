/-
# Assurance.Ext6GateProofControllerAdmission -- honest Ext6 security boundary

The deterministic controller checks transcript order and proof algebra, but a
succinct semantic theorem still needs real PCS, subfield, proximity, binding,
ROM, and final-LDT reductions.  This module names those obligations at their
exact join rather than replacing them with an acceptance flag.

All events below live on one finite coin type.  The local failure taxonomy is
deliberately Ext6-specific: it does not relabel LogUp or additive-FRI events.
Injection into a future global extensible ledger remains a separate residual.
-/

import Assurance.ProofCompositionGame
import Compiler.Ext6GateProofController

namespace Minidregg.Assurance.Ext6GateProofControllerAdmission

open scoped BigOperators
open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Compiler
open Minidregg.Compiler.Ext6GateProofController
open Minidregg.Compiler.GateFactoredExt6
open Minidregg.Compiler.GateMleExt6
open Minidregg.Selvage

set_option autoImplicit false

noncomputable section

/-! ## One honestly named Ext6 failure ledger -/

inductive Ext6FailureClass
  | gateAlgebra
  | gatePcs
  | subfield
  | proximity
  | binding
  | oracleTransport
  | challengeSampling
  | finalLdt
deriving DecidableEq, Fintype, Repr

abbrev Ext6FailureLedger (Omega : Type) [Fintype Omega] :=
  Ext6FailureClass -> PricedFailure Omega

namespace Ext6FailureLedger

variable {Omega : Type} [Fintype Omega]

def Bad (ledger : Ext6FailureLedger Omega) (omega : Omega) : Prop :=
  (ledger .gateAlgebra).event omega ∨
  (ledger .gatePcs).event omega ∨
  (ledger .subfield).event omega ∨
  (ledger .proximity).event omega ∨
  (ledger .binding).event omega ∨
  (ledger .oracleTransport).event omega ∨
  (ledger .challengeSampling).event omega ∨
  (ledger .finalLdt).event omega

def total (ledger : Ext6FailureLedger Omega) : Real :=
  (ledger .gateAlgebra).price +
  (ledger .gatePcs).price +
  (ledger .subfield).price +
  (ledger .proximity).price +
  (ledger .binding).price +
  (ledger .oracleTransport).price +
  (ledger .challengeSampling).price +
  (ledger .finalLdt).price

def Good (ledger : Ext6FailureLedger Omega)
    (failure : Ext6FailureClass) (omega : Omega) : Prop :=
  ¬(ledger failure).event omega

theorem good_of_not_bad (ledger : Ext6FailureLedger Omega) {omega : Omega}
    (good : ¬ledger.Bad omega) (failure : Ext6FailureClass) :
    ledger.Good failure omega := by
  intro bad
  cases failure with
  | gateAlgebra => exact good (Or.inl bad)
  | gatePcs => exact good (Or.inr (Or.inl bad))
  | subfield => exact good (Or.inr (Or.inr (Or.inl bad)))
  | proximity => exact good (Or.inr (Or.inr (Or.inr (Or.inl bad))))
  | binding => exact good (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl bad)))))
  | oracleTransport =>
      exact good (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl bad))))))
  | challengeSampling =>
      exact good
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl bad)))))))
  | finalLdt =>
      exact good
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr bad)))))))

theorem bad_le_total (ledger : Ext6FailureLedger Omega) :
    uniformProb Omega ledger.Bad ≤ ledger.total := by
  have h1 := uniformProb_or_le (ledger .gateAlgebra).event (fun omega =>
    (ledger .gatePcs).event omega ∨ (ledger .subfield).event omega ∨
    (ledger .proximity).event omega ∨ (ledger .binding).event omega ∨
    (ledger .oracleTransport).event omega ∨
    (ledger .challengeSampling).event omega ∨ (ledger .finalLdt).event omega)
  have h2 := uniformProb_or_le (ledger .gatePcs).event (fun omega =>
    (ledger .subfield).event omega ∨ (ledger .proximity).event omega ∨
    (ledger .binding).event omega ∨ (ledger .oracleTransport).event omega ∨
    (ledger .challengeSampling).event omega ∨ (ledger .finalLdt).event omega)
  have h3 := uniformProb_or_le (ledger .subfield).event (fun omega =>
    (ledger .proximity).event omega ∨ (ledger .binding).event omega ∨
    (ledger .oracleTransport).event omega ∨
    (ledger .challengeSampling).event omega ∨ (ledger .finalLdt).event omega)
  have h4 := uniformProb_or_le (ledger .proximity).event (fun omega =>
    (ledger .binding).event omega ∨ (ledger .oracleTransport).event omega ∨
    (ledger .challengeSampling).event omega ∨ (ledger .finalLdt).event omega)
  have h5 := uniformProb_or_le (ledger .binding).event (fun omega =>
    (ledger .oracleTransport).event omega ∨
    (ledger .challengeSampling).event omega ∨ (ledger .finalLdt).event omega)
  have h6 := uniformProb_or_le (ledger .oracleTransport).event (fun omega =>
    (ledger .challengeSampling).event omega ∨ (ledger .finalLdt).event omega)
  have h7 := uniformProb_or_le (ledger .challengeSampling).event
    (ledger .finalLdt).event
  unfold Bad total
  linarith [(ledger .gateAlgebra).bound, (ledger .gatePcs).bound,
    (ledger .subfield).bound, (ledger .proximity).bound,
    (ledger .binding).bound, (ledger .oracleTransport).bound,
    (ledger .challengeSampling).bound,
    (ledger .finalLdt).bound]

end Ext6FailureLedger

/-! ## Exact authenticated trace relations -/

variable {m nPadding : Nat}
variable {suite : Suite}
variable {statement : Statement m nPadding}

/-- The seven public affine forms derived from the literal emitted descriptor,
the receipt's transcript-derived gamma, and the receipt's sumcheck point. -/
def terminalForms (statement : Statement m nPadding) (receipt : Receipt m)
    (trace : Nat -> BabyBear) (j : Fin 7) : TraceAffineFunctional :=
  terminalFunctional (terminalOrder j) statement.descriptor trace
    (statement.encodingFor trace) receipt.gamma receipt.roundChallenge

/-- Weights of the full eta relation: seven terminal forms, every public-prefix
cell, and every advertised padding-zero cell. -/
def aggregateWeights (statement : Statement m nPadding) (receipt : Receipt m)
    (trace : Nat -> BabyBear) : Nat →₀ Ext6Q :=
  etaBatchedWeights (t := 7 + statement.descriptor.nPublic + nPadding)
    receipt.eta
    (GateTraceRelationExt6.extendedWeights
      (nPublic := statement.descriptor.nPublic) (nPadding := nPadding)
      (terminalForms statement receipt trace) statement.descriptor.nWires)

/-- What a real aggregate opening theorem must authenticate.  The trace is a
BabyBear word before lifting, so no arbitrary Ext6 word can masquerade as
base-limb provenance. -/
structure AuthenticatedAggregate (statement : Statement m nPadding)
    (receipt : Receipt m) (trace : Nat -> BabyBear) : Prop where
  aggregateExact : receipt.aggregateValue =
    Finsupp.linearCombination Ext6Q (liftWord (K := Ext6Q) trace)
      (aggregateWeights statement receipt trace)

/-- The exact semantic relation hidden by fresh-eta aggregation.  It includes
all seven operand terminal values, every public base limb, and every advertised
zero padding cell. -/
structure AuthenticatedTraceRelation (statement : Statement m nPadding)
    (receipt : Receipt m) (trace : Nat -> BabyBear) : Prop where
  terminalExact : ∀ j : Fin 7,
    receipt.terminalValue j =
      (terminalForms statement receipt trace j).eval (liftWord (K := Ext6Q) trace)
  publicExact : ∀ j : Fin statement.descriptor.nPublic,
    trace j.val = statement.publicValues j
  paddingExact : ∀ j : Fin nPadding,
    trace (statement.descriptor.nWires + j.val) = 0

/-! ## The precise missing cryptographic reductions -/

/-- Deployment laws on one coin space.  Every field is an exact theorem shape,
not a claimed implementation:

* `aggregateOpeningExact` is where the trace/operand roots and their proof
  bytes, PCS, subfield provenance, proximity, binding, and final LDT meet;
* `etaSound` is the fresh-eta root-counting/ROM step recovering every ordered
  relation from the authenticated aggregate;
* `sumcheckSound` excludes a degree-two laundering transcript; and
* `gammaSound` turns a zero gamma-batched emitted residual into literal
  `descriptorHolds`.

`challengeSampling` is separate from ROM: `digestToExt6` performs six
radix-`babyBearP` reductions and is not asserted uniform.  A deployment must
price that bias/reduction on the same coin.  This module constructs none of
these laws from completeness or from native behavior. -/
structure ReductionLaws (Omega : Type) [Fintype Omega]
    (ledger : Ext6FailureLedger Omega) where
  aggregateOpeningExact : ∀ omega (receipt : Receipt m),
    Accepts suite statement receipt ->
    ledger.Good .gatePcs omega -> ledger.Good .subfield omega ->
    ledger.Good .proximity omega -> ledger.Good .binding omega ->
    ledger.Good .oracleTransport omega -> ledger.Good .challengeSampling omega ->
    ledger.Good .finalLdt omega ->
    ∃ trace : Nat -> BabyBear, AuthenticatedAggregate statement receipt trace
  etaSound : ∀ omega (receipt : Receipt m) (trace : Nat -> BabyBear),
    Accepts suite statement receipt -> AuthenticatedAggregate statement receipt trace ->
    ledger.Good .gateAlgebra omega -> ledger.Good .oracleTransport omega ->
    ledger.Good .challengeSampling omega ->
    AuthenticatedTraceRelation statement receipt trace
  sumcheckSound : ∀ omega (receipt : Receipt m) (trace : Nat -> BabyBear),
    Accepts suite statement receipt -> AuthenticatedTraceRelation statement receipt trace ->
    ledger.Good .gateAlgebra omega -> ledger.Good .oracleTransport omega ->
    ledger.Good .challengeSampling omega ->
    gammaBatchedDescriptorResidual statement.descriptor trace receipt.gamma = 0
  gammaSound : ∀ omega (receipt : Receipt m) (trace : Nat -> BabyBear),
    ledger.Good .gateAlgebra omega -> ledger.Good .oracleTransport omega ->
    ledger.Good .challengeSampling omega ->
    gammaBatchedDescriptorResidual statement.descriptor trace receipt.gamma = 0 ->
    descriptorHolds statement.descriptor trace

namespace ReductionLaws

variable {Omega : Type} [Fintype Omega]
variable {ledger : Ext6FailureLedger Omega}

/-- Outside the exact seven-event ledger, accepted controller algebra produces
a base-field trace satisfying the literal emitted descriptor. -/
theorem semantic_of_not_bad (laws : ReductionLaws (suite := suite)
    (statement := statement) Omega ledger) {omega : Omega}
    (good : ¬ledger.Bad omega) (receipt : Receipt m)
    (accepted : Accepts suite statement receipt) :
    ∃ trace : Nat -> BabyBear,
      AuthenticatedTraceRelation statement receipt trace ∧
      descriptorHolds statement.descriptor trace := by
  have goodAlgebra := ledger.good_of_not_bad good .gateAlgebra
  have goodPcs := ledger.good_of_not_bad good .gatePcs
  have goodSubfield := ledger.good_of_not_bad good .subfield
  have goodProximity := ledger.good_of_not_bad good .proximity
  have goodBinding := ledger.good_of_not_bad good .binding
  have goodOracle := ledger.good_of_not_bad good .oracleTransport
  have goodSampling := ledger.good_of_not_bad good .challengeSampling
  have goodFinal := ledger.good_of_not_bad good .finalLdt
  obtain ⟨trace, aggregate⟩ := laws.aggregateOpeningExact omega receipt accepted
    goodPcs goodSubfield goodProximity goodBinding goodOracle goodSampling goodFinal
  have relation := laws.etaSound omega receipt trace accepted aggregate
    goodAlgebra goodOracle goodSampling
  have residualZero := laws.sumcheckSound omega receipt trace accepted relation
    goodAlgebra goodOracle goodSampling
  exact ⟨trace, relation,
    laws.gammaSound omega receipt trace goodAlgebra goodOracle goodSampling residualZero⟩

end ReductionLaws

/-! ## Byte execution and the local same-coin security game -/

variable {verifier : Verifier suite statement}

structure GameFamily (Omega : Type) [Fintype Omega]
    (Error : Type) (request : List UInt8) where
  ledger : Ext6FailureLedger Omega
  laws : ReductionLaws (suite := suite) (statement := statement) Omega ledger
  execution : Omega -> Option (AcceptedReceipt suite statement verifier request)
  runner : Omega -> OpaqueProofRunner Error
  executionExact : ∀ omega reply, execution omega = some reply ->
    run suite statement verifier (runner omega) request = .ok reply

namespace GameFamily

variable {Omega : Type} [Fintype Omega]
variable {Error : Type} {request : List UInt8}

/-- False acceptance means no BabyBear trace can satisfy the exact emitted
descriptor, while the Lean controller accepted one decoded receipt. -/
def FalseAccept (family : GameFamily (suite := suite) (statement := statement)
    (verifier := verifier) Omega Error request) (omega : Omega) : Prop :=
  ∃ reply, family.execution omega = some reply ∧
    ∀ trace : Nat -> BabyBear, ¬descriptorHolds statement.descriptor trace

theorem execution_runner_bytes
    (family : GameFamily (suite := suite) (statement := statement)
      (verifier := verifier) Omega Error request)
    {omega : Omega} {reply : AcceptedReceipt suite statement verifier request}
    (selected : family.execution omega = some reply) :
    family.runner omega request = .ok reply.proofBytes := by
  exact (run_success_integrity suite statement verifier (family.runner omega)
    request reply (family.executionExact omega reply selected)).1

/-- The exact deployment laws reduce false acceptance to one of the eight
Ext6 events on this same coin. -/
theorem falseAccept_bad
    (family : GameFamily (suite := suite) (statement := statement)
      (verifier := verifier) Omega Error request)
    (omega : Omega) (accepted : family.FalseAccept omega) :
    family.ledger.Bad omega := by
  by_contra good
  obtain ⟨reply, selected, falseStatement⟩ := accepted
  obtain ⟨trace, -, holds⟩ := family.laws.semantic_of_not_bad good
    reply.receipt reply.accepted
  exact falseStatement trace holds

theorem falseAccept_le
    (family : GameFamily (suite := suite) (statement := statement)
      (verifier := verifier) Omega Error request) :
    uniformProb Omega family.FalseAccept ≤ family.ledger.total :=
  le_trans (uniformProb_mono family.falseAccept_bad) family.ledger.bad_le_total

end GameFamily

/-- info: 'Minidregg.Assurance.Ext6GateProofControllerAdmission.Ext6FailureLedger.bad_le_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ext6FailureLedger.bad_le_total
/-- info: 'Minidregg.Assurance.Ext6GateProofControllerAdmission.ReductionLaws.semantic_of_not_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ReductionLaws.semantic_of_not_bad
/-- info: 'Minidregg.Assurance.Ext6GateProofControllerAdmission.GameFamily.falseAccept_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GameFamily.falseAccept_bad
/-- info: 'Minidregg.Assurance.Ext6GateProofControllerAdmission.GameFamily.falseAccept_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms GameFamily.falseAccept_le

end

end Minidregg.Assurance.Ext6GateProofControllerAdmission
