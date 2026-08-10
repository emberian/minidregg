/-
# Compiler.Logup256ReceiptClause -- manifest-closed indexed LogUp256 semantics

This module joins the existing canonical address link with the characteristic-
independent LogUp* pushforward identity.  A committed semantic trace owns one index
and its Boolean address word per row.  The clause requires those committed words to
be the canonical decoding of the semantic indices, derives literal unit-vector
incidence and exact pushforward, and concludes the indexed table-evaluation relation.

Tower256 arithmetic adequacy, PCS opening soundness, transcript order, commitment
collision resistance/binding, and the Fiat--Shamir random-oracle model remain explicit
boundary premises.  They are not implemented or proved here.  No protocol, native
verifier, or cross-characteristic map is introduced.

The v1 generic GF(2^64) clause pin cannot be reused: it names another opaque relation,
has the wrong degree, and requires an unrelated GF(2)-to-Ext6 bridge.  This clause uses
the distinct declared GF(2^256) carrier profile and has no bridge requirement.
-/
import Compiler.MinidreggV1Artifact
import Loom.LogupIndexLink

namespace Minidregg.Compiler.Logup256ReceiptClause

open Minidregg.Theory.TypedAuthorization
open Minidregg.Compiler.SemanticManifest
open Minidregg.Loom

set_option autoImplicit false

/-! ## A distinct, manifest-closed dialect relation pin -/

def clausePin : DialectClauseDecl where
  clauseId := MinidreggV1Artifact.id 404
  relationId := MinidreggV1Artifact.id 414
  carrierProfileId := MinidreggV1Artifact.gf2Tower256Carrier.id
  statementCodecId := MinidreggV1Artifact.dialectStatementCodec.codecId
  proofCodecId := MinidreggV1Artifact.dialectProofCodec.codecId
  proofSuiteId := MinidreggV1Artifact.id 424
  verifierControllerDigest := MinidreggV1Artifact.id 434
  requiredBridgeIds := []

/-- The base V1 manifest already declares the GF(2^256) carrier and codec, but this
semantic clause remains an extension: no concrete proof-suite/controller realization or
Rust correspondence is claimed by the base artifact. -/
def manifest : Manifest :=
  { MinidreggV1Artifact.manifest with
    dialectClauses := [clausePin] }

theorem manifest_wellFormed : manifest.WellFormed where
  codecIdsUnique := MinidreggV1Artifact.manifest_wellFormed.codecIdsUnique
  carrierIdsUnique := MinidreggV1Artifact.manifest_wellFormed.carrierIdsUnique
  bridgeIdsUnique := MinidreggV1Artifact.manifest_wellFormed.bridgeIdsUnique
  dialectClauseIdsUnique := by
    change ([MinidreggV1Artifact.id 404] : List Digest).Nodup
    decide
  receiptCodecClosed :=
    MinidreggV1Artifact.manifest_wellFormed.receiptCodecClosed
  mpcBasesClosed :=
    MinidreggV1Artifact.manifest_wellFormed.mpcBasesClosed
  bridgeEndpointsClosed :=
    MinidreggV1Artifact.manifest_wellFormed.bridgeEndpointsClosed
  dialectClausesClosed := by
    intro clause member
    simp only [manifest, List.mem_singleton] at member
    subst clause
    refine
      ⟨⟨MinidreggV1Artifact.gf2Tower256Carrier, by decide⟩,
       ⟨MinidreggV1Artifact.dialectStatementCodec, by decide⟩,
       ⟨MinidreggV1Artifact.dialectProofCodec, by decide⟩, ?_⟩
    intro bridgeId member
    simp [clausePin] at member

theorem clause_pin_registered :
    manifest.lookupClause clausePin.clauseId = some clausePin := by
  decide

theorem clause_pin_registry_closed :
    manifest.lookupCarrier clausePin.carrierProfileId =
        some MinidreggV1Artifact.gf2Tower256Carrier ∧
    manifest.lookupCodec clausePin.statementCodecId =
        some MinidreggV1Artifact.dialectStatementCodec ∧
    manifest.lookupCodec clausePin.proofCodecId =
        some MinidreggV1Artifact.dialectProofCodec ∧
    clausePin.requiredBridgeIds = [] := by
  decide

/-- The clause selects the distinct 256-bit profile and its declared value codec.  This
is manifest identity/shape data only, not a theorem about `prover::Tower256`. -/
theorem clause_pin_tower256_profile :
    clausePin.carrierProfileId = MinidreggV1Artifact.gf2Tower256Carrier.id ∧
    MinidreggV1Artifact.gf2Tower256Carrier =
      .gf2Tower (MinidreggV1Artifact.id 205)
        MinidreggV1Artifact.fanPaarTowerId
        MinidreggV1Artifact.fanPaarRecursiveBasisId
        MinidreggV1Artifact.tower256ValueCodec.codecId 256 := by
  exact ⟨rfl, rfl⟩

/-! ## Committed semantic trace and canonical address link -/

universe u

/-- The semantic trace fixes both the indexed map and its committed Boolean address
columns.  Roots are identifiers only; this type asserts no hash property. -/
structure CommittedSemanticTrace (κ : Type u) (k : Nat) where
  semanticTraceRoot : Digest
  addressRoot : Digest
  weightsRoot : Digest
  tableRoot : Digest
  index : κ → Fin (2 ^ k)
  addressBits : κ → Fin k → Bool

/-- The address columns are linked only when they are literally the canonical binary
decoding of the fixed semantic index in every committed row. -/
def CanonicalAddressLinked { κ : Type u } {k : Nat}
    (trace : CommittedSemanticTrace κ k) : Prop :=
  ∀ row, trace.addressBits row = binaryAddressBits k (trace.index row)

variable {F : Type*} [Field F]
variable {κ : Type u} [Fintype κ]
variable {k : Nat}

/-- One committed address bit embedded into the clause field. -/
def committedAddressColumn (trace : CommittedSemanticTrace κ k)
    (bit : Fin k) (row : κ) : F :=
  cubePt (trace.addressBits row) bit

theorem committedAddressColumn_eq_canonical
    (trace : CommittedSemanticTrace κ k) (linked : CanonicalAddressLinked trace)
    (bit : Fin k) (row : κ) :
    committedAddressColumn (F := F) trace bit row =
      canonicalIndexColumn k trace.index bit row := by
  simp [committedAddressColumn, canonicalIndexColumn, linked row]

theorem committedAddressColumn_boolean
    (trace : CommittedSemanticTrace κ k) (linked : CanonicalAddressLinked trace)
    (bit : Fin k) (row : κ) :
    committedAddressColumn (F := F) trace bit row = 0 ∨
      committedAddressColumn (F := F) trace bit row = 1 := by
  rw [committedAddressColumn_eq_canonical trace linked]
  exact canonicalIndexColumn_boolean k trace.index bit row

/-- Incidence reconstructed from the committed address columns, not from a prover-
selected field-valued address. -/
def committedIncidence (trace : CommittedSemanticTrace κ k)
    (row : κ) (tableIndex : Fin (2 ^ k)) : F :=
  binaryLookupEq k (cubePt (trace.addressBits row)) tableIndex

theorem committedIncidence_eq_canonical
    (trace : CommittedSemanticTrace κ k) (linked : CanonicalAddressLinked trace)
    (row : κ) :
    committedIncidence (F := F) trace row =
      canonicalIncidence k trace.index row := by
  funext tableIndex
  apply congrArg (fun address : Fin k → F => binaryLookupEq k address tableIndex)
  funext bit
  simp [committedIncidence, canonicalIncidence, canonicalIndexColumn, linked row,
    cubePt]

/-- Literal whole-vector equality rules out the characteristic-two parity shortcut. -/
theorem committedIncidence_eq_unitVector
    (trace : CommittedSemanticTrace κ k) (linked : CanonicalAddressLinked trace)
    (row : κ) :
    committedIncidence (F := F) trace row = binaryUnitVector (trace.index row) := by
  rw [committedIncidence_eq_canonical trace linked]
  exact canonicalIncidence_eq_unitVector k trace.index row

/-- Scatter the equality weights through the incidence reconstructed from committed
canonical Boolean addresses. -/
noncomputable def committedIncidencePushforward
    (trace : CommittedSemanticTrace κ k) (weights : κ → F) :
    Fin (2 ^ k) → F :=
  fun tableIndex => ∑ row, committedIncidence trace row tableIndex * weights row

theorem committedIncidencePushforward_eq_canonical
    (trace : CommittedSemanticTrace κ k) (linked : CanonicalAddressLinked trace)
    (weights : κ → F) :
    committedIncidencePushforward trace weights =
      canonicalIncidencePushforward k trace.index weights := by
  classical
  funext tableIndex
  apply Finset.sum_congr rfl
  intro row _
  rw [committedIncidence_eq_canonical trace linked]

theorem committedIncidencePushforward_eq_logupPushforward
    (trace : CommittedSemanticTrace κ k) (linked : CanonicalAddressLinked trace)
    (weights : κ → F) :
    committedIncidencePushforward trace weights =
      logupPushforward trace.index weights := by
  rw [committedIncidencePushforward_eq_canonical trace linked]
  exact canonicalIncidencePushforward_eq_logupPushforward k trace.index weights

/-! ## Receipt boundary premises and semantic conclusion -/

/-- First-order data exposed by the indexed-table receipt clause. -/
structure IndexedTableReceiptClaim (F : Type*) (κ : Type u) (k : Nat) where
  semanticTraceRoot : Digest
  addressRoot : Digest
  weightsRoot : Digest
  tableRoot : Digest
  weights : κ → F
  table : Fin (2 ^ k) → F
  claimedEvaluation : F

/-- Explicit proof-system boundary.  `PCSOpeningSound`, `CommitmentBindingCR`, and
`RandomOracleModel` are deployment predicates supplied by the selected Tower256
clause.  This semantic module neither defines nor discharges them.  The concrete
equalities are the semantic consequences that the clause admission path must recheck. -/
structure Tower256ClausePremises
    (trace : CommittedSemanticTrace κ k)
    (claim : IndexedTableReceiptClaim F κ k)
    (PCSOpeningSound : IndexedTableReceiptClaim F κ k →
      CommittedSemanticTrace κ k → Prop)
    (TranscriptSchedule : IndexedTableReceiptClaim F κ k →
      CommittedSemanticTrace κ k → Prop)
    (CommitmentBindingCR : IndexedTableReceiptClaim F κ k →
      CommittedSemanticTrace κ k → Prop)
    (RandomOracleModel : IndexedTableReceiptClaim F κ k → Prop) : Prop where
  /-- The abstract clause field has exactly the characteristic and cardinality pinned by
  the manifest profile.  This still asserts no representation correspondence. -/
  tower256Characteristic : CharP F 2
  tower256Cardinality : Nat.card F = 2 ^ 256
  tower256Arithmetic :
    claim.claimedEvaluation =
      logupDot claim.table (committedIncidencePushforward trace claim.weights)
  pcsOpeningSound : PCSOpeningSound claim trace
  pcsRootsBound :
    claim.addressRoot = trace.addressRoot ∧
    claim.weightsRoot = trace.weightsRoot ∧
    claim.tableRoot = trace.tableRoot
  /-- A deployment supplies a typed roots-before-challenge schedule.  The
  semantic clause no longer accepts unrelated timestamp integers as evidence. -/
  transcriptOrdered : TranscriptSchedule claim trace
  commitmentBindingCR : CommitmentBindingCR claim trace
  semanticTraceRootBound : claim.semanticTraceRoot = trace.semanticTraceRoot
  fiatShamirROM : RandomOracleModel claim

/-- The complete semantic result carried past clause admission.  It retains the
external Tower256/PCS/transcript/CR/ROM premises and exposes the Lean-derived address,
incidence, pushforward, and indexed-evaluation facts. -/
structure IndexedTableClauseConclusion
    (trace : CommittedSemanticTrace κ k)
    (claim : IndexedTableReceiptClaim F κ k)
    (PCSOpeningSound : IndexedTableReceiptClaim F κ k →
      CommittedSemanticTrace κ k → Prop)
    (TranscriptSchedule : IndexedTableReceiptClaim F κ k →
      CommittedSemanticTrace κ k → Prop)
    (CommitmentBindingCR : IndexedTableReceiptClaim F κ k →
      CommittedSemanticTrace κ k → Prop)
    (RandomOracleModel : IndexedTableReceiptClaim F κ k → Prop) : Prop where
  boundary : Tower256ClausePremises trace claim PCSOpeningSound TranscriptSchedule
    CommitmentBindingCR RandomOracleModel
  addressColumnsBoolean : ∀ bit row,
    committedAddressColumn (F := F) trace bit row = 0 ∨
      committedAddressColumn (F := F) trace bit row = 1
  incidenceIsLiteralUnitVector : ∀ row,
    committedIncidence (F := F) trace row = binaryUnitVector (trace.index row)
  pushforwardExact :
    committedIncidencePushforward trace claim.weights =
      logupPushforward trace.index claim.weights
  indexedEvaluation :
    claim.claimedEvaluation =
      logupDot (fun row => claim.table (trace.index row)) claim.weights

/-- The one semantic receipt clause: canonical address linkage plus the explicit
Tower256 boundary premises imply the exact indexed table-evaluation relation. -/
theorem indexedTableReceiptClause
    (trace : CommittedSemanticTrace κ k)
    (claim : IndexedTableReceiptClaim F κ k)
    (PCSOpeningSound : IndexedTableReceiptClaim F κ k →
      CommittedSemanticTrace κ k → Prop)
    (TranscriptSchedule : IndexedTableReceiptClaim F κ k →
      CommittedSemanticTrace κ k → Prop)
    (CommitmentBindingCR : IndexedTableReceiptClaim F κ k →
      CommittedSemanticTrace κ k → Prop)
    (RandomOracleModel : IndexedTableReceiptClaim F κ k → Prop)
    (linked : CanonicalAddressLinked trace)
    (premises : Tower256ClausePremises trace claim PCSOpeningSound TranscriptSchedule
      CommitmentBindingCR RandomOracleModel) :
    IndexedTableClauseConclusion trace claim PCSOpeningSound TranscriptSchedule
      CommitmentBindingCR RandomOracleModel where
  boundary := premises
  addressColumnsBoolean := fun bit row =>
    committedAddressColumn_boolean trace linked bit row
  incidenceIsLiteralUnitVector := fun row =>
    committedIncidence_eq_unitVector trace linked row
  pushforwardExact :=
    committedIncidencePushforward_eq_logupPushforward trace linked claim.weights
  indexedEvaluation := by
    calc
      claim.claimedEvaluation =
          logupDot claim.table (committedIncidencePushforward trace claim.weights) :=
        premises.tower256Arithmetic
      _ = logupDot claim.table (logupPushforward trace.index claim.weights) := by
        rw [committedIncidencePushforward_eq_logupPushforward trace linked]
      _ = logupDot (fun row => claim.table (trace.index row)) claim.weights :=
        (logup_pullback_pushforward trace.index claim.weights claim.table).symm

/-- info: 'Minidregg.Compiler.Logup256ReceiptClause.committedIncidence_eq_unitVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms committedIncidence_eq_unitVector
/-- info: 'Minidregg.Compiler.Logup256ReceiptClause.committedIncidencePushforward_eq_logupPushforward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms committedIncidencePushforward_eq_logupPushforward
/-- info: 'Minidregg.Compiler.Logup256ReceiptClause.indexedTableReceiptClause' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms indexedTableReceiptClause

end Minidregg.Compiler.Logup256ReceiptClause
