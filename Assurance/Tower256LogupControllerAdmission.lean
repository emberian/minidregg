/-
# Assurance.Tower256LogupControllerAdmission -- one honest LogUp admission seam

`Compiler.Tower256LogupAcceptedRun` already proves that one exact verified
controller execution reaches the indexed-table semantic clause.  Its generic
interface intentionally accepts caller-selected PCS, binding, and ROM
predicates, however, so it is not by itself the deployment-facing admission
boundary.

This module specializes those predicates to one coin in
`ProofCompositionGame`'s common failure ledger.  It also retains the two
position-binding obligations for the exact Merkle schemes opened by the
controller and pins the backend to Lean's recursive Fan--Paar Tower256 codec.
Consequently an admitted value contains:

* the actual verified controller trace and its proved roots-before-challenge
  schedule;
* the exact 32-byte recursive Fan--Paar field codec selected by Lean;
* functional Merkle opening checks performed by the controller, plus explicit
  position-binding premises for the table and checkpoint schemes; and
* non-`True` PCS, commitment-binding, and ROM judgments, all indexed by the
  same game coin.

No cryptographic property is proved here.  No Rust representation or native
semantics is mentioned: native work remains opaque and fallible, and only the
existing Lean controller can construct the terminal attestation.
-/

import Assurance.ProofCompositionGame
import Compiler.BinaryTower256Profile
import Compiler.Tower256LogupAcceptedRun

namespace Minidregg.Assurance.Tower256LogupControllerAdmission

open Minidregg.Assurance.ProofCompositionGame
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.AuthenticatedColumnLogupBridge
open Minidregg.Compiler.BinaryTower256Profile
open Minidregg.Compiler.Logup256ReceiptClause
open Minidregg.Compiler.Tower256CshakeMerkleController
open Minidregg.Compiler.Tower256LogupAcceptedRun
open Minidregg.Compiler.Tower256LogupControllerPlan
open Minidregg.Loom

set_option autoImplicit false

abbrev Tower256 := Minidregg.Compiler.BinaryTower256Profile.Tower256

variable {rowLog tableLog checkpointLog : Nat}
variable {backend : Backend Tower256}
variable {trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog}
variable {claim : IndexedTableReceiptClaim Tower256
  (Fin (2 ^ rowLog)) tableLog}
variable {inputs : ControllerInputs (checkpointLog := checkpointLog)
  backend trace claim}

/-! ## One common-game security boundary for the exact opened schemes -/

/-- Deployment evidence retained beside an accepted controller run.

The table and checkpoint fields name the literal commitment schemes used by
`ControllerInputs.plan`; their `SecurityPremises` contain real
`PositionBinding` propositions rather than a Boolean success flag.  PCS and
ROM judgments are the good events of one common-game coin.  Commitment
binding is retained as its own tagged good event because the semantic LogUp
clause prices it independently of PCS opening soundness. -/
structure ControllerGameSecurity
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    (backend : Backend Tower256)
    {trace : CommittedSemanticTrace (Fin (2 ^ rowLog)) tableLog}
    {claim : IndexedTableReceiptClaim Tower256
      (Fin (2 ^ rowLog)) tableLog}
    (inputs : ControllerInputs (checkpointLog := checkpointLog)
      backend trace claim) : Prop where
  towerProfileExact : backend.tower =
    Minidregg.Compiler.BinaryTower256Profile.profile
  table : Backend.SecurityPremises backend
    (ledger.Good .logupPcs omega)
    (ledger.Good .oracleTransport omega)
    (role := inputs.columns.tableSpec.role)
    (slotId := inputs.columns.tableSpec.slotId)
    (semanticTypeId := inputs.columns.tableSpec.semanticTypeId)
    (domainId := inputs.columns.tableSpec.domainId)
    (domainCodecPin := inputs.columns.tableSpec.domainCodecPin)
    (domainCodec := inputs.columns.tableSpec.domainCodec)
  checkpoint : Backend.SecurityPremises backend
    (ledger.Good .logupPcs omega)
    (ledger.Good .oracleTransport omega)
    (role := inputs.checkpointSpec.role)
    (slotId := inputs.checkpointSpec.slotId)
    (semanticTypeId := inputs.checkpointSpec.semanticTypeId)
    (domainId := inputs.checkpointSpec.domainId)
    (domainCodecPin := inputs.checkpointSpec.domainCodecPin)
    (domainCodec := inputs.checkpointSpec.domainCodec)
  commitmentBinding : ledger.Good .commitmentBinding omega

namespace ControllerGameSecurity

variable {Omega : Type} [Fintype Omega]
variable {ledger : FailureLedger Omega} {omega : Omega}

/-- The backend codec used by every controller column is literally the proved
recursive Fan--Paar Tower256 codec. -/
theorem towerCodecExact
    (security : ControllerGameSecurity ledger omega backend inputs) :
    backend.tower.valueCodec =
      Minidregg.Theory.BinaryTowerCodec.codec := by
  rw [security.towerProfileExact]
  exact Minidregg.Compiler.BinaryTower256Profile.profile_codec_exact

/-- Position binding for the exact table-opening scheme selected by the
controller, retained as a real deployment premise. -/
theorem tablePositionBinding
    (security : ControllerGameSecurity ledger omega backend inputs) :
    (backend.additiveMerkleScheme
      inputs.columns.tableSpec.role
      inputs.columns.tableSpec.slotId
      inputs.columns.tableSpec.semanticTypeId
      inputs.columns.tableSpec.domainId
      inputs.columns.tableSpec.domainCodecPin
      inputs.columns.tableSpec.domainCodec).PositionBinding :=
  security.table.merklePositionBinding

/-- Position binding for the exact challenge-dependent checkpoint column's
scheme.  The scheme is fixed before the challenge; only its committed column
and root depend on the Lean-derived round coin. -/
theorem checkpointPositionBinding
    (security : ControllerGameSecurity ledger omega backend inputs) :
    (backend.additiveMerkleScheme
      inputs.checkpointSpec.role
      inputs.checkpointSpec.slotId
      inputs.checkpointSpec.semanticTypeId
      inputs.checkpointSpec.domainId
      inputs.checkpointSpec.domainCodecPin
      inputs.checkpointSpec.domainCodec).PositionBinding :=
  security.checkpoint.merklePositionBinding

end ControllerGameSecurity

/-! ## Verified execution to admitted indexed lookup -/

/-- The exact clause law families selected by one common-game coin.  Candidate
claim/trace substitution is impossible because each law retains equality to
the controller's expected objects. -/
abbrev GamePcsLaw {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega) :=
  LogupPcsLaw ledger omega claim trace

abbrev GameBindingLaw {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega) :=
  LogupBindingLaw ledger omega claim trace

abbrev GameRomLaw {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega) :=
  LogupRomLaw ledger omega claim

/-- A deployment-facing admitted result.  `clause` is the existing exact
indexed-lookup conclusion; `security` prevents the controller result from
silently dropping the profile, Merkle-binding, or common-game premises that
remain outside deterministic Lean semantics. -/
structure AdmittedLookup
    {Omega : Type} [Fintype Omega]
    (ledger : FailureLedger Omega) (omega : Omega)
    {Error : Type} {runner : NativeRunner Error} {seed : List UInt8}
    [Decidable (LogupFinalStatement trace claim)]
    (execution : VerifiedExecution backend trace claim inputs runner seed) :
    Prop where
  security : ControllerGameSecurity ledger omega backend inputs
  clause : IndexedTableClauseConclusion trace claim
    (GamePcsLaw (trace := trace) (claim := claim) ledger omega)
    (ControllerTranscriptSchedule execution.attestation trace claim
      inputs.columns.required)
    (GameBindingLaw (trace := trace) (claim := claim) ledger omega)
    (GameRomLaw (claim := claim) ledger omega)

namespace AdmittedLookup

variable {Omega : Type} [Fintype Omega]
variable {ledger : FailureLedger Omega} {omega : Omega}
variable {Error : Type} {runner : NativeRunner Error} {seed : List UInt8}
variable [Decidable (LogupFinalStatement trace claim)]
variable {execution : VerifiedExecution backend trace claim inputs runner seed}

/-- The shortest honest end-to-end join: one exact verified execution plus
the exact backend/common-game boundary produces the admitted indexed-table
semantic conclusion. -/
def ofVerifiedExecution
    (execution : VerifiedExecution backend trace claim inputs runner seed)
    (security : ControllerGameSecurity ledger omega backend inputs) :
    AdmittedLookup ledger omega execution where
  security := security
  clause :=
    (execution.acceptedLogupRun
      (GamePcsLaw (trace := trace) (claim := claim) ledger omega)
      (GameBindingLaw (trace := trace) (claim := claim) ledger omega)
      (GameRomLaw (claim := claim) ledger omega)
      (logupPcsLaw_exact ledger omega claim trace
        security.table.pcsAndSampledDecider)
      (logupBindingLaw_exact ledger omega claim trace
        security.commitmentBinding)
      (logupRomLaw_exact ledger omega claim
        security.table.cshakeRomTransport)).indexedTableReceiptClause_of_attestation

/-- Consumer-facing exact admitted semantic result. -/
theorem indexedEvaluation
    (admitted : AdmittedLookup ledger omega execution) :
    claim.claimedEvaluation =
      logupDot (fun row => claim.table (trace.index row)) claim.weights :=
  admitted.clause.indexedEvaluation

/-- The admitted result retains the concrete root-prefix schedule extracted
from the actual terminal attestation. -/
theorem transcriptOrdered
    (admitted : AdmittedLookup ledger omega execution) :
    ControllerTranscriptSchedule execution.attestation trace claim
      inputs.columns.required claim trace :=
  admitted.clause.boundary.transcriptOrdered

end AdmittedLookup

/-- info: 'Minidregg.Assurance.Tower256LogupControllerAdmission.ControllerGameSecurity.towerCodecExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ControllerGameSecurity.towerCodecExact
/-- info: 'Minidregg.Assurance.Tower256LogupControllerAdmission.AdmittedLookup.ofVerifiedExecution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AdmittedLookup.ofVerifiedExecution
/-- info: 'Minidregg.Assurance.Tower256LogupControllerAdmission.AdmittedLookup.indexedEvaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AdmittedLookup.indexedEvaluation

end Minidregg.Assurance.Tower256LogupControllerAdmission
