/-
# Assurance.Tower256RawHistoryFsController -- the raw retained-history FS wire

This module gives the raw retained-history checkpoint an actual Fiat--Shamir
execution boundary.  It is deliberately built from `accReductionBcsRaw`: the
opening scheme is the checkpoint's concrete level-zero Merkle checker, and no
`BindingCommitment`, `PositionBinding`, or replacement universal binding axiom
appears in the carrier.

The verifier artifact owns every value which can change the protocol meaning:
the BCS query coordinates, the SR prover, both lazy-oracle coin vectors, the
request domain, and the codecs for `SrMove`, `SrOutput`, traces, and final
challenge vectors.  Native work returns only fallible byte strings.  A reply
is admitted only when Lean's reflected predicate says that those strings
decode to the literal `srTrace`, `srOut`, and `srFinalChal`, name the exact
checkpoint statement, use the retained history challenges, and pass the raw
BCS verifier at the authoritative semantic head.

Success therefore constructs a `CheckpointHistoryTranscript` containing the
exact roots, columns, and opening proofs submitted in the accepted
`SrOutput`.  Collision resistance, the random-oracle model, and MCA soundness
are not claimed here; this file only closes the executable control and wire
identity seam on which those separately priced predicates operate.
-/

import Assurance.RawSemanticHistoryCheckpointGame
import Selvage.AccRbrBcsRaw
import Selvage.FiatShamir

namespace Minidregg.Assurance.Tower256RawHistoryFsController

open Minidregg.Assurance.RawHistoryBcsOpenings
open Minidregg.Assurance.RawSemanticHistoryCheckpointGame
open Minidregg.Assurance.SemanticHistoryBcsClaimProjection
open Minidregg.Assurance.SemanticHistoryBcsGame
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Assurance.SemanticHistoryFamily
open Minidregg.Assurance.SemanticHistoryWARPAdditiveJoin
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.Tower256AdditiveFriRawAdmission
open Minidregg.Compiler.AuthenticatedColumnPlan
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.Tower256AdditiveFriRawController
open Minidregg.Compiler.Tower256CshakeMerkleController (encodeLength envelope)
open Minidregg.Selvage
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

noncomputable section

universe uSemantics uClauseInput uClauseQuery uClauseReply uClauseOutcome

abbrev TowerField :=
  Minidregg.Compiler.BinaryTower256Profile.Tower256

local instance : DecidableEq TowerField := Classical.decEq _
local instance : Fintype TowerField := Fintype.ofFinite _

variable {ell m n : Nat}
variable {pcs : RawMerklePcs ell}
variable {statement : Statement pcs m}
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n TowerField}
    {headerCells : HistoryAdmissionContext -> BindingIx -> TowerField}
    {C : Submodule TowerField (BoundReceiptIx n -> TowerField)}
    {idealS : BindingCommitment Digest TowerField
      (BoundReceiptIx n) (List UInt8)}

local notation "Coin" => IdealCoin statement
local notation "BoundCheckpoint" => RawCheckpoint
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS)

/-! ## The checkpoint-specialized raw reduction -/

/-- Everything which fixes one raw retained-history protocol instance.  In
particular `queries` is verifier-owned; it is never decoded from a proof. -/
structure Spec (checkpoint : BoundCheckpoint) where
  historyHasLink : 0 < checkpoint.head.foldRounds
  deltaStar : Real
  deltaStarPositive : 0 < deltaStar
  deltaStarLeOne : deltaStar <= 1
  domain : BoundReceiptIx n ↪ TowerField
  degree : Nat
  openedCount : Nat
  codeExact : C = reedSolomonCode domain degree
  degreeLeOpened : degree <= openedCount
  queries : Fin openedCount -> ReceiptCoordinate n
  queriesDistinct : Function.Injective (reindexDomain domain ∘ queries)

namespace Spec

local notation "BoundSpec" checkpoint => Spec
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS) checkpoint

/-- The binding-free reduction actually run by the history verifier. -/
@[reducible] noncomputable def reduction {checkpoint : BoundCheckpoint}
    (spec : BoundSpec checkpoint) : Reduction :=
  accReductionBcsRaw (reindexCode C) checkpoint.head.foldRoot
    (reindexChain (historyChain checkpoint.head))
    receiptCoordinateCountPositive
    (by simpa [historyChain_length] using spec.historyHasLink)
    spec.deltaStar spec.deltaStarPositive spec.deltaStarLeOne
    checkpoint.historyScheme (reindexDomain spec.domain) spec.degree spec.queries

/-- The exact source statement retained by the semantic history head. -/
def historyStatement {checkpoint : BoundCheckpoint}
    (spec : BoundSpec checkpoint) : Stmt spec.reduction :=
  ⟨(), reindexClaim (historyGenesisClaim checkpoint.head),
    reindexWord checkpoint.head.initialWord⟩

/-- Reduction rounds and retained head rounds are the same finite carrier,
through only the two proved list-length equivalences. -/
def roundEquiv {checkpoint : BoundCheckpoint} (spec : BoundSpec checkpoint) :
    Fin spec.reduction.k ≃ Fin checkpoint.head.foldRounds :=
  (chainIndexEquiv (historyChain checkpoint.head)).trans
    (historyRoundEquiv checkpoint.head)

/-- The exact retained challenge at one raw reduction round. -/
def historyChallenge {checkpoint : BoundCheckpoint}
    (spec : BoundSpec checkpoint) (k : Fin spec.reduction.k) : TowerField :=
  checkpoint.head.foldChallenges (spec.roundEquiv k)

/-- The authoritative target pair of the raw verifier. -/
def target {checkpoint : BoundCheckpoint} (spec : BoundSpec checkpoint) :
    spec.reduction.X' × (Fin spec.reduction.n' -> spec.reduction.A') :=
  (reindexClaim checkpoint.head.accumulator,
    reindexWord checkpoint.head.foldedWord)

end Spec

/-! ## Stable wire domain and verifier-owned codecs -/

/-- Stable identities for the four independent history-FS wire alphabets.
The proofs prevent a move, output, trace, or final-challenge codec from being
silently reused as another alphabet. -/
structure WireDomain where
  controllerId : Digest
  requestDomainId : Digest
  moveDomainId : Digest
  outputDomainId : Digest
  traceDomainId : Digest
  challengeDomainId : Digest
  controllerNonzero : controllerId ≠ Digest.mk 0
  requestNonzero : requestDomainId ≠ Digest.mk 0
  moveOutputDistinct : moveDomainId ≠ outputDomainId
  moveTraceDistinct : moveDomainId ≠ traceDomainId
  outputTraceDistinct : outputDomainId ≠ traceDomainId
  challengeDistinctMove : challengeDomainId ≠ moveDomainId
  challengeDistinctOutput : challengeDomainId ≠ outputDomainId
  challengeDistinctTrace : challengeDomainId ≠ traceDomainId

/-- Opaque native return object.  Every component remains bytes until the
verifier's own codec decodes it. -/
structure WireReply where
  traceBytes : List UInt8
  outputBytes : List UInt8
  finalChallengeBytes : List UInt8
deriving Repr

/-- Native authority ends at a fallible byte reply. -/
abbrev OpaqueRunner (Error : Type) :=
  List UInt8 -> Except Error WireReply

/-- Lazily sampled state-restoration parameters on the SAME coin as the raw
additive execution game. -/
structure OraclePlan {checkpoint : BoundCheckpoint} (spec : Spec checkpoint) where
  saltBudget : Nat
  queryBudget : Nat
  prover : SrProver spec.reduction saltBudget
  queryCoins : Coin -> Fin queryBudget -> spec.reduction.Chal
  finalCoins : Coin -> Fin spec.reduction.k -> spec.reduction.Chal

namespace OraclePlan

local notation "BoundSpec" checkpoint => Spec
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS) checkpoint

local notation "BoundPlan" spec => OraclePlan
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS) spec

abbrev Move {checkpoint : BoundCheckpoint} {spec : BoundSpec checkpoint}
    (plan : BoundPlan spec) := SrMove spec.reduction plan.saltBudget

abbrev Output {checkpoint : BoundCheckpoint} {spec : BoundSpec checkpoint}
    (plan : BoundPlan spec) := SrOutput spec.reduction plan.saltBudget

abbrev Trace {checkpoint : BoundCheckpoint} {spec : BoundSpec checkpoint}
    (plan : BoundPlan spec) := List (plan.Move × spec.reduction.Chal)

abbrev FinalChallenges {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} (plan : BoundPlan spec) :=
  Fin spec.reduction.k -> spec.reduction.Chal

/-- The literal SR trace selected by the plan on one common coin. -/
noncomputable def trace {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} (plan : BoundPlan spec) (coin : Coin) :
    plan.Trace :=
  srTrace plan.prover (plan.queryCoins coin)

/-- The final adversarial output after the literal trace responses. -/
noncomputable def output {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} (plan : BoundPlan spec) (coin : Coin) :
    plan.Output :=
  srOut plan.prover (plan.queryCoins coin)

/-- The exact lazy-oracle final challenge vector. -/
noncomputable def finalChallenges {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} (plan : BoundPlan spec) (coin : Coin) :
    plan.FinalChallenges :=
  srFinalChal plan.prover (plan.queryCoins coin) (plan.finalCoins coin)

end OraclePlan

/-- A fully decoded but not yet trusted native reply. -/
structure DecodedReply {checkpoint : BoundCheckpoint} (spec : Spec checkpoint)
    (plan : OraclePlan spec) where
  trace : plan.Trace
  output : plan.Output
  finalChallenges : plan.FinalChallenges

/-- The exact predicate reflected by the Lean-owned verifier.  It connects the
decoded bytes to the SR game, the canonical total oracle, the raw BCS verifier,
and the retained semantic history challenge schedule. -/
def ExecutionExact {checkpoint : BoundCheckpoint} {spec : Spec checkpoint}
    {plan : OraclePlan spec} (coin : Coin) (reply : DecodedReply spec plan) : Prop :=
  reply.trace = plan.trace coin ∧
  reply.output = plan.output coin ∧
  reply.finalChallenges = plan.finalChallenges coin ∧
  reply.output.stmt = spec.historyStatement ∧
  reply.finalChallenges = spec.historyChallenge ∧
  fiatShamir spec.reduction plan.saltBudget
      (fsOracle reply.output reply.finalChallenges) reply.output =
    some spec.target

/-- Verifier-owned wire codecs and the reflected execution test.  Individual
`SrMove` and `SrOutput` codecs are retained even though the native response is
decoded through a trace codec: they are the stable ABI for interactive and
batched runners respectively. -/
structure Verifier {checkpoint : BoundCheckpoint} (spec : Spec checkpoint)
    (plan : OraclePlan spec) where
  domain : WireDomain
  moveCodecPin : CodecPin
  outputCodecPin : CodecPin
  traceCodecPin : CodecPin
  finalChallengeCodecPin : CodecPin
  moveCodec : LawfulCodec plan.Move
  outputCodec : LawfulCodec plan.Output
  traceCodec : LawfulCodec plan.Trace
  finalChallengeCodec : LawfulCodec plan.FinalChallenges
  check : Coin -> DecodedReply spec plan -> Bool
  check_iff : ∀ coin reply, check coin reply = true ↔ ExecutionExact coin reply

namespace Verifier

local notation "BoundSpec" checkpoint => Spec
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS) checkpoint

local notation "BoundPlan" spec => OraclePlan
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS) spec

/-- The request frame is selected by the verifier's domain, never by native
code.  Every item is self-delimiting. -/
def requestBytes {checkpoint : BoundCheckpoint} {spec : BoundSpec checkpoint}
    {plan : BoundPlan spec} (verifier : Verifier spec plan)
    (payload : List UInt8) : List UInt8 :=
  envelope (encodeLength verifier.domain.controllerId.value) ++
    envelope (encodeLength verifier.domain.requestDomainId.value) ++
      envelope payload

/-- Decode all three native byte buffers with verifier-owned codecs. -/
def decode {checkpoint : BoundCheckpoint} {spec : BoundSpec checkpoint}
    {plan : BoundPlan spec} (verifier : Verifier spec plan)
    (reply : WireReply) : Option (DecodedReply spec plan) := do
  let trace <- verifier.traceCodec.decode reply.traceBytes
  let output <- verifier.outputCodec.decode reply.outputBytes
  let finalChallenges <-
    verifier.finalChallengeCodec.decode reply.finalChallengeBytes
  pure ⟨trace, output, finalChallenges⟩

@[simp] theorem decode_encoded {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {plan : BoundPlan spec}
    (verifier : Verifier spec plan) (reply : DecodedReply spec plan) :
    verifier.decode
      ⟨verifier.traceCodec.encode reply.trace,
        verifier.outputCodec.encode reply.output,
        verifier.finalChallengeCodec.encode reply.finalChallenges⟩ = some reply := by
  simp [decode, verifier.traceCodec.decode_encode,
    verifier.outputCodec.decode_encode,
    verifier.finalChallengeCodec.decode_encode]

end Verifier

/-! ## Opaque execution and exact accepted result -/

inductive Failure (Error : Type)
  | native (error : Error)
  | invalidEncoding
  | rejected
deriving Repr

/-- A successful reply retains the precise bytes and the reflected SR/FS
execution theorem. -/
structure AcceptedExecution {checkpoint : BoundCheckpoint}
    (spec : Spec checkpoint) (plan : OraclePlan spec)
    (verifier : Verifier spec plan) (coin : Coin) (payload : List UInt8) where
  wire : WireReply
  decoded : DecodedReply spec plan
  decoding : verifier.decode wire = some decoded
  exact : ExecutionExact coin decoded

/-- Run arbitrary native work, then decode and reflect all protocol meaning in
Lean. -/
def run {Error : Type} {checkpoint : BoundCheckpoint}
    {spec : Spec checkpoint} {plan : OraclePlan spec}
    (verifier : Verifier spec plan) (runner : OpaqueRunner Error)
    (coin : Coin) (payload : List UInt8) :
    Except (Failure Error) (AcceptedExecution spec plan verifier coin payload) :=
  match returned : runner (verifier.requestBytes payload) with
  | .error error => .error (.native error)
  | .ok wire =>
      match decoded : verifier.decode wire with
      | none => .error .invalidEncoding
      | some reply =>
          if checked : verifier.check coin reply = true then
            .ok ⟨wire, reply, decoded, (verifier.check_iff coin reply).mp checked⟩
          else .error .rejected

theorem run_success_integrity {Error : Type}
    {checkpoint : BoundCheckpoint} {spec : Spec checkpoint}
    {plan : OraclePlan spec} (verifier : Verifier spec plan)
    (runner : OpaqueRunner Error) (coin : Coin) (payload : List UInt8)
    (accepted : AcceptedExecution spec plan verifier coin payload)
    (success : run verifier runner coin payload = .ok accepted) :
    runner (verifier.requestBytes payload) = .ok accepted.wire ∧
      verifier.decode accepted.wire = some accepted.decoded ∧
      ExecutionExact coin accepted.decoded := by
  unfold run at success
  split at success
  next error failed => simp at success
  next wire returned =>
    split at success
    next decodeFailed => simp at success
    next reply decoded =>
      split at success
      next checked =>
        simp only [Except.ok.injEq] at success
        subst accepted
        exact ⟨returned, decoded, (verifier.check_iff coin reply).mp checked⟩
      next rejected => simp at success

/-! ## Accepted SR output to the raw checkpoint tape -/

namespace AcceptedExecution

local notation "BoundSpec" checkpoint => Spec
  (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) (idealS := idealS) checkpoint

/-- Raw FS acceptance is literally raw reduction acceptance at the decoded
final challenge vector. -/
theorem rawVerifierAccepted {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {plan : OraclePlan spec}
    {verifier : Verifier spec plan} {coin : Coin} {payload : List UInt8}
    (accepted : AcceptedExecution spec plan verifier coin payload) :
    spec.reduction.verify accepted.decoded.output.stmt.idx
        accepted.decoded.output.stmt.x accepted.decoded.output.stmt.y
        accepted.decoded.output.πs accepted.decoded.finalChallenges =
      some spec.target := by
  rw [← fiatShamir_fsOracle]
  exact accepted.exact.2.2.2.2.2

/-- Every submitted column in the accepted `SrOutput` passed the concrete raw
opening checker at the verifier-owned query coordinates. -/
theorem columnsAccepted {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {plan : OraclePlan spec}
    {verifier : Verifier spec plan} {coin : Coin} {payload : List UInt8}
    (accepted : AcceptedExecution spec plan verifier coin payload) :
    ∀ k, ColsOpen checkpoint.historyScheme spec.queries
      (accepted.decoded.output.πs k) := by
  have verified := accepted.rawVerifierAccepted
  have stmtExact := accepted.exact.2.2.2.1
  rw [stmtExact] at verified
  exact (accReductionBcsRaw.verify_eq_some_iff
    (reindexCode C) checkpoint.head.foldRoot
    (reindexChain (historyChain checkpoint.head))
    receiptCoordinateCountPositive
    (by simpa [historyChain_length] using spec.historyHasLink)
    spec.deltaStar spec.deltaStarPositive spec.deltaStarLeOne
    checkpoint.historyScheme (reindexDomain spec.domain) spec.degree spec.queries
    (reindexClaim (historyGenesisClaim checkpoint.head))
    (reindexWord checkpoint.head.initialWord)
    accepted.decoded.output.πs accepted.decoded.finalChallenges
    spec.target.1 spec.target.2).mp verified |>.1

/-- The accepted native reply projected to the exact raw history carrier.
Messages are not copied from any parallel schedule: each is the corresponding
`SrOutput.πs`, including its submitted root, columns, and opening paths. -/
def tape {checkpoint : BoundCheckpoint} {spec : BoundSpec checkpoint}
    {plan : OraclePlan spec} {verifier : Verifier spec plan}
    {coin : Coin} {payload : List UInt8}
    (accepted : AcceptedExecution spec plan verifier coin payload) :
    CheckpointHistoryTranscript
      (ell := ell) (m := m) (n := n) (pcs := pcs) (statement := statement)
      (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C) (idealS := idealS)
      (checkpoint := checkpoint) (domain := spec.domain)
      (degree := spec.degree) (openedCount := spec.openedCount) where
  codeExact := spec.codeExact
  degreeLeOpened := spec.degreeLeOpened
  queries := spec.queries
  queriesDistinct := spec.queriesDistinct
  messages := fun j => accepted.decoded.output.πs (spec.roundEquiv.symm j)
  columnsAccepted := fun j => accepted.columnsAccepted (spec.roundEquiv.symm j)

@[simp] theorem tape_queries {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {plan : OraclePlan spec}
    {verifier : Verifier spec plan} {coin : Coin} {payload : List UInt8}
    (accepted : AcceptedExecution spec plan verifier coin payload) :
    accepted.tape.queries = spec.queries := rfl

@[simp] theorem tape_message {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {plan : OraclePlan spec}
    {verifier : Verifier spec plan} {coin : Coin} {payload : List UInt8}
    (accepted : AcceptedExecution spec plan verifier coin payload)
    (j : Fin checkpoint.head.foldRounds) :
    (accepted.tape.messages j) =
      accepted.decoded.output.πs (spec.roundEquiv.symm j) := rfl

theorem tape_challengesExact {checkpoint : BoundCheckpoint}
    {spec : BoundSpec checkpoint} {plan : OraclePlan spec}
    {verifier : Verifier spec plan} {coin : Coin} {payload : List UInt8}
    (accepted : AcceptedExecution spec plan verifier coin payload)
    (j : Fin checkpoint.head.foldRounds) :
    accepted.decoded.finalChallenges (spec.roundEquiv.symm j) =
      checkpoint.head.foldChallenges j := by
  rw [accepted.exact.2.2.2.2.1]
  simp [Spec.historyChallenge]

end AcceptedExecution

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.Tower256RawHistoryFsController.run_success_integrity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms run_success_integrity
/-- info: 'Minidregg.Assurance.Tower256RawHistoryFsController.AcceptedExecution.columnsAccepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedExecution.columnsAccepted
/-- info: 'Minidregg.Assurance.Tower256RawHistoryFsController.AcceptedExecution.tape_challengesExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AcceptedExecution.tape_challengesExact

end

end Minidregg.Assurance.Tower256RawHistoryFsController
