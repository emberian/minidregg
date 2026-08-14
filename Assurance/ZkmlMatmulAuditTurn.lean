/-
# Assurance.ZkmlMatmulAuditTurn — one authorized, durable linear-layer audit

This is the first deliberately narrow vertical slice from the reorientation
note.  It does not call the still-unbuilt succinct BaseFold byte controller.
Instead, one fixed 2x2 F7 contraction is checked exactly by Lean and the audit
evidence carries:

* the registered, versioned audit/checker identity;
* equality of all four post-state cells with the literal contraction;
* all three root-bound MLE claims (output, left, and right);
* an accepted contraction sumcheck transcript; and
* the exact algebraic BaseFold opening budget which a scalable replacement
  must refine without hiding query/CR/FS terms.

That evidence is a disclosure on the same request-indexed `CommittedTurn` that
owns authorization, effects, state roots, and the canonical receipt relation.
The exact four result bytes and audit identity then enter one
`DurableDataIntent`; the positive execution installs them atomically, appends
the audit event, and retries as an exact replay.  A same-transaction audit-byte
tamper is a conflict.

The claim ceiling is intentional: this is an exact-recompute audit for a tiny
turn, not a succinct proof, native-verifier refinement, cryptographic binding
claim, physical durability theorem, or production registry.
-/
import Assurance.ZkmlMatmulBaseFold
import Assurance.SemanticTurnReceipt
import Kernel.DurableDataIntent

namespace Minidregg.Assurance.ZkmlMatmulAuditTurn

open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticTurnReceipt
open Minidregg.Assurance.MatmulExample
open Minidregg.Assurance.MatmulCommitmentExample
open Minidregg.Kernel.DurableCommitProtocol
open Minidregg.Kernel.DurableDataIntent
open Minidregg.Selvage
open Minidregg.Theory
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.ResourceCost
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

abbrev F := ZMod 7
abbrev Key := Fin 4

/-! ## The exact semantic computation -/

/-- Row-major output cells: `[[5,1],[1,1]]` in F7. -/
def output : Store Key F := ![5, 1, 1, 1]

def rowBits (key : Key) : Fin 1 → Bool :=
  fun _ => decide (2 ≤ key.val)

def columnBits (key : Key) : Fin 1 → Bool :=
  fun _ => decide (key.val % 2 = 1)

/-- Every installed output cell is the literal matrix contraction, not a
separately asserted fixture. -/
theorem output_is_contraction (key : Key) :
    output key = matmulTable eA eB (rowBits key) (columnBits key) := by
  fin_cases key <;> decide

def before : Store Key F := fun _ => 0

def delta : ReceiptDelta before output where
  touched := Finset.univ
  frame := by simp

/-- A small injective base-7 state projection at the fixed four-cell width.
The leading `8` makes the zero state equal the demo request's pinned pre-root. -/
def stateRoot (state : Store Key F) : Digest :=
  ⟨8 + (state 0).val + 7 * (state 1).val +
    49 * (state 2).val + 343 * (state 3).val⟩

def stateCommitment : StateCommitment Key F where
  root := stateRoot

@[simp] theorem before_root : stateCommitment.root before = demoRequest.preStateRoot := by
  rfl

/-! ## Versioned exact-audit evidence -/

structure AuditIdentity where
  suiteId : Digest
  checkerId : Digest
  statementId : Digest
  codecVersion : Nat
  deriving DecidableEq, Repr

def auditIdentity : AuditIdentity :=
  ⟨⟨101⟩, ⟨102⟩, ⟨103⟩, 1⟩

/-- The bounded registry selected by this slice.  Membership is evidence; a
production registry and authenticated upgrade policy remain separate. -/
def auditRegistry : List AuditIdentity := [auditIdentity]

theorem auditIdentity_registered : auditIdentity ∈ auditRegistry := by simp [auditRegistry]

abbrev S := idealCommitment F (Fin 4)

noncomputable def claims :=
  honestMatmulMleClaims S S S dom₇₄ dom₇₄ dom₇₄ eA eB
    (matmulTable eA eB) ![3] ![5] ![2]

theorem claims_hold :
    claims.output.Holds S dom₇₄ ∧
      claims.left.Holds S dom₇₄ ∧ claims.right.Holds S dom₇₄ := by
  exact honestMatmulMleClaims_hold S S S dom₇₄ dom₇₄ dom₇₄ eA eB
    (matmulTable eA eB) ![3] ![5] ![2]

/-- The inner contraction proof is a real accepted degree-three protocol
event on the fixed challenge `2`. -/
theorem contraction_sumcheck_accepts :
    SumcheckAccepts (v := 1)
      (matmulHonest eA eB ![3] ![5] (chalOf ![2]))
      (matmulHonest eA eB ![3] ![5] (chalOf ![2]))
      (mle₂ (matmulTable eA eB) ![3] ![5])
      (mle₂ (matmulTable eA eB) ![3] ![5]) ![2] :=
  matmulHonest_complete eA eB ![3] ![5] ![2]

/-- The toy field makes the scalable opening budget larger than one.  Keeping
that number visible prevents this exact audit from being advertised as a
cryptographically useful succinct configuration. -/
theorem opening_budget_exact :
    matmulBaseFoldIorAlgebraicBudget F 1 1 1 = (18 : ℝ) / 7 := by
  rw [matmulBaseFoldIorAlgebraicBudget_eq]
  norm_num

/-- Proof-relevant evidence carried by the semantic receipt. -/
structure AuditEvidence where
  identity : AuditIdentity
  identityExact : identity = auditIdentity
  registered : identity ∈ auditRegistry
  outputExact : ∀ key, output key =
    matmulTable eA eB (rowBits key) (columnBits key)
  openingsExact : claims.output.Holds S dom₇₄ ∧
    claims.left.Holds S dom₇₄ ∧ claims.right.Holds S dom₇₄
  contractionAccepted :
    SumcheckAccepts (v := 1)
      (matmulHonest eA eB ![3] ![5] (chalOf ![2]))
      (matmulHonest eA eB ![3] ![5] (chalOf ![2]))
      (mle₂ (matmulTable eA eB) ![3] ![5])
      (mle₂ (matmulTable eA eB) ![3] ![5]) ![2]
  openingBudgetExact :
    matmulBaseFoldIorAlgebraicBudget F 1 1 1 = (18 : ℝ) / 7

def auditEvidence : AuditEvidence where
  identity := auditIdentity
  identityExact := rfl
  registered := auditIdentity_registered
  outputExact := output_is_contraction
  openingsExact := claims_hold
  contractionAccepted := contraction_sumcheck_accepts
  openingBudgetExact := opening_budget_exact

/-- The evidence is admitted only as a disclosure of this exact authorized
request and exact registry identity. -/
def disclosurePolicy : DisclosurePolicy AuditEvidence where
  Permitted := fun {kind} request evidence =>
    (⟨kind, request⟩ : Σ requestKind, Request requestKind) =
        ⟨.object, demoRequest⟩ ∧
      evidence.identity = auditIdentity

abbrev Effect := Nat

def effectSemantics : EffectSemantics Key F Effect where
  digest := fun effects => ⟨effects.sum⟩
  Realizes := by
    intro _kind _request effects _pre post _delta
    exact effects = [6] ∧ post = output

/-- The authorized semantic commit.  The effect digest is the same `6` pinned
by `demoRequest`; its post state is the audited contraction output. -/
def commit : CommittedTurn demoPortal demoState demoRequest stateCommitment
    effectSemantics disclosurePolicy before where
  authorization := demo_authorized_positive
  post := output
  delta := delta
  postStateRoot := stateCommitment.root output
  postRootBound := rfl
  effects := [6]
  effectsDigestBound := rfl
  effectsRealize := ⟨rfl, rfl⟩
  disclosures := [auditEvidence]
  disclosuresPermitted := by
    intro evidence member
    simp only [List.mem_singleton] at member
    subst evidence
    exact ⟨rfl, rfl⟩

def receipt : TurnReceipt demoPortal demoState .object Unit stateCommitment
    effectSemantics disclosurePolicy :=
  TurnReceipt.committed demoRequest before before_root.symm commit

theorem receipt_core_relation :
    SemanticReceiptRelation commit.coreClaim.witness.encode :=
  commit.coreRelation

theorem receipt_post_is_contraction (key : Key) :
    receipt.post key = matmulTable eA eB (rowBits key) (columnBits key) := by
  simpa [receipt] using output_is_contraction key

/-! ## Canonical durable settlement -/

def beforeBytes : List UInt8 := [0, 0, 0, 0]
def outputBytes : List UInt8 := [5, 1, 1, 1]

/-- The byte root is intentionally only a four-byte fixture codec.  It agrees
exactly with `stateRoot` on this slice; no general collision-resistance claim
is made. -/
def rootBytes : List UInt8 → Digest
  | [a, b, c, d] =>
      ⟨8 + a.toNat + 7 * b.toNat + 49 * c.toNat + 343 * d.toNat⟩
  | _ => ⟨0⟩

theorem before_bytes_bind : rootBytes beforeBytes = stateCommitment.root before := by
  rfl

theorem output_bytes_bind : rootBytes outputBytes = commit.postStateRoot := by
  rfl

def computationCell : CellId := ⟨201⟩

def auditEventBytes : List UInt8 :=
  [1, 101, 102, 103, 5, 1, 1, 1]

def auditEvent : StableEvent where
  codecVersion := auditIdentity.codecVersion
  domain := auditIdentity.statementId
  eventId := auditIdentity.checkerId
  canonicalBytes := auditEventBytes

def resultWrite : DataWrite where
  cellId := computationCell
  expectedPre := stateCommitment.root before
  exactPost := commit.postStateRoot
  canonicalPostBytes := outputBytes

def durableIntent : DataIntent rootBytes where
  transactionId := ⟨200⟩
  writes := [resultWrite]
  readGuards := []
  nullifiers := []
  exactCharge := 0
  event := auditEvent
  postRootsBound := by
    intro write member
    simp only [List.mem_singleton] at member
    subst write
    exact output_bytes_bind
  guardsReadOnly := by simp

def beforeBytesAt (cell : CellId) : List UInt8 :=
  if cell = computationCell then beforeBytes else []

def beforeModel : Snapshot TransactionId CellId StableNullifier ReplayEnvelope where
  roots := fun cell => rootBytes (beforeBytesAt cell)
  consumed := fun _ => false
  available := 0
  history := []
  journal := []

def durableBefore : DataSnapshot rootBytes where
  model := beforeModel
  canonicalBytes := beforeBytesAt
  coherent := fun _ => rfl

@[simp] theorem durable_ready : durableIntent.preflight durableBefore = .ok () := by
  decide

/-- The exact result bytes, post root, audit event, and replay record install
in one atomic model transition. -/
theorem durable_install :
    Minidregg.Kernel.DurableDataIntent.execute
        .complete durableBefore durableIntent =
      .accepted (DataSnapshot.install durableBefore durableIntent) := by
  apply Minidregg.Kernel.DurableDataIntent.execute_complete_ready
  · rfl
  · exact durable_ready

@[simp] theorem installed_result_bytes :
    (DataSnapshot.install durableBefore durableIntent).canonicalBytes computationCell =
      outputBytes := by
  decide

@[simp] theorem installed_result_root :
    (DataSnapshot.install durableBefore durableIntent).model.roots computationCell =
      commit.postStateRoot := by
  decide

@[simp] theorem installed_audit_envelope :
    (DataSnapshot.install durableBefore durableIntent).model.history =
      [durableIntent.erase.event] := by
  rfl

/-- A lost successful response reopens as the identical journaled turn. -/
@[simp] theorem retry_replays :
    Minidregg.Kernel.DurableDataIntent.execute .complete
        (DataSnapshot.install durableBefore durableIntent) durableIntent =
      .replayed durableIntent.erase := by
  simp [Minidregg.Kernel.DurableDataIntent.execute,
    DataSnapshot.install, Snapshot.install,
    Snapshot.lookupRecorded, Intent.sameCheck_self]

def tamperedAuditEvent : StableEvent :=
  { auditEvent with canonicalBytes := auditEventBytes ++ [0] }

def tamperedIntent : DataIntent rootBytes :=
  { durableIntent with event := tamperedAuditEvent }

/-- Same transaction id and same result bytes cannot replay with altered audit
bytes: the exact envelope is part of journal identity. -/
@[simp] theorem audit_tamper_rejected :
    Minidregg.Kernel.DurableDataIntent.execute .complete
        (DataSnapshot.install durableBefore durableIntent) tamperedIntent =
      .rejected (.durable .transactionConflict) := by rfl

/-! ## Adjacent refusal tooth -/

def forgedOutput : Store Key F := ![6, 1, 1, 1]

theorem forged_output_refused :
    ¬ ∀ key, forgedOutput key =
      matmulTable eA eB (rowBits key) (columnBits key) := by
  intro forged
  have hfalse :
      forgedOutput (0 : Key) ≠
        matmulTable eA eB (rowBits 0) (columnBits 0) := by decide
  exact hfalse (forged 0)

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.ZkmlMatmulAuditTurn.receipt_core_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms receipt_core_relation
/-- info: 'Minidregg.Assurance.ZkmlMatmulAuditTurn.durable_install' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms durable_install
/-- info: 'Minidregg.Assurance.ZkmlMatmulAuditTurn.audit_tamper_rejected' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms audit_tamper_rejected

end

end Minidregg.Assurance.ZkmlMatmulAuditTurn
