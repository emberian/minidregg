/-
# Assurance.SemanticHistoryAccumulator -- verified semantic history folding

This module joins the current authoritative semantic-history objects without
introducing a second receipt or accumulator relation:

* `SemanticManifest.AdmissionContext.WellFormed` supplies manifest closure,
  history shape, and rejected-root atomicity;
* `SemanticTurnReceipt.TurnReceipt` supplies the proof-relevant committed or
  rejected semantic outcome;
* `SemanticReceiptRuntimeCodec.BoundReceiptWitness.encode` is the one word
  admitted for either outcome;
* `Loom.AccClaim` and `foldClaims_satisfies` perform every history fold.

`VerifiedHistoryHead` has a private constructor.  The exported `append`
operation consumes an `AppendLink` indexed by an existing verified head, so it
has no argument in which a caller can substitute a raw predecessor digest.

The cryptographic boundary is explicit.  `BindingCommitment` is Loom's
position-binding PCS interface; `FoldRecommitment` is the WARP recommitment
equation for one fold.  The deployed short-root Merkle/BCS realization and the
sampled-opening/proximity lift remain exactly Loom's named `[COMMIT-CR]`,
`[ACC-extract-bind]`, and `[DEC-proximity]` seams.  No axiom is declared here.
-/

import Compiler.SemanticManifest
import Assurance.SemanticReceiptRuntimeCodec
import Loom.Commitment

namespace Minidregg.Assurance.SemanticHistoryAccumulator

open Minidregg.Compiler.SemanticManifest
open Minidregg.Assurance.SemanticReceiptRelation
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SemanticTurnReceipt
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.ReactiveReceipt
open Minidregg.Theory.TypedAuthorization
open Minidregg.Loom

set_option autoImplicit false

universe uEffect uDisclosure uError uOp

noncomputable section

/-! ## One semantic outcome, one runtime word -/

/-- Rejection's semantic transition is the identity delta.  It has no touched
keys and its frame theorem is definitional. -/
def rejectionDelta {n : Nat} {F : Type*} [DecidableEq (Fin n)]
    (pre : Store (Fin n) F) : ReceiptDelta pre pre where
  touched := ∅
  frame := by simp

/-- Fixed semantic-turn type used throughout the join. -/
abbrev SemanticTurn
    (n : Nat) (F : Type*)
    (portal : Portal) (authState : AuthState) (kind : ResourceKind)
    (Effect : Type uEffect) (Disclosure : Type uDisclosure) (Error : Type uError)
    [DecidableEq (Fin n)]
    (stateCommitment : StateCommitment (Fin n) F)
    (effectSemantics : EffectSemantics (Fin n) F Effect)
    (disclosurePolicy : DisclosurePolicy Disclosure) :=
  TurnReceipt portal authState kind Error stateCommitment
    effectSemantics disclosurePolicy

section ReceiptWord

variable
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Effect : Type uEffect} {Disclosure : Type uDisclosure}
    {Error : Type uError}
    {stateCommitment : StateCommitment (Fin n) F}
    {effectSemantics : EffectSemantics (Fin n) F Effect}
    {disclosurePolicy : DisclosurePolicy Disclosure}

local notation "Turn" => SemanticTurn n F portal authState kind Effect
  Disclosure Error stateCommitment effectSemantics disclosurePolicy

/-- The semantic receipt core used by history.  A commit contributes its exact
carried delta; a rejection contributes the identity delta. -/
def historyCore (receipt : Turn) : ReceiptWitness (Fin n) F :=
  match receipt.outcome with
  | .inl _ => ReceiptWitness.ofDelta (rejectionDelta receipt.pre)
  | .inr commit => commit.coreClaim.witness

/-- Both outcome branches produce a genuinely valid semantic-receipt core. -/
theorem historyCore_valid (receipt : Turn) :
    (historyCore receipt).Satisfies := by
  cases h : receipt.outcome with
  | inl error =>
      simpa [historyCore, h] using
        ReceiptWitness.ofDelta_satisfies (rejectionDelta receipt.pre)
  | inr commit =>
      simpa [historyCore, h] using commit.coreClaim.valid

/-- Bind the admission header and semantic core into the exact codec witness
which `BoundSemanticReceiptClaim.acc` consumes.  `headerCells` is deliberately
an external Lean-owned codec/hash projection: its deployed digest realization
is `[HISTORY-HEADER-HASH]`, not invented here. -/
def historyWitness
    (headerCells : AdmissionContext → BindingIx → F)
    (context : AdmissionContext) (receipt : Turn) :
    BoundReceiptWitness n F where
  binding := headerCells context
  core := historyCore receipt

/-- The proof-relevant, codec-bound claim for either semantic outcome. -/
def historyClaim
    (headerCells : AdmissionContext → BindingIx → F)
    (context : AdmissionContext) (receipt : Turn) :
    BoundSemanticReceiptClaim n F where
  witness := historyWitness headerCells context receipt
  valid := historyCore_valid receipt

@[simp] theorem historyCore_rejected
    (request : Request kind) (pre : Store (Fin n) F)
    (preRootBound : request.preStateRoot = stateCommitment.root pre)
    (error : Error) :
    historyCore
      (TurnReceipt.rejected (portal := portal) (authState := authState)
        (effectSemantics := effectSemantics)
        (disclosurePolicy := disclosurePolicy)
        request pre preRootBound error) =
      ReceiptWitness.ofDelta (rejectionDelta pre) :=
  rfl

@[simp] theorem historyCore_committed
    (request : Request kind) (pre : Store (Fin n) F)
    (preRootBound : request.preStateRoot = stateCommitment.root pre)
    (commit : CommittedTurn portal authState request stateCommitment
      effectSemantics disclosurePolicy pre) :
    historyCore
      (TurnReceipt.committed (Error := Error) request pre preRootBound commit) =
      commit.coreClaim.witness :=
  rfl

/-- Rejection atomicity is present in the accumulated word itself, not only in
the admission header. -/
theorem historyCore_reject_atomic (receipt : Turn)
    {error : Error} (houtcome : receipt.outcome = .inl error) :
    (historyCore receipt).post = (historyCore receipt).pre := by
  simp [historyCore, houtcome, rejectionDelta, ReceiptWitness.ofDelta]

end ReceiptWord

/-! ## A manifest-admitted, proof-relevant history entry -/

section Entry

variable
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Effect : Type uEffect} {Disclosure : Type uDisclosure}
    {Error : Type uError}
    {stateCommitment : StateCommitment (Fin n) F}
    {effectSemantics : EffectSemantics (Fin n) F Effect}
    {disclosurePolicy : DisclosurePolicy Disclosure}

/-- Convert the typed semantic outcome to the manifest's first-order outcome
tag.  The error identifier is a declared codec projection, never native
acceptance. -/
def receiptAdmissionOutcome (errorId : Error → Digest)
    (receipt : SemanticTurn (n := n) (F := F) (portal := portal)
      (authState := authState) (kind := kind) (Effect := Effect)
      (Disclosure := Disclosure) (Error := Error)
      (stateCommitment := stateCommitment)
      (effectSemantics := effectSemantics)
      (disclosurePolicy := disclosurePolicy)) : AdmissionOutcome :=
  match receipt.outcome with
  | .inl error => .rejected (errorId error)
  | .inr _ => .committed

/-- One entry admitted simultaneously by the semantic receipt relation and the
manifest admission relation.  `codeword` is the honest-code/PCS boundary
needed by Loom; no cryptographic fact is inferred from the semantic proof. -/
structure VerifiedEntry
    (manifest : Manifest)
    (errorId : Error → Digest)
    (headerCells : AdmissionContext → BindingIx → F)
    (C : Submodule F (BoundReceiptIx n → F)) where
  context : AdmissionContext
  receipt : SemanticTurn (n := n) (F := F) (portal := portal)
    (authState := authState) (kind := kind) (Effect := Effect)
    (Disclosure := Disclosure) (Error := Error)
    (stateCommitment := stateCommitment)
    (effectSemantics := effectSemantics)
    (disclosurePolicy := disclosurePolicy)
  contextWellFormed : context.WellFormed manifest
  requestExact : context.request = ⟨kind, receipt.request⟩
  outcomeExact : context.outcome = receiptAdmissionOutcome errorId receipt
  preStateExact : context.preStateRoot = stateCommitment.root receipt.pre
  postStateExact : context.postStateRoot = stateCommitment.root receipt.post
  codeword :
    (historyClaim headerCells context receipt).witness.encode ∈ C

namespace VerifiedEntry

variable
    {manifest : Manifest} {errorId : Error → Digest}
    {headerCells : AdmissionContext → BindingIx → F}
    {C : Submodule F (BoundReceiptIx n → F)}

local notation "ThisEntry" => VerifiedEntry
  (n := n) (F := F) (portal := portal) (authState := authState)
  (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
  (Error := Error) (stateCommitment := stateCommitment)
  (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
  manifest errorId headerCells C

abbrev Claim (entry : ThisEntry) :=
  historyClaim (n := n) (F := F) (portal := portal) (authState := authState)
    (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
    (Error := Error) (stateCommitment := stateCommitment)
    (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
    headerCells entry.context entry.receipt

/-- The exact Loom/runtime-codec word for this entry. -/
def word (entry : ThisEntry) :
    BoundReceiptIx n → F :=
  entry.Claim.witness.encode

/-- The individual receipt root is derived by the binding commitment; callers
cannot attach an unrelated root to a verified entry. -/
def receiptRoot {Op : Type uOp}
    (S : BindingCommitment Digest F (BoundReceiptIx n) Op)
    (entry : ThisEntry) : Digest :=
  S.commit entry.word

theorem context_reject_atomic
    (entry : ThisEntry)
    {denial : Digest} (houtcome : entry.context.outcome = .rejected denial) :
    entry.context.postStateRoot = entry.context.preStateRoot := by
  simpa [houtcome] using entry.contextWellFormed.rejectedAtomic

/-- A rejected manifest outcome forces the receipt branch to be rejected and
therefore forces `post = pre` in the accumulated semantic core. -/
theorem word_reject_atomic
    (entry : ThisEntry)
    {denial : Digest} (houtcome : entry.context.outcome = .rejected denial) :
    entry.Claim.witness.core.post = entry.Claim.witness.core.pre := by
  cases hreceipt : entry.receipt.outcome with
  | inl error =>
      exact historyCore_reject_atomic entry.receipt hreceipt
  | inr commit =>
      have hexact := entry.outcomeExact
      simp [receiptAdmissionOutcome, hreceipt, houtcome] at hexact

/-- The commit branch enters with the exact semantic delta witness carried by
`CommittedTurn.coreClaim`. -/
theorem word_committed_core
    (entry : ThisEntry)
    {commit : CommittedTurn portal authState entry.receipt.request
      stateCommitment effectSemantics disclosurePolicy entry.receipt.pre}
    (houtcome : entry.receipt.outcome = .inr commit) :
    entry.Claim.witness.core = commit.coreClaim.witness := by
  simp [Claim, historyClaim, historyWitness, historyCore, houtcome]

end VerifiedEntry

end Entry


/-! ## Private verified history heads -/

section History

variable
    {n : Nat} {F : Type*} [Field F] [DecidableEq F]
    {portal : Portal} {authState : AuthState} {kind : ResourceKind}
    {Effect : Type uEffect} {Disclosure : Type uDisclosure}
    {Error : Type uError} {Op : Type uOp}
    {stateCommitment : StateCommitment (Fin n) F}
    {effectSemantics : EffectSemantics (Fin n) F Effect}
    {disclosurePolicy : DisclosurePolicy Disclosure}
    (manifest : Manifest)
    (errorId : Error → Digest)
    (headerCells : AdmissionContext → BindingIx → F)
    (C : Submodule F (BoundReceiptIx n → F))
    (S : BindingCommitment Digest F (BoundReceiptIx n) Op)
    (foldRoot : Digest → F → Digest → Digest)

local notation "HistoryEntry" => VerifiedEntry
  (n := n) (F := F) (portal := portal) (authState := authState)
  (kind := kind) (Effect := Effect) (Disclosure := Disclosure)
  (Error := Error) (stateCommitment := stateCommitment)
  (effectSemantics := effectSemantics) (disclosurePolicy := disclosurePolicy)
  manifest errorId headerCells C

abbrev ChannelCount := Fintype.card (BoundReceiptIx n)

/-- A verified head contains the complete proof-relevant entry list, its latest
entry, the single folded Loom claim/word, exact satisfaction, and commitment
binding.  The private constructor makes `start` and `append` the only public
ways to obtain one. -/
structure VerifiedHistoryHead where
  private mk ::
  entries : List HistoryEntry
  latest : HistoryEntry
  latestIsLast : entries.getLast? = some latest
  accumulator : AccClaim Digest F (BoundReceiptIx n) (ChannelCount (n := n))
  foldedWord : BoundReceiptIx n → F
  satisfies : AccClaim.Satisfies C accumulator foldedWord
  rootBound : accumulator.rt = S.commit foldedWord
  channelFixed : ∀ index,
    accumulator.weights index = boundEvalAt (boundReceiptCoord index)

namespace VerifiedHistoryHead

/-- History depth is the number of verified semantic entries retained by the
proof-relevant head. -/
def depth (head : VerifiedHistoryHead manifest errorId headerCells C S foldRoot) : Nat :=
  head.entries.length

/-- The only predecessor root exposed to the next append is derived from the
verified latest entry and the binding commitment. -/
def latestReceiptRoot
    (head : VerifiedHistoryHead manifest errorId headerCells C S foldRoot) : Digest :=
  head.latest.receiptRoot S

/-- Genesis from one verified entry.  The admission context itself must be the
genesis history link; an existential predecessor from `WellFormed` is not
accepted. -/
def start
    (entry : HistoryEntry)
    (sequenceZero : entry.context.sequence = 0)
    (noPredecessor : entry.context.previousReceiptRoot = none) :
    VerifiedHistoryHead manifest errorId headerCells C S foldRoot := by
  let claim := entry.Claim
  let root := entry.receiptRoot S
  let accumulator := claim.acc root
  let word := entry.word
  have hsatisfies : AccClaim.Satisfies C accumulator word :=
    (claim.acc_satisfies_iff root word).mpr ⟨entry.codeword, rfl⟩
  exact VerifiedHistoryHead.mk [entry] entry (by simp) accumulator word
    hsatisfies rfl (fun _ => rfl)

@[simp] theorem start_depth
    (entry : HistoryEntry)
    (sequenceZero : entry.context.sequence = 0)
    (noPredecessor : entry.context.previousReceiptRoot = none) :
    (start manifest errorId headerCells C S foldRoot entry sequenceZero
      noPredecessor).depth = 1 :=
  rfl

/-- The only legal history link for `entry`.  It is indexed by the complete
verified predecessor head; no raw digest parameter exists.  State continuity
is included alongside the manifest's causal receipt-root link. -/
structure AppendLink
    (head : VerifiedHistoryHead manifest errorId headerCells C S foldRoot)
    (entry : HistoryEntry) : Prop where
  historyDomainExact :
    entry.context.historyDomain = head.latest.context.historyDomain
  sequenceExact : entry.context.sequence = head.depth
  predecessorExact :
    entry.context.previousReceiptRoot = some head.latestReceiptRoot
  stateExact :
    entry.context.preStateRoot = head.latest.context.postStateRoot

/-- Explicit WARP/PCS seam for one step: the opaque root selected by
`foldRoot` must really commit the arithmetic folded word.  This is carried
proof data, not an axiom and not inferred from hash syntax. -/
structure FoldRecommitment
    (head : VerifiedHistoryHead manifest errorId headerCells C S foldRoot)
    (entry : HistoryEntry) (gamma : F) : Prop where
  rootExact :
    foldRoot head.accumulator.rt gamma (entry.receiptRoot S) =
      S.commit (head.foldedWord + gamma • entry.word)

/-- Append one verified semantic receipt and fold it into the single Loom
claim.  The caller supplies only the new verified entry, a link indexed by the
existing head, the Lean-controller challenge, and the explicit recommitment
proof. -/
def append
    (head : VerifiedHistoryHead manifest errorId headerCells C S foldRoot)
    (entry : HistoryEntry)
    (gamma : F) (_link : AppendLink manifest errorId headerCells C S foldRoot head entry)
    (recommit : FoldRecommitment manifest errorId headerCells C S foldRoot
      head entry gamma) :
    VerifiedHistoryHead manifest errorId headerCells C S foldRoot := by
  let linkClaim := entry.Claim.acc (entry.receiptRoot S)
  let accumulator := foldClaims foldRoot head.accumulator linkClaim gamma
  let word := head.foldedWord + gamma • entry.word
  have hshare : ∀ index, linkClaim.weights index = head.accumulator.weights index := by
    intro index
    simpa [linkClaim, VerifiedEntry.Claim, historyClaim, BoundSemanticReceiptClaim.acc,
      AccClaim.weights] using (head.channelFixed index).symm
  have hentry : AccClaim.Satisfies C linkClaim entry.word :=
    (entry.Claim.acc_satisfies_iff (entry.receiptRoot S) entry.word).mpr
      ⟨entry.codeword, rfl⟩
  have hsatisfies : AccClaim.Satisfies C accumulator word :=
    foldClaims_satisfies foldRoot gamma hshare head.satisfies hentry
  have hroot : accumulator.rt = S.commit word := by
    simpa [accumulator, word, linkClaim] using recommit.rootExact
  have hfixed : ∀ index,
      accumulator.weights index = boundEvalAt (boundReceiptCoord index) := by
    intro index
    simpa [accumulator, foldClaims, AccClaim.weights] using head.channelFixed index
  exact VerifiedHistoryHead.mk (head.entries ++ [entry]) entry (by simp)
    accumulator word hsatisfies hroot hfixed

@[simp] theorem append_depth
    (head : VerifiedHistoryHead manifest errorId headerCells C S foldRoot)
    (entry : HistoryEntry)
    (gamma : F) (link : AppendLink manifest errorId headerCells C S foldRoot head entry)
    (recommit : FoldRecommitment manifest errorId headerCells C S foldRoot
      head entry gamma) :
    (append manifest errorId headerCells C S foldRoot head entry gamma link
      recommit).depth = head.depth + 1 := by
  simp [append, depth]

@[simp] theorem append_latest
    (head : VerifiedHistoryHead manifest errorId headerCells C S foldRoot)
    (entry : HistoryEntry)
    (gamma : F) (link : AppendLink manifest errorId headerCells C S foldRoot head entry)
    (recommit : FoldRecommitment manifest errorId headerCells C S foldRoot
      head entry gamma) :
    (append manifest errorId headerCells C S foldRoot head entry gamma link
      recommit).latest = entry :=
  rfl

/-! ## Arbitrary-depth decision and the explicit opening seam -/

/-- Every constructible history head, at arbitrary depth, passes Loom's exact
one-time decider on its folded word.  This is directly the existing Loom
completeness theorem applied to the satisfaction proof preserved by `append`. -/
theorem decider_complete_at_head
    (head : VerifiedHistoryHead manifest errorId headerCells C S foldRoot) :
    decider C head.accumulator head.foldedWord :=
  Minidregg.Loom.decider_complete head.satisfies

/-- The honest full-opening side of the PCS seam.  Loom's existing commitment
theorem simultaneously supplies openings and the final decider result. -/
theorem opening_decider_complete
    (head : VerifiedHistoryHead manifest errorId headerCells C S foldRoot) :
    (∀ index, S.verifyOpen head.accumulator.rt index (head.foldedWord index)
      (S.openAt head.foldedWord index)) ∧
      decider C head.accumulator head.foldedWord :=
  S.decider_open_complete head.rootBound head.satisfies

/-- Binding/extraction tooth at arbitrary history depth: any fully opened word
which passes the final Loom decider is exactly the head's committed folded
word.  The deployed sampled-opening lift remains Loom's explicit
`[ACC-extract-bind]`/`[DEC-proximity]` obligation. -/
theorem opened_decider_extracts_head
    (head : VerifiedHistoryHead manifest errorId headerCells C S foldRoot)
    (opened : BoundReceiptIx n → F) (openings : BoundReceiptIx n → Op)
    (hopen : ∀ index,
      S.verifyOpen head.accumulator.rt index (opened index) (openings index))
    (hdecider : decider C head.accumulator opened) :
    opened = head.foldedWord ∧
      decider C head.accumulator head.foldedWord :=
  S.decider_open_sound head.rootBound hopen hdecider

end VerifiedHistoryHead

end History


#print axioms VerifiedHistoryHead.decider_complete_at_head
#print axioms VerifiedHistoryHead.opened_decider_extracts_head

end

end Minidregg.Assurance.SemanticHistoryAccumulator
