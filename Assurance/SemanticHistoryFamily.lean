/-
# Assurance.SemanticHistoryFamily -- request-shape-neutral semantic histories

`SemanticHistoryAccumulator.VerifiedEntry` was intentionally concrete: it
admitted one `SemanticTurnReceipt`, hence one `SomeRequest`.  A flat declared
hyperedge has a finite family of exact, potentially heterogeneously-kinded
requests.  Selecting one incidence as a primary request would erase the joint
semantics before accumulation.

This module factors history admission at the right boundary:

* `HistoryAdmissionContext` binds one complete semantic object by a canonical
  `semanticObjectRoot`; it does not contain a privileged request;
* `EntrySemanticsFamily.Evidence context claim` is a proof-relevant Lean type
  indexed by the exact public context and exact accumulated receipt claim;
* `VerifiedEntry` combines that semantic evidence with manifest closure,
  exact ordered clause evidence, and honest-code membership;
* `VerifiedHistoryHead` folds only these verified entries through Loom's one
  existing `AccClaim` relation.

Concrete families must prove that rejection makes the accumulated core
atomic.  The turn and hyperedge instances live in
`SemanticHistoryFamilyInstances`; in particular, the hyperedge instance binds
the complete incidence family through its semantic-object/header roots and
never synthesizes a primary request.

The sixteen field cells remain the explicit `[HISTORY-HEADER-HASH]` seam: a
deployment supplies a Lean-owned canonical context codec/hash projection as
`headerCells`.  This module neither invents a cryptographic hash theorem nor
calls a native verifier.
-/

import Assurance.SemanticHistoryAccumulator

namespace Minidregg.Assurance.SemanticHistoryFamily

open Minidregg.Compiler.SemanticManifest
open Minidregg.Compiler.DialectClauseDispatch
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Assurance.SemanticHistoryAccumulator
open Minidregg.Theory.TypedAuthorization
open Minidregg.Loom

set_option autoImplicit false

universe uSemantics uLeft uRight uOp
  uClauseInput uClauseQuery uClauseReply uClauseOutcome uClauseEvidence

noncomputable section

/-! ## Request-shape-neutral admission context -/

/-- Public history header common to singular turns and joint hyperedges.

`semanticObjectRoot` commits the complete semantic object in its native
canonical encoding.  For a singular turn that object contains the one exact
request.  For a hyperedge it contains the entire incidence family,
composition plan, shared apex, and canonical pre-cell. -/
structure HistoryAdmissionContext where
  manifestAddress : Digest
  historyDomain : Digest
  sequence : Nat
  previousReceiptRoot : Option Digest
  semanticObjectRoot : Digest
  semanticRelationId : Digest
  outcome : AdmissionOutcome
  preStateRoot : Digest
  postStateRoot : Digest
  effectRoot : Digest
  authorizationRoot : Digest
  disclosureRoot : Digest
  dialectClauseRoots : List DialectClauseRoots
deriving DecidableEq, Repr

/-- Manifest closure and causal/atomic history invariants which do not depend
on a singular request shape.  The semantic evidence family is responsible for
binding all semantic-object-specific fields to its exact Lean object. -/
structure HistoryAdmissionContext.WellFormed
    (manifest : Manifest) (context : HistoryAdmissionContext) : Prop where
  manifestExact : context.manifestAddress = manifest.contentAddress
  semanticRelationExact :
    context.semanticRelationId = manifest.semanticRelationId
  historyLink :
    (context.sequence = 0 /\ context.previousReceiptRoot = none) \/
    (0 < context.sequence /\ ∃ previous,
      context.previousReceiptRoot = some previous)
  rejectedAtomic : match context.outcome with
    | .rejected _ => context.postStateRoot = context.preStateRoot
    | .committed => True
  dialectClauseIdsUnique :
    (context.dialectClauseRoots.map DialectClauseRoots.clauseId).Nodup
  dialectClausesClosed : ∀ roots,
    roots ∈ context.dialectClauseRoots →
      ∃ clause, manifest.lookupClause roots.clauseId = some clause

/-- Lossless projection of the history/common portion of the legacy singular
`AdmissionContext`.  Its `turnId` becomes the complete semantic-object root;
the legacy `request` is deliberately not copied into the generic context. -/
def HistoryAdmissionContext.ofAdmissionContext
    (context : AdmissionContext) : HistoryAdmissionContext where
  manifestAddress := context.manifestAddress
  historyDomain := context.historyDomain
  sequence := context.sequence
  previousReceiptRoot := context.previousReceiptRoot
  semanticObjectRoot := context.turnId
  semanticRelationId := context.request.2.semantics
  outcome := context.outcome
  preStateRoot := context.preStateRoot
  postStateRoot := context.postStateRoot
  effectRoot := context.effectRoot
  authorizationRoot := context.authorizationRoot
  disclosureRoot := context.disclosureRoot
  dialectClauseRoots := context.dialectClauseRoots

/-- Legacy well-formed singular contexts remain well formed after the
request-shape-neutral projection. -/
theorem HistoryAdmissionContext.ofAdmissionContext_wellFormed
    {manifest : Manifest} {context : AdmissionContext}
    (wellFormed : context.WellFormed manifest) :
    (HistoryAdmissionContext.ofAdmissionContext context).WellFormed manifest where
  manifestExact := wellFormed.manifestExact
  semanticRelationExact := wellFormed.requestSemantics
  historyLink := wellFormed.historyLink
  rejectedAtomic := wellFormed.rejectedAtomic
  dialectClauseIdsUnique := wellFormed.dialectClauseIdsUnique
  dialectClausesClosed := wellFormed.dialectClausesClosed

/-! ## Proof-relevant semantic entry family -/

/-- A semantic family assigns a proof type to one exact context/claim pair.
It must expose rejection atomicity in the actual accumulated core.  No generic
native verifier predicate exists at this boundary. -/
structure EntrySemanticsFamily
    (n : Nat) (F : Type*) [Field F] [DecidableEq F] where
  Evidence : HistoryAdmissionContext →
    BoundSemanticReceiptClaim n F → Type uSemantics
  rejectedCoreAtomic : ∀ {context claim},
    Evidence context claim → ∀ {denial},
      context.outcome = .rejected denial →
        claim.witness.core.post = claim.witness.core.pre

namespace EntrySemanticsFamily

variable {n : Nat} {F : Type*} [Field F] [DecidableEq F]

/-- Proof-relevant disjoint union of semantic entry families.  This is the
typed composition operation which lets one causal history contain, for
example, both singular turns and flat hyperedges without weakening either
evidence type to an unindexed blob. -/
def sum
    (left : EntrySemanticsFamily.{uLeft} n F)
    (right : EntrySemanticsFamily.{uRight} n F) :
    EntrySemanticsFamily.{max uLeft uRight} n F where
  Evidence := fun context claim =>
    Sum (left.Evidence context claim) (right.Evidence context claim)
  rejectedCoreAtomic := by
    intro context claim evidence denial rejected
    cases evidence with
    | inl leftEvidence =>
        exact left.rejectedCoreAtomic leftEvidence rejected
    | inr rightEvidence =>
        exact right.rejectedCoreAtomic rightEvidence rejected

end EntrySemanticsFamily

section Entry

variable {n : Nat} {F : Type*} [Field F] [DecidableEq F]
variable
    {manifest : Manifest}
    {registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome}}
    {clauseEvidence : ClauseEvidenceFamily manifest registry}
    {family : EntrySemanticsFamily.{uSemantics} n F}
    {headerCells : HistoryAdmissionContext → BindingIx → F}
    {C : Submodule F (BoundReceiptIx n → F)}

/-- One exact semantic claim admitted by its Lean evidence family, the
manifest, all ordered dialect clauses, and the honest code. -/
structure VerifiedEntry where
  context : HistoryAdmissionContext
  claim : BoundSemanticReceiptClaim n F
  semantics : family.Evidence context claim
  contextWellFormed : context.WellFormed manifest
  dialectEvidence :
    ClauseEvidenceCoverage clauseEvidence context.dialectClauseRoots
  bindingExact : claim.witness.binding = headerCells context
  codeword : claim.witness.encode ∈ C

namespace VerifiedEntry

/-- Change only the semantic evidence carrier.  The exact context, claim,
manifest/clause proofs, binding equation, and codeword are retained
definitionally. -/
def mapFamily
    {source : EntrySemanticsFamily.{uLeft} n F}
    {target : EntrySemanticsFamily.{uRight} n F}
    (mapEvidence : ∀ {context claim},
      source.Evidence context claim → target.Evidence context claim)
    (entry : VerifiedEntry (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := source)
      (headerCells := headerCells) (C := C)) :
    VerifiedEntry (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := target)
      (headerCells := headerCells) (C := C) where
  context := entry.context
  claim := entry.claim
  semantics := mapEvidence entry.semantics
  contextWellFormed := entry.contextWellFormed
  dialectEvidence := entry.dialectEvidence
  bindingExact := entry.bindingExact
  codeword := entry.codeword

/-- Admit a left-family entry into a mixed-family history. -/
def toSumLeft
    {left : EntrySemanticsFamily.{uLeft} n F}
    (right : EntrySemanticsFamily.{uRight} n F)
    (entry : VerifiedEntry (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := left)
      (headerCells := headerCells) (C := C)) :
    VerifiedEntry (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence)
      (family := EntrySemanticsFamily.sum left right)
      (headerCells := headerCells) (C := C) :=
  entry.mapFamily (fun evidence => .inl evidence)

/-- Admit a right-family entry into a mixed-family history. -/
def toSumRight
    (left : EntrySemanticsFamily.{uLeft} n F)
    {right : EntrySemanticsFamily.{uRight} n F}
    (entry : VerifiedEntry (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := right)
      (headerCells := headerCells) (C := C)) :
    VerifiedEntry (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence)
      (family := EntrySemanticsFamily.sum left right)
      (headerCells := headerCells) (C := C) :=
  entry.mapFamily (fun evidence => .inr evidence)

/-- The exact runtime/Loom word. -/
def word (entry : VerifiedEntry (manifest := manifest) (registry := registry)
    (clauseEvidence := clauseEvidence) (family := family)
    (headerCells := headerCells) (C := C)) : BoundReceiptIx n → F :=
  entry.claim.witness.encode

/-- The entry root is derived from the commitment and exact word. -/
def receiptRoot {Op : Type uOp}
    (S : BindingCommitment Digest F (BoundReceiptIx n) Op)
    (entry : VerifiedEntry (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C)) : Digest :=
  S.commit entry.word

def resolvedClauseAt
    (entry : VerifiedEntry (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C))
    (index : Fin entry.context.dialectClauseRoots.length) :
    ResolvedClause manifest registry
      (entry.context.dialectClauseRoots.get index).clauseId :=
  entry.dialectEvidence.resolved index

def clauseEvidenceAt
    (entry : VerifiedEntry (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C))
    (index : Fin entry.context.dialectClauseRoots.length) :
    clauseEvidence.Evidence (entry.resolvedClauseAt index)
      (entry.context.dialectClauseRoots.get index).statementRoot
      (entry.context.dialectClauseRoots.get index).proofRoot :=
  entry.dialectEvidence.evidence index

theorem context_reject_atomic
    (entry : VerifiedEntry (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C))
    {denial : Digest} (rejected : entry.context.outcome = .rejected denial) :
    entry.context.postStateRoot = entry.context.preStateRoot := by
  simpa [rejected] using entry.contextWellFormed.rejectedAtomic

/-- Rejection atomicity is enforced in both the public roots and the
accumulated semantic core. -/
theorem word_reject_atomic
    (entry : VerifiedEntry (manifest := manifest) (registry := registry)
      (clauseEvidence := clauseEvidence) (family := family)
      (headerCells := headerCells) (C := C))
    {denial : Digest} (rejected : entry.context.outcome = .rejected denial) :
    entry.claim.witness.core.post = entry.claim.witness.core.pre :=
  family.rejectedCoreAtomic entry.semantics rejected

end VerifiedEntry

end Entry

/-! ## Generic verified causal history -/

section History

variable {n : Nat} {F : Type*} [Field F] [DecidableEq F]
variable {Op : Type uOp}
variable
    (manifest : Manifest)
    (registry : ControllerRegistry.{uClauseInput, uClauseQuery,
      uClauseReply, uClauseOutcome})
    (clauseEvidence : ClauseEvidenceFamily manifest registry)
    (family : EntrySemanticsFamily.{uSemantics} n F)
    (headerCells : HistoryAdmissionContext → BindingIx → F)
    (C : Submodule F (BoundReceiptIx n → F))
    (S : BindingCommitment Digest F (BoundReceiptIx n) Op)
    (foldRoot : Digest → F → Digest → Digest)

local notation "HistoryEntry" => VerifiedEntry
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C)

abbrev ChannelCount := Fintype.card (BoundReceiptIx n)

inductive HistoryChain : List HistoryEntry → Prop
  | start (entry : HistoryEntry)
      (sequenceZero : entry.context.sequence = 0)
      (noPredecessor : entry.context.previousReceiptRoot = none) :
      HistoryChain [entry]
  | append {entries : List HistoryEntry} {latest entry : HistoryEntry}
      (prior : HistoryChain entries)
      (latestIsLast : entries.getLast? = some latest)
      (historyDomainExact :
        entry.context.historyDomain = latest.context.historyDomain)
      (sequenceExact : entry.context.sequence = entries.length)
      (predecessorExact : entry.context.previousReceiptRoot =
        some (latest.receiptRoot S))
      (stateExact :
        entry.context.preStateRoot = latest.context.postStateRoot) :
      HistoryChain (entries ++ [entry])

local notation "LinkedEntries" => HistoryChain
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) (C := C) S

/-- Private-constructor history head over an arbitrary exact semantic family.
The arithmetic accumulator is still Loom's sole `AccClaim`; only entry
admission has been generalized. -/
structure VerifiedHistoryHead where
  private mk ::
  entries : List HistoryEntry
  latest : HistoryEntry
  latestIsLast : entries.getLast? = some latest
  linked : LinkedEntries entries
  accumulator : AccClaim Digest F (BoundReceiptIx n) (ChannelCount (n := n))
  foldedWord : BoundReceiptIx n → F
  satisfies : AccClaim.Satisfies C accumulator foldedWord
  rootBound : accumulator.rt = S.commit foldedWord
  channelFixed : ∀ index,
    accumulator.weights index = boundEvalAt (boundReceiptCoord index)

local notation "HistoryHead" => VerifiedHistoryHead
  (manifest := manifest) (registry := registry)
  (clauseEvidence := clauseEvidence) (family := family)
  (headerCells := headerCells) C S

namespace VerifiedHistoryHead

def depth (head : HistoryHead) : Nat := head.entries.length

def latestReceiptRoot (head : HistoryHead) : Digest :=
  head.latest.receiptRoot S

def start
    (entry : HistoryEntry)
    (sequenceZero : entry.context.sequence = 0)
    (noPredecessor : entry.context.previousReceiptRoot = none) :
    HistoryHead := by
  let root := entry.receiptRoot S
  let accumulator := entry.claim.acc root
  let word := entry.word
  have hsatisfies : AccClaim.Satisfies C accumulator word :=
    (entry.claim.acc_satisfies_iff root word).mpr ⟨entry.codeword, rfl⟩
  exact VerifiedHistoryHead.mk [entry] entry (by simp)
    (.start entry sequenceZero noPredecessor) accumulator word hsatisfies rfl
    (fun _ => rfl)

@[simp] theorem start_depth
    (entry : HistoryEntry)
    (sequenceZero : entry.context.sequence = 0)
    (noPredecessor : entry.context.previousReceiptRoot = none) :
    (start manifest registry clauseEvidence family headerCells C S entry
      sequenceZero noPredecessor).depth = 1 := rfl

structure AppendLink (head : HistoryHead) (entry : HistoryEntry) : Prop where
  historyDomainExact :
    entry.context.historyDomain = head.latest.context.historyDomain
  sequenceExact : entry.context.sequence = head.depth
  predecessorExact :
    entry.context.previousReceiptRoot = some head.latestReceiptRoot
  stateExact :
    entry.context.preStateRoot = head.latest.context.postStateRoot

structure FoldRecommitment
    (head : HistoryHead) (entry : HistoryEntry) (gamma : F) : Prop where
  rootExact :
    foldRoot head.accumulator.rt gamma (entry.receiptRoot S) =
      S.commit (head.foldedWord + gamma • entry.word)

def append
    (head : HistoryHead) (entry : HistoryEntry) (gamma : F)
    (link : AppendLink manifest registry clauseEvidence family
      headerCells C S head entry)
    (recommit : FoldRecommitment manifest registry clauseEvidence family
      headerCells C S foldRoot head entry gamma) : HistoryHead := by
  let linkClaim := entry.claim.acc (entry.receiptRoot S)
  let accumulator := foldClaims foldRoot head.accumulator linkClaim gamma
  let word := head.foldedWord + gamma • entry.word
  have hshare : ∀ index,
      linkClaim.weights index = head.accumulator.weights index := by
    intro index
    simpa [linkClaim, BoundSemanticReceiptClaim.acc, AccClaim.weights] using
      (head.channelFixed index).symm
  have hentry : AccClaim.Satisfies C linkClaim entry.word :=
    (entry.claim.acc_satisfies_iff (entry.receiptRoot S) entry.word).mpr
      ⟨entry.codeword, rfl⟩
  have hsatisfies : AccClaim.Satisfies C accumulator word :=
    foldClaims_satisfies foldRoot gamma hshare head.satisfies hentry
  have hroot : accumulator.rt = S.commit word := by
    simpa [accumulator, word, linkClaim] using recommit.rootExact
  have hfixed : ∀ index,
      accumulator.weights index = boundEvalAt (boundReceiptCoord index) := by
    intro index
    simpa [accumulator, foldClaims, AccClaim.weights] using
      head.channelFixed index
  have hlinked : LinkedEntries (head.entries ++ [entry]) :=
    .append head.linked head.latestIsLast link.historyDomainExact
      link.sequenceExact link.predecessorExact link.stateExact
  exact VerifiedHistoryHead.mk (head.entries ++ [entry]) entry (by simp)
    hlinked accumulator word hsatisfies hroot hfixed

@[simp] theorem append_depth
    (head : HistoryHead) (entry : HistoryEntry) (gamma : F)
    (link : AppendLink manifest registry clauseEvidence family
      headerCells C S head entry)
    (recommit : FoldRecommitment manifest registry clauseEvidence family
      headerCells C S foldRoot head entry gamma) :
    (append manifest registry clauseEvidence family headerCells C S foldRoot
      head entry gamma link recommit).depth = head.depth + 1 := by
  simp [append, depth]

@[simp] theorem append_latest
    (head : HistoryHead) (entry : HistoryEntry) (gamma : F)
    (link : AppendLink manifest registry clauseEvidence family
      headerCells C S head entry)
    (recommit : FoldRecommitment manifest registry clauseEvidence family
      headerCells C S foldRoot head entry gamma) :
    (append manifest registry clauseEvidence family headerCells C S foldRoot
      head entry gamma link recommit).latest = entry := rfl

theorem decider_complete_at_head (head : HistoryHead) :
    decider C head.accumulator head.foldedWord :=
  Minidregg.Loom.decider_complete head.satisfies

theorem opening_decider_complete (head : HistoryHead) :
    (∀ index, S.verifyOpen head.accumulator.rt index (head.foldedWord index)
      (S.openAt head.foldedWord index)) ∧
      decider C head.accumulator head.foldedWord :=
  Minidregg.Loom.decider_open_complete S head.rootBound head.satisfies

theorem opened_decider_extracts_head
    (head : HistoryHead)
    (opened : BoundReceiptIx n → F) (openings : BoundReceiptIx n → Op)
    (hopen : ∀ index,
      S.verifyOpen head.accumulator.rt index (opened index) (openings index))
    (hdecider : decider C head.accumulator opened) :
    opened = head.foldedWord ∧
      decider C head.accumulator head.foldedWord :=
  Minidregg.Loom.decider_open_sound S head.rootBound hopen hdecider

end VerifiedHistoryHead

end History

#print axioms HistoryAdmissionContext.ofAdmissionContext_wellFormed
#print axioms EntrySemanticsFamily.sum
#print axioms VerifiedEntry.toSumLeft
#print axioms VerifiedEntry.toSumRight
#print axioms VerifiedEntry.word_reject_atomic
#print axioms VerifiedHistoryHead.decider_complete_at_head
#print axioms VerifiedHistoryHead.opened_decider_extracts_head

end

end Minidregg.Assurance.SemanticHistoryFamily
