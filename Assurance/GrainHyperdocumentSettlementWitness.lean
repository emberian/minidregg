/-
# Assurance.GrainHyperdocumentSettlementWitness -- one built grain settlement

The generic grain boundary is useful only if an accepted deployed-schema turn
can actually cross it.  This module reuses the concrete genesis-to-link
Hyperdocument witness: its accepted link effect becomes the sole incidence of
a `TypedCellHyperedge`, its verified causal link node becomes the proposal
branch, its current credential admission is retained, and its accepted sparse
event-log post supplies the focused sparse plane.

The receipt uses the finite scoped-field adapter.  Its sixteen binding cells
are a deterministic projection of the accepted settlement, exact request,
verified history node, and focused sparse root; they are not caller-authored.
The Rat scalarizer is an existence witness, not a deployment codec or a
cryptographic commitment.

Negative witnesses reject a stale canonical head, a revoked capability, and a
two-leg declaration that attempts to settle the same link write twice under
disjoint composition.
-/
import Assurance.GrainForkScopedSettlement
import Assurance.HyperdocumentLinkPublicationWitness

namespace Minidregg.Assurance.GrainHyperdocumentSettlementWitness

open Minidregg.Assurance.GrainForkSettlement
open Minidregg.Assurance.GrainForkScopedSettlement
open Minidregg.Assurance.HyperdocumentLinkPublicationWitness
open Minidregg.Assurance.SemanticReceiptRuntimeCodec
open Minidregg.Kernel
open Minidregg.Kernel.TypedCellHyperedge
open Minidregg.Theory
open Minidregg.Theory.CredentialAuthorityFamily
open Minidregg.Theory.Hyperdocument
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

noncomputable section

/-! ## The accepted Hyperdocument effect as one typed incidence -/

abbrev S := Hyperdocument.cellSchema
abbrev M := Genesis.documentMaterializer
abbrev Portal := Genesis.permissivePortal
abbrev Incidence := Unit

def projection : AuthorizationProjection S where
  project := fun _ =>
    CredentialAuthorityState.authState Genesis.projection Genesis.authorityPre

/-- No authorization, declaration, outcome, patch, or disclosure is rebuilt:
the leg retains the already accepted concrete `.link` operation. -/
noncomputable def linkLeg :
    Leg (S := S) (M := M) Portal
      (projection.project genesisPost.logical) genesisPost where
  Nullifier := Nat
  family := HyperdocumentOperations.family config
  kind := .object
  request := linkDeclaration.toRequest config
  declaration := linkDeclaration
  outcome := ()
  accepted := linkAccepted.accepted

/-- The apex is the root of the already accepted link post. -/
noncomputable def declaration : Declaration S M Portal projection Incidence where
  pre := genesisPost
  apex := linkAccepted.accepted.prepared.post.root
  legs := fun _ => linkLeg
  composition := { fieldMode := .canonical, order := [()] }

def law : ResourceLaw S M Portal Unit Int where
  delta := fun _ _ => 0

theorem shapeValid : declaration.ShapeValid where
  orderComplete := by
    constructor
    · decide
    · intro incidence
      cases incidence
      change () ∈ [()]
      decide
  resourcesDisjoint := by
    intro left right different
    exact absurd (Subsingleton.elim left right) different
  fieldsValid := trivial

theorem jointPatchAccepted :
    Nonempty (CellState.ValidatedPatch M declaration.pre
      declaration.jointPatch) := by
  generalize exactOutcome : CellState.validate M declaration.pre
    declaration.jointPatch = outcome
  cases outcome with
  | accepted validated => exact ⟨validated⟩
  | rejected reason =>
      unfold CellState.validate at exactOutcome
      rw [dif_pos (show declaration.jointPatch.expectedPreRoot =
        declaration.pre.root from rfl)] at exactOutcome
      rw [dif_pos (show declaration.jointPatch.fieldFootprint =
        declaration.jointPatch.namedFields from rfl)] at exactOutcome
      rw [dif_pos (show declaration.jointPatch.resourceFootprint =
        declaration.jointPatch.namedResources from rfl)] at exactOutcome
      cases exactOutcome

noncomputable def jointValidated :
    CellState.ValidatedPatch M declaration.pre declaration.jointPatch :=
  Classical.choice jointPatchAccepted

theorem jointPostExact :
    jointValidated.apply = linkAccepted.accepted.prepared.post := by
  apply CellState.Materialized.ext
  rfl

/-- A real `TypedCellHyperedge.Commit` over the deployed Hyperdocument schema. -/
noncomputable def commit : Commit law declaration where
  shape := shapeValid
  validated := jointValidated
  apexExact := by
    change jointValidated.apply.root =
      linkAccepted.accepted.prepared.post.root
    exact congrArg CellState.Materialized.root jointPostExact
  aggregateBalanced := by
    funext coordinate
    simp [Declaration.aggregateDelta, law]

/-! ## Exact current head, proposal branch, and sparse focus -/

/-- The current grain head is the accepted genesis content root and verified
genesis history entry. -/
def base : CanonicalHead where
  historyDomain := genesisIntent.historyDomain
  sequence := 1
  receiptRoot := genesisNode.entryId
  stateRoot := genesisPost.root

def canonicalBranch : BranchHistory base where
  branchId := genesisNode.entryId
  steps := []
  linked := trivial

/-- The proposal step is built entirely from the accepted link and its verified
causal node. -/
def proposalStep : HistoryStep where
  sequence := base.sequence + 1
  previousReceiptRoot := base.receiptRoot
  receiptRoot := linkNode.entryId
  preStateRoot := declaration.pre.root
  postStateRoot := commit.prepared.post.root
  semanticObjectRoot := (declaration.legs ()).request.effectsDigest

def proposalBranch : BranchHistory base where
  branchId := linkNode.entryId
  steps := [proposalStep]
  linked := by
    refine ⟨rfl, rfl, ?_, trivial⟩
    rfl

@[simp] theorem proposal_receipt_exact :
    proposalStep.receiptRoot = linkNode.entryId :=
  rfl

@[simp] theorem proposal_effect_exact :
    proposalStep.semanticObjectRoot = linkNode.effectId :=
  rfl

/-- The actual accepted causal history contains the exact proposal node. -/
@[simp] theorem proposal_in_verified_history : linkNode ∈ history.events := by
  simp [history_exact]

abbrev SparseLayout := HyperdocumentEventLog.Sparse.layout
abbrev SparseMaterializer := eventRepresentation.sparseMaterializer

def sparseState : Unit ->
    Minidregg.Kernel.SparseAuthenticatedState.Materialized SparseMaterializer :=
  fun _ => eventAccepted.sparse.post

def focus : StateFocus S SparseLayout SparseMaterializer Unit sparseState where
  fields := declaration.jointPatch.fieldFootprint
  resources := declaration.jointPatch.resourceFootprint
  sparsePlanes := {()}

/-- A built `FocusCut`: exact current content root, exact accepted proposal
effect, exact finite typed footprints, and an accepted sparse event-log plane. -/
def cut : FocusCut (L := SparseLayout)
    (sparseMaterializer := SparseMaterializer) (Plane := Unit)
    (sparseState := sparseState) base declaration where
  canonical := canonicalBranch
  branches := fun _ => proposalBranch
  focus := focus
  canonicalPreStateExact := rfl
  branchProposalExact := by
    intro incidence
    cases incidence
    rfl
  fieldsExact := rfl
  resourcesExact := rfl

/-- Successful settlement retains the typed commit and the exact current proof
authority of the already accepted link request. -/
def settlement : AcceptedSettlement (law := law) cut where
  commit := commit
  authorityPath := fun incidence => by
    cases incidence
    exact LiveAuthorityPath.ofLineage linkAccepted.accepted.authorization PUnit.unit

theorem settlement_nonempty : Nonempty (AcceptedSettlement (law := law) cut) :=
  ⟨settlement⟩

/-- The richer capability admission used to construct the accepted operation
is current for the exact credential-authority cell; the proof-portal path above
does not erase it. -/
def currentCapability :
    Genesis.capability.Admissible
      (CredentialAuthorityState.authState Genesis.projection Genesis.authorityPre)
      (linkDeclaration.toRequest config) :=
  linkCapabilityAdmissible

@[simp] theorem focused_link_field_present :
    (⟨.links, linkId⟩ : Hyperdocument.Address) ∈ cut.focus.fields := by
  rw [cut.fieldsExact]
  change (⟨.links, linkId⟩ : Hyperdocument.Address) ∈
    (linkDeclaration.patch config).fieldFootprint
  simp [HyperdocumentOperations.Declaration.patch,
    HyperdocumentOperations.Declaration.fieldWrites,
    HyperdocumentOperations.Declaration.packedWrites,
    HyperdocumentOperations.Action.packedWrites,
    HyperdocumentOperations.linkWrites,
    HyperdocumentOperations.PackedWrite.toFieldWrite,
    HyperdocumentOperations.PackedWrite.address,
    linkDeclaration, linkAction, linkPayload]
  exact Finset.mem_singleton_self _

@[simp] theorem accepted_post_contains_link :
    lookup settlement.post.logical .links linkId =
      some (HyperdocumentOperations.linkRecord
        (linkDeclaration.operationId config)
        Genesis.author linkPayload) := by
  rw [show settlement.post = linkAccepted.accepted.prepared.post by
    exact jointPostExact]
  exact link_post_contains_forward

@[simp] theorem focused_sparse_plane_exact :
    cut.focus.sparseRootAt () = eventAccepted.sparse.post.root :=
  rfl

/-! ## Finite receipt, with a derived header -/

def scalarizer : Scalarizer S Rat where
  root := fun digest => digest.value
  field := fun _ value => if value.isSome then 1 else 0

/-- Sixteen deterministic public cells.  Every cell is read from the accepted
settlement or from one of its exact retained inputs; there is no header argument
for a caller to nominate. -/
def headerCells
    (accepted : AcceptedSettlement (law := law) cut) (index : BindingIx) : Rat :=
  match index.val with
  | 0 => accepted.header.historyDomain.value
  | 1 => accepted.header.forkSequence
  | 2 => accepted.header.forkReceiptRoot.value
  | 3 => accepted.header.forkStateRoot.value
  | 4 => accepted.header.currentSequence
  | 5 => accepted.header.currentReceiptRoot.value
  | 6 => accepted.header.preStateRoot.value
  | 7 => accepted.header.postStateRoot.value
  | 8 => accepted.header.branchCount
  | 9 => (declaration.legs ()).request.effectsDigest.value
  | 10 => (declaration.legs ()).request.preStateRoot.value
  | 11 => linkNode.entryId.value
  | 12 => linkNode.preimage.historyDomain.value
  | 13 => cut.focus.sparseRootAt () |>.value
  | 14 => declaration.jointPatch.fieldFootprint.card
  | _ => declaration.jointPatch.resourceFootprint.card

noncomputable def receipt :
    ScopedCanonicalReceipt settlement scalarizer headerCells :=
  mintScopedReceipt settlement scalarizer headerCells

@[simp] theorem receipt_binding_derived :
    receipt.claim.witness.binding = headerCells settlement :=
  ScopedCanonicalReceipt.claim_binding_exact receipt

@[simp] theorem receipt_post_root_exact :
    settlement.header.postStateRoot = declaration.apex :=
  ScopedCanonicalReceipt.post_root_exact receipt

@[simp] theorem header_pre_cell_exact :
    headerCells settlement 6 = settlement.header.preStateRoot.value :=
  rfl

@[simp] theorem header_post_cell_exact :
    headerCells settlement 7 = settlement.header.postStateRoot.value :=
  rfl

@[simp] theorem header_effect_cell_exact :
    headerCells settlement 9 =
      (declaration.legs ()).request.effectsDigest.value :=
  rfl

/-! ## Rejection teeth -/

def staleBase : CanonicalHead :=
  { base with stateRoot := ⟨declaration.pre.root.value + 1⟩ }

def staleCanonicalBranch : BranchHistory staleBase where
  branchId := base.receiptRoot
  steps := []
  linked := trivial

theorem staleBase_not_pre : staleBase.stateRoot ≠ declaration.pre.root := by
  intro equal
  have values := congrArg Digest.value equal
  simp [staleBase] at values

/-- A caller cannot present the empty stale branch as the current canonical
head of this exact declaration. -/
theorem stale_canonical_rejected :
    ¬ ∃ staleCut : FocusCut (L := SparseLayout)
        (sparseMaterializer := SparseMaterializer) (Plane := Unit)
        (sparseState := sparseState) staleBase declaration,
      staleCut.canonical = staleCanonicalBranch := by
  rintro ⟨staleCut, canonicalExact⟩
  have exact := staleCut.canonicalPreStateExact
  rw [canonicalExact] at exact
  exact staleBase_not_pre exact

/-- Revoking the exact accepted capability makes the credential path
inadmissible; settlement currentness cannot be replayed in the changed state. -/
theorem stale_authority_rejected :
    ¬ Genesis.capability.Admissible revokedState
      (linkDeclaration.toRequest config) :=
  revoked_capability_rejected

/-- A deliberately invalid two-leg declaration asks disjoint composition to
write the exact same link field twice. -/
noncomputable def conflictingDeclaration :
    Declaration S M Portal projection Bool where
  pre := genesisPost
  apex := linkAccepted.accepted.prepared.post.root
  legs := fun _ => linkLeg
  composition := { fieldMode := .disjoint, order := [false, true] }

def conflictingLaw : ResourceLaw S M Portal Unit Int where
  delta := fun _ _ => 0

theorem linkFieldInFootprint (side : Bool) :
    (⟨.links, linkId⟩ : Hyperdocument.Address) ∈
      (conflictingDeclaration.legPatch side).fieldFootprint := by
  change (⟨.links, linkId⟩ : Hyperdocument.Address) ∈
    (linkDeclaration.patch config).fieldFootprint
  simp [HyperdocumentOperations.Declaration.patch,
    HyperdocumentOperations.Declaration.fieldWrites,
    HyperdocumentOperations.Declaration.packedWrites,
    HyperdocumentOperations.Action.packedWrites,
    HyperdocumentOperations.linkWrites,
    HyperdocumentOperations.PackedWrite.toFieldWrite,
    HyperdocumentOperations.PackedWrite.address,
    linkDeclaration, linkAction, linkPayload]
  exact Finset.mem_singleton_self _

def duplicateWriteConflict :
    MergeConflict conflictingDeclaration false true :=
  .field rfl (⟨.links, linkId⟩ : Hyperdocument.Address)
    (linkFieldInFootprint false) (linkFieldInFootprint true)

/-- The colliding declaration has no typed commit: the conflict is a real
shape rejection, not merely an out-of-band warning. -/
theorem duplicate_link_conflict_rejected :
    IsEmpty (Commit conflictingLaw conflictingDeclaration) :=
  ⟨fun candidate =>
    (GrainForkSettlement.Commit.noMergeConflict candidate (by decide))
      duplicateWriteConflict⟩

/-! ## Axiom audit -/

/-- info: 'Minidregg.Assurance.GrainHyperdocumentSettlementWitness.settlement_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms settlement_nonempty
/-- info: 'Minidregg.Assurance.GrainHyperdocumentSettlementWitness.receipt_binding_derived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms receipt_binding_derived
/-- info: 'Minidregg.Assurance.GrainHyperdocumentSettlementWitness.stale_canonical_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stale_canonical_rejected
/-- info: 'Minidregg.Assurance.GrainHyperdocumentSettlementWitness.duplicate_link_conflict_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duplicate_link_conflict_rejected

end

end Minidregg.Assurance.GrainHyperdocumentSettlementWitness
