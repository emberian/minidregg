/-
# Kernel.DeclaredHyperedgeWitness -- a deployed two-incidence legacy bridge

`Kernel.DeclaredHyperedge` is intentionally a migration surface, not the
canonical runtime.  This file proves that surface still has an honest subject
while callers cross to `TypedCellHyperedge`: one account transfer is split
across two flat incidences, consumes the deployed sparse effect materializer,
derives both complete requests from one pre-cell and apex, and executes to the
exact materialized post.

The witness is deliberately stronger than mere inhabitation:

* the transfer carries a nonempty full-width resource delta on both halves;
* the aggregate conservation check closes those halves to zero;
* stale authority and a nominated wrong apex each reject independently;
* every rejection materializes to the exact pre-cell.

The permissive proof portal is used only to inhabit the legacy bridge.  The
negative authority tooth keeps that choice visibly separate from a deployed
security claim.
-/
import Kernel.TypedCellHyperedge
import Theory.DeployedMaterializerWitness
import Theory.TypedAuthorizationWitness

namespace Minidregg.Kernel.DeclaredHyperedgeWitness

open Minidregg.Kernel.DeclaredHyperedge
open Minidregg.Theory
open Minidregg.Theory.AuthorizationDeclaration
open Minidregg.Theory.CellState
open Minidregg.Theory.DeployedMaterializerWitness
open Minidregg.Theory.EffectDeclaration
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.TypedAuthorization
open Minidregg.Theory.TypedAuthorizationWitness

set_option autoImplicit false

noncomputable section

/-! ## Deployed pre-cell and exact authority projection -/

/-- Authorization is projected from the very logical cell consumed by the
effect interpreter.  The constant projection is suitable only for this closed
inhabitation witness; it does not weaken the kernel's same-cell index. -/
def projection : AuthorizationProjection effectMaterializer where
  project := fun _ => authState

/-- The same portal, against a state whose policy epoch has advanced. -/
def staleProjection : AuthorizationProjection effectMaterializer where
  project := fun _ => rotatedState

/-- Complete raw proof presentation for the exact dependent request. -/
def proofPresentation {kind : ResourceKind} (request : Request kind) :
    Presentation permissivePortal request where
  evidence := .proof ()
  policyWitness := ()
  policyMembershipWitness := ()

/-! ## Two incidences carrying one account transfer -/

def source : ResourceId .account := ⟨100⟩
def destination : ResourceId .account := ⟨101⟩
def asset : Digest := ⟨200⟩
def amount : Int := 7
def debitKey : StateKey := .accountBalance source asset
def creditKey : StateKey := .accountBalance destination asset

/-- The deployed materializer consumes a genuinely sparse pre-state in which
the two account coordinates exist at zero.  Keeping presence distinct from
absence is necessary for the exact legacy-to-typed local-post certificate. -/
def preLogical : LogicalState DeclaredTurn.effectSchema where
  fields :=
    (effectCell.logical.fields.write
      (.accountBalance source asset) (0 : Int)).write
        (.accountBalance destination asset) (0 : Int)
  resources := effectCell.logical.resources

def preCell : Materialized effectMaterializer :=
  materialize effectMaterializer preLogical

/-- The debit incidence owns the actual transfer constructor. -/
def debitEffects : EffectDeclaration.Declaration source where
  effects := [.accountMove source destination asset amount]

/-- The credit incidence names the destination and makes the joint target
cover explicit.  Its half-delta is derived from the common transfer list. -/
def creditEffects : EffectDeclaration.Declaration destination where
  effects := []

def seed (target : ResourceId .account) (nonce : Nat) : Seed .account where
  domain := ⟨1⟩
  semantics := ⟨2⟩
  federation := ⟨3⟩
  subject := ⟨4⟩
  subjectKeyEpoch := 0
  target := target
  verb := .transfer
  nonce := nonce
  height := 9
  policyId := ⟨10⟩
  policyEpoch := 0
  cost := 11

def leg (preRoot apex : Digest) : Bool -> Leg permissivePortal preRoot apex
  | false =>
      { kind := .account
        seed := seed source 20
        effects := debitEffects
        presentation := proofPresentation _ }
  | true =>
      { kind := .account
        seed := seed destination 21
        effects := creditEffects
        presentation := proofPresentation _ }

/-- The exact legacy patch independently of the declaration wrapper. -/
def transferPatch : List Mutation := debitEffects.patch ++ creditEffects.patch

def transferFootprint : List StateKey :=
  (transferPatch.map Mutation.key).eraseDups

def preStore : Store := DeclaredTurn.storeOfLogical preCell.logical

def postStore : Store := applyPatch transferPatch preStore

def postLogical : LogicalState DeclaredTurn.effectSchema :=
  DeclaredTurn.logicalOfStore preCell.logical transferFootprint postStore

/-- Reifying the semantic default store at the explicit present-zero account
coordinates preserves the sparse pre-state exactly. -/
theorem pre_reified_exact :
    DeclaredTurn.logicalOfStore preCell.logical transferFootprint preStore =
      preCell.logical := by
  change
    { fields := DeclaredTurn.fieldsOfStore preLogical.fields preStore
        transferFootprint
      resources := preLogical.resources } = preLogical
  unfold preLogical
  congr
  apply DFinsupp.ext
  intro field
  rw [DeclaredTurn.fieldsOfStore_read]
  by_cases member : field ∈ transferFootprint
  · have cases : field = debitKey ∨ field = creditKey := by
      have raw : field ∈ [debitKey, creditKey] :=
        List.mem_eraseDups.mp (by
          simpa [transferFootprint, transferPatch, debitEffects,
            creditEffects, EffectDeclaration.Declaration.patch,
            Effect.patch, Mutation.key] using member)
      rcases List.mem_cons.mp raw with debit | tail
      · exact Or.inl debit
      · rcases List.mem_cons.mp tail with credit | impossible
        · exact Or.inr credit
        · exact nomatch impossible
    rcases cases with debit | credit
    · subst field
      rfl
    · subst field
      rfl
  · split
    · rename_i present
      exact False.elim (member present)
    · rfl

/-- The apex is derived from the deployed materializer's exact post, not
nominated independently. -/
def apex : Digest := (materialize effectMaterializer postLogical).root

def declarationAt (candidateApex : Digest) :
    Declaration permissivePortal effectMaterializer Bool where
  pre := preCell
  apex := candidateApex
  legs := leg preCell.root candidateApex
  composition := { mode := .disjoint, order := [false, true] }

def declaration : Declaration permissivePortal effectMaterializer Bool :=
  declarationAt apex

/-! ## Executable positive path -/

@[simp] theorem declaration_patch : declaration.patch = transferPatch := by
  rfl

@[simp] theorem declaration_footprint :
    declaration.footprint = transferFootprint := by
  rfl

@[simp] theorem declaration_preStore : declaration.preStore = preStore := rfl

theorem shapeAccepted : declaration.shapeCheck = true := by
  decide

theorem authorizationAccepted :
    declaration.authorizationCheck projection = true := by
  decide

/-- Conservation is non-vacuous: the exact asset occurs in the joint vector. -/
theorem asset_present : asset ∈ declaration.resources := by
  decide

/-- The source half is the full-width debit. -/
theorem source_half : declaration.halfDelta false asset = -amount := by
  decide

/-- The destination half is the matching full-width credit. -/
theorem destination_half : declaration.halfDelta true asset = amount := by
  decide

/-- The executable aggregate checker closes the two halves exactly. -/
theorem balanceAccepted : declaration.balanceCheck = true := by
  decide

theorem aggregate_conserved : declaration.aggregateDelta = 0 :=
  declaration.aggregateDelta_zero
    ((declaration.balanceCheck_eq_true_iff).mp balanceAccepted)

theorem guardsAccepted : declaration.guardsCheck = true := by
  decide

theorem postRoot_exact :
    (materialize effectMaterializer
      (declaration.logicalOfStore postStore)).root = declaration.apex := by
  rfl

theorem evaluated_exact :
    applyPatch declaration.patch declaration.preStore = postStore := by
  rfl

/-- The built declaration reaches the exact total post-store. -/
theorem executes_committed :
    execute projection declaration = .committed postStore := by
  unfold execute
  rw [if_pos shapeAccepted, if_pos authorizationAccepted,
    if_pos balanceAccepted, if_pos guardsAccepted]
  dsimp only
  rw [evaluated_exact]
  rw [if_pos postRoot_exact]

/-- Proof-relevant committed hyperedge for the executable result. -/
theorem committed_nonempty :
    Nonempty (CommittedHyperedge projection declaration postStore) :=
  execute_committed_hyperedge_sound projection declaration postStore
    executes_committed

/-! ## Independent rejection teeth -/

def wrongApex : Digest := ⟨apex.value + 1⟩

theorem wrongApex_ne : apex ≠ wrongApex := by
  intro equal
  have : apex.value = apex.value + 1 := congrArg Digest.value equal
  omega

def wrongApexDeclaration :
    Declaration permissivePortal effectMaterializer Bool :=
  declarationAt wrongApex

theorem wrongShapeAccepted : wrongApexDeclaration.shapeCheck = true := by
  decide

theorem wrongAuthorizationAccepted :
    wrongApexDeclaration.authorizationCheck projection = true := by
  decide

theorem wrongBalanceAccepted : wrongApexDeclaration.balanceCheck = true := by
  decide

theorem wrongGuardsAccepted : wrongApexDeclaration.guardsCheck = true := by
  decide

theorem wrongPostRoot :
    (materialize effectMaterializer
      (wrongApexDeclaration.logicalOfStore
        (applyPatch wrongApexDeclaration.patch
          wrongApexDeclaration.preStore))).root = apex := by
  rfl

theorem wrongPostRoot_ne :
    (materialize effectMaterializer
      (wrongApexDeclaration.logicalOfStore
        (applyPatch wrongApexDeclaration.patch
          wrongApexDeclaration.preStore))).root ≠ wrongApexDeclaration.apex := by
  rw [wrongPostRoot]
  exact wrongApex_ne

/-- Shape, authorization, balance, and guards still pass, but a caller cannot
nominate a different apex for the same patch. -/
theorem rejects_wrong_apex :
    execute projection wrongApexDeclaration = .rejected .apex := by
  unfold execute
  rw [if_pos wrongShapeAccepted, if_pos wrongAuthorizationAccepted,
    if_pos wrongBalanceAccepted, if_pos wrongGuardsAccepted]
  dsimp only
  rw [if_neg wrongPostRoot_ne]

theorem staleAuthorizationRejected :
    declaration.authorizationCheck staleProjection = false := by
  decide

/-- Rotating the projected policy epoch rejects both otherwise complete proof
presentations before any patch is evaluated. -/
theorem rejects_stale_authority :
    execute staleProjection declaration = .rejected .authorization := by
  have rejected :
      declaration.authorizationCheck staleProjection ≠ true := by
    rw [staleAuthorizationRejected]
    decide
  unfold execute
  rw [if_pos shapeAccepted, if_neg rejected]

/-- Both explicit rejections retain the exact deployed pre-cell. -/
theorem wrong_apex_unchanged :
    (execute projection wrongApexDeclaration).materialized = preCell :=
  execute_rejected_unchanged projection wrongApexDeclaration .apex
    rejects_wrong_apex

theorem stale_authority_unchanged :
    (execute staleProjection declaration).materialized = preCell :=
  execute_rejected_unchanged staleProjection declaration .authorization
    rejects_stale_authority

/-! ## Exact bridge into the canonical typed hyperedge

This is intentionally an adapter certificate, not a second runtime.  The
typed patches below are the finite sparse reification of the old transfer;
their accepted effects, joint validation, post-cell, and aggregate law are
then checked by the generic kernel.
-/

namespace Migration

def unitCodec : LawfulCodec Unit where
  encode := fun _ => []
  decode := fun _ => some ()
  decode_encode := fun _ => rfl

def debitPatch : Patch DeclaredTurn.effectSchema Digest where
  expectedPreRoot := preCell.root
  fieldFootprint := {debitKey, creditKey}
  resourceFootprint := ∅
  fieldWrites :=
    [{ field := debitKey, value := some (-amount) },
     { field := creditKey, value := some amount }]
  resourceWrites := []

def creditPatch : Patch DeclaredTurn.effectSchema Digest where
  expectedPreRoot := preCell.root
  fieldFootprint := ∅
  resourceFootprint := ∅
  fieldWrites := []
  resourceWrites := []

def debitFamily :
    SemanticEffectFamily DeclaredTurn.effectSchema effectMaterializer Unit where
  Declaration := Unit
  declarationCodec := unitCodec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun _ _ => Unit
  effectDigest := fun _ => debitEffects.digest
  patch := fun _ _ => debitPatch
  nullifier := fun _ _ => none
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => release.elim
  DisclosureAllowed := fun _ _ decision => decision = .sealed

def creditFamily :
    SemanticEffectFamily DeclaredTurn.effectSchema effectMaterializer Unit where
  Declaration := Unit
  declarationCodec := unitCodec
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun _ _ => Unit
  effectDigest := fun _ => creditEffects.digest
  patch := fun _ _ => creditPatch
  nullifier := fun _ _ => none
  Release := fun _ _ => PEmpty
  DeclassificationAuthority := fun _ _ => PEmpty
  ReleaseAuthorization := fun _ _ release => release.elim
  DisclosureAllowed := fun _ _ decision => decision = .sealed

theorem debitPatch_accepted :
    ∃ validated : ValidatedPatch effectMaterializer preCell debitPatch,
      validate effectMaterializer preCell debitPatch =
        ValidationOutcome.accepted validated := by
  unfold validate
  rw [dif_pos (show debitPatch.expectedPreRoot = preCell.root from rfl)]
  rw [dif_pos (show debitPatch.fieldFootprint = debitPatch.namedFields by
    decide)]
  rw [dif_pos (show debitPatch.resourceFootprint = debitPatch.namedResources by
    decide)]
  exact ⟨_, rfl⟩

theorem creditPatch_accepted :
    ∃ validated : ValidatedPatch effectMaterializer preCell creditPatch,
      validate effectMaterializer preCell creditPatch =
        ValidationOutcome.accepted validated := by
  unfold validate
  rw [dif_pos (show creditPatch.expectedPreRoot = preCell.root from rfl)]
  rw [dif_pos (show creditPatch.fieldFootprint = creditPatch.namedFields by
    decide)]
  rw [dif_pos (show creditPatch.resourceFootprint = creditPatch.namedResources by
    decide)]
  exact ⟨_, rfl⟩

noncomputable def debitValidated :
    ValidatedPatch effectMaterializer preCell debitPatch :=
  debitPatch_accepted.choose

noncomputable def creditValidated :
    ValidatedPatch effectMaterializer preCell creditPatch :=
  creditPatch_accepted.choose

def debitAuthorization : Authorized permissivePortal authState
    (declaration.legs false).request where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

def creditAuthorization : Authorized permissivePortal authState
    (declaration.legs true).request where
  evidence := .proof () rfl
  policyWitness := ()
  policyMembershipWitness := ()
  policyEpochExact := rfl
  policyAddressExact := rfl
  policyMembershipVerified := rfl
  policyVerified := rfl

noncomputable def debitAccepted :
    AcceptedCellEffect (portal := permissivePortal) (authState := authState)
      debitFamily (declaration.legs false).request preCell () () where
  authorization := debitAuthorization
  effectsDigestBound := rfl
  preRootBound := rfl
  modeEvidence := ()
  validated := debitValidated
  disclosure := .sealed
  disclosureAllowed := rfl

noncomputable def creditAccepted :
    AcceptedCellEffect (portal := permissivePortal) (authState := authState)
      creditFamily (declaration.legs true).request preCell () () where
  authorization := creditAuthorization
  effectsDigestBound := rfl
  preRootBound := rfl
  modeEvidence := ()
  validated := creditValidated
  disclosure := .sealed
  disclosureAllowed := rfl

noncomputable def typedLeg : Bool ->
    TypedCellHyperedge.Leg permissivePortal authState preCell
  | false =>
      { Nullifier := Unit
        family := debitFamily
        kind := .account
        request := (declaration.legs false).request
        declaration := ()
        outcome := ()
        accepted := debitAccepted }
  | true =>
      { Nullifier := Unit
        family := creditFamily
        kind := .account
        request := (declaration.legs true).request
        declaration := ()
        outcome := ()
        accepted := creditAccepted }

def typedProjection : TypedCellHyperedge.AuthorizationProjection
    DeclaredTurn.effectSchema :=
  TypedCellHyperedge.LegacyAdapter.authorizationProjection projection

noncomputable def typedDeclaration :
    TypedCellHyperedge.Declaration DeclaredTurn.effectSchema effectMaterializer
      permissivePortal typedProjection Bool where
  pre := preCell
  apex := apex
  legs := typedLeg
  composition := { fieldMode := .disjoint, order := [false, true] }

/-- The generic resource law uses the old aggregate vector as its migration
coordinate.  Both kernels check it is identically zero. -/
def typedLaw :
    TypedCellHyperedge.ResourceLaw DeclaredTurn.effectSchema effectMaterializer
      permissivePortal Digest Int where
  delta := fun _ _ => 0

theorem typedShape : typedDeclaration.ShapeValid where
  orderComplete := ⟨by decide, fun incidence => by cases incidence <;> decide⟩
  resourcesDisjoint := by
    intro left right _
    cases left <;> cases right <;> simp [typedDeclaration, typedLeg,
      TypedCellHyperedge.Declaration.legPatch, TypedCellHyperedge.Leg.patch,
      debitFamily, creditFamily,
      debitPatch, creditPatch]
  fieldsValid := by
    intro left right different
    cases left <;> cases right
    · exact absurd rfl different
    · simp [typedDeclaration, typedLeg,
        TypedCellHyperedge.Declaration.legPatch,
        TypedCellHyperedge.Leg.patch, debitFamily, creditFamily,
        debitPatch, creditPatch]
    · simp [typedDeclaration, typedLeg,
        TypedCellHyperedge.Declaration.legPatch,
        TypedCellHyperedge.Leg.patch, debitFamily, creditFamily,
        debitPatch, creditPatch]
    · exact absurd rfl different

theorem typedJointPatch_accepted :
    ∃ validated : ValidatedPatch effectMaterializer typedDeclaration.pre
        typedDeclaration.jointPatch,
      validate effectMaterializer typedDeclaration.pre
          typedDeclaration.jointPatch = ValidationOutcome.accepted validated := by
  unfold validate
  rw [dif_pos (show typedDeclaration.jointPatch.expectedPreRoot =
    typedDeclaration.pre.root from rfl)]
  rw [dif_pos (show typedDeclaration.jointPatch.fieldFootprint =
    typedDeclaration.jointPatch.namedFields from rfl)]
  rw [dif_pos (show typedDeclaration.jointPatch.resourceFootprint =
    typedDeclaration.jointPatch.namedResources from rfl)]
  exact ⟨_, rfl⟩

noncomputable def typedValidated :
    ValidatedPatch effectMaterializer typedDeclaration.pre
      typedDeclaration.jointPatch :=
  typedJointPatch_accepted.choose

noncomputable def typedCommit :
    TypedCellHyperedge.Commit typedLaw typedDeclaration where
  shape := typedShape
  validated := typedValidated
  apexExact := rfl
  aggregateBalanced := by
    funext coordinate
    simp [TypedCellHyperedge.Declaration.aggregateDelta, typedLaw]

theorem typed_commit_nonempty :
    Nonempty (TypedCellHyperedge.Commit typedLaw typedDeclaration) :=
  ⟨typedCommit⟩

theorem bridgeCertificate :
    TypedCellHyperedge.LegacyAdapter.Certificate projection declaration
      typedDeclaration
      typedLaw where
  preExact := rfl
  apexExact := rfl
  kindExact := by intro incidence; cases incidence <;> rfl
  requestExact := by intro incidence; cases incidence <;> rfl
  legFieldFootprintExact := by
    intro incidence
    cases incidence <;> decide
  legResourceFootprintEmpty := by
    intro incidence
    cases incidence <;> rfl
  legPostLogicalExact := by
    intro incidence
    cases incidence
    · rfl
    · change preCell.logical =
        DeclaredTurn.logicalOfStore preCell.logical transferFootprint preStore
      exact pre_reified_exact.symm
  jointPostLogicalExact := by
    intro validated
    rfl
  aggregateExact := by
    rw [aggregate_conserved]
    funext coordinate
    simp [TypedCellHyperedge.Declaration.aggregateDelta, typedLaw]

/-- The canonical typed commit reaches exactly the legacy committed post. -/
theorem typed_post_matches_legacy :
    typedCommit.prepared.post.logical = declaration.logicalOfStore
      (applyPatch declaration.patch declaration.preStore) :=
  TypedCellHyperedge.LegacyAdapter.committed_post_matches_legacy
    bridgeCertificate typedCommit

end Migration

/-! ## Axiom pins -/

/-- info: 'Minidregg.Kernel.DeclaredHyperedgeWitness.committed_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms committed_nonempty
/-- info: 'Minidregg.Kernel.DeclaredHyperedgeWitness.aggregate_conserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms aggregate_conserved
/-- info: 'Minidregg.Kernel.DeclaredHyperedgeWitness.rejects_wrong_apex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rejects_wrong_apex
/-- info: 'Minidregg.Kernel.DeclaredHyperedgeWitness.Migration.typed_commit_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Migration.typed_commit_nonempty
/-- info: 'Minidregg.Kernel.DeclaredHyperedgeWitness.Migration.bridgeCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Migration.bridgeCertificate

end

end Minidregg.Kernel.DeclaredHyperedgeWitness
