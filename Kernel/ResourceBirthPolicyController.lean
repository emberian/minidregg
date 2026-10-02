/-
# Kernel.ResourceBirthPolicyController -- source-pinned factory admission

The receiver checks the factory contract from the complete birth descriptor
before adding canonical old-policy authorization. These are the existing
`FactoryAuthorization` obligations, evaluated here rather than assumed from
host verdicts. The complete-domain policy adapter consumes this checked result.
-/
import Compiler.ResourceBirthCodec
import Compiler.DeclaredEffectCell
import Theory.PolicyInstall
import Kernel.ResourceBirthController
import Compiler.CredentialAuthorityPolicyRegistry
import Compiler.CanonicalRuntimeProfile
import Compiler.CanonicalAccountView
import Compiler.PhysicalLawResolution
import Compiler.WorldKindLawDependencies

namespace Minidregg.Kernel.ResourceBirthPolicyController

open Minidregg.Compiler
open Minidregg.Theory
open Minidregg.Theory.CellRegistry
open Minidregg.Theory.IndexedProgram
open Minidregg.Theory.ResourceBirth
open Minidregg.Theory.Store
open Minidregg.Theory.TypedAuthorization

set_option autoImplicit false

inductive Reject where
  | wrongFactory
  | emptyBirth
  | wrongPolicy
  | wrongFee
  | positiveSelfFee
  | schemaKind
  | ownerGrant
  | unrelatedGrant
  | duplicateGrant
  | fundingDestination
  | initialPolicy
  | grantTemplate
  /-- A born grant's authored `notBefore` lies past the admission height. -/
  | birthFuture
  /-- The admission height lies past a born grant's authored `notBefore` plus
  the template's `birthSlack`: the birth waited too long to land. -/
  | birthStale
  | ambiguousRequests
  | duplicateCell
  | capability
  | credentialShape
  | policySourceUnavailable
  | nativeSignature (reason : CredentialSignatureAdmission.Reject)
  | malformedIngress
  | preparation (reason : ResourceBirthController.Concrete.PreparationReject)
  | signature
  | policyUnavailable
  | policyRejected
  /-- A born grant's `ancestors` are not the lineage its birth requires: none
  for a root birth; for a birth under a room, the creator's presented placing
  capability and that capability's own ancestors (`BornLineage`). -/
  | roomLineage
  deriving DecidableEq, Repr

/-- The checkable part of the existing factory authorization. All fields
refer to the same complete descriptor, source pins and old authority state. -/
structure Checked {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (oldAuthority : AuthState) (descriptor : Descriptor registry) : Prop where
  factoryExact : descriptor.factory = pins.factory
  birthsPresent : descriptor.births ≠ []
  policyPinned : oldAuthority.policyAddress pins.policyId
    (oldAuthority.policyRevision pins.policyId) = pins.policyAddress
  feeBound : descriptor.FeeBound pins.tariff
  feeNontrivial : descriptor.fee.amount = 0 ∨
    descriptor.fee.payer ≠ descriptor.fee.collector
  kindsBound : ∀ item ∈ descriptor.births,
    item.resourceKind = encoding.resourceKindOf item.create.cell.kind
  ownersBound : descriptor.OwnerGrantsBound
  allGrantsBound : descriptor.AllGrantsBound
  grantIdsDistinct : descriptor.GrantIdsDistinct
  fundingBound : descriptor.FundingBound
  policiesBound : descriptor.InitialPoliciesBound

instance nativeGrantForBirthDecidable {registry : TypeRegistry Digest}
    (grant : AuthorityGrant) (item : BirthItem registry) :
    Decidable (grant.NativeForBirth item) := by
  unfold AuthorityGrant.NativeForBirth
  infer_instance

instance policyControlForBirthDecidable {registry : TypeRegistry Digest}
    (grant : AuthorityGrant) (item : BirthItem registry) :
    Decidable (grant.PolicyControlForBirth item) := by
  unfold AuthorityGrant.PolicyControlForBirth
  cases grant with
  | mk kind stored => cases kind <;> infer_instance

instance grantForBirthDecidable {registry : TypeRegistry Digest}
    (grant : AuthorityGrant) (item : BirthItem registry) :
    Decidable (grant.ForBirth item) := by
  unfold AuthorityGrant.ForBirth
  infer_instance

instance feeBoundDecidable {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) (tariff : CreationTariff) :
    Decidable (descriptor.FeeBound tariff) := by
  unfold Descriptor.FeeBound
  infer_instance

instance ownerGrantsBoundDecidable {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : Decidable descriptor.OwnerGrantsBound := by
  unfold Descriptor.OwnerGrantsBound
  infer_instance

instance allGrantsBoundDecidable {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : Decidable descriptor.AllGrantsBound := by
  unfold Descriptor.AllGrantsBound
  infer_instance

instance grantIdsDistinctDecidable {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : Decidable descriptor.GrantIdsDistinct := by
  unfold Descriptor.GrantIdsDistinct
  infer_instance

instance fundingBoundDecidable {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : Decidable descriptor.FundingBound := by
  unfold Descriptor.FundingBound
  infer_instance

instance initialPoliciesBoundDecidable {registry : TypeRegistry Digest}
    (descriptor : Descriptor registry) : Decidable descriptor.InitialPoliciesBound := by
  unfold Descriptor.InitialPoliciesBound
  infer_instance

def require (condition : Prop) [Decidable condition] (reason : Reject) :
    Except Reject (PLift condition) :=
  if accepted : condition then .ok ⟨accepted⟩ else .error reason

/-- The actual metadata admission path. Failing a later check returns no
prefix result and produces no authorization token. -/
def check {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (oldAuthority : AuthState) (descriptor : Descriptor registry) :
    Except Reject (PLift (Checked pins encoding oldAuthority descriptor)) := do
  let factoryExact ← require (descriptor.factory = pins.factory) .wrongFactory
  let birthsPresent ← require (descriptor.births ≠ []) .emptyBirth
  let policyPinned ← require (oldAuthority.policyAddress pins.policyId
    (oldAuthority.policyRevision pins.policyId) = pins.policyAddress) .wrongPolicy
  let feeBound ← require (descriptor.FeeBound pins.tariff) .wrongFee
  let feeNontrivial ← require (descriptor.fee.amount = 0 ∨
    descriptor.fee.payer ≠ descriptor.fee.collector) .positiveSelfFee
  let kindsBound ← require (∀ item ∈ descriptor.births,
    item.resourceKind = encoding.resourceKindOf item.create.cell.kind) .schemaKind
  let ownersBound ← require descriptor.OwnerGrantsBound .ownerGrant
  let allGrantsBound ← require descriptor.AllGrantsBound .unrelatedGrant
  let grantIdsDistinct ← require descriptor.GrantIdsDistinct .duplicateGrant
  let fundingBound ← require descriptor.FundingBound .fundingDestination
  let policiesBound ← require descriptor.InitialPoliciesBound .initialPolicy
  .ok ⟨⟨factoryExact.down, birthsPresent.down, policyPinned.down, feeBound.down,
    feeNontrivial.down, kindsBound.down, ownersBound.down, allGrantsBound.down,
    grantIdsDistinct.down, fundingBound.down, policiesBound.down⟩⟩

/-- Add the canonical authorization to these very checks. The result is the
existing shared factory token consumed by the conserved resource birth leg. -/
def Checked.authorize {registry : TypeRegistry Digest}
    {pins : FactoryPins} {encoding : SourceEncoding registry}
    {oldAuthority : AuthState} {descriptor : Descriptor registry}
    (checked : Checked pins encoding oldAuthority descriptor)
    {portal : Portal} {factoryPreRoot : Digest} {height : Height}
    (authorized : Authorized portal oldAuthority
      (factoryRequest pins encoding oldAuthority factoryPreRoot height descriptor)) :
    FactoryAuthorization pins encoding portal oldAuthority factoryPreRoot height descriptor where
  factoryExact := checked.factoryExact
  birthsPresent := checked.birthsPresent
  policyPinned := checked.policyPinned
  feeBound := checked.feeBound
  feeNontrivial := checked.feeNontrivial
  kindsBound := checked.kindsBound
  ownersBound := checked.ownersBound
  allGrantsBound := checked.allGrantsBound
  grantIdsDistinct := checked.grantIdsDistinct
  fundingBound := checked.fundingBound
  policiesBound := checked.policiesBound
  authorized := authorized

theorem check_of_checked {registry : TypeRegistry Digest}
    {pins : FactoryPins} {encoding : SourceEncoding registry}
    {oldAuthority : AuthState} {descriptor : Descriptor registry}
    (checked : Checked pins encoding oldAuthority descriptor) :
    check pins encoding oldAuthority descriptor = .ok ⟨checked⟩ := by
  simp [check, require, checked.factoryExact, checked.birthsPresent,
    checked.policyPinned, checked.feeBound, checked.feeNontrivial,
    checked.ownersBound, checked.allGrantsBound,
    checked.grantIdsDistinct, checked.fundingBound, checked.policiesBound, bind, Except.bind]
  rw [dif_pos checked.kindsBound]

/-- Runtime success is equivalent to the complete existing factory contract;
the reverse direction supplies the positive pole for every admissible input. -/
theorem check_accepts_iff {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (oldAuthority : AuthState) (descriptor : Descriptor registry) :
    (check pins encoding oldAuthority descriptor).toOption.isSome = true ↔
      Checked pins encoding oldAuthority descriptor := by
  constructor
  · intro accepted
    cases outcome : check pins encoding oldAuthority descriptor with
    | error reason => simp [outcome, Except.toOption] at accepted
    | ok result => exact result.down
  · intro checked
    rw [check_of_checked checked]
    rfl

theorem wrong_fee_cannot_pass {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (oldAuthority : AuthState) (descriptor : Descriptor registry)
    (wrong : descriptor.fee.amount ≠ descriptor.quotedFee pins.tariff) :
    (check pins encoding oldAuthority descriptor).toOption.isSome = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact wrong ((check_accepts_iff pins encoding oldAuthority descriptor).mp accepted).feeBound.1

theorem wrong_kind_cannot_pass {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (oldAuthority : AuthState) (descriptor : Descriptor registry)
    (item : BirthItem registry) (member : item ∈ descriptor.births)
    (wrong : item.resourceKind ≠ encoding.resourceKindOf item.create.cell.kind) :
    (check pins encoding oldAuthority descriptor).toOption.isSome = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact wrong (((check_accepts_iff pins encoding oldAuthority descriptor).mp accepted).kindsBound
    item member)

theorem check_wrong_factory {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (oldAuthority : AuthState) (descriptor : Descriptor registry)
    (wrong : descriptor.factory ≠ pins.factory) :
    check pins encoding oldAuthority descriptor = .error .wrongFactory := by
  simp [check, require, wrong, bind, Except.bind]

/-! ## The actual typed factory control-cell observation -/

abbrev FactoryCell := CellState.Materialized DeclaredEffectCell.materializer

/-- The factory's observation writes nothing: the empty patch. -/
def factoryPatch (_pre : FactoryCell) : Patch EffectDeclaration.effectLayout := []

private def unitCodec : LawfulCodec Unit where
  encode := fun _ => []
  decode := fun bytes => if bytes = [] then some () else none
  decode_encode := by intro value; cases value; simp

/-- The factory is an existing control object. Its observation is a no-op
typed leg, while the complete same descriptor commits all births and payments.
The receiving deployment fixes its kind and actual directory identity. -/
def factoryFamily {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (oldAuthority : AuthState) (pre : FactoryCell) (height : Height) :
    SemanticEffectFamily EffectDeclaration.effectLayout DeclaredEffectCell.materializer Unit where
  Declaration := Descriptor registry
  declarationCodec := encoding.codec
  pre := pre
  request := fun descriptor =>
    ⟨.object, factoryRequest pins encoding oldAuthority pre.root height descriptor⟩
  Outcome := fun _ => Unit
  outcomeCodec := fun _ => unitCodec
  ModeEvidence := fun _ _ => Unit
  Postcondition := fun _ _ logical => logical = pre.logical
  effectDigest := encoding.effectsDigest
  patch := fun _ _ => factoryPatch pre
  nullifier := fun _ _ => none
  Release := fun _ _ => Empty
  DeclassificationAuthority := fun _ _ => Empty
  ReleaseAuthorization := fun _ _ _ => Empty
  DisclosureAllowed := fun _ _ _ => True

theorem factoryValidated (pre : FactoryCell) :
    CellState.ValidatedPatch DeclaredEffectCell.materializer pre pre.root (factoryPatch pre) :=
  (CellState.validate_accepts _ pre pre.root (factoryPatch pre) rfl trivial).choose

def factoryCandidate {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (oldAuthority : AuthState) (pre : FactoryCell) (height : Height)
    (descriptor : Descriptor registry) :
    PolicyInstall.Candidate (factoryFamily pins encoding oldAuthority pre height)
      pre descriptor () where
  preStateBound := rfl
  modeEvidence := ()
  validated := factoryValidated pre
  postcondition := rfl

theorem factoryCandidate_preserves_control_cell {registry : TypeRegistry Digest}
    (pins : FactoryPins) (encoding : SourceEncoding registry)
    (oldAuthority : AuthState) (pre : FactoryCell) (height : Height)
    (descriptor : Descriptor registry) :
    (factoryCandidate pins encoding oldAuthority pre height descriptor).post.logical =
      pre.logical := rfl

/-! ## One fixed receiving tuple from the actual prepared birth -/
namespace Concrete

-- Keep the source-owned profile identity opaque during type inference. Without
-- this, Lean tries to invert its cSHAKE computation when recovering the runtime
-- profile from an indexed preparation. Runtime evaluation is unchanged.
attribute [local irreducible] CanonicalRuntimeProfile.Profile.compilerProfile

open Minidregg.Compiler.CanonicalPolicyAdmission
open Minidregg.Compiler.CredentialAuthorityPolicyRegistry
open Minidregg.Compiler.ResourceBirthCodec
open Minidregg.Kernel.MultiCellHyperedge
open Minidregg.Theory.CellState

abbrev Registry := CanonicalCellRegistry.registry
abbrev Deployment := CanonicalCellRegistry.Deployment
abbrev Durable := ResourceBirthController.Concrete.Durable
abbrev PreparedBirth {F : Type} [Field F] :=
  ResourceBirthController.Concrete.PreparedBirth (F := F)

/-- The authority incidence is the one authority cell at the deployment's pinned
identifier. Allocation incidences are already outer lifecycle slots and are
never packed into a second envelope. -/
inductive Incidence (count : Nat) where
  | factory
  | book
  | authority
  | allocation (index : Fin count)
  deriving DecidableEq, Fintype

abbrev Source (descriptor : Descriptor Registry) := { actual : Descriptor Registry // actual = descriptor }

abbrev Legs (descriptor : Descriptor Registry) := Incidence descriptor.createRequests.length

def creation (descriptor : Descriptor Registry) (index : Fin descriptor.createRequests.length) :=
  descriptor.createRequests.get index

section Receiving

variable {F : Type} [Field F] {profile : CanonicalRuntimeProfile.Profile F}
    {deployment : Deployment} {pins : FactoryPins} {durable : Durable}
    {descriptor : Descriptor Registry}

def oldAuthority (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) : AuthState :=
  prepared.authority.snapshot.authState

/-- The first factory issues exactly one ordinary owner grant and one separate
policy-control grant per newborn. Sharing is a later authorized delegation,
not permission to nominate extra arbitrary grants during creation. -/
def ownerVerbs : (kind : ResourceKind) → Finset (Verb kind)
  | .object => {.observeObject, .mutateObject, .delegateObject, .appendObject, .placeObject}
  | .account => {.observeAccount, .transfer, .delegateAccount, .mintAsset, .burnAsset}
  | .program => {.observeProgram, .installProgram, .delegateProgram}

/-- The admission window of one born grant. Its author names `notBefore` (the
height it authored at); the receiver admits the birth from that height through
`birthSlack` later heights. Any admission in between (a clock tick, a
friend's write) does not invalidate the birth. -/
def BirthWindow (template : CanonicalRuntimeProfile.FactoryTemplate)
    (height : Height) (grant : AuthorityGrant) : Prop :=
  grant.capability.head.notBefore ≤ height ∧
    height ≤ grant.capability.head.notBefore + template.birthSlack

/-- A root grant issued by the factory. Its window is the author's own:
`notAfter = notBefore + template.lifetime` fixes the lifetime from the authored
`notBefore`, and the admission height enters only through `BirthWindow`. The
grant installed is therefore the grant signed, at every admissible height. -/
def RootGrantShape (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (grant : AuthorityGrant) : Prop :=
  grant.capability.head.issuer = template.issuer ∧
  grant.capability.head.issuerEpoch = authority.issuerEpoch template.issuer ∧
  grant.capability.head.root = grant.capability.head.id ∧
  grant.capability.head.parent = none ∧
  grant.capability.head.channels = ∅ ∧
  grant.capability.ancestry = [] ∧
  BirthWindow template height grant ∧
  grant.capability.head.notAfter = grant.capability.head.notBefore + template.lifetime ∧
  grant.capability.head.scope.maxCost = template.ownerBudget

def NativeOwnerGrant (grant : AuthorityGrant) (item : BirthItem Registry) : Prop :=
  grant.NativeForBirth item ∧
    grant.capability.head.scope.verbs = ownerVerbs grant.kind ∧
    grant.capability.head.holder = .subject item.owner

def PolicyOwnerGrant (grant : AuthorityGrant) (item : BirthItem Registry) : Prop :=
  grant.PolicyControlForBirth item ∧ grant.capability.head.holder = .subject item.owner

/-- This source contract is evaluated over the complete committed descriptor.
Its issuer, time window and budget come from the shared runtime profile that
also identifies every installed policy; they are not fields of the ingress. -/
def TemplateBound (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (descriptor : Descriptor Registry) : Prop :=
  (∀ grant ∈ descriptor.grants, RootGrantShape template authority height grant) ∧
  (∀ item ∈ descriptor.births, ∃ native ∈ descriptor.grants,
    NativeOwnerGrant native item ∧ ∃ control ∈ descriptor.grants,
      PolicyOwnerGrant control item ∧ control.capability.head.id ≠ native.capability.head.id) ∧
  (∀ grant ∈ descriptor.grants, ∃ item ∈ descriptor.births,
    NativeOwnerGrant grant item ∨ PolicyOwnerGrant grant item) ∧
  descriptor.grants.length = 2 * descriptor.births.length

instance birthWindowDecidable (template : CanonicalRuntimeProfile.FactoryTemplate)
    (height : Height) (grant : AuthorityGrant) :
    Decidable (BirthWindow template height grant) := by
  unfold BirthWindow
  infer_instance

/-! ### A born grant's revocation lineage (PLACE §2.2: a kick takes down the docs)

Authority over a cell born in a room is an attenuation of the creator's room
grant. The born owner and control grants cannot be `Attenuates`-children of it:
`Capability` is kind-indexed (the control grant is `.program`, the room grant
`.object`) and `Attenuates.policyId` keeps the parent's policy while
`AuthorityGrant.NativeForBirth` gives every newborn its own (`policyId = cell`).
So they are roots (`parent = none`, `root = id`, `RootGrantShape`) whose
`ancestors` are the presented room grant's lineage: the placing capability and
its own ancestors. `Admissible.ancestorNotRevoked` then refuses them, and every
attenuation or delegation of them (each copies its parent's ancestors), once
that room grant or anything above it is revoked. A root birth names no placing
capability and its grants carry no ancestors. -/

/-- The revocation lineage of a stored object capability: its own ancestors,
read from the authority cell (`none`: no such capability). -/
def placementLineage {M : CellState.Materializer CredentialAuthorityState.layout Digest}
    (cell : CredentialAuthorityState.Cell M) (placement : CapabilityId) :
    Option (Finset CapabilityId) :=
  (CredentialAuthorityState.readCapability cell .object placement).map (·.head.ancestors)

/-- What a born grant's `ancestors` must be: empty for a root birth; for a
birth under a room, `insert placement (ancestors of placement)`. `none` when
the placement is not a stored capability (the room gate refuses that birth). -/
def bornAncestors (lineage : CapabilityId → Option (Finset CapabilityId))
    (item : BirthItem Registry) : Option (Finset CapabilityId) :=
  match item.placement with
  | none => some ∅
  | some placement => (lineage placement).map (insert placement)

/-- Every grant born for an item carries exactly that item's `bornAncestors`. -/
def BornLineage (lineage : CapabilityId → Option (Finset CapabilityId))
    (descriptor : Descriptor Registry) : Prop :=
  ∀ item ∈ descriptor.births, ∀ grant ∈ descriptor.grants, grant.ForBirth item →
    bornAncestors lineage item = some grant.capability.head.ancestors

instance bornLineageDecidable (lineage : CapabilityId → Option (Finset CapabilityId))
    (descriptor : Descriptor Registry) : Decidable (BornLineage lineage descriptor) := by
  unfold BornLineage
  infer_instance

/-- A grant born under a room carries the creator's placing capability among
its ancestors. -/
theorem placement_mem_born_ancestors {lineage : CapabilityId → Option (Finset CapabilityId)}
    {descriptor : Descriptor Registry} (bound : BornLineage lineage descriptor)
    {item : BirthItem Registry} (member : item ∈ descriptor.births)
    {placement : CapabilityId} (placed : item.placement = some placement)
    {grant : AuthorityGrant} (grantMember : grant ∈ descriptor.grants)
    (forBirth : grant.ForBirth item) :
    placement ∈ grant.capability.head.ancestors := by
  have pinned := bound item member grant grantMember forBirth
  simp only [bornAncestors, placed] at pinned
  cases found : lineage placement with
  | none => simp [found] at pinned
  | some ancestors =>
      simp only [found, Option.map_some, Option.some.injEq] at pinned
      rw [← pinned]
      exact Finset.mem_insert_self placement ancestors

/-- A root birth's grants carry no ancestors. -/
theorem root_born_ancestors_empty {lineage : CapabilityId → Option (Finset CapabilityId)}
    {descriptor : Descriptor Registry} (bound : BornLineage lineage descriptor)
    {item : BirthItem Registry} (member : item ∈ descriptor.births)
    (root : item.placement = none)
    {grant : AuthorityGrant} (grantMember : grant ∈ descriptor.grants)
    (forBirth : grant.ForBirth item) :
    grant.capability.head.ancestors = ∅ := by
  have pinned := bound item member grant grantMember forBirth
  simp only [bornAncestors, root] at pinned
  exact (Option.some.inj pinned).symm

instance rootGrantShapeDecidable (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (grant : AuthorityGrant) :
    Decidable (RootGrantShape template authority height grant) := by
  unfold RootGrantShape
  infer_instance

instance nativeOwnerGrantDecidable (grant : AuthorityGrant) (item : BirthItem Registry) :
    Decidable (NativeOwnerGrant grant item) := by
  unfold NativeOwnerGrant
  infer_instance

instance policyOwnerGrantDecidable (grant : AuthorityGrant) (item : BirthItem Registry) :
    Decidable (PolicyOwnerGrant grant item) := by
  unfold PolicyOwnerGrant
  infer_instance

instance templateBoundDecidable (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (descriptor : Descriptor Registry) :
    Decidable (TemplateBound template authority height descriptor) := by
  unfold TemplateBound
  infer_instance

/-- The template check, with the window refusals named before the shape. A
grant authored past the admission height is `birthFuture`; a birth admitted
past its slack is `birthStale`; `grantTemplate` is reserved for a descriptor
whose every window is open and whose shape is wrong. -/
def checkTemplateAt (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (descriptor : Descriptor Registry) :
    Except Reject (PLift (TemplateBound template authority height descriptor)) :=
  if ∃ grant ∈ descriptor.grants, height < grant.capability.head.notBefore then
    .error .birthFuture
  else if ∃ grant ∈ descriptor.grants,
      grant.capability.head.notBefore + template.birthSlack < height then
    .error .birthStale
  else require (TemplateBound template authority height descriptor) .grantTemplate

def checkTemplate (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) : Except Reject (PLift (TemplateBound profile.template
      (oldAuthority prepared) height descriptor)) :=
  checkTemplateAt profile.template (oldAuthority prepared) height descriptor

/-- A correct ordinary program-edit grant never includes policy replacement,
even though both resources use the same numerical target id. -/
theorem owner_program_cannot_replace_policy :
    (Verb.installPolicy) ∉ ownerVerbs .program := by decide

theorem template_issuer_exact (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (descriptor : Descriptor Registry)
    (bound : TemplateBound template authority height descriptor)
    (grant : AuthorityGrant) (member : grant ∈ descriptor.grants) :
    grant.capability.head.issuer = template.issuer := (bound.1 grant member).1

theorem arbitrary_issuer_refused (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (descriptor : Descriptor Registry)
    (grant : AuthorityGrant) (member : grant ∈ descriptor.grants)
    (wrong : grant.capability.head.issuer ≠ template.issuer) :
    ¬TemplateBound template authority height descriptor := by
  intro bound
  exact wrong (template_issuer_exact template authority height descriptor bound grant member)

/-! ## The birth window: the author names it, the receiver admits a bounded lag

The descriptor is authored at a height `H0` and its root grants carry
`notBefore = H0`, `notAfter = H0 + lifetime`. Any admission between authoring
and admission (a clock tick, a friend's write) moves the admission height; the
birth stays admissible while that height is within `birthSlack` of `H0`, and
the grant installed is the grant the author signed. -/

/-- The shape restated: a root grant admitted at `height` has its window open
at `height`, and its lifetime runs from the authored `notBefore`. -/
theorem rootGrantShape_window (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (grant : AuthorityGrant)
    (shape : RootGrantShape template authority height grant) :
    grant.capability.head.notBefore ≤ height ∧
      height ≤ grant.capability.head.notBefore + template.birthSlack ∧
      grant.capability.head.notAfter = grant.capability.head.notBefore + template.lifetime :=
  ⟨shape.2.2.2.2.2.2.1.1, shape.2.2.2.2.2.2.1.2, shape.2.2.2.2.2.2.2.1⟩

/-- A named projection keeps callers independent of the grant-shape tuple's
other fields. -/
theorem rootGrantShape_birthWindow (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (grant : AuthorityGrant)
    (shape : RootGrantShape template authority height grant) : BirthWindow template height grant :=
  ⟨(rootGrantShape_window template authority height grant shape).1,
    (rootGrantShape_window template authority height grant shape).2.1⟩

/-- The admission height enters a root grant's shape only through its window. -/
theorem rootGrantShape_height_move (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) {height height' : Height} (grant : AuthorityGrant)
    (shape : RootGrantShape template authority height grant)
    (window : BirthWindow template height' grant) :
    RootGrantShape template authority height' grant := by
  obtain ⟨issuer, epoch, root, parent, channels, ancestry, _, notAfter, budget⟩ := shape
  exact ⟨issuer, epoch, root, parent, channels, ancestry, window, notAfter, budget⟩

theorem templateBound_height_move (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) {height height' : Height} (descriptor : Descriptor Registry)
    (bound : TemplateBound template authority height descriptor)
    (windows : ∀ grant ∈ descriptor.grants, BirthWindow template height' grant) :
    TemplateBound template authority height' descriptor :=
  ⟨fun grant member => rootGrantShape_height_move template authority grant
      (bound.1 grant member) (windows grant member),
    bound.2.1, bound.2.2.1, bound.2.2.2⟩

/-- A grant outside its window refuses the whole template, whatever its shape. -/
theorem outside_window_not_templateBound (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (descriptor : Descriptor Registry)
    (grant : AuthorityGrant) (member : grant ∈ descriptor.grants)
    (outside : ¬BirthWindow template height grant) :
    ¬TemplateBound template authority height descriptor :=
  fun bound => outside (rootGrantShape_birthWindow template authority height grant (bound.1 grant member))

/-- An honest descriptor authored at `authored`: it satisfies the template at
its own height, and every grant names that height as its `notBefore`. -/
def AuthoredAt (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (authored : Height) (descriptor : Descriptor Registry) : Prop :=
  TemplateBound template authority authored descriptor ∧
    ∀ grant ∈ descriptor.grants, grant.capability.head.notBefore = authored

theorem checkTemplateAt_of_bound (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (descriptor : Descriptor Registry)
    (bound : TemplateBound template authority height descriptor) :
    checkTemplateAt template authority height descriptor = .ok ⟨bound⟩ := by
  have notFuture : ¬∃ grant ∈ descriptor.grants, height < grant.capability.head.notBefore := by
    rintro ⟨grant, member, early⟩
    exact Nat.not_le.mpr early
      (rootGrantShape_birthWindow template authority height grant (bound.1 grant member)).1
  have notStale : ¬∃ grant ∈ descriptor.grants,
      grant.capability.head.notBefore + template.birthSlack < height := by
    rintro ⟨grant, member, late⟩
    exact Nat.not_le.mpr late
      (rootGrantShape_birthWindow template authority height grant (bound.1 grant member)).2
  unfold checkTemplateAt
  rw [if_neg notFuture, if_neg notStale]
  unfold require
  rw [dif_pos bound]

/-- The check accepts exactly the template contract. -/
theorem checkTemplateAt_ok_iff (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) (height : Height) (descriptor : Descriptor Registry) :
    (checkTemplateAt template authority height descriptor).toOption.isSome = true ↔
      TemplateBound template authority height descriptor := by
  constructor
  · intro accepted
    cases outcome : checkTemplateAt template authority height descriptor with
    | error reason => simp [outcome, Except.toOption] at accepted
    | ok result => exact result.down
  · intro bound
    rw [checkTemplateAt_of_bound template authority height descriptor bound]
    rfl

/-- Positive pole: an honest birth authored at `authored` is admitted at every
height from `authored` through `authored + birthSlack`, and the grants it
installs keep the window their author named. -/
theorem birth_admitted_within_slack (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) {authored height : Height} (descriptor : Descriptor Registry)
    (honest : AuthoredAt template authority authored descriptor)
    (fromAuthored : authored ≤ height) (withinSlack : height ≤ authored + template.birthSlack) :
    (∃ bound, checkTemplateAt template authority height descriptor = .ok bound) ∧
      ∀ grant ∈ descriptor.grants, grant.capability.head.notBefore = authored ∧
        grant.capability.head.notAfter = authored + template.lifetime := by
  have windows : ∀ grant ∈ descriptor.grants, BirthWindow template height grant := by
    intro grant member
    rw [BirthWindow, honest.2 grant member]
    exact ⟨fromAuthored, withinSlack⟩
  refine ⟨⟨_, checkTemplateAt_of_bound template authority height descriptor
    (templateBound_height_move template authority descriptor honest.1 windows)⟩, ?_⟩
  intro grant member
  have notAfter := (rootGrantShape_window template authority authored grant
    (honest.1.1 grant member)).2.2
  rw [honest.2 grant member] at notAfter
  exact ⟨honest.2 grant member, notAfter⟩

/-- Negative pole: a birth admitted past a grant's `notBefore + birthSlack` is
refused `birthStale`, never `grantTemplate`. -/
theorem birth_refused_beyond_slack (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) {height : Height} (descriptor : Descriptor Registry)
    (notFuture : ∀ grant ∈ descriptor.grants, grant.capability.head.notBefore ≤ height)
    (stale : ∃ grant ∈ descriptor.grants,
      grant.capability.head.notBefore + template.birthSlack < height) :
    checkTemplateAt template authority height descriptor = .error .birthStale := by
  have early : ¬∃ grant ∈ descriptor.grants, height < grant.capability.head.notBefore := by
    rintro ⟨grant, member, before⟩
    exact Nat.not_le.mpr before (notFuture grant member)
  unfold checkTemplateAt
  rw [if_neg early, if_pos stale]

/-- The honest form: a birth authored at `authored` and admitted after
`authored + birthSlack` is refused `birthStale`. -/
theorem authored_birth_refused_beyond_slack (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) {authored height : Height} (descriptor : Descriptor Registry)
    (honest : AuthoredAt template authority authored descriptor)
    (nonempty : descriptor.grants ≠ []) (late : authored + template.birthSlack < height) :
    checkTemplateAt template authority height descriptor = .error .birthStale := by
  refine birth_refused_beyond_slack template authority descriptor ?_ ?_
  · intro grant member
    rw [honest.2 grant member]
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) late)
  · obtain ⟨grant, member⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨grant, member, by rw [honest.2 grant member]; exact late⟩

/-- A birth whose grant names a `notBefore` past the admission height is
refused `birthFuture`. -/
theorem future_birth_refused (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) {height : Height} (descriptor : Descriptor Registry)
    (future : ∃ grant ∈ descriptor.grants, height < grant.capability.head.notBefore) :
    checkTemplateAt template authority height descriptor = .error .birthFuture := by
  unfold checkTemplateAt
  rw [if_pos future]

/-- `grantTemplate` never names a window: when it is the refusal, every grant's
window is open at the admission height and the shape is what failed. -/
theorem grantTemplate_only_inside_window (template : CanonicalRuntimeProfile.FactoryTemplate)
    (authority : AuthState) {height : Height} (descriptor : Descriptor Registry)
    (refused : checkTemplateAt template authority height descriptor = .error .grantTemplate) :
    ∀ grant ∈ descriptor.grants, BirthWindow template height grant := by
  intro grant member
  unfold checkTemplateAt at refused
  by_cases future : ∃ grant ∈ descriptor.grants, height < grant.capability.head.notBefore
  · rw [if_pos future] at refused
    cases refused
  · rw [if_neg future] at refused
    by_cases stale : ∃ grant ∈ descriptor.grants,
        grant.capability.head.notBefore + template.birthSlack < height
    · rw [if_pos stale] at refused
      cases refused
    · exact ⟨Nat.not_lt.mp fun early => future ⟨grant, member, early⟩,
        Nat.not_lt.mp fun late => stale ⟨grant, member, late⟩⟩

/-! ### Both poles on one concrete descriptor

One object birth with its owner and control grants, authored at height 100
under a template with `birthSlack = 64`. The descriptor is admitted at 101
(the measured defect: one tick landed between authoring and admission) and at
164, and refused `birthStale` at 165 and `birthFuture` at 99. -/
namespace WindowExample

def template : CanonicalRuntimeProfile.FactoryTemplate := ⟨⟨5⟩, 100000, 10000, 64⟩

def authority : AuthState where
  capabilityRoot := ⟨0⟩
  revocationRoot := ⟨0⟩
  policyRoot := ⟨0⟩
  policyAddress := fun _ _ => ⟨0⟩
  revoked := ∅
  issuerEpoch := fun _ => 2
  policyEpoch := fun _ => 0
  policyRevision := fun _ => 0
  subjectKeyEpoch := fun _ => 0
  parent := Parentage.empty

def target : Nat := 7001

def item : BirthItem Registry where
  create := ⟨target, CellSlot.root CanonicalCellRegistry.registry .absent,
    CanonicalCellRegistry.Witness.emptyContent⟩
  resourceKind := .object
  owner := ⟨8⟩
  parent := none
  placement := none

def ownerCapability (authored : Height) : Capability .object where
  id := ⟨71⟩
  root := ⟨71⟩
  parent := none
  issuer := ⟨5⟩
  holder := .subject ⟨8⟩
  scope := ⟨.under target, ownerVerbs .object, 100000, none, ∅⟩
  notBefore := authored
  notAfter := authored + 10000
  issuerEpoch := 2
  policyId := ⟨target⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

def controlCapability (authored : Height) : Capability .program where
  id := ⟨72⟩
  root := ⟨72⟩
  parent := none
  issuer := ⟨5⟩
  holder := .subject ⟨8⟩
  scope := ⟨.explicit {⟨target⟩}, {Verb.installPolicy, Verb.revokeCapability}, 100000, none, ∅⟩
  notBefore := authored
  notAfter := authored + 10000
  issuerEpoch := 2
  policyId := ⟨target⟩
  policyEpoch := 0
  ancestors := ∅
  channels := ∅

def ownerGrant (authored : Height) : AuthorityGrant := ⟨.object, ⟨ownerCapability authored, []⟩⟩

def controlGrant (authored : Height) : AuthorityGrant :=
  ⟨.program, ⟨controlCapability authored, []⟩⟩

def birthDescriptor (authored : Height) : Descriptor Registry where
  factory := ⟨10⟩
  creator := ⟨8⟩
  transactionId := ⟨0⟩
  nonce := 0
  births := [item]
  auxiliaryCreates := []
  grants := [ownerGrant authored, controlGrant authored]
  authorityNullifier := 0
  funding := []
  fee := ⟨0, 0, 0, 0⟩

theorem authored : AuthoredAt template authority 100 (birthDescriptor 100) := by
  refine ⟨by decide, ?_⟩
  intro grant member
  simp only [birthDescriptor, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem admitted_one_tick_later :
    ∃ bound, checkTemplateAt template authority 101 (birthDescriptor 100) = .ok bound :=
  (birth_admitted_within_slack template authority (birthDescriptor 100) authored
    (by decide) (by decide)).1

theorem admitted_at_slack_edge :
    ∃ bound, checkTemplateAt template authority 164 (birthDescriptor 100) = .ok bound :=
  (birth_admitted_within_slack template authority (birthDescriptor 100) authored
    (by decide) (by decide)).1

theorem refused_past_slack :
    checkTemplateAt template authority 165 (birthDescriptor 100) = .error .birthStale :=
  authored_birth_refused_beyond_slack template authority (birthDescriptor 100) authored
    (by simp [birthDescriptor]) (by decide)

theorem refused_before_authored :
    checkTemplateAt template authority 99 (birthDescriptor 100) = .error .birthFuture :=
  future_birth_refused template authority (birthDescriptor 100)
    ⟨ownerGrant 100, by simp [birthDescriptor], by decide⟩

end WindowExample

/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.rootGrantShape_window' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rootGrantShape_window
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.templateBound_height_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms templateBound_height_move
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.checkTemplateAt_ok_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkTemplateAt_ok_iff
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.birth_admitted_within_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms birth_admitted_within_slack
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.birth_refused_beyond_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms birth_refused_beyond_slack
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.authored_birth_refused_beyond_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms authored_birth_refused_beyond_slack
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.future_birth_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms future_birth_refused
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.grantTemplate_only_inside_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms grantTemplate_only_inside_window
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.WindowExample.authored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WindowExample.authored
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.WindowExample.admitted_one_tick_later' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WindowExample.admitted_one_tick_later
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.WindowExample.admitted_at_slack_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WindowExample.admitted_at_slack_edge
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.WindowExample.refused_past_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WindowExample.refused_past_slack
/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.WindowExample.refused_before_authored' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms WindowExample.refused_before_authored

/-- Request metadata is entirely source-derived except the receiver's trusted
height. That height is a service input, not asserted to be a committed clock.
Each account's policy selector is its actual source account id. -/
def resourceContexts (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (source : Descriptor Registry) (position : Nat) :
    CanonicalResourceEffect.RequestContext :=
  let operation := source.resourceBatch.operations[position]?
  let policyId : PolicyId := ⟨(operation.map fun op => op.posting.source).getD source.fee.payer⟩
  { domain := pins.domain
    semantics := pins.semantics
    federation := pins.federation
    subject := source.creator
    subjectKeyEpoch := (oldAuthority prepared).subjectKeyEpoch source.creator
    nonce := source.nonce
    height := height
    policyId := policyId
    policyEpoch := (oldAuthority prepared).policyEpoch policyId
    policyRevision := (oldAuthority prepared).policyRevision policyId }

def layout (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) : CellLayout (Legs descriptor) where
  storeLayout
    | .factory => EffectDeclaration.effectLayout
    | .book => CanonicalResourceKernel.layout
    | .authority => CredentialAuthorityState.layout
    | .allocation _ => LifecycleSlot.layout Registry
  materializer
    | .factory => DeclaredEffectCell.materializer
    | .book => CanonicalResourcePageMaterializer.materializer
    | .authority => CredentialAuthorityCell.materializer
    | .allocation _ => LifecycleSlot.materializer Registry
  projectAuthority := fun _ _ => oldAuthority prepared
  cellId
    | .factory => ⟨deployment.factoryId⟩
    | .book => ⟨deployment.resourceBookId⟩
    | .authority => ⟨deployment.authorityCellId⟩
    | .allocation index => ⟨(creation descriptor index).cellId⟩

def rawLeg (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) (height : Height)
    (source : Source descriptor) : (incidence : Legs descriptor) →
      CandidateLegData (layout prepared) incidence
  | .factory =>
      { pre := prepared.factory.payload
        patch := factoryPatch prepared.factory.payload
        request := ⟨.object, factoryRequest pins CanonicalCellRegistry.sourceEncoding
          (oldAuthority prepared) prepared.factory.payload.root height source.val⟩
        Postcondition := fun post => post = prepared.factory.payload.logical }
  | .book =>
      { pre := prepared.book.payload
        patch := source.val.resourceBatch.patch prepared.book.payload
        request := ⟨.account, CanonicalResourceEffect.birthRequest
          CanonicalCellRegistry.sourceEncoding prepared.book.payload
          (resourceContexts prepared height source.val) source.val⟩
        Postcondition := fun post =>
          (source.val.resourceBatch.patch prepared.book.payload).ResultAt
            prepared.book.payload.logical post ∧
          CanonicalResourceKernel.logicalBook post = source.val.resourceBatch.apply
            (CanonicalResourceKernel.logicalBook prepared.book.payload.logical) }
  | .authority =>
      { pre := prepared.authority.snapshot.cell
        patch := ResourceBirthAuthority.patch prepared.authority.snapshot.cell source.val
        request := ⟨.object, ResourceBirthAuthority.request pins
          CanonicalCellRegistry.sourceEncoding
          prepared.authority.snapshot.cell height source.val⟩
        Postcondition := ResourceBirthAuthority.Postcondition source.val }
  | .allocation index =>
      { pre := ResourceBirthController.allocationPre prepared.directory.directory (creation descriptor index)
        patch := ResourceBirthController.allocationPatch (creation descriptor index)
        request := ⟨.object, ResourceBirthController.allocationRequest pins
          CanonicalCellRegistry.sourceEncoding (oldAuthority prepared) prepared.directory.directory
          (creation descriptor index) height source.val⟩
        Postcondition := fun post => post = LifecycleSlot.state Registry (.live (creation descriptor index).cell) }

def bindFamily (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) (height : Height)
    (source : Source descriptor) (portals : Legs descriptor → Portal) :
    (incidence : Legs descriptor) → SemanticLegBinding (rawLeg prepared height source incidence)
  | .factory =>
      { Nullifier := Unit
        family := factoryFamily pins CanonicalCellRegistry.sourceEncoding
          (oldAuthority prepared) prepared.factory.payload height
        declaration := source.val, outcome := ()
        preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }
  | .book =>
      { Nullifier := Unit
        family := CanonicalResourceEffect.birthFamily pins CanonicalCellRegistry.sourceEncoding
          (portals .factory) (portals .book) (oldAuthority prepared) prepared.factory.payload.root height
          prepared.book.payload (resourceContexts prepared height source.val)
        declaration := source.val, outcome := ()
        preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }
  | .authority =>
      { Nullifier := Nat
        family := ResourceBirthAuthority.family pins CanonicalCellRegistry.sourceEncoding
          prepared.authority.snapshot.cell height
        declaration := source.val, outcome := ()
        preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }
  | .allocation index =>
      { Nullifier := Nat
        family := ResourceBirthController.allocationFamily pins CanonicalCellRegistry.sourceEncoding
          (oldAuthority prepared) prepared.directory.directory (creation descriptor index) height
        declaration := source.val, outcome := ()
        preExact := rfl, requestExact := rfl, effectsExact := rfl, patchExact := rfl
        postconditionExact := fun _ => Iff.rfl }

def plan (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) (height : Height) :
    PreparationPlan (layout prepared) (Source descriptor) where
  leg := rawLeg prepared height
  jointDigest := fun source => CanonicalCellRegistry.sourceEncoding.effectsDigest source.val
  legEffectsDigest := fun source _ => CanonicalCellRegistry.sourceEncoding.effectsDigest source.val
  bindFamily := bindFamily prepared height

/-- Every allocated identity was fresh in the loaded directory: the allocator
accepted the whole descriptor. -/
theorem allocationFresh (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (index : Fin descriptor.createRequests.length) :
    LifecycleImage.view Registry prepared.directory.directory (creation descriptor index).cellId = .fresh :=
  prepared.allocated.fresh_pre (creation descriptor index) (List.get_mem _ _)

theorem validated (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) (height : Height) :
    (incidence : Legs descriptor) → ValidatedPatch ((layout prepared).materializer incidence)
      (rawLeg prepared height ⟨descriptor, rfl⟩ incidence).pre
      (rawLeg prepared height ⟨descriptor, rfl⟩ incidence).request.2.preStateRoot
      (rawLeg prepared height ⟨descriptor, rfl⟩ incidence).patch
  | .factory => factoryValidated prepared.factory.payload
  | .book => prepared.resources.validated
  | .authority => ResourceBirthAuthority.validated prepared.authority.snapshot.cell descriptor
      prepared.grants.mode
  | .allocation index => ResourceBirthController.allocationValidated
      prepared.directory.directory (creation descriptor index) (allocationFresh prepared index)

theorem postconditions (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) (height : Height) :
    ∀ incidence, (rawLeg prepared height ⟨descriptor, rfl⟩ incidence).Postcondition
      (validated prepared height incidence).apply.logical := by
  intro incidence
  cases incidence with
  | factory =>
      exact factoryCandidate_preserves_control_cell pins CanonicalCellRegistry.sourceEncoding
        (oldAuthority prepared) prepared.factory.payload height descriptor
  | book => exact ⟨prepared.resources.validated.resultAt, prepared.resources.post_logicalBook⟩
  | authority => exact prepared.grants.mode.postcondition
  | allocation index =>
      exact ResourceBirthController.allocation_post_exact
        prepared.directory.directory (creation descriptor index) (allocationFresh prepared index)

/-- This finite check verifies the real deployment/catalogue/allocation IDs.
It is not a proof supplied by the requester or a presumed hash-injectivity
law. All new identities were also checked by the permanent allocator. -/
def prepareTuple (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) (height : Height)
    (primary : Legs descriptor) : Option (PreparedTuple (plan prepared height)) :=
  if distinct : Function.Injective (layout prepared).cellId then
    some
      { source := ⟨descriptor, rfl⟩, primary := primary
        validated := validated prepared height
        postconditions := postconditions prepared height
        cellIdsDistinct := distinct
        requestEffects := by intro incidence; cases incidence <;> rfl }
  else none

/-- The shared byte-slot encoding is used only on explicitly selected source
data. Selecting a complete canonical cell is a disclosure decision. -/
def bytesSlots (stem : String) : Nat → List UInt8 → List (String × Int)
  | _, [] => []
  | offset, byte :: rest =>
      (s!"{stem}/{offset}", Int.ofNat byte.toNat) :: bytesSlots stem (offset + 1) rest

/-- The reviewable user command excludes source-generated auxiliary creates.
All remaining fields are the exact user-authored draft, not old world state. -/
def userCommandBytes (source : Descriptor Registry) : List UInt8 :=
  CanonicalCellRegistry.sourceEncoding.codec.encode { source with auxiliaryCreates := [] }

theorem userCommandBytes_auxiliary_independent (source : Descriptor Registry)
    (allocations : List (CreateRequest (CellId := Nat) Registry)) :
    userCommandBytes { source with auxiliaryCreates := allocations } = userCommandBytes source := rfl

/-- Account laws see their own balance cut. The complete Book still enters
conservation and exact candidate validation, but is not an oracle accessible to
user predicates. Factory laws see only their own resource; authority and
physical allocation state never enter this programmable projection. -/
def policyResourceSlots (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (wanted : PackedEffectRequest)
    (logical : (incidence : Legs descriptor) → Store ((layout prepared).storeLayout incidence)) :
    List (String × Int) :=
  match wanted with
  | ⟨.account, request⟩ =>
      CanonicalAccountView.slots
        (CanonicalResourceKernel.logicalBook (logical .book)) request.target.value
  | ⟨.object, request⟩ =>
      if request.policyId.value = deployment.factoryId then
        bytesSlots "cell/factory/bytes" 0
          (DeclaredEffectCell.materializer.codec.encode (logical .factory))
      else []
  | ⟨.program, _⟩ => []

/-- State-dependent input is restricted to the governing resource's cut.
The source descriptor still binds all proposed effects, while no account law
can inspect another balance via the observable accept/refuse result. -/
def projectForRequest (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) (_height : Height)
    (wanted : PackedEffectRequest) (source : Source descriptor)
    (logical : (incidence : Legs descriptor) → Store ((layout prepared).storeLayout incidence)) :
    Minidregg.Pred.State :=
  let header := WorldKindLawDependencies.targetSelectorSlots prepared.directory.directory
    wanted.2.target.value ++ CanonicalRuntimeProfile.requestSlots wanted.2 ++
    [ ("request/creator", Int.ofNat source.val.creator.value)

    , ("birth/count", Int.ofNat source.val.births.length)
    , ("fee/amount", Int.ofNat source.val.fee.amount) ]
  ⟨header ++ bytesSlots "command/bytes" 0 (userCommandBytes source.val) ++
    policyResourceSlots prepared wanted logical⟩

/-- Holding the signed request and user command fixed, arbitrary changes to
every other account, authority entry, factory field, or allocation cannot
change a source account's policy view. Roots in the signed request remain
explicit public commitments, not a hiding claim. -/
theorem account_projection_noninterference
    (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (wanted : Request .account) (source : Source descriptor)
    (left right : (incidence : Legs descriptor) → Store ((layout prepared).storeLayout incidence))
    (same : ∀ asset,
      (CanonicalResourceKernel.logicalBook (left .book)).balance wanted.target.value asset =
      (CanonicalResourceKernel.logicalBook (right .book)).balance wanted.target.value asset) :
    projectForRequest prepared height ⟨.account, wanted⟩ source left =
      projectForRequest prepared height ⟨.account, wanted⟩ source right := by
  have cut := CanonicalAccountView.slots_noninterference
    (CanonicalResourceKernel.logicalBook (left .book))
    (CanonicalResourceKernel.logicalBook (right .book)) wanted.target.value same
  simp only [projectForRequest, policyResourceSlots, cut]

theorem account_policy_verdict_noninterference
    (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (wanted : Request .account) (source : Source descriptor)
    (leftOld rightOld leftNew rightNew :
      (incidence : Legs descriptor) → Store ((layout prepared).storeLayout incidence))
    (oldSame : ∀ asset,
      (CanonicalResourceKernel.logicalBook (leftOld .book)).balance wanted.target.value asset =
      (CanonicalResourceKernel.logicalBook (rightOld .book)).balance wanted.target.value asset)
    (newSame : ∀ asset,
      (CanonicalResourceKernel.logicalBook (leftNew .book)).balance wanted.target.value asset =
      (CanonicalResourceKernel.logicalBook (rightNew .book)).balance wanted.target.value asset)
    (predicate : Minidregg.Pred.Pred) :
    Minidregg.Pred.eval predicate
      (projectForRequest prepared height ⟨.account, wanted⟩ source leftOld)
      (projectForRequest prepared height ⟨.account, wanted⟩ source leftNew) =
    Minidregg.Pred.eval predicate
      (projectForRequest prepared height ⟨.account, wanted⟩ source rightOld)
      (projectForRequest prepared height ⟨.account, wanted⟩ source rightNew) := by
  rw [account_projection_noninterference prepared height wanted source leftOld rightOld oldSame,
    account_projection_noninterference prepared height wanted source leftNew rightNew newSame]

/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.account_projection_noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms account_projection_noninterference

/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.account_policy_verdict_noninterference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms account_policy_verdict_noninterference

def project (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (primary : Legs descriptor) (source : Source descriptor)
    (logical : (incidence : Legs descriptor) → Store ((layout prepared).storeLayout incidence)) :
    Minidregg.Pred.State :=
  projectForRequest prepared height (rawLeg prepared height source primary).request source logical

def step (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) (height : Height)
    (tuple : PreparedTuple (plan prepared height)) : PolicyStepContext :=
  PolicyStepContext.ofPreparedTuple (project prepared height tuple.primary) profile.semantics tuple

theorem step_actual_states (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (tuple : PreparedTuple (plan prepared height)) :
    (step prepared height tuple).oldState = project prepared height tuple.primary tuple.source tuple.logicalPre ∧
      (step prepared height tuple).newState = project prepared height tuple.primary tuple.source tuple.logicalPost :=
  ⟨rfl, rfl⟩

/-- Every accepting compiled witness names a selected OLD policy and forces
that policy on its source-selected view of the actual pre/post tuple. This rules out
supplying a convenient witness state beside a different allocation or Book. -/
theorem selected_policy_evaluates_actual_tuple [DecidableEq F]
    (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) (height : Height)
    (tuple : PreparedTuple (plan prepared height))
    {config : CanonicalPolicyConfig F} {kind : ResourceKind} {request : Request kind}
    {witness : CompiledPolicyWitness F}
    (binding : config.stepBinding = .canonical (step prepared height tuple))
    (accepted : config.verifies request witness = true) :
    ∃ committed,
      config.registry.resolve request.policyId request.policyRevision = some committed ∧
      Minidregg.Pred.eval committed.record.predicate
        (project prepared height tuple.primary tuple.source tuple.logicalPre)
        (project prepared height tuple.primary tuple.source tuple.logicalPost) = true :=
  (canonical_context_verifies_sound (step prepared height tuple) binding accepted).2.2.2

/-- Final family construction and full mode authorization cannot alter a
single selected predicate slot evaluated beforehand. -/
theorem accepted_policy_view_exact
    (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) (height : Height)
    (tuple : PreparedTuple (plan prepared height)) (portals : Legs descriptor → Portal)
    (apex : Digest) (evidence : tuple.AdmissionEvidence portals) :
    project prepared height tuple.primary tuple.source
        (fun incidence => ((tuple.toDeclaration portals apex).post
          (tuple.accept portals apex evidence) incidence).logical) =
      project prepared height tuple.primary tuple.source tuple.logicalPost := by
  congr 1
  funext incidence
  exact congrArg Materialized.logical
    (tuple.accepted_posts_exact portals apex evidence incidence)


/-! ## Source-owned request dispatch over one checked joint candidate -/

/-- The Book's fee request is already one of its source requests; it is not
repeated as a second ambiguous policy branch. Every allocation has its own
source-bound coordinate in the complete signed request. -/
inductive PolicyBranch (allocations sources : Nat) where
  | factory
  | authority
  | allocation (index : Fin allocations)
  | source (index : Fin sources)
  deriving DecidableEq, Fintype

abbrev Branch (descriptor : Descriptor Registry) :=
  PolicyBranch descriptor.createRequests.length descriptor.resourceBatch.operations.length

/-- Executable exhaustive enumeration with no choice-based finite-set list. -/
def policyBranches (allocations sources : Nat) : List (PolicyBranch allocations sources) :=
  .factory :: .authority ::
    (List.finRange allocations).map .allocation ++ (List.finRange sources).map .source

theorem mem_policyBranches {allocations sources : Nat} (branch : PolicyBranch allocations sources) :
    branch ∈ policyBranches allocations sources := by
  cases branch <;> simp [policyBranches]

theorem policyBranches_nodup (allocations sources : Nat) :
    (policyBranches allocations sources).Nodup := by
  have allocationNodup : ((List.finRange allocations).map
      (PolicyBranch.allocation (sources := sources))).Nodup :=
    (List.nodup_finRange allocations).map (by intro left right same; cases same; rfl)
  have sourceNodup : ((List.finRange sources).map
      (PolicyBranch.source (allocations := allocations))).Nodup :=
    (List.nodup_finRange sources).map (by intro left right same; cases same; rfl)
  simp [policyBranches, List.nodup_append, allocationNodup, sourceNodup]

/-- Mapping each branch identity once preserves the original injectivity
guard for every identity function; collisions remain exact refusals. -/
theorem mapped_policyBranches_nodup_iff {allocations sources : Nat} {Value : Type}
    (identity : PolicyBranch allocations sources → Value) :
    ((policyBranches allocations sources).map identity).Nodup ↔ Function.Injective identity := by
  rw [List.nodup_map_iff_inj_on (policyBranches_nodup allocations sources)]
  simp only [mem_policyBranches, forall_const, Function.Injective]

/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.mapped_policyBranches_nodup_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapped_policyBranches_nodup_iff

def branchPrimary : Branch descriptor → Legs descriptor
  | .factory => .factory
  | .authority => .authority
  | .allocation index => .allocation index
  | .source _ => .book

def branchRequest
    (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) : Branch descriptor → PackedEffectRequest
  | .source index => ⟨.account, CanonicalResourceEffect.batchSourceRequest
      CanonicalCellRegistry.sourceEncoding prepared.book.payload
      (resourceContexts prepared height descriptor) descriptor index⟩
  | .factory => (rawLeg prepared height ⟨descriptor, rfl⟩ .factory).request
  | .authority => (rawLeg prepared height ⟨descriptor, rfl⟩ .authority).request
  | .allocation index => (rawLeg prepared height ⟨descriptor, rfl⟩ (.allocation index)).request

/-- Canonical wire equality is the actual branch discriminator. No digest
injectivity assumption or caller-selected source/context mapping is used. -/
def branchIdentity
    (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) (branch : Branch descriptor) :=
  AuthorizationDeclaration.encodeRequest (branchRequest prepared height branch)

structure Pending
    (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) : Prop where
  checked : Checked pins CanonicalCellRegistry.sourceEncoding (oldAuthority prepared) descriptor
  templateBound : TemplateBound profile.template (oldAuthority prepared) height descriptor
  bornLineage : BornLineage (placementLineage prepared.authority.snapshot.cell) descriptor
  cellIdsDistinct : Function.Injective (layout prepared).cellId
  requestsDistinct : Function.Injective (branchIdentity prepared height)

def preparePending
    (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor)
    (height : Height) : Except Reject (PLift (Pending prepared height)) := do
  let checked ← check pins CanonicalCellRegistry.sourceEncoding (oldAuthority prepared) descriptor
  let templateBound ← checkTemplate prepared height
  let bornLineage ← require (BornLineage (placementLineage prepared.authority.snapshot.cell)
    descriptor) .roomLineage
  letI : Decidable (Function.Injective (branchIdentity prepared height)) :=
    decidable_of_iff
      (((policyBranches descriptor.createRequests.length descriptor.resourceBatch.operations.length).map
        (branchIdentity prepared height)).Nodup)
      (mapped_policyBranches_nodup_iff (branchIdentity prepared height))
  if cells : Function.Injective (layout prepared).cellId then
    if requests : Function.Injective (branchIdentity prepared height) then
      .ok ⟨⟨checked.down, templateBound.down, bornLineage.down, cells, requests⟩⟩
    else .error .ambiguousRequests
  else .error .duplicateCell

def Pending.tuple
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (primary : Legs descriptor) :
    PreparedTuple (plan prepared height) where
  source := ⟨descriptor, rfl⟩
  primary := primary
  validated := validated prepared height
  postconditions := postconditions prepared height
  cellIdsDistinct := pending.cellIdsDistinct
  requestEffects := by intro incidence; cases incidence <;> rfl

/-- Both the source bytes and their read guard come from the complete original
physical directory. An arbitrary host-side blob map cannot enter this receiver. -/
def payloadStore
    (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) :
    Minidregg.Kernel.CanonicalPolicyRegistry.PayloadStore :=
  ⟨CanonicalCellRegistry.fetchPolicySource deployment.domain prepared.directory.directory⟩

/-- Select the already prepared pre-cell without constructing an unrelated
signed request merely to project `rawLeg.pre`. -/
def policyPreCell
    (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) :
    (incidence : Legs descriptor) → Materialized ((layout prepared).materializer incidence)
  | .factory => prepared.factory.payload
  | .book => prepared.book.payload
  | .authority => prepared.authority.snapshot.cell
  | .allocation index => ResourceBirthController.allocationPre prepared.directory.directory
      (creation descriptor index)

/-- These are the same actual candidate posts, obtained without constructing
the raw leg's request or its descriptor commitments. -/
def policyPostState
    (prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor) :
    (incidence : Legs descriptor) → Store ((layout prepared).storeLayout incidence)
  | .factory => prepared.factory.payload.logical
  | .book => prepared.resources.post.logical
  | .authority => (ResourceBirthAuthority.post prepared.authority.snapshot.cell descriptor
      prepared.grants.mode).logical
  | .allocation index => LifecycleSlot.state Registry (.live (creation descriptor index).cell)

theorem Pending.policyPreCell_exact
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (primary incidence : Legs descriptor) :
    policyPreCell prepared incidence = (pending.tuple primary).pre incidence := by
  cases incidence <;> rfl

theorem Pending.policyPostState_exact
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (primary incidence : Legs descriptor) :
    policyPostState prepared incidence = (pending.tuple primary).logicalPost incidence := by
  cases incidence with
  | factory => rfl
  | book => rfl
  | authority => rfl
  | allocation index =>
      exact (ResourceBirthController.allocation_post_exact prepared.directory.directory
        (creation descriptor index) (allocationFresh prepared index)).symm

def Pending.branchStep
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (branch : Branch descriptor) :
    PolicyStepContext :=
  let wanted := branchRequest prepared height branch
  PolicyStepContext.ofPreparedTupleExact (projectForRequest prepared height wanted)
    profile.semantics (pending.tuple (branchPrimary branch))
    (policyPreCell prepared) (policyPostState prepared)
    (pending.policyPreCell_exact (branchPrimary branch))
    (pending.policyPostState_exact (branchPrimary branch))

/-- The optimized selectors retain the complete original prepared-tuple
context, including the exact old/post policy states, effects, and pre-root. -/
theorem Pending.branchStep_prepared_exact
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (branch : Branch descriptor) :
    pending.branchStep branch =
  PolicyStepContext.ofPreparedTuple
    (projectForRequest prepared height (branchRequest prepared height branch))
    profile.semantics (pending.tuple (branchPrimary branch)) := by
  exact PolicyStepContext.ofPreparedTupleExact_eq _ _ _ _ _
    (pending.policyPreCell_exact (branchPrimary branch))
    (pending.policyPostState_exact (branchPrimary branch))

/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.Pending.branchStep_prepared_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Pending.branchStep_prepared_exact

/-- Structural selection uses the actual old governing target, including
factory-authorized allocation and authority branches. -/
def Pending.branchDependencies
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (_pending : Pending prepared height) (branch : Branch descriptor) :
    Option WorldKindLawDependencies.Dependencies :=
  WorldKindLawDependencies.loadTarget deployment prepared.directory.directory
    (branchRequest prepared height branch).2.target.value

/-- NativeHostContext/Genesis align the factory policy id with the factory
resource id. The v6 composed receiver intentionally refuses generic pins that
select a distinct governing policy; it never substitutes a newborn local law. -/
def Pending.branchConfig [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (branch : Branch descriptor) :
    ComposedPolicyAdmission.Config F :=
  PhysicalLawResolution.config profile.compilerProfile prepared.authority.snapshot
    prepared.directory.directory
    (sourcePortal prepared.authority.snapshot descriptor.authorityNullifier)
    (pending.branchStep branch) (branchRequest prepared height branch).2.target.value
    (((pending.branchDependencies branch).map (·.additional)).getD [])

/-- Failure to load the old target or any selected current/historical policy
source refuses the branch. No missing structural root becomes an empty law. -/
def Pending.branchReadGuards
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (branch : Branch descriptor) :
    Option (List (Nat × Digest)) := do
  let structural ← pending.branchDependencies branch
  let law ← PhysicalLawResolution.readGuards prepared.authority.snapshot
    prepared.directory.directory profile.semantics
    (branchRequest prepared height branch).2.target.value structural.additional
  some (structural.readGuards ++ law)

/-- All non-policy checks are the same fixed native source checks. Only the
policy witness adds an exact source-enumerated branch; each branch delegates
to the existing canonical compiler gate on its own full request and joint view. -/
def Pending.portal [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) : Portal :=
  let base := domainPortal prepared.authority.snapshot
    (sourcePortal prepared.authority.snapshot descriptor.authorityNullifier)
  { base with
    PolicyWitness := Branch descriptor × ComposedPolicyAdmission.Witness F
    policyAddress := fun witness => witness.2.compiled.address
    verifyCommittedPolicy := fun address kind request witness =>
      decide (AuthorizationDeclaration.encodeRequest ⟨kind, request⟩ =
        branchIdentity prepared height witness.1) &&
      (pending.branchConfig witness.1).portal.verifyCommittedPolicy address request witness.2 }

/-- Successful dispatch names its own complete request and canonical context.
In particular, changing cost, target, verb, pre-root or source arguments cannot
reuse the fee branch for a different funding authorization. -/
theorem Pending.dispatched_request_exact [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height)
    {kind : ResourceKind} (request : Request kind) (address : Digest)
    (witness : pending.portal.PolicyWitness)
    (accepted : pending.portal.verifyCommittedPolicy address request witness = true) :
    (⟨kind, request⟩ : PackedEffectRequest) = branchRequest prepared height witness.1 ∧
      (pending.branchConfig witness.1).portal.verifyCommittedPolicy address request witness.2 = true := by
  have checks := Bool.and_eq_true_iff.mp accepted
  constructor
  · have wire := of_decide_eq_true checks.1
    have decoded := congrArg AuthorizationDeclaration.decodeRequest wire
    simpa [branchIdentity, AuthorizationDeclaration.decodeRequest_encodeRequest] using decoded
  · exact checks.2

theorem Pending.no_other_branch [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height)
    (branch other : Branch descriptor) (different : branch ≠ other)
    (address : Digest) (compiled : ComposedPolicyAdmission.Witness F) :
    pending.portal.verifyCommittedPolicy address (branchRequest prepared height branch).2
      (other, compiled) = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have exactRequest := (pending.dispatched_request_exact _ _ (other, compiled) accepted).1
  apply different
  apply pending.requestsDistinct
  exact congrArg AuthorizationDeclaration.encodeRequest exactRequest

/-- Only the policy face changes during lifting. Every capability, native use
receipt, membership, issuer and revocation check is retained at the identical
actual request and old authority state. -/
def Pending.liftEvidence [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (branch : Branch descriptor)
    {kind : ResourceKind} {request : Request kind}
    (evidence : Evidence (pending.branchConfig branch).portal
      (oldAuthority prepared) request) : Evidence pending.portal (oldAuthority prepared) request := by
  unfold Pending.portal Pending.branchConfig PhysicalLawResolution.config
    ComposedPolicyAdmission.Config.portal at *
  cases evidence with
  | signature witness epoch verified => exact .signature witness epoch verified
  | proof witness verified => exact .proof witness verified
  | capability cap commitment commitmentWitness membershipWitness issuerWitness
      selfRevocationWitness useWitness semantic useVerified commitmentVerified
      membershipVerified issuerVerified selfRevocationVerified ancestorVerified channelVerified =>
      exact .capability cap commitment commitmentWitness membershipWitness issuerWitness
        selfRevocationWitness useWitness semantic useVerified commitmentVerified
        membershipVerified issuerVerified selfRevocationVerified ancestorVerified channelVerified

def Pending.liftAuthorization [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (branch : Branch descriptor)
    (authorized : Authorized (pending.branchConfig branch).portal (oldAuthority prepared)
      (branchRequest prepared height branch).2) :
    Authorized pending.portal (oldAuthority prepared) (branchRequest prepared height branch).2 where
  evidence := pending.liftEvidence branch authorized.evidence
  policyWitness := (branch, authorized.policyWitness)
  policyMembershipWitness := authorized.policyMembershipWitness
  policyEpochExact := authorized.policyEpochExact
  policyRevisionExact := authorized.policyRevisionExact
  policyAddressExact := authorized.policyAddressExact
  policyMembershipVerified := authorized.policyMembershipVerified
  policyVerified := by
    change (decide (AuthorizationDeclaration.encodeRequest (branchRequest prepared height branch) =
      branchIdentity prepared height branch) &&
      (pending.branchConfig branch).portal.verifyCommittedPolicy _ _ authorized.policyWitness) = true
    simp only [branchIdentity, decide_true, Bool.true_and]
    exact authorized.policyVerified


/-- The wire carries only the chosen source capability id and the actual
native envelope. Branch requests, profiles, snapshots and contexts are derived
by receiving source. Non-resource branches use the public factory's signed
identity path; every debit requires a source capability. -/
structure BranchCredential where
  capability : Option CapabilityId
  envelope : List UInt8
  deriving DecidableEq, Repr

def branchRequiresCapability : Branch descriptor → Bool
  | .source _ => true
  | _ => false

structure BranchAccepted [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (branch : Branch descriptor) : Type where
  credential : BranchCredential
  receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot
  envelopeExact : receipt.envelopeBytes = credential.envelope
  source : CanonicalCellRegistry.LoadedPolicySource deployment.domain prepared.directory.directory
    ((oldAuthority prepared).policyAddress (branchRequest prepared height branch).2.policyId
      (branchRequest prepared height branch).2.policyRevision)
  /-- Retain the already selected source's exact physical guard. Reconstructing
  its dependent address index later would recompute the entire branch request. -/
  sourceGuard : Nat × Digest
  sourceGuardExact : sourceGuard = source.readGuard
  lawGuards : List (Nat × Digest)
  lawGuardsExact : pending.branchReadGuards branch = some lawGuards
  lawGuardsBound : ∀ guard ∈ lawGuards,
    guard.2 = durable.snapshot.model.roots ⟨guard.1⟩
  authorization : Authorized pending.portal (oldAuthority prepared)
    (branchRequest prepared height branch).2
  modeBound : branchRequiresCapability branch = true →
    authorization.evidence.capabilityValue.isSome = true

def Pending.admitBranch [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (branch : Branch descriptor)
    (credential : BranchCredential)
    (receipt : CredentialSignatureAdmission.CheckedSignature prepared.authority.snapshot) :
    Except Reject { accepted : BranchAccepted pending branch // accepted.credential = credential } := do
  let envelopeExact ← require (receipt.envelopeBytes = credential.envelope) .credentialShape
  let wanted := branchRequest prepared height branch
  let config := pending.branchConfig branch
  let old := oldAuthority prepared
  let guards ← match exact : pending.branchReadGuards branch with
    | none => .error .policySourceUnavailable
    | some guards => .ok (⟨guards, exact⟩ : { guards // pending.branchReadGuards branch = some guards })
  let guardsBound ← require
    (∀ guard ∈ guards.val, guard.2 = durable.snapshot.model.roots ⟨guard.1⟩) .policySourceUnavailable
  let source ← match CanonicalCellRegistry.loadPolicySource deployment.domain
      prepared.directory.directory (old.policyAddress wanted.2.policyId wanted.2.policyRevision) with
    | none => .error .policySourceUnavailable
    | some loaded => .ok loaded
  let evidence : Evidence config.portal old wanted.2 ←
    if branchRequiresCapability branch then
        match credential.capability with
        | none => .error .capability
        | some identifier =>
            match config.capabilityEvidenceChecked wanted.2 identifier () receipt () (fun _ => ()) with
            | .error _ => .error .capability
            | .ok evidence => .ok evidence
    else
        if credential.capability = none then
          if epoch : wanted.2.subjectKeyEpoch = old.subjectKeyEpoch wanted.2.subject then
            if verified : config.portal.verifySignature wanted.2 receipt = true then
              .ok (.signature receipt epoch verified)
            else .error .signature
          else .error .signature
        else .error .credentialShape
  if epoch : wanted.2.policyEpoch = old.policyEpoch wanted.2.policyId then
    if revision : wanted.2.policyRevision = old.policyRevision wanted.2.policyId then
      match config.resolve? with
      | none => .error .policyUnavailable
      | some law =>
          let witness := law.witness
          match ComposedPolicyAdmission.admit config wanted.2 evidence witness
              (.policy wanted.2.policyId wanted.2.policyRevision) epoch revision with
          | none => .error .policyRejected
          | some admitted =>
              let authorization := pending.liftAuthorization branch admitted
              if modeBound : branchRequiresCapability branch = true →
                  authorization.evidence.capabilityValue.isSome = true then
                let accepted : BranchAccepted pending branch :=
                  { credential := credential
                    receipt := receipt
                    envelopeExact := envelopeExact.down
                    source := source
                    sourceGuard := source.readGuard
                    sourceGuardExact := rfl
                    lawGuards := guards.val
                    lawGuardsExact := guards.property
                    lawGuardsBound := guardsBound.down
                    authorization := authorization
                    modeBound := modeBound }
                .ok (show { accepted : BranchAccepted pending branch //
                  accepted.credential = credential } from ⟨accepted, rfl⟩)
              else .error .capability
    else .error .policyUnavailable
  else .error .policyUnavailable

def Pending.admitBranchNative [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (branch : Branch descriptor)
    (native : CredentialSignatureIO.NativeConfig) (credential : BranchCredential) :
    IO (Except Reject { accepted : BranchAccepted pending branch // accepted.credential = credential }) := do
  match ← CredentialSignatureAdmission.verifyNative native prepared.authority.snapshot
      descriptor.authorityNullifier (branchRequest prepared height branch).2 credential.envelope with
  | .error reason => return .error (.nativeSignature reason)
  | .ok receipt => return pending.admitBranch branch credential receipt

/-- A source-selected branch guard pins its exact immutable cell under the
actual outer storage root. Physical snapshot correspondence comes from the
prepared command's complete `LoadedDirectory`. -/
theorem BranchAccepted.source_capability_required [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} {pending : Pending prepared height}
    {position : Fin descriptor.resourceBatch.operations.length}
    (accepted : BranchAccepted pending (.source position)) :
    accepted.authorization.evidence.capabilityValue.isSome = true :=
  accepted.modeBound rfl

def BranchAccepted.readGuard [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} {pending : Pending prepared height} {branch : Branch descriptor}
    (accepted : BranchAccepted pending branch) := accepted.sourceGuard

/-- Retaining the guard changes no dependency, physical root, or branch
selection: it is exactly the value derived during this admission. -/
theorem BranchAccepted.readGuard_eq_source [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} {pending : Pending prepared height} {branch : Branch descriptor}
    (accepted : BranchAccepted pending branch) :
    accepted.readGuard = accepted.source.readGuard := accepted.sourceGuardExact

/-- info: 'Minidregg.Kernel.ResourceBirthPolicyController.Concrete.BranchAccepted.readGuard_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BranchAccepted.readGuard_eq_source


structure CredentialBundle where
  factory : BranchCredential
  authority : BranchCredential
  allocations : List BranchCredential
  sources : List BranchCredential
  deriving DecidableEq, Repr

open Minidregg.Compiler.Tower256ConcreteBackend in
def branchCredentialStream : StreamCodec BranchCredential :=
  StreamCodec.xmap (StreamCodec.product (StreamCodec.option CredentialAuthorityEntryCodec.capabilityIdStream) bytesStream)
    (fun credential => (credential.capability, credential.envelope))
    (fun pair => ⟨pair.1, pair.2⟩) (by intro credential; cases credential; rfl)

open Minidregg.Compiler.Tower256ConcreteBackend in
def credentialBundleStream : StreamCodec CredentialBundle :=
  StreamCodec.xmap
    (StreamCodec.product branchCredentialStream (StreamCodec.product branchCredentialStream
      (StreamCodec.product (StreamCodec.list branchCredentialStream)
        (StreamCodec.list branchCredentialStream))))
    (fun bundle => (bundle.factory, bundle.authority, bundle.allocations, bundle.sources))
    (fun tuple => ⟨tuple.1, tuple.2.1, tuple.2.2.1, tuple.2.2.2⟩)
    (by intro bundle; cases bundle; rfl)

/-- Complete canonical ingress retained for exact restart/reply replay. The
source descriptor remains its own strict versioned wire payload. -/
structure Ingress where
  descriptorBytes : List UInt8
  credentials : CredentialBundle
  deriving DecidableEq, Repr

open Minidregg.Compiler.Tower256ConcreteBackend in
def ingressStream : StreamCodec Ingress :=
  StreamCodec.xmap (StreamCodec.product bytesStream credentialBundleStream)
    (fun ingress => (ingress.descriptorBytes, ingress.credentials))
    (fun pair => ⟨pair.1, pair.2⟩) (by intro ingress; cases ingress; rfl)

def ingressFrame : List UInt8 := "DREGG/RESOURCE-BIRTH/SIGNED-INGRESS".toUTF8.toList ++ [2]

def ingressRawCodec : LawfulCodec Ingress where
  encode ingress := ingressFrame ++ ingressStream.encode ingress
  decode bytes := if bytes.take ingressFrame.length = ingressFrame then
    ingressStream.toLawful.decode (bytes.drop ingressFrame.length) else none
  decode_encode := by
    intro ingress
    have decoded := ingressStream.toLawful.decode_encode ingress
    change ingressStream.toLawful.decode (ingressStream.encode ingress) = some ingress at decoded
    simp [decoded]

def ingressCodec : LawfulCodec Ingress := strictCodec ingressRawCodec

structure DecodedIngress where
  private mk ::
  ingress : Ingress
  descriptor : Descriptor Registry
  descriptorExact : CanonicalCellRegistry.sourceEncoding.codec.decode ingress.descriptorBytes =
    some descriptor
  descriptorCanonical : CanonicalCellRegistry.sourceEncoding.codec.encode descriptor =
    ingress.descriptorBytes

def decodeIngress (bytes : List UInt8) : Option DecodedIngress := do
  let ingress ← ingressCodec.decode bytes
  match decoded : CanonicalCellRegistry.sourceEncoding.codec.decode ingress.descriptorBytes with
  | none => none
  | some descriptor => some ⟨ingress, descriptor, decoded,
      descriptor_decode_canonical Registry decoded⟩

def DecodedIngress.bytes (ingress : DecodedIngress) : List UInt8 :=
  ingressCodec.encode ingress.ingress

theorem decodeIngress_canonical {bytes : List UInt8} {ingress : DecodedIngress}
    (decoded : decodeIngress bytes = some ingress) : ingress.bytes = bytes := by
  unfold decodeIngress at decoded
  cases parsed : ingressCodec.decode bytes with
  | none => simp [parsed] at decoded
  | some raw =>
      simp only [parsed, bind, Option.bind] at decoded
      split at decoded
      · contradiction
      · cases Option.some.inj decoded
        exact strictCodec_canonical ingressRawCodec parsed

def CredentialBundle.forBranch (bundle : CredentialBundle) : Branch descriptor → Option BranchCredential
  | .factory => some bundle.factory
  | .authority => some bundle.authority
  | .allocation index => bundle.allocations[index.val]?
  | .source index => bundle.sources[index.val]?

structure AdmittedBundle [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height) (bundle : CredentialBundle) : Type where
  branches : (branch : Branch descriptor) → BranchAccepted pending branch
  inputsExact : ∀ branch, bundle.forBranch branch = some (branches branch).credential

/-- Select one dependent branch directly from its finite index. -/
private def directFinCases {n : Nat} {A : Fin (n + 1) → Type}
    (head : A 0) (tail : (index : Fin n) → A index.succ)
    (index : Fin (n + 1)) : A index :=
  if zero : index = 0 then
    zero.symm ▸ head
  else
    have positive : 0 < index.val := by
      by_contra notPositive
      have atZero : index.val = 0 := by omega
      exact zero (Fin.ext atZero)
    let previous : Fin n := ⟨index.val - 1, by omega⟩
    have same : previous.succ = index := by
      apply Fin.ext
      simp only [Fin.succ, previous]
      omega
    same ▸ tail previous

/-- The direct predecessor lookup preserves the full dependent `Fin.cases`
selection while avoiding its eager induction at runtime. -/
private theorem directFinCases_eq {n : Nat} {A : Fin (n + 1) → Type}
    (head : A 0) (tail : (index : Fin n) → A index.succ) :
    directFinCases head tail = Fin.cases head tail := by
  funext index
  cases index using Fin.cases with
  | zero => simp [directFinCases]
  | succ previous => simp [directFinCases]

/-- A dependent finite sequence checks every branch before exposing any
accepted bundle. Its callback is internal receiving code, never wire data. -/
private def sequenceFin {E : Type} : {n : Nat} → {A : Fin n → Type} →
    ((index : Fin n) → IO (Except E (A index))) → IO (Except E ((index : Fin n) → A index))
  | 0, _, _ => pure (.ok (fun index => Fin.elim0 index))
  | n + 1, A, action => do
      match ← action 0 with
      | .error error => return .error error
      | .ok head =>
          match ← sequenceFin (A := fun index : Fin n => A index.succ)
              (fun index => action index.succ) with
          | .error error => return .error error
          | .ok tail => return .ok (directFinCases head tail)

def Pending.admitBundleNative [DecidableEq F]
    {prepared : PreparedBirth profile.compilerProfile deployment pins durable descriptor}
    {height : Height} (pending : Pending prepared height)
    (native : CredentialSignatureIO.NativeConfig) (bundle : CredentialBundle) :
    IO (Except Reject (AdmittedBundle pending bundle)) := do
  if allocationCount : bundle.allocations.length = descriptor.createRequests.length then
    if sourceCount : bundle.sources.length = descriptor.resourceBatch.operations.length then
      let allocationIndex (index : Fin descriptor.createRequests.length) : Fin bundle.allocations.length :=
        Fin.cast allocationCount.symm index
      let sourceIndex (index : Fin descriptor.resourceBatch.operations.length) : Fin bundle.sources.length :=
        Fin.cast sourceCount.symm index
      match ← pending.admitBranchNative .factory native bundle.factory with
      | .error reason => return .error reason
      | .ok factory =>
          match ← pending.admitBranchNative .authority native bundle.authority with
          | .error reason => return .error reason
          | .ok authority =>
              match ← sequenceFin (E := Reject) (A := fun index : Fin descriptor.createRequests.length =>
                    { accepted : BranchAccepted pending (.allocation index) //
                      accepted.credential = bundle.allocations.get (allocationIndex index) })
                  (fun index => pending.admitBranchNative (.allocation index) native
                    (bundle.allocations.get (allocationIndex index))) with
              | .error reason => return .error reason
              | .ok allocations =>
                  let sourceResults : Except Reject
                      ((index : Fin descriptor.resourceBatch.operations.length) →
                        { accepted : BranchAccepted pending (.source index) //
                          accepted.credential = bundle.sources.get (sourceIndex index) }) ←
                    sequenceFin (E := Reject) (A := fun index : Fin descriptor.resourceBatch.operations.length =>
                        { accepted : BranchAccepted pending (.source index) //
                          accepted.credential = bundle.sources.get (sourceIndex index) })
                      (fun index => pending.admitBranchNative (.source index) native
                        (bundle.sources.get (sourceIndex index)))
                  match sourceResults with
                  | .error reason => return .error reason
                  | .ok sources =>
                      return .ok
                        { branches := fun branch => match branch with
                            | .factory => factory.val
                            | .authority => authority.val
                            | .allocation index => (allocations index).val
                            | .source index => (sources index).val
                          inputsExact := by
                            intro branch
                            cases branch with
                            | factory => exact congrArg some factory.property.symm
                            | authority => exact congrArg some authority.property.symm
                            | allocation index =>
                                change bundle.allocations[index.val]? = some (allocations index).val.credential
                                rw [(allocations index).property]
                                simp only [List.get_eq_getElem]
                                exact List.getElem?_eq_getElem (by omega)
                            | source index =>
                                change bundle.sources[index.val]? = some (sources index).val.credential
                                rw [(sources index).property]
                                simp only [List.get_eq_getElem]
                                exact List.getElem?_eq_getElem (by omega) }
    else return .error .credentialShape
  else return .error .credentialShape

/-- The actual admitted native birth. A caller cannot manufacture it by
supplying portals, successful Booleans, policy contexts or a prepared state.
The constructor below is reached only after the fixed whole-bundle verifier. -/
structure AcceptedBirth [DecidableEq F]
    (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment) (pins : FactoryPins)
    (durable : Durable) (height : Height) : Type where
  private mk ::
  ingress : DecodedIngress
  prepared : PreparedBirth profile.compilerProfile deployment pins durable ingress.descriptor
  pending : Pending prepared height
  admitted : AdmittedBundle pending ingress.ingress.credentials

/-- A replay-aware durable endpoint calls this only after comparing canonical
`ingress.bytes` with any recorded transaction. Fresh-state admission itself
has no replay bypass or source-state reconstruction from a historical receipt. -/
def admitDecodedNative [DecidableEq F]
    (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig) (durable : Durable) (height : Height)
    (ingress : DecodedIngress) : IO (Except Reject (AcceptedBirth profile deployment pins durable height)) := do
  match ResourceBirthController.Concrete.prepareBirth profile.compilerProfile
      profile.disabledEvaluators deployment pins
      durable ingress.descriptor height with
  | .error reason => return .error (.preparation reason)
  | .ok prepared =>
      match preparePending prepared height with
      | .error reason => return .error reason
      | .ok pending =>
          match ← pending.down.admitBundleNative native ingress.ingress.credentials with
          | .error reason => return .error reason
          | .ok branches => return .ok ⟨ingress, prepared, pending.down, branches⟩

def admitNative [DecidableEq F]
    (profile : CanonicalRuntimeProfile.Profile F) (deployment : Deployment) (pins : FactoryPins)
    (native : CredentialSignatureIO.NativeConfig) (durable : Durable) (height : Height)
    (bytes : List UInt8) : IO (Except Reject (AcceptedBirth profile deployment pins durable height)) :=
  match decodeIngress bytes with
  | none => pure (.error .malformedIngress)
  | some ingress => admitDecodedNative profile deployment pins native durable height ingress

end Receiving

variable {F : Type} [Field F] [DecidableEq F]
    {profile : CanonicalRuntimeProfile.Profile F}
    {deployment : Deployment} {pins : FactoryPins} {durable : Durable}

def AcceptedBirth.branches {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) := accepted.admitted.branches

theorem AcceptedBirth.native_ingress_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    (branch : Branch accepted.ingress.descriptor) :
    ∃ credential,
      accepted.ingress.ingress.credentials.forBranch branch = some credential ∧
      (accepted.branches branch).receipt.envelopeBytes = credential.envelope :=
  ⟨(accepted.branches branch).credential, accepted.admitted.inputsExact branch,
    (accepted.branches branch).envelopeExact⟩

def AcceptedBirth.descriptor {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) := accepted.ingress.descriptor

/-- **`birth_under_room_requires_grant`** at the native admission: an admitted
birth of an item into room `R` names the creator's placing capability, stored in
the authority cell, held by the creator and admissible for its `placeObject`
request on `R` (the gate ran at `admitDecodedNative`'s admission height, which
it passes to `prepareBirth`). `R`'s law accepting it is the remaining conjunct
of `PreparedBirth.birth_under_room_requires_grant`. -/
theorem AcceptedBirth.birth_under_room_requires_grant {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height)
    {item : BirthItem Registry} (member : item ∈ accepted.descriptor.births)
    {room : Nat} (inRoom : item.parent = some room) :
    ∃ placement cap, item.placement = some placement ∧
      RoomBirthGate.storedAt accepted.prepared.authority placement = some cap ∧
      cap.holder.Covers accepted.descriptor.creator ∧
      cap.Admissible accepted.prepared.authority.snapshot.authState
        (RoomBirthGate.placeRequest pins accepted.prepared.authority.snapshot.authState
          (RoomBirthGate.roomRoot accepted.prepared.directory.directory room) accepted.prepared.gateHeight
          accepted.descriptor room) :=
  let ⟨placement, cap, named, stored, holder, admissible, _⟩ :=
    accepted.prepared.birth_under_room_requires_grant member inRoom
  ⟨placement, cap, named, stored, holder, admissible⟩

def AcceptedBirth.tuple {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) :=
  accepted.pending.tuple .factory

def AcceptedBirth.portals {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) : Legs accepted.descriptor → Portal :=
  fun _ => accepted.pending.portal

def AcceptedBirth.admissionEvidence {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) :
    accepted.tuple.AdmissionEvidence accepted.portals where
  modes incidence := by
    cases incidence with
    | factory => exact ()
    | book =>
        exact
          { factory := accepted.pending.checked.authorize (accepted.branches .factory).authorization
            admission := accepted.prepared.resources.admission
            sources := fun position => (accepted.branches (.source position)).authorization }
    | authority => exact accepted.prepared.grants.mode
    | allocation index =>
        exact (ResourceBirthController.allocationCandidate pins CanonicalCellRegistry.sourceEncoding
          (oldAuthority accepted.prepared) accepted.prepared.allocated
          (creation accepted.descriptor index) (List.get_mem _ _) height).modeEvidence
  authorizations incidence := by
    cases incidence with
    | factory => exact (accepted.branches .factory).authorization
    | authority => exact (accepted.branches .authority).authorization
    | book => exact (accepted.branches (.source (CanonicalResourceEffect.feePosition accepted.descriptor))).authorization
    | allocation index => exact (accepted.branches (.allocation index)).authorization
  disclosure := fun _ => .sealed
  disclosureAllowed incidence := by
    cases incidence <;> trivial

def AcceptedBirth.acceptedLegs {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) (apex : Digest) :=
  accepted.tuple.accept accepted.portals apex accepted.admissionEvidence

/-- Every logical post lowered by the final turn is the one the branch
policies evaluated before any authorization was constructed. -/
theorem AcceptedBirth.actual_posts_exact {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) (apex : Digest)
    (incidence : Legs accepted.descriptor) :
    (accepted.tuple.toDeclaration accepted.portals apex).post
        (accepted.acceptedLegs apex) incidence = accepted.tuple.post incidence :=
  accepted.tuple.accepted_posts_exact accepted.portals apex accepted.admissionEvidence incidence

def AcceptedBirth.sourceReadGuards {height : Height}
    (accepted : AcceptedBirth profile deployment pins durable height) : List (Nat × Digest) :=
  (policyBranches accepted.descriptor.createRequests.length
    accepted.descriptor.resourceBatch.operations.length).flatMap fun branch =>
      (accepted.branches branch).lawGuards


end Concrete

end Minidregg.Kernel.ResourceBirthPolicyController
